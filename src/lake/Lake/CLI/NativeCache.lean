/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Init.System.IO
import Lean.Data.Json
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Native-code cache for dependency modules (`lake native-cache-populate`)

The Lean frontend loads a *bundle* of native code for imported modules from the native cache
(`src/library/native_cache.cpp`: `$LEAN_NATIVE_CACHE`, default `$XDG_CACHE_HOME/lean/native` or
`~/.cache/lean/native`, then `<githash>-<target>/bundles/<id>.{so,manifest}`) when every module of the
bundle was imported from the very same `.olean` file (device, inode, size, mtime). Then the
interpreter calls the native code of those modules (it prefers native symbols) and their module
initializers run natively, exactly as with `--load-dynlib` / `precompileModules`.

`lake build` starts ONE detached populate job per build (`spawnPopulate`), at the lowest CPU priority
and with at most half of the hardware threads, unless `LEAN_NATIVE_CACHE=0`. The job does nothing when
nothing changed since its last run for the workspace. Otherwise it waits for the build to exit, takes
the import closures of the root package's modules from Lake's `.setup.json` files, and for the most
common closures (dependency modules only: the root package changes too often; toolchain modules are
in `libleanshared` already) compiles the C that Lake emitted for each module once (content-addressed
by Lake's hash of the C file) and links a bundle with a manifest of the bundled `.olean` identities.
A module is bundled only if its `.c` and `.olean` come from the same build job (per its `.trace`),
the `.olean` was written by this toolchain, and all of its imports are bundled (import-closed set).
A library rebuild or a toolchain change thus invalidates bundles automatically (other identities or
another `<githash>` directory). The cache is bounded (`LEAN_NATIVE_CACHE_MAX_MB`, default 4096):
least recently used bundles (the loader refreshes a manifest's mtime when it uses it) and then
unreferenced objects are deleted.
-/

namespace Lake.NativeCache

open Lean (Json)

/-- `"<st_dev> <st_ino> <size> <mtime_ns>"` of a file (the identity the Lean frontend checks). -/
@[extern "lean_native_cache_file_key"]
opaque fileKey (path : @& String) : IO String

/-- The cache root, or `none` if disabled (`LEAN_NATIVE_CACHE=0`/`off`) or unknown. -/
public def cacheRoot? : IO (Option System.FilePath) := do
  match (← IO.getEnv "LEAN_NATIVE_CACHE") with
  | some "0" | some "off" => return none
  | some d => if d.isEmpty then pure () else return some d
  | none => pure ()
  if let some x ← IO.getEnv "XDG_CACHE_HOME" then
    unless x.isEmpty do return some (x / "lean" / "native")
  if let some h ← IO.getEnv "HOME" then
    unless h.isEmpty do return some (h / ".cache" / "lean" / "native")
  return none

def target : String :=
  if System.Platform.target.startsWith "x86_64" then "x86_64"
  else if System.Platform.target.startsWith "aarch64" || System.Platform.target.startsWith "arm64" then "aarch64"
  else "other"

/-- Everything the populate job needs; passed on its command line so it does not load the workspace. -/
public structure Config where
  githash : String
  cc : String
  ccFlags : Array String
  linkFlags : Array String
  /-- the toolchain's `lib/lean` (its modules are never bundled) -/
  leanLibDir : String
  /-- the toolchain's `include` (objects are kept per `lean.h` content) -/
  includeDir : String := ""
  /-- the root package's IR directory (where Lake writes `<mod>.setup.json`) -/
  rootIrDir : String
  jobs : Nat := 1
  waitPid : Option Nat := none
  maxBundles : Nat := 2
  deriving Inhabited

def Config.toArgs (c : Config) : Array String :=
  #["--githash", c.githash, "--cc", c.cc, "--lean-lib-dir", c.leanLibDir, "--include-dir", c.includeDir,
    "--root-ir-dir", c.rootIrDir,
    "--jobs", toString c.jobs] ++ (c.waitPid.map (fun p => #["--wait-pid", toString p]) |>.getD #[]) ++
  c.ccFlags.flatMap (fun f => #["--cflag", f]) ++ c.linkFlags.flatMap (fun f => #["--ldflag", f])

public partial def Config.ofArgs (args : List String) (c : Config := default) : Except String Config :=
  match args with
  | [] => .ok c
  | "--githash" :: v :: r => Config.ofArgs r {c with githash := v}
  | "--cc" :: v :: r => Config.ofArgs r {c with cc := v}
  | "--lean-lib-dir" :: v :: r => Config.ofArgs r {c with leanLibDir := v}
  | "--root-ir-dir" :: v :: r => Config.ofArgs r {c with rootIrDir := v}
  | "--include-dir" :: v :: r => Config.ofArgs r {c with includeDir := v}
  | "--jobs" :: v :: r => Config.ofArgs r {c with jobs := v.toNat?.getD 1}
  | "--wait-pid" :: v :: r => Config.ofArgs r {c with waitPid := v.toNat?}
  | "--cflag" :: v :: r => Config.ofArgs r {c with ccFlags := c.ccFlags.push v}
  | "--ldflag" :: v :: r => Config.ofArgs r {c with linkFlags := c.linkFlags.push v}
  | a :: _ => .error s!"native-cache-populate: unknown argument {a}"

def readTrim (p : System.FilePath) : IO (Option String) := do
  try return some (← IO.FS.readFile p).trimAscii.toString catch _ => return none

def hexOf (n : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 n.toNat)
  "".pushn '0' (16 - s.length) ++ s

def mtimeNs (p : System.FilePath) : IO Nat := do
  let m ← p.metadata
  return m.modified.sec.toNat * 1000000000 + m.modified.nsec.toNat

/-- `<mod>.olean` -> `<mod>.c` in Lake's layout (`.../lib/lean/A/B.olean` -> `.../ir/A/B.c`). -/
def cFileOf (olean : String) : Option String := do
  let parts := olean.splitOn "/lib/lean/"
  guard (parts.length ≥ 2)
  let pre := String.intercalate "/lib/lean/" parts.dropLast
  let rel ← parts.getLast?
  let stem ← rel.dropSuffix? ".olean"
  return pre ++ "/ir/" ++ stem.toString ++ ".c"

/-- The `importArts` of a `.setup.json`: module name -> its `.olean` path. -/
def readImportArts (setup : System.FilePath) : IO (Option (String × Array (String × String))) := do
  let some txt ← (try some <$> IO.FS.readFile setup catch _ => pure none) | return none
  let .ok j := Json.parse txt | return none
  let .ok name := j.getObjValAs? String "name" | return none
  let .ok (.obj arts) := j.getObjVal? "importArts" | return none
  let mut out := #[]
  for (m, v) in arts.toList do
    match v with
    | Json.arr groups =>
      match groups[0]? with
      | some (Json.arr files) =>
        match files[0]? with
        | some (Json.str ol) => out := out.push (m, ol)
        | _ => pure ()
      | _ => pure ()
    | _ => pure ()
  return some (name, out)

structure ModInfo where
  olean : String
  c : String
  chash : String
  /-- imports: module name and `.olean` path -/
  deps : Array (String × String)

/-- Eligibility of one dependency module (see the module docstring). -/
def moduleInfo (githash : String) (olean : String) : IO (Except String ModInfo) := do
  let some c := cFileOf olean | return .error "not in a Lake layout"
  unless (← System.FilePath.pathExists c) do return .error "no .c"
  let some ch ← readTrim (c ++ ".hash") | return .error "no .c.hash"
  let some oh ← readTrim (olean ++ ".hash") | return .error "no .olean.hash"
  let stem := (olean.dropSuffix? ".olean").map (·.toString) |>.getD olean
  let some tr ← (try some <$> IO.FS.readFile (stem ++ ".trace") catch _ => pure none) | return .error "no trace"
  let .ok tj := Json.parse tr | return .error "bad trace"
  let .ok outs := tj.getObjVal? "outputs" | return .error "trace without outputs"
  let cOut := (outs.getObjValAs? String "c").toOption.getD ""
  let oOut := match outs.getObjVal? "o" with
    | .ok (Json.arr a) => match a[0]? with | some (Json.str s) => s | _ => ""
    | .ok (Json.str s) => s
    | _ => ""
  unless (cOut.splitOn ".")[0]! == ch do return .error "c/trace mismatch"
  unless (oOut.splitOn ".")[0]! == oh do return .error "olean/trace mismatch"
  let h ← IO.FS.Handle.mk olean .read
  let hdr ← h.read 256
  let hdrStr := String.ofList (hdr.toList.map (fun b => Char.ofNat b.toNat))
  unless hdrStr.contains githash do
    return .error "olean from another toolchain"
  let some (_, arts) ← readImportArts (((c.dropSuffix? ".c").map (·.toString)).getD c ++ ".setup.json")
    | return .error "no setup.json"
  return .ok { olean, c, chash := ch, deps := arts }

/-- The toolchain identity the frontend checks (`native_cache.cpp`, `toolchain_id`):
`<name>:<dev>:<ino>:<size>:<mtime_ns>` of every `libleanshared*.so` in the toolchain's library dir. -/
def toolchainId (leanLibDir : String) : IO String := do
  let mut names := #[]
  for e in (← try System.FilePath.readDir leanLibDir catch _ => pure #[]) do
    if e.fileName.startsWith "libleanshared" && e.fileName.endsWith ".so" then names := names.push e.fileName
  let mut parts := #[]
  for n in names.qsort (· < ·) do
    parts := parts.push s!"{n}:{(← fileKey (leanLibDir ++ "/" ++ n)).replace " " ":"}"
  return String.intercalate ";" parts.toList

/-- Run `cmds` on `n` worker threads (each takes the next command when it is done); returns the number
that failed and the first failure's stderr. -/
def runPool (n : Nat) (cmds : Array IO.Process.SpawnArgs) : IO (Nat × String) := do
  let next ← IO.mkRef 0
  let worker : IO (Nat × String) := do
    let mut failed := 0
    let mut firstErr := ""
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < cmds.size then
        let ok ← try
            let out ← IO.Process.output cmds[i]
            if out.exitCode != 0 && failed == 0 then firstErr := out.stderr
            pure (out.exitCode == 0)
          catch e =>
            if failed == 0 then firstErr := toString e
            pure false
        unless ok do failed := failed + 1
      else
        break
    return (failed, firstErr)
  let tasks ← (List.range (max n 1)).toArray.mapM fun _ => IO.asTask worker Task.Priority.dedicated
  let mut failed := 0
  let mut firstErr := ""
  for t in tasks do
    match ← IO.wait t with
    | .ok (f, e) => if failed == 0 && f > 0 then firstErr := e
                    failed := failed + f
    | .error e => if failed == 0 then firstErr := toString e
                  failed := failed + 1
  return (failed, firstErr)

def isCore (leanLibDir : String) (olean : String) : Bool :=
  olean.startsWith (leanLibDir ++ "/") ||
  -- the toolchain's own modules (their code is in the toolchain's shared libraries), also when the
  -- toolchain is reached through another path
  ["Init", "Std", "Lean", "Lake", "LeanExport"].any fun r =>
    match (olean.splitOn "/lib/lean/").getLast? with
    | some rel => rel == r ++ ".olean" || rel.startsWith (r ++ "/")
    | none => false

/-- Delete least recently used bundles, then unreferenced objects, while the cache exceeds `maxBytes`. -/
def evict (dir : System.FilePath) (maxBytes : Nat) : IO Unit := do
  let bdir := dir / "bundles"
  let size (p : System.FilePath) : IO Nat := do try return (← p.metadata).byteSize.toNat catch _ => return 0
  let mut bundles : Array (Nat × String) := #[]
  let mut total := 0
  for e in (← try bdir.readDir catch _ => pure #[]) do
    total := total + (← size e.path)
    if e.fileName.endsWith ".manifest" then
      bundles := bundles.push (← mtimeNs e.path, (e.fileName.dropSuffix? ".manifest").get!.toString)
  let mut objs := #[]
  for d in (← try dir.readDir catch _ => pure #[]) do
    if d.fileName.startsWith "obj" then
      objs := objs ++ (← try d.path.readDir catch _ => pure #[])
  for e in objs do total := total + (← size e.path)
  if total ≤ maxBytes then return
  let mut kept := bundles.qsort (fun a b => a.1 < b.1)
  -- keep at least the newest bundle
  while total > maxBytes && kept.size > 1 do
    let id := kept[0]!.2
    for ext in [".so", ".manifest", ".objs"] do
      let p := bdir / (id ++ ext)
      total := total - min total (← size p)
      try IO.FS.removeFile p catch _ => pure ()
    kept := kept.extract 1 kept.size
  if total ≤ maxBytes then return
  let mut refd : Std.HashSet String := {}
  for (_, id) in kept do
    for l in ((← try IO.FS.readFile (bdir / (id ++ ".objs")) catch _ => pure "").splitOn "\n") do
      refd := refd.insert l
  for e in objs do
    if !refd.contains e.fileName && total > maxBytes then
      total := total - min total (← size e.path)
      try IO.FS.removeFile e.path catch _ => pure ()

/-- The populate job (`lake native-cache-populate ...`). Returns the number of bundles written. -/
public def populate (cfg : Config) (log' : String → IO Unit := fun _ => pure ()) : IO Nat := do
  let some root ← cacheRoot? | return 0
  let dir := root / s!"{cfg.githash}-{target}"
  IO.FS.createDirAll dir
  -- the job runs detached: also keep a log in the cache directory
  let log (msg : String) : IO Unit := do
    log' msg
    try
      let h ← IO.FS.Handle.mk (dir / "populate.log") .append
      h.putStrLn msg
    catch _ => pure ()
  let bdir := dir / "bundles"
  -- objects depend on the lean.h they were compiled against (toolchain builds may share a githash)
  let leanH ← try IO.FS.readFile (cfg.includeDir ++ "/lean/lean.h") catch _ => pure ""
  let odir := dir / s!"obj-{hexOf (hash leanH)}"
  IO.FS.createDirAll bdir; IO.FS.createDirAll odir
  -- one job at a time per toolchain cache; a lock older than 2 h is stale
  let lock := dir / "populate.lock"
  let tryLock : IO Bool := do
    try discard <| IO.FS.Handle.mk lock .writeNew; return true catch _ => return false
  unless (← tryLock) do
    let some m ← (try some <$> mtimeNs lock catch _ => pure none) | return 0
    -- "now" = the mtime of a file written now (same clock as the lock's mtime)
    let probe := dir / s!"now-{(← IO.Process.getPID)}"
    IO.FS.writeFile probe ""
    let now ← mtimeNs probe
    try IO.FS.removeFile probe catch _ => pure ()
    if now < m + 7200 * 1000000000 then return 0
    try IO.FS.removeFile lock catch _ => pure ()
    unless (← tryLock) do return 0
  try
    -- skip when no setup file changed since the last completed run for this workspace
    let marker := dir / s!"done-{hexOf (hash cfg.rootIrDir)}"
    let lastDone ← try mtimeNs marker catch _ => pure 0
    if let some pid := cfg.waitPid then
      -- the build that spawned us writes the setup files of the modules it builds
      while (← System.FilePath.pathExists s!"/proc/{pid}") do IO.sleep 2000
    let setups ← (System.FilePath.walkDir cfg.rootIrDir).catchExceptions (fun _ => pure #[])
    log s!"native-cache: populate for {cfg.rootIrDir} (cc {cfg.cc}, {cfg.jobs} jobs, objects in {odir})"
    let setups := setups.filter (·.toString.endsWith ".setup.json")
    let mut newest := 0
    for s in setups do newest := max newest (← mtimeNs s)
    if setups.isEmpty || (lastDone > 0 && newest ≤ lastDone) then return 0
    -- import closures of the root modules, restricted to dependency modules (one pass; only distinct
    -- closures are kept in memory). Root modules' oleans live in the root package's lib dir.
    let rootLib := (((cfg.rootIrDir.dropSuffix? "/ir").map (·.toString)).getD cfg.rootIrDir) ++ "/lib/lean/"
    let mut closures : Std.HashMap UInt64 (Nat × Array (String × String)) := {}
    for s in setups do
      if let some (_, arts) ← readImportArts s then
        let deps := arts.filter (fun (_, ol) => !ol.startsWith rootLib && !isCore cfg.leanLibDir ol)
        let deps := deps.qsort (fun a b => a.1 < b.1)
        let key := hash (String.intercalate "," (deps.map (·.1)).toList)
        match closures[key]? with
        | some (n, ds) => closures := closures.insert key (n + 1, ds)
        | none => closures := closures.insert key (1, deps)
    let chosen := (closures.toArray.qsort (fun a b => a.2.1 > b.2.1)).extract 0 cfg.maxBundles
    log s!"native-cache: {setups.size} setup files, {closures.size} distinct dependency closures"
    let mut written := 0
    let mut memo : Std.HashMap String (Except String ModInfo) := {}
    for (_, (_, deps)) in chosen do
      if deps.isEmpty then continue
      let mut info : Std.HashMap String ModInfo := {}
      let mut why : Array String := #[]
      for (m, ol) in deps do
        let r ← match memo[m]? with | some r => pure r | none => moduleInfo cfg.githash ol
        memo := memo.insert m r
        match r with
        | .ok i => info := info.insert m i
        | .error e => if why.size < 3 then why := why.push s!"{m}: {e}"
      unless why.isEmpty do log s!"native-cache: not eligible (first): {why}"
      -- import-closed: drop modules importing a module that is neither bundled nor a toolchain module
      let mut changed := true
      while changed do
        changed := false
        for (m, i) in info.toArray do
          if i.deps.any (fun (d, ol) => !info.contains d && !isCore cfg.leanLibDir ol) then
            info := info.erase m; changed := true
      if info.isEmpty then continue
      log s!"native-cache: {info.size} of {deps.size} dependency modules eligible"
      let mods := (info.toArray.qsort (fun a b => a.1 < b.1)).map (·.2)
      let cmds : Array IO.Process.SpawnArgs := mods.map fun i =>
        let o := (odir / (i.chash ++ ".o")).toString
        { cmd := cfg.cc, args := #["-c", "-o", o ++ ".tmp", i.c] ++ cfg.ccFlags ++
          #["-O3", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC"] }
      let mut todo : Array (IO.Process.SpawnArgs × ModInfo) := #[]
      for (cmd, i) in cmds.zip mods do
        unless (← System.FilePath.pathExists (odir / (i.chash ++ ".o"))) do todo := todo.push (cmd, i)
      let (nfail, err) ← runPool cfg.jobs (todo.map (·.1))
      if nfail > 0 then log s!"native-cache: {nfail} compilations failed, first: {err}"
      let mut ok := true
      for (_, i) in todo do
        let o := odir / (i.chash ++ ".o")
        try IO.FS.rename (o.toString ++ ".tmp") o catch _ => ok := false
      unless ok do log "native-cache: some objects failed to compile"; continue
      let objs := mods.map (fun i => (odir / (i.chash ++ ".o")).toString)
      let id := hexOf (hash (String.intercalate "\n" (mods.map (·.chash)).toList ++ cfg.githash))
      let so := bdir / (id ++ ".so"); let man := bdir / (id ++ ".manifest")
      unless (← so.pathExists) do
        let rsp := bdir / (id ++ ".rsp")
        IO.FS.writeFile rsp (String.intercalate "\n" objs.toList)
        let linkArgs := #["-shared", "-o", so.toString ++ ".tmp", "@" ++ rsp.toString] ++ cfg.linkFlags
        let out ← IO.Process.output { cmd := cfg.cc, args := linkArgs }
        try IO.FS.removeFile rsp catch _ => pure ()
        if out.exitCode != 0 then
          log s!"native-cache: link failed: {out.stderr}"
          continue
        IO.FS.rename (so.toString ++ ".tmp") so
      IO.FS.writeFile (bdir / (id ++ ".objs")) (String.intercalate "\n" (mods.map (·.chash ++ ".o")).toList)
      let mut lines := #[s!"lean-native-bundle 2 {cfg.githash} {← toolchainId cfg.leanLibDir}"]
      for i in mods do lines := lines.push s!"{← fileKey i.olean} {i.olean}"
      IO.FS.writeFile (man.toString ++ ".tmp") (String.intercalate "\n" lines.toList ++ "\n")
      IO.FS.rename (man.toString ++ ".tmp") man
      log s!"native-cache: bundle {so} ({mods.size} modules)"
      written := written + 1
    let maxMb := ((← IO.getEnv "LEAN_NATIVE_CACHE_MAX_MB").bind String.toNat?).getD 4096
    evict dir (maxMb * 1024 * 1024)
    IO.FS.writeFile marker ""
    return written
  finally
    try IO.FS.removeFile lock catch _ => pure ()

/-- Read the populate job's configuration (one argument per line, as written by `spawnPopulate`). -/
public def Config.load (file : System.FilePath) : IO Config := do
  let lines := (← IO.FS.readFile file).splitOn "\n" |>.filter (!·.isEmpty)
  match Config.ofArgs lines with
  | .ok c => return c
  | .error e => throw <| IO.userError e

/--
Start the populate job for a build, detached and at the lowest CPU priority, with at most half the
hardware threads. Does nothing when the cache is disabled or the workspace has no IR directory.
-/
public def spawnPopulate (lakeExe : System.FilePath) (cfg : Config) : IO Unit := do
  let some _ ← cacheRoot? | return
  if (← IO.getEnv "LAKE_NATIVE_CACHE_POPULATE") == some "0" then return
  let jobs := max 1 ((← nproc) / 2)
  let cfg := {cfg with jobs, waitPid := some (← IO.Process.getPID).toNat}
  try
    let some root ← cacheRoot? | return
    let dir := root / s!"{cfg.githash}-{target}"
    IO.FS.createDirAll dir
    let cfgFile := dir / s!"populate-{cfg.waitPid.getD 0}.args"
    IO.FS.writeFile cfgFile (String.intercalate "\n" cfg.toArgs.toList ++ "\n")
    let args := #["-n", "19", lakeExe.toString, "native-cache-populate", cfgFile.toString]
    discard <| IO.Process.spawn {cmd := "nice", args, stdin := .null, stdout := .null, stderr := .null, setsid := true}
  catch _ => pure ()
where
  nproc : IO Nat := do
    try
      let out ← IO.Process.output {cmd := "nproc", args := #[]}
      return out.stdout.trimAscii.toString.toNat?.getD 2
    catch _ => return 2

end Lake.NativeCache
