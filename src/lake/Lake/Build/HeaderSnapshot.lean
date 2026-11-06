/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Util.Log
public import Lake.Build.Trace
public import Lean.Setup
import Lake.Util.IO
import Lean.Elab.ParseImportsFast
import Init.Data.String.Search
import Init.System.Platform

/-! # Header Snapshots

Lake-managed reuse of Lean's header snapshots (`lean --incr-header-save` / `--incr-load`).

Elaborating a module starts by importing its header, which for a module on top of a large library
(e.g., Mathlib) can dominate the run (≈1 s of process start and import). Lean can save the
environment right after the header (`--incr-header-save`) and a later run whose header is
syntactically identical can start from it (`--incr-load`) instead of importing again.
The produced `.olean` and messages are unchanged.

Lake manages these snapshots automatically for every Lean run it starts (module builds and
`lake lean`):

* The *header key* hashes everything the post-header state depends on: the header text (the
  source prefix up to the end of the imports), the module setup (with the module name normalized:
  the frontend patches the main module of a loaded snapshot), the transitive import trace (so the
  hashes of every imported `.olean`), the Lean arguments and `LEAN_PATH`, and the identity of the
  `lean` binary (githash, path, size, mtime). A stale snapshot is therefore never reused.
* A snapshot exists → the run gets `--incr-load`.
* Otherwise, once a key has been used `minUses` times (default 2), a background process at nice 19
  saves the snapshot from an *import-only copy* of the header (never from the full module) into
  `<buildDir>/headers/<key>.hsnap`, checks that it loads, and publishes it atomically. The run
  that triggers the save is not delayed.
* Snapshots whose header produced any message are never published (the messages would carry the
  import-only file's name); modules with plugins or dynlibs never use snapshots (the setup's
  dynlibs are loaded during header processing, which a loaded snapshot skips).
* The directory is capped (default 8 GiB; the least used, then least recently used snapshots go
  first) and at most 2 saves run at a time (a key that finds no free slot is saved by a later use).
* `lake build` only *loads* snapshots by default: background saves next to a parallel build cost
  more than the loads gain on a clean build. Saves come from `lake lean` (the agent case, where the
  same header repeats) or, for builds, with `LAKE_HEADER_SNAPSHOT_BUILD_SAVES=1`. `lake build`
  stops the saves it started when it finishes (`LAKE_HEADER_SNAPSHOT_REAP=0` keeps them).

Environment variables: `LAKE_HEADER_SNAPSHOTS=0` disables the mechanism,
`LAKE_HEADER_SNAPSHOT_MIN_USES=<n>` sets the threshold (1 = save on first use),
`LAKE_HEADER_SNAPSHOT_MAX_MB=<n>` sets the cap, `LAKE_HEADER_SNAPSHOT_MAX_SAVES=<n>` bounds the
number of concurrent background saves per directory (default 2).
-/

open System Lean

namespace Lake.HeaderSnapshot

/-- What Lake decided for one Lean run. -/
public structure Plan where
  /-- Extra arguments for the Lean run (`--incr-load=<file>` when a snapshot exists). -/
  loadArgs : Array String := #[]
  /-- The background save to spawn, if any. -/
  save? : Option IO.Process.SpawnArgs := none
  deriving Inhabited

/-- Lean arguments that do not change the post-header state, or only via the key. -/
def isSafeArg (a : String) : Bool :=
  a.startsWith "-D" || a.startsWith "-j" || a.startsWith "--threads" ||
  a.startsWith "-t" || a.startsWith "--tstack" || a == "--json" ||
  a.startsWith "-E" || a.startsWith "--error" || a.startsWith "-M" || a.startsWith "--memory" ||
  a.startsWith "-T" || a.startsWith "--timeout" || a.startsWith "-R" || a.startsWith "--root"

/-- Output flags that take a value; they are dropped from the save run. -/
def outputFlags : List String :=
  ["-o", "-i", "-c", "-b", "--olean", "--ilean", "--c", "--bc"]

/--
Splits Lean arguments into the ones the save run must also get (all but outputs) and reports
whether snapshots are safe at all with these arguments (unknown flags disable them).
-/
public def filterArgs (args : Array String) : Option (Array String) := Id.run do
  let mut out := #[]
  let mut i := 0
  while h : i < args.size do
    let a := args[i]
    if outputFlags.contains a then
      i := i + 2
    else if outputFlags.any (fun f => f.startsWith "--" && a.startsWith (f ++ "=")) then
      i := i + 1
    else if isSafeArg a then
      out := out.push a
      i := i + 1
      -- `-D name=value`, `-j n`, ... with a separate value
      if a == "-D" || a == "-j" || a == "-t" || a == "-E" || a == "-M" || a == "-T" || a == "-R" then
        if h' : i < args.size then
          out := out.push args[i]
          i := i + 1
    else
      return none
  return some out

/-- The source prefix that holds the module header (up to the end of the imports). -/
public def headerPrefix? (input : String) : Option String :=
  let s := ParseImports.main input (ParseImports.whitespace input {})
  if s.error?.isSome then none else
  some (String.Pos.Raw.extract input 0 s.pos)

/-- The non-empty lines of `s` (local helper: only prelude functions, as Lake is also built by stage0). -/
public def nonEmptyLines (s : String) : List String :=
  let (cur, acc) := s.foldl (init := ("", ([] : List String))) fun (cur, acc) c =>
    if c == '\n' then ("", if cur.isEmpty then acc else cur :: acc) else (cur.push c, acc)
  (if cur.isEmpty then acc else cur :: acc).reverse

/-- Number of lines of `s`. -/
public def lineCount (s : String) : Nat :=
  s.foldl (init := 1) fun n c => if c == '\n' then n + 1 else n

/-- Appends one line to `<dir>/events.log` (`load|save <key>`), for diagnostics and measurements. -/
def logEvent (dir : FilePath) (line : String) : BaseIO Unit :=
  discard <| (IO.FS.withFile (dir / "events.log") .append fun h => h.putStrLn line).toBaseIO

def envNat? (var : String) : BaseIO (Option Nat) := do
  return (← IO.getEnv var).bind (·.toNat?)

/-- Whether Lake-managed header snapshots are enabled. -/
public def enabled : BaseIO Bool := do
  match (← IO.getEnv "LAKE_HEADER_SNAPSHOTS") with
  | some v => return !(v == "0" || v == "false" || v == "off" || v == "no")
  | none => return true

def mixStr (h : Hash) (s : String) : Hash :=
  -- length-delimited so that part boundaries matter
  h.mix (Hash.ofString s!"{s.utf8ByteSize}:") |>.mix (Hash.ofString s)

/-- Removes the least used (then least recently used) snapshots until the directory is below `capBytes`. -/
def evict (dir : FilePath) (capBytes : Nat) : IO Unit := do
  let entries ← dir.readDir
  let mut snaps : Array ((Nat × Nat) × FilePath × Nat) := #[] -- ((uses, last use), snapshot, bytes)
  let mut total := 0
  for e in entries do
    if e.path.extension == some "hsnap" && !(e.fileName.endsWith ".tmp.hsnap") then
      let size := (← e.path.metadata).byteSize.toNat +
        ((← (e.path.addExtension "deps").metadata.toBaseIO).toOption.map (·.byteSize.toNat) |>.getD 0)
      let uses := e.path.withExtension "uses"
      let t ← match (← uses.metadata.toBaseIO) with
        | .ok m => pure (m.byteSize.toNat, m.modified.sec.toNat)
        | .error _ => pure (0, 0)
      snaps := snaps.push (t, e.path, size)
      total := total + size
  if total ≤ capBytes then return
  -- least used first, then least recently used: shared/hot headers stay
  let sorted := snaps.qsort (fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2))
  for (_, p, size) in sorted do
    if total ≤ capBytes then break
    removeFileIfExists p
    removeFileIfExists (p.addExtension "deps")
    total := total - size

def saveScript : String :=
  "lean=\"$1\"; src=\"$2\"; setup=\"$3\"; tmp=\"$4\"; fin=\"$5\"; lock=\"$6\"; shift 6\n" ++
  "c=; trap 'rm -f \"$tmp\" \"$tmp.deps\" \"$tmp.out\" \"$lock\"' EXIT\n" ++
  "trap '[ -n \"$c\" ] && kill $c 2>/dev/null; exit 1' TERM INT\n" ++
  "echo $$ >> \"$lock\"\n" ++
  "n=; command -v nice >/dev/null 2>&1 && n='nice -n 19'\n" ++
  -- each lean runs in the background so that a TERM (reaper) stops it at once
  "$n \"$lean\" \"$@\" \"$src\" --setup \"$setup\" --incr-header-save=\"$tmp\" > \"$tmp.out\" 2>&1 & c=$!\n" ++
  "wait $c || exit 0; [ -s \"$tmp.out\" ] && exit 0\n" ++
  "$n \"$lean\" \"$@\" \"$src\" --setup \"$setup\" --incr-load=\"$tmp\" > \"$tmp.out\" 2>&1 & c=$!\n" ++
  "wait $c || exit 0; [ -s \"$tmp.out\" ] && exit 0\n" ++
  "mv -f \"$tmp.deps\" \"$fin.deps\" && mv -f \"$tmp\" \"$fin\"\n"

/-- Stale locks (a save that died) are ignored after this many seconds. -/
def lockTimeout : Nat := 900

/-- What `plan` needs from the module setup (precomputed by callers that cache it). -/
public structure SetupInfo where
  /-- Snapshots are safe with this setup (no dynlibs/plugins, imports from the header). -/
  ok : Bool
  /-- Hash of the setup with the module name normalized. -/
  digest : String
  /-- Writes the setup JSON to the given file (for the background save). -/
  write : FilePath → IO Unit

/-- `SetupInfo` of a module setup. -/
public def SetupInfo.ofSetup (setup : ModuleSetup) : SetupInfo where
  ok := setup.dynlibs.isEmpty && setup.plugins.isEmpty && setup.imports?.isNone
  digest := (Hash.ofString (toJson {setup with name := `_hsnap}).compress).hex
  write f := IO.FS.writeFile f (toJson setup).compress

/--
Decides how a Lean run on `srcText` uses header snapshots stored in `dir`.

* `si`: the module setup that is passed to Lean via `--setup` (see `SetupInfo`).
* `importHash`: the transitive import trace (hashes of every imported artifact).
* `leanArgs`: the Lean arguments other than the source file and `--setup`.
* `env`: the environment of the run (for `LEAN_PATH` and the save process).

Never throws: any problem means "no snapshot".
-/
public def planWith
  (dir : FilePath) (srcText : String) (si : SetupInfo) (importHash : Hash)
  (leanArgs : Array String) (lean : FilePath) (leanGithash : String)
  (env : Array (String × Option String)) (allowSave := true)
: BaseIO Plan := do
  let r ← (go).toBaseIO
  match r with
  | .ok p => return p
  | .error _ => return {}
where
  go : IO Plan := do
    unless (← enabled) do return {}
    if System.Platform.isWindows then return {}
    unless si.ok do return {}
    let some saveArgs := filterArgs leanArgs | return {}
    let some hdr := headerPrefix? srcText | return {}
    let leanMeta ← lean.metadata
    let leanPath := env.findSome? fun (k, v) => if k == "LEAN_PATH" then v else none
    let mut h := Hash.ofString "lake-header-snapshot-v1"
    h := mixStr h leanGithash
    h := mixStr h lean.toString
    h := mixStr h s!"{leanMeta.byteSize}/{leanMeta.modified.sec}/{leanMeta.modified.nsec}"
    h := mixStr h hdr
    h := mixStr h si.digest
    h := mixStr h importHash.hex
    h := mixStr h (String.intercalate "\x00" saveArgs.toList)
    h := mixStr h (leanPath.getD "")
    -- a second, independent 64-bit hash to make accidental collisions negligible
    let h2 := Hash.ofString s!"{h.hex}|{hdr}|{importHash.hex}|{leanGithash}"
    let key := h.hex ++ h2.hex
    let snap := dir / s!"{key}.hsnap"
    let uses := dir / s!"{key}.uses"
    IO.FS.createDirAll dir
    -- record the use (the mtime of `.uses` is the LRU clock; its size counts uses)
    let prevUses := (← uses.metadata.toBaseIO).toOption.map (·.byteSize.toNat) |>.getD 0
    IO.FS.withFile uses .append fun h => h.putStr "."
    if (← snap.pathExists) && (← (snap.addExtension "deps").pathExists) then
      logEvent dir s!"load {key}"
      return {loadArgs := #[s!"--incr-load={snap}"]}
    unless allowSave do return {}
    let minUses := (← envNat? "LAKE_HEADER_SNAPSHOT_MIN_USES").getD 2
    if prevUses + 1 < minUses then return {}
    -- the wall clock, read as the mtime of a fresh file (same clock as the locks' mtimes)
    let probe := dir / s!"{key}.probe"
    IO.FS.writeFile probe ""
    let nowWall := (← probe.metadata).modified.sec.toNat
    removeFileIfExists probe
    -- live save locks; a lock older than `lockTimeout` belongs to a save that died: drop it
    let mut running := 0
    for e in (← dir.readDir) do
      if e.path.extension == some "lock" then
        match (← e.path.metadata.toBaseIO) with
        | .ok m =>
          if nowWall < m.modified.sec.toNat + lockTimeout then
            running := running + 1
          else
            removeFileIfExists e.path
        | .error _ => pure ()
    -- bound the number of concurrent saves (each one imports the header once more)
    let maxSaves := (← envNat? "LAKE_HEADER_SNAPSHOT_MAX_SAVES").getD 2
    if running ≥ maxSaves then return {}
    -- take the save lock (fails if another process is saving this key)
    let lock := dir / s!"{key}.lock"
    let pid ← IO.Process.getPID
    let ok ← (do IO.FS.withFile lock .writeNew fun h => h.putStrLn (toString pid); pure true).catchExceptions
      fun _ => pure false
    unless ok do return {}
    let capMb := (← envNat? "LAKE_HEADER_SNAPSHOT_MAX_MB").getD 8192
    try evict dir (capMb * 1024 * 1024) catch _ => pure ()
    let src := dir / s!"{key}.lean"
    let setupFile := dir / s!"{key}.setup.json"
    IO.FS.writeFile src hdr
    si.write setupFile
    let tmp := dir / s!"{key}.tmp.hsnap"
    logEvent dir s!"save {key}"
    return {
      save? := some {
        cmd := "/bin/sh"
        args := #["-c", saveScript, "lake-header-snapshot", lean.toString, src.toString,
          setupFile.toString, tmp.toString, snap.toString, lock.toString] ++ saveArgs
        env
        stdin := .null, stdout := .null, stderr := .null
      }
    }

/-- `planWith` for a module setup. -/
public def plan
  (dir : FilePath) (srcText : String) (setup : ModuleSetup) (importHash : Hash)
  (leanArgs : Array String) (lean : FilePath) (leanGithash : String)
  (env : Array (String × Option String)) (allowSave := true)
: BaseIO Plan :=
  planWith dir srcText (.ofSetup setup) importHash leanArgs lean leanGithash env allowSave

/-- Starts the planned background save (if any) without waiting for it. -/
public def Plan.startSave (p : Plan) : BaseIO Unit := do
  if let some args := p.save? then
    discard <| (IO.Process.spawn args).toBaseIO

/--
Stops the background saves this process started in `dir` (their locks start with our pid), e.g.
at the end of `lake build`, so that no save outlives the build. Disabled by
`LAKE_HEADER_SNAPSHOT_REAP=0`.
-/
public def reap (dir : FilePath) : BaseIO Unit := do
  if let some v ← IO.getEnv "LAKE_HEADER_SNAPSHOT_REAP" then
    if v == "0" then return
  let r ← (show IO Unit from do
    unless (← dir.pathExists) do return
    let pid := toString (← IO.Process.getPID)
    for e in (← dir.readDir) do
      if e.path.extension == some "lock" then
        let lines := nonEmptyLines (← IO.FS.readFile e.path)
        if lines.head? == some pid then
          if let some shPid := lines[1]? then
            discard <| IO.Process.output {cmd := "kill", args := #["-TERM", shPid]}
  ).toBaseIO
  discard <| pure r

end Lake.HeaderSnapshot
