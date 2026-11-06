/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone, Siddharth Bhat
-/
module

prelude
public import Lake.Util.Log
import Lake.Util.Proc
import Lake.Util.FilePath
import Lake.Util.IO
import Lake.Util.Url
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.System.Platform
import Lean.CoreM
import Lean.Compiler.Options

/-! # Common Build Actions
Low level actions to build common Lean artifacts via the Lean toolchain.
-/

open System
open Lean hiding SearchPath

namespace Lake

public def compileLeanIR
  (setupFile irFile cFile : FilePath)
  (leanPath : SearchPath := [])
  (leanir : FilePath := "leanir")
: LogIO Unit := do
  createParentDirs irFile
  createParentDirs cFile
  proc {
    cmd := leanir.toString
    args := #[setupFile.toString, irFile.toString, cFile.toString]
    env := #[("LEAN_PATH", leanPath.toString)]
  }

/--
The compact JSON of one `importArts` entry of a module setup (`"<module>":<artifacts>`) per
module, with the artifacts it was rendered from. Every module of a build lists (mostly) the
same transitive imports, so the entries are rendered once instead of once per module.
-/
builtin_initialize setupImportArtsJsonCache : IO.Ref (NameMap (ImportArtifacts × String)) ←
  IO.mkRef {}

/--
Renders `setup` as compact JSON with the same value as `(toJson setup).compress` (the
`importArts` object lists the same entries, in name order), reusing the cached rendering of
each `importArts` entry.
-/
def renderModuleSetup (setup : ModuleSetup) : IO String := do
  let .obj fields := toJson {setup with importArts := {}}
    | return (toJson setup).compress
  let cache ← setupImportArtsJsonCache.get
  let mut fresh : Array (Name × ImportArtifacts × String) := #[]
  let mut arts := "{"
  let mut first := true
  for (n, a) in setup.importArts do
    let mut frag := ""
    if let some (cached, f) := cache.find? n then
      if cached.toArrays == a.toArrays then frag := f
    if frag.isEmpty then
      frag := (Json.str n.toString).compress ++ ":" ++ (toJson a).compress
      fresh := fresh.push (n, a, frag)
    unless first do arts := arts.push ','
    arts := arts ++ frag
    first := false
  arts := arts.push '}'
  unless fresh.isEmpty do
    setupImportArtsJsonCache.modify fun c => fresh.foldl (init := c) fun c (n, a, frag) =>
      c.insert n (a, frag)
  let mut out := "{"
  first := true
  for (k, v) in fields do
    unless first do out := out.push ','
    first := false
    out := out ++ (Json.str k).compress ++ ":" ++ (if k == "importArts" then arts else v.compress)
  return out.push '}'
/-! ## Per-module part packs (optional artefact; see `lean_compacted_region_read` in src/library/module.cpp)
A module's `.olean`/`.olean.server`/`.olean.private` (and its `.ir.sig`/`.ir`) are saved at consecutive 64 KiB-aligned base
addresses. The pack `<stem>.olean.pack` (`<stem>.ir.pack`) stores the unchanged bytes of each part at offset
`4096 + (part base - lowest base)` behind a 4 KiB header, so `lean` maps all parts of a family with one `mmap` at their own
addresses. Packs are an optimisation only: `lean` ignores a missing pack and serves a part from a pack only while the part's
size and mtime match the pack entry. `LAKE_OLEAN_PACK=0` turns writing off. -/

def packU64At (b : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [0:8] do
    v := v ||| ((b.get! (off + i)).toUInt64 <<< (8 * i).toUInt64)
  return v

def packPushU32 (b : ByteArray) (v : UInt32) : ByteArray := Id.run do
  let mut b := b
  for i in [0:4] do
    b := b.push (v >>> (8 * i).toUInt32).toUInt8
  return b

def packPushU64 (b : ByteArray) (v : UInt64) : ByteArray := Id.run do
  let mut b := b
  for i in [0:8] do
    b := b.push (v >>> (8 * i).toUInt64).toUInt8
  return b

def packPushZeros (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut b := b
  for _ in [0:n] do
    b := b.push 0
  return b

/-- Writes the pack of one part family (`fam` = `".olean"` or `".ir"`) of the module whose part files are `stem ++ suffix`. -/
def writePartPack (stem fam : String) (suffixes : Array String) : IO Unit := do
  let mut parts : Array (String × UInt64 × ByteArray × IO.FS.SystemTime) := #[]
  for suf in suffixes do
    let f : FilePath := stem ++ suf
    unless (← f.pathExists) do continue
    let md ← f.metadata
    let bytes ← IO.FS.readBinFile f
    -- `olean` marker and a header that holds the base address
    if bytes.size < 88 || bytes.size.toUInt64 != md.byteSize || bytes.extract 0 5 != "olean".toUTF8 then return
    parts := parts.push (suf, packU64At bytes 80, bytes, md.modified)
  if parts.isEmpty || parts.size > 8 then return
  -- bubble sort by base address (at most 3 parts)
  let mut sorted := parts
  for _ in [0:sorted.size] do
    for j in [1:sorted.size] do
      if sorted[j-1]!.2.1 > sorted[j]!.2.1 then
        sorted := sorted.swapIfInBounds (j-1) j
  let groupBase := sorted[0]!.2.1
  if groupBase % 4096 != 0 then return
  let mut endAddr := groupBase
  let mut total := 0
  for (_, base, bytes, _) in sorted do
    if base < endAddr then return
    endAddr := base + bytes.size.toUInt64
    total := total + bytes.size
  let dataSize := endAddr - groupBase
  -- the parts of one family are adjacent (64 KiB slots); anything else is not worth a pack
  if dataSize.toNat > total + sorted.size * 65536 then return
  let mut out := "leanpak1".toUTF8
  out := packPushU32 out sorted.size.toUInt32
  out := packPushU32 out 0
  out := packPushU64 out groupBase
  out := packPushU64 out 4096
  out := packPushU64 out dataSize
  for (suf, base, bytes, mtime) in sorted do
    let s := suf.toUTF8
    if s.size ≥ 16 then return
    out := packPushZeros (out ++ s) (16 - s.size)
    out := packPushU64 out base
    out := packPushU64 out bytes.size.toUInt64
    out := packPushU64 out mtime.sec.toNat.toUInt64
    out := packPushU64 out mtime.nsec.toUInt64
  out := packPushZeros out (4096 - out.size)
  let mut addr := groupBase
  for (_, base, bytes, _) in sorted do
    out := packPushZeros out (base - addr).toNat
    out := out ++ bytes
    addr := base + bytes.size.toUInt64
  let pack : FilePath := stem ++ fam ++ ".pack"
  let tmp : FilePath := pack.toString ++ ".tmp"
  IO.FS.writeBinFile tmp out
  IO.FS.rename tmp pack

/-- Writes `<stem>.olean.pack` and `<stem>.ir.pack` next to a freshly compiled module's parts (errors are ignored: the packs
are optional). -/
public def writeModulePartPacks (oleanFile : FilePath) : BaseIO Unit := do
  let go : IO Unit := do
    if (← IO.getEnv "LAKE_OLEAN_PACK") == some "0" then return
    unless oleanFile.extension == some "olean" do return
    let stem := (oleanFile.withExtension "").toString
    writePartPack stem ".olean" #[".olean", ".olean.server", ".olean.private"]
    writePartPack stem ".ir" #[".ir.sig", ".ir"]
  let _ ← go.toBaseIO

/-- The `lean` command line for building a module (the setup file is written separately). -/
def leanModuleArgs
  (leanFile : FilePath) (setup : ModuleSetup) (setupFile : FilePath) (arts : ModuleArtifacts)
  (leanArgs : Array String)
: IO (Array String) := do
  let mut args := leanArgs.push leanFile.toString
  if let some oleanFile := arts.olean? then
    createParentDirs oleanFile
    args := args ++ #["-o", oleanFile.toString]
  if let some ileanFile := arts.ilean? then
    createParentDirs ileanFile
    args := args ++ #["-i", ileanFile.toString]
  let opts := setup.options.toOptions
  let postponeCompile := setup.isModule && Compiler.compiler.postponeCompile.get opts
  if !postponeCompile then
    if let some cFile := arts.c? then
      createParentDirs cFile
      args := args ++ #["-c", cFile.toString]
  if let some bcFile := arts.bc? then
    createParentDirs bcFile
    args := args ++ #["-b", bcFile.toString]
  createParentDirs setupFile
  args := args ++ #["--setup", setupFile.toString]
  return args.push "--json"

/--
A `lean` started before the last of its module's imports were built (`LAKE_PRESTART=1`, see
`Module.maybePrestart`). It was given a setup without the late imports' `importArts` entries and
receives them on stdin (one JSON line per import) when they are built.
-/
public structure PrestartedLean where
  args : Array String
  /-- The setup it was started with (without the late imports' entries). -/
  setup : ModuleSetup
  /-- The late imports' entries, once all of them were sent. -/
  lateArts : Task (Except IO.Error (Array (Name × ImportArtifacts)))
  /-- Its stdout, stderr and exit code, once it exits. -/
  output : Task (Except IO.Error IO.Process.Output)
  kill : IO Unit

public inductive PrestartState where
  /-- The module's `lean` was (or is being) started the normal way: never pre-start it. -/
  | stock
  | pre (p : PrestartedLean)

/-- Pre-start state per module source file (`Name.mkSimple leanFile.toString`). -/
builtin_initialize prestartRef : IO.Ref (NameMap PrestartState) ← IO.mkRef {}

def prestartKey (leanFile : FilePath) : Name := .mkSimple leanFile.toString

def prestartSetupFile (setupFile : FilePath) : FilePath := setupFile.addExtension "prestart"

/-- Marks the module as started the normal way and returns its pre-started `lean`, if any. -/
public def takePrestarted? (leanFile : FilePath) : BaseIO (Option PrestartedLean) :=
  prestartRef.modifyGet fun m =>
    let k := prestartKey leanFile
    match m.find? k with
    | some (.pre p) => (some p, m.insert k .stock)
    | _ => (none, m.insert k .stock)

/-- Kills a pre-started `lean` of the module that was not adopted (e.g. the module is up-to-date). -/
public def killPrestarted (leanFile : FilePath) : BaseIO Unit := do
  if let some p ← takePrestarted? leanFile then
    discard <| p.kill.toBaseIO

/-- The number of pre-started `lean`s not yet adopted or killed. -/
public def prestartedCount : BaseIO Nat := do
  return (← prestartRef.get).foldl (init := 0) fun n _ s => match s with | .pre _ => n + 1 | _ => n

/--
Starts `lean` for a module whose imports `late` are not built yet (see `PrestartedLean`). Does
nothing (returns `false`) if the module was already started the normal way.
-/
public def prestartLeanModule
  (leanFile : FilePath) (setup : ModuleSetup) (setupFile : FilePath) (arts : ModuleArtifacts)
  (leanArgs : Array String) (leanPath : SearchPath) (lean : FilePath)
  (late : Array (Name × Task (Except IO.Error ImportArtifacts)))
: IO Bool := do
  if let some .stock := (← prestartRef.get).find? (prestartKey leanFile) then return false
  -- A separate setup file: the module may still be started the normal way concurrently.
  let args ← leanModuleArgs leanFile setup (prestartSetupFile setupFile) arts leanArgs
  IO.FS.writeFile (prestartSetupFile setupFile) (← renderModuleSetup setup)
  let child ← IO.Process.spawn {
    args, cmd := lean.toString
    env := #[("LEAN_PATH", leanPath.toString), ("LEAN_PRESTART_STDIN", "1")]
    stdin := .piped, stdout := .piped, stderr := .piped
  }
  let (stdin, child) ← child.takeStdin
  let pending := Json.arr (late.map fun (n, _) => toJson n)
  stdin.putStrLn (Json.mkObj [("pending", pending)]).compress
  stdin.flush
  let lateArts ← IO.asTask (prio := .dedicated) do
    let mut out := #[]
    for (n, t) in late do
      match t.get with
      | .ok a =>
        stdin.putStrLn (Json.mkObj [("ready", toJson n), ("arts", toJson a)]).compress
        stdin.flush
        out := out.push (n, a)
      | .error e =>
        stdin.putStrLn (Json.mkObj [("abort", true)]).compress
        stdin.flush
        throw e
    return out
  let output ← IO.asTask (prio := .dedicated) do
    let stderr ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
    let stdout ← child.stdout.readToEnd
    let exitCode ← child.wait
    let stderr ← IO.ofExcept stderr.get
    return {exitCode, stdout, stderr : IO.Process.Output}
  let p : PrestartedLean := {args, setup, lateArts, output, kill := child.kill}
  let ok ← prestartRef.modifyGet fun m =>
    let k := prestartKey leanFile
    match m.find? k with
    | some .stock => (false, m)
    | _ => (true, m.insert k (.pre p))
  unless ok do discard <| child.kill.toBaseIO
  return ok

public def prestartEnabled : BaseIO Bool := do
  return (← IO.getEnv "LAKE_PRESTART") == some "1"

/-- The number of module `lean`s started the normal way that are still running. -/
builtin_initialize runningLeansRef : IO.Ref Nat ← IO.mkRef 0

/--
Whether another `lean` may be pre-started now: pre-started plus running module `lean`s stay below
the job slots (`LAKE_PRESTART_MAX` if set, else `LEAN_NUM_THREADS`, else 16), so
pre-starting never oversubscribes the schedule.
-/
public def prestartSlotFree : BaseIO Bool := do
  let slots ← match (← IO.getEnv "LAKE_PRESTART_MAX").bind (·.toNat?) with
    | some n => pure n
    | none => match (← IO.getEnv "LEAN_NUM_THREADS").bind (·.toNat?) with
      | some n => pure n
      | none => pure 16
  return (← prestartedCount) + (← runningLeansRef.get) < slots

/-- Whether two setups are equal (`importArts` compared entry by entry). -/
def sameSetup (a b : ModuleSetup) : Bool := Id.run do
  let rest (s : ModuleSetup) := (toJson {s with importArts := {}}).compress
  if rest a != rest b then return false
  if Std.TreeMap.size a.importArts != Std.TreeMap.size b.importArts then return false
  for (n, x) in a.importArts do
    let some y := b.importArts.find? n | return false
    unless x.toArrays == y.toArrays do return false
  return true

/-- The output of a `lean` started by `compileLeanModule` or adopted from `prestartLeanModule`. -/
def runLeanModule
  (leanFile : FilePath) (setup : ModuleSetup) (setupFile : FilePath) (args : Array String)
  (leanPath : SearchPath) (lean : FilePath)
: LogIO IO.Process.Output := do
  if (← prestartEnabled) then
    if let some p ← takePrestarted? leanFile then
      let adopted? ← id do
        let pre := (prestartSetupFile setupFile).toString
        unless p.args.map (fun a => if a == pre then setupFile.toString else a) == args do return none
        let .ok late := (← IO.wait p.lateArts) | return none
        let full := late.foldl (init := p.setup) fun s (n, a) =>
          {s with importArts := s.importArts.insert n a}
        unless sameSetup full setup do return none
        let write ← IO.asTask (prio := .dedicated) do
          IO.FS.writeFile setupFile (← renderModuleSetup setup)
        runningLeansRef.modify (· + 1)
        let out? := (← IO.wait p.output).toOption
        runningLeansRef.modify (· - 1)
        discard <| IO.ofExcept (← IO.wait write)
        return out?
      if let some out := adopted? then
        logVerbose s!"adopted the pre-started lean for {leanFile}"
        return out
      discard <| p.kill.toBaseIO
      discard <| IO.wait p.output
  IO.FS.writeFile setupFile (← renderModuleSetup setup)
  let track ← prestartEnabled
  if track then runningLeansRef.modify (· + 1)
  try
    rawProc {
      args
      cmd := lean.toString
      env := #[
        ("LEAN_PATH", leanPath.toString)
      ]
    }
  finally
    if track then runningLeansRef.modify (· - 1)

public def compileLeanModule
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
: LogIO Unit := do
  let args ← leanModuleArgs leanFile setup setupFile arts leanArgs
  withLogErrorPos do
  let out ← runLeanModule leanFile setup setupFile args leanPath lean
  let outLogPos ← getLogPos
  unless out.stdout.isEmpty do
    let txt ← out.stdout.split '\n' |>.foldM (init := "") fun (txt : String) ln => do
      let ln := ln.copy
      if let .ok (msg : SerialMessage) := Json.parse ln >>= fromJson? then
        unless txt.isEmpty do
          logInfo s!"stdout:\n{txt}"
        let msg := {msg with fileName := mkRelPathString relLeanFile}
        logSerialMessage msg
        return txt
      else if txt.isEmpty && ln.isEmpty then
        return txt
      else
        return txt ++ ln ++ "\n"
    unless txt.isEmpty do
      logInfo s!"stdout:\n{txt}"
  unless out.stderr.isEmpty do
    logInfo s!"stderr:\n{out.stderr.trimAscii}"
  -- Elide the generic "Lean exited with code 1" when Lean already
  -- reported errors (the usual compiler-failure case). Keep it for other
  -- nonzero codes, for code 1 without diagnostics, and for the anomalous
  -- case where Lean logs errors but exits successfully.
  -- See https://github.com/leanprover/lean4/issues/10825
  let hasErrors := (← getLog).takeFrom outLogPos |>.any (·.level matches .error)
  if out.exitCode = 1 && hasErrors then
    failure
  else if out.exitCode ≠ 0 || hasErrors then
    error s!"Lean exited with code {out.exitCode}"
  else if let some oleanFile := arts.olean? then
    writeModulePartPacks oleanFile

public def compileO
  (oFile srcFile : FilePath)
  (moreArgs : Array String := #[]) (compiler : FilePath := "cc")
: LogIO Unit := do
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs
  }

public def mkArgs (basePath : FilePath) (args : Array String) : LogIO (Array String) := do
  -- Use response file to avoid potentially exceeding CLI length limits.
  -- On Windows this is always needed; on macOS/Linux this is needed for large
  -- projects like Mathlib where the number of object files exceeds ARG_MAX.
  let rspFile := basePath.addExtension "rsp"
  let h ← IO.FS.Handle.mk rspFile .write
  args.forM fun arg =>
    -- Escape special characters
    let arg := arg.foldl (init := "") fun s c =>
      if c == '\\' || c == '"' then
        s.push '\\' |>.push c
      else
        s.push c
    h.putStr s!"\"{arg}\"\n"
  return #[s!"@{rspFile}"]

public def compileStaticLib
  (libFile : FilePath) (oFiles : Array FilePath)
  (ar : FilePath := "ar") (thin := false)
: LogIO Unit := do
  createParentDirs libFile
  -- `ar rcs` does not remove old files from the archive, so it must be deleted first
  removeFileIfExists libFile
  let args := #["rcs"]
  let args := if thin then args.push "--thin" else args
  let args := args.push libFile.toString ++ (← mkArgs libFile <| oFiles.map toString)
  proc {cmd := ar.toString, args}

public def compileSharedLib
  (libFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc") (macosxDeploymentTarget? : Option String := none)
: LogIO Unit := do
  createParentDirs libFile
  proc {
    cmd := linker.toString
    args := #["-shared", "-o", libFile.toString] ++ (← mkArgs libFile linkArgs)
    -- See `BuildConfig.macosxDeploymentTarget?` for details
    env := macosxDeploymentTarget?.elim #[] fun ver => #[("MACOSX_DEPLOYMENT_TARGET", some ver)]
  }

public def compileExe
  (binFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc") (macosxDeploymentTarget? : Option String := none)
: LogIO Unit := do
  createParentDirs binFile
  proc {
    cmd := linker.toString
    args := #["-o", binFile.toString] ++ (← mkArgs binFile linkArgs)
    -- See `BuildConfig.macosxDeploymentTarget?` for details
    env :=  macosxDeploymentTarget?.elim #[] fun ver => #[("MACOSX_DEPLOYMENT_TARGET", some ver)]
  }

/-- Download a file using `curl`, clobbering any existing file. -/
public def download
  (url : String) (file : FilePath) (headers : Array String := #[])
: LogIO PUnit := do
  if (← file.pathExists) then
    IO.FS.removeFile file
  else
    createParentDirs file
  let args := #["-s", "-S", "-f", "-o", file.toString, "-L", url]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  proc (quiet := true) {cmd := ← Internal.getCurl, args}

/-- Unpack an archive `file` using `tar` into the directory `dir`. -/
public def untar (file : FilePath) (dir : FilePath) (gzip := true) : LogIO PUnit := do
  IO.FS.createDirAll dir
  let mut opts := "-xvv"
  if gzip then
    opts := opts.push 'z'
  proc (quiet := true) {
    cmd := "tar",
    args := #[opts, "-f", file.toString, "-C", dir.toString]
  }

/-- Pack a directory `dir` using `tar` into the archive `file`. -/
public def tar
  (dir : FilePath) (file : FilePath)
  (gzip := true) (excludePaths : Array FilePath := #[])
: LogIO PUnit := do
  createParentDirs file
  let mut args := #["-cvv"]
  if gzip then
    args := args.push "-z"
  for path in excludePaths do
    args := args.push s!"--exclude={path}"
  proc (quiet := true) {
    cmd := "tar"
    args := args ++ #["-f", file.toString, "-C", dir.toString, "."]
    -- don't pack `._` files on MacOS
    env := if Platform.isOSX then #[("COPYFILE_DISABLE", "true")] else #[]
  }
