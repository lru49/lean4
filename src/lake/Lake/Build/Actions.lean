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

/-!
lean-perf (DG): warm `lean` processes (Linux only; `LAKE_WARM_LEAN=<n>` spare processes, default 2, `0` = off).

A module's `lean` process spends its first ~0.3 s on process start-up, builtin initialization and reading (mapping)
the `.olean`/`.ir` parts of every module it imports, before it can do anything that depends on its own imports. With
`n` > 0, every time Lake starts compiling a module it also starts one spare `lean` process
(`LEAN_WARM_START`, see `lean_warm_start` in src/util/shell.cpp) that immediately reads the parts of that module's
transitive imports (this module's `importArts`) and then waits; the next module compile takes the most recently
started spare process (LIFO) and sends it its command line, working directory and `LEAN_PATH` instead of spawning a
new process. In a chain of modules the most recently started compile is the predecessor whose `.olean` the next module
waits for, and its import closure is the next module's import closure minus the predecessor itself, so the next
module finds almost all of its parts already read. The warm process reuses a part only if the file is unchanged
(device, inode, size, mtime) and reads everything else itself, so the outputs are those of a plain `lean` run.
At most `n` spare processes are kept (the oldest is killed); spare processes exit when Lake exits (end of stdin).
-/

abbrev WarmChild := IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }

builtin_initialize warmPool : IO.Ref (Array (IO.FS.Handle × WarmChild)) ← IO.mkRef #[]

def warmPoolSize : BaseIO Nat := do
  if System.Platform.isWindows || System.Platform.isOSX || System.Platform.isEmscripten then return 0
  return ((← IO.getEnv "LAKE_WARM_LEAN").bind (·.toNat?)).getD 2

/-- Starts a spare `lean` that reads the parts of `setup.importArts` (one line per part chain) and waits. -/
def spawnWarmLean (lean : FilePath) (setup : ModuleSetup) (listFile : FilePath) (n : Nat) : IO Unit := do
  let mut txt := ""
  for (_, arts) in setup.importArts do
    let o := arts.oleanParts (inServer := true)
    unless o.isEmpty do txt := txt ++ "\t".intercalate (o.toList.map (·.toString)) ++ "\n"
    let ir := arts.irParts
    unless ir.isEmpty do txt := txt ++ "\t".intercalate (ir.toList.map (·.toString)) ++ "\n"
  IO.FS.writeFile listFile txt
  let child ← IO.Process.spawn {
    cmd := lean.toString, args := #[], env := #[("LEAN_WARM_START", listFile.toString)]
    stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  let old ← warmPool.modifyGet fun pool =>
    let pool := pool.push (stdin, child)
    if pool.size > n then (pool[0]?, pool.extract 1 pool.size) else (none, pool)
  if let some (_, c) := old then
    c.kill
    discard <| IO.asTask (prio := .dedicated) c.wait

/-- Takes the most recently started spare process (if any), starts a new spare process for this module's imports,
then runs this compile on the taken process. `none`: no spare process was available or it did not take the request
(the caller then spawns `lean` as usual). -/
def runOnWarmLean (lean : FilePath) (setup : ModuleSetup) (setupFile : FilePath) (n : Nat)
    (args : Array String) (leanPath : String) : IO (Option IO.Process.Output) := do
  let taken? ← if args.any (·.contains '\n') || leanPath.contains '\n' then pure none
    else warmPool.modifyGet fun pool => (pool.back?, pool.pop)
  try spawnWarmLean lean setup (setupFile.withExtension "warm") n catch _ => pure ()
  let some (stdin, child) := taken? | return none
  let cwd ← IO.currentDir
  let req := s!"C {cwd}\nE LEAN_PATH={leanPath}\n" ++ String.join (args.toList.map (s!"A {·}\n")) ++ "R\n"
  try
    stdin.putStr req
    stdin.flush
  catch _ =>
    child.kill
    discard <| IO.asTask (prio := .dedicated) child.wait
    return none
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  return some { exitCode, stdout, stderr }

public def compileLeanModule
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
: LogIO Unit := do
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
  IO.FS.writeFile setupFile (toJson setup).pretty
  args := args ++ #["--setup", setupFile.toString]
  args := args.push "--json"
  withLogErrorPos do
  let spawnArgs : IO.Process.SpawnArgs := {
    args
    cmd := lean.toString
    env := #[
      ("LEAN_PATH", leanPath.toString)
    ]
  }
  let warmN ← warmPoolSize
  let warmOut? ← if warmN > 0 then
      match (← (runOnWarmLean lean setup setupFile warmN args leanPath.toString).toBaseIO) with
      | .ok out? => pure out?
      | .error _ => pure none
    else pure none
  let out ← match warmOut? with
    | some out => do logVerbose (mkCmdLog spawnArgs); pure out
    | none => rawProc spawnArgs
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
