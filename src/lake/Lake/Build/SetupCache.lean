/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Config.Workspace
public import Lake.Build.Trace
public import Lake.Build.HeaderSnapshot
public import Lean.Setup
import Lake.Util.IO
import Lean.Elab.ParseImportsFast

/-! # `lake lean` setup cache

`lake lean <file>` normally runs a build of the file's import closure before starting Lean: for a
file on top of Mathlib that means reading ~9 k trace files (with their stored logs), ~50 k hash
files and replaying the logs, which costs seconds per invocation although nothing needs to be
built. Agents that elaborate one file after another pay this every time.

After a successful preparation, Lake records the computed module setup together with a stamp
(size, mtime) of every file the result depends on: each imported artifact, the source of every
imported workspace module, the dynlibs/plugins, every package's configuration file and manifest,
and the `lean` binary. The next `lake lean` of a file with the same module identity, the same
imports and the same extra arguments re-stats these files (one `stat` per entry) and, if nothing
changed, starts Lean directly with the recorded setup. Any difference falls back to the normal
build (which then rewrites the entry). The fast path skips replaying the closure's stored logs.

`LAKE_LEAN_FAST=0` disables it. Entries live in `<root buildDir>/lean-setup/`.
-/

open System Lean

namespace Lake.SetupCache

/-- Whether the `lake lean` setup cache is enabled. -/
public def enabled : BaseIO Bool := do
  match (← IO.getEnv "LAKE_LEAN_FAST") with
  | some v => return !(v == "0" || v == "false" || v == "off" || v == "no")
  | none => return true

def stamp (p : FilePath) : BaseIO String := do
  match (← p.metadata.toBaseIO) with
  | .ok m => return s!"{m.byteSize}/{m.modified.sec}/{m.modified.nsec}"
  | .error _ => return "-"

def mixStr (h : Hash) (s : String) : Hash :=
  h.mix (Hash.ofString s!"{s.utf8ByteSize}:") |>.mix (Hash.ofString s)

/-- `args` without output flags and their values (outputs do not change the setup). -/
def dropOutputArgs (args : Array String) : Array String := Id.run do
  let flags := ["-o", "-i", "-c", "-b", "--olean", "--ilean", "--c", "--bc"]
  let mut out := #[]
  let mut skip := false
  for a in args do
    if skip then skip := false
    else if flags.contains a then skip := true
    else if flags.any (fun f => f.startsWith "--" && a.startsWith (f ++ "=")) then pure ()
    else out := out.push a
  return out

/-- The cache key of `lake lean <file> -- <moreArgs>`. -/
public def key (ws : Workspace) (modName : Name) (header : ModuleHeader) (moreArgs : Array String) : String :=
  let parts := #["lake-lean-setup-v1", modName.toString, (toJson header).compress,
    String.intercalate "\x00" (dropOutputArgs moreArgs).toList, ws.lakeEnv.lean.lean.toString,
    ws.lakeEnv.lean.githash, ws.root.dir.toString]
  let h := parts.foldl mixStr Hash.nil
  let h2 := Hash.ofString (String.intercalate "|" parts.toList ++ h.hex)
  h.hex ++ h2.hex

/-- The cache directory of a workspace. -/
public def dir (ws : Workspace) : FilePath :=
  ws.root.buildDir / "lean-setup"

/-- A recorded preparation. -/
public structure Entry where
  setupFile : FilePath
  cfgArgs : Array String
  importHash : String
  headersDir : FilePath
  setupOk : Bool
  setupDigest : String
  checks : Array (String × String)
  deriving ToJson, FromJson

/--
Records the preparation of a `lake lean` run. Never throws.
-/
public def write (ws : Workspace) (key : String) (setup : ModuleSetup) (cfgArgs : Array String)
    (importHash : Hash) (headersDir : FilePath) : BaseIO Unit := do
  discard <| (go).toBaseIO
where
  go : IO Unit := do
    unless (← enabled) do return
    let mut paths : Array FilePath := #[ws.lakeEnv.lean.lean]
    for pkg in ws.packages do
      paths := paths.push pkg.configFile |>.push pkg.manifestFile
    for (n, arts) in setup.importArts.toList do
      for a in arts.toArrays do
        for p in a do paths := paths.push p
      if let some m := ws.findModule? n then
        paths := paths.push m.leanFile
    paths := paths ++ setup.dynlibs ++ setup.plugins.map (·.path)
    let checks ← paths.mapM fun p => return (p.toString, ← stamp p)
    let d := dir ws
    IO.FS.createDirAll d
    let pid ← IO.Process.getPID
    let setupFile := d / s!"{key}.setup.json"
    let si := HeaderSnapshot.SetupInfo.ofSetup setup
    IO.FS.writeFile (d / s!"{key}.setup.json.{pid}") (toJson setup).compress
    IO.FS.rename (d / s!"{key}.setup.json.{pid}") setupFile
    let e : Entry := {
      setupFile, cfgArgs, importHash := importHash.hex, headersDir
      setupOk := si.ok, setupDigest := si.digest, checks }
    IO.FS.writeFile (d / s!"{key}.json.{pid}") (toJson e).compress
    IO.FS.rename (d / s!"{key}.json.{pid}") (d / s!"{key}.json")

/--
The spawn arguments of `lake lean <leanFile> -- <moreArgs>` from a valid recorded preparation, or
`none` (then the caller runs the normal preparation).
-/
public def tryFast (ws : Workspace) (leanFile : FilePath) (moreArgs : Array String) :
    BaseIO (Option IO.Process.SpawnArgs) := do
  match (← (go).toBaseIO) with
  | .ok r => return r
  | .error _ => return none
where
  go : IO (Option IO.Process.SpawnArgs) := do
    unless (← enabled) do return none
    let some path ← resolvePath? leanFile | return none
    let src ← IO.FS.readFile path
    let header ← Lean.parseImports' src leanFile.toString
    let modName := (ws.findModuleBySrc? path).map (·.name) |>.getD .anonymous
    let k := key ws modName header moreArgs
    let entryFile := dir ws / s!"{k}.json"
    unless (← entryFile.pathExists) do return none
    let some e := (Json.parse (← IO.FS.readFile entryFile) >>= fromJson? : Except String Entry).toOption
      | return none
    for (p, s) in e.checks do
      if (← stamp p) != s then return none
    unless (← e.setupFile.pathExists) do return none
    let env := ws.augmentedEnvVars
    let lean := ws.lakeEnv.lean.lean
    let si : HeaderSnapshot.SetupInfo := {
      ok := e.setupOk, digest := e.setupDigest
      write := fun f => do IO.FS.writeFile f (← IO.FS.readFile e.setupFile) }
    let hsnap ← HeaderSnapshot.planWith e.headersDir src si (Hash.ofHex e.importHash)
      (e.cfgArgs ++ moreArgs) lean ws.lakeEnv.lean.githash env
    hsnap.startSave
    return some {
      cmd := lean.toString
      args := e.cfgArgs.push path.toString ++ #["--setup", e.setupFile.toString] ++ moreArgs ++ hsnap.loadArgs
      env
    }

end Lake.SetupCache
