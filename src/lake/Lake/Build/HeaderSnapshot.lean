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
* Otherwise, once a key has been used `minUses` times (default 2), a background, niced process
  saves the snapshot from an *import-only copy* of the header (never from the full module) into
  `<buildDir>/headers/<key>.hsnap`, checks that it loads, and publishes it atomically. The run
  that triggers the save is not delayed.
* Snapshots whose header produced any message are never published (the messages would carry the
  import-only file's name); modules with plugins or dynlibs never use snapshots (the setup's
  dynlibs are loaded during header processing, which a loaded snapshot skips).
* The directory is capped (default 8 GiB, LRU by last use) and at most 2 saves run at a time
  (a key that finds no free slot is saved by a later use).

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

/-- Appends one line to `<dir>/events.log` (`load|save <key>`), for diagnostics and measurements. -/
def logEvent (dir : FilePath) (line : String) : BaseIO Unit :=
  discard <| (IO.FS.withFile (dir / "events.log") .append fun h => h.putStrLn line).toBaseIO

def envNat? (var : String) : BaseIO (Option Nat) := do
  return (← IO.getEnv var).bind (·.trimAscii.toString.toNat?)

/-- Whether Lake-managed header snapshots are enabled. -/
public def enabled : BaseIO Bool := do
  match (← IO.getEnv "LAKE_HEADER_SNAPSHOTS") with
  | some v => return !(v == "0" || v == "false" || v == "off" || v == "no")
  | none => return true

def mixStr (h : Hash) (s : String) : Hash :=
  -- length-delimited so that part boundaries matter
  h.mix (Hash.ofString s!"{s.utf8ByteSize}:") |>.mix (Hash.ofString s)

/-- Removes the least recently used snapshots until the directory is below `capBytes`. -/
def evict (dir : FilePath) (capBytes : Nat) : IO Unit := do
  let entries ← dir.readDir
  let mut snaps : Array (Nat × FilePath × Nat) := #[] -- (last use, snapshot, bytes)
  let mut total := 0
  for e in entries do
    if e.path.extension == some "hsnap" && !(e.fileName.endsWith ".tmp.hsnap") then
      let size := (← e.path.metadata).byteSize.toNat +
        ((← (e.path.addExtension "deps").metadata.toBaseIO).toOption.map (·.byteSize.toNat) |>.getD 0)
      let uses := e.path.withExtension "uses"
      let t ← match (← uses.metadata.toBaseIO) with
        | .ok m => pure m.modified.sec.toNat
        | .error _ => pure 0
      snaps := snaps.push (t, e.path, size)
      total := total + size
  if total ≤ capBytes then return
  let sorted := snaps.qsort (fun a b => a.1 < b.1)
  for (_, p, size) in sorted do
    if total ≤ capBytes then break
    removeFileIfExists p
    removeFileIfExists (p.addExtension "deps")
    total := total - size

def saveScript : String :=
  "lean=\"$1\"; src=\"$2\"; setup=\"$3\"; tmp=\"$4\"; fin=\"$5\"; lock=\"$6\"; shift 6\n" ++
  "trap 'rm -f \"$tmp\" \"$tmp.deps\" \"$lock\"' EXIT\n" ++
  "n=; command -v nice >/dev/null 2>&1 && n='nice -n 10'\n" ++
  "out=$($n \"$lean\" \"$@\" \"$src\" --setup \"$setup\" --incr-header-save=\"$tmp\" 2>&1) || exit 0\n" ++
  "[ -z \"$out\" ] || exit 0\n" ++
  "out=$($n \"$lean\" \"$@\" \"$src\" --setup \"$setup\" --incr-load=\"$tmp\" 2>&1) || exit 0\n" ++
  "[ -z \"$out\" ] || exit 0\n" ++
  "mv -f \"$tmp.deps\" \"$fin.deps\" && mv -f \"$tmp\" \"$fin\"\n"

/-- Stale locks (a save that died) are ignored after this many seconds. -/
def lockTimeout : Nat := 900

/--
Decides how a Lean run on `srcText` uses header snapshots stored in `dir`.

* `setup`: the module setup that is passed to Lean via `--setup`.
* `importHash`: the transitive import trace (hashes of every imported artifact).
* `leanArgs`: the Lean arguments other than the source file and `--setup`.
* `env`: the environment of the run (for `LEAN_PATH` and the save process).

Never throws: any problem means "no snapshot".
-/
public def plan
  (dir : FilePath) (srcText : String) (setup : ModuleSetup) (importHash : Hash)
  (leanArgs : Array String) (lean : FilePath) (leanGithash : String)
  (env : Array (String × Option String))
: BaseIO Plan := do
  let r ← (go).toBaseIO
  match r with
  | .ok p => return p
  | .error _ => return {}
where
  go : IO Plan := do
    unless (← enabled) do return {}
    if System.Platform.isWindows then return {}
    unless setup.dynlibs.isEmpty && setup.plugins.isEmpty && setup.imports?.isNone do return {}
    let some saveArgs := filterArgs leanArgs | return {}
    let some hdr := headerPrefix? srcText | return {}
    let leanMeta ← lean.metadata
    let setupNorm := {setup with name := `_hsnap}
    let leanPath := env.findSome? fun (k, v) => if k == "LEAN_PATH" then v else none
    let mut h := Hash.ofString "lake-header-snapshot-v1"
    h := mixStr h leanGithash
    h := mixStr h lean.toString
    h := mixStr h s!"{leanMeta.byteSize}/{leanMeta.modified.sec}/{leanMeta.modified.nsec}"
    h := mixStr h hdr
    h := mixStr h (toJson setupNorm).compress
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
    let ok ← (do IO.FS.withFile lock .writeNew fun _ => pure (); pure true).catchExceptions
      fun _ => pure false
    unless ok do return {}
    let capMb := (← envNat? "LAKE_HEADER_SNAPSHOT_MAX_MB").getD 8192
    try evict dir (capMb * 1024 * 1024) catch _ => pure ()
    let src := dir / s!"{key}.lean"
    let setupFile := dir / s!"{key}.setup.json"
    IO.FS.writeFile src hdr
    IO.FS.writeFile setupFile (toJson setup).compress
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

/-- Starts the planned background save (if any) without waiting for it. -/
public def Plan.startSave (p : Plan) : BaseIO Unit := do
  if let some args := p.save? then
    discard <| (IO.Process.spawn args).toBaseIO

end Lake.HeaderSnapshot
