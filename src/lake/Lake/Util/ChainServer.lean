/-
Copyright (c) 2026 lean-perf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init
public import Lean.Data.Name
public import Lean.Data.NameMap.Basic

/-!
# Chain servers (lean-perf chain batching, lane DP)

Lake compiles modules through a small pool of `lean --chain-server` processes (see
`Lean.chainServerPrepare` in Lean's `Shell.lean`; `LAKE_CHAIN_SERVERS=<n>`, default 2, `0` disables).
A server holds the import of the last module header it served; a module whose transitive imports
contain the module a server compiled last is sent to that server, which continues its held import
with the new modules (in a chain, the predecessor's fresh `.olean`) instead of a new process importing
everything again. The child it forks for the module produces exactly the outputs of a plain `lean`.
Selection is structural, from the import DAG: following "my last module is among your transitive
imports" keeps a server on a chain of the build (the critical path is such a chain). A module that no
server can continue takes an idle server that has served nothing yet, or else restarts an idle server
(a fresh import: the cost of a plain run) so that its dependents can continue from it. With all
servers busy, the module runs a plain `lean` as before; so does every request a server cannot serve
exactly (the server `exec`s one). `LAKE_CHAIN_MODULES=<file>` (module names, one per line) restricts
routing to the listed modules (a debugging override).
-/

namespace Lake

public abbrev ChainServerChild := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .null }

public structure ChainPool where
  /-- per server: the process, busy, last module compiled successfully (`none`: fresh) -/
  state    : IO.Ref (Array (Option ChainServerChild × Bool × Option Lean.Name))
  lean     : System.FilePath
  leanPath : String
  dir      : System.FilePath
  only?    : Option Lean.NameSet := none

def spawnServer (lean : System.FilePath) (leanPath : String) : IO ChainServerChild :=
  IO.Process.spawn {
    cmd := lean.toString, args := #["--chain-server"]
    env := #[("LEAN_PATH", leanPath)]
    stdin := .piped, stdout := .piped, stderr := .null }

/-- A pool of `n` chain servers (`lean --chain-server` with `LEAN_PATH := leanPath`), each started on
its first use (a build that compiles nothing starts no process and creates no directory). -/
public def ChainPool.start (lean : System.FilePath) (leanPath : String) (n : Nat)
    (dir : System.FilePath) : IO ChainPool := do
  let st := Array.replicate n (none, false, none)
  let only? ← match (← IO.getEnv "LAKE_CHAIN_MODULES") with
    | some f => do
      let ls ← IO.FS.lines f
      pure (some (ls.foldl (init := {}) fun s l => if l.isEmpty then s else s.insert l.toName))
    | none => pure none
  return { state := ← IO.mkRef st, lean, leanPath, dir, only? }

/--
Reserves a server for module `mod` whose transitive imports are `closure`: one that can continue
from its last module (`some (i, false)`), else a fresh (or not yet started) one (`some (i, false)`),
else an idle one to restart (`some (i, true)`); `none` if all are busy.
-/
public def ChainPool.acquire (pool : ChainPool) (mod : Lean.Name) (closure : Lean.Name → Bool) :
    BaseIO (Option (Nat × Bool)) :=
  if pool.only?.any (!·.contains mod) then return none else
  pool.state.modifyGet fun st =>
    let idle (e : Option ChainServerChild × Bool × Option Lean.Name) := !e.2.1
    let pick? := (st.findIdx? fun e => idle e && e.1.isSome && e.2.2.any closure).map (·, false) <|>
      (st.findIdx? fun e => idle e && e.2.2.isNone).map (·, false) <|>
      (st.findIdx? idle).map (·, true)
    match pick? with
    | some (i, _) => (pick?, st.modify i fun (c, _, l) => (c, true, l))
    | none => (none, st)

/--
Compiles `mod` with server `i` (reserved by `acquire`, restarted first if `restart`): `args` are the
`lean` arguments, run in the current directory. Returns the exit code, stdout and stderr of the run,
or `none` if the server failed (the caller then runs a plain `lean`).
-/
public def ChainPool.run (pool : ChainPool) (i : Nat) (restart : Bool) (mod : Lean.Name)
    (args : Array String) : IO (Option IO.Process.Output) := do
  let release (child? : Option ChainServerChild) (last? : Option Lean.Name → Option Lean.Name) :
      BaseIO Unit :=
    pool.state.modify fun st => st.modify i fun (_, _, l) => (child?, false, last? l)
  let some (child?, _, _) := (← pool.state.get)[i]? | return none
  let child ← match child?, restart with
    | some c, false => pure c
    | c?, _ =>
      if let some c := c? then
        try c.kill catch _ => pure ()
      match (← (spawnServer pool.lean pool.leanPath).toBaseIO) with
      | .ok c => pool.state.modify (·.modify i fun (_, b, _) => (some c, b, none)); pure c
      | .error _ => release none id; return none
  let cwd ← IO.currentDir
  IO.FS.createDirAll pool.dir
  let base := pool.dir / s!"{i}"
  let outFile := base.addExtension "out"
  let errFile := base.addExtension "err"
  let fields := #[cwd.toString, outFile.toString, errFile.toString, pool.leanPath] ++ args
  if fields.any (fun f => f.contains '\t' || f.contains '\n') then
    release (some child) id
    return none
  try
    child.stdin.putStrLn ("\t".intercalate fields.toList)
    child.stdin.flush
    let reply ← child.stdout.getLine
    let ws := reply.trimAscii.copy.splitOn " "
    let some rc := ws[0]?.bind (·.toNat?) | release none id; return none
    let stdout ← IO.FS.readFile outFile
    let stderr ← IO.FS.readFile errFile
    -- the held import of a server that compiled `mod` can continue with `mod`'s `.olean`
    let served := ws[1]? == some "served"
    -- a server keeps every environment it built (~0.15 GB per module on Mathlib-sized imports):
    -- one whose anonymous memory exceeds `LAKE_CHAIN_SERVER_MAX_MB` (default 4096) is stopped and
    -- started afresh on its next use
    let anonKb := ws.findSome? (fun w => (w.dropPrefix? "server_anon_kb=").bind (·.toNat?)) |>.getD 0
    let maxMb := (← IO.getEnv "LAKE_CHAIN_SERVER_MAX_MB").bind (·.toNat?) |>.getD 4096
    if anonKb > maxMb * 1024 then
      try child.kill catch _ => pure ()
      release none (fun _ => none)
    else
      release (some child) (if served && rc == 0 then fun _ => some mod else id)
    return some { exitCode := rc.toUInt32, stdout, stderr }
  catch _ =>
    release none id
    return none

end Lake
