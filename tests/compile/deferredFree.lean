/-!
Stress test for the runtime's deferred release of large object graphs: a `lean_dec_ref_cold` cascade
that frees more than `LEAN_DEFER_FREE_MIN` objects (default 16384) continues on a release thread.
Covers single-threaded graphs whose children are shared with live values (the release thread must
return those decrements to the owner thread), graphs dropped on task threads, and thread-shared graphs
(task results) dropped on the main thread. The printed checksums must not depend on any of this.
-/

def build (n : Nat) (shared : Array (List Nat)) : Array (List Nat) := Id.run do
  let mut a := #[]
  for i in [0:n] do
    if i % 7 == 0 then a := a.push shared[i % shared.size]!
    else if i % 11 == 0 then a := a.push (shared[i % shared.size]! ++ [i])
    else a := a.push (List.range (i % 5 + 1))
  return a

def checksum (a : Array (List Nat)) : Nat :=
  a.foldl (fun s l => s + l.foldl (· + ·) 0 + l.length) 0

@[noinline] def round (shared : Array (List Nat)) (k : Nat) : IO Nat := do
  let big := build (50000 + k) shared
  let c := checksum big
  -- `big` dies when this returns: most of it on the release thread
  return c

def main : IO Unit := do
  let mut shared := (Array.range 100).map fun i => List.range (i % 13 + 1)
  let mut total := 0
  for k in [0:20] do
    total := total + (← round shared k)
  IO.println s!"total {total} shared {checksum shared}"
  -- the shared values stay usable and updatable after the graphs that referenced them died
  for i in [0:shared.size] do
    shared := shared.modify i (0 :: ·)
  IO.println s!"after update {checksum shared}"
  -- graphs dropped on task threads
  let ts ← (List.range 8).mapM fun k => IO.asTask (round shared k)
  let rs ← ts.mapM fun t => IO.ofExcept t.get
  IO.println s!"tasks {rs.foldl (· + ·) 0}"
  -- thread-shared graphs (task results) dropped on this thread
  let mut mt := 0
  for k in [0:4] do
    let t ← IO.asTask (pure (build (40000 + k) shared))
    let big ← IO.ofExcept t.get
    mt := mt + checksum big
  IO.println s!"mt {mt} shared {checksum shared}"
