/-!
Owned thread-shared (MT) arrays, byte arrays and strings with a single reference are updated in place
(runtime: `mt_unique_to_st`). Values that are still shared must never change under their other holders.
-/

def churn (r : IO.Ref (Array Nat)) (n : Nat) : IO Unit := do
  for i in [0:n] do
    r.modify fun a => (a.push i).set! 0 i

def main : IO Unit := do
  -- an `IO.Ref` used by several tasks: its value is MT; `modify` takes the unique reference out
  let r ← IO.mkRef (Array.replicate 4 0)
  let ts ← (List.range 8).mapM fun _ => IO.asTask (churn r 1000)
  for t in ts do
    let _ ← IO.ofExcept t.get
  let a ← r.get
  IO.println s!"array size {a.size}"
  -- a snapshot taken before further updates must be unaffected by in-place updates of the ref's value
  let snap ← r.get
  let before := snap.size
  r.modify fun a => a.set! 1 12345
  r.modify fun a => a.push 7
  IO.println s!"snapshot unchanged {snap.size == before && snap[1]! != 12345}"
  IO.println s!"ref updated {(← r.get)[1]!} {(← r.get).back!}"
  -- task results are MT; consuming a unique task result and updating it in place
  let t := Task.spawn fun _ => (List.range 100).toArray
  let arr := t.get
  let arr2 := arr.set! 0 42
  IO.println s!"task array {arr[0]!} {arr2[0]!} {arr.size}"
  -- strings and byte arrays through a shared ref
  let sr ← IO.mkRef ""
  let bs ← IO.mkRef (ByteArray.empty)
  let ts ← (List.range 4).mapM fun k => IO.asTask do
    for _ in [0:250] do
      sr.modify (·.push (Char.ofNat (97 + k)))
      bs.modify (·.push k.toUInt8)
  for t in ts do
    let _ ← IO.ofExcept t.get
  let s ← sr.get
  let b ← bs.get
  IO.println s!"string {s.length} bytes {b.size}"
  let counts := (List.range 4).map fun k => (s.toList.filter (· == Char.ofNat (97 + k))).length
  IO.println s!"string counts {counts}"
  let bcounts := (List.range 4).map fun k => (b.toList.filter (· == k.toUInt8)).length
  IO.println s!"byte counts {bcounts}"
