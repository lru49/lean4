import Std.Data.HashMap
/-!
Values stored into global refs during initialization are marked MT only when initialization ends (runtime:
`defer_ref_mark`). Tables built by many `modify`s in `initialize` blocks must be complete and correct, and safe to
read and update from several threads afterwards.
-/

initialize tbl : IO.Ref (Std.HashMap Nat Nat) ← IO.mkRef {}
initialize arr : IO.Ref (Array String) ← IO.mkRef #[]

initialize do
  for i in [0:3000] do
    tbl.modify (·.insert i (i * i))
    arr.modify (·.push (toString i))

def main : IO Unit := do
  let ts ← (List.range 8).mapM fun k => IO.asTask do
    let m ← tbl.get
    let mut s := 0
    for i in [0:3000] do
      s := s + m.getD i 0
    tbl.modify (·.insert (10000 + k) k)
    arr.modify (·.push s!"t{k}")
    return s
  let mut sums := #[]
  for t in ts do
    sums := sums.push (← IO.ofExcept t.get)
  IO.println s!"sums {sums.toList.eraseDups}"
  IO.println s!"table {(← tbl.get).size} array {(← arr.get).size} first {(← arr.get)[0]!} 2999 {(← arr.get)[2999]!}"
