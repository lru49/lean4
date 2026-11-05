/-!
# `congr.closePostMaxHeartbeats`: the closing attempt after `congr` is bounded

After applying the congruence theorem, `congr` tries to close every residual goal with `Eq.refl`,
`HEq.refl` and `assumption` at default transparency. The definitional-equality check can be
arbitrarily expensive; each attempt gets its own heartbeat budget, and an attempt that exhausts it
counts as a failure (the goal is handed back to the user), never as an error.
-/

/-- `slow n` reduces to a numeral, but only by evaluating a list fold of `n` steps. -/
def slow (n : Nat) : Nat := (List.range n).foldl (· + ·) 0

/-- info: 124750 -/
#guard_msgs in
#eval slow 500

-- With the default budget `Eq.refl` closes the residual goal `slow 500 = 124750` by evaluation.
example (f : Nat → Nat) : f (slow 500) = f 124750 := by
  congr 1

-- With a budget of 1000 heartbeats the evaluation is abandoned, and the goal is left to the user.
set_option congr.closePostMaxHeartbeats 1 in
example (f : Nat → Nat) : f (slow 500) = f 124750 := by
  congr 1
  decide

-- An abandoned `Eq.refl` attempt does not prevent `assumption` from closing the goal.
set_option congr.closePostMaxHeartbeats 1 in
example (f : Nat → Nat) (h : slow 500 = 124750) : f (slow 500) = f 124750 := by
  congr 1

-- `congr.closePostMaxHeartbeats 0` keeps the ambient `maxHeartbeats` as the only limit.
set_option congr.closePostMaxHeartbeats 0 in
example (f : Nat → Nat) : f (slow 500) = f 124750 := by
  congr 1

-- The budget never extends the ambient `maxHeartbeats`: here the ambient limit is reached inside the
-- closing attempt and reported as the usual deterministic timeout of the whole tactic.
/--
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (1) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option maxHeartbeats 1 in
example (f : Nat → Nat) : f (slow 500) = f 124750 := by
  congr 1

-- Goals that `congr` closes today are still closed (the budget is generous): defeq by unfolding.
def g (n : Nat) : Nat := n + 1
example (a : Nat) (h : a = 2) : Nat.succ (g a) = Nat.succ (a + 1) := by
  congr 1
