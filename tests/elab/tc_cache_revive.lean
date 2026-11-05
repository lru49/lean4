/-!
Tests that the persistent tier of the type class resolution cache is brought back when a scope that
changed the instances in effect ends and restores the very instance table that was in effect
before (`Environment.reviveSynthCache`), and that it is not brought back when the instances in
effect differ.
-/

set_option trace.Meta.synthInstance.cache true

class Foo (α : Type) where
class Bar (α : Type) where

instance : Foo Nat := ⟨⟩

namespace S
scoped instance : Bar Nat := ⟨⟩
end S

/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def f1 : Unit := let _ : Foo Nat := inferInstance; ()

-- A command-level scope activating a scoped instance: inside, the instances differ.
open S in
/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def f2 : Unit := let _ : Foo Nat := inferInstance; ()

-- After the scope, the tier from before the `open` is revived.
/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def f3 : Unit := let _ : Foo Nat := inferInstance; ()

-- The scoped instance is not visible after the scope: the failure is computed afresh (it was never
-- queried outside), and is then cached.
/--
error: failed to synthesize instance of type class
  Bar Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: Bar Nat
-/
#guard_msgs in
def g1 : Unit := let _ : Bar Nat := inferInstance; ()

-- Inside the scope the instance is found: the cached failure is not served.
open S in
/-- trace: [Meta.synthInstance.cache] new: Bar Nat -/
#guard_msgs in
def g2 : Unit := let _ : Bar Nat := inferInstance; ()

-- After the scope, the failure cached before it is served again.
/--
error: failed to synthesize instance of type class
  Bar Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] cached: Bar Nat
-/
#guard_msgs in
def g3 : Unit := let _ : Bar Nat := inferInstance; ()

-- The `classical` tactic changes the instances in effect for its block only: inside it, the query is
-- computed afresh, after it the tier from before is revived.
/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
theorem t1 : True := by
  classical
  have : Foo Nat := inferInstance
  exact trivial

/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def f4 : Unit := let _ : Foo Nat := inferInstance; ()

-- A section in which a global instance is added: after it, the instances in effect differ from
-- those before the section, so nothing is revived.
section
class Baz (α : Type) where
instance : Baz Nat := ⟨⟩
end

/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def f5 : Unit := let _ : Foo Nat := inferInstance; ()

-- A local instance in a section: inside it is used, after the section the tier from before the
-- section is revived.
section
local instance : Bar Nat := ⟨⟩
/-- trace: [Meta.synthInstance.cache] new: Bar Nat -/
#guard_msgs in
def g4 : Unit := let _ : Bar Nat := inferInstance; ()
end

/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def f6 : Unit := let _ : Foo Nat := inferInstance; ()
