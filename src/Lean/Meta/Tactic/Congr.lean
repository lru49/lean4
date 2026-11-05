/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.CongrTheorems
public import Lean.Meta.Tactic.Assert
public import Lean.Meta.Tactic.Refl
public import Lean.Meta.Tactic.Assumption

public section

namespace Lean
open Meta

register_builtin_option congr.closePostMaxHeartbeats : Nat := {
  defValue := 20000
  descr := "maximum number of heartbeats (in thousands, like `maxHeartbeats`) the `congr` tactic may spend on each \
    attempt to close a residual goal with `Eq.refl`, `HEq.refl` or `assumption` at default transparency after the \
    congruence theorem has been applied (`closePost` in `Lean.MVarId.congrN`). When the budget is exhausted the \
    attempt is abandoned and the goal is returned to the user, exactly as if it had failed. A definitional-equality \
    check between two sides that are not definitionally equal (the usual case for a goal the user intends to prove by \
    rewriting after `congr`) can otherwise unfold both sides to exhaustion. 0 means no limit except `maxHeartbeats`"
}

builtin_initialize registerTraceClass `Meta.Tactic.congr

/--
Runs `x` with at most `maxHeartbeats` heartbeats (`0`: no limit of its own). The ambient `maxHeartbeats` limit is
never extended. Returns `none`, with the state rolled back, when the budget is exhausted; other exceptions propagate.
-/
private def withHeartbeatBudget? (maxHeartbeats : Nat) (x : MetaM α) : MetaM (Option α) := do
  let ctx ← readThe Core.Context
  let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
  let budget := if ctx.maxHeartbeats == 0 then maxHeartbeats else min maxHeartbeats (ctx.maxHeartbeats - used)
  if budget == 0 then
    -- no budget of our own, or the ambient budget is already exhausted (then `x` reports that itself)
    return some (← x)
  let s ← saveState
  tryCatchRuntimeEx
    (some <$> withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget }) (withCurrHeartbeats x))
    fun ex => do
      if ex.isMaxHeartbeat then
        s.restore
        return none
      else
        throw ex

/--
Preprocessor before applying congruence theorem.
Tries to close new goals using `Eq.refl`, `HEq.refl`, and `assumption`.
It also tries to apply `heq_of_eq`.

Each of the three closing attempts may use at most `maxHeartbeats` heartbeats (`0`: unlimited); an attempt
that exhausts its budget counts as failed, see `congr.closePostMaxHeartbeats`.
-/
def MVarId.congrPre (mvarId : MVarId) (maxHeartbeats : Nat := 0) : MetaM (Option MVarId) := do
  let mvarId ← mvarId.heqOfEq
  if (← closes "Eq.refl" ((·.isSome) <$> observing? mvarId.refl)) then return none
  if (← closes "HEq.refl" ((·.isSome) <$> observing? mvarId.hrefl)) then return none
  if (← closes "assumption" mvarId.assumptionCore) then return none
  return some mvarId
where
  closes (what : String) (x : MetaM Bool) : MetaM Bool := do
    let start ← IO.getNumHeartbeats
    let result? ← withHeartbeatBudget? maxHeartbeats x
    if (← isTracingEnabledFor `Meta.Tactic.congr) then
      let outcome := match result? with
        | some true => "closed the goal"
        | some false => "failed"
        | none => s!"abandoned, budget of {maxHeartbeats / 1000} heartbeats exhausted"
      let used := ((← IO.getNumHeartbeats) - start) / 1000
      trace[Meta.Tactic.congr] "{what} at {repr (← getTransparency)} transparency: {outcome} after {used} \
        heartbeats{indentD (MessageData.ofGoal mvarId)}"
    return result?.getD false

/--
Asserts the given congruence theorem as fresh hypothesis, and then applies it.
Return the `fvarId` for the new hypothesis and the new subgoals.
-/
private def applyCongrThm? (mvarId : MVarId) (congrThm : CongrTheorem) : MetaM (List MVarId) := do
  let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThm.type congrThm.proof
  let (fvarId, mvarId) ← mvarId.intro1P
  let mvarIds ← mvarId.apply (mkFVar fvarId) { synthAssignedInstances := false }
  mvarIds.mapM fun mvarId => mvarId.tryClear fvarId

/--
Try to apply a `simp` congruence theorem.
-/
def MVarId.congr? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext do commitWhenSomeNoEx? do
    mvarId.checkNotAssigned `congr
    let target ← mvarId.getType'
    let some (_, lhs, _) := target.eq? | return none
    let lhs := lhs.cleanupAnnotations
    unless lhs.isApp do return none
    let some congrThm ← mkCongrSimp? lhs.getAppFn (subsingletonInstImplicitRhs := false) (maxArgs? := lhs.getAppNumArgs) | return none
    applyCongrThm? mvarId congrThm

/--
Try to apply a `hcongr` congruence theorem, and then tries to close resulting goals
using `Eq.refl`, `HEq.refl`, and assumption.
-/
def MVarId.hcongr? (mvarId : MVarId) : MetaM (Option (List MVarId)) := do
  commitWhenSomeNoEx? do
    mvarId.checkNotAssigned `congr
    let mvarId ← mvarId.eqOfHEq
    mvarId.withContext do
      let target ← mvarId.getType'
      let some (_, lhs, _, _) := target.heq? | return none
      let lhs := lhs.cleanupAnnotations
      unless lhs.isApp do return none
      let congrThm ← mkHCongrWithArity lhs.getAppFn lhs.getAppNumArgs
      applyCongrThm? mvarId congrThm

/--
Try to apply `implies_congr`.
-/
def MVarId.congrImplies? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do
    let mvarId₁ :: mvarId₂ :: _ ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr)
      | throwError "Internal error: Expected at least two goals after applying `{.ofConstName ``implies_congr}`, but unexpectedly found fewer"
    return [mvarId₁, mvarId₂]

/--
Given a goal of the form `⊢ f as = f bs`, `⊢ (p → q) = (p' → q')`, or `⊢ f as ≍ f bs`, try to apply congruence.
It takes proof irrelevance into account, and the fact that `Decidable p` is a subsingleton.
-/
def MVarId.congrCore (mvarId : MVarId) : MetaM (List MVarId) := do
  if let some mvarIds ← mvarId.congr? then
    pure mvarIds
  else if let some mvarIds ← mvarId.hcongr? then
    pure mvarIds
  else if let some mvarIds ← mvarId.congrImplies? then
    pure mvarIds
  else
    throwTacticEx `congr mvarId "Failed to apply congruence"

/--
Given a goal of the form `⊢ f as = f bs`, `⊢ (p → q) = (p' → q')`, or `⊢ f as ≍ f bs`, try to apply congruence.
It takes proof irrelevance into account, and the fact that `Decidable p` is a subsingleton.

* Applies `congr` recursively up to depth `depth`.
* If `closePre := true`, it will attempt to close new goals
  using `Eq.refl`, `HEq.refl`, and `assumption` with reducible transparency.
* If `closePost := true`, it will try again on goals on which `congr` failed to make progress
  with default transparency, spending at most `congr.closePostMaxHeartbeats` heartbeats per attempt.
-/
def MVarId.congrN (mvarId : MVarId) (depth : Nat := 1000000) (closePre := true) (closePost := true) : MetaM (List MVarId) := do
  let (_, s) ← go depth mvarId |>.run #[]
  return s.toList
where
  post (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    let mode ← getTransparency
    if closePost && mode != .reducible && mode != .none then
      let maxHeartbeats := congr.closePostMaxHeartbeats.get (← getOptions) * 1000
      if let some mvarId ← mvarId.congrPre maxHeartbeats then
        modify (·.push mvarId)
    else
      modify (·.push mvarId)

  go (n : Nat) (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    if let some mvarId ← if closePre then withReducible mvarId.congrPre else pure mvarId then
      match n with
      | 0 => post mvarId
      | n+1 =>
        let some mvarIds ← observing? (m := MetaM) mvarId.congrCore
          | post mvarId
        mvarIds.forM (go n)
