/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Linter.Util

public section

set_option linter.missingDocs true

namespace Lean.Linter

open Lean Elab Command
open Lean.Linter (logLint)

/--
A linter that warns when bound variable names are the same as constructor names for their types,
modulo namespaces.
 -/
register_builtin_option linter.constructorNameAsVariable : Bool := {
  defValue := true,
  descr := "enable the linter that warns when bound variable names are nullary constructor names"
}

/--
Heartbeat budget (in thousands, like `maxHeartbeats`) for the weak-head normalization of one binder
type in `constructorNameAsVariable`. Normalizing a binder type at default transparency can evaluate
arbitrary computations: for `h : x ∈ s` with a concrete `s : Finset α`, `whnf` unfolds the
membership instance to `Quot.lift` and then evaluates `s` itself, which took seconds per binder in
proofs about concrete finite sets. A type whose normalization exceeds the budget is skipped.
-/
def constructorNameAsVariable.whnfHeartbeats : Nat := 1000

/--
The weak-head normal form of a binder type for `constructorNameAsVariable`, or `none` if computing
it exceeds `constructorNameAsVariable.whnfHeartbeats`. A type whose head is already an inductive
type is in weak-head normal form and is returned without calling `whnf`.
-/
def constructorNameAsVariable.binderTypeWhnf? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  if let .const tn _ := ty.getAppFn then
    if let some (.inductInfo _) := (← getEnv).find? tn then
      return some ty
  let ctx ← readThe Core.Context
  let budget := constructorNameAsVariable.whnfHeartbeats * 1000
  let budget := if ctx.maxHeartbeats == 0 then budget else min budget ctx.maxHeartbeats
  tryCatchRuntimeEx
    (some <$> withTheReader Core.Context
      (fun c => { c with maxHeartbeats := budget }) (withCurrHeartbeats (Meta.whnf ty)))
    fun ex => if ex.isMaxHeartbeat then return none else throw ex

open constructorNameAsVariable in
/--
Reports when bound variables' names overlap with constructor names for their type. This is to warn
especially new users that they have built a pattern that matches anything, rather than one that
matches a particular constructor. Use `linter.constructorNameAsVariable` to disable.
-/
def constructorNameAsVariable : Linter where
  run cmdStx := do
    unless getLinterValue linter.constructorNameAsVariable (← getLinterOptions) do
      return
    let some cmdStxRange := cmdStx.getRange?
      | return

    let infoTrees := (← get).infoState.trees.toArray
    let warnings : IO.Ref (Std.HashMap Lean.Syntax.Range (Syntax × Name × Name)) ← IO.mkRef {}
    let constRanges : IO.Ref (Std.HashSet Lean.Syntax.Range) ← IO.mkRef {}

    for tree in infoTrees do
      tree.visitM' (postNode := fun ci info _ => do
        match info with
        | .ofTermInfo ti =>
          match ti.expr with
          | .fvar id .. =>
            let some range := info.range? | return
            if (← warnings.get).contains range then return
            let .original .. := info.stx.getHeadInfo | return
            if ti.isBinder then
              -- This is a local variable declaration.
              let some ldecl := ti.lctx.find? id | return
              -- Skip declarations which are outside the command syntax range, like `variable`s
              -- (it would be confusing to lint these), or those which are macro-generated
              if !cmdStxRange.contains range.start || ldecl.userName.hasMacroScopes then return
              let opts ← ci.options.toLinterOptions
              -- we have to check for the option again here because it can be set locally
              if !getLinterValue linter.constructorNameAsVariable opts then return
              if let n@(.str .anonymous s) := info.stx.getId then
                -- Check whether the type is an inductive type, and get its constructors
                let ty ←
                  if let some t := ti.expectedType? then pure t
                  else ti.runMetaM ci (Meta.inferType ti.expr)
                let some ty ← ti.runMetaM ci (binderTypeWhnf? ty) | return
                if let .const tn _ := ty.getAppFn' then
                  if let some (.inductInfo i) := (← getEnv).find? tn then
                    for c in i.ctors do
                      -- Only warn when the constructor has 0 fields. Pattern variables can't be
                      -- confused with constructors that want arguments.
                      if let some (.ctorInfo ctorInfo) := (← getEnv).find? c then
                        if ctorInfo.numFields > 0 then continue
                      if let .str _ cn := c then
                        if cn == s then
                          warnings.modify (·.insert range (info.stx, n, c))
            else pure ()
          | .const .. =>
            let some range := info.range? | return
            let .original .. := info.stx.getHeadInfo | return
            if ti.isBinder then
              constRanges.modify fun s => s.insert range
          | _ => pure ()
        | _ => pure ())

    -- Sort the outputs by position, excluding those that are also defining global constants.
    -- Global constants occur for example in `structure` fields
    for (range, declStx, userName, ctorName) in (← warnings.get).toArray.qsort (·.1.start < ·.1.start) do
      unless (← constRanges.get).contains range do
        logLint linter.constructorNameAsVariable declStx <|
          m!"Local variable '{userName}' resembles constructor '{ctorName}' - " ++
          m!"write '.{userName}' (with a dot) or '{ctorName}' to use the constructor."

builtin_initialize addLinter constructorNameAsVariable
