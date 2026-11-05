/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Data.Json
public import Lean.Data.NameMap
import Lean.Environment
import Lean.Util.FoldConsts
import Std.Data.HashMap

/-! # Declaration-level cross-module dependencies

Computes, for one built module, which of its commands (top-level declarations, including unnamed ones
such as `example`s) reference constants of which workspace modules, directly or through other commands
of the same module. A scheduler can use this to start a dependent module before all of its imports are
finished and let each command wait only for the modules it actually references.

The analysis reads only build artifacts that already exist when the module has been built: the
module's own `.olean` (term-level references of every constant, which include instances and lemmas
inserted by tactics) and `.ilean` (declaration ranges and syntactic references, which also cover
unnamed commands), plus the constant-name tables of the module's workspace imports. It never runs
the elaborator and does not change any build output.

Caveat recorded in the output (`"envSensitive": true`): a command that references no constant of a
module may still observe that module's environment-extension state (simp sets, instances, unification
hints, `dsimp` lemmas leave no trace in terms), so starting it before that module is loaded is only
sound when the scheduler validates or excludes such reads.
-/

open Lean System

namespace Lake.DeclDeps

/-- One constant-name table per workspace olean (memoized for the lifetime of the Lake process). -/
builtin_initialize constTableCache : IO.Ref (Std.HashMap String (Array Name)) ← IO.mkRef {}

/-- The constant names of an `.olean` (the mapped region is deliberately kept alive). -/
def constNamesOf (olean : FilePath) : IO (Array Name) := do
  let key := olean.toString
  if let some ns := (← constTableCache.get).get? key then return ns
  let (md, _region) ← readModuleData olean
  let ns := md.constNames
  constTableCache.modify (·.insert key ns)
  return ns

/-- A command of the analysed module: identified by its first source line. -/
structure Cmd where
  line : Nat
  endLine : Nat := 0
  names : Array Name := #[]
  needs : NameSet := {}
  after : Std.HashSet Nat := {}

def jsonNat (j : Json) : Nat := (j.getNat?).toOption.getD 0

/--
Analyse module `mod` from its `olean`/`ilean` and the oleans of its workspace imports `deps`
(`(module, olean path)`, transitive). Returns the JSON document described in the module docstring.
-/
public def compute (mod : Name) (olean ilean : FilePath) (deps : Array (Name × FilePath))
    (srcHash : String := "") : IO Json := do
  let t0 ← IO.monoMsNow
  -- constant -> defining workspace module
  let mut owner : Std.HashMap Name Name := {}
  for (m, f) in deps do
    if m == mod then continue
    for n in (← constNamesOf f) do owner := owner.insert n m
  let (md, _region) ← readModuleData olean
  let own : NameSet := md.constNames.foldl (·.insert ·) {}
  -- declaration ranges and syntactic references from the ilean
  let il ← match Json.parse (← IO.FS.readFile ilean) with
    | .ok j => pure j | .error e => throw <| IO.userError s!"{ilean}: {e}"
  let mut ranges : Array (Nat × Nat × Name) := #[]
  if let .ok decls := (il.getObjValD "decls").getObj? then
    for (n, r) in decls do
      if let .ok a := r.getArr? then
        ranges := ranges.push (jsonNat a[0]!, jsonNat a[2]!, n.toName)
  let rangeOf : Std.HashMap Name Nat := ranges.foldl (fun m (s, _, n) => m.insert n s) {}
  let ownerLine (line : Nat) : Option Nat := Id.run do
    let mut best : Option Nat := none
    for (s, e, _) in ranges do
      if s ≤ line && line ≤ e && best.all (· < s) then best := some s
    return best
  let rec lineOfName (n : Name) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 => match rangeOf.get? n with
      | some l => some l
      | none => if n.isAnonymous then none else lineOfName n.getPrefix fuel
  let mut cmds : Std.HashMap Nat Cmd := {}
  for (s, e, n) in ranges do
    let c := cmds.getD s { line := s }
    cmds := cmds.insert s { c with endLine := max c.endLine e, names := c.names.push n }
  -- term-level references (olean)
  let mut lineOfConst : Std.HashMap Name Nat := {}
  for n in md.constNames do
    if let some l := lineOfName n 64 then lineOfConst := lineOfConst.insert n l
  for ci in md.constants do
    let some l := lineOfConst.get? ci.name | continue
    let mut c := cmds.getD l { line := l }
    for u in ci.getUsedConstantsAsSet do
      if own.contains u then
        if let some l' := lineOfConst.get? u then
          if l' != l then c := { c with after := c.after.insert l' }
      else if let some m := owner.get? u then
        c := { c with needs := c.needs.insert m }
    cmds := cmds.insert l c
  -- syntactic references (ilean), which also cover unnamed commands such as `example`s
  if let .ok refs := (il.getObjValD "references").getArr? then
    let mut i := 0
    while i + 1 < refs.size do
      let key := refs[i]!; let v := refs[i+1]!; i := i + 2
      let .ok k := key.getArr? | continue
      unless k.size == 3 && jsonNat k[0]! == 0 do continue
      let some dm := (k[1]!.getStr?).toOption.map (·.toName) | continue
      let some cn := (k[2]!.getStr?).toOption.map (·.toName) | continue
      let .ok us := (v.getObjValD "usages").getArr? | continue
      for u in us do
        let .ok ua := u.getArr? | continue
        let ln := jsonNat ua[0]!
        let l := (ownerLine ln).getD ln
        let mut c := cmds.getD l { line := l, endLine := ln }
        if dm == mod then
          if let some l' := lineOfConst.get? cn then
            if l' != l then c := { c with after := c.after.insert l' }
        else if deps.any (·.1 == dm) then
          c := { c with needs := c.needs.insert dm }
        cmds := cmds.insert l c
  -- transitive closure of `needs` through `after`
  let keys := cmds.toArray.map (·.1) |>.qsort (· < ·)
  let mut closed : Std.HashMap Nat NameSet := {}
  for _ in [0:keys.size] do   -- fixpoint (commands reference earlier ones; one pass usually suffices)
    let mut changed := false
    for l in keys do
      let c := cmds[l]!
      let mut s := (closed.getD l c.needs)
      for a in c.after do s := (closed.getD a ((cmds.get? a).map (·.needs) |>.getD {})).foldl (·.insert ·) s
      if s.toList.length != (closed.getD l {}).toList.length then changed := true
      closed := closed.insert l s
    if !changed then break
  let out := keys.map fun l =>
    let c := cmds[l]!
    Json.mkObj [("line", l), ("end", c.endLine), ("names", toJson (c.names.map toString)),
      ("needs", toJson ((closed.getD l {}).toList.map toString |>.toArray.qsort (· < ·))),
      ("direct", toJson (c.needs.toList.map toString |>.toArray.qsort (· < ·))),
      ("after", toJson (c.after.toArray.qsort (· < ·)))]
  let t1 ← IO.monoMsNow
  return Json.mkObj [("version", 1), ("module", mod.toString), ("src", srcHash), ("envSensitive", true),
    ("analysisMs", t1 - t0), ("commands", Json.arr out)]

end Lake.DeclDeps
