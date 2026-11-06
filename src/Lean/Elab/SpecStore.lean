/-
Copyright (c) 2026 lean-perf (lane DT2). Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Meta.Instances
public import Lean.Language.Basic

public section

/-!
lean-perf (lane DT2): in-process store for speculative elaboration across a module boundary
(docs/levers/L-dt2-spec.md). A pre-started `lean` (DY's `LEAN_PRESTART_STDIN` driver) elaborates the
module's commands in the environment it has without its late imports ("E0") on a dedicated thread while
it waits for them; every `Prop` example that elaborates cleanly leaves a record (its statement, the
counters it consumed, its info tree and snapshot, and its read set: constant and namespace misses,
extension reads, added constants, instance query key paths). The real elaboration after the late
imports landed ("E1") elaborates each example's statement as usual and, when a record with the same
syntax has the same closed statement and scope and a read set disjoint from everything the late
modules add, replays the record instead of running the proof (which this process' kernel already
checked in E0, a sub-environment of E1). Everything else elaborates as before.
-/

namespace Lean.Elab.SpecStore
open Lean.Meta

inductive Mode where
  | off | record | consume
  deriving BEq, Inhabited, Repr

/-- A recorded `Prop` example. -/
structure ExampleRec where
  /-- the statement closed over the local context (section variables), mvars instantiated -/
  closedType : Expr
  opts       : Options
  ns         : Name
  openDecls  : List OpenDecl
  levelNames : List Name
  /-- DC's asynchronous example path was taken (its main-thread steps are replayed, the task is not) -/
  async      : Bool
  ngenBefore : NameGenerator
  ngenAfter  : NameGenerator
  msBefore   : Nat
  msAfter    : Nat
  dngBefore  : DeclNameGenerator
  dngAfter   : DeclNameGenerator
  /-- synchronous path: the info trees the example pushed -/
  trees      : Array InfoTree := #[]
  /-- asynchronous path: the info tree the task resolved the hole with, and the snapshot it logged -/
  holeTask?  : Option (Task InfoTree) := none
  snapTask?  : Option (Task Language.SnapshotTree) := none
  -- read set of the whole command, filled when the command finished cleanly
  misses      : Array Name := #[]
  nsMisses    : Array Name := #[]
  exts        : Array Name := #[]
  added       : Array Name := #[]
  instQueries : Array (Array InstanceKey) := #[]
  deriving Nonempty

/-- What the late modules add, computed once in the real run. -/
structure DeltaInfo where
  newConsts : NameSet := {}
  newNs     : NameSet := {}
  /-- extensions the late modules export entries for -/
  exts      : NameSet := {}
  instKeys  : Array (Array InstanceKey) := #[]
  modules   : Array Name := #[]
  deriving Inhabited

structure State where
  mode        : Mode := .off
  specTid     : UInt64 := 0
  stop        : Bool := false
  env0Modules : Array Name := #[]
  records     : Std.HashMap UInt64 ExampleRec := {}
  /-- the example of the command being recorded (set by the elaborator, finalized by the loop) -/
  pending?    : Option (UInt64 × ExampleRec) := none
  /-- the command being recorded, by key, and a promise resolved when it is done -/
  inProgress? : Option (UInt64 × IO.Promise Unit) := none
  cancelTk?   : Option IO.CancelToken := none
  /-- monotonic deadline (ms) of the command being recorded; 0 = none -/
  deadline    : Nat := 0
  budgetMs    : Nat := 120000
  deltaInfo?  : Option DeltaInfo := none
  debug       : Bool := false
  nRecorded   : Nat := 0
  nCommitted  : Nat := 0
  nRejected   : Nat := 0
  rejections  : Array String := #[]
  /-- debug: commands the speculation loop elaborated, how it ended, its elapsed time (ms) -/
  nCmds       : Nat := 0
  loopEnd     : String := ""
  loopMs      : Nat := 0
  /-- debug: how long `stop` waited for the loop to quiesce (ms) -/
  joinMs      : Nat := 0
  deriving Nonempty

builtin_initialize stateRef : IO.Ref State ← IO.mkRef {}

def key (stx : Syntax) : UInt64 :=
  hash (toString stx)

/-- `.record` on the speculation thread while it runs, `.consume` elsewhere once something was
recorded or the loop is running, `.off` otherwise. -/
def currentMode : BaseIO Mode := do
  let s ← stateRef.get
  if s.mode == .off then
    return .off
  if (← IO.getTID) == s.specTid then
    return .record
  return .consume

def isOn : BaseIO Bool := do
  return (← stateRef.get).mode != .off

def setPending (k : UInt64) (r : ExampleRec) : BaseIO Unit :=
  stateRef.modify fun s => { s with pending? := some (k, r) }

/-- The record for `k`, waiting for the speculation thread if it is elaborating that command. -/
def lookup (k : UInt64) : BaseIO (Option ExampleRec) := do
  let s ← stateRef.get
  if let some (k', p) := s.inProgress? then
    if k' == k then
      let _ ← IO.wait p.result!
  return (← stateRef.get).records[k]?

def noteCommit : BaseIO Unit :=
  stateRef.modify fun s => { s with nCommitted := s.nCommitted + 1 }

def noteReject (reason : String) : BaseIO Unit :=
  stateRef.modify fun s =>
    let rejections := if s.rejections.size < 40 then s.rejections.push reason else s.rejections
    { s with nRejected := s.nRejected + 1, rejections }

/-- Module-level extensions (entries are about the module, not about declarations): a read of them in
E0 cannot have observed anything the late modules add. -/
def moduleLevelExts : List Name :=
  [`Lean.modPkgExt, `Lean.moduleDocExt, `Lean.exportedAxiomsExt, `Lean.extraModUsesExt]

/-- How a declaration-keyed extension's exported entries name the declaration they are about. -/
inductive DeclKeyed where
  | /-- `Name` -/ tag
  | /-- `Name × _`, or a structure whose first field is the name -/ pair
  | /-- `ScopedEnvExtension.Entry (Name × _)` -/ scopedPair

/-- Declaration-keyed extensions: entries about the exporting module's own declarations are harmless
for a speculative command (it cannot have looked those names up without a recorded miss); entries
about older declarations (`attribute [...] olderDecl` in the late module) invalidate any command that
read the extension. Extensions not listed here invalidate on any read when the late modules export entries. -/
def declKeyedExts : List (Name × DeclKeyed) :=
  [(`reducibilityCore, .pair), (`reducibilityExtra, .scopedPair), (`Lean.auxRecExt, .tag),
   (`Lean.noConfusionExt, .pair), (`Lean.projectionFnInfoExt, .pair), (`Lean.auxParentProjInfoExt, .pair),
   (`Lean.Meta.Match.matcherLikeExt, .tag), (`Lean.Elab.PartialFixpoint.eqnInfoExt, .pair),
   (`Lean.Elab.Structural.eqnInfoExt, .pair), (`Lean.Elab.WF.eqnInfoExt, .pair), (`Lean.declRangeExt, .pair),
   (`Lean.protectedExt, .tag), (`Lean.noncomputableExt, .tag), (`Lean.docStringExt, .pair),
   (`Lean.classExtension, .pair), (`Lean.Meta.Match.Extension.extension, .pair)]

/-- The exported entries of `ext` from module `i`, as a raw array (the caller knows the entry type). -/
private def rawEntries (data : ModuleData) (ext : Name) : Array EnvExtensionEntry :=
  match data.entries.find? (·.1 == ext) with
  | some (_, es) => es
  | none => #[]

private unsafe def castEntriesUnsafe {α : Type} (es : Array EnvExtensionEntry) : Array α := unsafeCast es
@[implemented_by castEntriesUnsafe] private opaque castEntries {α : Type} (_es : Array EnvExtensionEntry) : Array α

private def entryNames (kind : DeclKeyed) (es : Array EnvExtensionEntry) : Array Name :=
  match kind with
  | .tag => castEntries (α := Name) es
  | .pair => (castEntries (α := Name × Unit) es).map (·.1)
  | .scopedPair => (castEntries (α := ScopedEnvExtension.Entry (Name × Unit)) es).map fun
    | .global (n, _) => n
    | .scoped _ (n, _) => n

def computeDelta (env : Environment) (env0Modules : Array Name) : DeltaInfo := Id.run do
  let old : NameSet := env0Modules.foldl (·.insert ·) {}
  let mut d : DeltaInfo := {}
  for h : i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if old.contains m then continue
    d := { d with modules := d.modules.push m }
    let data := env.header.moduleData[i]!
    for n in data.constNames do d := { d with newConsts := d.newConsts.insert n }
    for n in data.extraConstNames do d := { d with newConsts := d.newConsts.insert n }
    for (e, es) in data.entries do
      if es.size > 0 then d := { d with exts := d.exts.insert e }
    for n in (castEntries (α := Name) (rawEntries data `Lean.namespacesExt)) do
      d := { d with newNs := d.newNs.insert n }
    for e in (castEntries (α := ScopedEnvExtension.Entry InstanceEntry) (rawEntries data `Lean.Meta.instanceExtension)) do
      match e with
      | .global v | .scoped _ v => d := { d with instKeys := d.instKeys.push v.keys }
  -- declaration-keyed extensions whose entries are all about the late modules' own declarations are harmless
  for (e, kind) in declKeyedExts do
    if d.exts.contains e then
      let mut ownOnly := true
      for h : i in [:env.header.moduleNames.size] do
        if old.contains env.header.moduleNames[i] then continue
        for n in entryNames kind (rawEntries env.header.moduleData[i]! e) do
          if !d.newConsts.contains n then ownOnly := false
      if ownOnly then d := { d with exts := d.exts.erase e }
  return d

def deltaInfo (env : Environment) : BaseIO DeltaInfo := do
  let s ← stateRef.get
  if let some d := s.deltaInfo? then return d
  let d := computeDelta env s.env0Modules
  stateRef.modify fun s => { s with deltaInfo? := some d }
  return d

/-- Index just after the subtree rooted at `i` in a pre-order key path. -/
private def skipSubtree (ks : Array InstanceKey) (i : Nat) : Nat := Id.run do
  let mut n := 1
  let mut i := i
  while n > 0 && i < ks.size do
    n := n - 1 + ks[i]!.arity
    i := i + 1
  return i

/-- Whether a query key path (mvars as stars) can unify with an entry's key path (its mvars as
stars): a star on either side matches the other side's subtree, otherwise keys must agree.
`.other` and `.arrow` are treated like stars on both sides (conservative). -/
partial def keysUnify (q e : Array InstanceKey) : Bool :=
  go 0 0
where
  go (i j : Nat) : Bool :=
    if i ≥ q.size || j ≥ e.size then i ≥ q.size && j ≥ e.size
    else
      match q[i]!, e[j]! with
      | .star, _ => go (i + 1) (skipSubtree e j)
      | _, .star => go (skipSubtree q i) (j + 1)
      | .other, _ | .arrow, _ => go (i + 1) (skipSubtree e j)
      | _, .other | _, .arrow => go (skipSubtree q i) (j + 1)
      | a, b => a == b && go (i + 1) (j + 1)

/-- `none` if the record's read set is disjoint from what the late modules add, else the reason. -/
def validate (d : DeltaInfo) (r : ExampleRec) : Option String := Id.run do
  -- new notation/syntax can change how any later command parses: no reuse at all after such a late module
  if d.exts.contains `Lean.Parser.parserExtension then return some "parser"
  for n in r.misses do
    if d.newConsts.contains n then return some s!"miss {n}"
  for n in r.added do
    if d.newConsts.contains n then return some s!"added {n}"
  for n in r.nsMisses do
    if d.newNs.contains n then return some s!"namespace {n}"
  for e in r.exts do
    if e == `Lean.Meta.instanceExtension || e == `Lean.namespacesExt || moduleLevelExts.contains e then continue
    if d.exts.contains e then return some s!"ext {e}"
  for q in r.instQueries do
    for ks in d.instKeys do
      if keysUnify q ks then return some s!"instance {repr ks}"
  return none

end Lean.Elab.SpecStore
