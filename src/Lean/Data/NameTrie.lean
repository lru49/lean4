/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Data.PrefixTree
import Init.Data.Ord.String

public section

namespace Lean

inductive NamePart
  | str (s : String)
  | num (n : Nat)
  deriving BEq, Inhabited

instance : ToString NamePart where
  toString
    | NamePart.str s => s
    | NamePart.num n => toString n

def NamePart.cmp : NamePart → NamePart → Ordering
  | NamePart.str a, NamePart.str b => compare a b
  | NamePart.num a, NamePart.num b => compare a b
  | NamePart.num _, NamePart.str _ => Ordering.lt
  | _, _ => Ordering.gt

def NamePart.lt : NamePart → NamePart → Bool
  | NamePart.str a, NamePart.str b => a < b
  | NamePart.num a, NamePart.num b => a < b
  | NamePart.num _, NamePart.str _ => true
  | _, _ => false

@[expose] def NameTrie (β : Type u) := PrefixTree NamePart β NamePart.cmp

private def toKey (n : Name) : List NamePart :=
  loop n []
where
  loop
    | Name.str p s,   parts => loop p (NamePart.str s :: parts)
    | Name.num p n,   parts => loop p (NamePart.num n :: parts)
    | Name.anonymous, parts => parts

def NameTrie.insert (t : NameTrie β) (n : Name) (b : β) : NameTrie β :=
  PrefixTree.insert t (toKey n) b

def NameTrie.empty : NameTrie β :=
  PrefixTree.empty

instance : Inhabited (NameTrie β) where
  default := NameTrie.empty

instance : EmptyCollection (NameTrie β) where
  emptyCollection := NameTrie.empty

def NameTrie.find? (t : NameTrie β) (k : Name) : Option β :=
  PrefixTree.find? t (toKey k)

@[inline, inherit_doc PrefixTree.findLongestPrefix?]
def NameTrie.findLongestPrefix? (t : NameTrie β) (k : Name) : Option β :=
  PrefixTree.findLongestPrefix? t (toKey k)

/-- Number of components of `n`, plus `acc`. -/
private def numPartsAux : Name → Nat → Nat
  | .str p _,  acc => numPartsAux p (acc + 1)
  | .num p _,  acc => numPartsAux p (acc + 1)
  | .anonymous, acc => acc

/-- `n` with its last `i` components removed. -/
private def dropLastParts : Name → Nat → Name
  | n,          0     => n
  | .str p _,   i + 1 => dropLastParts p i
  | .num p _,   i + 1 => dropLastParts p i
  | .anonymous, _ + 1 => .anonymous

/-- Compares the last component of `n` with `p` like `NamePart.cmp`, without allocating a `NamePart`. -/
@[inline] private def cmpLastPart (n : Name) (p : NamePart) : Ordering :=
  match n, p with
  | .str _ a, .str b => compare a b
  | .num _ a, .num b => compare a b
  | .num _ _, .str _ => .lt
  | _,        _      => .gt

/--
Returns the subtree of `t` whose root key is the last component of `n`, or `.leaf` if there is none.
Like `TreeMap.Raw.get?` but allocates neither a `NamePart` nor an `Option`.
-/
private def findChildImpl (n : Name) :
    Std.DTreeMap.Internal.Impl NamePart (fun _ => PrefixTreeNode NamePart β NamePart.cmp) →
    Std.DTreeMap.Internal.Impl NamePart (fun _ => PrefixTreeNode NamePart β NamePart.cmp)
  | .leaf => .leaf
  | t@(.inner _ k _ l r) =>
    match cmpLastPart n k with
    | .lt => findChildImpl n l
    | .gt => findChildImpl n r
    | .eq => t

/--
Like `NameTrie.findLongestPrefix?` but walks the components of `k` in place instead of first
converting `k` into a list of `NamePart`s, so that it does not allocate.
-/
def NameTrie.findLongestPrefixName? (t : NameTrie β) (k : Name) : Option β :=
  loop t.val none (numPartsAux k 0)
where
  /-- Mirrors `PrefixTreeNode.findLongestPrefix?.loop`; `i` is the number of components of `k` not
  yet consumed, so the next one is the last component of `dropLastParts k (i - 1)`. -/
  loop : PrefixTreeNode NamePart β NamePart.cmp → Option β → Nat → Option β
    | .Node val _, acc?, 0     => val <|> acc?
    | .Node val m, acc?, i + 1 =>
      match findChildImpl (dropLastParts k i) m.inner.inner with
      | .inner _ _ t _ _ => loop t (val <|> acc?) i
      | .leaf            => val

@[inline]
def NameTrie.foldMatchingM [Monad m] (t : NameTrie β) (k : Name) (init : σ) (f : β → σ → m σ) : m σ :=
  PrefixTree.foldMatchingM t (toKey k) init f

@[inline]
def NameTrie.foldM [Monad m] (t : NameTrie β) (init : σ) (f : β → σ → m σ) : m σ :=
  t.foldMatchingM Name.anonymous init f

@[inline]
def NameTrie.forMatchingM [Monad m] (t : NameTrie β) (k : Name) (f : β → m Unit) : m Unit :=
  PrefixTree.forMatchingM t (toKey k) f

@[inline]
def NameTrie.forM [Monad m] (t : NameTrie β) (f : β → m Unit) : m Unit :=
  t.forMatchingM Name.anonymous f

def NameTrie.matchingToArray (t : NameTrie β) (k : Name) : Array β :=
  Id.run <| t.foldMatchingM k #[] fun v acc => return acc.push v

def NameTrie.toArray (t : NameTrie β) : Array β :=
  Id.run <| t.foldM #[] fun v acc => return acc.push v

end Lean
