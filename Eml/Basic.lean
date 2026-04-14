/-
  EML Tree Algebra
  ================
  A foundational representation of elementary functions as binary trees
  over a single operator eml(x, y) = exp(x) - ln(y) and a single
  constant 1.

  Based on: Odrzywołek, "All elementary functions from a single operator" (2026)

  Key insight: we work purely at the tree level. No exp or ln is ever
  evaluated. Branch cuts do not exist in this algebra. The trees are
  syntactic objects; rewrite rules are structural transformations.
-/

/-- The fundamental type: an EML tree.
    Every elementary function has a finite representation as an `Eml` term.
    Grammar: S → 1 | xₙ | eml(S, S) -/
inductive Eml where
  | one  : Eml
  | var  : Nat → Eml
  | node : Eml → Eml → Eml
  deriving Repr, BEq, Inhabited, DecidableEq

namespace Eml

-- Convenient notation
scoped notation "𝟏" => Eml.one
scoped notation "eml(" l ", " r ")" => Eml.node l r

instance : OfNat Eml 1 where ofNat := .one

/-- Number of internal (eml) nodes. -/
def nodes : Eml → Nat
  | one     => 0
  | var _   => 0
  | node l r => 1 + l.nodes + r.nodes

/-- Number of leaves (1s and variables). -/
def leaves : Eml → Nat
  | one     => 1
  | var _   => 1
  | node l r => l.leaves + r.leaves

/-- Tree depth. -/
def depth : Eml → Nat
  | one     => 0
  | var _   => 0
  | node l r => 1 + max l.depth r.depth

/-- Substitute a variable for a subtree. -/
def subst (t : Eml) (x : Nat) (s : Eml) : Eml :=
  match t with
  | one      => one
  | var n    => if n == x then s else var n
  | node l r => node (l.subst x s) (r.subst x s)

/-- Check if a tree contains a given variable. -/
def hasVar (t : Eml) (x : Nat) : Bool :=
  match t with
  | one      => false
  | var n    => n == x
  | node l r => l.hasVar x || r.hasVar x

/-- Check if a tree is ground (no variables). -/
def isGround : Eml → Bool
  | one      => true
  | var _    => false
  | node l r => l.isGround && r.isGround

/-- Count total variable occurrences. -/
def varCount : Eml → Nat
  | one      => 0
  | var _    => 1
  | node l r => l.varCount + r.varCount

-- Basic structural theorems

theorem leaves_pos : ∀ t : Eml, 0 < t.leaves := by
  intro t
  induction t with
  | one => simp [leaves]
  | var _ => simp [leaves]
  | node l r ihl ihr => simp [leaves]; omega

theorem leaves_eq_nodes_succ : ∀ t : Eml, t.leaves = t.nodes + 1 := by
  intro t
  induction t with
  | one => simp [leaves, nodes]
  | var _ => simp [leaves, nodes]
  | node l r ihl ihr => simp [leaves, nodes, ihl, ihr]; omega

end Eml
