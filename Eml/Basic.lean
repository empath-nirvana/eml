/-
  EML Tree Algebra
  ================
  A foundational representation of elementary functions as binary trees
  over a single operator eml(x, y) = exp(x) - ln(y), the constant 1,
  and the extended constants -∞ and +∞.

  Based on: Odrzywołek, "All elementary functions from a single operator" (2026)

  Key insight: we work purely at the tree level. No exp or ln is ever
  evaluated. Branch cuts do not exist in this algebra. The trees are
  syntactic objects; rewrite rules are structural transformations.

  The extended constants -∞ and +∞ model the single point of partiality
  in elementary mathematics: ln(0) = -∞, exp(-∞) = 0, and -∞ + ∞ is
  the unique indeterminate form (corresponding to 0·∞, 0/0, etc.).
-/

/-- The fundamental type: an EML tree.
    Every elementary function has a finite representation as an `Eml` term.
    Grammar: S → 1 | -∞ | +∞ | xₙ | eml(S, S) -/
inductive Eml where
  | one    : Eml
  | negInf : Eml
  | posInf : Eml
  | var    : Nat → Eml
  | node   : Eml → Eml → Eml
  deriving Repr, BEq, Inhabited, DecidableEq

namespace Eml

-- Convenient notation
scoped notation "𝟏" => Eml.one
scoped notation "eml(" l ", " r ")" => Eml.node l r

instance : OfNat Eml 1 where ofNat := .one

/-- An atom is a non-variable leaf: 1, -∞, or +∞. -/
def isAtom : Eml → Bool
  | one | negInf | posInf => true
  | _ => false

/-- A tree is infinite if it is ±∞. -/
def isInfinite : Eml → Bool
  | negInf | posInf => true
  | _ => false

/-- Number of internal (eml) nodes. -/
def nodes : Eml → Nat
  | one | negInf | posInf => 0
  | var _   => 0
  | node l r => 1 + l.nodes + r.nodes

/-- Number of leaves (1s, ±∞, and variables). -/
def leaves : Eml → Nat
  | one | negInf | posInf => 1
  | var _   => 1
  | node l r => l.leaves + r.leaves

/-- Tree depth. -/
def depth : Eml → Nat
  | one | negInf | posInf => 0
  | var _   => 0
  | node l r => 1 + max l.depth r.depth

/-- Substitute a variable for a subtree. -/
def subst (t : Eml) (x : Nat) (s : Eml) : Eml :=
  match t with
  | one      => one
  | negInf   => negInf
  | posInf   => posInf
  | var n    => if n == x then s else var n
  | node l r => node (l.subst x s) (r.subst x s)

/-- Check if a tree contains a given variable. -/
def hasVar (t : Eml) (x : Nat) : Bool :=
  match t with
  | one | negInf | posInf => false
  | var n    => n == x
  | node l r => l.hasVar x || r.hasVar x

/-- Check if a tree is ground (no variables). -/
def isGround : Eml → Bool
  | one | negInf | posInf => true
  | var _    => false
  | node l r => l.isGround && r.isGround

/-- Count total variable occurrences. -/
def varCount : Eml → Nat
  | one | negInf | posInf => 0
  | var _    => 1
  | node l r => l.varCount + r.varCount

-- Basic structural theorems

theorem leaves_pos : ∀ t : Eml, 0 < t.leaves := by
  intro t
  induction t with
  | one => simp [leaves]
  | negInf => simp [leaves]
  | posInf => simp [leaves]
  | var _ => simp [leaves]
  | node l r ihl ihr => simp [leaves]; omega

theorem leaves_eq_nodes_succ : ∀ t : Eml, t.leaves = t.nodes + 1 := by
  intro t
  induction t with
  | one => simp [leaves, nodes]
  | negInf => simp [leaves, nodes]
  | posInf => simp [leaves, nodes]
  | var _ => simp [leaves, nodes]
  | node l r ihl ihr => simp [leaves, nodes, ihl, ihr]; omega

end Eml
