/-
  EML Rewrite System
  ==================
  Equational axioms for the EML tree algebra, expressed as rewrite rules.

  These rules are the "Peano axioms" of this system. They define which
  trees are considered equivalent without ever evaluating exp or ln.

  The rules fall into categories:
  1. Cancellation: exp∘ln and ln∘exp annihilate
  2. Identity: adding zero, multiplying by one
  3. Annihilation: multiplying by zero
  4. Involution: double negation, double reciprocal

  Soundness means: if two trees are related by these rules, they compute
  the same function (when evaluated). But we never need to evaluate to
  apply the rules -- they are purely syntactic.
-/

import Eml.Constructors

namespace Eml

/-! ## Structural pattern matching helpers -/

/-- Recognize the exp' pattern: eml(z, 1) -/
def isExp? : Eml → Option Eml
  | node z one => some z
  | _          => none

/-- Recognize the ln' pattern: eml(1, eml(eml(1, z), 1)) -/
def isLn? : Eml → Option Eml
  | node one (node (node one z) one) => some z
  | _ => none

/-- Recognize the sub' pattern: eml(ln'(x), exp'(y)) = eml(ln'(x), eml(y, 1)) -/
def isSub? : Eml → Option (Eml × Eml)
  | node lnx (node y one) =>
    match lnx.isLn? with
    | some x => some (x, y)
    | none   => none
  | _ => none

/-! ## One-step rewrite relation (propositional) -/

/-- Axiomatic one-step rewrites on EML trees.
    These are the foundational equalities of the algebra. -/
inductive Step : Eml → Eml → Prop where
  -- Cancellation laws
  -- NOTE: exp_ln is unguarded here but the axiom is inconsistent at z = -∞.
  -- See Soundness.lean for the full note. The KB analysis revealed this gap.
  | exp_ln  (z : Eml) : Step (exp' (ln' z)) z
  | ln_exp  (z : Eml) : Step (ln' (exp' z)) z

  -- Subtraction identities
  | sub_zero  (z : Eml) : Step (sub' z zero) z
  | sub_self  (z : Eml) : Step (sub' z z) zero

  -- Addition identities
  | add_zero_l (z : Eml) : Step (add' zero z) z
  | add_zero_r (z : Eml) : Step (add' z zero) z

  -- Multiplication identities
  | mul_one_l  (z : Eml) : Step (mul' one z) z
  | mul_one_r  (z : Eml) : Step (mul' z one) z
  | mul_zero_l (z : Eml) : Step (mul' zero z) zero
  | mul_zero_r (z : Eml) : Step (mul' z zero) zero

  -- Negation
  | neg_neg   (z : Eml) : Step (neg' (neg' z)) z

  -- Reciprocal
  | inv_inv   (z : Eml) : Step (inv' (inv' z)) z

  -- exp distributes over addition (multiplicativity)
  | exp_add (a b : Eml) : Step (exp' (add' a b)) (mul' (exp' a) (exp' b))

  -- ln of product
  | ln_mul (a b : Eml) : Step (ln' (mul' a b)) (add' (ln' a) (ln' b))

  -- ln(1) = 0
  | ln_one : Step (ln' one) zero

  -- exp(0) = 1
  | exp_zero : Step (exp' zero) one

  -- Distributivity
  | mul_add (a b c : Eml) : Step (mul' a (add' b c)) (add' (mul' a b) (mul' a c))

  -- Associativity / commutativity of addition
  | add_assoc (a b c : Eml) : Step (add' (add' a b) c) (add' a (add' b c))
  | add_comm  (a b : Eml)   : Step (add' a b) (add' b a)

  -- KB completion: partially-cancelled subtractions
  -- These close the sub_self × exp_ln/ln_exp confluence gap.
  -- eml(ln(ln(z)), z) = exp(ln(ln(z))) - ln(z) = ln(z) - ln(z) = 0
  | cancel_exp_ln (z : Eml) : Step (node (ln' (ln' z)) z) zero
  -- eml(z, exp(exp(z))) = exp(z) - ln(exp(exp(z))) = exp(z) - exp(z) = 0
  | cancel_ln_exp (z : Eml) : Step (node z (exp' (exp' z))) zero

  -- Congruence: rewrite inside a node
  | node_l (a a' b : Eml) : Step a a' → Step (node a b) (node a' b)
  | node_r (a b b' : Eml) : Step b b' → Step (node a b) (node a b')

/-- Reflexive-transitive closure: zero or more rewrite steps. -/
inductive Steps : Eml → Eml → Prop where
  | refl  (t : Eml)          : Steps t t
  | step  (a b c : Eml)      : Step a b → Steps b c → Steps a c

/-- Equivalence: two trees rewrite to the same normal form. -/
def Equiv (a b : Eml) : Prop := ∃ c, Steps a c ∧ Steps b c

scoped infix:50 " ≈ₑ " => Equiv

/-! ## Computable simplification -/

/-- Apply one simplification step at the root, returning none if no rule fires.
    This is the computable counterpart of Step.

    Pattern reference (expanded tree forms):
      exp'(z)    = node z one
      ln'(z)     = node one (node (node one z) one)
      zero       = node one (node (node one one) one)
      sub'(a, b) = node (node one (node (node one a) one)) (node b one)
      neg'(z)    = sub'(zero, z)
      add'(a, b) = sub'(a, neg'(b))
      mul'(a, b) = exp'(add'(ln'(a), ln'(b)))
      inv'(z)    = exp'(neg'(ln'(z)))
-/
def simplify1 : Eml → Option Eml
  -- exp(ln(z)) → z
  | node (node one (node (node one z) one)) one => some z
  -- ln(exp(z)) → z
  | node one (node (node one (node z one)) one) => some z
  -- Note: exp(0) → 1 is already handled: zero = ln'(one), so
  -- exp'(zero) = exp'(ln'(one)) matches exp_ln rule above → one.
  -- Similarly ln(1) = zero by definition, no rewrite needed.
  | _ => none

/-- Recognize the mul' pattern: exp'(add'(ln'(a), ln'(b)))
    mul'(a, b) = exp'(sub'(ln'(a), neg'(ln'(b))))
    = node (sub'(ln'(a), neg'(ln'(b)))) one
    The inner sub' has the form: node (ln'(ln'(a))) (exp'(neg'(ln'(b))))
    This is complex, so we look for: node X one where X is a sub'
    whose arguments are ln' patterns. -/
def isMul? (t : Eml) : Option (Eml × Eml) :=
  match t.isExp? with
  | some inner =>
    match inner.isSub? with
    | some (lnA, negLnB) =>
      match lnA.isLn? with
      | some a =>
        -- negLnB should be neg'(ln'(b)) = sub'(zero, ln'(b))
        match negLnB.isSub? with
        | some (z, lnB) =>
          if z == zero then
            match lnB.isLn? with
            | some b => some (a, b)
            | none => none
          else none
        | none => none
      | none => none
    | none => none
  | none => none

/-- Check if a tree is semantically zero.
    Recognizes: zero (= ln'(one)), and ln(1) in various forms. -/
def isZero (t : Eml) : Bool :=
  t == zero ||
  (match t.isLn? with
   | some z => z == one
   | none => false)

/-- Check if a tree is semantically one. -/
def isOne (t : Eml) : Bool :=
  t == one ||
  (match t.isExp? with
   | some z => isZero z
   | none => false)

/-- Semantic simplification: uses pattern recognizers to identify
    high-level operations and apply algebraic rules, then rebuilds
    the tree. This is more powerful than pure syntactic matching. -/
partial def semanticSimplify : Eml → Eml
  | one    => one
  | negInf => negInf
  | posInf => posInf
  | var n  => var n
  | t =>
    -- First, recursively simplify children
    let t := match t with
      | node l r => node (semanticSimplify l) (semanticSimplify r)
      | other => other
    -- Then try syntactic cancellation
    let t := match simplify1 t with
      | some s => s
      | none   => t
    -- Recognize mul'(a, b) and apply identity/zero rules
    match t.isMul? with
    | some (a, b) =>
      if isOne a then b                       -- 1 * x = x
      else if isOne b then a                  -- x * 1 = x
      else if isZero a || isZero b then zero  -- 0 * x = x * 0 = 0
      else t
    | none =>
    -- Recognize sub'(a, b) and apply rules
    match t.isSub? with
    | some (a, b) =>
      if a == b then zero                     -- x - x = 0
      else if isZero b then a                 -- x - 0 = x
      else if isZero a then neg' b            -- 0 - x = -x
      else t
    | none =>
    -- Recognize exp'(z) patterns
    match t.isExp? with
    | some z =>
      match z.isLn? with
      | some a => a                           -- exp(ln(a)) → a
      | none =>
      if isZero z then one                    -- exp(0) → 1
      else t
    | none =>
    -- Recognize ln'(z)
    match t.isLn? with
    | some z =>
      match z.isExp? with
      | some a => a                           -- ln(exp(a)) → a
      | none =>
      if isOne z then zero                    -- ln(1) → 0
      else t
    | none => t

/-- Recursively try to simplify all subtrees, bottom-up. -/
partial def simplifyOnce : Eml → Eml
  | one     => one
  | negInf  => negInf
  | posInf  => posInf
  | var n   => var n
  | node l r =>
    let l' := simplifyOnce l
    let r' := simplifyOnce r
    let t  := node l' r'
    match simplify1 t with
    | some s => s
    | none   => t

/-- Repeatedly simplify until no more rules fire (or fuel runs out). -/
partial def simplify (t : Eml) (fuel : Nat := 100) : Eml :=
  if fuel == 0 then t
  else
    let t' := semanticSimplify t
    if t' == t then t
    else simplify t' (fuel - 1)

/-! ## Basic equivalence proofs -/

/-- exp(ln(z)) ≈ z -/
theorem exp_ln_equiv (z : Eml) : Steps (exp' (ln' z)) z :=
  Steps.step _ z z (Step.exp_ln z) (Steps.refl z)

/-- ln(exp(z)) ≈ z -/
theorem ln_exp_equiv (z : Eml) : Steps (ln' (exp' z)) z :=
  Steps.step _ z z (Step.ln_exp z) (Steps.refl z)

/-! ## Tests -/

-- exp(ln(x)) should simplify to x
#eval simplify (exp' (ln' (var 0)))

-- ln(exp(x)) should simplify to x
#eval simplify (ln' (exp' (var 0)))

end Eml
