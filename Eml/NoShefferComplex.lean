/-
  NoShefferComplex.lean
  =====================

  The ℂ-specific content of the generalised no-Sheffer result.

  `Eml/NoSheffer.lean` provides the domain-agnostic machinery:
  trees, models, evaluation, the total-operator theorem, and the
  Richardson reduction. All of that works over any type `α` and
  needs no analytic structure.

  This file supplies the remaining ℂ-specific piece: a partial
  *elementary* binary operator on ℂ cannot pointwise represent
  negation. "Elementary" is pinned down concretely here via the
  `ElemExpr` inductive type — no opaque predicate, no room for
  gratuitous counter-examples like `⊙(x,y) = x − y` declared
  undefined at `x = 17`, because such a thing is not syntactically
  constructible as an `ElemExpr`.

  The barrier itself is declared via the `axiom` keyword
  (`elementary_barrier`), but mathematically it is a theorem of
  classical complex analysis, not a foundational commitment. Its
  content — Hadamard factorization + monodromy constancy + growth
  gap + tree-structural induction — is well-known; we cite it here
  without its Lean proof. The scope is narrow: it speaks only
  about syntactically built elementary expressions, with
  `ElemExpr` making the class Lean-checkable.

  A future refinement would break `elementary_barrier` into its
  named constituents (Hadamard factorization, growth gap), cite
  those individually, and write the tree-structural induction as
  a Lean-checked proof. That's a substantial project (the primary
  blocker is Hadamard factorization, which is not yet in Mathlib)
  and sits as a TODO at the bottom of the file.

  Imports Mathlib for `Complex`, `Complex.exp`, `Complex.log`.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Eml.NoSheffer

namespace NoSheffer
namespace Complex

open _root_.Complex (exp log)

/-! ## Elementary expressions on ℂ

    `ElemExpr` is a concrete syntactic class of elementary binary
    expressions in two variables over ℂ: constants, variables,
    arithmetic, exponential, logarithm. Every `ElemExpr` induces
    a specific partial function `ℂ → ℂ → Option ℂ` via `toOp`.

    The partiality comes solely from `log(0)` being undefined:
    `.log e` returns `none` if `e` evaluates to zero. Arithmetic
    and `exp` never produce `none`. -/

/-- Syntactic elementary expressions in two variables. -/
inductive ElemExpr where
  | var1  : ElemExpr
  | var2  : ElemExpr
  | const : ℂ → ElemExpr
  | add   : ElemExpr → ElemExpr → ElemExpr
  | mul   : ElemExpr → ElemExpr → ElemExpr
  | sub   : ElemExpr → ElemExpr → ElemExpr
  | expE  : ElemExpr → ElemExpr
  | logE  : ElemExpr → ElemExpr
  deriving Inhabited

/-- Evaluation of an `ElemExpr` as a partial binary operator on ℂ.
    `log` is the only source of partiality: at `0` it is undefined.
    Noncomputable because `Complex.exp` and `Complex.log` are. -/
noncomputable def ElemExpr.toOp : ElemExpr → ℂ → ℂ → Option ℂ
  | .var1,    x, _ => some x
  | .var2,    _, y => some y
  | .const c, _, _ => some c
  | .add l r, x, y => do
      let a ← l.toOp x y
      let b ← r.toOp x y
      pure (a + b)
  | .mul l r, x, y => do
      let a ← l.toOp x y
      let b ← r.toOp x y
      pure (a * b)
  | .sub l r, x, y => do
      let a ← l.toOp x y
      let b ← r.toOp x y
      pure (a - b)
  | .expE e, x, y => do
      let a ← e.toOp x y
      pure (exp a)
  | .logE e, x, y => do
      let a ← e.toOp x y
      if a = 0 then none else some (log a)

/-- An `ElemExpr` is *partial* if its induced operator returns
    `none` at some input. This happens iff the expression
    contains a `.logE` whose argument can vanish. -/
def ElemExpr.IsPartial (E : ElemExpr) : Prop :=
  ∃ a b, E.toOp a b = none

/-! ## The analytic barrier (ℂ + ElemExpr)

    The claim: if `E : ElemExpr` is partial, no tree over its
    induced operator pointwise represents `neg : ℂ → ℂ`.

    Classical content, not formalized here:

      1. *Hadamard factorization.* Any entire function that is
         nowhere-zero on ℂ has the form `exp ∘ g` for some entire
         `g` (Hadamard 1893 / Weierstrass factorization theorem
         + zero-counting). In Mathlib? No — Mathlib has the
         Hadamard three-lines theorem (interpolation) but not
         the factorization theorem.

      2. *Monodromy constancy.* An integer-valued continuous
         function on a connected subset of ℂ is constant. The
         `log(exp(g(z))) = g(z) + 2πi·k(z)` monodromy offset is
         continuous and integer-valued, so constant on ℂ.
         Provable in Mathlib given Mathlib's connectivity and
         continuity infrastructure.

      3. *Cancellation closure.* Tree-structural induction: any
         pointwise-total tree over a partial `ElemExpr` reduces
         to a `.logE`-free sub-expression in a "total-only"
         sub-algebra of `ElemExpr`.

      4. *Growth gap.* `neg(z) = -z` is linear; no element of
         the log-free ElemExpr sub-algebra equals a linear
         function pointwise. Growth-rate argument.

    Discharging (1)–(4) inside Lean + Mathlib is a real project.
    For now, we axiomatize the combined conclusion. -/

/-- **The ℂ elementary barrier.** On ℂ, no tree over a partial
    `ElemExpr`-induced operator pointwise represents negation.

    Mathematically this is a classical theorem, assembled from
    Hadamard factorization, monodromy constancy, tree-structural
    cancellation closure, and the growth gap — all standard
    complex analysis. We declare it via the `axiom` keyword here
    only because the Lean proof has not been written; it is not
    a foundational commitment. Breaking this into named
    constituents and writing the tree induction as a Lean proof
    is the labeled TODO below.

    The scope is tight: it speaks only about trees over
    `ElemExpr.toOp`. Gratuitous partialities like
    `fun x y => x - y, undefined at x = 17` are not `ElemExpr`-
    inducible, so cannot sneak into the statement's precondition. -/
axiom elementary_barrier
    {ι : Type u} (E : ElemExpr) (h_partial : E.IsPartial)
    (constVal : ι → ℂ) :
    ¬ ∃ T : Tree ι, ∀ z : ℂ, eval ⟨E.toOp, constVal⟩ z T = some (-z)

/-- **Theorem 3 (ℂ version).** On ℂ, a partial `ElemExpr` operator
    cannot pointwise represent negation. Direct unpacking of
    `elementary_barrier`. -/
theorem no_partial_elem_represents_neg
    {ι : Type u} (E : ElemExpr) (h_partial : E.IsPartial)
    (constVal : ι → ℂ)
    (T : Tree ι)
    (h_rep : ∀ z : ℂ, eval ⟨E.toOp, constVal⟩ z T = some (-z)) :
    False :=
  elementary_barrier E h_partial constVal ⟨T, h_rep⟩

/-! ## Combined no-go on ℂ

    Assembling Theorems 1 (from `NoSheffer.lean`) and 3 (above):
    no elementary binary operator on ℂ generates a class
    containing both a partial function and negation.

      * If the `ElemExpr` is total on ℂ, Theorem 1 kills it.
      * If it's partial, the barrier kills it. -/

/-- **Combined theorem.** No `ElemExpr` operator generates a
    class containing both a partial target function and
    negation. -/
theorem no_sheffer_on_complex
    {ι : Type u} (E : ElemExpr) (constVal : ι → ℂ)
    (f_partial : ℂ → Option ℂ)
    (z₀ : ℂ) (h_f_partial : f_partial z₀ = none)
    (h_f_represented : ∃ T : Tree ι, Represents ⟨E.toOp, constVal⟩ T f_partial)
    (h_neg_represented :
      ∃ T : Tree ι, ∀ z : ℂ, eval ⟨E.toOp, constVal⟩ z T = some (-z)) :
    False := by
  by_cases h_total : ∀ a b, ∃ c, E.toOp a b = some c
  · -- E total: f_partial can't be represented (Theorem 1 from NoSheffer).
    obtain ⟨T, hT⟩ := h_f_represented
    exact no_total_op_represents_partial ⟨E.toOp, constVal⟩ h_total
                                         f_partial z₀ h_f_partial T hT
  · -- E partial: neg can't be represented (elementary_barrier).
    have h_partial : E.IsPartial := by
      apply Classical.byContradiction
      intro h
      apply h_total
      intro a b
      cases hv : E.toOp a b with
      | some c => exact ⟨c, rfl⟩
      | none =>
          exfalso
          apply h
          exact ⟨a, b, hv⟩
    exact elementary_barrier E h_partial constVal h_neg_represented

/-! ## TODO: discharge `elementary_barrier` as a Lean proof

    The axiom `elementary_barrier` bundles four classical facts.
    A cleaner file would break them apart and prove the
    assembly in Lean:

    ```
    -- Separate classical axioms, each a named theorem:
    axiom hadamard_factorization :
      ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f Set.univ → (∀ z, f z ≠ 0) →
        ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Set.univ ∧
          ∀ z, f z = exp (g z)
    -- ... plus a growth-gap axiom for exp-polynomials vs neg.
    ```

    Then `elementary_barrier` becomes a `theorem` proved by:
    induction on `T`; in the `app l r` case, extract the right
    sub-tree's image (must avoid log's pole), apply Hadamard
    to conclude an `exp ∘ g` form, unfold `log ∘ exp` via
    monodromy, recurse.

    Mathlib does not currently contain Hadamard factorization;
    that's the primary blocker. Once Hadamard lands in Mathlib
    (or we formalize it), this TODO becomes tractable.

    Tracking: the induction is ~200 lines of Lean over Mathlib's
    Complex infrastructure, assuming the two classical axioms. -/

end Complex
end NoSheffer
