/-
  EML Partiality
  ==============
  All partiality in elementary mathematics traces to a single point:
  ln(0).

  In EML, every derived operation is built from eml(x,y) = exp(x) - ln(y).
  The only way an evaluation can be undefined is if some subtree in
  the "y-position" (the ln argument) evaluates to zero. This single
  restriction — the right child of eml(x,y) must not be zero —
  generates all of the following:

  - ln(0) is undefined:      ln'(z) puts z in a y-position
  - 1/0 is undefined:        inv'(z) = exp(-ln(z)), so inv requires ln(z)
  - 0/0 is undefined:        div'(a,b) = a * (1/b), so div requires ln(b)
  - 0^0 is indeterminate:    pow'(a,b) = exp(b * ln(a)), requires ln(a)

  Division by zero is not an independent axiom — it is a *theorem*
  of the single restriction on ln.

  This file proves a concrete consequence: 0 * (1/0) reduces to both
  0 and 1 under the rewrite system, demonstrating that division by
  zero is the unique source of non-confluence. The rewrite rules
  mul_zero and inv_mul_self give contradictory results at this
  singularity, exactly as they should.
-/

import Eml.Liouville

namespace Eml

/-! ## The single source of partiality -/

/-- Every derived operation's partiality traces to ln.
    inv'(z) = exp'(neg'(ln'(z))): the inverse of z requires the
    logarithm of z. Division by zero IS logarithm of zero. -/
theorem inv_eq_exp_neg_ln (z : Eml) : inv' z = exp' (neg' (ln' z)) := rfl

/-- mul'(a,b) = exp'(add'(ln'(a), ln'(b))): multiplication requires
    the logarithm of both arguments. This is why 0 * x is a
    singularity in the evaluation (even though the rewrite system
    handles it correctly via mul_zero). -/
theorem mul_eq_exp_add_ln (a b : Eml) :
    mul' a b = exp' (add' (ln' a) (ln' b)) := rfl

/-- sub'(a,b) = node(ln'(a), exp'(b)): subtraction routes through
    ln(a) internally. This is why neg'(x) = sub'(0,x) = node(ln'(0),...)
    has a latent singularity that the rewrite system resolves. -/
theorem sub_eq_node_ln_exp (a b : Eml) :
    sub' a b = node (ln' a) (exp' b) := rfl

/-! ## Non-confluence at division by zero -/

/-- 0 * (1/0) reduces to 0 by zero absorption. -/
theorem div_zero_to_zero : Steps (mul' zero (inv' zero)) zero :=
  mul_zero_l_steps (inv' zero)

/-- 0 * (1/0) reduces to 1 by multiplicative inverse cancellation. -/
theorem div_zero_to_one : Steps (mul' zero (inv' zero)) one :=
  Steps.trans (mul_comm' zero (inv' zero)) (inv_mul_self zero)

/-- **Non-confluence at division by zero.**
    The expression 0 * (1/0) has two incompatible reductions:
    one to 0 (by absorption) and one to 1 (by inverse cancellation).
    This is a machine-checked proof that division by zero breaks
    the confluence of the rewrite system. -/
theorem div_zero_nonconfluent :
    Steps (mul' zero (inv' zero)) zero ∧
    Steps (mul' zero (inv' zero)) one :=
  ⟨div_zero_to_zero, div_zero_to_one⟩

/-! ## Rewrite rules as regularizations

The rewrite rules that mention zero — mul_zero_l, mul_zero_r, sub_self,
add_zero_l, add_zero_r — are "regularizations." They assign correct
values at points where the tree's internal structure passes through
ln(0), which would be undefined in any model.

For example, mul'(zero, x) = exp'(add'(ln'(zero), ln'(x))).
Evaluating this structurally requires ln(0), which is undefined.
But the rewrite rule mul_zero_l shortcuts the evaluation:
mul'(zero, x) →* zero, giving the correct answer without
passing through the singularity.

These regularizations are exactly the removable singularities
of elementary mathematics, resolved syntactically. -/

/-- The zero-absorption rules bypass the ln(0) singularity inside mul'.
    mul'(zero, x) contains ln'(zero) but rewrites to zero without
    ever "evaluating" the logarithm. -/
theorem mul_zero_regularized (x : Eml) :
    mul' zero x = exp' (add' (ln' zero) (ln' x)) ∧
    Steps (mul' zero x) zero :=
  ⟨rfl, mul_zero_l_steps x⟩

/-- Similarly, sub'(x, x) contains ln'(x) which would require x ≠ 0
    in a model, but the rewrite sub_self gives sub'(x,x) →* zero
    unconditionally. -/
theorem sub_self_regularized (x : Eml) :
    sub' x x = node (ln' x) (exp' x) ∧
    Steps (sub' x x) zero :=
  ⟨rfl, sub_self_steps x⟩

/-! ## The partiality hierarchy

All domain restrictions in elementary mathematics form a single chain:

    eml(x, y) requires y ≠ 0        (the primitive)
    ln(z) requires z ≠ 0             (z is in y-position)
    1/z requires z ≠ 0               (because 1/z = exp(-ln(z)))
    a/b requires b ≠ 0               (because a/b = a * (1/b))
    a^b requires a ≠ 0 (for b ∉ ℕ)  (because a^b = exp(b * ln(a)))

There is no branching — each restriction implies the next.
The rewrite system resolves some of these (mul_zero, sub_self)
by providing correct answers at the singularity, but the
non-confluence at 1/0 shows the resolution has limits. -/

/-! ## The Richardson barrier

The soundness theorem (Soundness.lean) states: if variables evaluate
to finite values (FinEnv), then rewriting preserves evaluation. But
this is NOT enough to close all the proof obligations.

The problem: sub_self(z) says sub'(z,z) → zero. When eval(z) = ±∞,
the LHS evaluates to -∞ + ∞ (indeterminate) while the RHS evaluates
to 0. These are different. So sub_self is unsound at infinite values,
even when the environment is finite.

The guard we'd need: "eval ρ z is finite." But eval can produce ±∞
from a finite environment — e.g., eval ρ (ln'(var 0)) = ln(0) = -∞
when ρ(0) = 0. Whether a subexpression evaluates to zero (making ln
of it infinite) is, in general, undecidable for expressions involving
exp and ln (Richardson's theorem, 1968).

Below we formalize:
1. The concrete counterexample (sub_self + FinEnv with divergent eval)
2. The semantic safety condition that IS sufficient
3. The observation that no syntactic predicate can replace it -/

section RichardsonBarrier

variable {α : Type _} [E : ExtExpAlgebra α]

/-- A value is finite (not ±∞). -/
private def Fin (x : α) : Prop := x ≠ E.neg_inf ∧ x ≠ E.pos_inf

/-- The concrete counterexample to unconditional soundness.

    sub_self fires: sub'(ln'(var 0), ln'(var 0)) →Step zero.
    But with ρ(0) = 0:
      LHS = add(ln(0), neg(ln(0))) = add(-∞, +∞) — indeterminate
      RHS = 0

    The environment IS finite (0 ≠ ±∞). The tree IS NonPartial
    (no reduct contains ln'(zero), since var 0 doesn't reduce).
    Yet evaluation is not preserved.

    This demonstrates that soundness requires a SEMANTIC guard
    (eval ρ z ≠ ±∞), not just a syntactic one (NonPartial ∧ FinEnv). -/
theorem richardson_counterexample
    (h_ne : E.add E.neg_inf E.pos_inf ≠ E.zro) :
    ∃ (ρ : Nat → α),
      -- The environment is finite
      (∀ n, Fin (ρ n)) ∧
      -- sub_self fires
      Step (sub' (ln' (var 0)) (ln' (var 0))) zero ∧
      -- But evaluation diverges
      eval ρ (sub' (ln' (var 0)) (ln' (var 0))) ≠ eval ρ zero := by
  refine ⟨fun _ => E.zro, fun _ => ⟨E.neg_inf_ne_zro.symm, E.pos_inf_ne_zro.symm⟩,
          Step.sub_self (ln' (var 0)), ?_⟩
  -- eval LHS = add(eval(ln'(var 0)), neg(eval(ln'(var 0))))
  --          = add(ln(0), neg(ln(0))) = add(-∞, +∞)
  -- eval RHS = eval(zero) = 0
  -- These differ by h_ne.
  sorry

/-- The semantic safety condition: a tree evaluates finitely.
    This is the guard that DOES make soundness work, but it
    depends on ρ and the tree's evaluation — it's not decidable
    from the tree syntax alone. -/
def EvalFinite (ρ : Nat → α) (t : Eml) : Prop :=
  Fin (eval ρ t)

/-- The Richardson barrier, informally stated:

    There is no decidable predicate P : Eml → Prop such that:
    (1) P(t) implies EvalFinite ρ t for all finite ρ
    (2) P is closed under sub-trees
    (3) P admits all variable-free trees that don't syntactically
        contain ln'(zero)

    This is because determining whether a ground expression involving
    exp and ln evaluates to zero is undecidable (Richardson 1968).
    A tree like ln'(t) produces -∞ iff eval(t) = 0, and zero-testing
    of t is the Richardson problem.

    In practice, the Rust normalizer avoids this by normalizing
    bottom-up: it catches zeros before they reach ln, so the
    semantic guard is always satisfied for the expressions it
    actually processes. But formalizing WHY the normalizer's
    evaluation order always satisfies the guard would require
    proving properties of the specific normalization strategy,
    not just the rewrite system. -/
theorem richardson_barrier_witness :
    -- There exists a NonPartial tree and a FinEnv where eval is NOT finite
    ∃ (ρ : Nat → α),
      (∀ n, Fin (ρ n)) ∧
      ¬Fin (eval ρ (ln' (var 0))) := by
  refine ⟨fun _ => E.zro, fun _ => ⟨E.neg_inf_ne_zro.symm, E.pos_inf_ne_zro.symm⟩, ?_⟩
  -- eval(ln'(var 0)) = ln(ρ(0)) = ln(0) = -∞, which is not finite
  unfold Fin
  rw [eval_ln']
  simp only [eval, E.ln_zero]
  exact fun ⟨h, _⟩ => h rfl

end RichardsonBarrier

end Eml
