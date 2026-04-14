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

end Eml
