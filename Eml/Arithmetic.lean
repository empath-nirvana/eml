/-
  EML Arithmetic
  ==============
  Substitution, the product rule, and evaluation of derivatives
  at specific points.

  The headline result: a machine-checked proof that f'(3) = 6 for
  f(x) = x². This chains together symbolic differentiation (D(x²) →* x+x),
  substitution (x ↦ 3), and arithmetic (3 + 3 →* 6).
-/

import Eml.Liouville

namespace Eml

/-! ## Substitution preserves rewriting -/

/-- One-step rewrites are preserved under substitution.
    Each rewrite rule is a structural pattern that works regardless
    of what subtrees contain. -/
theorem Step.subst_compat {a b : Eml} (h : Step a b) (n : Nat) (s : Eml) :
    Step (a.subst n s) (b.subst n s) := by
  induction h with
  | exp_ln z => exact .exp_ln (z.subst n s)
  | ln_exp z => exact .ln_exp (z.subst n s)
  | sub_zero z => exact .sub_zero (z.subst n s)
  | sub_self z => exact .sub_self (z.subst n s)
  | add_zero_l z => exact .add_zero_l (z.subst n s)
  | add_zero_r z => exact .add_zero_r (z.subst n s)
  | mul_one_l z => exact .mul_one_l (z.subst n s)
  | mul_one_r z => exact .mul_one_r (z.subst n s)
  | mul_zero_l z => exact .mul_zero_l (z.subst n s)
  | mul_zero_r z => exact .mul_zero_r (z.subst n s)
  | neg_neg z => exact .neg_neg (z.subst n s)
  | inv_inv z => exact .inv_inv (z.subst n s)
  | exp_add a b => exact .exp_add (a.subst n s) (b.subst n s)
  | ln_mul a b => exact .ln_mul (a.subst n s) (b.subst n s)
  | mul_add a b c => exact .mul_add (a.subst n s) (b.subst n s) (c.subst n s)
  | ln_one => exact .ln_one
  | exp_zero => exact .exp_zero
  | add_assoc a b c => exact .add_assoc (a.subst n s) (b.subst n s) (c.subst n s)
  | add_comm a b => exact .add_comm (a.subst n s) (b.subst n s)
  | cancel_exp_ln z => exact .cancel_exp_ln (z.subst n s)
  | cancel_ln_exp z => exact .cancel_ln_exp (z.subst n s)
  | node_l a a' b _ ih => exact .node_l _ _ _ ih
  | node_r a b b' _ ih => exact .node_r _ _ _ ih

/-- Rewrite chains are preserved under substitution. -/
theorem Steps.subst_compat {a b : Eml} (h : Steps a b) (n : Nat) (s : Eml) :
    Steps (a.subst n s) (b.subst n s) := by
  induction h with
  | refl _ => exact Steps.refl _
  | step a' b' c hab _ ih => exact Steps.step _ _ _ (hab.subst_compat n s) ih

/-! ## D(x²) = x + x -/

/-- **D(x²) →* x + x**, proved from chain rules, distributivity,
    and cancellation.

    Chain:
      D(x·x) = D(exp(ln x + ln x))
      →* (x·x) · D(ln x + ln x)                    [exp chain rule]
      →* (x·x) · (1/x + 1/x)                       [sum rule + ln derivative]
      →* (x·x)·(1/x) + (x·x)·(1/x)                [distributivity]
      →* x + x                                       [(a·b)·(1/a) →* b, twice]  -/
theorem diff_x_squared :
    Steps (diff (mul' (var 0) (var 0)) 0) (add' (var 0) (var 0)) :=
  -- D(exp'(add'(ln' x, ln' x))) →* mul'(x², D(add'(ln' x, ln' x)))
  Steps.trans (diff_exp_general (add' (ln' (var 0)) (ln' (var 0))) 0)
  -- →* mul'(x², add'(D(ln x), D(ln x)))
  (Steps.trans (Steps.mul'_r (diff_add_general (ln' (var 0)) (ln' (var 0)) 0))
  -- →* mul'(x², add'(1/x, D(ln x)))
  (Steps.trans (Steps.mul'_r (Steps.add'_l (diff_ln_var 0)))
  -- →* mul'(x², add'(1/x, 1/x))
  (Steps.trans (Steps.mul'_r (Steps.add'_r (diff_ln_var 0)))
  -- →* add'(mul'(x², 1/x), mul'(x², 1/x))   [distributivity]
  (Steps.trans (Steps.single (Step.mul_add
      (mul' (var 0) (var 0)) (inv' (var 0)) (inv' (var 0))))
  -- →* add'(x, x)   [cancellation: (a·b)·(1/a) →* b]
  (Steps.add'_both
    (mul_cancel_left (var 0) (var 0))
    (mul_cancel_left (var 0) (var 0)))))))

/-! ## f'(3) = 6 for f(x) = x² -/

/-- **f'(3) = 6 for f(x) = x², machine-checked.**

    This chains together three independently proved results:
    1. **Symbolic differentiation**: D(x²) →* x + x
    2. **Substitution compatibility**: if a →* b then a[x:=3] →* b[x:=3]
    3. **Arithmetic**: 3 + 3 →* 6

    The proof computes the derivative of x² symbolically, substitutes
    x = 3 into the simplified form, and reduces the result to the
    canonical tree for 6. No evaluation — pure tree rewriting. -/
theorem deriv_x_squared_at_3 :
    Steps ((diff (mul' (var 0) (var 0)) 0).subst 0 (ofNat' 3)) (ofNat' 6) :=
  Steps.trans (diff_x_squared.subst_compat 0 (ofNat' 3)) (add_ofNat' 3 3)

end Eml
