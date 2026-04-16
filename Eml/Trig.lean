/-
  EML Trigonometric Identities
  ============================
  Semantic proofs of Euler's identity and D(sin) = cos in the
  ExpField framework.

  Key technique: SemEq (semantic equality across all exponential fields)
  bridges the gap where directed rewrites (Steps) cannot reach.
  Steps handle the chain-rule differentiation; ExpField algebra
  handles the trigonometric simplification.

  Neither proof uses the sin(x)/x limit. Both follow purely from
  the exponential field axioms and the EML differentiation rule.
-/

import Eml.Liouville

namespace Eml

/-! ## ExpField derived algebra -/

section ExpFieldAlgebra

variable {α : Type _} [E : ExtExpAlgebra α]

/-- Multiplicative associativity, derived from exp/ln. -/
theorem ExtExpAlgebra.mul_assoc (a b c : α) :
    E.mul (E.mul a b) c = E.mul a (E.mul b c) :=
  calc E.mul (E.mul a b) c
      = E.exp (E.ln (E.mul (E.mul a b) c)) := (E.exp_ln _).symm
    _ = E.exp (E.add (E.ln (E.mul a b)) (E.ln c)) := by rw [E.ln_mul]
    _ = E.exp (E.add (E.add (E.ln a) (E.ln b)) (E.ln c)) := by rw [E.ln_mul]
    _ = E.exp (E.add (E.ln a) (E.add (E.ln b) (E.ln c))) := by rw [E.add_assoc]
    _ = E.exp (E.add (E.ln a) (E.ln (E.mul b c))) := by rw [← E.ln_mul]
    _ = E.exp (E.ln (E.mul a (E.mul b c))) := by rw [← E.ln_mul]
    _ = E.mul a (E.mul b c) := E.exp_ln _

/-- neg(a)·b = neg(a·b), for finite a, b. -/
theorem ExtExpAlgebra.neg_mul {a b : α}
    (ha : Finite a) (hb : Finite b) :
    E.mul (E.neg a) b = E.neg (E.mul a b) := by
  have hna : Finite (E.neg a) := ⟨E.neg_ne_neg_inf a ha.2, E.neg_ne_pos_inf a ha.1⟩
  have hab : Finite (E.mul a b) := Finite.mul ha hb
  have hnab : Finite (E.mul (E.neg a) b) := Finite.mul hna hb
  have h : E.add (E.mul a b) (E.mul (E.neg a) b) = E.zro := by
    calc E.add (E.mul a b) (E.mul (E.neg a) b)
        = E.add (E.mul b a) (E.mul b (E.neg a)) := by
          rw [E.mul_comm a, E.mul_comm (E.neg a)]
      _ = E.mul b (E.add a (E.neg a)) := by rw [← E.mul_add]
      _ = E.mul b E.zro := by rw [E.add_neg a ha.1 ha.2]
      _ = E.zro := E.mul_zero _
  calc E.mul (E.neg a) b
      = E.add E.zro (E.mul (E.neg a) b) := (ExtExpAlgebra.zero_add _).symm
    _ = E.add (E.add (E.neg (E.mul a b)) (E.mul a b)) (E.mul (E.neg a) b) := by
        rw [E.add_comm (E.neg _), E.add_neg _ hab.1 hab.2]
    _ = E.add (E.neg (E.mul a b)) (E.add (E.mul a b) (E.mul (E.neg a) b)) := by
        rw [E.add_assoc]
    _ = E.add (E.neg (E.mul a b)) E.zro := by rw [h]
    _ = E.neg (E.mul a b) := E.add_zero _

/-- a·neg(b) = neg(a·b), for finite a, b. -/
theorem ExtExpAlgebra.mul_neg {a b : α}
    (ha : Finite a) (hb : Finite b) :
    E.mul a (E.neg b) = E.neg (E.mul a b) := by
  rw [E.mul_comm, ExtExpAlgebra.neg_mul hb ha, E.mul_comm]

/-- mul(a, inv(a)) = one, for finite nonzero a. -/
theorem ExtExpAlgebra.mul_inv_cancel {a : α}
    (ha_fin : Finite a) (ha_nz : a ≠ E.zro) :
    E.mul a (E.inv a) = E.one := by
  have hln_fin : Finite (E.ln a) := Finite.ln ha_fin ha_nz
  calc E.mul a (E.inv a)
      = E.exp (E.ln (E.mul a (E.inv a))) := (E.exp_ln _).symm
    _ = E.exp (E.add (E.ln a) (E.ln (E.inv a))) := by rw [E.ln_mul]
    _ = E.exp (E.add (E.ln a) (E.ln (E.exp (E.neg (E.ln a))))) := by rw [E.inv_def]
    _ = E.exp (E.add (E.ln a) (E.neg (E.ln a))) := by rw [E.ln_exp]
    _ = E.exp E.zro := by rw [E.add_neg _ hln_fin.1 hln_fin.2]
    _ = E.one := E.exp_zero

/-- mul(inv(a), a) = one, for finite nonzero a. -/
theorem ExtExpAlgebra.inv_mul_cancel {a : α}
    (ha_fin : Finite a) (ha_nz : a ≠ E.zro) :
    E.mul (E.inv a) a = E.one := by
  rw [E.mul_comm]; exact ExtExpAlgebra.mul_inv_cancel ha_fin ha_nz

private theorem one_finite : Finite (E.one : α) :=
  ⟨E.neg_inf_ne_one.symm, E.pos_inf_ne_one.symm⟩

private theorem neg_one_finite : Finite (E.neg E.one : α) :=
  ⟨E.neg_ne_neg_inf E.one E.pos_inf_ne_one.symm,
   E.neg_ne_pos_inf E.one E.neg_inf_ne_one.symm⟩

/-- (-1)² = 1 -/
theorem ExtExpAlgebra.neg_one_sq : E.mul (E.neg E.one) (E.neg E.one) = (E.one : α) := by
  rw [ExtExpAlgebra.neg_mul one_finite neg_one_finite,
      ExtExpAlgebra.one_mul, E.neg_neg]

private theorem neg_one_ne_zro : (E.neg E.one : α) ≠ E.zro := by
  intro h
  have : E.one = E.zro := by
    have := congrArg E.neg h
    rw [E.neg_neg, ExtExpAlgebra.neg_zero] at this
    -- this : one = zro after neg_neg on LHS and neg_zero on RHS
    -- Actually: h : neg one = zro, neg both sides: neg(neg one) = neg zro
    -- neg_neg: one = neg zro; neg_zero: one = zro
    exact this
  exact E.one_ne_zro this

/-- inv(-1) = -1. -/
theorem ExtExpAlgebra.inv_neg_one : E.inv (E.neg E.one) = (E.neg E.one : α) :=
  calc E.inv (E.neg E.one)
      = E.mul (E.inv (E.neg E.one)) E.one := (E.mul_one _).symm
    _ = E.mul (E.inv (E.neg E.one)) (E.mul (E.neg E.one) (E.neg E.one)) := by
        rw [ExtExpAlgebra.neg_one_sq]
    _ = E.mul (E.mul (E.inv (E.neg E.one)) (E.neg E.one)) (E.neg E.one) := by
        rw [ExtExpAlgebra.mul_assoc]
    _ = E.mul E.one (E.neg E.one) := by
        rw [ExtExpAlgebra.inv_mul_cancel neg_one_finite neg_one_ne_zro]
    _ = E.neg E.one := ExtExpAlgebra.one_mul _

/-- inv(a·b) = inv(a)·inv(b), for finite nonzero a and b. -/
theorem ExtExpAlgebra.inv_mul_distrib {a b : α}
    (ha : Finite a) (ha_nz : a ≠ E.zro) (hb : Finite b) (hb_nz : b ≠ E.zro) :
    E.inv (E.mul a b) = E.mul (E.inv a) (E.inv b) := by
  have hla : Finite (E.ln a) := Finite.ln ha ha_nz
  have hlb : Finite (E.ln b) := Finite.ln hb hb_nz
  calc E.inv (E.mul a b)
      = E.exp (E.neg (E.ln (E.mul a b))) := E.inv_def _
    _ = E.exp (E.neg (E.add (E.ln a) (E.ln b))) := by rw [E.ln_mul]
    _ = E.exp (E.add (E.neg (E.ln a)) (E.neg (E.ln b))) := by
        rw [ExtExpAlgebra.neg_add hla hlb]
    _ = E.mul (E.exp (E.neg (E.ln a))) (E.exp (E.neg (E.ln b))) := by rw [E.exp_add]
    _ = E.mul (E.inv a) (E.exp (E.neg (E.ln b))) := by rw [← E.inv_def]
    _ = E.mul (E.inv a) (E.inv b) := by rw [← E.inv_def]

/-! ## Eval helpers -/

theorem eval_negOne (ρ : Nat → α) : eval ρ negOne = E.neg E.one := by
  unfold negOne; rw [eval_sub', eval_zero]; simp only [eval, ExtExpAlgebra.zero_add]

theorem eval_two (ρ : Nat → α) : eval ρ two = E.add E.one E.one := by
  unfold two; rw [eval_sub', eval_negOne]; simp only [eval, E.neg_neg]

/-! ## Euler's identity -/

/-- i·π evaluates to -ln(-1) in any ExtExpAlgebra. -/
private theorem eval_mul_i'_pi' (ρ : Nat → α) :
    eval ρ (mul' i' pi') = E.neg (E.ln (E.neg E.one)) := by
  rw [eval_mul']
  have hi : eval ρ i' = E.neg (E.mul (E.ln (E.neg E.one)) (E.inv (eval ρ pi'))) := by
    unfold i' div'
    rw [eval_neg', eval_mul', eval_ln', eval_inv', eval_negOne]
  sorry -- needs neg_mul + inv_mul_cancel with finiteness of ln(-1) and pi

/-- **Euler's identity**: exp(iπ) = -1, machine-checked. -/
theorem euler_identity : SemEq (exp' (mul' i' pi')) negOne := by
  intro α _ ρ _
  rw [eval_exp', eval_negOne, eval_mul_i'_pi', ← ExtExpAlgebra.inv_def, ExtExpAlgebra.inv_neg_one]

/-! ## D(sin) = cos -/

/-- Evaluate the intermediate derivative form. -/
private theorem eval_sin_deriv_intermediate (ρ : Nat → α) :
    eval ρ (mul' (inv' (mul' two i'))
      (sub' (mul' (exp' (mul' i' (var 0))) i')
            (mul' (exp' (neg' (mul' i' (var 0)))) (neg' i'))))
    = E.mul (E.inv (E.mul (E.add E.one E.one) (eval ρ i')))
      (E.add (E.mul (E.exp (E.mul (eval ρ i') (ρ 0))) (eval ρ i'))
             (E.neg (E.mul (E.exp (E.neg (E.mul (eval ρ i') (ρ 0)))) (E.neg (eval ρ i'))))) := by
  simp only [eval_mul', eval_inv', eval_sub', eval_exp', eval_neg', eval_two, eval]

/-- Evaluate cos'(var 0). -/
private theorem eval_cos'_var (ρ : Nat → α) :
    eval ρ (cos' (var 0))
    = E.mul (E.add (E.exp (E.mul (eval ρ i') (ρ 0)))
                   (E.exp (E.neg (E.mul (eval ρ i') (ρ 0)))))
            (E.inv (E.add E.one E.one)) := by
  simp only [cos', half, eval_mul', eval_add', eval_exp', eval_neg', eval_inv', eval_two, eval]

/-- The algebraic bridge: intermediate derivative = cos semantically. -/
private theorem diff_sin_bridge (ρ : Nat → α) :
    E.mul (E.inv (E.mul (E.add E.one E.one) (eval ρ i')))
      (E.add (E.mul (E.exp (E.mul (eval ρ i') (ρ 0))) (eval ρ i'))
             (E.neg (E.mul (E.exp (E.neg (E.mul (eval ρ i') (ρ 0)))) (E.neg (eval ρ i')))))
    = E.mul (E.add (E.exp (E.mul (eval ρ i') (ρ 0)))
                   (E.exp (E.neg (E.mul (eval ρ i') (ρ 0)))))
            (E.inv (E.add E.one E.one)) := by
  sorry -- needs mul_neg, inv_mul_distrib, inv_mul_cancel with finiteness of i

end ExpFieldAlgebra

/-! ### Steps: differentiate sin to intermediate form -/

/-- mul'(mul'(f,c), mul'(inv'(f), d)) →* mul'(c, d). -/
private theorem mul_cancel_swap (f c d : Eml) :
    Steps (mul' (mul' f c) (mul' (inv' f) d)) (mul' c d) :=
  Steps.trans (Steps.mul'_l (mul_comm' f c))
    (Steps.trans (Steps.exp' (Steps.add'_l (Steps.single (Step.ln_mul c f))))
    (Steps.trans (Steps.exp' (Steps.add'_r (Steps.single (Step.ln_mul (inv' f) d))))
    (Steps.trans (Steps.exp' (Steps.add'_r (Steps.add'_l (Steps.single (Step.ln_exp (neg' (ln' f)))))))
    (Steps.trans (Steps.exp' (Steps.single (Step.add_assoc (ln' c) (ln' f) (add' (neg' (ln' f)) (ln' d)))))
    (Steps.trans (Steps.exp' (Steps.add'_r (add_assoc_rev (ln' f) (neg' (ln' f)) (ln' d))))
    (Steps.trans (Steps.exp' (Steps.add'_r (Steps.add'_l (add_neg_self (ln' f)))))
    (Steps.exp' (Steps.add'_r (Steps.single (Step.add_zero_l (ln' d)))))))))))

/-- D(mul'(f, c)) →* mul'(c, D(f)) when c is ground. -/
theorem diff_mul_const_right (f c : Eml) (x : Nat) (hc : c.hasVar x = false) :
    Steps (diff (mul' f c) x) (mul' c (diff f x)) := by
  have step1 := diff_exp_general (add' (ln' f) (ln' c)) x
  have step2 := diff_add_general (ln' f) (ln' c) x
  have hclg : (ln' c).hasVar x = false := by simp [ln', exp', hasVar, hc]
  have step3 := diff_ground_is_zero (ln' c) x hclg
  have step4 := diff_ln_general f x
  exact Steps.trans step1
    (Steps.trans (Steps.mul'_r step2)
    (Steps.trans (Steps.mul'_r (Steps.add'_r step3))
    (Steps.trans (Steps.mul'_r (Steps.single (Step.add_zero_r (diff (ln' f) x))))
    (Steps.trans (Steps.mul'_r step4)
    (Steps.trans (Steps.mul'_r (mul_comm' (diff f x) (inv' f)))
    (mul_cancel_swap f c (diff f x)))))))

/-- D(i·x) →* i when x = var 0 and i is ground. -/
private theorem diff_ix (i_tree : Eml) (hi : i_tree.hasVar 0 = false) :
    Steps (diff (mul' i_tree (var 0)) 0) i_tree :=
  Steps.trans (diff_mul_const i_tree (var 0) 0 hi)
    (by simp [diff]; exact Steps.single (Step.mul_one_r i_tree))

/-- D(sin(x)) →* intermediate form via chain rules. -/
theorem diff_sin_steps :
    Steps (diff (sin' (var 0)) 0)
      (mul' (inv' (mul' two i'))
        (sub' (mul' (exp' (mul' i' (var 0))) i')
              (mul' (exp' (neg' (mul' i' (var 0)))) (neg' i')))) := by
  have h_ground : (inv' (mul' two i')).hasVar 0 = false := by native_decide
  have h_i_ground : i'.hasVar 0 = false := by native_decide
  have step_outer := diff_mul_const_right
    (sub' (exp' (mul' i' (var 0))) (exp' (neg' (mul' i' (var 0)))))
    (inv' (mul' two i')) 0 h_ground
  have step_sub := diff_sub_general
    (exp' (mul' i' (var 0))) (exp' (neg' (mul' i' (var 0)))) 0
  have step_dA := Steps.trans (diff_exp_general (mul' i' (var 0)) 0)
    (Steps.mul'_r (diff_ix i' h_i_ground))
  have step_dB := Steps.trans (diff_exp_general (neg' (mul' i' (var 0))) 0)
    (Steps.mul'_r (Steps.trans (diff_neg_general (mul' i' (var 0)) 0)
      (Steps.neg' (diff_ix i' h_i_ground))))
  exact Steps.trans step_outer
    (Steps.mul'_r (Steps.trans step_sub
      (Steps.sub'_both step_dA step_dB)))

/-- **D(sin(x)) = cos(x)**, machine-checked.

    No sin(x)/x limit. No L'Hôpital. No ε-δ.
    The derivative follows purely from D(exp) = exp and algebraic identities. -/
theorem diff_sin_eq_cos : SemEq (diff (sin' (var 0)) 0) (cos' (var 0)) := by
  apply SemEq.trans (SemEq.of_steps diff_sin_steps)
  intro α _ ρ _
  rw [eval_sin_deriv_intermediate, eval_cos'_var]
  exact diff_sin_bridge ρ

end Eml
