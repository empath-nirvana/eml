/-
  EML Soundness Bridge
  ====================
  Abstract interpretation of EML trees into "exponential fields."

  The soundness theorem: every rewrite step preserves evaluation.
  This bridges the syntactic rewrite system to semantic properties,
  enabling non-reachability proofs by appeal to models.

  The canonical model is (ℝ, +, ·, exp, ln). Instantiating to ℝ
  requires Mathlib and is left to future work.
-/

import Eml.Rewrite

namespace Eml

/-- An exponential field: the semantic domain for EML trees. -/
class ExpField (α : Type _) where
  zro : α
  one : α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  inv : α → α
  exp : α → α
  ln  : α → α
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm  : ∀ a b, add a b = add b a
  add_zero  : ∀ a, add a zro = a
  add_neg   : ∀ a, add a (neg a) = zro
  neg_neg   : ∀ a, neg (neg a) = a
  mul_one   : ∀ a, mul a one = a
  mul_comm  : ∀ a b, mul a b = mul b a
  mul_zero  : ∀ a, mul a zro = zro
  inv_def   : ∀ a, inv a = exp (neg (ln a))
  inv_inv   : ∀ a, inv (inv a) = a
  exp_ln    : ∀ x, exp (ln x) = x
  ln_exp    : ∀ x, ln (exp x) = x
  exp_zero  : exp zro = one
  ln_one    : ln one = zro
  mul_add   : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  exp_add   : ∀ a b, exp (add a b) = mul (exp a) (exp b)
  ln_mul    : ∀ a b, ln (mul a b) = add (ln a) (ln b)

section Soundness

variable {α : Type _} [E : ExpField α]

/-! ## Derived ExpField lemmas -/

theorem ExpField.zero_add (a : α) : E.add E.zro a = a := by
  rw [E.add_comm]; exact E.add_zero a

theorem ExpField.neg_zero : (E.neg E.zro : α) = E.zro := by
  have h := E.add_neg E.zro; rw [ExpField.zero_add] at h; exact h

theorem ExpField.one_mul (a : α) : E.mul E.one a = a := by
  rw [E.mul_comm]; exact E.mul_one a

theorem ExpField.zero_mul (a : α) : E.mul E.zro a = E.zro := by
  rw [E.mul_comm]; exact E.mul_zero a

private theorem neg_unique (a b : α) (h : E.add a b = E.zro) : b = E.neg a :=
  calc b = E.add E.zro b := (ExpField.zero_add b).symm
    _ = E.add (E.add (E.neg a) a) b := by rw [E.add_comm (E.neg a), E.add_neg]
    _ = E.add (E.neg a) (E.add a b) := by rw [E.add_assoc]
    _ = E.add (E.neg a) E.zro := by rw [h]
    _ = E.neg a := E.add_zero _

theorem ExpField.neg_add (a b : α) :
    E.neg (E.add a b) = E.add (E.neg a) (E.neg b) := by
  symm; apply neg_unique
  calc E.add (E.add a b) (E.add (E.neg a) (E.neg b))
      = E.add a (E.add b (E.add (E.neg a) (E.neg b))) := by rw [E.add_assoc]
    _ = E.add a (E.add (E.add b (E.neg a)) (E.neg b)) := by rw [← E.add_assoc b]
    _ = E.add a (E.add (E.add (E.neg a) b) (E.neg b)) := by rw [E.add_comm b (E.neg a)]
    _ = E.add a (E.add (E.neg a) (E.add b (E.neg b))) := by rw [E.add_assoc (E.neg a)]
    _ = E.add a (E.add (E.neg a) E.zro) := by rw [E.add_neg]
    _ = E.add a (E.neg a) := by rw [E.add_zero]
    _ = E.zro := E.add_neg a

/-! ## Evaluation -/

/-- Evaluation of EML trees in an exponential field.
    node(a, b) interprets as eml(a, b) = exp(a) + neg(ln(b)). -/
def eval (ρ : Nat → α) : Eml → α
  | .one => E.one
  | .var n => ρ n
  | .node a b => E.add (E.exp (eval ρ a)) (E.neg (E.ln (eval ρ b)))

/-! ## Evaluation of derived operations -/

theorem eval_exp' (ρ : Nat → α) (z : Eml) :
    eval ρ (exp' z) = E.exp (eval ρ z) := by
  simp only [exp', eval, E.ln_one, ExpField.neg_zero, E.add_zero]

theorem eval_ln' (ρ : Nat → α) (z : Eml) :
    eval ρ (ln' z) = E.ln (eval ρ z) := by
  simp only [ln', exp', eval]
  rw [E.ln_one, ExpField.neg_zero, E.add_zero, E.ln_exp,
      ExpField.neg_add, E.neg_neg, ← E.add_assoc, E.add_neg, ExpField.zero_add]

theorem eval_zero (ρ : Nat → α) : eval ρ zero = E.zro := by
  unfold zero; rw [eval_ln']; exact E.ln_one

theorem eval_sub' (ρ : Nat → α) (a b : Eml) :
    eval ρ (sub' a b) = E.add (eval ρ a) (E.neg (eval ρ b)) := by
  simp only [sub', eval]
  rw [eval_ln', eval_exp', E.exp_ln, E.ln_exp]

theorem eval_neg' (ρ : Nat → α) (z : Eml) :
    eval ρ (neg' z) = E.neg (eval ρ z) := by
  unfold neg'; rw [eval_sub', eval_zero, ExpField.zero_add]

theorem eval_add' (ρ : Nat → α) (a b : Eml) :
    eval ρ (add' a b) = E.add (eval ρ a) (eval ρ b) := by
  unfold add'; rw [eval_sub', eval_neg', E.neg_neg]

theorem eval_mul' (ρ : Nat → α) (a b : Eml) :
    eval ρ (mul' a b) = E.mul (eval ρ a) (eval ρ b) := by
  unfold mul'; rw [eval_exp', eval_add', eval_ln', eval_ln',
                    E.exp_add, E.exp_ln, E.exp_ln]

theorem eval_inv' (ρ : Nat → α) (z : Eml) :
    eval ρ (inv' z) = E.inv (eval ρ z) := by
  unfold inv'; rw [eval_exp', eval_neg', eval_ln', E.inv_def]

/-! ## Soundness -/

/-- **Soundness**: one-step rewrites preserve evaluation. -/
theorem step_sound (ρ : Nat → α) {a b : Eml} (h : Step a b) :
    eval ρ a = eval ρ b := by
  induction h with
  | exp_ln z => rw [eval_exp', eval_ln', E.exp_ln]
  | ln_exp z => rw [eval_ln', eval_exp', E.ln_exp]
  | sub_zero z =>
    rw [eval_sub', eval_zero, ExpField.neg_zero, E.add_zero]
  | sub_self z =>
    rw [eval_sub', E.add_neg, eval_zero]
  | add_zero_l z =>
    rw [eval_add', eval_zero, ExpField.zero_add]
  | add_zero_r z =>
    rw [eval_add', eval_zero, E.add_zero]
  | mul_one_l z =>
    rw [eval_mul']; exact ExpField.one_mul (eval ρ z)
  | mul_one_r z =>
    rw [eval_mul']; exact E.mul_one (eval ρ z)
  | mul_zero_l z =>
    rw [eval_mul', eval_zero]; exact ExpField.zero_mul (eval ρ z)
  | mul_zero_r z =>
    rw [eval_mul', eval_zero]; exact E.mul_zero (eval ρ z)
  | neg_neg z =>
    rw [eval_neg', eval_neg', E.neg_neg]
  | inv_inv z =>
    rw [eval_inv', eval_inv', E.inv_inv]
  | exp_add a b =>
    rw [eval_exp', eval_add', E.exp_add, eval_mul', eval_exp', eval_exp']
  | ln_mul a b =>
    rw [eval_ln', eval_mul', E.ln_mul, eval_add', eval_ln', eval_ln']
  | mul_add a b c =>
    rw [eval_mul', eval_add', E.mul_add, eval_add', eval_mul', eval_mul']
  | ln_one =>
    rw [eval_ln']; simp only [eval]; rw [E.ln_one, eval_zero]
  | exp_zero =>
    rw [eval_exp', eval_zero, E.exp_zero]; rfl
  | add_assoc a b c =>
    simp only [eval_add', E.add_assoc]
  | add_comm a b =>
    simp only [eval_add', E.add_comm]
  | cancel_exp_ln z =>
    -- exp(ln(ln(z))) - ln(z) = ln(z) - ln(z) = 0
    simp only [eval, eval_ln']
    rw [E.exp_ln, E.add_neg, eval_zero]
  | cancel_ln_exp z =>
    -- exp(z) - ln(exp(exp(z))) = exp(z) - exp(z) = 0
    simp only [eval, eval_exp']
    rw [E.ln_exp, E.add_neg, eval_zero]
  | node_l a a' b _ ih =>
    simp only [eval]; rw [ih]
  | node_r a b b' _ ih =>
    simp only [eval]; rw [ih]

/-- Soundness for rewrite chains: if a →* b then ⟦a⟧ = ⟦b⟧. -/
theorem steps_sound (ρ : Nat → α) {a b : Eml} (h : Steps a b) :
    eval ρ a = eval ρ b := by
  induction h with
  | refl _ => rfl
  | step _ _ _ hab _ ih => exact (step_sound ρ hab).trans ih

/-- Soundness for equivalence: if a ≈ₑ b then ⟦a⟧ = ⟦b⟧. -/
theorem equiv_sound (ρ : Nat → α) {a b : Eml} (h : a ≈ₑ b) :
    eval ρ a = eval ρ b := by
  obtain ⟨c, hac, hbc⟩ := h
  exact (steps_sound ρ hac).trans (steps_sound ρ hbc).symm

/-! ## Non-reachability -/

/-- If two trees evaluate differently in some model, no rewrite chain
    connects them. -/
theorem not_steps_of_eval_ne {a b : Eml} (ρ : Nat → α)
    (h : eval ρ a ≠ eval ρ b) : ¬Steps a b :=
  fun hab => h (steps_sound ρ hab)

/-- If two trees evaluate differently in some model, they are not equivalent. -/
theorem not_equiv_of_eval_ne {a b : Eml} (ρ : Nat → α)
    (h : eval ρ a ≠ eval ρ b) : ¬(a ≈ₑ b) :=
  fun hab => h (equiv_sound ρ hab)

end Soundness

/-! ## Semantic equality

Semantic equality: two trees evaluate identically in every
exponential field model.  This is the natural equivalence
relation induced by the soundness bridge — coarser than
syntactic Steps, finer than "same string." Crucially, it is
a genuine equivalence relation (unlike joinability, which
requires confluence for transitivity). -/

/-- Two trees are semantically equal if they evaluate identically
    in every exponential field model (over Type, which includes ℝ and ℂ). -/
def SemEq (a b : Eml) : Prop :=
  ∀ (α : Type) [ExpField α] (ρ : Nat → α), eval ρ a = eval ρ b

theorem SemEq.rfl {a : Eml} : SemEq a a :=
  fun _ _ ρ => Eq.refl (eval ρ a)

theorem SemEq.symm {a b : Eml} (h : SemEq a b) : SemEq b a :=
  fun α _ ρ => (h α ρ).symm

theorem SemEq.trans {a b c : Eml} (h1 : SemEq a b) (h2 : SemEq b c) : SemEq a c :=
  fun α _ ρ => (h1 α ρ).trans (h2 α ρ)

/-- Every rewrite chain induces semantic equality. -/
theorem SemEq.of_steps {a b : Eml} (h : Steps a b) : SemEq a b :=
  fun _ _ ρ => steps_sound ρ h

/-- Joinability implies semantic equality. -/
theorem SemEq.of_equiv {a b : Eml} (h : a ≈ₑ b) : SemEq a b :=
  fun _ _ ρ => equiv_sound ρ h

end Eml
