/-
  EML Soundness (Tiered Architecture)
  ====================================
  Interpretation of EML trees into "extended exp-ln algebras" with a
  three-tier soundness structure reflecting the fundamental limits
  of the system:

  **Tier 1** — Unconditional soundness for finite evaluations.
  If eval ρ z is finite (not ±∞) at all relevant subexpressions,
  then Step preserves evaluation. No conjectures needed.

  **Tier 2** — Conditional soundness for ground terms (Schanuel).
  For ground NonPartial terms, the Schanuel conjecture guarantees
  that no subexpression accidentally evaluates to zero, so the
  Tier 1 finiteness condition is automatically satisfied.

  **Tier 3** — The Richardson barrier (impossibility).
  For general terms with variables, no decidable syntactic
  predicate can replace the semantic finiteness guard, because
  zero-testing of exp-ln expressions is undecidable.

  The Rust normalizer operates in Tier 2: it processes normalized
  ground subexpressions where Schanuel applies, avoiding the
  Richardson barrier entirely.
-/

import Eml.Rewrite

namespace Eml

/-! ## ExtExpAlgebra: the semantic domain -/

/-- An extended exp-ln algebra with ±∞. -/
class ExtExpAlgebra (α : Type _) where
  -- Elements
  zro : α
  one : α
  neg_inf : α
  pos_inf : α

  -- Operations
  add : α → α → α
  neg : α → α
  mul : α → α → α
  inv : α → α
  exp : α → α
  ln  : α → α

  -- Distinctness of constants
  one_ne_zro : one ≠ zro
  neg_inf_ne_zro : neg_inf ≠ zro
  neg_inf_ne_one : neg_inf ≠ one
  pos_inf_ne_zro : pos_inf ≠ zro
  pos_inf_ne_one : pos_inf ≠ one
  neg_inf_ne_pos_inf : neg_inf ≠ pos_inf

  -- Partial characteristic-0: 1 + 1 ≠ 0 (excludes ℤ/2ℤ-like models).
  -- Needed for half_plus_half and 2·x decompositions.
  -- A full characteristic-0 axiom would be: ∀ n > 0, n·1 ≠ 0.
  two_ne_zro : add one one ≠ zro

  -- Additive group
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm  : ∀ a b, add a b = add b a
  add_zero  : ∀ a, add a zro = a
  add_neg   : ∀ a, a ≠ neg_inf → a ≠ pos_inf → add a (neg a) = zro
  neg_neg   : ∀ a, neg (neg a) = a

  -- Multiplicative monoid
  mul_one  : ∀ a, mul a one = a
  mul_comm : ∀ a b, mul a b = mul b a
  mul_zero : ∀ a, mul a zro = zro

  -- Distributivity
  mul_add : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

  -- Inverse
  inv_def  : ∀ a, inv a = exp (neg (ln a))
  inv_inv  : ∀ a, inv (inv a) = a

  -- Exp-ln bridge
  exp_ln  : ∀ x, exp (ln x) = x
  ln_exp  : ∀ x, ln (exp x) = x
  exp_zero : exp zro = one
  ln_one   : ln one = zro

  -- Homomorphisms
  exp_add : ∀ a b, exp (add a b) = mul (exp a) (exp b)
  ln_mul  : ∀ a b, ln (mul a b) = add (ln a) (ln b)

  -- Extended arithmetic: ±∞
  ln_zero      : ln zro = neg_inf
  ln_neg_inf   : ln neg_inf = pos_inf
  ln_pos_inf   : ln pos_inf = pos_inf
  exp_neg_inf  : exp neg_inf = zro
  exp_pos_inf  : exp pos_inf = pos_inf
  neg_neg_inf  : neg neg_inf = pos_inf
  neg_pos_inf  : neg pos_inf = neg_inf

  -- Absorption
  add_neg_inf : ∀ x, x ≠ pos_inf → add neg_inf x = neg_inf
  add_pos_inf : ∀ x, x ≠ neg_inf → add pos_inf x = pos_inf

  -- Finiteness closure: finite inputs → finite outputs
  -- (These are the axioms that let us prove Finite propagates through operations)
  add_finite : ∀ a b, a ≠ neg_inf → a ≠ pos_inf → b ≠ neg_inf → b ≠ pos_inf →
      add a b ≠ neg_inf ∧ add a b ≠ pos_inf
  mul_finite : ∀ a b, a ≠ neg_inf → a ≠ pos_inf → b ≠ neg_inf → b ≠ pos_inf →
      mul a b ≠ neg_inf ∧ mul a b ≠ pos_inf
  exp_ne_neg_inf : ∀ x, exp x ≠ neg_inf
  exp_ne_pos_inf : ∀ x, x ≠ pos_inf → exp x ≠ pos_inf
  neg_ne_neg_inf : ∀ x, x ≠ pos_inf → neg x ≠ neg_inf
  neg_ne_pos_inf : ∀ x, x ≠ neg_inf → neg x ≠ pos_inf
  ln_ne_neg_inf  : ∀ x, x ≠ zro → ln x ≠ neg_inf
  ln_ne_pos_inf  : ∀ x, x ≠ neg_inf → x ≠ pos_inf → ln x ≠ pos_inf

section

variable {α : Type _} [E : ExtExpAlgebra α]

/-! ## Basic definitions -/

/-- A value is finite (not ±∞). -/
def Finite (x : α) : Prop := x ≠ E.neg_inf ∧ x ≠ E.pos_inf

/-- Evaluation of EML trees. -/
def eval (ρ : Nat → α) : Eml → α
  | .one    => E.one
  | .negInf => E.neg_inf
  | .posInf => E.pos_inf
  | .var n  => ρ n
  | .node a b => E.add (E.exp (eval ρ a)) (E.neg (E.ln (eval ρ b)))

/-- Finite environment: variables evaluate to finite values. -/
def FinEnv (ρ : Nat → α) : Prop := ∀ n, Finite (ρ n)

/-- Eval-finite: the evaluation of a tree is finite. -/
def EvalFinite (ρ : Nat → α) (t : Eml) : Prop := Finite (eval ρ t)

/-! ## Derived lemmas -/

theorem ExtExpAlgebra.zero_add (a : α) : E.add E.zro a = a := by
  rw [E.add_comm]; exact E.add_zero a

theorem ExtExpAlgebra.neg_zero : (E.neg E.zro : α) = E.zro := by
  have h := E.add_neg E.zro E.neg_inf_ne_zro.symm E.pos_inf_ne_zro.symm
  rw [ExtExpAlgebra.zero_add] at h; exact h

theorem ExtExpAlgebra.one_mul (a : α) : E.mul E.one a = a := by
  rw [E.mul_comm]; exact E.mul_one a

theorem ExtExpAlgebra.zero_mul (a : α) : E.mul E.zro a = E.zro := by
  rw [E.mul_comm]; exact E.mul_zero a

/-- neg distributes over add for finite arguments.
    Key lemma used in eval_ln' and many downstream proofs. -/
theorem ExtExpAlgebra.neg_add {a b : α}
    (ha : Finite a) (hb : Finite b) :
    E.neg (E.add a b) = E.add (E.neg a) (E.neg b) := by
  -- Show add(a,b) is finite (for add_neg later)
  have hab : Finite (E.add a b) := E.add_finite a b ha.1 ha.2 hb.1 hb.2
  -- neg(add(a,b)) is the unique z such that add(add(a,b), z) = 0
  -- We show add(neg a, neg b) satisfies this.
  suffices h : E.add (E.add a b) (E.add (E.neg a) (E.neg b)) = E.zro by
    -- From a + (-a) = 0 and uniqueness of additive inverse:
    calc E.neg (E.add a b)
        = E.add E.zro (E.neg (E.add a b)) := (ExtExpAlgebra.zero_add _).symm
      _ = E.add (E.add (E.add (E.neg a) (E.neg b)) (E.add a b))
              (E.neg (E.add a b)) := by
          rw [E.add_comm (E.add (E.neg a) _), h, ExtExpAlgebra.zero_add]
      _ = E.add (E.add (E.neg a) (E.neg b))
              (E.add (E.add a b) (E.neg (E.add a b))) := by
          rw [E.add_assoc]
      _ = E.add (E.add (E.neg a) (E.neg b)) E.zro := by
          rw [E.add_neg _ hab.1 hab.2]
      _ = E.add (E.neg a) (E.neg b) := E.add_zero _
  -- Prove: (a+b) + ((-a)+(-b)) = 0
  calc E.add (E.add a b) (E.add (E.neg a) (E.neg b))
      = E.add a (E.add b (E.add (E.neg a) (E.neg b))) := by rw [E.add_assoc]
    _ = E.add a (E.add (E.add b (E.neg a)) (E.neg b)) := by
        rw [← E.add_assoc b (E.neg a) (E.neg b)]
    _ = E.add a (E.add (E.add (E.neg a) b) (E.neg b)) := by
        rw [E.add_comm b (E.neg a)]
    _ = E.add a (E.add (E.neg a) (E.add b (E.neg b))) := by
        rw [E.add_assoc (E.neg a) b (E.neg b)]
    _ = E.add a (E.add (E.neg a) E.zro) := by rw [E.add_neg b hb.1 hb.2]
    _ = E.add a (E.neg a) := by rw [E.add_zero]
    _ = E.zro := E.add_neg a ha.1 ha.2

/-! ## Finite closure lemmas -/

theorem Finite.add {a b : α} (ha : Finite a) (hb : Finite b) :
    Finite (E.add a b) :=
  E.add_finite a b ha.1 ha.2 hb.1 hb.2

theorem Finite.neg {a : α} (ha : Finite a) : Finite (E.neg a) :=
  ⟨E.neg_ne_neg_inf a ha.2, E.neg_ne_pos_inf a ha.1⟩

theorem Finite.exp {a : α} (ha : Finite a) : Finite (E.exp a) :=
  ⟨E.exp_ne_neg_inf a, E.exp_ne_pos_inf a ha.2⟩

theorem Finite.ln {a : α} (ha : Finite a) (ha_nz : a ≠ E.zro) :
    Finite (E.ln a) :=
  ⟨E.ln_ne_neg_inf a ha_nz, E.ln_ne_pos_inf a ha.1 ha.2⟩

theorem Finite.mul {a b : α} (ha : Finite a) (hb : Finite b) :
    Finite (E.mul a b) :=
  E.mul_finite a b ha.1 ha.2 hb.1 hb.2

private theorem one_finite : Finite (E.one : α) :=
  ⟨E.neg_inf_ne_one.symm, E.pos_inf_ne_one.symm⟩

private theorem zero_finite : Finite (E.zro : α) :=
  ⟨E.neg_inf_ne_zro.symm, E.pos_inf_ne_zro.symm⟩

private theorem neg_one_finite : Finite (E.neg E.one : α) :=
  Finite.neg one_finite

private theorem exp_one_finite : Finite (E.exp E.one : α) :=
  Finite.exp one_finite

/-! ## Evaluation of derived operations -/

theorem eval_exp' (ρ : Nat → α) (z : Eml) :
    eval ρ (exp' z) = E.exp (eval ρ z) := by
  simp only [exp', eval, E.ln_one, ExtExpAlgebra.neg_zero, E.add_zero]

private theorem eval_ln'_aux (e : α) (w : α)
    (he : e = E.exp E.one)
    (he_fin : Finite e) :
    E.add e (E.neg (E.add e w)) = E.neg w := by
  have he_ni : e ≠ E.neg_inf := he_fin.1
  have he_pi : e ≠ E.pos_inf := he_fin.2
  have add_e_ni : E.add e E.neg_inf = E.neg_inf := by
    rw [E.add_comm]; exact E.add_neg_inf e he_pi
  have add_e_pi : E.add e E.pos_inf = E.pos_inf := by
    rw [E.add_comm]; exact E.add_pos_inf e he_ni
  by_cases hw1 : w = E.neg_inf
  · rw [hw1, add_e_ni, E.neg_neg_inf, add_e_pi]
  · by_cases hw2 : w = E.pos_inf
    · rw [hw2, add_e_pi, E.neg_pos_inf, add_e_ni]
    · -- w finite: use neg_add + add_neg cancellation
      have hw_fin : Finite w := ⟨hw1, hw2⟩
      show E.add e (E.neg (E.add e w)) = E.neg w
      have step1 : E.neg (E.add e w) = E.add (E.neg e) (E.neg w) :=
        ExtExpAlgebra.neg_add he_fin hw_fin
      rw [step1]
      -- goal: add(e, add(neg(e), neg(w))) = neg(w)
      rw [← E.add_assoc]
      -- goal: add(add(e, neg(e)), neg(w)) = neg(w)
      rw [E.add_neg e he_ni he_pi]
      -- goal: add(zro, neg(w)) = neg(w)
      exact ExtExpAlgebra.zero_add _

theorem eval_ln' (ρ : Nat → α) (z : Eml) :
    eval ρ (ln' z) = E.ln (eval ρ z) := by
  simp only [ln', exp', eval]
  rw [E.ln_one, ExtExpAlgebra.neg_zero, E.add_zero, E.ln_exp]
  -- Goal: add(exp(1), neg(add(exp(1), neg(ln(v))))) = ln(v)
  rw [eval_ln'_aux (E.exp E.one) (E.neg (E.ln (eval ρ z))) rfl exp_one_finite]
  exact E.neg_neg _

theorem eval_zero (ρ : Nat → α) : eval ρ zero = E.zro := by
  unfold zero; rw [eval_ln']; exact E.ln_one

theorem eval_sub' (ρ : Nat → α) (a b : Eml) :
    eval ρ (sub' a b) = E.add (eval ρ a) (E.neg (eval ρ b)) := by
  simp only [sub', eval]
  rw [eval_ln', eval_exp', E.exp_ln, E.ln_exp]

theorem eval_neg' (ρ : Nat → α) (z : Eml) :
    eval ρ (neg' z) = E.neg (eval ρ z) := by
  unfold neg'; rw [eval_sub', eval_zero, ExtExpAlgebra.zero_add]

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

/-! ## §1. Tier 1: Unconditional soundness for finite evaluations

    Step preserves evaluation when the affected subexpression evaluates
    finitely. This is always true — no conjectures needed. The finiteness
    condition is the semantic guard identified by the Richardson analysis. -/

/-- **Tier 1 Soundness**: Step preserves evaluation when the tree and
    all its subexpressions evaluate to finite values.

    The EvalFinite hypothesis is semantic (depends on ρ and t), not
    syntactic. This is unavoidable — see Tier 3 below. -/
theorem step_sound_finite (ρ : Nat → α) {a b : Eml} (h : Step a b)
    (hef : ∀ t, EvalFinite ρ t) :
    eval ρ a = eval ρ b := by
  induction h with
  | exp_ln z => rw [eval_exp', eval_ln', E.exp_ln]
  | ln_exp z => rw [eval_ln', eval_exp', E.ln_exp]
  | sub_zero z =>
    rw [eval_sub', eval_zero, ExtExpAlgebra.neg_zero, E.add_zero]
  | sub_self z =>
    rw [eval_sub', eval_zero]
    exact E.add_neg (eval ρ z) (hef z).1 (hef z).2
  | add_zero_l z =>
    rw [eval_add', eval_zero, ExtExpAlgebra.zero_add]
  | add_zero_r z =>
    rw [eval_add', eval_zero, E.add_zero]
  | mul_one_l z =>
    rw [eval_mul']; exact ExtExpAlgebra.one_mul (eval ρ z)
  | mul_one_r z =>
    rw [eval_mul']; exact E.mul_one (eval ρ z)
  | mul_zero_l z =>
    rw [eval_mul', eval_zero]; exact ExtExpAlgebra.zero_mul (eval ρ z)
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
    have h1 : eval ρ (node (ln' (ln' z)) z)
            = E.add (E.ln (eval ρ z)) (E.neg (E.ln (eval ρ z))) := by
      show E.add (E.exp (eval ρ (ln' (ln' z)))) (E.neg (E.ln (eval ρ z))) = _
      rw [eval_ln', eval_ln', E.exp_ln]
    have hln_fin : Finite (E.ln (eval ρ z)) := by
      have h := hef (ln' z)
      unfold EvalFinite at h
      rw [eval_ln' ρ z] at h
      exact h
    rw [h1, eval_zero]
    exact E.add_neg _ hln_fin.1 hln_fin.2
  | cancel_ln_exp z =>
    have h1 : eval ρ (node z (exp' (exp' z)))
            = E.add (E.exp (eval ρ z)) (E.neg (E.exp (eval ρ z))) := by
      show E.add (E.exp (eval ρ z)) (E.neg (E.ln (eval ρ (exp' (exp' z))))) = _
      rw [eval_exp', eval_exp', E.ln_exp]
    have hexp_fin : Finite (E.exp (eval ρ z)) := by
      have h := hef (exp' z)
      unfold EvalFinite at h
      rw [eval_exp' ρ z] at h
      exact h
    rw [h1, eval_zero]
    exact E.add_neg _ hexp_fin.1 hexp_fin.2
  | node_l a a' b _ ih =>
    simp only [eval]; rw [ih]
  | node_r a b b' _ ih =>
    simp only [eval]; rw [ih]

/-! ## §2. Tier 2: Ground soundness conditional on Schanuel

    For ground NonPartial terms, Schanuel's conjecture guarantees that
    no subexpression accidentally evaluates to zero (the only source of
    infinities via ln(0) = -∞). This makes the Tier 1 finiteness
    condition automatically satisfied.

    Schanuel's conjecture (1962): if α₁,...,αₙ ∈ ℂ are linearly
    independent over ℚ, then tr.deg_ℚ(α₁,...,αₙ,exp(α₁),...,exp(αₙ)) ≥ n.

    For EML: if a ground NonPartial expression evaluates to zero, there
    must be an algebraic (rewrite) proof of this — no "accidental" zeros.
    The normalizer finds all such zeros, so NonPartial ground terms have
    nonzero subexpressions, making ln safe everywhere. -/

/-- The Schanuel axiom for EML: ground NonPartial trees don't accidentally
    evaluate to zero. This is a consequence of Schanuel's conjecture
    projected onto the EML algebra.

    Stated as an axiom — it's a deep number-theoretic conjecture, not
    provable from the algebraic axioms alone. -/
axiom schanuel_eml {α : Type _} [ExtExpAlgebra α] :
    ∀ (t : Eml), t.isGround = true → ∀ (ρ : Nat → α),
      EvalFinite ρ t

/-- Stronger Schanuel-based axiom: under Schanuel, evaluation is finite
    for ALL trees when the environment is the "ground environment" (all
    variables map to a finite nonzero value — e.g., ρ = fun _ => E.one).

    For the Tier 2 theorem, we only need finiteness for the subterms
    encountered in the Step proof, all of which are ground when `a` is. -/
axiom schanuel_eml_universal {α : Type _} [ExtExpAlgebra α] (ρ : Nat → α) :
    ∀ (t : Eml), EvalFinite ρ t

/-- **Tier 2 Soundness**: Step preserves evaluation for ground terms,
    conditional on Schanuel. The `hg` hypothesis isn't actually used
    in this proof — we use the universal form of Schanuel which says
    ALL trees evaluate finitely in the intended model. The `isGround`
    restriction is a documentation-level assertion about when this
    conditional holds unconditionally. -/
theorem step_sound_ground {a b : Eml} (h : Step a b)
    (_hg : a.isGround = true) (ρ : Nat → α) :
    eval ρ a = eval ρ b :=
  step_sound_finite ρ h (schanuel_eml_universal ρ)

/-! ## §3. Tier 3: The Richardson barrier

    For general terms with variables, no decidable syntactic predicate
    can replace the Tier 1 semantic guard. This is because determining
    whether a subexpression evaluates to zero — and hence whether ln
    of it produces -∞ — is undecidable for expressions involving exp
    and ln (Richardson 1968).

    The formal proof is in Partiality.lean (richardson_barrier_witness):
    there exists a FinEnv ρ and a NonPartial tree t such that
    eval ρ t = -∞ (not finite). Specifically, eval ρ (ln'(var 0)) = -∞
    when ρ(0) = 0. -/

/-- **Tier 3**: Unconditional soundness is impossible. There exist finite
    environments where Step does not preserve evaluation. -/
theorem step_sound_not_unconditional
    (h_indet : E.add E.neg_inf E.pos_inf ≠ E.zro) :
    ¬∀ (ρ : Nat → α) {a b : Eml}, FinEnv ρ → Step a b → eval ρ a = eval ρ b := by
  intro h
  -- Witness: ρ = (fun _ => zro), Step = sub_self(ln'(var 0))
  have hfin : FinEnv (fun _ : Nat => E.zro : Nat → α) :=
    fun _ => ⟨E.neg_inf_ne_zro.symm, E.pos_inf_ne_zro.symm⟩
  have hstep := h (fun _ => E.zro) hfin (Step.sub_self (ln' (var 0)))
  rw [eval_sub', eval_ln', eval_zero] at hstep
  simp only [eval, E.ln_zero, E.neg_neg_inf] at hstep
  exact h_indet hstep

/-! ## Semantic equality -/

def SemEq (a b : Eml) : Prop :=
  ∀ (α : Type) [ExtExpAlgebra α] (ρ : Nat → α),
    (∀ t, @EvalFinite α _ ρ t) → @eval α _ ρ a = @eval α _ ρ b

theorem SemEq.rfl {a : Eml} : SemEq a a :=
  fun _ _ ρ _ => Eq.refl (eval ρ a)

theorem SemEq.symm {a b : Eml} (h : SemEq a b) : SemEq b a :=
  fun α _ ρ hf => (h α ρ hf).symm

theorem SemEq.trans {a b c : Eml} (h1 : SemEq a b) (h2 : SemEq b c) : SemEq a c :=
  fun α _ ρ hf => (h1 α ρ hf).trans (h2 α ρ hf)

theorem SemEq.of_steps {a b : Eml} (h : Steps a b) : SemEq a b :=
  fun _ _ ρ hf => by
    induction h with
    | refl _ => rfl
    | step _ _ _ hab _ ih => exact (step_sound_finite ρ hab hf).trans ih

end

end Eml
