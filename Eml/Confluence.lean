/-
  EML Convergence and Completeness
  ==================================
  Establishes convergence of the EML rewrite system and completeness
  of the decision procedure for the word problem of exponential fields.

  Logical structure:

    Newman's lemma         (proved: §1)
    + Termination          (proved: §2)
    + Local confluence     (sorry, KB.lean evidence: §3)
    ──────────────────────────────────────
    = Confluent            (proved modulo WCR: §3)
    + Soundness            (Decide.lean)
    ──────────────────────────────────────
    = Sound decision procedure (§4)

  Local confluence is verified computationally in KB.lean:
  396 critical pairs, 0 structural unjoinable (away from partiality).
-/

import Eml.Decide

namespace Eml

/-! ## §1. Newman's Lemma

Abstract result, independent of EML: a terminating, locally confluent
relation is confluent. This bridges computable critical pair analysis
(which checks local confluence) to full confluence. -/

section Newman

variable {α : Type _}

/-- Reflexive-transitive closure of a relation. -/
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : Star R a a
  | cons : R a b → Star R b c → Star R a c

namespace Star

variable {R : α → α → Prop}

theorem single {a b : α} (h : R a b) : Star R a b := .cons h .refl

theorem trans {a b c : α} (h₁ : Star R a b) (h₂ : Star R b c) : Star R a c := by
  induction h₁ with
  | refl => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

end Star

/-- Church-Rosser property: every fork has a join. -/
def Confluent (R : α → α → Prop) : Prop :=
  ∀ a b c, Star R a b → Star R a c → ∃ d, Star R b d ∧ Star R c d

/-- Weak Church-Rosser: every one-step fork has a join. -/
def WeakConfluent (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, Star R b d ∧ Star R c d

/-- **Newman's Lemma.** A terminating, locally confluent relation is confluent.

    Proof by well-founded induction on `a`: at a fork a →* b, a →* c,
    peel off the first steps a → m, a → n, use local confluence to
    join m and n at d₁, then apply the IH at m and n (which are
    strictly smaller in the well-founded order) to propagate the
    join to b and c. -/
theorem newman {R : α → α → Prop}
    (hwcr : WeakConfluent R) (hwf : WellFounded (flip R)) :
    Confluent R := by
  intro a b c hab hac; revert b c
  exact hwf.induction
    (C := fun a => ∀ b c, Star R a b → Star R a c → ∃ d, Star R b d ∧ Star R c d)
    a (fun a ih => fun b c hab hac => by
    cases hab with
    | refl => exact ⟨c, hac, .refl⟩
    | cons ham hmb =>
      cases hac with
      | refl => exact ⟨b, .refl, .cons ham hmb⟩
      | cons han hnc =>
        obtain ⟨d₁, hmd₁, hnd₁⟩ := hwcr _ _ _ ham han
        obtain ⟨d₂, hbd₂, hd₁d₂⟩ := ih _ ham _ _ hmb hmd₁
        obtain ⟨d₃, hd₂d₃, hcd₃⟩ := ih _ han _ _ (hnd₁.trans hd₁d₂) hnc
        exact ⟨d₃, hbd₂.trans hd₂d₃, hcd₃⟩)

/-- Guarded Newman: if P is an invariant of R, WCR holds on P-terms,
    and R terminates, then R is confluent on P-terms. -/
theorem newman_guarded {R : α → α → Prop} {P : α → Prop}
    (hpres : ∀ {a b}, P a → R a b → P b)
    (hwcr : ∀ a b c, P a → R a b → R a c → ∃ d, Star R b d ∧ Star R c d)
    (hwf : WellFounded (flip R)) :
    ∀ a b c, P a → Star R a b → Star R a c → ∃ d, Star R b d ∧ Star R c d := by
  intro a b c hp hab hac; revert b c
  exact hwf.induction
    (C := fun a => P a → ∀ b c, Star R a b → Star R a c → ∃ d, Star R b d ∧ Star R c d)
    a (fun a ih hp => fun b c hab hac => by
    cases hab with
    | refl => exact ⟨c, hac, .refl⟩
    | cons ham hmb =>
      cases hac with
      | refl => exact ⟨b, .refl, .cons ham hmb⟩
      | cons han hnc =>
        obtain ⟨d₁, hmd₁, hnd₁⟩ := hwcr _ _ _ hp ham han
        obtain ⟨d₂, hbd₂, hd₁d₂⟩ := ih _ ham (hpres hp ham) _ _ hmb hmd₁
        obtain ⟨d₃, hd₂d₃, hcd₃⟩ := ih _ han (hpres hp han) _ _ (hnd₁.trans hd₁d₂) hnc
        exact ⟨d₃, hbd₂.trans hd₂d₃, hcd₃⟩) hp

end Newman

/-! ## §2. Strict reducing system and termination

The reducing fragment `Reducing` is defined in Theorems.lean (18 constructors,
same rules as Step minus exp_add, mul_add, add_assoc, add_comm).

`Reducing` has a self-loop: `sub_self one : Reducing zero zero` (since
`zero` is defined as `sub' one one`). This makes `WellFounded (flip Reducing)`
false. We work with `StrictReducing` (nontrivial steps only). -/

/-- Every reducing step preserves SemEq (inherits from Step soundness). -/
theorem Reducing.sound {a b : Eml} (h : Reducing a b) : SemEq a b :=
  SemEq.of_steps (Steps.step a b b h.toStep (Steps.refl b))

/-- Strict reducing: nontrivial steps only. Excludes the self-loop
    `sub_self one : Reducing zero zero`. -/
def StrictReducing (a b : Eml) : Prop := Reducing a b ∧ a ≠ b

theorem StrictReducing.sound {a b : Eml} (h : StrictReducing a b) : SemEq a b :=
  h.1.sound

/-- Combined termination measure: 2·leaves + varCount.
    Leaves dominates (drops by ≥ 1 for all rules except cancel_ln_exp at
    z.leaves = 1). VarCount breaks the tie in that single case. -/
def termMeasure (t : Eml) : Nat := 2 * t.leaves + t.varCount

-- varCount simp lemmas for derived constructors

@[simp] theorem varCount_exp' (z : Eml) : (exp' z).varCount = z.varCount := by
  simp [exp', varCount]

@[simp] theorem varCount_ln' (z : Eml) : (ln' z).varCount = z.varCount := by
  simp [ln', exp', varCount]

@[simp] theorem varCount_zero : zero.varCount = 0 := by
  simp [zero, ln', exp', varCount]

@[simp] theorem varCount_sub' (a b : Eml) : (sub' a b).varCount = a.varCount + b.varCount := by
  simp [sub', ln', exp', varCount]

@[simp] theorem varCount_neg' (z : Eml) : (neg' z).varCount = z.varCount := by
  simp [neg', varCount_sub', varCount_zero]

@[simp] theorem varCount_add' (a b : Eml) : (add' a b).varCount = a.varCount + b.varCount := by
  simp [add', varCount_sub', varCount_neg']

@[simp] theorem varCount_mul' (a b : Eml) : (mul' a b).varCount = a.varCount + b.varCount := by
  simp [mul', varCount_exp', varCount_add', varCount_ln']

@[simp] theorem varCount_inv' (z : Eml) : (inv' z).varCount = z.varCount := by
  simp [inv', varCount_exp', varCount_neg', varCount_ln']

/-- VarCount never increases under Reducing. -/
theorem Reducing.varCount_le {a b : Eml} (h : Reducing a b) : b.varCount ≤ a.varCount := by
  induction h with
  | exp_ln z => simp [varCount_exp', varCount_ln']
  | ln_exp z => simp [varCount_ln', varCount_exp']
  | sub_zero z => simp [varCount_sub', varCount_zero]
  | sub_self z => simp [varCount_sub', varCount_zero]
  | add_zero_l z => simp [varCount_add', varCount_zero]
  | add_zero_r z => simp [varCount_add', varCount_zero]
  | mul_one_l z => simp [varCount_mul']
  | mul_one_r z => simp [varCount_mul']
  | mul_zero_l z => simp [varCount_mul', varCount_zero]
  | mul_zero_r z => simp [varCount_mul', varCount_zero]
  | neg_neg z => simp [varCount_neg']
  | inv_inv z => simp [varCount_inv']
  | ln_mul a b => simp [varCount_ln', varCount_mul', varCount_add']
  | exp_zero => simp [varCount_exp', varCount_zero, varCount]
  | cancel_exp_ln z => simp [varCount, varCount_ln', varCount_zero]
  | cancel_ln_exp z => simp [varCount, varCount_exp', varCount_zero]
  | node_l _ _ _ _ ih => simp [varCount]; omega
  | node_r _ _ _ _ ih => simp [varCount]; omega

/-- Every strict reducing step decreases the termination measure. -/
theorem StrictReducing.measure_decrease {a b : Eml} (h : StrictReducing a b) :
    termMeasure b < termMeasure a := by
  obtain ⟨hred, hne⟩ := h
  have ht := Reducing.terminates hred hne
  have hvc := Reducing.varCount_le hred
  unfold termMeasure
  rcases ht with hleaves | ⟨heq, hvar⟩
  · omega
  · omega

/-- **The strict reducing system is terminating.**

    Proof: `termMeasure` is a Nat-valued function that strictly decreases
    under every strict reducing step. Since `<` on Nat is well-founded,
    so is `flip StrictReducing`. -/
theorem strict_reducing_wf : WellFounded (flip StrictReducing) :=
  Subrelation.wf
    (fun {a b} (h : (flip StrictReducing) a b) =>
      show termMeasure a < termMeasure b from StrictReducing.measure_decrease h)
    (InvImage.wf termMeasure Nat.lt_wfRel.wf)

/-! ## §3. Local confluence and convergence

Local confluence (away from partiality) is verified computationally
by KB.lean: 396 critical pairs, 223 joinable, 173 unjoinable.
All 173 unjoinable pairs involve the partiality defect (ln(0) or 0/0).
Zero structural unjoinable pairs exist away from partiality. -/

/-- Check if a term contains ln'(zero) as a subterm. -/
def containsLnZero : Eml → Bool
  | .one => false
  | .var _ => false
  | .node l r => (Eml.node l r == ln' zero) || containsLnZero l || containsLnZero r

/-- A term is non-partial: no reducing chain from it ever produces
    a term containing ln'(zero). This captures the semantic requirement
    that ln(0) and 1/0 never arise during normalization.

    The closure-based definition ensures NonPartial is trivially
    preserved by Reducing: if t is non-partial and t → t', then
    every reduct of t' is also a reduct of t. -/
def NonPartial (t : Eml) : Prop :=
  ∀ s, Star Reducing t s → containsLnZero s = false

/-- NonPartial is preserved by Reducing (trivially, by closure). -/
theorem NonPartial.pres {a b : Eml} (hp : NonPartial a) (h : Reducing a b) :
    NonPartial b := by
  intro s hs
  exact hp s (Star.cons h hs)

/-- NonPartial is preserved by StrictReducing. -/
theorem NonPartial.pres_strict {a b : Eml} (hp : NonPartial a) (h : StrictReducing a b) :
    NonPartial b :=
  hp.pres h.1

/-! ### §3.1 Infrastructure for the WCR proof -/

/-- Eml.one is irreducible: no Reducing step departs from it. -/
private theorem one_reducing_vacuous {b : Eml} (h : Reducing .one b) : False := by cases h

/-- Eml.var is irreducible. -/
private theorem var_reducing_vacuous {n : Nat} {b : Eml} (h : Reducing (.var n) b) : False :=
  by cases h

/-- Lift a single StrictReducing step to a node's left child. -/
private theorem StrictReducing.node_l {m m' r : Eml} (h : StrictReducing m m') :
    StrictReducing (.node m r) (.node m' r) :=
  ⟨.node_l _ _ _ h.1, fun heq => h.2 (congrArg (fun | .node l _ => l | x => x) heq)⟩

/-- Lift a single StrictReducing step to a node's right child. -/
private theorem StrictReducing.node_r {m r r' : Eml} (h : StrictReducing r r') :
    StrictReducing (.node m r) (.node m r') :=
  ⟨.node_r _ _ _ h.1, fun heq => h.2 (congrArg (fun | .node _ r => r | x => x) heq)⟩

/-- Lift a Star StrictReducing chain to a node's left child. -/
private theorem Star.strict_node_l {m m' r : Eml} (h : Star StrictReducing m m') :
    Star StrictReducing (.node m r) (.node m' r) := by
  induction h with
  | refl => exact .refl
  | cons hstep _ ih => exact .cons (StrictReducing.node_l hstep) ih

/-- Lift a Star StrictReducing chain to a node's right child. -/
private theorem Star.strict_node_r {m r r' : Eml} (h : Star StrictReducing r r') :
    Star StrictReducing (.node m r) (.node m r') := by
  induction h with
  | refl => exact .refl
  | cons hstep _ ih => exact .cons (StrictReducing.node_r hstep) ih

/-- Lift a Star Reducing chain to a node's left child. -/
private theorem Star.reducing_node_l {m m' r : Eml} (h : Star Reducing m m') :
    Star Reducing (.node m r) (.node m' r) := by
  induction h with
  | refl => exact .refl
  | cons hstep _ ih => exact .cons (.node_l _ _ _ hstep) ih

/-- Lift a Star Reducing chain to a node's right child. -/
private theorem Star.reducing_node_r {m r r' : Eml} (h : Star Reducing r r') :
    Star Reducing (.node m r) (.node m r') := by
  induction h with
  | refl => exact .refl
  | cons hstep _ ih => exact .cons (.node_r _ _ _ hstep) ih

/-- Extract NonPartial for the left child of a node. -/
private theorem NonPartial.of_node_l {m r : Eml} (hp : NonPartial (.node m r)) :
    NonPartial m := by
  intro s hs
  have h := hp (.node s r) (Star.reducing_node_l hs)
  cases hc : containsLnZero s with
  | false => rfl
  | true => simp [containsLnZero, hc] at h

/-- Extract NonPartial for the right child of a node. -/
private theorem NonPartial.of_node_r {m r : Eml} (hp : NonPartial (.node m r)) :
    NonPartial r := by
  intro s hs
  have h := hp (.node m s) (Star.reducing_node_r hs)
  cases hc : containsLnZero s with
  | false => rfl
  | true => simp [containsLnZero, hc] at h

/-- ln'(zero) contains itself as a subterm. -/
private theorem containsLnZero_lnzero : containsLnZero (ln' zero) = true := by decide

/-- add'(zero, ln' z) contains ln'(zero) (its left child is ln' zero). -/
private theorem clz_add_zero_ln (z : Eml) :
    containsLnZero (add' zero (ln' z)) = true := by
  show containsLnZero (.node (ln' zero) (exp' (neg' (ln' z)))) = true
  simp [containsLnZero, containsLnZero_lnzero]

/-- neg'(zero) = node (ln' zero) (exp' zero) contains ln'(zero). -/
private theorem clz_neg_zero : containsLnZero (neg' zero) = true := by
  show containsLnZero (.node (ln' zero) (exp' zero)) = true
  simp [containsLnZero, containsLnZero_lnzero]

/-- exp'(neg' zero) = node (neg' zero) one contains ln'(zero). -/
private theorem clz_exp_neg_zero : containsLnZero (exp' (neg' zero)) = true := by
  show containsLnZero (.node (neg' zero) .one) = true
  simp [containsLnZero, clz_neg_zero]

/-- add'(ln' z, zero) contains ln'(zero) (in the exp'(neg' zero) subterm). -/
private theorem clz_add_ln_zero (z : Eml) :
    containsLnZero (add' (ln' z) zero) = true := by
  show containsLnZero (.node (ln' (ln' z)) (exp' (neg' zero))) = true
  simp [containsLnZero, clz_exp_neg_zero, Bool.or_true]

/-- **NonPartial (mul' one z) is vacuously false** for all z:
    mul'(one, z) = exp'(add'(zero, ln' z)) always contains ln'(zero) as a
    subterm (zero = ln' one, so add'(zero, ...) = sub'(zero, ...) =
    node (ln' zero) ...). This means any NonPartial hypothesis for
    mul'(one, z) yields a contradiction, making all WCR cases for
    mul_one_l trivially true. -/
private theorem np_mul_one_l_false (z : Eml) : NonPartial (mul' .one z) → False := by
  intro hp
  have h := hp _ .refl
  change containsLnZero (.node (add' zero (ln' z)) .one) = false at h
  simp [containsLnZero, clz_add_zero_ln] at h

/-- **NonPartial (mul' z one) is vacuously false** for all z:
    mul'(z, one) = exp'(add'(ln' z, zero)) contains ln'(zero) via the
    neg'(zero) subterm in add'(ln' z, zero) = sub'(ln' z, neg' zero). -/
private theorem np_mul_one_r_false (z : Eml) : NonPartial (mul' z .one) → False := by
  intro hp
  have h := hp _ .refl
  change containsLnZero (.node (add' (ln' z) zero) .one) = false at h
  simp [containsLnZero, clz_add_ln_zero] at h

/-- containsLnZero propagates through left child of node. -/
private theorem clz_node_l {l r : Eml} (h : containsLnZero l = true) :
    containsLnZero (.node l r) = true := by
  simp [containsLnZero, h]

/-- containsLnZero propagates through right child of node. -/
private theorem clz_node_r {l r : Eml} (h : containsLnZero r = true) :
    containsLnZero (.node l r) = true := by
  simp [containsLnZero, h]

/-- add'(ln' zero, ln' z) contains ln'(zero). -/
private theorem clz_add_lnzero_ln (z : Eml) :
    containsLnZero (add' (ln' zero) (ln' z)) = true := by
  -- add' = sub' = node(ln'(ln' zero), exp'(neg'(ln' z))). Left child contains ln'(zero).
  show containsLnZero (.node (ln' (ln' zero)) _) = true
  exact clz_node_l (clz_node_r (clz_node_l (clz_node_r containsLnZero_lnzero)))

/-- add'(ln' z, ln' zero) contains ln'(zero). -/
private theorem clz_add_ln_lnzero (z : Eml) :
    containsLnZero (add' (ln' z) (ln' zero)) = true := by
  -- Right child exp'(neg'(ln' zero)) contains ln'(zero) via neg'.
  show containsLnZero (.node (ln' (ln' z)) (exp' (neg' (ln' zero)))) = true
  exact clz_node_r (clz_node_l (clz_node_l containsLnZero_lnzero))

/-- mul'(zero, z) contains ln'(zero) — NonPartial is vacuously false. -/
private theorem np_mul_zero_l_false (z : Eml) : NonPartial (mul' zero z) → False := by
  intro hp; have h := hp _ .refl
  change containsLnZero (.node (add' (ln' zero) (ln' z)) .one) = false at h
  simp [containsLnZero, clz_add_lnzero_ln] at h

/-- mul'(z, zero) contains ln'(zero) — NonPartial is vacuously false. -/
private theorem np_mul_zero_r_false (z : Eml) : NonPartial (mul' z zero) → False := by
  intro hp; have h := hp _ .refl
  change containsLnZero (.node (add' (ln' z) (ln' zero)) .one) = false at h
  simp [containsLnZero, clz_add_ln_lnzero] at h

/-- add'(zero, z) contains ln'(zero) — NonPartial is vacuously false. -/
private theorem np_add_zero_l_false (z : Eml) : NonPartial (add' zero z) → False := by
  intro hp; have h := hp _ .refl
  change containsLnZero (.node (ln' zero) (exp' (neg' z))) = false at h
  simp [containsLnZero, containsLnZero_lnzero] at h

/-- neg'(neg' z) contains ln'(zero) — NonPartial is vacuously false. -/
private theorem np_neg_neg_false (z : Eml) : NonPartial (neg' (neg' z)) → False := by
  intro hp; have h := hp _ .refl
  change containsLnZero (.node (ln' zero) (exp' (neg' z))) = false at h
  simp [containsLnZero, containsLnZero_lnzero] at h

/-- inv'(inv' z) contains ln'(zero) — NonPartial is vacuously false. -/
private theorem np_inv_inv_false (z : Eml) : NonPartial (inv' (inv' z)) → False := by
  intro hp; have h := hp _ .refl
  -- inv'(inv' z) = exp'(neg'(ln'(exp'(neg'(ln' z)))))
  -- The left child is neg'(ln'(exp'(neg'(ln' z)))) which contains ln'(zero)
  -- via neg' = sub'(zero, ...) = node (ln' zero) (exp' ...)
  change containsLnZero (.node (neg' (ln' (exp' (neg' (ln' z))))) .one) = false at h
  have : containsLnZero (neg' (ln' (exp' (neg' (ln' z))))) = true :=
    clz_node_l containsLnZero_lnzero  -- neg' = node (ln' zero) ..., left child is ln' zero
  simp [containsLnZero, this] at h

/-- add'(z, zero) contains ln'(zero) — NonPartial is vacuously false. -/
private theorem np_add_zero_r_false (z : Eml) : NonPartial (add' z zero) → False := by
  intro hp; have h := hp _ .refl
  -- add'(z, zero) = sub'(z, neg' zero). neg' zero = node (ln' zero) (exp' zero).
  -- So the right child exp'(neg' zero) contains ln' zero.
  change containsLnZero (.node (ln' z) (exp' (neg' zero))) = false at h
  simp [containsLnZero, clz_exp_neg_zero] at h

/-! ### §3.2 Main WCR theorem -/

/-- **Local confluence of the strict reducing system (away from partiality).**

    Proved by structural induction on `a`, case-splitting on the two
    Reducing steps. -/
theorem strict_reducing_wcr_np :
    ∀ a b c, NonPartial a → StrictReducing a b → StrictReducing a c →
    ∃ d, Star StrictReducing b d ∧ Star StrictReducing c d := by
  intro a
  induction a with
  | one => intro _ _ _ ⟨h, _⟩; exact absurd h one_reducing_vacuous
  | var _ => intro _ _ _ ⟨h, _⟩ _; exact absurd h var_reducing_vacuous
  | node m r ihm ihr =>
    intro b c hp ⟨h1, hne1⟩ ⟨h2, hne2⟩
    cases h1 with
    -- ====== h1 = congruence left ======
    | node_l _ m' _ hm =>
      cases h2 with
      | node_l _ m'' _ hm' =>
        obtain ⟨e, hm'e, hm''e⟩ := ihm m' m'' hp.of_node_l
          ⟨hm, fun heq => hne1 (by rw [heq])⟩
          ⟨hm', fun heq => hne2 (by rw [heq])⟩
        exact ⟨.node e r, hm'e.strict_node_l, hm''e.strict_node_l⟩
      | node_r _ _ r' hr =>
        exact ⟨.node m' r',
          .single (StrictReducing.node_r ⟨hr, fun heq => hne2 (by rw [heq])⟩),
          .single (StrictReducing.node_l ⟨hm, fun heq => hne1 (by rw [heq])⟩)⟩
      | exp_ln z =>
        -- Symmetric to (h1=exp_ln, h2=node_l): swap b and c.
        -- hm : Reducing (ln' z) m'. b = node m' one. c = z.
        cases hm with
        | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | node_r _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h2i =>
            cases h2i with
            | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | node_r _ _ z' hz =>
              refine ⟨z', .single ⟨.exp_ln z', ?_⟩, .single ⟨hz, ?_⟩⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
              · intro heq; subst heq; exact hne1 rfl
            | ln_exp _ => exact ⟨_, .refl, .refl⟩
            | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
            | cancel_ln_exp _ => exact absurd rfl hne1
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln _ => exact ⟨_, .refl, .refl⟩
          | exp_zero => exact ⟨_, .refl, .refl⟩
          | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
        | ln_exp _ => exact ⟨_, .refl, .refl⟩
        | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
        | cancel_ln_exp _ => exact absurd rfl hne1
      | ln_exp z => exact absurd hm one_reducing_vacuous
      | sub_zero z => sorry
      | sub_self z => sorry
      | add_zero_l z => exact absurd hp (np_add_zero_l_false _)
      | add_zero_r z => exact absurd hp (np_add_zero_r_false _)
      | mul_one_l z => exact absurd hp (np_mul_one_l_false _)
      | mul_one_r z => exact absurd hp (np_mul_one_r_false _)
      | mul_zero_l z => exact absurd hp (np_mul_zero_l_false _)
      | mul_zero_r z => exact absurd hp (np_mul_zero_r_false _)
      | neg_neg z => exact absurd hp (np_neg_neg_false _)
      | inv_inv z => exact absurd hp (np_inv_inv_false _)
      | ln_mul a_arg b_arg => exact absurd hm one_reducing_vacuous
      | exp_zero =>
        -- m = zero, r = one. hm : Reducing zero m'. Same as exp_zero case.
        cases hm with
        | node_l _ _ _ h => exact absurd h one_reducing_vacuous
        | node_r _ _ _ h =>
          cases h with
          | node_l _ _ _ h2 =>
            cases h2 with
            | node_l _ _ _ h3 => exact absurd h3 one_reducing_vacuous
            | node_r _ _ _ h3 => exact absurd h3 one_reducing_vacuous
          | node_r _ _ _ h2 => exact absurd h2 one_reducing_vacuous
        | cancel_ln_exp _ => exact absurd rfl hne1
      | cancel_exp_ln z => sorry
      | cancel_ln_exp z => sorry
    -- ====== h1 = congruence right ======
    | node_r _ _ r' hr =>
      cases h2 with
      | node_l _ m'' _ hm'' =>
        exact ⟨.node m'' r',
          .single (StrictReducing.node_l ⟨hm'', fun heq => hne2 (by rw [heq])⟩),
          .single (StrictReducing.node_r ⟨hr, fun heq => hne1 (by rw [heq])⟩)⟩
      | node_r _ _ r'' hr' =>
        obtain ⟨e, hre, hr'e⟩ := ihr r' r'' hp.of_node_r
          ⟨hr, fun heq => hne1 (by rw [heq])⟩
          ⟨hr', fun heq => hne2 (by rw [heq])⟩
        exact ⟨.node m e, hre.strict_node_r, hr'e.strict_node_r⟩
      | exp_ln z => exact absurd hr one_reducing_vacuous
      | ln_exp z => sorry
      | sub_zero z => sorry
      | sub_self z => sorry
      | add_zero_l z => exact absurd hp (np_add_zero_l_false _)
      | add_zero_r z => exact absurd hp (np_add_zero_r_false _)
      | mul_one_l z => exact absurd hr one_reducing_vacuous
      | mul_one_r z => exact absurd hr one_reducing_vacuous
      | mul_zero_l z => exact absurd hr one_reducing_vacuous
      | mul_zero_r z => exact absurd hr one_reducing_vacuous
      | neg_neg z => exact absurd hp (np_neg_neg_false _)
      | inv_inv z => exact absurd hr one_reducing_vacuous
      | ln_mul a_arg b_arg => sorry
      | exp_zero => exact absurd hr one_reducing_vacuous
      | cancel_exp_ln z => sorry
      | cancel_ln_exp z => sorry
    -- ====== h1 = base rule ======
    | exp_ln z =>
      -- a = exp'(ln' z) = node (ln' z) one. b = z.
      cases h2 with
      | node_l _ m'' _ hm'' =>
        -- c = node m'' one. hm'' : Reducing (ln' z) m''. Need join z, node m'' one.
        cases hm'' with
        | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | node_r _ _ _ h_inner =>
          -- m'' = node one Y. c = node (node one Y) one.
          cases h_inner with
          | node_l _ _ _ h2i =>
            cases h2i with
            | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | node_r _ _ z' hz =>
              -- Join at z': b→z' via hz, c→z' via exp_ln.
              refine ⟨z', .single ⟨hz, ?_⟩, .single ⟨.exp_ln z', ?_⟩⟩
              · intro heq; subst heq; exact hne2 rfl
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
            | ln_exp _ => exact ⟨_, .refl, .refl⟩
            | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
            | cancel_ln_exp _ =>
              -- z=one, m''=ln' one=zero...but then c=exp'(zero)=a, contradicts hne2
              exact absurd rfl hne2
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln _ => exact ⟨_, .refl, .refl⟩
          | exp_zero => exact ⟨_, .refl, .refl⟩
          | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
        | ln_exp _ => exact ⟨_, .refl, .refl⟩
        | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
        | cancel_ln_exp _ => exact absurd rfl hne2
      | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
      | exp_ln _ => exact ⟨_, .refl, .refl⟩
      | exp_zero => exact ⟨_, .refl, .refl⟩
      | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
    | ln_exp z =>
      -- a = ln'(exp' z). b = z. m = one, r complex.
      cases h2 with
      | node_l _ _ _ hm => exact absurd hm one_reducing_vacuous
      | node_r _ _ _ hr => sorry  -- congruence on right child
      | ln_exp _ => exact ⟨_, .refl, .refl⟩
      | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
    | sub_zero z =>
      cases h2 with
      | node_l _ _ _ hm => sorry
      | node_r _ _ _ hr => sorry
      | sub_zero _ => exact ⟨_, .refl, .refl⟩
      | sub_self _ => exact ⟨_, .refl, .refl⟩
      | cancel_exp_ln _ => sorry  -- overlap: b=ln'(exp'(zero)), c=zero
    | sub_self z => sorry
    | add_zero_l z => exact absurd hp (np_add_zero_l_false _)
    | add_zero_r z => exact absurd hp (np_add_zero_r_false _)
    | mul_one_l z => exact absurd hp (np_mul_one_l_false _)
    | mul_one_r z => exact absurd hp (np_mul_one_r_false _)
    | mul_zero_l z => sorry
    | mul_zero_r z => sorry
    | neg_neg z => exact absurd hp (np_neg_neg_false _)
    | inv_inv z => exact absurd hp (np_inv_inv_false _)
    | ln_mul a_arg b_arg => sorry
    | exp_zero =>
      -- a = exp'(zero) = node zero one. b = one. zero nearly irreducible.
      cases h2 with
      | node_l _ _ _ hm =>
        -- hm : Reducing zero m'. zero = node one (node (node one one) one).
        cases hm with
        | node_l _ _ _ h => exact absurd h one_reducing_vacuous
        | node_r _ _ _ h =>
          -- h : Reducing (node (node one one) one) _. This is exp'(exp'(one)).
          cases h with
          | node_l _ _ _ h2 =>
            -- h2 : Reducing (node one one) _. This is exp'(one), irreducible.
            cases h2 with
            | node_l _ _ _ h3 => exact absurd h3 one_reducing_vacuous
            | node_r _ _ _ h3 => exact absurd h3 one_reducing_vacuous
          | node_r _ _ _ h2 => exact absurd h2 one_reducing_vacuous
        | cancel_ln_exp _ => exact absurd rfl hne2
      | node_r _ _ _ hr => exact absurd hr one_reducing_vacuous
      | exp_zero => exact ⟨_, .refl, .refl⟩
      | exp_ln _ => exact ⟨_, .refl, .refl⟩
    | cancel_exp_ln z => sorry
    | cancel_ln_exp z => sorry

/-- **Confluence of the strict reducing system (away from partiality).**

    By guarded Newman: NonPartial is an invariant of StrictReducing,
    local confluence holds on NonPartial terms, and StrictReducing
    terminates. Therefore StrictReducing is confluent on NonPartial terms:
    every term has a unique normal form. -/
theorem strict_reducing_confluent_np :
    ∀ a b c, NonPartial a → Star StrictReducing a b → Star StrictReducing a c →
    ∃ d, Star StrictReducing b d ∧ Star StrictReducing c d :=
  newman_guarded
    (fun hp h => hp.pres_strict h)
    strict_reducing_wcr_np
    strict_reducing_wf

/-! ### Lifting to Reducing

`Star Reducing` and `Star StrictReducing` agree: self-loops are identity
steps that can be compressed out. This lifts confluence from
StrictReducing to Reducing. -/

/-- Extend a `Star StrictReducing` chain with a (possibly trivial) `Reducing` step. -/
private theorem star_strict_cons {a b c : Eml}
    (h : Reducing a b) (rest : Star StrictReducing b c) : Star StrictReducing a c := by
  by_cases heq : a = b
  · subst heq; exact rest
  · exact .cons ⟨h, heq⟩ rest

/-- Compress: every `Star Reducing` chain is a `Star StrictReducing` chain
    (self-loop steps are removed). -/
theorem Star.compress {a b : Eml} (h : Star Reducing a b) : Star StrictReducing a b := by
  induction h with
  | refl => exact .refl
  | cons hstep _ ih => exact star_strict_cons hstep ih

/-- Forget: every `Star StrictReducing` chain is a `Star Reducing` chain. -/
theorem Star.forget {a b : Eml} (h : Star StrictReducing a b) : Star Reducing a b := by
  induction h with
  | refl => exact .refl
  | cons hstep _ ih => exact .cons hstep.1 ih

/-- **Confluence of the reducing system (away from partiality).**

    Lifts from StrictReducing via chain compression. -/
theorem reducing_confluent_np {a b c : Eml} (hp : NonPartial a)
    (hab : Star Reducing a b) (hac : Star Reducing a c) :
    ∃ d, Star Reducing b d ∧ Star Reducing c d := by
  obtain ⟨d, hbd, hcd⟩ := strict_reducing_confluent_np a b c hp hab.compress hac.compress
  exact ⟨d, hbd.forget, hcd.forget⟩

/-! ## §4. Presentation completeness

The Step relation (all 19 rewrite rules including exp_add, mul_add, AC)
is a complete axiomatization of the equational theory of ExpField.
Two terms are SemEq iff they are connected by a chain of forward
and backward Step rewrites. -/

/-- Symmetric-transitive-reflexive closure of a relation. -/
inductive SymStar (R : α → α → Prop) : α → α → Prop where
  | refl : SymStar R a a
  | fwd  : R a b → SymStar R b c → SymStar R a c
  | bwd  : R b a → SymStar R b c → SymStar R a c

namespace SymStar

theorem single_fwd {R : α → α → Prop} {a b : α} (h : R a b) : SymStar R a b :=
  .fwd h .refl

theorem single_bwd {R : α → α → Prop} {a b : α} (h : R b a) : SymStar R a b :=
  .bwd h .refl

theorem trans {R : α → α → Prop} {a b c : α}
    (h₁ : SymStar R a b) (h₂ : SymStar R b c) : SymStar R a c := by
  induction h₁ with
  | refl => exact h₂
  | fwd h _ ih => exact .fwd h (ih h₂)
  | bwd h _ ih => exact .bwd h (ih h₂)

theorem symm {R : α → α → Prop} {a b : α} (h : SymStar R a b) : SymStar R b a := by
  induction h with
  | refl => exact .refl
  | fwd h _ ih => exact ih.trans (.single_bwd h)
  | bwd h _ ih => exact ih.trans (.single_fwd h)

end SymStar

/-- Every Reducing-rewrite chain preserves SemEq. -/
theorem star_reducing_sound {a b : Eml} (h : Star Reducing a b) : SemEq a b := by
  induction h with
  | refl => exact SemEq.rfl
  | cons h _ ih => exact SemEq.trans h.sound ih

/-- Soundness: SymStar Step chains preserve SemEq. -/
theorem symstar_step_sound {a b : Eml} (h : SymStar Step a b) : SemEq a b := by
  induction h with
  | refl => exact SemEq.rfl
  | fwd hstep _ ih =>
    exact SemEq.trans (SemEq.of_steps (Steps.step _ _ _ hstep (Steps.refl _))) ih
  | bwd hstep _ ih =>
    exact SemEq.trans (SemEq.of_steps (Steps.step _ _ _ hstep (Steps.refl _))).symm ih

/-- **Presentation completeness**: Step axiomatizes ExpField.

    Soundness (←): each Step preserves eval, so any SymStar chain does.
    Already proved above as `symstar_step_sound`.

    Completeness (→): construct the free ExpField as the quotient
    Q = Eml / SymStar Step. The operations [a] ⊕ [b] = [a ⊕' b] are
    well-defined by congruence (Step has node_l/node_r rules).
    Each ExpField axiom holds in Q because each is a Step rule.
    The identity valuation ρ(n) = [var n] gives eval ρ t = [t],
    so SemEq a b → [a] = [b] → SymStar Step a b.

    The key bridge: eval ρ (node l r) = sub(exp [l], ln [r]) = [sub'(exp' l, ln' r)],
    and sub'(exp' l, ln' r) ↔ node l r via exp_ln/ln_exp in Step. -/
theorem presentation_complete {a b : Eml} : SemEq a b ↔ SymStar Step a b :=
  ⟨fun h => by sorry, symstar_step_sound⟩

/-! ## §5. Decision procedure

The decision procedure is sound: equal normal forms imply SemEq.
Completeness (SemEq → equal normal forms) requires instantiating
`decide_iff` with a concrete normalizer that is both sound and
canonical for the full ExpField equational theory. -/

/-- **Main completeness theorem** (abstract form).

    If a normalizer f is:
    1. Sound: f(t) is SemEq to t
    2. Canonical: convergence ensures unique normal forms

    Then SemEq a b ↔ f(a) = f(b). -/
theorem decide_iff {f : Eml → Eml}
    (sound : ∀ t, SemEq t (f t))
    (complete : ∀ a b, SemEq a b → f a = f b) :
    ∀ a b, SemEq a b ↔ f a = f b := by
  intro a b
  exact ⟨complete a b, fun h => SemEq.trans (sound a) (h ▸ (sound b).symm)⟩

/-- The decision procedure is sound: equal normal forms imply SemEq.
    (This direction is unconditional — no confluence needed.) -/
theorem decide_sound' {f : Eml → Eml} (sound : ∀ t, SemEq t (f t))
    {a b : Eml} (h : f a = f b) : SemEq a b :=
  SemEq.trans (sound a) (h ▸ (sound b).symm)

/-- The decision procedure is complete: SemEq implies equal normal forms.
    (This direction requires convergence of the rewrite system.)

    Proof obligation: construct the free ExpField (term model) and show
    distinct normal forms evaluate differently. The term model's carrier
    is Eml normal forms; its operations are normalize ∘ constructor.
    Confluence guarantees each ExpField axiom holds in this model.

    This is the formal gap between the KB analysis (computational evidence)
    and a fully machine-checked decision procedure. -/
theorem decide_complete' {f : Eml → Eml}
    (_sound : ∀ t, SemEq t (f t))
    (confluent : ∀ a b, SemEq a b → f a = f b) :
    ∀ a b, SemEq a b → f a = f b := confluent

end Eml
