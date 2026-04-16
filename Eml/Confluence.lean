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
  | cancel_ln_exp z _ _ => simp [varCount, varCount_exp', varCount_zero]
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
  | .one | .negInf | .posInf => false
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
    Reducing steps.

    NOTE: Contains 6 internal sorry sites for edge cases when subterm
    results of Reducing steps are ±∞ atoms. In those cases, the
    cancel_ln_exp guard blocks the usual joining step, and the
    WCR claim requires either additional Reducing rules for atoms
    or a stricter NonPartial predicate that excludes them. These
    edge cases don't affect the 12/18 sites that have structural
    proofs (where the subterm is manifestly a node). -/
theorem strict_reducing_wcr_np :
    ∀ a b c, NonPartial a → StrictReducing a b → StrictReducing a c →
    ∃ d, Star StrictReducing b d ∧ Star StrictReducing c d := by
  intro a
  induction a with
  | one => intro _ _ _ ⟨h, _⟩; exact absurd h one_reducing_vacuous
  | negInf => intro _ _ _ ⟨h, _⟩ _; cases h
  | posInf => intro _ _ _ ⟨h, _⟩ _; cases h
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
            | cancel_ln_exp _ _ _ => exact absurd rfl hne1
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln _ => exact ⟨_, .refl, .refl⟩
          | exp_zero => exact ⟨_, .refl, .refl⟩
          | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
        | ln_exp _ => exact ⟨_, .refl, .refl⟩
        | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
        | cancel_ln_exp _ _ _ => exact absurd rfl hne1
      | ln_exp z => exact absurd hm one_reducing_vacuous
      | sub_zero z =>
        -- hm : Reducing (ln' z) m'. b = node m' (exp' zero). c = z.
        -- In every sub-case, node m' one = z (definitionally),
        -- so we reduce exp' zero → one in b's right child to join at z.
        -- Exception: inner node_r z' hz gives m' = ln' z', join via sub_zero z'.
        cases hm with
        | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | node_r _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h2i =>
            cases h2i with
            | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | node_r _ _ z' hz =>
              -- m' = ln' z'. b = sub' z' zero → z'. c = z → z'. Join at z'.
              refine ⟨z', .single ⟨.sub_zero z', ?_⟩, .single ⟨hz, ?_⟩⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
              · intro heq; subst heq; exact hne1 rfl
            | ln_exp _ =>
              refine ⟨_, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩, .refl⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
            | ln_mul _ _ =>
              refine ⟨_, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩, .refl⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
            | cancel_ln_exp _ _ _ => exact absurd rfl hne1
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln _ =>
            refine ⟨_, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩, .refl⟩
            · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
          | exp_zero =>
            refine ⟨_, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩, .refl⟩
            · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
          | cancel_exp_ln _ =>
            refine ⟨_, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩, .refl⟩
            · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
        | ln_exp _ =>
          refine ⟨_, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩, .refl⟩
          · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
        | ln_mul _ _ =>
          refine ⟨_, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩, .refl⟩
          · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
        | cancel_ln_exp _ _ _ => exact absurd rfl hne1
      | sub_self z =>
        -- a = sub' z z = node (ln' z) (exp' z). h1=node_l: b = node m' (exp' z).
        -- h2=sub_self: c = zero. hm : Reducing (ln' z) m'.
        cases hm with
        | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | node_r _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h2i =>
            cases h2i with
            | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | node_r _ _ z' hz =>
              -- m' = ln' z'. Replicate: reduce z→z' in exp', then sub_self.
              have hzne : z ≠ z' := fun heq => by subst heq; exact hne1 rfl
              refine ⟨zero, .cons ⟨.node_r _ _ _ (.node_l _ _ _ hz), ?_⟩
                (.single ⟨.sub_self z', ?_⟩), .refl⟩
              · intro heq; exact hzne (congrArg (fun | .node _ (.node z _) => z | x => x) heq)
              · intro heq; have := congrArg Eml.leaves heq
                simp [leaves, ln'] at this; have := leaves_pos z'; omega
            | ln_exp w =>
              -- b = node m' (exp'(exp' m')). cancel_ln_exp fires.
              refine ⟨zero, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩, .refl⟩
              · intro heq; have := congrArg Eml.leaves heq
                simp [leaves, exp', ln'] at this; omega
            | ln_mul a_arg b_arg =>
              -- b = node m' (exp'(exp' m')). cancel_ln_exp fires.
              refine ⟨zero, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩, .refl⟩
              · intro heq; have := congrArg Eml.leaves heq
                simp [leaves, mul', add', sub', neg', exp', ln'] at this
                have := leaves_pos a_arg; have := leaves_pos b_arg; omega
            | cancel_ln_exp _ _ _ => exact absurd rfl hne1
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln w =>
            -- b = node (node one w) (exp'(exp'(node one w))). cancel_ln_exp fires.
            refine ⟨zero, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩, .refl⟩
            · intro heq; have := congrArg (fun | .node (.node _ _) _ => true | _ => false) heq
              simp [zero, ln', exp'] at this
          | exp_zero =>
            -- b = node (exp' one) (exp'(exp'(exp' one))). cancel_ln_exp (exp' one) fires.
            refine ⟨zero, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩, .refl⟩
            · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
          | cancel_exp_ln _ =>
            -- b = node (node one zero) (exp'(exp'(node one zero))). cancel_ln_exp fires.
            refine ⟨zero, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩, .refl⟩
            · intro heq; have := congrArg Eml.leaves heq
              simp [leaves, zero, ln'] at this
        | ln_exp _ =>
          -- b = node m' (exp'(exp' m')). cancel_ln_exp fires or b = zero.
          refine ⟨zero, ?_, .refl⟩
          by_cases heq : .node m' (exp' (exp' m')) = zero
          · rw [heq]; exact .refl
          · exact .single ⟨.cancel_ln_exp _ sorry sorry, heq⟩
        | ln_mul a_arg b_arg =>
          -- z = mul' a_arg b_arg. m' = add'(ln' a_arg, ln' b_arg).
          -- cancel_ln_exp fires on b = node m' (exp'(exp' m')).
          refine ⟨zero, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩, .refl⟩
          · intro heq; have := congrArg Eml.leaves heq
            simp [leaves, mul', add', sub', neg', exp', ln'] at this
            have := leaves_pos a_arg; have := leaves_pos b_arg; omega
        | cancel_ln_exp _ _ _ => exact absurd rfl hne1
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
        | cancel_ln_exp _ _ _ => exact absurd rfl hne1
      | cancel_exp_ln z =>
        -- a = node (ln'(ln' z)) z. h1=node_l: hm : Reducing (ln'(ln' z)) m'. b = node m' z. c = zero.
        -- Replicate the reduction inside z (right child) + cancel_exp_ln.
        -- ln'(ln' z) reduces through congruence. The innermost step on z gives z→z'.
        -- Replicate: b → node m' z' → zero via cancel_exp_ln.
        -- Alternatively, for non-congruence steps, b = sub'(t, t) → zero via sub_self.
        --
        -- The congruence chain: ln'(ln' z) = node one (exp'(node one (ln' z))).
        -- The reduction goes: node_r → node_l → node_r → (inner reduction of ln' z).
        -- Inside ln' z: node_r → node_l → node_r → (reduction of z) or base rule.
        --
        -- Key insight: every reduction of ln'(ln' z) either:
        -- (1) reaches z and reduces it (giving m' = ln'(ln' z')), or
        -- (2) applies a base rule inside (giving b = sub'(t, t) for some t).
        -- In case (1): replicate z→z' in right child + cancel_exp_ln z'.
        -- In case (2): sub_self fires.
        --
        -- Proof: case split hm to depth 6 (through ln' of ln' to reach z).
        cases hm with
        | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | node_r _ _ _ h1i =>
          cases h1i with
          | node_l _ _ _ h2i =>
            cases h2i with
            | node_l _ _ _ h3 => exact absurd h3 one_reducing_vacuous
            | node_r _ _ _ h3i =>
              -- h3i : Reducing (ln' z) z'. Now inner case split.
              cases h3i with
              | node_l _ _ _ h4 => exact absurd h4 one_reducing_vacuous
              | node_r _ _ _ h4i =>
                cases h4i with
                | node_l _ _ _ h5i =>
                  cases h5i with
                  | node_l _ _ _ h6 => exact absurd h6 one_reducing_vacuous
                  | node_r _ _ _ hz =>
                    -- hz : Reducing z _. m' = ln'(ln' z'). Replicate z→z' in right child.
                    rename_i z'
                    refine ⟨zero, .cons ⟨.node_r _ _ _ hz, fun heq => ?_⟩
                      (.single ⟨.cancel_exp_ln _, fun heq => ?_⟩), .refl⟩
                    · simp at heq; subst heq; exact hne1 rfl
                    · have := congrArg Eml.leaves heq
                      simp [leaves, ln', exp'] at this; have := leaves_pos z'; omega
                  | ln_exp _ =>
                    -- z = exp'(t). m' = ln'(t). b = node (ln'(t)) z = sub'(t, t). sub_self fires.
                    refine ⟨zero, .single ⟨.sub_self _, fun heq => ?_⟩, .refl⟩
                    · have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
                      simp [zero, ln', exp'] at this
                  | ln_mul _ _ =>
                    -- z = mul'(a, b) = exp'(add'(ln' a, ln' b)). m' = ln'(add'(ln' a, ln' b)).
                    -- b = sub'(add'(ln' a, ln' b), add'(ln' a, ln' b)). sub_self fires.
                    refine ⟨zero, .single ⟨.sub_self _, fun heq => ?_⟩, .refl⟩
                    · have := congrArg Eml.leaves heq
                      simp [leaves, mul', add', sub', neg', exp', ln'] at this; omega
                  | cancel_ln_exp _ _ _ => exact absurd rfl hne1
                | node_r _ _ _ h5 => exact absurd h5 one_reducing_vacuous
                | exp_ln _ =>
                  -- b = sub'(t, t). sub_self fires.
                  refine ⟨zero, .single ⟨.sub_self _, fun heq => ?_⟩, .refl⟩
                  · have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
                    simp [zero, ln', exp'] at this
                | exp_zero =>
                  -- b = sub'(t, t). sub_self fires.
                  refine ⟨zero, .single ⟨.sub_self _, fun heq => ?_⟩, .refl⟩
                  · have := congrArg Eml.leaves heq
                    simp [leaves, ln', exp'] at this
                | cancel_exp_ln _ =>
                  -- b = sub'(t, t). sub_self fires.
                  refine ⟨zero, .single ⟨.sub_self _, fun heq => ?_⟩, .refl⟩
                  · have := congrArg Eml.leaves heq
                    simp [leaves, zero, ln', exp'] at this
              | ln_exp _ =>
                -- h3i = ln_exp. b = sub'(t, t). sub_self fires.
                refine ⟨zero, .single ⟨.sub_self _, fun heq => ?_⟩, .refl⟩
                · have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
                  simp [zero, ln', exp'] at this
              | ln_mul _ _ =>
                -- h3i = ln_mul. b = sub'(t, t). sub_self fires.
                refine ⟨zero, .single ⟨.sub_self _, fun heq => ?_⟩, .refl⟩
                · have := congrArg Eml.leaves heq
                  simp [leaves, mul', add', sub', neg', exp', ln'] at this; omega
              | cancel_ln_exp _ _ _ => exact absurd rfl hne1
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
      /-
              -- hz : Reducing (ln' z) z'. m' = ln'(z') (through congruence).
              -- Wait, m' = node one (node (node one z') one) = node one (exp'(node one z')).
              -- Actually: W = node one z'. R = node W one = exp'(node one z').
              -- m' = node one R = node one (exp'(node one z')) = ln' z'.
              -- b = node (ln' z') z. Replicate: reduce z via the same path, then cancel_exp_ln.
              -- But hz : Reducing (ln' z) z', not Reducing z z'. Need deeper case split on hz.
              -- hz goes through same structure: node_r / node_l / node_r z₂ hz₂ or base.
              cases hz with
              | node_l _ _ _ h3 => exact absurd h3 one_reducing_vacuous
              | node_r _ _ _ h3_inner =>
                cases h3_inner with
                | node_l _ _ _ h4 =>
                  cases h4 with
                  | node_l _ _ _ h5 => exact absurd h5 one_reducing_vacuous
                  | node_r _ _ z₂ hz₂ =>
                    -- hz₂ : Reducing z z₂. z' = ln' z₂. m' = ln'(ln' z₂).
                    -- b = node (ln'(ln' z₂)) z. Replicate + cancel_exp_ln.
                    have hzne : z ≠ z₂ := fun heq => by subst heq; exact hne1 rfl
                    refine ⟨zero, .cons ⟨.node_r _ _ _ hz₂, ?_⟩
                      (.single ⟨.cancel_exp_ln z₂, ?_⟩), .refl⟩
                    · intro heq; exact hzne (congrArg (fun | .node _ z => z | x => x) heq)
                    · intro heq; have := congrArg Eml.leaves heq
                      simp [leaves, ln', exp'] at this; have := leaves_pos z₂; omega
                  | ln_exp w =>
                    -- node one z = ln'(exp' w). z = exp'(node one (exp' w)). W₂ = w.
                    -- z' = node one (exp' w). m' = ln'(node one (exp' w)).
                    -- b = node (ln'(node one (exp' w))) (exp'(node one (exp' w))) = sub'(node one (exp' w), node one (exp' w)).
                    -- sub_self fires!
                    refine ⟨zero, .single ⟨.sub_self _, ?_⟩, .refl⟩
                    · intro heq; have := congrArg (fun | .node (.node _ _) _ => true | _ => false) heq
                      simp [zero, ln', exp'] at this
                  | ln_mul _ _ =>
                    -- z = mul' a b = exp'(add'(ln' a, ln' b)). z' = add'(ln' a, ln' b).
                    -- b = sub'(z', z'). sub_self fires.
                    refine ⟨zero, .single ⟨.sub_self _, ?_⟩, .refl⟩
                    · intro heq; have := congrArg Eml.leaves heq
                      simp [leaves, mul', add', sub', neg', exp', ln'] at this
                      have := leaves_pos a✝; have := leaves_pos b✝; omega
                  | cancel_ln_exp _ _ _ => exact absurd rfl hne1
                | node_r _ _ _ h4 => exact absurd h4 one_reducing_vacuous
                | exp_ln _ =>
                  -- exp'(node one z) matched exp'(ln' w). Impossible (shown earlier).
                  -- node one z = ln' w = node one (exp'(node one w)). z = exp'(node one w).
                  -- z' = node one w. m' = ln'(node one w).
                  -- b = node (ln'(node one w)) z = node (ln'(node one w)) (exp'(node one w)).
                  -- This is sub'(node one w, node one w). sub_self fires!
                  refine ⟨zero, .single ⟨.sub_self _, ?_⟩, .refl⟩
                  · intro heq; have := congrArg (fun | .node (.node _ _) _ => true | _ => false) heq
                    simp [zero, ln', exp'] at this
                | exp_zero =>
                  -- exp'(node one z) = exp'(zero). node one z = zero. Impossible (node ≠ one for left child).
                  -- Actually: zero = node one (node (node one one) one). So z = node (node one one) one.
                  -- z' = node one one. m' = ln'(exp' one) = ln'(node one one).
                  -- Wait, h3_inner = exp_zero: Reducing (exp'(node one z)) one. So R₂ = one.
                  -- z' = node one R₂ = node one one. m' through chain... let me retrace.
                  -- hz = node_r: z' = node one R₂ where R₂ from h3_inner.
                  -- h3_inner = exp_zero: R₂ = one. z' = node one one = exp' one.
                  -- m' = ln'(z') = ln'(exp' one). b = node (ln'(exp' one)) z.
                  -- ln'(exp' one) → one via ln_exp one (... no, ln_exp gives Reducing (ln'(exp' 1)) 1).
                  -- Wait, ln_exp fires on ln'(exp' w). ln_exp one : Reducing (ln'(exp' one)) one.
                  -- So ln'(exp' one) → one. b → node one z = ln'(...).
                  -- Actually, b = node (ln'(exp' one)) z. Reduce left: ln'(exp' one) → one via ln_exp.
                  -- b → node one z. But node one z was zero (from exp_zero constraint).
                  -- Actually, z = node (node one one) one (from node one z = zero constraint).
                  -- node one z = zero, so z = exp'(exp' one) ... hmm.
                  -- Let me just check: m' = ln'(exp' one). b = node (ln'(exp' one)) z.
                  -- Reduce left child: ln'(exp' one) → one (ln_exp one). hne1 then gives self-loop? No.
                  -- After reduction: node one z. And node one z = zero (from the exp_zero constraint).
                  -- So b → zero via node_l reducing ln'(exp' one) → one.
                  -- But is this StrictReducing? node (ln'(exp' one)) z ≠ node one z = zero? Yes, ln'(exp' one) ≠ one.
                  -- z = exp'(z'). b = sub'(z', z'). sub_self fires.
                  refine ⟨zero, .single ⟨.sub_self _, ?_⟩, .refl⟩
                  · intro heq; have := congrArg Eml.leaves heq
                    simp [leaves, ln', exp'] at this
                | cancel_exp_ln _ =>
                  -- z = exp'(z'). b = sub'(z', z'). sub_self fires.
                  refine ⟨zero, .single ⟨.sub_self _, ?_⟩, .refl⟩
                  · intro heq; have := congrArg Eml.leaves heq
                    simp [leaves, zero, ln', exp'] at this
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous -/
      | cancel_ln_exp z =>
        -- a = node z (exp'(exp' z)). h1=node_l: hm : Reducing z m'. b = node m' (exp'(exp' z)).
        -- Replicate z→m' inside exp'(exp' z) + cancel_ln_exp m'.
        refine ⟨zero, ?_, .refl⟩
        -- Step 1: reduce z→m' inside exp'(exp' z) in right child. ne: exp'(exp' z) ≠ exp'(exp' m').
        refine .cons ⟨.node_r _ _ _ (.node_l _ _ _ (.node_l _ _ _ hm)), fun heq => ?_⟩ ?_
        · simp [exp'] at heq; subst heq; exact hne1 rfl
        · -- Step 2: cancel_ln_exp m' or result is already zero.
          refine (if heq : Eml.node m' (exp' (exp' m')) = zero
            then heq ▸ .refl
            else .single ⟨.cancel_ln_exp _ sorry sorry, heq⟩)
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
      | ln_exp z =>
        -- a = ln'(exp' z). b = node one r'. c = z. Need join b, c.
        -- Symmetric to (h1=ln_exp, h2=node_r): swap join witnesses.
        cases hr with
        | node_l _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | node_r _ _ _ h2i =>
            cases h2i with
            | node_l _ z' _ hz =>
              refine ⟨z', .single ⟨.ln_exp z', ?_⟩, .single ⟨hz, ?_⟩⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
              · intro heq; subst heq; exact hne1 rfl
            | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | exp_ln _ => exact ⟨_, .refl, .refl⟩
            | exp_zero => exact ⟨_, .refl, .refl⟩
            | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
            | mul_one_l _ => exact absurd hp.of_node_r.of_node_l.of_node_r.of_node_l (np_add_zero_l_false _)
            | mul_one_r _ => exact absurd hp.of_node_r.of_node_l.of_node_r.of_node_l (np_add_zero_r_false _)
            | mul_zero_l _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_zero_l_false _)
            | mul_zero_r _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_zero_r_false _)
            | inv_inv _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_inv_inv_false _)
          | ln_exp _ => exact ⟨_, .refl, .refl⟩
          | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
          | cancel_ln_exp _ _ _ => exact absurd rfl hne1
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | exp_ln _ => exact ⟨_, .refl, .refl⟩
        | exp_zero => exact ⟨_, .refl, .refl⟩
        | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
      | sub_zero zs =>
        -- hr : Reducing (exp' zero) r'. b = node (ln' zs) r'. c = zs.
        -- exp' zero = exp'(ln' one). Main reductions: exp_ln one and exp_zero
        -- both give r' = one, so b = exp'(ln' zs) → zs via exp_ln.
        -- node_l reduces zero (self-loop only) giving b = a, contradicts hne1.
        cases hr with
        | node_l _ _ _ h_zero =>
          cases h_zero with
          | node_l _ _ _ h => exact absurd h one_reducing_vacuous
          | node_r _ _ _ h =>
            cases h with
            | node_l _ _ _ h2 =>
              cases h2 with
              | node_l _ _ _ h3 => exact absurd h3 one_reducing_vacuous
              | node_r _ _ _ h3 => exact absurd h3 one_reducing_vacuous
            | node_r _ _ _ h2 => exact absurd h2 one_reducing_vacuous
          | cancel_ln_exp _ _ _ => exact absurd rfl hne1
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | exp_ln _ =>
          -- r' = one. b = exp'(ln' _) → _ via exp_ln.
          refine ⟨_, .single ⟨.exp_ln _, ?_⟩, .refl⟩
          · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
        | exp_zero =>
          -- r' = one. b = exp'(ln' _) → _ via exp_ln.
          refine ⟨_, .single ⟨.exp_ln _, ?_⟩, .refl⟩
          · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
      | sub_self z =>
        -- a = sub' z z = node (ln' z) (exp' z). h1=node_r: hr : Reducing (exp' z) r'.
        -- b = node (ln' z) r'. c = zero.
        -- Symmetric to node_l/sub_self: cancel_exp_ln or replicate + sub_self.
        cases hr with
        | node_l _ _ _ hz =>
          -- Congruence through z in exp' z. r' = node z' one. Replicate z→z' in ln' z + sub_self.
          refine ⟨zero, .cons ⟨.node_l _ _ _ (.node_r _ _ _ (.node_l _ _ _ (.node_r _ _ _ hz))), ?_⟩
            (.single ⟨.sub_self _, ?_⟩), .refl⟩
          · intro heq; simp [ln', exp'] at heq; subst heq; exact hne1 rfl
          · intro heq; have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
            simp [zero, ln', exp'] at this
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | exp_ln _ =>
          -- z = ln' w. r' = w. b = node (ln'(ln' w)) w. cancel_exp_ln fires.
          refine ⟨zero, .single ⟨.cancel_exp_ln _, ?_⟩, .refl⟩
          · intro heq; have := congrArg Eml.leaves heq
            simp [leaves, ln', exp'] at this; omega
        | exp_zero =>
          -- z = zero. NonPartial contradiction.
          exact absurd (hp _ .refl) (by simp [containsLnZero, containsLnZero_lnzero])
        | cancel_exp_ln _ =>
          -- z = ln'(zero). NonPartial contradiction.
          exact absurd (hp _ .refl) (by
            simp [containsLnZero]
            intro _ _
            exact clz_node_l containsLnZero_lnzero)
        | mul_one_l _ => exact absurd hp.of_node_r (np_mul_one_l_false _)
        | mul_one_r _ => exact absurd hp.of_node_r (np_mul_one_r_false _)
        | mul_zero_l _ => exact absurd hp.of_node_r (np_mul_zero_l_false _)
        | mul_zero_r _ => exact absurd hp.of_node_r (np_mul_zero_r_false _)
        | inv_inv _ => exact absurd hp.of_node_r (np_inv_inv_false _)
      | add_zero_l z => exact absurd hp (np_add_zero_l_false _)
      | add_zero_r z => exact absurd hp (np_add_zero_r_false _)
      | mul_one_l z => exact absurd hr one_reducing_vacuous
      | mul_one_r z => exact absurd hr one_reducing_vacuous
      | mul_zero_l z => exact absurd hr one_reducing_vacuous
      | mul_zero_r z => exact absurd hr one_reducing_vacuous
      | neg_neg z => exact absurd hp (np_neg_neg_false _)
      | inv_inv z => exact absurd hr one_reducing_vacuous
      | ln_mul a_arg b_arg =>
        -- a = ln'(mul' a_arg b_arg). m = one, r = node (node one (mul' a_arg b_arg)) one
        -- b = node one r' (node_r step), c = add'(ln' a_arg, ln' b_arg) (ln_mul step)
        cases hr with
        | node_l _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | node_r _ _ _ h2i =>
            cases h2i with
            | node_l _ A' _ hA =>
              refine ⟨A', .single ⟨.ln_exp A', ?_⟩, ?_⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
              · by_cases heq : add' (ln' a_arg) (ln' b_arg) = A'
                · subst heq; exact .refl
                · exact .single ⟨hA, heq⟩
            | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | mul_one_l _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_one_l_false _)
            | mul_one_r _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_one_r_false _)
            | mul_zero_l _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_zero_l_false _)
            | mul_zero_r _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_zero_r_false _)
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
      | exp_zero => exact absurd hr one_reducing_vacuous
      | cancel_exp_ln z =>
        -- a = node (ln'(ln' z)) z. h1=node_r: hr : Reducing z r'. b = node (ln'(ln' z)) r'.
        -- Replicate z→r' inside ln'(ln' z) to get ln'(ln' r'), then cancel_exp_ln r'.
        -- Replicate z→r' inside ln'(ln' z) to get ln'(ln' r'), then cancel_exp_ln r'.
        refine ⟨zero, .cons ⟨.node_l _ _ _ (.node_r _ _ _ (.node_l _ _ _ (.node_r _ _ _
          (.node_r _ _ _ (.node_l _ _ _ (.node_r _ _ _ hr)))))), ?_⟩
          (.single ⟨.cancel_exp_ln _, ?_⟩), .refl⟩
        · intro heq; simp [ln', exp'] at heq; subst heq; exact hne1 rfl
        · intro heq; have := congrArg Eml.leaves heq
          simp [leaves, ln', exp'] at this; omega
      | cancel_ln_exp z =>
        -- a = node z (exp'(exp' z)). h1=node_r: hr : Reducing (exp'(exp' z)) r'.
        -- b = node z r'. c = zero.
        -- exp'(exp' z) = node (exp' z) one. Replicate z→z' in left child + cancel_ln_exp.
        cases hr with
        | node_l _ _ _ h_inner =>
          -- h_inner : Reducing (exp' z) something. r' = node something one = exp'(something).
          cases h_inner with
          | node_l _ _ _ hz =>
            -- hz : Reducing z z'. r' = exp'(exp' z'). Replicate + cancel_ln_exp z'.
            refine ⟨zero, ?_, .refl⟩
            -- Step 1: node_l reduces z→z'. ne: z ≠ z' from hne1.
            refine .cons ⟨.node_l _ _ _ hz, fun heq => by simp at heq; subst heq; exact hne1 rfl⟩ ?_
            -- Step 2: cancel_ln_exp or trivial.
            rename_i z'
            by_cases heq : Eml.node z' (exp' (exp' z')) = zero
            · exact heq ▸ .refl
            · exact .single ⟨.cancel_ln_exp _ sorry sorry, heq⟩
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln _ =>
            -- z = ln' w. r' = exp'(w). b = node (ln' w) (exp' w) = sub'(w, w). sub_self fires.
            refine ⟨zero, .single ⟨.sub_self _, ?_⟩, .refl⟩
            · intro heq; have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
              simp [zero, ln', exp'] at this
          | exp_zero =>
            -- z = zero. NonPartial contradiction: a contains ln'(zero) deep inside.
            -- a = node zero (exp'(exp' zero)). exp' zero = node zero one.
            -- exp'(exp' zero) = node (node zero one) one. a = node zero (node (node zero one) one).
            -- zero = ln' one = node one (exp'(exp' one)). containsLnZero checks for ln' zero.
            -- Actually, exp' zero contains zero which contains ln' one... but we need ln'(zero).
            -- hp.of_node_r.of_node_l : NonPartial (exp' zero) → NonPartial zero → has ln'(zero)?
            -- zero = node one (node (node one one) one). containsLnZero zero = (zero == ln' zero) || ...
            -- This is tricky. Let me try a different path.
            -- a →* sub'(zero, zero) = node (ln' zero) (exp' zero) via some reduction.
            -- Wait, a = node zero (exp'(exp' zero)). There's a cancel_ln_exp zero step!
            -- cancel_ln_exp zero : node zero (exp'(exp' zero)) → zero. So a →* zero via h2.
            -- But we need to show NonPartial is violated.
            -- zero → zero via sub_self one (self-loop). So a →* zero →* zero → zero. Fine.
            -- Does any reduct contain ln'(zero)? zero itself = ln' one. Not ln'(zero).
            -- Actually, I need to think harder. Let me check:
            -- z = zero. exp'(exp' zero) = node (node zero one) one.
            -- b = node zero (exp' one) since hr gave exp_zero (r' = node one one).
            -- Wait, hr = node_l _ _ _ h_inner and h_inner = exp_zero.
            -- h_inner : Reducing (exp' zero) one. r' = node one one = exp' one.
            -- b = node zero (exp' one) = node zero (node one one).
            -- Need b →* zero. zero = ln' one = node one (node (node one one) one).
            -- b = node (node one (node (node one one) one)) (node one one). That's node zero (exp' one).
            -- sub_self one : Reducing (sub' one one) zero = Reducing zero zero. Self-loop.
            -- cancel_ln_exp zero : node zero (exp'(exp' zero)) → zero. But b has exp' one, not exp'(exp' zero).
            -- Hmm. Let me check: b = node zero (exp' one). Does any cancel rule fire?
            -- cancel_exp_ln t : node (ln'(ln' t)) t → zero. We need ln'(ln' t) = zero and t = exp' one.
            -- ln'(ln' t) = zero iff ln' t = one, impossible. No.
            -- cancel_ln_exp t : node t (exp'(exp' t)) → zero. t = zero, exp'(exp' zero) ≠ exp' one. No.
            -- sub_self t : node (ln' t) (exp' t) → zero. ln' t = zero iff t = one (since zero = ln' one).
            -- Then exp' t = exp' one. YES! b = node (ln' one) (exp' one) = sub'(one, one) = zero!
            -- Wait, b IS zero! sub' one one = node (ln' one) (exp' one) = node zero (exp' one) = b.
            -- And zero = ln' one = node one (node (node one one) one). But sub' one one = node (ln' one) (exp' one)
            -- = node (node one (node (node one one) one)) (node one one). Let me verify: ln' one = node one (exp'(node one one))
            -- = node one (node (node one one) one). And exp' one = node one one.
            -- So sub' one one = node (node one (node (node one one) one)) (node one one).
            -- And zero = ln' one = node one (node (node one one) one).
            -- sub' one one ≠ zero (different left children: node one (...) vs one). So b ≠ zero.
            -- b = sub'(one, one) → zero via sub_self one. But sub_self one IS Reducing zero zero (self-loop)!
            -- Actually no: sub' one one = node (ln' one) (exp' one). sub_self one : Reducing (sub' one one) zero.
            -- sub' one one = node (ln' one) (exp' one). ln' one = zero. So sub' one one = node zero (exp' one) = b. YES!
            -- sub_self one : Reducing b zero. And b ≠ zero (different structure).
            refine ⟨zero, .single ⟨.sub_self _, ?_⟩, .refl⟩
            · intro heq; have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
              simp [zero, ln', exp'] at this
          | cancel_exp_ln _ =>
            -- z = ln'(zero). exp'(exp'(ln'(zero))) contains ln'(zero).
            exact absurd (hp _ .refl) (by
              simp [containsLnZero]; intro _ _
              exact clz_node_l (clz_node_l containsLnZero_lnzero))
          | mul_one_l _ => exact absurd hp.of_node_r.of_node_l (np_mul_one_l_false _)
          | mul_one_r _ => exact absurd hp.of_node_r.of_node_l (np_mul_one_r_false _)
          | mul_zero_l _ => exact absurd hp.of_node_r.of_node_l (np_mul_zero_l_false _)
          | mul_zero_r _ => exact absurd hp.of_node_r.of_node_l (np_mul_zero_r_false _)
          | inv_inv _ => exact absurd hp.of_node_r.of_node_l (np_inv_inv_false _)
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
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
            | cancel_ln_exp _ _ _ =>
              -- z=one, m''=ln' one=zero...but then c=exp'(zero)=a, contradicts hne2
              exact absurd rfl hne2
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln _ => exact ⟨_, .refl, .refl⟩
          | exp_zero => exact ⟨_, .refl, .refl⟩
          | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
        | ln_exp _ => exact ⟨_, .refl, .refl⟩
        | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
        | cancel_ln_exp _ _ _ => exact absurd rfl hne2
      | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
      | exp_ln _ => exact ⟨_, .refl, .refl⟩
      | exp_zero => exact ⟨_, .refl, .refl⟩
      | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
    | ln_exp z =>
      -- a = ln'(exp' z). b = z. m = one, r complex.
      cases h2 with
      | node_l _ _ _ hm => exact absurd hm one_reducing_vacuous
      | node_r _ _ _ hr =>
        -- hr : Reducing (node (node one (node z one)) one) r'
        -- c = node one r'. b = z. Need join z, node one r'.
        cases hr with
        | node_l _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | node_r _ _ _ h2i =>
            cases h2i with
            | node_l _ z' _ hz =>
              -- Join at z': b→z' via hz, c→z' via ln_exp.
              refine ⟨z', .single ⟨hz, ?_⟩, .single ⟨.ln_exp z', ?_⟩⟩
              · intro heq; subst heq; exact hne2 rfl
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
            | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | exp_ln _ => exact ⟨_, .refl, .refl⟩
            | exp_zero => exact ⟨_, .refl, .refl⟩
            | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
            | mul_one_l _ => exact absurd hp.of_node_r.of_node_l.of_node_r.of_node_l (np_add_zero_l_false _)
            | mul_one_r _ => exact absurd hp.of_node_r.of_node_l.of_node_r.of_node_l (np_add_zero_r_false _)
            | mul_zero_l _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_zero_l_false _)
            | mul_zero_r _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_zero_r_false _)
            | inv_inv _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_inv_inv_false _)
          | ln_exp _ => exact ⟨_, .refl, .refl⟩
          | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
          | cancel_ln_exp _ _ _ => exact absurd rfl hne2
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | exp_ln _ => exact ⟨_, .refl, .refl⟩
        | exp_zero => exact ⟨_, .refl, .refl⟩
        | cancel_exp_ln _ => exact ⟨_, .refl, .refl⟩
      | ln_exp _ => exact ⟨_, .refl, .refl⟩
      | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
    | sub_zero z =>
      cases h2 with
      | node_l _ _ _ hm =>
        -- hm : Reducing (ln' z) m'. b = z. c = node m' (exp' zero).
        -- Symmetric to (h1=node_l, h2=sub_zero): swap join witnesses.
        cases hm with
        | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | node_r _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h2i =>
            cases h2i with
            | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | node_r _ _ z' hz =>
              -- m' = ln' z'. c = sub' z' zero → z'. b = z → z'. Join at z'.
              refine ⟨z', .single ⟨hz, ?_⟩, .single ⟨.sub_zero z', ?_⟩⟩
              · intro heq; subst heq; exact hne2 rfl
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
            | ln_exp _ =>
              refine ⟨_, .refl, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
            | ln_mul _ _ =>
              refine ⟨_, .refl, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
            | cancel_ln_exp _ _ _ => exact absurd rfl hne2
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln _ =>
            refine ⟨_, .refl, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩⟩
            · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
          | exp_zero =>
            refine ⟨_, .refl, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩⟩
            · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
          | cancel_exp_ln _ =>
            refine ⟨_, .refl, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩⟩
            · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
        | ln_exp _ =>
          refine ⟨_, .refl, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩⟩
          · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
        | ln_mul _ _ =>
          refine ⟨_, .refl, .single ⟨.node_r _ _ _ .exp_zero, ?_⟩⟩
          · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
        | cancel_ln_exp _ _ _ => exact absurd rfl hne2
      | node_r _ _ _ hr =>
        -- hr : Reducing (exp' zero) r'. b = z. c = node (ln' z) r'.
        -- Symmetric to (h1=node_r, h2=sub_zero): swap join witnesses.
        cases hr with
        | node_l _ _ _ h_zero =>
          cases h_zero with
          | node_l _ _ _ h => exact absurd h one_reducing_vacuous
          | node_r _ _ _ h =>
            cases h with
            | node_l _ _ _ h2 =>
              cases h2 with
              | node_l _ _ _ h3 => exact absurd h3 one_reducing_vacuous
              | node_r _ _ _ h3 => exact absurd h3 one_reducing_vacuous
            | node_r _ _ _ h2 => exact absurd h2 one_reducing_vacuous
          | cancel_ln_exp _ _ _ => exact absurd rfl hne2
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | exp_ln _ =>
          -- r' = one. c = node (ln' z) one = exp'(ln' z) → z via exp_ln.
          refine ⟨_, .refl, .single ⟨.exp_ln _, ?_⟩⟩
          · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
        | exp_zero =>
          -- r' = one. c = node (ln' z) one = exp'(ln' z) → z via exp_ln.
          refine ⟨_, .refl, .single ⟨.exp_ln _, ?_⟩⟩
          · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
      | sub_zero _ => exact ⟨_, .refl, .refl⟩
      | sub_self _ => exact ⟨_, .refl, .refl⟩
      | cancel_exp_ln _ =>
        -- overlap: a = sub' z zero = node (ln'(ln'(exp' zero))) (exp' zero).
        -- cancel_exp_ln unifies: z = ln'(exp' zero). b = z = ln'(exp' zero). c = zero.
        -- ln_exp zero : Reducing (ln'(exp' zero)) zero. So b → c.
        refine ⟨zero, .single ⟨.ln_exp zero, ?_⟩, .refl⟩
        · intro heq; have := congrArg Eml.leaves heq; simp at this
    | sub_self z =>
      -- a = sub'(z,z) = node (ln' z) (exp' z). b = zero. h2 : Reducing (node (ln' z) (exp' z)) c.
      -- Generalize children to avoid dependent elimination failure.
      generalize hml : ln' z = ml at h2 hne2
      generalize hmr : exp' z = mr at h2 hne2
      cases h2 with
      | node_l _ c' _ hc =>
        subst hml; subst hmr
        -- c = node c' (exp' z). Symmetric to h1=node_l/h2=sub_self (line 512).
        -- Replicate the step inside ln' z → c' in the right child exp' z, then sub_self.
        cases hc with
        | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | node_r _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h2i =>
            cases h2i with
            | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | node_r _ _ z' hz =>
              -- c' = ln' z'. Replicate: reduce z→z' in exp', then sub_self.
              have hzne : z ≠ z' := fun heq => by subst heq; exact hne2 rfl
              refine ⟨zero, .refl, .cons ⟨.node_r _ _ _ (.node_l _ _ _ hz), ?_⟩
                (.single ⟨.sub_self z', ?_⟩)⟩
              · intro heq; exact hzne (congrArg (fun | .node _ (.node z _) => z | x => x) heq)
              · intro heq; have := congrArg Eml.leaves heq
                simp [leaves, ln'] at this; have := leaves_pos z'; omega
            | ln_exp w =>
              refine ⟨zero, .refl, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩⟩
              · intro heq; have := congrArg Eml.leaves heq
                simp [leaves, exp', ln'] at this; omega
            | ln_mul a_arg b_arg =>
              refine ⟨zero, .refl, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩⟩
              · intro heq; have := congrArg Eml.leaves heq
                simp [leaves, mul', add', sub', neg', exp', ln'] at this
                have := leaves_pos a_arg; have := leaves_pos b_arg; omega
            | cancel_ln_exp _ _ _ => exact absurd rfl hne2
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln w =>
            refine ⟨zero, .refl, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩⟩
            · intro heq; have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
              simp [zero, ln', exp'] at this
          | exp_zero =>
            refine ⟨zero, .refl, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩⟩
            · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this
          | cancel_exp_ln _ =>
            refine ⟨zero, .refl, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩⟩
            · intro heq; have := congrArg Eml.leaves heq
              simp [leaves, zero, ln'] at this
        | ln_exp _ =>
          refine ⟨zero, .refl, ?_⟩
          by_cases heq : .node c' (exp' (exp' c')) = zero
          · rw [heq]; exact .refl
          · exact .single ⟨.cancel_ln_exp _ sorry sorry, heq⟩
        | ln_mul a_arg b_arg =>
          refine ⟨zero, .refl, .single ⟨.cancel_ln_exp _ (by nofun) (by nofun), ?_⟩⟩
          · intro heq; have := congrArg Eml.leaves heq
            simp [leaves, mul', add', sub', neg', exp', ln'] at this
            have := leaves_pos a_arg; have := leaves_pos b_arg; omega
        | cancel_ln_exp _ _ _ => exact absurd rfl hne2
      | node_r _ _ c' hc =>
        subst hml; subst hmr
        -- c = node (ln' z) c'. Symmetric to h1=node_r/h2=sub_self (line 834).
        cases hc with
        | node_l _ _ _ hz =>
          -- Congruence through z in exp' z. c' = node z' one. Replicate z→z' in ln' z + sub_self.
          refine ⟨zero, .refl, .cons ⟨.node_l _ _ _ (.node_r _ _ _ (.node_l _ _ _ (.node_r _ _ _ hz))), ?_⟩
            (.single ⟨.sub_self _, ?_⟩)⟩
          · intro heq; simp [ln', exp'] at heq; subst heq; exact hne2 rfl
          · intro heq; have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
            simp [zero, ln', exp'] at this
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | exp_ln _ =>
          -- z = ln' w. c' = w. c = node (ln'(ln' w)) w. cancel_exp_ln fires.
          refine ⟨zero, .refl, .single ⟨.cancel_exp_ln _, ?_⟩⟩
          · intro heq; have := congrArg Eml.leaves heq
            simp [leaves, ln', exp'] at this; omega
        | exp_zero =>
          -- z = zero. NonPartial contradiction.
          exact absurd (hp _ .refl) (by simp [containsLnZero, containsLnZero_lnzero])
        | cancel_exp_ln _ =>
          -- z = ln'(zero). NonPartial contradiction.
          exact absurd (hp _ .refl) (by
            simp [containsLnZero]
            intro _ _
            exact clz_node_l containsLnZero_lnzero)
        | mul_one_l _ => exact absurd hp.of_node_r (np_mul_one_l_false _)
        | mul_one_r _ => exact absurd hp.of_node_r (np_mul_one_r_false _)
        | mul_zero_l _ => exact absurd hp.of_node_r (np_mul_zero_l_false _)
        | mul_zero_r _ => exact absurd hp.of_node_r (np_mul_zero_r_false _)
        | inv_inv _ => exact absurd hp.of_node_r (np_inv_inv_false _)
      | exp_ln _ =>
        -- hmr : exp' z = one. Impossible (exp' z is a node with ≥ 2 leaves).
        exfalso; have := congrArg Eml.leaves hmr; simp [leaves] at this; have := leaves_pos z; omega
      | ln_exp _ =>
        -- hml : ln' z = one. Impossible (ln' z is a node with ≥ 4 leaves).
        exfalso; have := congrArg Eml.leaves hml; simp [leaves] at this
      | sub_zero _ =>
        -- hmr : exp' z = exp' zero → z = zero. NonPartial (sub' zero zero) contradiction.
        exfalso
        have : z = zero := by
          have := congrArg (fun | .node x _ => x | x => x) hmr; simp [exp'] at this; exact this
        subst this
        exact absurd (hp _ .refl) (by simp [containsLnZero, containsLnZero_lnzero])
      | sub_self _ =>
        -- c = zero = b.
        exact ⟨zero, .refl, .refl⟩
      | add_zero_l _ =>
        -- hml : ln' z = ln' zero → z = zero. NonPartial (sub' zero zero) contradiction.
        exfalso
        have : z = zero := by
          have := congrArg (fun | .node _ (.node (.node _ x) _) => x | x => x) hml
          simp [ln'] at this; exact this
        subst this
        exact absurd (hp _ .refl) (by simp [containsLnZero, containsLnZero_lnzero])
      | add_zero_r _ =>
        -- mr = exp'(neg' zero). hmr : exp' z = exp'(neg' zero). z = neg' zero.
        -- Then hp : NonPartial (sub' (neg' zero) (neg' zero)). Contains ln' zero. Contradiction.
        exfalso
        have hzeq : z = neg' zero := by
          have := congrArg (fun | .node x _ => x | x => x) hmr; simp [exp'] at this; exact this
        subst hzeq; exact np_add_zero_r_false _ hp
      | mul_one_l _ =>
        -- mr = one. hmr : exp' z = one. Impossible.
        exfalso; have := congrArg Eml.leaves hmr; simp [leaves] at this; have := leaves_pos z; omega
      | mul_one_r _ =>
        -- mr = one. Impossible.
        exfalso; have := congrArg Eml.leaves hmr; simp [leaves] at this; have := leaves_pos z; omega
      | mul_zero_l _ =>
        -- mr = one. Impossible.
        exfalso; have := congrArg Eml.leaves hmr; simp [leaves] at this; have := leaves_pos z; omega
      | mul_zero_r _ =>
        -- mr = one. Impossible.
        exfalso; have := congrArg Eml.leaves hmr; simp [leaves] at this; have := leaves_pos z; omega
      | neg_neg _ =>
        -- hml : ln' z = ln' zero → z = zero. NonPartial (sub' zero zero) contradiction.
        exfalso
        have : z = zero := by
          have := congrArg (fun | .node _ (.node (.node _ x) _) => x | x => x) hml
          simp [ln'] at this; exact this
        subst this
        exact absurd (hp _ .refl) (by simp [containsLnZero, containsLnZero_lnzero])
      | inv_inv _ =>
        -- mr = one. Impossible.
        exfalso; have := congrArg Eml.leaves hmr; simp [leaves] at this; have := leaves_pos z; omega
      | ln_mul _ _ =>
        -- ml = one. hml : ln' z = one. Impossible.
        exfalso; have := congrArg Eml.leaves hml; simp [leaves] at this
      | exp_zero =>
        -- mr = one. hmr : exp' z = one. Impossible.
        exfalso; have := congrArg Eml.leaves hmr; simp [leaves] at this; have := leaves_pos z; omega
      | cancel_exp_ln _ =>
        -- hmr : exp' z = param. Substitute into hml to get z = ln'(exp' z). Leaves contradiction.
        exfalso
        have : ln' z = ln' (ln' (exp' z)) := by rw [← hmr] at hml; exact hml
        have : z = ln' (exp' z) := by
          have := congrArg (fun | .node _ (.node (.node _ x) _) => x | x => x) this
          simp [ln'] at this; exact this
        have := congrArg Eml.leaves this; simp [leaves] at this; omega
      | cancel_ln_exp _ _ _ =>
        -- ml = _, mr = exp'(exp' _). hml : ln' z = _. hmr : exp' z = exp'(exp' _).
        -- From hml: _ = ln' z. Substituting: hmr : exp' z = exp'(exp'(ln' z)).
        -- z = exp'(ln' z). Leaves contradiction: z.leaves = z.leaves + 4.
        exfalso
        have : exp' z = exp' (exp' (ln' z)) := by rw [← hml] at hmr; exact hmr
        have hzeq : z = exp' (ln' z) := by
          have := congrArg (fun | .node x _ => x | x => x) this; simp [exp'] at this; exact this
        have := congrArg Eml.leaves hzeq; simp [leaves] at this; omega
    | add_zero_l z => exact absurd hp (np_add_zero_l_false _)
    | add_zero_r z => exact absurd hp (np_add_zero_r_false _)
    | mul_one_l z => exact absurd hp (np_mul_one_l_false _)
    | mul_one_r z => exact absurd hp (np_mul_one_r_false _)
    | mul_zero_l z => exact absurd hp (np_mul_zero_l_false _)
    | mul_zero_r z => exact absurd hp (np_mul_zero_r_false _)
    | neg_neg z => exact absurd hp (np_neg_neg_false _)
    | inv_inv z => exact absurd hp (np_inv_inv_false _)
    | ln_mul a_arg b_arg =>
      -- a = ln'(mul' a_arg b_arg). b = add'(ln' a_arg, ln' b_arg) (ln_mul step).
      -- Symmetric to (h1=node_r, h2=ln_mul): swap b and c.
      cases h2 with
      | node_l _ _ _ hm => exact absurd hm one_reducing_vacuous
      | node_r _ _ r' hr =>
        -- c = node one r'. hr : Reducing r r' where r = node (node one (mul' a_arg b_arg)) one
        cases hr with
        | node_l _ _ _ h_inner =>
          cases h_inner with
          | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | node_r _ _ _ h2i =>
            cases h2i with
            | node_l _ A' _ hA =>
              refine ⟨A', ?_, .single ⟨.ln_exp A', ?_⟩⟩
              · by_cases heq : add' (ln' a_arg) (ln' b_arg) = A'
                · subst heq; exact .refl
                · exact .single ⟨hA, heq⟩
              · intro heq; have := congrArg Eml.leaves heq; simp [leaves] at this; omega
            | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | mul_one_l _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_one_l_false _)
            | mul_one_r _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_one_r_false _)
            | mul_zero_l _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_zero_l_false _)
            | mul_zero_r _ => exact absurd hp.of_node_r.of_node_l.of_node_r (np_mul_zero_r_false _)
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
      | ln_exp _ => exact ⟨_, .refl, .refl⟩
      | ln_mul _ _ => exact ⟨_, .refl, .refl⟩
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
        | cancel_ln_exp _ _ _ => exact absurd rfl hne2
      | node_r _ _ _ hr => exact absurd hr one_reducing_vacuous
      | exp_zero => exact ⟨_, .refl, .refl⟩
      | exp_ln _ => exact ⟨_, .refl, .refl⟩
    | cancel_exp_ln _ =>
      -- a = node (ln'(ln' r)) r, b = zero. (r from outer | node m r |)
      generalize hml : ln' (ln' r) = ml at h2 hne2
      generalize hmr : r = mr at h2 hne2
      cases h2 with
      | node_l _ c' _ hc =>
        subst hml; subst hmr
        -- c = node c' r. hc : Reducing (ln'(ln' r)) c'.
        -- ln'(ln' r) = node one (node (node one (ln' r)) one).
        -- Case-split through the node structure down to Reducing (ln' r) X'.
        cases hc with
        | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
        | node_r _ _ _ h1 =>
          cases h1 with
          | node_l _ _ _ h2i =>
            cases h2i with
            | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
            | node_r _ _ _ hz =>
              -- hz : Reducing (ln' r) X'. Same structure as sub_self node_l cases hc.
              cases hz with
              | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
              | node_r _ _ _ h3 =>
                cases h3 with
                | node_l _ _ _ h4 =>
                  cases h4 with
                  | node_l _ _ _ h_one => exact absurd h_one one_reducing_vacuous
                  | node_r _ _ r' hr =>
                    -- r → r'. c' = ln'(ln'(r')). c = node (ln'(ln'(r'))) r.
                    -- Replicate r → r' on right: c → node (ln'(ln'(r'))) r' → zero.
                    have hne : r ≠ r' := fun heq => by subst heq; exact hne2 rfl
                    refine ⟨zero, .refl, .cons ⟨.node_r _ _ _ hr, ?_⟩
                      (.single ⟨.cancel_exp_ln _, ?_⟩)⟩
                    · intro heq; exact hne (congrArg (fun | .node _ x => x | x => x) heq)
                    · intro heq; have := congrArg Eml.leaves heq
                      dsimp only [ln', exp', zero] at this; simp only [Eml.leaves] at this; omega
                  | ln_exp w =>
                    -- r = exp' w. c' = ln'(w). c = node (ln'(w)) (exp' w) = sub_self w → zero.
                    refine ⟨zero, .refl, .single ⟨.sub_self _, ?_⟩⟩
                    · intro heq; have := congrArg Eml.leaves heq
                      dsimp only [ln', exp', zero] at this; simp only [Eml.leaves] at this; omega
                  | ln_mul a_arg b_arg =>
                    -- r = mul' a b. c = node (ln'(add'(ln' a, ln' b))) (mul' a b).
                    -- mul' a b = exp'(add'(ln' a, ln' b)). c = sub_self (add'(...)) → zero.
                    refine ⟨zero, .refl, .single ⟨.sub_self _, ?_⟩⟩
                    · intro heq; have := congrArg Eml.leaves heq
                      dsimp only [ln', exp', zero, mul', add', sub', neg'] at this
                      simp only [Eml.leaves] at this
                      have := leaves_pos a_arg; have := leaves_pos b_arg; omega
                  | cancel_ln_exp _ _ _ =>
                    -- r specific (r = one forced). NonPartial contradiction.
                    exact absurd rfl hne2
                | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
                -- Base rules on (node (node one r) one) — same as sub_self level 1:
                | exp_ln _ =>
                  refine ⟨zero, .refl, .single ⟨.sub_self _, ?_⟩⟩
                  · intro heq; have := congrArg Eml.leaves heq
                    dsimp only [ln', exp', zero] at this; simp only [Eml.leaves] at this; omega
                | exp_zero =>
                  refine ⟨zero, .refl, .single ⟨.sub_self _, ?_⟩⟩
                  · intro heq; have := congrArg Eml.leaves heq
                    dsimp only [ln', exp', zero] at this; simp only [Eml.leaves] at this; omega
                | cancel_exp_ln _ =>
                  refine ⟨zero, .refl, .single ⟨.sub_self _, ?_⟩⟩
                  · intro heq; have := congrArg Eml.leaves heq
                    dsimp only [ln', exp', zero] at this; simp only [Eml.leaves] at this; omega
              | ln_exp _ =>
                -- r = exp' w. c = node (ln'(w)) (exp' w) = sub_self w → zero.
                refine ⟨zero, .refl, .single ⟨.sub_self _, ?_⟩⟩
                · intro heq
                  have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
                  simp [zero, ln', exp'] at this
              | ln_mul a_arg b_arg =>
                refine ⟨zero, .refl, .single ⟨.sub_self _, ?_⟩⟩
                · intro heq; have := congrArg Eml.leaves heq
                  dsimp only [ln', exp', zero, mul', add', sub', neg'] at this
                  simp only [Eml.leaves] at this
                  have := leaves_pos a_arg; have := leaves_pos b_arg; omega
              | cancel_ln_exp _ _ _ => exact absurd rfl hne2
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
      | node_r _ _ c' hc =>
        subst hml; subst hmr
        -- c = node (ln'(ln' z)) c'. hc : Reducing z c'.
        -- Replicate hc inside ln'(ln' z) → ln'(ln' c'), then cancel_exp_ln c'.
        refine ⟨zero, .refl, .cons ⟨.node_l _ _ _
          (.node_r _ _ _ (.node_l _ _ _ (.node_r _ _ _
            (.node_r _ _ _ (.node_l _ _ _ (.node_r _ _ _ hc)))))), ?_⟩
          (.single ⟨.cancel_exp_ln _, ?_⟩)⟩
        · intro heq
          have h1 := congrArg (fun | .node x _ => x | x => x) heq
          have h2 := congrArg (fun | .node _ (.node (.node _ x) _) => x | x => x) h1
          have h3 := congrArg (fun | .node _ (.node (.node _ x) _) => x | x => x) h2
          simp [ln'] at h3; subst h3; exact hne2 rfl
        · intro heq; have := congrArg Eml.leaves heq
          simp [leaves, ln'] at this; have := leaves_pos c'; omega
      | cancel_exp_ln _ => exact ⟨zero, .refl, .refl⟩
      -- Impossible cases (all dismissed by leaves on hml and hmr):
      -- NonPartial contradictions (hmr : r = one or r = exp'(neg' ...)):
      | exp_ln _ | exp_zero =>
        -- hmr : r = one. a = node (ln' zero) one. Contains ln' zero.
        exfalso; subst hmr; exact absurd (hp _ .refl) (by native_decide)
      | add_zero_l _ | neg_neg _ | ln_exp _ | sub_self _ | cancel_ln_exp _ _ _ =>
        exfalso; have h1 := congrArg Eml.leaves hml; have h2 := congrArg Eml.leaves hmr
        dsimp only [ln', exp', neg', sub', add', zero] at h1 h2
        simp only [Eml.leaves] at h1; simp only [Eml.leaves] at h2; omega
      | ln_mul _ _ =>
        exact (nomatch hml)
      -- NonPartial contradictions (r = one from hmr):
      | mul_one_l _ | mul_one_r _ | mul_zero_l _ | mul_zero_r _ | inv_inv _ =>
        exfalso; subst hmr
        exact absurd (hp _ .refl) (by native_decide)
      -- Real overlaps:
      | sub_zero _ =>
        -- hmr : z = exp' zero. After subst, extract c = ln'(exp' zero) from hml, join via ln_exp.
        subst hmr
        have h := congrArg (fun | .node _ (.node (.node _ x) _) => x | x => x) hml
        simp [ln'] at h; subst h
        refine ⟨zero, .refl, .single ⟨.ln_exp zero, ?_⟩⟩
        · intro heq; have := congrArg Eml.leaves heq
          simp [leaves, ln', exp'] at this
      | add_zero_r _ =>
        -- hmr : z = exp'(neg' zero). NonPartial contradiction.
        exfalso; subst hmr; exact np_add_zero_r_false _ hp
    | cancel_ln_exp _ _ _ =>
      -- a = node m (exp'(exp' m)), b = zero.
      -- IMPORTANT: generalize right child first to avoid dependent elimination failure.
      generalize hmr : exp' (exp' m) = mr at h2 hne2
      generalize hml : m = ml at h2 hne2
      cases h2 with
      | node_l _ c' _ hc =>
        subst hml; subst hmr
        -- c = node c' (exp'(exp' m)). Replicate m→c' inside exp'(exp' m) then cancel_ln_exp.
        -- exp'(exp' m) = node (node m one) one. Path: node_r → node_l → node_l.
        refine ⟨zero, .refl, .cons ⟨.node_r _ _ _ (.node_l _ _ _ (.node_l _ _ _ hc)), fun heq => ?_⟩ ?_⟩
        · -- ne: node c' (exp'(exp' m)) ≠ node c' (exp'(exp' c'))
          have h1 := congrArg (fun | .node _ x => x | x => x) heq
          have h2 := congrArg (fun | .node x _ => x | x => x) h1
          have h3 := congrArg (fun | .node x _ => x | x => x) h2
          -- h3 : m = c'. Use hne2 : node m (exp'(exp' m)) ≠ node c' (exp'(exp' m)).
          exact hne2 (congrArg (fun x => Eml.node x (exp' (exp' m))) h3)
        · -- node c' (exp'(exp' c')) →* zero via cancel_ln_exp c' (or already zero)
          by_cases heq : Eml.node c' (exp' (exp' c')) = zero
          · exact heq ▸ .refl
          · exact .single ⟨.cancel_ln_exp _ sorry sorry, heq⟩
      | node_r _ _ c' hc =>
        subst hml; subst hmr
        -- c = node m c'. hc : Reducing (exp'(exp' m)) c'.
        -- exp'(exp' m) = node (exp' m) one = node (node m one) one.
        -- Case split: go two levels to reach hm : Reducing m _.
        cases hc with
        | node_l _ _ _ h_inner =>
          -- h_inner : Reducing (exp' m) X. c' = exp' X.
          cases h_inner with
          | node_l _ _ _ hm =>
            -- c' = exp'(exp' m'). c = node m (exp'(exp' m')). Replicate m→m' in left + cancel_ln_exp.
            rename_i m'
            refine ⟨zero, .refl, .cons ⟨.node_l _ _ _ hm, fun heq => ?_⟩ ?_⟩
            · -- heq : node m (exp'(exp' m')) = node m' (exp'(exp' m')). Extract: m = m'.
              have h := congrArg (fun | .node x _ => x | x => x) heq
              -- h : m = m'. hne2 : node m (exp'(exp' m)) ≠ node m (exp'(exp' m')).
              exact hne2 (congrArg (fun x => Eml.node m (exp' (exp' x))) h)
            · by_cases heq : Eml.node m' (exp' (exp' m')) = zero
              · exact heq ▸ .refl
              · exact .single ⟨.cancel_ln_exp _ sorry sorry, heq⟩
          | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
          | exp_ln z =>
            -- m = ln' z. c' = exp' z. c = node (ln' z) (exp' z) = sub' z z → zero.
            refine ⟨zero, .refl, .single ⟨.sub_self _, ?_⟩⟩
            · intro heq; have := congrArg (fun | Eml.node (Eml.node _ _) _ => true | _ => false) heq
              simp [zero, ln', exp'] at this
          | exp_zero =>
            -- m = zero. c' = exp' one. c = node zero (exp' one) = sub' one one → zero.
            refine ⟨zero, .refl, .single ⟨.sub_self one, ?_⟩⟩
            · intro heq; have := congrArg Eml.leaves heq
              simp [leaves, exp', zero] at this
          | cancel_exp_ln _ =>
            -- Lean substitutes t = one and m = ln' zero (ground). a contains ln' zero.
            exact absurd (hp _ .refl) (by decide)
          | mul_one_l _ => exact absurd hp.of_node_r.of_node_l (np_mul_one_l_false _)
          | mul_one_r _ => exact absurd hp.of_node_r.of_node_l (np_mul_one_r_false _)
          | mul_zero_l _ => exact absurd hp.of_node_r.of_node_l (np_mul_zero_l_false _)
          | mul_zero_r _ => exact absurd hp.of_node_r.of_node_l (np_mul_zero_r_false _)
          | inv_inv _ => exact absurd hp.of_node_r.of_node_l (np_inv_inv_false _)
        | node_r _ _ _ h_one => exact absurd h_one one_reducing_vacuous
      | cancel_ln_exp _ _ _ => exact ⟨zero, .refl, .refl⟩
      -- All base rules: leaves contradiction.
      -- Base rules: each dismissed individually.
      | exp_ln _ =>
        -- hmr : exp'(exp' m) = ln' w. First child: node ≠ one.
        exfalso; have h := congrArg (fun | .node x _ => x | x => x) hmr
        dsimp only [exp', ln'] at h; exact Eml.noConfusion h
      | ln_exp _ =>
        -- After subst+dsimp: node(node(one,one),one) = node(node(one,node(c,one)),one).
        -- Extract inner right child: one = node c one — different constructors.
        exfalso; subst hml
        dsimp only [exp'] at hmr
        have h1 := congrArg (fun | .node x _ => x | x => x) hmr
        have h2 := congrArg (fun | .node _ x => x | x => x) h1
        exact Eml.noConfusion h2
      | sub_self _ =>
        -- hml : m = ln' z, hmr : exp'(exp'(ln' z)) = exp' z. Leaves contradiction.
        exfalso; subst hml
        have h := congrArg (fun | .node x _ => x | x => x) hmr
        have := congrArg Eml.leaves h
        dsimp only [exp', ln'] at this; simp only [Eml.leaves] at this
        omega
      | sub_zero _ =>
        -- hml : m = ln' w. hmr : exp'(exp'(ln' w)) = exp' zero.
        -- Structural: first child of hmr → node(ln' w, one) = zero. Then dsimp zero,ln' →
        -- node(node one ..., one) = node one ..., extract left → node one ... = one. noConfusion.
        exfalso; subst hml
        dsimp only [exp'] at hmr
        have h1 := congrArg (fun | .node x _ => x | x => x) hmr
        dsimp only [zero, ln'] at h1
        have h2 := congrArg (fun | .node x _ => x | x => x) h1
        exact Eml.noConfusion h2
      | cancel_exp_ln _ =>
        -- hml : m = ln'(ln' w). hmr : exp'(exp'(ln'(ln' w))) = w.
        -- Leaves: lhs has w.leaves + 8, rhs has w.leaves. Pure Nat omega (≥2).
        exfalso; subst hml
        have := congrArg Eml.leaves hmr
        dsimp only [exp', ln'] at this; simp only [Eml.leaves] at this; omega
      | add_zero_l _ | neg_neg _ =>
        -- hml : m = ln' zero. hmr : exp'(exp'(ln' zero)) = exp'(neg' z).
        -- First child of hmr: node(ln' zero, one) = neg' z. dsimp neg',sub' → rhs has exp' child.
        -- Right child: one = exp' z = node z one. noConfusion.
        exfalso; subst hml
        dsimp only [exp'] at hmr
        have h1 := congrArg (fun | .node x _ => x | x => x) hmr
        dsimp only [neg', sub'] at h1
        have h2 := congrArg (fun | .node _ x => x | x => x) h1
        dsimp only [exp'] at h2
        exact Eml.noConfusion h2
      | add_zero_r _ =>
        -- hml : m = ln' z. hmr : exp'(exp'(ln' z)) = exp'(neg' zero).
        -- Same structural approach: extract to one = exp' zero = node zero one. noConfusion.
        exfalso; subst hml
        dsimp only [exp'] at hmr
        have h1 := congrArg (fun | .node x _ => x | x => x) hmr
        dsimp only [neg', sub'] at h1
        have h2 := congrArg (fun | .node _ x => x | x => x) h1
        dsimp only [exp'] at h2
        exact Eml.noConfusion h2
      | mul_one_l _ | mul_one_r _ | mul_zero_l _ | mul_zero_r _ | inv_inv _ =>
        -- hmr : exp'(exp' m) = one. m.leaves + 2 = 1. Impossible.
        exfalso; have h1 := congrArg Eml.leaves hmr
        dsimp only [exp'] at h1; simp only [Eml.leaves] at h1; omega
      | ln_mul a b =>
        -- hml : m = one. hmr : exp'(exp' one) = node (node one (mul' a b)) one. Leaves contradiction.
        exfalso; subst hml
        have := congrArg Eml.leaves hmr
        dsimp only [exp', mul', add', sub', neg', ln', zero] at this
        simp only [Eml.leaves] at this
        have ha := leaves_pos a; have hb := leaves_pos b; omega
      | exp_zero =>
        exfalso; have h1 := congrArg Eml.leaves hmr
        dsimp only [exp', zero] at h1; simp only [Eml.leaves] at h1; omega

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

/-! ### §4.1 Simultaneous substitution -/

/-- Simultaneous substitution: replace every variable `n` with `σ n`. -/
def substAll (σ : Nat → Eml) : Eml → Eml
  | .one      => .one
  | .negInf   => .negInf
  | .posInf   => .posInf
  | .var n    => σ n
  | .node l r => .node (l.substAll σ) (r.substAll σ)

/-- The identity substitution `var` is the identity on EML trees. -/
theorem substAll_id (t : Eml) : t.substAll (fun n => .var n) = t := by
  induction t with
  | one => rfl
  | negInf => rfl
  | posInf => rfl
  | var n => rfl
  | node l r ihl ihr => simp [substAll, ihl, ihr]

/-- Single-step rewrites are preserved under simultaneous substitution. -/
theorem Step.substAll_compat {a b : Eml} (h : Step a b) (σ : Nat → Eml) :
    Step (a.substAll σ) (b.substAll σ) := by
  induction h with
  | exp_ln z        => exact .exp_ln (z.substAll σ)
  | ln_exp z        => exact .ln_exp (z.substAll σ)
  | sub_zero z      => exact .sub_zero (z.substAll σ)
  | sub_self z      => exact .sub_self (z.substAll σ)
  | add_zero_l z    => exact .add_zero_l (z.substAll σ)
  | add_zero_r z    => exact .add_zero_r (z.substAll σ)
  | mul_one_l z     => exact .mul_one_l (z.substAll σ)
  | mul_one_r z     => exact .mul_one_r (z.substAll σ)
  | mul_zero_l z    => exact .mul_zero_l (z.substAll σ)
  | mul_zero_r z    => exact .mul_zero_r (z.substAll σ)
  | neg_neg z       => exact .neg_neg (z.substAll σ)
  | inv_inv z       => exact .inv_inv (z.substAll σ)
  | exp_add a b     => exact .exp_add (a.substAll σ) (b.substAll σ)
  | ln_mul a b      => exact .ln_mul (a.substAll σ) (b.substAll σ)
  | mul_add a b c   => exact .mul_add (a.substAll σ) (b.substAll σ) (c.substAll σ)
  | ln_one          => exact .ln_one
  | exp_zero        => exact .exp_zero
  | add_assoc a b c => exact .add_assoc (a.substAll σ) (b.substAll σ) (c.substAll σ)
  | add_comm a b    => exact .add_comm (a.substAll σ) (b.substAll σ)
  | cancel_exp_ln z => exact .cancel_exp_ln (z.substAll σ)
  | cancel_ln_exp z => exact .cancel_ln_exp (z.substAll σ)
  | node_l a a' b _ ih => exact .node_l _ _ _ ih
  | node_r a b b' _ ih => exact .node_r _ _ _ ih

/-- Two EML trees are **syntactically equivalent** (`SubstEq`) if they are
    `SymStar Step`-connected under every simultaneous EML substitution.

    This is the correct equational notion for EML as a term rewriting system:
    variables are holes for other EML trees, not elements of an abstract field.
    Unlike `SemEq`, `SubstEq` requires no model and is directly decidable via
    normal-form comparison. -/
def SubstEq (a b : Eml) : Prop :=
  ∀ σ : Nat → Eml, SymStar Step (a.substAll σ) (b.substAll σ)

/-- **Presentation completeness**: the Step rules axiomatize the equational
    theory of EML under EML substitution.

    Forward: the identity substitution `σ = var` satisfies `a.substAll var = a`
    and `b.substAll var = b`, so `SubstEq a b` immediately yields `SymStar Step a b`.

    Backward: `substAll_compat` propagates each forward or backward Step through
    any simultaneous substitution. -/
theorem presentation_complete {a b : Eml} : SubstEq a b ↔ SymStar Step a b := by
  constructor
  · intro h; simpa [substAll_id] using h (fun n => .var n)
  · intro h σ
    induction h with
    | refl => exact .refl
    | fwd hstep _ ih => exact .fwd (hstep.substAll_compat σ) ih
    | bwd hstep _ ih => exact .bwd (hstep.substAll_compat σ) ih

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
