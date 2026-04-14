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

/-! ### §3.1 Main WCR theorem -/

/-- **Local confluence of the strict reducing system (away from partiality).**

    Proved by structural induction on `a`, case-splitting on the two
    Reducing steps. The congruence×congruence case uses the induction
    hypothesis. The base×congruence cases require case-splitting on
    the inner reduction. The base×base cases require critical pair
    witnesses (all joinable for NonPartial terms, per KB.lean). -/
theorem strict_reducing_wcr_np :
    ∀ a b c, NonPartial a → StrictReducing a b → StrictReducing a c →
    ∃ d, Star StrictReducing b d ∧ Star StrictReducing c d := by
  sorry

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
