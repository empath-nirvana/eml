/-
  EML Tower Theory
  ================
  Tower-structured elementary extensions for Liouville's theorem.

  The classical proof of Liouville's theorem inducts on "tower height" —
  the number of new exp/ln transcendentals — rather than on the tree
  structure of the antiderivative. This file provides that infrastructure.

  Key definitions:
  - FieldClosure: algebraic closure (add, neg, mul, inv) without exp/ln
  - Tower: a sequence of single exp/ln extensions over a base class

  Axioms (stated without proof, classically provable from algebraic
  independence of exp/ln over differential fields):
  - exp_independence: exp extensions don't help integrate base elements
  - ln_structure: antiderivatives using ln are at most linear in ln

  The tower formulation reduces Liouville's theorem to:
  - Base case (tower height 0): F ∈ C is trivially in Liouville form ✓
  - Exponential step: exp_independence eliminates exp, IH finishes ✓
  - Logarithmic step: ln_structure decomposes F as v₀ + c·ln(g),
    IH handles v₀, derivative chain fully proved, but the log term
    requires g ∈ C (not just g ∈ D'). This "log argument descent"
    is the remaining formalization gap ☐
-/

import Eml.Liouville

namespace Eml

/-! ## Field closure -/

/-- The algebraic (field) closure of a predicate: everything buildable
    from D-elements using add', neg', mul', inv'. Crucially, NO exp'
    or ln' — those are the transcendental operations that increase
    the tower height. -/
inductive FieldClosure (D : Eml → Prop) : Eml → Prop where
  | incl : ∀ t, D t → FieldClosure D t
  | add_of : ∀ a b, FieldClosure D a → FieldClosure D b → FieldClosure D (add' a b)
  | neg_of : ∀ a, FieldClosure D a → FieldClosure D (neg' a)
  | mul_of : ∀ a b, FieldClosure D a → FieldClosure D b → FieldClosure D (mul' a b)
  | inv_of : ∀ a, FieldClosure D a → FieldClosure D (inv' a)

/-- If D is already closed under field operations, FieldClosure D collapses to D. -/
theorem FieldClosure_sub_of_closed {D : Eml → Prop}
    (hD_ops : ∀ a b, D a → D b → D (add' a b) ∧ D (mul' a b) ∧ D (inv' a))
    (hD_neg : ∀ a, D a → D (neg' a))
    {t : Eml} (h : FieldClosure D t) : D t := by
  induction h with
  | incl t ht => exact ht
  | add_of a b _ _ iha ihb => exact (hD_ops a b iha ihb).1
  | neg_of a _ ih => exact hD_neg a ih
  | mul_of a b _ _ iha ihb => exact (hD_ops a b iha ihb).2.1
  | inv_of a _ ih => exact (hD_ops a a ih ih).2.2

/-- FieldClosure is monotone: D ⊆ D' implies FieldClosure D ⊆ FieldClosure D'. -/
theorem FieldClosure.mono {D D' : Eml → Prop} (h : ∀ t, D t → D' t)
    {t : Eml} (ht : FieldClosure D t) : FieldClosure D' t := by
  induction ht with
  | incl t ht => exact .incl t (h t ht)
  | add_of _ _ _ _ iha ihb => exact .add_of _ _ iha ihb
  | neg_of _ _ ih => exact .neg_of _ ih
  | mul_of _ _ _ _ iha ihb => exact .mul_of _ _ iha ihb
  | inv_of _ _ ih => exact .inv_of _ ih

/-! ## Tower -/

/-- An elementary tower over C: a sequence of single exp/ln extensions,
    each followed by field closure.

    Tower C D means D is reachable from C by a chain of extensions:
      C → FieldClosure(C ∪ {θ₁}) → FieldClosure(... ∪ {θ₂}) → ... → D
    where each θᵢ is exp'(gᵢ) or ln'(gᵢ) with gᵢ at the previous level.

    This matches the classical differential algebra tower structure. -/
inductive Tower (C : Eml → Prop) : (Eml → Prop) → Prop where
  | base : Tower C C
  | exp_step (D : Eml → Prop) (g : Eml) :
      Tower C D → D g →
      Tower C (FieldClosure (fun t => D t ∨ t = exp' g))
  | ln_step (D : Eml → Prop) (g : Eml) :
      Tower C D → D g →
      Tower C (FieldClosure (fun t => D t ∨ t = ln' g))

/-- The base class is included in every tower level. -/
theorem Tower.base_sub {C D : Eml → Prop} (h : Tower C D) :
    ∀ t, C t → D t := by
  induction h with
  | base => intro t ht; exact ht
  | exp_step D g _ _ ih =>
    intro t ht; exact FieldClosure.incl t (Or.inl (ih t ht))
  | ln_step D g _ _ ih =>
    intro t ht; exact FieldClosure.incl t (Or.inl (ih t ht))

/-! ## Semantic congruence -/

/-- SemEq is compatible with add' in the left argument. -/
theorem SemEq.add'_congr_l {a a' : Eml} (h : SemEq a a') (b : Eml) :
    SemEq (add' a b) (add' a' b) := by
  intro α _ ρ
  simp only [eval_add']
  rw [h α ρ]

/-! ## LiouvilleForm monotonicity -/

/-- LiouvilleForm is monotone in the base predicate:
    if C ⊆ C' then LiouvilleForm C x ⊆ LiouvilleForm C' x. -/
theorem LiouvilleForm.mono' {C C' : Eml → Prop} (h : ∀ t, C t → C' t)
    {x : Nat} {G : Eml} (hG : LiouvilleForm C x G) : LiouvilleForm C' x G := by
  induction hG with
  | base v₀ hv₀ => exact LiouvilleForm.base v₀ (h v₀ hv₀)
  | log_term F c v _ hc hv ih => exact LiouvilleForm.log_term F c v ih hc (h v hv)

/-! ## Axioms

The two axioms below capture the key structural properties of
exponential and logarithmic extensions in differential algebra.

These are the tree-algebraic formulations of:
- (exp) If exp(g) is transcendental over D, it cannot help integrate
  elements of D. Any antiderivative using exp(g) has an equivalent
  antiderivative without it.
- (ln) If ln(g) is transcendental over D, an antiderivative using ln(g)
  is at most linear in ln(g): it has the form v₀ + c·ln(g).

Both axioms are classically provable from the algebraic independence
of exp/ln over differential fields. They are stated here as axioms
because their proofs require model-theoretic arguments (partial
fractions, degree counting) not yet formalized.

Note: the classical proofs additionally require the tower levels to
form differential fields (closed under differentiation). In our tree
algebra, diff-closure holds semantically — diff(t) evaluates to
the derivative of eval(t) in every ExpField model — but not
syntactically, since diff produces trees involving exp'/ln' which
escape the FieldClosure. The semantic diff-closure is implicit in
the SemEq-based formulation and need not be stated separately. -/

/-- **Exponential independence**: exp(g) doesn't help integrate
    elements of the base field.

    If F is a field expression over D ∪ {exp'(g)}, then some
    F' ∈ D has the same derivative as F (up to semantic equality). -/
axiom exp_independence (D : Eml → Prop) (g F : Eml) (x : Nat)
    (hD_ops : ∀ a b, D a → D b → D (add' a b) ∧ D (mul' a b) ∧ D (inv' a))
    (hg : D g)
    (hF : FieldClosure (fun t => D t ∨ t = exp' g) F) :
    ∃ F', D F' ∧ SemEq (diff F x) (diff F' x)

/-- **Logarithmic structure**: antiderivatives using ln(g) are at most
    linear in ln(g).

    If F is a field expression over D ∪ {ln'(g)}, then F has the same
    derivative as v₀ + c·ln'(g) for some v₀ ∈ D and constant c. -/
axiom ln_structure (D : Eml → Prop) (g F : Eml) (x : Nat)
    (hD_ops : ∀ a b, D a → D b → D (add' a b) ∧ D (mul' a b) ∧ D (inv' a))
    (hg : D g)
    (hF : FieldClosure (fun t => D t ∨ t = ln' g) F) :
    ∃ v₀ c, D v₀ ∧ c.hasVar x = false ∧
      SemEq (diff F x) (diff (add' v₀ (mul' c (ln' g))) x)

/-! ## Tower closure -/

/-- Each tower level is closed under field operations.
    This is immediate from the FieldClosure wrapper at each extension step. -/
theorem Tower.field_closed {C D : Eml → Prop} (hTower : Tower C D)
    (hC_ops : ∀ a b, C a → C b → C (add' a b) ∧ C (mul' a b) ∧ C (inv' a)) :
    ∀ a b, D a → D b → D (add' a b) ∧ D (mul' a b) ∧ D (inv' a) := by
  induction hTower with
  | base => exact hC_ops
  | exp_step D' g _ _ _ =>
    intro a b ha hb
    exact ⟨FieldClosure.add_of a b ha hb, FieldClosure.mul_of a b ha hb, FieldClosure.inv_of a ha⟩
  | ln_step D' g _ _ _ =>
    intro a b ha hb
    exact ⟨FieldClosure.add_of a b ha hb, FieldClosure.mul_of a b ha hb, FieldClosure.inv_of a ha⟩

/-! ## Tower Liouville theorem -/

/-- **Liouville's theorem (tower formulation).**

    If F is at some tower level over C, and D(F) is semantically
    equal to f, then there exists G in Liouville normal form (over C)
    with D(G) semantically equal to f.

    The proof proceeds by induction on the tower structure:
    - **Base case**: F ∈ C, so F is already in Liouville form.
    - **Exponential step**: by exp_independence, the exp extension
      is unnecessary — reduce to the previous tower level.
    - **Logarithmic step**: by ln_structure, F decomposes as
      v₀ + c·ln(g). By IH, v₀ has a Liouville-form antiderivative G₀.
      The candidate G = G₀ + c·ln(g) has the right derivative
      (fully proved via the chain rule and SemEq). But G is in
      LiouvilleForm C x only if g ∈ C; we have g ∈ D'.

    The "log argument descent" — that tower-level log arguments
    can be traced back to the base field — follows classically from
    algebraic independence in the tower. It is the one remaining
    formalization gap. -/
theorem liouville_tower (C D : Eml → Prop) (f F : Eml) (x : Nat)
    (hC_ops : ∀ a b, C a → C b → C (add' a b) ∧ C (mul' a b) ∧ C (inv' a))
    (hTower : Tower C D)
    (hF : D F)
    (hint : SemEq (diff F x) f) :
    ∃ G, LiouvilleForm C x G ∧ SemEq (diff G x) f := by
  induction hTower generalizing f F with
  | base =>
    -- Tower height 0: D = C, so F ∈ C is already in Liouville form.
    exact ⟨F, LiouvilleForm.base F hF, hint⟩
  | exp_step D' g hTower' hg ih =>
    -- D = FieldClosure(D' ∪ {exp'(g)}), F ∈ D, D(F) ≈ₛ f.
    -- By exponential independence: ∃ F' ∈ D' with D(F) ≈ₛ D(F').
    obtain ⟨F', hF'D, hF'eq⟩ := exp_independence D' g F x
      (Tower.field_closed hTower' hC_ops)
      hg hF
    -- D(F') ≈ₛ D(F) ≈ₛ f
    have hint' : SemEq (diff F' x) f := SemEq.trans hF'eq.symm hint
    -- By IH on D' (previous tower level).
    exact ih f F' hF'D hint'
  | ln_step D' g hTower' hg ih =>
    -- D = FieldClosure(D' ∪ {ln'(g)}), F ∈ D, D(F) ≈ₛ f.
    -- By logarithmic structure: F has same derivative as v₀ + c·ln(g).
    obtain ⟨v₀, c, hv₀D, hc, hdeq⟩ := ln_structure D' g F x
      (Tower.field_closed hTower' hC_ops)
      hg hF
    -- By IH on v₀ ∈ D': get G₀ in Liouville form with D(G₀) ≈ₛ D(v₀).
    obtain ⟨G₀, hG₀form, hG₀sem⟩ := ih (diff v₀ x) v₀ hv₀D SemEq.rfl
    -- The candidate G = G₀ + c·ln(g) has the right derivative:
    --   D(G) →* D(G₀) + c·D(g)/g        [diff_liouville_one_term]
    --       ≈ₛ D(v₀) + c·D(g)/g         [IH: D(G₀) ≈ₛ D(v₀)]
    --       ←* D(v₀ + c·ln(g))           [diff_liouville_one_term, reversed]
    --       ≈ₛ D(F) ≈ₛ f                [ln_structure + hypothesis]
    have _hGsem : SemEq (diff (add' G₀ (mul' c (ln' g))) x) f :=
      SemEq.trans (SemEq.of_steps (diff_liouville_one_term G₀ c g x hc))
        (SemEq.trans (SemEq.add'_congr_l hG₀sem _)
          (SemEq.trans (SemEq.of_steps (diff_liouville_one_term v₀ c g x hc)).symm
            (SemEq.trans hdeq.symm hint)))
    -- G₀ + c·ln(g) has the right derivative (above), but is in
    -- LiouvilleForm C x only if g ∈ C. We have g ∈ D' (previous level).
    -- The "log argument descent" to the base field is the remaining gap.
    sorry

end Eml
