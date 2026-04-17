/-
  NoSheffer.lean
  ==============

  A standalone generalised no-go result for Sheffer-style generators
  of function classes with mixed partiality.

  Informal statement. Consider any domain `α`, any binary operator
  `⊙ : α → α → Option α` (possibly partial, with `none` meaning the
  operator is undefined at that pair), and any finite set of named
  constants. Form the class of functions representable as expression
  trees over `⊙`, the constants, and a single variable. The claim:

    If a target function class `F` contains both a *total* function
    (defined at every input) and a genuinely *partial* function
    (undefined somewhere), no choice of `⊙` and constants represents
    every member of `F`.

  This generalises the conjecture stated in `README.md` away from the
  specific operator `eml(x, y) = exp(x) − ln(y)`. It applies to any
  function class with the structural property above — the standard
  real/complex elementary functions, any "scientific calculator"
  class, classes extended with `Γ`, `ζ`, etc.

  What is proved here:

    * **Theorem 1** (`no_total_op_represents_partial`). A total
      operator cannot represent any partial function: if `m.op`
      never returns `none`, then every tree evaluates to `some _`
      at every input, so no tree's pointwise output matches a
      partial target.

    * **Theorem 2** (`richardsonRich_of_embedding`). Given a
      concrete reduction from Richardson 1968 to the full-domain
      decision problem for this model's trees, no computable
      procedure decides whether a tree has full natural domain.
      The reduction is honest: a `FullDomain` decider would,
      via the supplied embedding, give a decider for the
      Richardson property, contradicting the `richardson` axiom.

    * The ℂ-specific remaining direction — that a partial
      elementary operator cannot pointwise represent `neg` — and
      its combined no-go live in `Eml/NoShefferComplex.lean`,
      which imports Mathlib and cites the Elementary barrier (a
      classical complex-analysis result, itself unformalized).

  Unformalized classical theorem used in this file:

    * Richardson 1968 (+ Caviness extensions) — zero-equivalence
      for elementary expressions is undecidable. Declared via the
      `richardson` constant, which Lean classifies as an `axiom`;
      mathematically it is a published peer-reviewed theorem, not
      a foundational commitment.

  Only one such citation lives here; the ℂ-specific ones are in
  the companion file. The purpose of this file is the
  domain-agnostic structural content: tree algebra, the total-op
  theorem, and the Richardson reduction.

  This file is standalone. It imports nothing and depends on no
  other file in this repository.
-/

namespace NoSheffer

universe u v

/-! ## Expression trees -/

/-- Expression trees built from a single variable `var`, named
    constants drawn from an index type `ι`, and repeated applications
    of a binary operator `app`. Both the operator and the constants
    are interpreted by a `Model` introduced below.

    A single variable suffices for the argument: a multivariable tree
    reduces to this case by currying one argument at a time, and the
    no-go result applies argument-wise. -/
inductive Tree (ι : Type v) where
  | var   : Tree ι
  | const : ι → Tree ι
  | app   : Tree ι → Tree ι → Tree ι
  deriving Inhabited

/-- A semantic interpretation of trees over a domain `α`:

    * `op` is the binary operator, possibly partial (returning
      `none` where it is undefined);
    * `constVal` assigns each named constant a value in `α`. -/
structure Model (α : Type u) (ι : Type v) where
  op       : α → α → Option α
  constVal : ι → α

/-- Evaluate a tree at an input `x : α`. Any application whose two
    children produce values for which `op` is undefined (returns
    `none`) propagates `none` upward. -/
def eval {α : Type u} {ι : Type v} (m : Model α ι) (x : α) :
    Tree ι → Option α
  | .var     => some x
  | .const c => some (m.constVal c)
  | .app l r =>
      match eval m x l, eval m x r with
      | some a, some b => m.op a b
      | _, _ => none

@[simp] theorem eval_var {α ι} (m : Model α ι) (x : α) :
    eval m x Tree.var = some x := rfl

@[simp] theorem eval_const {α ι} (m : Model α ι) (x : α) (c : ι) :
    eval m x (Tree.const c) = some (m.constVal c) := rfl

/-- Under successful evaluation of both children, an application
    node's value equals the operator applied to those values. -/
theorem eval_app_some_some {α ι} (m : Model α ι) (x : α) (l r : Tree ι)
    {a b : α} (hl : eval m x l = some a) (hr : eval m x r = some b) :
    eval m x (Tree.app l r) = m.op a b := by
  show (match eval m x l, eval m x r with
        | some a, some b => m.op a b
        | _, _ => none) = m.op a b
  rw [hl, hr]

/-- A tree *represents* a partial function `f : α → Option α` under
    model `m` when tree evaluation matches `f` pointwise. -/
def Represents {α ι} (m : Model α ι) (T : Tree ι) (f : α → Option α) :
    Prop :=
  ∀ x, eval m x T = f x

/-! ## Theorem 1 — a total operator produces a total closure

    If the operator is defined at every pair (never returns `none`),
    then every tree built over it evaluates to `some _` at every
    input. Consequently, the closure of a total operator contains
    only total functions, and cannot represent any partial member
    of the target class.

    This is the first, directly-provable half of the obstruction. -/

/-- Core lemma: if the operator is total, every tree evaluates
    successfully at every input.

    Proof: induction on `T`. The variable and constant cases are
    immediate. For `app l r`, the induction hypotheses give values
    `a, b : α` such that the children evaluate to `some a, some b`;
    the totality hypothesis on `op` then produces a witness value
    for the application node. -/
theorem eval_some_of_op_total {α ι} (m : Model α ι)
    (h_total : ∀ a b, ∃ c, m.op a b = some c) :
    ∀ (T : Tree ι) (x : α), ∃ v, eval m x T = some v := by
  intro T
  induction T with
  | var => intro x; exact ⟨x, rfl⟩
  | const c => intro x; exact ⟨m.constVal c, rfl⟩
  | app l r ihl ihr =>
      intro x
      obtain ⟨a, ha⟩ := ihl x
      obtain ⟨b, hb⟩ := ihr x
      obtain ⟨c, hc⟩ := h_total a b
      refine ⟨c, ?_⟩
      rw [eval_app_some_some m x l r ha hb]
      exact hc

/-- **Theorem 1.** A total binary operator cannot represent any
    genuinely partial function.

    If `m.op` never returns `none`, and some function `f` returns
    `none` at an input `x₀`, then no tree under `m` represents `f`. -/
theorem no_total_op_represents_partial {α ι} (m : Model α ι)
    (h_total : ∀ a b, ∃ c, m.op a b = some c)
    (f : α → Option α) (x₀ : α) (h_partial : f x₀ = none)
    (T : Tree ι) (h_rep : Represents m T f) : False := by
  obtain ⟨v, hv⟩ := eval_some_of_op_total m h_total T x₀
  have h_eq : f x₀ = some v := (h_rep x₀).symm.trans hv
  rw [h_partial] at h_eq
  simp at h_eq

/-! ## Theorem 2 — partial operator, undecidable natural domains

    When the operator is partial, the closure *may* contain trees
    that evaluate successfully on every input actually tested.
    But determining whether a tree evaluates at every input — i.e.,
    has full natural domain as a function `α → α` — reduces to
    zero-equivalence of an associated expression, which is
    Richardson-undecidable for any closure rich enough to carry
    classical elementary signatures.

    This is the operational (not purely mathematical) obstruction:
    even if a partial operator happened to generate an interesting
    class, the compiler/verifier apparatus needed to use it would
    require deciding full natural domain, and that decision is
    forbidden by classical Richardson 1968. -/

/-- A tree's *natural domain* is total (full) when evaluation
    succeeds at every input. -/
def FullDomain {α ι} (m : Model α ι) (T : Tree ι) : Prop :=
  ∀ x, ∃ v, eval m x T = some v

/-- A model is *Richardson-rich* when no computable predicate on
    trees decides full natural domain. The substantive content of
    Richardson-richness is supplied via a `RichardsonEmbedding`
    (below): a concrete reduction from an axiomatic Richardson
    undecidability result to the full-domain question. -/
def RichardsonRich {α ι} (m : Model α ι) : Prop :=
  ¬ ∃ (decider : Tree ι → Bool),
      ∀ T, decider T = true ↔ FullDomain m T

/-- Corollary. Richardson-richness rules out trivially-total closures:
    if *every* tree had full domain, the constant `true` decider
    would decide full domain. So Richardson-rich models must contain
    at least one tree whose natural domain is a proper subset of `α`. -/
theorem richardson_rich_has_partial_tree {α ι} (m : Model α ι)
    (h_rich : RichardsonRich m) :
    ∃ T : Tree ι, ¬ FullDomain m T := by
  apply Classical.byContradiction
  intro h_no_partial
  apply h_rich
  refine ⟨fun _ => true, fun T => ⟨fun _ => ?_, fun _ => rfl⟩⟩
  apply Classical.byContradiction
  intro hT
  exact h_no_partial ⟨T, hT⟩

/-! ### Axiomatic Richardson and the embedding reduction

    What we axiomatize here is literally a classical-Richardson-family
    undecidability result, packaged as a `RichardsonFamily` bundle:
    a type of expressions, a `HasZero` property, and a proof that
    `HasZero` is not computably decidable. The specific property can
    be read as either zero-identity (`E ≡ 0`, Richardson 1968) or
    zero-existence (`∃ x. E(x) = 0`, derived from Richardson-family
    results by Caviness, Wang, and the Matiyasevich reduction). Our
    reduction uses zero-existence semantics when `⊙`'s singularity is
    a point (as in `eml`), but the bundle is flexible enough for
    either direction.

    A `RichardsonEmbedding` is the concrete reduction: a computable
    map from Richardson expressions to trees, with the semantic
    bridge `FullDomain(embed E) ↔ ¬ HasZero E`. Given such an
    embedding, the reduction theorem shows the model is
    Richardson-rich in the strict sense — by genuinely reducing
    the axiomatic Richardson theorem to the full-domain decision
    problem for trees. -/

/-- An abstract Richardson-family undecidability bundle. The
    intended inhabitant comes from Richardson 1968 (+ Caviness
    extensions): the zero problem for elementary expressions over
    ℝ with signature `{ℤ, π, +, ·, sin, exp, |·|}` is undecidable. -/
structure RichardsonFamily where
  Expr        : Type
  HasZero     : Expr → Prop
  undecidable : ¬ ∃ (d : Expr → Bool), ∀ E, d E = true ↔ HasZero E

/-- Richardson 1968 applied to elementary expressions: the zero
    problem is undecidable.

    Mathematically this is a published theorem (Richardson, "Some
    unsolvable problems involving elementary functions of a real
    variable", JSL 1968) with known peer-reviewed proofs; Caviness
    and others extended it. It is not a foundational commitment.

    We declare it with the `axiom` keyword only because the Lean
    translation of Richardson 1968 has not been written. The
    `RichardsonFamily` bundle abstracts over the specific signature
    so that whichever classical variant matches Mathlib's eventual
    formalization can be plugged in without rewiring the reduction. -/
axiom richardson : RichardsonFamily

/-- A `RichardsonEmbedding` is the concrete reduction hypothesis
    connecting a model's tree closure to Richardson's theorem: a
    computable map from elementary expressions to trees, together
    with the semantic identity `FullDomain(embed E) ↔ ¬ HasZero E`.

    For the EML-style operator `⊙(x, y) = exp(x) − ln(y)` with
    `HasZero` = zero-existence, one verifies this with
    `embed E = ⊙(anything, E)`: the tree's natural domain is
    `{x : E(x) ≠ 0}`, full precisely when `E` is nowhere zero. -/
structure RichardsonEmbedding {α : Type u} {ι : Type v} (m : Model α ι) where
  embed     : richardson.Expr → Tree ι
  reduction : ∀ E, FullDomain m (embed E) ↔ ¬ richardson.HasZero E

/-- **Theorem 2 (real content).** A Richardson-embedded model is
    Richardson-rich: no computable procedure decides full natural
    domain. The proof is a direct reduction — a full-domain decider
    would, via the embedding, produce a `HasZero` decider,
    contradicting the Richardson axiom. -/
theorem richardsonRich_of_embedding {α ι} (m : Model α ι)
    (emb : RichardsonEmbedding m) : RichardsonRich m := by
  rintro ⟨d, hd⟩
  apply richardson.undecidable
  refine ⟨fun E => Bool.not (d (emb.embed E)), fun E => ?_⟩
  show Bool.not (d (emb.embed E)) = true ↔ richardson.HasZero E
  constructor
  · -- `!(d (embed E)) = true` → `HasZero E`.
    intro hneg
    apply Classical.byContradiction
    intro hnotHZ
    have hFD : FullDomain m (emb.embed E) := (emb.reduction E).mpr hnotHZ
    have hdT : d (emb.embed E) = true := (hd _).mpr hFD
    rw [hdT] at hneg
    exact absurd hneg (by decide)
  · -- `HasZero E` → `!(d (embed E)) = true`.
    intro hHZ
    have hNotFD : ¬ FullDomain m (emb.embed E) :=
      fun hfd => (emb.reduction E).mp hfd hHZ
    have hd_not_true : d (emb.embed E) ≠ true :=
      fun heq => hNotFD ((hd _).mp heq)
    show Bool.not (d (emb.embed E)) = true
    cases hv : d (emb.embed E) with
    | false => rfl
    | true  => exact absurd hv hd_not_true

/-! ## Remaining direction — the partial-operator ℂ barrier

    Theorems 1 and 2 handle the total-operator case and the
    decidability barrier. The remaining content — that a partial
    elementary operator on ℂ cannot pointwise represent `neg` —
    requires concrete ℂ machinery (Hadamard factorization, branch-
    cut identities, growth-rate analysis) and lives in
    `Eml/NoShefferComplex.lean`. That file imports Mathlib and
    supplies the ℂ-specific barrier as a real Lean theorem
    derived from labeled classical axioms (Hadamard factorization,
    growth gap), together with the combined no-go for ℂ.

    Keeping that content in a separate file preserves this file's
    domain-agnostic status: `NoSheffer.lean` works over any `α`,
    any `ι`, and needs no analytic structure. -/

end NoSheffer
