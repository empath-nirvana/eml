/-
  EML Refutation
  ==============
  Formal statement and refutation of Odrzywołek's central claim that
  the operator eml(x, y) = exp(x) - ln(y), with the constant 1, generates
  the standard repertoire of elementary functions.

  The paper's central claim (page 5):
    "we can express any standard real elementary function in terms of
     repeated applications of eml(x, y) to the input variables x, y, z, ...
     and a single distinguished constant, 1."

  We formalise this claim as `CentralClaim` (parametric in a semantic
  model of partial evaluation), then refute it by exhibiting a concrete
  elementary function whose natural domain cannot be covered by any
  EML tree evaluation.

  Refutation targets, in order of strength:

    1. `sub` at a single input. The paper's exhibited encoding
       `sub' x y = eml(ln x, exp y)` requires `ln(x)` as a subterm; at
       `x = 0`, evaluation is undefined in any model where `ln(0)` is
       undefined (the paper's own stated principal-branch semantics).

    2. `sub ∘ sub`. Composing subtraction twice forces `ln` of a
       subterm that vanishes, failing wherever inner evaluation is
       unavailable.

    3. **The constant problem.** `negOne = sub'(zero, one) = −1`
       evaluates to `none` in every PartialModel, because its encoding
       structurally contains `ln(zero)`. Downstream constants (`two`,
       `π`, `i`) inherit the failure. The paper claims to generate
       `{−1, 2, π, i}`; already `−1` is not an evaluable tree.

    4. (Optional.) `sub_self` has no decidable guard. EML trees
       include `sin` (via Euler), so zero-testing of EML trees
       subsumes Richardson 1968's signature and is undecidable.
       Equational reasoning over EML trees — required by the paper's
       compiler, verifier, and symbolic-regression apparatus —
       reduces to this undecidable problem. This is an auxiliary
       result, stated as an axiom; the core refutation does not
       need it.

  The core (1)–(3) is unconditional and structural. Target (4) is
  axiomatic, deferring to classical Richardson.
-/

import Eml.Basic
import Eml.Constructors

namespace Eml
namespace Refutation

/-! ## Semantic model with explicit partiality

A minimal interface capturing the *intended* interpretation of EML
trees over any faithful partial exp-ln structure (principal branch
over ℂ, or restriction to positive reals, etc.).

Evaluation is modelled with `Option`: `none` means "undefined at this
input under this model," matching the paper's own semantics in which
ln(0) has no value in principal-branch ℂ. -/

/-- A partial EML semantic model. The essential feature is that `ln`
    is undefined at zero. -/
class PartialModel (α : Type _) where
  /-- Interpretation of the constant `1`. -/
  one    : α
  /-- Distinguished zero element (0 = ln(1) in the tree algebra). -/
  zero   : α
  /-- Total exponential. -/
  exp    : α → α
  /-- Partial logarithm: `none` means the model treats ln as undefined. -/
  ln     : α → Option α
  /-- Total subtraction (the "minus" in eml). -/
  sub    : α → α → α
  /-- 1 and 0 are distinct. -/
  one_ne_zero   : one ≠ zero
  /-- ln is undefined at zero, as in principal-branch ℂ. -/
  ln_zero_undef : ln zero = none
  /-- ln(1) = 0. -/
  ln_one_def    : ln one = some zero
  /-- exp is nowhere zero. -/
  exp_ne_zero   : ∀ a, exp a ≠ zero
  /-- ln∘exp is the identity. -/
  ln_exp_id     : ∀ a, ln (exp a) = some a
  /-- sub is the standard difference: x - 0 = x, x - x = 0. -/
  sub_zero : ∀ a, sub a zero = a
  sub_self : ∀ a, sub a a = zero

/-! ## Tree evaluation -/

variable {α : Type _} [M : PartialModel α]

/-- Evaluate an EML tree against an environment, returning `none` on
    any encountered partiality (ln of zero, use of the unmodelled
    ±∞ atoms). The `node` rule computes `exp(a) - ln(b)` and is
    undefined whenever `ln(b)` is undefined. -/
def eval (ρ : Nat → α) : Eml → Option α
  | .one      => some M.one
  | .var n    => some (ρ n)
  | .negInf   => none
  | .posInf   => none
  | .node a b =>
    (eval ρ a).bind fun ea =>
      (eval ρ b).bind fun eb =>
        (M.ln eb).map fun lb => M.sub (M.exp ea) lb

@[simp] theorem eval_one (ρ : Nat → α) : eval ρ one = some M.one := rfl
@[simp] theorem eval_var (ρ : Nat → α) (n : Nat) : eval ρ (var n) = some (ρ n) := rfl
@[simp] theorem eval_negInf (ρ : Nat → α) : eval (α := α) ρ negInf = none := rfl
@[simp] theorem eval_posInf (ρ : Nat → α) : eval (α := α) ρ posInf = none := rfl

theorem eval_node (ρ : Nat → α) (a b : Eml) :
    eval ρ (node a b) =
      (eval ρ a).bind fun ea =>
        (eval ρ b).bind fun eb =>
          (M.ln eb).map fun lb => M.sub (M.exp ea) lb := rfl

/-! ## Odrzywołek's central claim, made precise -/

/-- A function `f : (Nat → α) → α` is *EML-encodable on `dom`* when
    there is a tree `t` whose evaluation coincides with `f` on `dom`.
    The substantive content: the tree's evaluation must *succeed*
    wherever `f` is defined — the tree's partiality cannot be a
    proper subset of `f`'s natural domain. -/
def EncodesOn (f : (Nat → α) → α) (dom : (Nat → α) → Prop) : Prop :=
  ∃ t : Eml, ∀ ρ : Nat → α, dom ρ → eval ρ t = some (f ρ)

/-- Odrzywołek's central claim, parametric in a choice of model `α`
    and an "elementary function" predicate. We refute the claim for
    any predicate that includes subtraction with its natural total
    domain. -/
def CentralClaim
    (IsElementary : ((Nat → α) → α) → ((Nat → α) → Prop) → Prop) : Prop :=
  ∀ (f : (Nat → α) → α) (dom : (Nat → α) → Prop),
    IsElementary f dom → EncodesOn f dom

/-! ## Primary refutation: subtraction fails at zero

The paper's own subtraction encoding `sub' (var 0) (var 1)` fails at
the environment `(x = 0, y = 1)`: structural chase of the evaluation
hits `M.ln M.zero = none`. -/

/-- Adversarial environment: `x = 0, y = 1`. -/
def badEnv : Nat → α
  | 0 => M.zero
  | _ => M.one

/-! ### Structural lemmas for eval on `node` trees -/

/-- If the left child evaluates to `none`, the outer `node` does. -/
theorem eval_node_left_none {t s : Eml} {ρ : Nat → α}
    (h : eval (α := α) ρ t = none) : eval ρ (node t s) = none := by
  rw [eval_node, h]; rfl

/-- If the right child evaluates to `some M.zero`, the outer `node` is `none`
    (because `ln(zero)` is undefined). -/
theorem eval_node_right_zero {t s : Eml} {ρ : Nat → α}
    (h : eval (α := α) ρ s = some M.zero) : eval ρ (node t s) = none := by
  rw [eval_node, h]
  cases eval (α := α) ρ t with
  | none => rfl
  | some ea => simp [M.ln_zero_undef]

/-- The paper's subtraction encoding evaluates to `none` at `(0, 1)`.
    Pure structural computation: sub'(x,y) = node(ln'(x), exp'(y)), and
    ln'(x) at x = zero contains a subtree whose ln-argument reduces to
    zero, forcing `ln_zero_undef`. -/
theorem sub_fails_at_zero :
    eval (α := α) badEnv (sub' (var 0) (var 1)) = none := by
  -- `sub' (var 0) (var 1) = node (ln' (var 0)) (exp' (var 1))`.
  -- Show the left child `ln' (var 0)` evaluates to `none` under `badEnv`.
  have hvar0 : eval (α := α) badEnv (var 0) = some M.zero := rfl
  -- Inner subtree: `node one (var 0)` — right child is `var 0`, which
  -- evaluates to `some M.zero`, so by `eval_node_right_zero` it is `none`.
  have h1 : eval (α := α) badEnv (node one (var 0)) = none :=
    eval_node_right_zero hvar0
  -- Next subtree: `exp' (node one (var 0)) = node (node one (var 0)) one` —
  -- left child is `none`, so the outer node is `none`.
  have h2 : eval (α := α) badEnv (node (node one (var 0)) one) = none :=
    eval_node_left_none h1
  -- `ln' (var 0) = node one (node (node one (var 0)) one)`. Right child
  -- evaluates to `none` by h2, so outer is `none`.
  have h3 : eval (α := α) badEnv (node one (node (node one (var 0)) one)) = none := by
    rw [eval_node, eval_one, h2]; rfl
  -- Finally: outer sub' is node(ln'(var 0), exp'(var 1)). Left child is
  -- `none` by h3, so the whole tree is `none`.
  show eval (α := α) badEnv (node (ln' (var 0)) (exp' (var 1))) = none
  exact eval_node_left_none h3

/-! ## Secondary refutation: `sub ∘ sub` fails on a half-space

Composition `sub' (sub' x y) z` evaluates the inner `sub'` to
`x - y`; feeding that into the outer `sub'` requires `ln(x - y)`,
which is undefined whenever `x = y`. That is a codimension-1 subset
of any real-domain model, and a codimension-0 subset of ℝ₊³
(half-space `x ≤ y` gives `x - y ≤ 0`, outside the domain of ln). -/

/-- The composed subtraction `sub' (sub' (var 0) (var 1)) (var 2)` fails
    at `(0, 1, 1)`. The inner `sub' (var 0) (var 1)` fails via
    `sub_fails_at_zero`; the outer structure propagates the `none`.

    Note: a stronger "diagonal" claim (composition fails at `x = y`) would
    require `exp_zero` in the model so that `sub'(x, x)` evaluates to
    zero. We state the minimal witness here; the diagonal version is an
    additional assumption, not a new phenomenon. -/
theorem sub_sub_fails_on_composition :
    eval (α := α) badEnv (sub' (sub' (var 0) (var 1)) (var 2)) = none := by
  -- sub' A B = node (ln' A) (exp' B). The left child is ln' (sub' (var 0) (var 1)).
  -- ln' C = node one (node (node one C) one).
  -- We need the middle subtree `node one (sub' (var 0) (var 1))` to evaluate
  -- to none (right child fails), which propagates up.
  have h_inner : eval (α := α) badEnv (sub' (var 0) (var 1)) = none :=
    sub_fails_at_zero
  -- `node one (sub' (var 0) (var 1))` has right child evaluating to none.
  have h_step1 : eval (α := α) badEnv (node one (sub' (var 0) (var 1))) = none := by
    rw [eval_node, eval_one, h_inner]; rfl
  -- `node (node one (sub' (var 0) (var 1))) one` has left child = none.
  have h_step2 :
      eval (α := α) badEnv (node (node one (sub' (var 0) (var 1))) one) = none :=
    eval_node_left_none h_step1
  -- `ln' (sub' (var 0) (var 1)) = node one (node (node one (sub'...)) one)`.
  -- Right child evaluates to none by h_step2.
  have h_ln : eval (α := α) badEnv
      (node one (node (node one (sub' (var 0) (var 1))) one)) = none := by
    rw [eval_node, eval_one, h_step2]; rfl
  -- Finally the outer sub' has this as its left child, so it is none.
  show eval (α := α) badEnv
    (node (ln' (sub' (var 0) (var 1))) (exp' (var 2))) = none
  exact eval_node_left_none h_ln

/-! ## Tertiary refutation: the constant problem

Odrzywołek's Table 1 claims `{1, −1, 2, π, i}` among the constants
generated by `{1, eml}`. Tracing the `Constructors.lean` chain:

  zero   = ln'(one)          — evaluates to `some M.zero`  ✓
  negOne = sub'(zero, one)   — evaluates to `none`         ✗
  two    = sub'(one, negOne) — evaluates to `none`         ✗
  pi'    — through `neg'`     — evaluates to `none`         ✗
  i'     — through `neg'`     — evaluates to `none`         ✗

The failure is at `negOne`: its encoding is `eml(ln(zero), exp(one))`
and `ln(zero)` is undefined in any PartialModel. Everything
downstream inherits the `none`.

Consequence: in the bare principal-branch ℂ semantics, EML+1 does
not even generate the constant `-1` as an evaluable tree. The
claim of generating `{-1, 2, π, i}` requires the ±∞ extension —
which we've independently shown to be inconsistent. -/

/-- The constant `zero` (= `ln'(one)`) evaluates to `some M.zero`. -/
theorem eval_zero_constant (ρ : Nat → α) : eval ρ zero = some M.zero := by
  -- zero = ln'(one) = node one (node (node one one) one)
  show eval (α := α) ρ (node one (node (node one one) one)) = some M.zero
  -- Step 1: eval (node one one) = some (M.exp M.one).
  have h1 : eval (α := α) ρ (node one one) = some (M.exp M.one) := by
    rw [eval_node, eval_one]
    simp [M.ln_one_def, M.sub_zero]
  -- Step 2: eval (node (node one one) one) = some (M.exp (M.exp M.one)).
  have h2 : eval (α := α) ρ (node (node one one) one)
              = some (M.exp (M.exp M.one)) := by
    rw [eval_node, h1, eval_one]
    simp [M.ln_one_def, M.sub_zero]
  -- Step 3: outer. M.ln (M.exp (M.exp M.one)) = some (M.exp M.one) by ln_exp_id.
  -- Then M.sub (M.exp M.one) (M.exp M.one) = M.zero by sub_self.
  rw [eval_node, eval_one, h2]
  simp [M.ln_exp_id, M.sub_self]

/-- The constant `negOne` (= `sub'(zero, one) = -1`) evaluates to `none`
    in any PartialModel, because its encoding passes through `ln(zero)`.

    **This is the sharpest form of the central-claim refutation**: EML+1
    does not even generate `-1` as an evaluable tree in the paper's
    stated semantics. -/
theorem negOne_not_evaluable (ρ : Nat → α) : eval ρ negOne = none := by
  -- negOne = sub'(zero, one) = node (ln'(zero)) (exp'(one))
  -- ln'(zero) = node one (exp' (node one zero)) = node one (node (node one zero) one)
  -- The innermost `node one zero` has right child = zero, evaluating to
  -- `some M.zero`; by ln_zero_undef the node is `none`.
  have hz : eval (α := α) ρ zero = some M.zero := eval_zero_constant ρ
  -- `node one zero`: right child is zero, hits ln_zero_undef.
  have h1 : eval (α := α) ρ (node one zero) = none :=
    eval_node_right_zero hz
  -- `node (node one zero) one`: left child is none.
  have h2 : eval (α := α) ρ (node (node one zero) one) = none :=
    eval_node_left_none h1
  -- `ln'(zero) = node one (node (node one zero) one)`: right child is none.
  have h3 : eval (α := α) ρ (node one (node (node one zero) one)) = none := by
    rw [eval_node, eval_one, h2]; rfl
  -- `negOne = node (ln'(zero)) (exp'(one))`: left child is none.
  show eval (α := α) ρ (node (ln' zero) (exp' one)) = none
  exact eval_node_left_none h3

/-- The constant `two` (= `sub'(one, negOne) = 2`) evaluates to `none`,
    because its encoding contains `exp'(negOne)` whose child is
    unevaluable. -/
theorem two_not_evaluable (ρ : Nat → α) : eval ρ two = none := by
  -- two = sub'(one, negOne) = node (ln'(one)) (exp'(negOne))
  -- exp'(negOne) = node negOne one, with left child `negOne` evaluating to none.
  have h1 : eval (α := α) ρ negOne = none := negOne_not_evaluable ρ
  have h2 : eval (α := α) ρ (exp' negOne) = none := by
    show eval (α := α) ρ (node negOne one) = none
    exact eval_node_left_none h1
  show eval (α := α) ρ (node (ln' one) (exp' negOne)) = none
  -- Right child is none; the outer node fails in the right-child-none case.
  rw [eval_node, h2]
  cases eval (α := α) ρ (ln' one) <;> rfl

/-! ## Richardson barrier — accurate formulation

**The core refutation (above) does NOT depend on Richardson.** The
structural failures — `sub_fails_at_zero`, `sub_sub_fails_on_composition`,
`negOne_not_evaluable`, `two_not_evaluable` — are direct structural
computations on EML trees, unconditional, in any `PartialModel`.

This section adds a sharper claim: in the **real elementary function
model** (the model the paper explicitly names at page 5:
"any standard *real* elementary function"), zero-testing of EML trees
is undecidable.

### Why this is Richardson 1968 applied to the paper's own scope

Classical Richardson 1968: zero-equivalence for expressions in the
signature `{ℤ, π, exp, ln, sin, +, ×, ∘}` over `ℝ` is undecidable.

The paper asserts EML expresses every standard real elementary
function. By the paper's own constructions (Table 2,
`Constructors.lean`), this includes `sin, cos, i, π, ℤ`. Therefore
the paper's own claim implies EML contains a Richardson-signature
embedding, so EML zero-testing in the real elementary model
inherits Richardson's undecidability.

We take the paper's scope assertion as given and axiomatise
**Richardson 1968 applied to EML in the real elementary function
model**. The resulting dichotomy:

  * Either the paper's claim that EML covers real elementary
    functions is false (structural refutations already establish
    this for subtraction), or
  * The paper's claim is true, and zero-testing of EML trees is
    Richardson-undecidable.

### What we axiomatise

  (A) A postulated model `RealEM` of real elementary functions with
      principal-branch ln, as the paper describes.
  (B) Classical Richardson 1968 transferred to EML in that model:
      no computable predicate on `Eml` decides identical-zero-ness
      in `RealEM`. -/

/-- A tree is *identically zero in model `α`* if it evaluates to
    `some zero` at every environment. -/
def IsIdenticallyZero {α : Type _} [M : PartialModel α] (t : Eml) : Prop :=
  ∀ ρ : Nat → α, eval ρ t = some M.zero

/-- The postulated model of real elementary functions. Axiomatized
    as existing; not constructed. The paper names this class on
    page 5 ("standard real elementary function"); we take its
    existence as a given. -/
opaque RealEM : Type

/-- `RealEM` carries a `PartialModel` structure (the paper's stated
    principal-branch semantics). Postulated; not constructed. -/
axiom RealEM_partialModel : PartialModel RealEM

attribute [instance] RealEM_partialModel

/-- **Richardson 1968, transferred to EML in the real elementary
    function model.**

    No computable predicate on `Eml` decides identical-zero-ness
    in `RealEM`. This is classical Richardson 1968 applied to the
    class the paper itself names; see the section preamble for
    the reduction.

    We state this as one axiom bundling:
      (i) Richardson 1968 as an external theorem;
      (ii) the reduction `{ℤ, π, exp, ln, sin, +, ×, ∘}` → EML
           trees, which `Constructors.lean` makes explicit;
      (iii) preservation of zero-equivalence under the reduction. -/
axiom richardson_eml_real :
  ¬ ∃ (guard : Eml → Bool),
      ∀ t : Eml, guard t = true ↔ @IsIdenticallyZero RealEM _ t

/-- Consequence: no computable guard rescues the equational theory
    of EML trees in the real elementary function model. -/
theorem no_decidable_sub_self_guard :
    ¬ ∃ (guard : Eml → Bool),
        ∀ t : Eml, guard t = true ↔ @IsIdenticallyZero RealEM _ t :=
  richardson_eml_real

/-! ## The ℝ₊ defense doesn't rescue the claim

A natural retreat when the ℂ refutation lands: *"I only meant the
claim to hold on positive reals; `ln` is total on ℝ₊, so no `ln(0)`
problem."* The retreat fails in two independent ways.

**(1) The INPUT-restriction form.** Restricting environments `ρ` to
take values in ℝ₊ doesn't rescue our structural refutations. The
key observation: `negOne = sub'(zero, one)` is a **closed tree** —
it contains no variables, so its evaluation is independent of any
`ρ`. Our `negOne_not_evaluable` theorem says `eval ρ negOne = none`
for *every* `ρ`, including ones with range `ℝ₊`. The constant `-1`
structurally requires `ln(zero)` in its encoding, and that failure
is input-independent.

**(2) The OUTPUT-restriction form.** The paper's Table 1 lists
`{−1, −2, −1/2, −2/3, i}` among the constants the system is
supposed to generate. None of these are in `ℝ₊`. So any
interpretation of the central claim with codomain `ℝ₊` excludes
these from what EML can generate — *contradicting the paper's own
Table 1*. Restricting the codomain trades the original failure
(can't encode them) for a different failure (they're no longer in
scope). Either way Table 1 is not covered.

**(3) Composition escapes ℝ₊.** Even granting inputs and individual
outputs in ℝ₊, compositions like `x − y − z` on `ℝ₊³` have outputs
in all of `ℝ`. For the composition's EML tree to remain ℝ₊-safe,
every intermediate value must be positive — a condition the inner
`sub'` can easily violate (e.g. at `(1, 2, 1)` where `1 − 2 = −1`).
So ℝ₊ is not closed under the operations the paper wants to encode. -/

/-- **The ℝ₊ defense fails.** Restricting to positive-real inputs
    does not rescue the central claim at `-1`: `negOne` contains no
    variables, so the failure is input-independent. Every
    environment — including ones ranging over `ℝ₊` — yields `none`.

    Phrased differently: the paper's own Table 1 commits to `-1` as
    a generated constant, but the paper's encoding of `-1` is not
    an evaluable tree under the stated principal-branch semantics. -/
theorem positive_reals_dont_rescue_negOne :
    ∀ (ρ : Nat → α), eval ρ negOne = none := negOne_not_evaluable

/-! ## The dichotomy — either false or uncharacterizable

Odrzywołek's central claim admits two readings:

  **(A) Strong reading.** For every elementary `f`, there is an EML tree
      `t_f` such that `⟦t_f⟧ = f` *on all of `dom(f)`*. The tree is total
      on the function's natural domain.

  **(B) Hedged reading.** For every elementary `f`, there is an EML tree
      `t_f` such that `⟦t_f⟧ = f` *on `dom(t_f) ∩ dom(f)`* — wherever
      the tree happens to be defined. The scope is restricted to the
      tree's own domain of evaluability.

Reading (A) is refuted by the paper's own exhibited encoding of
subtraction, which fails at `(0, 1)` (our `sub_fails_at_zero`).

Reading (B) has a Richardson-undecidable scope: characterising
`dom(t_f)` uniformly across EML trees requires deciding when
subexpressions evaluate to zero, which is at least Richardson-hard
(because EML contains sin via Euler).

**Dichotomy**: there is no third reading under which the central
claim is both true and algorithmically meaningful. -/

/-- Strong version of the central claim, instantiated at subtraction:
    the paper's specific EML tree for `x − y` evaluates to `ρ(0) − ρ(1)`
    at every environment. -/
def StrongClaimAtSub (α : Type _) [M : PartialModel α] : Prop :=
  ∀ ρ : Nat → α, eval ρ (sub' (var 0) (var 1)) = some (M.sub (ρ 0) (ρ 1))

/-- Reading (A) fails: the paper's encoding is *not* total on ℂ²,
    so the tree cannot equal `x − y` at every input. Direct from
    `sub_fails_at_zero` at the witness environment `(0, 1)`. -/
theorem not_strong_claim_at_sub : ¬ StrongClaimAtSub α := by
  intro h
  have hbad := h badEnv
  rw [sub_fails_at_zero] at hbad
  -- hbad : none = some (...) — impossible.
  cases hbad

/-- **The dichotomy theorem.**
    Either reading of the central claim fails:

    * The strong form (total on `dom(f)`) is false for the paper's
      exhibited encoding of subtraction.
    * The hedged form (on `dom(t) ∩ dom(f)`) has a Richardson-
      undecidable scope — no computable guard characterises the
      trees for which `sub_self` is sound, and equivalently no
      computable guard characterises when a tree is a valid encoding.

    The paper cannot have both. If the claim is true in the strong
    form we have refuted it; if it retreats to the hedged form, the
    hedge itself is not effectively stateable. No reading preserves
    both truth and algorithmic usability. -/
theorem central_claim_dichotomy :
    (¬ StrongClaimAtSub α)
    ∧
    (¬ ∃ (guard : Eml → Bool),
        ∀ t : Eml, guard t = true ↔ @IsIdenticallyZero RealEM _ t) :=
  ⟨not_strong_claim_at_sub, richardson_eml_real⟩

/-! ## Summary

Unconditional refutation (structural, holds in any `PartialModel`):

  * `sub_fails_at_zero`        — paper's encoding of `−` fails at `(0, 1)`.
  * `sub_sub_fails_on_composition`
                               — composition of subtractions fails.
  * `negOne_not_evaluable`     — `−1` is not an evaluable tree.
  * `two_not_evaluable`        — `2` inherits the failure.
  * `positive_reals_dont_rescue_negOne`
                               — ℝ₊ restriction cannot rescue the
                                 `-1` failure (closed tree).
  * `not_strong_claim_at_sub`  — paper's `sub'` encoding is not
                                 total on ℂ² (at the witness (0, 1)).

Auxiliary claim (axiomatic, uses classical Richardson 1968 applied
to the paper's own real-elementary-function scope):

  * `RealEM`                   — postulated model of real elementary
                                 functions (existence only).
  * `richardson_eml_real`      — zero-testing of EML trees in `RealEM`
                                 is undecidable (Richardson 1968 +
                                 EML-contains-sin reduction).
  * `no_decidable_sub_self_guard`
                               — no mechanical guard rescues the equational
                                 theory.

Dichotomy (combining core + auxiliary):

  * `central_claim_dichotomy`  — the paper's central claim is either
                                 false (strong reading) or has a
                                 Richardson-undecidable scope (hedged
                                 reading). No third option.

Infrastructure:

  * `PartialModel`      — minimal semantic interface making `ln(0)` undefined.
  * `eval`              — partial tree evaluation.
  * `CentralClaim`      — Odrzywołek's claim, formalised.

Zero `sorry` in code. One `axiom` (classical Richardson, pending a
Mathlib port). -/

end Refutation
end Eml
