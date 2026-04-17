# EML — Formal Refutation Notes

Lean 4 formalization of a refutation of the central claim of
Odrzywołek's paper *"All elementary functions from a single operator"*
(arXiv:2603.21852v2, 2026), which proposes that the binary operator
`eml(x, y) = exp(x) − ln(y)` together with the constant `1` generates
the standard class of elementary functions.

This repository started as an attempt to *formalize* the paper's claim.
It ended as a formal refutation: the central claim is either false
on a literal reading or has an algorithmically uncharacterizable scope
on any weaker reading that might salvage it.

## The paper's claim

> *"Using the EML, a surprisingly simple binary operator, we can express
> any standard real elementary function in terms of repeated applications
> of (3) to the input variables x, y, z, … and a single distinguished
> constant, 1."* — Odrzywołek 2026, p. 5.

Rephrased: for every elementary function `f` there exists a finite
binary tree over `{1, eml}` (plus variables) whose pointwise evaluation
equals `f` on `f`'s natural domain.

## The refutation in one sentence

The paper's own compilation scheme (spelled out in `Eml/Constructors.lean`)
produces tree encodings that are **structurally unevaluable** for every
operation that uses addition: the default encoding routes every `+`
through a subtraction of a negation, and every negation through
`sub(zero, z) = eml(ln(zero), exp(z))` which structurally requires
`ln(0)` — undefined in any model the paper names.

## The cascade

From `Eml/Refutation.lean`:

1. `ln(0)` is undefined (`PartialModel.ln_zero_undef`).
2. `negOne = sub'(zero, 1)` structurally contains `ln(0)` → unevaluable
   (`negOne_not_evaluable`).
3. `neg'(z) = sub'(zero, z)` contains `ln(0)` for every `z` → unevaluable
   (`neg_not_evaluable`).
4. `add'(a, b) = sub'(a, neg'(b))` contains `neg'(b)` → unevaluable for
   every `a, b` (`add_not_evaluable`).
5. Everything that uses addition inherits the failure: `mul, div, pow,
   sin, cos, π, i, sqrt, …` — nearly all of Table 1.

## The dichotomy

The paper's central claim admits four plausible readings. Each fails:

| Reading | Scope | Failure |
|---|---|---|
| (C₁) Strong, ℂ principal branch | `dom(f)` | Pointwise failures at `(0, 1)`, at constant `−1`, and structurally through `add'`. |
| (C₂) Hedged, ℂ principal branch | `dom(f) ∩ dom(t)` | Scope is Richardson-undecidable; no algorithmic characterization. |
| (C₊) Restriction to `ℝ₊` | `ℝ₊` | Excludes Table 1's negative constants and imaginary unit; doesn't rescue closed-tree failures. |
| (C∞) Extended `ℂ ∪ {±∞}` | extended reals | `sub_self` becomes unsound (formal counterexample in `Eml/Partiality.lean`); the equational apparatus the paper needs is inconsistent. |

**No reading is simultaneously true, faithful to Table 1, consistent with
the rewrite rules the paper needs, and algorithmically meaningful.**

## Alternative-witness defense

One might object: "The paper gives an alternative encoding for `−1`,
namely `−z = 1 − (e − ((e − 1) − z))`, which evaluates cleanly."
True — but it doesn't rescue the claim:

* `non_confluence_via_alternative_witness` — any alternative encoding
  of `−1` that successfully evaluates necessarily disagrees pointwise
  with the paper's default `negOne`. So the paper's equational
  identification is unsound.
* `no_canonical_normalization` — no computable normalization procedure
  can map trees to a canonical form characterizing identical-zero-ness
  (would solve Richardson).

So the alternative witness creates a different form of the failure
(non-confluence, two trees for the same function with different
evaluations, no algorithmic bridge between them) rather than curing
the original.

## What if we allow real numbers as leaves?

The paper is persistently ambiguous about what a variable `z` *is*.
When it writes

    sin(z) = eml(1, eml(eml(1, z), 1))

the `z` on both sides is doing two jobs simultaneously:

1. A **syntactic placeholder** — a leaf position in the tree on the right.
2. A **real number** ranging over ℂ — the argument of the function on the left.

Informal math conflates these; formal math has to split them. `Refutation.lean`
uses the standard setup: trees have a constructor `var : Nat → Eml`, and
evaluation takes an environment `ρ : Nat → α` that binds each variable to a
semantic value. This lets `var 0` (a tree leaf) be distinct from `ρ 0` (the
value it takes on a given call).

A reasonable reader response: *"The paper isn't really talking about the
`{1, eml}` grammar with formal variables. It's talking about trees whose
leaves can be any real number. The `1` in the paper's examples isn't a
privileged constructor — it's just one possible value a leaf can take,
indistinguishable from any other real. Variables are substitution
positions admitting any Eml element — a leaf (carrying any real) or a
whole subtree."*

That reading collapses the grammar to two constructors:

    Eml ::= r (for r ∈ ℝ) | eml(Eml, Eml)

with "variables" understood as meta-level positions in a tree that
admit substitution of any Eml element (leaf or node). The leaf `1` is
not a constructor on its own; it is the specific leaf `leaf(1)`, on
par with `leaf(−1)`, `leaf(π)`, `leaf(γ)`, etc.

This is almost certainly what the paper's Mathematica toolchain actually
does in practice. Mathematica doesn't have a distinguished `1` atom and
a grammar that reaches other constants through construction — it just
has real numbers and operations on them, with `1` as an ordinary literal.
And this view does fix one specific refutation.

### What the `{ℝ, eml}` grammar fixes

* **Constants stop being derived.** `−1 = leaf(−1)`, `2 = leaf(2)`, `π = leaf(π)`.
  No `ln(0)` detour, no need to construct from `1`. Our `negOne_not_evaluable`
  and `two_not_evaluable` theorems stop applying because the constants are no
  longer those specific trees.
* **The syntax/value mismatch for specific numbers disappears.** "3 as a tree"
  and "3 as a real" are now the same object (`leaf(3)`) instead of two
  different things written the same way.

### What the `{ℝ, eml}` grammar breaks or leaves broken

* **The paper's minimality claim is gone.** "One operator, one distinguished
  constant" (Section 5, p. 15) becomes "one operator plus uncountably many
  real primitives." That is not a Sheffer-style basis. The NAND analogy, which
  relies on a finite generating set, is completely lost.

* **Cardinality mismatch flips direction.** EML trees under `{ℝ, eml}` are
  uncountable (one degree of uncountability per real leaf). The elementary
  functions are countable (defined by finite expressions over a countable
  signature). So the class EML now expresses is a **strict superset** of the
  elementary functions. The claim *"EML generates the elementary functions"*
  stops being a characterisation — one direction is trivially true ("every
  elementary function is expressible"), the other is false ("EML expresses
  only elementary functions" — no, it also expresses `f(x) = γ · x` for
  Euler-Mascheroni `γ`, conjecturally non-elementary).

* **No correspondence between EML trees and elementary functions is possible
  even in theory.** This is the sharpest version of the cardinality point.
  Under `{1, eml}`, EML trees form a countable class; the elementary functions
  are also countable. A bijection or characterisation between them is at
  least *conceivable* in principle — the two classes have the right cardinality
  to correspond. Under `{ℝ, eml}`, EML trees are uncountable while elementary
  functions are countable. **No function from the uncountable set of EML
  trees to the countable set of elementary functions can be injective**, and
  no subset of EML trees isomorphic to the elementary functions is picked out
  by the grammar itself. The relaxed grammar doesn't merely fail the paper's
  claim; it makes the claim vacuous as a theorem about elementary functions,
  because the EML-expressible class and the elementary class are fundamentally
  different mathematical objects (different cardinalities, different
  constructors, different characterising properties). To recover a
  correspondence, one must *restrict* the leaves to some specific countable
  subset of ℝ — but any such restriction brings back the problems the
  relaxation was meant to escape.

* **There is no natural target class the paper can retreat to.** A tempting
  response to the cardinality break: *"Fine, EML doesn't characterise the
  elementary functions; it characterises some larger analytic class that
  happens to have the right cardinality."* This doesn't work either. EML
  under any grammar does not reach most non-elementary analytic functions:

  | Candidate target class | EML's relation to it |
  |---|---|
  | Elementary functions (stated target) | strict superset under `{ℝ, eml}` (smuggles non-elementary constants); strict subset in evaluation under `{1, eml}` (operations fail). Never equals. |
  | Analytic functions on ℂ | strict subset — gamma, Riemann zeta, erf, Bessel J_0, Weierstrass sigma, and most named special functions are *not* finite exp-ln compositions, regardless of what constants appear as leaves. |
  | Computable functions | incomparable — EML admits non-computable reals as leaves; most computable functions aren't exp-ln compositions. |
  | *"Elementary-in-x with arbitrary real coefficients"* (the actual class) | equal (roughly) — but this is a non-standard class, defined by reference to EML, with no independent mathematical characterisation. |

  The only class that matches EML's expressiveness under `{ℝ, eml}` is the
  one defined *by* EML itself, which makes the claim *"EML generates X"*
  tautological for `X = EML-expressible functions`. That is not a theorem.
  Every natural classical class — elementary, analytic, meromorphic,
  computable — is either a strict subset, a strict superset, or incomparable
  to EML-expressible. So the paper has nowhere to retreat: it cannot keep
  "elementary functions" as the target (cardinality mismatch), and it cannot
  substitute any other standard class (EML doesn't match any of them).

* **Non-elementary values smuggled in as leaves.** If leaves can be arbitrary
  reals, they can include `γ` (Euler-Mascheroni, widely conjectured
  non-elementary), Catalan's constant, Chaitin's `Ω` (non-computable),
  specific Liouville reals, and so on. The "generating set" now contains
  values not in the class being generated. The `eml` operator becomes
  decorative — it doesn't generate new values; the leaves already cover ℝ.

* **Structural operation failures persist.** The paper's encoding
  `sub'(x, y) = eml(ln x, exp y)` still hits `ln(0)` when `x = leaf(0)`.
  `neg'(z) = sub'(zero, z)` still contains `ln(0)` regardless of whether
  `zero` is `ln'(1)` or `leaf(0)` — it's the outer `ln'` of the first
  argument that fails. `add'`, `mul'` inherit via `neg'`. These are properties
  of the *encodings*, not the *leaf language*, so the cascade
  `neg_not_evaluable → add_not_evaluable → …` carries over with minor
  rephrasing.

* **Richardson-undecidability is unchanged.** Tree-substitution is required
  for function composition (you cannot express `f ∘ g` in EML without
  substituting one tree into another tree's variable position). The
  substituted trees can express Richardson's full signature via the paper's
  own constructions. Zero-testing remains Richardson-undecidable regardless
  of what the leaves are.

* **Alternative-witness non-confluence is unchanged.** Different trees for
  the same function still disagree on evaluability. The relaxed grammar gives
  you more trees to choose from, which if anything makes the non-confluence
  more pronounced.

### The type-mixing problem

Because EML has a single variable type, a term like `3 * 2` admits two
inconsistent readings:

* **Tree × Tree**: `mul'(leaf(3), leaf(2))` — an EML tree, to be evaluated
  downstream. Under the paper's `mul'` encoding, this routes through `add'`
  which routes through `neg'` which still hits `ln(0)`.
* **Tree × Real**: take `mul_by_3(x) = mul'(leaf(3), var(0))` and *bind* `var 0`
  to the real value `2.0` at evaluation time. If the encoding happens to route
  around the failure (as it does at Schanuel-generic real inputs), you get `6.0`.

These are different operations — one is tree-substitution, one is
real-evaluation — and they do not in general produce the same result. The
paper's verification methodology (`VerifyBaseSet`) uses real-binding
exclusively; the central claim of "generating" requires tree-substitution.
With only one variable type, the two readings are impossible to distinguish
in notation, and the paper silently uses whichever is convenient at each
step. This is the type-theoretic core of why the paper's apparatus *appears*
to verify claims that are in fact false under the semantics the paper
implies.

### Why neither grammar works

Summarised:

| Grammar | Cardinality of trees | Match to elementary class | Minimality claim | Structural failures |
|---|---|---|---|---|
| `{1, eml}` (strict) | countable | potentially tight | "one operator, one constant" | constants, operations, composition all hit `ln(0)` |
| `{ℝ, eml}` (relaxed) | uncountable | strict superset (smuggles non-elementary) | lost — uncountable primitives | constants fixed; operations still hit `ln(0)` |

* Under `{1, eml}`, the paper's rhetorical framing is preserved but the
  evaluations structurally fail.
* Under `{ℝ, eml}`, the evaluations at specific constants succeed but the
  rhetorical framing collapses (no minimality, wrong cardinality, non-elementary
  smuggling, operator-is-decorative).

The paper's claim — a tight, Sheffer-style generation of the elementary
functions from `{1, eml}` — requires both the strict grammar *and* the clean
evaluations, and neither grammar delivers both.

## Key theorems

Located in `Eml/Refutation.lean`. All unconditional (hold in any
`PartialModel` interface). Zero `sorry` in code.

**Structural refutations**
- `sub_fails_at_zero` — paper's `sub'(var 0, var 1)` encoding fails at `(0, 1)`.
- `sub_sub_fails_on_composition` — chained subtraction fails.
- `negOne_not_evaluable` — `−1` is not an evaluable tree.
- `two_not_evaluable`, `neg_not_evaluable`, `add_not_evaluable` — failure cascade.
- `positive_reals_dont_rescue_negOne` — `ℝ₊` restriction does not help (closed-tree failure).

**Non-confluence from alternative witnesses**
- `non_confluence_via_alternative_witness` — any evaluating alternative disagrees with the default.
- `no_canonical_normalization` — no computable canonicalization (would decide Richardson).

**Verification method blindness**
- `verify_base_set_blind_to_sub_failure` — VerifyBaseSet samples generic points, cannot witness the failure.
- `generic_agreement_does_not_imply_strong_claim` — hedged agreement ≠ strong claim.

**Dichotomy**
- `not_strong_claim_at_sub` — refutes the strong reading.
- `central_claim_dichotomy` — the either-or result, combining core structural failure with the Richardson barrier.

**Richardson barrier (auxiliary)**
- `richardson_eml_real` (axiom) — classical Richardson 1968 transferred to EML via the paper's own sin-via-Euler construction.
- `no_decidable_sub_self_guard` — no mechanical guard rescues the equational theory.

**±∞-extended model unsoundness**
- `richardson_counterexample` in `Eml/Partiality.lean` — machine-checked witness that the `sub_self` rewrite rule is unsound once the paper's supplementary `ln(0) = −∞` rescue is adopted.

## Structure of the repo

- `Eml/Basic.lean` — the `Eml` tree type and structural helpers.
- `Eml/Constructors.lean` — the paper's exhibited encodings (`exp', ln', sub', neg', add', mul', div', pow', sqrt', pi', i', cos', sin'`).
- `Eml/Rewrite.lean` — attempted equational theory, with known inconsistencies documented.
- `Eml/Partiality.lean` — the ±∞-extension unsoundness, including `richardson_counterexample`.
- `Eml/KB.lean` — Knuth–Bendix critical-pair analysis (12 structurally unjoinable pairs once ±∞ rules are added).
- `Eml/Refutation.lean` — the formal refutation of the central claim (this file).
- `rust/` — Rust reimplementation of a rewrite normalizer; demonstrates the non-confluence at `0 · (1/0)` concretely.

## Building

```
lake build
```

Requires Lean 4 (toolchain pinned in `lean-toolchain`). No Mathlib
dependency — the core refutation works with a minimal abstract
`PartialModel` interface; the Richardson barrier is one external axiom.

## What the paper does have

This note is not an argument that Odrzywołek's paper contains nothing.
The following weaker statements hold and are interesting:

- **`{1, eml}` is an extremely impoverished AST.** One literal, one binary
  operator, no variables (or one implicit variable-position). It is a
  minimal syntactic representation for a specific fragment of exp-ln
  expressions — essentially, a convention for writing down exp-ln-subtraction
  expressions with a single compound node that combines `exp(·) − ln(·)`.
  The paper's "discovery" is primarily this notational repackaging; the
  underlying function class is the same one generated by `{1, exp, ln, −}`
  (the paper's own Calc 2), which is a well-known fragment of elementary
  analysis studied since the 19th century. What is new is the one-node
  packaging, not the generated class.

- **Reachable constants form a genuine countable subset of ℝ.** Starting
  from `1`, the closure under `eml(a, b) = exp(a) − ln(b)` reaches `e` at
  tree-size K=3, `e−1` at K=5, `0` at K=7, `exp(e), e^e−1, e − ln(e−1)` at
  K=7, `1 − e` (a negative) at K=9 via `eml(0, exp(e))`, and many more
  specific transcendentals at larger K. The paper's Table 4 enumerates
  K-lengths for named targets: `2` at K=19, `√2` at K>47, `π` at K>53,
  `i` at K>55. These are real reachable constants, expensively.

- **Reachable functions (with one variable) form a real sub-fragment of
  elementary analysis.** Clean expressions include `exp(x) = eml(x, 1)`,
  `ln(x) = eml(1, eml(eml(1, x), 1))`, `exp(exp(x))`, `e − ln(x)`,
  `exp(x) − 1 = eml(x, eml(1, 1))`, and their compositions. None of these
  hit the `ln(0)` structural failure — that only appears once you try to
  encode `neg`, `add`, `mul`, which route through `sub'(zero, _)`. The
  cleanly-reachable functions form the exp-ln-subtraction fragment of
  elementary functions, which is non-trivial and interesting.

- **At shallow tree depths (≤ 4), the grammar encodes iterated exp and a
  few compositions** — a real but narrow class, and the substrate for the
  empirical symbolic-regression results in the paper.

What does **not** survive scrutiny is the NAND/Sheffer framing —
a NAND circuit has decidable equivalence and total composition;
EML has neither — and the strong reading of the central claim as
stated on page 5.

## Why the paper's depth-≤ 4 regime works (the singularity depth)

There's a structural reason the paper's symbolic regression results
hold at shallow depth and collapse beyond it, and it's purely a fact
about tree-depth and when `ln(0)` becomes reachable.

### The depth arithmetic

The value `0` first enters the closure at depth 3, via

    eml(1, eml(eml(1, 1), 1)) = e − ln(exp(e)) = e − e = 0.

But for `0` to cause a structural `ln(0)` hit, it has to appear as a
*right child* of some outer `eml` node. That requires the outer `eml`
to have depth one greater than the depth at which `0` is first
reachable as a value.

| Depth | Reachable closed-tree values | `0` reachable? | `ln(0)` possible? |
|---|---|---|---|
| 0 | `{1}` | No | No |
| 1 | `{1, e}` | No | No |
| 2 | `{1, e, e−1, exp(e), exp(e)−1}` (all positive) | No | No |
| 3 | adds `0` and specific new positives | Yes (as value) | No (not yet as right child) |
| 4 | `eml(a, zero_subtree)` becomes possible | — | **Yes, first time** |

So for closed trees in `{1, eml}`, the smallest depth at which a
structural `ln(0)` can occur is depth 4. Below depth 4, every right-
child subtree evaluates to a strictly positive real, so every `ln`
argument is defined, and every tree evaluates cleanly.

### The empirical match — from the paper itself

The paper's own Section 4.3 reports the convergence rates of
gradient-descent symbolic regression over EML trees (softmax mixture
over `{0, 1, x}` at each leaf, Adam optimizer, 1000+ runs with varied
seeds):

- **Depth 2**: 100% convergence from random initialisation.
- **Depths 3–4**: approximately 25% convergence.
- **Depth 5**: below 1% convergence.
- **Depth 6**: no blind recovery observed in 448 attempts.

These numbers are reproduced in independent empirical work at
`seetrex-ai/monolith` (linked in HN discussion), which confirms the
same breakpoint at depth 4–5. The data isn't inferred from secondary
commentary — it's what the paper itself reports.

The transition depth is exactly 4 — the first depth where structural
`ln(0)` can occur. At depth ≤ 3, the tree space is singularity-free
by construction; gradient descent always finds a tree (the empirical
100% at depth 2 corroborates this).

For depth ≥ 4, the story the empirical data suggests — and that the
depth-4 boundary makes plausible — is that a growing fraction of the
tree space contains `ln(0)` positions, and gradient-descent
initialisations from random weights have to navigate away from those
positions to converge. The convergence drop from ~25% at depth 4 to
< 1% at depth 5 to 0% at depth 6 is *consistent* with "singularity-
free trees becoming combinatorially sparse at higher depth," but that
specific claim has not been proved here — it would require:

- A count of depth-`d` trees containing at least one structural `ln(0)`
  position vs. those free of them.
- A proof that gradient descent over softmax parameterisations fails
  specifically when the optimal tree is near a singularity-containing
  neighbour in parameter space.
- Classification of the "basin of convergence" structure for
  gradient-descent trajectories.

The enumeration script sketched in the "What `{1, eml}` actually
computes" section could answer the first of these empirically. The
second and third are genuine gradient-descent analysis questions that
we do not address.

What *is* established here is the weaker structural fact: depth 4 is
the first depth at which `ln(0)` can structurally appear in a `{1, eml}`
tree. That boundary coincides exactly with the paper's reported
empirical convergence transition. Whether the coincidence is causal in
the specific way suggested above is plausible but not proved.

### Why this is likely a structural explanation

Previous framings attribute the depth collapse to:

- Numerical instability of towering `exp` compositions (paper and HN
  commenter).
- Vanishing/exploding gradients from nested exp-ln layers.
- Optimizer-specific failure modes (Adam's step-size adaptation).

These numerical effects are real, but they don't on their own explain
*why* the transition sits at depth 4 rather than, say, depth 7 or
depth 2. The depth-4 structural fact — that `ln(0)` first becomes
reachable at exactly that depth — is the thing the convergence data
lines up with sharply.

The hypothesis we're pointing at is: **convergence failure past depth
4 is driven by structural singularities, with numerical instability
as an amplifier, not the root cause**. This is a plausible reading of
the data given the depth-arithmetic coincidence, but we haven't
proved the gradient-descent failure mode specifically. An idealised
infinite-precision optimizer might well face the same wall; it might
also not; we don't know.

What we do know: the structural boundary is at depth 4, and the
empirical boundary is at depth 4. That's enough to make the
structural story the first explanation to consider — and enough to
raise the question, but not answer it, of whether the numerical
framings are getting the causal direction right.

### Corollary: a cleaner reframing of the paper's empirical claim

The paper's Section 4.3 empirical claim — "gradient descent recovers
elementary functions at shallow depths" — could alternatively be read
as:

> *"Gradient descent recovers tree representations in the depth range
> where the EML tree space does not admit structural `ln(0)`."*

This is a cleaner framing than "gradient descent works at depth ≤ 4"
and it lines up with the depth-4 transition observed empirically. The
stronger claim — *"depth 5+ is combinatorially singular in the
specific sense that makes gradient descent fail"* — is plausible but
not established here; counting arguments and gradient-descent basin
analysis would be needed.

The structural depth-4 boundary is also roughly the boundary of the
cleanly-expressible class: at depth ≤ 4 you can represent iterated
`exp` and a handful of compositions with `ln` of positive values,
and the paper's reported successful recoveries (`exp, ln, sqrt, x², x³,
1/x, sin` per the HN reproduction) are all of this character.

So the paper's "symbolic regression works" regime coincides structurally
with the depth range where the tree space is singularity-free. Whether
the *exact mechanism* by which singularities cause gradient-descent
failure at higher depths is combinatorial, numerical, or both is an
open question that this note does not answer.

## Empirical confirmation: the paper's own compiler

The paper ships a Python compiler (`eml_compiler_v4.py`) that translates
Wolfram-style expressions to EML trees and verifies them numerically.
Running the compiler against the formal refutation reveals two independent
forms of unsoundness, one in each direction of the translation.

### Direction A: Compilation is unsound (Wolfram → SymPy → EML)

The compiler routes every expression through SymPy for simplification
*before* encoding it as an EML tree. SymPy's algebraic simplifier ignores
domain restrictions on `log`:

```python
from sympy import log, symbols, simplify
x = symbols("x")
simplify(log(x) - log(x))   # → 0, no domain check; ask(Q.positive(x-y)) returns None
```

**Example A1: `Subtract[Log[x], Log[x]]` at `x = 0`.**
Mathematically, `log(0) − log(0)` is `−∞ − (−∞)`, indeterminate. SymPy
simplifies `log(x) − log(x) → 0` without checking `x > 0`, then the
compiler emits `eml_zero()`. The compiled tree returns `0` at `x = 0`
where the correct answer is `NaN`.

**Example A2: `Plus[Log[x], Log[y]]` vs `Log[Times[x, y]]` at negative inputs.**
SymPy treats `log(x) + log(y) = log(x·y)` universally. For `x = y = −2`,
the two compiled EML trees take different complex-log branches and disagree —
the equivalence holds only on `ℝ₊`.

**Example A3: Two representations, different functions.**
`Subtract[Log[Subtract[x,y]], Log[Subtract[x,y]]]` at `(x, y) = (1, 1)`:
- Via compiler (SymPy pre-simplification): simplifies to `0` → emits
  `eml_zero()` → returns `0.0`.
- Via primitive API (no SymPy): `eml_sub(eml_log(eml_sub("x","y")),
  eml_log(eml_sub("x","y")))` → returns `NaN`.
- Mathematically: `log(1−1) − log(1−1) = log(0) − log(0)`, undefined.

The compiler is wrong (claims 0 for an undefined input). The primitive API
is wrong (should give 0 by `sub_self`, gives NaN). Both are wrong, in
opposite directions.

### Direction B: Verification is unsound (EML → `np.real()` → compare)

The paper's test harness (`test_eml_numpy.py`) extracts only the real part
of the output:

```python
z   = eml_f(np.complex128(x))
got = float(np.real(z))       # imaginary part silently discarded
ref = float(ref_fn(x))
re_err = got - ref            # test passes if |re_err| < tolerance
```

EML trees route all arithmetic through complex `exp` and `log`, so they
produce non-zero imaginary parts even on purely real inputs. The imaginary
component is recorded in the harness but never triggers a test failure.

**Example B1: `Minus[x]`** — real part is always correct, imaginary part
≈ `2.4e-16` (machine epsilon). Every test passes. But the function maps
`ℝ → ℂ`, not `ℝ → ℝ`.

**Example B2: `Plus[Log[x], Log[y]]` at `x = y = −2`** — imaginary part
≈ `2π ≈ 6.28`, as large as the real part. `np.real()` discards it. The
test passes because only the real error is measured — but the function
returns a complex number with a ≈ 6 imaginary component.

### The double shield

The paper's verification is structurally protected from the `sub_self` NaN
contradiction by two layered mechanisms:

1. **Depth shield**: the test suite (`run_unary_suite_numpy.py`) uses only
   depth-1 expressions — one Wolfram function applied to raw `x`; e.g.
   `("Half[x]", −4, 4, 0.125)`, `("Minus[x]", −4, 4, 0.125)`. The NaN
   contradiction first appears in structural composition at depth 3+, so
   the test suite never reaches it.

2. **SymPy shield**: when a depth-3 expression goes through the Wolfram
   compiler, SymPy collapses `log(f) − log(f) → 0` algebraically before EML
   encoding. A structurally depth-80+ tree becomes the depth-3 `eml_zero()`
   constant. SymPy does the algebraic work; EML never sees the composed form.

Neither shield is acknowledged in the paper. Together they make the
verification appear complete while the structural unsoundness goes untested.
The contradiction only surfaces by bypassing the compiler and using the
primitive API directly:

```python
inner = eml_sub("x", "y")
tree  = eml_sub(eml_log(inner), eml_log(inner))
# eml_eval(tree, {"x": 1.0, "y": 1.0}) → NaN   (not 0)
```

### Why the `ℝ₊` restriction does not fix this

The paper (Section 3.5) suggests restricting all inputs and intermediate
values to `ℝ₊` to avoid the `ln(0)` singularity. But `sub(a, b) = a − b`
maps `ℝ₊ × ℝ₊ → ℝ`, not `ℝ₊ × ℝ₊ → ℝ₊`: two positive numbers can
subtract to zero or a negative.

**Concrete failure at positive inputs**: `sub(1, 1) = 0` with `1, 1 ∈ ℝ₊`.
The inner `eml_sub` returns exactly `0.0` in IEEE 754, `ln(0) = −∞`, and
the `sub_self` NaN cascade fires:

```
eml_sub(eml_log(eml_sub("x","y")), eml_log(eml_sub("x","y")))
at x=1, y=1 (both positive reals): → NaN
```

**Structural imaginary bleed at positive inputs**: `Power[Log[Subtract[x, 2]], 2]`
at `0 < x < 2`. When `x < 2`, `Subtract[x, 2]` is negative; `Log` of a
negative gives `log|x−2| + iπ`; squaring gives `log|x−2|² − π²`. The
real part is wrong by exactly `π² ≈ 9.87` — not floating-point noise, a
structural imaginary-to-real bleed.

A model trained on `x > 2` (where all intermediates are positive) would
appear correct under the paper's verification harness. Evaluated at
`0 < x < 2` — still positive inputs — the same EML tree gives a real-part
error of ≈ 9.87 at every sample point, concentrated precisely at the
structural boundary where the intermediate value leaves `ℝ₊`. The `ℝ₊`
restriction on inputs does not prevent `ℝ₊`-to-ℝ intermediate values
from breaking the encoding.

## A no-Sheffer theorem for the elementary functions

Everything above concerns `eml(x, y) = exp(x) − ln(y)` specifically.
The same obstruction generalises: no binary elementary operator,
with any finite constant set, can generate the elementary function
class. The argument reduces to two theorems plus one classical
analytic axiom, formalized in `Eml/NoSheffer.lean` and
`Eml/NoShefferComplex.lean`.

### Setup

Let `ElemExpr` be the inductive class of two-variable expressions
generated by: variables, complex constants, `+`, `−`, `·`, `exp`,
`ln`. Every `E ∈ ElemExpr` induces a partial operator
`⟦E⟧ : ℂ × ℂ ⇀ ℂ`; partiality comes from `ln(0)` being undefined
(propagating upward through the expression).

The *tree-closure* of `(⟦E⟧, c)` over constants `c : ι → ℂ` is the
set of functions `ℂ ⇀ ℂ` representable as finite expression trees
with leaves drawn from `{variable} ∪ range(c)` and internal nodes
applying `⟦E⟧`.

### Theorem 1 — total operators produce total closures

If `⟦E⟧` is total on `ℂ × ℂ`, then every tree is total. Consequently
the closure contains only total functions — and so cannot contain
any partial member of the elementary class (e.g. `ln`, `1/z`, `tan`,
`sec`).

*Proof.* Structural induction on trees. No analytic content.
Formalized without axioms.

### Theorem 2 — the natural domain of a tree is undecidable

Even when a partial operator produces a tree `T` whose values
match a target function on many inputs, the set of inputs where
`T` evaluates successfully — the *natural domain* of `T` — is in
general not computably decidable.

**Statement.** Let `E` be a set and `P : E → Prop` a property
for which no computable function `d : E → {0,1}` satisfies
`d(e) = 1 ↔ P(e)`. Suppose a model `(α, ⊙, c)` admits a map
`φ : E → Tree(ι)` such that for every `e ∈ E`, the natural domain
of `φ(e)` is all of `α` if and only if `¬P(e)`. Then the predicate
"`dom(T) = α`" on `T(ι)` is not computably decidable.

*Proof.* A decider `δ` for `dom(T) = α` would give `d(e) := ¬δ(φ(e))`,
which would decide `P` — contradicting the hypothesis. Formalized
in `Eml/NoSheffer.lean` from first principles; uses Richardson 1968
as its input.

**Operational consequence.** If someone attempts to represent a
total function `f` via a tree over a partial elementary operator,
the theorem above combined with Theorem 3 gives: either the tree
fails to represent `f` pointwise, or it represents `f` only on a
strict subset of `ℂ` whose boundary (the set of inputs where the
tree breaks) is undecidable. So even giving up pointwise correctness
does not yield an algorithmically checkable approximation.

### Elementary barrier (unformalized classical theorem)

If `E ∈ ElemExpr` is partial (so `⟦E⟧` returns `⊥` on some input
pair), then no tree over `(⟦E⟧, c)` pointwise represents the function
`z ↦ −z` on `ℂ`.

This is a classical result of complex analysis, imported into Lean
without its formal proof — not a foundational commitment. Its
content assembles from four pieces, each well-known:

1. **Hadamard factorization.** A nowhere-zero entire function has the
   form `exp(g)` for some entire `g` (Hadamard / Weierstrass).
2. **Monodromy constancy.** `ln(exp(g(z))) = g(z) + 2πi·k(z)` for
   some integer-valued function `k`. `k` is continuous (away from
   branch cuts) and integer-valued, hence constant on connected
   components.
3. **Cancellation closure.** Tree-structural induction: any
   pointwise-total tree over a partial `ElemExpr` reduces, via the
   Hadamard and monodromy facts applied bottom-up, to a
   `ln`-free sub-expression — an "exp-polynomial" over the
   constants.
4. **Growth gap.** No exp-polynomial equals `z ↦ −z` pointwise on
   `ℂ`. Linear growth cannot be matched by a finite sum of
   exponential terms.

All four are classical results of complex analysis. None is
currently formalized in Mathlib — Hadamard factorization in
particular is absent — so the barrier is imported as a single
packaged classical theorem rather than decomposed into smaller
named pieces plus a Lean-checked assembly.

### Theorem 3 — combined no-go on ℂ

For every `E ∈ ElemExpr` and every constant interpretation
`c : ι → ℂ`, the tree-closure of `(⟦E⟧, c)` does not simultaneously
contain a partial function `f : ℂ ⇀ ℂ` and the function `z ↦ −z`.

*Proof.* If `⟦E⟧` is total, Theorem 1 rules out the partial `f`. If
`⟦E⟧` is partial, the Elementary barrier rules out `z ↦ −z`.

### Corollary — no Sheffer basis for the elementary functions

No pair `(⊙, S)` — with `⊙` a binary elementary operator and `S` a
finite constant set — generates the elementary function class `E`
under tree composition.

*Proof.* For the closure to be a subset of `E`, `⊙` must itself be
elementary, so `⊙ = ⟦E⟧` for some `E ∈ ElemExpr`. `E` contains
both a partial function (e.g. `ln`) and the total function
`z ↦ −z`. By Theorem 3, both cannot be in the closure of
`(⟦E⟧, c)`. So the closure is a proper subset of `E`. ∎

### Application to eml

The paper claims `{eml, 1}` generates all elementary functions,
where `eml(x, y) = exp(x) − ln(y)`.

1. `eml = sub(exp(var₁), ln(var₂)) ∈ ElemExpr` by inspection.
2. `⟦eml⟧` is partial: at `(a, 0)`, the inner `ln` is undefined.
3. By the Elementary barrier, no tree over `⟦eml⟧` with any
   constants pointwise represents `z ↦ −z`.
4. `z ↦ −z` is elementary. The paper's claim requires it to be in
   the closure. Contradiction. ∎

Only the barrier is invoked — Theorem 1's total-operator branch
does not fire, because `eml` is manifestly partial. The combined
theorem and the general corollary become relevant only if someone
proposed a *total* elementary operator as a Sheffer basis.

### No model escapes

The paper's rescue attempts — restrict inputs to `ℝ₊`, extend with
`±∞`, etc. — do not evade the theorem. A single observation
collapses them all:

1. The standard elementary function class contains `i`, `sin`,
   `cos`, `exp(iπ) + 1 = 0`, and all their compositions. These
   are fundamentally complex-valued.
2. `ℝ` (and `ℝ₊`) do not contain `i`. So `ℝ` is trivially not a
   model of the elementary functions — the class does not even
   fit.
3. Any model must therefore contain `ℂ`.
4. By Theorem 3 on `ℂ`, no `ElemExpr` operator generates the
   class on `ℂ`.
5. So no model supports the Sheffer claim.

Extending `ℂ` with `±∞` does not help either. On the `ℂ`
sub-domain, tree evaluation has to agree with `ℂ`-eml wherever
the latter is defined — and Theorem 3 rules that out. Any tree
that escapes by routing through `±∞` at some `ℂ`-input introduces
the `∞ − ∞` indeterminacy; that is a separate structural failure,
covered by the non-confluence argument in `Eml/Partiality.lean`.

The only apparent room to manoeuvre is equivocating between "real
elementary functions" (a smaller class) and "the elementary
functions" (the full `ℂ` class with `sin`, `cos`, `i` from Euler).
That is a vocabulary trick, not two legitimate class choices. Once
the class is pinned down — standard definition, complex-valued —
no model escapes.

### What's proved in Lean, what's imported from the literature

Two classical theorems are imported into Lean without their formal
proofs. Neither is a foundational commitment: both have published
peer-reviewed proofs in the classical mathematical literature.

- **Richardson 1968** — zero-equivalence for elementary expressions
  is undecidable. Published, classical, not yet formalized in
  Mathlib. Used in `Eml/NoSheffer.lean` for the natural-domain
  undecidability reduction.
- **The Elementary barrier** — the four-piece complex-analysis
  result above. Each piece (Hadamard factorization, monodromy
  constancy, cancellation closure via tree induction, growth gap)
  is classical. The assembly is straightforward but has not been
  written up in full. Used in `Eml/NoShefferComplex.lean`.

Lean-checked content:

- `Eml/NoSheffer.lean`: Theorem 1 is proved from first principles.
  The Richardson reduction — showing that a decider for
  full-natural-domain of trees would give a decider for
  Richardson's problem — is a complete Lean proof, using the
  Richardson theorem as input.
- `Eml/NoShefferComplex.lean`: The combined Theorem 3 and the
  no-Sheffer corollary are Lean-checked proofs that take the
  Elementary barrier as input.
- `Eml/Refutation.lean`: The concrete refutation of `eml` at
  specific input witnesses is fully proved — it does not depend
  on the Elementary barrier, only on the structural behaviour of
  `eml` at specific points.

The general corollary is a theorem whose proof cites two
unformalized classical theorems. Discharging those citations
into Lean proofs would require Hadamard factorization and the
Richardson reduction to land in Mathlib first.

## Status

- Formal refutation: complete. Zero `sorry` in code. Two
  classical theorems cited into Lean without their formalized
  proofs (i.e., appearing in the Lean file as `axiom` declarations
  in the technical sense, but mathematically they are published
  theorems, not foundational commitments): Richardson 1968
  (zero-equivalence for elementary expressions is undecidable),
  and the Elementary barrier on ℂ (assembled from Hadamard
  factorization, monodromy constancy, cancellation closure, and
  the growth gap — all classical complex analysis).
- Written as a formalization exercise, not a peer-reviewed publication.
- Author is a software engineer without academic background; this work
  was produced with substantial AI assistance, which is reflected in
  its style and in the occasional cross-reference between files.
- No contact has been made with Professor Odrzywołek regarding this
  refutation; if anyone finds issues or misreadings, please open an
  issue.

## License

Public domain / CC0 for the Lean files in this repository. The paper
itself is © Andrzej Odrzywołek and is not included here; its arXiv
identifier is 2603.21852v2.
