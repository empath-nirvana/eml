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

- `exp` and `ln` combined into a single binary node yield a clean
  context-free grammar `S → 1 | eml(S, S)` that is expressive enough
  for dense-agreement encoding of the elementary functions. This is
  a fact about `exp` and `ln` known since the 17th–19th century,
  restated syntactically.
- At shallow tree depths (≤ 4), the grammar encodes iterated exp
  and a few compositions — a real but narrow class, and the
  substrate for the empirical symbolic-regression results in the
  paper.

What does **not** survive scrutiny is the NAND/Sheffer framing —
a NAND circuit has decidable equivalence and total composition;
EML has neither — and the strong reading of the central claim as
stated on page 5.

## Status

- Formal refutation: complete. Zero `sorry` in code. One external axiom
  (classical Richardson 1968).
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
