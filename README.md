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
