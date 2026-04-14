# EML: A Single-Operator Tree Algebra for Calculus

## The Idea

Define a single binary operation on trees:

    eml(x, y) = exp(x) - ln(y)

with one constant terminal, `1`. That's it. From this alone -- one
binary node, one leaf -- you can derive:

    exp(z)  = eml(z, 1)
    ln(z)   = eml(1, eml(eml(1, z), 1))
    x - y   = eml(ln(x), exp(y))
    -z      = 0 - z           where 0 = ln(1)
    x + y   = x - (-y)
    1/z     = exp(-ln(z))
    x * y   = exp(ln(x) + ln(y))
    x / y   = x * (1/y)

Every elementary function -- polynomials, rational functions,
exponentials, logarithms, trigonometric and hyperbolic functions,
their inverses and compositions -- is a finite binary tree over this
single operation. The constant e is eml(1,1). The imaginary unit
i = exp(ln(-1)/2). Euler's formula gives cos and sin.

## What's Proved

The Lean 4 formalization establishes the following results, all fully
machine-checked with no axioms, no sorry, and no dependency on Mathlib.

### Structure

- **Full binary tree property.** Every EML tree satisfies
  leaves = nodes + 1.

### Differentiation

Differentiation is a total, computable function on trees, defined by
a single recursive rule:

    D(eml(A, B)) = exp(A) * D(A) - D(B) * (1/B)

with D(1) = 0 and D(x) = 1 (or 0 for other variables). This is the
chain rule applied to eml(x,y) = exp(x) - ln(y), but it requires no
semantic interpretation -- it's pure tree surgery.

The following are proved as rewrite chains (directed, no evaluation):

- **Constants vanish.** D(t) rewrites to zero for any variable-free
  tree t. This covers e, pi, i, and all EML-encoded constants.
  The proof uses only three algebraic rules: multiplication absorbs
  zero, and subtraction self-cancels. No exp, ln, or evaluation
  is involved anywhere.

- **D(exp(x)) = exp(x).** The derivative of the exponential is
  itself, proved as a three-step rewrite chain.

- **D(ln(x)) = 1/x.** The logarithmic derivative, derived from
  the generalized chain rule.

### Chain Rules

Both chain rules are proved for arbitrary subtrees (not just variables):

- **Exponential chain rule.** D(exp(f)) rewrites to exp(f) * D(f).
- **Logarithmic chain rule.** D(ln(f)) rewrites to D(f) * (1/f).
  This proof chains through five intermediate forms and uses
  multiplicative cancellation as the key step.

### Linearity

Full linearity of differentiation, derived from the chain rules:

- **Sum rule.** D(a + b) rewrites to D(a) + D(b).
- **Difference rule.** D(a - b) rewrites to D(a) - D(b).
- **Negation rule.** D(-f) rewrites to -D(f).
- **Constant multiple rule.** D(c * f) rewrites to c * D(f) when
  c has no variables. The proof requires a non-trivial algebraic
  cancellation involving six ln-level rearrangement steps.

### Algebra

Key algebraic identities proved as rewrite chains:

- a + (-a) rewrites to 0
- a * (1/a) rewrites to 1
- (a * b) * (1/a) rewrites to b (left cancellation, 8 steps)
- a * ((1/a) * b) rewrites to b (right-inverse cancellation)
- Commutativity and associativity of addition (as rewrite rules)
- Commutativity of multiplication (derived from add_comm on logarithms)
- Associativity of multiplication (via joinability -- both sides
  reduce to a common form)

## What's Not Here (Yet)

### Semantic interpretation

The rewrite system is purely syntactic. To connect EML trees to actual
real-valued functions, one needs to interpret them in a model -- the
obvious candidate being (R, +, *, exp, ln). This requires Mathlib and
raises a subtlety: the EML tree algebra treats exp and ln as total,
mutually inverse operations, while on R (and C), ln is partial and
multi-valued. The tree algebra is thus a richer structure than the
reals: the free algebra where exp and ln work everywhere without
domain restrictions.

### Confluence

The rewrite system is not proved confluent. This means some equalities
can only be established by joinability (both sides reduce to a common
form) rather than by directed rewriting. Multiplication associativity
is an example. Confluence is a natural next target.

### Liouville's theorem

Partial progress exists toward a tree-algebraic Liouville theorem
(elementary antiderivatives have the form v0 + sum of ci * ln(vi)).
The structural machinery is in place -- Liouville forms, their
derivative structure, synthesis from derivative decompositions -- but
the main theorem requires tower-height induction and axioms about
the algebraic independence of exp and ln, which remain open.

## Why This Matters

1. **Minimality.** One operation, one constant, no integers, no
   recursion schemes. The algebra is as small as a nontrivial
   calculus can be.

2. **Computability.** Differentiation is a total computable function.
   There is no "undefined" -- every tree has a derivative, and the
   derivative is another tree.

3. **Self-contained proofs.** The key results (constants have zero
   derivative, exp is its own derivative, chain rules, linearity)
   are proved using only tree rewrites. No real analysis, no
   limits, no epsilon-delta.

4. **The algebra itself.** EML trees with their equational theory
   form the free exponential-logarithmic algebra -- the universal
   structure where exp and ln are total mutual inverses. The reals
   and complex numbers are quotients of this structure, not the
   other way around. This reversal of the usual perspective --
   trees first, reals as a specialization -- may be of independent
   algebraic interest.
