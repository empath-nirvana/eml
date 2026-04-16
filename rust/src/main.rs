//! EML Tree Algebra in Rust
//!
//! All elementary functions from a single operator: eml(x, y) = exp(x) - ln(y)
//! Based on Odrzywołek, "All elementary functions from a single operator" (2026)
//!
//! The Lean 4 version proves the rules sound. This one uses them.

use std::fmt;

// ── Core type ──────────────────────────────────────────────────────────────

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Eml {
    One,
    Var(u32),
    Node(Box<Eml>, Box<Eml>),
    /// -∞: the value of ln(0). Absorbs under addition with finite values.
    NegInf,
    /// +∞: the value of 1/0 = exp(+∞). Equal to neg(-∞).
    PosInf,
}

impl Eml {
    fn node(l: Eml, r: Eml) -> Self {
        Eml::Node(Box::new(l), Box::new(r))
    }

    // ── Derived constructors ───────────────────────────────────────────
    // Each encodes a named operation via eml(x, y) = exp(x) - ln(y)

    fn exp(z: Eml) -> Self { Self::node(z, Eml::One) }

    fn ln(z: Eml) -> Self {
        Self::node(Eml::One, Self::exp(Self::node(Eml::One, z)))
    }

    fn zero() -> Self { Self::ln(Eml::One) }

    fn sub(x: Eml, y: Eml) -> Self {
        Self::node(Self::ln(x), Self::exp(y))
    }

    fn neg(z: Eml) -> Self { Self::sub(Self::zero(), z) }
    fn add(x: Eml, y: Eml) -> Self { Self::sub(x, Self::neg(y)) }
    fn inv(z: Eml) -> Self { Self::exp(Self::neg(Self::ln(z))) }

    fn mul(x: Eml, y: Eml) -> Self {
        Self::exp(Self::add(Self::ln(x), Self::ln(y)))
    }

    fn div(x: Eml, y: Eml) -> Self { Self::mul(x, Self::inv(y)) }

    fn of_nat(n: u32) -> Self {
        match n {
            0 => Self::zero(),
            n => Self::add(Eml::One, Self::of_nat(n - 1)),
        }
    }

    // ── Trig constructors ─────────────────────────────────────────────
    // Built from Euler's formula. No new primitives — just tree templates.

    fn neg_one() -> Self { Self::sub(Self::zero(), Eml::One) }
    fn two() -> Self { Self::sub(Eml::One, Self::neg_one()) }
    fn half() -> Self { Self::inv(Self::two()) }
    fn sqr(z: Eml) -> Self { Self::mul(z.clone(), z) }
    fn sqrt(z: Eml) -> Self { Self::exp(Self::mul(Self::ln(z), Self::half())) }

    /// π = √(-(ln(-1))²)
    fn pi() -> Self { Self::sqrt(Self::neg(Self::sqr(Self::ln(Self::neg_one())))) }

    /// i = -ln(-1)/π
    fn i_unit() -> Self { Self::neg(Self::div(Self::ln(Self::neg_one()), Self::pi())) }

    /// cos(z) = (exp(iz) + exp(-iz)) / 2
    fn cos(z: Eml) -> Self {
        let iz = Self::mul(Self::i_unit(), z);
        Self::mul(Self::add(Self::exp(iz.clone()), Self::exp(Self::neg(iz))), Self::half())
    }

    /// sin(z) = (exp(iz) - exp(-iz)) / (2i)
    fn sin(z: Eml) -> Self {
        let iz = Self::mul(Self::i_unit(), z);
        Self::div(Self::sub(Self::exp(iz.clone()), Self::exp(Self::neg(iz))),
                  Self::mul(Self::two(), Self::i_unit()))
    }

    /// tan(z) = sin(z) / cos(z)
    fn tan(z: Eml) -> Self { Self::div(Self::sin(z.clone()), Self::cos(z)) }

    // ── Pattern recognizers ────────────────────────────────────────────

    fn as_exp(&self) -> Option<&Eml> {
        match self {
            Eml::Node(z, r) if **r == Eml::One => Some(z),
            _ => None,
        }
    }

    fn as_ln(&self) -> Option<&Eml> {
        // ln(z) = node(1, node(node(1, z), 1))
        if let Eml::Node(l, inner) = self {
            if **l != Eml::One { return None; }
            if let Eml::Node(inner_l, inner_r) = &**inner {
                if **inner_r != Eml::One { return None; }
                if let Eml::Node(ll, z) = &**inner_l {
                    if **ll == Eml::One { return Some(z); }
                }
            }
        }
        None
    }

    fn as_sub(&self) -> Option<(&Eml, &Eml)> {
        if let Eml::Node(l, r) = self {
            if let (Some(x), Some(y)) = (l.as_ln(), r.as_exp()) {
                return Some((x, y));
            }
        }
        None
    }

    fn is_zero(&self) -> bool {
        self.as_ln().is_some_and(|z| *z == Eml::One)
    }

    fn as_neg(&self) -> Option<&Eml> {
        let (x, y) = self.as_sub()?;
        if x.is_zero() { Some(y) } else { None }
    }

    fn as_add(&self) -> Option<(&Eml, &Eml)> {
        let (x, neg_y) = self.as_sub()?;
        let y = neg_y.as_neg()?;
        Some((x, y))
    }

    fn as_inv(&self) -> Option<&Eml> {
        self.as_exp()?.as_neg()?.as_ln()
    }

    fn as_mul(&self) -> Option<(&Eml, &Eml)> {
        let (a, b) = self.as_exp()?.as_add()?;
        Some((a.as_ln()?, b.as_ln()?))
    }

    fn as_nat(&self) -> Option<u32> {
        if self.is_zero() { return Some(0); }
        if *self == Eml::One { return Some(1); }
        let (a, b) = self.as_add()?;
        if *a == Eml::One { b.as_nat().map(|n| n + 1) } else { None }
    }

    // ── Structural helpers ─────────────────────────────────────────────

    fn leaves(&self) -> usize {
        match self {
            Eml::One | Eml::Var(_) | Eml::NegInf | Eml::PosInf => 1,
            Eml::Node(l, r) => l.leaves() + r.leaves(),
        }
    }

    fn subst(&self, x: u32, s: &Eml) -> Eml {
        match self {
            Eml::One | Eml::NegInf | Eml::PosInf => self.clone(),
            Eml::Var(n) => if *n == x { s.clone() } else { self.clone() },
            Eml::Node(l, r) => Eml::node(l.subst(x, s), r.subst(x, s)),
        }
    }

    // ── Structural helpers ─────────────────────────────────────────────

    fn has_var(&self, x: u32) -> bool {
        match self {
            Eml::One | Eml::NegInf | Eml::PosInf => false,
            Eml::Var(n) => *n == x,
            Eml::Node(l, r) => l.has_var(x) || r.has_var(x),
        }
    }

    fn is_ground(&self) -> bool {
        match self {
            Eml::One | Eml::NegInf | Eml::PosInf => true,
            Eml::Var(_) => false,
            Eml::Node(l, r) => l.is_ground() && r.is_ground(),
        }
    }

    fn is_infinite(&self) -> bool {
        matches!(self, Eml::NegInf | Eml::PosInf)
    }


    // ── Differentiation ────────────────────────────────────────────────
    // Derived-form diff: pattern-match on mul, inv, add, neg, sub, exp, ln
    // and apply standard chain rules. Produces clean intermediate trees
    // without eml(1,...) residues. has_var short-circuits ground subtrees.

    fn diff(&self, x: u32) -> Eml {
        if !self.has_var(x) { return Eml::zero(); }
        match self {
            Eml::One => Eml::zero(),
            Eml::Var(n) => if *n == x { Eml::One } else { Eml::zero() },
            _ => {
                // Most derived forms first (same priority order as normalize)
                // D(f·g) = f·D(g) + g·D(f)
                if let Some((f, g)) = self.as_mul() {
                    let (f, g) = (f.clone(), g.clone());
                    return Eml::add(Eml::mul(f.clone(), g.diff(x)),
                                    Eml::mul(g.clone(), f.diff(x)));
                }
                // D(1/f) = -D(f)·(1/f)²
                if let Some(f) = self.as_inv() {
                    let f = f.clone();
                    let df = f.diff(x);
                    return Eml::neg(Eml::mul(df,
                        Eml::mul(Eml::inv(f.clone()), Eml::inv(f))));
                }
                // D(f+g) = D(f) + D(g)
                if let Some((f, g)) = self.as_add() {
                    return Eml::add(f.diff(x), g.diff(x));
                }
                // D(-f) = -D(f)
                if let Some(f) = self.as_neg() {
                    return Eml::neg(f.diff(x));
                }
                // D(f-g) = D(f) - D(g)
                if let Some((f, g)) = self.as_sub() {
                    return Eml::sub(f.diff(x), g.diff(x));
                }
                // D(exp(f)) = exp(f)·D(f)
                if let Some(f) = self.as_exp() {
                    let f = f.clone();
                    return Eml::mul(self.clone(), f.diff(x));
                }
                // D(ln(f)) = D(f)/f
                if let Some(f) = self.as_ln() {
                    let f = f.clone();
                    return Eml::mul(f.diff(x), Eml::inv(f));
                }
                // Raw fallback — should rarely fire on well-formed trees
                if let Eml::Node(a, b) = self {
                    let da = a.diff(x);
                    let db = b.diff(x);
                    Eml::sub(
                        Eml::mul(Eml::exp(a.as_ref().clone()), da),
                        Eml::mul(db, Eml::inv(b.as_ref().clone())),
                    )
                } else {
                    Eml::zero()
                }
            }
        }
    }
}

// ── Display ────────────────────────────────────────────────────────────────

/// Collect additive terms from a flattened sum (for display).
fn collect_display_terms(t: &Eml) -> Vec<&Eml> {
    let mut out = Vec::new();
    fn go<'a>(t: &'a Eml, out: &mut Vec<&'a Eml>) {
        if let Some((a, b)) = t.as_add() {
            go(a, out);
            go(b, out);
        } else {
            out.push(t);
        }
    }
    go(t, &mut out);
    out
}

/// Try to display as a product: exp(sum of ln-terms) → a * b * ...
fn fmt_maybe_product(inner: &Eml, f: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
    let terms = collect_display_terms(inner);
    if terms.len() < 2 { return None; }
    let factors: Vec<&Eml> = terms.iter().filter_map(|t| t.as_ln()).collect();
    if factors.len() != terms.len() { return None; }
    Some((|| {
        write!(f, "(")?;
        for (i, fac) in factors.iter().enumerate() {
            if i > 0 { write!(f, " * ")?; }
            write!(f, "{fac}")?;
        }
        write!(f, ")")
    })())
}

impl fmt::Display for Eml {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(n) = self.as_nat() { return write!(f, "{n}"); }
        // mul (2-factor, via as_mul pattern)
        if let Some((a, b)) = self.as_mul() { return write!(f, "({a} * {b})"); }
        // multi-factor product: exp(ln(a) + ln(b) + ...)
        if let Some(inner) = self.as_exp() {
            if let Some(result) = fmt_maybe_product(inner, f) { return result; }
        }
        if let Some(z) = self.as_inv() { return write!(f, "(1/{z})"); }
        if let Some((a, b)) = self.as_add() { return write!(f, "({a} + {b})"); }
        if let Some(z) = self.as_neg() { return write!(f, "(-{z})"); }
        if let Some((a, b)) = self.as_sub() { return write!(f, "({a} - {b})"); }
        if self.is_zero() { return write!(f, "0"); }
        if let Some(z) = self.as_ln() { return write!(f, "ln({z})"); }
        if let Some(z) = self.as_exp() { return write!(f, "exp({z})"); }
        match self {
            Eml::One => write!(f, "1"),
            Eml::NegInf => write!(f, "-∞"),
            Eml::PosInf => write!(f, "+∞"),
            Eml::Var(n) => {
                const NAMES: [&str; 4] = ["x", "y", "z", "w"];
                if (*n as usize) < NAMES.len() {
                    write!(f, "{}", NAMES[*n as usize])
                } else {
                    write!(f, "x{n}")
                }
            }
            Eml::Node(l, r) => write!(f, "eml({l}, {r})"),
        }
    }
}

impl fmt::Debug for Eml {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Eml::One => write!(f, "𝟏"),
            Eml::NegInf => write!(f, "-∞"),
            Eml::PosInf => write!(f, "+∞"),
            Eml::Var(n) => write!(f, "v{n}"),
            Eml::Node(l, r) => write!(f, "⟨{l:?}|{r:?}⟩"),
        }
    }
}

// ── Normalization ──────────────────────────────────────────────────────────
//
// Top-down: recognize the highest-level derived form, normalize its semantic
// children, then apply rules and rebuild. This preserves encoding structure
// (unlike bottom-up raw-node normalization, which breaks derived patterns).
//
// Layers:
//   1. Transcendental TRS: exp/ln cancellation, identities
//   2. AC addition: flatten, cancel inverses, sort
//   3. Polynomial: distribute multiplication over addition

/// Normalize an EML tree to canonical form.
pub fn normalize(t: &Eml) -> Eml {
    // Most derived forms first — mul/inv before add/neg/sub before ln/exp
    if let Some((a, b)) = t.as_mul() {
        return norm_mul(normalize(a), normalize(b));
    }
    if let Some(z) = t.as_inv() {
        return norm_inv(normalize(z));
    }
    if let Some((a, b)) = t.as_add() {
        return norm_add(normalize(a), normalize(b));
    }
    if let Some(z) = t.as_neg() {
        return norm_neg(normalize(z));
    }
    if let Some((a, b)) = t.as_sub() {
        return norm_sub(normalize(a), normalize(b));
    }
    if let Some(z) = t.as_ln() {
        return norm_ln(normalize(z));
    }
    if let Some(z) = t.as_exp() {
        return norm_exp(normalize(z));
    }
    match t {
        Eml::One | Eml::NegInf | Eml::PosInf => t.clone(),
        Eml::Var(n) => Eml::Var(*n),
        Eml::Node(l, r) => {
            // Genuine raw eml(l, r) — not any derived form
            let l = normalize(l);
            let r = normalize(r);
            reduce_raw(Eml::node(l, r))
        }
    }
}

// ── Normalization rules ────────────────────────────────────────────────────
// Each norm_* assumes its arguments are already normalized.

fn norm_exp(z: Eml) -> Eml {
    // exp(-∞) → 0
    if z == Eml::NegInf { return Eml::zero(); }
    // exp(+∞) → +∞
    if z == Eml::PosInf { return Eml::PosInf; }
    // exp(ln(w)) → w
    if let Some(w) = z.as_ln() { return w.clone(); }
    // exp(0) → 1
    if z.is_zero() { return Eml::One; }
    // exp(neg(ln(w))) = inv(w) — redirect to norm_inv
    if let Some(inner) = z.as_neg() {
        if let Some(w) = inner.as_ln() {
            return norm_inv(w.clone());
        }
    }
    Eml::exp(z)
}

fn norm_ln(z: Eml) -> Eml {
    // ln(0) → -∞
    if z.is_zero() { return Eml::NegInf; }
    // ln(+∞) → +∞
    if z == Eml::PosInf { return Eml::PosInf; }
    // ln(-∞) → +∞ (ln(|x|) → ∞ as x → -∞; branch cut gives +∞ + iπ but we keep +∞)
    if z == Eml::NegInf { return Eml::PosInf; }
    // ln(exp(w)) → w
    if let Some(w) = z.as_exp() { return w.clone(); }
    // ln(1) → 0
    if z == Eml::One { return Eml::zero(); }
    // Only decompose non-ground terms — ground constants stay atomic under ln,
    // preventing structural divergence (e.g. ln(i) stays opaque so inv(i)*i cancels).
    if !z.is_ground() {
        // ln(a*b) → ln(a) + ln(b)
        if let Some((a, b)) = z.as_mul() {
            return norm_add(norm_ln(a.clone()), norm_ln(b.clone()));
        }
        // ln(neg(x)) → ln(x) + ln(-1)
        if let Some(inner) = z.as_neg() {
            return norm_add(norm_ln(inner.clone()), Eml::ln(Eml::neg_one()));
        }
    }
    Eml::ln(z)
}

fn norm_sub(a: Eml, b: Eml) -> Eml {
    if b.is_zero() { return a; }          // a - 0 → a
    if a.is_zero() { return norm_neg(b); } // 0 - b → -b
    // a - a → 0, but NOT for ±∞ (∞ - ∞ is indeterminate)
    if a == b && !a.is_infinite() { return Eml::zero(); }
    // Always reduce sub to add(a, neg(b)) — ensures norm_mul can distribute
    norm_add(a, norm_neg(b))
}

fn norm_neg(z: Eml) -> Eml {
    if z == Eml::NegInf { return Eml::PosInf; }         // -(-∞) → +∞
    if z == Eml::PosInf { return Eml::NegInf; }         // -(+∞) → -∞
    if let Some(w) = z.as_neg() { return w.clone(); }   // -(-w) → w
    if z.is_zero() { return Eml::zero(); }               // -(0) → 0
    // neg(a + b) → neg(a) + neg(b) — distribute, so AC cancellation sees atoms
    if let Some((a, b)) = z.as_add() {
        return norm_add(norm_neg(a.clone()), norm_neg(b.clone()));
    }
    Eml::neg(z)
}

fn norm_add(a: Eml, b: Eml) -> Eml {
    // ±∞ absorption (but -∞ + ∞ is indeterminate — leave unreduced)
    if a == Eml::NegInf {
        return if b == Eml::PosInf { Eml::add(a, b) } else { Eml::NegInf };
    }
    if a == Eml::PosInf {
        return if b == Eml::NegInf { Eml::add(a, b) } else { Eml::PosInf };
    }
    if b == Eml::NegInf {
        return if a == Eml::PosInf { Eml::add(a, b) } else { Eml::NegInf };
    }
    if b == Eml::PosInf {
        return if a == Eml::NegInf { Eml::add(a, b) } else { Eml::PosInf };
    }
    if a.is_zero() { return b; }
    if b.is_zero() { return a; }
    if let Some(inner) = b.as_neg() {
        if *inner == a { return Eml::zero(); }
    }
    if let Some(inner) = a.as_neg() {
        if *inner == b { return Eml::zero(); }
    }
    ac_normalize_add(a, b)
}

fn norm_mul(a: Eml, b: Eml) -> Eml {
    if a == Eml::One { return b; }
    if b == Eml::One { return a; }
    // 0 * x → 0, but 0 * ±∞ is indeterminate (0 · ∞)
    if a.is_zero() && !b.is_infinite() { return Eml::zero(); }
    if b.is_zero() && !a.is_infinite() { return Eml::zero(); }
    // Integer multiplication — before distribution so 2*3 → 6 directly
    if let (Some(na), Some(nb)) = (a.as_nat(), b.as_nat()) {
        return normalize(&Eml::of_nat(na * nb));
    }
    // neg(a) * b → neg(a * b)  — sound by ExpField.neg_mul
    if let Some(inner) = a.as_neg() {
        return norm_neg(norm_mul(inner.clone(), b));
    }
    // a * neg(b) → neg(a * b)  — sound by ExpField.mul_neg
    if let Some(inner) = b.as_neg() {
        return norm_neg(norm_mul(a, inner.clone()));
    }
    // Distribute: a * (c + d) → a*c + a*d
    // Gate: only for non-ground products. Ground products stay in multiplicative
    // form exp(ln(a)+ln(b)) so inv(2i)*i can cancel ln(i) terms via AC.
    if !(a.is_ground() && b.is_ground()) {
        if let Some((c, d)) = b.as_add() {
            let (c, d) = (c.clone(), d.clone());
            return norm_add(norm_mul(a.clone(), c), norm_mul(a, d));
        }
        if let Some((c, d)) = a.as_add() {
            let (c, d) = (c.clone(), d.clone());
            return norm_add(norm_mul(c, b.clone()), norm_mul(d, b));
        }
    }
    // Build canonical mul: exp(ln(a) + ln(b)) with normalized encoding
    let ln_a = norm_ln(a);
    let ln_b = norm_ln(b);
    let sum = norm_add(ln_a, ln_b);
    norm_exp(sum)
}

fn norm_inv(z: Eml) -> Eml {
    // inv(0) → +∞  (1/0 = ∞)
    if z.is_zero() { return Eml::PosInf; }
    // inv(±∞) → 0
    if z.is_infinite() { return Eml::zero(); }
    if let Some(w) = z.as_inv() { return w.clone(); }  // inv(inv(w)) → w
    if z == Eml::One { return Eml::One; }
    // inv(neg(a)) → neg(inv(a))  — sound by ExpField.inv_def + neg_mul
    if let Some(inner) = z.as_neg() {
        return norm_neg(norm_inv(inner.clone()));
    }
    // inv(a*b) → inv(a)*inv(b) — sound by ExpField.inv_mul_distrib
    if let Some((a, b)) = z.as_mul() {
        return norm_mul(norm_inv(a.clone()), norm_inv(b.clone()));
    }
    // Build exp(neg(ln(z))) with normalized inner parts.
    // Use Eml::exp (raw) instead of norm_exp to avoid cycle:
    // norm_exp would see exp(neg(ln(w))) and call back into norm_inv.
    let ln_z = norm_ln(z);
    let neg_ln_z = norm_neg(ln_z);
    Eml::exp(neg_ln_z)
}

fn reduce_raw(t: Eml) -> Eml {
    if let Eml::Node(ref l, ref r) = t {
        // KB: node(ln(ln(z)), z) → 0
        if let Some(inner) = l.as_ln() {
            if let Some(z) = inner.as_ln() {
                if *z == **r { return Eml::zero(); }
            }
        }
        // KB: node(z, exp(exp(z))) → 0
        if let Some(inner) = r.as_exp() {
            if let Some(z) = inner.as_exp() {
                if *z == **l { return Eml::zero(); }
            }
        }
    }
    t
}

// ── AC normalization for addition ──────────────────────────────────────────

fn flatten_add(t: &Eml, out: &mut Vec<Eml>) {
    if let Some((a, b)) = t.as_add() {
        flatten_add(a, out);
        flatten_add(b, out);
    } else {
        out.push(t.clone());
    }
}

fn build_sum(terms: &[Eml]) -> Eml {
    match terms.len() {
        0 => Eml::zero(),
        1 => terms[0].clone(),
        _ => Eml::add(terms[0].clone(), build_sum(&terms[1..])),
    }
}

fn ac_normalize_add(a: Eml, b: Eml) -> Eml {
    let mut terms = Vec::new();
    flatten_add(&a, &mut terms);
    flatten_add(&b, &mut terms);
    terms.retain(|t| !t.is_zero());

    // If any term is ±∞, the whole sum absorbs to that infinity
    // (unless both +∞ and -∞ are present — indeterminate)
    let has_neg_inf = terms.iter().any(|t| *t == Eml::NegInf);
    let has_pos_inf = terms.iter().any(|t| *t == Eml::PosInf);
    if has_neg_inf && has_pos_inf {
        return Eml::add(Eml::NegInf, Eml::PosInf); // indeterminate
    }
    if has_neg_inf { return Eml::NegInf; }
    if has_pos_inf { return Eml::PosInf; }

    // Cancel inverse pairs: a + (-a) → remove both
    let mut cancelled = vec![false; terms.len()];
    for i in 0..terms.len() {
        if cancelled[i] { continue; }
        for j in (i + 1)..terms.len() {
            if cancelled[j] { continue; }
            let pair = match terms[j].as_neg() {
                Some(inner) if *inner == terms[i] => true,
                _ => matches!(terms[i].as_neg(), Some(inner) if *inner == terms[j]),
            };
            if pair {
                cancelled[i] = true;
                cancelled[j] = true;
                break;
            }
        }
    }
    let mut terms: Vec<Eml> = terms.into_iter()
        .enumerate()
        .filter(|(i, _)| !cancelled[*i])
        .map(|(_, t)| t)
        .collect();

    terms.sort();

    // Collect ground like terms: n copies of ground t → norm_mul(n, t)
    // Safe: ground*ground distribution is gated, so norm_mul won't re-expand.
    let mut collected: Vec<Eml> = Vec::new();
    let mut i = 0;
    while i < terms.len() {
        // Skip One and neg(One) — mul(n, One) = n = sum of Ones, causing a loop.
        let skip = terms[i] == Eml::One
            || terms[i].as_neg().is_some_and(|inner| *inner == Eml::One);
        if terms[i].is_ground() && !skip {
            let mut count = 1usize;
            while i + count < terms.len() && terms[i + count] == terms[i] {
                count += 1;
            }
            if count > 1 {
                let combined = norm_mul(normalize(&Eml::of_nat(count as u32)), terms[i].clone());
                if !combined.is_zero() {
                    collected.push(combined);
                }
            } else {
                collected.push(terms[i].clone());
            }
            i += count;
        } else {
            collected.push(terms[i].clone());
            i += 1;
        }
    }
    // ── Combine non-ground exp duplicates with rational denominators ──
    // n copies of exp(neg(ln(n)) + rest) → exp(rest)
    // Sound by: n · exp(A) = exp(ln(n) + A), and ln(n) + neg(ln(n)) = 0.
    // Handles sqrt(x)^2 = x, cbrt(x)^3 = x, x^(p/q) patterns.
    // Bypasses norm_mul (which would distribute back into sum form).
    {
        let mut changed = false;
        let mut new_collected: Vec<Eml> = Vec::new();
        let mut i = 0;
        while i < collected.len() {
            if !collected[i].is_ground() {
                if let Some(a) = collected[i].as_exp() {
                    let mut inner = Vec::new();
                    flatten_add(a, &mut inner);
                    let denom = inner.iter().enumerate().find_map(|(idx, t)| {
                        let n = t.as_neg()?.as_ln()?.as_nat()?;
                        if n >= 2 { Some((idx, n as usize)) } else { None }
                    });
                    if let Some((neg_ln_idx, n)) = denom {
                        let mut count = 1usize;
                        while i + count < collected.len()
                            && collected[i + count] == collected[i]
                        {
                            count += 1;
                        }
                        let batches = count / n;
                        let remainder = count % n;
                        if batches > 0 {
                            let rest: Vec<Eml> = inner.iter().enumerate()
                                .filter(|(j, _)| *j != neg_ln_idx)
                                .map(|(_, t)| t.clone())
                                .collect();
                            let simplified = norm_exp(build_sum(&rest));
                            for _ in 0..batches {
                                new_collected.push(simplified.clone());
                            }
                            for _ in 0..remainder {
                                new_collected.push(collected[i].clone());
                            }
                            i += count;
                            changed = true;
                            continue;
                        }
                    }
                }
            }
            new_collected.push(collected[i].clone());
            i += 1;
        }
        collected = new_collected;
        if changed {
            // Re-run inverse pair cancellation for newly exposed pairs
            collected.sort();
            let mut cancelled3 = vec![false; collected.len()];
            for i in 0..collected.len() {
                if cancelled3[i] { continue; }
                for j in (i + 1)..collected.len() {
                    if cancelled3[j] { continue; }
                    let pair = match collected[j].as_neg() {
                        Some(inner) if *inner == collected[i] => true,
                        _ => matches!(collected[i].as_neg(), Some(inner) if *inner == collected[j]),
                    };
                    if pair {
                        cancelled3[i] = true;
                        cancelled3[j] = true;
                        break;
                    }
                }
            }
            collected = collected.into_iter()
                .enumerate()
                .filter(|(i, _)| !cancelled3[*i])
                .map(|(_, t)| t)
                .collect();
        }
    }
    // Conditional ln(neg(exp)) decomposition: when neg(ln(neg(exp(A)))) and A
    // both appear, decompose ln(neg(exp(A))) = A + ln(-1) to enable cancellation.
    // Sound by ln(mul(-1, exp(A))) = ln(-1) + ln(exp(A)) = ln(-1) + A.
    // Only fires when A is present — avoids changing representations elsewhere.
    let mut expanded = false;
    for i in 0..collected.len() {
        // Match neg(ln(neg(exp(A))))
        let a = (|| {
            let inner_ln = collected[i].as_neg()?;
            let inner_neg_exp = inner_ln.as_ln()?;
            let inner_exp = inner_neg_exp.as_neg()?;
            inner_exp.as_exp()
        })();
        if let Some(a) = a {
            if collected.iter().enumerate().any(|(j, t)| j != i && *t == *a) {
                // Replace neg(ln(neg(exp(A)))) with neg(A) + neg(ln(-1))
                collected[i] = norm_neg(a.clone());
                collected.push(norm_neg(Eml::ln(Eml::neg_one())));
                expanded = true;
            }
        }
    }
    if expanded {
        // Re-run full AC normalization to cancel the newly exposed terms
        collected.sort();
        collected.retain(|t| !t.is_zero());
        // Cancel inverse pairs again
        let mut cancelled2 = vec![false; collected.len()];
        for i in 0..collected.len() {
            if cancelled2[i] { continue; }
            for j in (i + 1)..collected.len() {
                if cancelled2[j] { continue; }
                let pair = match collected[j].as_neg() {
                    Some(inner) if *inner == collected[i] => true,
                    _ => matches!(collected[i].as_neg(), Some(inner) if *inner == collected[j]),
                };
                if pair {
                    cancelled2[i] = true;
                    cancelled2[j] = true;
                    break;
                }
            }
        }
        collected = collected.into_iter()
            .enumerate()
            .filter(|(i, _)| !cancelled2[*i])
            .map(|(_, t)| t)
            .collect();
    }

    collected.sort();
    build_sum(&collected)
}

// ── Exact ground evaluation: Gaussian rationals Q(i) ──────────────────────
//
// Every ground trig coefficient is a rational function of i where i² = -1.
// We precompute normalize(i_unit()) as a tree, then ground_eval recognizes
// it as the symbolic value i and does exact Q(i) arithmetic.
//
// This handles i/2 = -1/(2i), i+1/i = 0, D(cos) = -sin, etc. without
// any floating-point approximation.

/// Exact rational number (always reduced, den > 0).
#[derive(Clone, Copy, Debug)]
struct Rat { n: i64, d: i64 }

impl Rat {
    const ZERO: Rat = Rat { n: 0, d: 1 };
    const ONE: Rat = Rat { n: 1, d: 1 };

    fn new(n: i64, d: i64) -> Self {
        if d == 0 { panic!("Rat: zero denominator"); }
        if n == 0 { return Self::ZERO; }
        let g = gcd(n.unsigned_abs(), d.unsigned_abs()) as i64;
        let sign = if d < 0 { -1 } else { 1 };
        Rat { n: sign * n / g, d: sign * d / g }
    }

    fn is_zero(self) -> bool { self.n == 0 }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

impl PartialEq for Rat {
    fn eq(&self, other: &Self) -> bool { self.n == other.n && self.d == other.d }
}
impl Eq for Rat {}

impl std::ops::Add for Rat {
    type Output = Rat;
    fn add(self, rhs: Rat) -> Rat {
        Rat::new(self.n * rhs.d + rhs.n * self.d, self.d * rhs.d)
    }
}

impl std::ops::Sub for Rat {
    type Output = Rat;
    fn sub(self, rhs: Rat) -> Rat {
        Rat::new(self.n * rhs.d - rhs.n * self.d, self.d * rhs.d)
    }
}

impl std::ops::Mul for Rat {
    type Output = Rat;
    fn mul(self, rhs: Rat) -> Rat {
        Rat::new(self.n * rhs.n, self.d * rhs.d)
    }
}

impl std::ops::Neg for Rat {
    type Output = Rat;
    fn neg(self) -> Rat { Rat { n: -self.n, d: self.d } }
}

/// Gaussian rational: a + bi, a,b ∈ Q.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct QI { re: Rat, im: Rat }

impl QI {
    const ZERO: QI = QI { re: Rat::ZERO, im: Rat::ZERO };
    const ONE: QI = QI { re: Rat::ONE, im: Rat::ZERO };
    const I: QI = QI { re: Rat::ZERO, im: Rat::ONE };

    fn is_zero(self) -> bool { self.re.is_zero() && self.im.is_zero() }

    fn inv(self) -> Option<QI> {
        // 1/(a+bi) = (a-bi)/(a²+b²)
        let denom = self.re * self.re + self.im * self.im;
        if denom.is_zero() { return None; }
        Some(QI { re: Rat::new(self.re.n * denom.d, self.re.d * denom.n * denom.d / denom.d),
                  im: Rat::new(-self.im.n * denom.d, self.im.d * denom.n * denom.d / denom.d) })
    }
}

impl QI {
    // Cleaner inv using the formula directly
    fn inverse(self) -> Option<QI> {
        // (a+bi)^-1 = (a-bi)/(a²+b²)
        let norm_sq = self.re * self.re + self.im * self.im;
        if norm_sq.is_zero() { return None; }
        Some(QI {
            re: Rat::new(self.re.n * norm_sq.d, self.re.d * norm_sq.n),
            im: Rat::new(-self.im.n * norm_sq.d, self.im.d * norm_sq.n),
        })
    }
}

impl std::ops::Add for QI {
    type Output = QI;
    fn add(self, rhs: QI) -> QI {
        QI { re: self.re + rhs.re, im: self.im + rhs.im }
    }
}

impl std::ops::Sub for QI {
    type Output = QI;
    fn sub(self, rhs: QI) -> QI {
        QI { re: self.re - rhs.re, im: self.im - rhs.im }
    }
}

impl std::ops::Mul for QI {
    type Output = QI;
    fn mul(self, rhs: QI) -> QI {
        // (a+bi)(c+di) = (ac-bd) + (ad+bc)i
        QI {
            re: self.re * rhs.re - self.im * rhs.im,
            im: self.re * rhs.im + self.im * rhs.re,
        }
    }
}

impl std::ops::Neg for QI {
    type Output = QI;
    fn neg(self) -> QI { QI { re: -self.re, im: -self.im } }
}

impl fmt::Display for QI {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.im.is_zero() {
            write!(f, "{}/{}", self.re.n, self.re.d)
        } else if self.re.is_zero() {
            write!(f, "{}/{}·i", self.im.n, self.im.d)
        } else {
            write!(f, "{}/{}+{}/{}·i", self.re.n, self.re.d, self.im.n, self.im.d)
        }
    }
}

/// Precomputed normalized trees for ground evaluation.
struct GroundCtx {
    i_tree: Eml,   // normalize(i)
    l_tree: Eml,   // normalize(ln(-1)) — the fundamental transcendental L
    p_tree: Eml,   // exponent of π: the tree P such that exp(P) = π
}

impl GroundCtx {
    fn new() -> Self {
        let i_tree = normalize(&Eml::i_unit());
        let l_tree = normalize(&Eml::ln(Eml::neg_one()));
        let pi_tree = normalize(&Eml::pi());
        // π = exp(P), so P = the exponent inside pi_tree
        let p_tree = pi_tree.as_exp()
            .expect("normalized pi should be exp(...)").clone();
        GroundCtx { i_tree, l_tree, p_tree }
    }
}

/// Evaluate a normalized ground EML tree to Q(i).
///
/// Strategy: parse the exp/ln product encoding, recognizing L = ln(-1)
/// and P = ln(π) as symbolic factors. Use L = -iπ to collapse them.
fn ground_eval(t: &Eml, ctx: &GroundCtx) -> Option<QI> {
    // Known constant trees
    if *t == ctx.i_tree { return Some(QI::I); }
    if *t == Eml::One { return Some(QI::ONE); }
    if t.is_zero() { return Some(QI::ZERO); }
    if let Some(n) = t.as_nat() {
        return Some(QI { re: Rat::new(n as i64, 1), im: Rat::ZERO });
    }

    // Arithmetic forms (derived structure)
    if let Some(z) = t.as_neg() {
        return Some(-ground_eval(z, ctx)?);
    }
    if let Some((a, b)) = t.as_add() {
        return Some(ground_eval(a, ctx)? + ground_eval(b, ctx)?);
    }
    if let Some((a, b)) = t.as_sub() {
        return Some(ground_eval(a, ctx)? - ground_eval(b, ctx)?);
    }
    // as_mul/as_inv handled via the exp-product path below

    // exp(sum_of_terms) = multi-factor product
    // This is the main path: products are encoded as exp(ln(a) + ln(b) + ...)
    if let Some(exponent) = t.as_exp() {
        return eval_exp_product(exponent, ctx);
    }

    None
}

/// Expand compound AC terms so that eval_exp_product can handle them.
/// Applies three rules recursively:
///   neg(X)       → flip sign, recurse on X
///   ln(neg(X))   → ln(-1) + ln(X)  (log of negative)
///   ln(exp(K))   → K               (log-exp cancellation)
///   n·X = exp(ln(n)+ln(X)) → X+X+...+X  (uncollect integer multiples)
fn expand_ac_term(term: &Eml, negated: bool, out: &mut Vec<Eml>) {
    // neg(X): flip sign and recurse
    if let Some(inner) = term.as_neg() {
        expand_ac_term(inner, !negated, out);
        return;
    }

    if let Some(x) = term.as_ln() {
        // ln(neg(X)) → ln(-1) + ln(X), but NOT for ln(-1) itself (base case)
        if let Some(inner) = x.as_neg() {
            if *inner != Eml::One {
                let ln_neg1 = Eml::ln(Eml::neg_one());
                expand_ac_term(&ln_neg1, negated, out);
                expand_ac_term(&Eml::ln(inner.clone()), negated, out);
                return;
            }
        }
        // ln(exp(K)) → flatten K
        if let Some(k) = x.as_exp() {
            let mut k_terms = Vec::new();
            flatten_add(k, &mut k_terms);
            for t in &k_terms {
                expand_ac_term(t, negated, out);
            }
            return;
        }
    }

    // exp(ln(n) + ln(Y)) = n·Y → Y repeated n times in the outer sum
    // (because exp(n·Y) = exp(Y + Y + ... + Y))
    if let Some(k) = term.as_exp() {
        let mut k_terms = Vec::new();
        flatten_add(k, &mut k_terms);
        if k_terms.len() == 2 {
            for (i, j) in [(0usize, 1usize), (1, 0)] {
                if let Some(x) = k_terms[i].as_ln() {
                    if let Some(n) = x.as_nat() {
                        if n > 0 && n <= 20 {
                            // k_terms[j] = ln(Y), extract Y
                            if let Some(base_val) = k_terms[j].as_ln() {
                                for _ in 0..n {
                                    expand_ac_term(base_val, negated, out);
                                }
                                return;
                            }
                        }
                    }
                }
            }
        }
    }

    // Default: keep as-is
    if negated {
        out.push(Eml::neg(term.clone()));
    } else {
        out.push(term.clone());
    }
}

/// Evaluate exp(exponent) where exponent is a (possibly multi-term) AC sum.
/// Each term in the sum contributes a multiplicative factor:
///   ln(X) → factor X
///   neg(ln(X)) → factor 1/X
///   P_tree → factor π (since exp(P) = π)
///   neg(P_tree) → factor 1/π
///
/// Uses the relation L = -iπ to cancel transcendentals:
///   L^k · π^j = (-i)^k · π^(k+j).  Result is in Q(i) iff k+j = 0.
fn eval_exp_product(exponent: &Eml, ctx: &GroundCtx) -> Option<QI> {
    // Handle the trivial case: exp(0) = 1
    if exponent.is_zero() { return Some(QI::ONE); }

    // Flatten the additive sum, expand compound terms, cancel inverses
    let mut raw_terms = Vec::new();
    flatten_add(exponent, &mut raw_terms);
    let mut expanded = Vec::new();
    for t in &raw_terms {
        expand_ac_term(t, false, &mut expanded);
    }
    // Cancel t + neg(t) pairs
    let mut pos: Vec<Eml> = Vec::new();
    let mut neg: Vec<Eml> = Vec::new();
    for t in expanded {
        if let Some(inner) = t.as_neg() {
            neg.push(inner.clone());
        } else {
            pos.push(t);
        }
    }
    let mut terms = Vec::new();
    for p in pos {
        if let Some(idx) = neg.iter().position(|n| *n == p) {
            neg.remove(idx);
        } else {
            terms.push(p);
        }
    }
    for n in neg {
        terms.push(Eml::neg(n));
    }

    // If it's a single ln term: exp(ln(X)) = X
    if terms.len() == 1 {
        if let Some(x) = terms[0].as_ln() {
            return ground_eval(x, ctx);
        }
        if let Some(inner) = terms[0].as_neg() {
            if let Some(x) = inner.as_ln() {
                return ground_eval(x, ctx)?.inverse();
            }
        }
    }

    let mut qi_acc = QI::ONE;
    let mut l_power: i32 = 0;
    let mut pi_power: i32 = 0;

    for term in &terms {
        // P_tree (= ln(π)): exp(P) = π
        if *term == ctx.p_tree {
            pi_power += 1;
            continue;
        }

        // neg(P_tree): exp(-P) = 1/π
        if let Some(inner) = term.as_neg() {
            if *inner == ctx.p_tree {
                pi_power -= 1;
                continue;
            }
            // neg(ln(X)) → factor 1/X
            if let Some(x) = inner.as_ln() {
                if *x == ctx.l_tree {
                    l_power -= 1;
                } else {
                    qi_acc = qi_acc * ground_eval(x, ctx)?.inverse()?;
                }
                continue;
            }
            // Unrecognized neg(something)
            return None;
        }

        // ln(X) → factor X
        if let Some(x) = term.as_ln() {
            if *x == ctx.l_tree {
                l_power += 1;
            } else {
                qi_acc = qi_acc * ground_eval(x, ctx)?;
            }
            continue;
        }

        // Unrecognized term in the product
        return None;
    }

    // Collapse L and π using L = -iπ:
    // L^k · π^j = (-i)^k · π^(k+j)
    // For the result to be in Q(i), need k + j = 0.
    if l_power + pi_power != 0 { return None; }

    // (-i)^k mod 4
    let neg_i_pow = match l_power.rem_euclid(4) {
        0 => QI::ONE,
        1 => -QI::I,
        2 => -QI::ONE,
        3 => QI::I,
        _ => unreachable!(),
    };

    Some(qi_acc * neg_i_pow)
}

/// Compare two normalized ground trees for semantic equality via Q(i).
fn ground_eq(a: &Eml, b: &Eml, ctx: &GroundCtx) -> bool {
    if a == b { return true; }
    match (ground_eval(a, ctx), ground_eval(b, ctx)) {
        (Some(va), Some(vb)) => va == vb,
        _ => false,
    }
}

/// Signature of an additive term: (sorted non-ground exponent parts, Q(i) coefficient).
/// For a term ±exp(ground_terms + var_terms), the coefficient absorbs the sign.
#[derive(Debug)]
struct TermSig {
    var_terms: Vec<Eml>,
    coeff: QI,
}

/// Decompose a normalized term into its signature.
/// Handles: exp(sum), neg(exp(sum)), ground constants, neg(ground).
fn term_sig(t: &Eml, ctx: &GroundCtx) -> Option<TermSig> {
    // Ground term with no var component
    if t.is_ground() {
        let coeff = ground_eval(t, ctx)?;
        return Some(TermSig { var_terms: vec![], coeff });
    }

    // exp(E) or neg(exp(E))
    let (exp_inner, is_neg) = if let Some(e) = t.as_exp() {
        (e, false)
    } else if let Some(inner) = t.as_neg() {
        if let Some(e) = inner.as_exp() {
            (e, true)
        } else {
            return None;
        }
    } else {
        return None;
    };

    let mut terms = Vec::new();
    flatten_add(exp_inner, &mut terms);

    let mut ground = Vec::new();
    let mut var = Vec::new();
    for term in terms {
        if term.is_ground() {
            ground.push(term);
        } else {
            var.push(term);
        }
    }
    var.sort();

    let mut coeff = if ground.is_empty() {
        QI::ONE
    } else {
        let ground_sum = build_sum(&ground);
        eval_exp_product(&ground_sum, ctx)?
    };
    if is_neg { coeff = -coeff; }

    Some(TermSig { var_terms: var, coeff })
}

/// Semantic equality: two normalized trees are equal if their additive terms
/// match pairwise (modulo AC reordering) with equal Q(i) coefficients and
/// identical non-ground structure.
/// Group term signatures by var_terms and sum their Q(i) coefficients.
/// Returns sorted groups with non-zero coefficients.
fn group_sigs(sigs: Vec<TermSig>) -> Vec<TermSig> {
    use std::collections::BTreeMap;
    let mut groups: BTreeMap<Vec<Eml>, QI> = BTreeMap::new();
    for sig in sigs {
        let entry = groups.entry(sig.var_terms).or_insert(QI::ZERO);
        *entry = *entry + sig.coeff;
    }
    let mut result: Vec<TermSig> = groups
        .into_iter()
        .filter(|(_, coeff)| *coeff != QI::ZERO)
        .map(|(var_terms, coeff)| TermSig { var_terms, coeff })
        .collect();
    result.sort_by(|x, y| x.var_terms.cmp(&y.var_terms));
    result
}

fn semantic_eq(a: &Eml, b: &Eml, ctx: &GroundCtx) -> bool {
    if a == b { return true; }
    if a.is_ground() && b.is_ground() {
        return ground_eq(a, b, ctx);
    }

    // Flatten both sides into additive terms
    let mut a_flat = Vec::new();
    let mut b_flat = Vec::new();
    flatten_add(a, &mut a_flat);
    flatten_add(b, &mut b_flat);

    // Compute signatures for all terms
    let a_sigs: Vec<_> = a_flat.iter().filter_map(|t| term_sig(t, ctx)).collect();
    let b_sigs: Vec<_> = b_flat.iter().filter_map(|t| term_sig(t, ctx)).collect();

    if a_sigs.len() != a_flat.len() || b_sigs.len() != b_flat.len() {
        return false;
    }

    // Group by var_terms and sum coefficients, then compare
    let a_grouped = group_sigs(a_sigs);
    let b_grouped = group_sigs(b_sigs);

    a_grouped.len() == b_grouped.len()
        && a_grouped.iter().zip(b_grouped.iter()).all(|(a, b)| {
            a.var_terms == b.var_terms && a.coeff == b.coeff
        })
}

// ── Demo ───────────────────────────────────────────────────────────────────

fn main() {
    let x = Eml::Var(0);
    let y = Eml::Var(1);

    println!("=== EML Tree Algebra ===\n");

    println!("--- Tree sizes ---");
    println!("  1       = {:>2} leaves", Eml::One.leaves());
    println!("  exp(x)  = {:>2} leaves", Eml::exp(x.clone()).leaves());
    println!("  ln(x)   = {:>2} leaves", Eml::ln(x.clone()).leaves());
    println!("  x + y   = {:>2} leaves", Eml::add(x.clone(), y.clone()).leaves());
    println!("  x * y   = {:>2} leaves", Eml::mul(x.clone(), y.clone()).leaves());
    println!();

    println!("--- Cancellation ---");
    let tests: Vec<(&str, Eml)> = vec![
        ("exp(ln(x))",   Eml::exp(Eml::ln(x.clone()))),
        ("ln(exp(x))",   Eml::ln(Eml::exp(x.clone()))),
        ("x - x",        Eml::sub(x.clone(), x.clone())),
        ("x + 0",        Eml::add(x.clone(), Eml::zero())),
        ("-(-x)",         Eml::neg(Eml::neg(x.clone()))),
        ("inv(inv(x))",  Eml::inv(Eml::inv(x.clone()))),
        ("1 * x",        Eml::mul(Eml::One, x.clone())),
        ("x * 1",        Eml::mul(x.clone(), Eml::One)),
        ("x * 0",        Eml::mul(x.clone(), Eml::zero())),
        ("0 * x",        Eml::mul(Eml::zero(), x.clone())),
        ("exp(0)",       Eml::exp(Eml::zero())),
        ("ln(1)",        Eml::ln(Eml::One)),
    ];
    for (name, term) in &tests {
        println!("  {name:20} = {}", normalize(&term));
    }
    println!();

    println!("--- Arithmetic ---");
    for (a, b) in [(2, 3), (3, 4), (5, 5), (0, 7)] {
        let sum = Eml::add(Eml::of_nat(a), Eml::of_nat(b));
        println!("  {a} + {b} = {}", normalize(&sum));
    }
    for (a, b) in [(2, 3), (3, 4), (1, 7), (0, 5)] {
        let prod = Eml::mul(Eml::of_nat(a), Eml::of_nat(b));
        println!("  {a} * {b} = {}", normalize(&prod));
    }
    println!();

    println!("--- Distributivity ---");
    let dist = Eml::mul(x.clone(), Eml::add(y.clone(), Eml::Var(2)));
    println!("  x*(y+z)      = {}", normalize(&dist));
    let expand = Eml::mul(
        Eml::add(x.clone(), Eml::One),
        Eml::add(x.clone(), Eml::One),
    );
    println!("  (x+1)*(x+1)  = {}", normalize(&expand));
    println!();

    println!("--- Differentiation ---");
    println!("  D(exp(x))  = {}", normalize(&Eml::exp(x.clone()).diff(0)));
    println!("  D(ln(x))   = {}", normalize(&Eml::ln(x.clone()).diff(0)));
    let x_sq = Eml::mul(x.clone(), x.clone());
    let dx_sq = normalize(&x_sq.diff(0));
    println!("  D(x^2)     = {}", dx_sq);
    let at3 = dx_sq.subst(0, &Eml::of_nat(3));
    println!("  D(x^2)|x=3 = {}", normalize(&at3));
    println!();

    println!("--- Homomorphisms ---");
    println!("  ln(x*y) = {}", normalize(&Eml::ln(Eml::mul(x.clone(), y.clone()))));
    println!();

    println!("--- Equality decision ---");
    let check = |name: &str, a: &Eml, b: &Eml| {
        let na = normalize(a);
        let nb = normalize(b);
        println!("  {name:30} {}", if na == nb { "YES" } else { "NO" });
    };
    check("2*3 == 6?",
        &Eml::mul(Eml::of_nat(2), Eml::of_nat(3)),
        &Eml::of_nat(6));
    check("x*(y+z) == x*y + x*z?",
        &Eml::mul(x.clone(), Eml::add(y.clone(), Eml::Var(2))),
        &Eml::add(Eml::mul(x.clone(), y.clone()), Eml::mul(x.clone(), Eml::Var(2))));
    check("x+(-x) == 0?",
        &Eml::add(x.clone(), Eml::neg(x.clone())),
        &Eml::zero());
    check("exp(ln(x)) == x?",
        &Eml::exp(Eml::ln(x.clone())),
        &x);
    check("ln(x*y) == ln(x)+ln(y)?",
        &Eml::ln(Eml::mul(x.clone(), y.clone())),
        &Eml::add(Eml::ln(x.clone()), Eml::ln(y.clone())));
    check("(x+1)^2 == x^2+2x+1?",
        &Eml::mul(Eml::add(x.clone(), Eml::One), Eml::add(x.clone(), Eml::One)),
        &Eml::add(Eml::add(Eml::mul(x.clone(), x.clone()),
                  Eml::add(x.clone(), x.clone())), Eml::One));
    check("x*(y*z) == (x*y)*z?",
        &Eml::mul(x.clone(), Eml::mul(y.clone(), Eml::Var(2))),
        &Eml::mul(Eml::mul(x.clone(), y.clone()), Eml::Var(2)));

    println!("--- Trigonometric functions ---");
    println!("  sin(x) = {}", Eml::sin(x.clone()));
    println!("  cos(x) = {}", Eml::cos(x.clone()));
    println!("  sin(x): {} leaves", Eml::sin(x.clone()).leaves());
    println!("  cos(x): {} leaves", Eml::cos(x.clone()).leaves());
    println!();

    println!("--- Trig diagnostics ---");
    let i = Eml::i_unit();
    let inv2i = Eml::inv(Eml::mul(Eml::two(), i.clone()));
    let inv2 = Eml::inv(Eml::two());
    let inv2i_i = Eml::mul(inv2i.clone(), i.clone());
    println!("  inv(2i)*i          = {}", normalize(&inv2i_i));
    println!("  inv(2)             = {}", normalize(&inv2));
    println!("  inv(2i)*i == 1/2?  {}", if normalize(&inv2i_i) == normalize(&inv2) { "YES" } else { "NO" });
    let i_sq = Eml::mul(i.clone(), i.clone());
    println!("  i^2                = {}", normalize(&i_sq));
    println!("  i^2 == -1?         {}", if normalize(&i_sq) == normalize(&Eml::neg_one()) { "YES" } else { "NO" });
    println!();

    println!("--- Trig differentiation ---");
    let d_sin = normalize(&Eml::sin(x.clone()).diff(0));
    let n_cos = normalize(&Eml::cos(x.clone()));
    println!("  D(sin(x))          = {d_sin}");
    println!("  cos(x)             = {n_cos}");
    println!("  D(sin(x)) == cos?  {}", if d_sin == n_cos { "YES" } else { "NO" });

    let d_cos = normalize(&Eml::cos(x.clone()).diff(0));
    let n_neg_sin = normalize(&Eml::neg(Eml::sin(x.clone())));
    println!("  D(cos(x))          = {d_cos}");
    println!("  -sin(x)            = {n_neg_sin}");
    println!("  D(cos(x)) == -sin? {}", if d_cos == n_neg_sin { "YES" } else { "NO" });
    println!();

    println!("--- Euler's identity ---");
    let euler = Eml::exp(Eml::mul(Eml::i_unit(), Eml::pi()));
    let n_euler = normalize(&euler);
    let n_neg1 = normalize(&Eml::neg_one());
    println!("  exp(iπ)            = {n_euler}");
    println!("  -1                 = {n_neg1}");
    println!("  exp(iπ) == -1?     {}", if n_euler == n_neg1 { "YES" } else { "NO" });
    println!();

    println!("--- Coefficient check ---");
    // D(cos) has coefficient i/2, -sin has coefficient -1/(2i)
    // These should be equal when i²=-1
    let i_half = Eml::mul(i.clone(), Eml::half());
    let neg_inv_2i = Eml::neg(Eml::inv(Eml::mul(Eml::two(), i.clone())));
    println!("  i/2               = {}", normalize(&i_half));
    println!("  -1/(2i)           = {}", normalize(&neg_inv_2i));
    println!("  i/2 == -1/(2i)?   {}", if normalize(&i_half) == normalize(&neg_inv_2i) { "YES" } else { "NO" });
    println!("  i/2 [debug]       = {:?}", normalize(&i_half));
    println!("  -1/(2i) [debug]   = {:?}", normalize(&neg_inv_2i));
    println!("  i [debug]         = {:?}", normalize(&i));
    // Also check: i + 1/i = 0 (equivalent to i²=-1)
    let i_plus_inv_i = Eml::add(i.clone(), Eml::inv(i.clone()));
    println!("  i + 1/i           = {}", normalize(&i_plus_inv_i));
    println!("  i + 1/i == 0?     {}", if normalize(&i_plus_inv_i) == normalize(&Eml::zero()) { "YES" } else { "NO" });
    println!("  i+1/i [debug]     = {:?}", normalize(&i_plus_inv_i));
    println!();

    println!("--- L2 feasibility checks ---");
    // Does sqrt(x)^2 = x?  (critical for π² = -(ln(-1))²)
    let ln_neg1 = Eml::ln(Eml::neg_one());
    let neg_sq_ln = Eml::neg(Eml::sqr(ln_neg1.clone()));
    let pi_sq = Eml::sqr(Eml::pi());
    println!("  π²                  = {}", normalize(&pi_sq));
    println!("  -(ln(-1))²          = {}", normalize(&neg_sq_ln));
    println!("  π² == -(ln(-1))²?   {}", if normalize(&pi_sq) == normalize(&neg_sq_ln) { "YES" } else { "NO" });
    // Does 2*(X*half) = X?  (critical step in like-term collection)
    let big_x = Eml::ln(Eml::of_nat(7)); // arbitrary test value
    let two_x_half = Eml::mul(Eml::two(), Eml::mul(big_x.clone(), Eml::half()));
    println!("  2*(ln7 * ½)         = {}", normalize(&two_x_half));
    println!("  ln(7)               = {}", normalize(&big_x));
    println!("  2*(ln7*½) == ln7?   {}", if normalize(&two_x_half) == normalize(&big_x) { "YES" } else { "NO" });
    // Does a/(-a) = -1?
    let a = Eml::sqr(ln_neg1.clone());
    let a_over_neg_a = Eml::div(a.clone(), Eml::neg(a.clone()));
    println!("  a/(-a)              = {}", normalize(&a_over_neg_a));
    println!("  a/(-a) == -1?       {}", if normalize(&a_over_neg_a) == normalize(&Eml::neg_one()) { "YES" } else { "NO" });
    println!();

    println!("--- Ground evaluator (Q(i)) ---");
    let ctx = GroundCtx::new();
    let gcheck = |name: &str, t: &Eml| {
        let nt = normalize(t);
        match ground_eval(&nt, &ctx) {
            Some(v) => println!("  {name:25} = {v}"),
            None => println!("  {name:25} = ???"),
        }
    };
    gcheck("i", &Eml::i_unit());
    gcheck("-1", &Eml::neg_one());
    gcheck("2", &Eml::of_nat(2));
    gcheck("1/2", &Eml::half());
    gcheck("i^2", &Eml::mul(Eml::i_unit(), Eml::i_unit()));
    gcheck("i/2", &i_half);
    gcheck("-1/(2i)", &neg_inv_2i);
    gcheck("i + 1/i", &i_plus_inv_i);
    let geq = |name: &str, a: &Eml, b: &Eml| {
        let na = normalize(a);
        let nb = normalize(b);
        println!("  {name:25} {}", if ground_eq(&na, &nb, &ctx) { "YES" } else { "NO" });
    };
    geq("i/2 == -1/(2i)?", &i_half, &neg_inv_2i);
    geq("i + 1/i == 0?", &i_plus_inv_i, &Eml::zero());
    let d_cos_n = normalize(&Eml::cos(Eml::Var(0)).diff(0));
    let neg_sin_n = normalize(&Eml::neg(Eml::sin(Eml::Var(0))));
    println!("  D(cos(x)) norm          = {d_cos_n}");
    println!("  -sin(x) norm            = {neg_sin_n}");
    geq("D(cos(x)) == -sin(x)?",
        &Eml::cos(Eml::Var(0)).diff(0),
        &Eml::neg(Eml::sin(Eml::Var(0))));

    println!("\n--- Semantic equality (Q(i) coefficients) ---");
    let seq = |name: &str, a: &Eml, b: &Eml| {
        let na = normalize(a);
        let nb = normalize(b);
        println!("  {name:30} {}", if semantic_eq(&na, &nb, &ctx) { "YES" } else { "NO" });
    };
    seq("D(cos(x)) == -sin(x)?",
        &Eml::cos(Eml::Var(0)).diff(0),
        &Eml::neg(Eml::sin(Eml::Var(0))));
    seq("D(sin(x)) == cos(x)?",
        &Eml::sin(Eml::Var(0)).diff(0),
        &Eml::cos(Eml::Var(0)));
    seq("exp(iπ) == -1?",
        &Eml::exp(Eml::mul(Eml::i_unit(), Eml::pi())),
        &Eml::neg_one());
    seq("i/2 == -1/(2i)?", &i_half, &neg_inv_2i);
    seq("2*3 == 6?",
        &Eml::mul(Eml::of_nat(2), Eml::of_nat(3)),
        &Eml::of_nat(6));

    // Tier 1: derivative cycle
    // Must normalize between diffs — diff operates on tree structure
    println!("  -- Tier 1: derivative cycle --");
    let d1_sin = normalize(&Eml::sin(x.clone()).diff(0));
    let d2_sin = normalize(&d1_sin.diff(0));
    let d3_sin = normalize(&d2_sin.diff(0));
    let d4_sin = normalize(&d3_sin.diff(0));
    let d1_cos = normalize(&Eml::cos(x.clone()).diff(0));
    let d2_cos = normalize(&d1_cos.diff(0));
    {
        let neg_sin = normalize(&Eml::neg(Eml::sin(x.clone())));
        let neg_cos = normalize(&Eml::neg(Eml::cos(x.clone())));
        let sin_n = normalize(&Eml::sin(x.clone()));
        println!("  {:<30} {}", "D²(sin(x)) == -sin(x)?",
            if semantic_eq(&d2_sin, &neg_sin, &ctx) { "YES" } else { "NO" });
        println!("  {:<30} {}", "D²(cos(x)) == -cos(x)?",
            if semantic_eq(&d2_cos, &neg_cos, &ctx) { "YES" } else { "NO" });
        println!("  {:<30} {}", "D⁴(sin(x)) == sin(x)?",
            if semantic_eq(&d4_sin, &sin_n, &ctx) { "YES" } else { "NO" });
    }

    // Tier 2: trig at zero
    println!("  -- Tier 2: trig at zero --");
    let sin0 = Eml::sin(x.clone()).subst(0, &Eml::zero());
    let cos0 = Eml::cos(x.clone()).subst(0, &Eml::zero());
    seq("sin(0) == 0?", &sin0, &Eml::zero());
    seq("cos(0) == 1?", &cos0, &Eml::One);

    // Tier 3: Euler's formula decomposed
    println!("  -- Tier 3: Euler decomposed --");
    seq("exp(ix) == cos(x)+i·sin(x)?",
        &Eml::exp(Eml::mul(Eml::i_unit(), x.clone())),
        &Eml::add(Eml::cos(x.clone()),
                   Eml::mul(Eml::i_unit(), Eml::sin(x.clone()))));

    // Tier 4: Pythagorean identity
    println!("  -- Tier 4: Pythagorean --");
    seq("sin²(x)+cos²(x) == 1?",
        &Eml::add(Eml::sqr(Eml::sin(x.clone())),
                   Eml::sqr(Eml::cos(x.clone()))),
        &Eml::One);

    // Tier 5: double angle
    println!("  -- Tier 5: double angle --");
    let two_x = Eml::add(x.clone(), x.clone());
    seq("2·sin(x)·cos(x) == sin(x+x)?",
        &Eml::mul(Eml::mul(Eml::two(), Eml::sin(x.clone())), Eml::cos(x.clone())),
        &Eml::sin(two_x.clone()));
    seq("cos²(x)-sin²(x) == cos(x+x)?",
        &Eml::sub(Eml::sqr(Eml::cos(x.clone())),
                   Eml::sqr(Eml::sin(x.clone()))),
        &Eml::cos(two_x.clone()));

    // Negative tests (should all be NO)
    println!("  -- Negative tests --");
    seq("sin(x) == cos(x)?",
        &Eml::sin(x.clone()), &Eml::cos(x.clone()));
    seq("sin(x) == 0?",
        &Eml::sin(x.clone()), &Eml::zero());
    seq("cos(x) == 1?",
        &Eml::cos(x.clone()), &Eml::One);
    seq("exp(ix) == 1?",
        &Eml::exp(Eml::mul(Eml::i_unit(), x.clone())), &Eml::One);
    seq("sin²(x)+cos²(x) == 2?",
        &Eml::add(Eml::sqr(Eml::sin(x.clone())),
                   Eml::sqr(Eml::cos(x.clone()))),
        &Eml::two());
    seq("D(sin(x)) == -sin(x)?",
        &Eml::sin(x.clone()).diff(0),
        &Eml::neg(Eml::sin(x.clone())));
    seq("sin(x) == sin(y)?",
        &Eml::sin(x.clone()), &Eml::sin(y.clone()));
    seq("i == -i?",
        &Eml::i_unit(), &Eml::neg(Eml::i_unit()));
    seq("exp(iπ) == 1?",
        &Eml::exp(Eml::mul(Eml::i_unit(), Eml::pi())),
        &Eml::One);

    // Compositions
    println!("  -- Compositions --");
    // Derivative of Pythagorean = 0
    let pyth = Eml::add(Eml::sqr(Eml::sin(x.clone())), Eml::sqr(Eml::cos(x.clone())));
    let d_pyth = normalize(&pyth).diff(0);
    seq("D(sin²+cos²) == 0?", &d_pyth, &Eml::zero());

    // Product rule: D(sin·cos) = cos²-sin²
    let sin_cos = Eml::mul(Eml::sin(x.clone()), Eml::cos(x.clone()));
    let d_sin_cos = normalize(&sin_cos).diff(0);
    seq("D(sin·cos) == cos²-sin²?",
        &d_sin_cos,
        &Eml::sub(Eml::sqr(Eml::cos(x.clone())),
                   Eml::sqr(Eml::sin(x.clone()))));

    // Chain rule: D(sin²) = 2·sin·cos
    let d_sin_sq = normalize(&Eml::sqr(Eml::sin(x.clone()))).diff(0);
    seq("D(sin²(x)) == 2sin·cos?",
        &d_sin_sq,
        &Eml::mul(Eml::mul(Eml::two(), Eml::sin(x.clone())), Eml::cos(x.clone())));

    // Half-angle: sin²(x) = (1-cos(2x))/2
    seq("sin²(x) == (1-cos(2x))/2?",
        &Eml::sqr(Eml::sin(x.clone())),
        &Eml::mul(Eml::sub(Eml::One, Eml::cos(two_x.clone())), Eml::half()));

    // Euler at 2x
    seq("exp(2ix) == cos(2x)+i·sin(2x)?",
        &Eml::exp(Eml::mul(Eml::i_unit(), two_x.clone())),
        &Eml::add(Eml::cos(two_x.clone()),
                   Eml::mul(Eml::i_unit(), Eml::sin(two_x.clone()))));

    // Two-variable: sin²(x)+cos²(x)+sin²(y)+cos²(y) = 2
    seq("sin²x+cos²x+sin²y+cos²y == 2?",
        &Eml::add(
            Eml::add(Eml::sqr(Eml::sin(x.clone())), Eml::sqr(Eml::cos(x.clone()))),
            Eml::add(Eml::sqr(Eml::sin(y.clone())), Eml::sqr(Eml::cos(y.clone())))),
        &Eml::two());
    println!();

    println!("--- Adversarial: indirect zero in ln ---");
    // Try to sneak zero past the normalizer via indirect construction

    // 1. ln(x - x) -- sub_self gives zero, does ln see it?
    let ln_x_minus_x = Eml::ln(Eml::sub(x.clone(), x.clone()));
    let ln_zero_direct = Eml::ln(Eml::zero());
    println!("  ln(x-x)            = {}", normalize(&ln_x_minus_x));
    println!("  ln(0)              = {}", normalize(&ln_zero_direct));
    println!("  ln(x-x) == ln(0)?  {}", if normalize(&ln_x_minus_x) == normalize(&ln_zero_direct) { "YES" } else { "NO" });

    // 2. ln(0 * x) -- does mul_zero fire before ln sees it?
    let ln_zero_x = Eml::ln(Eml::mul(Eml::zero(), x.clone()));
    println!("  ln(0*x)            = {}", normalize(&ln_zero_x));
    println!("  ln(0*x) == ln(0)?  {}", if normalize(&ln_zero_x) == normalize(&ln_zero_direct) { "YES" } else { "NO" });

    // 3. The collapse test: does ln(0) + ln(x) == ln(0) ?
    // (This is what the trivial theory says)
    let ln0_plus_lnx = Eml::add(Eml::ln(Eml::zero()), Eml::ln(x.clone()));
    let ln0 = Eml::ln(Eml::zero());
    println!("  ln(0)+ln(x)        = {}", normalize(&ln0_plus_lnx));
    println!("  ln(0)              = {}", normalize(&ln0));
    println!("  ln(0)+ln(x)==ln(0)?{}", if normalize(&ln0_plus_lnx) == normalize(&ln0) { " YES" } else { " NO" });

    // 4. The real collapse: can we derive 0 == 1?
    println!("  0 == 1?            {}", if normalize(&Eml::zero()) == normalize(&Eml::One) { "YES" } else { "NO" });

    // 5. exp(ln(0)) -- should this be 0 or blow up?
    let exp_ln_0 = Eml::exp(Eml::ln(Eml::zero()));
    println!("  exp(ln(0))         = {}", normalize(&exp_ln_0));
    println!("  exp(ln(0)) == 0?   {}", if normalize(&exp_ln_0) == normalize(&Eml::zero()) { "YES" } else { "NO" });

    // 6. Try the full collapse chain:
    // ln(mul(zero, exp(a))) should give ln(0) via mul_zero
    // but also add(ln(0), ln(exp(a))) = add(ln(0), a) via ln_mul+ln_exp
    // Does the normalizer agree on both paths?
    let a = Eml::Var(2);
    let path1 = Eml::ln(Eml::mul(Eml::zero(), Eml::exp(a.clone())));
    println!("  ln(0*exp(z))       = {}", normalize(&path1));

    // 7. 0 * (1/0) -- the known non-confluence point
    let zero_times_inv_zero = Eml::mul(Eml::zero(), Eml::inv(Eml::zero()));
    println!("  0*(1/0)            = {}", normalize(&zero_times_inv_zero));
    println!("  0*(1/0) == 0?      {}", if normalize(&zero_times_inv_zero) == normalize(&Eml::zero()) { "YES" } else { "NO" });
    println!("  0*(1/0) == 1?      {}", if normalize(&zero_times_inv_zero) == normalize(&Eml::One) { "YES" } else { "NO" });

    // 8. Subtle: (x - x) * y -- zero constructed indirectly, then multiplied
    let indirect_zero_times_y = Eml::mul(Eml::sub(x.clone(), x.clone()), y.clone());
    println!("  (x-x)*y            = {}", normalize(&indirect_zero_times_y));
    println!("  (x-x)*y == 0?      {}", if normalize(&indirect_zero_times_y) == normalize(&Eml::zero()) { "YES" } else { "NO" });

    // 9. ln((x-x)*y) -- the sneaky one. Does sub_self fire inside mul,
    //    then mul_zero, then ln sees zero? Or does ln see the product first?
    let ln_indirect = Eml::ln(Eml::mul(Eml::sub(x.clone(), x.clone()), y.clone()));
    println!("  ln((x-x)*y)        = {}", normalize(&ln_indirect));
    println!("  ln((x-x)*y)==ln(0)?{}", if normalize(&ln_indirect) == normalize(&ln_zero_direct) { " YES" } else { " NO" });

    // 10. Can we get inconsistency? Two things that should be different
    //     but the normalizer might confuse due to ln(0) propagation?
    //     ln(0) is opaque, so ln(0) + a and ln(0) + b should differ if a ≠ b
    let t1 = Eml::add(Eml::ln(Eml::zero()), x.clone());
    let t2 = Eml::add(Eml::ln(Eml::zero()), y.clone());
    println!("  ln(0)+x            = {}", normalize(&t1));
    println!("  ln(0)+y            = {}", normalize(&t2));
    println!("  ln(0)+x==ln(0)+y?  {}", if normalize(&t1) == normalize(&t2) { "YES (BUG!)" } else { "NO (good)" });
    println!();

    println!("--- Adversarial: consistency probes ---");
    // If exp(ln(0)) = 0, and 0*(1/0) = 0, can we derive contradictions?

    // exp(ln(0)) = 0, but ln(0) is opaque.
    // What about exp(ln(0) + ln(x))? If ln distributes: = exp(ln(0*x)) = exp(ln(0)) = 0
    // But also exp(ln(0) + ln(x)) = exp(ln(0)) * exp(ln(x)) = 0 * x = 0
    // So this should be 0 either way. Is it?
    let e1 = Eml::exp(Eml::add(Eml::ln(Eml::zero()), Eml::ln(x.clone())));
    println!("  exp(ln(0)+ln(x))   = {}", normalize(&e1));
    println!("  == 0?              {}", if normalize(&e1) == normalize(&Eml::zero()) { "YES" } else { "NO" });
    println!("  == x?              {}", if normalize(&e1) == normalize(&x) { "YES" } else { "NO" });

    // What about exp(ln(x) + ln(0))?  Same thing, different order
    let e2 = Eml::exp(Eml::add(Eml::ln(x.clone()), Eml::ln(Eml::zero())));
    println!("  exp(ln(x)+ln(0))   = {}", normalize(&e2));
    println!("  == 0?              {}", if normalize(&e2) == normalize(&Eml::zero()) { "YES" } else { "NO" });

    // 0 * x via the exp/ln encoding directly (not using mul constructor)
    // mul(a,b) = exp(ln(a) + ln(b)), so mul(0,x) = exp(ln(0) + ln(x))
    // The normalizer should give 0 here (same as 0*x)
    println!("  0*x                = {}", normalize(&Eml::mul(Eml::zero(), x.clone())));

    // exp(ln(0)) * x -- should be 0 * x = 0
    let e3 = Eml::mul(Eml::exp(Eml::ln(Eml::zero())), x.clone());
    println!("  exp(ln(0))*x       = {}", normalize(&e3));
    println!("  == 0?              {}", if normalize(&e3) == normalize(&Eml::zero()) { "YES" } else { "NO" });

    // THE BIG TEST: does the normalizer respect that 0*(1/0) could be 1?
    // inv(0) = exp(-ln(0)). If exp(ln(0)) = 0, then:
    // 0 * inv(0) = 0 * exp(-ln(0))
    // = exp(ln(0) + (-ln(0))) = exp(0) = 1   <-- via exp_add path
    // But normalizer says 0*(1/0) = 0         <-- via mul_zero path
    // Are there other ways to reach 1 through this?
    let inv_zero = Eml::inv(Eml::zero());
    let product = Eml::mul(Eml::zero(), inv_zero.clone());
    let via_exp = Eml::exp(Eml::add(Eml::ln(Eml::zero()), Eml::neg(Eml::ln(Eml::zero()))));
    println!("  0*(1/0)            = {}", normalize(&product));
    println!("  exp(ln0+(-ln0))    = {}", normalize(&via_exp));
    println!("  exp(ln0+(-ln0))==1?{}", if normalize(&via_exp) == normalize(&Eml::One) { " YES" } else { " NO" });
    println!("  exp(ln0+(-ln0))==0?{}", if normalize(&via_exp) == normalize(&Eml::zero()) { " YES" } else { " NO" });
    println!();

    println!("--- KB critical pair sanity check (extended ±∞ rules) ---");
    let mut kb_pass = 0;
    let mut kb_fail = 0;
    let inf_n = Eml::NegInf;
    let inf_p = Eml::PosInf;

    // Helper: check that two expressions normalize to the same thing
    let mut kb = |name: &str, a: &Eml, b: &Eml| {
        let na = normalize(a);
        let nb = normalize(b);
        let ok = na == nb;
        if !ok {
            println!("  FAIL {name}: {na} ≠ {nb}");
            kb_fail += 1;
        } else {
            kb_pass += 1;
        }
    };

    // 1. exp_ln × ln_zero: exp(ln(0)) — via exp_ln→0, via ln→-∞ then exp→0
    kb("exp(ln(0))=0", &Eml::exp(Eml::ln(Eml::zero())), &Eml::zero());

    // 2. ln_exp × exp_neg_inf: ln(exp(-∞)) — via ln_exp→-∞, via exp→0 then ln→-∞
    kb("ln(exp(-∞))=-∞", &Eml::ln(Eml::exp(inf_n.clone())), &inf_n);

    // 3. ln_mul × mul_zero_l: ln(0*x) — via mul_zero→ln(0)→-∞, via ln_mul→ln(0)+ln(x)→-∞
    kb("ln(0*x)=-∞", &Eml::ln(Eml::mul(Eml::zero(), x.clone())), &inf_n);

    // 4. ln_mul × mul_zero_r: ln(x*0)
    kb("ln(x*0)=-∞", &Eml::ln(Eml::mul(x.clone(), Eml::zero())), &inf_n);

    // 5. exp_add × add_neg_inf: exp(-∞ + a) — via absorption→exp(-∞)→0
    kb("exp(-∞+x)=0", &Eml::exp(Eml::add(inf_n.clone(), Eml::ln(x.clone()))), &Eml::zero());

    // 6. mul_zero × encoding: 0*x via mul vs via exp(ln(0)+ln(x))
    kb("0*x=0", &Eml::mul(Eml::zero(), x.clone()), &Eml::zero());

    // 7. inv(0) consistent paths
    kb("inv(0)=+∞", &Eml::inv(Eml::zero()), &inf_p);

    // 8. inv(+∞)=0
    kb("inv(+∞)=0", &Eml::inv(inf_p.clone()), &Eml::zero());

    // 9. inv(inv(0))=0: inv(+∞)=0
    kb("inv(inv(0))=0", &Eml::inv(Eml::inv(Eml::zero())), &Eml::zero());

    // 10. neg(-∞)=+∞
    kb("neg(-∞)=+∞", &Eml::neg(inf_n.clone()), &inf_p);

    // 11. neg(+∞)=-∞
    kb("neg(+∞)=-∞", &Eml::neg(inf_p.clone()), &inf_n);

    // 12. neg(neg(-∞))=-∞
    kb("neg(neg(-∞))=-∞", &Eml::neg(Eml::neg(inf_n.clone())), &inf_n);

    // 13. 0*(1/0) = indeterminate = exp(-∞ + ∞) — both paths
    let zero_inv_zero = Eml::mul(Eml::zero(), Eml::inv(Eml::zero()));
    let exp_inf_sum = Eml::exp(Eml::add(inf_n.clone(), inf_p.clone()));
    kb("0*(1/0)=exp(-∞+∞)", &zero_inv_zero, &exp_inf_sum);

    // 14. ln(0)+ln(x) = -∞ (absorption)
    kb("ln(0)+ln(x)=-∞", &Eml::add(Eml::ln(Eml::zero()), Eml::ln(x.clone())), &inf_n);

    // 15. exp(-∞)=0
    kb("exp(-∞)=0", &Eml::exp(inf_n.clone()), &Eml::zero());

    // 16. exp(+∞)=+∞
    kb("exp(+∞)=+∞", &Eml::exp(inf_p.clone()), &inf_p);

    // 17. ln(0*x) = ln(0) via both paths
    kb("ln(0*x)=ln(0)", &Eml::ln(Eml::mul(Eml::zero(), x.clone())),
       &Eml::ln(Eml::zero()));

    // 18. 0*0=0 (no infinity involved)
    kb("0*0=0", &Eml::mul(Eml::zero(), Eml::zero()), &Eml::zero());

    // 19. sub_self(-∞) should NOT be 0 — should be indeterminate
    let sub_inf = Eml::sub(inf_n.clone(), inf_n.clone());
    let add_inf = Eml::add(inf_n.clone(), inf_p.clone());
    kb("-∞-(-∞)=-∞+∞", &sub_inf, &add_inf);

    // 20. (x-x)*(1/(x-x)) = 0*inv(0) = indeterminate
    let xx = Eml::sub(x.clone(), x.clone());
    kb("(x-x)*(1/(x-x))=indet",
       &Eml::mul(xx.clone(), Eml::inv(xx.clone())),
       &Eml::mul(Eml::zero(), Eml::inv(Eml::zero())));

    // 21. exp(ln(0)+(-ln(0))) = exp(-∞+∞) — the original inconsistency, now consistent
    kb("exp(ln0+(-ln0))=exp(-∞+∞)",
       &Eml::exp(Eml::add(Eml::ln(Eml::zero()), Eml::neg(Eml::ln(Eml::zero())))),
       &exp_inf_sum);

    // 22. mul_one × infinity: 1*(-∞) = -∞? But mul encoding goes through ln(1)+ln(-∞)...
    kb("1*x=x (finite)", &Eml::mul(Eml::One, x.clone()), &x);

    // 23. mul(-∞, x) — what happens? Through encoding: exp(ln(-∞)+ln(x))=exp(+∞+ln(x))=exp(+∞)=+∞?
    //     Mathematically -∞ * positive = -∞, but our "mul" encodes through exp/ln.
    //     Let's just check consistency:
    let mul_inf_x = normalize(&Eml::mul(inf_n.clone(), x.clone()));
    println!("  INFO -∞*x = {mul_inf_x}");

    // 24. add_assoc with infinity: (-∞+a)+b = -∞+(a+b) — both -∞
    kb("(-∞+x)+y=-∞",
       &Eml::add(Eml::add(inf_n.clone(), x.clone()), y.clone()),
       &inf_n);

    // 25. 0+0=0 (sanity)
    kb("0+0=0", &Eml::add(Eml::zero(), Eml::zero()), &Eml::zero());

    // 26. exp(0)=1 still works
    kb("exp(0)=1", &Eml::exp(Eml::zero()), &Eml::One);

    // 27. ln(1)=0 still works
    kb("ln(1)=0", &Eml::ln(Eml::One), &Eml::zero());

    println!("  KB sanity: {kb_pass} pass, {kb_fail} fail");
    println!();

    println!("--- Summary ---");
    println!("  Core: 1 type, 2 constants (1, ±∞), 1 binary operator");
    println!("  Derived: exp, ln, +, -, *, /, neg, inv, integers, D");
    println!("  Trig: sin, cos, tan, π, i (from Euler's formula)");
    println!("  Extended: ln(0)=-∞, exp(-∞)=0, -∞+finite=-∞");
    println!("  Singularity: -∞+∞ (indeterminate, left unreduced)");
}

// ── Test suite ─────────────────────────────────────────────────────────────
//
// Alignment with Lean Step rules (Eml/Confluence.lean):
//   All 20 Lean rules are covered below, named after their Lean constructors.
//   Rust extras not in Lean Step (but derivable and sound):
//     - neg_distribute:             neg(a+b) → neg(a)+neg(b)
//     - neg_zero:                   neg(0) → 0
//     - ln_neg_product:             ln(neg(x)) → ln(x)+ln(-1)  [non-ground]
//     - conditional_ln_decomposition: smart AC cancellation
//     - Q(i) ground evaluation:     exact arithmetic for ground terms
//     - semantic_eq:                variable-term coefficient matching
//   Extended ±∞ model (not yet in Lean):
//     - ln(0) → -∞, exp(-∞) → 0, inv(0) → +∞
//     - -∞ + finite → -∞ (absorption)
//     - -∞ + ∞ left unreduced (indeterminate)
//     - mul_zero and sub_self guarded at ±∞

#[cfg(test)]
mod tests {
    use super::*;

    fn x() -> Eml { Eml::Var(0) }
    fn y() -> Eml { Eml::Var(1) }
    fn z() -> Eml { Eml::Var(2) }

    /// Structural equality after normalization.
    fn eq(a: &Eml, b: &Eml) -> bool {
        normalize(a) == normalize(b)
    }

    /// Semantic equality (handles variables via Q(i) coefficient matching).
    fn seq(a: &Eml, b: &Eml) -> bool {
        let ctx = GroundCtx::new();
        let na = normalize(a);
        let nb = normalize(b);
        semantic_eq(&na, &nb, &ctx)
    }

    // ── Lean rules: one test per Step constructor ─────────────────────────

    #[test] fn rule_exp_ln() {
        assert!(eq(&Eml::exp(Eml::ln(x())), &x()));
    }

    #[test] fn rule_ln_exp() {
        assert!(eq(&Eml::ln(Eml::exp(x())), &x()));
    }

    #[test] fn rule_sub_zero() {
        assert!(eq(&Eml::sub(x(), Eml::zero()), &x()));
    }

    #[test] fn rule_sub_self() {
        assert!(eq(&Eml::sub(x(), x()), &Eml::zero()));
    }

    #[test] fn rule_add_zero_l() {
        assert!(eq(&Eml::add(Eml::zero(), x()), &x()));
    }

    #[test] fn rule_add_zero_r() {
        assert!(eq(&Eml::add(x(), Eml::zero()), &x()));
    }

    #[test] fn rule_mul_one_l() {
        assert!(eq(&Eml::mul(Eml::One, x()), &x()));
    }

    #[test] fn rule_mul_one_r() {
        assert!(eq(&Eml::mul(x(), Eml::One), &x()));
    }

    #[test] fn rule_mul_zero_l() {
        assert!(eq(&Eml::mul(Eml::zero(), x()), &Eml::zero()));
    }

    #[test] fn rule_mul_zero_r() {
        assert!(eq(&Eml::mul(x(), Eml::zero()), &Eml::zero()));
    }

    #[test] fn rule_neg_neg() {
        assert!(eq(&Eml::neg(Eml::neg(x())), &x()));
    }

    #[test] fn rule_inv_inv() {
        assert!(eq(&Eml::inv(Eml::inv(x())), &x()));
    }

    #[test] fn rule_exp_add() {
        // exp(x+y) == exp(x)*exp(y)
        assert!(eq(
            &Eml::exp(Eml::add(x(), y())),
            &Eml::mul(Eml::exp(x()), Eml::exp(y())),
        ));
    }

    #[test] fn rule_ln_mul() {
        // ln(x*y) == ln(x)+ln(y)  [non-ground variables: gating correct]
        assert!(eq(
            &Eml::ln(Eml::mul(x(), y())),
            &Eml::add(Eml::ln(x()), Eml::ln(y())),
        ));
    }

    #[test] fn rule_mul_add() {
        // x*(y+z) == x*y + x*z
        assert!(eq(
            &Eml::mul(x(), Eml::add(y(), z())),
            &Eml::add(Eml::mul(x(), y()), Eml::mul(x(), z())),
        ));
    }

    #[test] fn rule_ln_one() {
        assert!(eq(&Eml::ln(Eml::One), &Eml::zero()));
    }

    #[test] fn rule_exp_zero() {
        assert!(eq(&Eml::exp(Eml::zero()), &Eml::One));
    }

    #[test] fn rule_add_assoc() {
        // (x+y)+z == x+(y+z)
        assert!(eq(
            &Eml::add(Eml::add(x(), y()), z()),
            &Eml::add(x(), Eml::add(y(), z())),
        ));
    }

    #[test] fn rule_add_comm() {
        assert!(eq(&Eml::add(x(), y()), &Eml::add(y(), x())));
    }

    #[test] fn rule_cancel_exp_ln() {
        // exp(ln(ln(x))) - ln(x) == 0
        assert!(eq(
            &Eml::sub(Eml::exp(Eml::ln(Eml::ln(x()))), Eml::ln(x())),
            &Eml::zero(),
        ));
    }

    #[test] fn rule_cancel_ln_exp() {
        // exp(x) - ln(exp(exp(x))) == 0
        assert!(eq(
            &Eml::sub(Eml::exp(x()), Eml::ln(Eml::exp(Eml::exp(x())))),
            &Eml::zero(),
        ));
    }

    // ── Ground arithmetic ─────────────────────────────────────────────────

    #[test] fn ground_add() {
        assert!(eq(&Eml::add(Eml::of_nat(2), Eml::of_nat(3)), &Eml::of_nat(5)));
    }

    #[test] fn ground_mul() {
        assert!(eq(&Eml::mul(Eml::of_nat(3), Eml::of_nat(4)), &Eml::of_nat(12)));
    }

    #[test] fn ground_i_sq() {
        // i² == -1
        assert!(eq(&Eml::mul(Eml::i_unit(), Eml::i_unit()), &Eml::neg_one()));
    }

    #[test] fn ground_euler() {
        // exp(iπ) == -1
        assert!(seq(
            &Eml::exp(Eml::mul(Eml::i_unit(), Eml::pi())),
            &Eml::neg_one(),
        ));
    }

    // ── Identities requiring semantic equality ────────────────────────────

    #[test] fn identity_pythagorean() {
        assert!(seq(
            &Eml::add(Eml::sqr(Eml::sin(x())), Eml::sqr(Eml::cos(x()))),
            &Eml::One,
        ));
    }

    #[test] fn identity_diff_sin_is_cos() {
        assert!(seq(&Eml::sin(x()).diff(0), &Eml::cos(x())));
    }

    #[test] fn identity_diff_cos_is_neg_sin() {
        assert!(seq(&Eml::cos(x()).diff(0), &Eml::neg(Eml::sin(x()))));
    }

    #[test] fn identity_double_angle_sin() {
        // 2·sin(x)·cos(x) == sin(2x)
        assert!(seq(
            &Eml::mul(Eml::mul(Eml::two(), Eml::sin(x())), Eml::cos(x())),
            &Eml::sin(Eml::add(x(), x())),
        ));
    }

    #[test] fn identity_double_angle_cos() {
        // cos²(x) - sin²(x) == cos(2x)
        assert!(seq(
            &Eml::sub(Eml::sqr(Eml::cos(x())), Eml::sqr(Eml::sin(x()))),
            &Eml::cos(Eml::add(x(), x())),
        ));
    }

    #[test] fn identity_euler_formula() {
        // exp(ix) == cos(x) + i·sin(x)
        assert!(seq(
            &Eml::exp(Eml::mul(Eml::i_unit(), x())),
            &Eml::add(Eml::cos(x()), Eml::mul(Eml::i_unit(), Eml::sin(x()))),
        ));
    }

    #[test] fn identity_diff_fourth_sin() {
        // D⁴(sin(x)) == sin(x)
        let d1 = normalize(&Eml::sin(x()).diff(0));
        let d2 = normalize(&d1.diff(0));
        let d3 = normalize(&d2.diff(0));
        let d4 = normalize(&d3.diff(0));
        assert!(seq(&d4, &Eml::sin(x())));
    }

    #[test] fn identity_two_variable_pythagorean() {
        // sin²(x)+cos²(x)+sin²(y)+cos²(y) == 2
        assert!(seq(
            &Eml::add(
                Eml::add(Eml::sqr(Eml::sin(x())), Eml::sqr(Eml::cos(x()))),
                Eml::add(Eml::sqr(Eml::sin(y())), Eml::sqr(Eml::cos(y()))),
            ),
            &Eml::two(),
        ));
    }

    // ── Negative tests: things that must NOT be equal ─────────────────────

    #[test] fn neg_sin_ne_cos() {
        assert!(!seq(&Eml::sin(x()), &Eml::cos(x())));
    }

    #[test] fn neg_sin_ne_zero() {
        assert!(!seq(&Eml::sin(x()), &Eml::zero()));
    }

    #[test] fn neg_cos_ne_one() {
        // cos(x) is not the constant 1
        assert!(!seq(&Eml::cos(x()), &Eml::One));
    }

    #[test] fn neg_exp_ne_ln() {
        assert!(!eq(&Eml::exp(x()), &Eml::ln(x())));
    }

    #[test] fn neg_add_ne_mul() {
        assert!(!eq(&Eml::add(x(), y()), &Eml::mul(x(), y())));
    }

    #[test] fn neg_x_ne_x_plus_one() {
        assert!(!eq(&x(), &Eml::add(x(), Eml::One)));
    }

    #[test] fn neg_sin_x_ne_sin_y() {
        // Different variables
        assert!(!seq(&Eml::sin(x()), &Eml::sin(y())));
    }

    #[test] fn neg_exp_i_pi_ne_one() {
        // exp(iπ) = -1, not 1
        assert!(!seq(
            &Eml::exp(Eml::mul(Eml::i_unit(), Eml::pi())),
            &Eml::One,
        ));
    }

    #[test] fn neg_pyth_ne_two() {
        // sin²+cos² = 1, not 2
        assert!(!seq(
            &Eml::add(Eml::sqr(Eml::sin(x())), Eml::sqr(Eml::cos(x()))),
            &Eml::two(),
        ));
    }

    #[test] fn neg_i_ne_neg_i() {
        assert!(!seq(&Eml::i_unit(), &Eml::neg(Eml::i_unit())));
    }

    // ── Ground constant expressions (π and e as EML trees) ───────────────
    //
    // π = sqrt(-(ln(-1))²) and e = exp(1) are valid ground EML trees.
    // The Q(i) evaluator handles π via ln(-1) = -iπ exactly.
    // e = exp(1) is outside Q(i) — the evaluator returns None and says NO.
    // So the checker is SOUND (never false positive) but not complete for
    // expressions mixing e with non-Q(i) transcendentals.

    #[test] fn ground_pi_sq_is_neg_ln_neg_one_sq() {
        // π² = -(ln(-1))²  — directly from the definition of π
        assert!(seq(
            &Eml::sqr(Eml::pi()),
            &Eml::neg(Eml::sqr(Eml::ln(Eml::neg_one()))),
        ));
    }

    #[test] fn ground_exp_ln_nat() {
        // exp(ln(7)) = 7  — exp_ln rule on a ground natural
        assert!(eq(&Eml::exp(Eml::ln(Eml::of_nat(7))), &Eml::of_nat(7)));
    }

    #[test] fn ground_ln_exp_nat() {
        // ln(exp(3)) = 3
        assert!(eq(&Eml::ln(Eml::exp(Eml::of_nat(3))), &Eml::of_nat(3)));
    }

    #[test] fn ground_pi_plus_e_ne_7() {
        // π + e ≠ 7  (π≈3.14, e≈2.72, sum≈5.86)
        // Both sides are ground EML trees; checker correctly returns NO.
        assert!(!seq(
            &Eml::add(Eml::pi(), Eml::exp(Eml::One)),
            &Eml::of_nat(7),
        ));
    }

    #[test] fn ground_pi_plus_e_eq_self() {
        // π + e = π + e  — reflexivity, always YES
        let pi_e = Eml::add(Eml::pi(), Eml::exp(Eml::One));
        assert!(seq(&pi_e, &pi_e));
    }

    #[test] fn ground_two_pi_ne_pi() {
        // 2π ≠ π
        assert!(!seq(&Eml::mul(Eml::two(), Eml::pi()), &Eml::pi()));
    }

    // ── Adversarial tests: trying to find bugs ────────────────────────────
    //
    // Each test is annotated with the expected outcome and a brief reason.
    // YES = checker should accept (completeness test: would a false negative show up?)
    // NO  = checker should reject  (soundness test: would a false positive show up?)

    // --- Parity / symmetry ---

    #[test] fn adversarial_sin_odd() {
        // YES: sin(-x) = -sin(x)  — sin is an odd function
        assert!(seq(&Eml::sin(Eml::neg(x())), &Eml::neg(Eml::sin(x()))));
    }

    #[test] fn adversarial_cos_even() {
        // YES: cos(-x) = cos(x)  — cos is an even function
        assert!(seq(&Eml::cos(Eml::neg(x())), &Eml::cos(x())));
    }

    #[test] fn adversarial_sin_ne_sin_neg() {
        // NO: sin(x) ≠ sin(-x)  — if they were equal, sin would be identically 0
        assert!(!seq(&Eml::sin(x()), &Eml::sin(Eml::neg(x()))));
    }

    // --- Angle addition formulas ---

    #[test] fn adversarial_sin_add() {
        // YES: sin(x+y) = sin(x)cos(y) + cos(x)sin(y)
        assert!(seq(
            &Eml::sin(Eml::add(x(), y())),
            &Eml::add(
                Eml::mul(Eml::sin(x()), Eml::cos(y())),
                Eml::mul(Eml::cos(x()), Eml::sin(y())),
            ),
        ));
    }

    #[test] fn adversarial_cos_add() {
        // YES: cos(x+y) = cos(x)cos(y) - sin(x)sin(y)
        assert!(seq(
            &Eml::cos(Eml::add(x(), y())),
            &Eml::sub(
                Eml::mul(Eml::cos(x()), Eml::cos(y())),
                Eml::mul(Eml::sin(x()), Eml::sin(y())),
            ),
        ));
    }

    #[test] fn adversarial_sin_ne_linear() {
        // NO: sin(x+y) ≠ sin(x) + sin(y)  — sin is not linear
        assert!(!seq(
            &Eml::sin(Eml::add(x(), y())),
            &Eml::add(Eml::sin(x()), Eml::sin(y())),
        ));
    }

    #[test] fn adversarial_cos_ne_linear() {
        // NO: cos(x+y) ≠ cos(x) + cos(y)
        assert!(!seq(
            &Eml::cos(Eml::add(x(), y())),
            &Eml::add(Eml::cos(x()), Eml::cos(y())),
        ));
    }

    // --- Product-to-sum formula ---

    #[test] fn adversarial_product_to_sum() {
        // YES: sin(x)sin(y) = (cos(x-y) - cos(x+y)) / 2
        assert!(seq(
            &Eml::mul(Eml::sin(x()), Eml::sin(y())),
            &Eml::mul(
                Eml::sub(Eml::cos(Eml::sub(x(), y())), Eml::cos(Eml::add(x(), y()))),
                Eml::half(),
            ),
        ));
    }

    // --- Algebraic identities ---

    #[test] fn adversarial_mul_assoc() {
        // YES: (x*y)*z = x*(y*z)  — multiplicative associativity
        assert!(eq(
            &Eml::mul(Eml::mul(x(), y()), z()),
            &Eml::mul(x(), Eml::mul(y(), z())),
        ));
    }

    #[test] fn adversarial_diff_squares() {
        // YES: (x+y)*(x-y) = x^2 - y^2
        assert!(eq(
            &Eml::mul(Eml::add(x(), y()), Eml::sub(x(), y())),
            &Eml::sub(Eml::sqr(x()), Eml::sqr(y())),
        ));
    }

    #[test] fn adversarial_sqrt_sqr() {
        // YES: sqrt(x)^2 = x — AC normalizer combines n copies of
        // exp(neg(ln(n)) + rest) → exp(rest), cancelling the 1/n denominator.
        assert!(eq(&Eml::sqr(Eml::sqrt(x())), &x()));
    }

    #[test] fn adversarial_mul_cancel_right() {
        // YES: (x*y)/y = x  — multiplicative cancellation
        assert!(eq(&Eml::div(Eml::mul(x(), y()), y()), &x()));
    }

    #[test] fn adversarial_div_self() {
        // YES: x/x = 1
        assert!(eq(&Eml::div(x(), x()), &Eml::One));
    }

    #[test] fn adversarial_ln_div() {
        // YES: ln(x/y) = ln(x) - ln(y)
        assert!(eq(
            &Eml::ln(Eml::div(x(), y())),
            &Eml::sub(Eml::ln(x()), Eml::ln(y())),
        ));
    }

    #[test] fn adversarial_exp_sqr() {
        // YES: exp(x)^2 = exp(2x) = exp(x+x)
        assert!(eq(&Eml::sqr(Eml::exp(x())), &Eml::exp(Eml::add(x(), x()))));
    }

    #[test] fn adversarial_ln_sum_ne() {
        // NO: ln(x+y) ≠ ln(x)+ln(y)  — critical: log doesn't distribute over +
        assert!(!eq(
            &Eml::ln(Eml::add(x(), y())),
            &Eml::add(Eml::ln(x()), Eml::ln(y())),
        ));
    }

    #[test] fn adversarial_exp_mul_ne() {
        // NO: exp(x*y) ≠ exp(x)*exp(y)  — exp distributes over +, not *
        assert!(!eq(
            &Eml::exp(Eml::mul(x(), y())),
            &Eml::mul(Eml::exp(x()), Eml::exp(y())),
        ));
    }

    #[test] fn adversarial_sin_ne_neg_sin() {
        // NO: sin(x) ≠ -sin(x)  — would force sin = 0 everywhere
        assert!(!seq(&Eml::sin(x()), &Eml::neg(Eml::sin(x()))));
    }

    #[test] fn adversarial_cos_ne_neg_cos() {
        // NO: cos(x) ≠ -cos(x)
        assert!(!seq(&Eml::cos(x()), &Eml::neg(Eml::cos(x()))));
    }

    // --- Derivative tests ---

    #[test] fn adversarial_d_tan() {
        // KNOWN INCOMPLETENESS: D(tan(x)) = 1 + tan(x)^2 is mathematically true,
        // but semantic_eq cannot verify it.  The proof requires the Pythagorean
        // identity (sin²+cos²=1) as an intermediate step: D(tan) simplifies to
        // (sin²+cos²)/cos² = 1/cos², and 1+tan² = (cos²+sin²)/cos² = 1/cos².
        // semantic_eq matches additive terms pairwise — it cannot algebraically
        // invoke Pythagorean to combine the sin² and cos² terms.
        // Both sides correctly share the same mathematical value; the checker is
        // SOUND (never wrong) but not COMPLETE for identities requiring sub-proofs.
        let d_tan = normalize(&Eml::tan(x()).diff(0));
        let one_plus_tan_sq = Eml::add(Eml::One, Eml::sqr(Eml::tan(x())));
        assert!(!seq(&d_tan, &one_plus_tan_sq),
            "semantic_eq gained Pythagorean-aware simplification — update this test");
    }

    #[test] fn adversarial_d_x_cubed() {
        // YES: D(x^3) = 3*x^2
        let x_cubed = Eml::mul(Eml::sqr(x()), x());
        let dx3 = normalize(&x_cubed.diff(0));
        let three_x_sq = Eml::mul(Eml::of_nat(3), Eml::sqr(x()));
        assert!(seq(&dx3, &three_x_sq));
    }

    #[test] fn adversarial_d_exp_sq() {
        // YES: D(exp(x)^2) = 2*exp(x)^2
        let exp_sq = Eml::sqr(Eml::exp(x()));
        let d_exp_sq = normalize(&exp_sq.diff(0));
        let two_exp_sq = Eml::mul(Eml::two(), Eml::sqr(Eml::exp(x())));
        assert!(seq(&d_exp_sq, &two_exp_sq));
    }

    #[test] fn adversarial_d_ln_sq() {
        // YES: D(ln(x)^2) = 2*ln(x)/x = 2*ln(x)*inv(x)
        let ln_sq = Eml::sqr(Eml::ln(x()));
        let d_ln_sq = normalize(&ln_sq.diff(0));
        let two_ln_inv = Eml::mul(Eml::mul(Eml::two(), Eml::ln(x())), Eml::inv(x()));
        assert!(seq(&d_ln_sq, &two_ln_inv));
    }

    // --- Ground power-of-(-1) tests ---

    #[test] fn adversarial_exp_2pi_is_one() {
        // YES: (-1)^2 = 1, i.e. exp(2*ln(-1)) = exp(2iπ) = 1
        assert!(seq(
            &Eml::exp(Eml::mul(Eml::two(), Eml::ln(Eml::neg_one()))),
            &Eml::One,
        ));
    }

    #[test] fn adversarial_exp_3pi_is_neg_one() {
        // YES: (-1)^3 = -1
        assert!(seq(
            &Eml::exp(Eml::mul(Eml::of_nat(3), Eml::ln(Eml::neg_one()))),
            &Eml::neg_one(),
        ));
    }

    #[test] fn adversarial_exp_4pi_is_one() {
        // YES: (-1)^4 = 1
        assert!(seq(
            &Eml::exp(Eml::mul(Eml::of_nat(4), Eml::ln(Eml::neg_one()))),
            &Eml::One,
        ));
    }

    // --- Hyperbolic / cross identities ---

    #[test] fn adversarial_euler_decomposed() {
        // YES: exp(ix) = cos(x) + i*sin(x)
        assert!(seq(
            &Eml::exp(Eml::mul(Eml::i_unit(), x())),
            &Eml::add(Eml::cos(x()), Eml::mul(Eml::i_unit(), Eml::sin(x()))),
        ));
    }

    #[test] fn adversarial_half_angle_sin() {
        // YES: sin^2(x) = (1 - cos(2x)) / 2
        assert!(seq(
            &Eml::sqr(Eml::sin(x())),
            &Eml::mul(
                Eml::sub(Eml::One, Eml::cos(Eml::add(x(), x()))),
                Eml::half(),
            ),
        ));
    }

    #[test] fn adversarial_half_angle_cos() {
        // YES: cos^2(x) = (1 + cos(2x)) / 2
        assert!(seq(
            &Eml::sqr(Eml::cos(x())),
            &Eml::mul(
                Eml::add(Eml::One, Eml::cos(Eml::add(x(), x()))),
                Eml::half(),
            ),
        ));
    }

    // --- Stability under composition ---

    #[test] fn adversarial_d_pyth_is_zero() {
        // YES: D(sin^2(x) + cos^2(x)) = 0  — derivative of a constant
        let pyth = Eml::add(Eml::sqr(Eml::sin(x())), Eml::sqr(Eml::cos(x())));
        let d_pyth = normalize(&pyth).diff(0);
        assert!(seq(&d_pyth, &Eml::zero()));
    }

    #[test] fn adversarial_ln_exp_compose() {
        // YES: ln(exp(x+y)) = x+y
        assert!(eq(&Eml::ln(Eml::exp(Eml::add(x(), y()))), &Eml::add(x(), y())));
    }

    // --- Potential soundness stress: things that should differ ---

    #[test] fn adversarial_ln_x_ne_x() {
        // NO: ln(x) ≠ x in general
        assert!(!eq(&Eml::ln(x()), &x()));
    }

    #[test] fn adversarial_exp_x_ne_x() {
        // NO: exp(x) ≠ x in general
        assert!(!eq(&Eml::exp(x()), &x()));
    }

    #[test] fn adversarial_sin_x_ne_x() {
        // NO: sin(x) ≠ x (only approximate for small x)
        assert!(!seq(&Eml::sin(x()), &x()));
    }

    #[test] fn adversarial_x_sq_ne_x() {
        // NO: x^2 ≠ x  (true only at x=0,1)
        assert!(!eq(&Eml::sqr(x()), &x()));
    }

    // --- No-crash edge cases ---

    #[test] fn adversarial_ln_zero_no_crash() {
        // Should not panic; just produce some normalized tree
        let _ = normalize(&Eml::ln(Eml::zero()));
    }

    #[test] fn adversarial_inv_zero_no_crash() {
        // Should not panic
        let _ = normalize(&Eml::inv(Eml::zero()));
    }

    #[test] fn adversarial_div_by_zero_no_crash() {
        // Should not panic; checker should say x/0 ≠ 1
        let _ = normalize(&Eml::div(x(), Eml::zero()));
        assert!(!eq(&Eml::div(x(), Eml::zero()), &Eml::One));
    }

    #[test] fn adversarial_large_nat_mul() {
        // Should not panic or overflow visibly; 20*20 = 400
        assert!(eq(
            &Eml::mul(Eml::of_nat(20), Eml::of_nat(20)),
            &Eml::of_nat(400),
        ));
    }
}


#[cfg(test)]
mod gap_survey {
    use super::*;
    fn x() -> Eml { Eml::Var(0) }
    fn y() -> Eml { Eml::Var(1) }
    fn seq(a: &Eml, b: &Eml) -> bool {
        let ctx = GroundCtx::new();
        semantic_eq(&normalize(a), &normalize(b), &ctx)
    }
    fn eq(a: &Eml, b: &Eml) -> bool { normalize(a) == normalize(b) }

    // Class 1: rational-scalar × log creates double-log
    // All of these are mathematically valid but normalizer can't reduce them.

    #[test] fn gap_x_to_3_halves() {
        // x^(3/2) = x * sqrt(x)  — rational exponent 3/2
        let lhs = Eml::exp(Eml::mul(Eml::mul(Eml::of_nat(3), Eml::ln(x())), Eml::half()));
        let rhs = Eml::mul(x(), Eml::sqrt(x()));
        println!("x^(3/2) eq x*sqrt(x): {}", eq(&lhs, &rhs));
    }

    #[test] fn gap_cube_root_cubed() {
        // cbrt(x)^3 = x — cube root
        let cbrt = Eml::exp(Eml::div(Eml::ln(x()), Eml::of_nat(3)));
        let lhs = Eml::mul(Eml::mul(cbrt.clone(), cbrt.clone()), cbrt.clone());
        println!("cbrt(x)^3 eq x: {}", eq(&lhs, &x()));
    }

    #[test] fn gap_exp_half_pi_is_i() {
        // Ground: exp(iπ/2) = i  — quarter-turn in complex plane
        // fails because iπ/2 = mul(mul(i,π), half()) hits double-log
        let exp_half_i_pi = Eml::exp(Eml::mul(
            Eml::mul(Eml::i_unit(), Eml::pi()),
            Eml::half(),
        ));
        let ctx = GroundCtx::new();
        let result = ground_eval(&normalize(&exp_half_i_pi), &ctx);
        println!("exp(iπ/2) evaluates to: {:?}", result);
        println!("expected i = {:?}", QI::I);
    }

    // Class 2: Pythagorean-depth — identity needs sin²+cos²=1 as a sub-lemma

    #[test] fn gap_cos_double_alt() {
        // cos(2x) = 1 - 2sin²(x)  — needs Pythagorean to relate to cos²-sin²
        println!("cos(2x) eq 1-2sin²: {}", seq(
            &Eml::cos(Eml::add(x(), x())),
            &Eml::sub(Eml::One, Eml::mul(Eml::two(), Eml::sqr(Eml::sin(x())))),
        ));
    }

    #[test] fn gap_sec_squared() {
        // 1/cos²(x) = 1 + tan²(x)  — direct Pythagorean rearrangement
        let sec_sq = Eml::inv(Eml::sqr(Eml::cos(x())));
        let one_plus_tan_sq = Eml::add(Eml::One, Eml::sqr(Eml::tan(x())));
        println!("1/cos² eq 1+tan²: {}", seq(&sec_sq, &one_plus_tan_sq));
    }

    // Class 3: expand_ac_term only handles exponents with exactly 2 terms,
    // one of which is ln(nat). 3-term exponents or non-nat scalars fall through.

    #[test] fn gap_exp_i_pi_over_2() {
        // Ground: exp(ln(-1)/2) = i  — since ln(-1) = iπ, half gives i
        let exp_ln_neg1_half = Eml::exp(Eml::mul(Eml::ln(Eml::neg_one()), Eml::half()));
        let ctx = GroundCtx::new();
        let result = ground_eval(&normalize(&exp_ln_neg1_half), &ctx);
        println!("exp(ln(-1)/2) = {:?}  (expected i = {:?})", result, QI::I);
    }

    // Class 4: log-product in reverse — factoring out of ln

    #[test] fn gap_rational_function_cancel() {
        // (x² - 1)/(x - 1) = x + 1  — requires polynomial factoring
        let lhs = Eml::div(Eml::sub(Eml::sqr(x()), Eml::One), Eml::sub(x(), Eml::One));
        println!("(x²-1)/(x-1) eq x+1: {}", eq(&lhs, &Eml::add(x(), Eml::One)));
    }

    #[test] fn gap_sin_cos_shift() {
        // sin(x) = cos(x - π/2)  — phase shift identity
        let cos_shifted = Eml::cos(Eml::sub(x(), Eml::mul(Eml::pi(), Eml::half())));
        println!("sin(x) eq cos(x-π/2): {}", seq(&Eml::sin(x()), &cos_shifted));
    }

    // ── Extended ±∞ model ─────────────────────────────────────────────────
    //
    // These tests verify the extended arithmetic where ln(0) = -∞ and
    // exp(-∞) = 0. The key property: the normalizer is CONSISTENT — no
    // expression normalizes to two different values via different paths.
    // The single indeterminate form -∞ + ∞ corresponds to classical
    // indeterminate forms (0·∞, 0/0, ∞-∞, etc.).

    #[test] fn ext_ln_zero_is_neg_inf() {
        assert_eq!(normalize(&Eml::ln(Eml::zero())), Eml::NegInf);
    }

    #[test] fn ext_exp_neg_inf_is_zero() {
        assert!(eq(&Eml::exp(Eml::NegInf), &Eml::zero()));
    }

    #[test] fn ext_exp_pos_inf_is_pos_inf() {
        assert_eq!(normalize(&Eml::exp(Eml::PosInf)), Eml::PosInf);
    }

    #[test] fn ext_inv_zero_is_pos_inf() {
        assert_eq!(normalize(&Eml::inv(Eml::zero())), Eml::PosInf);
    }

    #[test] fn ext_inv_pos_inf_is_zero() {
        assert!(eq(&Eml::inv(Eml::PosInf), &Eml::zero()));
    }

    #[test] fn ext_inv_neg_inf_is_zero() {
        assert!(eq(&Eml::inv(Eml::NegInf), &Eml::zero()));
    }

    #[test] fn ext_neg_neg_inf_is_pos_inf() {
        assert_eq!(normalize(&Eml::neg(Eml::NegInf)), Eml::PosInf);
    }

    #[test] fn ext_neg_pos_inf_is_neg_inf() {
        assert_eq!(normalize(&Eml::neg(Eml::PosInf)), Eml::NegInf);
    }

    #[test] fn ext_neg_inf_absorption() {
        // -∞ + x = -∞ for finite x
        assert_eq!(normalize(&Eml::add(Eml::NegInf, x())), Eml::NegInf);
        assert_eq!(normalize(&Eml::add(x(), Eml::NegInf)), Eml::NegInf);
    }

    #[test] fn ext_pos_inf_absorption() {
        // +∞ + x = +∞ for finite x
        assert_eq!(normalize(&Eml::add(Eml::PosInf, x())), Eml::PosInf);
        assert_eq!(normalize(&Eml::add(x(), Eml::PosInf)), Eml::PosInf);
    }

    #[test] fn ext_zero_times_finite_is_zero() {
        // 0 * x = 0 still works (x is finite)
        assert!(eq(&Eml::mul(Eml::zero(), x()), &Eml::zero()));
        assert!(eq(&Eml::mul(x(), Eml::zero()), &Eml::zero()));
    }

    #[test] fn ext_zero_times_inv_zero_indeterminate() {
        // 0 * (1/0) is indeterminate — NOT 0, NOT 1
        let result = normalize(&Eml::mul(Eml::zero(), Eml::inv(Eml::zero())));
        assert_ne!(result, normalize(&Eml::zero()));
        assert_ne!(result, Eml::One);
    }

    #[test] fn ext_both_paths_agree() {
        // The original inconsistency: 0*(1/0) via mul vs via exp(ln(0)+(-ln(0)))
        // Both must give the same result now.
        let via_mul = normalize(&Eml::mul(Eml::zero(), Eml::inv(Eml::zero())));
        let via_exp = normalize(&Eml::exp(Eml::add(
            Eml::ln(Eml::zero()), Eml::neg(Eml::ln(Eml::zero())))));
        assert_eq!(via_mul, via_exp);
    }

    #[test] fn ext_sub_self_inf_indeterminate() {
        // -∞ - (-∞) is indeterminate (= -∞ + ∞)
        let result = normalize(&Eml::sub(Eml::NegInf, Eml::NegInf));
        assert_ne!(result, normalize(&Eml::zero()));
    }

    // KB critical pairs: every overlap between extended rules and existing rules joins

    #[test] fn kb_exp_ln_zero() {
        // exp(ln(0)): via exp_ln → 0, via ln_zero+exp_neg_inf → 0
        assert!(eq(&Eml::exp(Eml::ln(Eml::zero())), &Eml::zero()));
    }

    #[test] fn kb_ln_exp_neg_inf() {
        // ln(exp(-∞)): via ln_exp → -∞, via exp_neg_inf+ln_zero → -∞
        assert_eq!(normalize(&Eml::ln(Eml::exp(Eml::NegInf))), Eml::NegInf);
    }

    #[test] fn kb_ln_mul_zero_l() {
        // ln(0*x): via mul_zero+ln → -∞, via ln_mul+absorption → -∞
        assert_eq!(normalize(&Eml::ln(Eml::mul(Eml::zero(), x()))), Eml::NegInf);
    }

    #[test] fn kb_ln_mul_zero_r() {
        assert_eq!(normalize(&Eml::ln(Eml::mul(x(), Eml::zero()))), Eml::NegInf);
    }

    #[test] fn kb_exp_add_neg_inf() {
        // exp(-∞ + x) = exp(-∞) = 0 (via absorption)
        assert!(eq(&Eml::exp(Eml::add(Eml::NegInf, Eml::ln(x()))), &Eml::zero()));
    }

    #[test] fn kb_inv_inv_zero() {
        // inv(inv(0)) = inv(+∞) = 0
        assert!(eq(&Eml::inv(Eml::inv(Eml::zero())), &Eml::zero()));
    }

    #[test] fn kb_neg_neg_neg_inf() {
        // neg(neg(-∞)) = -∞
        assert_eq!(normalize(&Eml::neg(Eml::neg(Eml::NegInf))), Eml::NegInf);
    }

    #[test] fn kb_indirect_zero_consistent() {
        // (x-x)*(1/(x-x)) = 0*(1/0) — indirect zero gives same indeterminate
        let xx = Eml::sub(x(), x());
        let indirect = normalize(&Eml::mul(xx.clone(), Eml::inv(xx)));
        let direct = normalize(&Eml::mul(Eml::zero(), Eml::inv(Eml::zero())));
        assert_eq!(indirect, direct);
    }

    #[test] fn kb_zero_zero_is_zero() {
        assert!(eq(&Eml::mul(Eml::zero(), Eml::zero()), &Eml::zero()));
    }

    #[test] fn kb_basics_still_work() {
        assert!(eq(&Eml::exp(Eml::zero()), &Eml::One));
        assert!(eq(&Eml::ln(Eml::One), &Eml::zero()));
        assert!(eq(&Eml::add(Eml::zero(), Eml::zero()), &Eml::zero()));
    }
}
