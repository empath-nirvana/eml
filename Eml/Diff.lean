/-
  EML Differentiation
  ====================
  Differentiation as a total, mechanical tree → tree function.

  The single rule:
    d/dx eml(A, B) = exp(A) · A' − B' / B

  This is the ONLY differentiation rule needed. Since every elementary
  function is an EML tree, this one rule (plus base cases) differentiates
  everything: polynomials, trig, exponentials, logarithms, all of it.

  Compare with traditional symbolic differentiation which needs a
  separate rule for each function (sin, cos, tan, arcsin, ...).
-/

import Eml.Constructors

namespace Eml

/-- Differentiate an EML tree with respect to variable `x`.

    Base cases:
      D(1)   = 0
      D(xₙ)  = 1 if n = x, else 0

    Recursive case:
      D(eml(A, B)) = exp(A)·D(A) − D(B)·(1/B)

    This is purely structural. No exp or ln is evaluated.
    The output is always a valid EML tree. -/
def diff (t : Eml) (x : Nat := 0) : Eml :=
  match t with
  | one   => zero
  | var n => if n == x then one else zero
  | node a b =>
    let da := diff a x
    let db := diff b x
    -- exp(A) · D(A) − D(B) · (1/B)
    sub' (mul' (exp' a) da) (mul' db (inv' b))

/-- Second derivative. -/
def diff2 (t : Eml) (x : Nat := 0) : Eml :=
  diff (diff t x) x

/-- n-th derivative. -/
def diffN (t : Eml) (n : Nat) (x : Nat := 0) : Eml :=
  match n with
  | 0     => t
  | n + 1 => diff (diffN t n x) x

/-- Partial derivative with respect to variable `x`. Same as diff,
    but named for clarity with multivariate expressions. -/
abbrev pdiff := diff

/-- Gradient: partial derivatives with respect to variables 0..n-1. -/
def gradient (t : Eml) (nvars : Nat) : List Eml :=
  List.range nvars |>.map (diff t ·)

/-! ## Basic theorems about differentiation -/

/-- Derivative of the constant 1 is zero. -/
theorem diff_one (x : Nat) : diff one x = zero := by
  simp [diff]

/-- Derivative of variable x with respect to x is 1. -/
theorem diff_var_self (x : Nat) : diff (var x) x = one := by
  simp [diff]

/-- Derivative of variable y ≠ x with respect to x is zero. -/
theorem diff_var_other {x y : Nat} (h : x ≠ y) : diff (var y) x = zero := by
  simp [diff]
  omega

/-- Derivative of e = eml(1,1) is zero (e is a constant). -/
theorem diff_e (x : Nat) : diff e' x = sub' (mul' (exp' one) zero) (mul' zero (inv' one)) := by
  simp [diff, e']

/-- Derivative of exp(xₙ) with respect to xₙ.
    D(eml(xₙ, 1)) = exp(xₙ)·1 − 0·(1/1)
    which should simplify to exp(xₙ) under rewrite rules. -/
theorem diff_exp_var (n : Nat) :
    diff (exp' (var n)) n =
    sub' (mul' (exp' (var n)) one) (mul' zero (inv' one)) := by
  simp [diff, exp']

/-! ## Size analysis -/

/-- The derivative always produces a tree with the same structure at the top:
    it's always a sub'(mul'(...), mul'(...)). -/
theorem diff_node_shape (a b : Eml) (x : Nat) :
    ∃ p q, diff (node a b) x = sub' (mul' (exp' a) p) (mul' q (inv' b)) := by
  exact ⟨diff a x, diff b x, rfl⟩

/-! ## Examples -/

-- d/dx exp(x) -- should be exp(x) after simplification
#eval (diff (exp' (var 0))).leaves

-- d/dx ln(x)
#eval (diff (ln' (var 0))).leaves

-- d/dx (x * x) -- derivative of x²
#eval (diff (mul' (var 0) (var 0))).leaves

end Eml
