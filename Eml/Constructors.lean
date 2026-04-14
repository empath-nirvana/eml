/-
  EML Tree Constructors
  =====================
  Derived operations as tree-grafting templates.

  Each constructor builds a specific EML subtree pattern that, if evaluated,
  would compute the named operation. But we never evaluate -- these are
  purely structural definitions.

  From the EML compiler (SI Section 2.1):
    exp(z) ↦ eml(z, 1)
    ln(z)  ↦ eml(1, exp(eml(1, z)))
    x - y  ↦ eml(ln(x), exp(y))
    -z     ↦ (ln 1) - z
    x + y  ↦ x - (-y)
    1/z    ↦ exp(-ln z)
    x · y  ↦ exp(ln x + ln y)
-/

import Eml.Basic

namespace Eml

/-! ## Primitive constructors (depth 1 from eml) -/

/-- exp(z) = eml(z, 1) -/
def exp' (z : Eml) : Eml := node z one

/-- ln(z) = eml(1, exp(eml(1, z))) = eml(1, eml(eml(1, z), 1)) -/
def ln' (z : Eml) : Eml := node one (exp' (node one z))

/-! ## Constants -/

/-- e = eml(1, 1) = exp(1) - ln(1) = e - 0 = e -/
def e' : Eml := node one one

/-- 0 = ln(1) -/
def zero : Eml := ln' one

/-! ## Arithmetic constructors -/

/-- x - y = eml(ln(x), exp(y)) -/
def sub' (x y : Eml) : Eml := node (ln' x) (exp' y)

/-- -z = 0 - z -/
def neg' (z : Eml) : Eml := sub' zero z

/-- x + y = x - (-y) -/
def add' (x y : Eml) : Eml := sub' x (neg' y)

/-- 1/z = exp(-ln(z)) -/
def inv' (z : Eml) : Eml := exp' (neg' (ln' z))

/-- x * y = exp(ln(x) + ln(y)) -/
def mul' (x y : Eml) : Eml := exp' (add' (ln' x) (ln' y))

/-- x / y = x * (1/y) -/
def div' (x y : Eml) : Eml := mul' x (inv' y)

/-! ## Derived constants -/

/-- -1 = 0 - 1 -/
def negOne : Eml := sub' zero one

/-- 2 = 1 - (-1) -/
def two : Eml := sub' one negOne

/-- 1/2 -/
def half : Eml := inv' two

/-! ## Higher functions -/

/-- x² = exp(2 · ln(x)) ... or more directly, x * x -/
def sqr (z : Eml) : Eml := mul' z z

/-- √x = exp(ln(x) / 2) -/
def sqrt' (z : Eml) : Eml := exp' (mul' (ln' z) half)

/-- xʸ = exp(y · ln(x)) -/
def pow' (x y : Eml) : Eml := exp' (mul' y (ln' x))

/-! ## Transcendental constants -/

/-- π = √(-(ln(-1))²)
    Since ln(-1) = iπ on principal branch, (ln(-1))² = -π², so -(ln(-1))² = π². -/
def pi' : Eml := sqrt' (neg' (sqr (ln' negOne)))

/-- i = -ln(-1)/π -/
def i' : Eml := neg' (div' (ln' negOne) pi')

/-! ## Trigonometric functions (via Euler's formula) -/

/-- cos(z) = (exp(iz) + exp(-iz)) / 2 ... as tree template -/
def cos' (z : Eml) : Eml :=
  mul' (add' (exp' (mul' i' z)) (exp' (neg' (mul' i' z)))) half

/-- sin(z) = (exp(iz) - exp(-iz)) / (2i) -/
def sin' (z : Eml) : Eml :=
  div' (sub' (exp' (mul' i' z)) (exp' (neg' (mul' i' z)))) (mul' two i')

/-! ## Leaf counts of key constructions -/

-- These can be checked with #eval

#eval e'.leaves        -- should be small
#eval zero.leaves      -- = ln(1)
#eval negOne.leaves
#eval two.leaves
#eval (exp' (var 0)).leaves   -- exp(x): 2 leaves
#eval (ln' (var 0)).leaves    -- ln(x): 4 leaves

end Eml
