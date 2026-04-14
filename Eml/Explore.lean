/-
  EML Exploration
  ===============
  Interactive exploration: pretty printing, differentiation tests,
  and verification that the rewrite system works.

  Current status of the simplifier:
  - exp(ln(x)) → x       ✓
  - ln(exp(x)) → x       ✓
  - exp(0) → 1           ✓  (via exp(ln(1)) → 1)
  - d/dx exp(x) = exp(x) ✓  (62 leaves → 2 leaves!)
  - d/dx ln(x) = 1/x     ✗  needs mul/sub identity rules at tree level
  - d/dx e = 0            ✗  needs mul-by-zero at tree level

  The gap reveals the core research question: what is the minimal
  set of tree rewrite rules needed for a useful EML calculus?
-/

import Eml.Diff
import Eml.Rewrite

namespace Eml

/-! ## Pretty printer -/

/-- Convert an EML tree to a human-readable string using the
    derived operation names when patterns are recognized. -/
partial def pretty : Eml → String
  | one   => "1"
  | var n => s!"x{n}"
  | t =>
    match t.isExp? with
    | some z => s!"exp({pretty z})"
    | none =>
    match t.isLn? with
    | some z => s!"ln({pretty z})"
    | none =>
    match t.isSub? with
    | some (a, b) => s!"({pretty a} - {pretty b})"
    | none =>
    match t with
    | node l r => s!"eml({pretty l}, {pretty r})"
    | _ => "?"

instance : ToString Eml where toString := pretty

/-! ## Leaf counts of core constructions -/

#eval s!"exp(x):  {(exp' (var 0)).leaves} leaves"
#eval s!"ln(x):   {(ln' (var 0)).leaves} leaves"
#eval s!"zero:    {zero.leaves} leaves"
#eval s!"e:       {e'.leaves} leaves"
#eval s!"x-y:     {(sub' (var 0) (var 1)).leaves} leaves"
#eval s!"x+y:     {(add' (var 0) (var 1)).leaves} leaves"
#eval s!"x*y:     {(mul' (var 0) (var 1)).leaves} leaves"
#eval s!"1/x:     {(inv' (var 0)).leaves} leaves"

/-! ## Differentiation results -/

-- d/dx exp(x) = exp(x)  ✓
#eval s!"d/dx exp(x)    = {simplify (diff (exp' (var 0)))}"
#eval s!"  matches exp: {simplify (diff (exp' (var 0))) == exp' (var 0)}"
#eval s!"  {(diff (exp' (var 0))).leaves} leaves → {(simplify (diff (exp' (var 0)))).leaves}"

-- d/dx ln(x) -- needs more rules to reach 1/x
#eval s!"d/dx ln(x)     leaves: {(diff (ln' (var 0))).leaves} → {(simplify (diff (ln' (var 0)))).leaves}"

-- d/dx 1 = 0  ✓  (returns zero = ln(1))
#eval s!"d/dx 1         = {diff one}"

-- d/dx x = 1  ✓
#eval s!"d/dx x         = {diff (var 0)}"

/-! ## Cancellation laws -/

#eval s!"exp(ln(x))  → {simplify (exp' (ln' (var 0)))}"
#eval s!"ln(exp(x))  → {simplify (ln' (exp' (var 0)))}"
#eval s!"exp(0)      → {simplify (exp' zero)}"

end Eml
