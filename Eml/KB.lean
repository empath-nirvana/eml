/-
  EML Knuth-Bendix Completion Analysis
  =====================================
  Computable exploration of confluence properties via critical pair analysis.

  This is an exploration tool — all `partial def` / `def`, no theorems.
  It computes critical pairs between rewrite rules, normalizes both sides,
  and reports which pairs are joinable vs unjoinable.

  Key questions:
  - Which rule overlaps create non-confluence?
  - Are they all related to partiality (0/0), or structural?
  - What new rules would a completion procedure propose?
-/

import Eml.Rewrite

namespace Eml

/-! ## Term comparison -/

/-- Lexicographic structural ordering. one < var < node. -/
def cmp : Eml → Eml → Ordering
  | .one, .one => .eq
  | .one, _ => .lt
  | _, .one => .gt
  | .var m, .var n => compare m n
  | .var _, .node _ _ => .lt
  | .node _ _, .var _ => .gt
  | .node l1 r1, .node l2 r2 =>
    match cmp l1 l2 with
    | .eq => cmp r1 r2
    | ord => ord

/-! ## Substitution infrastructure -/

abbrev KBSubst := List (Nat × Eml)

def applyKBSubst (σ : KBSubst) : Eml → Eml
  | .one => .one
  | .var n => σ.lookup n |>.getD (.var n)
  | .node l r => .node (applyKBSubst σ l) (applyKBSubst σ r)

def occursIn (n : Nat) : Eml → Bool
  | .one => false
  | .var m => m == n
  | .node l r => occursIn n l || occursIn n r

def shiftVars : Eml → Nat → Eml
  | .one, _ => .one
  | .var n, k => .var (n + k)
  | .node l r, k => .node (shiftVars l k) (shiftVars r k)

/-! ## Matching and unification -/

/-- Extend substitution with n ↦ t, composing into existing bindings. -/
private def extendSubst (σ : KBSubst) (n : Nat) (t : Eml) : KBSubst :=
  (n, t) :: σ.map fun (k, v) => (k, applyKBSubst [(n, t)] v)

/-- One-way matching: find σ with `pattern[σ] = target`.
    Only pattern variables are bound; target is rigid. -/
def matchTerm (pattern target : Eml) (σ : KBSubst) : Option KBSubst :=
  match pattern, target with
  | .var n, t =>
    match σ.lookup n with
    | some t' => if t' == t then some σ else none
    | none => some ((n, t) :: σ)
  | .one, .one => some σ
  | .node l1 r1, .node l2 r2 =>
    match matchTerm l1 l2 σ with
    | some σ' => matchTerm r1 r2 σ'
    | none => none
  | _, _ => none

/-- Most general unifier. -/
partial def unify (s t : Eml) (σ : KBSubst := []) : Option KBSubst :=
  let s' := applyKBSubst σ s
  let t' := applyKBSubst σ t
  match s', t' with
  | .one, .one => some σ
  | .var n, .var m =>
    if n == m then some σ else some (extendSubst σ n (.var m))
  | .var n, t' =>
    if occursIn n t' then none else some (extendSubst σ n t')
  | s', .var n =>
    if occursIn n s' then none else some (extendSubst σ n s')
  | .node l1 r1, .node l2 r2 => do
    let σ' ← unify l1 l2 σ
    unify r1 r2 σ'
  | _, _ => none

/-! ## Pattern recognizers -/

private def kbIsNeg? (t : Eml) : Option Eml :=
  match t.isSub? with
  | some (z, b) => if isZero z then some b else none
  | none => none

private def kbIsAdd? (t : Eml) : Option (Eml × Eml) :=
  match t.isSub? with
  | some (a, negB) =>
    match kbIsNeg? negB with
    | some b => some (a, b)
    | none => none
  | none => none

private def kbIsInv? (t : Eml) : Option Eml :=
  match t.isExp? with
  | some inner =>
    match kbIsNeg? inner with
    | some lnZ =>
      match lnZ.isLn? with
      | some z => some z
      | none => none
    | none => none
  | none => none

/-! ## Pretty printer -/

partial def pp : Eml → String
  | .one => "1"
  | .var n => s!"x{n}"
  | t =>
    if t == zero then "0"
    else
    match t.isMul? with
    | some (a, b) => s!"({pp a} · {pp b})"
    | none =>
    match kbIsInv? t with
    | some z => s!"(1/{pp z})"
    | none =>
    match kbIsAdd? t with
    | some (a, b) => s!"({pp a} + {pp b})"
    | none =>
    match kbIsNeg? t with
    | some z => s!"(-{pp z})"
    | none =>
    match t.isSub? with
    | some (a, b) => s!"({pp a} - {pp b})"
    | none =>
    match t.isExp? with
    | some z => s!"exp({pp z})"
    | none =>
    match t.isLn? with
    | some z => s!"ln({pp z})"
    | none =>
    match t with
    | .node l r => s!"eml({pp l}, {pp r})"
    | _ => "?"

/-! ## Rules as data -/

structure KBRule where
  name : String
  lhs  : Eml
  rhs  : Eml

/-- The 17 oriented rewrite rules (excluding add_comm, congruence, and ln_one).
    ln_one is excluded because `ln'(one) = zero` definitionally — the LHS and RHS
    are the same tree, making it a no-op that causes the normalizer to loop. -/
def kbRules : List KBRule :=
  let x := var 0; let y := var 1; let z := var 2
  [ { name := "exp_ln",     lhs := exp' (ln' x),       rhs := x }
  , { name := "ln_exp",     lhs := ln' (exp' x),       rhs := x }
  , { name := "sub_zero",   lhs := sub' x zero,        rhs := x }
  , { name := "sub_self",   lhs := sub' x x,           rhs := zero }
  , { name := "add_zero_l", lhs := add' zero x,        rhs := x }
  , { name := "add_zero_r", lhs := add' x zero,        rhs := x }
  , { name := "mul_one_l",  lhs := mul' one x,         rhs := x }
  , { name := "mul_one_r",  lhs := mul' x one,         rhs := x }
  , { name := "mul_zero_l", lhs := mul' zero x,        rhs := zero }
  , { name := "mul_zero_r", lhs := mul' x zero,        rhs := zero }
  , { name := "neg_neg",    lhs := neg' (neg' x),      rhs := x }
  , { name := "inv_inv",    lhs := inv' (inv' x),      rhs := x }
  , { name := "exp_add",    lhs := exp' (add' x y),    rhs := mul' (exp' x) (exp' y) }
  , { name := "ln_mul",     lhs := ln' (mul' x y),     rhs := add' (ln' x) (ln' y) }
  , { name := "mul_add",    lhs := mul' x (add' y z),  rhs := add' (mul' x y) (mul' x z) }
  , { name := "exp_zero",   lhs := exp' zero,          rhs := one }
  -- add_assoc excluded: handled by AC normalization (like add_comm)
  -- KB completion rules: close the sub_self × exp_ln/ln_exp interaction
  , { name := "cancel_exp_ln_sub",  lhs := node (ln' (ln' x)) x,       rhs := zero }
  , { name := "cancel_ln_exp_sub",  lhs := node x (exp' (exp' x)),      rhs := zero }
  ]

/-! ## Subterm positions -/

abbrev Pos := List Bool   -- true = left, false = right

def subtermAt : Eml → Pos → Option Eml
  | t, [] => some t
  | .node l _, true :: rest => subtermAt l rest
  | .node _ r, false :: rest => subtermAt r rest
  | _, _ => none

def replaceAt : Eml → Pos → Eml → Option Eml
  | _, [], s => some s
  | .node l r, true :: rest, s => do
    let l' ← replaceAt l rest s
    some (.node l' r)
  | .node l r, false :: rest, s => do
    let r' ← replaceAt r rest s
    some (.node l r')
  | _, _, _ => none

/-- All node (non-leaf) positions in a tree. -/
def nodePositions : Eml → List Pos
  | .one | .var _ => []
  | .node l r =>
    [[]] ++
    (nodePositions l).map (true :: ·) ++
    (nodePositions r).map (false :: ·)

/-! ## Critical pair computation -/

structure CriticalPair where
  rule1  : String       -- rule applied at root
  rule2  : String       -- rule applied at overlap position
  pos    : Pos
  source : Eml          -- the unified term
  lhs    : Eml          -- result of rule1
  rhs    : Eml          -- result of rule2

/-- Compute critical pairs: overlap rule2 into subterms of rule1's LHS. -/
def criticalPairsOf (r1 r2 : KBRule) : List CriticalPair :=
  let offset := 100   -- all rules use vars 0-2, so 100 is safe
  let r2lhs := shiftVars r2.lhs offset
  let r2rhs := shiftVars r2.rhs offset
  let positions := nodePositions r1.lhs
  positions.filterMap fun pos => do
    -- Skip trivial root self-overlap
    if pos.isEmpty && r1.name == r2.name then .none
    else
    let sub ← subtermAt r1.lhs pos
    let σ ← unify sub r2lhs
    let source := applyKBSubst σ r1.lhs
    let cpLeft := applyKBSubst σ r1.rhs
    let cpRight ← replaceAt source pos (applyKBSubst σ r2rhs)
    .some { rule1 := r1.name, rule2 := r2.name
            pos, source, lhs := cpLeft, rhs := cpRight }

def allCriticalPairs (rules : List KBRule := kbRules) : List CriticalPair :=
  rules.foldl (fun acc r1 =>
    rules.foldl (fun acc' r2 =>
      acc' ++ criticalPairsOf r1 r2
    ) acc
  ) []

/-! ## Normalization -/

/-- Flatten add' into summands. -/
partial def flattenAdd (t : Eml) : List Eml :=
  match kbIsAdd? t with
  | some (a, b) => flattenAdd a ++ flattenAdd b
  | none => [t]

def buildAdd : List Eml → Eml
  | [] => zero
  | [t] => t
  | t :: rest => add' t (buildAdd rest)

private def insertSorted (x : Eml) : List Eml → List Eml
  | [] => [x]
  | y :: ys => if cmp x y != .gt then x :: y :: ys
               else y :: insertSorted x ys

private def sortTerms : List Eml → List Eml
  | [] => []
  | x :: xs => insertSorted x (sortTerms xs)

/-- AC-normalize addition: flatten, sort, rebuild right-associated. -/
partial def acNormAdd (t : Eml) : Eml :=
  match kbIsAdd? t with
  | some _ =>
    let terms := flattenAdd t
    if terms.length ≤ 1 then t
    else buildAdd (sortTerms terms)
  | none => t

/-- Bottom-up AC normalization of all subterms. -/
partial def acNorm : Eml → Eml
  | .one => .one
  | .var n => .var n
  | .node l r =>
    let t := Eml.node (acNorm l) (acNorm r)
    acNormAdd t

/-- Apply KBO-compatible rules at root (derived operation level).
    Excludes exp_add and mul_add — they increase term size and are not
    KBO-compatible.  Includes ln_mul which IS KBO-compatible. -/
partial def kbApplyRoot (t : Eml) : Eml :=
  match t.isMul? with
  | some (a, b) =>
    if isOne a then b
    else if isOne b then a
    else if isZero a || isZero b then zero
    else t
  | none =>
  match kbIsInv? t with
  | some z =>
    match kbIsInv? z with
    | some a => a                                -- inv(inv(a)) → a
    | none => t
  | none =>
  match kbIsAdd? t with
  | some (a, b) =>
    if isZero a then b                           -- 0+x → x
    else if isZero b then a                      -- x+0 → x
    else t
  | none =>
  match kbIsNeg? t with
  | some z =>
    match kbIsNeg? z with
    | some a => a                                -- -(-a) → a
    | none => t
  | none =>
  match t.isSub? with
  | some (a, b) =>
    if a == b then zero                          -- x-x → 0
    else if isZero b then a                      -- x-0 → x
    else t
  | none =>
  match t.isExp? with
  | some z =>
    match z.isLn? with
    | some a => a                                -- exp(ln(a)) → a
    | none =>
    if isZero z then one                         -- exp(0) → 1
    else t
  | none =>
  match t.isLn? with
  | some z =>
    match z.isExp? with
    | some a => a                                -- ln(exp(a)) → a
    | none =>
    if isOne z then zero                         -- ln(1) → 0
    else
    match z.isMul? with
    | some (a, b) => add' (ln' a) (ln' b)        -- ln(a·b) → ln(a)+ln(b)
    | none => t
  | none =>
  -- KB completion rules: partially-cancelled subtractions
  match t with
  | .node l r =>
    -- cancel_exp_ln_sub: node (ln'(ln'(z))) z → zero
    match l.isLn? with
    | some lnz =>
      match lnz.isLn? with
      | some z => if z == r then zero else t
      | none => t
    | none =>
    -- cancel_ln_exp_sub: node z (exp'(exp'(z))) → zero
    match r.isExp? with
    | some er =>
      match er.isExp? with
      | some z => if z == l then zero else t
      | none => t
    | none => t
  | _ => t

/-- One-pass simplification at derived operation level.
    Recognizes the outermost derived operation, recursively simplifies
    its arguments, rebuilds in canonical form, then applies rules at root.
    This avoids the "encoding boundary" problem where raw tree-level
    normalization breaks derived operation patterns. -/
partial def kbDeepSimplify : Eml → Eml
  | .one => .one
  | .var n => .var n
  | t =>
    match t.isMul? with
    | some (a, b) =>
      kbApplyRoot (mul' (kbDeepSimplify a) (kbDeepSimplify b))
    | none =>
    match kbIsInv? t with
    | some z => kbApplyRoot (inv' (kbDeepSimplify z))
    | none =>
    match kbIsAdd? t with
    | some (a, b) =>
      kbApplyRoot (add' (kbDeepSimplify a) (kbDeepSimplify b))
    | none =>
    match kbIsNeg? t with
    | some z => kbApplyRoot (neg' (kbDeepSimplify z))
    | none =>
    match t.isSub? with
    | some (a, b) =>
      kbApplyRoot (sub' (kbDeepSimplify a) (kbDeepSimplify b))
    | none =>
    match t.isExp? with
    | some z => kbApplyRoot (exp' (kbDeepSimplify z))
    | none =>
    match t.isLn? with
    | some z => kbApplyRoot (ln' (kbDeepSimplify z))
    | none =>
    -- Raw node: not a recognized derived operation; simplify children then
    -- try KB completion rules for partially-cancelled subtractions
    match t with
    | .node l r =>
      let l' := kbDeepSimplify l
      let r' := kbDeepSimplify r
      kbApplyRoot (.node l' r')
    | _ => t

/-- Normalize via iterated derived-op simplification + AC normalization. -/
partial def kbNormalize (t : Eml) (fuel : Nat := 50) : Eml :=
  if fuel == 0 then t
  else
    let t' := kbDeepSimplify t
    let t' := acNorm t'
    if t' == t then t
    else kbNormalize t' (fuel - 1)

/-! ## Analysis -/

def isJoinable (cp : CriticalPair) : Bool :=
  kbNormalize cp.lhs == kbNormalize cp.rhs

/-- Classify whether a term involves ln(0) — a partiality marker.
    Recurses through all subterms to catch nested occurrences like ln(ln(0)). -/
partial def involvesLnZero : Eml → Bool
  | .one => false
  | .var _ => false
  | t =>
    (match t.isLn? with | some z => isZero z | none => false) ||
    (match t with | .node l r => involvesLnZero l || involvesLnZero r | _ => false)

/-- Check if a critical pair's RHS is a raw eml() node (encoding boundary issue). -/
def isRawNode (t : Eml) : Bool :=
  match t with
  | .node _ _ =>
    t.isExp?.isNone && t.isLn?.isNone && t.isSub?.isNone &&
    t.isMul?.isNone && !isZero t
  | _ => false

/-- Check if a rule is KBO-compatible (LHS has strictly more leaves than RHS,
    or equal leaves with LHS > RHS lexicographically). -/
def isKBOCompat (r : KBRule) : Bool :=
  r.lhs.leaves > r.rhs.leaves ||
  (r.lhs.leaves == r.rhs.leaves && cmp r.lhs r.rhs == .gt)

/-- Full critical pair analysis with classification. -/
def kbAnalyze : IO Unit := do
  let rules := kbRules
  IO.println "EML Knuth-Bendix Critical Pair Analysis"
  IO.println "======================================="
  IO.println ""

  -- KBO compatibility check
  IO.println "--- Term ordering (KBO with leaf-count weight) ---"
  for r in rules do
    let compat := if isKBOCompat r then "OK" else "FAIL"
    let wl := r.lhs.leaves
    let wr := r.rhs.leaves
    IO.println s!"  {r.name}: w({wl}) -> w({wr})  [{compat}]"
  IO.println ""

  let kboFail := rules.filter (!isKBOCompat ·)
  if kboFail.isEmpty then
    IO.println "All rules KBO-compatible!"
  else
    IO.println s!"KBO-incompatible rules ({kboFail.length}):"
    for r in kboFail do
      IO.println s!"  {r.name} — RHS is larger than LHS"
    IO.println "  (These rules expand terms; KB completion cannot orient them.)"
  IO.println ""

  -- Critical pairs
  let pairs := allCriticalPairs rules
  IO.println s!"--- Critical pairs ---"
  IO.println s!"Total: {pairs.length}"

  let mut joinCount := 0
  let mut unjoinable : List CriticalPair := []

  for cp in pairs do
    if isJoinable cp then
      joinCount := joinCount + 1
    else
      unjoinable := cp :: unjoinable

  IO.println s!"  Joinable:   {joinCount}"
  IO.println s!"  Unjoinable: {unjoinable.length}"
  IO.println ""

  if unjoinable.isEmpty then
    IO.println "All critical pairs joinable!"
    IO.println "System is locally confluent (modulo AC)."
  else
    -- Classify unjoinable pairs
    let mut partiality := 0    -- involves ln(0)
    let mut boundary := 0      -- produces raw eml() nodes
    let mut structural := 0    -- different normal forms, no partiality
    for cp in unjoinable do
      let nL := kbNormalize cp.lhs
      let nR := kbNormalize cp.rhs
      if involvesLnZero nL || involvesLnZero nR ||
         involvesLnZero cp.source || involvesLnZero cp.lhs || involvesLnZero cp.rhs then
        partiality := partiality + 1
      else if isRawNode nL || isRawNode nR then
        boundary := boundary + 1
      else
        structural := structural + 1

    IO.println "--- Classification of unjoinable pairs ---"
    IO.println s!"  Partiality (involves ln(0)):     {partiality}"
    IO.println s!"  Encoding boundary (raw nodes):   {boundary}"
    IO.println s!"  Structural (genuine):            {structural}"
    IO.println ""

    IO.println "--- Encoding boundary pairs ---"
    IO.println ""
    for cp in unjoinable.reverse do
      let nL := kbNormalize cp.lhs
      let nR := kbNormalize cp.rhs
      let isPartial := involvesLnZero nL || involvesLnZero nR ||
                     involvesLnZero cp.source || involvesLnZero cp.lhs || involvesLnZero cp.rhs
      if !isPartial && (isRawNode nL || isRawNode nR) then
        IO.println s!"  {cp.rule1} x {cp.rule2}"
        IO.println s!"    source:      {pp cp.source}"
        IO.println s!"    LHS normal:  {pp nL}"
        IO.println s!"    RHS normal:  {pp nR}"
        IO.println ""

    IO.println "--- Sample unjoinable pairs (structural only) ---"
    IO.println ""
    let mut shown := 0
    for cp in unjoinable.reverse do
      if shown >= 10 then break
      let nL := kbNormalize cp.lhs
      let nR := kbNormalize cp.rhs
      let isPartial := involvesLnZero nL || involvesLnZero nR ||
                     involvesLnZero cp.source || involvesLnZero cp.lhs || involvesLnZero cp.rhs
      if !isPartial && !isRawNode nL && !isRawNode nR then
        IO.println s!"  {cp.rule1} x {cp.rule2}"
        IO.println s!"    source:      {pp cp.source}"
        IO.println s!"    LHS normal:  {pp nL}"
        IO.println s!"    RHS normal:  {pp nR}"
        IO.println ""
        shown := shown + 1

#eval kbAnalyze

end Eml
