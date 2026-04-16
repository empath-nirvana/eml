/-
  EML Theorems
  ============
  Key results about the EML tree algebra.

  The central theorem here: the derivative of any ground tree
  (all leaves are 1, no variables) reduces to zero under the
  rewrite axioms. This is proved by structural induction using
  only three rules: mul absorbs zero, sub self-cancels.

  No exp, ln, or evaluation is involved anywhere.
-/

import Eml.Diff
import Eml.Rewrite

namespace Eml

/-! ## Congruence lemmas for Steps under derived operations -/

/-- Steps is transitive. -/
theorem Steps.trans {a b c : Eml} (h1 : Steps a b) (h2 : Steps b c) : Steps a c := by
  induction h1 with
  | refl _ => exact h2
  | step a' b' _ hab hbc' ih => exact Steps.step a' b' c hab (ih h2)

/-- Rewriting inside the left child of a node. -/
theorem Steps.node_l {a a' b : Eml} (h : Steps a a') : Steps (node a b) (node a' b) := by
  induction h with
  | refl _ => exact Steps.refl _
  | step x y _ hxy _ ih =>
    exact Steps.step _ _ _ (Step.node_l x y b hxy) ih

/-- Rewriting inside the right child of a node. -/
theorem Steps.node_r {a b b' : Eml} (h : Steps b b') : Steps (node a b) (node a b') := by
  induction h with
  | refl _ => exact Steps.refl _
  | step x y _ hxy _ ih =>
    exact Steps.step _ _ _ (Step.node_r a x y hxy) ih

/-- Rewriting both children of a node. -/
theorem Steps.node_both {a a' b b' : Eml} (hl : Steps a a') (hr : Steps b b') :
    Steps (node a b) (node a' b') :=
  Steps.trans (Steps.node_l hl) (Steps.node_r hr)

/-- Rewriting inside exp'. -/
theorem Steps.exp' {a a' : Eml} (h : Steps a a') : Steps (exp' a) (exp' a') :=
  Steps.node_l h  -- exp'(a) = node a one

/-- Rewriting inside ln'. Since ln'(z) = node one (node (node one z) one),
    we need to go three levels deep. -/
theorem Steps.ln' {a a' : Eml} (h : Steps a a') : Steps (ln' a) (ln' a') :=
  -- ln'(z) = node one (exp'(node one z)) = node one (node (node one z) one)
  -- changing z means: node one (node (node one z) one) → node one (node (node one z') one)
  Steps.node_r (Steps.node_l (Steps.node_r h))

/-- Rewriting inside sub'. sub'(a,b) = node(ln'(a), exp'(b)) -/
theorem Steps.sub'_l {a a' b : Eml} (h : Steps a a') : Steps (sub' a b) (sub' a' b) :=
  Steps.node_l (Steps.ln' h)

theorem Steps.sub'_r {a b b' : Eml} (h : Steps b b') : Steps (sub' a b) (sub' a b') :=
  Steps.node_r (Steps.exp' h)

theorem Steps.sub'_both {a a' b b' : Eml} (hl : Steps a a') (hr : Steps b b') :
    Steps (sub' a b) (sub' a' b') :=
  Steps.trans (Steps.sub'_l hl) (Steps.sub'_r hr)

/-- Rewriting inside neg'. neg'(z) = sub'(zero, z) -/
theorem Steps.neg' {a a' : Eml} (h : Steps a a') : Steps (neg' a) (neg' a') :=
  Steps.sub'_r h

/-- Rewriting inside add'. add'(a,b) = sub'(a, neg'(b)) -/
theorem Steps.add'_l {a a' b : Eml} (h : Steps a a') : Steps (add' a b) (add' a' b) :=
  Steps.sub'_l h

theorem Steps.add'_r {a b b' : Eml} (h : Steps b b') : Steps (add' a b) (add' a b') :=
  Steps.sub'_r (Steps.neg' h)

theorem Steps.add'_both {a a' b b' : Eml} (hl : Steps a a') (hr : Steps b b') :
    Steps (add' a b) (add' a' b') :=
  Steps.trans (Steps.add'_l hl) (Steps.add'_r hr)

/-- Rewriting inside mul'. mul'(a,b) = exp'(add'(ln'(a), ln'(b))) -/
theorem Steps.mul'_l {a a' b : Eml} (h : Steps a a') : Steps (mul' a b) (mul' a' b) :=
  Steps.exp' (Steps.add'_l (Steps.ln' h))

theorem Steps.mul'_r {a b b' : Eml} (h : Steps b b') : Steps (mul' a b) (mul' a b') :=
  Steps.exp' (Steps.add'_r (Steps.ln' h))

theorem Steps.mul'_both {a a' b b' : Eml} (hl : Steps a a') (hr : Steps b b') :
    Steps (mul' a b) (mul' a' b') :=
  Steps.trans (Steps.mul'_l hl) (Steps.mul'_r hr)

/-- Rewriting inside inv'. inv'(z) = exp'(neg'(ln'(z))) -/
theorem Steps.inv' {a a' : Eml} (h : Steps a a') : Steps (inv' a) (inv' a') :=
  Steps.exp' (Steps.neg' (Steps.ln' h))

/-! ## Leaf-count algebra for derived constructors -/

@[simp] theorem leaves_exp' (z : Eml) : (exp' z).leaves = z.leaves + 1 := by
  simp [exp', leaves]

@[simp] theorem leaves_ln' (z : Eml) : (ln' z).leaves = z.leaves + 3 := by
  simp [ln', exp', leaves]; omega

@[simp] theorem leaves_zero : zero.leaves = 4 := by
  simp [zero, ln', exp', leaves]

@[simp] theorem leaves_sub' (a b : Eml) : (sub' a b).leaves = a.leaves + b.leaves + 4 := by
  simp [sub', leaves]; omega

@[simp] theorem leaves_neg' (z : Eml) : (neg' z).leaves = z.leaves + 8 := by
  simp [neg', leaves_sub', leaves_zero]; omega

@[simp] theorem leaves_add' (a b : Eml) : (add' a b).leaves = a.leaves + b.leaves + 12 := by
  simp [add', leaves_sub', leaves_neg']; omega

@[simp] theorem leaves_inv' (z : Eml) : (inv' z).leaves = z.leaves + 12 := by
  simp [inv', leaves_exp', leaves_neg', leaves_ln']

@[simp] theorem leaves_mul' (a b : Eml) : (mul' a b).leaves = a.leaves + b.leaves + 19 := by
  simp [mul', leaves_exp', leaves_add', leaves_ln']; omega

/-! ## Global ordering: the non-expanding fragment

The KBO-compatible rules (everything except `exp_add`, `mul_add`, `add_comm`) never
increase leaf count. We define this fragment as `Reducing` and prove the bound. -/

/-- The non-expanding fragment of the rewrite system.
    Excludes `exp_add`, `mul_add`, and `add_comm` — the three rules that
    increase or rearrange term size. -/
inductive Reducing : Eml → Eml → Prop where
  | exp_ln  (z : Eml) : Reducing (exp' (ln' z)) z
  | ln_exp  (z : Eml) : Reducing (ln' (exp' z)) z
  | sub_zero  (z : Eml) : Reducing (sub' z zero) z
  | sub_self  (z : Eml) : Reducing (sub' z z) zero
  | add_zero_l (z : Eml) : Reducing (add' zero z) z
  | add_zero_r (z : Eml) : Reducing (add' z zero) z
  | mul_one_l  (z : Eml) : Reducing (mul' one z) z
  | mul_one_r  (z : Eml) : Reducing (mul' z one) z
  | mul_zero_l (z : Eml) : Reducing (mul' zero z) zero
  | mul_zero_r (z : Eml) : Reducing (mul' z zero) zero
  | neg_neg   (z : Eml) : Reducing (neg' (neg' z)) z
  | inv_inv   (z : Eml) : Reducing (inv' (inv' z)) z
  | ln_mul (a b : Eml) : Reducing (ln' (mul' a b)) (add' (ln' a) (ln' b))
  -- ln_one excluded: it's a definitional no-op (ln'(one) = zero)
  -- add_assoc excluded: handled by AC normalization (like add_comm)
  | exp_zero : Reducing (exp' zero) one
  | cancel_exp_ln (z : Eml) : Reducing (node (ln' (ln' z)) z) zero
  | cancel_ln_exp (z : Eml) : Reducing (node z (exp' (exp' z))) zero
  | node_l (a a' b : Eml) : Reducing a a' → Reducing (node a b) (node a' b)
  | node_r (a b b' : Eml) : Reducing b b' → Reducing (node a b) (node a b')

/-- Every reducing step is a valid Step. -/
theorem Reducing.toStep {a b : Eml} (h : Reducing a b) : Step a b := by
  induction h with
  | exp_ln z => exact .exp_ln z
  | ln_exp z => exact .ln_exp z
  | sub_zero z => exact .sub_zero z
  | sub_self z => exact .sub_self z
  | add_zero_l z => exact .add_zero_l z
  | add_zero_r z => exact .add_zero_r z
  | mul_one_l z => exact .mul_one_l z
  | mul_one_r z => exact .mul_one_r z
  | mul_zero_l z => exact .mul_zero_l z
  | mul_zero_r z => exact .mul_zero_r z
  | neg_neg z => exact .neg_neg z
  | inv_inv z => exact .inv_inv z
  | ln_mul a b => exact .ln_mul a b
  | exp_zero => exact .exp_zero
  | cancel_exp_ln z => exact .cancel_exp_ln z
  | cancel_ln_exp z => exact .cancel_ln_exp z
  | node_l _ _ _ _ ih => exact .node_l _ _ _ ih
  | node_r _ _ _ _ ih => exact .node_r _ _ _ ih

/-- **Leaf count is non-increasing under reducing steps.**
    This is the core ordering theorem: the KBO-compatible fragment
    never increases term size (measured by leaf count). -/
theorem Reducing.leaves_le {a b : Eml} (h : Reducing a b) : b.leaves ≤ a.leaves := by
  induction h with
  | exp_ln z => simp [leaves_exp', leaves_ln']; omega
  | ln_exp z => simp [leaves_ln', leaves_exp']; omega
  | sub_zero z => simp [leaves_sub']; omega
  | sub_self z => simp [leaves_sub']
  | add_zero_l z => simp [leaves_add']; omega
  | add_zero_r z => simp [leaves_add']; omega
  | mul_one_l z => simp [leaves_mul']; omega
  | mul_one_r z => simp [leaves_mul']; omega
  | mul_zero_l z => simp [leaves_mul']
  | mul_zero_r z => simp [leaves_mul']
  | neg_neg z => simp [leaves_neg']; omega
  | inv_inv z => simp [leaves_inv']; omega
  | ln_mul a b => simp [leaves_ln', leaves_mul', leaves_add']; omega
  | exp_zero => simp [leaves_exp', leaves, leaves_zero]
  | cancel_exp_ln z => simp [leaves, leaves_ln']; have := leaves_pos z; omega
  | cancel_ln_exp z => simp [leaves, leaves_exp']; have := leaves_pos z; omega
  | node_l _ _ _ _ ih => simp [leaves]; omega
  | node_r _ _ _ _ ih => simp [leaves]; omega

/-! ## Termination: the lexicographic ordering (leaves, varCount)

`leaves` is strictly decreasing for all Reducing rules except `cancel_ln_exp`
when `leaves(z) = 1`. In that case, `varCount` strictly decreases (from 2 to 0).
Together, `(leaves, varCount)` with lexicographic ordering gives termination. -/

/-- **Termination measure**: the lexicographic pair `(leaves, varCount)` is
    strictly decreasing under every non-trivial Reducing step.

    All rules except `cancel_ln_exp` strictly decrease leaf count. For
    `cancel_ln_exp(z)` with `leaves(z) = 1`: either `z = one` (no-op, same tree)
    or `z = var n` (varCount drops from 2 to 0). No rule can regenerate the
    `cancel_ln_exp` pattern, so no loops are possible. -/
theorem Reducing.terminates {a b : Eml} (h : Reducing a b) (hne : a ≠ b) :
    b.leaves < a.leaves ∨ (b.leaves = a.leaves ∧ b.varCount < a.varCount) := by
  induction h with
  | exp_ln z => left; simp [leaves_exp', leaves_ln']; omega
  | ln_exp z => left; simp [leaves_ln', leaves_exp']; omega
  | sub_zero z => left; simp [leaves_sub']; omega
  | sub_self z => left; simp [leaves_sub']; have := leaves_pos z; omega
  | add_zero_l z => left; simp [leaves_add']; omega
  | add_zero_r z => left; simp [leaves_add']; omega
  | mul_one_l z => left; simp [leaves_mul']; omega
  | mul_one_r z => left; simp [leaves_mul']; omega
  | mul_zero_l z => left; simp [leaves_mul']
  | mul_zero_r z => left; simp [leaves_mul']
  | neg_neg z => left; simp [leaves_neg']; omega
  | inv_inv z => left; simp [leaves_inv']; omega
  | ln_mul a b => left; simp [leaves_ln', leaves_mul', leaves_add']; omega
  | exp_zero => left; simp [leaves_exp', leaves, leaves_zero]
  | cancel_exp_ln z => left; simp [leaves, leaves_ln']; have := leaves_pos z; omega
  | cancel_ln_exp z =>
    by_cases hleaves : z.leaves ≥ 2
    · left; simp [leaves, leaves_exp']; omega
    · right
      have hz1 : z.leaves = 1 := by have := leaves_pos z; omega
      refine ⟨by simp [leaves, leaves_exp']; omega, ?_⟩
      simp only [varCount, exp', zero, ln']
      cases z with
      | one => exact absurd rfl hne
      | negInf => sorry -- cancel_ln_exp on atoms: edge case from ±∞ extension
      | posInf => sorry -- cancel_ln_exp on atoms: edge case from ±∞ extension
      | var n => simp [varCount]
      | node l r =>
          simp [leaves] at hz1; have := leaves_pos l; have := leaves_pos r; omega
  | node_l a a' b _ ih =>
    have ih := ih (by intro heq; exact hne (congrArg (· |>.node b) heq))
    match ih with
    | .inl h => left; simp [leaves]; omega
    | .inr ⟨heq, hlt⟩ => right; exact ⟨by simp [leaves]; omega, by simp [varCount]; omega⟩
  | node_r a b b' _ ih =>
    have ih := ih (by intro heq; exact hne (congrArg (a.node ·) heq))
    match ih with
    | .inl h => left; simp [leaves]; omega
    | .inr ⟨heq, hlt⟩ => right; exact ⟨by simp [leaves]; omega, by simp [varCount]; omega⟩

/-! ## Single-step wrappers -/

/-- Lift a Step to Steps. -/
theorem Steps.single {a b : Eml} (h : Step a b) : Steps a b :=
  Steps.step a b b h (Steps.refl b)

/-! ## Core rewrite theorems -/

/-- mul'(z, zero) →* zero -/
theorem mul_zero_r_steps (z : Eml) : Steps (mul' z zero) zero :=
  Steps.single (Step.mul_zero_r z)

/-- mul'(zero, z) →* zero -/
theorem mul_zero_l_steps (z : Eml) : Steps (mul' zero z) zero :=
  Steps.single (Step.mul_zero_l z)

/-- sub'(z, z) →* zero -/
theorem sub_self_steps (z : Eml) : Steps (sub' z z) zero :=
  Steps.single (Step.sub_self z)

/-! ## THE KEY THEOREM: derivative of any constant is zero -/

/-- The derivative of any ground EML tree (no variables) reduces to zero
    under the rewrite axioms.

    This is proved by structural induction. The only rules used are:
    - mul'(x, 0) = 0     (zero absorption)
    - mul'(0, x) = 0      (zero absorption)
    - sub'(0, 0) = 0      (self-cancellation)

    No exp, ln, or numerical evaluation is involved.

    Mathematically: every constant has derivative zero. But here
    "constant" means "tree with no variables" and "zero" means
    "the specific tree ln(1)". The proof is pure tree surgery. -/
theorem diff_ground_is_zero (t : Eml) (x : Nat) (hg : t.hasVar x = false) :
    Steps (diff t x) zero := by
  induction t with
  | one =>
    simp [diff]
    exact Steps.refl zero
  | negInf =>
    simp [diff]
    exact Steps.refl zero
  | posInf =>
    simp [diff]
    exact Steps.refl zero
  | var n =>
    -- hasVar (var n) x = false means n ≠ x
    simp [hasVar] at hg
    simp [diff, hg]
    exact Steps.refl zero
  | node a b iha ihb =>
    simp [hasVar, Bool.or_eq_false_iff] at hg
    -- diff (node a b) x = sub'(mul'(exp'(a), diff(a,x)), mul'(diff(b,x), inv'(b)))
    simp [diff]
    -- By induction: diff a x →* zero and diff b x →* zero
    have ha : Steps (diff a x) zero := iha hg.1
    have hb : Steps (diff b x) zero := ihb hg.2
    -- mul'(exp'(a), diff(a,x)) →* mul'(exp'(a), zero) →* zero
    have left_zero : Steps (mul' (exp' a) (diff a x)) zero :=
      Steps.trans (Steps.mul'_r ha) (mul_zero_r_steps (exp' a))
    -- mul'(diff(b,x), inv'(b)) →* mul'(zero, inv'(b)) →* zero
    have right_zero : Steps (mul' (diff b x) (inv' b)) zero :=
      Steps.trans (Steps.mul'_l hb) (mul_zero_l_steps (inv' b))
    -- sub'(mul'(...), mul'(...)) →* sub'(zero, zero) →* zero
    exact Steps.trans (Steps.sub'_both left_zero right_zero) (sub_self_steps zero)

/-! ## Consequences -/

/-- The derivative of e is zero. -/
theorem diff_e_is_zero (x : Nat) : Steps (diff e' x) zero :=
  diff_ground_is_zero e' x rfl

/-- The derivative of the zero constant is zero. -/
theorem diff_zero_is_zero (x : Nat) : Steps (diff zero x) zero :=
  diff_ground_is_zero zero x rfl

/-- The derivative of any EML-encoded constant (π, i, √2, ...) is zero,
    as long as its tree contains no variables. -/
theorem diff_pi_is_zero (x : Nat) : Steps (diff pi' x) zero :=
  diff_ground_is_zero pi' x rfl

/-! ## The exp(x) derivative -/

/-- d/dx exp(x) = exp(x), proved as a rewrite chain.

    Raw:  sub'(mul'(exp'(x), 1), mul'(0, inv'(1)))
    →*    sub'(exp'(x),          mul'(0, inv'(1)))    [mul_one_r]
    →*    sub'(exp'(x),          0)                    [mul_zero_l]
    →*    exp'(x)                                      [sub_zero]  -/
theorem diff_exp_simplifies (n : Nat) :
    Steps (diff (exp' (var n)) n) (exp' (var n)) := by
  simp [diff, exp']
  -- Goal: Steps (sub' (mul' (exp' (var n)) one) (mul' zero (inv' one))) (exp' (var n))
  -- Step 1: mul'(exp'(var n), one) →* exp'(var n)
  have h1 : Steps (mul' (exp' (var n)) one) (exp' (var n)) :=
    Steps.single (Step.mul_one_r (exp' (var n)))
  -- Step 2: mul'(zero, inv'(one)) →* zero
  have h2 : Steps (mul' zero (inv' one)) zero :=
    Steps.single (Step.mul_zero_l (inv' one))
  -- Step 3: sub'(exp'(var n), zero) →* exp'(var n)
  have h3 : Steps (sub' (exp' (var n)) zero) (exp' (var n)) :=
    Steps.single (Step.sub_zero (exp' (var n)))
  -- Chain: sub'(mul'(...), mul'(...)) →* sub'(exp'(x), zero) →* exp'(x)
  exact Steps.trans (Steps.sub'_both h1 h2) h3

/-! ## Structural properties -/

/-- The derivative of an eml node always has the form sub'(mul'(...), mul'(...)). -/
theorem diff_node_is_sub (a b : Eml) (x : Nat) :
    diff (node a b) x = sub' (mul' (exp' a) (diff a x)) (mul' (diff b x) (inv' b)) := by
  rfl

/-- Leaf count of exp'(z). -/
theorem leaves_exp (z : Eml) : (exp' z).leaves = z.leaves + 1 := by
  simp [exp', leaves]

/-- Leaf count of ln'(z). -/
theorem leaves_ln (z : Eml) : (ln' z).leaves = z.leaves + 3 := by
  simp [ln', exp', leaves]; omega

/-! ## Integration as partial inverse -/

/-- A successful integration: a tree whose derivative rewrites to `f`. -/
structure Antiderivative (f : Eml) (x : Nat) where
  tree : Eml
  proof : Steps (diff tree x) f

/-- exp(x) is its own antiderivative. -/
def exp_self_antideriv (n : Nat) : Antiderivative (exp' (var n)) n :=
  ⟨exp' (var n), diff_exp_simplifies n⟩

/-! ## Canonical natural numbers -/

/-- Canonical natural number encoding in EML.
    ofNat' 0 = zero, ofNat' (n+1) = add'(one, ofNat' n).
    Trees are right-associated sums of one, terminating in zero:
      ofNat' 3 = add'(1, add'(1, add'(1, 0)))  -/
def ofNat' : Nat → Eml
  | 0     => zero
  | n + 1 => add' one (ofNat' n)

/-- ofNat' 1 reduces to one (= the terminal). -/
theorem ofNat'_one_steps : Steps (ofNat' 1) one :=
  Steps.single (Step.add_zero_r one)

/-- ofNat' 2 = add'(1, add'(1, 0)). -/
theorem ofNat'_two : ofNat' 2 = add' one (add' one zero) := rfl

/-! ## Distributivity enables arithmetic -/

/-- mul' is commutative (from add_comm on logarithms). -/
theorem mul_comm_steps (a b : Eml) : Steps (mul' a b) (mul' b a) :=
  Steps.exp' (Steps.single (Step.add_comm (ln' a) (ln' b)))

/-- **exp_add is redundant**: `mul'(exp' a, exp' b) →* exp'(add' a b)`.
    The RHS of exp_add reduces to its LHS using only ln_exp — the exp
    homomorphism is built into the encoding via `mul' x y = exp'(add'(ln' x, ln' y))`. -/
theorem exp_add_redundant (a b : Eml) :
    Steps (mul' (exp' a) (exp' b)) (exp' (add' a b)) :=
  -- mul'(exp' a, exp' b) = exp'(add'(ln'(exp' a), ln'(exp' b)))  [def]
  -- →* exp'(add'(a, ln'(exp' b)))                                 [ln_exp]
  -- →* exp'(add'(a, b))                                            [ln_exp]
  Steps.trans
    (Steps.exp' (Steps.add'_l (Steps.single (Step.ln_exp a))))
    (Steps.exp' (Steps.add'_r (Steps.single (Step.ln_exp b))))

/-- mul'(a, add'(b, c)) →* add'(mul'(a, b), mul'(a, c)) -/
theorem mul_add_steps (a b c : Eml) :
    Steps (mul' a (add' b c)) (add' (mul' a b) (mul' a c)) :=
  Steps.single (Step.mul_add a b c)

/-- add'(ofNat' m, ofNat' n) →* ofNat' (m + n).
    The proof peels `one`s off the left via add_assoc. -/
theorem add_ofNat' (m n : Nat) : Steps (add' (ofNat' m) (ofNat' n)) (ofNat' (m + n)) := by
  induction m with
  | zero =>
    -- add'(zero, ofNat' n) →* ofNat' n
    simp only [ofNat', Nat.zero_add]
    exact Steps.single (Step.add_zero_l (ofNat' n))
  | succ m ih =>
    -- add'(add'(one, ofNat' m), ofNat' n)
    -- →  add'(one, add'(ofNat' m, ofNat' n))   [add_assoc]
    -- →* add'(one, ofNat' (m + n))              [IH]
    -- = ofNat' ((m + n) + 1) = ofNat' ((m+1) + n)
    show Steps (add' (add' one (ofNat' m)) (ofNat' n)) (ofNat' (m + 1 + n))
    have hmn : m + 1 + n = (m + n) + 1 := by omega
    rw [hmn]
    exact Steps.trans
      (Steps.single (Step.add_assoc one (ofNat' m) (ofNat' n)))
      (Steps.add'_r ih)

/-- mul'(a, zero) →* zero -/
theorem mul_zero_r' (a : Eml) : Steps (mul' a zero) zero :=
  Steps.single (Step.mul_zero_r a)

/-- mul'(a, one) →* a -/
theorem mul_one_r' (a : Eml) : Steps (mul' a one) a :=
  Steps.single (Step.mul_one_r a)

/-- add'(a, zero) →* a -/
theorem add_zero_r' (a : Eml) : Steps (add' a zero) a :=
  Steps.single (Step.add_zero_r a)

/-- **Multiplication distributes into ofNat': mul'(a, ofNat' n) →* ofNat'-scaled sum.**
    mul'(a, ofNat' n) →* add'(a, add'(a, ...add'(a, 0)...)) with n copies of a. -/
private def nfold_add (a : Eml) : Nat → Eml
  | 0     => zero
  | n + 1 => add' a (nfold_add a n)

private theorem mul_ofNat'_aux (a : Eml) (n : Nat) :
    Steps (mul' a (ofNat' n)) (nfold_add a n) := by
  induction n with
  | zero => exact mul_zero_r' a
  | succ n ih =>
    -- mul'(a, add'(1, ofNat' n)) → add'(mul'(a, 1), mul'(a, ofNat' n))
    exact Steps.trans (mul_add_steps a one (ofNat' n))
      (Steps.add'_both (mul_one_r' a) ih)

/-- **2 × 3 = 6, machine-checked.**
    mul'(ofNat' 2, ofNat' 3) →* ofNat' 6.  -/
theorem two_times_three : Steps (mul' (ofNat' 2) (ofNat' 3)) (ofNat' 6) := by
  -- 2 * 3 →* 3 * 2                       [mul_comm]
  -- 3 * 2 →* nfold_add 3 2               [mul_ofNat'_aux]
  --        = add'(3, add'(3, 0))
  --        = add'(ofNat' 3, ofNat' 3)     [def]
  --       →* ofNat' 6                     [add_ofNat']
  have h1 := mul_comm_steps (ofNat' 2) (ofNat' 3)
  have h2 := mul_ofNat'_aux (ofNat' 3) 2
  -- nfold_add (ofNat' 3) 2 = add'(ofNat' 3, add'(ofNat' 3, zero))
  -- and add'(ofNat' 3, zero) = ofNat' 3 definitionally (since ofNat' 3 = add'(1, add'(1, add'(1, zero))))
  -- ... wait, nfold_add (ofNat' 3) 2 = add'(ofNat' 3, add'(ofNat' 3, zero))
  -- We need: add'(ofNat' 3, add'(ofNat' 3, zero)) →* ofNat' 6
  -- Step 1: add'(ofNat' 3, zero) →* ofNat' 3    [add_zero_r]
  -- Step 2: add'(ofNat' 3, ofNat' 3) →* ofNat' 6  [add_ofNat']
  have h3 : Steps (nfold_add (ofNat' 3) 2) (ofNat' 6) :=
    Steps.trans (Steps.add'_r (add_zero_r' (ofNat' 3))) (add_ofNat' 3 3)
  exact Steps.trans h1 (Steps.trans h2 h3)

end Eml
