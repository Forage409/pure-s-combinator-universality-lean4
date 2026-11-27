import formal_order_and_isolated.order_classification

/-!
# Exact Leaf-Preserving Dynamics (`|M| = |N|`), Ranked Conservation Laws, and Isolated Normal Forms

Constructive, axiom-free Lean 4.33.1 formalization (`namespace FormalOrderAndIsolated`) of:
1. **Bergstra's Exact Leaf-Preserving Reduction Criterion & Quantitative Potential Law**:
   - Every `Step a b` decomposes as `a = plugCtx c (S ⋅ x ⋅ y ⋅ z)` and `b = plugCtx c ((x ⋅ z) ⋅ (y ⋅ z))`
     with `leaves b + 1 = leaves a + leaves z`.
   - `leaves a = leaves b` **iff** `leaves z = 1` (for closed terms, uniquely `S ⋅ x ⋅ y ⋅ S`);
     otherwise `leaves a + 1 ≤ leaves b`.
   - Bergstra's weight `bergstraWeight (a ⋅ b) = 2 * bergstraWeight a + bergstraWeight b` drops by
     **exact** `6 * 2 ^ (leftDepth c)` on every leaf-preserving step, and satisfies the sharp
     two-sided envelope `2 * leaves t - 1 ≤ bergstraWeight t ≤ 2 ^ (leaves t) - 1` (attained on
     closed terms uniquely by `rightComb n` [Order 3] and `leftComb n`), yielding Bergstra's
     explicit exponential upper bound `6 * k + 2 * leaves t ≤ 2 ^ (leaves t)`.
2. **Exact Ranked Conservation Law (`leftSubtreeSum`), Global `SN` + `CR`, & Quarter-Square $\Theta(|M|^2)$ Bound**:
   - `leftSubtreeSum (a ⋅ b) = leftSubtreeSum a + leftSubtreeSum b + leaves a` drops by **exact
     constant `2`** (`leftSubtreeSum a = leftSubtreeSum b + 2`) on every leaf-preserving step at
     any depth!
   - `LeafPresStep` is globally strongly normalizing (`leafPres_sn`) and globally confluent
     (`leafPres_church_rosser`), so every pure-`S` term `t` (even divergent terms like `AAA`) has a
     unique canonical leaf-preserving normal form, and **all maximal leaf-preserving reductions from
     `t` have the exact same length** (Jordan–Hölder ranked diamond property).
   - Improves Bergstra's $O(2^{|M|})$ bound to quadratic `4 * k ≤ (leaves t - 1) * (leaves t - 2)`,
     matched up to $\lfloor(|M|-2)/4\rfloor$ by `leftComb n`, which reduces in **exact quarter-square**
     `((n - 2) * (n - 2)) / 4` leaf-preserving steps to `leftCombLPNF n`!
3. **Isolated Normal Forms & Singleton Convertibility Classes (`Question 30`)**:
   - For **every** open or closed pure-`S` term `t`, `(∀ u, ConvS t u ↔ u = t) ↔ IsIsolatedNF t`
     (`IsNormalForm t ∧ HasNoPredecessor t`).
   - Exact linear-time deciders `hasContractumSubterm`, `isClosedNFBool`, and `isIsolatedClosedNF`,
     proving `isIsolatedClosedNF t = true ↔ (noVars t = true ∧ IsIsolatedNF t)`, isolation of all
     Order-3 towers `rightComb n`, and uniqueness of `S ⋅ S ⋅ (S ⋅ S)` as the minimal non-isolated
     normal form at leaf size `4`.

Verified with zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`, and zero `Classical.choice`.
-/

namespace FormalOrderAndIsolated

open FormalAlgebra

local infixl:70 (priority := high) " ⋅ " => FormalAlgebra.Term.app

/-! ## 1. Redex Context Decomposition, Leaf-Preserving Steps, and Bergstra's `6 · 2^d` Law -/

def leftDepth : Ctx → Nat
  | .hole => 0
  | .left c _ => 1 + leftDepth c
  | .right _ c => leftDepth c

def ctxLeaves : Ctx → Nat
  | .hole => 0
  | .left c r => ctxLeaves c + leaves r
  | .right l c => leaves l + ctxLeaves c

theorem leaves_plugCtx (c : Ctx) (u : Term) :
    leaves (plugCtx c u) = ctxLeaves c + leaves u := by
  induction c with
  | hole => exact (Nat.zero_add (leaves u)).symm
  | left c r ih =>
    change leaves (plugCtx c u) + leaves r = (ctxLeaves c + leaves r) + leaves u
    rw [ih, Nat.add_assoc, Nat.add_comm (leaves u) (leaves r), ← Nat.add_assoc]
  | right l c ih =>
    change leaves l + leaves (plugCtx c u) = (leaves l + ctxLeaves c) + leaves u
    rw [ih, ← Nat.add_assoc]

theorem plugCtx_step {c : Ctx} {u v : Term} (h : Step u v) :
    Step (plugCtx c u) (plugCtx c v) := by
  induction c with
  | hole => exact h
  | left _ _ ih => exact FormalAlgebra.Step.left ih
  | right _ _ ih => exact FormalAlgebra.Step.right ih

theorem step_ctx_decomp {a b : Term} (h : Step a b) :
    ∃ (c : Ctx) (x y z : Term),
      a = plugCtx c (S ⋅ x ⋅ y ⋅ z) ∧ b = plugCtx c ((x ⋅ z) ⋅ (y ⋅ z)) := by
  induction h with
  | root x y z => exact ⟨.hole, x, y, z, rfl, rfl⟩
  | @left _ _ r _ ih =>
    obtain ⟨c, x, y, z, ha, hb⟩ := ih
    exact ⟨.left c r, x, y, z, congrArg (· ⋅ r) ha, congrArg (· ⋅ r) hb⟩
  | @right l _ _ _ ih =>
    obtain ⟨c, x, y, z, ha, hb⟩ := ih
    exact ⟨.right l c, x, y, z, congrArg (l ⋅ ·) ha, congrArg (l ⋅ ·) hb⟩

theorem step_leaves_balance (c : Ctx) (x y z : Term) :
    leaves (plugCtx c ((x ⋅ z) ⋅ (y ⋅ z))) + 1 =
      leaves (plugCtx c (S ⋅ x ⋅ y ⋅ z)) + leaves z := by
  rw [leaves_plugCtx, leaves_plugCtx]
  change (ctxLeaves c + ((leaves x + leaves z) + (leaves y + leaves z))) + 1 =
    (ctxLeaves c + (((1 + leaves x) + leaves y) + leaves z)) + leaves z
  have hcore : ((leaves x + leaves z) + (leaves y + leaves z)) + 1 =
      (((1 + leaves x) + leaves y) + leaves z) + leaves z := by
    omega
  rw [Nat.add_assoc (ctxLeaves c), Nat.add_assoc (ctxLeaves c), hcore]

/-- A 1-step `CL(S)` reduction is **leaf-preserving** iff `leaves a = leaves b`. -/
def LeafPresStep (a b : Term) : Prop :=
  Step a b ∧ leaves a = leaves b

inductive LeafPresReduces : Term → Term → Prop where
  | refl (a : Term) : LeafPresReduces a a
  | next {a b c : Term} : LeafPresStep a b → LeafPresReduces b c → LeafPresReduces a c

inductive LeafPresStepsN : Nat → Term → Term → Prop where
  | zero (a : Term) : LeafPresStepsN 0 a a
  | succ {k : Nat} {a b c : Term} : LeafPresStep a b → LeafPresStepsN k b c → LeafPresStepsN (k + 1) a c

def IsLeafPresNF (t : Term) : Prop :=
  ∀ t', ¬ LeafPresStep t t'

/-- **Exact Syntactic Characterization of Leaf-Preserving Steps** (open or closed!): -/
theorem step_leaves_eq_iff {a b : Term} (h : Step a b) :
    leaves a = leaves b ↔
      ∃ (c : Ctx) (x y z : Term),
        a = plugCtx c (S ⋅ x ⋅ y ⋅ z) ∧ b = plugCtx c ((x ⋅ z) ⋅ (y ⋅ z)) ∧ leaves z = 1 := by
  constructor
  · intro heq
    obtain ⟨c, x, y, z, ha, hb⟩ := step_ctx_decomp h
    have hbal := step_leaves_balance c x y z
    rw [← ha, ← hb, heq] at hbal
    exact ⟨c, x, y, z, ha, hb, (Nat.add_left_cancel hbal).symm⟩
  · intro ⟨c, x, y, z, ha, hb, hz1⟩
    have hbal := step_leaves_balance c x y z
    rw [← ha, ← hb, hz1] at hbal
    exact (Nat.add_right_cancel hbal).symm

private theorem noVars_of_plugCtx {c : Ctx} {u : Term} (hv : noVars (plugCtx c u) = true) :
    noVars u = true := by
  induction c with
  | hole => exact hv
  | left _ _ ih => exact ih ((Bool.and_eq_true _ _).mp hv).1
  | right _ _ ih => exact ih ((Bool.and_eq_true _ _).mp hv).2

private theorem closed_leaves_eq_one_eq_s {z : Term} (hv : noVars z = true) (hz1 : leaves z = 1) :
    z = S := by
  cases z with
  | s => rfl
  | var _ => cases hv
  | app p q =>
    have hp : 1 ≤ leaves p := leaves_pos p
    have hq : 1 ≤ leaves q := leaves_pos q
    have h2 : 2 ≤ leaves p + leaves q := Nat.add_le_add hp hq
    change leaves p + leaves q = 1 at hz1
    rw [hz1] at h2
    exact False.elim (absurd h2 (by decide))

/-- **Closed Bergstra Criterion**: On closed pure-`S` terms, `Step a b` preserves leaf count
    **iff** the contracted redex has the exact form `S ⋅ x ⋅ y ⋅ S`! -/
theorem closed_step_leaves_eq_iff {a b : Term} (hv : noVars a = true) :
    LeafPresStep a b ↔
      ∃ (c : Ctx) (x y : Term),
        a = plugCtx c (S ⋅ x ⋅ y ⋅ S) ∧ b = plugCtx c ((x ⋅ S) ⋅ (y ⋅ S)) := by
  constructor
  · intro ⟨hs, heq⟩
    obtain ⟨c, x, y, z, ha, hb, hz1⟩ := (step_leaves_eq_iff hs).mp heq
    have hv_red : noVars (S ⋅ x ⋅ y ⋅ z) = true := noVars_of_plugCtx (ha ▸ hv)
    have hvz : noVars z = true := ((Bool.and_eq_true _ _).mp hv_red).2
    have hzS : z = S := closed_leaves_eq_one_eq_s hvz hz1
    subst hzS
    exact ⟨c, x, y, ha, hb⟩
  · intro ⟨c, x, y, ha, hb⟩
    subst ha; subst hb
    have hs : Step (plugCtx c (S ⋅ x ⋅ y ⋅ S)) (plugCtx c ((x ⋅ S) ⋅ (y ⋅ S))) :=
      plugCtx_step (FormalAlgebra.Step.root x y S)
    have hbal : leaves (plugCtx c ((x ⋅ S) ⋅ (y ⋅ S))) + 1 =
        leaves (plugCtx c (S ⋅ x ⋅ y ⋅ S)) + 1 := step_leaves_balance c x y S
    exact ⟨hs, (Nat.add_right_cancel hbal).symm⟩

theorem step_leaves_strict_increase_of_ne {a b : Term} (hs : Step a b) (hne : leaves a ≠ leaves b) :
    leaves a + 1 ≤ leaves b := by
  have hle : leaves a ≤ leaves b := leaves_mono_step hs
  exact Nat.lt_of_le_of_ne hle hne

/-- Context scaling law for `bergstraWeight`: a drop of `k` at `c` becomes `(2 ^ leftDepth c) * k` at the root. -/
theorem bergstraWeight_plugCtx_diff (c : Ctx) {u v : Term} {k : Nat}
    (h : bergstraWeight u = bergstraWeight v + k) :
    bergstraWeight (plugCtx c u) = bergstraWeight (plugCtx c v) + (2 ^ leftDepth c) * k := by
  induction c with
  | hole =>
    change bergstraWeight u = bergstraWeight v + 1 * k
    rw [Nat.one_mul]
    exact h
  | left c r ih =>
    change 2 * bergstraWeight (plugCtx c u) + bergstraWeight r =
      (2 * bergstraWeight (plugCtx c v) + bergstraWeight r) + (2 ^ (1 + leftDepth c)) * k
    have hp : (2 ^ (1 + leftDepth c)) * k = 2 * ((2 ^ leftDepth c) * k) := by
      rw [Nat.add_comm 1 (leftDepth c), Nat.pow_succ, Nat.mul_comm (2 ^ leftDepth c) 2, Nat.mul_assoc]
    rw [ih, hp, Nat.mul_add]
    omega
  | right l c ih =>
    change 2 * bergstraWeight l + bergstraWeight (plugCtx c u) =
      (2 * bergstraWeight l + bergstraWeight (plugCtx c v)) + (2 ^ leftDepth c) * k
    rw [ih, Nat.add_assoc]

/-- **Bergstra's Quantitative `6 · 2^d` Weight-Drop Law** (open or closed!):
    Contracting `S ⋅ x ⋅ y ⋅ z` with `leaves z = 1` inside context `c` decreases `bergstraWeight`
    by **exact** `6 * (2 ^ leftDepth c)`! -/
theorem bergstraWeight_leafPres_exact_drop (c : Ctx) (x y z : Term) (hz1 : leaves z = 1) :
    bergstraWeight (plugCtx c (S ⋅ x ⋅ y ⋅ z)) =
      bergstraWeight (plugCtx c ((x ⋅ z) ⋅ (y ⋅ z))) + 6 * (2 ^ leftDepth c) := by
  have hwz : bergstraWeight z = 1 := leaves_eq_one_weight z hz1
  have hroot : bergstraWeight (S ⋅ x ⋅ y ⋅ z) = bergstraWeight ((x ⋅ z) ⋅ (y ⋅ z)) + 6 := by
    change 2 * (2 * (2 * 1 + bergstraWeight x) + bergstraWeight y) + bergstraWeight z =
      (2 * (2 * bergstraWeight x + bergstraWeight z) + (2 * bergstraWeight y + bergstraWeight z)) + 6
    rw [hwz]
    omega
  rw [bergstraWeight_plugCtx_diff c hroot, Nat.mul_comm]

private theorem pow2_pos (n : Nat) : 1 ≤ 2 ^ n := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ d ih =>
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.le_trans ih (Nat.le_add_left _ _)

theorem leafPresStep_weight_drop_ge_6 {a b : Term} (hlp : LeafPresStep a b) :
    bergstraWeight b + 6 ≤ bergstraWeight a := by
  obtain ⟨c, x, y, z, ha, hb, hz1⟩ := (step_leaves_eq_iff hlp.1).mp hlp.2
  have hdrop := bergstraWeight_leafPres_exact_drop c x y z hz1
  rw [← ha, ← hb] at hdrop
  have h6 : 6 ≤ 6 * (2 ^ leftDepth c) := by
    have hm := Nat.mul_le_mul_left 6 (pow2_pos (leftDepth c))
    rw [Nat.mul_one] at hm
    exact hm
  rw [hdrop]
  exact Nat.add_le_add_left h6 _

/-! ### Sharp Two-Sided Envelope of `bergstraWeight` and Explicit Exponential Step Bound -/

/-- Left-comb (`S^n = S ⋅ S ⋅ ... ⋅ S`, Klop's flat term of `n` leaves). -/
def leftComb : Nat → Term
  | 0 => S
  | 1 => S
  | k + 2 => leftComb (k + 1) ⋅ S

theorem noVars_leftComb (n : Nat) : noVars (leftComb n) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m => exact (Bool.and_eq_true _ _).mpr ⟨ih, rfl⟩

theorem leaves_leftComb {n : Nat} (hn : 1 ≤ n) : leaves (leftComb n) = n := by
  induction n with
  | zero => cases hn
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m =>
      change leaves (leftComb (m + 1)) + 1 = m + 2
      rw [ih (Nat.succ_le_succ (Nat.zero_le m))]

private theorem pow2_ge_2 {j : Nat} (hj : 1 ≤ j) : 2 ≤ 2 ^ j := by
  cases j with
  | zero => cases hj
  | succ j0 =>
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.add_le_add (pow2_pos j0) (pow2_pos j0)

private theorem exp_merge_ge2 {j : Nat} (hj : 1 ≤ j) (k1 : Nat) :
    2 * (2 ^ j) + (2 ^ (k1 + 2)) ≤ 2 ^ (j + (k1 + 2)) := by
  induction k1 with
  | zero =>
    have hx : 2 ≤ 2 ^ j := pow2_ge_2 hj
    have h4 : 4 ≤ 2 * (2 ^ j) := by
      rw [Nat.two_mul]
      exact Nat.add_le_add hx hx
    have hrhs : 2 ^ (j + 2) = 2 * (2 ^ j) + 2 * (2 ^ j) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_succ, Nat.mul_comm (2 ^ j) 2]
    rw [show (2 : Nat) ^ 2 = 4 from rfl, hrhs]
    exact Nat.add_le_add (Nat.le_refl _) h4
  | succ m ih =>
    have hl : 2 ^ (m + 3) = 2 ^ (m + 2) + 2 ^ (m + 2) := by
      rw [Nat.pow_succ, Nat.mul_two]
    have hr : 2 ^ (j + (m + 3)) = 2 ^ (j + (m + 2)) + 2 ^ (j + (m + 2)) := by
      rw [← Nat.add_assoc j (m + 2) 1, Nat.pow_succ, Nat.mul_two]
    rw [hl, hr, ← Nat.add_assoc]
    exact Nat.add_le_add ih (Nat.le_trans (Nat.le_add_left _ _) ih)

private theorem not_add_two_le_self (x : Nat) (h : x + 2 ≤ x) : False :=
  Nat.not_succ_le_self x (Nat.le_trans (Nat.le_succ (x + 1)) h)

private theorem exp_merge_ineq {j k : Nat} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    2 * (2 ^ j) + (2 ^ k) ≤ (2 ^ (j + k)) + 2 ∧
    (2 * (2 ^ j) + (2 ^ k) = (2 ^ (j + k)) + 2 ↔ k = 1) := by
  cases k with
  | zero => cases hk
  | succ k0 =>
    cases k0 with
    | zero =>
      have heq0 : 2 * (2 ^ j) + (2 ^ 1) = (2 ^ (j + 1)) + 2 := by
        rw [show (2 : Nat) ^ 1 = 2 from rfl, Nat.pow_succ, Nat.mul_comm]
      exact ⟨Nat.le_of_eq heq0, ⟨fun _ => rfl, fun _ => heq0⟩⟩
    | succ k1 =>
      have hge2 : 2 * (2 ^ j) + (2 ^ (k1 + 2)) ≤ 2 ^ (j + (k1 + 2)) := exp_merge_ge2 hj k1
      refine ⟨Nat.le_trans hge2 (Nat.le_add_right _ 2), ⟨fun heq => ?_, fun h1 => ?_⟩⟩
      · rw [heq] at hge2
        exact False.elim (not_add_two_le_self _ hge2)
      · injection h1 with h0
        cases h0

/-- **Sharp Two-Sided Envelope of Bergstra's Weight** (`2|t| - 1 ≤ W(t) ≤ 2^|t| - 1`):
    - Lower bound `2 * leaves t - 1` is attained on closed terms **iff `t = rightComb (leaves t)`** (Order 3!).
    - Upper bound `2 ^ (leaves t) - 1` is attained on closed terms **iff `t = leftComb (leaves t)`**! -/
theorem bergstraWeight_bounds (t : Term) :
    2 * leaves t ≤ bergstraWeight t + 1 ∧ bergstraWeight t + 1 ≤ 2 ^ (leaves t) := by
  induction t with
  | s => exact ⟨Nat.le_refl 2, Nat.le_refl 2⟩
  | var _ => exact ⟨Nat.le_refl 2, Nat.le_refl 2⟩
  | app a b iha ihb =>
    have ha : 1 ≤ leaves a := leaves_pos a
    have hb : 1 ≤ leaves b := leaves_pos b
    have ⟨hm_le, _⟩ := exp_merge_ineq ha hb
    change 2 * (leaves a + leaves b) ≤ (2 * bergstraWeight a + bergstraWeight b) + 1 ∧
      (2 * bergstraWeight a + bergstraWeight b) + 1 ≤ 2 ^ (leaves a + leaves b)
    constructor
    · have hwa1 : 1 ≤ bergstraWeight a :=
        Nat.le_of_succ_le_succ (Nat.le_trans (Nat.mul_le_mul_left 2 ha) iha.1)
      have h2la : 2 * leaves a ≤ 2 * bergstraWeight a := by
        have hstep : bergstraWeight a + 1 ≤ 2 * bergstraWeight a := by
          rw [Nat.two_mul]
          exact Nat.add_le_add_left hwa1 _
        exact Nat.le_trans iha.1 hstep
      rw [Nat.mul_add, Nat.add_assoc]
      exact Nat.add_le_add h2la ihb.1
    · have h1 : 2 * (bergstraWeight a + 1) + (bergstraWeight b + 1) ≤
          2 * (2 ^ leaves a) + (2 ^ leaves b) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 iha.2) ihb.2
      have h2 : 2 * (bergstraWeight a + 1) + (bergstraWeight b + 1) =
          ((2 * bergstraWeight a + bergstraWeight b) + 1) + 2 := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [h2] at h1
      exact Nat.le_of_add_le_add_right (Nat.le_trans h1 hm_le)

private theorem bergstraWeight_rightComb {n : Nat} (hn : 1 ≤ n) :
    bergstraWeight (rightComb n) + 1 = 2 * n := by
  induction n with
  | zero => cases hn
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m =>
      change (2 * 1 + bergstraWeight (rightComb (m + 1))) + 1 = 2 * (m + 2)
      have ihm := ih (Nat.succ_le_succ (Nat.zero_le m))
      rw [Nat.add_assoc (2 * 1), ihm, Nat.mul_add 2 (m + 1) 1]
      exact Nat.add_comm 2 (2 * (m + 1))

private theorem bergstraWeight_leftComb {n : Nat} (hn : 1 ≤ n) :
    bergstraWeight (leftComb n) + 1 = 2 ^ n := by
  induction n with
  | zero => cases hn
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m =>
      change (2 * bergstraWeight (leftComb (m + 1)) + 1) + 1 = 2 ^ (m + 2)
      have ihm := ih (Nat.succ_le_succ (Nat.zero_le m))
      have hl : (2 * bergstraWeight (leftComb (m + 1)) + 1) + 1 =
          2 * (bergstraWeight (leftComb (m + 1)) + 1) := by
        rw [Nat.add_assoc, Nat.mul_add]
      rw [hl, ihm, Nat.pow_succ 2 (m + 1), Nat.mul_comm]

private theorem nat_squeeze_add {a1 a2 b1 b2 c : Nat}
    (ha : a1 ≤ a2) (hb : b1 ≤ b2) (hsum : a1 + b1 = c) (hhi : a2 + b2 ≤ c) :
    a1 = a2 ∧ a2 + b2 = c := by
  have heq_hi : a2 + b2 = c := Nat.le_antisymm hhi (hsum ▸ Nat.add_le_add ha hb)
  have ha2_le : a2 ≤ a1 := by
    have hstep : a2 + b1 ≤ a1 + b1 := by
      rw [hsum, ← heq_hi]
      exact Nat.add_le_add_left hb a2
    exact Nat.le_of_add_le_add_right hstep
  exact ⟨Nat.le_antisymm ha ha2_le, heq_hi⟩

theorem closed_bergstraWeight_extremals {t : Term} (hv : noVars t = true) :
    (bergstraWeight t + 1 = 2 * leaves t ↔ t = rightComb (leaves t)) ∧
    (bergstraWeight t + 1 = 2 ^ (leaves t) ↔ t = leftComb (leaves t)) := by
  induction t with
  | s => exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, ⟨fun _ => rfl, fun _ => rfl⟩⟩
  | var _ => cases hv
  | app a b iha ihb =>
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    have hvb := ((Bool.and_eq_true _ _).mp hv).2
    have ha_pos : 1 ≤ leaves a := leaves_pos a
    have hb_pos : 1 ≤ leaves b := leaves_pos b
    have ⟨ba1, ba2⟩ := bergstraWeight_bounds a
    have ⟨bb1, bb2⟩ := bergstraWeight_bounds b
    have ⟨hm_le, hm_eq_iff⟩ := exp_merge_ineq ha_pos hb_pos
    refine ⟨?_, ?_⟩
    · constructor
      · intro hmin
        change (2 * bergstraWeight a + bergstraWeight b) + 1 = 2 * (leaves a + leaves b) at hmin
        have hwa_pos : 1 ≤ bergstraWeight a :=
          Nat.le_of_succ_le_succ (Nat.le_trans (Nat.mul_le_mul_left 2 ha_pos) ba1)
        have ha1_and_hb : leaves a = 1 ∧ bergstraWeight b + 1 = 2 * leaves b := by
          cases hwa : bergstraWeight a with
          | zero => rw [hwa] at hwa_pos; cases hwa_pos
          | succ wa0 =>
            cases wa0 with
            | zero =>
              rw [hwa] at ba1 hmin
              have hla_le1 : leaves a ≤ 1 := by
                cases hla : leaves a with
                | zero => exact Nat.zero_le 1
                | succ l0 =>
                  cases l0 with
                  | zero => exact Nat.le_refl 1
                  | succ l1 =>
                    rw [hla] at ba1
                    have h4 : 4 ≤ 2 * (l1 + 2) := Nat.mul_le_mul_left 2 (Nat.le_add_left 2 l1)
                    exact False.elim (absurd (Nat.le_trans h4 ba1) (by decide))
              have ha1 : leaves a = 1 := Nat.le_antisymm hla_le1 ha_pos
              rw [ha1, Nat.mul_add 2 1 (leaves b), Nat.add_assoc (2 * 1)] at hmin
              exact ⟨ha1, Nat.add_left_cancel hmin⟩
            | succ wa1 =>
              rw [hwa] at ba1 hmin
              have hstrict : 2 * leaves a + 1 ≤ 2 * (wa1 + 2) := by
                have h2 : (wa1 + 3) + 1 ≤ 2 * (wa1 + 2) := by
                  rw [Nat.two_mul]
                  have hle : 2 ≤ wa1 + 2 := Nat.le_add_left 2 wa1
                  have hsum : (wa1 + 2) + 2 = (wa1 + 3) + 1 := rfl
                  rw [← hsum]
                  exact Nat.add_le_add_left hle (wa1 + 2)
                exact Nat.le_trans (Nat.add_le_add_right ba1 1) h2
              have hcomb : 2 * (leaves a + leaves b) + 1 ≤ (2 * (wa1 + 2) + bergstraWeight b) + 1 := by
                have heq_l : 2 * (leaves a + leaves b) + 1 = (2 * leaves a + 1) + 2 * leaves b := by
                  rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm (2 * leaves b) 1, ← Nat.add_assoc]
                have heq_r : (2 * (wa1 + 2) + bergstraWeight b) + 1 = 2 * (wa1 + 2) + (bergstraWeight b + 1) :=
                  Nat.add_assoc _ _ _
                rw [heq_l, heq_r]
                exact Nat.add_le_add hstrict bb1
              rw [hmin] at hcomb
              exact False.elim (Nat.not_succ_le_self _ hcomb)
        have haS : a = S := closed_leaves_eq_one_eq_s hva ha1_and_hb.1
        have hb_rc : b = rightComb (leaves b) := (ihb hvb).1.mp ha1_and_hb.2
        subst haS
        cases hlb : leaves b with
        | zero => rw [hlb] at hb_pos; cases hb_pos
        | succ m =>
          change S ⋅ b = rightComb (1 + leaves b)
          rw [hlb] at hb_rc
          rw [hlb, hb_rc, Nat.add_comm 1 (m + 1)]
          rfl
      · intro heq
        have hpos_ab : 1 ≤ leaves (a ⋅ b) := leaves_pos (a ⋅ b)
        conv => lhs; rw [heq]
        exact bergstraWeight_rightComb hpos_ab
    · constructor
      · intro hmax
        change (2 * bergstraWeight a + bergstraWeight b) + 1 = 2 ^ (leaves a + leaves b) at hmax
        have hsum_eq : 2 * (bergstraWeight a + 1) + (bergstraWeight b + 1) =
            (2 ^ (leaves a + leaves b)) + 2 := by
          have hl : 2 * (bergstraWeight a + 1) + (bergstraWeight b + 1) =
              ((2 * bergstraWeight a + bergstraWeight b) + 1) + 2 := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
          rw [hl, hmax]
        have ⟨h2a_eq, heq_merge⟩ :=
          nat_squeeze_add (Nat.mul_le_mul_left 2 ba2) bb2 hsum_eq hm_le
        have ha_max : bergstraWeight a + 1 = 2 ^ leaves a :=
          Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2a_eq
        have hb1 : leaves b = 1 := hm_eq_iff.mp heq_merge
        have hbS : b = S := closed_leaves_eq_one_eq_s hvb hb1
        have ha_lc : a = leftComb (leaves a) := (iha hva).2.mp ha_max
        subst hbS
        cases hla : leaves a with
        | zero => rw [hla] at ha_pos; cases ha_pos
        | succ m =>
          change a ⋅ S = leftComb (leaves a + 1)
          rw [hla] at ha_lc
          rw [hla, ha_lc]
          rfl
      · intro heq
        have hpos_ab : 1 ≤ leaves (a ⋅ b) := leaves_pos (a ⋅ b)
        conv => lhs; rw [heq]
        exact bergstraWeight_leftComb hpos_ab

/-- **Explicit Bergstra `O(2^|M|)` Bound on Consecutive Leaf-Preserving Steps** (open or closed!): -/
theorem bergstra_leafPres_exp_bound {k : Nat} {a b : Term} (h : LeafPresStepsN k a b) :
    leaves a = leaves b ∧
    6 * k + bergstraWeight b ≤ bergstraWeight a ∧
    6 * k + 2 * leaves a ≤ 2 ^ (leaves a) := by
  have ⟨hl_eq, hw_le⟩ : leaves a = leaves b ∧ 6 * k + bergstraWeight b ≤ bergstraWeight a := by
    induction h with
    | zero a0 =>
      refine ⟨rfl, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add]
      exact Nat.le_refl _
    | @succ k0 a0 b0 c0 hs _ ih =>
      have hd : bergstraWeight b0 + 6 ≤ bergstraWeight a0 := leafPresStep_weight_drop_ge_6 hs
      refine ⟨hs.2.trans ih.1, ?_⟩
      have h1 : 6 * (k0 + 1) + bergstraWeight c0 = (6 * k0 + bergstraWeight c0) + 6 := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 6 (bergstraWeight c0), ← Nat.add_assoc]
      rw [h1]
      exact Nat.le_trans (Nat.add_le_add_right ih.2 6) hd
  have ⟨hb_lo, _⟩ := bergstraWeight_bounds b
  have ⟨_, ha_hi⟩ := bergstraWeight_bounds a
  rw [← hl_eq] at hb_lo
  refine ⟨hl_eq, hw_le, ?_⟩
  have hstep1 : 6 * k + 2 * leaves a ≤ (6 * k + bergstraWeight b) + 1 := by
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left hb_lo (6 * k)
  have hstep2 : (6 * k + bergstraWeight b) + 1 ≤ bergstraWeight a + 1 :=
    Nat.add_le_add_right hw_le 1
  exact Nat.le_trans hstep1 (Nat.le_trans hstep2 ha_hi)

/-! ## 2. Exact Ranked Conservation Law (`leftSubtreeSum`), Global `SN` + `CR` of `LeafPresStep`,
    and the Quarter-Square $\Theta(|M|^2)$ Theorem -/

/-- Sum of left-child leaf counts across all application nodes (`L(a ⋅ b) = L(a) + L(b) + leaves a`). -/
def leftSubtreeSum : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app a b => leftSubtreeSum a + leftSubtreeSum b + leaves a

private theorem leftSubtreeSum_zero_of_leaves_one {z : Term} (hz1 : leaves z = 1) :
    leftSubtreeSum z = 0 := by
  cases z with
  | s => rfl
  | var _ => rfl
  | app p q =>
    have hp : 1 ≤ leaves p := leaves_pos p
    have hq : 1 ≤ leaves q := leaves_pos q
    have h2 : 2 ≤ leaves p + leaves q := Nat.add_le_add hp hq
    change leaves p + leaves q = 1 at hz1
    rw [hz1] at h2
    exact False.elim (absurd h2 (by decide))

/-- **Exact Ranked Conservation Identity**:
    Every leaf-preserving step `LeafPresStep a b` (at ANY depth in ANY open/closed term!)
    decreases `leftSubtreeSum` by **exact constant `2`**! -/
theorem leftSubtreeSum_leafPresStep {a b : Term} (hlp : LeafPresStep a b) :
    leftSubtreeSum a = leftSubtreeSum b + 2 := by
  rcases hlp with ⟨hs, heq⟩
  induction hs with
  | root x y z =>
    have hbal := step_leaves_balance .hole x y z
    change leaves ((x ⋅ z) ⋅ (y ⋅ z)) + 1 = leaves (S ⋅ x ⋅ y ⋅ z) + leaves z at hbal
    rw [← heq] at hbal
    have hz1 : leaves z = 1 := (Nat.add_left_cancel hbal).symm
    have hLz : leftSubtreeSum z = 0 := leftSubtreeSum_zero_of_leaves_one hz1
    change (((0 + leftSubtreeSum x + 1) + leftSubtreeSum y + (1 + leaves x)) +
      leftSubtreeSum z + (1 + leaves x + leaves y)) =
      ((leftSubtreeSum x + leftSubtreeSum z + leaves x) +
       (leftSubtreeSum y + leftSubtreeSum z + leaves y) + (leaves x + leaves z)) + 2
    rw [hz1, hLz]
    omega
  | @left l l' r _ ih =>
    have hleq : leaves l = leaves l' := Nat.add_right_cancel (heq : leaves l + leaves r = leaves l' + leaves r)
    have ih' := ih hleq
    change leftSubtreeSum l + leftSubtreeSum r + leaves l =
      (leftSubtreeSum l' + leftSubtreeSum r + leaves l') + 2
    rw [ih', hleq]
    omega
  | @right l r r' _ ih =>
    have hreq : leaves r = leaves r' := Nat.add_left_cancel (heq : leaves l + leaves r = leaves l + leaves r')
    have ih' := ih hreq
    change leftSubtreeSum l + leftSubtreeSum r + leaves l =
      (leftSubtreeSum l + leftSubtreeSum r' + leaves l) + 2
    rw [ih']
    omega

theorem leftSubtreeSum_leafPresStepsN {k : Nat} {a b : Term} (h : LeafPresStepsN k a b) :
    leftSubtreeSum a = leftSubtreeSum b + 2 * k := by
  induction h with
  | zero _ => simp only [Nat.mul_zero, Nat.add_zero]
  | @succ k0 _ _ c0 hs _ ih =>
    have hd := leftSubtreeSum_leafPresStep hs
    rw [hd, ih, Nat.mul_add, Nat.mul_one, Nat.add_assoc]

private theorem leafPres_sn_aux (B : Nat) :
    ∀ {t : Term}, leftSubtreeSum t ≤ B → Acc (fun b a => LeafPresStep a b) t := by
  induction B with
  | zero =>
    intro t hB
    refine Acc.intro t (fun b hlp => ?_)
    have hd := leftSubtreeSum_leafPresStep hlp
    rw [hd] at hB
    exact False.elim (Nat.not_succ_le_zero _ hB)
  | succ B ih =>
    intro t hB
    refine Acc.intro t (fun b hlp => ?_)
    have hd := leftSubtreeSum_leafPresStep hlp
    rw [hd] at hB
    exact ih (Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_succ _) hB))

/-- **Global Strong Normalization of Leaf-Preserving Reduction** on all open and closed pure-`S` terms! -/
theorem leafPres_sn (t : Term) : Acc (fun b a => LeafPresStep a b) t :=
  leafPres_sn_aux (leftSubtreeSum t) (Nat.le_refl _)

theorem leftSubtreeSum_bounds (t : Term) :
    leaves t ≤ leftSubtreeSum t + 1 ∧ 2 * leftSubtreeSum t + leaves t ≤ (leaves t) * (leaves t) := by
  induction t with
  | s => exact ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  | var _ => exact ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  | app a b iha ihb =>
    have hb : 1 ≤ leaves b := leaves_pos b
    have hcross : 2 * leaves a ≤ 2 * (leaves a * leaves b) :=
      Nat.mul_le_mul_left 2 (by
        have hm := Nat.mul_le_mul_left (leaves a) hb
        rw [Nat.mul_one] at hm; exact hm)
    have hsq : (leaves a + leaves b) * (leaves a + leaves b) =
        (leaves a * leaves a + leaves b * leaves b) + 2 * (leaves a * leaves b) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm (leaves b) (leaves a)]
      omega
    change leaves a + leaves b ≤ (leftSubtreeSum a + leftSubtreeSum b + leaves a) + 1 ∧
      2 * (leftSubtreeSum a + leftSubtreeSum b + leaves a) + (leaves a + leaves b) ≤
        (leaves a + leaves b) * (leaves a + leaves b)
    constructor
    · have h1 : leaves a + leaves b ≤ leaves a + (leftSubtreeSum b + 1) :=
        Nat.add_le_add_left ihb.1 (leaves a)
      have h2 : leaves a + (leftSubtreeSum b + 1) ≤ (leftSubtreeSum a + leftSubtreeSum b + leaves a) + 1 := by
        have heq : leaves a + (leftSubtreeSum b + 1) = (0 + leftSubtreeSum b + leaves a) + 1 := by
          omega
        rw [heq]
        exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.zero_le _) _) _) 1
      exact Nat.le_trans h1 h2
    · have hlhs : 2 * (leftSubtreeSum a + leftSubtreeSum b + leaves a) + (leaves a + leaves b) =
          ((2 * leftSubtreeSum a + leaves a) + (2 * leftSubtreeSum b + leaves b)) + 2 * leaves a := by
        rw [Nat.mul_add, Nat.mul_add]
        omega
      rw [hlhs, hsq]
      exact Nat.add_le_add (Nat.add_le_add iha.2 ihb.2) hcross

/-- **Quadratic $\Theta(|M|^2)$ Upper Bound on Consecutive Leaf-Preserving Steps** (`4k ≤ (|a|-1)(|a|-2)`):
    Exponentially strengthens Bergstra's `O(2^|a|)` bound for ALL open and closed pure-`S` terms! -/
theorem leafPresStepsN_quadratic_upper_bound {k : Nat} {a b : Term} (h : LeafPresStepsN k a b) :
    4 * k ≤ (leaves a - 1) * (leaves a - 2) := by
  have hlen := leftSubtreeSum_leafPresStepsN h
  have ⟨hl_eq, _, _⟩ := bergstra_leafPres_exp_bound h
  have ⟨hb_lo, _⟩ := leftSubtreeSum_bounds b
  have ⟨_, ha_hi⟩ := leftSubtreeSum_bounds a
  rw [← hl_eq] at hb_lo
  have hpos : 1 ≤ leaves a := leaves_pos a
  cases n : leaves a with
  | zero => rw [n] at hpos; cases hpos
  | succ m =>
    rw [n] at hb_lo ha_hi
    cases m with
    | zero =>
      change 4 * k ≤ 0 * 0
      rw [hlen] at ha_hi
      have h0 : 2 * (leftSubtreeSum b + 2 * k) ≤ 0 :=
        Nat.le_of_add_le_add_right (ha_hi : 2 * (leftSubtreeSum b + 2 * k) + 1 ≤ 0 + 1)
      have h4k_le : 4 * k ≤ 2 * (leftSubtreeSum b + 2 * k) := by
        have heq : 2 * (leftSubtreeSum b + 2 * k) = 2 * leftSubtreeSum b + 4 * k := by
          rw [Nat.mul_add, ← Nat.mul_assoc]
        rw [heq]
        exact Nat.le_add_left _ _
      exact Nat.le_trans h4k_le h0
    | succ m0 =>
      change 4 * k ≤ (m0 + 1) * m0
      have hb_m0 : m0 + 1 ≤ leftSubtreeSum b := Nat.le_of_succ_le_succ hb_lo
      rw [hlen] at ha_hi
      have hlhs : 4 * k + (2 * (m0 + 1) + (m0 + 2)) ≤ 2 * (leftSubtreeSum b + 2 * k) + (m0 + 2) := by
        have h1 : 2 * (m0 + 1) + 4 * k ≤ 2 * (leftSubtreeSum b + 2 * k) := by
          have hr : 2 * (leftSubtreeSum b + 2 * k) = 2 * leftSubtreeSum b + 4 * k := by
            rw [Nat.mul_add, ← Nat.mul_assoc]
          rw [hr]
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hb_m0) (4 * k)
        have hcomm : 4 * k + (2 * (m0 + 1) + (m0 + 2)) = (2 * (m0 + 1) + 4 * k) + (m0 + 2) := by
          rw [← Nat.add_assoc, Nat.add_comm (4 * k) (2 * (m0 + 1))]
        rw [hcomm]
        exact Nat.add_le_add_right h1 (m0 + 2)
      have hrhs : (m0 + 2) * (m0 + 2) = (m0 + 1) * m0 + (2 * (m0 + 1) + (m0 + 2)) := by
        have hstep : (m0 + 2) * (m0 + 2) = ((m0 + 1) + 1) * (m0 + 2) := rfl
        rw [hstep, Nat.add_mul, Nat.one_mul, Nat.mul_add (m0 + 1) m0 2,
            Nat.mul_comm (m0 + 1) 2, Nat.add_assoc]
      rw [hrhs] at ha_hi
      exact Nat.le_of_add_le_add_right (Nat.le_trans hlhs ha_hi)

/-! ### Global Confluence (`leafPres_church_rosser`) & Jordan–Hölder Ranked Diamond Theorem -/

inductive ParLP : Term → Term → Prop where
  | s : ParLP .s .s
  | var (k : Nat) : ParLP (.var k) (.var k)
  | app {a a' b b' : Term} : ParLP a a' → ParLP b b' → ParLP (a ⋅ b) (a' ⋅ b')
  | beta {x x' y y' z : Term} :
      ParLP x x' → ParLP y y' → leaves z = 1 →
      ParLP (S ⋅ x ⋅ y ⋅ z) ((x' ⋅ z) ⋅ (y' ⋅ z))

private theorem parLP_refl (t : Term) : ParLP t t := by
  induction t with
  | s => exact .s
  | var k => exact .var k
  | app _ _ iha ihb => exact .app iha ihb

private theorem parLP_eq_of_leaves_one {z b : Term} (hz1 : leaves z = 1) (h : ParLP z b) : b = z := by
  cases z with
  | s => cases h; rfl
  | var k => cases h; rfl
  | app p q =>
    have hp : 1 ≤ leaves p := leaves_pos p
    have hq : 1 ≤ leaves q := leaves_pos q
    have h2 : 2 ≤ leaves p + leaves q := Nat.add_le_add hp hq
    change leaves p + leaves q = 1 at hz1
    rw [hz1] at h2
    exact False.elim (absurd h2 (by decide))

private theorem leafPresStep_to_parLP {a b : Term} (h : LeafPresStep a b) : ParLP a b := by
  rcases h with ⟨hs, heq⟩
  induction hs with
  | root x y z =>
    have hbal := step_leaves_balance .hole x y z
    change leaves ((x ⋅ z) ⋅ (y ⋅ z)) + 1 = leaves (S ⋅ x ⋅ y ⋅ z) + leaves z at hbal
    rw [← heq] at hbal
    exact .beta (parLP_refl x) (parLP_refl y) (Nat.add_left_cancel hbal).symm
  | @left l l' r _ ih =>
    have hleq : leaves l = leaves l' := Nat.add_right_cancel (heq : leaves l + leaves r = leaves l' + leaves r)
    exact .app (ih hleq) (parLP_refl r)
  | @right l r r' _ ih =>
    have hreq : leaves r = leaves r' := Nat.add_left_cancel (heq : leaves l + leaves r = leaves l + leaves r')
    exact .app (parLP_refl l) (ih hreq)

theorem leafPresReduces_trans {a b c : Term}
    (h1 : LeafPresReduces a b) (h2 : LeafPresReduces b c) : LeafPresReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem leafPresReduces_left {a a' : Term} (h : LeafPresReduces a a') (b : Term) :
    LeafPresReduces (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih =>
    exact .next ⟨FormalAlgebra.Step.left hs.1, by change leaves _ + leaves b = leaves _ + leaves b; rw [hs.2]⟩ ih

theorem leafPresReduces_right (a : Term) {b b' : Term} (h : LeafPresReduces b b') :
    LeafPresReduces (a ⋅ b) (a ⋅ b') := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih =>
    exact .next ⟨FormalAlgebra.Step.right hs.1, by change leaves a + leaves _ = leaves a + leaves _; rw [hs.2]⟩ ih

private theorem parLP_to_leafPresReduces {a b : Term} (h : ParLP a b) : LeafPresReduces a b := by
  induction h with
  | s => exact .refl .s
  | var k => exact .refl (.var k)
  | app _ _ iha ihb => exact leafPresReduces_trans (leafPresReduces_left iha _) (leafPresReduces_right _ ihb)
  | @beta x x' y y' z _ _ hz1 ihx ihy =>
    have h1 := leafPresReduces_left
      (leafPresReduces_trans (leafPresReduces_left (leafPresReduces_right S ihx) y)
        (leafPresReduces_right (S ⋅ x') ihy)) z
    have hbal := step_leaves_balance .hole x' y' z
    change leaves ((x' ⋅ z) ⋅ (y' ⋅ z)) + 1 = leaves (S ⋅ x' ⋅ y' ⋅ z) + leaves z at hbal
    rw [hz1] at hbal
    have hroot : LeafPresStep (S ⋅ x' ⋅ y' ⋅ z) ((x' ⋅ z) ⋅ (y' ⋅ z)) :=
      ⟨FormalAlgebra.Step.root x' y' z, (Nat.add_right_cancel hbal).symm⟩
    exact leafPresReduces_trans h1 (.next hroot (.refl _))

def completeDevLP : Term → Term
  | .app (.app (.app .s x) y) z =>
    if leaves z = 1 then (completeDevLP x ⋅ z) ⋅ (completeDevLP y ⋅ z)
    else ((S ⋅ completeDevLP x) ⋅ completeDevLP y) ⋅ completeDevLP z
  | .app a b => completeDevLP a ⋅ completeDevLP b
  | .s => .s
  | .var k => .var k

private theorem completeDevLP_non_redex (a b : Term) (hnot : ∀ x y, a ≠ S ⋅ x ⋅ y) :
    completeDevLP (a ⋅ b) = completeDevLP a ⋅ completeDevLP b := by
  cases a with
  | s => rfl
  | var _ => rfl
  | app a1 y =>
    cases a1 with
    | s => rfl
    | var _ => rfl
    | app a2 x =>
      cases a2 with
      | s => exfalso; exact hnot x y rfl
      | var _ => rfl
      | app _ _ => rfl

private theorem parLP_triangle {a b : Term} (h : ParLP a b) : ParLP b (completeDevLP a) := by
  induction h with
  | s => exact .s
  | var k => exact .var k
  | @beta x x' y y' z _ _ hz1 ihx ihy =>
    change ParLP ((x' ⋅ z) ⋅ (y' ⋅ z))
      (if leaves z = 1 then (completeDevLP x ⋅ z) ⋅ (completeDevLP y ⋅ z)
       else ((S ⋅ completeDevLP x) ⋅ completeDevLP y) ⋅ completeDevLP z)
    rw [if_pos hz1]
    exact .app (.app ihx (parLP_refl z)) (.app ihy (parLP_refl z))
  | @app a a' b b' ha hb iha ihb =>
    cases a with
    | s => cases ha; exact .app .s ihb
    | var k => cases ha; exact .app (.var k) ihb
    | app a1 y =>
      cases a1 with
      | s =>
        cases ha with
        | app hs _ =>
          cases hs
          cases iha with
          | app _ ihy => exact .app (.app .s ihy) ihb
      | var k =>
        rw [completeDevLP_non_redex (.var k ⋅ y) b (fun _ _ h => by injection h with h1 _; cases h1)]
        exact .app iha ihb
      | app a2 x =>
        cases a2 with
        | var k =>
          rw [completeDevLP_non_redex (.var k ⋅ x ⋅ y) b
            (fun _ _ h => by injection h with h1 _; injection h1 with h2 _; cases h2)]
          exact .app iha ihb
        | app u v =>
          rw [completeDevLP_non_redex (u ⋅ v ⋅ x ⋅ y) b
            (fun _ _ h => by injection h with h1 _; injection h1 with h2 _; cases h2)]
          exact .app iha ihb
        | s =>
          change ParLP (a' ⋅ b')
            (if leaves b = 1 then (completeDevLP x ⋅ b) ⋅ (completeDevLP y ⋅ b)
             else ((S ⋅ completeDevLP x) ⋅ completeDevLP y) ⋅ completeDevLP b)
          cases hd : decide (leaves b = 1) with
          | true =>
            have hz1 : leaves b = 1 := of_decide_eq_true hd
            rw [if_pos hz1]
            have hb_eq : b' = b := parLP_eq_of_leaves_one hz1 hb
            subst hb_eq
            cases ha with
            | app ha1 _ =>
              cases ha1 with
              | app hs _ =>
                cases hs
                cases iha with
                | app hsx ihy =>
                  cases hsx with
                  | app _ ihx => exact .beta ihx ihy hz1
          | false =>
            have hnz : leaves b ≠ 1 := of_decide_eq_false hd
            rw [if_neg hnz]
            exact .app iha ihb

private inductive ParLPReduces : Term → Term → Prop where
  | refl (a : Term) : ParLPReduces a a
  | next {a b c : Term} : ParLP a b → ParLPReduces b c → ParLPReduces a c

private theorem parLPReduces_to_leafPres {a b : Term} (h : ParLPReduces a b) : LeafPresReduces a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact leafPresReduces_trans (parLP_to_leafPresReduces hs) ih

private theorem leafPres_to_parLPReduces {a b : Term} (h : LeafPresReduces a b) : ParLPReduces a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (leafPresStep_to_parLP hs) ih

private theorem parLP_strip {a b c : Term} (hab : ParLP a b) (hac : ParLPReduces a c) :
    ∃ d, ParLPReduces b d ∧ ParLP c d := by
  induction hac generalizing b with
  | refl _ => exact ⟨b, .refl b, hab⟩
  | next ha1 _ ih =>
    have hm1 := parLP_triangle ha1
    have hbm := parLP_triangle hab
    obtain ⟨d, hmd, hcd⟩ := ih hm1
    exact ⟨d, .next hbm hmd, hcd⟩

private theorem parLPReduces_confluence {a b c : Term}
    (hab : ParLPReduces a b) (hac : ParLPReduces a c) :
    ∃ d, ParLPReduces b d ∧ ParLPReduces c d := by
  induction hab generalizing c with
  | refl _ => exact ⟨c, hac, .refl c⟩
  | next ha1 _ ih =>
    obtain ⟨m, ha1m, hcm⟩ := parLP_strip ha1 hac
    obtain ⟨d, hbd, hmd⟩ := ih ha1m
    exact ⟨d, hbd, .next hcm hmd⟩

/-- **Global Church–Rosser Theorem for Leaf-Preserving Reduction (`LeafPresReduces`)**: -/
theorem leafPres_church_rosser {a b c : Term}
    (hab : LeafPresReduces a b) (hac : LeafPresReduces a c) :
    ∃ d, LeafPresReduces b d ∧ LeafPresReduces c d := by
  obtain ⟨d, hbd, hcd⟩ := parLPReduces_confluence
    (leafPres_to_parLPReduces hab) (leafPres_to_parLPReduces hac)
  exact ⟨d, parLPReduces_to_leafPres hbd, parLPReduces_to_leafPres hcd⟩

private theorem leafPresStepsN_to_reduces {k : Nat} {a b : Term} (h : LeafPresStepsN k a b) :
    LeafPresReduces a b := by
  induction h with
  | zero _ => exact .refl _
  | succ hs _ ih => exact .next hs ih

private theorem leafPresReduces_eq_of_nf {a d : Term} (hnf : IsLeafPresNF a) (h : LeafPresReduces a d) :
    d = a := by
  cases h with
  | refl _ => rfl
  | next hs _ => exfalso; exact hnf _ hs

/-- **Jordan–Hölder / Ranked Unique-Normal-Form Theorem for Leaf-Preserving Reduction**:
    Any two leaf-preserving reductions from `a` to leaf-preserving normal forms `nf1` and `nf2`
    reach the **exact same normal form (`nf1 = nf2`) in the exact same number of steps (`k1 = k2`)**! -/
theorem leafPres_jordan_holder {k1 k2 : Nat} {a nf1 nf2 : Term}
    (h1 : LeafPresStepsN k1 a nf1) (h2 : LeafPresStepsN k2 a nf2)
    (hnf1 : IsLeafPresNF nf1) (hnf2 : IsLeafPresNF nf2) :
    nf1 = nf2 ∧ k1 = k2 := by
  obtain ⟨d, hd1, hd2⟩ := leafPres_church_rosser
    (leafPresStepsN_to_reduces h1) (leafPresStepsN_to_reduces h2)
  have e1 : d = nf1 := leafPresReduces_eq_of_nf hnf1 hd1
  have e2 : d = nf2 := leafPresReduces_eq_of_nf hnf2 hd2
  have hnf_eq : nf1 = nf2 := e1.symm.trans e2
  have hl1 := leftSubtreeSum_leafPresStepsN h1
  have hl2 := leftSubtreeSum_leafPresStepsN h2
  rw [hnf_eq] at hl1
  have h2k : 2 * k1 = 2 * k2 := Nat.add_left_cancel (hl1.symm.trans hl2)
  exact ⟨hnf_eq, Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2k⟩

/-! ### Exact Quarter-Square (`⌊(n - 2)^2 / 4⌋`) Reduction of `leftComb n` to `leftCombLPNF n` -/

def leftCombLPNF : Nat → Term
  | 0 => S
  | 1 => S
  | 2 => S ⋅ S
  | 3 => S ⋅ S ⋅ S
  | m + 4 => (S ⋅ S) ⋅ leftCombLPNF (m + 2)

private theorem leaves_leftCombLPNF_aux (B : Nat) :
    ∀ n, n ≤ B → 1 ≤ n → leaves (leftCombLPNF n) = n := by
  induction B with
  | zero =>
    intro n hn0 h1
    cases Nat.eq_zero_of_le_zero hn0
    cases h1
  | succ B ih =>
    intro n hnB h1
    cases n with
    | zero => cases h1
    | succ n1 =>
      cases n1 with
      | zero => rfl
      | succ n2 =>
        cases n2 with
        | zero => rfl
        | succ n3 =>
          cases n3 with
          | zero => rfl
          | succ m =>
            change 2 + leaves (leftCombLPNF (m + 2)) = m + 4
            have hmB : m + 2 ≤ B :=
              Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_succ (m + 3)) hnB)
            rw [ih (m + 2) hmB (Nat.succ_le_succ (Nat.zero_le (m + 1)))]
            exact Nat.add_comm 2 (m + 2)

theorem leaves_leftCombLPNF {n : Nat} (hn : 1 ≤ n) : leaves (leftCombLPNF n) = n :=
  leaves_leftCombLPNF_aux n n (Nat.le_refl n) hn

private theorem isLeafPresNF_leftCombLPNF_aux (B : Nat) :
    ∀ n, n ≤ B → IsLeafPresNF (leftCombLPNF n) := by
  induction B with
  | zero =>
    intro n hn0
    cases Nat.eq_zero_of_le_zero hn0
    intro _ ⟨hs, _⟩
    cases hs
  | succ B ih =>
    intro n hnB
    cases n with
    | zero => intro _ ⟨hs, _⟩; cases hs
    | succ n1 =>
      cases n1 with
      | zero => intro _ ⟨hs, _⟩; cases hs
      | succ n2 =>
        cases n2 with
        | zero =>
          intro _ ⟨hs, _⟩
          cases hs with
          | left hl => cases hl
          | right hr => cases hr
        | succ n3 =>
          cases n3 with
          | zero =>
            intro _ ⟨hs, _⟩
            cases hs with
            | left hl =>
              cases hl with
              | left hll => cases hll
              | right hlr => cases hlr
            | right hr => cases hr
          | succ m =>
            intro u ⟨hs, heq⟩
            change Step ((S ⋅ S) ⋅ leftCombLPNF (m + 2)) u at hs
            cases hs with
            | left hl =>
              cases hl with
              | left hll => cases hll
              | right hlr => cases hlr
            | @right _ _ r' hr =>
              have hreq : leaves (leftCombLPNF (m + 2)) = leaves r' :=
                Nat.add_left_cancel (heq : 2 + leaves (leftCombLPNF (m + 2)) = 2 + leaves r')
              have hmB : m + 2 ≤ B :=
                Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_succ (m + 3)) hnB)
              exact ih (m + 2) hmB r' ⟨hr, hreq⟩

theorem isLeafPresNF_leftCombLPNF (n : Nat) : IsLeafPresNF (leftCombLPNF n) :=
  isLeafPresNF_leftCombLPNF_aux n n (Nat.le_refl n)

private theorem leafPresStepsN_trans {k1 k2 : Nat} {a b c : Term}
    (h1 : LeafPresStepsN k1 a b) (h2 : LeafPresStepsN k2 b c) :
    LeafPresStepsN (k1 + k2) a c := by
  induction h1 with
  | zero _ => rw [Nat.zero_add]; exact h2
  | @succ k0 _ _ _ hs _ ih =>
    rw [Nat.succ_add]
    exact .succ hs (ih h2)

private theorem leafPresStepsN_left {k : Nat} {a a' : Term}
    (h : LeafPresStepsN k a a') (b : Term) :
    LeafPresStepsN k (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | zero _ => exact .zero _
  | succ hs _ ih =>
    exact .succ ⟨FormalAlgebra.Step.left hs.1, by change leaves _ + leaves b = leaves _ + leaves b; rw [hs.2]⟩ ih

private theorem leafPresStepsN_right (a : Term) {k : Nat} {b b' : Term}
    (h : LeafPresStepsN k b b') :
    LeafPresStepsN k (a ⋅ b) (a ⋅ b') := by
  induction h with
  | zero _ => exact .zero _
  | succ hs _ ih =>
    exact .succ ⟨FormalAlgebra.Step.right hs.1, by change leaves a + leaves _ = leaves a + leaves _; rw [hs.2]⟩ ih

private theorem leftComb_peel_step (m : Nat) :
    LeafPresStepsN (m + 1) (leftComb (m + 4)) ((S ⋅ S) ⋅ leftComb (m + 2)) := by
  induction m with
  | zero =>
    exact .succ ⟨FormalAlgebra.Step.root S S S, rfl⟩ (.zero _)
  | succ m ih =>
    have h1 : LeafPresStepsN (m + 1) (leftComb (m + 4) ⋅ S) (((S ⋅ S) ⋅ leftComb (m + 2)) ⋅ S) :=
      leafPresStepsN_left ih S
    have hbal := step_leaves_balance .hole S (leftComb (m + 2)) S
    change leaves ((S ⋅ S) ⋅ (leftComb (m + 2) ⋅ S)) + 1 =
      leaves (((S ⋅ S) ⋅ leftComb (m + 2)) ⋅ S) + 1 at hbal
    have h2 : LeafPresStepsN 1 (((S ⋅ S) ⋅ leftComb (m + 2)) ⋅ S) ((S ⋅ S) ⋅ (leftComb (m + 2) ⋅ S)) :=
      .succ ⟨FormalAlgebra.Step.root S (leftComb (m + 2)) S, (Nat.add_right_cancel hbal).symm⟩ (.zero _)
    exact leafPresStepsN_trans h1 h2

private theorem add_four_mul_div_four (a k : Nat) :
    (a + 4 * k) / 4 = a / 4 + k := by
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.add_zero]
  | succ k ih =>
    have hstep : a + 4 * (k + 1) = (a + 4 * k) + 4 := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
    rw [hstep, Nat.add_div_right (a + 4 * k) (by decide : 0 < 4), ih, Nat.add_assoc]

private theorem leftComb_quarter_square_aux (B : Nat) :
    ∀ n, n ≤ B → 2 ≤ n →
      LeafPresStepsN (((n - 2) * (n - 2)) / 4) (leftComb n) (leftCombLPNF n) := by
  induction B with
  | zero =>
    intro n hn0 h2
    cases Nat.eq_zero_of_le_zero hn0
    cases h2
  | succ B ih =>
    intro n hnB h2
    cases n with
    | zero => cases h2
    | succ n1 =>
      cases n1 with
      | zero => exact False.elim (absurd h2 (by decide))
      | succ n2 =>
        cases n2 with
        | zero => exact .zero (S ⋅ S)
        | succ n3 =>
          cases n3 with
          | zero => exact .zero (S ⋅ S ⋅ S)
          | succ m =>
            have hmB : m + 2 ≤ B :=
              Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_succ (m + 3)) hnB)
            have hpeel := leftComb_peel_step m
            have hsub := leafPresStepsN_right (S ⋅ S) (ih (m + 2) hmB (Nat.le_add_left 2 m))
            change LeafPresStepsN ((m * m) / 4) _ _ at hsub
            have hcomb := leafPresStepsN_trans hpeel hsub
            change LeafPresStepsN (((m + 2) * (m + 2)) / 4) (leftComb (m + 4)) ((S ⋅ S) ⋅ leftCombLPNF (m + 2))
            have hexp : (m + 2) * (m + 2) = m * m + 4 * (m + 1) := by
              rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_assoc (m * m)]
              refine congrArg (m * m + ·) ?_
              rw [Nat.mul_comm m 2, ← Nat.add_assoc (2 * m) (2 * m) (2 * 2),
                  ← Nat.add_mul 2 2 m, Nat.mul_add 4 m 1]
            have hq : (m + 1) + ((m * m) / 4) = ((m + 2) * (m + 2)) / 4 := by
              rw [hexp, add_four_mul_div_four (m * m) (m + 1), Nat.add_comm]
            rw [hq] at hcomb
            exact hcomb

/-- **Exact Quarter-Square Theorem for `leftComb n`**:
    For **every** `n ≥ 2`, `leftComb n` reduces to its unique leaf-preserving normal form
    `leftCombLPNF n` in **exact** `((n - 2) * (n - 2)) / 4` leaf-preserving steps! -/
theorem leftComb_leafPres_quarter_square {n : Nat} (hn : 2 ≤ n) :
    LeafPresStepsN (((n - 2) * (n - 2)) / 4) (leftComb n) (leftCombLPNF n) ∧
    IsLeafPresNF (leftCombLPNF n) :=
  ⟨leftComb_quarter_square_aux n n (Nat.le_refl n) hn, isLeafPresNF_leftCombLPNF n⟩

/-! ## 3. Isolated Normal Forms (`IsIsolatedNF`) & Question 30 Singleton Convertibility Classes -/

def HasNoPredecessor (t : Term) : Prop :=
  ∀ m, ¬ Step m t

/-- An **Isolated Normal Form** has neither outgoing nor incoming 1-step reductions in `CL(S)`. -/
def IsIsolatedNF (t : Term) : Prop :=
  IsNormalForm t ∧ HasNoPredecessor t

theorem convS_iff_reduces_join {a b : Term} :
    ConvS a b ↔ ∃ d, Reduces a d ∧ Reduces b d := by
  constructor
  · intro hc
    induction hc with
    | refl x => exact ⟨x, .refl x, .refl x⟩
    | step hs => exact ⟨_, .next hs (.refl _), .refl _⟩
    | symm _ ih =>
      obtain ⟨d, h1, h2⟩ := ih
      exact ⟨d, h2, h1⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨d1, ha1, hb1⟩ := ih1
      obtain ⟨d2, hb2, hc2⟩ := ih2
      obtain ⟨d, hd1, hd2⟩ := church_rosser hb1 hb2
      exact ⟨d, reduces_trans ha1 hd1, reduces_trans hc2 hd2⟩
  · intro ⟨d, had, hbd⟩
    have toConv : ∀ {x y}, Reduces x y → ConvS x y := by
      intro x y hr
      induction hr with
      | refl _ => exact .refl _
      | next hs _ ih => exact .trans (.step hs) ih
    exact .trans (toConv had) (.symm (toConv hbd))

private theorem reduces_eq_of_nf {t d : Term} (hnf : IsNormalForm t) (hr : Reduces t d) : d = t := by
  cases hr with
  | refl _ => rfl
  | next hs _ => exfalso; exact hnf _ hs

private theorem reduces_last_step_or_eq {u t : Term} (hr : Reduces u t) :
    u = t ∨ ∃ m, Step m t := by
  induction hr with
  | refl _ => exact Or.inl rfl
  | @next _ b _ hs _ ih =>
    rcases ih with rfl | ⟨m, hm⟩
    · exact Or.inr ⟨_, hs⟩
    · exact Or.inr ⟨m, hm⟩

/-- **Question 30 Singleton Convertibility Class Theorem**:
    For **every** open or closed pure-`S` term `t`, `[t]_{=S} = {t}` (`∀ u, ConvS t u ↔ u = t`)
    holds **iff** `t` is an Isolated Normal Form! -/
theorem convS_singleton_iff_isolatedNF (t : Term) :
    (∀ u, ConvS t u ↔ u = t) ↔ IsIsolatedNF t := by
  constructor
  · intro hsing
    refine ⟨fun u hs => ?_, fun m hm => ?_⟩
    · have heq : u = t := (hsing u).mp (.step hs)
      subst heq
      exact bergstra_no_cycle u (.single hs)
    · have heq : m = t := (hsing m).mp (.symm (.step hm))
      subst heq
      exact bergstra_no_cycle m (.single hm)
  · intro ⟨hnf, hnopred⟩ u
    constructor
    · intro hc
      obtain ⟨d, htd, hud⟩ := convS_iff_reduces_join.mp hc
      have hd : d = t := reduces_eq_of_nf hnf htd
      subst hd
      rcases reduces_last_step_or_eq hud with rfl | ⟨m, hm⟩
      · rfl
      · exfalso; exact hnopred m hm
    · intro hu
      subst hu
      exact .refl _

/-! ### Exact Linear-Time Boolean Deciders for `HasNoPredecessor`, `IsNormalForm`, and `IsIsolatedNF` -/

def isContractumNode : Term → Bool
  | .app (.app _ z1) (.app _ z2) => decide (z1 = z2)
  | _ => false

def hasContractumSubterm : Term → Bool
  | .s => false
  | .var _ => false
  | .app a b => isContractumNode (.app a b) || hasContractumSubterm a || hasContractumSubterm b

private theorem isContractumNode_iff (t : Term) :
    isContractumNode t = true ↔ ∃ x y z, t = (x ⋅ z) ⋅ (y ⋅ z) := by
  cases t with
  | s => exact ⟨fun h => (by cases h), fun ⟨_, ⟨_, ⟨_, h⟩⟩⟩ => (by cases h)⟩
  | var _ => exact ⟨fun h => (by cases h), fun ⟨_, ⟨_, ⟨_, h⟩⟩⟩ => (by cases h)⟩
  | app l r =>
    cases l with
    | s => exact ⟨fun h => (by cases h), fun ⟨_, ⟨_, ⟨_, h⟩⟩⟩ => (by injection h with h1 _; cases h1)⟩
    | var _ => exact ⟨fun h => (by cases h), fun ⟨_, ⟨_, ⟨_, h⟩⟩⟩ => (by injection h with h1 _; cases h1)⟩
    | app x z1 =>
      cases r with
      | s => exact ⟨fun h => (by cases h), fun ⟨_, ⟨_, ⟨_, h⟩⟩⟩ => (by injection h with _ h2; cases h2)⟩
      | var _ => exact ⟨fun h => (by cases h), fun ⟨_, ⟨_, ⟨_, h⟩⟩⟩ => (by injection h with _ h2; cases h2)⟩
      | app y z2 =>
        change decide (z1 = z2) = true ↔ ∃ x' y' z', (x ⋅ z1) ⋅ (y ⋅ z2) = (x' ⋅ z') ⋅ (y' ⋅ z')
        constructor
        · intro hd
          have heq := of_decide_eq_true hd
          subst heq
          exact ⟨x, y, z1, rfl⟩
        · rintro ⟨_, _, _, h⟩
          injection h with h1 h2
          injection h1 with _ hz1
          injection h2 with _ hz2
          exact decide_eq_true (hz1.trans hz2.symm)

theorem hasContractumSubterm_iff_exists_pred (t : Term) :
    hasContractumSubterm t = true ↔ ∃ m, Step m t := by
  induction t with
  | s =>
    exact ⟨fun h => (by cases h), fun ⟨_, hs⟩ => (by cases hs)⟩
  | var _ =>
    exact ⟨fun h => (by cases h), fun ⟨_, hs⟩ => (by cases hs)⟩
  | app a b iha ihb =>
    change (isContractumNode (a ⋅ b) || hasContractumSubterm a || hasContractumSubterm b) = true ↔
      ∃ m, Step m (a ⋅ b)
    simp only [Bool.or_eq_true, isContractumNode_iff, iha, ihb]
    constructor
    · rintro ((⟨x, y, z, heq⟩ | ⟨ma, hsa⟩) | ⟨mb, hsb⟩)
      · rw [heq]; exact ⟨S ⋅ x ⋅ y ⋅ z, FormalAlgebra.Step.root x y z⟩
      · exact ⟨ma ⋅ b, FormalAlgebra.Step.left hsa⟩
      · exact ⟨a ⋅ mb, FormalAlgebra.Step.right hsb⟩
    · rintro ⟨m, hs⟩
      cases hs with
      | root x y z => exact Or.inl (Or.inl ⟨x, y, z, rfl⟩)
      | left hsa => exact Or.inl (Or.inr ⟨_, hsa⟩)
      | right hsb => exact Or.inr ⟨_, hsb⟩

theorem hasNoPredecessor_iff (t : Term) :
    HasNoPredecessor t ↔ hasContractumSubterm t = false := by
  unfold HasNoPredecessor
  cases hc : hasContractumSubterm t with
  | false =>
    refine ⟨fun _ => rfl, fun _ m hm => ?_⟩
    have ht := (hasContractumSubterm_iff_exists_pred t).mpr ⟨m, hm⟩
    rw [hc] at ht
    cases ht
  | true =>
    obtain ⟨m, hm⟩ := (hasContractumSubterm_iff_exists_pred t).mp hc
    exact ⟨fun hno => False.elim (hno m hm), fun h => by cases h⟩

theorem noVars_of_step_target {m t : Term} (hs : Step m t) (hv : noVars t = true) :
    noVars m = true := by
  induction hs with
  | root x y z =>
    simp only [FormalAlgebra.noVars, Bool.and_eq_true] at hv ⊢
    exact ⟨⟨⟨rfl, hv.1.1⟩, hv.2.1⟩, hv.1.2⟩
  | left _ ih =>
    simp only [FormalAlgebra.noVars, Bool.and_eq_true] at hv ⊢
    exact ⟨ih hv.1, hv.2⟩
  | right _ ih =>
    simp only [FormalAlgebra.noVars, Bool.and_eq_true] at hv ⊢
    exact ⟨hv.1, ih hv.2⟩

/-- For closed `t`, absence of open predecessors and absence of closed predecessors coincide! -/
theorem closed_hasNoPredecessor_iff_closedPred {t : Term} (hv : noVars t = true) :
    HasNoPredecessor t ↔ (∀ m, noVars m = true → ¬ Step m t) :=
  ⟨fun h m _ hm => h m hm, fun h m hm => h m (noVars_of_step_target hm hv) hm⟩

def endsWithArg : Term → Term → Bool
  | .app _ z, a => decide (z = a)
  | _, _ => false

def isClosedNFBool : Term → Bool
  | .s => true
  | .var _ => false
  | .app .s a => isClosedNFBool a
  | .app (.app .s a) b => isClosedNFBool a && isClosedNFBool b
  | .app _ _ => false

def isIsolatedClosedNF : Term → Bool
  | .s => true
  | .var _ => false
  | .app .s a => isIsolatedClosedNF a
  | .app (.app .s a) b => !endsWithArg b a && isIsolatedClosedNF a && isIsolatedClosedNF b
  | .app _ _ => false

theorem isClosedNFBool_iff (t : Term) :
    isClosedNFBool t = true ↔ (noVars t = true ∧ IsNormalForm t) := by
  induction t with
  | s => exact ⟨fun _ => ⟨rfl, fun _ hs => (by cases hs)⟩, fun _ => rfl⟩
  | var _ => exact ⟨fun h => (by cases h), fun ⟨hv, _⟩ => (by cases hv)⟩
  | app l b ihl ihb =>
    cases l with
    | s =>
      change isClosedNFBool b = true ↔ (noVars (S ⋅ b) = true ∧ IsNormalForm (S ⋅ b))
      rw [ihb]
      constructor
      · intro ⟨hvb, hnfb⟩
        refine ⟨(Bool.and_eq_true _ _).mpr ⟨rfl, hvb⟩, fun u hs => ?_⟩
        cases hs with
        | left hl => cases hl
        | right hr => exact hnfb _ hr
      · intro ⟨hv, hnf⟩
        exact ⟨((Bool.and_eq_true _ _).mp hv).2, fun b' hb => hnf (S ⋅ b') (FormalAlgebra.Step.right hb)⟩
    | var _ =>
      exact ⟨fun h => (by cases h), fun ⟨hv, _⟩ => (by
        have hvl := ((Bool.and_eq_true _ _).mp hv).1; cases hvl)⟩
    | app l1 a =>
      cases l1 with
      | s =>
        change (isClosedNFBool a && isClosedNFBool b) = true ↔
          (noVars (S ⋅ a ⋅ b) = true ∧ IsNormalForm (S ⋅ a ⋅ b))
        have iha' : isClosedNFBool a = true ↔ (noVars (S ⋅ a) = true ∧ IsNormalForm (S ⋅ a)) := ihl
        rw [Bool.and_eq_true, iha', ihb]
        constructor
        · intro ⟨⟨hva, hnfsa⟩, ⟨hvb, hnfb⟩⟩
          refine ⟨(Bool.and_eq_true _ _).mpr ⟨hva, hvb⟩, fun u hs => ?_⟩
          cases hs with
          | left hl => exact hnfsa _ hl
          | right hr => exact hnfb _ hr
        · intro ⟨hv, hnf⟩
          have ⟨hvsa, hvb⟩ := (Bool.and_eq_true _ _).mp hv
          exact ⟨⟨hvsa, fun u hl => hnf (u ⋅ b) (FormalAlgebra.Step.left hl)⟩,
                 ⟨hvb, fun b' hr => hnf (S ⋅ a ⋅ b') (FormalAlgebra.Step.right hr)⟩⟩
      | var _ =>
        exact ⟨fun h => (by cases h), fun ⟨hv, _⟩ => (by
          have hv1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv).1).1
          cases hv1)⟩
      | app l2 x =>
        constructor
        · intro h; cases h
        · intro ⟨hv, hnf⟩
          exfalso
          have hhnone : headStepOpt (l2 ⋅ x ⋅ a ⋅ b) = none := by
            cases hh : headStepOpt (l2 ⋅ x ⋅ a ⋅ b) with
            | none => rfl
            | some w => exfalso; exact hnf w (headStep_to_step (headStepOpt_some hh))
          have hsl := headStepOpt_none_spineLen hv hhnone
          change 1 + (1 + (1 + spineLen l2)) ≤ 2 at hsl
          have h3 : 3 ≤ 1 + (1 + (1 + spineLen l2)) := by
            rw [Nat.add_comm 1 (spineLen l2), Nat.add_comm 1 (spineLen l2 + 1),
                Nat.add_comm 1 (spineLen l2 + 1 + 1)]
            exact Nat.le_add_left 3 (spineLen l2)
          exact absurd (Nat.le_trans h3 hsl) (by decide)

/-- **Exact Syntactic & Algorithmic Characterization of Isolated Closed Normal Forms**:
    `isIsolatedClosedNF t = true ↔ (noVars t = true ∧ IsIsolatedNF t)`! -/
theorem isIsolatedClosedNF_iff (t : Term) :
    isIsolatedClosedNF t = true ↔ (noVars t = true ∧ IsIsolatedNF t) := by
  induction t with
  | s =>
    exact ⟨fun _ => ⟨rfl, ⟨fun _ hs => (by cases hs), (hasNoPredecessor_iff S).mpr rfl⟩⟩, fun _ => rfl⟩
  | var _ =>
    exact ⟨fun h => (by cases h), fun ⟨hv, _⟩ => (by cases hv)⟩
  | app l b ihl ihb =>
    cases l with
    | s =>
      change isIsolatedClosedNF b = true ↔ (noVars (S ⋅ b) = true ∧ IsIsolatedNF (S ⋅ b))
      rw [ihb]
      constructor
      · intro ⟨hvb, hnfb, hnopb⟩
        have hcb : hasContractumSubterm b = false := (hasNoPredecessor_iff b).mp hnopb
        refine ⟨(Bool.and_eq_true _ _).mpr ⟨rfl, hvb⟩, ⟨fun u hs => ?_, ?_⟩⟩
        · cases hs with
          | left hl => cases hl
          | right hr => exact hnfb _ hr
        · rw [hasNoPredecessor_iff]
          change (false || false || hasContractumSubterm b) = false
          rw [hcb]; rfl
      · intro ⟨hv, hnf, hnop⟩
        have hcb_all : hasContractumSubterm (S ⋅ b) = false := (hasNoPredecessor_iff _).mp hnop
        change (false || false || hasContractumSubterm b) = false at hcb_all
        simp only [Bool.false_or] at hcb_all
        exact ⟨((Bool.and_eq_true _ _).mp hv).2,
          ⟨fun b' hr => hnf (S ⋅ b') (FormalAlgebra.Step.right hr),
           (hasNoPredecessor_iff b).mpr hcb_all⟩⟩
    | var _ =>
      exact ⟨fun h => (by cases h), fun ⟨hv, _⟩ => (by
        have hvl := ((Bool.and_eq_true _ _).mp hv).1; cases hvl)⟩
    | app l1 a =>
      cases l1 with
      | s =>
        change (!endsWithArg b a && isIsolatedClosedNF a && isIsolatedClosedNF b) = true ↔
          (noVars (S ⋅ a ⋅ b) = true ∧ IsIsolatedNF (S ⋅ a ⋅ b))
        have iha' : isIsolatedClosedNF a = true ↔ (noVars (S ⋅ a) = true ∧ IsIsolatedNF (S ⋅ a)) := ihl
        constructor
        · intro h
          have ⟨h12, hb_iso⟩ := (Bool.and_eq_true _ _).mp h
          have ⟨hne_end, ha_iso⟩ := (Bool.and_eq_true _ _).mp h12
          obtain ⟨hvsa, hnfsa, hnopsa⟩ := iha'.mp ha_iso
          obtain ⟨hvb, hnfb, hnopb⟩ := ihb.mp hb_iso
          have hcsa : hasContractumSubterm (S ⋅ a) = false := (hasNoPredecessor_iff _).mp hnopsa
          have hcb : hasContractumSubterm b = false := (hasNoPredecessor_iff _).mp hnopb
          have hroot_false : isContractumNode ((S ⋅ a) ⋅ b) = false := by
            cases b with
            | s => rfl
            | var _ => rfl
            | app y z2 =>
              change decide (a = z2) = false
              change (!decide (z2 = a)) = true at hne_end
              cases hd : decide (a = z2) with
              | false => rfl
              | true =>
                rw [decide_eq_true (of_decide_eq_true hd).symm] at hne_end
                cases hne_end
          refine ⟨(Bool.and_eq_true _ _).mpr ⟨hvsa, hvb⟩, ⟨fun u hs => ?_, ?_⟩⟩
          · cases hs with
            | left hl => exact hnfsa _ hl
            | right hr => exact hnfb _ hr
          · rw [hasNoPredecessor_iff]
            change (isContractumNode ((S ⋅ a) ⋅ b) || hasContractumSubterm (S ⋅ a) || hasContractumSubterm b) = false
            rw [hroot_false, hcsa, hcb]; rfl
        · intro ⟨hv, hnf, hnop⟩
          have ⟨hvsa, hvb⟩ := (Bool.and_eq_true _ _).mp hv
          have hc_all : hasContractumSubterm ((S ⋅ a) ⋅ b) = false := (hasNoPredecessor_iff _).mp hnop
          change (isContractumNode ((S ⋅ a) ⋅ b) || hasContractumSubterm (S ⋅ a) || hasContractumSubterm b) = false at hc_all
          simp only [Bool.or_eq_false_iff] at hc_all
          have ⟨⟨hroot_f, hcsa⟩, hcb⟩ := hc_all
          have ha_iso : isIsolatedClosedNF a = true :=
            iha'.mpr ⟨hvsa, fun u hl => hnf (u ⋅ b) (FormalAlgebra.Step.left hl),
              (hasNoPredecessor_iff _).mpr hcsa⟩
          have hb_iso : isIsolatedClosedNF b = true :=
            ihb.mpr ⟨hvb, fun b' hr => hnf (S ⋅ a ⋅ b') (FormalAlgebra.Step.right hr),
              (hasNoPredecessor_iff _).mpr hcb⟩
          have hne_end : (!endsWithArg b a) = true := by
            cases b with
            | s => rfl
            | var _ => rfl
            | app y z2 =>
              change decide (a = z2) = false at hroot_f
              change (!decide (z2 = a)) = true
              have hne_az : a ≠ z2 := of_decide_eq_false hroot_f
              rw [decide_eq_false (Ne.symm hne_az)]
              rfl
          simp only [hne_end, ha_iso, hb_iso, Bool.and_self]
      | var _ =>
        exact ⟨fun h => (by cases h), fun ⟨hv, _⟩ => (by
          have hv1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv).1).1
          cases hv1)⟩
      | app l2 x =>
        exact ⟨fun h => (by cases h), fun ⟨hv, hnf, _⟩ => (by
          have hc : isClosedNFBool (l2 ⋅ x ⋅ a ⋅ b) = true := (isClosedNFBool_iff _).mpr ⟨hv, hnf⟩
          cases hc)⟩

/-- **Isolation of Every Order-3 Combinator (`rightComb n`)**:
    Every right-comb tower `rightComb n` is an Isolated Normal Form, so `[rightComb n]_{=S} = {rightComb n}`! -/
theorem rightComb_isIsolatedNF (n : Nat) :
    IsIsolatedNF (rightComb n) ∧ (∀ u, ConvS (rightComb n) u ↔ u = rightComb n) := by
  have hiso : isIsolatedClosedNF (rightComb n) = true := by
    induction n with
    | zero => rfl
    | succ k ih =>
      cases k with
      | zero => rfl
      | succ m => exact ih
  have ⟨_, hnf_iso⟩ := (isIsolatedClosedNF_iff _).mp hiso
  exact ⟨hnf_iso, (convS_singleton_iff_isolatedNF _).mpr hnf_iso⟩

/-- **Sharp Minimal Non-Isolated Normal Form Threshold (`n = 4`)**:
    - Every closed pure-`S` term of size `≤ 3` (`S`, `SS`, `S(SS)`, `SSS`) is an Isolated Normal Form.
    - At size `4`, `S ⋅ S ⋅ (S ⋅ S)` is the **unique** closed Normal Form that is NOT isolated! -/
theorem minimal_non_isolated_nf_threshold :
    (∀ t, noVars t = true → leaves t ≤ 3 → IsIsolatedNF t) ∧
    (∀ t, noVars t = true → leaves t = 4 →
      ((IsNormalForm t ∧ ¬ IsIsolatedNF t) ↔ t = S ⋅ S ⋅ (S ⋅ S))) := by
  have c_le3 : FormalMinimality.listAll isIsolatedClosedNF
      (FormalMinimality.treesOfLeaves 1 ++ FormalMinimality.treesOfLeaves 2 ++
       FormalMinimality.treesOfLeaves 3) = true := rfl
  have c_eq4 : FormalMinimality.filterList (fun t => isClosedNFBool t && !isIsolatedClosedNF t)
      (FormalMinimality.treesOfLeaves 4) = [S ⋅ S ⋅ (S ⋅ S)] := rfl
  refine ⟨?_, ?_⟩
  · intro t hv hl
    have hpos : 1 ≤ leaves t := leaves_pos t
    have hmem : t ∈ (FormalMinimality.treesOfLeaves 1 ++ FormalMinimality.treesOfLeaves 2 ++
        FormalMinimality.treesOfLeaves 3) := by
      cases hlt : leaves t with
      | zero => rw [hlt] at hpos; cases hpos
      | succ k0 =>
        cases k0 with
        | zero =>
          exact List.mem_append_left _ (List.mem_append_left _
            (FormalMinimality.treesOfLeaves_complete hv hlt))
        | succ k1 =>
          cases k1 with
          | zero =>
            exact List.mem_append_left _ (List.mem_append_right _
              (FormalMinimality.treesOfLeaves_complete hv hlt))
          | succ k2 =>
            cases k2 with
            | zero =>
              exact List.mem_append_right _
                (FormalMinimality.treesOfLeaves_complete hv hlt)
            | succ k3 =>
              rw [hlt] at hl
              exact False.elim (absurd (Nat.le_trans (Nat.le_add_left 4 k3) hl) (by decide))
    exact ((isIsolatedClosedNF_iff t).mp (FormalMinimality.listAll_sound c_le3 hmem)).2
  · intro t hv hl
    have hm := FormalMinimality.treesOfLeaves_complete hv hl
    have hiff := FormalMinimality.mem_witnesses_iff_of_filter_eq c_eq4 hm
    constructor
    · intro ⟨hnf, hniso⟩
      have hc1 : isClosedNFBool t = true := (isClosedNFBool_iff t).mpr ⟨hv, hnf⟩
      have hc2 : isIsolatedClosedNF t = false := by
        cases h : isIsolatedClosedNF t with
        | false => rfl
        | true => exfalso; exact hniso ((isIsolatedClosedNF_iff t).mp h).2
      have hw := hiff.mp (by rw [hc1, hc2]; rfl)
      cases hw with
      | head _ => rfl
      | tail _ hnil => cases hnil
    · intro rfl
      refine ⟨((isClosedNFBool_iff _).mp rfl).2, fun hiso => ?_⟩
      have hc : isIsolatedClosedNF (S ⋅ S ⋅ (S ⋅ S)) = true := (isIsolatedClosedNF_iff _).mpr ⟨rfl, hiso⟩
      cases hc

end FormalOrderAndIsolated

#print axioms FormalOrderAndIsolated.step_leaves_eq_iff
#print axioms FormalOrderAndIsolated.closed_step_leaves_eq_iff
#print axioms FormalOrderAndIsolated.bergstraWeight_leafPres_exact_drop
#print axioms FormalOrderAndIsolated.bergstraWeight_bounds
#print axioms FormalOrderAndIsolated.closed_bergstraWeight_extremals
#print axioms FormalOrderAndIsolated.bergstra_leafPres_exp_bound
#print axioms FormalOrderAndIsolated.leftSubtreeSum_leafPresStep
#print axioms FormalOrderAndIsolated.leafPres_sn
#print axioms FormalOrderAndIsolated.leafPresStepsN_quadratic_upper_bound
#print axioms FormalOrderAndIsolated.leafPres_church_rosser
#print axioms FormalOrderAndIsolated.leafPres_jordan_holder
#print axioms FormalOrderAndIsolated.leftComb_leafPres_quarter_square
#print axioms FormalOrderAndIsolated.convS_singleton_iff_isolatedNF
#print axioms FormalOrderAndIsolated.hasNoPredecessor_iff
#print axioms FormalOrderAndIsolated.isIsolatedClosedNF_iff
#print axioms FormalOrderAndIsolated.rightComb_isIsolatedNF
#print axioms FormalOrderAndIsolated.minimal_non_isolated_nf_threshold
