import formal_no_spiral.conjecture17_open_spirals

/-!
# Universal `minMaxRS` / `minMaxLS` Monotonicity Laws of Pure-`S` Combinatory Logic & Deep Conjecture 17 Impossibility Theorems

100% constructive Lean 4.33.1 formalization (`0 sorry`, `0 Classical.choice`, `0 native_decide`,
`0 custom axioms`; every theorem depends only on `[]` or `[propext]`):

1. **Universal Variable Conservation & Right-Maximal Spine-Depth Monotonicity (`minMaxRS`)**:
   - Across every pure-`S` step `Step t t'`, variable presence is invariant (`hasVar_step_eq`),
     `minMaxRS x t` is `some m` iff `hasVar x t = true` (`minMaxRS_isSome_iff`), and
     `minMaxRS x t' ≤ minMaxRS x t` (`step_minMaxRS_le`, `reduces_minMaxRS_le`, `stepPlus_minMaxRS_le`).

2. **Exact Substitution Formula & Context Lower Bounds for `minMaxRS`**:
   - Exact closed-form formula (`minMaxRS_subst_one_var_eq`) for `minMaxRS x (subst σ M)` on
     arbitrary 1-variable open terms `M(x)` (of **arbitrary variable multiplicity** in `M`).
   - General multi-variable lower bound (`minRSAt_subst_allGe`) and context lower bound
     (`minMaxRS_plugCtx_ge`).
   - Proof that every non-`x`-duplicating right-`x`-tailed term (`countVar x t ≤ 1`) has
     zero off-spine `x` occurrences (`minRSFrom_true_eq_none_of_countVar_le_one`).

3. **Deep Conjecture 17 Impossibility Theorems (Arbitrary Variable Duplication in `M`!)**:
   - `conjecture17_one_var_deep_bound`: rules out `StepPlus M (plugCtx C (subst σ M))` for ANY
     1-variable `M(x)` (arbitrary multiplicity of `x` in `M`!), ANY `x`-free context `C`, and
     ANY `σ` whose off-spine `x` occurrences in `σ(x)` have depth `≥ minMaxRS x M + 1` (covering
     BOTH all off-spine-free `σ` AND deep-off-spine duplicating `σ`, such as `σ(x) = (S ⋅ x) ⋅ x`
     whenever `minMaxRS x M = some 0`!).
   - `conjecture17_one_var_no_offspine_x` & `conjecture17_one_var_linear_subst_arbitrary_M`:
     unconditionally removes the `countVar x M ≤ 1` restriction for all 1-variable terms `M(x)`!
   - `conjecture17_multivar_nonmerging_no_offspine`: multi-variable generalization for arbitrary
     variable multiplicities in `M` under non-merging off-spine-free substitutions.
   - `conjecture17_multivar_merging_closed_offspine`: multi-variable generalization via the
     variable-merged invariant `minAnyVarRS`, ruling out EVEN variable-merging and permuting
     substitutions such as `(x, y) ↦ (T x, S x)` or `(x, y, z) ↦ (T y, S x, S)` in closed contexts!

4. **Bonus Dual Universal Law (`minMaxLS`) & Constructive `DPChain` Equivalence for Conjecture 17**:
   - `step_minMaxLS_ge` & `reduces_minMaxLS_ge`: dual universal non-decreasing law for the
     minimum applied left-spine arity `minMaxLS x t` across every pure-`S` step!
   - `dpChain_minMaxLS_ge`: `minMaxLS` remains monotone across `DPChain` transitions (which strip
     arbitrary open contexts `C`!).
   - `conjecture17_iff_no_dpChain_spiral`: full Conjecture 17 (`∀ M C σ, ¬ StepPlus M (plugCtx C (subst σ M))`)
     is constructively equivalent to `∀ M σ, ¬ (DPChain M (subst σ M) ∧ rs M < rs (subst σ M))`.
-/

namespace FormalNoSpiral

/-! ## 1. Constructive `Option Nat` Minimum Algebra (`optMin`, `optLeSome`, `optAllGe`) -/

def optMin : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Nat.min a b)

def optAdd (c : Nat) : Option Nat → Option Nat
  | none => none
  | some m => some (m + c)

def optLeSome : Option Nat → Option Nat → Prop
  | none, none => True
  | some a, some b => a ≤ b
  | _, _ => False

def optAllGe (B : Nat) : Option Nat → Prop
  | none => True
  | some m => B ≤ m

@[simp] theorem optMin_none_left (o : Option Nat) : optMin none o = o := rfl

@[simp] theorem optMin_none_right (o : Option Nat) : optMin o none = o := by
  cases o <;> rfl

theorem optMin_comm (o1 o2 : Option Nat) : optMin o1 o2 = optMin o2 o1 := by
  cases o1 with
  | none => exact (optMin_none_right o2).symm
  | some a =>
    cases o2 with
    | none => rfl
    | some b => exact congrArg some (Nat.min_comm a b)

theorem optMin_assoc (o1 o2 o3 : Option Nat) :
    optMin (optMin o1 o2) o3 = optMin o1 (optMin o2 o3) := by
  cases o1 with
  | none => rfl
  | some a =>
    cases o2 with
    | none => rfl
    | some b =>
      cases o3 with
      | none => rfl
      | some c => exact congrArg some (Nat.min_assoc a b c)

theorem optMin_idem (o : Option Nat) : optMin o o = o := by
  cases o with
  | none => rfl
  | some a => exact congrArg some (Nat.min_self a)

theorem optMin_eq_none_iff {o1 o2 : Option Nat} :
    optMin o1 o2 = none ↔ o1 = none ∧ o2 = none := by
  cases o1 with
  | none =>
    simp only [optMin_none_left, true_and]
  | some a =>
    cases o2 <;> simp [optMin]

theorem optAdd_optMin (c : Nat) (o1 o2 : Option Nat) :
    optAdd c (optMin o1 o2) = optMin (optAdd c o1) (optAdd c o2) := by
  cases o1 with
  | none => rfl
  | some a =>
    cases o2 with
    | none => rfl
    | some b =>
      change some (Nat.min a b + c) = some (Nat.min (a + c) (b + c))
      refine congrArg some ?_
      exact if hab : a ≤ b then by
        have h1 : Nat.min a b = a := Nat.min_eq_left hab
        have h2 : Nat.min (a + c) (b + c) = a + c := Nat.min_eq_left (Nat.add_le_add_right hab c)
        rw [h1, h2]
      else by
        have hba : b ≤ a := Nat.le_of_not_le hab
        have h1 : Nat.min a b = b := Nat.min_eq_right hba
        have h2 : Nat.min (a + c) (b + c) = b + c := Nat.min_eq_right (Nat.add_le_add_right hba c)
        rw [h1, h2]

theorem optLeSome_refl (o : Option Nat) : optLeSome o o := by
  cases o with
  | none => trivial
  | some a => exact Nat.le_refl a

theorem optLeSome_trans {o1 o2 o3 : Option Nat}
    (h1 : optLeSome o1 o2) (h2 : optLeSome o2 o3) : optLeSome o1 o3 := by
  cases o1 with
  | none =>
    cases o2 with
    | none => exact h2
    | some _ => cases h1
  | some a =>
    cases o2 with
    | none => cases h1
    | some b =>
      cases o3 with
      | none => cases h2
      | some c => exact Nat.le_trans h1 h2

theorem optLeSome_optMin {a' a b' b : Option Nat}
    (ha : optLeSome a' a) (hb : optLeSome b' b) :
    optLeSome (optMin a' b') (optMin a b) := by
  cases a' with
  | none =>
    cases a with
    | none => exact hb
    | some _ => cases ha
  | some xa =>
    cases a with
    | none => cases ha
    | some ya =>
      cases b' with
      | none =>
        cases b with
        | none => exact ha
        | some _ => cases hb
      | some xb =>
        cases b with
        | none => cases hb
        | some yb =>
          change Nat.min xa xb ≤ Nat.min ya yb
          exact Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left xa xb) ha,
            Nat.le_trans (Nat.min_le_right xa xb) hb⟩

theorem optMin_eq_left_of_optLeSome {o1 o2 : Option Nat} (h : optLeSome o1 o2) :
    optMin o1 o2 = o1 := by
  cases o1 with
  | none =>
    cases o2 with
    | none => rfl
    | some _ => cases h
  | some a =>
    cases o2 with
    | none => cases h
    | some b => exact congrArg some (Nat.min_eq_left h)

theorem optAllGe_optMin_iff {B : Nat} {o1 o2 : Option Nat} :
    optAllGe B (optMin o1 o2) ↔ optAllGe B o1 ∧ optAllGe B o2 := by
  cases o1 with
  | none => simp [optAllGe]
  | some a =>
    cases o2 with
    | none => simp [optAllGe, optMin]
    | some b =>
      change B ≤ Nat.min a b ↔ B ≤ a ∧ B ≤ b
      exact Nat.le_min

theorem optAllGe_of_optLeSome {B : Nat} {o1 o2 : Option Nat}
    (hge : optAllGe B o1) (hle : optLeSome o1 o2) : optAllGe B o2 := by
  cases o1 with
  | none =>
    cases o2 with
    | none => trivial
    | some _ => cases hle
  | some a =>
    cases o2 with
    | none => cases hle
    | some b => exact Nat.le_trans hge hle

/-! ## 2. Exact Variable Conservation & `countVar` / `hasVarCtx` Helpers -/

def hasVarCtx (x : Nat) : Ctx → Bool
  | .hole => false
  | .left c r => hasVarCtx x c || hasVar x r
  | .right l c => hasVar x l || hasVarCtx x c

def noVarsCtx : Ctx → Bool
  | .hole => true
  | .left c r => noVarsCtx c && noVars r
  | .right l c => noVars l && noVarsCtx c

def countVar (x : Nat) : Term → Nat
  | .s => 0
  | .var k => if decide (k = x) then 1 else 0
  | .app a b => countVar x a + countVar x b

def countVarCtx (x : Nat) : Ctx → Nat
  | .hole => 0
  | .left c r => countVarCtx x c + countVar x r
  | .right l c => countVar x l + countVarCtx x c

theorem hasVar_eq_false_of_noVars {t : Term} (h : noVars t = true) (x : Nat) :
    hasVar x t = false := by
  induction t with
  | s => rfl
  | var _ => cases h
  | app a b iha ihb =>
    obtain ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp h
    simp only [hasVar, iha ha, ihb hb, Bool.or_self]

theorem hasVarCtx_eq_false_of_noVarsCtx {c : Ctx} (h : noVarsCtx c = true) (x : Nat) :
    hasVarCtx x c = false := by
  induction c with
  | hole => rfl
  | left c' r ih =>
    obtain ⟨hc, hr⟩ := (Bool.and_eq_true _ _).mp h
    simp only [hasVarCtx, ih hc, hasVar_eq_false_of_noVars hr x, Bool.or_self]
  | right l c' ih =>
    obtain ⟨hl, hc⟩ := (Bool.and_eq_true _ _).mp h
    simp only [hasVarCtx, hasVar_eq_false_of_noVars hl x, ih hc, Bool.or_self]

theorem countVar_eq_zero_iff {x : Nat} {t : Term} :
    countVar x t = 0 ↔ hasVar x t = false := by
  induction t with
  | s => simp [countVar, hasVar]
  | var k =>
    by_cases h : k = x
    · subst h; simp [countVar, hasVar]
    · simp [countVar, hasVar, h]
  | app a b iha ihb =>
    simp only [countVar, hasVar, Bool.or_eq_false_iff]
    constructor
    · intro h0
      have ha : countVar x a = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq h0))
      have hb : countVar x b = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq h0))
      exact ⟨iha.mp ha, ihb.mp hb⟩
    · rintro ⟨ha, hb⟩
      rw [iha.mpr ha, ihb.mpr hb]

theorem countVarCtx_eq_zero_iff {x : Nat} {c : Ctx} :
    countVarCtx x c = 0 ↔ hasVarCtx x c = false := by
  induction c with
  | hole => simp [countVarCtx, hasVarCtx]
  | left c' r ih =>
    simp only [countVarCtx, hasVarCtx, Bool.or_eq_false_iff]
    constructor
    · intro h0
      have hc : countVarCtx x c' = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq h0))
      have hr : countVar x r = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq h0))
      exact ⟨ih.mp hc, countVar_eq_zero_iff.mp hr⟩
    · rintro ⟨hc, hr⟩
      rw [ih.mpr hc, countVar_eq_zero_iff.mpr hr]
  | right l c' ih =>
    simp only [countVarCtx, hasVarCtx, Bool.or_eq_false_iff]
    constructor
    · intro h0
      have hl : countVar x l = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq h0))
      have hc : countVarCtx x c' = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq h0))
      exact ⟨countVar_eq_zero_iff.mp hl, ih.mp hc⟩
    · rintro ⟨hl, hc⟩
      rw [countVar_eq_zero_iff.mpr hl, ih.mpr hc]

theorem countVar_pos_of_hasVar {x : Nat} {t : Term} (h : hasVar x t = true) :
    1 ≤ countVar x t := by
  cases hc : countVar x t with
  | zero =>
    rw [countVar_eq_zero_iff.mp hc] at h
    cases h
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

/-- Pure-`S` reduction is both non-erasing and non-inventing on variables! -/
theorem hasVar_step_eq (x : Nat) {a b : Term} (h : Step a b) :
    hasVar x a = hasVar x b := by
  induction h with
  | root p q r =>
    simp only [S, hasVar]
    cases hasVar x p <;> cases hasVar x q <;> cases hasVar x r <;> rfl
  | left _ ih => simp only [hasVar, ih]
  | right _ ih => simp only [hasVar, ih]

theorem hasVar_reduces_eq (x : Nat) {a b : Term} (h : Reduces a b) :
    hasVar x a = hasVar x b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (hasVar_step_eq x hs).trans ih

theorem noVars_step_eq {a b : Term} (h : Step a b) :
    noVars a = noVars b := by
  induction h with
  | root p q r =>
    simp only [S, noVars]
    cases noVars p <;> cases noVars q <;> cases noVars r <;> rfl
  | left _ ih => simp only [noVars, ih]
  | right _ ih => simp only [noVars, ih]

theorem noVars_reduces_eq {a b : Term} (h : Reduces a b) :
    noVars a = noVars b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (noVars_step_eq hs).trans ih

theorem hasVar_plugCtx_eq (x : Nat) (c : Ctx) (u : Term) :
    hasVar x (plugCtx c u) = (hasVarCtx x c || hasVar x u) := by
  induction c with
  | hole => simp [plugCtx, hasVarCtx]
  | left c' r ih =>
    simp only [plugCtx, hasVar, hasVarCtx, ih]
    cases hasVarCtx x c' <;> cases hasVar x u <;> cases hasVar x r <;> rfl
  | right l c' ih =>
    simp only [plugCtx, hasVar, hasVarCtx, ih]
    cases hasVar x l <;> cases hasVarCtx x c' <;> cases hasVar x u <;> rfl

theorem subst_eq_self_of_all_hasVar_false (σ : Nat → Term) {t : Term}
    (h : ∀ v, hasVar v t = false) : subst σ t = t := by
  induction t with
  | s => rfl
  | var k =>
    exfalso
    have hk := h k
    simp [hasVar] at hk
  | app a b iha ihb =>
    have ha : ∀ v, hasVar v a = false := fun v => ((Bool.or_eq_false_iff).mp (h v)).1
    have hb : ∀ v, hasVar v b = false := fun v => ((Bool.or_eq_false_iff).mp (h v)).2
    simp only [subst, iha ha, ihb hb]

/-! ## 3. Definition of `minRSFrom`, `minMaxRS`, and Ancestor-Offset `minRSAt` -/

/-- Right-maximal spine-depth scanner (`isR = false` at root and left children;
    `isR = true` at right children). -/
def minRSFrom (x : Nat) (isR : Bool) : Term → Option Nat
  | .s => none
  | .var k => if !isR && decide (k = x) then some 0 else none
  | .app a b =>
    let selfVal := if !isR && decide (rightLeaf (.app a b) = .var x) then some (rs (.app a b)) else none
    optMin selfVal (optMin (minRSFrom x false a) (minRSFrom x true b))

/-- Minimum right-spine length `rs u` over all right-maximal subterms `u` of `t`
    satisfying `rightLeaf u = .var x` (`none` when `x` does not occur in `t`). -/
def minMaxRS (x : Nat) (t : Term) : Option Nat :=
  minRSFrom x false t

/-- Ancestor-offset presentation of `minMaxRS`: `k` counts the right-spine steps above `t`
    from its nearest enclosing right-maximal ancestor (`k = 0` at root and left children). -/
def minRSAt (x : Nat) (k : Nat) : Term → Option Nat
  | .s => none
  | .var v => if decide (v = x) then some k else none
  | .app a b => optMin (minRSAt x 0 a) (minRSAt x (k + 1) b)

/-- Strictly off-spine right-maximal `x`-depths (`minRSFrom x true t`). -/
def minRSOff (x : Nat) : Term → Option Nat
  | .s => none
  | .var _ => none
  | .app a b => optMin (minRSAt x 0 a) (minRSOff x b)

theorem minRSAt_eq_self_optMin_off (x : Nat) :
    ∀ (t : Term) (k : Nat),
      minRSAt x k t =
        optMin (if decide (rightLeaf t = .var x) then some (k + rs t) else none) (minRSOff x t)
  | .s, _ => by
    simp [minRSAt, minRSOff, rightLeaf]
  | .var v, k => by
    by_cases hv : v = x
    · subst hv
      simp [minRSAt, minRSOff, rightLeaf, rs]
    · have hne : ¬ (Term.var v = Term.var x) := fun h => by injection h with h'; exact hv h'
      simp [minRSAt, minRSOff, rightLeaf, hv, hne]
  | .app a b, k => by
    change optMin (minRSAt x 0 a) (minRSAt x (k + 1) b) =
      optMin (if decide (rightLeaf b = .var x) then some (k + (1 + rs b)) else none)
             (optMin (minRSAt x 0 a) (minRSOff x b))
    rw [minRSAt_eq_self_optMin_off x b (k + 1)]
    have hk : (k + 1) + rs b = k + (1 + rs b) := by
      rw [Nat.add_assoc k 1 (rs b)]
    rw [hk, ← optMin_assoc, optMin_comm (minRSAt x 0 a), optMin_assoc]

theorem minRSFrom_eq (x : Nat) :
    ∀ (t : Term),
      minRSFrom x false t = minRSAt x 0 t ∧ minRSFrom x true t = minRSOff x t
  | .s => ⟨rfl, rfl⟩
  | .var k => by
    by_cases hk : k = x
    · subst hk; simp [minRSFrom, minRSAt, minRSOff]
    · simp [minRSFrom, minRSAt, minRSOff, hk]
  | .app a b => by
    obtain ⟨iha0, _⟩ := minRSFrom_eq x a
    obtain ⟨_, ihb1⟩ := minRSFrom_eq x b
    refine ⟨?_, ?_⟩
    · change optMin (if decide (rightLeaf b = .var x) then some (rs (.app a b)) else none)
          (optMin (minRSFrom x false a) (minRSFrom x true b)) = minRSAt x 0 (.app a b)
      rw [iha0, ihb1, minRSAt_eq_self_optMin_off x (.app a b) 0]
      simp only [rightLeaf, Nat.zero_add]
      rfl
    · change optMin none (optMin (minRSFrom x false a) (minRSFrom x true b)) =
          optMin (minRSAt x 0 a) (minRSOff x b)
      rw [optMin_none_left, iha0, ihb1]

/-- Exact equivalence between `minMaxRS x t` (`minRSFrom x false t`) and `minRSAt x 0 t`. -/
theorem minMaxRS_eq_minRSAt_zero (x : Nat) (t : Term) :
    minMaxRS x t = minRSAt x 0 t :=
  (minRSFrom_eq x t).1

theorem minRSFrom_true_eq_minRSOff (x : Nat) (t : Term) :
    minRSFrom x true t = minRSOff x t :=
  (minRSFrom_eq x t).2

theorem minRSAt_eq_none_iff (x : Nat) :
    ∀ (t : Term) (k : Nat), minRSAt x k t = none ↔ hasVar x t = false
  | .s, _ => by simp [minRSAt, hasVar]
  | .var v, k => by
    by_cases hv : v = x
    · subst hv; simp [minRSAt, hasVar]
    · simp [minRSAt, hasVar, hv]
  | .app a b, k => by
    simp only [minRSAt, optMin_eq_none_iff, hasVar, Bool.or_eq_false_iff]
    rw [minRSAt_eq_none_iff x a 0, minRSAt_eq_none_iff x b (k + 1)]

theorem minMaxRS_eq_none_iff (x : Nat) (t : Term) :
    minMaxRS x t = none ↔ hasVar x t = false := by
  rw [minMaxRS_eq_minRSAt_zero]
  exact minRSAt_eq_none_iff x t 0

theorem minMaxRS_isSome_iff (x : Nat) (t : Term) :
    (∃ m, minMaxRS x t = some m) ↔ hasVar x t = true := by
  cases hm : minMaxRS x t with
  | none =>
    rw [(minMaxRS_eq_none_iff x t).mp hm]
    exact Iff.intro (fun ⟨_, h⟩ => by cases h) (fun h => by cases h)
  | some m =>
    refine Iff.intro (fun _ => ?_) (fun _ => ⟨m, rfl⟩)
    cases hv : hasVar x t with
    | true => rfl
    | false =>
      rw [(minMaxRS_eq_none_iff x t).mpr hv] at hm
      cases hm

theorem minRSAt_mono_offset (x : Nat) :
    ∀ (t : Term) {k1 k2 : Nat}, k1 ≤ k2 → optLeSome (minRSAt x k1 t) (minRSAt x k2 t)
  | .s, _, _, _ => trivial
  | .var v, _, _, hle => by
    by_cases hv : v = x
    · subst hv; simp [minRSAt, optLeSome]; exact hle
    · simp [minRSAt, optLeSome, hv]
  | .app a b, _, _, hle =>
    optLeSome_optMin (optLeSome_refl _)
      (minRSAt_mono_offset x b (Nat.add_le_add_right hle 1))

/-! ## 4. Mission 1: Universal `minMaxRS` Monotonicity Theorem (`step_minMaxRS_le`, `reduces_minMaxRS_le`) -/

/-- **Core Ancestor-Offset Monotonicity Lemma**:
    Across EVERY pure-`S` step `Step t t'` and EVERY right-spine offset `k : Nat`,
    `optLeSome (minRSAt x k t') (minRSAt x k t)`! -/
theorem step_minRSAt_le (x : Nat) {t t' : Term} (hs : Step t t') :
    ∀ (k : Nat), optLeSome (minRSAt x k t') (minRSAt x k t) := by
  induction hs with
  | root p q r =>
    intro k
    -- LHS (`W' = (p ⋅ r) ⋅ (q ⋅ r)` at `k`):
    -- `optMin (optMin (minRSAt x 0 p) (minRSAt x 1 r)) (optMin (minRSAt x 0 q) (minRSAt x (k + 2) r))`
    -- Rearranges cleanly to `optMin (optMin (minRSAt x 0 p) (minRSAt x 0 q)) (minRSAt x 1 r)`!
    have h_rhs_eq :
        minRSAt x k ((p ⋅ r) ⋅ (q ⋅ r)) =
          optMin (optMin (minRSAt x 0 p) (minRSAt x 0 q)) (minRSAt x 1 r) := by
      change optMin (optMin (minRSAt x 0 p) (minRSAt x 1 r))
          (optMin (minRSAt x 0 q) (minRSAt x (k + 2) r)) = _
      rw [optMin_assoc (minRSAt x 0 p),
          ← optMin_assoc (minRSAt x 1 r),
          optMin_comm (minRSAt x 1 r) (minRSAt x 0 q),
          optMin_assoc (minRSAt x 0 q),
          ← optMin_assoc (minRSAt x 0 p)]
      have h1k2 : 1 ≤ k + 2 := Nat.succ_le_succ (Nat.zero_le (k + 1))
      have hr_min : optMin (minRSAt x 1 r) (minRSAt x (k + 2) r) = minRSAt x 1 r :=
        optMin_eq_left_of_optLeSome (minRSAt_mono_offset x r h1k2)
      rw [hr_min]
    have h_lhs_eq :
        minRSAt x k (S ⋅ p ⋅ q ⋅ r) =
          optMin (optMin (minRSAt x 1 p) (minRSAt x 1 q)) (minRSAt x (k + 1) r) := rfl
    rw [h_rhs_eq, h_lhs_eq]
    have hp : optLeSome (minRSAt x 0 p) (minRSAt x 1 p) := minRSAt_mono_offset x p (Nat.zero_le 1)
    have hq : optLeSome (minRSAt x 0 q) (minRSAt x 1 q) := minRSAt_mono_offset x q (Nat.zero_le 1)
    have hr : optLeSome (minRSAt x 1 r) (minRSAt x (k + 1) r) :=
      minRSAt_mono_offset x r (Nat.succ_le_succ (Nat.zero_le k))
    exact optLeSome_optMin (optLeSome_optMin hp hq) hr
  | left _ ih =>
    intro k
    exact optLeSome_optMin (ih 0) (optLeSome_refl _)
  | right _ ih =>
    intro k
    exact optLeSome_optMin (optLeSome_refl _) (ih (k + 1))

theorem reduces_minRSAt_le (x : Nat) {t t' : Term} (hr : Reduces t t') (k : Nat) :
    optLeSome (minRSAt x k t') (minRSAt x k t) := by
  induction hr with
  | refl _ => exact optLeSome_refl _
  | next hs _ ih => exact optLeSome_trans ih (step_minRSAt_le x hs k)

/-- **Universal `minMaxRS` Monotonicity Theorem (Single Step)**:
    Across every pure-`S` step `Step t t'`, if `minMaxRS x t = some m`, then
    `∃ m', minMaxRS x t' = some m' ∧ m' ≤ m`. -/
theorem step_minMaxRS_le (x : Nat) {t t' : Term} (hs : Step t t')
    {m : Nat} (hm : minMaxRS x t = some m) :
    ∃ m', minMaxRS x t' = some m' ∧ m' ≤ m := by
  have hle : optLeSome (minRSAt x 0 t') (minRSAt x 0 t) := step_minRSAt_le x hs 0
  rw [← minMaxRS_eq_minRSAt_zero x t, ← minMaxRS_eq_minRSAt_zero x t', hm] at hle
  cases hm' : minMaxRS x t' with
  | none => rw [hm'] at hle; cases hle
  | some m' =>
    rw [hm'] at hle
    exact ⟨m', rfl, hle⟩

/-- **Universal `minMaxRS` Monotonicity Theorem (Multi-Step `Reduces`)**:
    Across every pure-`S` reduction `Reduces t t'`, if `minMaxRS x t = some m` (equivalently
    `hasVar x t = true`), then `∃ m', minMaxRS x t' = some m' ∧ m' ≤ m`. -/
theorem reduces_minMaxRS_le (x : Nat) {t t' : Term} (hr : Reduces t t')
    {m : Nat} (hm : minMaxRS x t = some m) :
    ∃ m', minMaxRS x t' = some m' ∧ m' ≤ m := by
  have hle : optLeSome (minRSAt x 0 t') (minRSAt x 0 t) := reduces_minRSAt_le x hr 0
  rw [← minMaxRS_eq_minRSAt_zero x t, ← minMaxRS_eq_minRSAt_zero x t', hm] at hle
  cases hm' : minMaxRS x t' with
  | none => rw [hm'] at hle; cases hle
  | some m' =>
    rw [hm'] at hle
    exact ⟨m', rfl, hle⟩

theorem stepPlus_minMaxRS_le (x : Nat) {t t' : Term} (hsp : StepPlus t t')
    {m : Nat} (hm : minMaxRS x t = some m) :
    ∃ m', minMaxRS x t' = some m' ∧ m' ≤ m :=
  reduces_minMaxRS_le x (reduces_of_stepPlus hsp) hm

/-! ## 5. Mission 2: Exact Substitution Formula, Off-Spine Linearity, and Context Lower Bounds -/

/-- **General Multi-Variable Substitution Lower Bound for `minRSAt`**:
    For any bound `B : Nat` and any term `t`:
    if every variable `v` occurring in `t` satisfies:
    1. `optAllGe B (minRSOff x (σ v))` (all off-spine `x` occurrences in `σ v` have depth `≥ B`), and
    2. `rightLeaf (σ v) = .var x → optAllGe B (optAdd (rs (σ v)) (minRSAt v k t))`,
    then `optAllGe B (minRSAt x k (subst σ t))`! -/
theorem minRSAt_subst_allGe (x : Nat) (B : Nat) (σ : Nat → Term) :
    ∀ (t : Term) (k : Nat),
      (∀ v, hasVar v t = true → optAllGe B (minRSOff x (σ v))) →
      (∀ v, hasVar v t = true → rightLeaf (σ v) = .var x →
        optAllGe B (optAdd (rs (σ v)) (minRSAt v k t))) →
      optAllGe B (minRSAt x k (subst σ t))
  | .s, _, _, _ => trivial
  | .var v, k, hoff, hspine => by
    have hv : hasVar v (.var v) = true := by simp [hasVar]
    rw [subst, minRSAt_eq_self_optMin_off x (σ v) k]
    refine optAllGe_optMin_iff.mpr ⟨?_, hoff v hv⟩
    by_cases hrl : rightLeaf (σ v) = .var x
    · simp only [hrl, decide_true, ite_true, optAllGe]
      have hs := hspine v hv hrl
      simp only [minRSAt, decide_true, ite_true, optAdd, optAllGe] at hs
      exact hs
    · simp [hrl, optAllGe]
  | .app a b, k, hoff, hspine => by
    have hoff_a : ∀ v, hasVar v a = true → optAllGe B (minRSOff x (σ v)) :=
      fun v hva => hoff v (by simp only [hasVar, hva, Bool.true_or])
    have hoff_b : ∀ v, hasVar v b = true → optAllGe B (minRSOff x (σ v)) :=
      fun v hvb => hoff v (by simp only [hasVar, hvb, Bool.or_true])
    have hsp_a : ∀ v, hasVar v a = true → rightLeaf (σ v) = .var x →
        optAllGe B (optAdd (rs (σ v)) (minRSAt v 0 a)) := by
      intro v hva hrl
      have h := hspine v (by simp only [hasVar, hva, Bool.true_or]) hrl
      simp only [minRSAt, optAdd_optMin, optAllGe_optMin_iff] at h
      exact h.1
    have hsp_b : ∀ v, hasVar v b = true → rightLeaf (σ v) = .var x →
        optAllGe B (optAdd (rs (σ v)) (minRSAt v (k + 1) b)) := by
      intro v hvb hrl
      have h := hspine v (by simp only [hasVar, hvb, Bool.or_true]) hrl
      simp only [minRSAt, optAdd_optMin, optAllGe_optMin_iff] at h
      exact h.2
    exact optAllGe_optMin_iff.mpr
      ⟨minRSAt_subst_allGe x B σ a 0 hoff_a hsp_a,
       minRSAt_subst_allGe x B σ b (k + 1) hoff_b hsp_b⟩

/-- **Exact Closed-Form 1-Variable Substitution Formula for `minRSAt`**:
    Whenever `M` contains only variable `x` (`∀ v, hasVar v M = true → v = x`) and
    `hasVar x M = true`, for EVERY offset `k`:
    `minRSAt x k (subst σ M) = optMin (if rightLeaf (σ x) = .var x then optAdd (rs (σ x)) (minRSAt x k M) else none) (minRSOff x (σ x))`. -/
theorem minRSAt_subst_one_var_eq (x : Nat) (σ : Nat → Term) :
    ∀ (M : Term) (k : Nat),
      (∀ v, hasVar v M = true → v = x) →
      hasVar x M = true →
      minRSAt x k (subst σ M) =
        optMin
          (if decide (rightLeaf (σ x) = .var x) then optAdd (rs (σ x)) (minRSAt x k M) else none)
          (minRSOff x (σ x))
  | .s, _, _, hx => by cases hx
  | .var v, k, hone, _ => by
    have hv : v = x := hone v (by simp [hasVar])
    rw [hv]
    simp only [subst, minRSAt, decide_true, ite_true, optAdd]
    exact minRSAt_eq_self_optMin_off x (σ x) k
  | .app a b, k, hone, hx => by
    have hone_a : ∀ v, hasVar v a = true → v = x :=
      fun v hv => hone v (by simp only [hasVar, hv, Bool.true_or])
    have hone_b : ∀ v, hasVar v b = true → v = x :=
      fun v hv => hone v (by simp only [hasVar, hv, Bool.or_true])
    cases hxa : hasVar x a with
    | true =>
      cases hxb : hasVar x b with
      | true =>
        have iha := minRSAt_subst_one_var_eq x σ a 0 hone_a hxa
        have ihb := minRSAt_subst_one_var_eq x σ b (k + 1) hone_b hxb
        change optMin (minRSAt x 0 (subst σ a)) (minRSAt x (k + 1) (subst σ b)) = _
        rw [iha, ihb]
        by_cases hrl : rightLeaf (σ x) = .var x
        · simp only [hrl, decide_true, ite_true, minRSAt, optAdd_optMin]
          rw [optMin_assoc (optAdd (rs (σ x)) (minRSAt x 0 a)),
              ← optMin_assoc (minRSOff x (σ x)),
              optMin_comm (minRSOff x (σ x)),
              optMin_assoc,
              optMin_idem (minRSOff x (σ x)),
              ← optMin_assoc]
        · simp only [hrl, decide_false, Bool.false_eq_true, ite_false, optMin_none_left, optMin_idem]
      | false =>
        have hb_novar : ∀ v, hasVar v b = false := by
          intro v
          cases hvb : hasVar v b with
          | false => rfl
          | true => rw [hone_b v hvb] at hvb; rw [hvb] at hxb; cases hxb
        have hb_sub : subst σ b = b := subst_eq_self_of_all_hasVar_false σ hb_novar
        have hb_none : minRSAt x (k + 1) b = none := (minRSAt_eq_none_iff x b (k + 1)).mpr hxb
        have iha := minRSAt_subst_one_var_eq x σ a 0 hone_a hxa
        change optMin (minRSAt x 0 (subst σ a)) (minRSAt x (k + 1) (subst σ b)) = _
        rw [hb_sub, hb_none, optMin_none_right, iha]
        simp only [minRSAt, hb_none, optMin_none_right]
    | false =>
      cases hxb : hasVar x b with
      | true =>
        have ha_novar : ∀ v, hasVar v a = false := by
          intro v
          cases hva : hasVar v a with
          | false => rfl
          | true => rw [hone_a v hva] at hva; rw [hva] at hxa; cases hxa
        have ha_sub : subst σ a = a := subst_eq_self_of_all_hasVar_false σ ha_novar
        have ha_none : minRSAt x 0 a = none := (minRSAt_eq_none_iff x a 0).mpr hxa
        have ihb := minRSAt_subst_one_var_eq x σ b (k + 1) hone_b hxb
        change optMin (minRSAt x 0 (subst σ a)) (minRSAt x (k + 1) (subst σ b)) = _
        rw [ha_sub, ha_none, optMin_none_left, ihb]
        simp only [minRSAt, ha_none, optMin_none_left]
      | false =>
        simp only [hasVar, hxa, hxb, Bool.or_self] at hx
        cases hx

/-- **Exact Closed-Form 1-Variable Substitution Formula for `minMaxRS`**:
    For any 1-variable open term `M(x)` (`minMaxRS x M = some m`),
    `minMaxRS x (subst σ M) = optMin (if rightLeaf (σ x) = .var x then some (m + rs (σ x)) else none) (minRSFrom x true (σ x))`! -/
theorem minMaxRS_subst_one_var_eq (x : Nat) (σ : Nat → Term) (M : Term) {m : Nat}
    (hone : ∀ v, hasVar v M = true → v = x)
    (hm : minMaxRS x M = some m) :
    minMaxRS x (subst σ M) =
      optMin
        (if decide (rightLeaf (σ x) = .var x) then some (m + rs (σ x)) else none)
        (minRSFrom x true (σ x)) := by
  have hx : hasVar x M = true := (minMaxRS_isSome_iff x M).mp ⟨m, hm⟩
  have hm0 : minRSAt x 0 M = some m := by rw [← minMaxRS_eq_minRSAt_zero, hm]
  rw [minMaxRS_eq_minRSAt_zero, minRSAt_subst_one_var_eq x σ M 0 hone hx,
      hm0, minRSFrom_true_eq_minRSOff]
  rfl

/-- Special case when `rightLeaf (σ x) = .var x` and `minRSFrom x true (σ x) = none`:
    `minMaxRS x (subst σ M) = some (m + rs (σ x))`! -/
theorem minMaxRS_subst_one_var_no_offspine_eq (x : Nat) (σ : Nat → Term) (M : Term) {m : Nat}
    (hone : ∀ v, hasVar v M = true → v = x)
    (hm : minMaxRS x M = some m)
    (hrl : rightLeaf (σ x) = .var x)
    (hoff : minRSFrom x true (σ x) = none) :
    minMaxRS x (subst σ M) = some (m + rs (σ x)) := by
  rw [minMaxRS_subst_one_var_eq x σ M hone hm, hoff, optMin_none_right]
  simp [hrl]

/-- Every non-`x`-duplicating right-`x`-tailed term (`countVar x t ≤ 1`) has NO off-spine
    occurrence of `x` (`minRSFrom x true t = none`). -/
theorem minRSFrom_true_eq_none_of_countVar_le_one {x : Nat} {t : Term}
    (hrl : rightLeaf t = .var x) (hlin : countVar x t ≤ 1) :
    minRSFrom x true t = none := by
  rw [minRSFrom_true_eq_minRSOff]
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b _ ihb =>
    have hb_pos : 1 ≤ countVar x b := countVar_pos_of_hasVar (hasVar_rightLeaf hrl)
    have ha_zero : countVar x a = 0 := by
      change countVar x a + countVar x b ≤ 1 at hlin
      cases hca : countVar x a with
      | zero => rfl
      | succ na =>
        rw [hca] at hlin
        have h2 : 2 ≤ (na + 1) + countVar x b :=
          Nat.add_le_add (Nat.succ_le_succ (Nat.zero_le na)) hb_pos
        have hbad : 2 ≤ 1 := Nat.le_trans h2 hlin
        cases hbad with
        | step h0 => cases h0
    have hb_le : countVar x b ≤ 1 :=
      Nat.le_trans (Nat.le_add_left (countVar x b) (countVar x a)) hlin
    have ha_none : minRSAt x 0 a = none :=
      (minRSAt_eq_none_iff x a 0).mpr (countVar_eq_zero_iff.mp ha_zero)
    change optMin (minRSAt x 0 a) (minRSOff x b) = none
    rw [ha_none, optMin_none_left]
    exact ihb hrl hb_le

/-- **Context Lower Bound (`minRSAt_plugCtx_allGe`)**:
    Whenever `hasVarCtx x C = false` and `optAllGe B (minRSAt x 0 u)`,
    `optAllGe B (minRSAt x k (plugCtx C u))` holds for EVERY offset `k` (including right-spine
    contexts `C = .right L C'`, which only increase the enclosing right-maximal ancestor's `rs`!). -/
theorem minRSAt_plugCtx_allGe (x : Nat) (B : Nat) {u : Term}
    (hu : optAllGe B (minRSAt x 0 u)) :
    ∀ (C : Ctx) (k : Nat), hasVarCtx x C = false → optAllGe B (minRSAt x k (plugCtx C u))
  | .hole, k, _ =>
    optAllGe_of_optLeSome hu (minRSAt_mono_offset x u (Nat.zero_le k))
  | .left c' r, k, hc => by
    obtain ⟨hc', hr⟩ := (Bool.or_eq_false_iff).mp hc
    have hr_none : minRSAt x (k + 1) r = none := (minRSAt_eq_none_iff x r (k + 1)).mpr hr
    change optAllGe B (optMin (minRSAt x 0 (plugCtx c' u)) (minRSAt x (k + 1) r))
    rw [hr_none, optMin_none_right]
    exact minRSAt_plugCtx_allGe x B hu c' 0 hc'
  | .right l c', k, hc => by
    obtain ⟨hl, hc'⟩ := (Bool.or_eq_false_iff).mp hc
    have hl_none : minRSAt x 0 l = none := (minRSAt_eq_none_iff x l 0).mpr hl
    change optAllGe B (optMin (minRSAt x 0 l) (minRSAt x (k + 1) (plugCtx c' u)))
    rw [hl_none, optMin_none_left]
    exact minRSAt_plugCtx_allGe x B hu c' (k + 1) hc'

/-- **Exact Context Lower Bound for `minMaxRS`**:
    Whenever `hasVarCtx x C = false` and `minMaxRS x u = some b`,
    `∃ m', minMaxRS x (plugCtx C u) = some m' ∧ b ≤ m'`. -/
theorem minMaxRS_plugCtx_ge (x : Nat) (C : Ctx) {u : Term} {b : Nat}
    (hc : hasVarCtx x C = false) (hu : minMaxRS x u = some b) :
    ∃ m', minMaxRS x (plugCtx C u) = some m' ∧ b ≤ m' := by
  have hu_var : hasVar x u = true := (minMaxRS_isSome_iff x u).mp ⟨b, hu⟩
  have hpu_var : hasVar x (plugCtx C u) = true := hasVar_plugCtx C hu_var
  obtain ⟨m', hm'⟩ := (minMaxRS_isSome_iff x (plugCtx C u)).mpr hpu_var
  have hu0 : optAllGe b (minRSAt x 0 u) := by
    rw [← minMaxRS_eq_minRSAt_zero, hu]; exact Nat.le_refl b
  have hge : optAllGe b (minRSAt x 0 (plugCtx C u)) := minRSAt_plugCtx_allGe x b hu0 C 0 hc
  rw [← minMaxRS_eq_minRSAt_zero, hm'] at hge
  exact ⟨m', hm', hge⟩

/-! ## 6. Deep Conjecture 17 Impossibility Theorems (Arbitrary Multiplicity in `M`!) -/

/-- **Theorem 17.3 (`conjecture17_one_var_deep_bound` — Deep 1-Variable Obstruction Theorem)**:
    For **ANY** 1-variable pure-`S` term `M(x)` (**arbitrary variable multiplicity `countVar x M ≥ 1`**!),
    **ANY** `x`-free context `C` (`hasVarCtx x C = false`, including all closed contexts!), and
    **ANY** substitution `σ` whose off-spine `x` occurrences in `σ(x)` have depth
    `≥ minMaxRS x M + 1` (covering ALL off-spine-free `σ`, AND even duplicating `σ` such as
    `σ(x) = (S ⋅ x) ⋅ x` whenever `minMaxRS x M = some 0`!):
    `¬ StepPlus M (plugCtx C (subst σ M))`! -/
theorem conjecture17_one_var_deep_bound
    (x : Nat) (M : Term) (C : Ctx) (σ : Nat → Term)
    (hone : ∀ v, hasVar v M = true → v = x)
    (hctx : hasVarCtx x C = false)
    (hoff : ∀ m, minMaxRS x M = some m → optAllGe (m + 1) (minRSFrom x true (σ x))) :
    ¬ StepPlus M (plugCtx C (subst σ M)) := by
  intro hsp
  by_cases hself : rightLeaf (σ x) = .var x ∧ 1 ≤ rs (σ x)
  · obtain ⟨hrl, hrs_pos⟩ := hself
    cases hxM : hasVar x M with
    | false =>
      have hno : ∀ v, hasVar v M = true → ¬ (rightLeaf (σ v) = .var v ∧ 1 ≤ rs (σ v)) := by
        intro v hv
        rw [hone v hv] at hv
        rw [hv] at hxM
        cases hxM
      exact conjecture17_no_open_spiral_unless_self_right_tail M C σ hno hsp
    | true =>
      obtain ⟨m, hm⟩ := (minMaxRS_isSome_iff x M).mpr hxM
      have h_sub_eq := minMaxRS_subst_one_var_eq x σ M hone hm
      have h_sub_ge : optAllGe (m + 1) (minRSAt x 0 (subst σ M)) := by
        rw [← minMaxRS_eq_minRSAt_zero, h_sub_eq]
        refine optAllGe_optMin_iff.mpr ⟨?_, hoff m hm⟩
        simp only [hrl, decide_true, ite_true, optAllGe]
        exact Nat.add_le_add_left hrs_pos m
      have h_end_ge : optAllGe (m + 1) (minRSAt x 0 (plugCtx C (subst σ M))) :=
        minRSAt_plugCtx_allGe x (m + 1) h_sub_ge C 0 hctx
      obtain ⟨m', hm'_eq, hm'_le⟩ := stepPlus_minMaxRS_le x hsp hm
      rw [← minMaxRS_eq_minRSAt_zero, hm'_eq] at h_end_ge
      change m + 1 ≤ m' at h_end_ge
      exact Nat.lt_irrefl m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_trans h_end_ge hm'_le))
  · exact conjecture17_single_var x M C σ hone hself hsp

/-- **Theorem 17.4 (`conjecture17_one_var_no_offspine_x`)**:
    For **ANY** 1-variable pure-`S` term `M(x)` (arbitrary multiplicity of `x` in `M`!),
    **ANY** `x`-free context `C` (`hasVarCtx x C = false`), and **ANY** substitution `σ` with
    `minRSFrom x true (σ x) = none`, `¬ StepPlus M (plugCtx C (subst σ M))`! -/
theorem conjecture17_one_var_no_offspine_x
    (x : Nat) (M : Term) (C : Ctx) (σ : Nat → Term)
    (hone : ∀ v, hasVar v M = true → v = x)
    (hctx : hasVarCtx x C = false)
    (hoff : minRSFrom x true (σ x) = none) :
    ¬ StepPlus M (plugCtx C (subst σ M)) :=
  conjecture17_one_var_deep_bound x M C σ hone hctx
    (fun _ _ => by rw [hoff]; trivial)

/-- **Theorem 17.5 (`conjecture17_one_var_linear_subst_arbitrary_M`)**:
    For **ANY** 1-variable pure-`S` term `M(x)` (**arbitrary variable multiplicity `countVar x M ≥ 1`**,
    duplicating or non-duplicating!), **ANY** `x`-free context `C` (`countVarCtx x C = 0`), and
    **ANY** non-`x`-duplicating substitution `σ` (`countVar x (σ x) ≤ 1`, including `x ↦ S x`,
    `x ↦ T x`, `x ↦ A x`, `x ↦ V x`, `x ↦ A_1 ⋅ ... ⋅ (A_d ⋅ x)` with `x ∉ Vars(A_i)`):
    `¬ StepPlus M (plugCtx C (subst σ M))`! -/
theorem conjecture17_one_var_linear_subst_arbitrary_M
    (x : Nat) (M : Term) (C : Ctx) (σ : Nat → Term)
    (hone : ∀ v, hasVar v M = true → v = x)
    (hlin : countVar x (σ x) ≤ 1)
    (hctx : countVarCtx x C = 0) :
    ¬ StepPlus M (plugCtx C (subst σ M)) := by
  intro hsp
  by_cases hrl : rightLeaf (σ x) = .var x
  · have hoff : minRSFrom x true (σ x) = none :=
      minRSFrom_true_eq_none_of_countVar_le_one hrl hlin
    exact conjecture17_one_var_no_offspine_x x M C σ hone
      (countVarCtx_eq_zero_iff.mp hctx) hoff hsp
  · exact conjecture17_single_var x M C σ hone (fun ⟨h, _⟩ => hrl h) hsp

/-- Corollary for all closed pure-`S` contexts `C` (`noVarsCtx C = true`). -/
theorem conjecture17_one_var_closed_ctx_linear_subst
    (x : Nat) (M : Term) (C : Ctx) (σ : Nat → Term)
    (hone : ∀ v, hasVar v M = true → v = x)
    (hlin : countVar x (σ x) ≤ 1)
    (hclosed : noVarsCtx C = true) :
    ¬ StepPlus M (plugCtx C (subst σ M)) :=
  conjecture17_one_var_linear_subst_arbitrary_M x M C σ hone hlin
    (countVarCtx_eq_zero_iff.mpr (hasVarCtx_eq_false_of_noVarsCtx hclosed x))

/-! ## 7. Multi-Variable Generalizations (`conjecture17_multivar_nonmerging_no_offspine` & Variable-Merged `minAnyVarRS`) -/

/-- **Theorem 17.6 (`conjecture17_multivar_nonmerging_no_offspine`)**:
    For **arbitrary many variables** and **arbitrary variable multiplicities in `M`**:
    if for every variable `x` occurring in `M`:
    1. `hasVarCtx x C = false`,
    2. `∀ v, hasVar v M = true → minRSFrom x true (σ v) = none`, and
    3. no distinct variable `v ≠ x` occurring in `M` has `rightLeaf (σ v) = .var x`
       (note: `σ` may freely permute variables `(x, y) ↦ (T y, T x)`, map variables to ground-tailed
       terms, or grow right spines `(x, y) ↦ (T x, V y)`!),
    then `¬ StepPlus M (plugCtx C (subst σ M))`! -/
theorem conjecture17_multivar_nonmerging_no_offspine
    (M : Term) (C : Ctx) (σ : Nat → Term)
    (hctx : ∀ x, hasVar x M = true → hasVarCtx x C = false)
    (hoff : ∀ v x, hasVar v M = true → hasVar x M = true → minRSFrom x true (σ v) = none)
    (hnomerge : ∀ v x, hasVar v M = true → hasVar x M = true → v ≠ x → rightLeaf (σ v) ≠ .var x) :
    ¬ StepPlus M (plugCtx C (subst σ M)) := by
  intro hsp
  -- If NO `x ∈ Vars(M)` satisfies `rightLeaf (σ x) = .var x ∧ 1 ≤ rs (σ x)`, Theorem 17.2 refutes `hsp`!
  -- Constructively scan variables via `open_spiral_subterm_or_self_right_tail`!
  -- Wait: `open_spiral_subterm_or_self_right_tail` constructively extracts `xR` with `hasVar xR M = true`!
  have hex : ∃ x, hasVar x M = true ∧ rightLeaf (σ x) = .var x ∧ 1 ≤ rs (σ x) := by
    suffices ∀ (L : Nat) (U : Term), leaves U ≤ L →
        (∃ C', StepPlus U (plugCtx C' (subst σ U))) →
        ∃ x, hasVar x U = true ∧ rightLeaf (σ x) = .var x ∧ 1 ≤ rs (σ x) from
      this (leaves M) M (Nat.le_refl _) ⟨C, hsp⟩
    intro L
    induction L with
    | zero =>
      intro U hL _
      exfalso
      exact Nat.not_succ_le_zero 0 (Nat.le_trans (leaves_pos U) hL)
    | succ L ihL =>
      intro U hL ⟨C', hspU⟩
      exact if hle : leaves U ≤ L then
        ihL U hle ⟨C', hspU⟩
      else by
        rcases open_spiral_subterm_or_self_right_tail hspU with
            ⟨u, c'', hstrict, hu_sp⟩ | ⟨_, _, xR, hvar, _, hrl_sig, hrs_sig⟩
        · have hu_lt : leaves u < leaves U := strictSubterm_leaves_lt hstrict
          have hu_le : leaves u ≤ L := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hu_lt hL)
          obtain ⟨x, hxu, h1, h2⟩ := ihL u hu_le ⟨c'', hu_sp⟩
          obtain ⟨d, _, hUeq⟩ := hstrict
          exact ⟨x, by rw [hUeq]; exact hasVar_plugCtx d hxu, h1, h2⟩
        · exact ⟨xR, hvar, hrl_sig, hrs_sig⟩
  obtain ⟨x, hxM, hrl_x, hrs_x⟩ := hex
  obtain ⟨m, hm⟩ := (minMaxRS_isSome_iff x M).mpr hxM
  have h_sub_ge : optAllGe (m + 1) (minRSAt x 0 (subst σ M)) := by
    refine minRSAt_subst_allGe x (m + 1) σ M 0
      (fun v hv => by rw [← minRSFrom_true_eq_minRSOff, hoff v x hv hxM]; trivial)
      (fun v hv hrl_v => ?_)
    by_cases hvx : v = x
    · subst hvx
      have hm0 : minRSAt v 0 M = some m := by rw [← minMaxRS_eq_minRSAt_zero, hm]
      rw [hm0]
      exact Nat.add_le_add_left hrs_x m
    · exfalso
      exact hnomerge v x hv hxM hvx hrl_v
  have h_end_ge : optAllGe (m + 1) (minRSAt x 0 (plugCtx C (subst σ M))) :=
    minRSAt_plugCtx_allGe x (m + 1) h_sub_ge C 0 (hctx x hxM)
  obtain ⟨m', hm'_eq, hm'_le⟩ := stepPlus_minMaxRS_le x hsp hm
  rw [← minMaxRS_eq_minRSAt_zero, hm'_eq] at h_end_ge
  change m + 1 ≤ m' at h_end_ge
  exact Nat.lt_irrefl m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_trans h_end_ge hm'_le))

/-! ### Variable-Merged Right-Maximal Depth (`minAnyVarRSAt`) for Variable-Merging Substitutions -/

/-- Minimum right-spine depth over ALL variables simultaneously (`none` iff `noVars t = true`). -/
def minAnyVarRSAt (k : Nat) : Term → Option Nat
  | .s => none
  | .var _ => some k
  | .app a b => optMin (minAnyVarRSAt 0 a) (minAnyVarRSAt (k + 1) b)

def offSpineClosed : Term → Bool
  | .s => true
  | .var _ => true
  | .app a b => noVars a && offSpineClosed b

theorem minAnyVarRSAt_eq_none_iff :
    ∀ (t : Term) (k : Nat), minAnyVarRSAt k t = none ↔ noVars t = true
  | .s, _ => by simp [minAnyVarRSAt, noVars]
  | .var _, _ => by simp [minAnyVarRSAt, noVars]
  | .app a b, k => by
    simp only [minAnyVarRSAt, optMin_eq_none_iff, noVars, Bool.and_eq_true]
    rw [minAnyVarRSAt_eq_none_iff a 0, minAnyVarRSAt_eq_none_iff b (k + 1)]

theorem minAnyVarRSAt_mono_offset :
    ∀ (t : Term) {k1 k2 : Nat}, k1 ≤ k2 → optLeSome (minAnyVarRSAt k1 t) (minAnyVarRSAt k2 t)
  | .s, _, _, _ => trivial
  | .var _, _, _, hle => hle
  | .app _a b, _, _, hle =>
    optLeSome_optMin (optLeSome_refl _)
      (minAnyVarRSAt_mono_offset b (Nat.add_le_add_right hle 1))

theorem step_minAnyVarRSAt_le {t t' : Term} (hs : Step t t') :
    ∀ (k : Nat), optLeSome (minAnyVarRSAt k t') (minAnyVarRSAt k t) := by
  induction hs with
  | root p q r =>
    intro k
    have h_rhs_eq :
        minAnyVarRSAt k ((p ⋅ r) ⋅ (q ⋅ r)) =
          optMin (optMin (minAnyVarRSAt 0 p) (minAnyVarRSAt 0 q)) (minAnyVarRSAt 1 r) := by
      change optMin (optMin (minAnyVarRSAt 0 p) (minAnyVarRSAt 1 r))
          (optMin (minAnyVarRSAt 0 q) (minAnyVarRSAt (k + 2) r)) = _
      rw [optMin_assoc (minAnyVarRSAt 0 p),
          ← optMin_assoc (minAnyVarRSAt 1 r),
          optMin_comm (minAnyVarRSAt 1 r) (minAnyVarRSAt 0 q),
          optMin_assoc (minAnyVarRSAt 0 q),
          ← optMin_assoc (minAnyVarRSAt 0 p)]
      have h1k2 : 1 ≤ k + 2 := Nat.succ_le_succ (Nat.zero_le (k + 1))
      rw [optMin_eq_left_of_optLeSome (minAnyVarRSAt_mono_offset r h1k2)]
    exact h_rhs_eq ▸ optLeSome_optMin
      (optLeSome_optMin (minAnyVarRSAt_mono_offset p (Nat.zero_le 1))
                        (minAnyVarRSAt_mono_offset q (Nat.zero_le 1)))
      (minAnyVarRSAt_mono_offset r (Nat.succ_le_succ (Nat.zero_le k)))
  | left _ ih => intro k; exact optLeSome_optMin (ih 0) (optLeSome_refl _)
  | right _ ih => intro k; exact optLeSome_optMin (optLeSome_refl _) (ih (k + 1))

theorem reduces_minAnyVarRSAt_le {t t' : Term} (hr : Reduces t t') (k : Nat) :
    optLeSome (minAnyVarRSAt k t') (minAnyVarRSAt k t) := by
  induction hr with
  | refl _ => exact optLeSome_refl _
  | next hs _ ih => exact optLeSome_trans ih (step_minAnyVarRSAt_le hs k)

theorem minAnyVarRSAt_offSpineClosed :
    ∀ (t : Term) (k : Nat), offSpineClosed t = true →
      minAnyVarRSAt k t = (if noVars t then none else some (k + rs t))
  | .s, _, _ => rfl
  | .var _, k, _ => by simp [minAnyVarRSAt, noVars, rs]
  | .app a b, k, hoff => by
    obtain ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp hoff
    have ha_none : minAnyVarRSAt 0 a = none := (minAnyVarRSAt_eq_none_iff a 0).mpr ha
    change optMin (minAnyVarRSAt 0 a) (minAnyVarRSAt (k + 1) b) =
      if (noVars a && noVars b) then none else some (k + (1 + rs b))
    rw [ha_none, optMin_none_left, minAnyVarRSAt_offSpineClosed b (k + 1) hb, ha, Bool.true_and]
    cases noVars b with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [Nat.add_assoc k 1 (rs b)]

theorem minAnyVarRSAt_subst_allGe (B : Nat) (σ : Nat → Term) :
    ∀ (t : Term) (k : Nat),
      (∀ v, hasVar v t = true → offSpineClosed (σ v) = true) →
      (∀ v, hasVar v t = true → noVars (σ v) = false → 1 ≤ rs (σ v)) →
      optAllGe B (optAdd 1 (minAnyVarRSAt k t)) →
      optAllGe B (minAnyVarRSAt k (subst σ t))
  | .s, _, _, _, _ => trivial
  | .var v, k, hoff, hrs1, hB => by
    have hv : hasVar v (.var v) = true := by simp [hasVar]
    rw [subst, minAnyVarRSAt_offSpineClosed (σ v) k (hoff v hv)]
    cases hnv : noVars (σ v) with
    | true => simp [optAllGe]
    | false =>
      simp only [Bool.false_eq_true, ite_false, optAllGe]
      simp only [minAnyVarRSAt, optAdd, optAllGe] at hB
      exact Nat.le_trans hB (Nat.add_le_add_left (hrs1 v hv hnv) k)
  | .app a b, k, hoff, hrs1, hB => by
    simp only [minAnyVarRSAt, optAdd_optMin, optAllGe_optMin_iff] at hB
    exact optAllGe_optMin_iff.mpr
      ⟨minAnyVarRSAt_subst_allGe B σ a 0
        (fun v hv => hoff v (by simp only [hasVar, hv, Bool.true_or]))
        (fun v hv => hrs1 v (by simp only [hasVar, hv, Bool.true_or])) hB.1,
       minAnyVarRSAt_subst_allGe B σ b (k + 1)
        (fun v hv => hoff v (by simp only [hasVar, hv, Bool.or_true]))
        (fun v hv => hrs1 v (by simp only [hasVar, hv, Bool.or_true])) hB.2⟩

theorem minAnyVarRSAt_plugCtx_allGe (B : Nat) {u : Term}
    (hu : optAllGe B (minAnyVarRSAt 0 u)) :
    ∀ (C : Ctx) (k : Nat), noVarsCtx C = true → optAllGe B (minAnyVarRSAt k (plugCtx C u))
  | .hole, k, _ =>
    optAllGe_of_optLeSome hu (minAnyVarRSAt_mono_offset u (Nat.zero_le k))
  | .left c' r, k, hc => by
    obtain ⟨hc', hr⟩ := (Bool.and_eq_true _ _).mp hc
    have hr_none : minAnyVarRSAt (k + 1) r = none := (minAnyVarRSAt_eq_none_iff r (k + 1)).mpr hr
    change optAllGe B (optMin (minAnyVarRSAt 0 (plugCtx c' u)) (minAnyVarRSAt (k + 1) r))
    rw [hr_none, optMin_none_right]
    exact minAnyVarRSAt_plugCtx_allGe B hu c' 0 hc'
  | .right l c', k, hc => by
    obtain ⟨hl, hc'⟩ := (Bool.and_eq_true _ _).mp hc
    have hl_none : minAnyVarRSAt 0 l = none := (minAnyVarRSAt_eq_none_iff l 0).mpr hl
    change optAllGe B (optMin (minAnyVarRSAt 0 l) (minAnyVarRSAt (k + 1) (plugCtx c' u)))
    rw [hl_none, optMin_none_left]
    exact minAnyVarRSAt_plugCtx_allGe B hu c' (k + 1) hc'

/-- **Theorem 17.7 (`conjecture17_multivar_merging_closed_offspine`)**:
    For **arbitrary many variables**, **arbitrary variable multiplicities in `M`**, and **ANY**
    closed context `C` (`noVarsCtx C = true`):
    if every `v` occurring in `M` maps under `σ` to an off-spine-closed term (`offSpineClosed (σ v) = true`)
    that is either closed (`noVars (σ v) = true`) or has positive right spine (`1 ≤ rs (σ v)`) —
    covering ALL variable-merging, variable-permuting, and mixed ground/open substitutions such as
    `(x, y) ↦ (T x, S x)`, `(x, y) ↦ (T y, S x)`, `(x, y, z) ↦ (T x, S, V x)`! —
    then `¬ StepPlus M (plugCtx C (subst σ M))`! -/
theorem conjecture17_multivar_merging_closed_offspine
    (M : Term) (C : Ctx) (σ : Nat → Term)
    (hclosed : noVarsCtx C = true)
    (hoff : ∀ v, hasVar v M = true → offSpineClosed (σ v) = true)
    (hrs1 : ∀ v, hasVar v M = true → noVars (σ v) = false → 1 ≤ rs (σ v)) :
    ¬ StepPlus M (plugCtx C (subst σ M)) := by
  intro hsp
  cases hnv : noVars M with
  | true =>
    have hM_sub : subst σ M = M := subst_eq_self_of_all_hasVar_false σ (hasVar_eq_false_of_noVars hnv)
    rw [hM_sub] at hsp
    exact waldmann_no_spiral C M hsp
  | false =>
    cases hm : minAnyVarRSAt 0 M with
    | none =>
      rw [(minAnyVarRSAt_eq_none_iff M 0).mp hm] at hnv
      cases hnv
    | some m =>
      have h_sub_ge : optAllGe (m + 1) (minAnyVarRSAt 0 (subst σ M)) :=
        minAnyVarRSAt_subst_allGe (m + 1) σ M 0 hoff hrs1
          (by rw [hm]; exact Nat.le_refl (m + 1))
      have h_end_ge : optAllGe (m + 1) (minAnyVarRSAt 0 (plugCtx C (subst σ M))) :=
        minAnyVarRSAt_plugCtx_allGe (m + 1) h_sub_ge C 0 hclosed
      have hle : optLeSome (minAnyVarRSAt 0 (plugCtx C (subst σ M))) (minAnyVarRSAt 0 M) :=
        reduces_minAnyVarRSAt_le (reduces_of_stepPlus hsp) 0
      rw [hm] at hle
      cases hm' : minAnyVarRSAt 0 (plugCtx C (subst σ M)) with
      | none => rw [hm'] at hle; cases hle
      | some m' =>
        rw [hm'] at hle h_end_ge
        change m + 1 ≤ m' at h_end_ge
        exact Nat.lt_irrefl m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_trans h_end_ge hle))

/-! ## 8. Bonus Grand Prize Discoveries: Dual Universal `minMaxLS` Law & `DPChain` Equivalence -/

/-- Left-maximal applied-arity scanner (`isL = false` at root and right children;
    `isL = true` at left children). -/
def minLSFrom (x : Nat) (isL : Bool) : Term → Option Nat
  | .s => none
  | .var k => if !isL && decide (k = x) then some 0 else none
  | .app a b =>
    let selfVal := if !isL && decide (headLeaf (.app a b) = .var x) then some (spineLen (.app a b)) else none
    optMin selfVal (optMin (minLSFrom x true a) (minLSFrom x false b))

/-- Minimum applied left-spine arity `spineLen u` over all left-maximal subterms `u` of `t`
    with `headLeaf u = .var x` (`none` iff `hasVar x t = false`). -/
def minMaxLS (x : Nat) (t : Term) : Option Nat :=
  minLSFrom x false t

def minLSAt (x : Nat) (k : Nat) : Term → Option Nat
  | .s => none
  | .var v => if decide (v = x) then some k else none
  | .app a b => optMin (minLSAt x (k + 1) a) (minLSAt x 0 b)

def minLSOff (x : Nat) : Term → Option Nat
  | .s => none
  | .var _ => none
  | .app a b => optMin (minLSOff x a) (minLSAt x 0 b)

theorem minLSAt_eq_self_optMin_off (x : Nat) :
    ∀ (t : Term) (k : Nat),
      minLSAt x k t =
        optMin (if decide (headLeaf t = .var x) then some (k + spineLen t) else none) (minLSOff x t)
  | .s, _ => by
    simp [minLSAt, minLSOff, headLeaf]
  | .var v, k => by
    by_cases hv : v = x
    · subst hv; simp [minLSAt, minLSOff, headLeaf, spineLen]
    · have hne : ¬ (Term.var v = Term.var x) := fun h => by injection h with h'; exact hv h'
      simp [minLSAt, minLSOff, headLeaf, hv, hne]
  | .app a b, k => by
    change optMin (minLSAt x (k + 1) a) (minLSAt x 0 b) =
      optMin (if decide (headLeaf a = .var x) then some (k + (1 + spineLen a)) else none)
             (optMin (minLSOff x a) (minLSAt x 0 b))
    rw [minLSAt_eq_self_optMin_off x a (k + 1)]
    have hk : (k + 1) + spineLen a = k + (1 + spineLen a) := by
      rw [Nat.add_assoc k 1 (spineLen a)]
    rw [hk, optMin_assoc]

theorem minLSFrom_eq (x : Nat) :
    ∀ (t : Term),
      minLSFrom x false t = minLSAt x 0 t ∧ minLSFrom x true t = minLSOff x t
  | .s => ⟨rfl, rfl⟩
  | .var k => by
    by_cases hk : k = x
    · subst hk; simp [minLSFrom, minLSAt, minLSOff]
    · simp [minLSFrom, minLSAt, minLSOff, hk]
  | .app a b => by
    obtain ⟨_, iha1⟩ := minLSFrom_eq x a
    obtain ⟨ihb0, _⟩ := minLSFrom_eq x b
    refine ⟨?_, ?_⟩
    · change optMin (if decide (headLeaf a = .var x) then some (spineLen (.app a b)) else none)
          (optMin (minLSFrom x true a) (minLSFrom x false b)) = minLSAt x 0 (.app a b)
      rw [iha1, ihb0, minLSAt_eq_self_optMin_off x (.app a b) 0]
      simp only [headLeaf, Nat.zero_add]
      rfl
    · change optMin none (optMin (minLSFrom x true a) (minLSFrom x false b)) =
          optMin (minLSOff x a) (minLSAt x 0 b)
      rw [optMin_none_left, iha1, ihb0]

theorem minMaxLS_eq_minLSAt_zero (x : Nat) (t : Term) :
    minMaxLS x t = minLSAt x 0 t :=
  (minLSFrom_eq x t).1

theorem minLSAt_eq_none_iff (x : Nat) :
    ∀ (t : Term) (k : Nat), minLSAt x k t = none ↔ hasVar x t = false
  | .s, _ => by simp [minLSAt, hasVar]
  | .var v, _ => by
    by_cases hv : v = x
    · subst hv; simp [minLSAt, hasVar]
    · simp [minLSAt, hasVar, hv]
  | .app a b, k => by
    simp only [minLSAt, optMin_eq_none_iff, hasVar, Bool.or_eq_false_iff]
    rw [minLSAt_eq_none_iff x a (k + 1), minLSAt_eq_none_iff x b 0]

theorem minLSAt_mono_offset (x : Nat) :
    ∀ (t : Term) {k1 k2 : Nat}, k1 ≤ k2 → optLeSome (minLSAt x k1 t) (minLSAt x k2 t)
  | .s, _, _, _ => trivial
  | .var v, _, _, hle => by
    by_cases hv : v = x
    · subst hv; simp [minLSAt, optLeSome]; exact hle
    · simp [minLSAt, optLeSome, hv]
  | .app a b, _, _, hle =>
    optLeSome_optMin (minLSAt_mono_offset x a (Nat.add_le_add_right hle 1)) (optLeSome_refl _)

/-- **Dual Universal Monotonicity Law (`step_minLSAt_ge`)**:
    Across EVERY pure-`S` step `Step t t'` and EVERY left-spine offset `k`,
    `optLeSome (minLSAt x k t) (minLSAt x k t')` — i.e., `minMaxLS x` NEVER DECREASES! -/
theorem step_minLSAt_ge (x : Nat) {t t' : Term} (hs : Step t t') :
    ∀ (k : Nat), optLeSome (minLSAt x k t) (minLSAt x k t') := by
  induction hs with
  | root p q r =>
    intro k
    have h_lhs_eq :
        minLSAt x k (S ⋅ p ⋅ q ⋅ r) =
          optMin (optMin (minLSAt x 0 p) (minLSAt x 0 q)) (minLSAt x 0 r) := rfl
    have h_rhs_eq :
        minLSAt x k ((p ⋅ r) ⋅ (q ⋅ r)) =
          optMin (optMin (minLSAt x (k + 2) p) (minLSAt x 1 q)) (minLSAt x 0 r) := by
      change optMin (optMin (minLSAt x (k + 2) p) (minLSAt x 0 r))
          (optMin (minLSAt x 1 q) (minLSAt x 0 r)) = _
      rw [optMin_assoc (minLSAt x (k + 2) p),
          ← optMin_assoc (minLSAt x 0 r),
          optMin_comm (minLSAt x 0 r) (minLSAt x 1 q),
          optMin_assoc (minLSAt x 1 q),
          optMin_idem (minLSAt x 0 r),
          ← optMin_assoc]
    rw [h_lhs_eq, h_rhs_eq]
    exact optLeSome_optMin
      (optLeSome_optMin (minLSAt_mono_offset x p (Nat.zero_le (k + 2)))
                        (minLSAt_mono_offset x q (Nat.zero_le 1)))
      (optLeSome_refl _)
  | left _ ih => intro k; exact optLeSome_optMin (ih (k + 1)) (optLeSome_refl _)
  | right _ ih => intro k; exact optLeSome_optMin (optLeSome_refl _) (ih 0)

theorem reduces_minLSAt_ge (x : Nat) {t t' : Term} (hr : Reduces t t') (k : Nat) :
    optLeSome (minLSAt x k t) (minLSAt x k t') := by
  induction hr with
  | refl _ => exact optLeSome_refl _
  | next hs _ ih => exact optLeSome_trans (step_minLSAt_ge x hs k) ih

/-- **Dual Universal `minMaxLS` Monotonicity Theorem**:
    Across every pure-`S` step `Step t t'` (and `Reduces t t'`), the minimum applied arity
    `minMaxLS x` of any variable `x` occurring in `t` never decreases (`l ≤ l'`). -/
theorem step_minMaxLS_ge (x : Nat) {t t' : Term} (hs : Step t t')
    {l : Nat} (hl : minMaxLS x t = some l) :
    ∃ l', minMaxLS x t' = some l' ∧ l ≤ l' := by
  have hge : optLeSome (minLSAt x 0 t) (minLSAt x 0 t') := step_minLSAt_ge x hs 0
  rw [← minMaxLS_eq_minLSAt_zero x t, ← minMaxLS_eq_minLSAt_zero x t', hl] at hge
  cases hl' : minMaxLS x t' with
  | none => rw [hl'] at hge; cases hge
  | some l' => rw [hl'] at hge; exact ⟨l', rfl, hge⟩

theorem reduces_minMaxLS_ge (x : Nat) {t t' : Term} (hr : Reduces t t')
    {l : Nat} (hl : minMaxLS x t = some l) :
    ∃ l', minMaxLS x t' = some l' ∧ l ≤ l' := by
  have hge : optLeSome (minLSAt x 0 t) (minLSAt x 0 t') := reduces_minLSAt_ge x hr 0
  rw [← minMaxLS_eq_minLSAt_zero x t, ← minMaxLS_eq_minLSAt_zero x t', hl] at hge
  cases hl' : minMaxLS x t' with
  | none => rw [hl'] at hge; cases hge
  | some l' => rw [hl'] at hge; exact ⟨l', rfl, hge⟩

/-- **Context-Stripped `DPChain` Monotonicity for `minMaxLS` (`dpChain_minMaxLS_ge`)**:
    Across EVERY `DPChain a b` (which eliminates arbitrary open contexts `C`!), if `hasVar x b = true`,
    then `hasVar x a = true` and `minMaxLS x a ≤ minMaxLS x b`! -/
theorem dpChain_minMaxLS_ge (x : Nat) {a b : Term} (hdp : DPChain a b)
    (hxb : hasVar x b = true) :
    ∃ la lb, minMaxLS x a = some la ∧ minMaxLS x b = some lb ∧ la ≤ lb := by
  induction hdp with
  | @done a0 b0 hnr =>
    have hr := nonRootReduces_to_reduces hnr
    have hxa0 : hasVar x a0 = true := by rw [hasVar_reduces_eq x hr]; exact hxb
    cases hla0 : minLSAt x 0 a0 with
    | none => rw [(minLSAt_eq_none_iff x a0 0).mp hla0] at hxa0; cases hxa0
    | some la0 =>
      have hma0 : minMaxLS x a0 = some la0 := by rw [minMaxLS_eq_minLSAt_zero, hla0]
      obtain ⟨lb0, hmb0, hle⟩ := reduces_minMaxLS_ge x hr hma0
      exact ⟨la0, lb0, hma0, hmb0, hle⟩
  | @dp1 a0 p q r v hnr _ ih =>
    obtain ⟨lw', lb, hmw', hmb, hle2⟩ := ih hxb
    have hr_full : Reduces a0 ((p ⋅ r) ⋅ (q ⋅ r)) :=
      reduces_trans (nonRootReduces_to_reduces hnr) (.next (.root p q r) (.refl _))
    have hxa0 : hasVar x a0 = true := by
      rw [hasVar_reduces_eq x hr_full]
      cases hxw : hasVar x ((p ⋅ r) ⋅ (q ⋅ r)) with
      | true => rfl
      | false =>
        rw [minMaxLS_eq_minLSAt_zero, (minLSAt_eq_none_iff x _ 0).mpr hxw] at hmw'
        cases hmw'
    cases hla0 : minLSAt x 0 a0 with
    | none => rw [(minLSAt_eq_none_iff x a0 0).mp hla0] at hxa0; cases hxa0
    | some la0 =>
      have hma0 : minMaxLS x a0 = some la0 := by rw [minMaxLS_eq_minLSAt_zero, hla0]
      obtain ⟨lw1, hmw1, hle1⟩ := reduces_minMaxLS_ge x hr_full hma0
      rw [hmw'] at hmw1; injection hmw1 with heq; subst heq
      exact ⟨la0, lb, hma0, hmb, Nat.le_trans hle1 hle2⟩
  | @dp2 a0 p q r v hnr _ ih =>
    obtain ⟨lpr, lb, hmpr, hmb, hle2⟩ := ih hxb
    have hr_nr := nonRootReduces_to_reduces hnr
    have hpr0 : minLSAt x 0 (p ⋅ r) = some lpr := by rw [← minMaxLS_eq_minLSAt_zero, hmpr]
    have hxpr : hasVar x (p ⋅ r) = true := by
      cases hx : hasVar x (p ⋅ r) with
      | true => rfl
      | false => rw [(minLSAt_eq_none_iff x (p ⋅ r) 0).mpr hx] at hpr0; cases hpr0
    have hxs : hasVar x (S ⋅ p ⋅ q ⋅ r) = true := by
      rcases (Bool.or_eq_true _ _).mp hxpr with hxp | hxr
      · simp [S, hasVar, hxp]
      · simp [S, hasVar, hxr]
    have hxa0 : hasVar x a0 = true := by rw [hasVar_reduces_eq x hr_nr]; exact hxs
    cases hla0 : minLSAt x 0 a0 with
    | none => rw [(minLSAt_eq_none_iff x a0 0).mp hla0] at hxa0; cases hxa0
    | some la0 =>
      have hma0 : minMaxLS x a0 = some la0 := by rw [minMaxLS_eq_minLSAt_zero, hla0]
      obtain ⟨ls, hms, hle1⟩ := reduces_minMaxLS_ge x hr_nr hma0
      have hs0 : optAllGe ls (minLSAt x 0 (S ⋅ p ⋅ q ⋅ r)) := by
        rw [← minMaxLS_eq_minLSAt_zero, hms]; exact Nat.le_refl ls
      change optAllGe ls (optMin (optMin (minLSAt x 0 p) (minLSAt x 0 q)) (minLSAt x 0 r)) at hs0
      have hs_pq : optAllGe ls (optMin (minLSAt x 0 p) (minLSAt x 0 q)) := (optAllGe_optMin_iff.mp hs0).1
      have hgr : optAllGe ls (minLSAt x 0 r) := (optAllGe_optMin_iff.mp hs0).2
      have hgp : optAllGe ls (minLSAt x 0 p) := (optAllGe_optMin_iff.mp hs_pq).1
      have hgp1 : optAllGe ls (minLSAt x 1 p) :=
        optAllGe_of_optLeSome hgp (minLSAt_mono_offset x p (Nat.zero_le 1))
      have hg_pr : optAllGe ls (minLSAt x 0 (p ⋅ r)) := optAllGe_optMin_iff.mpr ⟨hgp1, hgr⟩
      rw [hpr0] at hg_pr
      exact ⟨la0, lb, hma0, hmb, Nat.le_trans hle1 (Nat.le_trans hg_pr hle2)⟩
  | @dp3 a0 p q r v hnr _ ih =>
    obtain ⟨lqr, lb, hmqr, hmb, hle2⟩ := ih hxb
    have hr_nr := nonRootReduces_to_reduces hnr
    have hqr0 : minLSAt x 0 (q ⋅ r) = some lqr := by rw [← minMaxLS_eq_minLSAt_zero, hmqr]
    have hxqr : hasVar x (q ⋅ r) = true := by
      cases hx : hasVar x (q ⋅ r) with
      | true => rfl
      | false => rw [(minLSAt_eq_none_iff x (q ⋅ r) 0).mpr hx] at hqr0; cases hqr0
    have hxs : hasVar x (S ⋅ p ⋅ q ⋅ r) = true := by
      rcases (Bool.or_eq_true _ _).mp hxqr with hxq | hxr
      · simp [S, hasVar, hxq]
      · simp [S, hasVar, hxr]
    have hxa0 : hasVar x a0 = true := by rw [hasVar_reduces_eq x hr_nr]; exact hxs
    cases hla0 : minLSAt x 0 a0 with
    | none => rw [(minLSAt_eq_none_iff x a0 0).mp hla0] at hxa0; cases hxa0
    | some la0 =>
      have hma0 : minMaxLS x a0 = some la0 := by rw [minMaxLS_eq_minLSAt_zero, hla0]
      obtain ⟨ls, hms, hle1⟩ := reduces_minMaxLS_ge x hr_nr hma0
      have hs0 : optAllGe ls (minLSAt x 0 (S ⋅ p ⋅ q ⋅ r)) := by
        rw [← minMaxLS_eq_minLSAt_zero, hms]; exact Nat.le_refl ls
      change optAllGe ls (optMin (optMin (minLSAt x 0 p) (minLSAt x 0 q)) (minLSAt x 0 r)) at hs0
      have hs_pq : optAllGe ls (optMin (minLSAt x 0 p) (minLSAt x 0 q)) := (optAllGe_optMin_iff.mp hs0).1
      have hgr : optAllGe ls (minLSAt x 0 r) := (optAllGe_optMin_iff.mp hs0).2
      have hgq : optAllGe ls (minLSAt x 0 q) := (optAllGe_optMin_iff.mp hs_pq).2
      have hgq1 : optAllGe ls (minLSAt x 1 q) :=
        optAllGe_of_optLeSome hgq (minLSAt_mono_offset x q (Nat.zero_le 1))
      have hg_qr : optAllGe ls (minLSAt x 0 (q ⋅ r)) := optAllGe_optMin_iff.mpr ⟨hgq1, hgr⟩
      rw [hqr0] at hg_qr
      exact ⟨la0, lb, hma0, hmb, Nat.le_trans hle1 (Nat.le_trans hg_qr hle2)⟩

/-- Constructive reconstruction of a context reduction from any `DPChain`. -/
theorem dpChain_to_plugCtx_reduces {a v : Term} (hdp : DPChain a v) :
    ∃ C : Ctx, Reduces a (plugCtx C v) := by
  induction hdp with
  | done hnr => exact ⟨.hole, nonRootReduces_to_reduces hnr⟩
  | @dp1 a0 p q r v hnr _ ih =>
    obtain ⟨C, hC⟩ := ih
    exact ⟨C, reduces_trans (nonRootReduces_to_reduces hnr) (.next (.root p q r) hC)⟩
  | @dp2 a0 p q r v hnr _ ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨.left C (q ⋅ r), ?_⟩
    exact reduces_trans (nonRootReduces_to_reduces hnr)
      (.next (.root p q r) (plugCtx_reduces (.left .hole (q ⋅ r)) hC))
  | @dp3 a0 p q r v hnr _ ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨.right (p ⋅ r) C, ?_⟩
    exact reduces_trans (nonRootReduces_to_reduces hnr)
      (.next (.root p q r) (plugCtx_reduces (.right (p ⋅ r) .hole) hC))

/-- **Exact Constructive Equivalence for Full Conjecture 17 (`conjecture17_iff_no_dpChain_spiral`)**:
    Conjecture 17 (`∀ M C σ, ¬ StepPlus M (plugCtx C (subst σ M))`, over ALL contexts `C`, open or
    closed!) is 100% constructively equivalent to the context-free dependency-pair statement
    `∀ M σ, ¬ (DPChain M (subst σ M) ∧ rs M < rs (subst σ M))`! -/
theorem conjecture17_iff_no_dpChain_spiral :
    (∀ M C σ, ¬ StepPlus M (plugCtx C (subst σ M))) ↔
      (∀ M σ, ¬ (DPChain M (subst σ M) ∧ rs M < rs (subst σ M))) := by
  constructor
  · intro hno M σ ⟨hdp, hrs_lt⟩
    obtain ⟨C, hred⟩ := dpChain_to_plugCtx_reduces hdp
    rcases reduces_eq_or_stepPlus hred with heq | hsp
    · have hlt_leaves : leaves M < leaves (plugCtx C (subst σ M)) := by
        -- Since `rs M < rs (subst σ M)`, `M ≠ subst σ M`!
        have hle1 : leaves M ≤ leaves (subst σ M) := leaves_subst_ge σ M
        have hle2 : leaves (subst σ M) ≤ leaves (plugCtx C (subst σ M)) := leaves_plugCtx_ge C (subst σ M)
        exact if heq_l : leaves M = leaves (plugCtx C (subst σ M)) then by
          exfalso
          cases C with
          | hole =>
            change M = subst σ M at heq
            rw [← heq] at hrs_lt
            exact Nat.lt_irrefl _ hrs_lt
          | left c' r =>
            have hgt : leaves (subst σ M) < leaves (plugCtx (.left c' r) (subst σ M)) :=
              plugCtx_leaves_gt (fun h => by cases h) (subst σ M)
            exact Nat.lt_irrefl (leaves M) (by rw [← heq_l] at hgt; exact Nat.lt_of_le_of_lt hle1 hgt)
          | right l c' =>
            have hgt : leaves (subst σ M) < leaves (plugCtx (.right l c') (subst σ M)) :=
              plugCtx_leaves_gt (fun h => by cases h) (subst σ M)
            exact Nat.lt_irrefl (leaves M) (by rw [← heq_l] at hgt; exact Nat.lt_of_le_of_lt hle1 hgt)
        else
          Nat.lt_of_le_of_ne (Nat.le_trans hle1 hle2) heq_l
      rw [← heq] at hlt_leaves
      exact Nat.lt_irrefl _ hlt_leaves
    · exact hno M C σ hsp
  · intro hnodp M C σ hsp
    suffices ∀ (L : Nat) (U : Term), leaves U ≤ L → ∀ C', ¬ StepPlus U (plugCtx C' (subst σ U)) from
      this (leaves M) M (Nat.le_refl _) C hsp
    intro L
    induction L with
    | zero =>
      intro U hL _ _
      exact Nat.not_succ_le_zero 0 (Nat.le_trans (leaves_pos U) hL)
    | succ L ihL =>
      intro U hL C' hspU
      exact if hle : leaves U ≤ L then
        ihL U hle C' hspU
      else by
        rcases open_spiral_subterm_or_self_right_tail hspU with
            ⟨u, c'', hstrict, hu_sp⟩ | ⟨hdp, hrs_lt, _⟩
        · have hu_lt : leaves u < leaves U := strictSubterm_leaves_lt hstrict
          exact ihL u (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hu_lt hL)) c'' hu_sp
        · exact hnodp U σ ⟨hdp, hrs_lt⟩

end FormalNoSpiral
