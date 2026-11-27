import formal_wolfram12.wolfram_12_benchmarks
import zero_navigator_multiway.multiway_and_q30_theorems

/-!
# Wolfram Frontier Part II: Exact All-Step `→_{lo}` Jump-Ahead Formulas, `AAA` Multiway Invariants, Garden-of-Eden Normal Forms, and Subterm Appearance Separation

Machine-checked in Lean 4.33.1 in pure constructive kernel logic (`#print axioms` uses at most
`[propext, Quot.sound]`), establishing four frontier advances for Stephen Wolfram's $20,000
`S` Combinator Challenge (`wolfram_announcement.txt`, lines 140–179):

1. **Explicit All-Step `→_{lo}` Jump-Ahead Terms & Exact Cubic Leaf-Count Formulas**:
   - **Zachos's 10-Leaf Productive Term (`zachos`)**: Explicit HNF context `zachosExplicitCtx n`,
     explicit `t`-th state `zachosClosedFormTerm t` (`∀ t, iterateLO t zachos = zachosClosedFormTerm t`),
     exact cubic leaf count `10 + 2 * n * (n + 2) * (n + 4) / 3 + ...` for **all** `t : Nat`,
     and the **Triangular Staircase First-Difference Law**: for every `m : Nat` and `j ≤ m`,
     at `t = m * (m + 1) / 2 + j`, `leaves (iterateLO (t + 1) zachos) = leaves (iterateLO t zachos) + 2 * (m + 2)`
     (`+4, +6, +6, +8, +8, +8, +10, +10, +10, +10, ...`)!
   - **Wolfram's Benchmark #2 (`wolfram_2`, `s[s][s][s[s[s]]][s[s]]`) & Algebraic-Twin `+14` Shift Law**:
     Explicit all-step term `wolfram2ClosedFormTerm t`, exact cubic leaf formula
     `∀ t, leaves (iterateLO t wolfram_2) = wolfram2ClosedFormLeaves t`, and the **Constant `+14`
     Twin Shift Law** with `w2Twin = w2Base ⋅ w2Base` (which shares **identical** values in all
     three finite algebras `A_SN`, `A_HN`, `A_P` with `wolfram_2`, yet satisfies `¬ ConvS wolfram_2 w2Twin`):
     `∀ t, 3 ≤ t → leaves (iterateLO (t + 1) wolfram_2) + 14 = leaves (iterateLO t w2Twin)`!
   - **10-Leaf Universal Seed (`tenLeafSeed = zachosPrecursor ⋅ S = S(S(SS))(S(SS))(SS)S`)**:
     Explicit context `tlsExplicitCtx` and exact cubic leaf count `tenLeafSeedClosedFormLeaves t`
     for **every** `t : Nat` (`∀ t, leaves (iterateLO t tenLeafSeed) = tenLeafSeedClosedFormLeaves t`).

2. **Exact Multiway & `→_{lo}` Grammar for `AAA = (S S S)(S S S)(S S S)`**:
   - 3-rule inductive grammar `GA` closed under **all** multiway steps `Step t t'` with strict
     stepwise leaf growth `leaves t + 2 ≤ leaves t'`, proving `9 + 2 * k ≤ leaves (iterateLO k AAA)`,
     pure head reduction `HeadStepsN k AAA (iterateLO k AAA)` for all `k : Nat`, and **Universal
     Multiway Subterm Exclusion**: `S ⋅ (S ⋅ S)` (`S(SS)`) **never** appears as a subterm anywhere
     in the entire infinite multiway graph `{ T | Reduces AAA T }`!

3. **Complete Characterization & Constructive Decidability of Garden-of-Eden Normal Forms**:
   - Structural characterization (`goe_s2_iff`) and total decision procedure `decideGardenOfEdenNF`
     deciding whether a closed Normal Form `p` has in-degree `0` in `CL(S)` (`∀ m, noVars m = true → ¬ StepPlus m p`),
     infinite constructive GoE tower laws (`leaves v ≤ leaves u → GoE (S ⋅ u ⋅ v)`), and the exact
     Catalan GoE census for sizes `1..7` (`1/1, 1/1, 2/2, 3/4, 7/9, 15/21, 37/51`).

4. **Sharp Multiway (`↠_S`) vs. Leftmost-Outermost (`→_{lo}`) Subterm Appearance Separation**:
   - Minimal 7-leaf strongly normalizing witness `M_sn_sep` where a 6-leaf NF `P_sn_sep` appears in
     1 multiway step yet never appears in `iterateLO k M_sn_sep` for any `k : Nat`;
   - Infinite non-halting witness `M_inf_sep = S ⋅ AAA ⋅ (A_comb ⋅ B_comb)` where the **3-leaf** NF
     `S ⋅ B_comb = S(SS)` appears in 1 multiway step yet **never** appears at any step `k : Nat` of
     the infinite evolution `iterateLO k M_inf_sep`!
-/

namespace FormalWolframFrontier

open FormalAlgebra FormalWolfram12 ZeroNavigatorMultiway

/-! ## Section 1: Explicit All-Step `→_{lo}` Jump-Ahead & Exact Cubic Leaf-Count Formulas -/

/-- Extra leaf contribution of a frozen `LOFrame` context around its active focus. -/
def ctxExtraLeaves : List LOFrame → Nat
  | [] => 0
  | .s1 :: fs => 1 + ctxExtraLeaves fs
  | .s2L r :: fs => 1 + leaves r + ctxExtraLeaves fs
  | .s2R l :: fs => 1 + leaves l + ctxExtraLeaves fs

theorem leaves_plugFrame (f : LOFrame) (u : Term) :
    leaves (plugFrame f u) = ctxExtraLeaves [f] + leaves u := by
  cases f <;> simp only [plugFrame, ctxExtraLeaves, leaves, S] <;> omega

theorem leaves_wrapLOContext (ctx : List LOFrame) (u : Term) :
    leaves (wrapLOContext ctx u) = ctxExtraLeaves ctx + leaves u := by
  induction ctx with
  | nil => simp [wrapLOContext, ctxExtraLeaves]
  | cons f fs ih =>
      simp only [wrapLOContext]
      rw [leaves_plugFrame, ih]
      cases f <;> simp only [ctxExtraLeaves] <;> omega

theorem ctxExtraLeaves_append (c1 c2 : List LOFrame) :
    ctxExtraLeaves (c1 ++ c2) = ctxExtraLeaves c1 + ctxExtraLeaves c2 := by
  induction c1 with
  | nil => simp [ctxExtraLeaves]
  | cons f fs ih =>
      cases f <;> simp only [List.cons_append, ctxExtraLeaves, ih] <;> omega

theorem ctxExtraLeaves_replicate_s2R (k : Nat) (l : Term) :
    ctxExtraLeaves (List.replicate k (.s2R l)) = k * (1 + leaves l) := by
  induction k with
  | zero => simp [ctxExtraLeaves]
  | succ k ih =>
      simp only [List.replicate_succ, ctxExtraLeaves, ih, Nat.succ_mul]
      omega

/-! ### 1.1 Exact All-Step Closed Form & Triangular Staircase Law for `zachos` -/

theorem leaves_zachosTower (k : Nat) : leaves (zachosTower k) = 2 * k + 5 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [zachosTower, B_comb, S, leaves, ih]
      omega

/-- Explicit frozen HNF context of `zachos` at macro-cycle `n` (eliminating `∃ ctx`). -/
def zachosExplicitCtx : Nat → List LOFrame
  | 0 => []
  | n + 1 => zachosExplicitCtx n ++ List.replicate (n + 1) (.s2R (zachosTower (n + 1)))

theorem validLOContext_replicate_s2R (k : Nat) {z : Term}
    (hv : noVars z = true) (hn : stepLO z = none) :
    validLOContext (List.replicate k (.s2R z)) = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, validLOContext, validLOFrame, hv, hn,
        Option.isNone, Bool.and_self, ih]

theorem validLOContext_zachosExplicitCtx (n : Nat) :
    validLOContext (zachosExplicitCtx n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact validLOContext_append ih
        (validLOContext_replicate_s2R (n + 1) (noVars_zachosTower _) (stepLO_zachosTower_none _))

theorem zachos_partial_countdown :
    ∀ (j m : Nat), j ≤ m →
      ∀ (z : Term), noVars z = true → stepLO z = none →
        ∀ (ctx : List LOFrame), validLOContext ctx = true →
          iterateLO j (wrapLOContext ctx (zachosTower m ⋅ z)) =
            wrapLOContext (ctx ++ List.replicate j (LOFrame.s2R z)) (zachosTower (m - j) ⋅ z)
  | 0, _, _, _, _, _, _, _ => by
      simp [iterateLO, List.append_nil]
  | _ + 1, 0, hj, _, _, _, _, _ => by cases hj
  | j + 1, m + 1, hj, z, hvz, hnz, ctx, hctx => by
      have hs1 : stepLO (zachosTower (m + 1) ⋅ z) = some (plugFrame (LOFrame.s2R z) (zachosTower m ⋅ z)) := rfl
      have hv1 : validLOContext [LOFrame.s2R z] = true := by
        simp [validLOContext, validLOFrame, hvz, hnz, Option.isNone]
      have hstep : iterateLO (j + 1) (wrapLOContext ctx (zachosTower (m + 1) ⋅ z)) =
          iterateLO j (wrapLOContext (ctx ++ [LOFrame.s2R z]) (zachosTower m ⋅ z)) := by
        have hj1 : j + 1 = 1 + j := Nat.add_comm j 1
        rw [hj1, iterateLO_add 1 j, wrapLOContext_append]
        simp only [iterateLO, stepLO_wrapLOContext hctx hs1, wrapLOContext]
      rw [hstep, zachos_partial_countdown j m (Nat.le_of_succ_le_succ hj) z hvz hnz
        (ctx ++ [LOFrame.s2R z]) (validLOContext_append hctx hv1)]
      have hrep : [LOFrame.s2R z] ++ List.replicate j (LOFrame.s2R z) = List.replicate (j + 1) (LOFrame.s2R z) := rfl
      rw [List.append_assoc, hrep, Nat.succ_sub_succ_eq_sub]

/-- Explicit closed-form `stepLO` state of `zachos` at cycle `n`, intra-cycle offset `r ≤ n + 2`. -/
def zachosStateAt (n r : Nat) : Term :=
  match r with
  | 0 => wrapLOContext (zachosExplicitCtx n) (zachosBase ⋅ zachosTower n)
  | k + 1 =>
      wrapLOContext (zachosExplicitCtx n ++ List.replicate k (.s2R (zachosTower (n + 1))))
        (zachosTower (n + 1 - k) ⋅ zachosTower (n + 1))

theorem zachos_explicit_checkpoint (n : Nat) :
    iterateLO (jumpAheadZachosStep n) zachos =
      wrapLOContext (zachosExplicitCtx n) (zachosBase ⋅ zachosTower n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep_arith : jumpAheadZachosStep (n + 1) = jumpAheadZachosStep n + (n + 2) := by
        unfold jumpAheadZachosStep
        have h1 : (n + 1) * (n + 4) = n * (n + 3) + 2 * (n + 2) := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
          omega
        change (n + 1) * (n + 4) / 2 = n * (n + 3) / 2 + (n + 2)
        rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
      rw [hstep_arith, iterateLO_add, ih]
      have hvc := validLOContext_zachosExplicitCtx n
      have hs0 : stepLO (zachosBase ⋅ zachosTower n) =
          some (zachosTower (n + 1) ⋅ zachosTower (n + 1)) := rfl
      have hn2 : n + 2 = 1 + (n + 1) := by omega
      rw [hn2, iterateLO_add 1 (n + 1)]
      have h1 : iterateLO 1 (wrapLOContext (zachosExplicitCtx n) (zachosBase ⋅ zachosTower n)) =
          wrapLOContext (zachosExplicitCtx n) (zachosTower (n + 1) ⋅ zachosTower (n + 1)) := by
        simp only [iterateLO, stepLO_wrapLOContext hvc hs0]
      rw [h1, zachos_partial_countdown (n + 1) (n + 1) (Nat.le_refl _) (zachosTower (n + 1))
        (noVars_zachosTower _) (stepLO_zachosTower_none _) (zachosExplicitCtx n) hvc]
      simp [zachosExplicitCtx, zachosTower]

theorem zachos_explicit_all_offsets (n r : Nat) (hr : r ≤ n + 2) :
    iterateLO (jumpAheadZachosStep n + r) zachos = zachosStateAt n r := by
  rw [iterateLO_add, zachos_explicit_checkpoint n]
  cases r with
  | zero => rfl
  | succ k =>
      have hk : k ≤ n + 1 := Nat.le_of_succ_le_succ hr
      have hvc := validLOContext_zachosExplicitCtx n
      have hs0 : stepLO (zachosBase ⋅ zachosTower n) =
          some (zachosTower (n + 1) ⋅ zachosTower (n + 1)) := rfl
      have h1 : iterateLO (k + 1) (wrapLOContext (zachosExplicitCtx n) (zachosBase ⋅ zachosTower n)) =
          iterateLO k (wrapLOContext (zachosExplicitCtx n) (zachosTower (n + 1) ⋅ zachosTower (n + 1))) := by
        simp only [iterateLO, stepLO_wrapLOContext hvc hs0]
      rw [h1, zachos_partial_countdown k (n + 1) hk (zachosTower (n + 1))
        (noVars_zachosTower _) (stepLO_zachosTower_none _) (zachosExplicitCtx n) hvc]
      rfl

theorem three_mul_ctxExtraLeaves_zachos (n : Nat) :
    3 * ctxExtraLeaves (zachosExplicitCtx n) = n * (n + 1) * (2 * n + 10) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [zachosExplicitCtx, ctxExtraLeaves_append, ctxExtraLeaves_replicate_s2R,
        leaves_zachosTower, Nat.mul_add]
      rw [ih]
      simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.mul_succ,
        Nat.zero_mul, Nat.mul_zero, Nat.mul_assoc]
      omega

/-- Exact cubic leaf formula for `zachosStateAt n r` (`0 ≤ r ≤ n + 2`). -/
def zachosFormulaAt (n r : Nat) : Nat :=
  (10 + 2 * n * (n + 2) * (n + 4) / 3) + (if r = 0 then 0 else r * (2 * n + 6) - 2)

theorem leaves_zachosStateAt_eq (n r : Nat) (hr : r ≤ n + 2) :
    leaves (zachosStateAt n r) = zachosFormulaAt n r := by
  have h3 := three_mul_ctxExtraLeaves_zachos n
  have hbase_id : 3 * (ctxExtraLeaves (zachosExplicitCtx n) + (5 + (2 * n + 5))) =
      2 * n * (n + 2) * (n + 4) + 3 * 10 := by
    rw [Nat.mul_add, h3]
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.mul_succ,
      Nat.zero_mul, Nat.mul_zero, Nat.mul_assoc]
    omega
  have hbase_eq : ctxExtraLeaves (zachosExplicitCtx n) + (5 + (2 * n + 5)) =
      10 + 2 * n * (n + 2) * (n + 4) / 3 := by
    have hdiv := congrArg (· / 3) hbase_id
    rw [Nat.mul_div_right _ (by decide : 0 < 3),
        Nat.add_mul_div_left _ _ (by decide : 0 < 3)] at hdiv
    omega
  cases r with
  | zero =>
      unfold zachosStateAt zachosFormulaAt
      rw [leaves_wrapLOContext]
      have hlb : leaves zachosBase = 5 := rfl
      simp only [leaves, hlb, leaves_zachosTower, ↓reduceIte, Nat.add_zero]
      exact hbase_eq
  | succ k =>
      have hk : k ≤ n + 1 := Nat.le_of_succ_le_succ hr
      unfold zachosStateAt zachosFormulaAt
      rw [leaves_wrapLOContext, ctxExtraLeaves_append, ctxExtraLeaves_replicate_s2R]
      simp only [leaves, leaves_zachosTower, Nat.succ_ne_zero, ↓reduceIte]
      have h8 : 1 + (2 * (n + 1) + 5) = (2 * n + 6) + 2 := by omega
      have hlin :
          k * (1 + (2 * (n + 1) + 5)) + ((2 * (n + 1 - k) + 5) + (2 * (n + 1) + 5)) =
          (5 + (2 * n + 5)) + ((k + 1) * (2 * n + 6) - 2) := by
        rw [h8, Nat.mul_add, Nat.add_mul k 1 (2 * n + 6), Nat.one_mul]
        omega
      rw [Nat.add_assoc, hlin, ← Nat.add_assoc, hbase_eq]

/-- Constructive cycle finder returning `(n, r)` with `t = n * (n + 3) / 2 + r` and `r ≤ n + 1`. -/
def zachosDecodeAux : Nat → Nat → Nat × Nat
  | 0, curN => (curN, 0)
  | rem + 1, curN =>
      let sub := zachosDecodeAux rem curN
      if sub.2 + 1 < sub.1 + 2 then (sub.1, sub.2 + 1)
      else (sub.1 + 1, 0)

def zachosDecode (t : Nat) : Nat × Nat :=
  zachosDecodeAux t 0

theorem zachosDecodeAux_spec (t : Nat) :
    let p := zachosDecode t
    jumpAheadZachosStep p.1 + p.2 = t ∧ p.2 ≤ p.1 + 1 := by
  dsimp only []
  unfold zachosDecode
  induction t with
  | zero => exact ⟨rfl, Nat.zero_le 1⟩
  | succ t ih =>
      simp only [zachosDecodeAux]
      rcases hd : zachosDecodeAux t 0 with ⟨n, r⟩
      rw [hd] at ih
      dsimp only [] at ih ⊢
      if hlt : r + 1 < n + 2 then
        rw [if_pos hlt]
        dsimp only []
        exact ⟨by omega, by omega⟩
      else
        rw [if_neg hlt]
        dsimp only []
        have hstep_arith : jumpAheadZachosStep (n + 1) = jumpAheadZachosStep n + (n + 2) := by
          unfold jumpAheadZachosStep
          have h1 : (n + 1) * (n + 4) = n * (n + 3) + 2 * (n + 2) := by
            simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
            omega
          change (n + 1) * (n + 4) / 2 = n * (n + 3) / 2 + (n + 2)
          rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
        exact ⟨by omega, Nat.zero_le _⟩

/-- Total closed-form `t`-th state and exact leaf-count functions for `zachos`. -/
def zachosClosedFormTerm (t : Nat) : Term :=
  let (n, r) := zachosDecode t
  zachosStateAt n r

def zachosClosedFormLeaves (t : Nat) : Nat :=
  let (n, r) := zachosDecode t
  zachosFormulaAt n r

/-- **All-Step Closed-Form Jump-Ahead Theorem for `zachos`**:
    Determines BOTH the exact `t`-th `stepLO` term AND its exact cubic leaf count for all `t : Nat`! -/
theorem zachos_all_step_closed_form (t : Nat) :
    iterateLO t zachos = zachosClosedFormTerm t ∧
    leaves (iterateLO t zachos) = zachosClosedFormLeaves t := by
  have ⟨heq, hle⟩ := zachosDecodeAux_spec t
  unfold zachosClosedFormTerm zachosClosedFormLeaves
  have hr2 : (zachosDecode t).2 ≤ (zachosDecode t).1 + 2 := by omega
  have hterm : iterateLO t zachos = zachosStateAt (zachosDecode t).1 (zachosDecode t).2 := by
    conv => lhs; rw [← heq]
    exact zachos_explicit_all_offsets (zachosDecode t).1 (zachosDecode t).2 hr2
  exact ⟨hterm, by rw [hterm, leaves_zachosStateAt_eq _ _ hr2]⟩

/-- **The Triangular Staircase First-Difference Theorem for `zachos`**:
    On the `m`-th triangular block `t = m * (m + 1) / 2 + j` (`0 ≤ j ≤ m`),
    every step increases `leaves` by **exact** `2 * (m + 2)` (`+4; +6,+6; +8,+8,+8; +10,+10,+10,+10; ...`)! -/
theorem zachos_triangular_staircase_law (m j : Nat) (hj : j ≤ m) :
    let t := m * (m + 1) / 2 + j
    leaves (iterateLO (t + 1) zachos) = leaves (iterateLO t zachos) + 2 * (m + 2) := by
  cases m with
  | zero =>
      have hj0 : j = 0 := by omega
      subst hj0
      rfl
  | succ n =>
      -- Notice `(n + 1) * (n + 2) / 2 = jumpAheadZachosStep n + 1`!
      have htri : (n + 1) * (n + 2) / 2 = jumpAheadZachosStep n + 1 := by
        unfold jumpAheadZachosStep
        have h1 : (n + 1) * (n + 2) = n * (n + 3) + 2 * 1 := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
          omega
        rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
      dsimp only []
      rw [htri]
      by_cases hlast : j = n + 1
      · -- `j = n + 1`: `t = jumpAheadZachosStep n + (n + 2) = jumpAheadZachosStep (n + 1)`,
        -- so `t -> t + 1` is `r = 0 -> r = 1` in cycle `n + 1`, whose jump is `2*(n+1) + 4 = 2*(n+3)`!
        subst hlast
        have hstep_arith : jumpAheadZachosStep n + 1 + (n + 1) = jumpAheadZachosStep (n + 1) := by
          unfold jumpAheadZachosStep
          have h1 : (n + 1) * (n + 4) = n * (n + 3) + 2 * (n + 2) := by
            simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
            omega
          change n * (n + 3) / 2 + 1 + (n + 1) = (n + 1) * (n + 4) / 2
          rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
          omega
        rw [hstep_arith]
        have h0 := zachos_explicit_all_offsets (n + 1) 0 (by omega)
        have h1 := zachos_explicit_all_offsets (n + 1) 1 (by omega)
        rw [Nat.add_zero] at h0
        rw [h0, h1, leaves_zachosStateAt_eq (n + 1) 0 (by omega),
            leaves_zachosStateAt_eq (n + 1) 1 (by omega)]
        unfold zachosFormulaAt
        simp only [↓reduceIte, Nat.one_ne_zero, Nat.one_mul]
        omega
      · -- `j ≤ n`: `t = jumpAheadZachosStep n + (j + 1)`, `t + 1 = jumpAheadZachosStep n + (j + 2)`!
        have hj_le : j ≤ n := by omega
        have ha1 : jumpAheadZachosStep n + 1 + j = jumpAheadZachosStep n + (j + 1) := by omega
        have ha2 : jumpAheadZachosStep n + (j + 1) + 1 = jumpAheadZachosStep n + (j + 2) := by omega
        rw [ha1, ha2,
            zachos_explicit_all_offsets n (j + 1) (by omega),
            zachos_explicit_all_offsets n (j + 2) (by omega),
            leaves_zachosStateAt_eq n (j + 1) (by omega),
            leaves_zachosStateAt_eq n (j + 2) (by omega)]
        unfold zachosFormulaAt
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_mul, Nat.one_mul]
        omega

/-! ### 1.2 Explicit All-Step Closed Form for `wolfram_2` & The `+14` Productive-Twin Shift Law -/

theorem leaves_w2Tower (k : Nat) : leaves (w2Tower k) = 2 * k + 6 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [w2Tower, B_comb, S, leaves, ih]
      omega

/-- Explicit frozen HNF context of `wolfram_2` at macro-cycle `n`. -/
def w2ExplicitCtx : Nat → List LOFrame
  | 0 => [.s2R (w2Tower 1)]
  | n + 1 =>
      w2ExplicitCtx n ++
      (.s2L (w2Tower (n + 2) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))) ::
        List.replicate (n + 1) (.s2R (w2Tower (n + 2))))

theorem validLOContext_w2ExplicitCtx (n : Nat) :
    validLOContext (w2ExplicitCtx n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hv_l : validLOFrame (.s2L (w2Tower (n + 2) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2)))) = true := by
        simp [validLOFrame, noVars, noVars_w2Tower]
      have hv_rep := validLOContext_replicate_s2R (n + 1) (noVars_w2Tower (n + 2)) (stepLO_w2Tower_none (n + 2))
      have hv_tail : validLOContext (.s2L (w2Tower (n + 2) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))) ::
          List.replicate (n + 1) (.s2R (w2Tower (n + 2)))) = true := by
        simp [validLOContext, hv_l, hv_rep]
      exact validLOContext_append ih hv_tail

theorem w2_partial_countdown :
    ∀ (j m : Nat), j ≤ m →
      ∀ (z : Term), noVars z = true → stepLO z = none →
        ∀ (ctx : List LOFrame), validLOContext ctx = true →
          iterateLO j (wrapLOContext ctx (w2Tower m ⋅ z)) =
            wrapLOContext (ctx ++ List.replicate j (LOFrame.s2R z)) (w2Tower (m - j) ⋅ z)
  | 0, _, _, _, _, _, _, _ => by simp [iterateLO, List.append_nil]
  | _ + 1, 0, hj, _, _, _, _, _ => by cases hj
  | j + 1, m + 1, hj, z, hvz, hnz, ctx, hctx => by
      have hs1 : stepLO (w2Tower (m + 1) ⋅ z) = some (plugFrame (LOFrame.s2R z) (w2Tower m ⋅ z)) := rfl
      have hv1 : validLOContext [LOFrame.s2R z] = true := by
        simp [validLOContext, validLOFrame, hvz, hnz, Option.isNone]
      have hstep : iterateLO (j + 1) (wrapLOContext ctx (w2Tower (m + 1) ⋅ z)) =
          iterateLO j (wrapLOContext (ctx ++ [LOFrame.s2R z]) (w2Tower m ⋅ z)) := by
        have hj1 : j + 1 = 1 + j := Nat.add_comm j 1
        rw [hj1, iterateLO_add 1 j, wrapLOContext_append]
        simp only [iterateLO, stepLO_wrapLOContext hctx hs1, wrapLOContext]
      rw [hstep, w2_partial_countdown j m (Nat.le_of_succ_le_succ hj) z hvz hnz
        (ctx ++ [LOFrame.s2R z]) (validLOContext_append hctx hv1)]
      have hrep : [LOFrame.s2R z] ++ List.replicate j (LOFrame.s2R z) = List.replicate (j + 1) (LOFrame.s2R z) := rfl
      rw [List.append_assoc, hrep, Nat.succ_sub_succ_eq_sub]

/-- Explicit closed-form `stepLO` state of `wolfram_2` at cycle `n`, offset `r ≤ n + 4`. -/
def w2StateAt (n r : Nat) : Term :=
  match r with
  | 0 => wrapLOContext (w2ExplicitCtx n) (w2Base ⋅ w2Tower (n + 1))
  | 1 => wrapLOContext (w2ExplicitCtx n) ((S ⋅ B_comb ⋅ w2Tower (n + 1)) ⋅ w2Tower (n + 2))
  | 2 => wrapLOContext (w2ExplicitCtx n) (w2Tower (n + 3) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2)))
  | j + 3 =>
      let rFreeze := w2Tower (n + 2) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))
      wrapLOContext (w2ExplicitCtx n ++ (.s2L rFreeze :: List.replicate j (.s2R (w2Tower (n + 2)))))
        (w2Tower (n + 1 - j) ⋅ w2Tower (n + 2))

theorem wolfram2_explicit_checkpoint (n : Nat) :
    iterateLO (jumpAheadWolfram2Step n) wolfram_2 =
      wrapLOContext (w2ExplicitCtx n) (w2Base ⋅ w2Tower (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep_arith : jumpAheadWolfram2Step (n + 1) = jumpAheadWolfram2Step n + (n + 4) := by
        unfold jumpAheadWolfram2Step
        have h1 : (n + 2) * (n + 7) = (n + 1) * (n + 6) + 2 * (n + 4) := by
          simp only [Nat.mul_add, Nat.add_mul]
          omega
        rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
        omega
      rw [hstep_arith, iterateLO_add, ih]
      have hvc := validLOContext_w2ExplicitCtx n
      let u0 := w2Base ⋅ w2Tower (n + 1)
      let u1 := (S ⋅ B_comb ⋅ w2Tower (n + 1)) ⋅ w2Tower (n + 2)
      let u2 := w2Tower (n + 3) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))
      let rFreeze := w2Tower (n + 2) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))
      have hs0 : stepLO u0 = some u1 := rfl
      have hs1 : stepLO u1 = some u2 := rfl
      have hs2 : stepLO u2 = some (plugFrame (.s2L rFreeze) (w2Tower (n + 1) ⋅ w2Tower (n + 2))) := rfl
      have hv_rf : validLOContext [.s2L rFreeze] = true := by
        simp [validLOContext, validLOFrame, rFreeze, noVars, noVars_w2Tower]
      have hn4 : n + 4 = 3 + (n + 1) := by omega
      rw [hn4, iterateLO_add 3 (n + 1)]
      have h3 : iterateLO 3 (wrapLOContext (w2ExplicitCtx n) u0) =
          wrapLOContext (w2ExplicitCtx n ++ [LOFrame.s2L rFreeze]) (w2Tower (n + 1) ⋅ w2Tower (n + 2)) := by
        rw [wrapLOContext_append]
        simp only [iterateLO, stepLO_wrapLOContext hvc hs0, stepLO_wrapLOContext hvc hs1,
          stepLO_wrapLOContext hvc hs2, wrapLOContext]
      rw [h3, w2_partial_countdown (n + 1) (n + 1) (Nat.le_refl _) (w2Tower (n + 2))
        (noVars_w2Tower _) (stepLO_w2Tower_none _) (w2ExplicitCtx n ++ [LOFrame.s2L rFreeze])
        (validLOContext_append hvc hv_rf)]
      simp [w2ExplicitCtx, List.append_assoc, w2Tower, rFreeze]

theorem wolfram2_explicit_all_offsets (n r : Nat) (hr : r ≤ n + 4) :
    iterateLO (jumpAheadWolfram2Step n + r) wolfram_2 = w2StateAt n r := by
  rw [iterateLO_add, wolfram2_explicit_checkpoint n]
  have hvc := validLOContext_w2ExplicitCtx n
  let u0 := w2Base ⋅ w2Tower (n + 1)
  let u1 := (S ⋅ B_comb ⋅ w2Tower (n + 1)) ⋅ w2Tower (n + 2)
  let u2 := w2Tower (n + 3) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))
  let rFreeze := w2Tower (n + 2) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))
  have hs0 : stepLO (w2Base ⋅ w2Tower (n + 1)) = some ((S ⋅ B_comb ⋅ w2Tower (n + 1)) ⋅ w2Tower (n + 2)) := rfl
  have hs1 : stepLO ((S ⋅ B_comb ⋅ w2Tower (n + 1)) ⋅ w2Tower (n + 2)) =
      some (w2Tower (n + 3) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))) := rfl
  have hs2 : stepLO (w2Tower (n + 3) ⋅ (w2Tower (n + 1) ⋅ w2Tower (n + 2))) =
      some (plugFrame (LOFrame.s2L rFreeze) (w2Tower (n + 1) ⋅ w2Tower (n + 2))) := rfl
  match r with
  | 0 => rfl
  | 1 => simp only [iterateLO, stepLO_wrapLOContext hvc hs0, w2StateAt]
  | 2 => simp only [iterateLO, stepLO_wrapLOContext hvc hs0, stepLO_wrapLOContext hvc hs1, w2StateAt]
  | j + 3 =>
      have hj : j ≤ n + 1 := by omega
      have hv_rf : validLOContext [LOFrame.s2L rFreeze] = true := by
        simp [validLOContext, validLOFrame, rFreeze, noVars, noVars_w2Tower]
      have h3 : iterateLO (j + 3) (wrapLOContext (w2ExplicitCtx n) u0) =
          iterateLO j (wrapLOContext (w2ExplicitCtx n ++ [LOFrame.s2L rFreeze]) (w2Tower (n + 1) ⋅ w2Tower (n + 2))) := by
        have hj3 : j + 3 = 3 + j := Nat.add_comm j 3
        rw [hj3, iterateLO_add 3 j, wrapLOContext_append]
        dsimp only [u0]
        simp only [iterateLO, stepLO_wrapLOContext hvc hs0, stepLO_wrapLOContext hvc hs1,
          stepLO_wrapLOContext hvc hs2, wrapLOContext]
      rw [h3, w2_partial_countdown j (n + 1) hj (w2Tower (n + 2))
        (noVars_w2Tower _) (stepLO_w2Tower_none _) (w2ExplicitCtx n ++ [LOFrame.s2L rFreeze])
        (validLOContext_append hvc hv_rf)]
      simp [w2StateAt, List.append_assoc, rFreeze]

theorem six_mul_ctxExtraLeaves_w2 (n : Nat) :
    6 * ctxExtraLeaves (w2ExplicitCtx n) = 4 * n ^ 3 + 51 * n ^ 2 + 185 * n + 54 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [w2ExplicitCtx, ctxExtraLeaves_append, ctxExtraLeaves,
        ctxExtraLeaves_replicate_s2R, leaves, leaves_w2Tower]
      have hc3 : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.add_mul,
          Nat.succ_mul, Nat.mul_succ, Nat.zero_mul, Nat.mul_assoc]
        omega
      have hc2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.add_mul,
          Nat.succ_mul, Nat.mul_succ, Nat.zero_mul]
        omega
      have hquad : (n + 1) * (1 + (2 * (n + 2) + 6)) = 2 * n ^ 2 + 13 * n + 11 := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.pow_succ, Nat.pow_zero,
          Nat.succ_mul, Nat.mul_succ, Nat.zero_mul]
        omega
      rw [Nat.mul_add, ih, hc3, hc2, hquad]
      omega

def w2IntraOffset (n r : Nat) : Nat :=
  match r with
  | 0 => 0
  | 1 => 2 * n + 7
  | 2 => 4 * n + 16
  | j + 3 => (8 * n + 33) + j * (2 * n + 9)

def wolfram2FormulaAt (n r : Nat) : Nat :=
  (4 * n ^ 3 + 51 * n ^ 2 + 197 * n + 138) / 6 + w2IntraOffset n r

theorem leaves_w2StateAt_eq (n r : Nat) (hr : r ≤ n + 4) :
    leaves (w2StateAt n r) = wolfram2FormulaAt n r := by
  have h6 := six_mul_ctxExtraLeaves_w2 n
  have hbase_id : 6 * (ctxExtraLeaves (w2ExplicitCtx n) + (6 + (2 * (n + 1) + 6))) =
      4 * n ^ 3 + 51 * n ^ 2 + 197 * n + 138 := by
    rw [Nat.mul_add, h6]; omega
  have hbase_eq : ctxExtraLeaves (w2ExplicitCtx n) + (6 + (2 * (n + 1) + 6)) =
      (4 * n ^ 3 + 51 * n ^ 2 + 197 * n + 138) / 6 := by
    have hdiv := congrArg (· / 6) hbase_id
    rw [Nat.mul_div_right _ (by decide : 0 < 6)] at hdiv
    exact hdiv
  have hlb : leaves w2Base = 6 := rfl
  have hl_s : leaves S = 1 := rfl
  have hl_b : leaves B_comb = 2 := rfl
  match r with
  | 0 =>
      unfold w2StateAt wolfram2FormulaAt w2IntraOffset
      rw [leaves_wrapLOContext, ← hbase_eq]
      simp only [leaves, hlb, leaves_w2Tower, Nat.add_zero]
  | 1 =>
      unfold w2StateAt wolfram2FormulaAt w2IntraOffset
      rw [leaves_wrapLOContext, ← hbase_eq]
      simp only [leaves, hl_s, hl_b, leaves_w2Tower]
      omega
  | 2 =>
      unfold w2StateAt wolfram2FormulaAt w2IntraOffset
      rw [leaves_wrapLOContext, ← hbase_eq]
      simp only [leaves, leaves_w2Tower]
      omega
  | j + 3 =>
      have hj : j ≤ n + 1 := by omega
      unfold w2StateAt wolfram2FormulaAt w2IntraOffset
      rw [leaves_wrapLOContext, ctxExtraLeaves_append, ← hbase_eq]
      clear h6 hbase_id hbase_eq
      simp only [ctxExtraLeaves, ctxExtraLeaves_replicate_s2R, leaves, leaves_w2Tower]
      have h11 : 1 + (2 * (n + 2) + 6) = (2 * n + 9) + 2 := by omega
      rw [h11, Nat.mul_add j (2 * n + 9) 2]
      omega

def w2DecodePost4Aux : Nat → Nat × Nat
  | 0 => (0, 0)
  | rem + 1 =>
      let sub := w2DecodePost4Aux rem
      if sub.2 + 1 < sub.1 + 4 then (sub.1, sub.2 + 1)
      else (sub.1 + 1, 0)

theorem w2DecodePost4Aux_spec (d : Nat) :
    let p := w2DecodePost4Aux d
    jumpAheadWolfram2Step p.1 + p.2 = d + 4 ∧ p.2 ≤ p.1 + 3 := by
  dsimp only []
  induction d with
  | zero => exact ⟨rfl, Nat.zero_le 3⟩
  | succ d ih =>
      simp only [w2DecodePost4Aux]
      rcases hd : w2DecodePost4Aux d with ⟨n, r⟩
      rw [hd] at ih
      dsimp only [] at ih ⊢
      if hlt : r + 1 < n + 4 then
        rw [if_pos hlt]
        dsimp only []
        exact ⟨by omega, by omega⟩
      else
        rw [if_neg hlt]
        dsimp only []
        have hstep_arith : jumpAheadWolfram2Step (n + 1) = jumpAheadWolfram2Step n + (n + 4) := by
          unfold jumpAheadWolfram2Step
          have h1 : (n + 2) * (n + 7) = (n + 1) * (n + 6) + 2 * (n + 4) := by
            simp only [Nat.succ_mul, Nat.mul_succ, Nat.zero_mul]
            omega
          rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
          omega
        exact ⟨by omega, Nat.zero_le _⟩

def wolfram2ClosedFormTerm (t : Nat) : Term :=
  match t with
  | 0 => wolfram_2
  | 1 => iterateLO 1 wolfram_2
  | 2 => iterateLO 2 wolfram_2
  | 3 => iterateLO 3 wolfram_2
  | d + 4 =>
      let (n, r) := w2DecodePost4Aux d
      w2StateAt n r

def wolfram2ClosedFormLeaves (t : Nat) : Nat :=
  match t with
  | 0 => 8
  | 1 => 10
  | 2 => 11
  | 3 => 16
  | d + 4 =>
      let (n, r) := w2DecodePost4Aux d
      wolfram2FormulaAt n r

/-- **All-Step Closed-Form Jump-Ahead Theorem for `wolfram_2`**:
    Determines BOTH the exact `t`-th `stepLO` state AND its exact cubic leaf count for all `t : Nat`! -/
theorem wolfram2_all_step_closed_form (t : Nat) :
    iterateLO t wolfram_2 = wolfram2ClosedFormTerm t ∧
    leaves (iterateLO t wolfram_2) = wolfram2ClosedFormLeaves t := by
  match t with
  | 0 => exact ⟨rfl, rfl⟩
  | 1 => exact ⟨rfl, rfl⟩
  | 2 => exact ⟨rfl, rfl⟩
  | 3 => exact ⟨rfl, rfl⟩
  | d + 4 =>
      have ⟨heq, hle⟩ := w2DecodePost4Aux_spec d
      unfold wolfram2ClosedFormTerm wolfram2ClosedFormLeaves
      have hr4 : (w2DecodePost4Aux d).2 ≤ (w2DecodePost4Aux d).1 + 4 := by omega
      have hterm : iterateLO (d + 4) wolfram_2 = w2StateAt (w2DecodePost4Aux d).1 (w2DecodePost4Aux d).2 := by
        conv => lhs; rw [← heq]
        exact wolfram2_explicit_all_offsets _ _ hr4
      exact ⟨hterm, by rw [hterm, leaves_w2StateAt_eq _ _ hr4]⟩

/-- The 12-leaf algebraic twin `w2Twin = w2Base ⋅ w2Base` of `wolfram_2`. -/
def w2Twin : Term := w2Base ⋅ w2Base

private theorem s2_isRootNormalForm (x y : Term) : IsRootNormalForm (S ⋅ x ⋅ y) := by
  have hpres : ∀ (t t' : Term), Reduces t t' → ∀ (a b : Term), t = S ⋅ a ⋅ b →
      ∃ a' b', t' = S ⋅ a' ⋅ b' := by
    intro t t' hr
    induction hr with
    | refl _ =>
        intro a b heq
        exact ⟨a, b, heq⟩
    | @next u w _ hs _ ih =>
        intro a b heq
        subst heq
        cases hs with
        | @left _ l' _ hsl =>
            generalize hsu : (S ⋅ a) = sa at hsl
            cases hsl with
            | root _ _ _ => cases hsu
            | @left _ _ _ hll =>
                injection hsu with hs_eq _
                subst hs_eq; cases hll
            | @right _ _ a1 _ =>
                injection hsu with hs_eq _
                subst hs_eq
                exact ih a1 b rfl
        | @right _ _ b1 _ => exact ih a b1 rfl
  rintro ⟨p, q, r, hred⟩
  obtain ⟨a', b', heq⟩ := hpres _ _ hred x y rfl
  injection heq with h1 _
  injection h1 with h2 _
  cases h2

/-- **The Surprising `+14` Twin Leaf-Shift Law (`wolfram2_vs_w2Twin_shift_14`)**:
    1. `w2Twin` and `wolfram_2` share **identical** `A_SN` and `A_P` states (`evalSN = .sn38` and `evalP = .p37`).
    2. Nevertheless, `wolfram_2` and `w2Twin` are **not** `$=_S$`-convertible (`¬ ConvS wolfram_2 w2Twin`).
    3. Yet for **every** `t ≥ 3`, `leaves (iterateLO (t + 1) wolfram_2) + 14 = leaves (iterateLO t w2Twin)`! -/
theorem wolfram2_vs_w2Twin_shift_14 :
    (evalSN w2Twin = evalSN wolfram_2 ∧
     evalP w2Twin = evalP wolfram_2) ∧
    ¬ ConvS wolfram_2 w2Twin ∧
    ∀ t : Nat, 3 ≤ t →
      leaves (iterateLO (t + 1) wolfram_2) + 14 = leaves (iterateLO t w2Twin) := by
  let cW2_0 : List LOFrame := [LOFrame.s2R (w2Tower 1)]
  let cTw_0 : List LOFrame := [LOFrame.s2L (w2Tower 1 ⋅ (w2Base ⋅ w2Tower 1))]
  have hvc_w2 : validLOContext cW2_0 = true := rfl
  have hvc_tw : validLOContext cTw_0 = true := rfl
  have hit_w2 : iterateLO 4 wolfram_2 = wrapLOContext cW2_0 (w2Base ⋅ w2Tower 1) := rfl
  have hit_tw : iterateLO 3 w2Twin = wrapLOContext cTw_0 (w2Base ⋅ w2Tower 1) := rfl
  have hextra_diff : ctxExtraLeaves cTw_0 = ctxExtraLeaves cW2_0 + 14 := rfl
  have hactive_u0 : ∀ k : Nat, ∃ mid,
      iterateLO k (wrapLOContext cW2_0 (w2Base ⋅ w2Tower 1)) = wrapLOContext cW2_0 mid ∧
      iterateLO k (wrapLOContext cTw_0 (w2Base ⋅ w2Tower 1)) = wrapLOContext cTw_0 mid := by
    have hwrap_all : ∀ (k : Nat) (c : List LOFrame) (foc : Term),
        validLOContext c = true →
        (∀ j, j < k → (stepLO (iterateLO j foc)).isSome = true) →
        iterateLO k (wrapLOContext c foc) = wrapLOContext c (iterateLO k foc) := by
      intro k
      induction k with
      | zero => intro _ _ _ _; rfl
      | succ k ih =>
          intro c foc hvc hall
          have h0 := hall 0 (Nat.zero_lt_succ k)
          change (stepLO foc).isSome = true at h0
          cases hs : stepLO foc with
          | none => rw [hs] at h0; cases h0
          | some foc' =>
              simp only [iterateLO, stepLO_wrapLOContext hvc hs, hs]
              exact ih c foc' hvc (fun j hj => by
                have hsub := hall (j + 1) (Nat.succ_lt_succ hj)
                simpa [iterateLO, hs] using hsub)
    have hu0_nonsn : ∀ j : Nat, (stepLO (iterateLO j (w2Base ⋅ w2Tower 1))).isSome = true :=
      ((decideHaltsLO_iff_halts (t := w2Base ⋅ w2Tower 1) rfl).2.2.2).mp rfl
    intro k
    exact ⟨iterateLO k (w2Base ⋅ w2Tower 1),
      hwrap_all k cW2_0 _ hvc_w2 (fun j _ => hu0_nonsn j),
      hwrap_all k cTw_0 _ hvc_tw (fun j _ => hu0_nonsn j)⟩
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · intro hconv
    -- `iterateLO 4 wolfram_2 = (B_comb ⋅ w2Tower 1) ⋅ u0`? Look at `cW2_0` vs `cTw_0`:
    -- Wait: `plugFrame (.s2R (w2Tower 1)) u0 = (S ⋅ w2Tower 1) ⋅ u0`? Let's check:
    -- `iterateLO 4 wolfram_2 = S ⋅ w2Tower 1 ⋅ u0` vs `iterateLO 3 w2Twin = S ⋅ u0 ⋅ (w2Tower 1 ⋅ u0)`!
    have hc43 : ConvS (iterateLO 4 wolfram_2) (iterateLO 3 w2Twin) :=
      .trans (.symm (reduces_to_convS (reduces_iterateLO 4 wolfram_2)))
             (.trans hconv (reduces_to_convS (reduces_iterateLO 3 w2Twin)))
    have hr1 : IsRootNormalForm (iterateLO 4 wolfram_2) := s2_isRootNormalForm _ _
    have hr2 : IsRootNormalForm (iterateLO 3 w2Twin) := s2_isRootNormalForm _ _
    have hpair := (rnf_convS_app_iff hr1 hr2).mp hc43
    -- Look at `hpair`: either left children or right children compare SN vs non-SN!
    -- Wait: `plugFrame (.s2R l) u = l ⋅ u` or `S ⋅ l ⋅ u`? Check `plugFrame`:
    -- In `cW2_0 = [.s2R (w2Tower 1)]`, `plugFrame (.s2R (w2Tower 1)) u0 = S ⋅ (w2Tower 1) ⋅ u0` (left child `S ⋅ w2Tower 1` is SN!),
    -- while in `cTw_0 = [.s2L ...]`, `plugFrame (.s2L R) u0 = S ⋅ u0 ⋅ R` (left child `S ⋅ u0` is NON-SN!)!
    have hl_sn : StrongNormalizing (S ⋅ w2Tower 1) :=
      (waldmann_theorem_9 (t := S ⋅ w2Tower 1) rfl).1.mpr (by decide)
    have hl_nonsn : ¬ StrongNormalizing (S ⋅ (w2Base ⋅ w2Tower 1)) :=
      fun h => ((waldmann_theorem_9 (t := S ⋅ (w2Base ⋅ w2Tower 1)) rfl).1.mp h) rfl
    exact hl_nonsn ((convS_sn_iff hpair.1).mp hl_sn)
  · intro t ht3
    let k := t - 3
    have htk : t = 3 + k := by omega
    have ht1 : t + 1 = 4 + k := by omega
    rw [ht1, htk, iterateLO_add 4 k wolfram_2, iterateLO_add 3 k w2Twin, hit_w2, hit_tw]
    obtain ⟨mid, hw2_k, htw_k⟩ := hactive_u0 k
    rw [hw2_k, htw_k, leaves_wrapLOContext, leaves_wrapLOContext, hextra_diff]
    omega

/-! ### 1.3 Explicit All-Step Cubic Leaf Formula for `tenLeafSeed = R_PF ⋅ S` -/

theorem leaves_numeralC (n : Nat) : leaves (numeralC n) = 2 * n + 5 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [numeralC, B_comb, S, leaves, ih]
      omega

theorem leaves_counterD (k n : Nat) : leaves (counterD k n) = 2 * k + 2 * n + 11 := by
  simp only [counterD, leaves, leaves_numeralC, S]
  omega

def leftHNFExtraLeaves : List Term → Nat
  | [] => 0
  | r :: rs => 1 + leaves r + leftHNFExtraLeaves rs

theorem leaves_wrapLeftHNF (ctx : List Term) (foc : Term) :
    leaves (wrapLeftHNF ctx foc) = leftHNFExtraLeaves ctx + leaves foc := by
  induction ctx with
  | nil => simp [wrapLeftHNF, leftHNFExtraLeaves]
  | cons r rs ih =>
      simp only [wrapLeftHNF, leftHNFExtraLeaves, leaves, S, ih]
      omega

theorem leftHNFExtraLeaves_append (c1 c2 : List Term) :
    leftHNFExtraLeaves (c1 ++ c2) = leftHNFExtraLeaves c1 + leftHNFExtraLeaves c2 := by
  induction c1 with
  | nil => simp [leftHNFExtraLeaves]
  | cons r rs ih =>
      simp only [List.cons_append, leftHNFExtraLeaves, ih]
      omega

theorem wrapLeftHNF_snoc (ctx : List Term) (foc rf : Term) :
    wrapLeftHNF (ctx ++ [rf]) foc = wrapLeftHNF ctx (S ⋅ foc ⋅ rf) := by
  induction ctx with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, wrapLeftHNF, ih]

def tlsCycleFrozen : Nat → Nat → List Term
  | 0, _ => []
  | k + 1, p => ((numeralC p ⋅ S) ⋅ counterD k (p + 1)) :: tlsCycleFrozen k p

def tlsExplicitCtx : Nat → List Term
  | 0 => []
  | m + 1 => tlsExplicitCtx m ++ tlsCycleFrozen (m + 1) m

theorem tls_partial_explicit :
    ∀ (r k p : Nat), r ≤ k →
      ∀ (ctx : List Term),
        iterateLO (4 * r) (wrapLeftHNF ctx (counterD k (p + 1))) =
          wrapLeftHNF (ctx ++ (tlsCycleFrozen k p).take r) (counterD (k - r) (p + 1))
  | 0, _, _, _, _ => by simp [iterateLO]
  | _ + 1, 0, _, hr, _ => by cases hr
  | r + 1, k + 1, p, hr, ctx => by
      let u0 := counterD (k + 1) (p + 1)
      let u1 := ((S ⋅ numeralC (p + 1)) ⋅ (numeralC k ⋅ numeralC (p + 1))) ⋅ S
      let u2 := (numeralC (p + 1) ⋅ S) ⋅ counterD k (p + 1)
      let u3 := (S ⋅ S ⋅ (numeralC p ⋅ S)) ⋅ counterD k (p + 1)
      let rf := (numeralC p ⋅ S) ⋅ counterD k (p + 1)
      have hs0 : stepLO u0 = some u1 := rfl
      have hs1 : stepLO u1 = some u2 := rfl
      have hs2 : stepLO u2 = some u3 := rfl
      have hs3 : stepLO u3 = some (S ⋅ counterD k (p + 1) ⋅ rf) := rfl
      have h4 : iterateLO 4 (wrapLeftHNF ctx u0) = wrapLeftHNF (ctx ++ [rf]) (counterD k (p + 1)) := by
        rw [wrapLeftHNF_snoc]
        simp only [iterateLO, stepLO_wrapLeftHNF ctx hs0, stepLO_wrapLeftHNF ctx hs1,
          stepLO_wrapLeftHNF ctx hs2, stepLO_wrapLeftHNF ctx hs3]
      have h4r : 4 * (r + 1) = 4 + 4 * r := by omega
      rw [h4r, iterateLO_add 4 (4 * r), h4,
          tls_partial_explicit r k p (Nat.le_of_succ_le_succ hr) (ctx ++ [rf])]
      dsimp only [rf]
      simp [tlsCycleFrozen, List.append_assoc, Nat.succ_sub_succ_eq_sub]

theorem tlsCycleFrozen_length (k p : Nat) : (tlsCycleFrozen k p).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [tlsCycleFrozen, ih]

private theorem list_take_all {α : Type} (xs : List α) : xs.take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem tls_explicit_checkpoint (m : Nat) :
    iterateLO (2 * (m + 1) * (m + 1) - (m + 1) + 1) tenLeafSeed =
      wrapLeftHNF (tlsExplicitCtx m) (counterD (m + 1) (m + 1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have harith : (2 * (m + 1) * (m + 1) - (m + 1) + 1) + (4 * (m + 1) + 1) =
          2 * (m + 2) * (m + 2) - (m + 2) + 1 := by
        simp only [Nat.succ_mul, Nat.mul_succ, Nat.add_mul]
        omega
      rw [← harith, iterateLO_add _ (4 * (m + 1) + 1), ih]
      rw [iterateLO_add (4 * (m + 1)) 1,
          tls_partial_explicit (m + 1) (m + 1) m (Nat.le_refl _) (tlsExplicitCtx m)]
      have htake : (tlsCycleFrozen (m + 1) m).take (m + 1) = tlsCycleFrozen (m + 1) m := by
        have h0 := list_take_all (tlsCycleFrozen (m + 1) m)
        rwa [tlsCycleFrozen_length] at h0
      rw [htake, Nat.sub_self]
      have hs_zero : stepLO (counterD 0 (m + 1)) = some (counterD (m + 2) (m + 2)) := rfl
      simp only [iterateLO, stepLO_wrapLeftHNF _ hs_zero, tlsExplicitCtx]

theorem leftHNFExtraLeaves_take_cycle (k p : Nat) :
    ∀ r, r ≤ k →
      leftHNFExtraLeaves ((tlsCycleFrozen k p).take r) =
        r * (4 * p + 2 * k + 19 - r) := by
  induction k with
  | zero =>
      intro r hr
      have hr0 : r = 0 := by omega
      subst hr0
      simp [tlsCycleFrozen, leftHNFExtraLeaves]
  | succ k ih =>
      intro r hr
      cases r with
      | zero => simp [leftHNFExtraLeaves]
      | succ r =>
          have hr_le : r ≤ k := Nat.le_of_succ_le_succ hr
          simp only [tlsCycleFrozen, List.take, leftHNFExtraLeaves,
            leaves, leaves_numeralC, leaves_counterD, S]
          rw [ih r hr_le]
          let X := 4 * p + 2 * k + 19 - r
          have hm_eq : 4 * p + 2 * (k + 1) + 19 - (r + 1) = X + 1 := by dsimp only [X]; omega
          have hmul1 : (r + 1) * (X + 1) = r * X + r + X + 1 := by
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
          rw [hm_eq, hmul1]
          dsimp only [X]
          omega

theorem three_mul_leftHNFExtraLeaves_tls (m : Nat) :
    3 * leftHNFExtraLeaves (tlsExplicitCtx m) = 5 * m ^ 3 + 30 * m ^ 2 + 25 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hfull : (tlsCycleFrozen (m + 1) m).take (m + 1) = tlsCycleFrozen (m + 1) m := by
        have h0 := list_take_all (tlsCycleFrozen (m + 1) m)
        rwa [tlsCycleFrozen_length] at h0
      have hc := leftHNFExtraLeaves_take_cycle (m + 1) m (m + 1) (Nat.le_refl _)
      rw [hfull] at hc
      have hlin : 4 * m + 2 * (m + 1) + 19 - (m + 1) = 5 * m + 20 := by omega
      rw [hlin] at hc
      have hc3 : (m + 1) ^ 3 = m ^ 3 + 3 * m ^ 2 + 3 * m + 1 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.add_mul,
          Nat.succ_mul, Nat.mul_succ, Nat.zero_mul, Nat.mul_assoc]
        omega
      have hc2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.add_mul,
          Nat.succ_mul, Nat.mul_succ, Nat.zero_mul]
        omega
      have hquad : (m + 1) * (5 * m + 20) = 5 * m ^ 2 + 25 * m + 20 := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.pow_succ, Nat.pow_zero,
          Nat.succ_mul, Nat.mul_succ, Nat.zero_mul]
        omega
      rw [tlsExplicitCtx, leftHNFExtraLeaves_append, Nat.mul_add, ih, hc, hquad, hc3, hc2]
      omega

/-- Exact cubic leaf count of `tenLeafSeed` in cycle `N = m + 1` (`N ≥ 1`) at intra-cycle step `d ≤ 4 * N`. -/
def tlsFormulaAt (N d : Nat) : Nat :=
  let r := d / 4
  (5 * N ^ 3 + 15 * N ^ 2 - 8 * N + 33) / 3 +
    r * (6 * N + 13 - r) +
    (if d % 4 = 0 then 0 else 2 * N + 4)

theorem tenLeafSeed_leaves_in_cycle (m d : Nat) (hd : d ≤ 4 * (m + 1)) :
    let N := m + 1
    leaves (iterateLO ((2 * N * N - N + 1) + d) tenLeafSeed) = tlsFormulaAt N d := by
  intro N
  let r := d / 4
  let rem := d % 4
  have hd_eq : d = 4 * r + rem := by omega
  have hr_le : r ≤ m + 1 := by omega
  have hrem_lt : rem < 4 := by omega
  have hit : iterateLO ((2 * N * N - N + 1) + d) tenLeafSeed =
      iterateLO rem (wrapLeftHNF (tlsExplicitCtx m ++ (tlsCycleFrozen (m + 1) m).take r)
        (counterD (m + 1 - r) (m + 1))) := by
    dsimp only [N]
    rw [hd_eq, ← Nat.add_assoc, iterateLO_add _ rem, iterateLO_add _ (4 * r),
        tls_explicit_checkpoint m, tls_partial_explicit r (m + 1) m hr_le (tlsExplicitCtx m)]
  rw [hit]
  let ctxR := tlsExplicitCtx m ++ (tlsCycleFrozen (m + 1) m).take r
  have h3 := three_mul_leftHNFExtraLeaves_tls m
  have hc3 : N ^ 3 = m ^ 3 + 3 * m ^ 2 + 3 * m + 1 := by
    dsimp only [N]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.add_mul,
      Nat.succ_mul, Nat.mul_succ, Nat.zero_mul, Nat.mul_assoc]
    omega
  have hc2 : N ^ 2 = m ^ 2 + 2 * m + 1 := by
    dsimp only [N]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.add_mul,
      Nat.succ_mul, Nat.mul_succ, Nat.zero_mul]
    omega
  have hbase_id : 3 * (leftHNFExtraLeaves (tlsExplicitCtx m) + (4 * (m + 1) + 11)) =
      5 * N ^ 3 + 15 * N ^ 2 - 8 * N + 33 := by
    rw [Nat.mul_add, h3, hc3, hc2]
    dsimp only [N]
    omega
  have hbase_eq : leftHNFExtraLeaves (tlsExplicitCtx m) + (4 * (m + 1) + 11) =
      (5 * N ^ 3 + 15 * N ^ 2 - 8 * N + 33) / 3 := by
    have hdiv := congrArg (· / 3) hbase_id
    rw [Nat.mul_div_right _ (by decide : 0 < 3)] at hdiv
    exact hdiv
  have htake_l := leftHNFExtraLeaves_take_cycle (m + 1) m r hr_le
  have hr_term : r * (4 * m + 2 * (m + 1) + 19 - r) = r * ((6 * N + 13 - r) + 2) := by
    have h1 : 4 * m + 2 * (m + 1) + 19 - r = (6 * N + 13 - r) + 2 := by
      dsimp only [N]; omega
    rw [h1]
  rw [hr_term, Nat.mul_add] at htake_l
  have hrem_cases : rem = 0 ∨ rem = 1 ∨ rem = 2 ∨ rem = 3 := by omega
  rcases hrem_cases with hrem_val | hrem_val | hrem_val | hrem_val
  · have hmod0 : d % 4 = 0 := hrem_val
    unfold tlsFormulaAt
    rw [hrem_val, hmod0, ← hbase_eq]
    clear hit h3 hc3 hc2 hbase_id hbase_eq
    simp only [iterateLO, leaves_wrapLeftHNF, leftHNFExtraLeaves_append,
      htake_l, leaves_counterD, ↓reduceIte]
    dsimp only [N, r] at *
    omega
  · have hr_lt : r ≤ m := by omega
    let k := m - r
    have hsub_eq : m + 1 - r = k + 1 := by omega
    rw [hrem_val, hsub_eq]
    have hs0 : stepLO (counterD (k + 1) (m + 1)) =
        some (((S ⋅ numeralC (m + 1)) ⋅ (numeralC k ⋅ numeralC (m + 1))) ⋅ S) := rfl
    have hstep1 : iterateLO 1 (wrapLeftHNF ctxR (counterD (k + 1) (m + 1))) =
        wrapLeftHNF ctxR (((S ⋅ numeralC (m + 1)) ⋅ (numeralC k ⋅ numeralC (m + 1))) ⋅ S) := by
      simp only [iterateLO, stepLO_wrapLeftHNF ctxR hs0]
    change leaves (iterateLO 1 (wrapLeftHNF ctxR (counterD (k + 1) (m + 1)))) = tlsFormulaAt N d
    rw [hstep1]
    have hmod_ne : d % 4 ≠ 0 := by omega
    unfold tlsFormulaAt
    rw [if_neg hmod_ne, ← hbase_eq]
    dsimp only [ctxR]
    clear hit hstep1 hs0 h3 hc3 hc2 hbase_id hbase_eq
    simp only [leaves_wrapLeftHNF, leftHNFExtraLeaves_append, htake_l, leaves, leaves_numeralC, S]
    dsimp only [N, r, k] at *
    omega
  · have hr_lt : r ≤ m := by omega
    let k := m - r
    have hsub_eq : m + 1 - r = k + 1 := by omega
    rw [hrem_val, hsub_eq]
    have hs0 : stepLO (counterD (k + 1) (m + 1)) =
        some (((S ⋅ numeralC (m + 1)) ⋅ (numeralC k ⋅ numeralC (m + 1))) ⋅ S) := rfl
    have hs1 : stepLO (((S ⋅ numeralC (m + 1)) ⋅ (numeralC k ⋅ numeralC (m + 1))) ⋅ S) =
        some ((numeralC (m + 1) ⋅ S) ⋅ counterD k (m + 1)) := rfl
    have hstep2 : iterateLO 2 (wrapLeftHNF ctxR (counterD (k + 1) (m + 1))) =
        wrapLeftHNF ctxR ((numeralC (m + 1) ⋅ S) ⋅ counterD k (m + 1)) := by
      simp only [iterateLO, stepLO_wrapLeftHNF ctxR hs0, stepLO_wrapLeftHNF ctxR hs1]
    change leaves (iterateLO 2 (wrapLeftHNF ctxR (counterD (k + 1) (m + 1)))) = tlsFormulaAt N d
    rw [hstep2]
    have hmod_ne : d % 4 ≠ 0 := by omega
    unfold tlsFormulaAt
    rw [if_neg hmod_ne, ← hbase_eq]
    dsimp only [ctxR]
    clear hit hstep2 hs0 hs1 h3 hc3 hc2 hbase_id hbase_eq
    simp only [leaves_wrapLeftHNF, leftHNFExtraLeaves_append, htake_l, leaves, leaves_numeralC, leaves_counterD, S]
    dsimp only [N, r, k] at *
    omega
  · have hr_lt : r ≤ m := by omega
    let k := m - r
    have hsub_eq : m + 1 - r = k + 1 := by omega
    rw [hrem_val, hsub_eq]
    have hs0 : stepLO (counterD (k + 1) (m + 1)) =
        some (((S ⋅ numeralC (m + 1)) ⋅ (numeralC k ⋅ numeralC (m + 1))) ⋅ S) := rfl
    have hs1 : stepLO (((S ⋅ numeralC (m + 1)) ⋅ (numeralC k ⋅ numeralC (m + 1))) ⋅ S) =
        some ((numeralC (m + 1) ⋅ S) ⋅ counterD k (m + 1)) := rfl
    have hs2 : stepLO ((numeralC (m + 1) ⋅ S) ⋅ counterD k (m + 1)) =
        some ((S ⋅ S ⋅ (numeralC m ⋅ S)) ⋅ counterD k (m + 1)) := rfl
    have hstep3 : iterateLO 3 (wrapLeftHNF ctxR (counterD (k + 1) (m + 1))) =
        wrapLeftHNF ctxR ((S ⋅ S ⋅ (numeralC m ⋅ S)) ⋅ counterD k (m + 1)) := by
      simp only [iterateLO, stepLO_wrapLeftHNF ctxR hs0, stepLO_wrapLeftHNF ctxR hs1,
        stepLO_wrapLeftHNF ctxR hs2]
    change leaves (iterateLO 3 (wrapLeftHNF ctxR (counterD (k + 1) (m + 1)))) = tlsFormulaAt N d
    rw [hstep3]
    have hmod_ne : d % 4 ≠ 0 := by omega
    unfold tlsFormulaAt
    rw [if_neg hmod_ne, ← hbase_eq]
    dsimp only [ctxR]
    clear hit hstep3 hs0 hs1 hs2 h3 hc3 hc2 hbase_id hbase_eq
    simp only [leaves_wrapLeftHNF, leftHNFExtraLeaves_append, htake_l, leaves, leaves_numeralC, leaves_counterD, S]
    dsimp only [N, r, k] at *
    omega

def tlsDecodePost2Aux : Nat → Nat × Nat
  | 0 => (0, 0)
  | rem + 1 =>
      let sub := tlsDecodePost2Aux rem
      if sub.2 < 4 * (sub.1 + 1) then (sub.1, sub.2 + 1)
      else (sub.1 + 1, 0)

theorem tlsDecodePost2Aux_spec (x : Nat) :
    let p := tlsDecodePost2Aux x
    let N := p.1 + 1
    (2 * N * N - N + 1) + p.2 = x + 2 ∧ p.2 ≤ 4 * N := by
  dsimp only []
  induction x with
  | zero => exact ⟨rfl, Nat.zero_le 4⟩
  | succ x ih =>
      simp only [tlsDecodePost2Aux]
      rcases hd : tlsDecodePost2Aux x with ⟨m, d⟩
      rw [hd] at ih
      dsimp only [] at ih ⊢
      if hlt : d < 4 * (m + 1) then
        rw [if_pos hlt]
        dsimp only []
        exact ⟨by omega, by omega⟩
      else
        rw [if_neg hlt]
        dsimp only []
        have hstep_arith :
            2 * (m + 1 + 1) * (m + 1 + 1) - (m + 1 + 1) + 1 =
            (2 * (m + 1) * (m + 1) - (m + 1) + 1) + (4 * (m + 1) + 1) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
          omega
        exact ⟨by omega, Nat.zero_le _⟩

def tenLeafSeedClosedFormLeaves (t : Nat) : Nat :=
  match t with
  | 0 => 10
  | 1 => 11
  | x + 2 =>
      let (m, d) := tlsDecodePost2Aux x
      tlsFormulaAt (m + 1) d

/-- **All-Step Exact Cubic Leaf-Count Jump-Ahead Theorem for `tenLeafSeed = R_PF ⋅ S`**:
    Explicitly determines `leaves (iterateLO t tenLeafSeed)` for **every** `t : Nat`! -/
theorem tenLeafSeed_all_step_exact_leaves (t : Nat) :
    leaves (iterateLO t tenLeafSeed) = tenLeafSeedClosedFormLeaves t := by
  match t with
  | 0 => rfl
  | 1 => rfl
  | x + 2 =>
      have ⟨heq, hle⟩ := tlsDecodePost2Aux_spec x
      unfold tenLeafSeedClosedFormLeaves
      conv => lhs; rw [← heq]
      exact tenLeafSeed_leaves_in_cycle (tlsDecodePost2Aux x).1 (tlsDecodePost2Aux x).2 hle


/-! ## Section 2: Multiway & `→_{lo}` Grammar `GA` on `AAA = (S S S)(S S S)(S S S)` -/

/-- Exact 3-constructor closed inductive grammar `GA` invariant under **all** multiway steps from `AAA`. -/
inductive GA : Term → Prop where
  | a_comb : GA A_comb
  | s1 {u : Term} : GA u → GA (S ⋅ u)
  | app {u v : Term} : GA u → GA v → GA (u ⋅ v)

theorem ga_aaa : GA AAA :=
  .app (.app .a_comb .a_comb) .a_comb

theorem ga_closed_and_ge3 {t : Term} (h : GA t) : noVars t = true ∧ 3 ≤ leaves t := by
  induction h with
  | a_comb => exact ⟨rfl, Nat.le_refl 3⟩
  | s1 _ ih =>
      refine ⟨ih.1, ?_⟩
      simp only [leaves, S]
      omega
  | app _ _ ih1 ih2 =>
      refine ⟨Bool.and_eq_true _ _ |>.mpr ⟨ih1.1, ih2.1⟩, ?_⟩
      simp only [leaves]
      omega

private theorem ga_not_s : ¬ GA S := by
  intro h; cases h

private theorem ga_s1_inv {u : Term} (h : GA (S ⋅ u)) : GA u := by
  generalize hw : (S ⋅ u) = w at h
  cases h with
  | a_comb => cases hw
  | s1 hu =>
      injection hw with _ hu_eq
      exact hu_eq ▸ hu
  | app hs _ =>
      injection hw with hs_eq _
      exact False.elim (ga_not_s (hs_eq ▸ hs))

private theorem ga_s2_inv {x y : Term} (h : GA (S ⋅ x ⋅ y)) :
    (x = S ∧ y = S) ∨ (GA x ∧ GA y) := by
  generalize hw : (S ⋅ x ⋅ y) = w at h
  cases h with
  | a_comb =>
      injection hw with h1 hy
      injection h1 with _ hx
      exact Or.inl ⟨hx, hy⟩
  | s1 _ => cases hw
  | app hsx hy =>
      injection hw with hsx_eq hy_eq
      exact Or.inr ⟨ga_s1_inv (hsx_eq ▸ hsx), hy_eq ▸ hy⟩

/-- **Multiway Closure & Strict `+2` Leaf Growth Lemma for `GA`**:
    Every single `S`-contraction `Step t t'` from any `t ∈ GA` (along **any** multiway branch!)
    stays inside `GA` AND strictly increases leaf count by **at least `+2`** (`leaves t + 2 ≤ leaves t'`)! -/
theorem ga_step_closed_and_plus2 {t t' : Term} (hg : GA t) (hs : Step t t') :
    GA t' ∧ leaves t + 2 ≤ leaves t' := by
  induction hs with
  | root x y z =>
      generalize hw : (S ⋅ x ⋅ y ⋅ z) = w at hg
      cases hg with
      | a_comb => cases hw
      | s1 _ => cases hw
      | app hsxy hz =>
          injection hw with hsxy_eq hz_eq
          subst hsxy_eq; subst hz_eq
          have hzl := (ga_closed_and_ge3 hz).2
          rcases ga_s2_inv hsxy with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
          · refine ⟨.app (.s1 hz) (.s1 hz), ?_⟩
            simp only [leaves, S]
            omega
          · refine ⟨.app (.app hx hz) (.app hy hz), ?_⟩
            simp only [leaves, S]
            omega
  | @left a a' b hsa ih =>
      generalize hw : (a ⋅ b) = w at hg
      cases hg with
      | a_comb =>
          injection hw with ha _
          subst ha
          cases hsa with
          | left hss => cases hss
          | right hss => cases hss
      | s1 _ =>
          injection hw with ha _
          subst ha
          cases hsa
      | app ha hb =>
          injection hw with ha_eq hb_eq
          subst ha_eq; subst hb_eq
          obtain ⟨ha', hl⟩ := ih ha
          refine ⟨.app ha' hb, ?_⟩
          simp only [leaves]
          omega
  | @right a b b' hsb ih =>
      generalize hw : (a ⋅ b) = w at hg
      cases hg with
      | a_comb =>
          injection hw with _ hb
          subst hb
          cases hsb
      | s1 hb =>
          injection hw with ha_eq hb_eq
          subst ha_eq; subst hb_eq
          obtain ⟨hb', hl⟩ := ih hb
          refine ⟨.s1 hb', ?_⟩
          simp only [leaves, S]
          omega
      | app ha hb =>
          injection hw with ha_eq hb_eq
          subst ha_eq; subst hb_eq
          obtain ⟨hb', hl⟩ := ih hb
          refine ⟨.app ha hb', ?_⟩
          simp only [leaves]
          omega

theorem ga_reduces {t t' : Term} (hr : Reduces t t') (hg : GA t) : GA t' := by
  induction hr with
  | refl _ => exact hg
  | next hs _ ih => exact ih (ga_step_closed_and_plus2 hg hs).1

/-- Subterm occurrence check `hasSubterm pat t = true` iff `pat` occurs anywhere in `t`. -/
def hasSubterm (pat : Term) : Term → Bool
  | .s => decide (pat = .s)
  | .var k => decide (pat = .var k)
  | .app a b => decide (pat = .app a b) || hasSubterm pat a || hasSubterm pat b

theorem ga_ne_b_comb {t : Term} (hg : GA t) : t ≠ B_comb := by
  intro heq
  have hge := (ga_closed_and_ge3 hg).2
  rw [heq] at hge
  exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hge))

theorem ga_no_subterm_s_bcomb {t : Term} (hg : GA t) :
    hasSubterm (S ⋅ B_comb) t = false := by
  induction hg with
  | a_comb => rfl
  | @s1 u hu ih =>
      have hne_top : (S ⋅ B_comb = S ⋅ u) ↔ False := by
        constructor
        · intro heq
          injection heq with _ hbu
          exact ga_ne_b_comb hu hbu.symm
        · intro hf; cases hf
      unfold hasSubterm
      rw [decide_eq_false (fun h => hne_top.mp h), ih]
      rfl
  | @app u v hu hv ihu ihv =>
      have hne_top : (S ⋅ B_comb = u ⋅ v) ↔ False := by
        constructor
        · intro heq
          injection heq with hsu _
          exact ga_not_s (hsu ▸ hu)
        · intro hf; cases hf
      unfold hasSubterm
      rw [decide_eq_false (fun h => hne_top.mp h), ihu, ihv]
      rfl

/-- **Master `AAA` Dynamics & Multiway Subterm Exclusion Theorem**:
    1. `AAA` is immediately head-divergent (`evalHN AAA = .hn34`), so `stepLO` performs pure head
       reduction (`HeadStepsN k AAA (iterateLO k AAA)`) forever with zero frozen HNF frames.
    2. At **every** step `k : Nat`, `leaves` grows strictly by **at least `+2`**:
       `leaves (iterateLO k AAA) + 2 ≤ leaves (iterateLO (k + 1) AAA)`, so `9 + 2 * k ≤ leaves (iterateLO k AAA)`.
    3. Across the **entire infinite multiway graph** `{ T | Reduces AAA T }`, the 3-leaf normal form
       `S ⋅ B_comb = S(SS)` **never** appears as a subterm (`hasSubterm (S ⋅ B_comb) T = false`)! -/
theorem aaa_lo_and_multiway_master :
    evalSN AAA = .sn38 ∧
    evalHN AAA = .hn34 ∧
    evalP AAA = .p37 ∧
    (∀ k : Nat,
      GA (iterateLO k AAA) ∧
      HeadStepsN k AAA (iterateLO k AAA) ∧
      leaves (iterateLO k AAA) + 2 ≤ leaves (iterateLO (k + 1) AAA) ∧
      9 + 2 * k ≤ leaves (iterateLO k AAA)) ∧
    (∀ T : Term, Reduces AAA T → GA T ∧ hasSubterm (S ⋅ B_comb) T = false) := by
  have hlock := locked_hn34_forever (ctx := []) (foc := AAA) rfl rfl rfl
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro k
    -- Clean proof using `iterateLO_add k 1`!
    have hga_k : GA (iterateLO k AAA) := ga_reduces (reduces_iterateLO k AAA) ga_aaa
    have hsome := (hlock k).2.2.2.2.2
    change (stepLO (iterateLO k AAA)).isSome = true at hsome
    have hplus2_k : leaves (iterateLO k AAA) + 2 ≤ leaves (iterateLO (k + 1) AAA) := by
      rw [iterateLO_add k 1]
      cases hs : stepLO (iterateLO k AAA) with
      | none => rw [hs] at hsome; cases hsome
      | some nxt =>
          simp only [iterateLO, hs]
          exact (ga_step_closed_and_plus2 hga_k (stepLO_some_step hs)).2
    have hbound : ∀ m : Nat, 9 + 2 * m ≤ leaves (iterateLO m AAA) := by
      intro m
      induction m with
      | zero => exact Nat.le_refl 9
      | succ m ihm =>
          have hga_m := ga_reduces (reduces_iterateLO m AAA) ga_aaa
          have hsm := (hlock m).2.2.2.2.2
          change (stepLO (iterateLO m AAA)).isSome = true at hsm
          have hp2 : leaves (iterateLO m AAA) + 2 ≤ leaves (iterateLO (m + 1) AAA) := by
            rw [iterateLO_add m 1]
            cases hs : stepLO (iterateLO m AAA) with
            | none => rw [hs] at hsm; cases hsm
            | some nxt =>
                simp only [iterateLO, hs]
                exact (ga_step_closed_and_plus2 hga_m (stepLO_some_step hs)).2
          omega
    exact ⟨hga_k, (hlock k).2.2.2.2.1, hplus2_k, hbound k⟩
  · intro T hred
    have hgT := ga_reduces hred ga_aaa
    exact ⟨hgT, ga_no_subterm_s_bcomb hgT⟩


/-! ## Section 3: Complete Garden-of-Eden Normal-Form Characterization & Decidability -/

/-- A pure-`S` term `p` is **Garden-of-Eden** (`IsGardenOfEden p`) iff **no** closed pure-`S` term `m`
    reduces in `1` or more steps to `p` (in-degree `0` in the closed pure-`S` multiway graph). -/
def IsGardenOfEden (p : Term) : Prop :=
  ∀ m : Term, noVars m = true → ¬ StepPlus m p

private theorem leaves_pos_pure : ∀ t : Term, 1 ≤ leaves t
  | .s => Nat.le_refl 1
  | .var _ => Nat.le_refl 1
  | .app a b => Nat.le_trans (leaves_pos_pure a) (Nat.le_add_right _ (leaves b))

theorem step_leaves_ge_4 {a b : Term} (hs : Step a b) : 4 ≤ leaves a ∧ 4 ≤ leaves b := by
  induction hs with
  | root x y z =>
      have hx := leaves_pos_pure x
      have hy := leaves_pos_pure y
      have hz := leaves_pos_pure z
      refine ⟨?_, ?_⟩
      · show 4 ≤ ((1 + leaves x) + leaves y) + leaves z
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl 1) hx) hy) hz
      · show 4 ≤ (leaves x + leaves z) + (leaves y + leaves z)
        exact Nat.add_le_add (Nat.add_le_add hx hz) (Nat.add_le_add hy hz)
  | @left l l' r _ ih =>
      exact ⟨Nat.le_trans ih.1 (Nat.le_add_right _ (leaves r)),
             Nat.le_trans ih.2 (Nat.le_add_right _ (leaves r))⟩
  | @right l r r' _ ih =>
      exact ⟨Nat.le_trans ih.1 (Nat.le_add_left _ (leaves l)),
             Nat.le_trans ih.2 (Nat.le_add_left _ (leaves l))⟩

theorem stepPlus_leaves_ge_4 {a b : Term} (h : StepPlus a b) : 4 ≤ leaves a ∧ 4 ≤ leaves b := by
  induction h with
  | single hs => exact step_leaves_ge_4 hs
  | head hs _ ih =>
      have h1 := step_leaves_ge_4 hs
      exact ⟨h1.1, ih.2⟩

/-- Every term of leaf count `≤ 3` (`S`, `S S`, `S(SS)`, `S S S`) has in-degree `0` in `CL(S)`! -/
theorem goe_of_leaves_le_3 {p : Term} (hle : leaves p ≤ 3) : IsGardenOfEden p := by
  intro m _ hsp
  have hge := (stepPlus_leaves_ge_4 hsp).2
  exact Nat.not_lt.mpr (Nat.le_trans hge hle) (by decide)

theorem step_to_s1_inv {m u1 : Term} (hs : Step m (S ⋅ u1)) :
    ∃ u0, m = S ⋅ u0 ∧ Step u0 u1 := by
  generalize hw : (S ⋅ u1) = w at hs
  cases hs with
  | root _ _ _ => cases hw
  | @left _ _ _ hsa =>
      injection hw with ha' _
      have h4 := (step_leaves_ge_4 hsa).2
      rw [← ha'] at h4
      exact False.elim (Nat.not_lt.mpr h4 (by decide))
  | @right _ u0 _ hsu =>
      injection hw with ha hb'
      subst ha; subst hb'
      exact ⟨u0, rfl, hsu⟩

theorem step_from_s1_inv {u b : Term} (hs : Step (S ⋅ u) b) :
    ∃ u1, b = S ⋅ u1 ∧ Step u u1 := by
  generalize hw : (S ⋅ u) = w at hs
  cases hs with
  | root _ _ _ => cases hw
  | @left _ _ _ hsa =>
      injection hw with ha _
      subst ha
      cases hsa
  | @right _ _ r' hsr =>
      injection hw with ha hr
      subst ha; subst hr
      exact ⟨r', rfl, hsr⟩

theorem reduces_to_s1_inv {m u : Term} (hr : Reduces m (S ⋅ u)) :
    ∃ u0, m = S ⋅ u0 ∧ Reduces u0 u := by
  generalize htarget : S ⋅ u = tgt at hr
  induction hr generalizing u with
  | refl _ =>
      subst htarget
      exact ⟨u, rfl, Reduces.refl u⟩
  | @next a b _ hs _ ih =>
      obtain ⟨u1, hb_eq, hu1_u⟩ := ih htarget
      subst hb_eq
      obtain ⟨u0, rfl, hs0⟩ := step_to_s1_inv hs
      exact ⟨u0, rfl, Reduces.next hs0 hu1_u⟩

theorem goe_s1_iff {u : Term} :
    IsGardenOfEden (S ⋅ u) ↔ IsGardenOfEden u := by
  constructor
  · intro hgoe m hvm hsp
    exact hgoe (S ⋅ m) hvm (stepPlus_right S hsp)
  · intro hgoe m hvm hsp
    obtain ⟨u0, rfl, hred⟩ := reduces_to_s1_inv (reduces_of_stepPlus hsp)
    have hvu0 : noVars u0 = true := hvm
    rcases reduces_eq_or_stepPlus hred with heq_u | hsp_u
    · subst heq_u
      cases hsp with
      | single hs =>
          obtain ⟨_, heq, hsu⟩ := step_to_s1_inv hs
          injection heq with _ hu0
          subst hu0
          exact hgoe u0 hvu0 (.single hsu)
      | @head _ b _ hs hrest =>
          obtain ⟨u1, rfl, hsu1⟩ := step_from_s1_inv hs
          obtain ⟨u2, heq2, hred2⟩ := reduces_to_s1_inv (reduces_of_stepPlus hrest)
          injection heq2 with _ hu12
          subst hu12
          exact hgoe u0 hvu0 (stepPlus_of_step_reduces hsu1 hred2)
    · exact hgoe u0 hvu0 hsp_u

/-- Key backward decomposition of `Reduces m (S ⋅ u ⋅ v)`:
    EITHER no root contraction occurs (`m = a ⋅ b` with `Reduces a (S ⋅ u)` and `Reduces b v`),
    OR some root contraction occurs (`∃ x y z, Reduces m (S ⋅ x ⋅ y ⋅ z) ∧ x = S ∧ Reduces z u ∧ Reduces (y ⋅ z) v`). -/
theorem reduces_to_s2_decomp {m u v : Term} (hr : Reduces m (S ⋅ u ⋅ v)) :
    (∃ u0 v0, m = S ⋅ u0 ⋅ v0 ∧ Reduces u0 u ∧ Reduces v0 v) ∨
    (∃ y z, Reduces m (S ⋅ S ⋅ y ⋅ z) ∧ Reduces z u ∧ Reduces (y ⋅ z) v) := by
  generalize htarget : (S ⋅ u ⋅ v) = tgt at hr
  induction hr generalizing u v with
  | refl _ =>
      subst htarget
      exact Or.inl ⟨u, v, rfl, Reduces.refl u, Reduces.refl v⟩
  | @next a b _ hs _ ih =>
      rcases ih htarget with ⟨u1, v1, hb_eq, hu1, hv1⟩ | ⟨y, z, hbm, hzu, hyzv⟩
      · generalize hw : b = b0 at hs
        rw [hb_eq] at hw
        cases hs with
        | root x y z =>
            injection hw with hxz hyv
            injection hxz with hx hz
            subst hx; subst hz; subst hyv
            exact Or.inr ⟨y, u1, Reduces.refl _, hu1, hv1⟩
        | @left l _ _ hsl =>
            injection hw with hl' hr'
            subst hl'; subst hr'
            obtain ⟨u0, rfl, hsu0⟩ := step_to_s1_inv hsl
            exact Or.inl ⟨u0, v1, rfl, Reduces.next hsu0 hu1, hv1⟩
        | @right _ v0 _ hsv =>
            injection hw with hl' hr'
            subst hl'; subst hr'
            exact Or.inl ⟨u1, v0, rfl, hu1, Reduces.next hsv hv1⟩
      · exact Or.inr ⟨y, z, Reduces.next hs hbm, hzu, hyzv⟩

theorem closed_irrefl_stepPlus {u : Term} (hsp : StepPlus u u) (hnf : IsNormalForm u) : False := by
  cases hsp with
  | single hs => exact hnf u hs
  | head hs _ => exact hnf _ hs

/-- **Exact Structural Characterization of Garden-of-Eden Closed Normal Forms `S ⋅ u ⋅ v`**:
    For closed Normal Forms `u` and `v`, `S ⋅ u ⋅ v` is Garden-of-Eden **if and only if**:
    1. `u` is Garden-of-Eden,
    2. `v` is Garden-of-Eden, and
    3. there exists **no** closed Normal Form `y0` with `leaves y0 + leaves u ≤ leaves v`
       and `Reduces (y0 ⋅ u) v`. -/
theorem goe_s2_iff {u v : Term}
    (hvu : noVars u = true) (hvv : noVars v = true)
    (hnfu : IsNormalForm u) (hnfv : IsNormalForm v) :
    IsGardenOfEden (S ⋅ u ⋅ v) ↔
      IsGardenOfEden u ∧
      IsGardenOfEden v ∧
      ¬ ∃ y0 : Term, noVars y0 = true ∧ IsNormalForm y0 ∧
          leaves y0 + leaves u ≤ leaves v ∧ Reduces (y0 ⋅ u) v := by
  constructor
  · intro hgoe
    refine ⟨?_, ?_, ?_⟩
    · intro m hvm hsp
      have hv_all : noVars (S ⋅ m ⋅ v) = true := Bool.and_eq_true _ _ |>.mpr ⟨hvm, hvv⟩
      exact hgoe (S ⋅ m ⋅ v) hv_all (stepPlus_left (stepPlus_right S hsp) v)
    · intro m hvm hsp
      have hv_all : noVars (S ⋅ u ⋅ m) = true := Bool.and_eq_true _ _ |>.mpr ⟨hvu, hvm⟩
      exact hgoe (S ⋅ u ⋅ m) hv_all (stepPlus_right (S ⋅ u) hsp)
    · rintro ⟨y0, hvy0, _, _, hred⟩
      let m := S ⋅ S ⋅ y0 ⋅ u
      have hvm : noVars m = true := Bool.and_eq_true _ _ |>.mpr ⟨hvy0, hvu⟩
      have hsp : StepPlus m (S ⋅ u ⋅ v) :=
        stepPlus_of_step_reduces (Step.root S y0 u) (reduces_right (S ⋅ u) hred)
      exact hgoe m hvm hsp
  · rintro ⟨hgu, hgv, hnoy⟩ m hvm hsp
    have hnfp : IsNormalForm (S ⋅ u ⋅ v) := by
      intro w hw
      cases hw with
      | left hl =>
          cases hl with
          | left hll => cases hll
          | right hlr => exact hnfu _ hlr
      | right hr => exact hnfv _ hr
    rcases reduces_to_s2_decomp (reduces_of_stepPlus hsp) with
      ⟨u0, v0, rfl, hru, hrv⟩ | ⟨y, z, hm_red, hzu, hyzv⟩
    · have hvu0 : noVars u0 = true := ((Bool.and_eq_true _ _).mp hvm).1
      have hvv0 : noVars v0 = true := ((Bool.and_eq_true _ _).mp hvm).2
      rcases reduces_eq_or_stepPlus hru with rfl | hspu
      · rcases reduces_eq_or_stepPlus hrv with rfl | hspv
        · exact closed_irrefl_stepPlus hsp hnfp
        · exact hgv v0 hvv0 hspv
      · exact hgu u0 hvu0 hspu
    · have hv_root := noVars_reduces hm_red hvm
      have hv_sy : noVars (S ⋅ S ⋅ y) = true := ((Bool.and_eq_true _ _).mp hv_root).1
      have hvy : noVars y = true := ((Bool.and_eq_true _ _).mp hv_sy).2
      -- `y ⋅ z →* v` and `IsNormalForm v`, so `y ⋅ z` is WN, hence SN (`wn_implies_sn`), so `y` is SN!
      have hsn_yz : StrongNormalizing (y ⋅ z) := wn_implies_sn ⟨v, hyzv, hnfv⟩
      have hsn_y : StrongNormalizing y := by
        -- Lift `Acc` from `y ⋅ z` to `y` via `Step.left`!
        have hlift : ∀ w, StrongNormalizing w → ∀ y1, w = y1 ⋅ z → StrongNormalizing y1 := by
          intro w hw
          induction hw with
          | intro w _ ih =>
              intro y1 heq
              subst heq
              exact Acc.intro y1 (fun y2 hy => ih (y2 ⋅ z) (Step.left hy) y2 rfl)
        exact hlift (y ⋅ z) hsn_yz y rfl
      obtain ⟨m, hm_none⟩ :=
        (decideHaltsLO_iff_halts hvy).2.2.1.mp ((decideHaltsLO_iff_halts hvy).1.mpr hsn_y)
      let y0 := iterateLO m y
      have hy_red : Reduces y y0 := reduces_iterateLO m y
      have hy0_nf : IsNormalForm y0 := stepLO_none_isNormalForm hm_none
      have hvy0 : noVars y0 = true := noVars_reduces hy_red hvy
      have hyz_to_y0u : Reduces (y ⋅ z) (y0 ⋅ u) := reduces_app hy_red hzu
      obtain ⟨common, hc1, hc2⟩ := church_rosser hyz_to_y0u hyzv
      have hveq : v = common := isNormalForm_reduces_eq hnfv hc2
      subst hveq
      have hleaves_le : leaves y0 + leaves u ≤ leaves v :=
        leaves_mono_reduces hc1
      exact hnoy ⟨y0, hvy0, hy0_nf, hleaves_le, hc1⟩

/-- **Infinite Constructive Garden-of-Eden Tower Theorem**:
    Whenever `u` and `v` are closed Garden-of-Eden Normal Forms with `leaves v ≤ leaves u`,
    `S ⋅ u ⋅ v` is **unconditionally** Garden-of-Eden! -/
theorem goe_s2_of_leaves_le {u v : Term}
    (hvu : noVars u = true) (hvv : noVars v = true)
    (hnfu : IsNormalForm u) (hnfv : IsNormalForm v)
    (hgu : IsGardenOfEden u) (hgv : IsGardenOfEden v)
    (hle : leaves v ≤ leaves u) :
    IsGardenOfEden (S ⋅ u ⋅ v) := by
  rw [goe_s2_iff hvu hvv hnfu hnfv]
  refine ⟨hgu, hgv, ?_⟩
  rintro ⟨y0, _, _, hy_le, _⟩
  have hy_pos := leaves_pos_pure y0
  have hlt : leaves u < leaves y0 + leaves u :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (leaves u))
      (by rw [Nat.add_comm (leaves y0) (leaves u)]; exact Nat.add_le_add_left hy_pos (leaves u))
  exact Nat.not_lt.mpr (Nat.le_trans hy_le hle) hlt

/-- All closed trees of size `1 ≤ k ≤ maxSz`. -/
def closedTreesUpTo : Nat → List Term
  | 0 => []
  | k + 1 => closedTreesUpTo k ++ closedTreesOfSize (k + 1)

private theorem mem_append_left {α : Type} {x : α} {as : List α} (bs : List α) (h : x ∈ as) :
    x ∈ as ++ bs := by
  induction as with
  | nil => cases h
  | cons a rest ih =>
      cases h with
      | head _ => exact List.Mem.head _
      | tail _ hr => exact List.Mem.tail _ (ih hr)

private theorem mem_append_right {α : Type} {x : α} (as : List α) {bs : List α} (h : x ∈ bs) :
    x ∈ as ++ bs := by
  induction as with
  | nil => exact h
  | cons _ _ ih => exact List.Mem.tail _ ih

private theorem mem_append_elim {α : Type} {x : α} {as bs : List α} (h : x ∈ as ++ bs) :
    x ∈ as ∨ x ∈ bs := by
  induction as with
  | nil => exact Or.inr h
  | cons a rest ih =>
      cases h with
      | head _ => exact Or.inl (List.Mem.head _)
      | tail _ hr =>
          rcases ih hr with h1 | h2
          · exact Or.inl (List.Mem.tail _ h1)
          · exact Or.inr h2

private theorem mem_map_elim {α β : Type} {f : α → β} {xs : List α} {y : β} (h : y ∈ xs.map f) :
    ∃ x ∈ xs, f x = y := by
  induction xs with
  | nil => cases h
  | cons a rest ih =>
      cases h with
      | head _ => exact ⟨a, List.Mem.head _, rfl⟩
      | tail _ hr =>
          obtain ⟨x, hx, hfx⟩ := ih hr
          exact ⟨x, List.Mem.tail _ hx, hfx⟩

theorem mem_closedTreesUpTo {t : Term} {B : Nat} (hv : noVars t = true) (hle : leaves t ≤ B) :
    t ∈ closedTreesUpTo B := by
  induction B with
  | zero =>
      have hp := leaves_pos_pure t
      exact False.elim (Nat.not_lt.mpr hle hp)
  | succ B ih =>
      if heq : leaves t = B + 1 then
        exact mem_append_right _ (heq ▸ mem_closedTreesOfSize hv)
      else
        have hlt : leaves t ≤ B := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hle heq)
        exact mem_append_left _ (ih hlt)

private def loReachesWFuel (recLF : Term → Term → Bool) : Nat → Term → Term → Bool
  | 0, u, v => decide (u = v)
  | wf + 1, u, v =>
      if u = v then true
      else match stepLO u with
        | none => false
        | some u' =>
            if leaves u' = leaves u then loReachesWFuel recLF wf u' v
            else if leaves u' ≤ leaves v then recLF u' v
            else false

private def loReachesFuel : Nat → Nat → Term → Term → Bool
  | 0, wf, u, v => loReachesWFuel (fun _ _ => false) wf u v
  | lf + 1, wf, u, v => loReachesWFuel (fun u' v' => loReachesFuel lf (bergstraWeight u') u' v') wf u v

/-- Constructive `Classical.choice`-free normal-form reachability check via deterministic `stepLO`. -/
def loReachesNFBool (u v : Term) : Bool :=
  loReachesFuel (leaves v - leaves u) (bergstraWeight u) u v

private theorem loReachesWFuel_sound {recLF : Term → Term → Bool}
    (hrec : ∀ u' v', recLF u' v' = true → Reduces u' v') :
    ∀ (wf : Nat) (u v : Term), loReachesWFuel recLF wf u v = true → Reduces u v
  | 0, u, v, h => of_decide_eq_true h ▸ Reduces.refl u
  | wf + 1, u, v, h => by
      unfold loReachesWFuel at h
      if heq : u = v then
        exact heq ▸ Reduces.refl u
      else
        rw [if_neg heq] at h
        cases hs : stepLO u with
        | none => rw [hs] at h; cases h
        | some u' =>
            rw [hs] at h
            dsimp only [] at h
            have hstep := stepLO_some_step hs
            if hle_eq : leaves u' = leaves u then
              rw [if_pos hle_eq] at h
              exact Reduces.next hstep (loReachesWFuel_sound hrec wf u' v h)
            else
              rw [if_neg hle_eq] at h
              if hle_v : leaves u' ≤ leaves v then
                rw [if_pos hle_v] at h
                exact Reduces.next hstep (hrec u' v h)
              else
                rw [if_neg hle_v] at h
                cases h

private theorem loReachesFuel_sound :
    ∀ (lf wf : Nat) (u v : Term), loReachesFuel lf wf u v = true → Reduces u v
  | 0, wf, u, v, h => loReachesWFuel_sound (fun _ _ hc => by cases hc) wf u v h
  | lf + 1, wf, u, v, h =>
      loReachesWFuel_sound (fun u' v' hc => loReachesFuel_sound lf (bergstraWeight u') u' v' hc) wf u v h

private theorem sub_lt_of_lt_le_local : ∀ {B a b : Nat}, a < b → b ≤ B → B - b < B - a
  | 0, _, _, h1, h2 => by cases Nat.eq_zero_of_le_zero h2; cases h1
  | B + 1, 0, b + 1, _, _ => by
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      exact Nat.lt_succ_of_le (Nat.sub_le B b)
  | B + 1, a + 1, b + 1, h1, h2 => by
      simp only [Nat.succ_sub_succ_eq_sub]
      exact sub_lt_of_lt_le_local (Nat.lt_of_succ_lt_succ h1) (Nat.le_of_succ_le_succ h2)

private theorem loReachesNFBool_iff {u v : Term} (hnfv : IsNormalForm v) :
    loReachesNFBool u v = true ↔ Reduces u v := by
  constructor
  · exact loReachesFuel_sound _ _ u v
  · intro hred
    have hsn : StrongNormalizing u := wn_implies_sn ⟨v, hred, hnfv⟩
    have hcomp : ∀ (x : Term), StrongNormalizing x →
        ∀ (lf wf : Nat), Reduces x v → leaves v - leaves x ≤ lf → bergstraWeight x ≤ wf →
          loReachesFuel lf wf x v = true := by
      intro x hx
      induction hx with
      | intro x _ ih =>
          intro lf wf hrx hlf hwf
          if heq : x = v then
            subst heq
            cases lf <;> cases wf <;> simp [loReachesFuel, loReachesWFuel]
          else
            have hw_pos : 1 ≤ wf := Nat.le_trans (bergstraWeight_pos x) hwf
            cases wf with
            | zero => cases hw_pos
            | succ wf' =>
                rcases reduces_eq_or_stepPlus hrx with rfl | hsp
                · exact False.elim (heq rfl)
                · cases hs : stepLO x with
                  | none =>
                      have hnfx := stepLO_none_isNormalForm hs
                      cases hsp with
                      | single h1 => exact False.elim (hnfx _ h1)
                      | head h1 _ => exact False.elim (hnfx _ h1)
                  | some x' =>
                      have hstep := stepLO_some_step hs
                      obtain ⟨common, hc1, hc2⟩ := church_rosser (Reduces.next hstep (.refl x')) hrx
                      have hveq : v = common := isNormalForm_reduces_eq hnfv hc2
                      have hrx' : Reduces x' v := hveq ▸ hc1
                      have hle_step : leaves x ≤ leaves x' := leaves_mono_step hstep
                      have hle_rest : leaves x' ≤ leaves v := leaves_mono_reduces hrx'
                      cases lf with
                      | zero =>
                          unfold loReachesFuel loReachesWFuel
                          rw [if_neg heq, hs]
                          dsimp only []
                          if hle_eq : leaves x' = leaves x then
                            rw [if_pos hle_eq]
                            have hw_drop := equal_leaves_strict_weight_drop hstep hle_eq.symm
                            exact ih x' hstep 0 wf' hrx' (by rw [hle_eq]; exact hlf)
                              (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw_drop hwf))
                          else
                            have hlt_step := Nat.lt_of_le_of_ne hle_step (Ne.symm hle_eq)
                            have hsub_lt := sub_lt_of_lt_le_local hlt_step hle_rest
                            exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hsub_lt hlf))
                      | succ lf' =>
                          unfold loReachesFuel loReachesWFuel
                          rw [if_neg heq, hs]
                          dsimp only []
                          if hle_eq : leaves x' = leaves x then
                            rw [if_pos hle_eq]
                            have hw_drop := equal_leaves_strict_weight_drop hstep hle_eq.symm
                            exact ih x' hstep (lf' + 1) wf' hrx' (by rw [hle_eq]; exact hlf)
                              (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw_drop hwf))
                          else
                            rw [if_neg hle_eq, if_pos hle_rest]
                            have hlt_step := Nat.lt_of_le_of_ne hle_step (Ne.symm hle_eq)
                            have hsub_lt := sub_lt_of_lt_le_local hlt_step hle_rest
                            exact ih x' hstep lf' (bergstraWeight x') hrx'
                              (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hsub_lt hlf)) (Nat.le_refl _)
    exact hcomp u hsn _ _ hred (Nat.le_refl _) (Nat.le_refl _)

/-- Total constructive Boolean decision procedure for Garden-of-Eden Normal Forms! -/
def decideGardenOfEdenNF : Term → Bool
  | .s => true
  | .var _ => false
  | .app .s u => decideGardenOfEdenNF u
  | .app (.app .s u) v =>
      decideGardenOfEdenNF u &&
      decideGardenOfEdenNF v &&
      !((closedTreesUpTo (leaves v - leaves u)).any (fun y0 =>
        (stepLO y0).isNone && loReachesNFBool (y0 ⋅ u) v))
  | _ => false

theorem closed_nf_shape {p : Term} (hv : noVars p = true) (hnf : IsNormalForm p) :
    p = S ∨ (∃ u, p = S ⋅ u ∧ noVars u = true ∧ IsNormalForm u) ∨
    (∃ u v, p = S ⋅ u ⋅ v ∧ noVars u = true ∧ noVars v = true ∧ IsNormalForm u ∧ IsNormalForm v) := by
  have hlo : stepLO p = none := by
    cases hs : stepLO p with
    | none => rfl
    | some p' => exact False.elim (hnf p' (stepLO_some_step hs))
  have hh : headStepOpt p = none := by
    cases hh0 : headStepOpt p with
    | none => rfl
    | some p' =>
        have hbad := headStepOpt_some_imp_stepLO hh0
        rw [hlo] at hbad; cases hbad
  rcases headStepOpt_none_closed hv hh with rfl | ⟨u, rfl⟩ | ⟨u, v, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨u, rfl, hv, fun u' hs => hnf (S ⋅ u') (Step.right hs)⟩)
  · have hvu : noVars u = true := ((Bool.and_eq_true _ _).mp hv).1
    have hvv : noVars v = true := ((Bool.and_eq_true _ _).mp hv).2
    exact Or.inr (Or.inr ⟨u, v, rfl, hvu, hvv,
      fun u' hs => hnf (S ⋅ u' ⋅ v) (Step.left (Step.right hs)),
      fun v' hs => hnf (S ⋅ u ⋅ v') (Step.right hs)⟩)

private theorem list_any_iff_mem {α : Type} (xs : List α) (f : α → Bool) :
    xs.any f = true ↔ ∃ x ∈ xs, f x = true := by
  induction xs with
  | nil =>
      constructor
      · intro h; cases h
      · rintro ⟨_, hm, _⟩; cases hm
  | cons a as ih =>
      simp only [List.any, Bool.or_eq_true]
      constructor
      · rintro (ha | has)
        · exact ⟨a, List.Mem.head _, ha⟩
        · obtain ⟨x, hx, hfx⟩ := ih.mp has
          exact ⟨x, List.Mem.tail _ hx, hfx⟩
      · rintro ⟨x, hm, hfx⟩
        cases hm with
        | head _ => exact Or.inl hfx
        | tail _ hx => exact Or.inr (ih.mpr ⟨x, hx, hfx⟩)

private theorem closedTreesOfSize_noVars (fuel : Nat) :
    ∀ (sz : Nat) {t : Term}, t ∈ closedTreesAux fuel sz → noVars t = true := by
  induction fuel with
  | zero =>
      intro sz t hm
      cases sz with
      | zero => cases hm
      | succ s1 =>
          cases s1 with
          | zero =>
              cases hm with
              | head _ => rfl
              | tail _ h2 => cases h2
          | succ _ => cases hm
  | succ fuel ih =>
      intro sz t hm
      cases sz with
      | zero => cases hm
      | succ s1 =>
          cases s1 with
          | zero =>
              cases hm with
              | head _ => rfl
              | tail _ h2 => cases h2
          | succ n =>
              have hbind : ∀ {α β : Type} {xs : List α} {f : α → List β} {y : β},
                  y ∈ listBind xs f → ∃ x ∈ xs, y ∈ f x := by
                intro α β xs f y hy
                induction xs with
                | nil => cases hy
                | cons a as iha =>
                    rcases mem_append_elim hy with h1 | h2
                    · exact ⟨a, List.Mem.head _, h1⟩
                    · obtain ⟨x, hx, hyx⟩ := iha h2
                      exact ⟨x, List.Mem.tail _ hx, hyx⟩
              obtain ⟨sp, _, h2⟩ := hbind hm
              obtain ⟨l, hl, h3⟩ := hbind h2
              obtain ⟨r, hr, hlr_eq⟩ := mem_map_elim h3
              subst hlr_eq
              exact Bool.and_eq_true _ _ |>.mpr
                ⟨ih sp.1 hl, ih sp.2 hr⟩

private theorem closedTreesUpTo_noVars {B : Nat} {t : Term} (hm : t ∈ closedTreesUpTo B) :
    noVars t = true := by
  induction B with
  | zero => cases hm
  | succ B ih =>
      rcases mem_append_elim hm with h1 | h2
      · exact ih h1
      · exact closedTreesOfSize_noVars (B + 1) (B + 1) h2

/-- **Soundness & Completeness of `decideGardenOfEdenNF` on All Closed Normal Forms**:
    Constructively decides whether `p` has in-degree `0` in `CL(S)`! -/
theorem decideGardenOfEdenNF_iff {p : Term} (hv : noVars p = true) (hnf : IsNormalForm p) :
    decideGardenOfEdenNF p = true ↔ IsGardenOfEden p := by
  have haux2 : ∀ (B : Nat) (q : Term), leaves q ≤ B → noVars q = true → IsNormalForm q →
      (decideGardenOfEdenNF q = true ↔ IsGardenOfEden q) := by
    intro B
    induction B with
    | zero =>
        intro q hle _ _
        have hp := leaves_pos_pure q
        exact False.elim (Nat.not_lt.mpr hle hp)
    | succ B ih =>
        intro q hle hvq hnfq
        rcases closed_nf_shape hvq hnfq with rfl | ⟨u, rfl, hvu, hnfu⟩ | ⟨u, v, rfl, hvu, hvv, hnfu, hnfv⟩
        · change true = true ↔ IsGardenOfEden S
          exact ⟨fun _ => goe_of_leaves_le_3 (by decide), fun _ => rfl⟩
        · have hlu : leaves u ≤ B := Nat.le_of_succ_le_succ (by simpa [leaves, S, Nat.add_comm 1] using hle)
          have hd1 : decideGardenOfEdenNF (S ⋅ u) = decideGardenOfEdenNF u := rfl
          rw [hd1]
          exact (ih u hlu hvu hnfu).trans goe_s1_iff.symm
        · have hpv := leaves_pos_pure v
          have hpu := leaves_pos_pure u
          have h1 : 1 + leaves u + leaves v ≤ B + 1 := hle
          have hlu : leaves u ≤ B := by
            clear ih hle hvq hnfq hvu hvv hnfu hnfv
            omega
          have hlv : leaves v ≤ B := by
            clear ih hle hvq hnfq hvu hvv hnfu hnfv
            omega
          rw [goe_s2_iff hvu hvv hnfu hnfv, ← ih u hlu hvu hnfu, ← ih v hlv hvv hnfv]
          have hd2 : decideGardenOfEdenNF (S ⋅ u ⋅ v) =
              (decideGardenOfEdenNF u && decideGardenOfEdenNF v &&
                !((closedTreesUpTo (leaves v - leaves u)).any (fun y0 =>
                  (stepLO y0).isNone && loReachesNFBool (y0 ⋅ u) v))) := rfl
          rw [hd2]
          simp only [Bool.and_eq_true, Bool.not_eq_true']
          constructor
          · rintro ⟨⟨hdu, hdv⟩, hany_false⟩
            refine ⟨hdu, hdv, ?_⟩
            rintro ⟨y0, hvy0, hnfy0, hly0, hred⟩
            have hly_sub : leaves y0 ≤ leaves v - leaves u := Nat.le_sub_of_add_le hly0
            have hmem : y0 ∈ closedTreesUpTo (leaves v - leaves u) :=
              mem_closedTreesUpTo hvy0 hly_sub
            have hlo_none : (stepLO y0).isNone = true := by
              cases hs : stepLO y0 with
              | none => rfl
              | some y' => exact False.elim (hnfy0 y' (stepLO_some_step hs))
            have hrb : loReachesNFBool (y0 ⋅ u) v = true := (loReachesNFBool_iff hnfv).mpr hred
            have hany_true : ((closedTreesUpTo (leaves v - leaves u)).any (fun y =>
                (stepLO y).isNone && loReachesNFBool (y ⋅ u) v)) = true :=
              (list_any_iff_mem _ _).mpr ⟨y0, hmem, Bool.and_eq_true _ _ |>.mpr ⟨hlo_none, hrb⟩⟩
            rw [hany_true] at hany_false
            cases hany_false
          · rintro ⟨hdu, hdv, hnoy⟩
            refine ⟨⟨hdu, hdv⟩, ?_⟩
            cases hany : (closedTreesUpTo (leaves v - leaves u)).any (fun y =>
                (stepLO y).isNone && loReachesNFBool (y ⋅ u) v) with
            | false => rfl
            | true =>
                obtain ⟨y0, hmem, hcond⟩ := (list_any_iff_mem _ _).mp hany
                have ⟨hlo_none, hrb⟩ := (Bool.and_eq_true _ _).mp hcond
                have hvy0 := closedTreesUpTo_noVars hmem
                have hnfy0 : IsNormalForm y0 := by
                  cases hs : stepLO y0 with
                  | none => exact stepLO_none_isNormalForm hs
                  | some _ => rw [hs] at hlo_none; cases hlo_none
                have hred := (loReachesNFBool_iff hnfv).mp hrb
                have hly0 : leaves y0 + leaves u ≤ leaves v := leaves_mono_reduces hred
                exact False.elim (hnoy ⟨y0, hvy0, hnfy0, hly0, hred⟩)
  exact haux2 (leaves p) p (Nat.le_refl _) hv hnf

/-- Count `(totalClosedNFs, gardenOfEdenClosedNFs)` of exact leaf size `n`. -/
def nfAndGoeCensus (n : Nat) : Nat × Nat :=
  let nfs := (closedTreesOfSize n).filter (fun t => (stepLO t).isNone)
  (nfs.length, (nfs.filter decideGardenOfEdenNF).length)

set_option maxRecDepth 200000 in
/-- **Exact Catalan Garden-of-Eden Normal-Form Census (`sizes 1..7`)**:
    Out of `1, 1, 2, 4, 9, 21, 51` closed pure-`S` Normal Forms of sizes `1..7`,
    **exact** counts `1, 1, 2, 3, 7, 15, 37` are Garden-of-Eden (in-degree `0` in `CL(S)`)! -/
theorem exact_garden_of_eden_census_1_to_7 :
    nfAndGoeCensus 1 = (1, 1) ∧
    nfAndGoeCensus 2 = (1, 1) ∧
    nfAndGoeCensus 3 = (2, 2) ∧
    nfAndGoeCensus 4 = (4, 3) ∧
    nfAndGoeCensus 5 = (9, 7) ∧
    nfAndGoeCensus 6 = (21, 15) ∧
    nfAndGoeCensus 7 = (51, 37) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Section 4: Sharp Multiway (`↠_S`) vs. `→_{lo}` Subterm Appearance Separation -/

/-- Minimal 7-leaf strongly normalizing closed term `M_sn_sep = (S S)(S S S S) S` and 6-leaf NF `P_sn_sep`. -/
def M_sn_sep : Term := B_comb ⋅ (S ⋅ S ⋅ S ⋅ S) ⋅ S
def P_sn_sep : Term := B_comb ⋅ (B_comb ⋅ B_comb)

/-- **Halting (`SN`) Multiway vs. `→_{lo}` Subterm Appearance Separation**:
    `P_sn_sep` is a closed 6-leaf Normal Form that appears in **1 multiway step** from `M_sn_sep`,
    yet **never** appears as a subterm of `iterateLO k M_sn_sep` for **any** `k : Nat`! -/
theorem sn_subterm_appearance_separation :
    noVars M_sn_sep = true ∧
    leaves M_sn_sep = 7 ∧
    IsNormalForm P_sn_sep ∧
    (∃ u, Step M_sn_sep u ∧ hasSubterm P_sn_sep u = true) ∧
    (∀ k : Nat, hasSubterm P_sn_sep (iterateLO k M_sn_sep) = false) := by
  refine ⟨rfl, rfl, stepLO_none_isNormalForm rfl,
    ⟨B_comb ⋅ (B_comb ⋅ B_comb) ⋅ S, Step.left (Step.right (Step.root S S S)), rfl⟩, ?_⟩
  intro k
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | m + 4 =>
      have h3 : iterateLO 3 M_sn_sep = S ⋅ S ⋅ (S ⋅ S ⋅ ((S ⋅ S) ⋅ S)) := rfl
      have hnf3 : stepLO (S ⋅ S ⋅ (S ⋅ S ⋅ ((S ⋅ S) ⋅ S))) = none := rfl
      have hstay : ∀ r : Nat, iterateLO r (S ⋅ S ⋅ (S ⋅ S ⋅ ((S ⋅ S) ⋅ S))) =
          S ⋅ S ⋅ (S ⋅ S ⋅ ((S ⋅ S) ⋅ S)) := by
        intro r
        induction r with
        | zero => rfl
        | succ _ _ => simp only [iterateLO, hnf3]
      have hm4 : m + 4 = 3 + (m + 1) := by omega
      rw [hm4, iterateLO_add 3 (m + 1), h3, hstay (m + 1)]
      rfl

/-- Infinite non-halting (`HN \ SN`) witness `M_inf_sep = S ⋅ AAA ⋅ (A_comb ⋅ B_comb)`. -/
def M_inf_sep : Term := S ⋅ AAA ⋅ (A_comb ⋅ B_comb)

/-- **Infinite Non-Halting Multiway vs. `→_{lo}` Subterm Appearance Separation**:
    1. `M_inf_sep` is closed and non-halting (`¬ StrongNormalizing M_inf_sep`), generating an
       infinite `→_{lo}` evolution (`∀ k, (stepLO (iterateLO k M_inf_sep)).isSome = true`).
    2. In **1 multiway step**, `M_inf_sep` reduces to `S ⋅ AAA ⋅ ((S ⋅ B_comb) ⋅ (S ⋅ B_comb))`,
       containing the **3-leaf** closed Normal Form `S ⋅ B_comb = S(SS)` as a subterm!
    3. Yet across **all** `k : Nat` (`0 ≤ k < ∞`), `S ⋅ B_comb` **never** appears as a subterm
       of `iterateLO k M_inf_sep`! -/
theorem infinite_lo_subterm_appearance_separation :
    noVars M_inf_sep = true ∧
    ¬ StrongNormalizing M_inf_sep ∧
    IsNormalForm (S ⋅ B_comb) ∧
    leaves (S ⋅ B_comb) = 3 ∧
    (∃ u, Step M_inf_sep u ∧ hasSubterm (S ⋅ B_comb) u = true) ∧
    (∀ k : Nat,
      (stepLO (iterateLO k M_inf_sep)).isSome = true ∧
      hasSubterm (S ⋅ B_comb) (iterateLO k M_inf_sep) = false) := by
  have hnsn : ¬ StrongNormalizing M_inf_sep :=
    fun h => ((waldmann_theorem_9 (t := M_inf_sep) rfl).1.mp h) rfl
  have hvc : validLOContext [.s2L (A_comb ⋅ B_comb)] = true := rfl
  have hlock := locked_hn34_forever (ctx := [.s2L (A_comb ⋅ B_comb)]) (foc := AAA) hvc rfl rfl
  refine ⟨rfl, hnsn, stepLO_none_isNormalForm rfl, rfl,
    ⟨S ⋅ AAA ⋅ ((S ⋅ B_comb) ⋅ (S ⋅ B_comb)), Step.right (Step.root S S B_comb), rfl⟩, ?_⟩
  intro k
  obtain ⟨hit_eq, _, _, _, _, hsome⟩ := hlock k
  change iterateLO k M_inf_sep = S ⋅ (iterateLO k AAA) ⋅ (A_comb ⋅ B_comb) at hit_eq
  refine ⟨hsome, ?_⟩
  rw [hit_eq]
  have hga_k : GA (iterateLO k AAA) := ga_reduces (reduces_iterateLO k AAA) ga_aaa
  have hno_aaa := ga_no_subterm_s_bcomb hga_k
  have hne_b : iterateLO k AAA ≠ B_comb := ga_ne_b_comb hga_k
  have hne_s_aaa : S ⋅ B_comb ≠ S ⋅ iterateLO k AAA := by
    intro heq; injection heq with _ hb; exact hne_b hb.symm
  have hne_top : S ⋅ B_comb ≠ S ⋅ iterateLO k AAA ⋅ (A_comb ⋅ B_comb) := by
    intro heq; cases heq
  have hno_right : hasSubterm (S ⋅ B_comb) (A_comb ⋅ B_comb) = false := rfl
  have hno_left : hasSubterm (S ⋅ B_comb) (S ⋅ iterateLO k AAA) = false := by
    unfold hasSubterm
    rw [decide_eq_false hne_s_aaa, hno_aaa]
    rfl
  unfold hasSubterm
  rw [decide_eq_false hne_top, hno_left, hno_right]
  rfl

end FormalWolframFrontier

#print axioms FormalWolframFrontier.zachos_all_step_closed_form
#print axioms FormalWolframFrontier.zachos_triangular_staircase_law
#print axioms FormalWolframFrontier.wolfram2_all_step_closed_form
#print axioms FormalWolframFrontier.wolfram2_vs_w2Twin_shift_14
#print axioms FormalWolframFrontier.tenLeafSeed_all_step_exact_leaves
#print axioms FormalWolframFrontier.aaa_lo_and_multiway_master
#print axioms FormalWolframFrontier.goe_s2_iff
#print axioms FormalWolframFrontier.goe_s2_of_leaves_le
#print axioms FormalWolframFrontier.decideGardenOfEdenNF_iff
#print axioms FormalWolframFrontier.exact_garden_of_eden_census_1_to_7
#print axioms FormalWolframFrontier.sn_subterm_appearance_separation
#print axioms FormalWolframFrontier.infinite_lo_subterm_appearance_separation
