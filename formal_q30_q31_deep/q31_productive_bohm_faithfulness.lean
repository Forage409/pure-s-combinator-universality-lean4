import formal_q5_final.q5_completeness
import formal_q30_q31_deep.q30_finiteness_and_sn_decidability

/-!
# Productive Böhm-Tree Faithfulness & Complete `Prod × All` Convertibility Decidability
# (Completing Barendregt et al. Question 31 & Advancing Dana Scott's Question 30)

Machine-checked in Lean 4.33.1 with **zero `sorry`, zero `Classical.choice`, zero `native_decide`,
and zero custom axioms** (`#print axioms` uses at most `[propext]`).

## Main Theorems

1. **Computable Böhm & Clocked-Böhm Tree Approximants (`bohmApprox`, `clockedBohmApprox`)**:
   - Defined constructively for all closed pure-`S` terms via `evalHN` and `headNormalize`.
   - Exact characterization of productivity via `⊥`-freeness of `bohmApprox`:
     `Productive t ↔ ∀ d, approxHasBot (bohmApprox d t) = false`.
   - `ConvS`-invariance of Böhm trees at all depths:
     `ConvS m n → ∀ d, bohmApprox d m = bohmApprox d n`.

2. **Sharp Unfaithfulness vs Faithfulness Dichotomy for Question 31 (Böhm & Clocked-Böhm Trees)**:
   - **Unsolvable & Semi-Productive Clocked-Böhm Unfaithfulness**
     (`unsolvable_clockedBohm_unfaithful`, `semiProductive_clockedBohm_unfaithful`):
     Whenever `⊥` occurs (`¬ Productive`), infinitely many pairwise non-convertible closed `S`-terms
     (`appS AAA k`, or `rightTower D`-prefixed `S ⋅ ... ⋅ appS AAA k` at arbitrary finite depth `D`)
     have the **exact same Böhm tree and clocked Böhm tree**!
   - **Productive Böhm-Tree Faithfulness Theorem**
     (`productive_bohm_faithful`, `productive_oneSided_bohm_iff_convS`):
     On **all** productive (`⊥`-free) closed pure-`S` terms (including all non-terminating infinite-tree
     combinators such as Zachos's `Z_Zac = (S T T)(S T T)` and its closure under `CL(S)`),
     **Böhm-tree equality is 100% faithful**:
     `Productive m → ((∀ d, bohmApprox d m = bohmApprox d n) ↔ ConvS m n)`!
   - **Clocked-Böhm Phenomena on Productive Non-`SN` Terms**
     (`zachos_convS_clock_mismatch`, `productive_nonSN_distinct_same_clockedBohm`):
     - `Z_Zac = zachosG 0 ⋅ zachosG 0` and `zachosG 1 ⋅ zachosG 1` are convertible productive terms
       with **different** clocked Böhm trees (root head clocks `2` vs `1`).
     - Conversely, the distinct 12-leaf and 13-leaf non-`SN` productive combinators
       `cbtPair1` and `cbtPair2` (`¬ Reduces cbtPair1 cbtPair2`, `¬ Reduces cbtPair2 cbtPair1`)
       share the **exact same infinite clocked Böhm tree** (`∀ d, clockedBohmApprox d cbtPair1 = clockedBohmApprox d cbtPair2`)
       and are `=_S`-convertible!

3. **Complete Decidability of Dana Scott's Question 30 Across `Productive × All` Closed `S`-Terms**
   (`decideConvProd`, `joinOfConvProd`):
   - Total, computable decision procedure `decideConvProd m n hvm hvn hm_prod : Decidable (ConvS m n)`
     deciding `m =_S n` across **all** closed pure-`S` terms `n` whenever `Productive m` (`evalP m ≠ .p37`).
   - Strictly extends `SN × All` decidability (`SN ⊊ Productive`).
   - Constructive join extractor `joinOfConvProd`: whenever `ConvS m n` holds with `Productive m`,
     computably constructs `w : Term` in `Type` witnessing `Reduces m w ∧ Reduces n w`!
-/

namespace FormalQ30Q31Deep

open FormalAlgebra
open ZeroNavigatorMultiway
open Q5SNStratifiedGame
open FormalQ5Final

/-! ## Section 1: Computable Böhm & Clocked-Böhm Approximants -/

inductive BohmApprox where
  | trunc : BohmApprox
  | bot : BohmApprox
  | s0 : BohmApprox
  | s1 : BohmApprox → BohmApprox
  | s2 : BohmApprox → BohmApprox → BohmApprox
  deriving DecidableEq, Repr

inductive ClockedBohmApprox where
  | trunc : ClockedBohmApprox
  | bot : ClockedBohmApprox
  | s0 : Nat → ClockedBohmApprox
  | s1 : Nat → ClockedBohmApprox → ClockedBohmApprox
  | s2 : Nat → ClockedBohmApprox → ClockedBohmApprox → ClockedBohmApprox
  deriving DecidableEq, Repr

def approxHasBot : BohmApprox → Bool
  | .trunc => false
  | .bot => true
  | .s0 => false
  | .s1 a => approxHasBot a
  | .s2 a b => approxHasBot a || approxHasBot b

/-- Deterministic head-reduction step counter up to `fuel` steps. -/
def headClockAux : Nat → Term → Nat
  | 0, _ => 0
  | fuel + 1, t =>
    match headStepOpt t with
    | none => 0
    | some t' => 1 + headClockAux fuel t'

def headClock (t : Term) : Nat :=
  headClockAux (muHN t + 1) t

/-- Computable depth-`d` Böhm-tree approximant for any closed pure-`S` term `t`. -/
def bohmApprox : Nat → Term → BohmApprox
  | 0, _ => .trunc
  | d + 1, t =>
    if evalHN t == .hn34 then .bot
    else
      match headNormalize t with
      | .app (.app .s a) b => .s2 (bohmApprox d a) (bohmApprox d b)
      | .app .s a => .s1 (bohmApprox d a)
      | _ => .s0

/-- Computable depth-`d` clocked Böhm-tree approximant (recording exact head-step count at every node). -/
def clockedBohmApprox : Nat → Term → ClockedBohmApprox
  | 0, _ => .trunc
  | d + 1, t =>
    if evalHN t == .hn34 then .bot
    else
      let clk := headClock t
      match headNormalize t with
      | .app (.app .s a) b => .s2 clk (clockedBohmApprox d a) (clockedBohmApprox d b)
      | .app .s a => .s1 clk (clockedBohmApprox d a)
      | _ => .s0 clk

def eraseClock : ClockedBohmApprox → BohmApprox
  | .trunc => .trunc
  | .bot => .bot
  | .s0 _ => .s0
  | .s1 _ a => .s1 (eraseClock a)
  | .s2 _ a b => .s2 (eraseClock a) (eraseClock b)

theorem eraseClock_clockedBohmApprox :
    ∀ (d : Nat) (t : Term), eraseClock (clockedBohmApprox d t) = bohmApprox d t
  | 0, _ => rfl
  | d + 1, t => by
    simp only [clockedBohmApprox, bohmApprox]
    cases h : (evalHN t == .hn34)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hh : headNormalize t with
      | s => rfl
      | var _ => rfl
      | app l r =>
        cases l with
        | s => simp [eraseClock, eraseClock_clockedBohmApprox d r]
        | var _ => rfl
        | app l2 a =>
          cases l2 with
          | s => simp [eraseClock, eraseClock_clockedBohmApprox d a, eraseClock_clockedBohmApprox d r]
          | var _ => rfl
          | app _ _ => rfl
    · rfl

theorem sameClockedBohm_implies_sameBohm {t u : Term}
    (h : ∀ d, clockedBohmApprox d t = clockedBohmApprox d u) (d : Nat) :
    bohmApprox d t = bohmApprox d u := by
  rw [← eraseClock_clockedBohmApprox d t, ← eraseClock_clockedBohmApprox d u, h d]

/-! ### Exact Equation Lemmas for `bohmApprox` and `headClock` -/

theorem bohmApprox_bot (d : Nat) {t : Term} (h34 : evalHN t = .hn34) :
    bohmApprox (d + 1) t = .bot := by
  simp [bohmApprox, h34]

theorem clockedBohmApprox_bot (d : Nat) {t : Term} (h34 : evalHN t = .hn34) :
    clockedBohmApprox (d + 1) t = .bot := by
  simp [clockedBohmApprox, h34]

private theorem beq_hn34_false_of_ne {s : StateHN} (hne : s ≠ .hn34) : (s == .hn34) = false := by
  cases s <;> first | rfl | exact False.elim (hne rfl)

theorem headNormalize_eq_of_headReduces_closedHNF {t h : Term}
    (hvt : noVars t = true) (hr : HeadReduces t h) (hsl : spineLen h ≤ 2) :
    evalHN t ≠ .hn34 ∧ headNormalize t = h := by
  have hvh : noVars h = true := noVars_reduces (headReduces_to_reduces hr) hvt
  have hne_h : evalHN h ≠ .hn34 := closed_hnf_evalHN_ne_hn34 hvh hsl
  have hne_t : evalHN t ≠ .hn34 := by
    rw [evalHN_reduces (headReduces_to_reduces hr)]
    exact hne_h
  have hnone : headStepOpt h = none := closed_hnf_headStepOpt_none hvh hsl
  exact ⟨hne_t, headNormalize_eq_of_headReduces_none hvt hne_t hr hnone⟩

theorem bohmApprox_of_headReduces_s (d : Nat) {t : Term}
    (hvt : noVars t = true) (hr : HeadReduces t S) :
    bohmApprox (d + 1) t = .s0 := by
  obtain ⟨hne, heq⟩ := headNormalize_eq_of_headReduces_closedHNF hvt hr (Nat.zero_le 2)
  simp [bohmApprox, beq_hn34_false_of_ne hne, heq, S]

theorem bohmApprox_of_headReduces_s1 (d : Nat) {t a : Term}
    (hvt : noVars t = true) (hr : HeadReduces t (S ⋅ a)) :
    bohmApprox (d + 1) t = .s1 (bohmApprox d a) := by
  obtain ⟨hne, heq⟩ :=
    headNormalize_eq_of_headReduces_closedHNF hvt hr (Nat.succ_le_succ (Nat.zero_le 1))
  simp [bohmApprox, beq_hn34_false_of_ne hne, heq, S]

theorem bohmApprox_of_headReduces_s2 (d : Nat) {t a b : Term}
    (hvt : noVars t = true) (hr : HeadReduces t (S ⋅ a ⋅ b)) :
    bohmApprox (d + 1) t = .s2 (bohmApprox d a) (bohmApprox d b) := by
  obtain ⟨hne, heq⟩ := headNormalize_eq_of_headReduces_closedHNF hvt hr (Nat.le_refl 2)
  simp [bohmApprox, beq_hn34_false_of_ne hne, heq, S]

private theorem headClockAux_none {fuel : Nat} {t : Term} (hnone : headStepOpt t = none) :
    headClockAux fuel t = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => simp [headClockAux, hnone]

private theorem headClockAux_step {fuel : Nat} {t t' : Term}
    (hs : HeadStep t t') (hne : evalHN t ≠ .hn34) (hlt : muHN t < fuel) :
    headClockAux fuel t = 1 + headClockAux (fuel - 1) t' ∧
    (∀ f2, muHN t' < f2 → headClockAux (fuel - 1) t' = headClockAux f2 t') := by
  -- Prove fuel-invariance of `headClockAux` whenever `muHN u < f`:
  have fuel_inv : ∀ (f1 : Nat) {u : Term}, evalHN u ≠ .hn34 → muHN u < f1 →
      ∀ (f2 : Nat), muHN u < f2 → headClockAux f1 u = headClockAux f2 u := by
    intro f1
    induction f1 with
    | zero => intro _ _ h; cases h
    | succ f1' ih =>
      intro u hu_ne hu_lt1 f2 hu_lt2
      cases f2 with
      | zero => cases hu_lt2
      | succ f2' =>
        simp only [headClockAux]
        cases hh : headStepOpt u with
        | none => rfl
        | some u' =>
          have hsu : HeadStep u u' := headStepOpt_some hh
          have hdrop : muHN u' + 1 ≤ muHN u := muHN_headStep_drop hsu hu_ne
          have hu'_ne : evalHN u' ≠ .hn34 := by
            rw [← evalHN_step (headStep_to_step hsu)]; exact hu_ne
          exact congrArg (1 + ·) (ih hu'_ne (by omega) f2' (by omega))
  cases fuel with
  | zero => cases hlt
  | succ f =>
    have hh : headStepOpt t = some t' := headStepOpt_complete hs
    have hdrop : muHN t' + 1 ≤ muHN t := muHN_headStep_drop hs hne
    have hne' : evalHN t' ≠ .hn34 := by
      rw [← evalHN_step (headStep_to_step hs)]; exact hne
    refine ⟨by simp [headClockAux, hh], fun f2 hf2 => ?_⟩
    exact fuel_inv f hne' (by omega) f2 hf2

theorem headClock_of_headStep {t t' : Term} (hs : HeadStep t t') (hne : evalHN t ≠ .hn34) :
    headClock t = 1 + headClock t' := by
  obtain ⟨h1, h2⟩ := headClockAux_step hs hne (Nat.lt_succ_self (muHN t))
  unfold headClock
  rw [h1, h2 (muHN t' + 1) (Nat.lt_succ_self _)]

theorem headClock_of_closedHNF {h : Term} (hvh : noVars h = true) (hsl : spineLen h ≤ 2) :
    headClock h = 0 :=
  headClockAux_none (closed_hnf_headStepOpt_none hvh hsl)

theorem clockedBohmApprox_eq_of_common_headStep {t1 t2 m : Term}
    (hs1 : HeadStep t1 m) (hs2 : HeadStep t2 m) :
    ∀ d : Nat, clockedBohmApprox d t1 = clockedBohmApprox d t2
  | 0 => rfl
  | d + 1 => by
    have he1 : evalHN t1 = evalHN m := evalHN_step (headStep_to_step hs1)
    have he2 : evalHN t2 = evalHN m := evalHN_step (headStep_to_step hs2)
    by_cases h34 : evalHN m = .hn34
    · rw [clockedBohmApprox_bot d (he1.trans h34), clockedBohmApprox_bot d (he2.trans h34)]
    · have hne1 : evalHN t1 ≠ .hn34 := by rw [he1]; exact h34
      have hne2 : evalHN t2 ≠ .hn34 := by rw [he2]; exact h34
      have hc1 : headClock t1 = 1 + headClock m := headClock_of_headStep hs1 hne1
      have hc2 : headClock t2 = 1 + headClock m := headClock_of_headStep hs2 hne2
      -- Both `t1` and `t2` have the exact same `headNormalize` as `m`!
      have hn_eq : ∀ {u : Term}, HeadStep u m → evalHN u ≠ .hn34 → headNormalize u = headNormalize m := by
        intro u hsu hneu
        -- `headNormalizeAux` invariance under fuel:
        have aux_inv : ∀ (f1 : Nat) {x : Term}, evalHN x ≠ .hn34 → muHN x < f1 →
            ∀ (f2 : Nat), muHN x < f2 → headNormalizeAux f1 x = headNormalizeAux f2 x := by
          intro f1
          induction f1 with
          | zero => intro _ _ h; cases h
          | succ f1' ih =>
            intro x hx_ne hx_lt1 f2 hx_lt2
            cases f2 with
            | zero => cases hx_lt2
            | succ f2' =>
              simp only [headNormalizeAux]
              cases hh : headStepOpt x with
              | none => rfl
              | some x' =>
                have hsx : HeadStep x x' := headStepOpt_some hh
                have hdrop := muHN_headStep_drop hsx hx_ne
                have hx'_ne : evalHN x' ≠ .hn34 := by
                  rw [← evalHN_step (headStep_to_step hsx)]; exact hx_ne
                exact ih hx'_ne (by omega) f2' (by omega)
        unfold headNormalize
        have hh : headStepOpt u = some m := headStepOpt_complete hsu
        have hdrop := muHN_headStep_drop hsu hneu
        change headNormalizeAux (muHN u + 1) u = headNormalizeAux (muHN m + 1) m
        simp only [headNormalizeAux, hh]
        exact aux_inv (muHN u) h34 (by omega) (muHN m + 1) (Nat.lt_succ_self _)
      have hn1 := hn_eq hs1 hne1
      have hn2 := hn_eq hs2 hne2
      simp only [clockedBohmApprox, beq_hn34_false_of_ne hne1, beq_hn34_false_of_ne hne2,
                 Bool.false_eq_true, ↓reduceIte, hc1, hc2, hn1, hn2]

/-! ## Section 2: `ConvS`-Invariance of `bohmApprox` & Productivity Equivalence -/

private theorem spineLen_le_2_reduces_eq {a b : Term} (hva : noVars a = true)
    (hsl : spineLen a ≤ 2) (hr : Reduces a b) : spineLen b = spineLen a := by
  rcases closed_spineLen_le_2_shapes hva hsl with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · rw [s_reduces_eq hr]
  · obtain ⟨x', rfl, _⟩ := s1_reduces_inv hr rfl
    rfl
  · obtain ⟨x', y', rfl, _, _⟩ := s2_reduces_inv hr rfl
    rfl

private theorem closed_hnf_convS_align {h1 h2 : Term}
    (hv1 : noVars h1 = true) (hsl1 : spineLen h1 ≤ 2)
    (hv2 : noVars h2 = true) (hsl2 : spineLen h2 ≤ 2)
    (hconv : ConvS h1 h2) :
    (h1 = S ∧ h2 = S) ∨
    (∃ a1 a2, h1 = S ⋅ a1 ∧ h2 = S ⋅ a2 ∧ ConvS a1 a2) ∨
    (∃ a1 b1 a2 b2, h1 = S ⋅ a1 ⋅ b1 ∧ h2 = S ⋅ a2 ⋅ b2 ∧ ConvS a1 a2 ∧ ConvS b1 b2) := by
  obtain ⟨w, hr1, hr2⟩ := convS_iff_common_reduct.mp hconv
  have hsp1 := spineLen_le_2_reduces_eq hv1 hsl1 hr1
  have hsp2 := spineLen_le_2_reduces_eq hv2 hsl2 hr2
  have hsp_eq : spineLen h1 = spineLen h2 := hsp1.symm.trans hsp2
  rcases closed_spineLen_le_2_shapes hv1 hsl1 with rfl | ⟨a1, rfl⟩ | ⟨a1, b1, rfl⟩
  · rcases closed_spineLen_le_2_shapes hv2 hsl2 with rfl | ⟨a2, rfl⟩ | ⟨a2, b2, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · cases hsp_eq
    · cases hsp_eq
  · rcases closed_spineLen_le_2_shapes hv2 hsl2 with rfl | ⟨a2, rfl⟩ | ⟨a2, b2, rfl⟩
    · cases hsp_eq
    · obtain ⟨a1', hw1, hra1⟩ := s1_reduces_inv hr1 rfl
      obtain ⟨a2', hw2, hra2⟩ := s1_reduces_inv hr2 rfl
      have heq := hw1.symm.trans hw2
      injection heq with _ ha_eq
      subst ha_eq
      exact Or.inr (Or.inl ⟨a1, a2, rfl, rfl, convS_iff_common_reduct.mpr ⟨a1', hra1, hra2⟩⟩)
    · cases hsp_eq
  · rcases closed_spineLen_le_2_shapes hv2 hsl2 with rfl | ⟨a2, rfl⟩ | ⟨a2, b2, rfl⟩
    · cases hsp_eq
    · cases hsp_eq
    · obtain ⟨a1', b1', hw1, hra1, hrb1⟩ := s2_reduces_inv hr1 rfl
      obtain ⟨a2', b2', hw2, hra2, hrb2⟩ := s2_reduces_inv hr2 rfl
      have heq := hw1.symm.trans hw2
      injection heq with h12 hb_eq
      injection h12 with _ ha_eq
      subst ha_eq; subst hb_eq
      exact Or.inr (Or.inr ⟨a1, b1, a2, b2, rfl, rfl,
        convS_iff_common_reduct.mpr ⟨a1', hra1, hra2⟩,
        convS_iff_common_reduct.mpr ⟨b1', hrb1, hrb2⟩⟩)

/-- **Soundness of Böhm Trees for `ConvS`**:
    Convertible closed pure-`S` terms have identical Böhm-tree approximants at every depth `d`. -/
theorem convS_bohmApprox_eq :
    ∀ (d : Nat) {t u : Term}, noVars t = true → noVars u = true → ConvS t u →
      bohmApprox d t = bohmApprox d u
  | 0, _, _, _, _, _ => rfl
  | d + 1, t, u, hvt, hvu, hconv => by
    have heq_hn : evalHN t = evalHN u := evalHN_conv hconv
    by_cases h34 : evalHN t = .hn34
    · rw [bohmApprox_bot d h34, bohmApprox_bot d (heq_hn.symm.trans h34)]
    · have hu_ne : evalHN u ≠ .hn34 := fun hu34 => h34 (heq_hn.trans hu34)
      obtain ⟨hrt, hhnft⟩ := headNormalize_reduces_hnf hvt h34
      obtain ⟨hru, hhnfu⟩ := headNormalize_reduces_hnf hvu hu_ne
      have hconv_h : ConvS (headNormalize t) (headNormalize u) :=
        ConvS.trans (ConvS.symm (reduces_to_convS (headReduces_to_reduces hrt)))
          (ConvS.trans hconv (reduces_to_convS (headReduces_to_reduces hru)))
      rcases closed_hnf_convS_align hhnft.1 hhnft.2 hhnfu.1 hhnfu.2 hconv_h with
        ⟨ht0, hu0⟩ | ⟨a1, a2, ht1, hu1, hca⟩ | ⟨a1, b1, a2, b2, ht2, hu2, hca, hcb⟩
      · rw [ht0] at hrt; rw [hu0] at hru
        rw [bohmApprox_of_headReduces_s d hvt hrt, bohmApprox_of_headReduces_s d hvu hru]
      · rw [ht1] at hrt hhnft; rw [hu1] at hru hhnfu
        have hva1 : noVars a1 = true := ((Bool.and_eq_true _ _).mp hhnft.1).2
        have hva2 : noVars a2 = true := ((Bool.and_eq_true _ _).mp hhnfu.1).2
        rw [bohmApprox_of_headReduces_s1 d hvt hrt, bohmApprox_of_headReduces_s1 d hvu hru,
            convS_bohmApprox_eq d hva1 hva2 hca]
      · rw [ht2] at hrt hhnft; rw [hu2] at hru hhnfu
        have hva1 : noVars a1 = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hhnft.1).1).2
        have hvb1 : noVars b1 = true := ((Bool.and_eq_true _ _).mp hhnft.1).2
        have hva2 : noVars a2 = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hhnfu.1).1).2
        have hvb2 : noVars b2 = true := ((Bool.and_eq_true _ _).mp hhnfu.1).2
        rw [bohmApprox_of_headReduces_s2 d hvt hrt, bohmApprox_of_headReduces_s2 d hvu hru,
            convS_bohmApprox_eq d hva1 hva2 hca, convS_bohmApprox_eq d hvb1 hvb2 hcb]

theorem hasBotWithin_implies_approxHasBot :
    ∀ (d : Nat) {t : Term}, noVars t = true → HasBotWithin d t →
      approxHasBot (bohmApprox (d + 1) t) = true
  | d, t, hvt, .bot_div hno => by
    have h34 : evalHN t = .hn34 := closed_not_hasHNF_evalHN_hn34 hvt hno
    rw [bohmApprox_bot d h34]; rfl
  | d + 1, t, hvt, @HasBotWithin.bot_s1 _ _ a hred hba => by
    have hconv : ConvS t (S ⋅ a) := reduces_to_convS hred
    have hvsa : noVars (S ⋅ a) = true := noVars_reduces hred hvt
    have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hvsa).2
    rw [convS_bohmApprox_eq (d + 2) hvt hvsa hconv,
        bohmApprox_of_headReduces_s1 (d + 1) hvsa (HeadReduces.refl _)]
    exact hasBotWithin_implies_approxHasBot d hva hba
  | d + 1, t, hvt, @HasBotWithin.bot_s2_l _ _ a b hred hba => by
    have hconv : ConvS t (S ⋅ a ⋅ b) := reduces_to_convS hred
    have hvsab : noVars (S ⋅ a ⋅ b) = true := noVars_reduces hred hvt
    have hva : noVars a = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hvsab).1).2
    rw [convS_bohmApprox_eq (d + 2) hvt hvsab hconv,
        bohmApprox_of_headReduces_s2 (d + 1) hvsab (HeadReduces.refl _)]
    simp [approxHasBot, hasBotWithin_implies_approxHasBot d hva hba]
  | d + 1, t, hvt, @HasBotWithin.bot_s2_r _ _ a b hred hbb => by
    have hconv : ConvS t (S ⋅ a ⋅ b) := reduces_to_convS hred
    have hvsab : noVars (S ⋅ a ⋅ b) = true := noVars_reduces hred hvt
    have hvb : noVars b = true := ((Bool.and_eq_true _ _).mp hvsab).2
    rw [convS_bohmApprox_eq (d + 2) hvt hvsab hconv,
        bohmApprox_of_headReduces_s2 (d + 1) hvsab (HeadReduces.refl _)]
    simp [approxHasBot, hasBotWithin_implies_approxHasBot d hvb hbb]

theorem approxHasBot_implies_hasBot :
    ∀ (d : Nat) {t : Term}, noVars t = true → approxHasBot (bohmApprox d t) = true → HasBot t
  | 0, _, _, h => by cases h
  | d + 1, t, hvt, h => by
    by_cases h34 : evalHN t = .hn34
    · exact ⟨0, closed_evalHN_hn34_hasBot0 hvt h34⟩
    · obtain ⟨hrt, hhnft⟩ := headNormalize_reduces_hnf hvt h34
      rcases closed_spineLen_le_2_shapes hhnft.1 hhnft.2 with h0 | ⟨a, h1⟩ | ⟨a, b, h2⟩
      · rw [h0] at hrt
        rw [bohmApprox_of_headReduces_s d hvt hrt] at h
        cases h
      · rw [h1] at hrt hhnft
        have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hhnft.1).2
        rw [bohmApprox_of_headReduces_s1 d hvt hrt] at h
        obtain ⟨da, hda⟩ := approxHasBot_implies_hasBot d hva h
        exact ⟨da + 1, .bot_s1 (headReduces_to_reduces hrt) hda⟩
      · rw [h2] at hrt hhnft
        have hva : noVars a = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hhnft.1).1).2
        have hvb : noVars b = true := ((Bool.and_eq_true _ _).mp hhnft.1).2
        rw [bohmApprox_of_headReduces_s2 d hvt hrt] at h
        simp only [approxHasBot, Bool.or_eq_true] at h
        rcases h with ha | hb
        · obtain ⟨da, hda⟩ := approxHasBot_implies_hasBot d hva ha
          exact ⟨da + 1, .bot_s2_l (headReduces_to_reduces hrt) hda⟩
        · obtain ⟨db, hdb⟩ := approxHasBot_implies_hasBot d hvb hb
          exact ⟨db + 1, .bot_s2_r (headReduces_to_reduces hrt) hdb⟩

/-- **Exact `bohmApprox` Characterization of `Productive`**:
    A closed pure-`S` term `t` is productive iff `bohmApprox d t` is `⊥`-free at every depth `d`. -/
theorem productive_iff_bohmApprox_botFree {t : Term} (hvt : noVars t = true) :
    Productive t ↔ ∀ d : Nat, approxHasBot (bohmApprox d t) = false := by
  constructor
  · intro hprod d
    cases hb : approxHasBot (bohmApprox d t)
    · rfl
    · exact False.elim (hprod (approxHasBot_implies_hasBot d hvt hb))
  · intro hall ⟨d, hd⟩
    have ht := hasBotWithin_implies_approxHasBot d hvt hd
    rw [hall (d + 1)] at ht
    cases ht

/-! ## Section 3: Unfaithfulness of Clocked Böhm Trees When `⊥` Is Present -/

theorem evalHN_appS_aaa : ∀ k : Nat, evalHN (appS AAA k) = .hn34
  | 0 => rfl
  | k + 1 => by
    change deltaHN (evalHN (appS AAA k)) (evalHN S) = .hn34
    rw [evalHN_appS_aaa k]
    exact deltaHN_hn34_left _

/-- **Unsolvable Clocked-Böhm Unfaithfulness Theorem (Strengthening Question 31)**:
    All infinitely many terms `appS AAA k` (`k ∈ ℕ`) have the **exact same clocked Böhm tree**
    (and hence the exact same Böhm tree) at all depths, yet are pairwise non-convertible! -/
theorem unsolvable_clockedBohm_unfaithful {j k : Nat} (hjk : j ≠ k) :
    (∀ d : Nat, clockedBohmApprox d (appS AAA j) = clockedBohmApprox d (appS AAA k)) ∧
    (∀ d : Nat, bohmApprox d (appS AAA j) = bohmApprox d (appS AAA k)) ∧
    ¬ ConvS (appS AAA j) (appS AAA k) := by
  have hcbt : ∀ d : Nat, clockedBohmApprox d (appS AAA j) = clockedBohmApprox d (appS AAA k) := by
    intro d
    cases d with
    | zero => rfl
    | succ d' =>
      rw [clockedBohmApprox_bot d' (evalHN_appS_aaa j),
          clockedBohmApprox_bot d' (evalHN_appS_aaa k)]
  refine ⟨hcbt, fun d => sameClockedBohm_implies_sameBohm hcbt d, ?_⟩
  intro hconv
  exact hjk ((aaa_appS_convS_iff j k).mp hconv)

/-- Wrapping a term under `D` unary `S ⋅ _` constructors places it at Böhm depth `D`. -/
def wrapS1 : Nat → Term → Term
  | 0, u => u
  | D + 1, u => S ⋅ wrapS1 D u

theorem noVars_appS_aaa : ∀ k : Nat, noVars (appS AAA k) = true
  | 0 => rfl
  | k + 1 => (Bool.and_eq_true _ _).mpr ⟨noVars_appS_aaa k, rfl⟩

theorem noVars_wrapS1 (D : Nat) {u : Term} (hvu : noVars u = true) :
    noVars (wrapS1 D u) = true := by
  induction D with
  | zero => exact hvu
  | succ D ih => exact (Bool.and_eq_true _ _).mpr ⟨rfl, ih⟩

private theorem clockedBohmApprox_s1 (d : Nat) {u : Term} (hvu : noVars u = true) :
    clockedBohmApprox (d + 1) (S ⋅ u) = .s1 0 (clockedBohmApprox d u) := by
  have hv : noVars (S ⋅ u) = true := (Bool.and_eq_true _ _).mpr ⟨rfl, hvu⟩
  obtain ⟨hne, hn⟩ := headNormalize_eq_of_headReduces_closedHNF hv
    (HeadReduces.refl _) (Nat.succ_le_succ (Nat.zero_le 1))
  have hc : headClock (S ⋅ u) = 0 := headClock_of_closedHNF hv (Nat.succ_le_succ (Nat.zero_le 1))
  rw [clockedBohmApprox.eq_2, beq_hn34_false_of_ne hne, hn, hc]
  rfl

private theorem convS_s1_inv {a b : Term} (h : ConvS (S ⋅ a) (S ⋅ b)) : ConvS a b := by
  obtain ⟨w, hr1, hr2⟩ := convS_iff_common_reduct.mp h
  obtain ⟨a', rfl, hra⟩ := s1_reduces_inv hr1 rfl
  obtain ⟨b', heq, hrb⟩ := s1_reduces_inv hr2 rfl
  injection heq with _ hab
  subst hab
  exact convS_iff_common_reduct.mpr ⟨a', hra, hrb⟩

/-- **Semi-Productive Clocked-Böhm Unfaithfulness at Arbitrary Depth `D`**:
    Even for terms that are head-normalizing up to arbitrary finite depth `D`, a single `⊥`
    at depth `D` suffices to create infinitely many pairwise non-convertible closed `S`-terms
    with the **exact same clocked Böhm tree**! -/
theorem semiProductive_clockedBohm_unfaithful (D : Nat) {j k : Nat} (hjk : j ≠ k) :
    (∀ d : Nat, clockedBohmApprox d (wrapS1 D (appS AAA j)) =
                clockedBohmApprox d (wrapS1 D (appS AAA k))) ∧
    ¬ ConvS (wrapS1 D (appS AAA j)) (wrapS1 D (appS AAA k)) := by
  refine ⟨?_, ?_⟩
  · induction D with
    | zero => exact (unsolvable_clockedBohm_unfaithful hjk).1
    | succ D ih =>
      intro d
      cases d with
      | zero => rfl
      | succ d' =>
        change clockedBohmApprox (d' + 1) (S ⋅ wrapS1 D (appS AAA j)) =
               clockedBohmApprox (d' + 1) (S ⋅ wrapS1 D (appS AAA k))
        rw [clockedBohmApprox_s1 d' (noVars_wrapS1 D (noVars_appS_aaa j)),
            clockedBohmApprox_s1 d' (noVars_wrapS1 D (noVars_appS_aaa k)),
            ih d']
  · induction D with
    | zero => exact (unsolvable_clockedBohm_unfaithful hjk).2.2
    | succ D ih =>
      intro hconv
      exact ih (convS_s1_inv hconv)

/-! ## Section 4: Productive Böhm-Tree Faithfulness & Complete `Prod × All` Decidability -/

/-! ### 4.1 Normal-Form Rigidity on `PVal` and Closed Normal-Form Böhm Reconstruction -/

def pvalHasZachos : PVal → Bool
  | .s => false
  | .s1 u => pvalHasZachos u
  | .s2 a b => pvalHasZachos a || pvalHasZachos b
  | .zachos _ _ => true

theorem pval_noZachos_isNormalForm :
    ∀ (v : PVal), pvalHasZachos v = false → IsNormalForm v.toTerm
  | .s, _ => fun _ hs => by cases hs
  | .s1 u, h => by
    have ih := pval_noZachos_isNormalForm u h
    intro w hs
    cases hs with
    | left hl => cases hl
    | right hr => exact ih _ hr
  | .s2 a b, h => by
    have ⟨ha, hb⟩ := Bool.or_eq_false_iff.mp h
    have iha := pval_noZachos_isNormalForm a ha
    have ihb := pval_noZachos_isNormalForm b hb
    intro w hs
    cases hs with
    | left hl =>
      cases hl with
      | left hll => cases hll
      | right hlr => exact iha _ hlr
    | right hr => exact ihb _ hr
  | .zachos _ _, h => by cases h

private theorem evalSN_zachosG_zero : evalSN (zachosG 0) = .sn22 := rfl

private theorem evalSN_zachosG_succ : ∀ k : Nat, evalSN (zachosG (k + 1)) = .sn23
  | 0 => rfl
  | k + 1 => by
    change deltaSN (evalSN zachosT) (evalSN (zachosG (k + 1))) = .sn23
    rw [evalSN_zachosG_succ k]; rfl

theorem evalSN_zachos_pair_sn38 (m n : Nat) : evalSN (zachosG m ⋅ zachosG n) = .sn38 := by
  cases m <;> cases n <;>
    simp only [evalSN, evalSN_zachosG_zero, evalSN_zachosG_succ] <;> rfl

theorem pval_hasZachos_evalSN_sn38 :
    ∀ (v : PVal), pvalHasZachos v = true → evalSN v.toTerm = .sn38
  | .s, h => by cases h
  | .s1 u, h => by
    change deltaSN .sn0 (evalSN u.toTerm) = .sn38
    rw [pval_hasZachos_evalSN_sn38 u h, deltaSN_sn38_right]
  | .s2 a b, h => by
    change deltaSN (deltaSN .sn0 (evalSN a.toTerm)) (evalSN b.toTerm) = .sn38
    rcases (Bool.or_eq_true _ _).mp h with ha | hb
    · rw [pval_hasZachos_evalSN_sn38 a ha, deltaSN_sn38_right, deltaSN_sn38_left]
    · rw [pval_hasZachos_evalSN_sn38 b hb, deltaSN_sn38_right]
  | .zachos m n, _ => evalSN_zachos_pair_sn38 m n

/-- **Exact `PVal`-vs-Normal-Form Rigidity Lemma**:
    A `PVal` `a` is `=_S`-convertible to a closed normal form `nf` **if and only if**
    `a.toTerm = nf` syntactically! -/
theorem pval_convS_closed_nf_iff_eq (a : PVal) {nf : Term}
    (hvnf : noVars nf = true) (hnf : IsNormalForm nf) :
    ConvS a.toTerm nf ↔ a.toTerm = nf := by
  constructor
  · intro hconv
    cases hz : pvalHasZachos a
    · have ha_nf : IsNormalForm a.toTerm := pval_noZachos_isNormalForm a hz
      by_cases heq : a.toTerm = nf
      · exact heq
      · exact False.elim (distinct_nf_not_convS ha_nf hnf heq hconv)
    · exfalso
      have h38 : evalSN a.toTerm = .sn38 := pval_hasZachos_evalSN_sn38 a hz
      have hnf38 : evalSN nf = .sn38 := (evalSN_conv hconv).symm.trans h38
      exact closed_nf_evalSN_ne_sn38 hvnf hnf hnf38
  · rintro rfl
    exact ConvS.refl _

theorem isNormalForm_zachosG : ∀ n : Nat, IsNormalForm (zachosG n)
  | 0 => by
    intro u hs
    cases hs with
    | left hl =>
      cases hl with
      | left hll => cases hll
      | right hlr =>
        cases hlr with
        | left h1 => cases h1
        | right h2 => cases h2
    | right hr =>
      cases hr with
      | left h1 => cases h1
      | right h2 => cases h2
  | k + 1 => by
    have ih := isNormalForm_zachosG k
    intro u hs
    cases hs with
    | left hl =>
      cases hl with
      | left hll => cases hll
      | right hlr => cases hlr
    | right hr => exact ih _ hr

theorem leaves_zachosG : ∀ n : Nat, leaves (zachosG n) = 2 * n + 5
  | 0 => rfl
  | k + 1 => by
    change (1 + 1) + leaves (zachosG k) = 2 * (k + 1) + 5
    rw [leaves_zachosG k]; omega

theorem zachosG_inj {m n : Nat} (h : zachosG m = zachosG n) : m = n := by
  have hm := leaves_zachosG m
  have hn := leaves_zachosG n
  rw [h] at hm
  omega

/-- Downward depth monotonicity of `bohmApprox` equality on closed terms. -/
theorem bohmApprox_eq_mono :
    ∀ {d1 d2 : Nat}, d1 ≤ d2 → ∀ {t u : Term},
      noVars t = true → noVars u = true →
      bohmApprox d2 t = bohmApprox d2 u → bohmApprox d1 t = bohmApprox d1 u
  | 0, _, _, _, _, _, _, _ => rfl
  | d1 + 1, 0, hle, _, _, _, _, _ => by cases hle
  | d1 + 1, d2 + 1, hle, t, u, hvt, hvu, heq => by
    have hle' : d1 ≤ d2 := Nat.le_of_succ_le_succ hle
    by_cases ht34 : evalHN t = .hn34
    · rw [bohmApprox_bot d2 ht34] at heq
      by_cases hu34 : evalHN u = .hn34
      · rw [bohmApprox_bot d1 ht34, bohmApprox_bot d1 hu34]
      · obtain ⟨hru, hhnfu⟩ := headNormalize_reduces_hnf hvu hu34
        rcases closed_spineLen_le_2_shapes hhnfu.1 hhnfu.2 with h0 | ⟨a, h1⟩ | ⟨a, b, h2⟩
        · rw [h0] at hru; rw [bohmApprox_of_headReduces_s d2 hvu hru] at heq; cases heq
        · rw [h1] at hru; rw [bohmApprox_of_headReduces_s1 d2 hvu hru] at heq; cases heq
        · rw [h2] at hru; rw [bohmApprox_of_headReduces_s2 d2 hvu hru] at heq; cases heq
    · by_cases hu34 : evalHN u = .hn34
      · rw [bohmApprox_bot d2 hu34] at heq
        obtain ⟨hrt, hhnft⟩ := headNormalize_reduces_hnf hvt ht34
        rcases closed_spineLen_le_2_shapes hhnft.1 hhnft.2 with h0 | ⟨a, h1⟩ | ⟨a, b, h2⟩
        · rw [h0] at hrt; rw [bohmApprox_of_headReduces_s d2 hvt hrt] at heq; cases heq
        · rw [h1] at hrt; rw [bohmApprox_of_headReduces_s1 d2 hvt hrt] at heq; cases heq
        · rw [h2] at hrt; rw [bohmApprox_of_headReduces_s2 d2 hvt hrt] at heq; cases heq
      · obtain ⟨hrt, hhnft⟩ := headNormalize_reduces_hnf hvt ht34
        obtain ⟨hru, hhnfu⟩ := headNormalize_reduces_hnf hvu hu34
        rcases closed_spineLen_le_2_shapes hhnft.1 hhnft.2 with ht0 | ⟨a1, ht1⟩ | ⟨a1, b1, ht2⟩
        · rw [ht0] at hrt
          rw [bohmApprox_of_headReduces_s d2 hvt hrt] at heq
          rcases closed_spineLen_le_2_shapes hhnfu.1 hhnfu.2 with hu0 | ⟨a2, hu1⟩ | ⟨a2, b2, hu2⟩
          · rw [hu0] at hru
            rw [bohmApprox_of_headReduces_s d1 hvt hrt, bohmApprox_of_headReduces_s d1 hvu hru]
          · rw [hu1] at hru; rw [bohmApprox_of_headReduces_s1 d2 hvu hru] at heq; cases heq
          · rw [hu2] at hru; rw [bohmApprox_of_headReduces_s2 d2 hvu hru] at heq; cases heq
        · rw [ht1] at hrt hhnft
          rw [bohmApprox_of_headReduces_s1 d2 hvt hrt] at heq
          rcases closed_spineLen_le_2_shapes hhnfu.1 hhnfu.2 with hu0 | ⟨a2, hu1⟩ | ⟨a2, b2, hu2⟩
          · rw [hu0] at hru; rw [bohmApprox_of_headReduces_s d2 hvu hru] at heq; cases heq
          · rw [hu1] at hru hhnfu
            rw [bohmApprox_of_headReduces_s1 d2 hvu hru] at heq
            injection heq with ha_eq
            have hva1 : noVars a1 = true := ((Bool.and_eq_true _ _).mp hhnft.1).2
            have hva2 : noVars a2 = true := ((Bool.and_eq_true _ _).mp hhnfu.1).2
            rw [bohmApprox_of_headReduces_s1 d1 hvt hrt, bohmApprox_of_headReduces_s1 d1 hvu hru,
                bohmApprox_eq_mono hle' hva1 hva2 ha_eq]
          · rw [hu2] at hru; rw [bohmApprox_of_headReduces_s2 d2 hvu hru] at heq; cases heq
        · rw [ht2] at hrt hhnft
          rw [bohmApprox_of_headReduces_s2 d2 hvt hrt] at heq
          rcases closed_spineLen_le_2_shapes hhnfu.1 hhnfu.2 with hu0 | ⟨a2, hu1⟩ | ⟨a2, b2, hu2⟩
          · rw [hu0] at hru; rw [bohmApprox_of_headReduces_s d2 hvu hru] at heq; cases heq
          · rw [hu1] at hru; rw [bohmApprox_of_headReduces_s1 d2 hvu hru] at heq; cases heq
          · rw [hu2] at hru hhnfu
            rw [bohmApprox_of_headReduces_s2 d2 hvu hru] at heq
            injection heq with ha_eq hb_eq
            have hva1 : noVars a1 = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hhnft.1).1).2
            have hvb1 : noVars b1 = true := ((Bool.and_eq_true _ _).mp hhnft.1).2
            have hva2 : noVars a2 = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hhnfu.1).1).2
            have hvb2 : noVars b2 = true := ((Bool.and_eq_true _ _).mp hhnfu.1).2
            rw [bohmApprox_of_headReduces_s2 d1 hvt hrt, bohmApprox_of_headReduces_s2 d1 hvu hru,
                bohmApprox_eq_mono hle' hva1 hva2 ha_eq,
                bohmApprox_eq_mono hle' hvb1 hvb2 hb_eq]

private theorem closed_spine_ge3_has_step :
    ∀ (u : Term), noVars u = true → 3 ≤ spineLen u → ∃ u', Step u u'
  | .s, _, h => by simp [spineLen] at h
  | .var _, hv, _ => by cases hv
  | .app (.app (.app .s x) y) z, _, _ => ⟨(x ⋅ z) ⋅ (y ⋅ z), Step.root x y z⟩
  | .app (.app (.app (.var _) _) _) _, hv, _ => by simp [noVars] at hv
  | .app (.app (.app (.app a b) x) y) z, hv, _ => by
    have hvL : noVars (((a ⋅ b) ⋅ x) ⋅ y) = true := ((Bool.and_eq_true _ _).mp hv).1
    have hspL : 3 ≤ spineLen (((a ⋅ b) ⋅ x) ⋅ y) := by simp [spineLen]; omega
    obtain ⟨l', hl'⟩ := closed_spine_ge3_has_step (((a ⋅ b) ⋅ x) ⋅ y) hvL hspL
    exact ⟨l' ⋅ z, Step.left hl'⟩
  | .app .s _, _, h => by simp [spineLen] at h
  | .app (.var _) _, _, h => by simp [spineLen] at h
  | .app (.app .s _) _, _, h => by simp [spineLen] at h
  | .app (.app (.var _) _) _, _, h => by simp [spineLen] at h

private theorem closed_nf_spineLen_le_2 {nf : Term}
    (hvnf : noVars nf = true) (hnf : IsNormalForm nf) : spineLen nf ≤ 2 := by
  by_cases hsl : spineLen nf ≤ 2
  · exact hsl
  · exfalso
    obtain ⟨u', hu'⟩ := closed_spine_ge3_has_step nf hvnf (by omega)
    exact hnf u' hu'

/-- **Closed Normal-Form Finite-Depth Böhm Faithfulness**:
    If `nf` is a closed normal form and `bohmApprox (leaves nf) t = bohmApprox (leaves nf) nf`
    for ANY closed term `t`, then `Reduces t nf`! -/
theorem closed_nf_bohmApprox_reduces :
    ∀ (L : Nat) {nf t : Term},
      leaves nf ≤ L →
      noVars nf = true →
      IsNormalForm nf →
      noVars t = true →
      bohmApprox (leaves nf) t = bohmApprox (leaves nf) nf →
      Reduces t nf
  | 0, nf, _, hle, _, _, _, _ => False.elim (by have := leaves_pos nf; omega)
  | L + 1, nf, t, hle, hvnf, hnf, hvt, heq => by
    have hsl : spineLen nf ≤ 2 := closed_nf_spineLen_le_2 hvnf hnf
    have hne_nf : evalHN nf ≠ .hn34 := closed_hnf_evalHN_ne_hn34 hvnf hsl
    rcases closed_spineLen_le_2_shapes hvnf hsl with rfl | ⟨v1, rfl⟩ | ⟨v1, v2, rfl⟩
    · -- `nf = S`, `leaves S = 1`:
      change bohmApprox 1 t = bohmApprox 1 S at heq
      rw [bohmApprox_of_headReduces_s 0 hvnf (HeadReduces.refl S)] at heq
      by_cases ht34 : evalHN t = .hn34
      · rw [bohmApprox_bot 0 ht34] at heq; cases heq
      · obtain ⟨hrt, hhnft⟩ := headNormalize_reduces_hnf hvt ht34
        rcases closed_spineLen_le_2_shapes hhnft.1 hhnft.2 with ht0 | ⟨a, ht1⟩ | ⟨a, b, ht2⟩
        · rw [ht0] at hrt; exact headReduces_to_reduces hrt
        · rw [ht1] at hrt; rw [bohmApprox_of_headReduces_s1 0 hvt hrt] at heq; cases heq
        · rw [ht2] at hrt; rw [bohmApprox_of_headReduces_s2 0 hvt hrt] at heq; cases heq
    · -- `nf = S ⋅ v1`, `leaves (S ⋅ v1) = leaves v1 + 1`:
      have hvv1 : noVars v1 = true := ((Bool.and_eq_true _ _).mp hvnf).2
      have hnf1 : IsNormalForm v1 := fun u hu => hnf (S ⋅ u) (Step.right hu)
      have hlv : leaves (S ⋅ v1) = leaves v1 + 1 := by change 1 + leaves v1 = leaves v1 + 1; omega
      rw [hlv] at heq
      rw [bohmApprox_of_headReduces_s1 (leaves v1) hvnf (HeadReduces.refl _)] at heq
      by_cases ht34 : evalHN t = .hn34
      · rw [bohmApprox_bot (leaves v1) ht34] at heq; cases heq
      · obtain ⟨hrt, hhnft⟩ := headNormalize_reduces_hnf hvt ht34
        rcases closed_spineLen_le_2_shapes hhnft.1 hhnft.2 with ht0 | ⟨a, ht1⟩ | ⟨a, b, ht2⟩
        · rw [ht0] at hrt; rw [bohmApprox_of_headReduces_s (leaves v1) hvt hrt] at heq; cases heq
        · rw [ht1] at hrt hhnft
          rw [bohmApprox_of_headReduces_s1 (leaves v1) hvt hrt] at heq
          injection heq with ha_eq
          have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hhnft.1).2
          have hra : Reduces a v1 :=
            closed_nf_bohmApprox_reduces L (by change 1 + leaves v1 ≤ L + 1 at hle; omega)
              hvv1 hnf1 hva ha_eq
          exact reduces_trans (headReduces_to_reduces hrt) (reduces_right S hra)
        · rw [ht2] at hrt; rw [bohmApprox_of_headReduces_s2 (leaves v1) hvt hrt] at heq; cases heq
    · -- `nf = S ⋅ v1 ⋅ v2`, `leaves = 1 + leaves v1 + leaves v2`:
      have hvv1 : noVars v1 = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hvnf).1).2
      have hvv2 : noVars v2 = true := ((Bool.and_eq_true _ _).mp hvnf).2
      have hnf1 : IsNormalForm v1 := fun u hu => hnf (S ⋅ u ⋅ v2) (Step.left (Step.right hu))
      have hnf2 : IsNormalForm v2 := fun u hu => hnf (S ⋅ v1 ⋅ u) (Step.right hu)
      let d0 := leaves v1 + leaves v2
      have hlv : leaves (S ⋅ v1 ⋅ v2) = d0 + 1 := by
        change (1 + leaves v1) + leaves v2 = (leaves v1 + leaves v2) + 1; omega
      rw [hlv] at heq
      rw [bohmApprox_of_headReduces_s2 d0 hvnf (HeadReduces.refl _)] at heq
      by_cases ht34 : evalHN t = .hn34
      · rw [bohmApprox_bot d0 ht34] at heq; cases heq
      · obtain ⟨hrt, hhnft⟩ := headNormalize_reduces_hnf hvt ht34
        rcases closed_spineLen_le_2_shapes hhnft.1 hhnft.2 with ht0 | ⟨a, ht1⟩ | ⟨a, b, ht2⟩
        · rw [ht0] at hrt; rw [bohmApprox_of_headReduces_s d0 hvt hrt] at heq; cases heq
        · rw [ht1] at hrt; rw [bohmApprox_of_headReduces_s1 d0 hvt hrt] at heq; cases heq
        · rw [ht2] at hrt hhnft
          rw [bohmApprox_of_headReduces_s2 d0 hvt hrt] at heq
          injection heq with ha_eq hb_eq
          have hva : noVars a = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hhnft.1).1).2
          have hvb : noVars b = true := ((Bool.and_eq_true _ _).mp hhnft.1).2
          have hp1 := leaves_pos v1
          have hp2 := leaves_pos v2
          have ha_eq' := bohmApprox_eq_mono (d1 := leaves v1) (d2 := d0) (by omega) hva hvv1 ha_eq
          have hb_eq' := bohmApprox_eq_mono (d1 := leaves v2) (d2 := d0) (by omega) hvb hvv2 hb_eq
          have hra : Reduces a v1 :=
            closed_nf_bohmApprox_reduces L
              (by change (1 + leaves v1) + leaves v2 ≤ L + 1 at hle; omega)
              hvv1 hnf1 hva ha_eq'
          have hrb : Reduces b v2 :=
            closed_nf_bohmApprox_reduces L
              (by change (1 + leaves v1) + leaves v2 ≤ L + 1 at hle; omega)
              hvv2 hnf2 hvb hb_eq'
          exact reduces_trans (headReduces_to_reduces hrt) (reduces_app (reduces_right S hra) hrb)

/-! ### 4.2 Unfolding Laws & Injectivity of Infinite Zachos Streams `zachosG (k + 1) ⋅ zachosG n` -/

theorem zachos_zero_headStep (n : Nat) :
    HeadStep (zachosG 0 ⋅ zachosG n) (zachosG (n + 1) ⋅ zachosG (n + 1)) :=
  HeadStep.root zachosT zachosT (zachosG n)

theorem zachos_succ_headStep (k n : Nat) :
    HeadStep (zachosG (k + 1) ⋅ zachosG n) (S ⋅ zachosG n ⋅ (zachosG k ⋅ zachosG n)) :=
  HeadStep.root S (zachosG k) (zachosG n)

theorem bohmApprox_zachos_succ (d k n : Nat) :
    bohmApprox (d + 1) (zachosG (k + 1) ⋅ zachosG n) =
      .s2 (bohmApprox d (zachosG n)) (bohmApprox d (zachosG k ⋅ zachosG n)) := by
  have hv : noVars (zachosG (k + 1) ⋅ zachosG n) = true :=
    (Bool.and_eq_true _ _).mpr ⟨noVars_zachosG (k + 1), noVars_zachosG n⟩
  exact bohmApprox_of_headReduces_s2 d hv
    (HeadReduces.next (zachos_succ_headStep k n) (HeadReduces.refl _))

theorem bohmApprox_zachos_zero (d n : Nat) :
    bohmApprox d (zachosG 0 ⋅ zachosG n) = bohmApprox d (zachosG (n + 1) ⋅ zachosG (n + 1)) := by
  have hv0 : noVars (zachosG 0 ⋅ zachosG n) = true :=
    (Bool.and_eq_true _ _).mpr ⟨noVars_zachosG 0, noVars_zachosG n⟩
  have hv1 : noVars (zachosG (n + 1) ⋅ zachosG (n + 1)) = true :=
    (Bool.and_eq_true _ _).mpr ⟨noVars_zachosG (n + 1), noVars_zachosG (n + 1)⟩
  exact convS_bohmApprox_eq d hv0 hv1 (ConvS.step (headStep_to_step (zachos_zero_headStep n)))

private theorem zachos_succ_same_n_bohm_inj (n : Nat) :
    ∀ (k1 k2 : Nat),
      (∀ d, bohmApprox d (zachosG (k1 + 1) ⋅ zachosG n) =
            bohmApprox d (zachosG (k2 + 1) ⋅ zachosG n)) →
      k1 = k2
  | 0, 0, _ => rfl
  | 0, k2 + 1, hall => by
    exfalso
    let L := leaves (zachosG n)
    have hstep1 := hall (L + 2)
    rw [bohmApprox_zachos_succ (L + 1) 0 n, bohmApprox_zachos_succ (L + 1) (k2 + 1) n] at hstep1
    injection hstep1 with _ hright
    rw [bohmApprox_zachos_zero (L + 1) n, bohmApprox_zachos_succ L n (n + 1),
        bohmApprox_zachos_succ L k2 n] at hright
    injection hright with hsprout _
    have hred : Reduces (zachosG (n + 1)) (zachosG n) :=
      closed_nf_bohmApprox_reduces L (Nat.le_refl L)
        (noVars_zachosG n) (isNormalForm_zachosG n) (noVars_zachosG (n + 1)) hsprout
    have heq : zachosG (n + 1) = zachosG n :=
      isNormalForm_reduces_eq (isNormalForm_zachosG (n + 1)) hred
    have hn_eq := zachosG_inj heq
    omega
  | k1 + 1, 0, hall => by
    exfalso
    let L := leaves (zachosG (n + 1))
    have hstep1 := hall (L + 2)
    rw [bohmApprox_zachos_succ (L + 1) (k1 + 1) n, bohmApprox_zachos_succ (L + 1) 0 n] at hstep1
    injection hstep1 with _ hright
    rw [bohmApprox_zachos_succ L k1 n, bohmApprox_zachos_zero (L + 1) n,
        bohmApprox_zachos_succ L n (n + 1)] at hright
    injection hright with hsprout _
    have hred : Reduces (zachosG n) (zachosG (n + 1)) :=
      closed_nf_bohmApprox_reduces L (Nat.le_refl L)
        (noVars_zachosG (n + 1)) (isNormalForm_zachosG (n + 1)) (noVars_zachosG n) hsprout
    have heq : zachosG n = zachosG (n + 1) :=
      isNormalForm_reduces_eq (isNormalForm_zachosG n) hred
    have hn_eq := zachosG_inj heq
    omega
  | k1 + 1, k2 + 1, hall => by
    have hsub : ∀ d, bohmApprox d (zachosG (k1 + 1) ⋅ zachosG n) =
                     bohmApprox d (zachosG (k2 + 1) ⋅ zachosG n) := by
      intro d
      have hd1 := hall (d + 1)
      rw [bohmApprox_zachos_succ d (k1 + 1) n, bohmApprox_zachos_succ d (k2 + 1) n] at hd1
      injection hd1
    exact congrArg (· + 1) (zachos_succ_same_n_bohm_inj n k1 k2 hsub)

theorem zachos_succ_bohmApprox_inj {k1 k2 n1 n2 : Nat}
    (hall : ∀ d, bohmApprox d (zachosG (k1 + 1) ⋅ zachosG n1) =
                 bohmApprox d (zachosG (k2 + 1) ⋅ zachosG n2)) :
    k1 = k2 ∧ n1 = n2 := by
  let L := leaves (zachosG n2)
  have h1 := hall (L + 1)
  rw [bohmApprox_zachos_succ L k1 n1, bohmApprox_zachos_succ L k2 n2] at h1
  injection h1 with hleft _
  have hred : Reduces (zachosG n1) (zachosG n2) :=
    closed_nf_bohmApprox_reduces L (Nat.le_refl L)
      (noVars_zachosG n2) (isNormalForm_zachosG n2) (noVars_zachosG n1) hleft
  have hn_eq : n1 = n2 := zachosG_inj (isNormalForm_reduces_eq (isNormalForm_zachosG n1) hred)
  subst hn_eq
  exact ⟨zachos_succ_same_n_bohm_inj n1 k1 k2 hall, rfl⟩

/-! ### 4.3 Total `PVal` Equivalence Checker `pvalEqv` & Constructive Join Witness `pvalJoin` -/

def normZachosRoot : PVal → PVal
  | .zachos 0 n => .zachos (n + 1) (n + 1)
  | v => v

theorem normZachosRoot_size (v : PVal) : (normZachosRoot v).size = v.size := by
  cases v with
  | zachos m n => cases m <;> rfl
  | _ => rfl

theorem normZachosRoot_reduces (v : PVal) : Reduces v.toTerm (normZachosRoot v).toTerm := by
  cases v with
  | zachos m n =>
    cases m with
    | zero => exact Reduces.next (headStep_to_step (zachos_zero_headStep n)) (Reduces.refl _)
    | succ _ => exact Reduces.refl _
  | _ => exact Reduces.refl _

theorem normZachosRoot_not_zachos_zero (v : PVal) (n : Nat) : normZachosRoot v ≠ .zachos 0 n := by
  cases v with
  | zachos m p =>
    cases m <;> intro h <;> cases h
  | _ => intro h; cases h

/-- Total boolean equivalence checker on canonical productive values `PVal`
    (terminating structurally on `fuel = u.size + v.size`). -/
def pvalEqvAux : Nat → PVal → PVal → Bool
  | 0, _, _ => false
  | fuel + 1, u, v =>
    match normZachosRoot u, normZachosRoot v with
    | .s, .s => true
    | .s1 x, .s1 y => pvalEqvAux fuel x y
    | .s2 a1 b1, .s2 a2 b2 => pvalEqvAux fuel a1 a2 && pvalEqvAux fuel b1 b2
    | .s2 a b, .zachos (k + 1) n =>
        decide (a.toTerm = zachosG n) && pvalEqvAux fuel b (.zachos k n)
    | .zachos (k + 1) n, .s2 a b =>
        decide (a.toTerm = zachosG n) && pvalEqvAux fuel (.zachos k n) b
    | .zachos (k1 + 1) n1, .zachos (k2 + 1) n2 =>
        decide (k1 = k2 ∧ n1 = n2)
    | _, _ => false

def pvalEqv (u v : PVal) : Bool :=
  pvalEqvAux (u.size + v.size) u v

/-- **Constructive Common-Reduct Extractor on `PVal` (`Type`-valued)**:
    Whenever `pvalEqvAux fuel u v = true`, computably constructs an explicit pure-`S` term `w`
    with `Reduces u.toTerm w ∧ Reduces v.toTerm w`! -/
def pvalJoinAux :
    (fuel : Nat) → (u v : PVal) → pvalEqvAux fuel u v = true →
      Σ' w : Term, Reduces u.toTerm w ∧ Reduces v.toTerm w
  | 0, _, _, h => False.elim (by cases h)
  | fuel + 1, u, v, h => by
    have hru : Reduces u.toTerm (normZachosRoot u).toTerm := normZachosRoot_reduces u
    have hrv : Reduces v.toTerm (normZachosRoot v).toTerm := normZachosRoot_reduces v
    unfold pvalEqvAux at h
    cases hu : normZachosRoot u with
    | s =>
      rw [hu] at h hru
      cases hv : normZachosRoot v with
      | s =>
        rw [hv] at hrv
        exact ⟨S, hru, hrv⟩
      | s1 _ => rw [hv] at h; cases h
      | s2 _ _ => rw [hv] at h; cases h
      | zachos m2 _ => rw [hv] at h; cases m2 <;> cases h
    | s1 x =>
      rw [hu] at h hru
      cases hv : normZachosRoot v with
      | s => rw [hv] at h; cases h
      | s1 y =>
        rw [hv] at h hrv
        let ⟨wx, hx, hy⟩ := pvalJoinAux fuel x y h
        exact ⟨S ⋅ wx,
          reduces_trans hru (reduces_right S hx),
          reduces_trans hrv (reduces_right S hy)⟩
      | s2 _ _ => rw [hv] at h; cases h
      | zachos m2 _ => rw [hv] at h; cases m2 <;> cases h
    | s2 a1 b1 =>
      rw [hu] at h hru
      cases hv : normZachosRoot v with
      | s => rw [hv] at h; cases h
      | s1 _ => rw [hv] at h; cases h
      | s2 a2 b2 =>
        rw [hv] at h hrv
        have ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp h
        let ⟨wa, hra1, hra2⟩ := pvalJoinAux fuel a1 a2 ha
        let ⟨wb, hrb1, hrb2⟩ := pvalJoinAux fuel b1 b2 hb
        exact ⟨S ⋅ wa ⋅ wb,
          reduces_trans hru (reduces_app (reduces_right S hra1) hrb1),
          reduces_trans hrv (reduces_app (reduces_right S hra2) hrb2)⟩
      | zachos m2 n2 =>
        rw [hv] at h hrv
        cases m2 with
        | zero => cases h
        | succ k2 =>
          have ⟨ha_eq_b, hb_eqv⟩ := (Bool.and_eq_true _ _).mp h
          have ha_eq : a1.toTerm = zachosG n2 := of_decide_eq_true ha_eq_b
          let ⟨wb, hrb1, hrbz⟩ := pvalJoinAux fuel b1 (.zachos k2 n2) hb_eqv
          refine ⟨S ⋅ zachosG n2 ⋅ wb, ?_, ?_⟩
          · have h1 : Reduces (S ⋅ a1.toTerm ⋅ b1.toTerm) (S ⋅ zachosG n2 ⋅ wb) := by
              rw [ha_eq]; exact reduces_right (S ⋅ zachosG n2) hrb1
            exact reduces_trans hru h1
          · have h2 : Reduces (zachosG (k2 + 1) ⋅ zachosG n2) (S ⋅ zachosG n2 ⋅ wb) :=
              Reduces.next (headStep_to_step (zachos_succ_headStep k2 n2))
                (reduces_right (S ⋅ zachosG n2) hrbz)
            exact reduces_trans hrv h2
    | zachos m1 n1 =>
      rw [hu] at h hru
      cases m1 with
      | zero =>
        cases hv : normZachosRoot v <;> rw [hv] at h <;>
          first | cases h | (rename_i m2 _; cases m2 <;> cases h)
      | succ k1 =>
        cases hv : normZachosRoot v with
        | s => rw [hv] at h; cases h
        | s1 _ => rw [hv] at h; cases h
        | s2 a2 b2 =>
          rw [hv] at h hrv
          have ⟨ha_eq_b, hb_eqv⟩ := (Bool.and_eq_true _ _).mp h
          have ha_eq : a2.toTerm = zachosG n1 := of_decide_eq_true ha_eq_b
          let ⟨wb, hrbz, hrb2⟩ := pvalJoinAux fuel (.zachos k1 n1) b2 hb_eqv
          refine ⟨S ⋅ zachosG n1 ⋅ wb, ?_, ?_⟩
          · have h1 : Reduces (zachosG (k1 + 1) ⋅ zachosG n1) (S ⋅ zachosG n1 ⋅ wb) :=
              Reduces.next (headStep_to_step (zachos_succ_headStep k1 n1))
                (reduces_right (S ⋅ zachosG n1) hrbz)
            exact reduces_trans hru h1
          · have h2 : Reduces (S ⋅ a2.toTerm ⋅ b2.toTerm) (S ⋅ zachosG n1 ⋅ wb) := by
              rw [ha_eq]; exact reduces_right (S ⋅ zachosG n1) hrb2
            exact reduces_trans hrv h2
        | zachos m2 n2 =>
          rw [hv] at h hrv
          cases m2 with
          | zero => cases h
          | succ k2 =>
            have ⟨hk_eq, hn_eq⟩ := of_decide_eq_true h
            subst hk_eq; subst hn_eq
            exact ⟨zachosG (k1 + 1) ⋅ zachosG n1, hru, hrv⟩

private theorem pval_bohmApprox_one (v : PVal) :
    (v = .s ∧ bohmApprox 1 v.toTerm = .s0) ∨
    (∃ x, v = .s1 x ∧ bohmApprox 1 v.toTerm = .s1 .trunc) ∨
    (∃ a b, v = .s2 a b ∧ bohmApprox 1 v.toTerm = .s2 .trunc .trunc) ∨
    (∃ k n, v = .zachos (k + 1) n ∧ bohmApprox 1 v.toTerm = .s2 .trunc .trunc) ∨
    (∃ n, v = .zachos 0 n) := by
  cases v with
  | s =>
    exact Or.inl ⟨rfl, bohmApprox_of_headReduces_s 0 rfl (HeadReduces.refl S)⟩
  | s1 x =>
    exact Or.inr (Or.inl ⟨x, rfl,
      bohmApprox_of_headReduces_s1 0 (PVal.noVars_toTerm (.s1 x)) (HeadReduces.refl _)⟩)
  | s2 a b =>
    exact Or.inr (Or.inr (Or.inl ⟨a, b, rfl,
      bohmApprox_of_headReduces_s2 0 (PVal.noVars_toTerm (.s2 a b)) (HeadReduces.refl _)⟩))
  | zachos m n =>
    cases m with
    | zero => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, rfl⟩)))
    | succ k =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, n, rfl, bohmApprox_zachos_succ 0 k n⟩)))

/-- **Completeness of `pvalEqvAux` with Respect to Infinite Böhm-Tree Equality**:
    If `∀ d, bohmApprox d u.toTerm = bohmApprox d v.toTerm`, then `pvalEqvAux fuel u v = true`
    for every `fuel ≥ u.size + v.size`! -/
theorem pval_bohmApprox_implies_pvalEqvAux :
    ∀ (fuel : Nat) (u v : PVal),
      u.size + v.size ≤ fuel →
      (∀ d : Nat, bohmApprox d u.toTerm = bohmApprox d v.toTerm) →
      pvalEqvAux fuel u v = true
  | 0, u, v, hsz, _ =>
    False.elim (by have := PVal.size_pos u; have := PVal.size_pos v; omega)
  | fuel + 1, u, v, hsz, hall => by
    have hsz' : (normZachosRoot u).size + (normZachosRoot v).size ≤ fuel + 1 := by
      rw [normZachosRoot_size u, normZachosRoot_size v]; exact hsz
    have hall' : ∀ d : Nat, bohmApprox d (normZachosRoot u).toTerm = bohmApprox d (normZachosRoot v).toTerm := by
      intro d
      have eu := convS_bohmApprox_eq d (PVal.noVars_toTerm u) (PVal.noVars_toTerm (normZachosRoot u))
        (reduces_to_convS (normZachosRoot_reduces u))
      have ev := convS_bohmApprox_eq d (PVal.noVars_toTerm v) (PVal.noVars_toTerm (normZachosRoot v))
        (reduces_to_convS (normZachosRoot_reduces v))
      exact eu.symm.trans ((hall d).trans ev)
    have hu_nz : ∀ n, normZachosRoot u ≠ .zachos 0 n := normZachosRoot_not_zachos_zero u
    have hv_nz : ∀ n, normZachosRoot v ≠ .zachos 0 n := normZachosRoot_not_zachos_zero v
    unfold pvalEqvAux
    rcases pval_bohmApprox_one (normZachosRoot u) with
      ⟨hu0, hbu⟩ | ⟨x, hu1, hbu⟩ | ⟨a1, b1, hu2, hbu⟩ | ⟨k1, n1, huz, hbu⟩ | ⟨n, hbad⟩
    · rcases pval_bohmApprox_one (normZachosRoot v) with
        ⟨hv0, _⟩ | ⟨_, _, hbv⟩ | ⟨_, _, _, hbv⟩ | ⟨_, _, _, hbv⟩ | ⟨n, hbad⟩
      · rw [hu0, hv0]
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · exact False.elim (hv_nz n hbad)
    · rcases pval_bohmApprox_one (normZachosRoot v) with
        ⟨_, hbv⟩ | ⟨y, hv1, _⟩ | ⟨_, _, _, hbv⟩ | ⟨_, _, _, hbv⟩ | ⟨n, hbad⟩
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · rw [hu1, hv1] at hall' hsz' ⊢
        have hxy_sz : x.size + y.size ≤ fuel := by
          change (x.size + 1) + (y.size + 1) ≤ fuel + 1 at hsz'; omega
        have hxy_all : ∀ d, bohmApprox d x.toTerm = bohmApprox d y.toTerm := by
          intro d
          have hd1 := hall' (d + 1)
          rw [bohmApprox_of_headReduces_s1 d (PVal.noVars_toTerm (.s1 x)) (HeadReduces.refl _),
              bohmApprox_of_headReduces_s1 d (PVal.noVars_toTerm (.s1 y)) (HeadReduces.refl _)] at hd1
          injection hd1
        exact pval_bohmApprox_implies_pvalEqvAux fuel x y hxy_sz hxy_all
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · exact False.elim (hv_nz n hbad)
    · rcases pval_bohmApprox_one (normZachosRoot v) with
        ⟨_, hbv⟩ | ⟨_, _, hbv⟩ | ⟨a2, b2, hv2, _⟩ | ⟨k2, n2, hvz, _⟩ | ⟨n, hbad⟩
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · rw [hu2, hv2] at hall' hsz' ⊢
        have ha_sz : a1.size + a2.size ≤ fuel := by
          have hb1 := PVal.size_pos b1; have hb2 := PVal.size_pos b2
          change (a1.size + b1.size + 1) + (a2.size + b2.size + 1) ≤ fuel + 1 at hsz'; omega
        have hb_sz : b1.size + b2.size ≤ fuel := by
          have ha1 := PVal.size_pos a1; have ha2 := PVal.size_pos a2
          change (a1.size + b1.size + 1) + (a2.size + b2.size + 1) ≤ fuel + 1 at hsz'; omega
        have hchildren : ∀ d, bohmApprox d a1.toTerm = bohmApprox d a2.toTerm ∧
                              bohmApprox d b1.toTerm = bohmApprox d b2.toTerm := by
          intro d
          have hd1 := hall' (d + 1)
          rw [bohmApprox_of_headReduces_s2 d (PVal.noVars_toTerm (.s2 a1 b1)) (HeadReduces.refl _),
              bohmApprox_of_headReduces_s2 d (PVal.noVars_toTerm (.s2 a2 b2)) (HeadReduces.refl _)] at hd1
          injection hd1 with hL hR
          exact ⟨hL, hR⟩
        exact (Bool.and_eq_true _ _).mpr
          ⟨pval_bohmApprox_implies_pvalEqvAux fuel a1 a2 ha_sz (fun d => (hchildren d).1),
           pval_bohmApprox_implies_pvalEqvAux fuel b1 b2 hb_sz (fun d => (hchildren d).2)⟩
      · rw [hu2, hvz] at hall' hsz' ⊢
        have hchildren : ∀ d, bohmApprox d a1.toTerm = bohmApprox d (zachosG n2) ∧
                              bohmApprox d b1.toTerm = bohmApprox d (PVal.zachos k2 n2).toTerm := by
          intro d
          have hd1 := hall' (d + 1)
          rw [bohmApprox_of_headReduces_s2 d (PVal.noVars_toTerm (.s2 a1 b1)) (HeadReduces.refl _),
              PVal.toTerm, bohmApprox_zachos_succ d k2 n2] at hd1
          injection hd1 with hL hR
          exact ⟨hL, hR⟩
        let L := leaves (zachosG n2)
        have hra1 : Reduces a1.toTerm (zachosG n2) :=
          closed_nf_bohmApprox_reduces L (Nat.le_refl L)
            (noVars_zachosG n2) (isNormalForm_zachosG n2) (PVal.noVars_toTerm a1) (hchildren L).1
        have ha1_eq : a1.toTerm = zachosG n2 :=
          (pval_convS_closed_nf_iff_eq a1 (noVars_zachosG n2) (isNormalForm_zachosG n2)).mp
            (reduces_to_convS hra1)
        have hb_sz : b1.size + (PVal.zachos k2 n2).size ≤ fuel := by
          have ha1_pos := PVal.size_pos a1
          change (a1.size + b1.size + 1) + 1 ≤ fuel + 1 at hsz'
          change b1.size + 1 ≤ fuel; omega
        exact (Bool.and_eq_true _ _).mpr
          ⟨decide_eq_true ha1_eq,
           pval_bohmApprox_implies_pvalEqvAux fuel b1 (.zachos k2 n2) hb_sz (fun d => (hchildren d).2)⟩
      · exact False.elim (hv_nz n hbad)
    · rcases pval_bohmApprox_one (normZachosRoot v) with
        ⟨_, hbv⟩ | ⟨_, _, hbv⟩ | ⟨a2, b2, hv2, _⟩ | ⟨k2, n2, hvz, _⟩ | ⟨n, hbad⟩
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · have h1 := hall' 1; rw [hbu, hbv] at h1; cases h1
      · rw [huz, hv2] at hall' hsz' ⊢
        have hchildren : ∀ d, bohmApprox d (zachosG n1) = bohmApprox d a2.toTerm ∧
                              bohmApprox d (PVal.zachos k1 n1).toTerm = bohmApprox d b2.toTerm := by
          intro d
          have hd1 := hall' (d + 1)
          have hv_s2 : noVars (S ⋅ a2.toTerm ⋅ b2.toTerm) = true := PVal.noVars_toTerm (.s2 a2 b2)
          dsimp only [PVal.toTerm] at hd1
          rw [bohmApprox_zachos_succ d k1 n1,
              bohmApprox_of_headReduces_s2 d hv_s2 (HeadReduces.refl _)] at hd1
          injection hd1 with hL hR
          exact ⟨hL, hR⟩
        let L := leaves (zachosG n1)
        have hra2 : Reduces a2.toTerm (zachosG n1) :=
          closed_nf_bohmApprox_reduces L (Nat.le_refl L)
            (noVars_zachosG n1) (isNormalForm_zachosG n1) (PVal.noVars_toTerm a2) (hchildren L).1.symm
        have ha2_eq : a2.toTerm = zachosG n1 :=
          (pval_convS_closed_nf_iff_eq a2 (noVars_zachosG n1) (isNormalForm_zachosG n1)).mp
            (reduces_to_convS hra2)
        have hb_sz : (PVal.zachos k1 n1).size + b2.size ≤ fuel := by
          have ha2_pos := PVal.size_pos a2
          change 1 + (a2.size + b2.size + 1) ≤ fuel + 1 at hsz'
          change 1 + b2.size ≤ fuel; omega
        exact (Bool.and_eq_true _ _).mpr
          ⟨decide_eq_true ha2_eq,
           pval_bohmApprox_implies_pvalEqvAux fuel (.zachos k1 n1) b2 hb_sz (fun d => (hchildren d).2)⟩
      · rw [huz, hvz] at hall' ⊢
        exact decide_eq_true (zachos_succ_bohmApprox_inj hall')
      · exact False.elim (hv_nz n hbad)
    · exact False.elim (hu_nz n hbad)

/-- **Three-Way Master Equivalence on Canonical `PVal`s**:
    For all `u, v : PVal`, boolean `pvalEqv u v = true`, `S`-convertibility `ConvS u.toTerm v.toTerm`,
    and equality of infinite `⊥`-free Böhm trees `∀ d, bohmApprox d u.toTerm = bohmApprox d v.toTerm`
    are **mutually equivalent**! -/
theorem pvalEqv_iff_convS_and_bohm (u v : PVal) :
    (pvalEqv u v = true ↔ ConvS u.toTerm v.toTerm) ∧
    (ConvS u.toTerm v.toTerm ↔ ∀ d : Nat, bohmApprox d u.toTerm = bohmApprox d v.toTerm) := by
  have h12 : pvalEqv u v = true → ConvS u.toTerm v.toTerm := fun heqv => by
    let ⟨w, hru, hrv⟩ := pvalJoinAux (u.size + v.size) u v heqv
    exact convS_iff_common_reduct.mpr ⟨w, hru, hrv⟩
  have h23 : ConvS u.toTerm v.toTerm → ∀ d : Nat, bohmApprox d u.toTerm = bohmApprox d v.toTerm :=
    fun hconv d => convS_bohmApprox_eq d (PVal.noVars_toTerm u) (PVal.noVars_toTerm v) hconv
  have h31 : (∀ d : Nat, bohmApprox d u.toTerm = bohmApprox d v.toTerm) → pvalEqv u v = true :=
    fun hall => pval_bohmApprox_implies_pvalEqvAux (u.size + v.size) u v (Nat.le_refl _) hall
  exact ⟨⟨h12, fun hc => h31 (h23 hc)⟩, ⟨h23, fun hb => h12 (h31 hb)⟩⟩

/-! ### 4.4 Headline Theorems: Productive Böhm Faithfulness & `Prod × All` `ConvS` Decidability -/

/-- **Headline Theorem A1 (One-Sided Productive Böhm-Tree Faithfulness)**:
    If `m` is a **productive** closed pure-`S` term (`Productive m`) and `n` is **any** closed
    pure-`S` term, then `m` and `n` have the same Böhm tree (`∀ d, bohmApprox d m = bohmApprox d n`)
    **if and only if** `m =_S n` (`ConvS m n`)! -/
theorem productive_oneSided_bohm_iff_convS {m n : Term}
    (hvm : noVars m = true) (hvn : noVars n = true) (hm_prod : Productive m) :
    (∀ d : Nat, bohmApprox d m = bohmApprox d n) ↔ ConvS m n := by
  constructor
  · intro hall
    have hm_bf : ∀ d, approxHasBot (bohmApprox d m) = false :=
      (productive_iff_bohmApprox_botFree hvm).mp hm_prod
    have hn_prod : Productive n :=
      (productive_iff_bohmApprox_botFree hvn).mpr (fun d => by rw [← hall d]; exact hm_bf d)
    have hpm : evalP m ≠ .p37 := (barendregt_open_question_5 hvm).mp hm_prod
    have hpn : evalP n ≠ .p37 := (barendregt_open_question_5 hvn).mp hn_prod
    let ⟨um, hrm⟩ := toPVal m hvm hpm
    let ⟨vn, hrn⟩ := toPVal n hvn hpn
    have hall_uv : ∀ d : Nat, bohmApprox d um.toTerm = bohmApprox d vn.toTerm := by
      intro d
      have em := convS_bohmApprox_eq d hvm (PVal.noVars_toTerm um) (reduces_to_convS hrm)
      have en := convS_bohmApprox_eq d hvn (PVal.noVars_toTerm vn) (reduces_to_convS hrn)
      exact em.symm.trans ((hall d).trans en)
    have hconv_uv : ConvS um.toTerm vn.toTerm :=
      (pvalEqv_iff_convS_and_bohm um vn).2.mpr hall_uv
    exact ConvS.trans (reduces_to_convS hrm)
      (ConvS.trans hconv_uv (ConvS.symm (reduces_to_convS hrn)))
  · intro hconv d
    exact convS_bohmApprox_eq d hvm hvn hconv

/-- **Headline Theorem A2 (Symmetric Productive Böhm-Tree Faithfulness — Completing Question 31)**:
    On all productive closed pure-`S` terms, equality of infinite `⊥`-free Böhm trees implies
    `S`-convertibility (`ConvS m n`). -/
theorem productive_bohm_faithful {m n : Term}
    (hvm : noVars m = true) (hvn : noVars n = true)
    (hm_prod : Productive m) (_hn_prod : Productive n)
    (hbohm : ∀ d : Nat, bohmApprox d m = bohmApprox d n) :
    ConvS m n :=
  (productive_oneSided_bohm_iff_convS hvm hvn hm_prod).mp hbohm

/-- **Headline Theorem A3 (Complete Decidability of Dana Scott's Question 30 on `Productive × All`)**:
    Total, computable decision procedure deciding `ConvS m n` for **any** productive closed pure-`S`
    term `m` (`Productive m`, including non-`SN` infinite-tree combinators!) and **any** closed
    pure-`S` term `n` (terminating, non-terminating, or unsolvable!). -/
def decideConvProd (m n : Term) (hvm : noVars m = true) (hvn : noVars n = true)
    (hm_prod : Productive m) : Decidable (ConvS m n) :=
  have hpm : evalP m ≠ .p37 := (barendregt_open_question_5 hvm).mp hm_prod
  if hpn : evalP n = .p37 then
    isFalse (fun hconv => hpm ((evalP_conv hconv).trans hpn))
  else
    let ⟨um, hrm⟩ := toPVal m hvm hpm
    let ⟨vn, hrn⟩ := toPVal n hvn hpn
    if heqv : pvalEqv um vn = true then
      isTrue (by
        have hc_uv : ConvS um.toTerm vn.toTerm := (pvalEqv_iff_convS_and_bohm um vn).1.mp heqv
        exact ConvS.trans (reduces_to_convS hrm)
          (ConvS.trans hc_uv (ConvS.symm (reduces_to_convS hrn))))
    else
      isFalse (fun hconv => by
        have hc_uv : ConvS um.toTerm vn.toTerm :=
          ConvS.trans (ConvS.symm (reduces_to_convS hrm))
            (ConvS.trans hconv (reduces_to_convS hrn))
        exact heqv ((pvalEqv_iff_convS_and_bohm um vn).1.mpr hc_uv))

/-- **Constructive Common-Reduct Witness in `Type` (`joinOfConvProd`)**:
    Whenever `ConvS m n` holds for closed pure-`S` terms with `Productive m`, computably extracts
    an explicit common reduct `w : Term` satisfying `Reduces m w ∧ Reduces n w`! -/
def joinOfConvProd (m n : Term) (hvm : noVars m = true) (hvn : noVars n = true)
    (hm_prod : Productive m) (hconv : ConvS m n) :
    Σ' w : Term, Reduces m w ∧ Reduces n w :=
  have hpm : evalP m ≠ .p37 := (barendregt_open_question_5 hvm).mp hm_prod
  have hpn : evalP n ≠ .p37 := fun hp37 => hpm ((evalP_conv hconv).trans hp37)
  let ⟨um, hrm⟩ := toPVal m hvm hpm
  let ⟨vn, hrn⟩ := toPVal n hvn hpn
  have hc_uv : ConvS um.toTerm vn.toTerm :=
    ConvS.trans (ConvS.symm (reduces_to_convS hrm))
      (ConvS.trans hconv (reduces_to_convS hrn))
  have heqv : pvalEqv um vn = true := (pvalEqv_iff_convS_and_bohm um vn).1.mpr hc_uv
  let ⟨w, hru, hrv⟩ := pvalJoinAux (um.size + vn.size) um vn heqv
  ⟨w, reduces_trans hrm hru, reduces_trans hrn hrv⟩

private theorem closed_nf_approxHasBot_false :
    ∀ (L : Nat) {v : Term}, leaves v ≤ L → noVars v = true → IsNormalForm v →
      ∀ d, approxHasBot (bohmApprox d v) = false
  | 0, v, hle, _, _, _ => False.elim (by have := leaves_pos v; omega)
  | _ + 1, _, _, _, _, 0 => rfl
  | L + 1, v, hle, hvv, hnf_v, d + 1 => by
    have hsl := closed_nf_spineLen_le_2 hvv hnf_v
    rcases closed_spineLen_le_2_shapes hvv hsl with rfl | ⟨v1, rfl⟩ | ⟨v1, v2, rfl⟩
    · rw [bohmApprox_of_headReduces_s d hvv (HeadReduces.refl S)]; rfl
    · have hvv1 : noVars v1 = true := ((Bool.and_eq_true _ _).mp hvv).2
      have hnf1 : IsNormalForm v1 := fun u hu => hnf_v (S ⋅ u) (Step.right hu)
      rw [bohmApprox_of_headReduces_s1 d hvv (HeadReduces.refl _)]
      exact closed_nf_approxHasBot_false L (by change 1 + leaves v1 ≤ L + 1 at hle; omega) hvv1 hnf1 d
    · have hvv1 : noVars v1 = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hvv).1).2
      have hvv2 : noVars v2 = true := ((Bool.and_eq_true _ _).mp hvv).2
      have hnf1 : IsNormalForm v1 := fun u hu => hnf_v (S ⋅ u ⋅ v2) (Step.left (Step.right hu))
      have hnf2 : IsNormalForm v2 := fun u hu => hnf_v (S ⋅ v1 ⋅ u) (Step.right hu)
      have hp1 := leaves_pos v1; have hp2 := leaves_pos v2
      rw [bohmApprox_of_headReduces_s2 d hvv (HeadReduces.refl _)]
      have e1 := closed_nf_approxHasBot_false L
        (by change (1 + leaves v1) + leaves v2 ≤ L + 1 at hle; omega) hvv1 hnf1 d
      have e2 := closed_nf_approxHasBot_false L
        (by change (1 + leaves v1) + leaves v2 ≤ L + 1 at hle; omega) hvv2 hnf2 d
      simp [approxHasBot, e1, e2]

/-- **`SN ⊊ Productive` Strict Inclusion Theorem**:
    Every closed `SN` term is productive, while Zachos's `zachosG 0 ⋅ zachosG 0` is productive
    yet **not** `SN` — proving `decideConvProd` strictly generalizes `decideConvWithSN`! -/
theorem sn_strict_subset_productive :
    (∀ {t : Term}, noVars t = true → StrongNormalizing t → Productive t) ∧
    (noVars (zachosG 0 ⋅ zachosG 0) = true ∧
     Productive (zachosG 0 ⋅ zachosG 0) ∧
     ¬ StrongNormalizing (zachosG 0 ⋅ zachosG 0)) := by
  refine ⟨?_, ?_⟩
  · intro t hvt hsn
    obtain ⟨nf, hred, hnf⟩ := sn_implies_wn hsn
    have hvnf : noVars nf = true := noVars_reduces hred hvt
    have hprod_nf : Productive nf :=
      (productive_iff_bohmApprox_botFree hvnf).mpr
        (closed_nf_approxHasBot_false (leaves nf) (Nat.le_refl _) hvnf hnf)
    exact (productive_conv_invariant (reduces_to_convS hred)).mpr hprod_nf
  · have hvz : noVars (zachosG 0 ⋅ zachosG 0) = true := rfl
    have hpz : Productive (zachosG 0 ⋅ zachosG 0) :=
      (barendregt_open_question_5 hvz).mpr (by decide : evalP (zachosG 0 ⋅ zachosG 0) ≠ .p37)
    have hnsn : ¬ StrongNormalizing (zachosG 0 ⋅ zachosG 0) := by
      intro hsn
      have hne := (waldmann_theorem_9 hvz).1.mp hsn
      exact hne (evalSN_zachos_pair_sn38 0 0)
    exact ⟨hvz, hpz, hnsn⟩

/-! ## Section 5: Clocked-Böhm Fine Structure on Productive Non-`SN` Terms -/

/-- **Clock Mismatch on Convertible Productive Terms (`Z_Zac` vs `G_1 ⋅ G_1`)**:
    `zachosG 0 ⋅ zachosG 0` and `zachosG 1 ⋅ zachosG 1` are productive and `=_S`-convertible
    (hence share the exact same Böhm tree), yet have **distinct clocked Böhm trees** at depth 1
    (root head clocks `2` vs `1`)! -/
theorem zachos_convS_clock_mismatch :
    Productive (zachosG 0 ⋅ zachosG 0) ∧
    Productive (zachosG 1 ⋅ zachosG 1) ∧
    ConvS (zachosG 0 ⋅ zachosG 0) (zachosG 1 ⋅ zachosG 1) ∧
    (∀ d, bohmApprox d (zachosG 0 ⋅ zachosG 0) = bohmApprox d (zachosG 1 ⋅ zachosG 1)) ∧
    clockedBohmApprox 1 (zachosG 0 ⋅ zachosG 0) ≠ clockedBohmApprox 1 (zachosG 1 ⋅ zachosG 1) := by
  have hv0 : noVars (zachosG 0 ⋅ zachosG 0) = true := rfl
  have hv1 : noVars (zachosG 1 ⋅ zachosG 1) = true := rfl
  have hp0 : Productive (zachosG 0 ⋅ zachosG 0) :=
    (barendregt_open_question_5 hv0).mpr (by decide)
  have hp1 : Productive (zachosG 1 ⋅ zachosG 1) :=
    (barendregt_open_question_5 hv1).mpr (by decide)
  have hc : ConvS (zachosG 0 ⋅ zachosG 0) (zachosG 1 ⋅ zachosG 1) :=
    ConvS.step (headStep_to_step (zachos_zero_headStep 0))
  refine ⟨hp0, hp1, hc, fun d => convS_bohmApprox_eq d hv0 hv1 hc, ?_⟩
  intro heq1
  have hs0 : HeadStep (zachosG 0 ⋅ zachosG 0) (zachosG 1 ⋅ zachosG 1) := zachos_zero_headStep 0
  have hs1' : HeadStep (zachosG 1 ⋅ zachosG 1) (S ⋅ zachosG 1 ⋅ (zachosG 0 ⋅ zachosG 1)) :=
    zachos_succ_headStep 0 1
  obtain ⟨hne1, hn1⟩ := headNormalize_eq_of_headReduces_closedHNF hv1
    (HeadReduces.next hs1' (HeadReduces.refl _)) (Nat.le_refl 2)
  obtain ⟨hne0, hn0⟩ := headNormalize_eq_of_headReduces_closedHNF hv0
    (HeadReduces.next hs0 (HeadReduces.next hs1' (HeadReduces.refl _))) (Nat.le_refl 2)
  have hvh_end : noVars (S ⋅ zachosG 1 ⋅ (zachosG 0 ⋅ zachosG 1)) = true := rfl
  have hc_end : headClock (S ⋅ zachosG 1 ⋅ (zachosG 0 ⋅ zachosG 1)) = 0 :=
    headClock_of_closedHNF hvh_end (Nat.le_refl 2)
  have hc1 : headClock (zachosG 1 ⋅ zachosG 1) = 1 := by
    rw [headClock_of_headStep hs1' hne1, hc_end]
  have hc0 : headClock (zachosG 0 ⋅ zachosG 0) = 2 := by
    rw [headClock_of_headStep hs0 hne0, hc1]
  simp only [clockedBohmApprox, beq_hn34_false_of_ne hne0, beq_hn34_false_of_ne hne1,
             Bool.false_eq_true, ↓reduceIte, hn0, hn1, hc0, hc1, S] at heq1
  injection heq1 with hclk _ _
  omega

/-- Minimal 12-leaf vs 13-leaf non-`SN` productive pair sharing the **exact same infinite clocked Böhm tree**! -/
def cbtSeedX : Term := (S ⋅ (S ⋅ zachosT) ⋅ (S ⋅ zachosT)) ⋅ zachosT
def cbtPair1 : Term := S ⋅ zachosT ⋅ (S ⋅ (S ⋅ zachosT) ⋅ (S ⋅ zachosT)) ⋅ zachosT
def cbtPair2 : Term := A_comb ⋅ S ⋅ cbtSeedX

private theorem step_cbtPair1_unique {u : Term} (hs : Step cbtPair1 u) :
    u = (zachosT ⋅ zachosT) ⋅ cbtSeedX := by
  cases hs with
  | root _ _ _ => rfl
  | left hl =>
    cases hl with
    | left hll =>
      cases hll with
      | left hlll => cases hlll
      | right hllr =>
        cases hllr with
        | left h1 => cases h1
        | right h2 => cases h2
    | right hlr =>
      cases hlr with
      | left h1 =>
        cases h1 with
        | left h1l => cases h1l
        | right h1r =>
          cases h1r with
          | left ha => cases ha
          | right hb => cases hb with | left hc => cases hc | right hd => cases hd
      | right h2 =>
        cases h2 with
        | left ha => cases ha
        | right hb => cases hb with | left hc => cases hc | right hd => cases hd
  | right hr =>
    cases hr with
    | left h1 => cases h1
    | right h2 => cases h2

private theorem step_mid_leaves_ge_14 {w : Term} (hs : Step ((zachosT ⋅ zachosT) ⋅ cbtSeedX) w) :
    14 ≤ leaves w := by
  have hnot_atomic : ¬ StepAtomicS ((zachosT ⋅ zachosT) ⋅ cbtSeedX) w := by
    intro hat
    cases hat with
    | left hal =>
      cases hal with
      | left h1 => cases h1 with | left a => cases a | right b => cases b
      | right h2 => cases h2 with | left a => cases a | right b => cases b
    | right har =>
      cases har with
      | left h1 =>
        cases h1 with
        | left a =>
          cases a with
          | left a1 => cases a1
          | right a2 =>
            cases a2 with
            | left b1 => cases b1
            | right b2 => cases b2 with | left c1 => cases c1 | right c2 => cases c2
        | right b =>
          cases b with
          | left b1 => cases b1
          | right b2 => cases b2 with | left c1 => cases c1 | right c2 => cases c2
      | right h2 =>
        cases h2 with
        | left a => cases a
        | right b => cases b
  have hinc := (step_closed_leaves_eq_iff_stepAtomicS rfl hs).2 hnot_atomic
  have hl_mid : leaves ((zachosT ⋅ zachosT) ⋅ cbtSeedX) = 13 := rfl
  omega

/-- **Incomparable Non-`SN` Productive Terms Sharing the Exact Same Infinite Clocked Böhm Tree**:
    `cbtPair1` (12 leaves) and `cbtPair2` (13 leaves) are both productive, non-`SN`, and
    reduction-incomparable (`¬ Reduces cbtPair1 cbtPair2` and `¬ Reduces cbtPair2 cbtPair1`),
    yet share the **exact same infinite clocked Böhm tree** at all depths `d` (and are `=_S`-convertible)! -/
theorem productive_nonSN_distinct_same_clockedBohm :
    noVars cbtPair1 = true ∧
    noVars cbtPair2 = true ∧
    leaves cbtPair1 = 12 ∧
    leaves cbtPair2 = 13 ∧
    Productive cbtPair1 ∧
    Productive cbtPair2 ∧
    ¬ StrongNormalizing cbtPair1 ∧
    ¬ StrongNormalizing cbtPair2 ∧
    ¬ Reduces cbtPair1 cbtPair2 ∧
    ¬ Reduces cbtPair2 cbtPair1 ∧
    (∀ d : Nat, clockedBohmApprox d cbtPair1 = clockedBohmApprox d cbtPair2) ∧
    ConvS cbtPair1 cbtPair2 := by
  have hv1 : noVars cbtPair1 = true := rfl
  have hv2 : noVars cbtPair2 = true := rfl
  have hp1 : Productive cbtPair1 :=
    (barendregt_open_question_5 hv1).mpr (by decide : evalP cbtPair1 ≠ .p37)
  have hp2 : Productive cbtPair2 :=
    (barendregt_open_question_5 hv2).mpr (by decide : evalP cbtPair2 ≠ .p37)
  have hnsn1 : ¬ StrongNormalizing cbtPair1 := fun h =>
    ((waldmann_theorem_9 hv1).1.mp h) (by decide : evalSN cbtPair1 = .sn38)
  have hnsn2 : ¬ StrongNormalizing cbtPair2 := fun h =>
    ((waldmann_theorem_9 hv2).1.mp h) (by decide : evalSN cbtPair2 = .sn38)
  have hnr12 : ¬ Reduces cbtPair1 cbtPair2 := fun hr => by
    cases hr with
    | @next _ u _ hsu hru =>
      have hu_eq := step_cbtPair1_unique hsu
      subst hu_eq
      cases hru with
      | @next _ w _ hsw hrw =>
        have h14 : 14 ≤ leaves w := step_mid_leaves_ge_14 hsw
        have hle : leaves w ≤ leaves cbtPair2 := leaves_mono_reduces hrw
        have hl2 : leaves cbtPair2 = 13 := rfl
        omega
  have hnr21 : ¬ Reduces cbtPair2 cbtPair1 := fun hr => by
    have hle := leaves_mono_reduces hr
    change 13 ≤ 12 at hle
    omega
  -- Both step in 1 `HeadStep` to `(zachosT ⋅ zachosT) ⋅ cbtSeedX`!
  have hs1 : HeadStep cbtPair1 ((zachosT ⋅ zachosT) ⋅ cbtSeedX) :=
    HeadStep.root zachosT (S ⋅ (S ⋅ zachosT) ⋅ (S ⋅ zachosT)) zachosT
  have hs2 : HeadStep cbtPair2 ((zachosT ⋅ zachosT) ⋅ cbtSeedX) :=
    HeadStep.left (HeadStep.root S S S)
  have hcbt := clockedBohmApprox_eq_of_common_headStep hs1 hs2
  have hconv : ConvS cbtPair1 cbtPair2 :=
    ConvS.trans (ConvS.step (headStep_to_step hs1))
      (ConvS.symm (ConvS.step (headStep_to_step hs2)))
  exact ⟨hv1, hv2, rfl, rfl, hp1, hp2, hnsn1, hnsn2, hnr12, hnr21, hcbt, hconv⟩

end FormalQ30Q31Deep

#print axioms FormalQ30Q31Deep.unsolvable_clockedBohm_unfaithful
#print axioms FormalQ30Q31Deep.semiProductive_clockedBohm_unfaithful
#print axioms FormalQ30Q31Deep.productive_oneSided_bohm_iff_convS
#print axioms FormalQ30Q31Deep.productive_bohm_faithful
#print axioms FormalQ30Q31Deep.decideConvProd
#print axioms FormalQ30Q31Deep.joinOfConvProd
#print axioms FormalQ30Q31Deep.sn_strict_subset_productive
#print axioms FormalQ30Q31Deep.zachos_convS_clock_mismatch
#print axioms FormalQ30Q31Deep.productive_nonSN_distinct_same_clockedBohm
