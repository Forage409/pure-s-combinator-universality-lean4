import formal_q32_equational.lambda_i_rigidity

/-!
# Parametric `S`-Towers, `S`-Free Probe Cones, and Global `λβ`-Rigidity

Constructs the non-uniform 2-tower separation family `(A_open, B_open)` and its closed
counterpart `(M_closed, N_closed)`, proves `ConvBeta (toLam (A_open (m + 1) y)) (toLam (B_open (m + 1) y))`
for all `m : Nat` and `y : Term` via variable closing (`closeFVar`), and proves exact global
`λβ`-rigidity in `Ter(CL(S))` of:
1. `sTower k (S ⋅ S)` for all `k : Nat`,
2. `S ⋅ sTower k (S ⋅ S) ⋅ .var y` for all `k, y : Nat`,
3. `S ⋅ (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y)` for all `m, y : Nat`,
4. `A_var (m + 1) u y` (`u ≠ y`) for all `m, u, y : Nat`,
by combining `sFree_rigidity` with exact backward `CL(S)` reduction-cone characterization.

Zero `sorry`, zero `Classical.choice`, zero `native_decide`, zero custom axioms.
-/

namespace FormalQ32

open FormalAlgebra

/-! ## 1. Variable Closing (`closeFVar`) in `Lam` and Symbolic `S2` `λβ`-Equivalence -/

def closeFVar (v : Nat) (k : Nat) : Lam → Lam
  | .bvar i => .bvar i
  | .fvar w => if w = v then .bvar k else .fvar w
  | .lam m => .lam (closeFVar v (k + 1) m)
  | .app m n => .app (closeFVar v k m) (closeFVar v k n)

theorem closeFVar_shift (v : Nat) {d c : Nat} (j : Nat) (hdc : d ≤ c) (n : Lam) :
    closeFVar v (c + j) (shift j d n) = shift j d (closeFVar v c n) := by
  induction n generalizing d c with
  | bvar i =>
    simp only [shift, closeFVar]
    split <;> rfl
  | fvar w =>
    simp only [shift, closeFVar]
    by_cases hw : w = v
    · subst hw
      simp only [↓reduceIte, shift, if_pos hdc]
    · simp only [if_neg hw, shift]
  | lam m ih =>
    have hdc' : d + 1 ≤ c + 1 := Nat.add_le_add_right hdc 1
    have heq : (c + 1) + j = (c + j) + 1 := by omega
    simp only [shift, closeFVar, ← heq, ih hdc']
  | app m1 m2 ih1 ih2 =>
    simp only [shift, closeFVar, ih1 hdc, ih2 hdc]

theorem closeFVar_substB_aux (v k j : Nat) (n m : Lam) :
    closeFVar v (k + j) (substB j n m) =
      substB j (closeFVar v k n) (closeFVar v (k + 1 + j) m) := by
  induction m generalizing j with
  | bvar i =>
    simp only [substB, closeFVar]
    by_cases hij : i < j
    · simp only [if_pos hij, closeFVar]
    · simp only [if_neg hij]
      by_cases heq : i = j
      · subst heq
        simp only [↓reduceIte]
        exact closeFVar_shift v i (Nat.zero_le k) n
      · simp only [if_neg heq, closeFVar]
  | fvar w =>
    simp only [substB, closeFVar]
    by_cases hw : w = v
    · subst hw
      have hlt : ¬ (k + 1 + j < j) := by omega
      have hne : k + 1 + j ≠ j := by omega
      have hsub : k + 1 + j - 1 = k + j := by omega
      simp only [↓reduceIte, substB, if_neg hlt, if_neg hne, hsub]
    · simp only [if_neg hw, substB]
  | lam body ih =>
    have heq1 : k + j + 1 = k + (j + 1) := by omega
    have heq2 : k + 1 + j + 1 = k + 1 + (j + 1) := by omega
    simp only [substB, closeFVar, heq1, heq2, ih (j + 1)]
  | app m1 m2 ih1 ih2 =>
    simp only [substB, closeFVar, ih1 j, ih2 j]

theorem closeFVar_betaStep (v k : Nat) {a b : Lam} (h : BetaStep a b) :
    BetaStep (closeFVar v k a) (closeFVar v k b) := by
  induction h generalizing k with
  | root m n =>
    simp only [closeFVar]
    have hsub := closeFVar_substB_aux v k 0 n m
    simp only [Nat.add_zero] at hsub
    rw [hsub]
    exact .root _ _
  | lam _ ih => exact .lam (ih (k + 1))
  | left _ ih => exact .left (ih k)
  | right _ ih => exact .right (ih k)

theorem closeFVar_convBeta (v k : Nat) {a b : Lam} (h : ConvBeta a b) :
    ConvBeta (closeFVar v k a) (closeFVar v k b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact .step (closeFVar_betaStep v k hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem closeFVar_toLam_of_hasVar_false {v : Nat} (k : Nat) {t : Term}
    (hno : hasVar v t = false) :
    closeFVar v k (toLam t) = toLam t := by
  induction t with
  | s => rfl
  | var w =>
    simp only [hasVar, decide_eq_false_iff_not] at hno
    simp only [toLam, closeFVar, if_neg hno]
  | app a b iha ihb =>
    simp only [hasVar, Bool.or_eq_false_iff] at hno
    simp only [toLam, closeFVar, iha hno.1, ihb hno.2]

theorem convBeta_s2_of_convS_probe {L1 R1 L2 R2 : Term} {a : Nat}
    (hL1 : hasVar a L1 = false) (hR1 : hasVar a R1 = false)
    (hL2 : hasVar a L2 = false) (hR2 : hasVar a R2 = false)
    (hconv : ConvS ((L1 ⋅ .var a) ⋅ (R1 ⋅ .var a)) ((L2 ⋅ .var a) ⋅ (R2 ⋅ .var a))) :
    ConvBeta (toLam (S ⋅ L1 ⋅ R1)) (toLam (S ⋅ L2 ⋅ R2)) := by
  have hcb : ConvBeta (toLam ((L1 ⋅ .var a) ⋅ (R1 ⋅ .var a)))
      (toLam ((L2 ⋅ .var a) ⋅ (R2 ⋅ .var a))) := convS_to_convBeta hconv
  have hcl : ConvBeta (.lam (closeFVar a 0 (toLam ((L1 ⋅ .var a) ⋅ (R1 ⋅ .var a)))))
      (.lam (closeFVar a 0 (toLam ((L2 ⋅ .var a) ⋅ (R2 ⋅ .var a))))) :=
    convBeta_lam (closeFVar_convBeta a 0 hcb)
  simp only [toLam, closeFVar, ↓reduceIte,
             closeFVar_toLam_of_hasVar_false 0 hL1,
             closeFVar_toLam_of_hasVar_false 0 hR1,
             closeFVar_toLam_of_hasVar_false 0 hL2,
             closeFVar_toLam_of_hasVar_false 0 hR2] at hcl
  have hr1 : ConvBeta (toLam (S ⋅ L1 ⋅ R1)) (.lam ((toLam L1 ∘ₗ .bvar 0) ∘ₗ (toLam R1 ∘ₗ .bvar 0))) :=
    betaReduces_to_conv (lamS_app2 (bvarBound_toLam L1) (bvarBound_toLam R1))
  have hr2 : ConvBeta (toLam (S ⋅ L2 ⋅ R2)) (.lam ((toLam L2 ∘ₗ .bvar 0) ∘ₗ (toLam R2 ∘ₗ .bvar 0))) :=
    betaReduces_to_conv (lamS_app2 (bvarBound_toLam L2) (bvarBound_toLam R2))
  exact .trans hr1 (.trans hcl hr2.symm)

/-! ## 2. Parametric `S`-Towers, Fibonacci Probe Words, and the `(A_open, B_open)` Family -/

def sTower : Nat → Term → Term
  | 0, u => u
  | k + 1, u => S ⋅ sTower k u

def fibW (a0 b0 : Term) : Nat → Term
  | 0 => a0
  | 1 => b0
  | k + 2 => fibW a0 b0 k ⋅ fibW a0 b0 (k + 1)

def dSeq (y a : Nat) (k : Nat) : Term :=
  fibW (.var a) (.var y ⋅ .var a) k

def A_open (n : Nat) (y : Term) : Term :=
  S ⋅ (S ⋅ sTower n (S ⋅ S) ⋅ y) ⋅ (S ⋅ sTower (n - 1) (S ⋅ S) ⋅ y)

def B_open (n : Nat) (y : Term) : Term :=
  S ⋅ (S ⋅ sTower (n - 1) ((S ⋅ S) ⋅ (S ⋅ S)) ⋅ y) ⋅ (S ⋅ sTower n (S ⋅ S ⋅ S) ⋅ y)

def A_var (n : Nat) (u y : Nat) : Term :=
  S ⋅ (S ⋅ sTower n (.var u) ⋅ .var y) ⋅ (S ⋅ sTower (n - 1) (.var u) ⋅ .var y)

def M_closed (n : Nat) : Term := A_open n S
def N_closed (n : Nat) : Term := B_open n S

def maxVar : Term → Nat
  | .s => 0
  | .var k => k
  | .app a b => Nat.max (maxVar a) (maxVar b)

theorem app_left_inj {a1 a2 b1 b2 : Term} (h : a1 ⋅ b1 = a2 ⋅ b2) : a1 = a2 := by
  injection h

theorem app_right_inj {a1 a2 b1 b2 : Term} (h : a1 ⋅ b1 = a2 ⋅ b2) : b1 = b2 := by
  injection h

theorem hasVar_of_gt_maxVar {v : Nat} {t : Term} (h : maxVar t < v) :
    hasVar v t = false := by
  induction t with
  | s => rfl
  | var k =>
    simp only [maxVar] at h
    have hne : k ≠ v := by omega
    simp only [hasVar, decide_eq_false_iff_not, hne, not_false_eq_true]
  | app a b iha ihb =>
    simp only [maxVar, Nat.max_lt] at h
    simp only [hasVar, iha h.1, ihb h.2, Bool.or_self]

theorem hasVar_of_noVars (v : Nat) {t : Term} (h : noVars t = true) :
    hasVar v t = false := by
  induction t with
  | s => rfl
  | var _ => cases h
  | app a b iha ihb =>
    simp only [noVars, Bool.and_eq_true] at h
    simp only [hasVar, iha h.1, ihb h.2, Bool.or_self]

theorem hasVar_var_ne {u w : Nat} (h : u ≠ w) : hasVar u (.var w) = false := by
  have hw : w ≠ u := fun heq => h heq.symm
  simp only [hasVar, decide_eq_false_iff_not, hw, not_false_eq_true]

theorem noVars_sTower (k : Nat) {u : Term} (h : noVars u = true) :
    noVars (sTower k u) = true := by
  induction k with
  | zero => exact h
  | succ _ ih => simp only [sTower, S, noVars, ih, Bool.and_self]

theorem leaves_sTower (k : Nat) (u : Term) : leaves (sTower k u) = k + leaves u := by
  induction k with
  | zero => simp only [sTower, Nat.zero_add]
  | succ _ ih =>
    simp only [sTower, S, leaves, ih]
    omega

theorem fibW_shift (a0 b0 : Term) : ∀ k, fibW b0 (a0 ⋅ b0) k = fibW a0 b0 (k + 1)
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by simp only [fibW, fibW_shift a0 b0 k, fibW_shift a0 b0 (k + 1)]

theorem sTower_reduces (k : Nat) (u a0 b0 : Term) :
    Reduces (sTower k u ⋅ a0 ⋅ b0) (u ⋅ fibW a0 b0 k ⋅ fibW a0 b0 (k + 1)) := by
  induction k generalizing a0 b0 with
  | zero => exact .refl _
  | succ k' ih =>
    have hs : Step (S ⋅ sTower k' u ⋅ a0 ⋅ b0) (sTower k' u ⋅ b0 ⋅ (a0 ⋅ b0)) :=
      .root (sTower k' u) a0 b0
    have hrest := ih b0 (a0 ⋅ b0)
    rw [fibW_shift a0 b0 k', fibW_shift a0 b0 (k' + 1)] at hrest
    exact .next hs hrest

theorem arm_reduces (k : Nat) (u y x : Term) :
    Reduces (S ⋅ sTower k u ⋅ y ⋅ x)
      (u ⋅ fibW x (y ⋅ x) k ⋅ fibW x (y ⋅ x) (k + 1)) :=
  .next (.root (sTower k u) y x) (sTower_reduces k u x (y ⋅ x))

/-- **Theorem (`A_open =_{λβ} B_open`)**: For every `m : Nat` and `y : Term`,
    `A_open (m + 1) y` and `B_open (m + 1) y` have `λβ`-convertible translations. -/
theorem convBeta_A_B_open (m : Nat) (y : Term) :
    ConvBeta (toLam (A_open (m + 1) y)) (toLam (B_open (m + 1) y)) := by
  let a := maxVar y + 1
  have hya : hasVar a y = false := hasVar_of_gt_maxVar (Nat.lt_succ_self _)
  let LA := S ⋅ sTower (m + 1) (S ⋅ S) ⋅ y
  let RA := S ⋅ sTower m (S ⋅ S) ⋅ y
  let LB := S ⋅ sTower m ((S ⋅ S) ⋅ (S ⋅ S)) ⋅ y
  let RB := S ⋅ sTower (m + 1) (S ⋅ S ⋅ S) ⋅ y
  have ht1 : hasVar a (sTower (m + 1) (S ⋅ S)) = false :=
    hasVar_of_noVars a (noVars_sTower (m + 1) rfl)
  have ht2 : hasVar a (sTower m (S ⋅ S)) = false :=
    hasVar_of_noVars a (noVars_sTower m rfl)
  have ht3 : hasVar a (sTower m ((S ⋅ S) ⋅ (S ⋅ S))) = false :=
    hasVar_of_noVars a (noVars_sTower m rfl)
  have ht4 : hasVar a (sTower (m + 1) (S ⋅ S ⋅ S)) = false :=
    hasVar_of_noVars a (noVars_sTower (m + 1) rfl)
  have happ : ∀ {u v : Term}, hasVar a u = false → hasVar a v = false → hasVar a (u ⋅ v) = false := by
    intro u v hu hv; unfold hasVar; rw [hu, hv]; rfl
  have hLA : hasVar a LA = false := happ (happ rfl ht1) hya
  have hRA : hasVar a RA = false := happ (happ rfl ht2) hya
  have hLB : hasVar a LB = false := happ (happ rfl ht3) hya
  have hRB : hasVar a RB = false := happ (happ rfl ht4) hya
  let d := fun j => fibW (.var a) (y ⋅ .var a) j
  let E := S ⋅ d (m + 1) ⋅ d (m + 2)
  have hd2 : d m ⋅ d (m + 1) = d (m + 2) := rfl
  have hd3 : d (m + 1) ⋅ d (m + 2) = d (m + 3) := rfl
  have rLA : Reduces (LA ⋅ .var a) (S ⋅ d (m + 2) ⋅ d (m + 3)) := by
    have h1 := arm_reduces (m + 1) (S ⋅ S) y (.var a)
    have h2 : Step ((S ⋅ S) ⋅ d (m + 1) ⋅ d (m + 2)) (S ⋅ d (m + 2) ⋅ (d (m + 1) ⋅ d (m + 2))) :=
      .root S (d (m + 1)) (d (m + 2))
    rw [hd3] at h2
    exact reduces_trans h1 (.next h2 (.refl _))
  have rRA : Reduces (RA ⋅ .var a) E := by
    have h1 := arm_reduces m (S ⋅ S) y (.var a)
    have h2 : Step ((S ⋅ S) ⋅ d m ⋅ d (m + 1)) (S ⋅ d (m + 1) ⋅ (d m ⋅ d (m + 1))) :=
      .root S (d m) (d (m + 1))
    rw [hd2] at h2
    exact reduces_trans h1 (.next h2 (.refl _))
  have rA : Reduces ((LA ⋅ .var a) ⋅ (RA ⋅ .var a)) ((d (m + 2) ⋅ E) ⋅ (d (m + 3) ⋅ E)) :=
    reduces_trans (reduces_app rLA rRA) (.next (.root (d (m + 2)) (d (m + 3)) E) (.refl _))
  have rLB : Reduces (LB ⋅ .var a) (d (m + 2) ⋅ E) := by
    have h1 := arm_reduces m ((S ⋅ S) ⋅ (S ⋅ S)) y (.var a)
    have h2 : Step (((S ⋅ S) ⋅ (S ⋅ S) ⋅ d m) ⋅ d (m + 1))
        (((S ⋅ d m) ⋅ ((S ⋅ S) ⋅ d m)) ⋅ d (m + 1)) :=
      .left (.root S (S ⋅ S) (d m))
    have h3 : Step (((S ⋅ d m) ⋅ ((S ⋅ S) ⋅ d m)) ⋅ d (m + 1))
        ((d m ⋅ d (m + 1)) ⋅ ((S ⋅ S) ⋅ d m ⋅ d (m + 1))) :=
      .root (d m) ((S ⋅ S) ⋅ d m) (d (m + 1))
    have h4 : Step ((d m ⋅ d (m + 1)) ⋅ ((S ⋅ S) ⋅ d m ⋅ d (m + 1)))
        ((d m ⋅ d (m + 1)) ⋅ (S ⋅ d (m + 1) ⋅ (d m ⋅ d (m + 1)))) :=
      .right (.root S (d m) (d (m + 1)))
    rw [hd2] at h4
    exact reduces_trans h1 (.next h2 (.next h3 (.next h4 (.refl _))))
  have rRB : Reduces (RB ⋅ .var a) (d (m + 3) ⋅ E) := by
    have h1 := arm_reduces (m + 1) (S ⋅ S ⋅ S) y (.var a)
    have h2 : Step ((S ⋅ S ⋅ S ⋅ d (m + 1)) ⋅ d (m + 2))
        (((S ⋅ d (m + 1)) ⋅ (S ⋅ d (m + 1))) ⋅ d (m + 2)) :=
      .left (.root S S (d (m + 1)))
    have h3 : Step (((S ⋅ d (m + 1)) ⋅ (S ⋅ d (m + 1))) ⋅ d (m + 2))
        ((d (m + 1) ⋅ d (m + 2)) ⋅ (S ⋅ d (m + 1) ⋅ d (m + 2))) :=
      .root (d (m + 1)) (S ⋅ d (m + 1)) (d (m + 2))
    rw [hd3] at h3
    exact reduces_trans h1 (.next h2 (.next h3 (.refl _)))
  have rB : Reduces ((LB ⋅ .var a) ⋅ (RB ⋅ .var a)) ((d (m + 2) ⋅ E) ⋅ (d (m + 3) ⋅ E)) :=
    reduces_app rLB rRB
  have hconvS : ConvS ((LA ⋅ .var a) ⋅ (RA ⋅ .var a)) ((LB ⋅ .var a) ⋅ (RB ⋅ .var a)) :=
    .trans (convS_of_reduces rA) (convS_of_reduces rB).symm
  simpa only [A_open, B_open, Nat.add_sub_cancel] using
    convBeta_s2_of_convS_probe hLA hRA hLB hRB hconvS

theorem convBeta_M_N_closed (m : Nat) :
    ConvBeta (toLam (M_closed (m + 1))) (toLam (N_closed (m + 1))) :=
  convBeta_A_B_open m S

/-! ## 3. Anti-Redex Helpers & Properties of `fibW`, `dSeq`, and `sTower` -/

theorem hasAntiRedex_app_eq_false {a b : Term}
    (hroot : ∀ z1 z2, rightArgOpt a = some z1 → rightArgOpt b = some z2 → z1 ≠ z2)
    (ha : hasAntiRedex a = false) (hb : hasAntiRedex b = false) :
    hasAntiRedex (a ⋅ b) = false := by
  unfold hasAntiRedex
  rw [ha, hb]
  cases ha_opt : rightArgOpt a with
  | none => rfl
  | some z1 =>
    cases hb_opt : rightArgOpt b with
    | none => rfl
    | some z2 =>
      have hne := hroot z1 z2 ha_opt hb_opt
      simp only [hne]
      rfl

theorem hasAntiRedex_s_left {b : Term} (hb : hasAntiRedex b = false) :
    hasAntiRedex (.s ⋅ b) = false :=
  hasAntiRedex_app_eq_false (fun _ _ h => by cases h) rfl hb

theorem hasAntiRedex_var_left (v : Nat) {b : Term} (hb : hasAntiRedex b = false) :
    hasAntiRedex (.var v ⋅ b) = false :=
  hasAntiRedex_app_eq_false (fun _ _ h => by cases h) rfl hb

theorem hasAntiRedex_var_right {a : Term} (v : Nat) (ha : hasAntiRedex a = false) :
    hasAntiRedex (a ⋅ .var v) = false :=
  hasAntiRedex_app_eq_false (fun _ _ _ h => by cases h) ha rfl

theorem isSFree_fibW {a0 b0 : Term} (ha : isSFree a0 = true) (hb : isSFree b0 = true) :
    ∀ k, isSFree (fibW a0 b0 k) = true
  | 0 => ha
  | 1 => hb
  | k + 2 => by
    simp only [fibW, isSFree, isSFree_fibW ha hb k, isSFree_fibW ha hb (k + 1), Bool.and_self]

theorem hasVar_false_fibW {v : Nat} {a0 b0 : Term}
    (ha : hasVar v a0 = false) (hb : hasVar v b0 = false) :
    ∀ k, hasVar v (fibW a0 b0 k) = false
  | 0 => ha
  | 1 => hb
  | k + 2 => by
    simp only [fibW, hasVar, hasVar_false_fibW ha hb k, hasVar_false_fibW ha hb (k + 1), Bool.or_self]

theorem leaves_fibW_vars_ge (a b : Nat) :
    ∀ k, 1 ≤ leaves (fibW (.var a) (.var b) k) ∧
         (1 ≤ k → leaves (fibW (.var a) (.var b) k) < leaves (fibW (.var a) (.var b) (k + 1)))
  | 0 => ⟨Nat.le_refl 1, fun h => False.elim (by omega)⟩
  | 1 => ⟨Nat.le_refl 1, fun _ => by simp only [fibW, leaves]; omega⟩
  | k + 2 => by
    have ⟨hpos_k, _⟩ := leaves_fibW_vars_ge a b k
    have ⟨hpos_k1, _⟩ := leaves_fibW_vars_ge a b (k + 1)
    simp only [fibW, leaves]
    exact ⟨by omega, fun _ => by omega⟩

theorem leaves_fibW_vars_ge_two (a b : Nat) {k : Nat} (hk : 2 ≤ k) :
    2 ≤ leaves (fibW (.var a) (.var b) k) := by
  cases k with
  | zero => exfalso; omega
  | succ k1 =>
    cases k1 with
    | zero => exfalso; omega
    | succ m =>
      have h1 := (leaves_fibW_vars_ge a b m).1
      have h2 := (leaves_fibW_vars_ge a b (m + 1)).1
      simp only [fibW, leaves]
      omega

theorem hasAntiRedex_fibW_vars (a b : Nat) :
    ∀ k, hasAntiRedex (fibW (.var a) (.var b) k) = false
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | k + 4 => by
    have ih1 := hasAntiRedex_fibW_vars a b (k + 2)
    have ih2 := hasAntiRedex_fibW_vars a b (k + 3)
    have hlt := (leaves_fibW_vars_ge a b (k + 1)).2 (by omega)
    have hne : fibW (.var a) (.var b) (k + 1) ≠ fibW (.var a) (.var b) (k + 2) :=
      fun heq => Nat.ne_of_lt hlt (congrArg leaves heq)
    refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_) ih1 ih2
    change rightArgOpt (fibW (.var a) (.var b) k ⋅ fibW (.var a) (.var b) (k + 1)) = some z1 at hz1
    change rightArgOpt (fibW (.var a) (.var b) (k + 1) ⋅ fibW (.var a) (.var b) (k + 2)) = some z2 at hz2
    injection hz1 with hz1'
    injection hz2 with hz2'
    rw [← hz1', ← hz2']
    exact hne

theorem dSeq_succ2 (y a k : Nat) :
    dSeq y a (k + 2) = dSeq y a k ⋅ dSeq y a (k + 1) := rfl

theorem leaves_dSeq_strict (y a : Nat) :
    ∀ k, k + 1 ≤ leaves (dSeq y a k) ∧ leaves (dSeq y a k) < leaves (dSeq y a (k + 1))
  | 0 => ⟨Nat.le_refl 1, by simp only [dSeq, fibW, leaves]; omega⟩
  | 1 => ⟨by simp only [dSeq, fibW, leaves]; omega, by simp only [dSeq, fibW, leaves]; omega⟩
  | k + 2 => by
    have ⟨h1, _⟩ := leaves_dSeq_strict y a k
    have ⟨h2, _⟩ := leaves_dSeq_strict y a (k + 1)
    rw [dSeq_succ2 y a k, dSeq_succ2 y a (k + 1)]
    simp only [leaves]
    exact ⟨by omega, by omega⟩

theorem dSeq_inj (y a : Nat) {p q : Nat} (h : dSeq y a p = dSeq y a q) : p = q := by
  have hmono : ∀ i j, i < j → leaves (dSeq y a i) < leaves (dSeq y a j) := by
    intro i j hij
    induction hij with
    | refl => exact (leaves_dSeq_strict y a i).2
    | @step m _ ih => exact Nat.lt_trans ih (leaves_dSeq_strict y a m).2
  by_cases hpq : p = q
  · exact hpq
  · exfalso
    have heq := congrArg leaves h
    by_cases hlt : p < q
    · exact Nat.ne_of_lt (hmono p q hlt) heq
    · exact Nat.ne_of_gt (hmono q p (by omega)) heq

theorem dSeq_succ_app (y a k : Nat) : ∃ L, dSeq y a (k + 1) = L ⋅ dSeq y a k := by
  cases k with
  | zero => exact ⟨.var y, rfl⟩
  | succ m => exact ⟨dSeq y a m, rfl⟩

theorem hasAntiRedex_dSeq (y a : Nat) :
    ∀ k, hasAntiRedex (dSeq y a k) = false
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | k + 3 => by
    have ih1 := hasAntiRedex_dSeq y a (k + 1)
    have ih2 := hasAntiRedex_dSeq y a (k + 2)
    have hlt := (leaves_dSeq_strict y a k).2
    have hne : dSeq y a k ≠ dSeq y a (k + 1) :=
      fun heq => Nat.ne_of_lt hlt (congrArg leaves heq)
    obtain ⟨L1, hL1⟩ := dSeq_succ_app y a k
    change hasAntiRedex (dSeq y a (k + 1) ⋅ dSeq y a (k + 2)) = false
    refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_) ih1 ih2
    rw [hL1] at hz1
    rw [dSeq_succ2 y a k] at hz2
    injection hz1 with hz1'
    injection hz2 with hz2'
    rw [← hz1', ← hz2']
    exact hne

theorem hasAntiRedex_sTower_SS : ∀ k, hasAntiRedex (sTower k (S ⋅ S)) = false
  | 0 => rfl
  | k + 1 => hasAntiRedex_s_left (hasAntiRedex_sTower_SS k)

theorem hasAntiRedex_sTower_var (u : Nat) : ∀ k, hasAntiRedex (sTower k (.var u)) = false
  | 0 => rfl
  | k + 1 => hasAntiRedex_s_left (hasAntiRedex_sTower_var u k)

private theorem noVars_false_of_isSFree {t : Term} (h : isSFree t = true) :
    noVars t = false := by
  induction t with
  | s => cases h
  | var _ => rfl
  | app a b iha _ =>
    simp only [isSFree, Bool.and_eq_true] at h
    simp only [noVars, iha h.1, Bool.false_and]

private theorem hasAntiRedex_sTower_SS_app_sfree (j : Nat) {w : Term}
    (hsf : isSFree w = true) (hno : hasAntiRedex w = false) :
    hasAntiRedex (sTower j (S ⋅ S) ⋅ w) = false := by
  have hj := hasAntiRedex_sTower_SS j
  have hclosed : ∃ r0, sTower j (S ⋅ S) = .s ⋅ r0 ∧ noVars r0 = true := by
    cases j with
    | zero => exact ⟨.s, rfl, rfl⟩
    | succ j' => exact ⟨sTower j' (S ⋅ S), rfl, noVars_sTower j' rfl⟩
  obtain ⟨r0, heq, hcr0⟩ := hclosed
  refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_) hj hno
  rw [heq] at hz1
  injection hz1 with hz1'
  cases w with
  | s => cases hsf
  | var _ => cases hz2
  | app w1 w2 =>
    simp only [isSFree, Bool.and_eq_true] at hsf
    injection hz2 with hz2'
    rw [← hz1', ← hz2']
    intro hh
    have hnw2 : noVars w2 = false := noVars_false_of_isSFree hsf.2
    rw [hh] at hcr0
    rw [hcr0] at hnw2
    cases hnw2

/-! ## 4. Backward Cone 1: Global `λβ`-Rigidity of `sTower k (S ⋅ S)` -/

private def InConeTower (k a b c : Nat) (X : Term) : Prop :=
  X = (fibW (.var a) (.var b) (k + 1) ⋅ .var c) ⋅ (fibW (.var a) (.var b) (k + 2) ⋅ .var c) ∨
  X = S ⋅ fibW (.var a) (.var b) (k + 1) ⋅ fibW (.var a) (.var b) (k + 2) ⋅ .var c ∨
  ∃ j r, j + r = k ∧ X = sTower j (S ⋅ S) ⋅ fibW (.var a) (.var b) r ⋅ fibW (.var a) (.var b) (r + 1) ⋅ .var c

private theorem coneTower_step_back {k a b c : Nat} {Y X : Term}
    (hs : Step Y X) (hx : InConeTower k a b c X) :
    InConeTower k a b c Y := by
  have hsf : ∀ m, isSFree (fibW (.var a) (.var b) m) = true := isSFree_fibW rfl rfl
  have hno : ∀ m, hasAntiRedex (fibW (.var a) (.var b) m) = false := hasAntiRedex_fibW_vars a b
  rcases hx with rfl | rfl | ⟨j, r, hjr, rfl⟩
  · cases hs with
    | root _ _ _ => exact Or.inr (Or.inl rfl)
    | left hl =>
      exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_var_right c (hno (k + 1))) hl)
    | right hr =>
      exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_var_right c (hno (k + 2))) hr)
  · cases hs with
    | right hr => cases hr
    | left hl =>
      cases hl with
      | root _ _ _ => exact Or.inr (Or.inr ⟨0, k, Nat.zero_add k, rfl⟩)
      | left hll =>
        exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_s_left (hno (k + 1))) hll)
      | right hlr =>
        exact False.elim (no_step_into_of_no_antiRedex (hno (k + 2)) hlr)
  · cases hs with
    | right hr => cases hr
    | left hl =>
      cases r with
      | zero =>
        exact False.elim (no_step_into_of_no_antiRedex
          (hasAntiRedex_var_right b (hasAntiRedex_sTower_SS_app_sfree j (hsf 0) (hno 0))) hl)
      | succ m =>
        change Step _ ((sTower j (S ⋅ S) ⋅ fibW (.var a) (.var b) (m + 1)) ⋅
            (fibW (.var a) (.var b) m ⋅ fibW (.var a) (.var b) (m + 1))) at hl
        cases hl with
        | root _ _ _ => exact Or.inr (Or.inr ⟨j + 1, m, by omega, rfl⟩)
        | left hll =>
          exact False.elim (no_step_into_of_no_antiRedex
            (hasAntiRedex_sTower_SS_app_sfree j (hsf (m + 1)) (hno (m + 1))) hll)
        | right hlr =>
          exact False.elim (no_step_into_of_no_antiRedex (hno (m + 2)) hlr)

private theorem coneTower_reduces_back {k a b c : Nat} {Y X : Term}
    (hr : Reduces Y X) (hx : InConeTower k a b c X) :
    InConeTower k a b c Y := by
  induction hr with
  | refl _ => exact hx
  | next hs _ ih => exact coneTower_step_back hs (ih hx)

/-- **Global `λβ`-Rigidity of `sTower k (S ⋅ S)`**: For all `k : Nat` and `R : Term`,
    `ConvBeta (toLam (sTower k (S ⋅ S))) (toLam R) → R = sTower k (S ⋅ S)`. -/
theorem rigidity_sTower_SS (k : Nat) (R : Term)
    (hconv : ConvBeta (toLam (sTower k (S ⋅ S))) (toLam R)) :
    R = sTower k (S ⋅ S) := by
  let a := 0
  let b := 1
  let c := 2
  have hsf : ∀ m, isSFree (fibW (.var a) (.var b) m) = true := isSFree_fibW rfl rfl
  let target := (fibW (.var a) (.var b) (k + 1) ⋅ .var c) ⋅
                (fibW (.var a) (.var b) (k + 2) ⋅ .var c)
  have hredL : Reduces (sTower k (S ⋅ S) ⋅ .var a ⋅ .var b ⋅ .var c) target := by
    have h1 := reduces_left (sTower_reduces k (S ⋅ S) (.var a) (.var b)) (.var c)
    have h2 : Step ((S ⋅ S) ⋅ fibW (.var a) (.var b) k ⋅ fibW (.var a) (.var b) (k + 1) ⋅ .var c)
        ((S ⋅ fibW (.var a) (.var b) (k + 1) ⋅
          (fibW (.var a) (.var b) k ⋅ fibW (.var a) (.var b) (k + 1))) ⋅ .var c) :=
      .left (.root S (fibW (.var a) (.var b) k) (fibW (.var a) (.var b) (k + 1)))
    have h3 : Step ((S ⋅ fibW (.var a) (.var b) (k + 1) ⋅ fibW (.var a) (.var b) (k + 2)) ⋅ .var c)
        target :=
      .root (fibW (.var a) (.var b) (k + 1)) (fibW (.var a) (.var b) (k + 2)) (.var c)
    exact reduces_trans h1 (.next h2 (.next h3 (.refl _)))
  have hconvApp : ConvBeta (toLam (sTower k (S ⋅ S) ⋅ .var a ⋅ .var b ⋅ .var c))
      (toLam (R ⋅ .var a ⋅ .var b ⋅ .var c)) :=
    convBeta_left (convBeta_left (convBeta_left hconv (.fvar a)) (.fvar b)) (.fvar c)
  have hconvT : ConvBeta (toLam target) (toLam (R ⋅ .var a ⋅ .var b ⋅ .var c)) :=
    .trans (convS_to_convBeta (convS_of_reduces hredL)).symm hconvApp
  have hsfT : isSFree target = true := by
    simp only [target, isSFree, hsf, Bool.and_self]
  have hcone := coneTower_reduces_back (sFree_rigidity hsfT hconvT) (Or.inl rfl)
  rcases hcone with h1 | h2 | ⟨j, r, hjr, h3⟩
  · exfalso
    have hl := congrArg leaves (app_right_inj h1)
    have hge := leaves_fibW_vars_ge_two a b (k := k + 2) (by omega)
    simp only [leaves] at hl
    omega
  · exfalso
    have hl := congrArg leaves (app_right_inj (app_left_inj h2))
    have hge := leaves_fibW_vars_ge_two a b (k := k + 2) (by omega)
    simp only [leaves] at hl
    omega
  · cases r with
    | zero =>
      have hjk : j = k := by omega
      rw [hjk] at h3
      exact app_left_inj (app_left_inj (app_left_inj h3))
    | succ m =>
      exfalso
      have hl := congrArg leaves (app_right_inj (app_left_inj h3))
      have hge := leaves_fibW_vars_ge_two a b (k := (m + 1) + 1) (by omega)
      simp only [leaves] at hl
      omega

/-! ## 5. Backward Cones 2 & 3: Rigidity of `S ⋅ sTower k T ⋅ .var y` and `S ⋅ (S ⋅ sTower (m + 1) T ⋅ .var y)` -/

private def InConeArm (k y a b : Nat) (X : Term) : Prop :=
  X = (dSeq y a (k + 1) ⋅ .var b) ⋅ (dSeq y a (k + 2) ⋅ .var b) ∨
  X = S ⋅ dSeq y a (k + 1) ⋅ dSeq y a (k + 2) ⋅ .var b ∨
  (∃ j r, j + r = k ∧ X = sTower j (S ⋅ S) ⋅ dSeq y a r ⋅ dSeq y a (r + 1) ⋅ .var b) ∨
  X = (S ⋅ sTower k (S ⋅ S) ⋅ .var y) ⋅ .var a ⋅ .var b

private theorem coneArm_step_back {k y a b : Nat} {Y X : Term}
    (hs : Step Y X) (hx : InConeArm k y a b X) :
    InConeArm k y a b Y := by
  have hsf : ∀ m, isSFree (dSeq y a m) = true := isSFree_fibW rfl rfl
  have hno : ∀ m, hasAntiRedex (dSeq y a m) = false := hasAntiRedex_dSeq y a
  rcases hx with rfl | rfl | ⟨j, r, hjr, rfl⟩ | rfl
  · cases hs with
    | root _ _ _ => exact Or.inr (Or.inl rfl)
    | left hl =>
      exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_var_right b (hno (k + 1))) hl)
    | right hr =>
      exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_var_right b (hno (k + 2))) hr)
  · cases hs with
    | right hr => cases hr
    | left hl =>
      change Step _ ((S ⋅ dSeq y a (k + 1)) ⋅ (dSeq y a k ⋅ dSeq y a (k + 1))) at hl
      cases hl with
      | root _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨0, k, Nat.zero_add k, rfl⟩))
      | left hll =>
        exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_s_left (hno (k + 1))) hll)
      | right hlr =>
        exact False.elim (no_step_into_of_no_antiRedex (hno (k + 2)) hlr)
  · cases hs with
    | right hr => cases hr
    | left hl =>
      cases r with
      | zero =>
        change Step _ ((sTower j (S ⋅ S) ⋅ .var a) ⋅ (.var y ⋅ .var a)) at hl
        cases hl with
        | root _ _ _ =>
          have hjk : j = k := by omega
          subst hjk
          exact Or.inr (Or.inr (Or.inr rfl))
        | left hll =>
          exact False.elim (no_step_into_of_no_antiRedex
            (hasAntiRedex_sTower_SS_app_sfree j (hsf 0) (hno 0)) hll)
        | right hlr =>
          exact False.elim (no_step_into_of_no_antiRedex (hno 1) hlr)
      | succ m =>
        change Step _ ((sTower j (S ⋅ S) ⋅ dSeq y a (m + 1)) ⋅ (dSeq y a m ⋅ dSeq y a (m + 1))) at hl
        cases hl with
        | root _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨j + 1, m, by omega, rfl⟩))
        | left hll =>
          exact False.elim (no_step_into_of_no_antiRedex
            (hasAntiRedex_sTower_SS_app_sfree j (hsf (m + 1)) (hno (m + 1))) hll)
        | right hlr =>
          exact False.elim (no_step_into_of_no_antiRedex (hno (m + 2)) hlr)
  · exact False.elim (no_step_into_of_no_antiRedex
      (hasAntiRedex_var_right b
        (hasAntiRedex_var_right a
          (hasAntiRedex_var_right y (hasAntiRedex_s_left (hasAntiRedex_sTower_SS k))))) hs)

private theorem coneArm_reduces_back {k y a b : Nat} {Y X : Term}
    (hr : Reduces Y X) (hx : InConeArm k y a b X) :
    InConeArm k y a b Y := by
  induction hr with
  | refl _ => exact hx
  | next hs _ ih => exact coneArm_step_back hs (ih hx)

theorem rigidity_arm_SS (k y : Nat) (R : Term)
    (hconv : ConvBeta (toLam (S ⋅ sTower k (S ⋅ S) ⋅ .var y)) (toLam R)) :
    R = S ⋅ sTower k (S ⋅ S) ⋅ .var y := by
  let a := y + 1
  let b := y + 2
  have hsf : ∀ m, isSFree (dSeq y a m) = true := isSFree_fibW rfl rfl
  let target := (dSeq y a (k + 1) ⋅ .var b) ⋅ (dSeq y a (k + 2) ⋅ .var b)
  have hredL : Reduces ((S ⋅ sTower k (S ⋅ S) ⋅ .var y) ⋅ .var a ⋅ .var b) target := by
    have h1 := reduces_left (arm_reduces k (S ⋅ S) (.var y) (.var a)) (.var b)
    have h2 : Step ((S ⋅ S) ⋅ dSeq y a k ⋅ dSeq y a (k + 1) ⋅ .var b)
        ((S ⋅ dSeq y a (k + 1) ⋅ (dSeq y a k ⋅ dSeq y a (k + 1))) ⋅ .var b) :=
      .left (.root S (dSeq y a k) (dSeq y a (k + 1)))
    have h3 : Step ((S ⋅ dSeq y a (k + 1) ⋅ dSeq y a (k + 2)) ⋅ .var b) target :=
      .root (dSeq y a (k + 1)) (dSeq y a (k + 2)) (.var b)
    exact reduces_trans h1 (.next h2 (.next h3 (.refl _)))
  have hconvApp : ConvBeta (toLam ((S ⋅ sTower k (S ⋅ S) ⋅ .var y) ⋅ .var a ⋅ .var b))
      (toLam (R ⋅ .var a ⋅ .var b)) :=
    convBeta_left (convBeta_left hconv (.fvar a)) (.fvar b)
  have hconvT : ConvBeta (toLam target) (toLam (R ⋅ .var a ⋅ .var b)) :=
    .trans (convS_to_convBeta (convS_of_reduces hredL)).symm hconvApp
  have hsfT : isSFree target = true := by
    simp only [target, isSFree, hsf, Bool.and_self]
  have hcone := coneArm_reduces_back (sFree_rigidity hsfT hconvT) (Or.inl rfl)
  rcases hcone with h1 | h2 | ⟨j, r, _, h3⟩ | h4
  · exfalso
    have hl := congrArg leaves (app_right_inj h1)
    have hge := (leaves_dSeq_strict y a (k + 2)).1
    simp only [leaves] at hl
    omega
  · exfalso
    have hl := congrArg leaves (app_right_inj (app_left_inj h2))
    have hge := (leaves_dSeq_strict y a (k + 2)).1
    simp only [leaves] at hl
    omega
  · exfalso
    have hl := congrArg leaves (app_right_inj (app_left_inj h3))
    have hge := (leaves_dSeq_strict y a (r + 1)).1
    simp only [leaves] at hl
    omega
  · exact app_left_inj (app_left_inj h4)

private def InConeSArm (m y w a : Nat) (X : Term) : Prop :=
  let B := .var w ⋅ .var a
  X = (dSeq y a (m + 2) ⋅ B) ⋅ (dSeq y a (m + 3) ⋅ B) ∨
  X = S ⋅ dSeq y a (m + 2) ⋅ dSeq y a (m + 3) ⋅ B ∨
  (∃ j r, j + r = m + 1 ∧ X = sTower j (S ⋅ S) ⋅ dSeq y a r ⋅ dSeq y a (r + 1) ⋅ B) ∨
  X = ((S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y) ⋅ .var a) ⋅ B ∨
  X = (S ⋅ (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y)) ⋅ .var w ⋅ .var a

private theorem dSeq_succ_ne_var (y a k v : Nat) : dSeq y a (k + 1) ≠ .var v := by
  intro heq
  have hl := congrArg leaves heq
  have hge := (leaves_dSeq_strict y a (k + 1)).1
  simp only [leaves] at hl
  omega

private theorem hasAntiRedex_dSeq_succ2_app_B (y w a k : Nat) :
    hasAntiRedex (dSeq y a (k + 2) ⋅ (.var w ⋅ .var a)) = false := by
  refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_)
    (hasAntiRedex_dSeq y a (k + 2)) rfl
  rw [dSeq_succ2 y a k] at hz1
  injection hz1 with hz1'
  injection hz2 with hz2'
  rw [← hz1', ← hz2']
  exact dSeq_succ_ne_var y a k a

private theorem coneSArm_step_back {m y w a : Nat} {Y X : Term}
    (hs : Step Y X) (hx : InConeSArm m y w a X) :
    InConeSArm m y w a Y := by
  have hsf : ∀ n, isSFree (dSeq y a n) = true := isSFree_fibW rfl rfl
  have hno : ∀ n, hasAntiRedex (dSeq y a n) = false := hasAntiRedex_dSeq y a
  rcases hx with rfl | rfl | ⟨j, r, hjr, rfl⟩ | rfl | rfl
  · cases hs with
    | root _ _ _ => exact Or.inr (Or.inl rfl)
    | left hl =>
      exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_dSeq_succ2_app_B y w a m) hl)
    | right hr =>
      exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_dSeq_succ2_app_B y w a (m + 1)) hr)
  · cases hs with
    | right hr =>
      exact False.elim (no_step_into_of_no_antiRedex (t := .var w ⋅ .var a) rfl hr)
    | left hl =>
      change Step _ ((S ⋅ dSeq y a (m + 2)) ⋅ (dSeq y a (m + 1) ⋅ dSeq y a (m + 2))) at hl
      cases hl with
      | root _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨0, m + 1, Nat.zero_add _, rfl⟩))
      | left hll =>
        exact False.elim (no_step_into_of_no_antiRedex (hasAntiRedex_s_left (hno (m + 2))) hll)
      | right hlr =>
        exact False.elim (no_step_into_of_no_antiRedex (hno (m + 3)) hlr)
  · cases r with
    | zero =>
      change Step Y (((sTower j (S ⋅ S) ⋅ .var a) ⋅ (.var y ⋅ .var a)) ⋅ (.var w ⋅ .var a)) at hs
      cases hs with
      | right hr =>
        exact False.elim (no_step_into_of_no_antiRedex (t := .var w ⋅ .var a) rfl hr)
      | left hl =>
        cases hl with
        | root _ _ _ =>
          have hjm : j = m + 1 := by omega
          subst hjm
          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        | left hll =>
          exact False.elim (no_step_into_of_no_antiRedex
            (hasAntiRedex_sTower_SS_app_sfree j (hsf 0) (hno 0)) hll)
        | right hlr =>
          exact False.elim (no_step_into_of_no_antiRedex (hno 1) hlr)
    | succ r' =>
      change Step Y (((sTower j (S ⋅ S) ⋅ dSeq y a (r' + 1)) ⋅
          (dSeq y a r' ⋅ dSeq y a (r' + 1))) ⋅ (.var w ⋅ .var a)) at hs
      cases hs with
      | right hr =>
        exact False.elim (no_step_into_of_no_antiRedex (t := .var w ⋅ .var a) rfl hr)
      | left hl =>
        cases hl with
        | root _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨j + 1, r', by omega, rfl⟩))
        | left hll =>
          exact False.elim (no_step_into_of_no_antiRedex
            (hasAntiRedex_sTower_SS_app_sfree j (hsf (r' + 1)) (hno (r' + 1))) hll)
        | right hlr =>
          exact False.elim (no_step_into_of_no_antiRedex (hno (r' + 2)) hlr)
  · cases hs with
    | root _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    | left hl =>
      exact False.elim (no_step_into_of_no_antiRedex
        (hasAntiRedex_var_right a
          (hasAntiRedex_var_right y (hasAntiRedex_s_left (hasAntiRedex_sTower_SS (m + 1))))) hl)
    | right hr =>
      exact False.elim (no_step_into_of_no_antiRedex (t := .var w ⋅ .var a) rfl hr)
  · exact False.elim (no_step_into_of_no_antiRedex
      (hasAntiRedex_var_right a
        (hasAntiRedex_var_right w
          (hasAntiRedex_s_left
            (hasAntiRedex_var_right y (hasAntiRedex_s_left (hasAntiRedex_sTower_SS (m + 1))))))) hs)

private theorem coneSArm_reduces_back {m y w a : Nat} {Y X : Term}
    (hr : Reduces Y X) (hx : InConeSArm m y w a X) :
    InConeSArm m y w a Y := by
  induction hr with
  | refl _ => exact hx
  | next hs _ ih => exact coneSArm_step_back hs (ih hx)

theorem rigidity_s_arm_SS (m y : Nat) (R : Term)
    (hconv : ConvBeta (toLam (S ⋅ (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y))) (toLam R)) :
    R = S ⋅ (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y) := by
  let w := y + 1
  let a := y + 2
  have hsf : ∀ n, isSFree (dSeq y a n) = true := isSFree_fibW rfl rfl
  let B : Term := .var w ⋅ .var a
  let P := S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y
  let target := (dSeq y a (m + 2) ⋅ B) ⋅ (dSeq y a (m + 3) ⋅ B)
  have hredL : Reduces ((S ⋅ P) ⋅ .var w ⋅ .var a) target := by
    have h0 : Step ((S ⋅ P) ⋅ .var w ⋅ .var a) ((P ⋅ .var a) ⋅ B) := .root P (.var w) (.var a)
    have h1 := reduces_left (arm_reduces (m + 1) (S ⋅ S) (.var y) (.var a)) B
    have h2 : Step (((S ⋅ S) ⋅ dSeq y a (m + 1) ⋅ dSeq y a (m + 2)) ⋅ B)
        ((S ⋅ dSeq y a (m + 2) ⋅ (dSeq y a (m + 1) ⋅ dSeq y a (m + 2))) ⋅ B) :=
      .left (.root S (dSeq y a (m + 1)) (dSeq y a (m + 2)))
    have h3 : Step ((S ⋅ dSeq y a (m + 2) ⋅ dSeq y a (m + 3)) ⋅ B) target :=
      .root (dSeq y a (m + 2)) (dSeq y a (m + 3)) B
    exact .next h0 (reduces_trans h1 (.next h2 (.next h3 (.refl _))))
  have hconvApp : ConvBeta (toLam ((S ⋅ P) ⋅ .var w ⋅ .var a)) (toLam (R ⋅ .var w ⋅ .var a)) :=
    convBeta_left (convBeta_left hconv (.fvar w)) (.fvar a)
  have hconvT : ConvBeta (toLam target) (toLam (R ⋅ .var w ⋅ .var a)) :=
    .trans (convS_to_convBeta (convS_of_reduces hredL)).symm hconvApp
  have hsfT : isSFree target = true := by
    simp only [target, B, isSFree, hsf, Bool.and_self]
  have hcone := coneSArm_reduces_back (sFree_rigidity hsfT hconvT) (Or.inl rfl)
  rcases hcone with h1 | h2 | ⟨j, r, _, h3⟩ | h4 | h5
  · exfalso
    have hl := congrArg leaves (app_right_inj h1)
    have hge := (leaves_dSeq_strict y a (m + 3)).1
    simp only [leaves] at hl
    omega
  · exfalso
    have hl := congrArg leaves (app_right_inj h2)
    simp only [leaves] at hl
    omega
  · exfalso
    have hl := congrArg leaves (app_right_inj h3)
    simp only [leaves] at hl
    omega
  · exfalso
    have hl := congrArg leaves (app_right_inj h4)
    simp only [leaves] at hl
    omega
  · exact app_left_inj (app_left_inj h5)

/-! ## 6. Backward Cone 4: Global `λβ`-Rigidity of `A_var (m + 1) u y` (`u ≠ y`) -/

private def ArmVarElem (k u y a : Nat) (X : Term) : Prop :=
  X = S ⋅ sTower k (.var u) ⋅ .var y ⋅ .var a ∨
  ∃ j r, j + r = k ∧ X = (sTower j (.var u) ⋅ dSeq y a r) ⋅ dSeq y a (r + 1)

private theorem hasVar_sTower_var_true (u : Nat) : ∀ k, hasVar u (sTower k (.var u)) = true
  | 0 => by simp only [sTower, hasVar, decide_true]
  | k + 1 => by simp only [sTower, S, hasVar, hasVar_sTower_var_true u k, Bool.false_or]

private theorem hasVar_u_dSeq_false {u y a : Nat} (huy : u ≠ y) (hua : u ≠ a) (r : Nat) :
    hasVar u (dSeq y a r) = false := by
  have ha0 : hasVar u (.var a) = false := hasVar_var_ne hua
  have hy0 : hasVar u (.var y) = false := hasVar_var_ne huy
  have hb0 : hasVar u (.var y ⋅ .var a) = false := by
    unfold hasVar
    rw [hy0, ha0]
    rfl
  exact hasVar_false_fibW ha0 hb0 r

private theorem hasAntiRedex_sTower_var_app_dSeq {u y a : Nat}
    (huy : u ≠ y) (hua : u ≠ a) (j r : Nat) :
    hasAntiRedex (sTower j (.var u) ⋅ dSeq y a r) = false := by
  refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_)
    (hasAntiRedex_sTower_var u j) (hasAntiRedex_dSeq y a r)
  cases j with
  | zero => cases hz1
  | succ j' =>
    injection hz1 with hz1'
    have hu_false := hasVar_u_dSeq_false huy hua r
    cases hd : dSeq y a r with
    | s => rw [hd] at hz2; cases hz2
    | var _ => rw [hd] at hz2; cases hz2
    | app d1 d2 =>
      rw [hd] at hz2 hu_false
      injection hz2 with hz2'
      simp only [hasVar, Bool.or_eq_false_iff] at hu_false
      rw [← hz1', ← hz2']
      intro hh
      have hu_true := hasVar_sTower_var_true u j'
      rw [hh] at hu_true
      rw [hu_true] at hu_false
      cases hu_false.2

private theorem armVarElem_step_back {k u y a : Nat} (huy : u ≠ y) (hua : u ≠ a)
    {Y X : Term} (hs : Step Y X) (hx : ArmVarElem k u y a X) :
    ArmVarElem k u y a Y := by
  have hno : ∀ n, hasAntiRedex (dSeq y a n) = false := hasAntiRedex_dSeq y a
  rcases hx with rfl | ⟨j, r, hjr, rfl⟩
  · exact False.elim (no_step_into_of_no_antiRedex
      (hasAntiRedex_var_right a
        (hasAntiRedex_var_right y (hasAntiRedex_s_left (hasAntiRedex_sTower_var u k)))) hs)
  · cases r with
    | zero =>
      change Step Y ((sTower j (.var u) ⋅ .var a) ⋅ (.var y ⋅ .var a)) at hs
      cases hs with
      | root _ _ _ =>
        have hjk : j = k := by omega
        subst hjk
        exact Or.inl rfl
      | left hl =>
        exact False.elim (no_step_into_of_no_antiRedex
          (hasAntiRedex_sTower_var_app_dSeq huy hua j 0) hl)
      | right hr =>
        exact False.elim (no_step_into_of_no_antiRedex (hno 1) hr)
    | succ m =>
      change Step Y ((sTower j (.var u) ⋅ dSeq y a (m + 1)) ⋅ (dSeq y a m ⋅ dSeq y a (m + 1))) at hs
      cases hs with
      | root _ _ _ => exact Or.inr ⟨j + 1, m, by omega, rfl⟩
      | left hl =>
        exact False.elim (no_step_into_of_no_antiRedex
          (hasAntiRedex_sTower_var_app_dSeq huy hua j (m + 1)) hl)
      | right hr =>
        exact False.elim (no_step_into_of_no_antiRedex (hno (m + 2)) hr)

private theorem armVarElem_leaves_ge_four {k u y a : Nat} {X : Term}
    (hx : ArmVarElem k u y a X) : 4 ≤ leaves X := by
  rcases hx with rfl | ⟨j, r, _, rfl⟩
  · simp only [S, leaves, leaves_sTower]
    omega
  · have h1 := (leaves_dSeq_strict y a r).1
    have h2 := (leaves_dSeq_strict y a (r + 1)).1
    simp only [leaves, leaves_sTower]
    omega

private def InConeAVar (m u y a : Nat) (W : Term) : Prop :=
  (∃ XL XR, W = XL ⋅ XR ∧ ArmVarElem (m + 1) u y a XL ∧ ArmVarElem m u y a XR) ∨
  W = A_var (m + 1) u y ⋅ .var a ∨
  ∃ r, r ≤ m ∧
    W = S ⋅ (sTower (m + 1 - r) (.var u) ⋅ dSeq y a r) ⋅
            (sTower (m - r) (.var u) ⋅ dSeq y a r) ⋅ dSeq y a (r + 1)

private theorem coneAVar_step_back {m u y a : Nat} (huy : u ≠ y) (hua : u ≠ a)
    {Y W : Term} (hs : Step Y W) (hw : InConeAVar m u y a W) :
    InConeAVar m u y a Y := by
  rcases hw with ⟨XL, XR, rfl, hXL, hXR⟩ | rfl | ⟨r, hrm, rfl⟩
  · cases hs with
    | left hl =>
      exact Or.inl ⟨_, XR, rfl, armVarElem_step_back huy hua hl hXL, hXR⟩
    | right hr =>
      exact Or.inl ⟨XL, _, rfl, hXL, armVarElem_step_back huy hua hr hXR⟩
    | root x y' z =>
      rcases hXL with hL0 | ⟨j1, r1, hj1, hL1⟩
      · rcases hXR with hR0 | ⟨j2, r2, _, hR1⟩
        · have hxL := app_left_inj hL0
          have hzL := app_right_inj hL0
          have hyR := app_left_inj hR0
          subst hxL; subst hyR; subst hzL
          exact Or.inr (Or.inl rfl)
        · exfalso
          have hzL := app_right_inj hL0
          have hzR := app_right_inj hR1
          exact dSeq_succ_ne_var y a r2 a (hzR.symm.trans hzL)
      · rcases hXR with hR0 | ⟨j2, r2, hj2, hR1⟩
        · exfalso
          have hzL := app_right_inj hL1
          have hzR := app_right_inj hR0
          exact dSeq_succ_ne_var y a r1 a (hzL.symm.trans hzR)
        · have hxL := app_left_inj hL1
          have hzL := app_right_inj hL1
          have hyR := app_left_inj hR1
          have hzR := app_right_inj hR1
          have hd_eq : dSeq y a (r1 + 1) = dSeq y a (r2 + 1) := hzL.symm.trans hzR
          have hr_eq : r1 = r2 := Nat.succ.inj (dSeq_inj y a hd_eq)
          subst hr_eq
          have hrm1 : r1 ≤ m := by omega
          have hj1_eq : j1 = m + 1 - r1 := by omega
          have hj2_eq : j2 = m - r1 := by omega
          subst hj1_eq; subst hj2_eq; subst hxL; subst hyR; subst hzL
          exact Or.inr (Or.inr ⟨r1, hrm1, rfl⟩)
  · exfalso
    refine no_step_into_of_no_antiRedex (hasAntiRedex_var_right a ?_) hs
    have hLA : hasAntiRedex (S ⋅ sTower (m + 1) (.var u) ⋅ .var y) = false :=
      hasAntiRedex_var_right y (hasAntiRedex_s_left (hasAntiRedex_sTower_var u (m + 1)))
    have hRA : hasAntiRedex (S ⋅ sTower m (.var u) ⋅ .var y) = false :=
      hasAntiRedex_var_right y (hasAntiRedex_s_left (hasAntiRedex_sTower_var u m))
    simp only [A_var, Nat.add_sub_cancel]
    refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_) (hasAntiRedex_s_left hLA) hRA
    injection hz1 with hz1'
    injection hz2 with hz2'
    rw [← hz1', ← hz2']
    intro hh
    have hl := congrArg leaves hh
    simp only [S, leaves, leaves_sTower] at hl
    omega
  · exfalso
    let A1 := sTower (m + 1 - r) (.var u) ⋅ dSeq y a r
    let A2 := sTower (m - r) (.var u) ⋅ dSeq y a r
    have hnoA1 : hasAntiRedex A1 = false := hasAntiRedex_sTower_var_app_dSeq huy hua (m + 1 - r) r
    have hnoA2 : hasAntiRedex A2 = false := hasAntiRedex_sTower_var_app_dSeq huy hua (m - r) r
    have hnoD : hasAntiRedex (dSeq y a (r + 1)) = false := hasAntiRedex_dSeq y a (r + 1)
    have hinner : hasAntiRedex ((S ⋅ A1) ⋅ A2) = false := by
      refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_) (hasAntiRedex_s_left hnoA1) hnoA2
      injection hz1 with hz1'
      injection hz2 with hz2'
      rw [← hz1', ← hz2']
      intro hh
      have hl := congrArg leaves hh
      simp only [A1, leaves, leaves_sTower] at hl
      omega
    refine no_step_into_of_no_antiRedex ?_ hs
    refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_) hinner hnoD
    injection hz1 with hz1'
    obtain ⟨L_d, hLd⟩ := dSeq_succ_app y a r
    rw [hLd] at hz2
    injection hz2 with hz2'
    rw [← hz1', ← hz2']
    intro hh
    have huA2 : hasVar u (sTower (m - r) (.var u) ⋅ dSeq y a r) = true := by
      simp only [hasVar, hasVar_sTower_var_true u (m - r), Bool.true_or]
    have huD : hasVar u (dSeq y a r) = false := hasVar_u_dSeq_false huy hua r
    rw [hh] at huA2
    rw [huA2] at huD
    cases huD

private theorem coneAVar_reduces_back {m u y a : Nat} (huy : u ≠ y) (hua : u ≠ a)
    {Y W : Term} (hr : Reduces Y W) (hw : InConeAVar m u y a W) :
    InConeAVar m u y a Y := by
  induction hr with
  | refl _ => exact hw
  | next hs _ ih => exact coneAVar_step_back huy hua hs (ih hw)

/-- **Global `λβ`-Rigidity of `A_var (m + 1) u y` (`u ≠ y`)**: For all `m, u, y : Nat` with `u ≠ y`
    and all `R : Term`, `ConvBeta (toLam (A_var (m + 1) u y)) (toLam R) → R = A_var (m + 1) u y`. -/
theorem rigidity_A_var (m u y : Nat) (huy : u ≠ y) (R : Term)
    (hconv : ConvBeta (toLam (A_var (m + 1) u y)) (toLam R)) :
    R = A_var (m + 1) u y := by
  let a := u + y + 1
  have hua : u ≠ a := by omega
  have hsf : ∀ n, isSFree (dSeq y a n) = true := isSFree_fibW rfl rfl
  let target := ((.var u ⋅ dSeq y a (m + 1)) ⋅ dSeq y a (m + 2)) ⋅
                ((.var u ⋅ dSeq y a m) ⋅ dSeq y a (m + 1))
  have hredL : Reduces (A_var (m + 1) u y ⋅ .var a) target := by
    have h0 : Step (A_var (m + 1) u y ⋅ .var a)
        ((S ⋅ sTower (m + 1) (.var u) ⋅ .var y ⋅ .var a) ⋅
         (S ⋅ sTower m (.var u) ⋅ .var y ⋅ .var a)) :=
      .root _ _ (.var a)
    have h1 := arm_reduces (m + 1) (.var u) (.var y) (.var a)
    have h2 := arm_reduces m (.var u) (.var y) (.var a)
    exact .next h0 (reduces_app h1 h2)
  have hconvApp : ConvBeta (toLam (A_var (m + 1) u y ⋅ .var a)) (toLam (R ⋅ .var a)) :=
    convBeta_left hconv (.fvar a)
  have hconvT : ConvBeta (toLam target) (toLam (R ⋅ .var a)) :=
    .trans (convS_to_convBeta (convS_of_reduces hredL)).symm hconvApp
  have hsfT : isSFree target = true := by
    simp only [target, isSFree, hsf, Bool.and_self]
  have hinit : InConeAVar m u y a target :=
    Or.inl ⟨_, _, rfl,
      Or.inr ⟨0, m + 1, Nat.zero_add _, rfl⟩,
      Or.inr ⟨0, m, Nat.zero_add _, rfl⟩⟩
  have hcone := coneAVar_reduces_back huy hua (sFree_rigidity hsfT hconvT) hinit
  rcases hcone with ⟨XL, XR, h1, _, hXR⟩ | h2 | ⟨r, _, h3⟩
  · exfalso
    have hl := congrArg leaves (app_right_inj h1)
    have hge := armVarElem_leaves_ge_four hXR
    simp only [leaves] at hl
    omega
  · exact app_left_inj h2
  · exfalso
    exact dSeq_succ_ne_var y a r a (app_right_inj h3).symm

end FormalQ32
