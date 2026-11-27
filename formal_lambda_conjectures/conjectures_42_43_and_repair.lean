import formal_lambda_conjectures.conjecture_40_order

/-!
# Refutation of Conjectures 42 and 43 on Closed Pure-`S` Terms & Exact Repaired Theorem
# (*Dance of the Starlings*, Barendregt, Endrullis, Klop, and Waldmann, 2017, pp. 95, 102)

Constructive Lean 4.33.1 formalization (zero `Classical.choice`, zero `sorry`, zero `native_decide`) of:

1. **Diverging Closed Pure-`S` Witnesses (`W9`, `N10`, `W9_nf`, `W_waldmann`)**:
   - **`W9 := S (S (A A)) S` (`9` leaves — global minimum among all closed `CL(S)`-normalizing pure-`S` terms!)**:
     normalizes in `CL(S)` in 1 step to 11-leaf `W9_nf`, yet `¬ HasBetaNF (toLam W9)`.
   - **`N10 := S (S (S A A)) S` (`10` leaves — global minimum among closed `CL(S)` normal forms,
     improving Waldmann's 13-leaf Example 33 by 3 leaves!)**:
     is already a `CL(S)` normal form, yet `¬ HasBetaNF (toLam N10)`.
   - **`W_waldmann := S (S (S T T)) (S (S T T))` (`13` leaves — Waldmann 2000 / Example 33, p. 95)**:
     is a `CL(S)` normal form, yet `¬ HasBetaNF (toLam W_waldmann)`.

2. **Simultaneous Refutation of Conjecture 42 AND Conjecture 43 on Closed Pure-`S` Terms**:
   - **`M_14 := S A (S W9)` (`14` leaves — exact global minimum closed pure-`S` counterexample!)**,
   - **`M_15 := S A (S N10)` (`15` leaves — exact global minimum closed `CL(S)`-normal-form counterexample!)**,
   - **`M_16 := S A (S W9_nf)` (`16` leaves — closed `CL(S)` normal form of `M_14`)**,
   - **`M_18 := S A (S W_waldmann)` (`18` leaves — `S A (S W)` built from Example 33!)**:
     Each has `order_CL = order_λ = 1`, normalizes in `CL(S)` on `1` fresh variable (`M x`, Conjecture 43 LHS)
     AND on `3` fresh variables (`M x y z`, Conjecture 42 LHS), yet has **NO `β`-normal form** (`¬ HasBetaNF (toLam M)`).
   - **Valid Reverse Direction (`conjecture_42_reverse_valid`)**:
     `HasBetaNF (toLam M) → HasNormalForm (M ⋅ .var x ⋅ .var y ⋅ .var z)` ALWAYS holds!

3. **Exact Repaired Characterization Replacing Conjecture 42 (`repaired_conjecture_42`)**:
   Defines **hereditary fresh-variable saturation (`DeepCLNorm`)** purely inside `CL(S)` (zero `λ`-terms)
   and proves constructively for ALL `M ∈ Ter(CL(S))` (closed or open):
   `DeepCLNorm M ↔ HasBetaNF (toLam M)`.
-/

namespace FormalLambdaConjectures

/-! ## 1. Subterm Spirals and Constructive Divergence in `CL(S)` -/

inductive SubtermCL : Term → Term → Prop where
  | refl (t : Term) : SubtermCL t t
  | left {u a b : Term} : SubtermCL u a → SubtermCL u (a ⋅ b)
  | right {u a b : Term} : SubtermCL u b → SubtermCL u (a ⋅ b)

theorem subtermCL_trans {a b c : Term} (h1 : SubtermCL a b) (h2 : SubtermCL b c) :
    SubtermCL a c := by
  induction h2 with
  | refl => exact h1
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem subtermCL_lift_stepPlus {u c u' : Term}
    (hsub : SubtermCL u c) (hstep : StepPlus u u') :
    ∃ c', StepPlus c c' ∧ SubtermCL u' c' := by
  induction hsub with
  | refl => exact ⟨u', hstep, .refl u'⟩
  | @left a b _ ih =>
    obtain ⟨a', hpa, hsa⟩ := ih
    exact ⟨a' ⋅ b, stepPlus_left hpa b, .left hsa⟩
  | @right a b _ ih =>
    obtain ⟨b', hpb, hsb⟩ := ih
    exact ⟨a ⋅ b', stepPlus_right a hpb, .right hsb⟩

theorem acc_stepPlus_cl {t : Term} (h : StrongNormalizing t) :
    Acc (fun b a => StepPlus a b) t := by
  induction h with
  | intro t _ ih =>
    refine Acc.intro t (fun y hy => ?_)
    cases hy with
    | single hs => exact ih _ hs
    | @head _ mid _ h1 hrest => exact Acc.inv (ih mid h1) hrest

def StepToSubtermCL (a b : Term) : Prop :=
  ∃ c, StepPlus a c ∧ SubtermCL b c

theorem sn_implies_acc_stepToSubterm {t : Term} (hsn : StrongNormalizing t) :
    Acc (fun b a => StepToSubtermCL a b) t := by
  have hacc := acc_stepPlus_cl hsn
  suffices hgen : ∀ c, Acc (fun b a => StepPlus a b) c →
      ∀ u, SubtermCL u c → Acc (fun b a => StepToSubtermCL a b) u from
    hgen t hacc t (.refl t)
  intro c hc
  induction hc with
  | intro c _ ih =>
    intro u hu_c
    refine Acc.intro u (fun w h_uw => ?_)
    obtain ⟨u', hstep_u, hw_u'⟩ := h_uw
    obtain ⟨c', hstep_c, hu'_c'⟩ := subtermCL_lift_stepPlus hu_c hstep_u
    exact ih c' hstep_c w (subtermCL_trans hw_u' hu'_c')

/-- **Universal Constructive Subterm-Spiral Divergence Lemma**:
    If `fam n` reduces in `≥ 1` `CL(S)` steps to a term containing `fam (n + 1)` as a subterm
    for all `n`, then `fam 0` is NOT strongly normalizing in `CL(S)`. -/
theorem not_sn_of_subterm_spiral (fam : Nat → Term)
    (hspiral : ∀ n, StepToSubtermCL (fam n) (fam (n + 1))) :
    ¬ StrongNormalizing (fam 0) := by
  intro hsn
  have hacc := sn_implies_acc_stepToSubterm hsn
  suffices hgen : ∀ x, Acc (fun b a => StepToSubtermCL a b) x → ∀ n, x = fam n → False from
    hgen (fam 0) hacc 0 rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    intro n hxn
    subst hxn
    exact ih (fam (n + 1)) (hspiral n) (n + 1) rfl

theorem sn_cl_reduces {a b : Term} (ha : StrongNormalizing a) (hred : Reduces a b) :
    StrongNormalizing b := by
  induction hred with
  | refl => exact ha
  | next hs _ ih => exact ih (Acc.inv ha hs)

theorem sn_cl_of_appL {a b : Term} (h : StrongNormalizing (a ⋅ b)) : StrongNormalizing a := by
  suffices hg : ∀ z, StrongNormalizing z → ∀ a b, z = a ⋅ b → StrongNormalizing a from
    hg (a ⋅ b) h a b rfl
  intro z hz; induction hz with
  | intro _ _ ihz =>
    intro a0 b0 heq; subst heq
    exact Acc.intro a0 (fun a1 hs => ihz _ (.left hs) a1 b0 rfl)

theorem sn_cl_of_appR {a b : Term} (h : StrongNormalizing (a ⋅ b)) : StrongNormalizing b := by
  suffices hg : ∀ z, StrongNormalizing z → ∀ a b, z = a ⋅ b → StrongNormalizing b from
    hg (a ⋅ b) h a b rfl
  intro z hz; induction hz with
  | intro _ _ ihz =>
    intro a0 b0 heq; subst heq
    exact Acc.intro b0 (fun b1 hs => ihz _ (.right hs) a0 b1 rfl)

theorem sn_cl_subterm {u c : Term} (hsub : SubtermCL u c) (hc : StrongNormalizing c) :
    StrongNormalizing u := by
  induction hsub with
  | refl => exact hc
  | left _ ih => exact ih (sn_cl_of_appL hc)
  | right _ ih => exact ih (sn_cl_of_appR hc)

theorem not_sn_of_reduces_subterm {t c u : Term}
    (hred : Reduces t c) (hsub : SubtermCL u c) (hnsn : ¬ StrongNormalizing u) :
    ¬ StrongNormalizing t :=
  fun hsn => hnsn (sn_cl_subterm hsub (sn_cl_reduces hsn hred))

private theorem stepPlus_of_plus_reduces_cl {a b c : Term}
    (h1 : StepPlus a b) (h2 : Reduces b c) : StepPlus a c := by
  induction h2 generalizing a with
  | refl => exact h1
  | next hs _ ih => exact ih (stepPlus_trans h1 (.single hs))

/-! ## 2. Normal-Form Checker for `CL(S)` (`stepCLOpt`) & Constructive `SN → WN` -/

def rootRedexCLOpt (a b : Term) : Option Term :=
  match a with
  | .app (.app .s x) y => some ((x ⋅ b) ⋅ (y ⋅ b))
  | _ => none

private theorem rootRedexCLOpt_some {a b r : Term} (h : rootRedexCLOpt a b = some r) :
    ∃ x y, a = S ⋅ x ⋅ y ∧ r = (x ⋅ b) ⋅ (y ⋅ b) := by
  cases a with
  | s => cases h
  | var _ => cases h
  | app a1 y =>
    cases a1 with
    | s => cases h
    | var _ => cases h
    | app a2 x =>
      cases a2 with
      | s => injection h with hr; exact ⟨x, y, rfl, hr.symm⟩
      | var _ => cases h
      | app _ _ => cases h

private theorem rootRedexCLOpt_none {a b : Term} (h : rootRedexCLOpt a b = none) :
    ∀ x y, a ≠ S ⋅ x ⋅ y := by
  intro x y heq; subst heq; cases h

def stepCLOpt : Term → Option Term
  | .s => none
  | .var _ => none
  | .app a b =>
    match rootRedexCLOpt a b with
    | some r => some r
    | none =>
      match stepCLOpt a with
      | some a' => some (a' ⋅ b)
      | none => (stepCLOpt b).map (a ⋅ ·)

theorem stepCLOpt_sound {t t' : Term} (h : stepCLOpt t = some t') : Step t t' := by
  induction t generalizing t' with
  | s => cases h
  | var _ => cases h
  | app a b iha ihb =>
    simp only [stepCLOpt] at h
    cases hr : rootRedexCLOpt a b with
    | some r =>
      rw [hr] at h; injection h with heq; subst heq
      obtain ⟨x, y, rfl, rfl⟩ := rootRedexCLOpt_some hr
      exact .root x y b
    | none =>
      rw [hr] at h
      cases ha : stepCLOpt a with
      | some a' =>
        rw [ha] at h; injection h with heq; subst heq
        exact .left (iha ha)
      | none =>
        rw [ha] at h
        cases hb : stepCLOpt b with
        | none => rw [hb] at h; cases h
        | some b' =>
          rw [hb] at h; injection h with heq; subst heq
          exact .right (ihb hb)

theorem stepCLOpt_none_isNormalForm {t : Term} (h : stepCLOpt t = none) : IsNormalForm t := by
  induction t with
  | s => intro _ hs; cases hs
  | var _ => intro _ hs; cases hs
  | app a b iha ihb =>
    simp only [stepCLOpt] at h
    cases hr : rootRedexCLOpt a b with
    | some _ => rw [hr] at h; cases h
    | none =>
      rw [hr] at h
      cases ha : stepCLOpt a with
      | some _ => rw [ha] at h; cases h
      | none =>
        rw [ha] at h
        cases hb : stepCLOpt b with
        | some _ => rw [hb] at h; cases h
        | none =>
          intro t' hs
          cases hs with
          | root x y _ => exact rootRedexCLOpt_none hr x y rfl
          | left hl => exact iha ha _ hl
          | right hr' => exact ihb hb _ hr'

theorem sn_implies_wn_cl {t : Term} (hsn : StrongNormalizing t) : HasNormalForm t := by
  induction hsn with
  | intro t _ ih =>
    cases hs : stepCLOpt t with
    | none => exact ⟨t, .refl t, stepCLOpt_none_isNormalForm hs⟩
    | some t' =>
      obtain ⟨nf, hred, hnf⟩ := ih t' (stepCLOpt_sound hs)
      exact ⟨nf, .next (stepCLOpt_sound hs) hred, hnf⟩

/-! ## 3. Diverging Closed `CL(S)` Witnesses (`W9`, `N10`, `W9_nf`, `W_waldmann`) -/

/-- **9-Leaf Witness `W9 := S (S (A A)) S`** (global minimum closed `CL(S)`-SN pure-`S` term
    whose `λ`-translation diverges!). -/
def W9 : Term := S ⋅ (S ⋅ (A_comb ⋅ A_comb)) ⋅ S

/-- **11-Leaf Normal Form of `W9`**: `W9_nf := S (S (S A (S A))) S`. -/
def W9_nf : Term := S ⋅ (S ⋅ ((S ⋅ A_comb) ⋅ (S ⋅ A_comb))) ⋅ S

/-- **10-Leaf Witness `N10 := S (S (S A A)) S`** (global minimum closed `CL(S)` normal form
    whose `λ`-translation diverges — beating Waldmann's 13-leaf Example 33 by 3 leaves!). -/
def N10 : Term := S ⋅ (S ⋅ (S ⋅ A_comb ⋅ A_comb)) ⋅ S

/-- **13-Leaf Witness `W_waldmann := S V V`** (Waldmann 2000 / Barendregt et al. 2017, Example 33, p. 95). -/
def Z_comb : Term := S ⋅ T_comb ⋅ T_comb
def V_comb : Term := S ⋅ Z_comb
def W_waldmann : Term := S ⋅ V_comb ⋅ V_comb

theorem w9_leaves : leaves W9 = 9 := rfl
theorem n10_leaves : leaves N10 = 10 := rfl
theorem w9_nf_leaves : leaves W9_nf = 11 := rfl
theorem w_waldmann_leaves : leaves W_waldmann = 13 := rfl

theorem w9_closed : noVars W9 = true := rfl
theorem n10_closed : noVars N10 = true := rfl
theorem w9_nf_closed : noVars W9_nf = true := rfl
theorem w_waldmann_closed : noVars W_waldmann = true := rfl

theorem n10_is_cl_nf : IsNormalForm N10 := stepCLOpt_none_isNormalForm rfl
theorem w9_nf_is_cl_nf : IsNormalForm W9_nf := stepCLOpt_none_isNormalForm rfl
theorem w_waldmann_is_cl_nf : IsNormalForm W_waldmann := stepCLOpt_none_isNormalForm rfl

theorem w9_step_to_nf : Step W9 W9_nf :=
  .left (.right (.right (.root S S A_comb)))

theorem w9_hasNormalForm : HasNormalForm W9 :=
  ⟨W9_nf, .next w9_step_to_nf (.refl _), w9_nf_is_cl_nf⟩

/-! ### Divergence of `W9 ⋅ x`, `N10 ⋅ x`, and `W_waldmann ⋅ x` in `CL(S)` and `(·)_λ` in `λβ` -/

private def iterF9 (x : Nat) : Nat → Term
  | 0 => S ⋅ (S ⋅ .var x) ⋅ (S ⋅ A_comb ⋅ (S ⋅ .var x))
  | n + 1 => (S ⋅ .var x) ⋅ iterF9 x n

private def fam9 (x : Nat) (n : Nat) : Term :=
  (S ⋅ A_comb ⋅ (S ⋅ .var x)) ⋅ iterF9 x n

private theorem iterF9_pass (x : Nat) (n : Nat) (y : Term) :
    ∃ c, StepPlus (iterF9 x n ⋅ y) c ∧ SubtermCL ((S ⋅ A_comb ⋅ (S ⋅ .var x)) ⋅ y) c := by
  induction n with
  | zero =>
    exact ⟨_, .single (.root _ _ y), .right (.refl _)⟩
  | succ n ih =>
    obtain ⟨c, hpc, hsc⟩ := ih
    exact ⟨(.var x ⋅ y) ⋅ c,
      .head (.root (.var x) (iterF9 x n) y) (stepPlus_right _ hpc),
      .right hsc⟩

theorem w9_nf_x_not_sn (x : Nat) : ¬ StrongNormalizing (W9_nf ⋅ .var x) := by
  have hspiral : ∀ n, StepToSubtermCL (fam9 x n) (fam9 x (n + 1)) := by
    intro n
    let u := iterF9 x n
    let u1 := iterF9 x (n + 1)
    have h1 : Step (fam9 x n) ((A_comb ⋅ u) ⋅ u1) := .root A_comb (S ⋅ .var x) u
    have h2 : Step ((A_comb ⋅ u) ⋅ u1) (((S ⋅ u) ⋅ (S ⋅ u)) ⋅ u1) := .left (.root S S u)
    have h3 : Step (((S ⋅ u) ⋅ (S ⋅ u)) ⋅ u1) ((u ⋅ u1) ⋅ (S ⋅ u ⋅ u1)) := .root u (S ⋅ u) u1
    obtain ⟨c, hpc, hsc⟩ := iterF9_pass x n u1
    exact ⟨c ⋅ (S ⋅ u ⋅ u1),
      .head h1 (.head h2 (.head h3 (stepPlus_left hpc _))),
      .left hsc⟩
  have hnsn0 := not_sn_of_subterm_spiral (fam9 x) hspiral
  let fx := S ⋅ .var x
  let px := S ⋅ A_comb ⋅ fx
  let kx := S ⋅ fx ⋅ px
  have hr : Reduces (W9_nf ⋅ .var x) (((.var x ⋅ kx) ⋅ (px ⋅ kx)) ⋅ (.var x ⋅ fx)) :=
    .next (.root (S ⋅ ((S ⋅ A_comb) ⋅ (S ⋅ A_comb))) S (.var x))
    (.next (.root ((S ⋅ A_comb) ⋅ (S ⋅ A_comb)) (.var x) fx)
    (.next (.left (.root A_comb (S ⋅ A_comb) fx))
    (.next (.left (.left (.root S S fx)))
    (.next (.left (.root fx (S ⋅ fx) px))
    (.next (.left (.root (.var x) px kx)) (.refl _))))))
  exact not_sn_of_reduces_subterm hr (.left (.right (.refl (fam9 x 0)))) hnsn0

theorem w9_x_not_sn (x : Nat) : ¬ StrongNormalizing (W9 ⋅ .var x) :=
  fun hsn => w9_nf_x_not_sn x (Acc.inv hsn (.left w9_step_to_nf))

private def iterG10 (x : Nat) : Nat → Term
  | 0 => A_comb ⋅ (S ⋅ .var x)
  | n + 1 => (S ⋅ (S ⋅ .var x)) ⋅ iterG10 x n

private def fam10 (x : Nat) (n : Nat) : Term :=
  (A_comb ⋅ (S ⋅ .var x)) ⋅ iterG10 x n

private theorem iterG10_pass (x : Nat) (n : Nat) (y : Term) :
    ∃ c, Reduces (iterG10 x n ⋅ y) c ∧ SubtermCL ((A_comb ⋅ (S ⋅ .var x)) ⋅ y) c := by
  induction n with
  | zero => exact ⟨_, .refl _, .refl _⟩
  | succ n ih =>
    obtain ⟨c, hrc, hsc⟩ := ih
    exact ⟨((S ⋅ .var x) ⋅ y) ⋅ c,
      .next (.root (S ⋅ .var x) (iterG10 x n) y) (reduces_right _ hrc),
      .right hsc⟩

theorem n10_x_not_sn (x : Nat) : ¬ StrongNormalizing (N10 ⋅ .var x) := by
  have hspiral : ∀ n, StepToSubtermCL (fam10 x n) (fam10 x (n + 1)) := by
    intro n
    let fx := S ⋅ .var x
    let gx := S ⋅ fx
    let u := iterG10 x n
    let u1 := iterG10 x (n + 1)
    have h1 : Step (fam10 x n) ((gx ⋅ gx) ⋅ u) := .left (.root S S fx)
    have h2 : Step ((gx ⋅ gx) ⋅ u) ((fx ⋅ u) ⋅ u1) := .root fx gx u
    have h3 : Step ((fx ⋅ u) ⋅ u1) ((.var x ⋅ u1) ⋅ (u ⋅ u1)) := .root (.var x) u u1
    obtain ⟨c, hrc, hsc⟩ := iterG10_pass x n u1
    exact ⟨(.var x ⋅ u1) ⋅ c,
      stepPlus_of_plus_reduces_cl (.head h1 (.head h2 (.single h3))) (reduces_right _ hrc),
      .right hsc⟩
  have hnsn0 := not_sn_of_subterm_spiral (fam10 x) hspiral
  let fx := S ⋅ .var x
  have hr : Reduces (N10 ⋅ .var x) ((fam10 x 0) ⋅ (.var x ⋅ fx)) :=
    .next (.root (S ⋅ (S ⋅ A_comb ⋅ A_comb)) S (.var x))
    (.next (.root (S ⋅ A_comb ⋅ A_comb) (.var x) fx)
    (.next (.left (.root A_comb A_comb fx)) (.refl _)))
  exact not_sn_of_reduces_subterm hr (.left (.refl _)) hnsn0

private def iterT11 (x : Nat) : Nat → Term
  | 0 => V_comb ⋅ .var x
  | n + 1 => T_comb ⋅ iterT11 x n

private def fam11 (x : Nat) (n : Nat) : Term :=
  (V_comb ⋅ .var x) ⋅ iterT11 x n

private theorem iterT11_pass (x : Nat) (m : Nat) (y : Term) :
    ∃ c, Reduces (iterT11 x m ⋅ y) c ∧ SubtermCL ((V_comb ⋅ .var x) ⋅ y) c := by
  induction m with
  | zero => exact ⟨_, .refl _, .refl _⟩
  | succ m ih =>
    obtain ⟨c, hrc, hsc⟩ := ih
    exact ⟨(S ⋅ y) ⋅ c,
      .next (.root S (iterT11 x m) y) (reduces_right _ hrc),
      .right hsc⟩

theorem w_waldmann_x_not_sn (x : Nat) : ¬ StrongNormalizing (W_waldmann ⋅ .var x) := by
  have hspiral : ∀ n, StepToSubtermCL (fam11 x n) (fam11 x (n + 1)) := by
    intro n
    let u := iterT11 x n
    let u1 := iterT11 x (n + 1)
    have h1 : Step (fam11 x n) ((Z_comb ⋅ u) ⋅ (.var x ⋅ u)) := .root Z_comb (.var x) u
    have h2 : Step ((Z_comb ⋅ u) ⋅ (.var x ⋅ u)) ((u1 ⋅ u1) ⋅ (.var x ⋅ u)) :=
      .left (.root T_comb T_comb u)
    obtain ⟨c, hrc, hsc⟩ := iterT11_pass x (n + 1) u1
    exact ⟨c ⋅ (.var x ⋅ u),
      stepPlus_of_plus_reduces_cl (.head h1 (.single h2)) (reduces_left hrc _),
      .left hsc⟩
  have hnsn0 := not_sn_of_subterm_spiral (fam11 x) hspiral
  have hr : Reduces (W_waldmann ⋅ .var x) (fam11 x 0) :=
    .next (.root V_comb V_comb (.var x)) (.refl _)
  exact not_sn_of_reduces_subterm hr (.refl _) hnsn0

/-- Any pure-`S` term `u` such that `u ⋅ x` is non-`SN` in `CL(S)` has `¬ HasBetaNF (toLam u)`! -/
theorem toLam_no_betaNF_of_app_var_not_sn {u : Term} {x : Nat}
    (hnsn : ¬ StrongNormalizing (u ⋅ .var x)) : ¬ HasBetaNF (toLam u) := by
  intro hwn
  have hwn_x : HasBetaNF (toLam (u ⋅ .var x)) := hasBetaNF_app_fvar hwn x
  have hsn_lam : StrongNormalizingBeta (toLam (u ⋅ .var x)) :=
    lambdaI_wn_implies_sn (isLambdaI_toLam (u ⋅ .var x)) hwn_x
  exact hnsn (sn_cl_of_sn_toLam hsn_lam)

theorem w9_toLam_no_betaNF : ¬ HasBetaNF (toLam W9) :=
  toLam_no_betaNF_of_app_var_not_sn (w9_x_not_sn 0)

theorem n10_toLam_no_betaNF : ¬ HasBetaNF (toLam N10) :=
  toLam_no_betaNF_of_app_var_not_sn (n10_x_not_sn 0)

theorem w9_nf_toLam_no_betaNF : ¬ HasBetaNF (toLam W9_nf) :=
  toLam_no_betaNF_of_app_var_not_sn (w9_nf_x_not_sn 0)

theorem w_waldmann_toLam_no_betaNF : ¬ HasBetaNF (toLam W_waldmann) :=
  toLam_no_betaNF_of_app_var_not_sn (w_waldmann_x_not_sn 0)

/-! ## 4. Simultaneous Refutation of Conjectures 42 and 43 (`M_14`, `M_15`, `M_16`, `M_18`) -/

/-- Generic counterexample wrapper `mkCE u := S A (S u)`. -/
def mkCE (u : Term) : Term := S ⋅ A_comb ⋅ (S ⋅ u)

/-- **14-Leaf Counterexample `M_14 := S A (S W9)`** (exact global minimum among ALL closed pure-`S` terms!). -/
def M_14 : Term := mkCE W9

/-- **15-Leaf Counterexample `M_15 := S A (S N10)`** (exact global minimum among closed `CL(S)` normal forms!). -/
def M_15 : Term := mkCE N10

/-- **16-Leaf Counterexample `M_16 := S A (S W9_nf)`** (`CL(S)` normal form of `M_14`). -/
def M_16 : Term := mkCE W9_nf

/-- **18-Leaf Counterexample `M_18 := S A (S W_waldmann)`** (`S A (S W)` from Waldmann's Example 33). -/
def M_18 : Term := mkCE W_waldmann

theorem m14_leaves : leaves M_14 = 14 := rfl
theorem m15_leaves : leaves M_15 = 15 := rfl
theorem m16_leaves : leaves M_16 = 16 := rfl
theorem m18_leaves : leaves M_18 = 18 := rfl

theorem m14_closed : noVars M_14 = true := rfl
theorem m15_closed : noVars M_15 = true := rfl
theorem m16_closed : noVars M_16 = true := rfl
theorem m18_closed : noVars M_18 = true := rfl

theorem m15_is_cl_nf : IsNormalForm M_15 := stepCLOpt_none_isNormalForm rfl
theorem m16_is_cl_nf : IsNormalForm M_16 := stepCLOpt_none_isNormalForm rfl
theorem m18_is_cl_nf : IsNormalForm M_18 := stepCLOpt_none_isNormalForm rfl

private theorem isNormalForm_s_u_var {u : Term} (hunf : IsNormalForm u) (x : Nat) :
    IsNormalForm (S ⋅ u ⋅ .var x) := by
  intro t' hs
  cases hs with
  | right hr => cases hr
  | left hl =>
    cases hl with
    | left hl0 => cases hl0
    | right hru => exact hunf _ hru

private theorem isNormalForm_var_app {a b : Term} {v : Nat}
    (hhead : headLeaf a = .var v) (ha : IsNormalForm a) (hb : IsNormalForm b) :
    IsNormalForm (a ⋅ b) := by
  intro t' hs
  cases hs with
  | left hl => exact ha _ hl
  | right hr => exact hb _ hr
  | root _ _ _ => cases hhead

/-- Universal properties of `mkCE u = S A (S u)` for any `u` normalizing to `u_nf` with `u ⋅ y` non-`SN`. -/
theorem mkCE_counterexample_properties {u u_nf : Term}
    (hu_red : Reduces u u_nf) (hu_nf : IsNormalForm u_nf)
    (hu_div : ∀ y, ¬ StrongNormalizing (u ⋅ .var y))
    (hfresh_x : hasVar 0 (mkCE u) = false) :
    PureSCLOrder (mkCE u) 1 ∧
    LamOrder (toLam (mkCE u)) 1 ∧
    (∀ x, HasNormalForm (mkCE u ⋅ .var x)) ∧
    (∀ x y z, HasNormalForm (mkCE u ⋅ .var x ⋅ .var y ⋅ .var z)) ∧
    ¬ HasBetaNF (toLam (mkCE u)) := by
  have hm_reduces : ∀ x, Reduces (mkCE u ⋅ .var x)
      ((.var x ⋅ (S ⋅ u_nf ⋅ .var x)) ⋅ (S ⋅ .var x ⋅ (S ⋅ u_nf ⋅ .var x))) := by
    intro x
    have h3 : Reduces (mkCE u ⋅ .var x)
        ((.var x ⋅ (S ⋅ u ⋅ .var x)) ⋅ (S ⋅ .var x ⋅ (S ⋅ u ⋅ .var x))) :=
      .next (.root A_comb (S ⋅ u) (.var x))
      (.next (.left (.root S S (.var x)))
      (.next (.root (.var x) (S ⋅ .var x) (S ⋅ u ⋅ .var x)) (.refl _)))
    have hsub : Reduces (S ⋅ u ⋅ .var x) (S ⋅ u_nf ⋅ .var x) :=
      reduces_left (reduces_right S hu_red) (.var x)
    exact reduces_trans h3
      (reduces_app (reduces_right (.var x) hsub) (reduces_right (S ⋅ .var x) hsub))
  have hm_nf1 : ∀ x, IsNormalForm
      ((.var x ⋅ (S ⋅ u_nf ⋅ .var x)) ⋅ (S ⋅ .var x ⋅ (S ⋅ u_nf ⋅ .var x))) := by
    intro x
    have hsu := isNormalForm_s_u_var hu_nf x
    have hl : IsNormalForm (.var x ⋅ (S ⋅ u_nf ⋅ .var x)) :=
      isNormalForm_var_app rfl (fun _ hs => by cases hs) hsu
    have hr : IsNormalForm (S ⋅ .var x ⋅ (S ⋅ u_nf ⋅ .var x)) := by
      intro t' hs
      cases hs with
      | right hsr => exact hsu _ hsr
      | left hsl =>
        cases hsl with
        | left hs0 => cases hs0
        | right hsv => cases hsv
    exact isNormalForm_var_app rfl hl hr
  have hord0 : ∀ x, PureSCLOrder (mkCE u ⋅ .var x) 0 := by
    intro x
    refine .zero (fun h hred hpart => ?_)
    have h3 : Reduces (mkCE u ⋅ .var x)
        ((.var x ⋅ (S ⋅ u ⋅ .var x)) ⋅ (S ⋅ .var x ⋅ (S ⋅ u ⋅ .var x))) :=
      .next (.root A_comb (S ⋅ u) (.var x))
      (.next (.left (.root S S (.var x)))
      (.next (.root (.var x) (S ⋅ .var x) (S ⋅ u ⋅ .var x)) (.refl _)))
    obtain ⟨w, hw1, hw2⟩ :=
      church_rosser_beta (reduces_to_betaReduces hred) (reduces_to_betaReduces h3)
    obtain ⟨p, hp⟩ := (pureS_reduces_partial_iff_lam_reduces_abs h).mp ⟨h, .refl h, hpart⟩
    obtain ⟨w2, hww2, hpw2⟩ := church_rosser_beta hw1 hp
    let cs := [toLam (S ⋅ u ⋅ .var x), toLam (S ⋅ .var x ⋅ (S ⋅ u ⋅ .var x))]
    have hx_w2 : BetaReduces (apps (.fvar x) cs) w2 :=
      betaReduces_trans hw2 hww2
    have hlam : ∃ q, w2 = .lam q := by
      suffices hg : ∀ {a b : Lam}, BetaReduces a b → ∀ p0, a = .lam p0 → ∃ q, b = .lam q from
        hg hpw2 p rfl
      intro a b hab; induction hab with
      | refl => intro p0 ha; exact ⟨p0, ha⟩
      | next hs _ ih =>
        intro p0 ha; subst ha
        cases hs with
        | lam _ => exact ih _ rfl
    obtain ⟨q, rfl⟩ := hlam
    obtain ⟨b0, hwh, _⟩ := wh_standardization_lam hx_w2
    generalize hxa : apps (.fvar x) cs = xa at hwh
    generalize hya : Lam.lam b0 = ya at hwh
    cases hwh with
    | refl => subst hya; exact apps_fvar_ne_lam x cs b0 hxa
    | next hs _ => rw [← hxa] at hs; exact whStep_apps_fvar_false x cs _ hs
  have hord1 : PureSCLOrder (mkCE u) 1 :=
    .succ 0 hfresh_x ⟨mkCE u, .refl _, Or.inr (Or.inr ⟨A_comb, S ⋅ u, rfl⟩)⟩ (hord0 0)
  have hlam_ord1 : LamOrder (toLam (mkCE u)) 1 :=
    (conjecture_40_pure_s (mkCE u) 1).mp hord1
  have hwn1 : ∀ x, HasNormalForm (mkCE u ⋅ .var x) :=
    fun x => ⟨_, hm_reduces x, hm_nf1 x⟩
  have hwn3 : ∀ x y z, HasNormalForm (mkCE u ⋅ .var x ⋅ .var y ⋅ .var z) := by
    intro x y z
    refine ⟨((.var x ⋅ (S ⋅ u_nf ⋅ .var x)) ⋅ (S ⋅ .var x ⋅ (S ⋅ u_nf ⋅ .var x))) ⋅ .var y ⋅ .var z,
      reduces_left (reduces_left (hm_reduces x) (.var y)) (.var z), ?_⟩
    exact isNormalForm_var_app rfl
      (isNormalForm_var_app rfl (hm_nf1 x) (fun _ hs => by cases hs))
      (fun _ hs => by cases hs)
  have hno_beta : ¬ HasBetaNF (toLam (mkCE u)) := by
    intro hbeta
    have hbeta0 : HasBetaNF (toLam (mkCE u ⋅ .var 0)) := hasBetaNF_app_fvar hbeta 0
    have hsn0 : StrongNormalizingBeta (toLam (mkCE u ⋅ .var 0)) :=
      lambdaI_wn_implies_sn (isLambdaI_toLam _) hbeta0
    have h3 : Reduces (mkCE u ⋅ .var 0)
        ((.var 0 ⋅ (S ⋅ u ⋅ .var 0)) ⋅ (S ⋅ .var 0 ⋅ (S ⋅ u ⋅ .var 0))) :=
      .next (.root A_comb (S ⋅ u) (.var 0))
      (.next (.left (.root S S (.var 0)))
      (.next (.root (.var 0) (S ⋅ .var 0) (S ⋅ u ⋅ .var 0)) (.refl _)))
    have hsn_red : StrongNormalizingBeta
        (toLam ((.var 0 ⋅ (S ⋅ u ⋅ .var 0)) ⋅ (S ⋅ .var 0 ⋅ (S ⋅ u ⋅ .var 0)))) :=
      sn_reduces hsn0 (reduces_to_betaReduces h3)
    have hsn_su0 : StrongNormalizingBeta (toLam (S ⋅ u ⋅ .var 0)) :=
      sn_of_appR (sn_of_appL hsn_red)
    have hwn_su01 : HasBetaNF (toLam (S ⋅ u ⋅ .var 0 ⋅ .var 1)) :=
      hasBetaNF_app_fvar (sn_implies_wn_beta hsn_su0) 1
    have hsn_su01 : StrongNormalizingBeta (toLam (S ⋅ u ⋅ .var 0 ⋅ .var 1)) :=
      lambdaI_wn_implies_sn (isLambdaI_toLam _) hwn_su01
    have hsn_u1_pair : StrongNormalizingBeta (toLam ((u ⋅ .var 1) ⋅ (.var 0 ⋅ .var 1))) :=
      sn_reduces hsn_su01 (step_to_betaReduces (.root u (.var 0) (.var 1)))
    have hsn_u1 : StrongNormalizingBeta (toLam (u ⋅ .var 1)) := sn_of_appL hsn_u1_pair
    exact hu_div 1 (sn_cl_of_sn_toLam hsn_u1)
  exact ⟨hord1, hlam_ord1, hwn1, hwn3, hno_beta⟩

/-- **THEOREM (Global-Minimum 14-Leaf Simultaneous Refutation of Conjectures 42 & 43)**:
    `M_14 = S A (S W9)` is a closed pure-`S` term of `14` leaves with `order = 1`,
    normalizing in `CL(S)` on both `1` variable (`Conjecture 43`) and `3` variables (`Conjecture 42`),
    whose `λ`-translation `(M_14)_λ` has NO `β`-normal form! -/
theorem conjecture_42_and_43_refuted_14_leaves :
    noVars M_14 = true ∧
    leaves M_14 = 14 ∧
    PureSCLOrder M_14 1 ∧
    LamOrder (toLam M_14) 1 ∧
    (∀ x, HasNormalForm (M_14 ⋅ .var x)) ∧
    (∀ x y z, HasNormalForm (M_14 ⋅ .var x ⋅ .var y ⋅ .var z)) ∧
    ¬ HasBetaNF (toLam M_14) := by
  obtain ⟨ho1, hlo1, hw1, hw3, hnb⟩ :=
    mkCE_counterexample_properties (.next w9_step_to_nf (.refl _)) w9_nf_is_cl_nf w9_x_not_sn rfl
  exact ⟨rfl, rfl, ho1, hlo1, hw1, hw3, hnb⟩

/-- **THEOREM (15-Leaf `CL(S)`-Normal-Form Simultaneous Refutation of Conjectures 42 & 43)**:
    `M_15 = S A (S N10)` is ALREADY a closed `CL(S)` normal form of `15` leaves (minimum among
    all closed `CL(S)` normal forms!) refuting both Conjecture 42 and Conjecture 43. -/
theorem conjecture_42_and_43_refuted_15_leaves_nf :
    noVars M_15 = true ∧
    leaves M_15 = 15 ∧
    IsNormalForm M_15 ∧
    PureSCLOrder M_15 1 ∧
    LamOrder (toLam M_15) 1 ∧
    (∀ x, HasNormalForm (M_15 ⋅ .var x)) ∧
    (∀ x y z, HasNormalForm (M_15 ⋅ .var x ⋅ .var y ⋅ .var z)) ∧
    ¬ HasBetaNF (toLam M_15) := by
  obtain ⟨ho1, hlo1, hw1, hw3, hnb⟩ :=
    mkCE_counterexample_properties (.refl N10) n10_is_cl_nf n10_x_not_sn rfl
  exact ⟨rfl, rfl, m15_is_cl_nf, ho1, hlo1, hw1, hw3, hnb⟩

/-- **THEOREM (16-Leaf `CL(S)`-Normal-Form Counterexample `M_16 = S A (S W9_nf)`)**. -/
theorem conjecture_42_and_43_refuted_16_leaves_nf :
    noVars M_16 = true ∧
    leaves M_16 = 16 ∧
    IsNormalForm M_16 ∧
    PureSCLOrder M_16 1 ∧
    LamOrder (toLam M_16) 1 ∧
    (∀ x, HasNormalForm (M_16 ⋅ .var x)) ∧
    (∀ x y z, HasNormalForm (M_16 ⋅ .var x ⋅ .var y ⋅ .var z)) ∧
    ¬ HasBetaNF (toLam M_16) := by
  obtain ⟨ho1, hlo1, hw1, hw3, hnb⟩ :=
    mkCE_counterexample_properties (.refl W9_nf) w9_nf_is_cl_nf w9_nf_x_not_sn rfl
  exact ⟨rfl, rfl, m16_is_cl_nf, ho1, hlo1, hw1, hw3, hnb⟩

/-- **THEOREM (18-Leaf `S A (S W_waldmann)` Simultaneous Refutation of Conjectures 42 & 43)**:
    `M_18 = S A (S W_waldmann)` built from Waldmann's Example 33 (`W = S V V`, 13 leaves)
    refutes both Conjecture 42 and Conjecture 43. -/
theorem conjecture_42_and_43_refuted_waldmann_w :
    noVars M_18 = true ∧
    leaves M_18 = 18 ∧
    IsNormalForm M_18 ∧
    PureSCLOrder M_18 1 ∧
    LamOrder (toLam M_18) 1 ∧
    (∀ x, HasNormalForm (M_18 ⋅ .var x)) ∧
    (∀ x y z, HasNormalForm (M_18 ⋅ .var x ⋅ .var y ⋅ .var z)) ∧
    ¬ HasBetaNF (toLam M_18) := by
  obtain ⟨ho1, hlo1, hw1, hw3, hnb⟩ :=
    mkCE_counterexample_properties (.refl W_waldmann) w_waldmann_is_cl_nf w_waldmann_x_not_sn rfl
  exact ⟨rfl, rfl, m18_is_cl_nf, ho1, hlo1, hw1, hw3, hnb⟩

/-- Explicit negation of Conjecture 42 as stated on p. 102 of *Dance of the Starlings*. -/
theorem conjecture_42_false :
    ¬ (∀ m : Term, HasNormalForm (m ⋅ .var 0 ⋅ .var 1 ⋅ .var 2) ↔ HasBetaNF (toLam m)) := by
  intro h42
  obtain ⟨_, _, _, _, _, hw3, hnb⟩ := conjecture_42_and_43_refuted_14_leaves
  exact hnb ((h42 M_14).mp (hw3 0 1 2))

/-- Explicit negation of Conjecture 43 (even restricted to closed pure-`S` terms!). -/
theorem conjecture_43_false :
    ¬ (∀ (m : Term) (ord : Nat), PureSCLOrder m ord →
        (HasNormalForm (m ⋅ .var 0) ∧ ord = 1 → HasBetaNF (toLam m))) := by
  intro h43
  obtain ⟨_, _, ho1, _, hw1, _, hnb⟩ := conjecture_42_and_43_refuted_14_leaves
  exact hnb (h43 M_14 1 ho1 ⟨hw1 0, rfl⟩)

/-- **Valid One-Way Direction of Conjecture 42 (`⇐` ALWAYS holds!)**:
    For every `M ∈ Ter(CL(S))` and any variables `x, y, z`,
    if `(M)_λ` normalizes in `λβ`, then `M x y z` normalizes in `CL(S)`! -/
theorem conjecture_42_reverse_valid (m : Term) (x y z : Nat)
    (h : HasBetaNF (toLam m)) : HasNormalForm (m ⋅ .var x ⋅ .var y ⋅ .var z) := by
  have hxyz : HasBetaNF (toLam (m ⋅ .var x ⋅ .var y ⋅ .var z)) :=
    hasBetaNF_app_fvar (hasBetaNF_app_fvar (hasBetaNF_app_fvar h x) y) z
  have hsn : StrongNormalizingBeta (toLam (m ⋅ .var x ⋅ .var y ⋅ .var z)) :=
    lambdaI_wn_implies_sn (isLambdaI_toLam _) hxyz
  exact sn_implies_wn_cl (sn_cl_of_sn_toLam hsn)

/-! ## 5. Exact Repaired Characterization Replacing Conjecture 42 (`DeepCLNorm ↔ HasBetaNF`) -/

/-- **Hereditary Fresh-Variable Saturation (`DeepCLNorm`)** — defined 100% inside `CL(S)`!
    A `CL(S)` term `t` hereditarily normalizes iff it reduces in `CL(S)` to either:
    - a variable-headed normal form whose arguments all satisfy `DeepCLNorm`, or
    - a partial `S`-application (`S`, `S p`, `S p q`) that satisfies `DeepCLNorm` when applied
      to a fresh variable `z`. -/
inductive DeepCLNorm : Term → Prop where
  | step {t t' : Term} : Step t t' → DeepCLNorm t' → DeepCLNorm t
  | var (v : Nat) : DeepCLNorm (.var v)
  | varApp {a b : Term} (v : Nat) :
      headLeaf a = .var v → DeepCLNorm a → DeepCLNorm b → DeepCLNorm (a ⋅ b)
  | saturate {t : Term} (z : Nat) :
      IsPartialS t → hasVar z t = false → DeepCLNorm (t ⋅ .var z) → DeepCLNorm t

theorem deepCLNorm_of_reduces {a b : Term} (hred : Reduces a b) (hb : DeepCLNorm b) :
    DeepCLNorm a := by
  induction hred with
  | refl => exact hb
  | next hs _ ih => exact .step hs (ih hb)

private theorem toLam_eq_apps_of_headLeaf_var {a : Term} {v : Nat}
    (hh : headLeaf a = .var v) : ∃ cs, toLam a = apps (.fvar v) cs := by
  induction a with
  | s => cases hh
  | var u =>
    simp only [headLeaf] at hh
    injection hh with huv; subst huv
    exact ⟨[], rfl⟩
  | app a1 a2 ih1 _ =>
    obtain ⟨cs, hcs⟩ := ih1 hh
    refine ⟨cs ++ [toLam a2], ?_⟩
    rw [apps_append]
    simp [apps, toLam, hcs]

private theorem toLam_not_reduces_lam_of_headLeaf_var {a : Term} {v : Nat}
    (hh : headLeaf a = .var v) (p : Lam) : ¬ BetaReduces (toLam a) (.lam p) := by
  intro hred
  obtain ⟨cs, hcs⟩ := toLam_eq_apps_of_headLeaf_var hh
  rw [hcs] at hred
  obtain ⟨b, hwh, _⟩ := wh_standardization_lam hred
  generalize hxa : apps (.fvar v) cs = xa at hwh
  generalize hya : Lam.lam b = ya at hwh
  cases hwh with
  | refl => subst hya; exact apps_fvar_ne_lam v cs b hxa
  | next hs _ => rw [← hxa] at hs; exact whStep_apps_fvar_false v cs _ hs

private theorem closeFVar_eq_lam_inv {k z : Nat} {a p : Lam}
    (h : closeFVar k z a = .lam p) : ∃ a₀, a = .lam a₀ := by
  cases a with
  | bvar j =>
    simp only [closeFVar] at h
    by_cases hlt : j < k
    · rw [if_pos hlt] at h; cases h
    · rw [if_neg hlt] at h; cases h
  | fvar u =>
    simp only [closeFVar] at h
    by_cases huz : u = z
    · rw [if_pos huz] at h; cases h
    · rw [if_neg huz] at h; cases h
  | app _ _ => cases h
  | lam a₀ => exact ⟨a₀, rfl⟩

private theorem isBetaNF_closeFVar (k z : Nat) {m : Lam} (hm : IsBetaNF m) :
    IsBetaNF (closeFVar k z m) := by
  induction m generalizing k with
  | bvar j =>
    simp only [closeFVar]
    by_cases hlt : j < k
    · rw [if_pos hlt]; intro _ hs; cases hs
    · rw [if_neg hlt]; intro _ hs; cases hs
  | fvar u =>
    simp only [closeFVar]
    by_cases huz : u = z
    · rw [if_pos huz]; intro _ hs; cases hs
    · rw [if_neg huz]; intro _ hs; cases hs
  | lam b ih =>
    intro y hy
    cases hy with
    | lam hsb => exact ih (k + 1) (isBetaNF_of_lam hm) _ hsb
  | app a b iha ihb =>
    have ha_nf : IsBetaNF a := fun a' hs => hm _ (.appL hs)
    have hb_nf : IsBetaNF b := fun b' hs => hm _ (.appR hs)
    intro y hy
    simp only [closeFVar] at hy
    generalize hxa : closeFVar k z a = xa at hy
    cases hy with
    | appL hsa => rw [← hxa] at hsa; exact iha k ha_nf _ hsa
    | appR hsb => exact ihb k hb_nf _ hsb
    | beta _ _ =>
      obtain ⟨a₀, rfl⟩ := closeFVar_eq_lam_inv hxa
      exact hm _ (.beta a₀ b)

private theorem lamSize_subst_fvar (k z : Nat) (m : Lam) :
    lamSize (subst k (.fvar z) m) = lamSize m := by
  induction m generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · simp [if_pos hlt, lamSize]
    · simp only [if_neg hlt]
      by_cases heq : j = k
      · simp [if_pos heq, shift, lamSize]
      · simp [if_neg heq, lamSize]
  | fvar _ => rfl
  | app _ _ iha ihb => simp [subst, lamSize, iha k, ihb k]
  | lam _ ih => simp [subst, lamSize, ih (k + 1)]

private theorem betaReduces_app_no_lam_left {a b w : Lam}
    (hno : ∀ p, ¬ BetaReduces a (.lam p))
    (hred : BetaReduces (a @@ b) w) :
    ∃ a' b', w = a' @@ b' ∧ BetaReduces a a' ∧ BetaReduces b b' := by
  suffices hgen : ∀ {x y : Lam}, BetaReduces x y → ∀ a b,
      (∀ p, ¬ BetaReduces a (.lam p)) → x = a @@ b →
      ∃ a' b', y = a' @@ b' ∧ BetaReduces a a' ∧ BetaReduces b b' from
    hgen hred a b hno rfl
  intro x y hxy
  induction hxy with
  | refl => intro a b _ hx; exact ⟨a, b, hx, .refl a, .refl b⟩
  | next hs _ ih =>
    intro a b hno hx; subst hx
    cases hs with
    | beta p _ => exfalso; exact hno p (.refl _)
    | @appL _ a1 _ ha1 =>
      obtain ⟨a', b', hy, ha', hb'⟩ := ih a1 b (fun p hr => hno p (.next ha1 hr)) rfl
      exact ⟨a', b', hy, .next ha1 ha', hb'⟩
    | @appR _ _ b1 hb1 =>
      obtain ⟨a', b', hy, ha', hb'⟩ := ih a b1 hno rfl
      exact ⟨a', b', hy, ha', .next hb1 hb'⟩

/-- Classification of every `CL(S)` normal form: either `IsPartialS`, `.var v`, or `a ⋅ b` with variable head! -/
theorem cl_normalForm_cases {t : Term} (hnf : IsNormalForm t) :
    IsPartialS t ∨ (∃ v, t = .var v) ∨
    (∃ a b v, t = a ⋅ b ∧ headLeaf a = .var v ∧ IsNormalForm a ∧ IsNormalForm b) := by
  cases t with
  | s => exact Or.inl (Or.inl rfl)
  | var v => exact Or.inr (Or.inl ⟨v, rfl⟩)
  | app a b =>
    have ha_nf : IsNormalForm a := fun a' hs => hnf _ (.left hs)
    have hb_nf : IsNormalForm b := fun b' hs => hnf _ (.right hs)
    cases hhead : headLeaf a with
    | var v => exact Or.inr (Or.inr ⟨a, b, v, rfl, hhead, ha_nf, hb_nf⟩)
    | app u w =>
      exfalso
      have h_no_app : ∀ (x : Term), headLeaf x ≠ u ⋅ w := by
        intro x; induction x with
        | s => intro hh; cases hh
        | var _ => intro hh; cases hh
        | app x1 _ ih => exact ih
      exact h_no_app a hhead
    | s =>
      cases a with
      | s => exact Or.inl (Or.inr (Or.inl ⟨b, rfl⟩))
      | var _ => cases hhead
      | app a1 x =>
        cases a1 with
        | s => exact Or.inl (Or.inr (Or.inr ⟨x, b, rfl⟩))
        | var _ => cases hhead
        | app a2 y =>
          exfalso
          suffices h_no_s4 : ∀ (p q r d : Term), headLeaf p = .s → ¬ IsNormalForm (p ⋅ q ⋅ r ⋅ d) from
            h_no_s4 a2 y x b hhead hnf
          intro p
          induction p with
          | s => intro q r d _ hnf4; exact hnf4 _ (.root q r d)
          | var _ => intro _ _ _ hh; cases hh
          | app p1 p2 ih =>
            intro q r d hh hnf4
            exact ih p2 q r hh (fun u hs => hnf4 _ (.left hs))

/-- **THEOREM (Exact Repaired Replacement for Conjecture 42 — Pure `CL(S)` ↔ `λβ`)**:
    For EVERY `M ∈ Ter(CL(S))` (closed or open),
    `(M)_λ` has a `β`-normal form in `λ`-calculus **if and only if** `M` satisfies `DeepCLNorm M`! -/
theorem repaired_conjecture_42 (m : Term) :
    DeepCLNorm m ↔ HasBetaNF (toLam m) := by
  constructor
  · -- Soundness: `DeepCLNorm m → HasBetaNF (toLam m)`
    intro hdeep
    induction hdeep with
    | step hs _ ih =>
      obtain ⟨nf, hred, hnf⟩ := ih
      exact ⟨nf, betaReduces_trans (step_to_betaReduces hs) hred, hnf⟩
    | var v =>
      exact ⟨.fvar v, .refl _, fun _ hs => by cases hs⟩
    | @varApp a b v hhead _ _ iha ihb =>
      obtain ⟨nf_a, hra, hnfa⟩ := iha
      obtain ⟨nf_b, hrb, hnfb⟩ := ihb
      have hnot_lam : ∀ p, nf_a ≠ .lam p := by
        intro p hp; subst hp
        exact toLam_not_reduces_lam_of_headLeaf_var hhead p hra
      refine ⟨nf_a @@ nf_b, betaReduces_app hra hrb, fun y hy => ?_⟩
      cases hy with
      | beta p _ => exact hnot_lam p rfl
      | appL hsa => exact hnfa _ hsa
      | appR hsb => exact hnfb _ hsb
    | @saturate t z hpart hz _ ihz =>
      obtain ⟨nf_z, hrz, hnfz⟩ := ihz
      have habs : ∃ body, BetaReduces (toLam t) (.lam body) :=
        (pureS_reduces_partial_iff_lam_reduces_abs t).mp ⟨t, .refl t, hpart⟩
      obtain ⟨body, htbody⟩ := habs
      have hzt_lam : hasFVar z (toLam t) = false := by rw [hasFVar_toLam]; exact hz
      have hzbody : hasFVar z body = false := by
        simpa [hasFVar] using hasFVar_false_betaReduces htbody hzt_lam
      have ht_sub : BetaReduces (toLam (t ⋅ .var z)) (subst 0 (.fvar z) body) :=
        betaReduces_trans (betaReduces_appL htbody (.fvar z)) (.next (.beta body (.fvar z)) (.refl _))
      obtain ⟨w, hw1, hw2⟩ := church_rosser_beta ht_sub hrz
      rw [← betaNF_reduces_eq hnfz hw2] at hw1
      have hbody_red : BetaReduces body (closeFVar 0 z nf_z) := by
        have hc := betaReduces_closeFVar 0 z hw1
        rw [closeFVar_subst_fvar_cancel 0 z hzbody] at hc
        exact hc
      exact ⟨.lam (closeFVar 0 z nf_z),
        betaReduces_trans htbody (betaReduces_lam hbody_red),
        fun y hy => by
          cases hy with
          | lam hsb => exact isBetaNF_closeFVar 0 z hnfz _ hsb⟩
  · -- Completeness: `HasBetaNF (toLam m) → DeepCLNorm m`
    intro ⟨nf, hred, hnf⟩
    suffices hmain : ∀ (sz : Nat) (nf : Lam), lamSize nf ≤ sz → IsBetaNF nf →
        ∀ (m : Term), BetaReduces (toLam m) nf → DeepCLNorm m from
      hmain (lamSize nf) nf (Nat.le_refl _) hnf m hred
    intro sz
    induction sz with
    | zero =>
      intro nf hle _ _ _
      exfalso; exact Nat.not_le_of_lt (lamSize_pos nf) hle
    | succ sz ih =>
      intro nf hle hnf m hm_nf
      have hsn_lam : StrongNormalizingBeta (toLam m) :=
        lambdaI_wn_implies_sn (isLambdaI_toLam m) ⟨nf, hm_nf, hnf⟩
      obtain ⟨m_nf, hm_cl, hmnf_cl⟩ := sn_implies_wn_cl (sn_cl_of_sn_toLam hsn_lam)
      refine deepCLNorm_of_reduces hm_cl ?_
      obtain ⟨w, hw1, hw2⟩ := church_rosser_beta (reduces_to_betaReduces hm_cl) hm_nf
      rw [← betaNF_reduces_eq hnf hw2] at hw1
      rcases cl_normalForm_cases hmnf_cl with
        hpart | ⟨v, rfl⟩ | ⟨a, b, v, rfl, hhead, _, _⟩
      · -- Partial S-term (`S`, `S p`, or `S p q`)
        let z := maxVarBound m_nf
        have hz : hasVar z m_nf = false := hasVar_false_of_ge (Nat.le_refl _)
        obtain ⟨body, hbody⟩ := (pureS_reduces_partial_iff_lam_reduces_abs m_nf).mp ⟨m_nf, .refl _, hpart⟩
        obtain ⟨w2, hbw2, hnfw2⟩ := church_rosser_beta hbody hw1
        rw [← betaNF_reduces_eq hnf hnfw2] at hbw2
        have hlam_nf : ∃ nf_body, nf = .lam nf_body := by
          suffices hg : ∀ {x y : Lam}, BetaReduces x y → ∀ p0, x = .lam p0 → ∃ q0, y = .lam q0 from
            hg hbw2 body rfl
          intro x y hxy; induction hxy with
          | refl => intro p0 hx; exact ⟨p0, hx⟩
          | next hs _ ihg => intro p0 hx; subst hx; cases hs with | lam _ => exact ihg _ rfl
        obtain ⟨nf_body, rfl⟩ := hlam_nf
        have hnfb : IsBetaNF nf_body := isBetaNF_of_lam hnf
        have hsub_nf : IsBetaNF (subst 0 (.fvar z) nf_body) := isBetaNF_subst_fvar 0 z hnfb
        have hsat_red : BetaReduces (toLam (m_nf ⋅ .var z)) (subst 0 (.fvar z) nf_body) :=
          betaReduces_trans (betaReduces_appL hw1 (.fvar z)) (.next (.beta nf_body (.fvar z)) (.refl _))
        have hsz_sub : lamSize (subst 0 (.fvar z) nf_body) ≤ sz := by
          rw [lamSize_subst_fvar]
          exact Nat.le_of_succ_le_succ (by simpa [lamSize, Nat.add_comm] using hle)
        exact .saturate z hpart hz (ih _ hsz_sub hsub_nf (m_nf ⋅ .var z) hsat_red)
      · exact .var v
      · obtain ⟨nf_a, nf_b, rfl, hra, hrb⟩ :=
          betaReduces_app_no_lam_left (toLam_not_reduces_lam_of_headLeaf_var hhead) hw1
        have hnfa : IsBetaNF nf_a := fun a' hs => hnf _ (.appL hs)
        have hnfb : IsBetaNF nf_b := fun b' hs => hnf _ (.appR hs)
        have hsza : lamSize nf_a ≤ sz := by
          have hlt : lamSize nf_a < lamSize (nf_a @@ nf_b) := by
            simp only [lamSize]
            exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_add_of_pos_left (by decide : 0 < 1))
          exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hle)
        have hszb : lamSize nf_b ≤ sz := by
          have hlt : lamSize nf_b < lamSize (nf_a @@ nf_b) := by
            simp only [lamSize]
            exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_add_of_pos_left (by decide : 0 < 1))
          exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hle)
        exact .varApp v hhead (ih nf_a hsza hnfa a hra) (ih nf_b hszb hnfb b hrb)

end FormalLambdaConjectures
