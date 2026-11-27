import zero_navigator_cellular.cellular_defs
import zero_navigator_cellular.chunks.chunk_00
import zero_navigator_cellular.chunks.chunk_01
import zero_navigator_cellular.chunks.chunk_02
import zero_navigator_cellular.chunks.chunk_03
import zero_navigator_cellular.chunks.chunk_04
import zero_navigator_cellular.chunks.chunk_05
import zero_navigator_cellular.chunks.chunk_06
import zero_navigator_cellular.chunks.chunk_07
import zero_navigator_cellular.chunks.chunk_08
import zero_navigator_cellular.chunks.chunk_09
import zero_navigator_cellular.chunks.chunk_10
import zero_navigator_cellular.chunks.chunk_11
import zero_navigator_cellular.chunks.chunk_12
import zero_navigator_cellular.chunks.chunk_13
import zero_navigator_cellular.chunks.chunk_14
import zero_navigator_cellular.chunks.chunk_15

/-!
# Post's Lattice Boolean Clones, Finite `S`-Algebras, Minimal Pure-`S` Rule 110, and Dynamic Driver Obstructions

Constructively machine-checked in Lean 4.33.1 inside `namespace ZeroNavigatorCellular`.
-/

namespace ZeroNavigatorCellular

/-! ## Section 1. Compatible Preorder Soundness & General Non-Monotone Reduction -/

theorem compat_preorder_app {Q : Type} {op : Q → Q → Q} {le : Q → Q → Bool}
    (hc : IsCompatPreorder op le) {x1 x2 y1 y2 : Q}
    (hx : le x1 x2 = true) (hy : le y1 y2 = true) :
    le (op x1 y1) (op x2 y2) = true :=
  hc.trans _ (op x2 y1) _ (hc.left x1 x2 y1 hx) (hc.right y1 y2 x2 hy)

theorem compat_preorder_evalPoly1 {Q : Type} (op : Q → Q → Q) (le : Q → Q → Bool)
    (hc : IsCompatPreorder op le) (U : Poly Q 1) {a b : Q} (hab : le a b = true) :
    le (evalPoly op U (fun _ => a)) (evalPoly op U (fun _ => b)) = true := by
  induction U with
  | const c => exact hc.refl c
  | var _ => exact hab
  | app p1 p2 ih1 ih2 => exact compat_preorder_app hc ih1 ih2

theorem compat_preorder_no_swap {Q : Type} (op : Q → Q → Q) (le : Q → Q → Bool)
    (hc : IsCompatPreorder op le) (U : Poly Q 1) (q0 q1 : Q)
    (h0 : evalPoly op U (fun _ => q0) = q1)
    (h1 : evalPoly op U (fun _ => q1) = q0)
    (hsep : (le q0 q1 != le q1 q0) = true) : False := by
  cases h01 : le q0 q1 with
  | true =>
    rw [h01] at hsep
    cases h10 : le q1 q0 with
    | true => rw [h10] at hsep; cases hsep
    | false =>
      have hpres := compat_preorder_evalPoly1 op le hc U h01
      rw [h0, h1, h10] at hpres
      cases hpres
  | false =>
    rw [h01] at hsep
    cases h10 : le q1 q0 with
    | false => rw [h10] at hsep; cases hsep
    | true =>
      have hpres := compat_preorder_evalPoly1 op le hc U h10
      rw [h1, h0, h01] at hpres
      cases hpres

def pairEnv {Q : Type} (a b : Q) : Fin 2 → Q
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

def tripleEnv {Q : Type} (a b c : Q) : Fin 3 → Q
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

def IsPolyNAND {Q : Type} (op : Q → Q → Q) (P : Poly Q 2) (q0 q1 : Q) : Prop :=
  evalPoly op P (pairEnv q0 q0) = q1 ∧
  evalPoly op P (pairEnv q0 q1) = q1 ∧
  evalPoly op P (pairEnv q1 q0) = q1 ∧
  evalPoly op P (pairEnv q1 q1) = q0

def IsPolyXOR {Q : Type} (op : Q → Q → Q) (P : Poly Q 2) (q0 q1 : Q) : Prop :=
  evalPoly op P (pairEnv q0 q0) = q0 ∧
  evalPoly op P (pairEnv q0 q1) = q1 ∧
  evalPoly op P (pairEnv q1 q0) = q1 ∧
  evalPoly op P (pairEnv q1 q1) = q0

def IsPolyRule110 {Q : Type} (op : Q → Q → Q) (P : Poly Q 3) (q0 q1 : Q) : Prop :=
  evalPoly op P (tripleEnv q0 q0 q0) = q0 ∧
  evalPoly op P (tripleEnv q0 q0 q1) = q1 ∧
  evalPoly op P (tripleEnv q0 q1 q0) = q1 ∧
  evalPoly op P (tripleEnv q0 q1 q1) = q1 ∧
  evalPoly op P (tripleEnv q1 q0 q0) = q0 ∧
  evalPoly op P (tripleEnv q1 q0 q1) = q1 ∧
  evalPoly op P (tripleEnv q1 q1 q0) = q1 ∧
  evalPoly op P (tripleEnv q1 q1 q1) = q0

theorem nonmono_edge_implies_eq_of_no_not {Q : Type} (op : Q → Q → Q)
    (no_not : ∀ (U : Poly Q 1) (a b : Q),
      evalPoly op U (fun _ => a) = b → evalPoly op U (fun _ => b) = a → a = b)
    {k : Nat} (P : Poly Q k) (q0 q1 : Q) (env : Fin k → Bool) (i : Fin k)
    (h : evalPoly op P (fun j => cond (j.val == i.val) q0 (cond (env j) q1 q0)) = q1 ∧
         evalPoly op P (fun j => cond (j.val == i.val) q1 (cond (env j) q1 q0)) = q0) :
    q0 = q1 := by
  let U : Poly Q 1 := substPoly
    (fun j => cond (j.val == i.val) (.var ⟨0, Nat.zero_lt_one⟩) (.const (cond (env j) q1 q0))) P
  have hU0 : evalPoly op U (fun _ => q0) = q1 := by
    rw [evalPoly_subst]
    have heq : (fun j : Fin k => evalPoly op (cond (j.val == i.val) (Poly.var ⟨0, Nat.zero_lt_one⟩) (Poly.const (cond (env j) q1 q0))) (fun _ => q0)) =
               (fun j : Fin k => cond (j.val == i.val) q0 (cond (env j) q1 q0)) := by
      funext j
      cases (j.val == i.val) <;> rfl
    rw [heq]
    exact h.1
  have hU1 : evalPoly op U (fun _ => q1) = q0 := by
    rw [evalPoly_subst]
    have heq : (fun j : Fin k => evalPoly op (cond (j.val == i.val) (Poly.var ⟨0, Nat.zero_lt_one⟩) (Poly.const (cond (env j) q1 q0))) (fun _ => q1)) =
               (fun j : Fin k => cond (j.val == i.val) q1 (cond (env j) q1 q0)) := by
      funext j
      cases (j.val == i.val) <;> rfl
    rw [heq]
    exact h.2
  exact no_not U q0 q1 hU0 hU1

theorem nand_implies_eq_of_no_not {Q : Type} (op : Q → Q → Q)
    (no_not : ∀ (U : Poly Q 1) (a b : Q),
      evalPoly op U (fun _ => a) = b → evalPoly op U (fun _ => b) = a → a = b)
    (P : Poly Q 2) (q0 q1 : Q) (h : IsPolyNAND op P q0 q1) : q0 = q1 := by
  let f : Fin 2 → Poly Q 1 := fun _ => .var ⟨0, Nat.zero_lt_one⟩
  let U : Poly Q 1 := substPoly f P
  have hU0 : evalPoly op U (fun _ => q0) = q1 := by
    rw [evalPoly_subst]
    have heq : (fun i : Fin 2 => evalPoly op (f i) (fun _ => q0)) = pairEnv q0 q0 := by
      funext ⟨j, hj⟩
      match j with | 0 => rfl | 1 => rfl
    rw [heq]
    exact h.1
  have hU1 : evalPoly op U (fun _ => q1) = q0 := by
    rw [evalPoly_subst]
    have heq : (fun i : Fin 2 => evalPoly op (f i) (fun _ => q1)) = pairEnv q1 q1 := by
      funext ⟨j, hj⟩
      match j with | 0 => rfl | 1 => rfl
    rw [heq]
    exact h.2.2.2
  exact no_not U q0 q1 hU0 hU1

theorem xor_implies_eq_of_no_not {Q : Type} (op : Q → Q → Q)
    (no_not : ∀ (U : Poly Q 1) (a b : Q),
      evalPoly op U (fun _ => a) = b → evalPoly op U (fun _ => b) = a → a = b)
    (P : Poly Q 2) (q0 q1 : Q) (h : IsPolyXOR op P q0 q1) : q0 = q1 := by
  let f : Fin 2 → Poly Q 1
    | ⟨0, _⟩ => .var ⟨0, Nat.zero_lt_one⟩
    | ⟨1, _⟩ => .const q1
  let U : Poly Q 1 := substPoly f P
  have hU0 : evalPoly op U (fun _ => q0) = q1 := by
    rw [evalPoly_subst]
    have heq : (fun i : Fin 2 => evalPoly op (f i) (fun _ => q0)) = pairEnv q0 q1 := by
      funext ⟨j, hj⟩
      match j with | 0 => rfl | 1 => rfl
    rw [heq]
    exact h.2.1
  have hU1 : evalPoly op U (fun _ => q1) = q0 := by
    rw [evalPoly_subst]
    have heq : (fun i : Fin 2 => evalPoly op (f i) (fun _ => q1)) = pairEnv q1 q1 := by
      funext ⟨j, hj⟩
      match j with | 0 => rfl | 1 => rfl
    rw [heq]
    exact h.2.2.2
  exact no_not U q0 q1 hU0 hU1

theorem rule110_implies_eq_of_no_not {Q : Type} (op : Q → Q → Q)
    (no_not : ∀ (U : Poly Q 1) (a b : Q),
      evalPoly op U (fun _ => a) = b → evalPoly op U (fun _ => b) = a → a = b)
    (P : Poly Q 3) (q0 q1 : Q) (h : IsPolyRule110 op P q0 q1) : q0 = q1 := by
  let f : Fin 3 → Poly Q 1
    | ⟨0, _⟩ => .var ⟨0, Nat.zero_lt_one⟩
    | ⟨1, _⟩ => .const q1
    | ⟨2, _⟩ => .const q1
  let U : Poly Q 1 := substPoly f P
  have hU0 : evalPoly op U (fun _ => q0) = q1 := by
    rw [evalPoly_subst]
    have heq : (fun i : Fin 3 => evalPoly op (f i) (fun _ => q0)) = tripleEnv q0 q1 q1 := by
      funext ⟨j, hj⟩
      match j with | 0 => rfl | 1 => rfl | 2 => rfl
    rw [heq]
    exact h.2.2.2.1
  have hU1 : evalPoly op U (fun _ => q1) = q0 := by
    rw [evalPoly_subst]
    have heq : (fun i : Fin 3 => evalPoly op (f i) (fun _ => q1)) = tripleEnv q1 q1 q1 := by
      funext ⟨j, hj⟩
      match j with | 0 => rfl | 1 => rfl | 2 => rfl
    rw [heq]
    exact h.2.2.2.2.2.2.2
  exact no_not U q0 q1 hU0 hU1


/-! ## Section 2. Monotonicity & No-Inversion Across `A_HN`, `A_SN`, and `A_P` -/
theorem deltaHN_s_law (x y z : StateHN) :
    deltaHN (deltaHN (deltaHN .h0 x) y) z =
    deltaHN (deltaHN x z) (deltaHN y z) :=
  match x with
  | .h0 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_0 y z)
  | .h1 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_1 y z)
  | .h2 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_2 y z)
  | .h3 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_3 y z)
  | .h4 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_4 y z)
  | .h5 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_5 y z)
  | .h6 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_6 y z)
  | .h7 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_7 y z)
  | .h8 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_8 y z)
  | .h9 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_9 y z)
  | .h10 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_10 y z)
  | .h11 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_11 y z)
  | .h12 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_12 y z)
  | .h13 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_13 y z)
  | .h14 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_14 y z)
  | .h15 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_15 y z)
  | .h16 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_16 y z)
  | .h17 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_17 y z)
  | .h18 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_18 y z)
  | .h19 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_19 y z)
  | .h20 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_20 y z)
  | .h21 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_21 y z)
  | .h22 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_22 y z)
  | .h23 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_23 y z)
  | .h24 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_24 y z)
  | .h25 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_25 y z)
  | .h26 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_26 y z)
  | .h27 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_27 y z)
  | .h28 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_28 y z)
  | .h29 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_29 y z)
  | .h30 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_30 y z)
  | .h31 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_31 y z)
  | .h32 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_32 y z)
  | .h33 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_33 y z)
  | .h34 => beq_StateHN_eq (checkAll2_StateHN_sound _ s_row_HN_34 y z)

def evalHN : Term → StateHN
  | .s => .h0
  | .var _ => .h0
  | .app a b => deltaHN (evalHN a) (evalHN b)

theorem evalHN_step_invariant {a b : Term} (h : Step a b) : evalHN a = evalHN b := by
  induction h with
  | root x y z => exact deltaHN_s_law (evalHN x) (evalHN y) (evalHN z)
  | left _ ih => simp only [evalHN, ih]
  | right _ ih => simp only [evalHN, ih]

theorem evalHN_conv_invariant {a b : Term} (h : ConvS a b) : evalHN a = evalHN b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalHN_step_invariant hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem allPreorders_HN_sound (x y z : StateHN) :
    allPreordersStep_HN x y z = true :=
  match x with
  | .h0 => checkAll2_StateHN_sound _ preorders_HN_row_0 y z
  | .h1 => checkAll2_StateHN_sound _ preorders_HN_row_1 y z
  | .h2 => checkAll2_StateHN_sound _ preorders_HN_row_2 y z
  | .h3 => checkAll2_StateHN_sound _ preorders_HN_row_3 y z
  | .h4 => checkAll2_StateHN_sound _ preorders_HN_row_4 y z
  | .h5 => checkAll2_StateHN_sound _ preorders_HN_row_5 y z
  | .h6 => checkAll2_StateHN_sound _ preorders_HN_row_6 y z
  | .h7 => checkAll2_StateHN_sound _ preorders_HN_row_7 y z
  | .h8 => checkAll2_StateHN_sound _ preorders_HN_row_8 y z
  | .h9 => checkAll2_StateHN_sound _ preorders_HN_row_9 y z
  | .h10 => checkAll2_StateHN_sound _ preorders_HN_row_10 y z
  | .h11 => checkAll2_StateHN_sound _ preorders_HN_row_11 y z
  | .h12 => checkAll2_StateHN_sound _ preorders_HN_row_12 y z
  | .h13 => checkAll2_StateHN_sound _ preorders_HN_row_13 y z
  | .h14 => checkAll2_StateHN_sound _ preorders_HN_row_14 y z
  | .h15 => checkAll2_StateHN_sound _ preorders_HN_row_15 y z
  | .h16 => checkAll2_StateHN_sound _ preorders_HN_row_16 y z
  | .h17 => checkAll2_StateHN_sound _ preorders_HN_row_17 y z
  | .h18 => checkAll2_StateHN_sound _ preorders_HN_row_18 y z
  | .h19 => checkAll2_StateHN_sound _ preorders_HN_row_19 y z
  | .h20 => checkAll2_StateHN_sound _ preorders_HN_row_20 y z
  | .h21 => checkAll2_StateHN_sound _ preorders_HN_row_21 y z
  | .h22 => checkAll2_StateHN_sound _ preorders_HN_row_22 y z
  | .h23 => checkAll2_StateHN_sound _ preorders_HN_row_23 y z
  | .h24 => checkAll2_StateHN_sound _ preorders_HN_row_24 y z
  | .h25 => checkAll2_StateHN_sound _ preorders_HN_row_25 y z
  | .h26 => checkAll2_StateHN_sound _ preorders_HN_row_26 y z
  | .h27 => checkAll2_StateHN_sound _ preorders_HN_row_27 y z
  | .h28 => checkAll2_StateHN_sound _ preorders_HN_row_28 y z
  | .h29 => checkAll2_StateHN_sound _ preorders_HN_row_29 y z
  | .h30 => checkAll2_StateHN_sound _ preorders_HN_row_30 y z
  | .h31 => checkAll2_StateHN_sound _ preorders_HN_row_31 y z
  | .h32 => checkAll2_StateHN_sound _ preorders_HN_row_32 y z
  | .h33 => checkAll2_StateHN_sound _ preorders_HN_row_33 y z
  | .h34 => checkAll2_StateHN_sound _ preorders_HN_row_34 y z
theorem le_HN_0_is_compat_preorder : IsCompatPreorder deltaHN le_HN_0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_left (checkAll1_StateHN_sound _ preorders_HN_refl x)))
  · intro x y z hxy
    have hst : le_HN_0_step x y z = true := (and_left (and_left (allPreorders_HN_sound x y z)))
    unfold le_HN_0_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_HN_0_step x y z = true := (and_left (and_left (allPreorders_HN_sound x y z)))
    unfold le_HN_0_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_HN_0_step x y z = true := (and_left (and_left (allPreorders_HN_sound x y z)))
    unfold le_HN_0_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_HN_1_is_compat_preorder : IsCompatPreorder deltaHN le_HN_1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_right (and_left (checkAll1_StateHN_sound _ preorders_HN_refl x))))
  · intro x y z hxy
    have hst : le_HN_1_step x y z = true := (and_left (and_right (and_left (allPreorders_HN_sound x y z))))
    unfold le_HN_1_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_HN_1_step x y z = true := (and_left (and_right (and_left (allPreorders_HN_sound x y z))))
    unfold le_HN_1_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_HN_1_step x y z = true := (and_left (and_right (and_left (allPreorders_HN_sound x y z))))
    unfold le_HN_1_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_HN_2_is_compat_preorder : IsCompatPreorder deltaHN le_HN_2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_right (and_right (and_left (checkAll1_StateHN_sound _ preorders_HN_refl x))))
  · intro x y z hxy
    have hst : le_HN_2_step x y z = true := (and_right (and_right (and_left (allPreorders_HN_sound x y z))))
    unfold le_HN_2_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_HN_2_step x y z = true := (and_right (and_right (and_left (allPreorders_HN_sound x y z))))
    unfold le_HN_2_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_HN_2_step x y z = true := (and_right (and_right (and_left (allPreorders_HN_sound x y z))))
    unfold le_HN_2_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_HN_3_is_compat_preorder : IsCompatPreorder deltaHN le_HN_3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_right (checkAll1_StateHN_sound _ preorders_HN_refl x)))
  · intro x y z hxy
    have hst : le_HN_3_step x y z = true := (and_left (and_right (allPreorders_HN_sound x y z)))
    unfold le_HN_3_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_HN_3_step x y z = true := (and_left (and_right (allPreorders_HN_sound x y z)))
    unfold le_HN_3_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_HN_3_step x y z = true := (and_left (and_right (allPreorders_HN_sound x y z)))
    unfold le_HN_3_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_HN_4_is_compat_preorder : IsCompatPreorder deltaHN le_HN_4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_right (and_right (checkAll1_StateHN_sound _ preorders_HN_refl x))))
  · intro x y z hxy
    have hst : le_HN_4_step x y z = true := (and_left (and_right (and_right (allPreorders_HN_sound x y z))))
    unfold le_HN_4_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_HN_4_step x y z = true := (and_left (and_right (and_right (allPreorders_HN_sound x y z))))
    unfold le_HN_4_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_HN_4_step x y z = true := (and_left (and_right (and_right (allPreorders_HN_sound x y z))))
    unfold le_HN_4_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_HN_5_is_compat_preorder : IsCompatPreorder deltaHN le_HN_5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_right (and_right (and_right (checkAll1_StateHN_sound _ preorders_HN_refl x))))
  · intro x y z hxy
    have hst : le_HN_5_step x y z = true := (and_right (and_right (and_right (allPreorders_HN_sound x y z))))
    unfold le_HN_5_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_HN_5_step x y z = true := (and_right (and_right (and_right (allPreorders_HN_sound x y z))))
    unfold le_HN_5_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_HN_5_step x y z = true := (and_right (and_right (and_right (allPreorders_HN_sound x y z))))
    unfold le_HN_5_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem no_unary_not_HN (U : Poly StateHN 1) (q0 q1 : StateHN)
    (h0 : evalPoly deltaHN U (fun _ => q0) = q1)
    (h1 : evalPoly deltaHN U (fun _ => q1) = q0) : q0 = q1 := by
  cases hbeq : beq_StateHN q0 q1 with
  | true => exact beq_StateHN_eq hbeq
  | false =>
    have hall := checkAll2_StateHN_sound _ sep_HN_all_bool q0 q1
    rw [hbeq] at hall
    have hsep : sep_HN q0 q1 = true := hall
    unfold sep_HN at hsep
    cases or_eq_true_elim hsep with
    | inr hcur => exfalso; exact compat_preorder_no_swap deltaHN le_HN_5 le_HN_5_is_compat_preorder U q0 q1 h0 h1 hcur
    | inl hsep =>
      cases or_eq_true_elim hsep with
      | inr hcur => exfalso; exact compat_preorder_no_swap deltaHN le_HN_4 le_HN_4_is_compat_preorder U q0 q1 h0 h1 hcur
      | inl hsep =>
        cases or_eq_true_elim hsep with
        | inr hcur => exfalso; exact compat_preorder_no_swap deltaHN le_HN_3 le_HN_3_is_compat_preorder U q0 q1 h0 h1 hcur
        | inl hsep =>
          cases or_eq_true_elim hsep with
          | inr hcur => exfalso; exact compat_preorder_no_swap deltaHN le_HN_2 le_HN_2_is_compat_preorder U q0 q1 h0 h1 hcur
          | inl hsep =>
            cases or_eq_true_elim hsep with
            | inr hcur => exfalso; exact compat_preorder_no_swap deltaHN le_HN_1 le_HN_1_is_compat_preorder U q0 q1 h0 h1 hcur
            | inl hsep =>
              exfalso; exact compat_preorder_no_swap deltaHN le_HN_0 le_HN_0_is_compat_preorder U q0 q1 h0 h1 hsep

theorem no_nand_HN (P : Poly StateHN 2) (q0 q1 : StateHN) (hne : q0 ≠ q1) :
    ¬ IsPolyNAND deltaHN P q0 q1 :=
  fun h => hne (nand_implies_eq_of_no_not deltaHN (no_unary_not_HN) P q0 q1 h)

theorem no_xor_HN (P : Poly StateHN 2) (q0 q1 : StateHN) (hne : q0 ≠ q1) :
    ¬ IsPolyXOR deltaHN P q0 q1 :=
  fun h => hne (xor_implies_eq_of_no_not deltaHN (no_unary_not_HN) P q0 q1 h)

theorem no_rule110_HN (P : Poly StateHN 3) (q0 q1 : StateHN) (hne : q0 ≠ q1) :
    ¬ IsPolyRule110 deltaHN P q0 q1 :=
  fun h => hne (rule110_implies_eq_of_no_not deltaHN (no_unary_not_HN) P q0 q1 h)

theorem clone_monotone_all_arities_HN {k : Nat} (P : Poly StateHN k)
    (q0 q1 : StateHN) (hne : q0 ≠ q1) (env : Fin k → Bool) (i : Fin k) :
    ¬ (evalPoly deltaHN P (fun j => cond (j.val == i.val) q0 (cond (env j) q1 q0)) = q1 ∧
       evalPoly deltaHN P (fun j => cond (j.val == i.val) q1 (cond (env j) q1 q0)) = q0) :=
  fun h => hne (nonmono_edge_implies_eq_of_no_not deltaHN (no_unary_not_HN) P q0 q1 env i h)
theorem deltaSN_s_law (x y z : StateSN) :
    deltaSN (deltaSN (deltaSN .s0 x) y) z =
    deltaSN (deltaSN x z) (deltaSN y z) :=
  match x with
  | .s0 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_0 y z)
  | .s1 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_1 y z)
  | .s2 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_2 y z)
  | .s3 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_3 y z)
  | .s4 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_4 y z)
  | .s5 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_5 y z)
  | .s6 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_6 y z)
  | .s7 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_7 y z)
  | .s8 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_8 y z)
  | .s9 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_9 y z)
  | .s10 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_10 y z)
  | .s11 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_11 y z)
  | .s12 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_12 y z)
  | .s13 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_13 y z)
  | .s14 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_14 y z)
  | .s15 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_15 y z)
  | .s16 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_16 y z)
  | .s17 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_17 y z)
  | .s18 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_18 y z)
  | .s19 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_19 y z)
  | .s20 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_20 y z)
  | .s21 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_21 y z)
  | .s22 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_22 y z)
  | .s23 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_23 y z)
  | .s24 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_24 y z)
  | .s25 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_25 y z)
  | .s26 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_26 y z)
  | .s27 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_27 y z)
  | .s28 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_28 y z)
  | .s29 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_29 y z)
  | .s30 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_30 y z)
  | .s31 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_31 y z)
  | .s32 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_32 y z)
  | .s33 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_33 y z)
  | .s34 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_34 y z)
  | .s35 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_35 y z)
  | .s36 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_36 y z)
  | .s37 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_37 y z)
  | .s38 => beq_StateSN_eq (checkAll2_StateSN_sound _ s_row_SN_38 y z)

def evalSN : Term → StateSN
  | .s => .s0
  | .var _ => .s0
  | .app a b => deltaSN (evalSN a) (evalSN b)

theorem evalSN_step_invariant {a b : Term} (h : Step a b) : evalSN a = evalSN b := by
  induction h with
  | root x y z => exact deltaSN_s_law (evalSN x) (evalSN y) (evalSN z)
  | left _ ih => simp only [evalSN, ih]
  | right _ ih => simp only [evalSN, ih]

theorem evalSN_conv_invariant {a b : Term} (h : ConvS a b) : evalSN a = evalSN b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalSN_step_invariant hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem allPreorders_SN_sound (x y z : StateSN) :
    allPreordersStep_SN x y z = true :=
  match x with
  | .s0 => checkAll2_StateSN_sound _ preorders_SN_row_0 y z
  | .s1 => checkAll2_StateSN_sound _ preorders_SN_row_1 y z
  | .s2 => checkAll2_StateSN_sound _ preorders_SN_row_2 y z
  | .s3 => checkAll2_StateSN_sound _ preorders_SN_row_3 y z
  | .s4 => checkAll2_StateSN_sound _ preorders_SN_row_4 y z
  | .s5 => checkAll2_StateSN_sound _ preorders_SN_row_5 y z
  | .s6 => checkAll2_StateSN_sound _ preorders_SN_row_6 y z
  | .s7 => checkAll2_StateSN_sound _ preorders_SN_row_7 y z
  | .s8 => checkAll2_StateSN_sound _ preorders_SN_row_8 y z
  | .s9 => checkAll2_StateSN_sound _ preorders_SN_row_9 y z
  | .s10 => checkAll2_StateSN_sound _ preorders_SN_row_10 y z
  | .s11 => checkAll2_StateSN_sound _ preorders_SN_row_11 y z
  | .s12 => checkAll2_StateSN_sound _ preorders_SN_row_12 y z
  | .s13 => checkAll2_StateSN_sound _ preorders_SN_row_13 y z
  | .s14 => checkAll2_StateSN_sound _ preorders_SN_row_14 y z
  | .s15 => checkAll2_StateSN_sound _ preorders_SN_row_15 y z
  | .s16 => checkAll2_StateSN_sound _ preorders_SN_row_16 y z
  | .s17 => checkAll2_StateSN_sound _ preorders_SN_row_17 y z
  | .s18 => checkAll2_StateSN_sound _ preorders_SN_row_18 y z
  | .s19 => checkAll2_StateSN_sound _ preorders_SN_row_19 y z
  | .s20 => checkAll2_StateSN_sound _ preorders_SN_row_20 y z
  | .s21 => checkAll2_StateSN_sound _ preorders_SN_row_21 y z
  | .s22 => checkAll2_StateSN_sound _ preorders_SN_row_22 y z
  | .s23 => checkAll2_StateSN_sound _ preorders_SN_row_23 y z
  | .s24 => checkAll2_StateSN_sound _ preorders_SN_row_24 y z
  | .s25 => checkAll2_StateSN_sound _ preorders_SN_row_25 y z
  | .s26 => checkAll2_StateSN_sound _ preorders_SN_row_26 y z
  | .s27 => checkAll2_StateSN_sound _ preorders_SN_row_27 y z
  | .s28 => checkAll2_StateSN_sound _ preorders_SN_row_28 y z
  | .s29 => checkAll2_StateSN_sound _ preorders_SN_row_29 y z
  | .s30 => checkAll2_StateSN_sound _ preorders_SN_row_30 y z
  | .s31 => checkAll2_StateSN_sound _ preorders_SN_row_31 y z
  | .s32 => checkAll2_StateSN_sound _ preorders_SN_row_32 y z
  | .s33 => checkAll2_StateSN_sound _ preorders_SN_row_33 y z
  | .s34 => checkAll2_StateSN_sound _ preorders_SN_row_34 y z
  | .s35 => checkAll2_StateSN_sound _ preorders_SN_row_35 y z
  | .s36 => checkAll2_StateSN_sound _ preorders_SN_row_36 y z
  | .s37 => checkAll2_StateSN_sound _ preorders_SN_row_37 y z
  | .s38 => checkAll2_StateSN_sound _ preorders_SN_row_38 y z
theorem le_SN_0_is_compat_preorder : IsCompatPreorder deltaSN le_SN_0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_left (checkAll1_StateSN_sound _ preorders_SN_refl x)))
  · intro x y z hxy
    have hst : le_SN_0_step x y z = true := (and_left (and_left (allPreorders_SN_sound x y z)))
    unfold le_SN_0_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_SN_0_step x y z = true := (and_left (and_left (allPreorders_SN_sound x y z)))
    unfold le_SN_0_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_SN_0_step x y z = true := (and_left (and_left (allPreorders_SN_sound x y z)))
    unfold le_SN_0_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_SN_1_is_compat_preorder : IsCompatPreorder deltaSN le_SN_1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_right (and_left (checkAll1_StateSN_sound _ preorders_SN_refl x)))
  · intro x y z hxy
    have hst : le_SN_1_step x y z = true := (and_right (and_left (allPreorders_SN_sound x y z)))
    unfold le_SN_1_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_SN_1_step x y z = true := (and_right (and_left (allPreorders_SN_sound x y z)))
    unfold le_SN_1_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_SN_1_step x y z = true := (and_right (and_left (allPreorders_SN_sound x y z)))
    unfold le_SN_1_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_SN_2_is_compat_preorder : IsCompatPreorder deltaSN le_SN_2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_right (checkAll1_StateSN_sound _ preorders_SN_refl x)))
  · intro x y z hxy
    have hst : le_SN_2_step x y z = true := (and_left (and_right (allPreorders_SN_sound x y z)))
    unfold le_SN_2_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_SN_2_step x y z = true := (and_left (and_right (allPreorders_SN_sound x y z)))
    unfold le_SN_2_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_SN_2_step x y z = true := (and_left (and_right (allPreorders_SN_sound x y z)))
    unfold le_SN_2_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_SN_3_is_compat_preorder : IsCompatPreorder deltaSN le_SN_3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_right (and_right (checkAll1_StateSN_sound _ preorders_SN_refl x))))
  · intro x y z hxy
    have hst : le_SN_3_step x y z = true := (and_left (and_right (and_right (allPreorders_SN_sound x y z))))
    unfold le_SN_3_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_SN_3_step x y z = true := (and_left (and_right (and_right (allPreorders_SN_sound x y z))))
    unfold le_SN_3_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_SN_3_step x y z = true := (and_left (and_right (and_right (allPreorders_SN_sound x y z))))
    unfold le_SN_3_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_SN_4_is_compat_preorder : IsCompatPreorder deltaSN le_SN_4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_right (and_right (and_right (checkAll1_StateSN_sound _ preorders_SN_refl x))))
  · intro x y z hxy
    have hst : le_SN_4_step x y z = true := (and_right (and_right (and_right (allPreorders_SN_sound x y z))))
    unfold le_SN_4_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_SN_4_step x y z = true := (and_right (and_right (and_right (allPreorders_SN_sound x y z))))
    unfold le_SN_4_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_SN_4_step x y z = true := (and_right (and_right (and_right (allPreorders_SN_sound x y z))))
    unfold le_SN_4_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem no_unary_not_SN (U : Poly StateSN 1) (q0 q1 : StateSN)
    (h0 : evalPoly deltaSN U (fun _ => q0) = q1)
    (h1 : evalPoly deltaSN U (fun _ => q1) = q0) : q0 = q1 := by
  cases hbeq : beq_StateSN q0 q1 with
  | true => exact beq_StateSN_eq hbeq
  | false =>
    have hall := checkAll2_StateSN_sound _ sep_SN_all_bool q0 q1
    rw [hbeq] at hall
    have hsep : sep_SN q0 q1 = true := hall
    unfold sep_SN at hsep
    cases or_eq_true_elim hsep with
    | inr hcur => exfalso; exact compat_preorder_no_swap deltaSN le_SN_4 le_SN_4_is_compat_preorder U q0 q1 h0 h1 hcur
    | inl hsep =>
      cases or_eq_true_elim hsep with
      | inr hcur => exfalso; exact compat_preorder_no_swap deltaSN le_SN_3 le_SN_3_is_compat_preorder U q0 q1 h0 h1 hcur
      | inl hsep =>
        cases or_eq_true_elim hsep with
        | inr hcur => exfalso; exact compat_preorder_no_swap deltaSN le_SN_2 le_SN_2_is_compat_preorder U q0 q1 h0 h1 hcur
        | inl hsep =>
          cases or_eq_true_elim hsep with
          | inr hcur => exfalso; exact compat_preorder_no_swap deltaSN le_SN_1 le_SN_1_is_compat_preorder U q0 q1 h0 h1 hcur
          | inl hsep =>
            exfalso; exact compat_preorder_no_swap deltaSN le_SN_0 le_SN_0_is_compat_preorder U q0 q1 h0 h1 hsep

theorem no_nand_SN (P : Poly StateSN 2) (q0 q1 : StateSN) (hne : q0 ≠ q1) :
    ¬ IsPolyNAND deltaSN P q0 q1 :=
  fun h => hne (nand_implies_eq_of_no_not deltaSN (no_unary_not_SN) P q0 q1 h)

theorem no_xor_SN (P : Poly StateSN 2) (q0 q1 : StateSN) (hne : q0 ≠ q1) :
    ¬ IsPolyXOR deltaSN P q0 q1 :=
  fun h => hne (xor_implies_eq_of_no_not deltaSN (no_unary_not_SN) P q0 q1 h)

theorem no_rule110_SN (P : Poly StateSN 3) (q0 q1 : StateSN) (hne : q0 ≠ q1) :
    ¬ IsPolyRule110 deltaSN P q0 q1 :=
  fun h => hne (rule110_implies_eq_of_no_not deltaSN (no_unary_not_SN) P q0 q1 h)

theorem clone_monotone_all_arities_SN {k : Nat} (P : Poly StateSN k)
    (q0 q1 : StateSN) (hne : q0 ≠ q1) (env : Fin k → Bool) (i : Fin k) :
    ¬ (evalPoly deltaSN P (fun j => cond (j.val == i.val) q0 (cond (env j) q1 q0)) = q1 ∧
       evalPoly deltaSN P (fun j => cond (j.val == i.val) q1 (cond (env j) q1 q0)) = q0) :=
  fun h => hne (nonmono_edge_implies_eq_of_no_not deltaSN (no_unary_not_SN) P q0 q1 env i h)
theorem deltaP_s_law (x y z : StateP) :
    deltaP (deltaP (deltaP .p0 x) y) z =
    deltaP (deltaP x z) (deltaP y z) :=
  match x with
  | .p0 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_0 y z)
  | .p1 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_1 y z)
  | .p2 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_2 y z)
  | .p3 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_3 y z)
  | .p4 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_4 y z)
  | .p5 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_5 y z)
  | .p6 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_6 y z)
  | .p7 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_7 y z)
  | .p8 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_8 y z)
  | .p9 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_9 y z)
  | .p10 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_10 y z)
  | .p11 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_11 y z)
  | .p12 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_12 y z)
  | .p13 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_13 y z)
  | .p14 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_14 y z)
  | .p15 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_15 y z)
  | .p16 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_16 y z)
  | .p17 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_17 y z)
  | .p18 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_18 y z)
  | .p19 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_19 y z)
  | .p20 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_20 y z)
  | .p21 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_21 y z)
  | .p22 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_22 y z)
  | .p23 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_23 y z)
  | .p24 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_24 y z)
  | .p25 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_25 y z)
  | .p26 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_26 y z)
  | .p27 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_27 y z)
  | .p28 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_28 y z)
  | .p29 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_29 y z)
  | .p30 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_30 y z)
  | .p31 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_31 y z)
  | .p32 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_32 y z)
  | .p33 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_33 y z)
  | .p34 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_34 y z)
  | .p35 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_35 y z)
  | .p36 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_36 y z)
  | .p37 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_37 y z)
  | .p38 => beq_StateP_eq (checkAll2_StateP_sound _ s_row_P_38 y z)

def evalP : Term → StateP
  | .s => .p0
  | .var _ => .p0
  | .app a b => deltaP (evalP a) (evalP b)

theorem evalP_step_invariant {a b : Term} (h : Step a b) : evalP a = evalP b := by
  induction h with
  | root x y z => exact deltaP_s_law (evalP x) (evalP y) (evalP z)
  | left _ ih => simp only [evalP, ih]
  | right _ ih => simp only [evalP, ih]

theorem evalP_conv_invariant {a b : Term} (h : ConvS a b) : evalP a = evalP b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalP_step_invariant hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem allPreorders_P_sound (x y z : StateP) :
    allPreordersStep_P x y z = true :=
  match x with
  | .p0 => checkAll2_StateP_sound _ preorders_P_row_0 y z
  | .p1 => checkAll2_StateP_sound _ preorders_P_row_1 y z
  | .p2 => checkAll2_StateP_sound _ preorders_P_row_2 y z
  | .p3 => checkAll2_StateP_sound _ preorders_P_row_3 y z
  | .p4 => checkAll2_StateP_sound _ preorders_P_row_4 y z
  | .p5 => checkAll2_StateP_sound _ preorders_P_row_5 y z
  | .p6 => checkAll2_StateP_sound _ preorders_P_row_6 y z
  | .p7 => checkAll2_StateP_sound _ preorders_P_row_7 y z
  | .p8 => checkAll2_StateP_sound _ preorders_P_row_8 y z
  | .p9 => checkAll2_StateP_sound _ preorders_P_row_9 y z
  | .p10 => checkAll2_StateP_sound _ preorders_P_row_10 y z
  | .p11 => checkAll2_StateP_sound _ preorders_P_row_11 y z
  | .p12 => checkAll2_StateP_sound _ preorders_P_row_12 y z
  | .p13 => checkAll2_StateP_sound _ preorders_P_row_13 y z
  | .p14 => checkAll2_StateP_sound _ preorders_P_row_14 y z
  | .p15 => checkAll2_StateP_sound _ preorders_P_row_15 y z
  | .p16 => checkAll2_StateP_sound _ preorders_P_row_16 y z
  | .p17 => checkAll2_StateP_sound _ preorders_P_row_17 y z
  | .p18 => checkAll2_StateP_sound _ preorders_P_row_18 y z
  | .p19 => checkAll2_StateP_sound _ preorders_P_row_19 y z
  | .p20 => checkAll2_StateP_sound _ preorders_P_row_20 y z
  | .p21 => checkAll2_StateP_sound _ preorders_P_row_21 y z
  | .p22 => checkAll2_StateP_sound _ preorders_P_row_22 y z
  | .p23 => checkAll2_StateP_sound _ preorders_P_row_23 y z
  | .p24 => checkAll2_StateP_sound _ preorders_P_row_24 y z
  | .p25 => checkAll2_StateP_sound _ preorders_P_row_25 y z
  | .p26 => checkAll2_StateP_sound _ preorders_P_row_26 y z
  | .p27 => checkAll2_StateP_sound _ preorders_P_row_27 y z
  | .p28 => checkAll2_StateP_sound _ preorders_P_row_28 y z
  | .p29 => checkAll2_StateP_sound _ preorders_P_row_29 y z
  | .p30 => checkAll2_StateP_sound _ preorders_P_row_30 y z
  | .p31 => checkAll2_StateP_sound _ preorders_P_row_31 y z
  | .p32 => checkAll2_StateP_sound _ preorders_P_row_32 y z
  | .p33 => checkAll2_StateP_sound _ preorders_P_row_33 y z
  | .p34 => checkAll2_StateP_sound _ preorders_P_row_34 y z
  | .p35 => checkAll2_StateP_sound _ preorders_P_row_35 y z
  | .p36 => checkAll2_StateP_sound _ preorders_P_row_36 y z
  | .p37 => checkAll2_StateP_sound _ preorders_P_row_37 y z
  | .p38 => checkAll2_StateP_sound _ preorders_P_row_38 y z
theorem le_P_0_is_compat_preorder : IsCompatPreorder deltaP le_P_0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_left (checkAll1_StateP_sound _ preorders_P_refl x)))
  · intro x y z hxy
    have hst : le_P_0_step x y z = true := (and_left (and_left (allPreorders_P_sound x y z)))
    unfold le_P_0_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_P_0_step x y z = true := (and_left (and_left (allPreorders_P_sound x y z)))
    unfold le_P_0_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_P_0_step x y z = true := (and_left (and_left (allPreorders_P_sound x y z)))
    unfold le_P_0_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_P_1_is_compat_preorder : IsCompatPreorder deltaP le_P_1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_right (and_left (checkAll1_StateP_sound _ preorders_P_refl x)))
  · intro x y z hxy
    have hst : le_P_1_step x y z = true := (and_right (and_left (allPreorders_P_sound x y z)))
    unfold le_P_1_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_P_1_step x y z = true := (and_right (and_left (allPreorders_P_sound x y z)))
    unfold le_P_1_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_P_1_step x y z = true := (and_right (and_left (allPreorders_P_sound x y z)))
    unfold le_P_1_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_P_2_is_compat_preorder : IsCompatPreorder deltaP le_P_2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_right (checkAll1_StateP_sound _ preorders_P_refl x)))
  · intro x y z hxy
    have hst : le_P_2_step x y z = true := (and_left (and_right (allPreorders_P_sound x y z)))
    unfold le_P_2_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_P_2_step x y z = true := (and_left (and_right (allPreorders_P_sound x y z)))
    unfold le_P_2_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_P_2_step x y z = true := (and_left (and_right (allPreorders_P_sound x y z)))
    unfold le_P_2_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_P_3_is_compat_preorder : IsCompatPreorder deltaP le_P_3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_left (and_right (and_right (checkAll1_StateP_sound _ preorders_P_refl x))))
  · intro x y z hxy
    have hst : le_P_3_step x y z = true := (and_left (and_right (and_right (allPreorders_P_sound x y z))))
    unfold le_P_3_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_P_3_step x y z = true := (and_left (and_right (and_right (allPreorders_P_sound x y z))))
    unfold le_P_3_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_P_3_step x y z = true := (and_left (and_right (and_right (allPreorders_P_sound x y z))))
    unfold le_P_3_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem le_P_4_is_compat_preorder : IsCompatPreorder deltaP le_P_4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact (and_right (and_right (and_right (checkAll1_StateP_sound _ preorders_P_refl x))))
  · intro x y z hxy
    have hst : le_P_4_step x y z = true := (and_right (and_right (and_right (allPreorders_P_sound x y z))))
    unfold le_P_4_step at hst; rw [hxy] at hst
    exact and_left (and_left hst)
  · intro x y z hxy
    have hst : le_P_4_step x y z = true := (and_right (and_right (and_right (allPreorders_P_sound x y z))))
    unfold le_P_4_step at hst; rw [hxy] at hst
    exact and_right (and_left hst)
  · intro x y z hxy hyz
    have hst : le_P_4_step x y z = true := (and_right (and_right (and_right (allPreorders_P_sound x y z))))
    unfold le_P_4_step at hst; rw [hxy] at hst
    have htr := and_right hst; rw [hyz] at htr; exact htr
theorem no_unary_not_P (U : Poly StateP 1) (q0 q1 : StateP)
    (h0 : evalPoly deltaP U (fun _ => q0) = q1)
    (h1 : evalPoly deltaP U (fun _ => q1) = q0) : q0 = q1 := by
  cases hbeq : beq_StateP q0 q1 with
  | true => exact beq_StateP_eq hbeq
  | false =>
    have hall := checkAll2_StateP_sound _ sep_P_all_bool q0 q1
    rw [hbeq] at hall
    have hsep : sep_P q0 q1 = true := hall
    unfold sep_P at hsep
    cases or_eq_true_elim hsep with
    | inr hcur => exfalso; exact compat_preorder_no_swap deltaP le_P_4 le_P_4_is_compat_preorder U q0 q1 h0 h1 hcur
    | inl hsep =>
      cases or_eq_true_elim hsep with
      | inr hcur => exfalso; exact compat_preorder_no_swap deltaP le_P_3 le_P_3_is_compat_preorder U q0 q1 h0 h1 hcur
      | inl hsep =>
        cases or_eq_true_elim hsep with
        | inr hcur => exfalso; exact compat_preorder_no_swap deltaP le_P_2 le_P_2_is_compat_preorder U q0 q1 h0 h1 hcur
        | inl hsep =>
          cases or_eq_true_elim hsep with
          | inr hcur => exfalso; exact compat_preorder_no_swap deltaP le_P_1 le_P_1_is_compat_preorder U q0 q1 h0 h1 hcur
          | inl hsep =>
            exfalso; exact compat_preorder_no_swap deltaP le_P_0 le_P_0_is_compat_preorder U q0 q1 h0 h1 hsep

theorem no_nand_P (P : Poly StateP 2) (q0 q1 : StateP) (hne : q0 ≠ q1) :
    ¬ IsPolyNAND deltaP P q0 q1 :=
  fun h => hne (nand_implies_eq_of_no_not deltaP (no_unary_not_P) P q0 q1 h)

theorem no_xor_P (P : Poly StateP 2) (q0 q1 : StateP) (hne : q0 ≠ q1) :
    ¬ IsPolyXOR deltaP P q0 q1 :=
  fun h => hne (xor_implies_eq_of_no_not deltaP (no_unary_not_P) P q0 q1 h)

theorem no_rule110_P (P : Poly StateP 3) (q0 q1 : StateP) (hne : q0 ≠ q1) :
    ¬ IsPolyRule110 deltaP P q0 q1 :=
  fun h => hne (rule110_implies_eq_of_no_not deltaP (no_unary_not_P) P q0 q1 h)

theorem clone_monotone_all_arities_P {k : Nat} (P : Poly StateP k)
    (q0 q1 : StateP) (hne : q0 ≠ q1) (env : Fin k → Bool) (i : Fin k) :
    ¬ (evalPoly deltaP P (fun j => cond (j.val == i.val) q0 (cond (env j) q1 q0)) = q1 ∧
       evalPoly deltaP P (fun j => cond (j.val == i.val) q1 (cond (env j) q1 q0)) = q0) :=
  fun h => hne (nonmono_edge_implies_eq_of_no_not deltaP (no_unary_not_P) P q0 q1 env i h)


def snOrWitness : Poly StateSN 2 := (.app (.const .s0) (.app (.var ⟨0, Nat.zero_lt_succ 1⟩) (.var ⟨1, Nat.succ_lt_succ Nat.zero_lt_one⟩)))

theorem sn_or_witness_correct :
    evalPoly deltaSN snOrWitness (pairEnv .s6 .s6) = .s6 ∧
    evalPoly deltaSN snOrWitness (pairEnv .s6 .s38) = .s38 ∧
    evalPoly deltaSN snOrWitness (pairEnv .s38 .s6) = .s38 ∧
    evalPoly deltaSN snOrWitness (pairEnv .s38 .s38) = .s38 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 3. Minimal Non-Aperiodic (`n = 3`) & Functionally Complete (`n = 4`) `S`-Algebras -/

inductive StateDNOT where
  | n0 | n1 | n2
  deriving DecidableEq, Repr

def deltaDNOT : StateDNOT → StateDNOT → StateDNOT
  | .n0, .n1 => .n2
  | .n0, _   => .n1
  | _,   _   => .n1

theorem deltaDNOT_s_law (x y z : StateDNOT) :
    deltaDNOT (deltaDNOT (deltaDNOT .n0 x) y) z =
    deltaDNOT (deltaDNOT x z) (deltaDNOT y z) := by
  cases x <;> cases y <;> cases z <;> rfl

def evalDNOT : Term → StateDNOT
  | .s => .n0
  | .var _ => .n0
  | .app a b => deltaDNOT (evalDNOT a) (evalDNOT b)

theorem evalDNOT_conv_invariant {a b : Term} (h : ConvS a b) : evalDNOT a = evalDNOT b := by
  induction h with
  | refl _ => rfl
  | step hs =>
    induction hs with
    | root x y z => exact deltaDNOT_s_law (evalDNOT x) (evalDNOT y) (evalDNOT z)
    | left _ ih => simp only [evalDNOT, ih]
    | right _ ih => simp only [evalDNOT, ih]
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem dnot_curried_s_swaps :
    evalDNOT S = .n0 ∧
    evalDNOT (S ⋅ S) = .n1 ∧
    evalDNOT (S ⋅ (S ⋅ S)) = .n2 ∧
    deltaDNOT .n0 .n1 = .n2 ∧
    deltaDNOT .n0 .n2 = .n1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

inductive StateDNAND where
  | d0 | d1 | d2 | d3
  deriving DecidableEq, Repr

def deltaDNAND : StateDNAND → StateDNAND → StateDNAND
  | .d0, .d3 => .d2
  | .d0, _   => .d1
  | .d2, .d0 => .d1
  | .d2, .d1 => .d1
  | _,   _   => .d3

theorem deltaDNAND_s_law (x y z : StateDNAND) :
    deltaDNAND (deltaDNAND (deltaDNAND .d0 x) y) z =
    deltaDNAND (deltaDNAND x z) (deltaDNAND y z) := by
  cases x <;> cases y <;> cases z <;> rfl

def evalDNAND : Term → StateDNAND
  | .s => .d0
  | .var _ => .d0
  | .app a b => deltaDNAND (evalDNAND a) (evalDNAND b)

theorem evalDNAND_step_invariant {a b : Term} (h : Step a b) : evalDNAND a = evalDNAND b := by
  induction h with
  | root x y z => exact deltaDNAND_s_law (evalDNAND x) (evalDNAND y) (evalDNAND z)
  | left _ ih => simp only [evalDNAND, ih]
  | right _ ih => simp only [evalDNAND, ih]

theorem evalDNAND_conv_invariant {a b : Term} (h : ConvS a b) : evalDNAND a = evalDNAND b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalDNAND_step_invariant hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def FalseTerm : Term := S ⋅ S
def TrueTerm  : Term := S ⋅ (S ⋅ S ⋅ S)

def encodeBoolState : Bool → StateDNAND
  | false => .d1
  | true  => .d2

def encodeBoolTerm : Bool → Term
  | false => FalseTerm
  | true  => TrueTerm

theorem dnand_1generated :
    evalDNAND S = .d0 ∧
    evalDNAND FalseTerm = .d1 ∧
    evalDNAND TrueTerm = .d2 ∧
    evalDNAND (S ⋅ S ⋅ S) = .d3 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem evalDNAND_encodeBool (b : Bool) : evalDNAND (encodeBoolTerm b) = encodeBoolState b := by
  cases b <;> rfl

def notTerm (x : Term) : Term := S ⋅ (x ⋅ S)
def nandTerm (x y : Term) : Term := S ⋅ (x ⋅ (y ⋅ S))
def rule110Term (x y z : Term) : Term :=
  S ⋅ (S ⋅ (y ⋅ x) ⋅ (S ⋅ (y ⋅ z) ⋅ (S ⋅ (z ⋅ y) ⋅ S)))

inductive Gate16 where
  | g0 | g1 | g2 | g3 | g4 | g5 | g6 | g7 | g8 | g9 | g10 | g11 | g12 | g13 | g14 | g15
  deriving DecidableEq, Repr

def binGateTerm : Gate16 → Term → Term → Term
  | .g0,  _, _ => S ⋅ S
  | .g1,  x, y => S ⋅ (S ⋅ (S ⋅ (x ⋅ S) ⋅ y) ⋅ S)
  | .g2,  x, y => S ⋅ (S ⋅ (y ⋅ x) ⋅ S)
  | .g3,  x, _ => S ⋅ (x ⋅ S)
  | .g4,  x, y => S ⋅ (S ⋅ (x ⋅ y) ⋅ S)
  | .g5,  _, y => S ⋅ (y ⋅ S)
  | .g6,  x, y => S ⋅ (S ⋅ (x ⋅ y) ⋅ (S ⋅ (y ⋅ x) ⋅ S))
  | .g7,  x, y => S ⋅ (x ⋅ (y ⋅ S))
  | .g8,  x, y => S ⋅ (S ⋅ (x ⋅ (y ⋅ S)) ⋅ S)
  | .g9,  x, y => S ⋅ (S ⋅ (S ⋅ (x ⋅ y) ⋅ (S ⋅ (y ⋅ x) ⋅ S)) ⋅ S)
  | .g10, _, y => y
  | .g11, x, y => S ⋅ (x ⋅ y)
  | .g12, x, _ => x
  | .g13, x, y => S ⋅ (y ⋅ x)
  | .g14, x, y => S ⋅ (S ⋅ (x ⋅ S) ⋅ y)
  | .g15, x, _ => S ⋅ (x ⋅ x)

def specBinGate : Gate16 → Bool → Bool → Bool
  | .g0,  _,  _   => false
  | .g1,  bx, by_ => !(bx || by_)
  | .g2,  bx, by_ => (!bx) && by_
  | .g3,  bx, _   => !bx
  | .g4,  bx, by_ => bx && (!by_)
  | .g5,  _,  by_ => !by_
  | .g6,  bx, by_ => bx != by_
  | .g7,  bx, by_ => !(bx && by_)
  | .g8,  bx, by_ => bx && by_
  | .g9,  bx, by_ => bx == by_
  | .g10, _,  by_ => by_
  | .g11, bx, by_ => (!bx) || by_
  | .g12, bx, _   => bx
  | .g13, bx, by_ => bx || (!by_)
  | .g14, bx, by_ => bx || by_
  | .g15, _,  _   => true

theorem dnand_linear_nand_correct (x y : Term) (bx by_ : Bool)
    (hx : evalDNAND x = encodeBoolState bx) (hy : evalDNAND y = encodeBoolState by_) :
    evalDNAND (nandTerm x y) = encodeBoolState (!(bx && by_)) := by
  simp only [nandTerm, evalDNAND, hx, hy]
  cases bx <;> cases by_ <;> rfl

theorem dnand_all_16_binary_gates_correct (g : Gate16) (x y : Term) (bx by_ : Bool)
    (hx : evalDNAND x = encodeBoolState bx) (hy : evalDNAND y = encodeBoolState by_) :
    evalDNAND (binGateTerm g x y) = encodeBoolState (specBinGate g bx by_) := by
  cases g <;> simp only [binGateTerm, specBinGate, evalDNAND, hx, hy] <;> cases bx <;> cases by_ <;> rfl

def rule110Bool (bL bC bR : Bool) : Bool :=
  match bL, bC, bR with
  | true,  true,  true  => false
  | true,  true,  false => true
  | true,  false, true  => true
  | true,  false, false => false
  | false, true,  true  => true
  | false, true,  false => true
  | false, false, true  => true
  | false, false, false => false

theorem dnand_rule110_correct (x y z : Term) (bL bC bR : Bool)
    (hx : evalDNAND x = encodeBoolState bL)
    (hy : evalDNAND y = encodeBoolState bC)
    (hz : evalDNAND z = encodeBoolState bR) :
    evalDNAND (rule110Term x y z) = encodeBoolState (rule110Bool bL bC bR) := by
  simp only [rule110Term, evalDNAND, hx, hy, hz]
  cases bL <;> cases bC <;> cases bR <;> rfl

def isNF : Term → Bool
  | .s => true
  | .var _ => true
  | .app .s a => isNF a
  | .app (.app .s a) b => isNF a && isNF b
  | .app (.app (.app _ _) _) _ => false
  | .app (.var _) a => isNF a
  | .app (.app (.var _) a) b => isNF a && isNF b

theorem isNF_sound : ∀ (t : Term), isNF t = true → ∀ (t' : Term), ¬ Step t t'
  | .s, _, _, hs => by cases hs
  | .var _, _, _, hs => by cases hs
  | .app .s a, hnf, _, hs => by
    cases hs with
    | left hl => cases hl
    | right hr => exact isNF_sound a hnf _ hr
  | .app (.var _) a, hnf, _, hs => by
    cases hs with
    | left hl => cases hl
    | right hr => exact isNF_sound a hnf _ hr
  | .app (.app .s a) b, hnf, _, hs => by
    have ha := and_left hnf
    have hb := and_right hnf
    cases hs with
    | left hl =>
      cases hl with
      | left hll => cases hll
      | right hlr => exact isNF_sound a ha _ hlr
    | right hr => exact isNF_sound b hb _ hr
  | .app (.app (.var _) a) b, hnf, _, hs => by
    have ha := and_left hnf
    have hb := and_right hnf
    cases hs with
    | left hl =>
      cases hl with
      | left hll => cases hll
      | right hlr => exact isNF_sound a ha _ hlr
    | right hr => exact isNF_sound b hb _ hr
  | .app (.app (.app _ _) _) _, hnf, _, _ => by cases hnf

def isSpine1NF : Term → Bool
  | .app .s w => isNF w
  | _ => false

theorem isSpine1NF_implies_isNF (t : Term) (h : isSpine1NF t = true) : isNF t = true := by
  cases t with
  | s => cases h
  | var _ => cases h
  | app l r =>
    cases l with
    | s => exact h
    | var _ => cases h
    | app _ _ => cases h

theorem base_cells_spine1NF (b : Bool) : isSpine1NF (encodeBoolTerm b) = true := by
  cases b <;> rfl

theorem rule110Term_preserves_spine1NF (x y z : Term)
    (hx : isSpine1NF x = true) (hy : isSpine1NF y = true) (hz : isSpine1NF z = true) :
    isSpine1NF (rule110Term x y z) = true := by
  cases x with
  | s => cases hx
  | var _ => cases hx
  | app lx wx =>
    cases lx with
    | var _ => cases hx
    | app _ _ => cases hx
    | s =>
      cases y with
      | s => cases hy
      | var _ => cases hy
      | app ly wy =>
        cases ly with
        | var _ => cases hy
        | app _ _ => cases hy
        | s =>
          cases z with
          | s => cases hz
          | var _ => cases hz
          | app lz wz =>
            cases lz with
            | var _ => cases hz
            | app _ _ => cases hz
            | s =>
              have hwx : isNF wx = true := hx
              have hwy : isNF wy = true := hy
              have hwz : isNF wz = true := hz
              change ((isNF wy && isNF wx) && ((isNF wy && isNF wz) && ((isNF wz && isNF wy) && true))) = true
              rw [hwx, hwy, hwz]
              rfl

def stepRule110Terms {W : Nat} (hW : 0 < W) (row : Fin W → Term) : Fin W → Term :=
  fun i =>
    let iL : Fin W := ⟨(i.val + W - 1) % W, Nat.mod_lt _ hW⟩
    let iR : Fin W := ⟨(i.val + 1) % W, Nat.mod_lt _ hW⟩
    rule110Term (row iL) (row i) (row iR)

def stepRule110Bools {W : Nat} (hW : 0 < W) (row : Fin W → Bool) : Fin W → Bool :=
  fun i =>
    let iL : Fin W := ⟨(i.val + W - 1) % W, Nat.mod_lt _ hW⟩
    let iR : Fin W := ⟨(i.val + 1) % W, Nat.mod_lt _ hW⟩
    rule110Bool (row iL) (row i) (row iR)

def iterRule110Terms {W : Nat} (hW : 0 < W) : Nat → (Fin W → Term) → (Fin W → Term)
  | 0, row => row
  | t + 1, row => iterRule110Terms hW t (stepRule110Terms hW row)

def iterRule110Bools {W : Nat} (hW : 0 < W) : Nat → (Fin W → Bool) → (Fin W → Bool)
  | 0, row => row
  | t + 1, row => iterRule110Bools hW t (stepRule110Bools hW row)

theorem iterRule110_exact_simulation {W : Nat} (hW : 0 < W) (t : Nat)
    (rowT : Fin W → Term) (rowB : Fin W → Bool)
    (hinit : ∀ i, evalDNAND (rowT i) = encodeBoolState (rowB i) ∧ isSpine1NF (rowT i) = true) :
    ∀ i, evalDNAND (iterRule110Terms hW t rowT i) = encodeBoolState (iterRule110Bools hW t rowB i) ∧
         isSpine1NF (iterRule110Terms hW t rowT i) = true := by
  induction t generalizing rowT rowB with
  | zero => exact hinit
  | succ t ih =>
    apply ih
    intro i
    let iL : Fin W := ⟨(i.val + W - 1) % W, Nat.mod_lt _ hW⟩
    let iR : Fin W := ⟨(i.val + 1) % W, Nat.mod_lt _ hW⟩
    exact ⟨
      dnand_rule110_correct _ _ _ _ _ _ (hinit iL).1 (hinit i).1 (hinit iR).1,
      rule110Term_preserves_spine1NF _ _ _ (hinit iL).2 (hinit i).2 (hinit iR).2
    ⟩

/-! ## Section 4. Three-Fold Dynamic Cellular Driver Obstruction Theorem -/

theorem dnand_curried2_collapses_to_d3 (g y : StateDNAND) (bx : Bool) :
    deltaDNAND (deltaDNAND g (encodeBoolState bx)) y = .d3 := by
  cases g <;> cases bx <;> cases y <;> rfl

theorem dnand_curried3_collapses_to_d3 (g y z : StateDNAND) (bx : Bool) :
    deltaDNAND (deltaDNAND (deltaDNAND g (encodeBoolState bx)) y) z = .d3 := by
  cases g <;> cases bx <;> cases y <;> cases z <;> rfl

theorem dnand_no_curried_nand_combinator (G : Term) :
    ¬ (∀ (bx by_ : Bool),
        evalDNAND ((G ⋅ encodeBoolTerm bx) ⋅ encodeBoolTerm by_) = encodeBoolState (!(bx && by_))) := by
  intro h
  have h00 := h false false
  simp only [evalDNAND, evalDNAND_encodeBool] at h00
  rw [dnand_curried2_collapses_to_d3] at h00
  cases h00

theorem dnand_no_curried_rule110_combinator (G : Term) :
    ¬ (∀ (bL bC bR : Bool),
        evalDNAND (((G ⋅ encodeBoolTerm bL) ⋅ encodeBoolTerm bC) ⋅ encodeBoolTerm bR) =
        encodeBoolState (rule110Bool bL bC bR)) := by
  intro h
  have h000 := h false false false
  simp only [evalDNAND, evalDNAND_encodeBool] at h000
  rw [dnand_curried3_collapses_to_d3] at h000
  cases h000

def hasSpineGe2 : Term → Bool
  | .app (.app _ _) _ => true
  | _ => false

theorem spineGe2_preserved_step {a b : Term} (h : Step a b) :
    hasSpineGe2 a = true → hasSpineGe2 b = true := by
  cases h with
  | root x y z => intro _; rfl
  | @left l l' r hl =>
    cases hl with
    | root x y z => intro _; rfl
    | left _ => intro _; rfl
    | @right ll lr lr' _ => cases ll <;> intro _ <;> rfl
  | @right l r r' _ =>
    cases l with
    | s => intro hge; cases hge
    | var _ => intro hge; cases hge
    | app _ _ => intro _; rfl

theorem spineGe2_preserved_reduces {a b : Term} (h : Reduces a b) :
    hasSpineGe2 a = true → hasSpineGe2 b = true := by
  induction h with
  | refl _ => intro hge; exact hge
  | next hs _ ih => intro hge; exact ih (spineGe2_preserved_step hs hge)

theorem no_dynamic_spine1_cell (a b c w : Term) :
    ¬ Reduces ((a ⋅ b) ⋅ c) (S ⋅ w) := by
  intro h
  have hge := spineGe2_preserved_reduces h rfl
  cases hge

theorem no_combinator_reduces_to_nandTerm (G x y : Term) :
    ¬ Reduces ((G ⋅ x) ⋅ y) (nandTerm x y) :=
  no_dynamic_spine1_cell G x y (x ⋅ (y ⋅ S))

theorem no_combinator_reduces_to_rule110Term (G x y z : Term) :
    ¬ Reduces (((G ⋅ x) ⋅ y) ⋅ z) (rule110Term x y z) :=
  no_dynamic_spine1_cell (G ⋅ x) y z (S ⋅ (y ⋅ x) ⋅ (S ⋅ (y ⋅ z) ⋅ (S ⋅ (z ⋅ y) ⋅ S)))

theorem no_combinator_conv_nandTerm (G : Term) :
    ¬ (ConvS ((G ⋅ FalseTerm) ⋅ FalseTerm) (nandTerm FalseTerm FalseTerm)) := by
  intro hconv
  have heq := evalDNAND_conv_invariant hconv
  have hlhs : evalDNAND ((G ⋅ FalseTerm) ⋅ FalseTerm) = .d3 :=
    dnand_curried2_collapses_to_d3 (evalDNAND G) .d1 false
  have hrhs : evalDNAND (nandTerm FalseTerm FalseTerm) = .d2 := rfl
  rw [hlhs, hrhs] at heq
  cases heq

theorem no_combinator_conv_rule110Term (G : Term) :
    ¬ (ConvS (((G ⋅ FalseTerm) ⋅ FalseTerm) ⋅ FalseTerm) (rule110Term FalseTerm FalseTerm FalseTerm)) := by
  intro hconv
  have heq := evalDNAND_conv_invariant hconv
  have hlhs : evalDNAND (((G ⋅ FalseTerm) ⋅ FalseTerm) ⋅ FalseTerm) = .d3 :=
    dnand_curried3_collapses_to_d3 (evalDNAND G) .d1 .d1 false
  have hrhs : evalDNAND (rule110Term FalseTerm FalseTerm FalseTerm) = .d1 := rfl
  rw [hlhs, hrhs] at heq
  cases heq

end ZeroNavigatorCellular
