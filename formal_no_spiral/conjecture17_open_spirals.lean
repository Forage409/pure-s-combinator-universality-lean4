import formal_no_spiral.waldmann_no_spiral

/-!
# Attack on Conjecture 17, Parts I & II (*Dance of the Starlings*, 2018, Section 5.4, p. 89): Leaf-Merged Weighted Right-Spine LPO & Constructive Dependency-Pair Self-Right-Tail Theorem

100% self-contained, constructive Lean 4.33.1 formalization (zero `Classical.choice`, zero `sorry`,
zero `native_decide`, independent of `A_HN`):

1. **Part I — Leaf-Merged Weighted Right-Spine LPO (`conjecture17_weighted_waldmann`)**:
   Whenever variable weights `w : Nat → Nat` satisfy `rhoW w (σ x) ≤ w x` for all `x` occurring in `M`,
   `∀ C, ¬ StepPlus M (plugCtx C (subst σ M))`.
   Corollaries: `conjecture17_ground_right_spine_subst` and `conjecture17_nonincreasing_rs_subst`.

2. **Part II — Constructive Step-Indexed Dependency-Pair Extractor & Master Self-Right-Tail Theorem
   (`conjecture17_no_open_spiral_unless_self_right_tail`)**:
   Constructively proves that if NO variable `x` occurring in `M` satisfies BOTH
   `rightLeaf (σ x) = .var x` AND `1 ≤ rs (σ x)`, then `∀ C, ¬ StepPlus M (plugCtx C (subst σ M))`!
   Corollaries: `conjecture17_distinct_rightLeaf_subst` (eliminating all period-`≥ 2` cyclic right-spine
   growth substitutions!) and `conjecture17_single_var`.
-/

namespace FormalNoSpiral

/-! ## 0. Exact `rightLeaf`, `rs`, and `hasVar` Structural Laws -/

theorem rightLeaf_step {a b : Term} (h : Step a b) : rightLeaf a = rightLeaf b := by
  induction h with
  | root x y z => rfl
  | left _ _ => rfl
  | right _ ih => exact ih

theorem rightLeaf_reduces {a b : Term} (h : Reduces a b) : rightLeaf a = rightLeaf b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (rightLeaf_step hs).trans ih

theorem rightLeaf_leaves_one (t : Term) :
    rightLeaf t = .s ∨ ∃ x, rightLeaf t = .var x := by
  induction t with
  | s => exact Or.inl rfl
  | var x => exact Or.inr ⟨x, rfl⟩
  | app _ _ _ ihb => exact ihb

theorem hasVar_rightLeaf {x : Nat} {t : Term} (h : rightLeaf t = .var x) :
    hasVar x t = true := by
  induction t with
  | s => cases h
  | var k =>
    injection h with hk
    subst hk
    simp [hasVar]
  | app _ _ _ ihb =>
    simp only [hasVar, Bool.or_eq_true]
    exact Or.inr (ihb h)

theorem hasVar_plugCtx {x : Nat} (c : Ctx) {u : Term} (hu : hasVar x u = true) :
    hasVar x (plugCtx c u) = true := by
  induction c with
  | hole => exact hu
  | left _ _ ih =>
    simp only [plugCtx, hasVar, Bool.or_eq_true]
    exact Or.inl ih
  | right _ _ ih =>
    simp only [plugCtx, hasVar, Bool.or_eq_true]
    exact Or.inr ih

theorem rightLeaf_subst_of_s {t : Term} (σ : Nat → Term) (h : rightLeaf t = .s) :
    rightLeaf (subst σ t) = .s ∧ rs (subst σ t) = rs t := by
  induction t with
  | s => exact ⟨rfl, rfl⟩
  | var _ => cases h
  | app _ _ _ ihb =>
    obtain ⟨hrl, hrs⟩ := ihb h
    exact ⟨hrl, congrArg (1 + ·) hrs⟩

theorem rightLeaf_subst_of_var {t : Term} {x : Nat} (σ : Nat → Term) (h : rightLeaf t = .var x) :
    rightLeaf (subst σ t) = rightLeaf (σ x) ∧ rs (subst σ t) = rs t + rs (σ x) := by
  induction t with
  | s => cases h
  | var k =>
    injection h with hk
    subst hk
    exact ⟨rfl, (Nat.zero_add (rs (σ k))).symm⟩
  | app _ _ _ ihb =>
    obtain ⟨hrl, hrs⟩ := ihb h
    refine ⟨hrl, ?_⟩
    change 1 + rs (subst σ _) = (1 + rs _) + rs (σ x)
    rw [hrs, Nat.add_assoc]

/-! ## 1. Part I: Leaf-Merged Weighted Right-Spine LPO (`conjecture17_weighted_waldmann`) -/

def rhoW (w : Nat → Nat) : Term → Nat
  | .s => 1
  | .var k => w k
  | .app _ b => 1 + rhoW w b

theorem rhoW_mono_step (w : Nat → Nat) {a b : Term} (h : Step a b) :
    rhoW w a ≤ rhoW w b := by
  induction h with
  | root x y z =>
    change 1 + rhoW w z ≤ 1 + (1 + rhoW w z)
    exact Nat.add_le_add_left (Nat.le_add_left (rhoW w z) 1) 1
  | left _ _ => exact Nat.le_refl _
  | right _ ih => exact Nat.add_le_add_left ih 1

theorem rhoW_subst_of_s (w : Nat → Nat) (σ : Nat → Term) {t : Term} (h : rightLeaf t = .s) :
    rhoW w (subst σ t) = rhoW w t := by
  induction t with
  | s => rfl
  | var _ => cases h
  | app _ _ _ ihb => exact congrArg (1 + ·) (ihb h)

theorem rhoW_subst_of_var (w : Nat → Nat) (σ : Nat → Term) {t : Term} {x : Nat}
    (h : rightLeaf t = .var x) :
    rhoW w (subst σ t) = rs t + rhoW w (σ x) ∧ rhoW w t = rs t + w x := by
  induction t with
  | s => cases h
  | var k =>
    injection h with hk
    subst hk
    exact ⟨(Nat.zero_add (rhoW w (σ k))).symm, (Nat.zero_add (w k)).symm⟩
  | app _ b _ ihb =>
    obtain ⟨h1, h2⟩ := ihb h
    refine ⟨?_, ?_⟩
    · change 1 + rhoW w (subst σ b) = (1 + rs b) + rhoW w (σ x)
      rw [h1, Nat.add_assoc]
    · change 1 + rhoW w b = (1 + rs b) + w x
      rw [h2, Nat.add_assoc]

theorem rhoW_subst_le (w : Nat → Nat) (σ : Nat → Term) (t : Term)
    (hw : ∀ x, hasVar x t = true → rhoW w (σ x) ≤ w x) :
    rhoW w (subst σ t) ≤ rhoW w t := by
  rcases rightLeaf_leaves_one t with hs | ⟨x, hx⟩
  · rw [rhoW_subst_of_s w σ hs]
    exact Nat.le_refl _
  · obtain ⟨h1, h2⟩ := rhoW_subst_of_var w σ hx
    rw [h1, h2]
    exact Nat.add_le_add_left (hw x (hasVar_rightLeaf hx)) (rs t)

inductive LeafLTerm where
  | leaf : LeafLTerm
  | app : Nat → LeafLTerm → LeafLTerm → LeafLTerm
  deriving DecidableEq, Repr

def toLeafLTerm (w : Nat → Nat) : Term → LeafLTerm
  | .s => .leaf
  | .var _ => .leaf
  | .app a b => .app (rhoW w b) (toLeafLTerm w a) (toLeafLTerm w b)

def maxLeafLabel : LeafLTerm → Nat
  | .leaf => 0
  | .app k a b => Nat.max k (Nat.max (maxLeafLabel a) (maxLeafLabel b))

theorem maxLeafLabel_app_le_iff {k : Nat} {a b : LeafLTerm} {B : Nat} :
    maxLeafLabel (.app k a b) ≤ B ↔ k ≤ B ∧ maxLeafLabel a ≤ B ∧ maxLeafLabel b ≤ B := by
  simp only [maxLeafLabel, Nat.max_le]

def flipLeafLabels (B : Nat) : LeafLTerm → LeafLTerm
  | .leaf => .leaf
  | .app k a b => .app (B - k) (flipLeafLabels B a) (flipLeafLabels B b)

inductive StepRBLeaf : LeafLTerm → LeafLTerm → Prop where
  | left {d : Nat} {a a' b : LeafLTerm} : StepRBLeaf a a' → StepRBLeaf (.app d a b) (.app d a' b)
  | right {d : Nat} {a b b' : LeafLTerm} : StepRBLeaf b b' → StepRBLeaf (.app d a b) (.app d a b')
  | subL (d : Nat) (a b : LeafLTerm) : StepRBLeaf (.app d a b) a
  | subR (d : Nat) (a b : LeafLTerm) : StepRBLeaf (.app d a b) b
  | lift {d d' : Nat} (a b : LeafLTerm) : d' < d → StepRBLeaf (.app d a b) (.app d' a b)
  | beta {d d' d1 d2 : Nat} (x y z : LeafLTerm) :
      d' < d → StepRBLeaf (.app d (.app d2 (.app d1 .leaf x) y) z) (.app d' (.app d x z) (.app d y z))

private theorem stepRBLeaf_left_trans {d : Nat} {a a' : LeafLTerm}
    (h : TransGen StepRBLeaf a a') (b : LeafLTerm) :
    TransGen StepRBLeaf (.app d a b) (.app d a' b) := by
  induction h with
  | single hs => exact .single (.left hs)
  | tail _ hs ih => exact .tail ih (.left hs)

private theorem stepRBLeaf_right_trans {d : Nat} (a : LeafLTerm) {b b' : LeafLTerm}
    (h : TransGen StepRBLeaf b b') :
    TransGen StepRBLeaf (.app d a b) (.app d a b') := by
  induction h with
  | single hs => exact .single (.right hs)
  | tail _ hs ih => exact .tail ih (.right hs)

private theorem stepRBLeaf_left_reflTrans {d : Nat} {a a' : LeafLTerm}
    (h : ReflTransGen StepRBLeaf a a') (b : LeafLTerm) :
    ReflTransGen StepRBLeaf (.app d a b) (.app d a' b) := by
  induction h with
  | refl _ => exact .refl _
  | head hs _ ih => exact .head (.left hs) ih

private theorem stepRBLeaf_right_reflTrans {d : Nat} (a : LeafLTerm) {b b' : LeafLTerm}
    (h : ReflTransGen StepRBLeaf b b') :
    ReflTransGen StepRBLeaf (.app d a b) (.app d a b') := by
  induction h with
  | refl _ => exact .refl _
  | head hs _ ih => exact .head (.right hs) ih

private theorem stepRBLeaf_app_acc :
    ∀ (d : Nat),
      (∀ d' < d, ∀ u v,
        Acc (fun y x => TransGen StepRBLeaf x y) u →
        Acc (fun y x => TransGen StepRBLeaf x y) v →
        Acc (fun y x => TransGen StepRBLeaf x y) (.app d' u v)) →
      ∀ (a : LeafLTerm), Acc (fun y x => TransGen StepRBLeaf x y) a →
      ∀ (b : LeafLTerm), Acc (fun y x => TransGen StepRBLeaf x y) b →
      Acc (fun y x => StepRBLeaf x y) (.app d a b) := by
  intro d ih_d a ha
  induction ha with
  | intro a h_prev_a ih_a =>
    intro b hb
    induction hb with
    | intro b h_prev_b ih_b =>
      have ha_acc : Acc (fun y x => TransGen StepRBLeaf x y) a := Acc.intro a h_prev_a
      have hb_acc : Acc (fun y x => TransGen StepRBLeaf x y) b := Acc.intro b h_prev_b
      refine Acc.intro (LeafLTerm.app d a b) (fun w hw => ?_)
      cases hw with
      | left ha' => exact ih_a _ (.single ha') b hb_acc
      | right hb' => exact ih_b _ (.single hb')
      | subL _ _ _ => exact acc_of_transGen ha_acc
      | subR _ _ _ => exact acc_of_transGen hb_acc
      | lift _ _ hlt => exact acc_of_transGen (ih_d _ hlt a b ha_acc hb_acc)
      | @beta _ d' d1 d2 x y _ hlt =>
        have hax : TransGen StepRBLeaf (LeafLTerm.app d2 (LeafLTerm.app d1 .leaf x) y) x :=
          transGen_head (.subL d2 (.app d1 .leaf x) y) (.single (.subR d1 .leaf x))
        have hay : TransGen StepRBLeaf (LeafLTerm.app d2 (LeafLTerm.app d1 .leaf x) y) y :=
          .single (.subR d2 (.app d1 .leaf x) y)
        have h_xb : Acc (fun y0 x0 => TransGen StepRBLeaf x0 y0) (.app d x b) :=
          acc_transGen (ih_a x hax b hb_acc)
        have h_yb : Acc (fun y0 x0 => TransGen StepRBLeaf x0 y0) (.app d y b) :=
          acc_transGen (ih_a y hay b hb_acc)
        exact acc_of_transGen (ih_d d' hlt (.app d x b) (.app d y b) h_xb h_yb)

private theorem stepRBLeaf_app_all (k : Nat) :
    ∀ d, d ≤ k → ∀ u v,
      Acc (fun y x => TransGen StepRBLeaf x y) u →
      Acc (fun y x => TransGen StepRBLeaf x y) v →
      Acc (fun y x => TransGen StepRBLeaf x y) (.app d u v) := by
  induction k with
  | zero =>
    intro d hd u v hu hv
    refine acc_transGen (stepRBLeaf_app_acc d (fun d' hlt => ?_) u hu v hv)
    cases Nat.eq_zero_of_le_zero hd
    cases hlt
  | succ k ihk =>
    intro d hd u v hu hv
    exact acc_transGen (stepRBLeaf_app_acc d
      (fun d' hlt => ihk d' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hd))) u hu v hv)

theorem stepRBLeaf_acc_plus (t : LeafLTerm) :
    Acc (fun y x => TransGen StepRBLeaf x y) t := by
  induction t with
  | leaf => exact acc_transGen (Acc.intro LeafLTerm.leaf (fun _ hy => by cases hy))
  | app d u v ihu ihv => exact stepRBLeaf_app_all d d (Nat.le_refl d) u v ihu ihv

private theorem leafLTerm_reduces_to_leaf (t : LeafLTerm) :
    ReflTransGen StepRBLeaf t LeafLTerm.leaf := by
  induction t with
  | leaf => exact .refl LeafLTerm.leaf
  | app d a b iha _ => exact .head (.subL d a b) iha

private theorem step_to_stepRBLeaf (B : Nat) (w : Nat → Nat) {a b : Term} (hs : Step a b)
    (ha : maxLeafLabel (toLeafLTerm w a) ≤ B) (hb : maxLeafLabel (toLeafLTerm w b) ≤ B) :
    TransGen StepRBLeaf (flipLeafLabels B (toLeafLTerm w a)) (flipLeafLabels B (toLeafLTerm w b)) := by
  induction hs with
  | root x y z =>
    have hb' : rhoW w (y ⋅ z) ≤ B := (maxLeafLabel_app_le_iff.mp hb).1
    have hlt_rho : rhoW w z < rhoW w (y ⋅ z) := by
      change rhoW w z < 1 + rhoW w z
      rw [Nat.add_comm 1 (rhoW w z)]
      exact Nat.lt_succ_self (rhoW w z)
    have hlt : B - rhoW w (y ⋅ z) < B - rhoW w z := sub_lt_sub_of_lt hlt_rho hb'
    exact .single (.beta (flipLeafLabels B (toLeafLTerm w x))
      (flipLeafLabels B (toLeafLTerm w y)) (flipLeafLabels B (toLeafLTerm w z)) hlt)
  | @left l l' r _ ih =>
    have hal := (maxLeafLabel_app_le_iff.mp ha).2.1
    have hbl := (maxLeafLabel_app_le_iff.mp hb).2.1
    exact stepRBLeaf_left_trans (ih hal hbl) (flipLeafLabels B (toLeafLTerm w r))
  | @right l r r' hr ih =>
    have har := (maxLeafLabel_app_le_iff.mp ha).2.2
    have hbr := (maxLeafLabel_app_le_iff.mp hb).2.2
    have hk_b := (maxLeafLabel_app_le_iff.mp hb).1
    have hmono := rhoW_mono_step w hr
    have ih_r := ih har hbr
    exact if heq : rhoW w r = rhoW w r' then by
      simp only [toLeafLTerm, flipLeafLabels, heq]
      exact stepRBLeaf_right_trans (flipLeafLabels B (toLeafLTerm w l)) ih_r
    else
      have hlt : B - rhoW w r' < B - rhoW w r :=
        sub_lt_sub_of_lt (Nat.lt_of_le_of_ne hmono heq) hk_b
      transGen_head (.lift _ _ hlt)
        (stepRBLeaf_right_trans (flipLeafLabels B (toLeafLTerm w l)) ih_r)

private theorem stepPlus_exists_leaf_bound (w : Nat → Nat) {a b : Term} (h : StepPlus a b) :
    ∃ B0, ∀ B, B0 ≤ B →
      maxLeafLabel (toLeafLTerm w a) ≤ B ∧ maxLeafLabel (toLeafLTerm w b) ≤ B ∧
      TransGen StepRBLeaf (flipLeafLabels B (toLeafLTerm w a)) (flipLeafLabels B (toLeafLTerm w b)) := by
  induction h with
  | @single a b hs =>
    refine ⟨Nat.max (maxLeafLabel (toLeafLTerm w a)) (maxLeafLabel (toLeafLTerm w b)), fun B hB => ?_⟩
    have ha := Nat.le_trans (Nat.le_max_left _ _) hB
    have hb := Nat.le_trans (Nat.le_max_right _ _) hB
    exact ⟨ha, hb, step_to_stepRBLeaf B w hs ha hb⟩
  | @head a m b hs _ ih =>
    obtain ⟨B1, hB1⟩ := ih
    refine ⟨Nat.max (maxLeafLabel (toLeafLTerm w a)) B1, fun B hB => ?_⟩
    have ha := Nat.le_trans (Nat.le_max_left _ _) hB
    have h1 := Nat.le_trans (Nat.le_max_right _ _) hB
    obtain ⟨hm, hb, hmb⟩ := hB1 B h1
    exact ⟨ha, hb, transGen_trans (step_to_stepRBLeaf B w hs ha hm) hmb⟩

private theorem plugCtx_to_stepRBLeaf (B : Nat) (w : Nat → Nat) (c : Ctx) (t : Term) :
    ReflTransGen StepRBLeaf
      (flipLeafLabels B (toLeafLTerm w (plugCtx c t)))
      (flipLeafLabels B (toLeafLTerm w t)) := by
  induction c with
  | hole => exact .refl _
  | left _ _ ih => exact .head (.subL _ _ _) ih
  | right _ _ ih => exact .head (.subR _ _ _) ih

private theorem subst_to_stepRBLeaf (B : Nat) (w : Nat → Nat) (σ : Nat → Term) (t : Term)
    (ht : maxLeafLabel (toLeafLTerm w t) ≤ B)
    (hw : ∀ x, hasVar x t = true → rhoW w (σ x) ≤ w x) :
    ReflTransGen StepRBLeaf
      (flipLeafLabels B (toLeafLTerm w (subst σ t)))
      (flipLeafLabels B (toLeafLTerm w t)) := by
  induction t with
  | s => exact .refl LeafLTerm.leaf
  | var k => exact leafLTerm_reduces_to_leaf (flipLeafLabels B (toLeafLTerm w (σ k)))
  | app a b iha ihb =>
    have ⟨hkb, hma, hmb⟩ := maxLeafLabel_app_le_iff.mp ht
    have hwa : ∀ x, hasVar x a = true → rhoW w (σ x) ≤ w x :=
      fun x hx => hw x (by simp only [hasVar, Bool.or_eq_true]; exact Or.inl hx)
    have hwb : ∀ x, hasVar x b = true → rhoW w (σ x) ≤ w x :=
      fun x hx => hw x (by simp only [hasVar, Bool.or_eq_true]; exact Or.inr hx)
    have hle_rho : rhoW w (subst σ b) ≤ rhoW w b := rhoW_subst_le w σ b hwb
    have h_children : ReflTransGen StepRBLeaf
        (.app (B - rhoW w b) (flipLeafLabels B (toLeafLTerm w (subst σ a))) (flipLeafLabels B (toLeafLTerm w (subst σ b))))
        (.app (B - rhoW w b) (flipLeafLabels B (toLeafLTerm w a)) (flipLeafLabels B (toLeafLTerm w b))) :=
      reflTransGen_trans
        (stepRBLeaf_left_reflTrans (iha hma hwa) _)
        (stepRBLeaf_right_reflTrans _ (ihb hmb hwb))
    exact if heq : rhoW w (subst σ b) = rhoW w b then by
      simp only [subst, toLeafLTerm, flipLeafLabels, heq]
      exact h_children
    else
      have hlt : B - rhoW w b < B - rhoW w (subst σ b) :=
        sub_lt_sub_of_lt (Nat.lt_of_le_of_ne hle_rho heq) hkb
      .head (.lift _ _ hlt) h_children

/-- **Theorem 17.1 (`conjecture17_weighted_waldmann`)**:
    If variable weights `w` satisfy `rhoW w (σ x) ≤ w x` on `Vars(M)`, then
    `¬ StepPlus M (plugCtx C (subst σ M))`. -/
theorem conjecture17_weighted_waldmann (w : Nat → Nat) (M : Term) (C : Ctx) (σ : Nat → Term)
    (hw : ∀ x, hasVar x M = true → rhoW w (σ x) ≤ w x) :
    ¬ StepPlus M (plugCtx C (subst σ M)) := by
  intro hsp
  obtain ⟨B0, hB0⟩ := stepPlus_exists_leaf_bound w hsp
  have ⟨hM_B, _, htr⟩ := hB0 B0 (Nat.le_refl B0)
  have hctx := plugCtx_to_stepRBLeaf B0 w C (subst σ M)
  have hsub := subst_to_stepRBLeaf B0 w σ M hM_B hw
  have hcyc := transGen_of_transGen_reflTransGen htr (reflTransGen_trans hctx hsub)
  exact acc_irrefl (stepRBLeaf_acc_plus (flipLeafLabels B0 (toLeafLTerm w M))) hcyc

/-- **Corollary 17.1a (All Ground-Right-Spine Substitutions)**:
    Whenever `rightLeaf (σ x) = .s` for all `x` occurring in `M`, `¬ StepPlus M (plugCtx C (subst σ M))`. -/
theorem conjecture17_ground_right_spine_subst (M : Term) (C : Ctx) (σ : Nat → Term)
    (hground : ∀ x, hasVar x M = true → rightLeaf (σ x) = .s) :
    ¬ StepPlus M (plugCtx C (subst σ M)) := by
  let w : Nat → Nat := fun x => 1 + rs (σ x)
  refine conjecture17_weighted_waldmann w M C σ (fun x hx => ?_)
  have hs : rightLeaf (σ x) = .s := hground x hx
  have heq : rhoW w (σ x) = 1 + rs (σ x) := by
    suffices ∀ t, rightLeaf t = .s → rhoW w t = 1 + rs t from this (σ x) hs
    intro t ht
    induction t with
    | s => rfl
    | var _ => cases ht
    | app _ _ _ ihb => exact congrArg (1 + ·) (ihb ht)
  rw [heq]
  exact Nat.le_refl _

/-- **Corollary 17.1b (All Zero-Right-Spine / Leaf & Variable-Renaming Substitutions)**:
    Whenever `rs (σ x) = 0` for all `x` occurring in `M`, `¬ StepPlus M (plugCtx C (subst σ M))`. -/
theorem conjecture17_nonincreasing_rs_subst (M : Term) (C : Ctx) (σ : Nat → Term)
    (hrs0 : ∀ x, hasVar x M = true → rs (σ x) = 0) :
    ¬ StepPlus M (plugCtx C (subst σ M)) := by
  let w : Nat → Nat := fun _ => 1
  refine conjecture17_weighted_waldmann w M C σ (fun x hx => ?_)
  have h0 := hrs0 x hx
  cases hsx : σ x with
  | s => exact Nat.le_refl 1
  | var _ => exact Nat.le_refl 1
  | app _ b =>
    rw [hsx] at h0
    change 1 + rs b = 0 at h0
    rw [Nat.add_comm 1 (rs b)] at h0
    exact False.elim (Nat.succ_ne_zero (rs b) h0)

/-! ## 2. Part II: Constructive Dependency-Pair Extractor & Master Self-Right-Tail Theorem -/

inductive ReducesN : Nat → Term → Term → Prop where
  | zero (a : Term) : ReducesN 0 a a
  | succ {n : Nat} {a b c : Term} : Step a b → ReducesN n b c → ReducesN (n + 1) a c

inductive NonRootReducesN : Nat → Term → Term → Prop where
  | zero (a : Term) : NonRootReducesN 0 a a
  | succ {n : Nat} {a b c : Term} : NonRootStep a b → NonRootReducesN n b c → NonRootReducesN (n + 1) a c

theorem reducesN_to_reduces {n : Nat} {a b : Term} (h : ReducesN n a b) : Reduces a b := by
  induction h with
  | zero _ => exact .refl _
  | succ hs _ ih => exact .next hs ih

theorem nonRootReducesN_to_nonRootReduces {n : Nat} {a b : Term} (h : NonRootReducesN n a b) :
    NonRootReduces a b := by
  induction h with
  | zero _ => exact .refl _
  | succ hs _ ih => exact .next hs ih

theorem stepPlus_to_reducesN {a b : Term} (h : StepPlus a b) :
    ∃ n, 1 ≤ n ∧ ReducesN n a b := by
  induction h with
  | single hs => exact ⟨1, Nat.le_refl 1, .succ hs (.zero _)⟩
  | head hs _ ih =>
    obtain ⟨n, _, hn⟩ := ih
    exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), .succ hs hn⟩

theorem reducesN_trans {m n : Nat} {a b c : Term}
    (h1 : ReducesN m a b) (h2 : ReducesN n b c) : ReducesN (m + n) a c := by
  induction h1 with
  | zero _ => rw [Nat.zero_add]; exact h2
  | @succ _ _ _ _ hs _ ih =>
    rw [Nat.succ_add]
    exact .succ hs (ih h2)

theorem plugCtx_reducesN (c : Ctx) {n : Nat} {a b : Term} (h : ReducesN n a b) :
    ReducesN n (plugCtx c a) (plugCtx c b) := by
  induction h with
  | zero _ => exact .zero _
  | succ hs _ ih => exact .succ (plugCtx_step c hs) ih

theorem reducesN_split_first_root {n : Nat} {a b : Term} (h : ReducesN n a b) :
    NonRootReducesN n a b ∨
      ∃ k m x y z, k + 1 + m = n ∧
        NonRootReducesN k a (S ⋅ x ⋅ y ⋅ z) ∧
        ReducesN m ((x ⋅ z) ⋅ (y ⋅ z)) b := by
  induction h with
  | zero x => exact Or.inl (.zero x)
  | @succ n0 _ _ _ hs hrest ih =>
    rcases step_iff_root_or_nonRoot.mp hs with ⟨x, y, z⟩ | hnr
    · exact Or.inr ⟨0, n0, x, y, z, by rw [Nat.zero_add, Nat.add_comm 1 n0], .zero _, hrest⟩
    · rcases ih with hnr_rest | ⟨k, m, x, y, z, heq, hnr_k, hm⟩
      · exact Or.inl (.succ hnr hnr_rest)
      · have hidx : (k + 1) + 1 + m = n0 + 1 := by
          rw [← heq, Nat.add_right_comm (k + 1) 1 m]
        exact Or.inr ⟨k + 1, m, x, y, z, hidx, .succ hnr hnr_k, hm⟩

theorem nonRootReducesN_app_inv {k : Nat} {m n : Term} (h : NonRootReducesN k m n) :
    ∀ a b, m = a ⋅ b →
      ∃ kL kR a' b', kL + kR = k ∧ n = a' ⋅ b' ∧ ReducesN kL a a' ∧ ReducesN kR b b' := by
  induction h with
  | zero _ =>
    intro a b hm
    exact ⟨0, 0, a, b, rfl, hm, .zero a, .zero b⟩
  | @succ _ _ _ _ hs _ ih =>
    intro a b hm
    subst hm
    cases hs with
    | @left _ a1 _ ha1 =>
      obtain ⟨kL, kR, a', b', hk, hn, hra, hrb⟩ := ih a1 b rfl
      refine ⟨kL + 1, kR, a', b', ?_, hn, .succ ha1 hra, hrb⟩
      rw [← hk, Nat.add_right_comm kL 1 kR]
    | @right _ _ b1 hb1 =>
      obtain ⟨kL, kR, a', b', hk, hn, hra, hrb⟩ := ih a b1 rfl
      refine ⟨kL, kR + 1, a', b', ?_, hn, hra, .succ hb1 hrb⟩
      rw [← hk, Nat.add_assoc kL kR 1]

private theorem nonRootReducesN_leaf_not_app {k : Nat} {a b : Term} (h : NonRootReducesN k a b)
    (hleaf : a = .s ∨ ∃ j, a = .var j) (u v : Term) (hb : b = u ⋅ v) : False := by
  cases h with
  | zero _ =>
    rcases hleaf with rfl | ⟨j, rfl⟩ <;> cases hb
  | succ hs _ =>
    rcases hleaf with rfl | ⟨j, rfl⟩ <;> cases hs

theorem nonRootReduces_app_inv {m n : Term} (h : NonRootReduces m n) :
    ∀ a b, m = a ⋅ b → ∃ a' b', n = a' ⋅ b' ∧ Reduces a a' ∧ Reduces b b' := by
  induction h with
  | refl _ =>
    intro a b hm
    exact ⟨a, b, hm, .refl a, .refl b⟩
  | @next _ _ _ hs _ ih =>
    intro a b hm
    subst hm
    cases hs with
    | @left _ a1 _ ha1 =>
      obtain ⟨a', b', hn, hra, hrb⟩ := ih a1 b rfl
      exact ⟨a', b', hn, .next ha1 hra, hrb⟩
    | @right _ _ b1 hb1 =>
      obtain ⟨a', b', hn, hra, hrb⟩ := ih a b1 rfl
      exact ⟨a', b', hn, hra, .next hb1 hrb⟩

def Subterm (u t : Term) : Prop := ∃ d : Ctx, t = plugCtx d u
def StrictSubterm (u t : Term) : Prop := ∃ d : Ctx, d ≠ .hole ∧ t = plugCtx d u

theorem strictSubterm_leaves_lt {u t : Term} (h : StrictSubterm u t) : leaves u < leaves t := by
  obtain ⟨d, hd, heq⟩ := h
  rw [heq]
  exact plugCtx_leaves_gt hd u

theorem strictSubterm_left (a b : Term) : StrictSubterm a (a ⋅ b) :=
  ⟨.left .hole b, (fun h => by cases h), rfl⟩

theorem strictSubterm_right (a b : Term) : StrictSubterm b (a ⋅ b) :=
  ⟨.right a .hole, (fun h => by cases h), rfl⟩

private theorem subterm_app_cases {u a b : Term} (h : Subterm u (a ⋅ b)) :
    u = a ⋅ b ∨ Subterm u a ∨ Subterm u b := by
  obtain ⟨d, heq⟩ := h
  cases d with
  | hole => exact Or.inl heq.symm
  | left d' _ =>
    injection heq with ha _
    exact Or.inr (Or.inl ⟨d', ha⟩)
  | right _ d' =>
    injection heq with _ hb
    exact Or.inr (Or.inr ⟨d', hb⟩)

private theorem strictSubterm_app_cases {u a b : Term} (h : StrictSubterm u (a ⋅ b)) :
    Subterm u a ∨ Subterm u b := by
  obtain ⟨d, hd, heq⟩ := h
  cases d with
  | hole => exfalso; exact hd rfl
  | left d' _ =>
    injection heq with ha _
    exact Or.inl ⟨d', ha⟩
  | right _ d' =>
    injection heq with _ hb
    exact Or.inr ⟨d', hb⟩

private theorem strictSubterm_rhs_cases {u x y z : Term}
    (h : StrictSubterm u ((x ⋅ z) ⋅ (y ⋅ z))) :
    u = x ⋅ z ∨ u = y ⋅ z ∨ Subterm u x ∨ Subterm u y ∨ Subterm u z := by
  rcases strictSubterm_app_cases h with hl | hr
  · rcases subterm_app_cases hl with heq | hx | hz
    · exact Or.inl heq
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hz)))
  · rcases subterm_app_cases hr with heq | hy | hz
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hy)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hz)))

inductive DPChain : Term → Term → Prop where
  | done {a b : Term} : NonRootReduces a b → DPChain a b
  | dp1 {a x y z v : Term} : NonRootReduces a (S ⋅ x ⋅ y ⋅ z) → DPChain ((x ⋅ z) ⋅ (y ⋅ z)) v → DPChain a v
  | dp2 {a x y z v : Term} : NonRootReduces a (S ⋅ x ⋅ y ⋅ z) → DPChain (x ⋅ z) v → DPChain a v
  | dp3 {a x y z v : Term} : NonRootReduces a (S ⋅ x ⋅ y ⋅ z) → DPChain (y ⋅ z) v → DPChain a v

inductive DPChain23 : Term → Term → Prop where
  | done {a b : Term} : NonRootReduces a b → DPChain23 a b
  | dp2 {a x y z v : Term} : NonRootReduces a (S ⋅ x ⋅ y ⋅ z) → DPChain23 (x ⋅ z) v → DPChain23 a v
  | dp3 {a x y z v : Term} : NonRootReduces a (S ⋅ x ⋅ y ⋅ z) → DPChain23 (y ⋅ z) v → DPChain23 a v

private theorem lift_subterm_in_x {kL kR m m' : Nat} {tL tR x y u v : Term} {c' : Ctx}
    (hL : ReducesN kL tL (S ⋅ x ⋅ y)) (hsub : Subterm u x)
    (hu : ReducesN m' u (plugCtx c' v)) (hm' : m' ≤ m) :
    ∃ n' u0 c0, n' ≤ (kL + kR) + m ∧ StrictSubterm u0 (tL ⋅ tR) ∧ ReducesN n' u0 (plugCtx c0 v) := by
  obtain ⟨dx, hxeq⟩ := hsub
  subst hxeq
  let outer : Ctx := .left (.right S dx) y
  have hsxy : ReducesN m' (S ⋅ plugCtx dx u ⋅ y) (plugCtx (compCtx outer c') v) := by
    rw [plugCtx_comp]
    exact plugCtx_reducesN outer hu
  have htL : ReducesN (kL + m') tL (plugCtx (compCtx outer c') v) :=
    reducesN_trans hL hsxy
  have hbound : kL + m' ≤ (kL + kR) + m :=
    Nat.add_le_add (Nat.le_add_right kL kR) hm'
  exact ⟨kL + m', tL, compCtx outer c', hbound, strictSubterm_left tL tR, htL⟩

private theorem lift_subterm_in_y {kL kR m m' : Nat} {tL tR x y u v : Term} {c' : Ctx}
    (hL : ReducesN kL tL (S ⋅ x ⋅ y)) (hsub : Subterm u y)
    (hu : ReducesN m' u (plugCtx c' v)) (hm' : m' ≤ m) :
    ∃ n' u0 c0, n' ≤ (kL + kR) + m ∧ StrictSubterm u0 (tL ⋅ tR) ∧ ReducesN n' u0 (plugCtx c0 v) := by
  obtain ⟨dy, hyeq⟩ := hsub
  subst hyeq
  let outer : Ctx := .right (S ⋅ x) dy
  have hsxy : ReducesN m' (S ⋅ x ⋅ plugCtx dy u) (plugCtx (compCtx outer c') v) := by
    rw [plugCtx_comp]
    exact plugCtx_reducesN outer hu
  have htL : ReducesN (kL + m') tL (plugCtx (compCtx outer c') v) :=
    reducesN_trans hL hsxy
  have hbound : kL + m' ≤ (kL + kR) + m :=
    Nat.add_le_add (Nat.le_add_right kL kR) hm'
  exact ⟨kL + m', tL, compCtx outer c', hbound, strictSubterm_left tL tR, htL⟩

private theorem lift_subterm_in_z {kL kR m m' : Nat} {tL tR z u v : Term} {c' : Ctx}
    (hR : ReducesN kR tR z) (hsub : Subterm u z)
    (hu : ReducesN m' u (plugCtx c' v)) (hm' : m' ≤ m) :
    ∃ n' u0 c0, n' ≤ (kL + kR) + m ∧ StrictSubterm u0 (tL ⋅ tR) ∧ ReducesN n' u0 (plugCtx c0 v) := by
  obtain ⟨dz, hzeq⟩ := hsub
  subst hzeq
  have hz : ReducesN m' (plugCtx dz u) (plugCtx (compCtx dz c') v) := by
    rw [plugCtx_comp]
    exact plugCtx_reducesN dz hu
  have htR : ReducesN (kR + m') tR (plugCtx (compCtx dz c') v) :=
    reducesN_trans hR hz
  have hbound : kR + m' ≤ (kL + kR) + m :=
    Nat.add_le_add (Nat.le_add_left kR kL) hm'
  exact ⟨kR + m', tR, compCtx dz c', hbound, strictSubterm_right tL tR, htR⟩

private theorem extract_dp_or_subterm (v : Term) :
    ∀ (B : Nat) {n : Nat}, n ≤ B →
      ∀ (t : Term) (c : Ctx), ReducesN n t (plugCtx c v) →
        (∃ n' u c', n' ≤ n ∧ StrictSubterm u t ∧ ReducesN n' u (plugCtx c' v)) ∨ DPChain t v := by
  intro B
  induction B with
  | zero =>
    intro n hn t c hred
    cases Nat.eq_zero_of_le_zero hn
    cases hred with
    | zero _ =>
      cases c with
      | hole => exact Or.inr (.done (.refl _))
      | left c1 r =>
        exact Or.inl ⟨0, plugCtx c1 v, c1, Nat.le_refl 0,
          strictSubterm_left (plugCtx c1 v) r, .zero _⟩
      | right l c2 =>
        exact Or.inl ⟨0, plugCtx c2 v, c2, Nat.le_refl 0,
          strictSubterm_right l (plugCtx c2 v), .zero _⟩
  | succ B ihB =>
    intro n hn t c hred
    exact if hnB : n ≤ B then
      ihB hnB t c hred
    else by
      rcases reducesN_split_first_root hred with hnr | ⟨k, m, x, y, z, hkm, hnr_k, hm_rest⟩
      · cases c with
        | hole => exact Or.inr (.done (nonRootReducesN_to_nonRootReduces hnr))
        | left c1 r =>
          cases t with
          | s => exfalso; exact nonRootReducesN_leaf_not_app hnr (Or.inl rfl) _ _ rfl
          | var j => exfalso; exact nonRootReducesN_leaf_not_app hnr (Or.inr ⟨j, rfl⟩) _ _ rfl
          | app tL tR =>
            obtain ⟨kL, kR, a', b', hk, heq, hrL, _⟩ := nonRootReducesN_app_inv hnr tL tR rfl
            injection heq with ha' _
            subst ha'
            have hkL_le : kL ≤ n := by rw [← hk]; exact Nat.le_add_right kL kR
            exact Or.inl ⟨kL, tL, c1, hkL_le, strictSubterm_left tL tR, hrL⟩
        | right l c2 =>
          cases t with
          | s => exfalso; exact nonRootReducesN_leaf_not_app hnr (Or.inl rfl) _ _ rfl
          | var j => exfalso; exact nonRootReducesN_leaf_not_app hnr (Or.inr ⟨j, rfl⟩) _ _ rfl
          | app tL tR =>
            obtain ⟨kL, kR, a', b', hk, heq, _, hrR⟩ := nonRootReducesN_app_inv hnr tL tR rfl
            injection heq with _ hb'
            subst hb'
            have hkR_le : kR ≤ n := by rw [← hk]; exact Nat.le_add_left kR kL
            exact Or.inl ⟨kR, tR, c2, hkR_le, strictSubterm_right tL tR, hrR⟩
      · have hkm_le_B : k + m ≤ B := by
          have hlt : k + m < n := by
            rw [← hkm, Nat.add_assoc k 1 m, Nat.add_comm 1 m, ← Nat.add_assoc k m 1]
            exact Nat.lt_succ_self (k + m)
          exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hn)
        have hm_le_B : m ≤ B := Nat.le_trans (Nat.le_add_left m k) hkm_le_B
        cases t with
        | s => exfalso; exact nonRootReducesN_leaf_not_app hnr_k (Or.inl rfl) _ _ rfl
        | var j => exfalso; exact nonRootReducesN_leaf_not_app hnr_k (Or.inr ⟨j, rfl⟩) _ _ rfl
        | app tL tR =>
          obtain ⟨kL, kR, a', b', hk_eq, heq, hrL, hrR⟩ := nonRootReducesN_app_inv hnr_k tL tR rfl
          injection heq with ha' hb'
          subst ha'; subst hb'
          have hnr_plain : NonRootReduces (tL ⋅ tR) (S ⋅ x ⋅ y ⋅ z) :=
            nonRootReducesN_to_nonRootReduces hnr_k
          have hbound_lift : (kL + kR) + m ≤ n := by
            rw [hk_eq, ← hkm, Nat.add_assoc k 1 m, Nat.add_comm 1 m, ← Nat.add_assoc k m 1]
            exact Nat.le_succ (k + m)
          rcases ihB hm_le_B ((x ⋅ z) ⋅ (y ⋅ z)) c hm_rest with
              ⟨m1, u1, c1, hm1_le, hsub1, hu1⟩ | hdp1
          · rcases strictSubterm_rhs_cases hsub1 with h_xz | h_yz | h_x | h_y | h_z
            · subst h_xz
              rcases ihB (Nat.le_trans hm1_le hm_le_B) (x ⋅ z) c1 hu1 with
                  ⟨m2, u2, c2, hm2_le, hsub2, hu2⟩ | hdp2
              · rcases strictSubterm_app_cases hsub2 with h_in_x | h_in_z
                · obtain ⟨n', u0, c0, hn', hst0, hr0⟩ :=
                    lift_subterm_in_x hrL h_in_x hu2 (Nat.le_trans hm2_le hm1_le)
                  exact Or.inl ⟨n', u0, c0, Nat.le_trans hn' hbound_lift, hst0, hr0⟩
                · obtain ⟨n', u0, c0, hn', hst0, hr0⟩ :=
                    lift_subterm_in_z hrR h_in_z hu2 (Nat.le_trans hm2_le hm1_le)
                  exact Or.inl ⟨n', u0, c0, Nat.le_trans hn' hbound_lift, hst0, hr0⟩
              · exact Or.inr (.dp2 hnr_plain hdp2)
            · subst h_yz
              rcases ihB (Nat.le_trans hm1_le hm_le_B) (y ⋅ z) c1 hu1 with
                  ⟨m2, u2, c2, hm2_le, hsub2, hu2⟩ | hdp3
              · rcases strictSubterm_app_cases hsub2 with h_in_y | h_in_z
                · obtain ⟨n', u0, c0, hn', hst0, hr0⟩ :=
                    lift_subterm_in_y hrL h_in_y hu2 (Nat.le_trans hm2_le hm1_le)
                  exact Or.inl ⟨n', u0, c0, Nat.le_trans hn' hbound_lift, hst0, hr0⟩
                · obtain ⟨n', u0, c0, hn', hst0, hr0⟩ :=
                    lift_subterm_in_z hrR h_in_z hu2 (Nat.le_trans hm2_le hm1_le)
                  exact Or.inl ⟨n', u0, c0, Nat.le_trans hn' hbound_lift, hst0, hr0⟩
              · exact Or.inr (.dp3 hnr_plain hdp3)
            · obtain ⟨n', u0, c0, hn', hst0, hr0⟩ := lift_subterm_in_x hrL h_x hu1 hm1_le
              exact Or.inl ⟨n', u0, c0, Nat.le_trans hn' hbound_lift, hst0, hr0⟩
            · obtain ⟨n', u0, c0, hn', hst0, hr0⟩ := lift_subterm_in_y hrL h_y hu1 hm1_le
              exact Or.inl ⟨n', u0, c0, Nat.le_trans hn' hbound_lift, hst0, hr0⟩
            · obtain ⟨n', u0, c0, hn', hst0, hr0⟩ := lift_subterm_in_z hrR h_z hu1 hm1_le
              exact Or.inl ⟨n', u0, c0, Nat.le_trans hn' hbound_lift, hst0, hr0⟩
          · exact Or.inr (.dp1 hnr_plain hdp1)

theorem dpChain_rightLeaf_and_rs {a b : Term} (h : DPChain a b) :
    rightLeaf a = rightLeaf b ∧ rs a ≤ rs b := by
  induction h with
  | done hnr =>
    have hr := nonRootReduces_to_reduces hnr
    exact ⟨rightLeaf_reduces hr, rs_mono_reduces hr⟩
  | @dp1 a x y z v hnr _ ih =>
    have hr := nonRootReduces_to_reduces hnr
    have hrl1 : rightLeaf a = rightLeaf (S ⋅ x ⋅ y ⋅ z) := rightLeaf_reduces hr
    have hrs1 : rs a ≤ 1 + rs z := rs_mono_reduces hr
    have hrs_step : 1 + rs z ≤ 1 + (1 + rs z) :=
      Nat.add_le_add_left (Nat.le_add_left (rs z) 1) 1
    exact ⟨hrl1.trans ih.1, Nat.le_trans hrs1 (Nat.le_trans hrs_step ih.2)⟩
  | @dp2 a x y z v hnr _ ih =>
    have hr := nonRootReduces_to_reduces hnr
    exact ⟨(rightLeaf_reduces hr).trans ih.1, Nat.le_trans (rs_mono_reduces hr) ih.2⟩
  | @dp3 a x y z v hnr _ ih =>
    have hr := nonRootReduces_to_reduces hnr
    exact ⟨(rightLeaf_reduces hr).trans ih.1, Nat.le_trans (rs_mono_reduces hr) ih.2⟩

theorem dpChain_split_dp23_or_rs_lt {a b : Term} (h : DPChain a b) :
    DPChain23 a b ∨ rs a < rs b := by
  induction h with
  | done hnr => exact Or.inl (.done hnr)
  | @dp1 a x y z v hnr hrest _ =>
    have hrs1 : rs a ≤ 1 + rs z := rs_mono_reduces (nonRootReduces_to_reduces hnr)
    have hlt_mid : 1 + rs z < 1 + (1 + rs z) := by
      rw [Nat.add_comm 1 (1 + rs z)]
      exact Nat.lt_succ_self (1 + rs z)
    have hrs2 : 1 + (1 + rs z) ≤ rs v := (dpChain_rightLeaf_and_rs hrest).2
    exact Or.inr (Nat.lt_of_le_of_lt hrs1 (Nat.lt_of_lt_of_le hlt_mid hrs2))
  | @dp2 a x y z v hnr _ ih =>
    rcases ih with h23 | hlt
    · exact Or.inl (.dp2 hnr h23)
    · have hrs1 : rs a ≤ 1 + rs z := rs_mono_reduces (nonRootReduces_to_reduces hnr)
      exact Or.inr (Nat.lt_of_le_of_lt hrs1 hlt)
  | @dp3 a x y z v hnr _ ih =>
    rcases ih with h23 | hlt
    · exact Or.inl (.dp3 hnr h23)
    · have hrs1 : rs a ≤ 1 + rs z := rs_mono_reduces (nonRootReduces_to_reduces hnr)
      exact Or.inr (Nat.lt_of_le_of_lt hrs1 hlt)

private theorem dpChain23_app_inv {u v : Term} (h : DPChain23 u v) :
    ∀ a0 b0 a' b', u = a0 ⋅ b0 → v = a' ⋅ b' →
      (Reduces a0 a' ∧ Reduces b0 b') ∨
        ∃ d : Ctx, d ≠ .hole ∧ Reduces a0 (plugCtx d a') := by
  induction h with
  | done hnr =>
    intro a0 b0 a' b' hu hv
    subst hu; subst hv
    obtain ⟨l', r', heq, hrL, hrR⟩ := nonRootReduces_app_inv hnr a0 b0 rfl
    injection heq with hl hr
    subst hl; subst hr
    exact Or.inl ⟨hrL, hrR⟩
  | @dp2 _ x y z _ hnr _ ih =>
    intro a0 b0 a' b' hu hv
    subst hu
    obtain ⟨l', r', heq, hrL, _⟩ := nonRootReduces_app_inv hnr a0 b0 rfl
    injection heq with hl _
    subst hl
    rcases ih x z a' b' rfl hv with ⟨hx, _⟩ | ⟨d1, _, hx⟩
    · refine Or.inr ⟨.left (.right S .hole) y, (fun hc => by cases hc), ?_⟩
      exact reduces_trans hrL (plugCtx_reduces (.left (.right S .hole) y) hx)
    · refine Or.inr ⟨.left (.right S d1) y, (fun hc => by cases hc), ?_⟩
      have hsxy : Reduces (S ⋅ x ⋅ y) (plugCtx (.left (.right S d1) y) a') :=
        plugCtx_reduces (.left (.right S .hole) y) hx
      exact reduces_trans hrL hsxy
  | @dp3 _ x y z _ hnr _ ih =>
    intro a0 b0 a' b' hu hv
    subst hu
    obtain ⟨l', r', heq, hrL, _⟩ := nonRootReduces_app_inv hnr a0 b0 rfl
    injection heq with hl _
    subst hl
    rcases ih y z a' b' rfl hv with ⟨hy, _⟩ | ⟨d1, _, hy⟩
    · refine Or.inr ⟨.right (S ⋅ x) .hole, (fun hc => by cases hc), ?_⟩
      exact reduces_trans hrL (plugCtx_reduces (.right (S ⋅ x) .hole) hy)
    · refine Or.inr ⟨.right (S ⋅ x) d1, (fun hc => by cases hc), ?_⟩
      have hsxy : Reduces (S ⋅ x ⋅ y) (plugCtx (.right (S ⋅ x) d1) a') :=
        plugCtx_reduces (.right (S ⋅ x) .hole) hy
      exact reduces_trans hrL hsxy

/-- **Core Constructive Descent Lemma for Open Spirals**:
    For ANY open spiral `StepPlus M (plugCtx C (subst σ M))`, EITHER a proper subterm `u` of `M`
    already open-spirals under the SAME `σ`, OR `M` itself satisfies `DPChain M (subst σ M)`,
    `rs M < rs (subst σ M)`, and `rightLeaf M = .var xR` with `rightLeaf (σ xR) = .var xR ∧ 1 ≤ rs (σ xR)`. -/
theorem open_spiral_subterm_or_self_right_tail {M : Term} {C : Ctx} {σ : Nat → Term}
    (hsp : StepPlus M (plugCtx C (subst σ M))) :
    (∃ u C', StrictSubterm u M ∧ StepPlus u (plugCtx C' (subst σ u))) ∨
      (DPChain M (subst σ M) ∧ rs M < rs (subst σ M) ∧
        ∃ xR, hasVar xR M = true ∧ rightLeaf M = .var xR ∧
          rightLeaf (σ xR) = .var xR ∧ 1 ≤ rs (σ xR)) := by
  obtain ⟨n, _, hn⟩ := stepPlus_to_reducesN hsp
  rcases extract_dp_or_subterm (subst σ M) n (Nat.le_refl n) M C hn with
      ⟨_, u, c', _, hstrict, hu_redN⟩ | hdp
  · obtain ⟨d, hd, hMeq⟩ := hstrict
    have hu_red : Reduces u (plugCtx c' (subst σ M)) := reducesN_to_reduces hu_redN
    have htarget_eq : plugCtx c' (subst σ M) = plugCtx (compCtx c' (substCtx σ d)) (subst σ u) := by
      rw [hMeq, subst_plugCtx, plugCtx_comp]
    rw [htarget_eq] at hu_red
    have hlt_leaves : leaves u < leaves (plugCtx (compCtx c' (substCtx σ d)) (subst σ u)) := by
      have h1 : leaves u < leaves M := strictSubterm_leaves_lt ⟨d, hd, hMeq⟩
      have h2 : leaves M ≤ leaves (subst σ M) := leaves_subst_ge σ M
      have h3 : leaves (subst σ M) ≤ leaves (plugCtx c' (subst σ M)) := leaves_plugCtx_ge c' (subst σ M)
      rw [← htarget_eq]
      exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3)
    rcases reduces_eq_or_stepPlus hu_red with heq | hu_sp
    · exfalso; rw [← heq] at hlt_leaves; exact Nat.lt_irrefl _ hlt_leaves
    · exact Or.inl ⟨u, compCtx c' (substCtx σ d), ⟨d, hd, hMeq⟩, hu_sp⟩
  · rcases dpChain_split_dp23_or_rs_lt hdp with h23 | hrs_lt
    · cases M with
      | s => exfalso; exact waldmann_no_spiral C .s hsp
      | var _ =>
        exfalso
        cases hsp with
        | single hs => cases hs
        | head hs _ => cases hs
      | app a0 b0 =>
        rcases dpChain23_app_inv h23 a0 b0 (subst σ a0) (subst σ b0) rfl rfl with
            ⟨hra, hrb⟩ | ⟨d, hd, hra_ctx⟩
        · rcases reduces_eq_or_stepPlus hra with ha_eq | ha_sp
          · rcases reduces_eq_or_stepPlus hrb with hb_eq | hb_sp
            · exfalso
              have hMeq : subst σ (a0 ⋅ b0) = a0 ⋅ b0 := by
                simp only [subst, ← ha_eq, ← hb_eq]
              rw [hMeq] at hsp
              exact waldmann_no_spiral C (a0 ⋅ b0) hsp
            · exact Or.inl ⟨b0, .hole, strictSubterm_right a0 b0, hb_sp⟩
          · exact Or.inl ⟨a0, .hole, strictSubterm_left a0 b0, ha_sp⟩
        · have hlt_a0 : leaves a0 < leaves (plugCtx d (subst σ a0)) :=
            Nat.lt_of_le_of_lt (leaves_subst_ge σ a0) (plugCtx_leaves_gt hd (subst σ a0))
          rcases reduces_eq_or_stepPlus hra_ctx with ha_eq | ha_sp
          · exfalso; rw [← ha_eq] at hlt_a0; exact Nat.lt_irrefl _ hlt_a0
          · exact Or.inl ⟨a0, d, strictSubterm_left a0 b0, ha_sp⟩
    · have hrl_eq : rightLeaf M = rightLeaf (subst σ M) := (dpChain_rightLeaf_and_rs hdp).1
      rcases rightLeaf_leaves_one M with hs | ⟨xR, hxR⟩
      · exfalso
        have hrs_eq : rs (subst σ M) = rs M := (rightLeaf_subst_of_s σ hs).2
        rw [hrs_eq] at hrs_lt
        exact Nat.lt_irrefl _ hrs_lt
      · obtain ⟨hrl_sub, hrs_sub⟩ := rightLeaf_subst_of_var σ hxR
        have hrl_sigma : rightLeaf (σ xR) = .var xR := by
          rw [← hrl_sub, ← hrl_eq, hxR]
        have hrs_pos : 1 ≤ rs (σ xR) := by
          rw [hrs_sub] at hrs_lt
          exact if h0 : rs (σ xR) = 0 then by
            rw [h0, Nat.add_zero] at hrs_lt
            exfalso; exact Nat.lt_irrefl _ hrs_lt
          else
            Nat.pos_of_ne_zero h0
        exact Or.inr ⟨hdp, hrs_lt, xR, hasVar_rightLeaf hxR, hxR, hrl_sigma, hrs_pos⟩

private theorem no_open_spiral_by_leaves (σ : Nat → Term) :
    ∀ (L : Nat) (M : Term), leaves M ≤ L →
      (∀ x, hasVar x M = true → ¬ (rightLeaf (σ x) = .var x ∧ 1 ≤ rs (σ x))) →
      ∀ (C : Ctx), ¬ StepPlus M (plugCtx C (subst σ M)) := by
  intro L
  induction L with
  | zero =>
    intro M hL _ _ _
    exfalso
    exact Nat.not_succ_le_zero 0 (Nat.le_trans (leaves_pos M) hL)
  | succ L ihL =>
    intro M hL hno C hsp
    exact if hle : leaves M ≤ L then
      ihL M hle hno C hsp
    else by
      rcases open_spiral_subterm_or_self_right_tail hsp with
          ⟨u, c', hstrict, hu_sp⟩ | ⟨_, _, xR, hvar, _, hrl_sig, hrs_sig⟩
      · have hu_lt : leaves u < leaves M := strictSubterm_leaves_lt hstrict
        have hu_le : leaves u ≤ L := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hu_lt hL)
        obtain ⟨d, _, hMeq⟩ := hstrict
        have hno_u : ∀ x, hasVar x u = true → ¬ (rightLeaf (σ x) = .var x ∧ 1 ≤ rs (σ x)) :=
          fun x hxu => hno x (by rw [hMeq]; exact hasVar_plugCtx d hxu)
        exact ihL u hu_le hno_u c' hu_sp
      · exact hno xR hvar ⟨hrl_sig, hrs_sig⟩

/-- **MASTER THEOREM 17.2 (`conjecture17_no_open_spiral_unless_self_right_tail`)**:
    For EVERY pure-`S` term `M`, context `C`, and substitution `σ`:
    If no variable `x` occurring in `M` is a positive right-spine self-loop of `σ`
    (`rightLeaf (σ x) = .var x ∧ 1 ≤ rs (σ x)`), then `¬ StepPlus M (plugCtx C (subst σ M))`! -/
theorem conjecture17_no_open_spiral_unless_self_right_tail
    (M : Term) (C : Ctx) (σ : Nat → Term)
    (hno : ∀ x, hasVar x M = true → ¬ (rightLeaf (σ x) = .var x ∧ 1 ≤ rs (σ x))) :
    ¬ StepPlus M (plugCtx C (subst σ M)) :=
  no_open_spiral_by_leaves σ (leaves M) M (Nat.le_refl _) hno C

/-- **Corollary 17.2a (All Distinct-Right-Leaf Substitutions, Including Period `p ≥ 2` Cycles)**:
    If `rightLeaf (σ x) ≠ .var x` for all `x` occurring in `M`, then `¬ StepPlus M (plugCtx C (subst σ M))`. -/
theorem conjecture17_distinct_rightLeaf_subst
    (M : Term) (C : Ctx) (σ : Nat → Term)
    (hdist : ∀ x, hasVar x M = true → rightLeaf (σ x) ≠ .var x) :
    ¬ StepPlus M (plugCtx C (subst σ M)) :=
  conjecture17_no_open_spiral_unless_self_right_tail M C σ
    (fun x hx ⟨hrl, _⟩ => hdist x hx hrl)

/-- **Corollary 17.2b (Single-Variable Open Terms)**:
    If `M` contains at most one variable `v`, then `¬ StepPlus M (plugCtx C (subst σ M))` for ALL
    `(C, σ)` except when `rightLeaf (σ v) = .var v ∧ 1 ≤ rs (σ v)`. -/
theorem conjecture17_single_var
    (v : Nat) (M : Term) (C : Ctx) (σ : Nat → Term)
    (honly : ∀ x, hasVar x M = true → x = v)
    (hnot_self : ¬ (rightLeaf (σ v) = .var v ∧ 1 ≤ rs (σ v))) :
    ¬ StepPlus M (plugCtx C (subst σ M)) :=
  conjecture17_no_open_spiral_unless_self_right_tail M C σ
    (fun x hx hself => by rw [honly x hx] at hself; exact hnot_self hself)

end FormalNoSpiral
