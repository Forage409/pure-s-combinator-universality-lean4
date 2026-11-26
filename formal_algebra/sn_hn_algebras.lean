import formal_algebra.s_structural_laws

/-!
# Exact Finite S-Algebras (`A_SN`, `A_HN`, and 112-State Joint Algebra), Constructive Resolution of Open Problem 10 & Waldmann's Theorem 9, Footnote 4, 5-Composite RNF Ceiling, 3rd-Argument Head Exclusion, and Selector-Free `stepLO` Quadratic Counter

Machine-checked in Lean 4.33.1 with zero `sorry`, zero custom axioms, and zero `Classical.choice`.
-/

namespace FormalAlgebra

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true a b).mp h).1

theorem and_right {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true a b).mp h).2

theorem imp_decide {p : Prop} [Decidable p] {b : Bool} (hp : p) (h : (!decide p || b) = true) : b = true := by
  rw [decide_eq_true hp] at h
  exact h

theorem imp_bool {a b : Bool} (ha : a = true) (h : (!a || b) = true) : b = true := by
  rw [ha] at h
  exact h

private abbrev natBle (a b : Nat) : Bool := decide (a ≤ b)

private theorem natBle_sound {a b : Nat} (h : natBle a b = true) : a ≤ b :=
  of_decide_eq_true h

/-! ## 1. Deterministic Reducers (`rootRedexOpt`, `headStepOpt`, `stepLO`) and Constructive `SN ↔ WN` -/

def rootRedexOpt (a b : Term) : Option Term :=
  match a with
  | .app (.app .s x) y => some ((x ⋅ b) ⋅ (y ⋅ b))
  | _ => none

theorem rootRedexOpt_some {a b r : Term} (h : rootRedexOpt a b = some r) :
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
      | s =>
        injection h with hr
        exact ⟨x, y, rfl, hr.symm⟩
      | var _ => cases h
      | app _ _ => cases h

theorem rootRedexOpt_none {a b : Term} (h : rootRedexOpt a b = none) :
    ∀ x y, a ≠ S ⋅ x ⋅ y := by
  intro x y heq
  subst heq
  cases h

def headStepOpt : Term → Option Term
  | .s => none
  | .var _ => none
  | .app a b =>
    match rootRedexOpt a b with
    | some r => some r
    | none =>
      match headStepOpt a with
      | some a' => some (a' ⋅ b)
      | none => none

theorem headStepOpt_some {t t' : Term} (h : headStepOpt t = some t') : HeadStep t t' := by
  induction t generalizing t' with
  | s => cases h
  | var _ => cases h
  | app a b iha _ =>
    simp only [headStepOpt] at h
    cases hr : rootRedexOpt a b with
    | some r =>
      rw [hr] at h
      injection h with heq
      subst heq
      obtain ⟨x, y, ha, hreq⟩ := rootRedexOpt_some hr
      subst ha; subst hreq
      exact HeadStep.root x y b
    | none =>
      rw [hr] at h
      cases ha : headStepOpt a with
      | some a' =>
        rw [ha] at h
        injection h with heq
        subst heq
        exact HeadStep.left (iha ha)
      | none =>
        rw [ha] at h
        cases h

theorem headStepOpt_none_closed {t : Term} (hv : noVars t = true) (h : headStepOpt t = none) :
    t = S ∨ (∃ x, t = S ⋅ x) ∨ (∃ x y, t = S ⋅ x ⋅ y) := by
  induction t with
  | s => exact Or.inl rfl
  | var _ => cases hv
  | app a b iha _ =>
    simp only [noVars, Bool.and_eq_true] at hv
    simp only [headStepOpt] at h
    cases hr : rootRedexOpt a b with
    | some r => rw [hr] at h; cases h
    | none =>
      rw [hr] at h
      cases ha : headStepOpt a with
      | some a' => rw [ha] at h; cases h
      | none =>
        rcases iha hv.1 ha with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
        · exact Or.inr (Or.inl ⟨b, rfl⟩)
        · exact Or.inr (Or.inr ⟨x, b, rfl⟩)
        · exfalso; exact rootRedexOpt_none hr x y rfl

theorem headStepOpt_none_spineLen {t : Term} (hv : noVars t = true) (h : headStepOpt t = none) :
    spineLen t ≤ 2 := by
  rcases headStepOpt_none_closed hv h with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · exact Nat.zero_le 2
  · exact Nat.succ_le_succ (Nat.zero_le 1)
  · exact Nat.le_refl 2

def stepLO : Term → Option Term
  | .s => none
  | .var _ => none
  | .app a b =>
    match rootRedexOpt a b with
    | some r => some r
    | none =>
      match stepLO a with
      | some a' => some (a' ⋅ b)
      | none =>
        match stepLO b with
        | some b' => some (a ⋅ b')
        | none => none

theorem stepLO_some_step {t t' : Term} (h : stepLO t = some t') : Step t t' := by
  induction t generalizing t' with
  | s => cases h
  | var _ => cases h
  | app a b iha ihb =>
    simp only [stepLO] at h
    cases hr : rootRedexOpt a b with
    | some r =>
      rw [hr] at h
      injection h with heq
      subst heq
      obtain ⟨x, y, ha, hreq⟩ := rootRedexOpt_some hr
      subst ha; subst hreq
      exact Step.root x y b
    | none =>
      rw [hr] at h
      cases ha : stepLO a with
      | some a' =>
        rw [ha] at h
        injection h with heq
        subst heq
        exact Step.left (iha ha)
      | none =>
        rw [ha] at h
        cases hb : stepLO b with
        | some b' =>
          rw [hb] at h
          injection h with heq
          subst heq
          exact Step.right (ihb hb)
        | none =>
          rw [hb] at h
          cases h

theorem stepLO_none_isNormalForm {t : Term} (h : stepLO t = none) : IsNormalForm t := by
  intro t' hs
  induction hs with
  | root x y z =>
    cases h
  | @left a a' b _ iha =>
    simp only [stepLO] at h
    cases hr : rootRedexOpt a b with
    | some _ => rw [hr] at h; cases h
    | none =>
      rw [hr] at h
      cases ha : stepLO a with
      | some _ => rw [ha] at h; cases h
      | none => exact iha ha
  | @right a b b' _ ihb =>
    simp only [stepLO] at h
    cases hr : rootRedexOpt a b with
    | some _ => rw [hr] at h; cases h
    | none =>
      rw [hr] at h
      cases ha : stepLO a with
      | some _ => rw [ha] at h; cases h
      | none =>
        rw [ha] at h
        cases hb : stepLO b with
        | some _ => rw [hb] at h; cases h
        | none => exact ihb hb

theorem sn_implies_wn {t : Term} (hsn : StrongNormalizing t) : HasNormalForm t := by
  induction hsn with
  | intro t _ ih =>
    cases h : stepLO t with
    | none => exact ⟨t, Reduces.refl t, stepLO_none_isNormalForm h⟩
    | some t' =>
      obtain ⟨nf, hred, hnf⟩ := ih t' (stepLO_some_step h)
      exact ⟨nf, Reduces.next (stepLO_some_step h) hred, hnf⟩

/-- **Constructive Equivalence `SN ↔ WN` for all pure-`S` terms (open or closed)**. -/
theorem sn_iff_wn (t : Term) : StrongNormalizing t ↔ HasNormalForm t :=
  ⟨sn_implies_wn, wn_implies_sn⟩

/-! ## 2. Exact 39-State Strong Normalization S-Algebra `A_SN` & Waldmann's Theorem 9 -/

inductive StateSN where
  | sn0 | sn1 | sn2 | sn3 | sn4 | sn5 | sn6 | sn7 | sn8 | sn9 | sn10 | sn11 | sn12 | sn13 | sn14 | sn15 | sn16 | sn17 | sn18 | sn19 | sn20 | sn21 | sn22 | sn23 | sn24 | sn25 | sn26 | sn27 | sn28 | sn29 | sn30 | sn31 | sn32 | sn33 | sn34 | sn35 | sn36 | sn37 | sn38
  deriving DecidableEq, Repr

def stateSNToNat : StateSN → Nat
  | .sn0 => 0
  | .sn1 => 1
  | .sn2 => 2
  | .sn3 => 3
  | .sn4 => 4
  | .sn5 => 5
  | .sn6 => 6
  | .sn7 => 7
  | .sn8 => 8
  | .sn9 => 9
  | .sn10 => 10
  | .sn11 => 11
  | .sn12 => 12
  | .sn13 => 13
  | .sn14 => 14
  | .sn15 => 15
  | .sn16 => 16
  | .sn17 => 17
  | .sn18 => 18
  | .sn19 => 19
  | .sn20 => 20
  | .sn21 => 21
  | .sn22 => 22
  | .sn23 => 23
  | .sn24 => 24
  | .sn25 => 25
  | .sn26 => 26
  | .sn27 => 27
  | .sn28 => 28
  | .sn29 => 29
  | .sn30 => 30
  | .sn31 => 31
  | .sn32 => 32
  | .sn33 => 33
  | .sn34 => 34
  | .sn35 => 35
  | .sn36 => 36
  | .sn37 => 37
  | .sn38 => 38

def deltaSN : StateSN → StateSN → StateSN
  | .sn0, y => match y with | .sn0 => .sn1 | .sn1 => .sn2 | .sn2 => .sn3 | .sn3 => .sn4 | .sn4 => .sn5 | .sn7 => .sn8 | .sn8 => .sn5 | .sn9 => .sn10 | .sn10 => .sn5 | .sn11 => .sn12 | .sn12 => .sn5 | .sn13 => .sn4 | .sn14 => .sn5 | .sn15 => .sn10 | .sn16 => .sn5 | .sn17 => .sn5 | .sn18 => .sn5 | .sn19 => .sn20 | .sn32 => .sn21 | .sn36 => .sn21 | .sn38 => .sn38 | _ => .sn6
  | .sn1, y => match y with | .sn0 => .sn7 | .sn1 => .sn9 | .sn2 => .sn11 | .sn3 => .sn13 | .sn4 => .sn14 | .sn5 => .sn5 | .sn6 => .sn6 | .sn8 => .sn16 | .sn10 => .sn17 | .sn11 => .sn11 | .sn12 => .sn18 | .sn13 => .sn13 | .sn14 => .sn14 | .sn16 => .sn16 | .sn17 => .sn17 | .sn18 => .sn18 | .sn19 => .sn19 | .sn20 => .sn21 | .sn21 => .sn21 | .sn22 => .sn23 | .sn23 => .sn23 | .sn24 => .sn24 | .sn25 => .sn25 | .sn26 => .sn26 | .sn27 => .sn27 | .sn28 => .sn28 | .sn29 => .sn29 | .sn30 => .sn30 | .sn31 => .sn31 | .sn32 => .sn32 | .sn33 => .sn33 | .sn34 => .sn34 | .sn35 => .sn35 | .sn36 => .sn36 | .sn37 => .sn37 | .sn38 => .sn38 | _ => .sn15
  | .sn2, y => match y with | .sn0 => .sn19 | .sn1 => .sn22 | .sn2 => .sn24 | .sn7 => .sn26 | .sn9 => .sn26 | .sn15 => .sn26 | .sn29 => .sn29 | .sn30 => .sn30 | .sn31 => .sn31 | .sn32 => .sn31 | .sn33 => .sn31 | .sn34 => .sn29 | .sn35 => .sn29 | .sn36 => .sn31 | .sn37 => .sn31 | .sn38 => .sn38 | _ => .sn25
  | .sn3, y => match y with | .sn0 => .sn27 | .sn1 => .sn28 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn29 | .sn19 => .sn29 | .sn32 => .sn29 | .sn36 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn4, y => match y with | .sn0 => .sn31 | .sn1 => .sn31 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn29 | .sn19 => .sn29 | .sn32 => .sn29 | .sn36 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn5, y => match y with | .sn0 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn6, y => match y with | .sn38 => .sn38 | _ => .sn30
  | .sn7, y => match y with | .sn0 => .sn9 | .sn1 => .sn24 | .sn2 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn8, y => match y with | .sn0 => .sn32 | .sn1 => .sn33 | .sn7 => .sn34 | .sn9 => .sn34 | .sn15 => .sn34 | .sn30 => .sn30 | .sn38 => .sn38 | _ => .sn29
  | .sn9, y => match y with | .sn0 => .sn15 | .sn1 => .sn26 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn34 | .sn9 => .sn35 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn35 | .sn38 => .sn38 | _ => .sn30
  | .sn10, y => match y with | .sn0 => .sn36 | .sn1 => .sn37 | .sn7 => .sn35 | .sn9 => .sn35 | .sn15 => .sn35 | .sn30 => .sn30 | .sn38 => .sn38 | _ => .sn29
  | .sn11, y => match y with | .sn0 => .sn19 | .sn1 => .sn25 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn12, y => match y with | .sn0 => .sn37 | .sn1 => .sn31 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn29 | .sn19 => .sn29 | .sn32 => .sn29 | .sn36 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn13, y => match y with | .sn0 => .sn27 | .sn1 => .sn25 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn14, y => match y with | .sn0 => .sn31 | .sn1 => .sn31 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn15, y => match y with | .sn0 => .sn15 | .sn1 => .sn25 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn16, y => match y with | .sn0 => .sn32 | .sn1 => .sn31 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn17, y => match y with | .sn0 => .sn36 | .sn1 => .sn31 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn18, y => match y with | .sn0 => .sn37 | .sn1 => .sn31 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn19, y => match y with | .sn0 => .sn24 | .sn1 => .sn29 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn20, y => match y with | .sn0 => .sn29 | .sn1 => .sn29 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn21, y => match y with | .sn0 => .sn29 | .sn1 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn22, y => match y with | .sn0 => .sn29 | .sn1 => .sn35 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn23, y => match y with | .sn0 => .sn29 | .sn1 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn24, y => match y with | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn25, y => match y with | .sn19 => .sn38 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn27 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn26, y => match y with | .sn0 => .sn29 | .sn19 => .sn38 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn27 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn27, y => match y with | .sn0 => .sn29 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn28, y => match y with | .sn1 => .sn29 | .sn19 => .sn38 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn27 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn29, y => match y with | .sn0 => .sn30 | _ => .sn38
  | .sn30, _ => .sn38
  | .sn31, y => match y with | .sn0 => .sn30 | .sn1 => .sn30 | _ => .sn38
  | .sn32, y => match y with | .sn0 => .sn26 | .sn1 => .sn30 | _ => .sn38
  | .sn33, y => match y with | .sn0 => .sn34 | .sn1 => .sn30 | _ => .sn38
  | .sn34, y => match y with | .sn0 => .sn35 | _ => .sn38
  | .sn35, y => match y with | .sn0 => .sn29 | _ => .sn38
  | .sn36, y => match y with | .sn0 => .sn25 | .sn1 => .sn30 | _ => .sn38
  | .sn37, y => match y with | .sn0 => .sn29 | .sn1 => .sn30 | _ => .sn38
  | .sn38, _ => .sn38

def checkAll1_StateSN (p : StateSN → Bool) : Bool :=
  (((((p .sn0 && p .sn1) && (p .sn2 && p .sn3)) && ((p .sn4 && p .sn5) && (p .sn6 && (p .sn7 && p .sn8)))) && (((p .sn9 && p .sn10) && (p .sn11 && (p .sn12 && p .sn13))) && ((p .sn14 && p .sn15) && (p .sn16 && (p .sn17 && p .sn18))))) && ((((p .sn19 && p .sn20) && (p .sn21 && (p .sn22 && p .sn23))) && ((p .sn24 && p .sn25) && (p .sn26 && (p .sn27 && p .sn28)))) && (((p .sn29 && p .sn30) && (p .sn31 && (p .sn32 && p .sn33))) && ((p .sn34 && p .sn35) && (p .sn36 && (p .sn37 && p .sn38))))))

theorem checkAll1_StateSN_sound (p : StateSN → Bool)
    (h : checkAll1_StateSN p = true) (x : StateSN) : p x = true :=
  match x with
  | .sn0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .sn1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .sn2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .sn3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .sn4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .sn5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .sn6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .sn7 => (and_left (and_right (and_right (and_right (and_left (and_left h))))))
  | .sn8 => (and_right (and_right (and_right (and_right (and_left (and_left h))))))
  | .sn9 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .sn10 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .sn11 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .sn12 => (and_left (and_right (and_right (and_left (and_right (and_left h))))))
  | .sn13 => (and_right (and_right (and_right (and_left (and_right (and_left h))))))
  | .sn14 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .sn15 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .sn16 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .sn17 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .sn18 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .sn19 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .sn20 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .sn21 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .sn22 => (and_left (and_right (and_right (and_left (and_left (and_right h))))))
  | .sn23 => (and_right (and_right (and_right (and_left (and_left (and_right h))))))
  | .sn24 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .sn25 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .sn26 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .sn27 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .sn28 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .sn29 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .sn30 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .sn31 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .sn32 => (and_left (and_right (and_right (and_left (and_right (and_right h))))))
  | .sn33 => (and_right (and_right (and_right (and_left (and_right (and_right h))))))
  | .sn34 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .sn35 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .sn36 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .sn37 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .sn38 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateSN (p : StateSN → StateSN → Bool) : Bool :=
  checkAll1_StateSN (fun x => checkAll1_StateSN (fun y => p x y))

theorem checkAll2_StateSN_sound (p : StateSN → StateSN → Bool)
    (h : checkAll2_StateSN p = true) (x y : StateSN) : p x y = true :=
  checkAll1_StateSN_sound _ (checkAll1_StateSN_sound _ h x) y

private theorem s_row_StateSN_0 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn0) y) z = deltaSN (deltaSN .sn0 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_1 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn1) y) z = deltaSN (deltaSN .sn1 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_2 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn2) y) z = deltaSN (deltaSN .sn2 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_3 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn3) y) z = deltaSN (deltaSN .sn3 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_4 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn4) y) z = deltaSN (deltaSN .sn4 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_5 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn5) y) z = deltaSN (deltaSN .sn5 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_6 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn6) y) z = deltaSN (deltaSN .sn6 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_7 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn7) y) z = deltaSN (deltaSN .sn7 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_8 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn8) y) z = deltaSN (deltaSN .sn8 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_9 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn9) y) z = deltaSN (deltaSN .sn9 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_10 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn10) y) z = deltaSN (deltaSN .sn10 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_11 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn11) y) z = deltaSN (deltaSN .sn11 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_12 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn12) y) z = deltaSN (deltaSN .sn12 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_13 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn13) y) z = deltaSN (deltaSN .sn13 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_14 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn14) y) z = deltaSN (deltaSN .sn14 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_15 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn15) y) z = deltaSN (deltaSN .sn15 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_16 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn16) y) z = deltaSN (deltaSN .sn16 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_17 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn17) y) z = deltaSN (deltaSN .sn17 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_18 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn18) y) z = deltaSN (deltaSN .sn18 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_19 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn19) y) z = deltaSN (deltaSN .sn19 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_20 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn20) y) z = deltaSN (deltaSN .sn20 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_21 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn21) y) z = deltaSN (deltaSN .sn21 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_22 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn22) y) z = deltaSN (deltaSN .sn22 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_23 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn23) y) z = deltaSN (deltaSN .sn23 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_24 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn24) y) z = deltaSN (deltaSN .sn24 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_25 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn25) y) z = deltaSN (deltaSN .sn25 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_26 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn26) y) z = deltaSN (deltaSN .sn26 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_27 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn27) y) z = deltaSN (deltaSN .sn27 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_28 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn28) y) z = deltaSN (deltaSN .sn28 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_29 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn29) y) z = deltaSN (deltaSN .sn29 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_30 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn30) y) z = deltaSN (deltaSN .sn30 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_31 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn31) y) z = deltaSN (deltaSN .sn31 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_32 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn32) y) z = deltaSN (deltaSN .sn32 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_33 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn33) y) z = deltaSN (deltaSN .sn33 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_34 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn34) y) z = deltaSN (deltaSN .sn34 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_35 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn35) y) z = deltaSN (deltaSN .sn35 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_36 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn36) y) z = deltaSN (deltaSN .sn36 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_37 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn37) y) z = deltaSN (deltaSN .sn37 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_38 : checkAll2_StateSN (fun y z => decide (deltaSN (deltaSN (deltaSN .sn0 .sn38) y) z = deltaSN (deltaSN .sn38 z) (deltaSN y z))) = true := rfl

theorem deltaSN_s_law (x y z : StateSN) :
    deltaSN (deltaSN (deltaSN .sn0 x) y) z = deltaSN (deltaSN x z) (deltaSN y z) := by
  cases x with
  | sn0 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_0 y z)
  | sn1 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_1 y z)
  | sn2 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_2 y z)
  | sn3 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_3 y z)
  | sn4 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_4 y z)
  | sn5 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_5 y z)
  | sn6 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_6 y z)
  | sn7 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_7 y z)
  | sn8 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_8 y z)
  | sn9 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_9 y z)
  | sn10 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_10 y z)
  | sn11 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_11 y z)
  | sn12 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_12 y z)
  | sn13 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_13 y z)
  | sn14 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_14 y z)
  | sn15 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_15 y z)
  | sn16 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_16 y z)
  | sn17 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_17 y z)
  | sn18 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_18 y z)
  | sn19 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_19 y z)
  | sn20 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_20 y z)
  | sn21 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_21 y z)
  | sn22 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_22 y z)
  | sn23 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_23 y z)
  | sn24 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_24 y z)
  | sn25 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_25 y z)
  | sn26 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_26 y z)
  | sn27 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_27 y z)
  | sn28 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_28 y z)
  | sn29 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_29 y z)
  | sn30 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_30 y z)
  | sn31 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_31 y z)
  | sn32 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_32 y z)
  | sn33 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_33 y z)
  | sn34 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_34 y z)
  | sn35 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_35 y z)
  | sn36 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_36 y z)
  | sn37 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_37 y z)
  | sn38 => exact of_decide_eq_true (checkAll2_StateSN_sound _ s_row_StateSN_38 y z)

private theorem deltaSN_sn38_left_chk : checkAll1_StateSN (fun y => decide (deltaSN .sn38 y = .sn38)) = true := rfl
private theorem deltaSN_sn38_right_chk : checkAll1_StateSN (fun x => decide (deltaSN x .sn38 = .sn38)) = true := rfl
private theorem deltaSN_s1_ne38_chk : checkAll1_StateSN (fun x => decide (x ≠ .sn38 → deltaSN .sn0 x ≠ .sn38)) = true := rfl
private theorem deltaSN_s2_ne38_chk : checkAll2_StateSN (fun x y => decide (x ≠ .sn38 → y ≠ .sn38 → deltaSN (deltaSN .sn0 x) y ≠ .sn38)) = true := rfl

theorem deltaSN_sn38_left (y : StateSN) : deltaSN .sn38 y = .sn38 :=
  of_decide_eq_true (checkAll1_StateSN_sound _ deltaSN_sn38_left_chk y)

theorem deltaSN_sn38_right (x : StateSN) : deltaSN x .sn38 = .sn38 :=
  of_decide_eq_true (checkAll1_StateSN_sound _ deltaSN_sn38_right_chk x)

theorem deltaSN_ne_sn38_factors {x y : StateSN} (h : deltaSN x y ≠ .sn38) :
    x ≠ .sn38 ∧ y ≠ .sn38 := by
  constructor
  · intro hx; subst hx; exact h (deltaSN_sn38_left y)
  · intro hy; subst hy; exact h (deltaSN_sn38_right x)

theorem deltaSN_s1_ne_sn38 {x : StateSN} (hx : x ≠ .sn38) : deltaSN .sn0 x ≠ .sn38 :=
  (of_decide_eq_true (checkAll1_StateSN_sound _ deltaSN_s1_ne38_chk x)) hx

theorem deltaSN_s2_ne_sn38 {x y : StateSN} (hx : x ≠ .sn38) (hy : y ≠ .sn38) :
    deltaSN (deltaSN .sn0 x) y ≠ .sn38 :=
  (of_decide_eq_true (checkAll2_StateSN_sound _ deltaSN_s2_ne38_chk x y)) hx hy

def evalSN : Term → StateSN
  | .s => .sn0
  | .var _ => .sn0
  | .app a b => deltaSN (evalSN a) (evalSN b)

theorem evalSN_step {a b : Term} (h : Step a b) : evalSN a = evalSN b := by
  induction h with
  | root x y z => exact deltaSN_s_law (evalSN x) (evalSN y) (evalSN z)
  | left _ ih => simp only [evalSN, ih]
  | right _ ih => simp only [evalSN, ih]

theorem evalSN_reduces {a b : Term} (h : Reduces a b) : evalSN a = evalSN b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalSN_step hs).trans ih

theorem evalSN_conv {a b : Term} (h : ConvS a b) : evalSN a = evalSN b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalSN_step hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem closed_nf_evalSN_ne_sn38 {t : Term} (hv : noVars t = true) (hnf : IsNormalForm t) :
    evalSN t ≠ .sn38 := by
  induction t with
  | s => decide
  | var _ => cases hv
  | app a b iha ihb =>
    have hnone : headStepOpt (a ⋅ b) = none := by
      cases hh : headStepOpt (a ⋅ b) with
      | none => rfl
      | some w => exfalso; exact hnf w (headStep_to_step (headStepOpt_some hh))
    have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hv).1
    have hvb : noVars b = true := ((Bool.and_eq_true _ _).mp hv).2
    have hnfa : IsNormalForm a := fun a' hs => hnf (a' ⋅ b) (Step.left hs)
    have hnfb : IsNormalForm b := fun b' hs => hnf (a ⋅ b') (Step.right hs)
    rcases headStepOpt_none_closed hv hnone with heq | ⟨x, heq⟩ | ⟨x, y, heq⟩
    · cases heq
    · injection heq with ha hb
      subst ha; subst hb
      exact deltaSN_s1_ne_sn38 (ihb hvb hnfb)
    · injection heq with ha hb
      subst ha; subst hb
      exact deltaSN_s2_ne_sn38 ((deltaSN_ne_sn38_factors (iha hva hnfa)).2) (ihb hvb hnfb)

def isS2StateSN : StateSN → Bool
  | .sn5 => true | .sn6 => true | .sn7 => true | .sn9 => true | .sn11 => true | .sn13 => true | .sn14 => true | .sn15 => true | .sn16 => true | .sn17 => true | .sn18 => true | .sn19 => true | .sn21 => true | .sn22 => true | .sn23 => true | .sn24 => true | .sn25 => true | .sn26 => true | .sn27 => true | .sn28 => true | .sn29 => true | .sn30 => true | .sn31 => true | .sn32 => true | .sn33 => true | .sn34 => true | .sn35 => true | .sn36 => true | .sn37 => true
  | _ => false

def maxSubRankSN : StateSN → StateSN → Nat
  | .sn0, _ => 0
  | .sn1, _ => 0
  | .sn2, _ => 0
  | .sn3, _ => 0
  | .sn4, _ => 0
  | .sn5, y => match y with | .sn38 => 0 | _ => 1
  | .sn6, y => match y with | .sn38 => 0 | _ => 1
  | .sn7, y => match y with | .sn38 => 0 | _ => 1
  | .sn8, _ => 0
  | .sn9, y => match y with | .sn38 => 0 | _ => 1
  | .sn10, _ => 0
  | .sn11, y => match y with | .sn38 => 0 | _ => 1
  | .sn12, _ => 0
  | .sn13, y => match y with | .sn38 => 0 | _ => 1
  | .sn14, y => match y with | .sn38 => 0 | _ => 1
  | .sn15, y => match y with | .sn38 => 0 | _ => 1
  | .sn16, y => match y with | .sn38 => 0 | _ => 1
  | .sn17, y => match y with | .sn38 => 0 | _ => 1
  | .sn18, y => match y with | .sn38 => 0 | _ => 1
  | .sn19, y => match y with | .sn19 => 3 | .sn22 => 3 | .sn23 => 3 | .sn24 => 3 | .sn25 => 4 | .sn26 => 3 | .sn27 => 4 | .sn28 => 4 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2
  | .sn20, _ => 0
  | .sn21, y => match y with | .sn38 => 0 | _ => 1
  | .sn22, y => match y with | .sn19 => 4 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 5 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2
  | .sn23, y => match y with | .sn19 => 4 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 5 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2
  | .sn24, y => match y with | .sn19 => 5 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 5 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2
  | .sn25, y => match y with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3
  | .sn26, y => match y with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2
  | .sn27, y => match y with | .sn25 => 4 | .sn27 => 4 | .sn28 => 4 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3
  | .sn28, y => match y with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3
  | .sn29, y => match y with | .sn0 => 6 | _ => 0
  | .sn30, _ => 0
  | .sn31, y => match y with | .sn0 => 4 | .sn1 => 4 | _ => 0
  | .sn32, y => match y with | .sn0 => 2 | .sn1 => 3 | _ => 0
  | .sn33, y => match y with | .sn0 => 2 | .sn1 => 3 | _ => 0
  | .sn34, y => match y with | .sn0 => 2 | _ => 0
  | .sn35, y => match y with | .sn0 => 2 | _ => 0
  | .sn36, y => match y with | .sn0 => 2 | .sn1 => 4 | _ => 0
  | .sn37, y => match y with | .sn0 => 3 | .sn1 => 4 | _ => 0
  | .sn38, _ => 0

def tripleRankSN : StateSN → StateSN → StateSN → Nat
  | .sn0, y, z => match y with | .sn0 => (match z with | .sn38 => 0 | _ => 1) | .sn1 => (match z with | .sn38 => 0 | _ => 1) | .sn2 => (match z with | .sn38 => 0 | _ => 1) | .sn3 => (match z with | .sn38 => 0 | _ => 1) | .sn4 => (match z with | .sn38 => 0 | _ => 1) | .sn5 => (match z with | .sn38 => 0 | _ => 1) | .sn6 => (match z with | .sn38 => 0 | _ => 1) | .sn7 => (match z with | .sn38 => 0 | _ => 1) | .sn8 => (match z with | .sn38 => 0 | _ => 1) | .sn9 => (match z with | .sn38 => 0 | _ => 1) | .sn10 => (match z with | .sn38 => 0 | _ => 1) | .sn11 => (match z with | .sn38 => 0 | _ => 1) | .sn12 => (match z with | .sn38 => 0 | _ => 1) | .sn13 => (match z with | .sn38 => 0 | _ => 1) | .sn14 => (match z with | .sn38 => 0 | _ => 1) | .sn15 => (match z with | .sn38 => 0 | _ => 1) | .sn16 => (match z with | .sn38 => 0 | _ => 1) | .sn17 => (match z with | .sn38 => 0 | _ => 1) | .sn18 => (match z with | .sn38 => 0 | _ => 1) | .sn19 => (match z with | .sn19 => 3 | .sn22 => 3 | .sn23 => 3 | .sn24 => 3 | .sn25 => 4 | .sn26 => 3 | .sn27 => 4 | .sn28 => 4 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn20 => (match z with | .sn38 => 0 | _ => 1) | .sn21 => (match z with | .sn38 => 0 | _ => 1) | .sn22 => (match z with | .sn19 => 4 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 5 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn23 => (match z with | .sn19 => 4 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 5 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn24 => (match z with | .sn19 => 5 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 5 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn25 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3) | .sn26 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn27 => (match z with | .sn25 => 4 | .sn27 => 4 | .sn28 => 4 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3) | .sn28 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3) | .sn29 => (match z with | .sn0 => 6 | _ => 0) | .sn31 => (match z with | .sn0 => 4 | .sn1 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 2 | .sn1 => 3 | _ => 0) | .sn33 => (match z with | .sn0 => 2 | .sn1 => 3 | _ => 0) | .sn34 => (match z with | .sn0 => 2 | _ => 0) | .sn35 => (match z with | .sn0 => 2 | _ => 0) | .sn36 => (match z with | .sn0 => 2 | .sn1 => 4 | _ => 0) | .sn37 => (match z with | .sn0 => 3 | .sn1 => 4 | _ => 0) | _ => 0
  | .sn1, y, z => match y with | .sn0 => (match z with | .sn19 => 3 | .sn22 => 3 | .sn23 => 3 | .sn24 => 3 | .sn25 => 4 | .sn26 => 3 | .sn27 => 4 | .sn28 => 4 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn1 => (match z with | .sn19 => 4 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 5 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn2 => (match z with | .sn19 => 5 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 5 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn3 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn4 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn5 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn6 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn7 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn8 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn9 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn10 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn11 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn12 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn13 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn14 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn15 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn16 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn17 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn18 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn19 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn20 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn21 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn22 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn23 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn24 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn25 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3) | .sn26 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 2) | .sn27 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3) | .sn28 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3) | .sn29 => (match z with | .sn0 => 6 | _ => 0) | .sn31 => (match z with | .sn0 => 4 | .sn1 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 2 | .sn1 => 3 | _ => 0) | .sn33 => (match z with | .sn0 => 2 | .sn1 => 3 | _ => 0) | .sn34 => (match z with | .sn0 => 2 | _ => 0) | .sn35 => (match z with | .sn0 => 2 | _ => 0) | .sn36 => (match z with | .sn0 => 2 | .sn1 => 4 | _ => 0) | .sn37 => (match z with | .sn0 => 3 | .sn1 => 4 | _ => 0) | _ => 0
  | .sn2, y, z => match y with | .sn0 => (match z with | .sn25 => 4 | .sn27 => 4 | .sn28 => 4 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3) | .sn1 => (match z with | .sn19 => 0 | .sn22 => 0 | .sn23 => 0 | .sn24 => 0 | .sn25 => 0 | .sn26 => 0 | .sn27 => 0 | .sn28 => 0 | .sn29 => 0 | .sn30 => 0 | .sn31 => 0 | .sn32 => 0 | .sn33 => 0 | .sn34 => 0 | .sn35 => 0 | .sn36 => 0 | .sn37 => 0 | .sn38 => 0 | _ => 3) | .sn2 => (match z with | .sn0 => 4 | _ => 0) | .sn3 => (match z with | .sn0 => 5 | _ => 0) | .sn7 => (match z with | .sn0 => 3 | _ => 0) | .sn9 => (match z with | .sn0 => 3 | _ => 0) | .sn11 => (match z with | .sn0 => 4 | _ => 0) | .sn13 => (match z with | .sn0 => 5 | _ => 0) | .sn15 => (match z with | .sn0 => 3 | _ => 0) | .sn19 => (match z with | .sn0 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 4 | _ => 0) | .sn36 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn3, y, z => match y with | .sn0 => (match z with | .sn0 => 4 | .sn1 => 4 | _ => 0) | .sn1 => (match z with | .sn0 => 4 | .sn1 => 4 | _ => 0) | .sn2 => (match z with | .sn0 => 4 | _ => 0) | .sn3 => (match z with | .sn0 => 5 | _ => 0) | .sn7 => (match z with | .sn0 => 4 | _ => 0) | .sn9 => (match z with | .sn0 => 4 | _ => 0) | .sn11 => (match z with | .sn0 => 4 | _ => 0) | .sn13 => (match z with | .sn0 => 5 | _ => 0) | .sn15 => (match z with | .sn0 => 4 | _ => 0) | .sn19 => (match z with | .sn0 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 4 | _ => 0) | .sn36 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn4, y, z => match y with | .sn0 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn5, _, _ => 0
  | .sn6, _, _ => 0
  | .sn7, y, z => match y with | .sn0 => (match z with | .sn0 => 2 | .sn1 => 3 | _ => 0) | .sn1 => (match z with | .sn0 => 2 | .sn1 => 3 | _ => 0) | .sn2 => (match z with | .sn0 => 2 | _ => 0) | .sn3 => (match z with | .sn0 => 2 | _ => 0) | .sn4 => (match z with | .sn0 => 2 | _ => 0) | .sn5 => (match z with | .sn0 => 2 | _ => 0) | .sn6 => (match z with | .sn0 => 2 | _ => 0) | .sn7 => (match z with | .sn0 => 2 | _ => 0) | .sn8 => (match z with | .sn0 => 2 | _ => 0) | .sn9 => (match z with | .sn0 => 2 | _ => 0) | .sn10 => (match z with | .sn0 => 2 | _ => 0) | .sn11 => (match z with | .sn0 => 2 | _ => 0) | .sn12 => (match z with | .sn0 => 2 | _ => 0) | .sn13 => (match z with | .sn0 => 2 | _ => 0) | .sn14 => (match z with | .sn0 => 2 | _ => 0) | .sn15 => (match z with | .sn0 => 2 | _ => 0) | .sn16 => (match z with | .sn0 => 2 | _ => 0) | .sn17 => (match z with | .sn0 => 2 | _ => 0) | .sn18 => (match z with | .sn0 => 2 | _ => 0) | .sn19 => (match z with | .sn0 => 2 | _ => 0) | .sn20 => (match z with | .sn0 => 2 | _ => 0) | .sn21 => (match z with | .sn0 => 2 | _ => 0) | .sn22 => (match z with | .sn0 => 2 | _ => 0) | .sn23 => (match z with | .sn0 => 2 | _ => 0) | .sn24 => (match z with | .sn0 => 2 | _ => 0) | .sn25 => (match z with | .sn0 => 3 | _ => 0) | .sn26 => (match z with | .sn0 => 2 | _ => 0) | .sn27 => (match z with | .sn0 => 3 | _ => 0) | .sn28 => (match z with | .sn0 => 3 | _ => 0) | .sn29 => (match z with | .sn0 => 6 | _ => 0) | .sn31 => (match z with | .sn0 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 2 | _ => 0) | .sn33 => (match z with | .sn0 => 2 | _ => 0) | .sn34 => (match z with | .sn0 => 2 | _ => 0) | .sn35 => (match z with | .sn0 => 2 | _ => 0) | .sn36 => (match z with | .sn0 => 2 | _ => 0) | .sn37 => (match z with | .sn0 => 3 | _ => 0) | _ => 0
  | .sn8, y, z => match y with | .sn0 => (match z with | .sn0 => 4 | _ => 0) | _ => 0
  | .sn9, y, z => match y with | .sn0 => (match z with | .sn0 => 2 | .sn1 => 3 | _ => 0) | .sn1 => (match z with | .sn0 => 2 | .sn1 => 3 | _ => 0) | .sn2 => (match z with | .sn0 => 2 | _ => 0) | .sn3 => (match z with | .sn0 => 2 | _ => 0) | .sn4 => (match z with | .sn0 => 2 | _ => 0) | .sn5 => (match z with | .sn0 => 2 | _ => 0) | .sn6 => (match z with | .sn0 => 2 | _ => 0) | .sn7 => (match z with | .sn0 => 2 | _ => 0) | .sn8 => (match z with | .sn0 => 2 | _ => 0) | .sn9 => (match z with | .sn0 => 2 | _ => 0) | .sn10 => (match z with | .sn0 => 2 | _ => 0) | .sn11 => (match z with | .sn0 => 2 | _ => 0) | .sn12 => (match z with | .sn0 => 2 | _ => 0) | .sn13 => (match z with | .sn0 => 2 | _ => 0) | .sn14 => (match z with | .sn0 => 2 | _ => 0) | .sn15 => (match z with | .sn0 => 2 | _ => 0) | .sn16 => (match z with | .sn0 => 2 | _ => 0) | .sn17 => (match z with | .sn0 => 2 | _ => 0) | .sn18 => (match z with | .sn0 => 2 | _ => 0) | .sn19 => (match z with | .sn0 => 2 | _ => 0) | .sn20 => (match z with | .sn0 => 2 | _ => 0) | .sn21 => (match z with | .sn0 => 2 | _ => 0) | .sn22 => (match z with | .sn0 => 2 | _ => 0) | .sn23 => (match z with | .sn0 => 2 | _ => 0) | .sn24 => (match z with | .sn0 => 2 | _ => 0) | .sn25 => (match z with | .sn0 => 3 | _ => 0) | .sn26 => (match z with | .sn0 => 2 | _ => 0) | .sn27 => (match z with | .sn0 => 3 | _ => 0) | .sn28 => (match z with | .sn0 => 3 | _ => 0) | .sn29 => (match z with | .sn0 => 6 | _ => 0) | .sn31 => (match z with | .sn0 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 2 | _ => 0) | .sn33 => (match z with | .sn0 => 2 | _ => 0) | .sn34 => (match z with | .sn0 => 2 | _ => 0) | .sn35 => (match z with | .sn0 => 2 | _ => 0) | .sn36 => (match z with | .sn0 => 2 | _ => 0) | .sn37 => (match z with | .sn0 => 3 | _ => 0) | _ => 0
  | .sn10, y, z => match y with | .sn0 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn11, y, z => match y with | .sn0 => (match z with | .sn0 => 3 | .sn1 => 4 | _ => 0) | .sn1 => (match z with | .sn0 => 3 | .sn1 => 4 | _ => 0) | .sn2 => (match z with | .sn0 => 4 | _ => 0) | .sn3 => (match z with | .sn0 => 5 | _ => 0) | .sn7 => (match z with | .sn0 => 3 | _ => 0) | .sn9 => (match z with | .sn0 => 3 | _ => 0) | .sn11 => (match z with | .sn0 => 4 | _ => 0) | .sn13 => (match z with | .sn0 => 5 | _ => 0) | .sn15 => (match z with | .sn0 => 3 | _ => 0) | .sn19 => (match z with | .sn0 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 4 | _ => 0) | .sn36 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn12, y, z => match y with | .sn0 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn13, y, z => match y with | .sn0 => (match z with | .sn0 => 4 | .sn1 => 4 | _ => 0) | .sn1 => (match z with | .sn0 => 4 | .sn1 => 4 | _ => 0) | .sn2 => (match z with | .sn0 => 4 | _ => 0) | .sn3 => (match z with | .sn0 => 5 | _ => 0) | .sn7 => (match z with | .sn0 => 4 | _ => 0) | .sn9 => (match z with | .sn0 => 4 | _ => 0) | .sn11 => (match z with | .sn0 => 4 | _ => 0) | .sn13 => (match z with | .sn0 => 5 | _ => 0) | .sn15 => (match z with | .sn0 => 4 | _ => 0) | .sn19 => (match z with | .sn0 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 4 | _ => 0) | .sn36 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn14, y, z => match y with | .sn0 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn15, y, z => match y with | .sn0 => (match z with | .sn0 => 2 | .sn1 => 4 | _ => 0) | .sn1 => (match z with | .sn0 => 2 | .sn1 => 4 | _ => 0) | .sn2 => (match z with | .sn0 => 2 | _ => 0) | .sn3 => (match z with | .sn0 => 2 | _ => 0) | .sn4 => (match z with | .sn0 => 2 | _ => 0) | .sn5 => (match z with | .sn0 => 2 | _ => 0) | .sn6 => (match z with | .sn0 => 2 | _ => 0) | .sn7 => (match z with | .sn0 => 2 | _ => 0) | .sn8 => (match z with | .sn0 => 2 | _ => 0) | .sn9 => (match z with | .sn0 => 2 | _ => 0) | .sn10 => (match z with | .sn0 => 2 | _ => 0) | .sn11 => (match z with | .sn0 => 2 | _ => 0) | .sn12 => (match z with | .sn0 => 2 | _ => 0) | .sn13 => (match z with | .sn0 => 2 | _ => 0) | .sn14 => (match z with | .sn0 => 2 | _ => 0) | .sn15 => (match z with | .sn0 => 2 | _ => 0) | .sn16 => (match z with | .sn0 => 2 | _ => 0) | .sn17 => (match z with | .sn0 => 2 | _ => 0) | .sn18 => (match z with | .sn0 => 2 | _ => 0) | .sn19 => (match z with | .sn0 => 2 | _ => 0) | .sn20 => (match z with | .sn0 => 2 | _ => 0) | .sn21 => (match z with | .sn0 => 2 | _ => 0) | .sn22 => (match z with | .sn0 => 2 | _ => 0) | .sn23 => (match z with | .sn0 => 2 | _ => 0) | .sn24 => (match z with | .sn0 => 2 | _ => 0) | .sn25 => (match z with | .sn0 => 3 | _ => 0) | .sn26 => (match z with | .sn0 => 2 | _ => 0) | .sn27 => (match z with | .sn0 => 3 | _ => 0) | .sn28 => (match z with | .sn0 => 3 | _ => 0) | .sn29 => (match z with | .sn0 => 6 | _ => 0) | .sn31 => (match z with | .sn0 => 4 | _ => 0) | .sn32 => (match z with | .sn0 => 2 | _ => 0) | .sn33 => (match z with | .sn0 => 2 | _ => 0) | .sn34 => (match z with | .sn0 => 2 | _ => 0) | .sn35 => (match z with | .sn0 => 2 | _ => 0) | .sn36 => (match z with | .sn0 => 2 | _ => 0) | .sn37 => (match z with | .sn0 => 3 | _ => 0) | _ => 0
  | .sn16, y, z => match y with | .sn0 => (match z with | .sn0 => 4 | _ => 0) | _ => 0
  | .sn17, y, z => match y with | .sn0 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn18, y, z => match y with | .sn0 => (match z with | .sn0 => 5 | _ => 0) | _ => 0
  | .sn19, y, z => match y with | .sn0 => (match z with | .sn0 => 3 | _ => 0) | .sn1 => (match z with | .sn0 => 3 | _ => 0) | .sn2 => (match z with | .sn0 => 6 | _ => 0) | .sn3 => (match z with | .sn0 => 6 | _ => 0) | .sn7 => (match z with | .sn0 => 3 | _ => 0) | .sn9 => (match z with | .sn0 => 3 | _ => 0) | .sn11 => (match z with | .sn0 => 6 | _ => 0) | .sn13 => (match z with | .sn0 => 6 | _ => 0) | .sn15 => (match z with | .sn0 => 3 | _ => 0) | _ => 0
  | .sn20, _, _ => 0
  | .sn21, _, _ => 0
  | .sn22, _, _ => 0
  | .sn23, _, _ => 0
  | .sn24, _, _ => 0
  | .sn25, _, _ => 0
  | .sn26, _, _ => 0
  | .sn27, _, _ => 0
  | .sn28, _, _ => 0
  | .sn29, _, _ => 0
  | .sn30, _, _ => 0
  | .sn31, _, _ => 0
  | .sn32, y, z => match y with | .sn0 => (match z with | .sn0 => 3 | _ => 0) | .sn1 => (match z with | .sn0 => 3 | _ => 0) | .sn7 => (match z with | .sn0 => 3 | _ => 0) | .sn9 => (match z with | .sn0 => 3 | _ => 0) | .sn15 => (match z with | .sn0 => 3 | _ => 0) | _ => 0
  | .sn33, _, _ => 0
  | .sn34, _, _ => 0
  | .sn35, _, _ => 0
  | .sn36, y, z => match y with | .sn0 => (match z with | .sn0 => 4 | _ => 0) | .sn1 => (match z with | .sn0 => 4 | _ => 0) | .sn7 => (match z with | .sn0 => 4 | _ => 0) | .sn9 => (match z with | .sn0 => 4 | _ => 0) | .sn15 => (match z with | .sn0 => 4 | _ => 0) | _ => 0
  | .sn37, _, _ => 0
  | .sn38, _, _ => 0

private theorem isS2StateSN_chk : checkAll2_StateSN (fun a b => decide (a ≠ .sn38 → b ≠ .sn38 → isS2StateSN (deltaSN (deltaSN .sn0 a) b) = true)) = true := rfl

private theorem isS2StateSN_intro {a b : StateSN} (ha : a ≠ .sn38) (hb : b ≠ .sn38) :
    isS2StateSN (deltaSN (deltaSN .sn0 a) b) = true :=
  (of_decide_eq_true (checkAll2_StateSN_sound _ isS2StateSN_chk a b)) ha hb

private theorem sn_rk_sub_row_0 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn0 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn0 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn0) b) z))) = true := rfl
private theorem sn_rk_sub_row_1 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn1 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn1 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn1) b) z))) = true := rfl
private theorem sn_rk_sub_row_2 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn2 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn2 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn2) b) z))) = true := rfl
private theorem sn_rk_sub_row_3 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn3 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn3 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn3) b) z))) = true := rfl
private theorem sn_rk_sub_row_4 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn4 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn4 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn4) b) z))) = true := rfl
private theorem sn_rk_sub_row_5 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn5 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn5 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn5) b) z))) = true := rfl
private theorem sn_rk_sub_row_6 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn6 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn6 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn6) b) z))) = true := rfl
private theorem sn_rk_sub_row_7 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn7 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn7 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn7) b) z))) = true := rfl
private theorem sn_rk_sub_row_8 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn8 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn8 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn8) b) z))) = true := rfl
private theorem sn_rk_sub_row_9 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn9 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn9 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn9) b) z))) = true := rfl
private theorem sn_rk_sub_row_10 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn10 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn10 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn10) b) z))) = true := rfl
private theorem sn_rk_sub_row_11 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn11 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn11 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn11) b) z))) = true := rfl
private theorem sn_rk_sub_row_12 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn12 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn12 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn12) b) z))) = true := rfl
private theorem sn_rk_sub_row_13 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn13 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn13 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn13) b) z))) = true := rfl
private theorem sn_rk_sub_row_14 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn14 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn14 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn14) b) z))) = true := rfl
private theorem sn_rk_sub_row_15 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn15 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn15 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn15) b) z))) = true := rfl
private theorem sn_rk_sub_row_16 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn16 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn16 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn16) b) z))) = true := rfl
private theorem sn_rk_sub_row_17 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn17 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn17 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn17) b) z))) = true := rfl
private theorem sn_rk_sub_row_18 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn18 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn18 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn18) b) z))) = true := rfl
private theorem sn_rk_sub_row_19 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn19 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn19 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn19) b) z))) = true := rfl
private theorem sn_rk_sub_row_20 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn20 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn20 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn20) b) z))) = true := rfl
private theorem sn_rk_sub_row_21 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn21 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn21 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn21) b) z))) = true := rfl
private theorem sn_rk_sub_row_22 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn22 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn22 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn22) b) z))) = true := rfl
private theorem sn_rk_sub_row_23 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn23 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn23 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn23) b) z))) = true := rfl
private theorem sn_rk_sub_row_24 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn24 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn24 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn24) b) z))) = true := rfl
private theorem sn_rk_sub_row_25 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn25 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn25 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn25) b) z))) = true := rfl
private theorem sn_rk_sub_row_26 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn26 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn26 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn26) b) z))) = true := rfl
private theorem sn_rk_sub_row_27 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn27 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn27 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn27) b) z))) = true := rfl
private theorem sn_rk_sub_row_28 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn28 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn28 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn28) b) z))) = true := rfl
private theorem sn_rk_sub_row_29 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn29 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn29 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn29) b) z))) = true := rfl
private theorem sn_rk_sub_row_30 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn30 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn30 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn30) b) z))) = true := rfl
private theorem sn_rk_sub_row_31 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn31 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn31 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn31) b) z))) = true := rfl
private theorem sn_rk_sub_row_32 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn32 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn32 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn32) b) z))) = true := rfl
private theorem sn_rk_sub_row_33 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn33 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn33 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn33) b) z))) = true := rfl
private theorem sn_rk_sub_row_34 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn34 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn34 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn34) b) z))) = true := rfl
private theorem sn_rk_sub_row_35 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn35 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn35 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn35) b) z))) = true := rfl
private theorem sn_rk_sub_row_36 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn36 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn36 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn36) b) z))) = true := rfl
private theorem sn_rk_sub_row_37 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn37 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn37 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn37) b) z))) = true := rfl
private theorem sn_rk_sub_row_38 : checkAll2_StateSN (fun b z => (!decide (StateSN.sn38 ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN .sn38 b z) (maxSubRankSN (deltaSN (deltaSN .sn0 .sn38) b) z))) = true := rfl

private theorem tripleRankSN_le_maxSub {a b z : StateSN} (ha : a ≠ .sn38) (hb : b ≠ .sn38) :
    tripleRankSN a b z ≤ maxSubRankSN (deltaSN (deltaSN .sn0 a) b) z := by
  have h : (!decide (a ≠ .sn38) || !decide (b ≠ .sn38) || natBle (tripleRankSN a b z) (maxSubRankSN (deltaSN (deltaSN .sn0 a) b) z)) = true :=
    match a with
    | .sn0 => checkAll2_StateSN_sound _ sn_rk_sub_row_0 b z
    | .sn1 => checkAll2_StateSN_sound _ sn_rk_sub_row_1 b z
    | .sn2 => checkAll2_StateSN_sound _ sn_rk_sub_row_2 b z
    | .sn3 => checkAll2_StateSN_sound _ sn_rk_sub_row_3 b z
    | .sn4 => checkAll2_StateSN_sound _ sn_rk_sub_row_4 b z
    | .sn5 => checkAll2_StateSN_sound _ sn_rk_sub_row_5 b z
    | .sn6 => checkAll2_StateSN_sound _ sn_rk_sub_row_6 b z
    | .sn7 => checkAll2_StateSN_sound _ sn_rk_sub_row_7 b z
    | .sn8 => checkAll2_StateSN_sound _ sn_rk_sub_row_8 b z
    | .sn9 => checkAll2_StateSN_sound _ sn_rk_sub_row_9 b z
    | .sn10 => checkAll2_StateSN_sound _ sn_rk_sub_row_10 b z
    | .sn11 => checkAll2_StateSN_sound _ sn_rk_sub_row_11 b z
    | .sn12 => checkAll2_StateSN_sound _ sn_rk_sub_row_12 b z
    | .sn13 => checkAll2_StateSN_sound _ sn_rk_sub_row_13 b z
    | .sn14 => checkAll2_StateSN_sound _ sn_rk_sub_row_14 b z
    | .sn15 => checkAll2_StateSN_sound _ sn_rk_sub_row_15 b z
    | .sn16 => checkAll2_StateSN_sound _ sn_rk_sub_row_16 b z
    | .sn17 => checkAll2_StateSN_sound _ sn_rk_sub_row_17 b z
    | .sn18 => checkAll2_StateSN_sound _ sn_rk_sub_row_18 b z
    | .sn19 => checkAll2_StateSN_sound _ sn_rk_sub_row_19 b z
    | .sn20 => checkAll2_StateSN_sound _ sn_rk_sub_row_20 b z
    | .sn21 => checkAll2_StateSN_sound _ sn_rk_sub_row_21 b z
    | .sn22 => checkAll2_StateSN_sound _ sn_rk_sub_row_22 b z
    | .sn23 => checkAll2_StateSN_sound _ sn_rk_sub_row_23 b z
    | .sn24 => checkAll2_StateSN_sound _ sn_rk_sub_row_24 b z
    | .sn25 => checkAll2_StateSN_sound _ sn_rk_sub_row_25 b z
    | .sn26 => checkAll2_StateSN_sound _ sn_rk_sub_row_26 b z
    | .sn27 => checkAll2_StateSN_sound _ sn_rk_sub_row_27 b z
    | .sn28 => checkAll2_StateSN_sound _ sn_rk_sub_row_28 b z
    | .sn29 => checkAll2_StateSN_sound _ sn_rk_sub_row_29 b z
    | .sn30 => checkAll2_StateSN_sound _ sn_rk_sub_row_30 b z
    | .sn31 => checkAll2_StateSN_sound _ sn_rk_sub_row_31 b z
    | .sn32 => checkAll2_StateSN_sound _ sn_rk_sub_row_32 b z
    | .sn33 => checkAll2_StateSN_sound _ sn_rk_sub_row_33 b z
    | .sn34 => checkAll2_StateSN_sound _ sn_rk_sub_row_34 b z
    | .sn35 => checkAll2_StateSN_sound _ sn_rk_sub_row_35 b z
    | .sn36 => checkAll2_StateSN_sound _ sn_rk_sub_row_36 b z
    | .sn37 => checkAll2_StateSN_sound _ sn_rk_sub_row_37 b z
    | .sn38 => checkAll2_StateSN_sound _ sn_rk_sub_row_38 b z
  rw [decide_eq_true ha, decide_eq_true hb] at h
  exact natBle_sound h

private theorem sn_rk_main_row_0 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn0) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn0 y z) && natBle (maxSubRankSN .sn0 z) (tripleRankSN .sn0 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn0 y z) && (!isS2StateSN .sn0 || natBle (maxSubRankSN (deltaSN .sn0 z) (deltaSN y z) + 1) (tripleRankSN .sn0 y z)))))) = true := rfl
private theorem sn_rk_main_row_1 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn1) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn1 y z) && natBle (maxSubRankSN .sn1 z) (tripleRankSN .sn1 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn1 y z) && (!isS2StateSN .sn1 || natBle (maxSubRankSN (deltaSN .sn1 z) (deltaSN y z) + 1) (tripleRankSN .sn1 y z)))))) = true := rfl
private theorem sn_rk_main_row_2 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn2) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn2 y z) && natBle (maxSubRankSN .sn2 z) (tripleRankSN .sn2 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn2 y z) && (!isS2StateSN .sn2 || natBle (maxSubRankSN (deltaSN .sn2 z) (deltaSN y z) + 1) (tripleRankSN .sn2 y z)))))) = true := rfl
private theorem sn_rk_main_row_3 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn3) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn3 y z) && natBle (maxSubRankSN .sn3 z) (tripleRankSN .sn3 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn3 y z) && (!isS2StateSN .sn3 || natBle (maxSubRankSN (deltaSN .sn3 z) (deltaSN y z) + 1) (tripleRankSN .sn3 y z)))))) = true := rfl
private theorem sn_rk_main_row_4 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn4) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn4 y z) && natBle (maxSubRankSN .sn4 z) (tripleRankSN .sn4 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn4 y z) && (!isS2StateSN .sn4 || natBle (maxSubRankSN (deltaSN .sn4 z) (deltaSN y z) + 1) (tripleRankSN .sn4 y z)))))) = true := rfl
private theorem sn_rk_main_row_5 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn5) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn5 y z) && natBle (maxSubRankSN .sn5 z) (tripleRankSN .sn5 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn5 y z) && (!isS2StateSN .sn5 || natBle (maxSubRankSN (deltaSN .sn5 z) (deltaSN y z) + 1) (tripleRankSN .sn5 y z)))))) = true := rfl
private theorem sn_rk_main_row_6 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn6) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn6 y z) && natBle (maxSubRankSN .sn6 z) (tripleRankSN .sn6 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn6 y z) && (!isS2StateSN .sn6 || natBle (maxSubRankSN (deltaSN .sn6 z) (deltaSN y z) + 1) (tripleRankSN .sn6 y z)))))) = true := rfl
private theorem sn_rk_main_row_7 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn7) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn7 y z) && natBle (maxSubRankSN .sn7 z) (tripleRankSN .sn7 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn7 y z) && (!isS2StateSN .sn7 || natBle (maxSubRankSN (deltaSN .sn7 z) (deltaSN y z) + 1) (tripleRankSN .sn7 y z)))))) = true := rfl
private theorem sn_rk_main_row_8 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn8) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn8 y z) && natBle (maxSubRankSN .sn8 z) (tripleRankSN .sn8 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn8 y z) && (!isS2StateSN .sn8 || natBle (maxSubRankSN (deltaSN .sn8 z) (deltaSN y z) + 1) (tripleRankSN .sn8 y z)))))) = true := rfl
private theorem sn_rk_main_row_9 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn9) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn9 y z) && natBle (maxSubRankSN .sn9 z) (tripleRankSN .sn9 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn9 y z) && (!isS2StateSN .sn9 || natBle (maxSubRankSN (deltaSN .sn9 z) (deltaSN y z) + 1) (tripleRankSN .sn9 y z)))))) = true := rfl
private theorem sn_rk_main_row_10 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn10) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn10 y z) && natBle (maxSubRankSN .sn10 z) (tripleRankSN .sn10 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn10 y z) && (!isS2StateSN .sn10 || natBle (maxSubRankSN (deltaSN .sn10 z) (deltaSN y z) + 1) (tripleRankSN .sn10 y z)))))) = true := rfl
private theorem sn_rk_main_row_11 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn11) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn11 y z) && natBle (maxSubRankSN .sn11 z) (tripleRankSN .sn11 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn11 y z) && (!isS2StateSN .sn11 || natBle (maxSubRankSN (deltaSN .sn11 z) (deltaSN y z) + 1) (tripleRankSN .sn11 y z)))))) = true := rfl
private theorem sn_rk_main_row_12 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn12) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn12 y z) && natBle (maxSubRankSN .sn12 z) (tripleRankSN .sn12 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn12 y z) && (!isS2StateSN .sn12 || natBle (maxSubRankSN (deltaSN .sn12 z) (deltaSN y z) + 1) (tripleRankSN .sn12 y z)))))) = true := rfl
private theorem sn_rk_main_row_13 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn13) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn13 y z) && natBle (maxSubRankSN .sn13 z) (tripleRankSN .sn13 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn13 y z) && (!isS2StateSN .sn13 || natBle (maxSubRankSN (deltaSN .sn13 z) (deltaSN y z) + 1) (tripleRankSN .sn13 y z)))))) = true := rfl
private theorem sn_rk_main_row_14 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn14) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn14 y z) && natBle (maxSubRankSN .sn14 z) (tripleRankSN .sn14 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn14 y z) && (!isS2StateSN .sn14 || natBle (maxSubRankSN (deltaSN .sn14 z) (deltaSN y z) + 1) (tripleRankSN .sn14 y z)))))) = true := rfl
private theorem sn_rk_main_row_15 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn15) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn15 y z) && natBle (maxSubRankSN .sn15 z) (tripleRankSN .sn15 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn15 y z) && (!isS2StateSN .sn15 || natBle (maxSubRankSN (deltaSN .sn15 z) (deltaSN y z) + 1) (tripleRankSN .sn15 y z)))))) = true := rfl
private theorem sn_rk_main_row_16 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn16) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn16 y z) && natBle (maxSubRankSN .sn16 z) (tripleRankSN .sn16 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn16 y z) && (!isS2StateSN .sn16 || natBle (maxSubRankSN (deltaSN .sn16 z) (deltaSN y z) + 1) (tripleRankSN .sn16 y z)))))) = true := rfl
private theorem sn_rk_main_row_17 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn17) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn17 y z) && natBle (maxSubRankSN .sn17 z) (tripleRankSN .sn17 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn17 y z) && (!isS2StateSN .sn17 || natBle (maxSubRankSN (deltaSN .sn17 z) (deltaSN y z) + 1) (tripleRankSN .sn17 y z)))))) = true := rfl
private theorem sn_rk_main_row_18 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn18) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn18 y z) && natBle (maxSubRankSN .sn18 z) (tripleRankSN .sn18 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn18 y z) && (!isS2StateSN .sn18 || natBle (maxSubRankSN (deltaSN .sn18 z) (deltaSN y z) + 1) (tripleRankSN .sn18 y z)))))) = true := rfl
private theorem sn_rk_main_row_19 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn19) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn19 y z) && natBle (maxSubRankSN .sn19 z) (tripleRankSN .sn19 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn19 y z) && (!isS2StateSN .sn19 || natBle (maxSubRankSN (deltaSN .sn19 z) (deltaSN y z) + 1) (tripleRankSN .sn19 y z)))))) = true := rfl
private theorem sn_rk_main_row_20 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn20) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn20 y z) && natBle (maxSubRankSN .sn20 z) (tripleRankSN .sn20 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn20 y z) && (!isS2StateSN .sn20 || natBle (maxSubRankSN (deltaSN .sn20 z) (deltaSN y z) + 1) (tripleRankSN .sn20 y z)))))) = true := rfl
private theorem sn_rk_main_row_21 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn21) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn21 y z) && natBle (maxSubRankSN .sn21 z) (tripleRankSN .sn21 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn21 y z) && (!isS2StateSN .sn21 || natBle (maxSubRankSN (deltaSN .sn21 z) (deltaSN y z) + 1) (tripleRankSN .sn21 y z)))))) = true := rfl
private theorem sn_rk_main_row_22 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn22) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn22 y z) && natBle (maxSubRankSN .sn22 z) (tripleRankSN .sn22 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn22 y z) && (!isS2StateSN .sn22 || natBle (maxSubRankSN (deltaSN .sn22 z) (deltaSN y z) + 1) (tripleRankSN .sn22 y z)))))) = true := rfl
private theorem sn_rk_main_row_23 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn23) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn23 y z) && natBle (maxSubRankSN .sn23 z) (tripleRankSN .sn23 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn23 y z) && (!isS2StateSN .sn23 || natBle (maxSubRankSN (deltaSN .sn23 z) (deltaSN y z) + 1) (tripleRankSN .sn23 y z)))))) = true := rfl
private theorem sn_rk_main_row_24 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn24) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn24 y z) && natBle (maxSubRankSN .sn24 z) (tripleRankSN .sn24 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn24 y z) && (!isS2StateSN .sn24 || natBle (maxSubRankSN (deltaSN .sn24 z) (deltaSN y z) + 1) (tripleRankSN .sn24 y z)))))) = true := rfl
private theorem sn_rk_main_row_25 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn25) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn25 y z) && natBle (maxSubRankSN .sn25 z) (tripleRankSN .sn25 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn25 y z) && (!isS2StateSN .sn25 || natBle (maxSubRankSN (deltaSN .sn25 z) (deltaSN y z) + 1) (tripleRankSN .sn25 y z)))))) = true := rfl
private theorem sn_rk_main_row_26 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn26) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn26 y z) && natBle (maxSubRankSN .sn26 z) (tripleRankSN .sn26 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn26 y z) && (!isS2StateSN .sn26 || natBle (maxSubRankSN (deltaSN .sn26 z) (deltaSN y z) + 1) (tripleRankSN .sn26 y z)))))) = true := rfl
private theorem sn_rk_main_row_27 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn27) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn27 y z) && natBle (maxSubRankSN .sn27 z) (tripleRankSN .sn27 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn27 y z) && (!isS2StateSN .sn27 || natBle (maxSubRankSN (deltaSN .sn27 z) (deltaSN y z) + 1) (tripleRankSN .sn27 y z)))))) = true := rfl
private theorem sn_rk_main_row_28 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn28) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn28 y z) && natBle (maxSubRankSN .sn28 z) (tripleRankSN .sn28 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn28 y z) && (!isS2StateSN .sn28 || natBle (maxSubRankSN (deltaSN .sn28 z) (deltaSN y z) + 1) (tripleRankSN .sn28 y z)))))) = true := rfl
private theorem sn_rk_main_row_29 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn29) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn29 y z) && natBle (maxSubRankSN .sn29 z) (tripleRankSN .sn29 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn29 y z) && (!isS2StateSN .sn29 || natBle (maxSubRankSN (deltaSN .sn29 z) (deltaSN y z) + 1) (tripleRankSN .sn29 y z)))))) = true := rfl
private theorem sn_rk_main_row_30 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn30) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn30 y z) && natBle (maxSubRankSN .sn30 z) (tripleRankSN .sn30 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn30 y z) && (!isS2StateSN .sn30 || natBle (maxSubRankSN (deltaSN .sn30 z) (deltaSN y z) + 1) (tripleRankSN .sn30 y z)))))) = true := rfl
private theorem sn_rk_main_row_31 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn31) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn31 y z) && natBle (maxSubRankSN .sn31 z) (tripleRankSN .sn31 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn31 y z) && (!isS2StateSN .sn31 || natBle (maxSubRankSN (deltaSN .sn31 z) (deltaSN y z) + 1) (tripleRankSN .sn31 y z)))))) = true := rfl
private theorem sn_rk_main_row_32 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn32) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn32 y z) && natBle (maxSubRankSN .sn32 z) (tripleRankSN .sn32 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn32 y z) && (!isS2StateSN .sn32 || natBle (maxSubRankSN (deltaSN .sn32 z) (deltaSN y z) + 1) (tripleRankSN .sn32 y z)))))) = true := rfl
private theorem sn_rk_main_row_33 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn33) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn33 y z) && natBle (maxSubRankSN .sn33 z) (tripleRankSN .sn33 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn33 y z) && (!isS2StateSN .sn33 || natBle (maxSubRankSN (deltaSN .sn33 z) (deltaSN y z) + 1) (tripleRankSN .sn33 y z)))))) = true := rfl
private theorem sn_rk_main_row_34 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn34) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn34 y z) && natBle (maxSubRankSN .sn34 z) (tripleRankSN .sn34 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn34 y z) && (!isS2StateSN .sn34 || natBle (maxSubRankSN (deltaSN .sn34 z) (deltaSN y z) + 1) (tripleRankSN .sn34 y z)))))) = true := rfl
private theorem sn_rk_main_row_35 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn35) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn35 y z) && natBle (maxSubRankSN .sn35 z) (tripleRankSN .sn35 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn35 y z) && (!isS2StateSN .sn35 || natBle (maxSubRankSN (deltaSN .sn35 z) (deltaSN y z) + 1) (tripleRankSN .sn35 y z)))))) = true := rfl
private theorem sn_rk_main_row_36 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn36) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn36 y z) && natBle (maxSubRankSN .sn36 z) (tripleRankSN .sn36 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn36 y z) && (!isS2StateSN .sn36 || natBle (maxSubRankSN (deltaSN .sn36 z) (deltaSN y z) + 1) (tripleRankSN .sn36 y z)))))) = true := rfl
private theorem sn_rk_main_row_37 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn37) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn37 y z) && natBle (maxSubRankSN .sn37 z) (tripleRankSN .sn37 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn37 y z) && (!isS2StateSN .sn37 || natBle (maxSubRankSN (deltaSN .sn37 z) (deltaSN y z) + 1) (tripleRankSN .sn37 y z)))))) = true := rfl
private theorem sn_rk_main_row_38 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 .sn38) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN .sn38 y z) && natBle (maxSubRankSN .sn38 z) (tripleRankSN .sn38 y z)) && (natBle (maxSubRankSN y z) (tripleRankSN .sn38 y z) && (!isS2StateSN .sn38 || natBle (maxSubRankSN (deltaSN .sn38 z) (deltaSN y z) + 1) (tripleRankSN .sn38 y z)))))) = true := rfl

private theorem tripleRankSN_main_bounds {x y z : StateSN}
    (hvalid : deltaSN (deltaSN (deltaSN .sn0 x) y) z ≠ .sn38) :
    1 ≤ tripleRankSN x y z ∧
    maxSubRankSN x z ≤ tripleRankSN x y z ∧
    maxSubRankSN y z ≤ tripleRankSN x y z ∧
    (isS2StateSN x = true → maxSubRankSN (deltaSN x z) (deltaSN y z) < tripleRankSN x y z) := by
  have h : (!decide (deltaSN (deltaSN (deltaSN .sn0 x) y) z ≠ .sn38) || ((natBle 1 (tripleRankSN x y z) && natBle (maxSubRankSN x z) (tripleRankSN x y z)) && (natBle (maxSubRankSN y z) (tripleRankSN x y z) && (!isS2StateSN x || natBle (maxSubRankSN (deltaSN x z) (deltaSN y z) + 1) (tripleRankSN x y z))))) = true :=
    match x with
    | .sn0 => checkAll2_StateSN_sound _ sn_rk_main_row_0 y z
    | .sn1 => checkAll2_StateSN_sound _ sn_rk_main_row_1 y z
    | .sn2 => checkAll2_StateSN_sound _ sn_rk_main_row_2 y z
    | .sn3 => checkAll2_StateSN_sound _ sn_rk_main_row_3 y z
    | .sn4 => checkAll2_StateSN_sound _ sn_rk_main_row_4 y z
    | .sn5 => checkAll2_StateSN_sound _ sn_rk_main_row_5 y z
    | .sn6 => checkAll2_StateSN_sound _ sn_rk_main_row_6 y z
    | .sn7 => checkAll2_StateSN_sound _ sn_rk_main_row_7 y z
    | .sn8 => checkAll2_StateSN_sound _ sn_rk_main_row_8 y z
    | .sn9 => checkAll2_StateSN_sound _ sn_rk_main_row_9 y z
    | .sn10 => checkAll2_StateSN_sound _ sn_rk_main_row_10 y z
    | .sn11 => checkAll2_StateSN_sound _ sn_rk_main_row_11 y z
    | .sn12 => checkAll2_StateSN_sound _ sn_rk_main_row_12 y z
    | .sn13 => checkAll2_StateSN_sound _ sn_rk_main_row_13 y z
    | .sn14 => checkAll2_StateSN_sound _ sn_rk_main_row_14 y z
    | .sn15 => checkAll2_StateSN_sound _ sn_rk_main_row_15 y z
    | .sn16 => checkAll2_StateSN_sound _ sn_rk_main_row_16 y z
    | .sn17 => checkAll2_StateSN_sound _ sn_rk_main_row_17 y z
    | .sn18 => checkAll2_StateSN_sound _ sn_rk_main_row_18 y z
    | .sn19 => checkAll2_StateSN_sound _ sn_rk_main_row_19 y z
    | .sn20 => checkAll2_StateSN_sound _ sn_rk_main_row_20 y z
    | .sn21 => checkAll2_StateSN_sound _ sn_rk_main_row_21 y z
    | .sn22 => checkAll2_StateSN_sound _ sn_rk_main_row_22 y z
    | .sn23 => checkAll2_StateSN_sound _ sn_rk_main_row_23 y z
    | .sn24 => checkAll2_StateSN_sound _ sn_rk_main_row_24 y z
    | .sn25 => checkAll2_StateSN_sound _ sn_rk_main_row_25 y z
    | .sn26 => checkAll2_StateSN_sound _ sn_rk_main_row_26 y z
    | .sn27 => checkAll2_StateSN_sound _ sn_rk_main_row_27 y z
    | .sn28 => checkAll2_StateSN_sound _ sn_rk_main_row_28 y z
    | .sn29 => checkAll2_StateSN_sound _ sn_rk_main_row_29 y z
    | .sn30 => checkAll2_StateSN_sound _ sn_rk_main_row_30 y z
    | .sn31 => checkAll2_StateSN_sound _ sn_rk_main_row_31 y z
    | .sn32 => checkAll2_StateSN_sound _ sn_rk_main_row_32 y z
    | .sn33 => checkAll2_StateSN_sound _ sn_rk_main_row_33 y z
    | .sn34 => checkAll2_StateSN_sound _ sn_rk_main_row_34 y z
    | .sn35 => checkAll2_StateSN_sound _ sn_rk_main_row_35 y z
    | .sn36 => checkAll2_StateSN_sound _ sn_rk_main_row_36 y z
    | .sn37 => checkAll2_StateSN_sound _ sn_rk_main_row_37 y z
    | .sn38 => checkAll2_StateSN_sound _ sn_rk_main_row_38 y z
  have h' := imp_decide hvalid h
  have hL := and_left h'
  have hR := and_right h'
  refine ⟨natBle_sound (and_left hL), natBle_sound (and_right hL), natBle_sound (and_left hR), fun hs2 => ?_⟩
  exact natBle_sound (imp_bool hs2 (and_right hR))

private theorem sn_rk_s1_row_0 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn0)) y) z ≠ .sn38) || natBle (tripleRankSN .sn0 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn0) y z))) = true := rfl
private theorem sn_rk_s1_row_1 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn1)) y) z ≠ .sn38) || natBle (tripleRankSN .sn1 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn1) y z))) = true := rfl
private theorem sn_rk_s1_row_2 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn2)) y) z ≠ .sn38) || natBle (tripleRankSN .sn2 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn2) y z))) = true := rfl
private theorem sn_rk_s1_row_3 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn3)) y) z ≠ .sn38) || natBle (tripleRankSN .sn3 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn3) y z))) = true := rfl
private theorem sn_rk_s1_row_4 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn4)) y) z ≠ .sn38) || natBle (tripleRankSN .sn4 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn4) y z))) = true := rfl
private theorem sn_rk_s1_row_5 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn5)) y) z ≠ .sn38) || natBle (tripleRankSN .sn5 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn5) y z))) = true := rfl
private theorem sn_rk_s1_row_6 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn6)) y) z ≠ .sn38) || natBle (tripleRankSN .sn6 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn6) y z))) = true := rfl
private theorem sn_rk_s1_row_7 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn7)) y) z ≠ .sn38) || natBle (tripleRankSN .sn7 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn7) y z))) = true := rfl
private theorem sn_rk_s1_row_8 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn8)) y) z ≠ .sn38) || natBle (tripleRankSN .sn8 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn8) y z))) = true := rfl
private theorem sn_rk_s1_row_9 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn9)) y) z ≠ .sn38) || natBle (tripleRankSN .sn9 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn9) y z))) = true := rfl
private theorem sn_rk_s1_row_10 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn10)) y) z ≠ .sn38) || natBle (tripleRankSN .sn10 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn10) y z))) = true := rfl
private theorem sn_rk_s1_row_11 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn11)) y) z ≠ .sn38) || natBle (tripleRankSN .sn11 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn11) y z))) = true := rfl
private theorem sn_rk_s1_row_12 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn12)) y) z ≠ .sn38) || natBle (tripleRankSN .sn12 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn12) y z))) = true := rfl
private theorem sn_rk_s1_row_13 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn13)) y) z ≠ .sn38) || natBle (tripleRankSN .sn13 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn13) y z))) = true := rfl
private theorem sn_rk_s1_row_14 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn14)) y) z ≠ .sn38) || natBle (tripleRankSN .sn14 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn14) y z))) = true := rfl
private theorem sn_rk_s1_row_15 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn15)) y) z ≠ .sn38) || natBle (tripleRankSN .sn15 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn15) y z))) = true := rfl
private theorem sn_rk_s1_row_16 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn16)) y) z ≠ .sn38) || natBle (tripleRankSN .sn16 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn16) y z))) = true := rfl
private theorem sn_rk_s1_row_17 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn17)) y) z ≠ .sn38) || natBle (tripleRankSN .sn17 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn17) y z))) = true := rfl
private theorem sn_rk_s1_row_18 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn18)) y) z ≠ .sn38) || natBle (tripleRankSN .sn18 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn18) y z))) = true := rfl
private theorem sn_rk_s1_row_19 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn19)) y) z ≠ .sn38) || natBle (tripleRankSN .sn19 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn19) y z))) = true := rfl
private theorem sn_rk_s1_row_20 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn20)) y) z ≠ .sn38) || natBle (tripleRankSN .sn20 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn20) y z))) = true := rfl
private theorem sn_rk_s1_row_21 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn21)) y) z ≠ .sn38) || natBle (tripleRankSN .sn21 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn21) y z))) = true := rfl
private theorem sn_rk_s1_row_22 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn22)) y) z ≠ .sn38) || natBle (tripleRankSN .sn22 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn22) y z))) = true := rfl
private theorem sn_rk_s1_row_23 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn23)) y) z ≠ .sn38) || natBle (tripleRankSN .sn23 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn23) y z))) = true := rfl
private theorem sn_rk_s1_row_24 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn24)) y) z ≠ .sn38) || natBle (tripleRankSN .sn24 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn24) y z))) = true := rfl
private theorem sn_rk_s1_row_25 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn25)) y) z ≠ .sn38) || natBle (tripleRankSN .sn25 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn25) y z))) = true := rfl
private theorem sn_rk_s1_row_26 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn26)) y) z ≠ .sn38) || natBle (tripleRankSN .sn26 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn26) y z))) = true := rfl
private theorem sn_rk_s1_row_27 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn27)) y) z ≠ .sn38) || natBle (tripleRankSN .sn27 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn27) y z))) = true := rfl
private theorem sn_rk_s1_row_28 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn28)) y) z ≠ .sn38) || natBle (tripleRankSN .sn28 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn28) y z))) = true := rfl
private theorem sn_rk_s1_row_29 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn29)) y) z ≠ .sn38) || natBle (tripleRankSN .sn29 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn29) y z))) = true := rfl
private theorem sn_rk_s1_row_30 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn30)) y) z ≠ .sn38) || natBle (tripleRankSN .sn30 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn30) y z))) = true := rfl
private theorem sn_rk_s1_row_31 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn31)) y) z ≠ .sn38) || natBle (tripleRankSN .sn31 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn31) y z))) = true := rfl
private theorem sn_rk_s1_row_32 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn32)) y) z ≠ .sn38) || natBle (tripleRankSN .sn32 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn32) y z))) = true := rfl
private theorem sn_rk_s1_row_33 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn33)) y) z ≠ .sn38) || natBle (tripleRankSN .sn33 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn33) y z))) = true := rfl
private theorem sn_rk_s1_row_34 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn34)) y) z ≠ .sn38) || natBle (tripleRankSN .sn34 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn34) y z))) = true := rfl
private theorem sn_rk_s1_row_35 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn35)) y) z ≠ .sn38) || natBle (tripleRankSN .sn35 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn35) y z))) = true := rfl
private theorem sn_rk_s1_row_36 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn36)) y) z ≠ .sn38) || natBle (tripleRankSN .sn36 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn36) y z))) = true := rfl
private theorem sn_rk_s1_row_37 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn37)) y) z ≠ .sn38) || natBle (tripleRankSN .sn37 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn37) y z))) = true := rfl
private theorem sn_rk_s1_row_38 : checkAll2_StateSN (fun y z => (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 .sn38)) y) z ≠ .sn38) || natBle (tripleRankSN .sn38 z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 .sn38) y z))) = true := rfl

private theorem tripleRankSN_s1_lt {u y z : StateSN}
    (hvalid : deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 u)) y) z ≠ .sn38) :
    tripleRankSN u z (deltaSN y z) < tripleRankSN (deltaSN .sn0 u) y z := by
  have h : (!decide (deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 u)) y) z ≠ .sn38) || natBle (tripleRankSN u z (deltaSN y z) + 1) (tripleRankSN (deltaSN .sn0 u) y z)) = true :=
    match u with
    | .sn0 => checkAll2_StateSN_sound _ sn_rk_s1_row_0 y z
    | .sn1 => checkAll2_StateSN_sound _ sn_rk_s1_row_1 y z
    | .sn2 => checkAll2_StateSN_sound _ sn_rk_s1_row_2 y z
    | .sn3 => checkAll2_StateSN_sound _ sn_rk_s1_row_3 y z
    | .sn4 => checkAll2_StateSN_sound _ sn_rk_s1_row_4 y z
    | .sn5 => checkAll2_StateSN_sound _ sn_rk_s1_row_5 y z
    | .sn6 => checkAll2_StateSN_sound _ sn_rk_s1_row_6 y z
    | .sn7 => checkAll2_StateSN_sound _ sn_rk_s1_row_7 y z
    | .sn8 => checkAll2_StateSN_sound _ sn_rk_s1_row_8 y z
    | .sn9 => checkAll2_StateSN_sound _ sn_rk_s1_row_9 y z
    | .sn10 => checkAll2_StateSN_sound _ sn_rk_s1_row_10 y z
    | .sn11 => checkAll2_StateSN_sound _ sn_rk_s1_row_11 y z
    | .sn12 => checkAll2_StateSN_sound _ sn_rk_s1_row_12 y z
    | .sn13 => checkAll2_StateSN_sound _ sn_rk_s1_row_13 y z
    | .sn14 => checkAll2_StateSN_sound _ sn_rk_s1_row_14 y z
    | .sn15 => checkAll2_StateSN_sound _ sn_rk_s1_row_15 y z
    | .sn16 => checkAll2_StateSN_sound _ sn_rk_s1_row_16 y z
    | .sn17 => checkAll2_StateSN_sound _ sn_rk_s1_row_17 y z
    | .sn18 => checkAll2_StateSN_sound _ sn_rk_s1_row_18 y z
    | .sn19 => checkAll2_StateSN_sound _ sn_rk_s1_row_19 y z
    | .sn20 => checkAll2_StateSN_sound _ sn_rk_s1_row_20 y z
    | .sn21 => checkAll2_StateSN_sound _ sn_rk_s1_row_21 y z
    | .sn22 => checkAll2_StateSN_sound _ sn_rk_s1_row_22 y z
    | .sn23 => checkAll2_StateSN_sound _ sn_rk_s1_row_23 y z
    | .sn24 => checkAll2_StateSN_sound _ sn_rk_s1_row_24 y z
    | .sn25 => checkAll2_StateSN_sound _ sn_rk_s1_row_25 y z
    | .sn26 => checkAll2_StateSN_sound _ sn_rk_s1_row_26 y z
    | .sn27 => checkAll2_StateSN_sound _ sn_rk_s1_row_27 y z
    | .sn28 => checkAll2_StateSN_sound _ sn_rk_s1_row_28 y z
    | .sn29 => checkAll2_StateSN_sound _ sn_rk_s1_row_29 y z
    | .sn30 => checkAll2_StateSN_sound _ sn_rk_s1_row_30 y z
    | .sn31 => checkAll2_StateSN_sound _ sn_rk_s1_row_31 y z
    | .sn32 => checkAll2_StateSN_sound _ sn_rk_s1_row_32 y z
    | .sn33 => checkAll2_StateSN_sound _ sn_rk_s1_row_33 y z
    | .sn34 => checkAll2_StateSN_sound _ sn_rk_s1_row_34 y z
    | .sn35 => checkAll2_StateSN_sound _ sn_rk_s1_row_35 y z
    | .sn36 => checkAll2_StateSN_sound _ sn_rk_s1_row_36 y z
    | .sn37 => checkAll2_StateSN_sound _ sn_rk_s1_row_37 y z
    | .sn38 => checkAll2_StateSN_sound _ sn_rk_s1_row_38 y z
  exact natBle_sound (imp_decide hvalid h)

/-- Closed Normal Forms of `CL(S)` (`S`, `S ⋅ X`, `S ⋅ X ⋅ Y`). -/
inductive CNF where
  | s : CNF
  | s1 : CNF → CNF
  | s2 : CNF → CNF → CNF
  deriving DecidableEq, Repr

def CNF.toTerm : CNF → Term
  | .s => S
  | .s1 x => S ⋅ x.toTerm
  | .s2 x y => S ⋅ x.toTerm ⋅ y.toTerm

def CNF.size : CNF → Nat
  | .s => 1
  | .s1 x => 1 + x.size
  | .s2 x y => 1 + x.size + y.size

theorem CNF.size_pos (c : CNF) : 1 ≤ c.size := by
  cases c with
  | s => exact Nat.le_refl 1
  | s1 x => exact Nat.le_add_right 1 x.size
  | s2 x y =>
    rw [CNF.size, Nat.add_assoc 1 x.size y.size]
    exact Nat.le_add_right 1 (x.size + y.size)

theorem CNF.noVars_toTerm (c : CNF) : noVars c.toTerm = true := by
  induction c with
  | s => rfl
  | s1 x ihx => exact ihx
  | s2 x y ihx ihy => exact (Bool.and_eq_true _ _).mpr ⟨ihx, ihy⟩

theorem CNF.isNormalForm_toTerm (c : CNF) : IsNormalForm c.toTerm := by
  induction c with
  | s => intro _ hs; cases hs
  | s1 x ihx =>
    intro _ hs
    cases hs with
    | left hl => cases hl
    | right hr => exact ihx _ hr
  | s2 x y ihx ihy =>
    intro _ hs
    cases hs with
    | left hl =>
      cases hl with
      | left hll => cases hll
      | right hlr => exact ihx _ hlr
    | right hr => exact ihy _ hr

theorem CNF.evalSN_ne_sn38 (c : CNF) : evalSN c.toTerm ≠ .sn38 :=
  closed_nf_evalSN_ne_sn38 c.noVars_toTerm c.isNormalForm_toTerm

def cnfCallRank (f z : CNF) : Nat :=
  match f with
  | .s => 0
  | .s1 _ => 0
  | .s2 x y => tripleRankSN (evalSN x.toTerm) (evalSN y.toTerm) (evalSN z.toTerm)

private theorem cnf_callRank_le_maxSub (f z : CNF) :
    cnfCallRank f z ≤ maxSubRankSN (evalSN f.toTerm) (evalSN z.toTerm) := by
  cases f with
  | s => exact Nat.zero_le _
  | s1 _ => exact Nat.zero_le _
  | s2 x y =>
    exact tripleRankSN_le_maxSub x.evalSN_ne_sn38 y.evalSN_ne_sn38

private theorem cnf_apply_aux :
    ∀ (rk sz : Nat) (f z : CNF),
      evalSN (f.toTerm ⋅ z.toTerm) ≠ .sn38 →
      cnfCallRank f z ≤ rk →
      f.size ≤ sz →
      ∃ res : CNF, Reduces (f.toTerm ⋅ z.toTerm) res.toTerm ∧
        (f = .s → res = .s1 z) ∧
        (∀ u, f = .s1 u → res = .s2 u z) := by
  intro rk
  induction rk with
  | zero =>
    intro sz f z hval hrk _
    cases f with
    | s => exact ⟨.s1 z, Reduces.refl _, fun _ => rfl, fun _ h => (by cases h)⟩
    | s1 u => exact ⟨.s2 u z, Reduces.refl _, fun h => (by cases h), fun u' h => (by injection h with hu; subst hu; rfl)⟩
    | s2 x y =>
      have ⟨hpos, _, _, _⟩ := tripleRankSN_main_bounds hval
      exfalso
      exact Nat.not_succ_le_zero 0 (Nat.le_trans hpos hrk)
  | succ rk ihrk =>
    intro sz
    induction sz with
    | zero =>
      intro f _ _ _ hsz
      exfalso
      exact Nat.not_succ_le_zero 0 (Nat.le_trans f.size_pos hsz)
    | succ sz ihsz =>
      intro f z hval hrk hsz
      cases f with
      | s => exact ⟨.s1 z, Reduces.refl _, fun _ => rfl, fun _ h => (by cases h)⟩
      | s1 u => exact ⟨.s2 u z, Reduces.refl _, fun h => (by cases h), fun u' h => (by injection h with hu; subst hu; rfl)⟩
      | s2 x y =>
        have hval_rhs : evalSN ((x.toTerm ⋅ z.toTerm) ⋅ (y.toTerm ⋅ z.toTerm)) ≠ .sn38 := by
          intro h38
          exact hval ((deltaSN_s_law (evalSN x.toTerm) (evalSN y.toTerm) (evalSN z.toTerm)).trans h38)
        have ⟨hval_xz, hval_yz⟩ := deltaSN_ne_sn38_factors hval_rhs
        have ⟨_, hA, hB, hC3⟩ := tripleRankSN_main_bounds hval
        have hrk_x : cnfCallRank x z ≤ rk + 1 :=
          Nat.le_trans (cnf_callRank_le_maxSub x z) (Nat.le_trans hA hrk)
        have hrk_y : cnfCallRank y z ≤ rk + 1 :=
          Nat.le_trans (cnf_callRank_le_maxSub y z) (Nat.le_trans hB hrk)
        have hsz_x : x.size ≤ sz := by
          have h1 : x.size + 1 ≤ 1 + x.size + y.size := by
            rw [Nat.add_comm x.size 1]
            exact Nat.le_add_right (1 + x.size) y.size
          exact Nat.le_of_succ_le_succ (Nat.le_trans h1 hsz)
        have hsz_y : y.size ≤ sz := by
          have h1 : y.size + 1 ≤ 1 + x.size + y.size := by
            rw [Nat.add_comm y.size 1]
            exact Nat.add_le_add_right (Nat.le_add_right 1 x.size) y.size
          exact Nat.le_of_succ_le_succ (Nat.le_trans h1 hsz)
        obtain ⟨n1, hred1, hs0_1, hs1_1⟩ := ihsz x z hval_xz hrk_x hsz_x
        obtain ⟨n2, hred2, _, _⟩ := ihsz y z hval_yz hrk_y hsz_y
        have heq1 : evalSN n1.toTerm = deltaSN (evalSN x.toTerm) (evalSN z.toTerm) :=
          (evalSN_reduces hred1).symm
        have heq2 : evalSN n2.toTerm = deltaSN (evalSN y.toTerm) (evalSN z.toTerm) :=
          (evalSN_reduces hred2).symm
        have hval_12 : evalSN (n1.toTerm ⋅ n2.toTerm) ≠ .sn38 := by
          change deltaSN (evalSN n1.toTerm) (evalSN n2.toTerm) ≠ .sn38
          rw [heq1, heq2]
          exact hval_rhs
        have hrk_12 : cnfCallRank n1 n2 ≤ rk := by
          cases x with
          | s =>
            rw [hs0_1 rfl]
            exact Nat.zero_le rk
          | s1 u =>
            rw [hs1_1 u rfl]
            change tripleRankSN (evalSN u.toTerm) (evalSN z.toTerm) (evalSN n2.toTerm) ≤ rk
            rw [heq2]
            exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (tripleRankSN_s1_lt hval) hrk)
          | s2 a b =>
            have hs2 : isS2StateSN (evalSN (CNF.s2 a b).toTerm) = true :=
              isS2StateSN_intro a.evalSN_ne_sn38 b.evalSN_ne_sn38
            have hlt := hC3 hs2
            have hsub := cnf_callRank_le_maxSub n1 n2
            rw [heq1, heq2] at hsub
            exact Nat.le_of_lt_succ (Nat.lt_of_le_of_lt hsub (Nat.lt_of_lt_of_le hlt hrk))
        obtain ⟨res, hred3, _, _⟩ := ihrk n1.size n1 n2 hval_12 hrk_12 (Nat.le_refl _)
        have htotal : Reduces ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) res.toTerm :=
          Reduces.next (Step.root x.toTerm y.toTerm z.toTerm)
            (reduces_trans (reduces_app hred1 hred2) hred3)
        exact ⟨res, htotal, fun h => (by cases h), fun _ h => (by cases h)⟩

theorem cnf_apply (f z : CNF) (hval : evalSN (f.toTerm ⋅ z.toTerm) ≠ .sn38) :
    ∃ res : CNF, Reduces (f.toTerm ⋅ z.toTerm) res.toTerm := by
  obtain ⟨res, hred, _, _⟩ := cnf_apply_aux (cnfCallRank f z) f.size f z hval (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨res, hred⟩

theorem closed_evalSN_ne_sn38_reduces_cnf {t : Term} (hv : noVars t = true) (hval : evalSN t ≠ .sn38) :
    ∃ c : CNF, Reduces t c.toTerm := by
  induction t with
  | s => exact ⟨.s, Reduces.refl S⟩
  | var _ => cases hv
  | app a b iha ihb =>
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    have hvb := ((Bool.and_eq_true _ _).mp hv).2
    have ⟨ha, hb⟩ := deltaSN_ne_sn38_factors hval
    obtain ⟨ca, hreda⟩ := iha hva ha
    obtain ⟨cb, hredb⟩ := ihb hvb hb
    have hval_c : evalSN (ca.toTerm ⋅ cb.toTerm) ≠ .sn38 := by
      change deltaSN (evalSN ca.toTerm) (evalSN cb.toTerm) ≠ .sn38
      rw [← evalSN_reduces hreda, ← evalSN_reduces hredb]
      exact hval
    obtain ⟨res, hred_ab⟩ := cnf_apply ca cb hval_c
    exact ⟨res, reduces_trans (reduces_app hreda hredb) hred_ab⟩

/-- **Waldmann's Theorem 9 (2000; Barendregt et al. 2018, Fig. 5.11)**:
    For every closed pure-`S` term `t`, `t` is strongly normalizing iff `t` is weakly normalizing
    iff `evalSN t ≠ .sn38`. -/
theorem waldmann_theorem_9 {t : Term} (hv : noVars t = true) :
    (StrongNormalizing t ↔ evalSN t ≠ .sn38) ∧ (HasNormalForm t ↔ evalSN t ≠ .sn38) := by
  have hwn_iff : HasNormalForm t ↔ evalSN t ≠ .sn38 := by
    constructor
    · intro ⟨nf, hred, hnf⟩
      rw [evalSN_reduces hred]
      exact closed_nf_evalSN_ne_sn38 (noVars_reduces hred hv) hnf
    · intro hval
      obtain ⟨c, hred⟩ := closed_evalSN_ne_sn38_reduces_cnf hv hval
      exact ⟨c.toTerm, hred, c.isNormalForm_toTerm⟩
  exact ⟨(sn_iff_wn t).trans hwn_iff, hwn_iff⟩

/-! ## 3. Exact 35-State Head Normalization S-Algebra `A_HN` & Open Problem 10 -/

inductive StateHN where
  | hn0 | hn1 | hn2 | hn3 | hn4 | hn5 | hn6 | hn7 | hn8 | hn9 | hn10 | hn11 | hn12 | hn13 | hn14 | hn15 | hn16 | hn17 | hn18 | hn19 | hn20 | hn21 | hn22 | hn23 | hn24 | hn25 | hn26 | hn27 | hn28 | hn29 | hn30 | hn31 | hn32 | hn33 | hn34
  deriving DecidableEq, Repr

def stateHNToNat : StateHN → Nat
  | .hn0 => 0
  | .hn1 => 1
  | .hn2 => 2
  | .hn3 => 3
  | .hn4 => 4
  | .hn5 => 5
  | .hn6 => 6
  | .hn7 => 7
  | .hn8 => 8
  | .hn9 => 9
  | .hn10 => 10
  | .hn11 => 11
  | .hn12 => 12
  | .hn13 => 13
  | .hn14 => 14
  | .hn15 => 15
  | .hn16 => 16
  | .hn17 => 17
  | .hn18 => 18
  | .hn19 => 19
  | .hn20 => 20
  | .hn21 => 21
  | .hn22 => 22
  | .hn23 => 23
  | .hn24 => 24
  | .hn25 => 25
  | .hn26 => 26
  | .hn27 => 27
  | .hn28 => 28
  | .hn29 => 29
  | .hn30 => 30
  | .hn31 => 31
  | .hn32 => 32
  | .hn33 => 33
  | .hn34 => 34

def deltaHN : StateHN → StateHN → StateHN
  | .hn0, y => match y with | .hn0 => .hn1 | .hn1 => .hn2 | .hn2 => .hn3 | .hn3 => .hn4 | .hn4 => .hn5 | .hn5 => .hn5 | .hn6 => .hn7 | .hn7 => .hn8 | .hn8 => .hn9 | .hn11 => .hn12 | .hn12 => .hn8 | .hn13 => .hn12 | .hn14 => .hn15 | .hn15 => .hn8 | .hn16 => .hn8 | .hn17 => .hn9 | .hn18 => .hn19 | .hn19 => .hn9 | .hn20 => .hn21 | .hn21 => .hn9 | .hn26 => .hn27 | .hn28 => .hn9 | .hn29 => .hn9 | .hn30 => .hn9 | .hn31 => .hn27 | .hn32 => .hn9 | _ => .hn10
  | .hn1, y => match y with | .hn0 => .hn6 | .hn1 => .hn11 | _ => .hn13
  | .hn2, y => match y with | .hn0 => .hn14 | .hn1 => .hn16 | .hn2 => .hn8 | .hn3 => .hn9 | .hn6 => .hn17 | .hn7 => .hn9 | .hn11 => .hn17 | .hn12 => .hn9 | .hn13 => .hn17 | _ => .hn10
  | .hn3, y => match y with | .hn0 => .hn18 | _ => .hn20
  | .hn4, y => match y with | .hn0 => .hn8 | _ => .hn10
  | .hn5, _ => .hn10
  | .hn6, y => match y with | .hn0 => .hn11 | .hn1 => .hn8 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn22 | .hn11 => .hn22 | .hn13 => .hn22 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn7, y => match y with | .hn0 => .hn26 | .hn1 => .hn28 | .hn2 => .hn29 | .hn3 => .hn22 | .hn6 => .hn30 | .hn7 => .hn22 | .hn11 => .hn30 | .hn12 => .hn22 | .hn13 => .hn30 | _ => .hn24
  | .hn8, y => match y with | .hn0 => .hn24 | _ => .hn23
  | .hn9, y => match y with | .hn0 => .hn25 | _ => .hn23
  | .hn10, _ => .hn23
  | .hn11, y => match y with | .hn0 => .hn13 | .hn1 => .hn17 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn30 | .hn11 => .hn29 | .hn13 => .hn29 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn12, y => match y with | .hn0 => .hn31 | .hn1 => .hn29 | .hn2 => .hn29 | .hn3 => .hn22 | .hn6 => .hn29 | .hn7 => .hn22 | .hn11 => .hn29 | .hn12 => .hn22 | .hn13 => .hn29 | _ => .hn24
  | .hn13, y => match y with | .hn0 => .hn13 | .hn1 => .hn10 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn24 | .hn11 => .hn24 | .hn13 => .hn24 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn14, y => match y with | .hn0 => .hn8 | .hn1 => .hn20 | .hn2 => .hn10 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | _ => .hn23
  | .hn15, _ => .hn24
  | .hn16, y => match y with | .hn0 => .hn22 | .hn1 => .hn29 | _ => .hn24
  | .hn17, y => match y with | .hn0 => .hn22 | _ => .hn23
  | .hn18, y => match y with | .hn0 => .hn20 | .hn1 => .hn24 | _ => .hn23
  | .hn19, y => match y with | .hn0 => .hn32 | _ => .hn25
  | .hn20, y => match y with | .hn1 => .hn24 | _ => .hn23
  | .hn21, y => match y with | .hn0 => .hn33 | _ => .hn23
  | .hn22, y => match y with | .hn0 => .hn25 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn23, _ => .hn34
  | .hn24, y => match y with | .hn0 => .hn23 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn25, y => match y with | .hn0 => .hn23 | _ => .hn34
  | .hn26, y => match y with | .hn0 => .hn17 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn27, _ => .hn25
  | .hn28, y => match y with | .hn0 => .hn30 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn29, y => match y with | .hn0 => .hn24 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn30, y => match y with | .hn0 => .hn29 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn31, y => match y with | .hn0 => .hn10 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn32, y => match y with | .hn0 => .hn24 | .hn1 => .hn23 | _ => .hn34
  | .hn33, y => match y with | .hn1 => .hn23 | _ => .hn34
  | .hn34, _ => .hn34

def checkAll1_StateHN (p : StateHN → Bool) : Bool :=
  (((((p .hn0 && p .hn1) && (p .hn2 && p .hn3)) && ((p .hn4 && p .hn5) && (p .hn6 && p .hn7))) && (((p .hn8 && p .hn9) && (p .hn10 && p .hn11)) && ((p .hn12 && p .hn13) && (p .hn14 && (p .hn15 && p .hn16))))) && ((((p .hn17 && p .hn18) && (p .hn19 && p .hn20)) && ((p .hn21 && p .hn22) && (p .hn23 && (p .hn24 && p .hn25)))) && (((p .hn26 && p .hn27) && (p .hn28 && p .hn29)) && ((p .hn30 && p .hn31) && (p .hn32 && (p .hn33 && p .hn34))))))

theorem checkAll1_StateHN_sound (p : StateHN → Bool)
    (h : checkAll1_StateHN p = true) (x : StateHN) : p x = true :=
  match x with
  | .hn0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .hn1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .hn2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .hn3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .hn4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .hn5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .hn6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .hn7 => (and_right (and_right (and_right (and_left (and_left h)))))
  | .hn8 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .hn9 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .hn10 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .hn11 => (and_right (and_right (and_left (and_right (and_left h)))))
  | .hn12 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .hn13 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .hn14 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .hn15 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .hn16 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .hn17 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .hn18 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .hn19 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .hn20 => (and_right (and_right (and_left (and_left (and_right h)))))
  | .hn21 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .hn22 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .hn23 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .hn24 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .hn25 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .hn26 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .hn27 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .hn28 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .hn29 => (and_right (and_right (and_left (and_right (and_right h)))))
  | .hn30 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .hn31 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .hn32 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .hn33 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .hn34 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateHN (p : StateHN → StateHN → Bool) : Bool :=
  checkAll1_StateHN (fun x => checkAll1_StateHN (fun y => p x y))

theorem checkAll2_StateHN_sound (p : StateHN → StateHN → Bool)
    (h : checkAll2_StateHN p = true) (x y : StateHN) : p x y = true :=
  checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ h x) y

private theorem s_row_StateHN_0 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn0) y) z = deltaHN (deltaHN .hn0 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_1 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn1) y) z = deltaHN (deltaHN .hn1 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_2 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn2) y) z = deltaHN (deltaHN .hn2 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_3 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn3) y) z = deltaHN (deltaHN .hn3 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_4 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn4) y) z = deltaHN (deltaHN .hn4 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_5 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn5) y) z = deltaHN (deltaHN .hn5 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_6 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn6) y) z = deltaHN (deltaHN .hn6 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_7 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn7) y) z = deltaHN (deltaHN .hn7 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_8 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn8) y) z = deltaHN (deltaHN .hn8 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_9 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn9) y) z = deltaHN (deltaHN .hn9 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_10 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn10) y) z = deltaHN (deltaHN .hn10 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_11 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn11) y) z = deltaHN (deltaHN .hn11 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_12 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn12) y) z = deltaHN (deltaHN .hn12 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_13 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn13) y) z = deltaHN (deltaHN .hn13 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_14 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn14) y) z = deltaHN (deltaHN .hn14 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_15 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn15) y) z = deltaHN (deltaHN .hn15 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_16 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn16) y) z = deltaHN (deltaHN .hn16 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_17 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn17) y) z = deltaHN (deltaHN .hn17 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_18 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn18) y) z = deltaHN (deltaHN .hn18 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_19 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn19) y) z = deltaHN (deltaHN .hn19 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_20 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn20) y) z = deltaHN (deltaHN .hn20 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_21 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn21) y) z = deltaHN (deltaHN .hn21 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_22 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn22) y) z = deltaHN (deltaHN .hn22 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_23 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn23) y) z = deltaHN (deltaHN .hn23 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_24 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn24) y) z = deltaHN (deltaHN .hn24 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_25 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn25) y) z = deltaHN (deltaHN .hn25 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_26 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn26) y) z = deltaHN (deltaHN .hn26 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_27 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn27) y) z = deltaHN (deltaHN .hn27 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_28 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn28) y) z = deltaHN (deltaHN .hn28 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_29 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn29) y) z = deltaHN (deltaHN .hn29 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_30 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn30) y) z = deltaHN (deltaHN .hn30 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_31 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn31) y) z = deltaHN (deltaHN .hn31 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_32 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn32) y) z = deltaHN (deltaHN .hn32 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_33 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn33) y) z = deltaHN (deltaHN .hn33 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_34 : checkAll2_StateHN (fun y z => decide (deltaHN (deltaHN (deltaHN .hn0 .hn34) y) z = deltaHN (deltaHN .hn34 z) (deltaHN y z))) = true := rfl

theorem deltaHN_s_law (x y z : StateHN) :
    deltaHN (deltaHN (deltaHN .hn0 x) y) z = deltaHN (deltaHN x z) (deltaHN y z) := by
  cases x with
  | hn0 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_0 y z)
  | hn1 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_1 y z)
  | hn2 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_2 y z)
  | hn3 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_3 y z)
  | hn4 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_4 y z)
  | hn5 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_5 y z)
  | hn6 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_6 y z)
  | hn7 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_7 y z)
  | hn8 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_8 y z)
  | hn9 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_9 y z)
  | hn10 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_10 y z)
  | hn11 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_11 y z)
  | hn12 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_12 y z)
  | hn13 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_13 y z)
  | hn14 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_14 y z)
  | hn15 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_15 y z)
  | hn16 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_16 y z)
  | hn17 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_17 y z)
  | hn18 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_18 y z)
  | hn19 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_19 y z)
  | hn20 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_20 y z)
  | hn21 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_21 y z)
  | hn22 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_22 y z)
  | hn23 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_23 y z)
  | hn24 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_24 y z)
  | hn25 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_25 y z)
  | hn26 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_26 y z)
  | hn27 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_27 y z)
  | hn28 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_28 y z)
  | hn29 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_29 y z)
  | hn30 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_30 y z)
  | hn31 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_31 y z)
  | hn32 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_32 y z)
  | hn33 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_33 y z)
  | hn34 => exact of_decide_eq_true (checkAll2_StateHN_sound _ s_row_StateHN_34 y z)

private theorem deltaHN_hn34_left_chk : checkAll1_StateHN (fun y => decide (deltaHN .hn34 y = .hn34)) = true := rfl
private theorem deltaHN_ne_hn0_chk : checkAll2_StateHN (fun x y => decide (deltaHN x y ≠ .hn0)) = true := rfl
private theorem deltaHN_s1_ne34_chk : checkAll1_StateHN (fun x => decide (deltaHN .hn0 x ≠ .hn34)) = true := rfl
private theorem deltaHN_s2_ne34_chk : checkAll2_StateHN (fun x y => decide (deltaHN (deltaHN .hn0 x) y ≠ .hn34)) = true := rfl

theorem deltaHN_hn34_left (y : StateHN) : deltaHN .hn34 y = .hn34 :=
  of_decide_eq_true (checkAll1_StateHN_sound _ deltaHN_hn34_left_chk y)

theorem deltaHN_ne_hn34_left {x y : StateHN} (h : deltaHN x y ≠ .hn34) : x ≠ .hn34 := by
  intro hx; subst hx; exact h (deltaHN_hn34_left y)

theorem deltaHN_ne_hn0 (x y : StateHN) : deltaHN x y ≠ .hn0 :=
  of_decide_eq_true (checkAll2_StateHN_sound _ deltaHN_ne_hn0_chk x y)

theorem deltaHN_s1_ne_hn34 (x : StateHN) : deltaHN .hn0 x ≠ .hn34 :=
  of_decide_eq_true (checkAll1_StateHN_sound _ deltaHN_s1_ne34_chk x)

theorem deltaHN_s2_ne_hn34 (x y : StateHN) : deltaHN (deltaHN .hn0 x) y ≠ .hn34 :=
  of_decide_eq_true (checkAll2_StateHN_sound _ deltaHN_s2_ne34_chk x y)

def evalHN : Term → StateHN
  | .s => .hn0
  | .var _ => .hn0
  | .app a b => deltaHN (evalHN a) (evalHN b)

theorem evalHN_step {a b : Term} (h : Step a b) : evalHN a = evalHN b := by
  induction h with
  | root x y z => exact deltaHN_s_law (evalHN x) (evalHN y) (evalHN z)
  | left _ ih => simp only [evalHN, ih]
  | right _ ih => simp only [evalHN, ih]

theorem evalHN_reduces {a b : Term} (h : Reduces a b) : evalHN a = evalHN b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalHN_step hs).trans ih

theorem evalHN_conv {a b : Term} (h : ConvS a b) : evalHN a = evalHN b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalHN_step hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem evalHN_eq_hn0_iff {t : Term} (hv : noVars t = true) : evalHN t = .hn0 ↔ t = S := by
  cases t with
  | s => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | var _ => cases hv
  | app a b =>
    exact ⟨fun h => False.elim (deltaHN_ne_hn0 (evalHN a) (evalHN b) h), fun h => by cases h⟩

theorem closed_spineLen_le_2_shapes {t : Term} (hv : noVars t = true) (hsl : spineLen t ≤ 2) :
    t = S ∨ (∃ x, t = S ⋅ x) ∨ (∃ x y, t = S ⋅ x ⋅ y) := by
  cases t with
  | s => exact Or.inl rfl
  | var _ => cases hv
  | app a b =>
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    cases a with
    | s => exact Or.inr (Or.inl ⟨b, rfl⟩)
    | var _ => cases hva
    | app a1 y =>
      have hva1 := ((Bool.and_eq_true _ _).mp hva).1
      cases a1 with
      | s => exact Or.inr (Or.inr ⟨y, b, rfl⟩)
      | var _ => cases hva1
      | app a2 x =>
        -- Here `spineLen (a2 ⋅ x ⋅ y ⋅ b) = 3 + spineLen a2 ≥ 3`, contradicting `hsl ≤ 2`!
        have h3 : 3 ≤ 1 + (1 + (1 + spineLen a2)) :=
          Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.zero_le _) 1) 1) 1
        exfalso
        exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_trans h3 hsl)))

theorem closed_hnf_evalHN_ne_hn34 {h : Term} (hv : noVars h = true) (hsl : spineLen h ≤ 2) :
    evalHN h ≠ .hn34 := by
  rcases closed_spineLen_le_2_shapes hv hsl with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · decide
  · exact deltaHN_s1_ne_hn34 (evalHN x)
  · exact deltaHN_s2_ne_hn34 (evalHN x) (evalHN y)

def hnA : StateHN → StateHN → Nat
  | .hn0, y => match y with | .hn9 => 0 | .hn10 => 0 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn1, y => match y with | .hn0 => 2 | .hn1 => 2 | .hn2 => 1 | .hn6 => 1 | .hn7 => 1 | .hn11 => 1 | _ => 0
  | .hn2, y => match y with | .hn0 => 2 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn3, y => match y with | .hn0 => 4 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 2 | .hn11 => 1 | .hn13 => 1 | .hn18 => 1 | _ => 0
  | .hn4, y => match y with | .hn0 => 6 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | .hn28 => 1 | _ => 0
  | .hn5, y => match y with | .hn0 => 15 | .hn1 => 7 | .hn3 => 2 | .hn6 => 4 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn6, y => match y with | .hn0 => 3 | .hn1 => 2 | .hn2 => 2 | .hn6 => 2 | .hn9 => 0 | .hn10 => 0 | .hn11 => 2 | .hn13 => 2 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn7, y => match y with | .hn0 => 5 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 1 | .hn12 => 1 | .hn13 => 1 | .hn14 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn8, y => match y with | .hn0 => 12 | .hn1 => 6 | .hn2 => 2 | .hn3 => 2 | .hn6 => 5 | .hn7 => 1 | .hn11 => 3 | .hn13 => 2 | .hn18 => 2 | _ => 0
  | .hn9, y => match y with | .hn0 => 16 | .hn1 => 6 | .hn2 => 2 | .hn3 => 1 | .hn6 => 4 | .hn7 => 1 | .hn11 => 3 | .hn13 => 2 | .hn18 => 1 | _ => 0
  | .hn10, y => match y with | .hn0 => 30 | .hn1 => 15 | .hn2 => 3 | .hn3 => 2 | .hn6 => 7 | .hn7 => 3 | .hn11 => 4 | .hn13 => 2 | .hn18 => 1 | .hn28 => 1 | _ => 0
  | .hn11, y => match y with | .hn0 => 3 | .hn1 => 5 | .hn2 => 2 | .hn6 => 2 | .hn7 => 3 | .hn9 => 0 | .hn10 => 0 | .hn11 => 3 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn12, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn13, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn6 => 4 | .hn9 => 0 | .hn10 => 0 | .hn11 => 2 | .hn13 => 2 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn14, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn6 => 2 | .hn7 => 2 | .hn11 => 2 | .hn12 => 1 | .hn13 => 1 | .hn14 => 1 | .hn15 => 1 | .hn16 => 1 | .hn18 => 1 | .hn20 => 1 | _ => 0
  | .hn15, y => match y with | .hn0 => 6 | .hn1 => 5 | .hn2 => 1 | .hn3 => 2 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn16, y => match y with | .hn0 => 6 | .hn1 => 8 | .hn2 => 3 | .hn6 => 3 | .hn7 => 3 | .hn11 => 3 | _ => 0
  | .hn17, y => match y with | .hn0 => 10 | .hn1 => 7 | .hn2 => 3 | .hn6 => 3 | .hn7 => 1 | .hn11 => 4 | .hn13 => 1 | _ => 0
  | .hn18, y => match y with | .hn0 => 6 | .hn1 => 6 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn19, y => match y with | .hn0 => 9 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | .hn28 => 1 | _ => 0
  | .hn20, y => match y with | .hn0 => 8 | .hn1 => 9 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 3 | .hn11 => 3 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn21, y => match y with | .hn0 => 7 | _ => 0
  | .hn22, y => match y with | .hn0 => 9 | .hn1 => 7 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn23, _ => 0
  | .hn24, y => match y with | .hn0 => 18 | .hn1 => 12 | .hn2 => 7 | .hn3 => 4 | .hn4 => 2 | .hn5 => 1 | _ => 0
  | .hn25, y => match y with | .hn0 => 27 | _ => 0
  | .hn26, y => match y with | .hn0 => 8 | .hn1 => 4 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn27, y => match y with | .hn0 => 15 | .hn1 => 7 | .hn3 => 1 | .hn6 => 4 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn28, y => match y with | .hn0 => 7 | .hn1 => 8 | .hn2 => 4 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn29, y => match y with | .hn0 => 12 | .hn1 => 13 | .hn2 => 4 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn30, y => match y with | .hn0 => 12 | .hn1 => 2 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn31, y => match y with | .hn0 => 8 | .hn1 => 8 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn32, y => match y with | .hn0 => 15 | .hn1 => 13 | _ => 0
  | .hn33, y => match y with | .hn1 => 16 | _ => 0
  | .hn34, _ => 0

def hnB : StateHN → StateHN → Nat
  | .hn0, y => match y with | .hn0 => 2 | .hn1 => 3 | .hn2 => 3 | .hn3 => 4 | .hn4 => 3 | .hn5 => 4 | .hn6 => 4 | .hn8 => 2 | .hn11 => 3 | .hn13 => 2 | .hn14 => 5 | .hn15 => 2 | .hn18 => 5 | _ => 0
  | .hn1, y => match y with | .hn0 => 4 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn7 => 1 | _ => 0
  | .hn2, y => match y with | .hn0 => 9 | .hn1 => 3 | .hn2 => 2 | .hn3 => 4 | .hn4 => 2 | .hn5 => 2 | .hn6 => 3 | .hn7 => 4 | .hn9 => 2 | .hn11 => 2 | .hn12 => 3 | _ => 1
  | .hn3, y => match y with | .hn0 => 12 | .hn1 => 4 | .hn2 => 2 | .hn5 => 1 | .hn18 => 4 | _ => 0
  | .hn4, y => match y with | .hn0 => 19 | .hn1 => 1 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn7 => 1 | .hn11 => 1 | _ => 0
  | .hn5, y => match y with | .hn0 => 11 | .hn1 => 3 | .hn2 => 1 | .hn3 => 3 | .hn4 => 1 | .hn7 => 2 | _ => 0
  | .hn6, y => match y with | .hn0 => 4 | .hn1 => 6 | .hn2 => 6 | .hn3 => 4 | .hn4 => 3 | .hn5 => 6 | .hn6 => 9 | .hn8 => 4 | .hn11 => 9 | .hn12 => 1 | .hn13 => 4 | .hn14 => 5 | .hn15 => 2 | .hn16 => 1 | .hn18 => 5 | .hn20 => 1 | .hn31 => 1 | _ => 0
  | .hn7, y => match y with | .hn0 => 14 | .hn1 => 4 | .hn2 => 3 | .hn3 => 2 | .hn4 => 3 | .hn5 => 2 | .hn6 => 6 | .hn7 => 0 | .hn8 => 2 | .hn9 => 2 | .hn12 => 0 | .hn13 => 0 | .hn14 => 2 | .hn30 => 0 | .hn31 => 0 | .hn32 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn8, y => match y with | .hn0 => 22 | .hn1 => 4 | .hn2 => 5 | .hn3 => 2 | .hn4 => 1 | .hn5 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 1 | _ => 0
  | .hn9, y => match y with | .hn0 => 30 | .hn1 => 7 | .hn2 => 3 | .hn6 => 3 | .hn11 => 1 | .hn18 => 3 | _ => 0
  | .hn10, y => match y with | .hn0 => 68 | .hn1 => 8 | .hn2 => 3 | .hn3 => 3 | .hn4 => 1 | .hn5 => 1 | .hn6 => 4 | .hn7 => 1 | .hn8 => 1 | .hn11 => 2 | .hn18 => 4 | _ => 0
  | .hn11, y => match y with | .hn0 => 7 | .hn1 => 7 | .hn2 => 5 | .hn3 => 7 | .hn4 => 6 | .hn5 => 7 | .hn6 => 5 | .hn7 => 3 | .hn8 => 4 | .hn11 => 4 | .hn13 => 3 | .hn14 => 5 | .hn15 => 3 | .hn18 => 6 | _ => 1
  | .hn12, y => match y with | .hn0 => 15 | .hn1 => 9 | .hn2 => 2 | .hn3 => 5 | .hn4 => 3 | .hn5 => 2 | .hn6 => 1 | .hn7 => 6 | .hn8 => 2 | .hn9 => 1 | .hn11 => 1 | .hn12 => 3 | .hn14 => 2 | .hn15 => 1 | .hn16 => 1 | .hn18 => 2 | .hn19 => 2 | _ => 0
  | .hn13, y => match y with | .hn0 => 6 | .hn1 => 7 | .hn2 => 4 | .hn3 => 4 | .hn4 => 4 | .hn5 => 5 | .hn6 => 9 | .hn8 => 3 | .hn11 => 4 | .hn13 => 3 | .hn14 => 5 | .hn15 => 3 | .hn18 => 6 | _ => 1
  | .hn14, y => match y with | .hn0 => 11 | .hn1 => 3 | .hn2 => 2 | .hn3 => 4 | .hn4 => 4 | .hn5 => 7 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn13 => 1 | .hn14 => 4 | .hn15 => 1 | .hn16 => 1 | .hn18 => 3 | _ => 0
  | .hn15, y => match y with | .hn0 => 6 | .hn1 => 1 | .hn2 => 1 | .hn3 => 8 | _ => 0
  | .hn16, y => match y with | .hn0 => 18 | .hn1 => 7 | .hn2 => 4 | .hn3 => 3 | .hn4 => 2 | .hn5 => 2 | .hn6 => 1 | .hn7 => 3 | _ => 0
  | .hn17, y => match y with | .hn0 => 20 | .hn1 => 8 | .hn2 => 6 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn6 => 5 | .hn7 => 1 | .hn11 => 3 | .hn13 => 1 | _ => 0
  | .hn18, y => match y with | .hn0 => 13 | .hn1 => 4 | .hn2 => 2 | _ => 0
  | .hn19, y => match y with | .hn0 => 23 | .hn1 => 2 | .hn2 => 1 | .hn3 => 4 | .hn7 => 3 | .hn11 => 3 | _ => 0
  | .hn20, y => match y with | .hn0 => 23 | .hn1 => 2 | .hn2 => 2 | .hn3 => 4 | .hn4 => 2 | .hn5 => 2 | .hn6 => 4 | .hn7 => 3 | .hn8 => 2 | .hn9 => 2 | .hn10 => 1 | .hn11 => 1 | .hn12 => 3 | .hn14 => 1 | .hn15 => 1 | .hn16 => 2 | .hn17 => 1 | .hn18 => 1 | _ => 0
  | .hn21, y => match y with | .hn0 => 17 | _ => 0
  | .hn22, y => match y with | .hn0 => 20 | .hn1 => 6 | .hn2 => 5 | .hn3 => 5 | .hn4 => 3 | .hn5 => 6 | _ => 0
  | .hn23, _ => 0
  | .hn24, y => match y with | .hn0 => 30 | .hn1 => 9 | .hn2 => 6 | .hn3 => 7 | .hn4 => 6 | .hn5 => 7 | _ => 0
  | .hn25, y => match y with | .hn0 => 50 | _ => 0
  | .hn26, y => match y with | .hn0 => 10 | .hn1 => 4 | .hn2 => 5 | _ => 0
  | .hn27, y => match y with | .hn0 => 8 | _ => 0
  | .hn28, y => match y with | .hn0 => 12 | .hn1 => 5 | .hn2 => 4 | .hn3 => 2 | .hn4 => 1 | .hn5 => 3 | _ => 0
  | .hn29, y => match y with | .hn0 => 23 | .hn1 => 9 | .hn2 => 6 | .hn3 => 7 | .hn4 => 6 | .hn5 => 7 | _ => 0
  | .hn30, y => match y with | .hn0 => 12 | .hn1 => 5 | .hn2 => 5 | .hn3 => 4 | .hn4 => 3 | .hn5 => 5 | _ => 0
  | .hn31, y => match y with | .hn0 => 9 | .hn1 => 8 | .hn2 => 2 | _ => 0
  | .hn32, y => match y with | .hn0 => 14 | .hn1 => 10 | _ => 0
  | .hn33, y => match y with | .hn1 => 17 | _ => 0
  | .hn34, _ => 0

private theorem hn_cert_row_0 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn0) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn0) && natBle (hnA (deltaHN .hn0 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn0) y)) && (natBle (hnA .hn0 z + hnA (deltaHN .hn0 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn0) y) z) && natBle (hnB .hn0 z + hnA (deltaHN .hn0 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn0 z) (deltaHN y z) + 1) (hnB .hn0 .hn0 + hnB (deltaHN .hn0 .hn0) y + hnB (deltaHN (deltaHN .hn0 .hn0) y) z))))) = true := rfl
private theorem hn_cert_row_1 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn1) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn1) && natBle (hnA (deltaHN .hn1 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn1) y)) && (natBle (hnA .hn1 z + hnA (deltaHN .hn1 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn1) y) z) && natBle (hnB .hn1 z + hnA (deltaHN .hn1 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn1 z) (deltaHN y z) + 1) (hnB .hn0 .hn1 + hnB (deltaHN .hn0 .hn1) y + hnB (deltaHN (deltaHN .hn0 .hn1) y) z))))) = true := rfl
private theorem hn_cert_row_2 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn2) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn2) && natBle (hnA (deltaHN .hn2 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn2) y)) && (natBle (hnA .hn2 z + hnA (deltaHN .hn2 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn2) y) z) && natBle (hnB .hn2 z + hnA (deltaHN .hn2 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn2 z) (deltaHN y z) + 1) (hnB .hn0 .hn2 + hnB (deltaHN .hn0 .hn2) y + hnB (deltaHN (deltaHN .hn0 .hn2) y) z))))) = true := rfl
private theorem hn_cert_row_3 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn3) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn3) && natBle (hnA (deltaHN .hn3 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn3) y)) && (natBle (hnA .hn3 z + hnA (deltaHN .hn3 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn3) y) z) && natBle (hnB .hn3 z + hnA (deltaHN .hn3 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn3 z) (deltaHN y z) + 1) (hnB .hn0 .hn3 + hnB (deltaHN .hn0 .hn3) y + hnB (deltaHN (deltaHN .hn0 .hn3) y) z))))) = true := rfl
private theorem hn_cert_row_4 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn4) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn4) && natBle (hnA (deltaHN .hn4 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn4) y)) && (natBle (hnA .hn4 z + hnA (deltaHN .hn4 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn4) y) z) && natBle (hnB .hn4 z + hnA (deltaHN .hn4 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn4 z) (deltaHN y z) + 1) (hnB .hn0 .hn4 + hnB (deltaHN .hn0 .hn4) y + hnB (deltaHN (deltaHN .hn0 .hn4) y) z))))) = true := rfl
private theorem hn_cert_row_5 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn5) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn5) && natBle (hnA (deltaHN .hn5 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn5) y)) && (natBle (hnA .hn5 z + hnA (deltaHN .hn5 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn5) y) z) && natBle (hnB .hn5 z + hnA (deltaHN .hn5 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn5 z) (deltaHN y z) + 1) (hnB .hn0 .hn5 + hnB (deltaHN .hn0 .hn5) y + hnB (deltaHN (deltaHN .hn0 .hn5) y) z))))) = true := rfl
private theorem hn_cert_row_6 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn6) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn6) && natBle (hnA (deltaHN .hn6 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn6) y)) && (natBle (hnA .hn6 z + hnA (deltaHN .hn6 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn6) y) z) && natBle (hnB .hn6 z + hnA (deltaHN .hn6 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn6 z) (deltaHN y z) + 1) (hnB .hn0 .hn6 + hnB (deltaHN .hn0 .hn6) y + hnB (deltaHN (deltaHN .hn0 .hn6) y) z))))) = true := rfl
private theorem hn_cert_row_7 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn7) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn7) && natBle (hnA (deltaHN .hn7 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn7) y)) && (natBle (hnA .hn7 z + hnA (deltaHN .hn7 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn7) y) z) && natBle (hnB .hn7 z + hnA (deltaHN .hn7 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn7 z) (deltaHN y z) + 1) (hnB .hn0 .hn7 + hnB (deltaHN .hn0 .hn7) y + hnB (deltaHN (deltaHN .hn0 .hn7) y) z))))) = true := rfl
private theorem hn_cert_row_8 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn8) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn8) && natBle (hnA (deltaHN .hn8 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn8) y)) && (natBle (hnA .hn8 z + hnA (deltaHN .hn8 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn8) y) z) && natBle (hnB .hn8 z + hnA (deltaHN .hn8 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn8 z) (deltaHN y z) + 1) (hnB .hn0 .hn8 + hnB (deltaHN .hn0 .hn8) y + hnB (deltaHN (deltaHN .hn0 .hn8) y) z))))) = true := rfl
private theorem hn_cert_row_9 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn9) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn9) && natBle (hnA (deltaHN .hn9 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn9) y)) && (natBle (hnA .hn9 z + hnA (deltaHN .hn9 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn9) y) z) && natBle (hnB .hn9 z + hnA (deltaHN .hn9 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn9 z) (deltaHN y z) + 1) (hnB .hn0 .hn9 + hnB (deltaHN .hn0 .hn9) y + hnB (deltaHN (deltaHN .hn0 .hn9) y) z))))) = true := rfl
private theorem hn_cert_row_10 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn10) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn10) && natBle (hnA (deltaHN .hn10 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn10) y)) && (natBle (hnA .hn10 z + hnA (deltaHN .hn10 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn10) y) z) && natBle (hnB .hn10 z + hnA (deltaHN .hn10 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn10 z) (deltaHN y z) + 1) (hnB .hn0 .hn10 + hnB (deltaHN .hn0 .hn10) y + hnB (deltaHN (deltaHN .hn0 .hn10) y) z))))) = true := rfl
private theorem hn_cert_row_11 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn11) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn11) && natBle (hnA (deltaHN .hn11 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn11) y)) && (natBle (hnA .hn11 z + hnA (deltaHN .hn11 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn11) y) z) && natBle (hnB .hn11 z + hnA (deltaHN .hn11 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn11 z) (deltaHN y z) + 1) (hnB .hn0 .hn11 + hnB (deltaHN .hn0 .hn11) y + hnB (deltaHN (deltaHN .hn0 .hn11) y) z))))) = true := rfl
private theorem hn_cert_row_12 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn12) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn12) && natBle (hnA (deltaHN .hn12 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn12) y)) && (natBle (hnA .hn12 z + hnA (deltaHN .hn12 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn12) y) z) && natBle (hnB .hn12 z + hnA (deltaHN .hn12 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn12 z) (deltaHN y z) + 1) (hnB .hn0 .hn12 + hnB (deltaHN .hn0 .hn12) y + hnB (deltaHN (deltaHN .hn0 .hn12) y) z))))) = true := rfl
private theorem hn_cert_row_13 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn13) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn13) && natBle (hnA (deltaHN .hn13 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn13) y)) && (natBle (hnA .hn13 z + hnA (deltaHN .hn13 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn13) y) z) && natBle (hnB .hn13 z + hnA (deltaHN .hn13 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn13 z) (deltaHN y z) + 1) (hnB .hn0 .hn13 + hnB (deltaHN .hn0 .hn13) y + hnB (deltaHN (deltaHN .hn0 .hn13) y) z))))) = true := rfl
private theorem hn_cert_row_14 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn14) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn14) && natBle (hnA (deltaHN .hn14 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn14) y)) && (natBle (hnA .hn14 z + hnA (deltaHN .hn14 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn14) y) z) && natBle (hnB .hn14 z + hnA (deltaHN .hn14 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn14 z) (deltaHN y z) + 1) (hnB .hn0 .hn14 + hnB (deltaHN .hn0 .hn14) y + hnB (deltaHN (deltaHN .hn0 .hn14) y) z))))) = true := rfl
private theorem hn_cert_row_15 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn15) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn15) && natBle (hnA (deltaHN .hn15 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn15) y)) && (natBle (hnA .hn15 z + hnA (deltaHN .hn15 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn15) y) z) && natBle (hnB .hn15 z + hnA (deltaHN .hn15 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn15 z) (deltaHN y z) + 1) (hnB .hn0 .hn15 + hnB (deltaHN .hn0 .hn15) y + hnB (deltaHN (deltaHN .hn0 .hn15) y) z))))) = true := rfl
private theorem hn_cert_row_16 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn16) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn16) && natBle (hnA (deltaHN .hn16 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn16) y)) && (natBle (hnA .hn16 z + hnA (deltaHN .hn16 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn16) y) z) && natBle (hnB .hn16 z + hnA (deltaHN .hn16 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn16 z) (deltaHN y z) + 1) (hnB .hn0 .hn16 + hnB (deltaHN .hn0 .hn16) y + hnB (deltaHN (deltaHN .hn0 .hn16) y) z))))) = true := rfl
private theorem hn_cert_row_17 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn17) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn17) && natBle (hnA (deltaHN .hn17 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn17) y)) && (natBle (hnA .hn17 z + hnA (deltaHN .hn17 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn17) y) z) && natBle (hnB .hn17 z + hnA (deltaHN .hn17 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn17 z) (deltaHN y z) + 1) (hnB .hn0 .hn17 + hnB (deltaHN .hn0 .hn17) y + hnB (deltaHN (deltaHN .hn0 .hn17) y) z))))) = true := rfl
private theorem hn_cert_row_18 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn18) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn18) && natBle (hnA (deltaHN .hn18 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn18) y)) && (natBle (hnA .hn18 z + hnA (deltaHN .hn18 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn18) y) z) && natBle (hnB .hn18 z + hnA (deltaHN .hn18 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn18 z) (deltaHN y z) + 1) (hnB .hn0 .hn18 + hnB (deltaHN .hn0 .hn18) y + hnB (deltaHN (deltaHN .hn0 .hn18) y) z))))) = true := rfl
private theorem hn_cert_row_19 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn19) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn19) && natBle (hnA (deltaHN .hn19 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn19) y)) && (natBle (hnA .hn19 z + hnA (deltaHN .hn19 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn19) y) z) && natBle (hnB .hn19 z + hnA (deltaHN .hn19 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn19 z) (deltaHN y z) + 1) (hnB .hn0 .hn19 + hnB (deltaHN .hn0 .hn19) y + hnB (deltaHN (deltaHN .hn0 .hn19) y) z))))) = true := rfl
private theorem hn_cert_row_20 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn20) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn20) && natBle (hnA (deltaHN .hn20 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn20) y)) && (natBle (hnA .hn20 z + hnA (deltaHN .hn20 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn20) y) z) && natBle (hnB .hn20 z + hnA (deltaHN .hn20 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn20 z) (deltaHN y z) + 1) (hnB .hn0 .hn20 + hnB (deltaHN .hn0 .hn20) y + hnB (deltaHN (deltaHN .hn0 .hn20) y) z))))) = true := rfl
private theorem hn_cert_row_21 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn21) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn21) && natBle (hnA (deltaHN .hn21 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn21) y)) && (natBle (hnA .hn21 z + hnA (deltaHN .hn21 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn21) y) z) && natBle (hnB .hn21 z + hnA (deltaHN .hn21 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn21 z) (deltaHN y z) + 1) (hnB .hn0 .hn21 + hnB (deltaHN .hn0 .hn21) y + hnB (deltaHN (deltaHN .hn0 .hn21) y) z))))) = true := rfl
private theorem hn_cert_row_22 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn22) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn22) && natBle (hnA (deltaHN .hn22 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn22) y)) && (natBle (hnA .hn22 z + hnA (deltaHN .hn22 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn22) y) z) && natBle (hnB .hn22 z + hnA (deltaHN .hn22 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn22 z) (deltaHN y z) + 1) (hnB .hn0 .hn22 + hnB (deltaHN .hn0 .hn22) y + hnB (deltaHN (deltaHN .hn0 .hn22) y) z))))) = true := rfl
private theorem hn_cert_row_23 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn23) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn23) && natBle (hnA (deltaHN .hn23 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn23) y)) && (natBle (hnA .hn23 z + hnA (deltaHN .hn23 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn23) y) z) && natBle (hnB .hn23 z + hnA (deltaHN .hn23 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn23 z) (deltaHN y z) + 1) (hnB .hn0 .hn23 + hnB (deltaHN .hn0 .hn23) y + hnB (deltaHN (deltaHN .hn0 .hn23) y) z))))) = true := rfl
private theorem hn_cert_row_24 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn24) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn24) && natBle (hnA (deltaHN .hn24 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn24) y)) && (natBle (hnA .hn24 z + hnA (deltaHN .hn24 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn24) y) z) && natBle (hnB .hn24 z + hnA (deltaHN .hn24 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn24 z) (deltaHN y z) + 1) (hnB .hn0 .hn24 + hnB (deltaHN .hn0 .hn24) y + hnB (deltaHN (deltaHN .hn0 .hn24) y) z))))) = true := rfl
private theorem hn_cert_row_25 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn25) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn25) && natBle (hnA (deltaHN .hn25 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn25) y)) && (natBle (hnA .hn25 z + hnA (deltaHN .hn25 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn25) y) z) && natBle (hnB .hn25 z + hnA (deltaHN .hn25 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn25 z) (deltaHN y z) + 1) (hnB .hn0 .hn25 + hnB (deltaHN .hn0 .hn25) y + hnB (deltaHN (deltaHN .hn0 .hn25) y) z))))) = true := rfl
private theorem hn_cert_row_26 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn26) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn26) && natBle (hnA (deltaHN .hn26 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn26) y)) && (natBle (hnA .hn26 z + hnA (deltaHN .hn26 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn26) y) z) && natBle (hnB .hn26 z + hnA (deltaHN .hn26 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn26 z) (deltaHN y z) + 1) (hnB .hn0 .hn26 + hnB (deltaHN .hn0 .hn26) y + hnB (deltaHN (deltaHN .hn0 .hn26) y) z))))) = true := rfl
private theorem hn_cert_row_27 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn27) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn27) && natBle (hnA (deltaHN .hn27 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn27) y)) && (natBle (hnA .hn27 z + hnA (deltaHN .hn27 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn27) y) z) && natBle (hnB .hn27 z + hnA (deltaHN .hn27 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn27 z) (deltaHN y z) + 1) (hnB .hn0 .hn27 + hnB (deltaHN .hn0 .hn27) y + hnB (deltaHN (deltaHN .hn0 .hn27) y) z))))) = true := rfl
private theorem hn_cert_row_28 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn28) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn28) && natBle (hnA (deltaHN .hn28 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn28) y)) && (natBle (hnA .hn28 z + hnA (deltaHN .hn28 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn28) y) z) && natBle (hnB .hn28 z + hnA (deltaHN .hn28 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn28 z) (deltaHN y z) + 1) (hnB .hn0 .hn28 + hnB (deltaHN .hn0 .hn28) y + hnB (deltaHN (deltaHN .hn0 .hn28) y) z))))) = true := rfl
private theorem hn_cert_row_29 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn29) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn29) && natBle (hnA (deltaHN .hn29 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn29) y)) && (natBle (hnA .hn29 z + hnA (deltaHN .hn29 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn29) y) z) && natBle (hnB .hn29 z + hnA (deltaHN .hn29 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn29 z) (deltaHN y z) + 1) (hnB .hn0 .hn29 + hnB (deltaHN .hn0 .hn29) y + hnB (deltaHN (deltaHN .hn0 .hn29) y) z))))) = true := rfl
private theorem hn_cert_row_30 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn30) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn30) && natBle (hnA (deltaHN .hn30 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn30) y)) && (natBle (hnA .hn30 z + hnA (deltaHN .hn30 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn30) y) z) && natBle (hnB .hn30 z + hnA (deltaHN .hn30 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn30 z) (deltaHN y z) + 1) (hnB .hn0 .hn30 + hnB (deltaHN .hn0 .hn30) y + hnB (deltaHN (deltaHN .hn0 .hn30) y) z))))) = true := rfl
private theorem hn_cert_row_31 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn31) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn31) && natBle (hnA (deltaHN .hn31 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn31) y)) && (natBle (hnA .hn31 z + hnA (deltaHN .hn31 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn31) y) z) && natBle (hnB .hn31 z + hnA (deltaHN .hn31 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn31 z) (deltaHN y z) + 1) (hnB .hn0 .hn31 + hnB (deltaHN .hn0 .hn31) y + hnB (deltaHN (deltaHN .hn0 .hn31) y) z))))) = true := rfl
private theorem hn_cert_row_32 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn32) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn32) && natBle (hnA (deltaHN .hn32 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn32) y)) && (natBle (hnA .hn32 z + hnA (deltaHN .hn32 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn32) y) z) && natBle (hnB .hn32 z + hnA (deltaHN .hn32 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn32 z) (deltaHN y z) + 1) (hnB .hn0 .hn32 + hnB (deltaHN .hn0 .hn32) y + hnB (deltaHN (deltaHN .hn0 .hn32) y) z))))) = true := rfl
private theorem hn_cert_row_33 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn33) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn33) && natBle (hnA (deltaHN .hn33 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn33) y)) && (natBle (hnA .hn33 z + hnA (deltaHN .hn33 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn33) y) z) && natBle (hnB .hn33 z + hnA (deltaHN .hn33 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn33 z) (deltaHN y z) + 1) (hnB .hn0 .hn33 + hnB (deltaHN .hn0 .hn33) y + hnB (deltaHN (deltaHN .hn0 .hn33) y) z))))) = true := rfl
private theorem hn_cert_row_34 : checkAll2_StateHN (fun y z => (!decide (deltaHN (deltaHN (deltaHN .hn0 .hn34) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 .hn34) && natBle (hnA (deltaHN .hn34 z) (deltaHN y z)) (hnA (deltaHN .hn0 .hn34) y)) && (natBle (hnA .hn34 z + hnA (deltaHN .hn34 z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 .hn34) y) z) && natBle (hnB .hn34 z + hnA (deltaHN .hn34 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn34 z) (deltaHN y z) + 1) (hnB .hn0 .hn34 + hnB (deltaHN .hn0 .hn34) y + hnB (deltaHN (deltaHN .hn0 .hn34) y) z))))) = true := rfl

private theorem hn_cert_bounds {x y z : StateHN}
    (hvalid : deltaHN (deltaHN (deltaHN .hn0 x) y) z ≠ .hn34) :
    1 ≤ hnA .hn0 x ∧
    hnA (deltaHN x z) (deltaHN y z) ≤ hnA (deltaHN .hn0 x) y ∧
    hnA x z + hnA (deltaHN x z) (deltaHN y z) * hnA y z ≤ hnA (deltaHN (deltaHN .hn0 x) y) z ∧
    hnB x z + hnA (deltaHN x z) (deltaHN y z) * hnB y z + hnB (deltaHN x z) (deltaHN y z) + 1 ≤
      hnB .hn0 x + hnB (deltaHN .hn0 x) y + hnB (deltaHN (deltaHN .hn0 x) y) z := by
  have h : (!decide (deltaHN (deltaHN (deltaHN .hn0 x) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 x) && natBle (hnA (deltaHN x z) (deltaHN y z)) (hnA (deltaHN .hn0 x) y)) && (natBle (hnA x z + hnA (deltaHN x z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 x) y) z) && natBle (hnB x z + hnA (deltaHN x z) (deltaHN y z) * hnB y z + hnB (deltaHN x z) (deltaHN y z) + 1) (hnB .hn0 x + hnB (deltaHN .hn0 x) y + hnB (deltaHN (deltaHN .hn0 x) y) z)))) = true :=
    match x with
    | .hn0 => checkAll2_StateHN_sound _ hn_cert_row_0 y z
    | .hn1 => checkAll2_StateHN_sound _ hn_cert_row_1 y z
    | .hn2 => checkAll2_StateHN_sound _ hn_cert_row_2 y z
    | .hn3 => checkAll2_StateHN_sound _ hn_cert_row_3 y z
    | .hn4 => checkAll2_StateHN_sound _ hn_cert_row_4 y z
    | .hn5 => checkAll2_StateHN_sound _ hn_cert_row_5 y z
    | .hn6 => checkAll2_StateHN_sound _ hn_cert_row_6 y z
    | .hn7 => checkAll2_StateHN_sound _ hn_cert_row_7 y z
    | .hn8 => checkAll2_StateHN_sound _ hn_cert_row_8 y z
    | .hn9 => checkAll2_StateHN_sound _ hn_cert_row_9 y z
    | .hn10 => checkAll2_StateHN_sound _ hn_cert_row_10 y z
    | .hn11 => checkAll2_StateHN_sound _ hn_cert_row_11 y z
    | .hn12 => checkAll2_StateHN_sound _ hn_cert_row_12 y z
    | .hn13 => checkAll2_StateHN_sound _ hn_cert_row_13 y z
    | .hn14 => checkAll2_StateHN_sound _ hn_cert_row_14 y z
    | .hn15 => checkAll2_StateHN_sound _ hn_cert_row_15 y z
    | .hn16 => checkAll2_StateHN_sound _ hn_cert_row_16 y z
    | .hn17 => checkAll2_StateHN_sound _ hn_cert_row_17 y z
    | .hn18 => checkAll2_StateHN_sound _ hn_cert_row_18 y z
    | .hn19 => checkAll2_StateHN_sound _ hn_cert_row_19 y z
    | .hn20 => checkAll2_StateHN_sound _ hn_cert_row_20 y z
    | .hn21 => checkAll2_StateHN_sound _ hn_cert_row_21 y z
    | .hn22 => checkAll2_StateHN_sound _ hn_cert_row_22 y z
    | .hn23 => checkAll2_StateHN_sound _ hn_cert_row_23 y z
    | .hn24 => checkAll2_StateHN_sound _ hn_cert_row_24 y z
    | .hn25 => checkAll2_StateHN_sound _ hn_cert_row_25 y z
    | .hn26 => checkAll2_StateHN_sound _ hn_cert_row_26 y z
    | .hn27 => checkAll2_StateHN_sound _ hn_cert_row_27 y z
    | .hn28 => checkAll2_StateHN_sound _ hn_cert_row_28 y z
    | .hn29 => checkAll2_StateHN_sound _ hn_cert_row_29 y z
    | .hn30 => checkAll2_StateHN_sound _ hn_cert_row_30 y z
    | .hn31 => checkAll2_StateHN_sound _ hn_cert_row_31 y z
    | .hn32 => checkAll2_StateHN_sound _ hn_cert_row_32 y z
    | .hn33 => checkAll2_StateHN_sound _ hn_cert_row_33 y z
    | .hn34 => checkAll2_StateHN_sound _ hn_cert_row_34 y z
  have h' := imp_decide hvalid h
  have hL := and_left h'
  have hR := and_right h'
  exact ⟨natBle_sound (and_left hL), natBle_sound (and_right hL), natBle_sound (and_left hR), natBle_sound (and_right hR)⟩

/-- Context-sensitive integer potential `muHN` decreasing strictly on every `HeadStep` when `evalHN < 34`. -/
def muHN : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app l r => muHN l + hnA (evalHN l) (evalHN r) * muHN r + hnB (evalHN l) (evalHN r)

private theorem cert_algebra_lemma
    (mx my mz a0 as1 as2 ax ay auv b0 bs1 bs2 bx by_ buv : Nat)
    (h1 : 1 ≤ a0)
    (h2 : auv ≤ as1)
    (h3 : ax + auv * ay ≤ as2)
    (h4 : bx + auv * by_ + buv + 1 ≤ b0 + bs1 + bs2) :
    ((mx + ax * mz + bx) + auv * (my + ay * mz + by_) + buv) + 1 ≤
    (((0 + a0 * mx + b0) + as1 * my + bs1) + as2 * mz + bs2) := by
  have p1 : mx ≤ a0 * mx := by
    have hm := Nat.mul_le_mul_right mx h1
    rw [Nat.one_mul mx] at hm
    exact hm
  have p2 : auv * my ≤ as1 * my := Nat.mul_le_mul_right my h2
  have p3 : ax * mz + (auv * ay) * mz ≤ as2 * mz := by
    rw [← Nat.add_mul ax (auv * ay) mz]
    exact Nat.mul_le_mul_right mz h3
  have hsum : (mx + auv * my) + ((ax * mz + (auv * ay) * mz) + (bx + auv * by_ + buv + 1)) ≤
      (a0 * mx + as1 * my) + (as2 * mz + (b0 + bs1 + bs2)) :=
    Nat.add_le_add (Nat.add_le_add p1 p2) (Nat.add_le_add p3 h4)
  have hL : ((mx + ax * mz + bx) + auv * (my + ay * mz + by_) + buv) + 1 =
      (mx + auv * my) + ((ax * mz + (auv * ay) * mz) + (bx + auv * by_ + buv + 1)) := by
    rw [Nat.mul_add auv (my + ay * mz) by_, Nat.mul_add auv my (ay * mz), ← Nat.mul_assoc auv ay mz]
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hR : (((0 + a0 * mx + b0) + as1 * my + bs1) + as2 * mz + bs2) =
      (a0 * mx + as1 * my) + (as2 * mz + (b0 + bs1 + bs2)) := by
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [hL, hR]
  exact hsum

theorem muHN_headStep_drop {m m' : Term} (hs : HeadStep m m') (hval : evalHN m ≠ .hn34) :
    muHN m' + 1 ≤ muHN m := by
  induction hs with
  | root x y z =>
    have ⟨h1, h2, h3, h4⟩ := hn_cert_bounds hval
    exact cert_algebra_lemma
      (muHN x) (muHN y) (muHN z)
      (hnA .hn0 (evalHN x))
      (hnA (deltaHN .hn0 (evalHN x)) (evalHN y))
      (hnA (deltaHN (deltaHN .hn0 (evalHN x)) (evalHN y)) (evalHN z))
      (hnA (evalHN x) (evalHN z))
      (hnA (evalHN y) (evalHN z))
      (hnA (deltaHN (evalHN x) (evalHN z)) (deltaHN (evalHN y) (evalHN z)))
      (hnB .hn0 (evalHN x))
      (hnB (deltaHN .hn0 (evalHN x)) (evalHN y))
      (hnB (deltaHN (deltaHN .hn0 (evalHN x)) (evalHN y)) (evalHN z))
      (hnB (evalHN x) (evalHN z))
      (hnB (evalHN y) (evalHN z))
      (hnB (deltaHN (evalHN x) (evalHN z)) (deltaHN (evalHN y) (evalHN z)))
      h1 h2 h3 h4
  | @left l l' r hl ih =>
    have hl_val : evalHN l ≠ .hn34 := deltaHN_ne_hn34_left hval
    have hdrop := ih hl_val
    have heq_l : evalHN l' = evalHN l := (evalHN_step (headStep_to_step hl)).symm
    change (muHN l' + hnA (evalHN l') (evalHN r) * muHN r + hnB (evalHN l') (evalHN r)) + 1 ≤
      muHN l + hnA (evalHN l) (evalHN r) * muHN r + hnB (evalHN l) (evalHN r)
    rw [heq_l]
    have h1 := Nat.add_le_add_right hdrop (hnA (evalHN l) (evalHN r) * muHN r + hnB (evalHN l) (evalHN r))
    have hL : (muHN l' + hnA (evalHN l) (evalHN r) * muHN r + hnB (evalHN l) (evalHN r)) + 1 =
        (muHN l' + 1) + (hnA (evalHN l) (evalHN r) * muHN r + hnB (evalHN l) (evalHN r)) := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [hL, Nat.add_assoc (muHN l)]
    exact h1

def headNormalizeAux : Nat → Term → Term
  | 0, t => t
  | fuel + 1, t =>
    match headStepOpt t with
    | none => t
    | some t' => headNormalizeAux fuel t'

private theorem headNormalizeAux_spec :
    ∀ (fuel : Nat) {t : Term},
      noVars t = true →
      evalHN t ≠ .hn34 →
      muHN t < fuel →
      HeadReduces t (headNormalizeAux fuel t) ∧ IsClosedHNF (headNormalizeAux fuel t) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ hlt
    cases hlt
  | succ fuel ih =>
    intro t hv hval hlt
    simp only [headNormalizeAux]
    cases hh : headStepOpt t with
    | none =>
      exact ⟨HeadReduces.refl t, hv, headStepOpt_none_spineLen hv hh⟩
    | some t' =>
      have hs : HeadStep t t' := headStepOpt_some hh
      have hv' : noVars t' = true := noVars_step (headStep_to_step hs) hv
      have hval' : evalHN t' ≠ .hn34 := by
        rw [← evalHN_step (headStep_to_step hs)]
        exact hval
      have hdrop : muHN t' + 1 ≤ muHN t := muHN_headStep_drop hs hval
      have hlt' : muHN t' < fuel := Nat.lt_of_succ_lt_succ (Nat.lt_of_le_of_lt hdrop hlt)
      obtain ⟨hred, hhnf⟩ := ih hv' hval' hlt'
      exact ⟨HeadReduces.next hs hred, hhnf⟩

def headNormalize (t : Term) : Term :=
  headNormalizeAux (muHN t + 1) t

theorem headNormalize_reduces_hnf {t : Term} (hv : noVars t = true) (hval : evalHN t ≠ .hn34) :
    HeadReduces t (headNormalize t) ∧ IsClosedHNF (headNormalize t) :=
  headNormalizeAux_spec (muHN t + 1) hv hval (Nat.lt_succ_self (muHN t))

inductive HeadStepsN : Nat → Term → Term → Prop where
  | zero (t : Term) : HeadStepsN 0 t t
  | succ {k : Nat} {a b c : Term} : HeadStep a b → HeadStepsN k b c → HeadStepsN (k + 1) a c

theorem headStepsN_to_reduces {k : Nat} {a b : Term} (h : HeadStepsN k a b) : Reduces a b := by
  induction h with
  | zero _ => exact Reduces.refl _
  | succ hs _ ih => exact Reduces.next (headStep_to_step hs) ih

theorem evalHN_hn34_has_headStep {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) :
    ∃ t', headStepOpt t = some t' ∧ HeadStep t t' ∧ noVars t' = true ∧ evalHN t' = .hn34 := by
  cases hh : headStepOpt t with
  | none =>
    exfalso
    exact closed_hnf_evalHN_ne_hn34 hv (headStepOpt_none_spineLen hv hh) h34
  | some t' =>
    have hs := headStepOpt_some hh
    exact ⟨t', rfl, hs, noVars_step (headStep_to_step hs) hv,
      (evalHN_step (headStep_to_step hs)).symm.trans h34⟩

theorem evalHN_hn34_infinite_head {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) :
    ∀ k, ∃ u, HeadStepsN k t u := by
  intro k
  induction k generalizing t with
  | zero => exact ⟨t, HeadStepsN.zero t⟩
  | succ k ih =>
    obtain ⟨t', _, hs, hv', h34'⟩ := evalHN_hn34_has_headStep hv h34
    obtain ⟨u, hrest⟩ := ih hv' h34'
    exact ⟨u, HeadStepsN.succ hs hrest⟩

/-- **Complete Constructive Resolution of Barendregt, Endrullis, Klop, and Waldmann's Open Problem 10
    (2018, *Dance of the Starlings*, p. 84)**:
    For every closed pure-`S` term `t`, `t` has a Head Normal Form iff `evalHN t ≠ .hn34`,
    and `evalHN t = .hn34` iff `t` admits arbitrarily long head reduction sequences. -/
theorem barendregt_open_problem_10 {t : Term} (hv : noVars t = true) :
    (HasHNF t ↔ evalHN t ≠ .hn34) ∧ (evalHN t = .hn34 ↔ ∀ k, ∃ u, HeadStepsN k t u) := by
  have hhnf_iff : HasHNF t ↔ evalHN t ≠ .hn34 := by
    constructor
    · intro ⟨h, hred, hsl⟩
      rw [evalHN_reduces hred]
      exact closed_hnf_evalHN_ne_hn34 (noVars_reduces hred hv) hsl
    · intro hval
      obtain ⟨hred, _, hsl⟩ := headNormalize_reduces_hnf hv hval
      exact ⟨headNormalize t, headReduces_to_reduces hred, hsl⟩
  refine ⟨hhnf_iff, ?_⟩
  constructor
  · exact evalHN_hn34_infinite_head hv
  · intro hinf
    exact if h34 : evalHN t = .hn34 then h34
    else by
      exfalso
      obtain ⟨u, hsteps⟩ := hinf (muHN t + 1)
      have hdrop_k : ∀ {k a b}, HeadStepsN k a b → evalHN a ≠ .hn34 → muHN b + k ≤ muHN a := by
        intro k a b hs
        induction hs with
        | zero _ => intro _; exact Nat.le_refl _
        | @succ k0 a0 b0 c0 hs0 hrest ih =>
          intro hval0
          have hd1 := muHN_headStep_drop hs0 hval0
          have hval1 : evalHN b0 ≠ .hn34 := by
            rw [← evalHN_step (headStep_to_step hs0)]
            exact hval0
          have hd2 := ih hval1
          have h1 := Nat.add_le_add_right hd2 1
          rw [Nat.add_assoc (muHN c0) k0 1] at h1
          exact Nat.le_trans h1 hd1
      have hbad := hdrop_k hsteps h34
      have hgt : muHN t < muHN u + (muHN t + 1) := by
        rw [← Nat.add_assoc (muHN u) (muHN t) 1, Nat.add_comm (muHN u) (muHN t), Nat.add_assoc (muHN t) (muHN u) 1]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (muHN t)) (by
          rw [Nat.add_comm (muHN u) 1, ← Nat.add_assoc (muHN t) 1 (muHN u)]
          exact Nat.le_add_right (muHN t + 1) (muHN u))
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hgt hbad)

def dagRankHN : StateHN → Nat
  | .hn0 => 7
  | .hn1 => 6
  | .hn2 => 4
  | .hn3 => 4
  | .hn4 => 3
  | .hn5 => 2
  | .hn6 => 5
  | .hn7 => 5
  | .hn8 => 2
  | .hn9 => 2
  | .hn10 => 1
  | .hn11 => 4
  | .hn12 => 3
  | .hn13 => 3
  | .hn14 => 3
  | .hn15 => 2
  | .hn16 => 3
  | .hn17 => 3
  | .hn18 => 3
  | .hn19 => 3
  | .hn20 => 2
  | .hn21 => 2
  | .hn22 => 2
  | .hn23 => 0
  | .hn24 => 1
  | .hn25 => 1
  | .hn26 => 4
  | .hn27 => 2
  | .hn28 => 4
  | .hn29 => 2
  | .hn30 => 3
  | .hn31 => 2
  | .hn32 => 2
  | .hn33 => 1
  | .hn34 => 0

def canReach13HN : StateHN → Bool
  | .hn0 => true | .hn1 => true | .hn6 => true | .hn11 => true | .hn13 => true
  | _ => false

private theorem g_spine_dag_chk : checkAll2_StateHN (fun x y =>
    (!decide (x ≠ .hn34) || !decide (deltaHN x y ≠ .hn34) ||
      decide (x = .hn13 ∧ y = .hn0 ∧ deltaHN x y = .hn13) ||
      natBle (dagRankHN (deltaHN x y) + 1) (dagRankHN x))) = true := rfl

private theorem canReach13_pred_chk : checkAll2_StateHN (fun x y =>
    (!canReach13HN (deltaHN x y) || canReach13HN x)) = true := rfl

private theorem canReach13_from0_chk : checkAll1_StateHN (fun y =>
    (!canReach13HN (deltaHN .hn0 y) || decide (y = .hn0))) = true := rfl

private theorem dagRank_from0_chk : checkAll1_StateHN (fun y =>
    natBle (dagRankHN (deltaHN .hn0 y)) 6) = true := rfl

theorem g_spine_dag_property {x y : StateHN} (hx : x ≠ .hn34) (hxy : deltaHN x y ≠ .hn34) :
    (x = .hn13 ∧ y = .hn0 ∧ deltaHN x y = .hn13) ∨ dagRankHN (deltaHN x y) < dagRankHN x := by
  have h := checkAll2_StateHN_sound _ g_spine_dag_chk x y
  rw [decide_eq_true hx, decide_eq_true hxy] at h
  simp only [Bool.not_true, Bool.false_or] at h
  cases hd : decide (x = .hn13 ∧ y = .hn0 ∧ deltaHN x y = .hn13) with
  | true => exact Or.inl (of_decide_eq_true hd)
  | false =>
    rw [hd, Bool.false_or] at h
    exact Or.inr (natBle_sound h)

/-! ## 4. Footnote 4 (Decidability of RNF) & 5-Composite-Argument Head-Consumption / RNF Ceiling -/

theorem closed_headLeaf_eq_s {t : Term} (hv : noVars t = true) : headLeaf t = S := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a _ iha _ => exact iha ((Bool.and_eq_true _ _).mp hv).1

private theorem spineLen_le_2_step_eq {a b : Term} (hs : Step a b)
    (hhead : headLeaf a = S) (hsl : spineLen a ≤ 2) :
    spineLen b = spineLen a ∧ headLeaf b = S := by
  induction hs with
  | root x y z =>
    change 3 ≤ 2 at hsl
    cases hsl with
    | step h1 => cases h1 with | step h2 => cases h2
  | @left l l' r hl ih =>
    have hll : spineLen l ≤ 2 := by
      change 1 + spineLen l ≤ 2 at hsl
      exact Nat.le_trans (Nat.le_add_left (spineLen l) 1) hsl
    have ⟨hsp, hhd⟩ := ih hhead hll
    exact ⟨congrArg (1 + ·) hsp, hhd⟩
  | right _ _ =>
    exact ⟨rfl, hhead⟩

private theorem spineLen_le_2_reduces_eq {a b : Term} (hr : Reduces a b)
    (hhead : headLeaf a = S) (hsl : spineLen a ≤ 2) : spineLen b = spineLen a := by
  induction hr with
  | refl _ => rfl
  | next hs _ ih =>
    have ⟨hsp, hhd⟩ := spineLen_le_2_step_eq hs hhead hsl
    have hsl' : spineLen _ ≤ 2 := hsp.symm ▸ hsl
    exact (ih hhd hsl').trans hsp

theorem reduces_app_no_sab {m n : Term} (hred : Reduces m n) :
    ∀ (a b : Term), (∀ p q, ¬ Reduces a (S ⋅ p ⋅ q)) → m = a ⋅ b →
      ∃ a' b', n = a' ⋅ b' ∧ Reduces a a' ∧ Reduces b b' := by
  induction hred with
  | refl _ =>
    intro a b _ hm
    exact ⟨a, b, hm, Reduces.refl a, Reduces.refl b⟩
  | @next _ m1 _ hs _ ih =>
    intro a b hno hm
    subst hm
    cases hs with
    | root p q _ => exfalso; exact hno p q (Reduces.refl _)
    | @left _ a1 _ ha1 =>
      have hno1 : ∀ p q, ¬ Reduces a1 (S ⋅ p ⋅ q) := fun p q hr => hno p q (Reduces.next ha1 hr)
      obtain ⟨a', b', hn, hra, hrb⟩ := ih a1 b hno1 rfl
      exact ⟨a', b', hn, Reduces.next ha1 hra, hrb⟩
    | @right _ _ b1 hb1 =>
      obtain ⟨a', b', hn, hra, hrb⟩ := ih a b1 hno rfl
      exact ⟨a', b', hn, hra, Reduces.next hb1 hrb⟩

/-- **Footnote 4 of Barendregt, Endrullis, Klop, and Waldmann (2018, p. 103 — Decidability of RNF)**:
    A closed pure-`S` term `t` is in Root Normal Form (`¬ ∃ x y z, t →* S ⋅ x ⋅ y ⋅ z`) iff
    `spineLen t ≤ 2` or `t = a ⋅ b` with `evalHN a = .hn34`. -/
theorem footnote4_rnf_iff {t : Term} (hv : noVars t = true) :
    IsRootNormalForm t ↔ (spineLen t ≤ 2 ∨ ∃ a b, t = a ⋅ b ∧ evalHN a = .hn34) := by
  constructor
  · intro hrnf
    exact if hsl : spineLen t ≤ 2 then Or.inl hsl
    else by
      cases t with
      | s => exfalso; exact hsl (Nat.zero_le 2)
      | var _ => cases hv
      | app a b =>
        have hva := ((Bool.and_eq_true _ _).mp hv).1
        exact if ha34 : evalHN a = .hn34 then Or.inr ⟨a, b, rfl, ha34⟩
        else by
          exfalso
          have ⟨h, hred_a, hsl_h⟩ := (barendregt_open_problem_10 hva).1.mpr ha34
          have hv_h := noVars_reduces hred_a hva
          -- Since `¬ spineLen (a ⋅ b) ≤ 2`, `spineLen a ≥ 2`, so `a = a1 ⋅ a2 ⋅ a3`!
          have ha_sp2 : 2 ≤ spineLen a := by
            exact if hle1 : spineLen a ≤ 1 then
              False.elim (hsl (Nat.add_le_add_left hle1 1))
            else
              match hsp : spineLen a with
              | 0 => False.elim (hle1 (by rw [hsp]; exact Nat.zero_le 1))
              | 1 => False.elim (hle1 (by rw [hsp]; exact Nat.le_refl 1))
              | _ + 2 => Nat.le_add_left 2 _
          have ha_ge2 : hasSpineGe2 a = true := by
            cases a with
            | s => cases ha_sp2
            | var _ => cases hva
            | app a1 a2 =>
              cases a1 with
              | s => exfalso; exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ ha_sp2)
              | var _ => cases ((Bool.and_eq_true _ _).mp hva).1
              | app _ _ => rfl
          have hh_ge2 : hasSpineGe2 h = true := spineGe2_preserved_reduces hred_a ha_ge2
          rcases closed_spineLen_le_2_shapes hv_h hsl_h with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
          · cases hh_ge2
          · cases hh_ge2
          · exact hrnf ⟨x, y, b, reduces_left hred_a b⟩
  · intro hcond ⟨x, y, z, hred⟩
    rcases hcond with hsl | ⟨a, b, rfl, ha34⟩
    · have hsp := spineLen_le_2_reduces_eq hred (closed_headLeaf_eq_s hv) hsl
      have h3le2 : 3 ≤ 2 := by
        have : spineLen (S ⋅ x ⋅ y ⋅ z) = 3 := rfl
        rw [← this, hsp]
        exact hsl
      cases h3le2 with
      | step h1 => cases h1 with | step h2 => cases h2
    · have hva := ((Bool.and_eq_true _ _).mp hv).1
      have hno : ∀ p q, ¬ Reduces a (S ⋅ p ⋅ q) := by
        intro p q hr
        have hnhnf : ¬ HasHNF a := fun hh => ((barendregt_open_problem_10 hva).1.mp hh) ha34
        exact hnhnf ⟨S ⋅ p ⋅ q, hr, Nat.le_refl 2⟩
      obtain ⟨a', b', heq, hra, _⟩ := reduces_app_no_sab hred a b hno rfl
      injection heq with ha' _
      exact hno x y (ha' ▸ hra)

private def inCompStep1 : StateHN → Bool
  | .hn2 => true | .hn3 => true | .hn4 => true | .hn5 => true | .hn7 => true | .hn8 => true | .hn9 => true | .hn10 => true | .hn11 => true | .hn12 => true | .hn13 => true | .hn15 => true | .hn16 => true | .hn17 => true | .hn19 => true | .hn20 => true | .hn21 => true | .hn22 => true | .hn23 => true | .hn24 => true | .hn25 => true | .hn27 => true | .hn28 => true | .hn29 => true | .hn30 => true | .hn34 => true
  | _ => false

private def inCompStep2 : StateHN → Bool
  | .hn8 => true | .hn9 => true | .hn10 => true | .hn16 => true | .hn17 => true | .hn20 => true | .hn22 => true | .hn23 => true | .hn24 => true | .hn25 => true | .hn28 => true | .hn29 => true | .hn30 => true | .hn34 => true
  | _ => false

private def inCompStep3 : StateHN → Bool
  | .hn23 => true | .hn24 => true | .hn29 => true | .hn34 => true
  | _ => false

private def inCompStep4 : StateHN → Bool
  | .hn23 => true | .hn34 => true
  | _ => false

private theorem comp_step_1_chk : checkAll2_StateHN (fun s u => (!decide (u ≠ .hn0) || inCompStep1 (deltaHN s u))) = true := rfl
private theorem comp_step_2_chk : checkAll2_StateHN (fun s u => (!inCompStep1 s || !decide (u ≠ .hn0) || inCompStep2 (deltaHN s u))) = true := rfl
private theorem comp_step_3_chk : checkAll2_StateHN (fun s u => (!inCompStep2 s || !decide (u ≠ .hn0) || inCompStep3 (deltaHN s u))) = true := rfl
private theorem comp_step_4_chk : checkAll2_StateHN (fun s u => (!inCompStep3 s || !decide (u ≠ .hn0) || inCompStep4 (deltaHN s u))) = true := rfl
private theorem comp_step_5_chk : checkAll2_StateHN (fun s u => (!inCompStep4 s || !decide (u ≠ .hn0) || decide (deltaHN s u = .hn34))) = true := rfl

theorem five_non_hn0_args_state (s u1 u2 u3 u4 u5 : StateHN)
    (h1 : u1 ≠ .hn0) (h2 : u2 ≠ .hn0) (h3 : u3 ≠ .hn0) (h4 : u4 ≠ .hn0) (h5 : u5 ≠ .hn0) :
    deltaHN (deltaHN (deltaHN (deltaHN (deltaHN s u1) u2) u3) u4) u5 = .hn34 := by
  have c1 := checkAll2_StateHN_sound _ comp_step_1_chk s u1
  rw [decide_eq_true h1] at c1
  simp only [Bool.not_true, Bool.false_or] at c1
  have c2 := checkAll2_StateHN_sound _ comp_step_2_chk (deltaHN s u1) u2
  rw [c1, decide_eq_true h2] at c2
  simp only [Bool.not_true, Bool.false_or] at c2
  have c3 := checkAll2_StateHN_sound _ comp_step_3_chk (deltaHN (deltaHN s u1) u2) u3
  rw [c2, decide_eq_true h3] at c3
  simp only [Bool.not_true, Bool.false_or] at c3
  have c4 := checkAll2_StateHN_sound _ comp_step_4_chk (deltaHN (deltaHN (deltaHN s u1) u2) u3) u4
  rw [c3, decide_eq_true h4] at c4
  simp only [Bool.not_true, Bool.false_or] at c4
  have c5 := checkAll2_StateHN_sound _ comp_step_5_chk (deltaHN (deltaHN (deltaHN (deltaHN s u1) u2) u3) u4) u5
  rw [c4, decide_eq_true h5] at c5
  simp only [Bool.not_true, Bool.false_or] at c5
  exact of_decide_eq_true c5

/-- **5-Composite-Argument Head-Consumption Ceiling**:
    Any closed pure-`S` term `m` applied to 5 closed composite (`≠ S`) arguments `u1..u5`
    evaluates to `.hn34` (has no Head Normal Form), and with any closed 6th argument `u6`
    is guaranteed to be in Root Normal Form (`u6` is never consumed at the root). -/
theorem five_composite_args_hn34 {m u1 u2 u3 u4 u5 : Term}
    (hm : noVars m = true)
    (hv1 : noVars u1 = true) (hv2 : noVars u2 = true) (hv3 : noVars u3 = true)
    (hv4 : noVars u4 = true) (hv5 : noVars u5 = true)
    (hn1 : u1 ≠ S) (hn2 : u2 ≠ S) (hn3 : u3 ≠ S) (hn4 : u4 ≠ S) (hn5 : u5 ≠ S) :
    evalHN (m ⋅ u1 ⋅ u2 ⋅ u3 ⋅ u4 ⋅ u5) = .hn34 ∧ ¬ HasHNF (m ⋅ u1 ⋅ u2 ⋅ u3 ⋅ u4 ⋅ u5) := by
  have hst : evalHN (m ⋅ u1 ⋅ u2 ⋅ u3 ⋅ u4 ⋅ u5) = .hn34 :=
    five_non_hn0_args_state (evalHN m) (evalHN u1) (evalHN u2) (evalHN u3) (evalHN u4) (evalHN u5)
      (fun h => hn1 ((evalHN_eq_hn0_iff hv1).mp h))
      (fun h => hn2 ((evalHN_eq_hn0_iff hv2).mp h))
      (fun h => hn3 ((evalHN_eq_hn0_iff hv3).mp h))
      (fun h => hn4 ((evalHN_eq_hn0_iff hv4).mp h))
      (fun h => hn5 ((evalHN_eq_hn0_iff hv5).mp h))
  have hv_all : noVars (m ⋅ u1 ⋅ u2 ⋅ u3 ⋅ u4 ⋅ u5) = true := by
    simp only [noVars, hm, hv1, hv2, hv3, hv4, hv5, Bool.and_self]
  exact ⟨hst, fun hh => ((barendregt_open_problem_10 hv_all).1.mp hh) hst⟩

theorem five_composite_args_rnf {m u1 u2 u3 u4 u5 u6 : Term}
    (hm : noVars m = true)
    (hv1 : noVars u1 = true) (hv2 : noVars u2 = true) (hv3 : noVars u3 = true)
    (hv4 : noVars u4 = true) (hv5 : noVars u5 = true) (hv6 : noVars u6 = true)
    (hn1 : u1 ≠ S) (hn2 : u2 ≠ S) (hn3 : u3 ≠ S) (hn4 : u4 ≠ S) (hn5 : u5 ≠ S) :
    IsRootNormalForm (m ⋅ u1 ⋅ u2 ⋅ u3 ⋅ u4 ⋅ u5 ⋅ u6) := by
  have ⟨hst, _⟩ := five_composite_args_hn34 hm hv1 hv2 hv3 hv4 hv5 hn1 hn2 hn3 hn4 hn5
  have hv_all : noVars (m ⋅ u1 ⋅ u2 ⋅ u3 ⋅ u4 ⋅ u5 ⋅ u6) = true := by
    simp only [noVars, hm, hv1, hv2, hv3, hv4, hv5, hv6, Bool.and_self]
  exact (footnote4_rnf_iff hv_all).mpr (Or.inr ⟨m ⋅ u1 ⋅ u2 ⋅ u3 ⋅ u4 ⋅ u5, u6, rfl, hst⟩)

/-! ## 5. Exact 112-State Joint S-Algebra (`A_SN × A_HN`: `112 = 94 + 17 + 1`, `SN ⊂ HN`) -/

def isJointPair : StateSN → StateHN → Bool
  | .sn0, y => match y with | .hn0 => true | _ => false
  | .sn1, y => match y with | .hn1 => true | _ => false
  | .sn2, y => match y with | .hn2 => true | _ => false
  | .sn3, y => match y with | .hn3 => true | _ => false
  | .sn4, y => match y with | .hn4 => true | .hn12 => true | _ => false
  | .sn5, y => match y with | .hn5 => true | .hn8 => true | .hn12 => true | .hn13 => true | _ => false
  | .sn6, y => match y with | .hn5 => true | .hn8 => true | .hn9 => true | .hn10 => true | .hn12 => true | .hn13 => true | .hn19 => true | .hn21 => true | .hn27 => true | _ => false
  | .sn7, y => match y with | .hn6 => true | _ => false
  | .sn8, y => match y with | .hn7 => true | _ => false
  | .sn9, y => match y with | .hn11 => true | _ => false
  | .sn10, y => match y with | .hn12 => true | _ => false
  | .sn11, y => match y with | .hn13 => true | _ => false
  | .sn12, y => match y with | .hn12 => true | _ => false
  | .sn13, y => match y with | .hn13 => true | _ => false
  | .sn14, y => match y with | .hn13 => true | _ => false
  | .sn15, y => match y with | .hn13 => true | _ => false
  | .sn16, y => match y with | .hn13 => true | _ => false
  | .sn17, y => match y with | .hn13 => true | _ => false
  | .sn18, y => match y with | .hn13 => true | _ => false
  | .sn19, y => match y with | .hn13 => true | .hn14 => true | _ => false
  | .sn20, y => match y with | .hn12 => true | .hn15 => true | _ => false
  | .sn21, y => match y with | .hn12 => true | .hn13 => true | .hn27 => true | _ => false
  | .sn22, y => match y with | .hn16 => true | _ => false
  | .sn23, y => match y with | .hn13 => true | _ => false
  | .sn24, y => match y with | .hn8 => true | .hn13 => true | _ => false
  | .sn25, y => match y with | .hn9 => true | .hn10 => true | .hn13 => true | .hn17 => true | _ => false
  | .sn26, y => match y with | .hn13 => true | .hn17 => true | _ => false
  | .sn27, y => match y with | .hn13 => true | .hn18 => true | _ => false
  | .sn28, y => match y with | .hn13 => true | .hn20 => true | _ => false
  | .sn29, y => match y with | .hn10 => true | .hn13 => true | .hn17 => true | .hn20 => true | .hn22 => true | .hn24 => true | .hn25 => true | .hn29 => true | .hn30 => true | .hn31 => true | _ => false
  | .sn30, y => match y with | .hn10 => true | .hn13 => true | .hn17 => true | .hn20 => true | .hn22 => true | .hn23 => true | .hn24 => true | .hn25 => true | .hn29 => true | .hn30 => true | .hn31 => true | .hn32 => true | .hn33 => true | _ => false
  | .sn31, y => match y with | .hn8 => true | .hn10 => true | .hn13 => true | .hn17 => true | .hn29 => true | .hn31 => true | _ => false
  | .sn32, y => match y with | .hn13 => true | .hn26 => true | _ => false
  | .sn33, y => match y with | .hn13 => true | .hn28 => true | _ => false
  | .sn34, y => match y with | .hn13 => true | .hn30 => true | _ => false
  | .sn35, y => match y with | .hn13 => true | .hn29 => true | _ => false
  | .sn36, y => match y with | .hn13 => true | .hn31 => true | _ => false
  | .sn37, y => match y with | .hn13 => true | .hn29 => true | .hn31 => true | _ => false
  | .sn38, y => match y with | .hn0 => false | .hn1 => false | .hn2 => false | .hn3 => false | .hn4 => false | .hn5 => false | .hn6 => false | .hn7 => false | .hn11 => false | .hn14 => false | .hn15 => false | .hn16 => false | .hn18 => false | .hn19 => false | .hn26 => false | .hn28 => false | .hn32 => false | _ => true

def JointInhabited (s : StateSN) (h : StateHN) : Prop :=
  ∃ t : Term, noVars t = true ∧ evalSN t = s ∧ evalHN t = h

private theorem j_inh_app {s1 s2 : StateSN} {h1 h2 : StateHN}
    (hp1 : JointInhabited s1 h1) (hp2 : JointInhabited s2 h2) :
    JointInhabited (deltaSN s1 s2) (deltaHN h1 h2) := by
  obtain ⟨t1, hv1, es1, eh1⟩ := hp1
  obtain ⟨t2, hv2, es2, eh2⟩ := hp2
  exact ⟨t1 ⋅ t2, (Bool.and_eq_true _ _).mpr ⟨hv1, hv2⟩,
    by simp only [evalSN, es1, es2], by simp only [evalHN, eh1, eh2]⟩

private theorem j_wit_0 : JointInhabited .sn0 .hn0 := ⟨S, rfl, rfl, rfl⟩
private theorem j_wit_1 : JointInhabited .sn1 .hn1 := j_inh_app j_wit_0 j_wit_0
private theorem j_wit_2 : JointInhabited .sn7 .hn6 := j_inh_app j_wit_1 j_wit_0
private theorem j_wit_3 : JointInhabited .sn2 .hn2 := j_inh_app j_wit_0 j_wit_1
private theorem j_wit_4 : JointInhabited .sn9 .hn11 := j_inh_app j_wit_1 j_wit_1
private theorem j_wit_5 : JointInhabited .sn8 .hn7 := j_inh_app j_wit_0 j_wit_2
private theorem j_wit_6 : JointInhabited .sn24 .hn8 := j_inh_app j_wit_2 j_wit_1
private theorem j_wit_7 : JointInhabited .sn15 .hn13 := j_inh_app j_wit_1 j_wit_2
private theorem j_wit_8 : JointInhabited .sn29 .hn22 := j_inh_app j_wit_2 j_wit_2
private theorem j_wit_9 : JointInhabited .sn29 .hn20 := j_inh_app j_wit_2 j_wit_3
private theorem j_wit_10 : JointInhabited .sn26 .hn17 := j_inh_app j_wit_3 j_wit_2
private theorem j_wit_11 : JointInhabited .sn34 .hn30 := j_inh_app j_wit_4 j_wit_2
private theorem j_wit_12 : JointInhabited .sn19 .hn14 := j_inh_app j_wit_3 j_wit_0
private theorem j_wit_13 : JointInhabited .sn3 .hn3 := j_inh_app j_wit_0 j_wit_3
private theorem j_wit_14 : JointInhabited .sn22 .hn16 := j_inh_app j_wit_3 j_wit_1
private theorem j_wit_15 : JointInhabited .sn11 .hn13 := j_inh_app j_wit_1 j_wit_3
private theorem j_wit_16 : JointInhabited .sn25 .hn9 := j_inh_app j_wit_3 j_wit_5
private theorem j_wit_17 : JointInhabited .sn29 .hn29 := j_inh_app j_wit_5 j_wit_3
private theorem j_wit_18 : JointInhabited .sn25 .hn10 := j_inh_app j_wit_3 j_wit_6
private theorem j_wit_19 : JointInhabited .sn30 .hn23 := j_inh_app j_wit_6 j_wit_3
private theorem j_wit_20 : JointInhabited .sn30 .hn20 := j_inh_app j_wit_7 j_wit_3
private theorem j_wit_21 : JointInhabited .sn29 .hn10 := j_inh_app j_wit_3 j_wit_8
private theorem j_wit_22 : JointInhabited .sn38 .hn23 := j_inh_app j_wit_8 j_wit_3
private theorem j_wit_23 : JointInhabited .sn10 .hn12 := j_inh_app j_wit_0 j_wit_4
private theorem j_wit_24 : JointInhabited .sn35 .hn29 := j_inh_app j_wit_4 j_wit_4
private theorem j_wit_25 : JointInhabited .sn29 .hn24 := j_inh_app j_wit_7 j_wit_4
private theorem j_wit_26 : JointInhabited .sn38 .hn34 := j_inh_app j_wit_8 j_wit_4
private theorem j_wit_27 : JointInhabited .sn30 .hn24 := j_inh_app j_wit_4 j_wit_12
private theorem j_wit_28 : JointInhabited .sn32 .hn26 := j_inh_app j_wit_5 j_wit_0
private theorem j_wit_29 : JointInhabited .sn5 .hn8 := j_inh_app j_wit_0 j_wit_5
private theorem j_wit_30 : JointInhabited .sn33 .hn28 := j_inh_app j_wit_5 j_wit_1
private theorem j_wit_31 : JointInhabited .sn16 .hn13 := j_inh_app j_wit_1 j_wit_5
private theorem j_wit_32 : JointInhabited .sn29 .hn30 := j_inh_app j_wit_5 j_wit_15
private theorem j_wit_33 : JointInhabited .sn38 .hn24 := j_inh_app j_wit_5 j_wit_22
private theorem j_wit_34 : JointInhabited .sn6 .hn9 := j_inh_app j_wit_0 j_wit_6
private theorem j_wit_35 : JointInhabited .sn24 .hn13 := j_inh_app j_wit_1 j_wit_6
private theorem j_wit_36 : JointInhabited .sn30 .hn10 := j_inh_app j_wit_7 j_wit_13
private theorem j_wit_37 : JointInhabited .sn30 .hn25 := j_inh_app j_wit_7 j_wit_28
private theorem j_wit_38 : JointInhabited .sn6 .hn10 := j_inh_app j_wit_0 j_wit_8
private theorem j_wit_39 : JointInhabited .sn29 .hn13 := j_inh_app j_wit_1 j_wit_8
private theorem j_wit_40 : JointInhabited .sn6 .hn21 := j_inh_app j_wit_0 j_wit_9
private theorem j_wit_41 : JointInhabited .sn26 .hn13 := j_inh_app j_wit_1 j_wit_10
private theorem j_wit_42 : JointInhabited .sn34 .hn13 := j_inh_app j_wit_1 j_wit_11
private theorem j_wit_43 : JointInhabited .sn20 .hn15 := j_inh_app j_wit_0 j_wit_12
private theorem j_wit_44 : JointInhabited .sn19 .hn13 := j_inh_app j_wit_1 j_wit_12
private theorem j_wit_45 : JointInhabited .sn27 .hn18 := j_inh_app j_wit_13 j_wit_0
private theorem j_wit_46 : JointInhabited .sn4 .hn4 := j_inh_app j_wit_0 j_wit_13
private theorem j_wit_47 : JointInhabited .sn28 .hn20 := j_inh_app j_wit_13 j_wit_1
private theorem j_wit_48 : JointInhabited .sn13 .hn13 := j_inh_app j_wit_1 j_wit_13
private theorem j_wit_49 : JointInhabited .sn38 .hn20 := j_inh_app j_wit_13 j_wit_22
private theorem j_wit_50 : JointInhabited .sn38 .hn10 := j_inh_app j_wit_39 j_wit_13
private theorem j_wit_51 : JointInhabited .sn6 .hn8 := j_inh_app j_wit_0 j_wit_14
private theorem j_wit_52 : JointInhabited .sn23 .hn13 := j_inh_app j_wit_1 j_wit_14
private theorem j_wit_53 : JointInhabited .sn12 .hn12 := j_inh_app j_wit_0 j_wit_15
private theorem j_wit_54 : JointInhabited .sn30 .hn22 := j_inh_app j_wit_2 j_wit_15
private theorem j_wit_55 : JointInhabited .sn25 .hn17 := j_inh_app j_wit_3 j_wit_15
private theorem j_wit_56 : JointInhabited .sn25 .hn13 := j_inh_app j_wit_1 j_wit_16
private theorem j_wit_57 : JointInhabited .sn30 .hn13 := j_inh_app j_wit_1 j_wit_19
private theorem j_wit_58 : JointInhabited .sn38 .hn13 := j_inh_app j_wit_1 j_wit_22
private theorem j_wit_59 : JointInhabited .sn36 .hn31 := j_inh_app j_wit_23 j_wit_0
private theorem j_wit_60 : JointInhabited .sn37 .hn29 := j_inh_app j_wit_23 j_wit_1
private theorem j_wit_61 : JointInhabited .sn17 .hn13 := j_inh_app j_wit_1 j_wit_23
private theorem j_wit_62 : JointInhabited .sn30 .hn29 := j_inh_app j_wit_23 j_wit_57
private theorem j_wit_63 : JointInhabited .sn38 .hn29 := j_inh_app j_wit_23 j_wit_58
private theorem j_wit_64 : JointInhabited .sn35 .hn13 := j_inh_app j_wit_1 j_wit_24
private theorem j_wit_65 : JointInhabited .sn21 .hn27 := j_inh_app j_wit_0 j_wit_28
private theorem j_wit_66 : JointInhabited .sn32 .hn13 := j_inh_app j_wit_1 j_wit_28
private theorem j_wit_67 : JointInhabited .sn31 .hn10 := j_inh_app j_wit_3 j_wit_28
private theorem j_wit_68 : JointInhabited .sn38 .hn25 := j_inh_app j_wit_35 j_wit_28
private theorem j_wit_69 : JointInhabited .sn5 .hn13 := j_inh_app j_wit_1 j_wit_29
private theorem j_wit_70 : JointInhabited .sn33 .hn13 := j_inh_app j_wit_1 j_wit_30
private theorem j_wit_71 : JointInhabited .sn5 .hn12 := j_inh_app j_wit_0 j_wit_31
private theorem j_wit_72 : JointInhabited .sn6 .hn13 := j_inh_app j_wit_1 j_wit_34
private theorem j_wit_73 : JointInhabited .sn6 .hn12 := j_inh_app j_wit_0 j_wit_35
private theorem j_wit_74 : JointInhabited .sn29 .hn17 := j_inh_app j_wit_3 j_wit_39
private theorem j_wit_75 : JointInhabited .sn30 .hn33 := j_inh_app j_wit_40 j_wit_0
private theorem j_wit_76 : JointInhabited .sn21 .hn13 := j_inh_app j_wit_1 j_wit_43
private theorem j_wit_77 : JointInhabited .sn20 .hn12 := j_inh_app j_wit_0 j_wit_44
private theorem j_wit_78 : JointInhabited .sn6 .hn19 := j_inh_app j_wit_0 j_wit_45
private theorem j_wit_79 : JointInhabited .sn27 .hn13 := j_inh_app j_wit_1 j_wit_45
private theorem j_wit_80 : JointInhabited .sn31 .hn8 := j_inh_app j_wit_46 j_wit_0
private theorem j_wit_81 : JointInhabited .sn5 .hn5 := j_inh_app j_wit_0 j_wit_46
private theorem j_wit_82 : JointInhabited .sn14 .hn13 := j_inh_app j_wit_1 j_wit_46
private theorem j_wit_83 : JointInhabited .sn28 .hn13 := j_inh_app j_wit_1 j_wit_47
private theorem j_wit_84 : JointInhabited .sn4 .hn12 := j_inh_app j_wit_0 j_wit_48
private theorem j_wit_85 : JointInhabited .sn38 .hn21 := j_inh_app j_wit_0 j_wit_49
private theorem j_wit_86 : JointInhabited .sn37 .hn31 := j_inh_app j_wit_53 j_wit_0
private theorem j_wit_87 : JointInhabited .sn31 .hn29 := j_inh_app j_wit_53 j_wit_1
private theorem j_wit_88 : JointInhabited .sn18 .hn13 := j_inh_app j_wit_1 j_wit_53
private theorem j_wit_89 : JointInhabited .sn30 .hn17 := j_inh_app j_wit_3 j_wit_57
private theorem j_wit_90 : JointInhabited .sn30 .hn30 := j_inh_app j_wit_5 j_wit_57
private theorem j_wit_91 : JointInhabited .sn38 .hn12 := j_inh_app j_wit_0 j_wit_58
private theorem j_wit_92 : JointInhabited .sn38 .hn22 := j_inh_app j_wit_2 j_wit_58
private theorem j_wit_93 : JointInhabited .sn38 .hn17 := j_inh_app j_wit_3 j_wit_58
private theorem j_wit_94 : JointInhabited .sn38 .hn30 := j_inh_app j_wit_5 j_wit_58
private theorem j_wit_95 : JointInhabited .sn36 .hn13 := j_inh_app j_wit_1 j_wit_59
private theorem j_wit_96 : JointInhabited .sn37 .hn13 := j_inh_app j_wit_1 j_wit_60
private theorem j_wit_97 : JointInhabited .sn38 .hn9 := j_inh_app j_wit_0 j_wit_63
private theorem j_wit_98 : JointInhabited .sn29 .hn25 := j_inh_app j_wit_65 j_wit_0
private theorem j_wit_99 : JointInhabited .sn21 .hn12 := j_inh_app j_wit_0 j_wit_66
private theorem j_wit_100 : JointInhabited .sn31 .hn17 := j_inh_app j_wit_3 j_wit_66
private theorem j_wit_101 : JointInhabited .sn31 .hn13 := j_inh_app j_wit_1 j_wit_67
private theorem j_wit_102 : JointInhabited .sn29 .hn31 := j_inh_app j_wit_71 j_wit_0
private theorem j_wit_103 : JointInhabited .sn30 .hn31 := j_inh_app j_wit_73 j_wit_0
private theorem j_wit_104 : JointInhabited .sn30 .hn32 := j_inh_app j_wit_78 j_wit_0
private theorem j_wit_105 : JointInhabited .sn6 .hn5 := j_inh_app j_wit_0 j_wit_81
private theorem j_wit_106 : JointInhabited .sn31 .hn31 := j_inh_app j_wit_84 j_wit_0
private theorem j_wit_107 : JointInhabited .sn38 .hn33 := j_inh_app j_wit_85 j_wit_0
private theorem j_wit_108 : JointInhabited .sn6 .hn27 := j_inh_app j_wit_0 j_wit_86
private theorem j_wit_109 : JointInhabited .sn38 .hn31 := j_inh_app j_wit_91 j_wit_0
private theorem j_wit_110 : JointInhabited .sn38 .hn8 := j_inh_app j_wit_0 j_wit_91
private theorem j_wit_111 : JointInhabited .sn38 .hn27 := j_inh_app j_wit_0 j_wit_109

private theorem joint_closed_row_0 : checkAll1_StateHN (fun h1 => (!isJointPair .sn0 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn0 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_1 : checkAll1_StateHN (fun h1 => (!isJointPair .sn1 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn1 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_2 : checkAll1_StateHN (fun h1 => (!isJointPair .sn2 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn2 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_3 : checkAll1_StateHN (fun h1 => (!isJointPair .sn3 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn3 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_4 : checkAll1_StateHN (fun h1 => (!isJointPair .sn4 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn4 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_5 : checkAll1_StateHN (fun h1 => (!isJointPair .sn5 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn5 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_6 : checkAll1_StateHN (fun h1 => (!isJointPair .sn6 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn6 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_7 : checkAll1_StateHN (fun h1 => (!isJointPair .sn7 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn7 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_8 : checkAll1_StateHN (fun h1 => (!isJointPair .sn8 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn8 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_9 : checkAll1_StateHN (fun h1 => (!isJointPair .sn9 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn9 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_10 : checkAll1_StateHN (fun h1 => (!isJointPair .sn10 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn10 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_11 : checkAll1_StateHN (fun h1 => (!isJointPair .sn11 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn11 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_12 : checkAll1_StateHN (fun h1 => (!isJointPair .sn12 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn12 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_13 : checkAll1_StateHN (fun h1 => (!isJointPair .sn13 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn13 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_14 : checkAll1_StateHN (fun h1 => (!isJointPair .sn14 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn14 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_15 : checkAll1_StateHN (fun h1 => (!isJointPair .sn15 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn15 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_16 : checkAll1_StateHN (fun h1 => (!isJointPair .sn16 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn16 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_17 : checkAll1_StateHN (fun h1 => (!isJointPair .sn17 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn17 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_18 : checkAll1_StateHN (fun h1 => (!isJointPair .sn18 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn18 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_19 : checkAll1_StateHN (fun h1 => (!isJointPair .sn19 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn19 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_20 : checkAll1_StateHN (fun h1 => (!isJointPair .sn20 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn20 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_21 : checkAll1_StateHN (fun h1 => (!isJointPair .sn21 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn21 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_22 : checkAll1_StateHN (fun h1 => (!isJointPair .sn22 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn22 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_23 : checkAll1_StateHN (fun h1 => (!isJointPair .sn23 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn23 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_24 : checkAll1_StateHN (fun h1 => (!isJointPair .sn24 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn24 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_25 : checkAll1_StateHN (fun h1 => (!isJointPair .sn25 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn25 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_26 : checkAll1_StateHN (fun h1 => (!isJointPair .sn26 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn26 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_27 : checkAll1_StateHN (fun h1 => (!isJointPair .sn27 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn27 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_28 : checkAll1_StateHN (fun h1 => (!isJointPair .sn28 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn28 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_29 : checkAll1_StateHN (fun h1 => (!isJointPair .sn29 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn29 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_30 : checkAll1_StateHN (fun h1 => (!isJointPair .sn30 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn30 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_31 : checkAll1_StateHN (fun h1 => (!isJointPair .sn31 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn31 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_32 : checkAll1_StateHN (fun h1 => (!isJointPair .sn32 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn32 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_33 : checkAll1_StateHN (fun h1 => (!isJointPair .sn33 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn33 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_34 : checkAll1_StateHN (fun h1 => (!isJointPair .sn34 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn34 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_35 : checkAll1_StateHN (fun h1 => (!isJointPair .sn35 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn35 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_36 : checkAll1_StateHN (fun h1 => (!isJointPair .sn36 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn36 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_37 : checkAll1_StateHN (fun h1 => (!isJointPair .sn37 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn37 s2) (deltaHN h1 h2)))))) = true := rfl
private theorem joint_closed_row_38 : checkAll1_StateHN (fun h1 => (!isJointPair .sn38 h1 || checkAll1_StateSN (fun s2 => checkAll1_StateHN (fun h2 => (!isJointPair s2 h2 || isJointPair (deltaSN .sn38 s2) (deltaHN h1 h2)))))) = true := rfl

theorem isJointPair_closed {s1 s2 : StateSN} {h1 h2 : StateHN}
    (hp1 : isJointPair s1 h1 = true) (hp2 : isJointPair s2 h2 = true) :
    isJointPair (deltaSN s1 s2) (deltaHN h1 h2) = true := by
  have hr : (!isJointPair s1 h1 || checkAll1_StateSN (fun s2' => checkAll1_StateHN (fun h2' => (!isJointPair s2' h2' || isJointPair (deltaSN s1 s2') (deltaHN h1 h2'))))) = true :=
    match s1 with
    | .sn0 => checkAll1_StateHN_sound _ joint_closed_row_0 h1
    | .sn1 => checkAll1_StateHN_sound _ joint_closed_row_1 h1
    | .sn2 => checkAll1_StateHN_sound _ joint_closed_row_2 h1
    | .sn3 => checkAll1_StateHN_sound _ joint_closed_row_3 h1
    | .sn4 => checkAll1_StateHN_sound _ joint_closed_row_4 h1
    | .sn5 => checkAll1_StateHN_sound _ joint_closed_row_5 h1
    | .sn6 => checkAll1_StateHN_sound _ joint_closed_row_6 h1
    | .sn7 => checkAll1_StateHN_sound _ joint_closed_row_7 h1
    | .sn8 => checkAll1_StateHN_sound _ joint_closed_row_8 h1
    | .sn9 => checkAll1_StateHN_sound _ joint_closed_row_9 h1
    | .sn10 => checkAll1_StateHN_sound _ joint_closed_row_10 h1
    | .sn11 => checkAll1_StateHN_sound _ joint_closed_row_11 h1
    | .sn12 => checkAll1_StateHN_sound _ joint_closed_row_12 h1
    | .sn13 => checkAll1_StateHN_sound _ joint_closed_row_13 h1
    | .sn14 => checkAll1_StateHN_sound _ joint_closed_row_14 h1
    | .sn15 => checkAll1_StateHN_sound _ joint_closed_row_15 h1
    | .sn16 => checkAll1_StateHN_sound _ joint_closed_row_16 h1
    | .sn17 => checkAll1_StateHN_sound _ joint_closed_row_17 h1
    | .sn18 => checkAll1_StateHN_sound _ joint_closed_row_18 h1
    | .sn19 => checkAll1_StateHN_sound _ joint_closed_row_19 h1
    | .sn20 => checkAll1_StateHN_sound _ joint_closed_row_20 h1
    | .sn21 => checkAll1_StateHN_sound _ joint_closed_row_21 h1
    | .sn22 => checkAll1_StateHN_sound _ joint_closed_row_22 h1
    | .sn23 => checkAll1_StateHN_sound _ joint_closed_row_23 h1
    | .sn24 => checkAll1_StateHN_sound _ joint_closed_row_24 h1
    | .sn25 => checkAll1_StateHN_sound _ joint_closed_row_25 h1
    | .sn26 => checkAll1_StateHN_sound _ joint_closed_row_26 h1
    | .sn27 => checkAll1_StateHN_sound _ joint_closed_row_27 h1
    | .sn28 => checkAll1_StateHN_sound _ joint_closed_row_28 h1
    | .sn29 => checkAll1_StateHN_sound _ joint_closed_row_29 h1
    | .sn30 => checkAll1_StateHN_sound _ joint_closed_row_30 h1
    | .sn31 => checkAll1_StateHN_sound _ joint_closed_row_31 h1
    | .sn32 => checkAll1_StateHN_sound _ joint_closed_row_32 h1
    | .sn33 => checkAll1_StateHN_sound _ joint_closed_row_33 h1
    | .sn34 => checkAll1_StateHN_sound _ joint_closed_row_34 h1
    | .sn35 => checkAll1_StateHN_sound _ joint_closed_row_35 h1
    | .sn36 => checkAll1_StateHN_sound _ joint_closed_row_36 h1
    | .sn37 => checkAll1_StateHN_sound _ joint_closed_row_37 h1
    | .sn38 => checkAll1_StateHN_sound _ joint_closed_row_38 h1
  have hr' := imp_bool hp1 hr
  have hc := checkAll1_StateHN_sound _ (checkAll1_StateSN_sound _ hr' s2) h2
  exact imp_bool hp2 hc

theorem eval_isJointPair {t : Term} (hv : noVars t = true) :
    isJointPair (evalSN t) (evalHN t) = true := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    exact isJointPair_closed (iha ((Bool.and_eq_true _ _).mp hv).1) (ihb ((Bool.and_eq_true _ _).mp hv).2)

private theorem j_row_inh_0 (h : StateHN) (hp : isJointPair .sn0 h = true) : JointInhabited .sn0 h := by
  cases h with
  | hn0 => exact j_wit_0
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_1 (h : StateHN) (hp : isJointPair .sn1 h = true) : JointInhabited .sn1 h := by
  cases h with
  | hn1 => exact j_wit_1
  | hn0 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_2 (h : StateHN) (hp : isJointPair .sn2 h = true) : JointInhabited .sn2 h := by
  cases h with
  | hn2 => exact j_wit_3
  | hn0 => cases hp
  | hn1 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_3 (h : StateHN) (hp : isJointPair .sn3 h = true) : JointInhabited .sn3 h := by
  cases h with
  | hn3 => exact j_wit_13
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_4 (h : StateHN) (hp : isJointPair .sn4 h = true) : JointInhabited .sn4 h := by
  cases h with
  | hn4 => exact j_wit_46
  | hn12 => exact j_wit_84
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_5 (h : StateHN) (hp : isJointPair .sn5 h = true) : JointInhabited .sn5 h := by
  cases h with
  | hn5 => exact j_wit_81
  | hn8 => exact j_wit_29
  | hn12 => exact j_wit_71
  | hn13 => exact j_wit_69
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_6 (h : StateHN) (hp : isJointPair .sn6 h = true) : JointInhabited .sn6 h := by
  cases h with
  | hn5 => exact j_wit_105
  | hn8 => exact j_wit_51
  | hn9 => exact j_wit_34
  | hn10 => exact j_wit_38
  | hn12 => exact j_wit_73
  | hn13 => exact j_wit_72
  | hn19 => exact j_wit_78
  | hn21 => exact j_wit_40
  | hn27 => exact j_wit_108
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn11 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn20 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_7 (h : StateHN) (hp : isJointPair .sn7 h = true) : JointInhabited .sn7 h := by
  cases h with
  | hn6 => exact j_wit_2
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_8 (h : StateHN) (hp : isJointPair .sn8 h = true) : JointInhabited .sn8 h := by
  cases h with
  | hn7 => exact j_wit_5
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_9 (h : StateHN) (hp : isJointPair .sn9 h = true) : JointInhabited .sn9 h := by
  cases h with
  | hn11 => exact j_wit_4
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn12 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_10 (h : StateHN) (hp : isJointPair .sn10 h = true) : JointInhabited .sn10 h := by
  cases h with
  | hn12 => exact j_wit_23
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_11 (h : StateHN) (hp : isJointPair .sn11 h = true) : JointInhabited .sn11 h := by
  cases h with
  | hn13 => exact j_wit_15
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_12 (h : StateHN) (hp : isJointPair .sn12 h = true) : JointInhabited .sn12 h := by
  cases h with
  | hn12 => exact j_wit_53
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_13 (h : StateHN) (hp : isJointPair .sn13 h = true) : JointInhabited .sn13 h := by
  cases h with
  | hn13 => exact j_wit_48
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_14 (h : StateHN) (hp : isJointPair .sn14 h = true) : JointInhabited .sn14 h := by
  cases h with
  | hn13 => exact j_wit_82
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_15 (h : StateHN) (hp : isJointPair .sn15 h = true) : JointInhabited .sn15 h := by
  cases h with
  | hn13 => exact j_wit_7
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_16 (h : StateHN) (hp : isJointPair .sn16 h = true) : JointInhabited .sn16 h := by
  cases h with
  | hn13 => exact j_wit_31
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_17 (h : StateHN) (hp : isJointPair .sn17 h = true) : JointInhabited .sn17 h := by
  cases h with
  | hn13 => exact j_wit_61
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_18 (h : StateHN) (hp : isJointPair .sn18 h = true) : JointInhabited .sn18 h := by
  cases h with
  | hn13 => exact j_wit_88
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_19 (h : StateHN) (hp : isJointPair .sn19 h = true) : JointInhabited .sn19 h := by
  cases h with
  | hn13 => exact j_wit_44
  | hn14 => exact j_wit_12
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_20 (h : StateHN) (hp : isJointPair .sn20 h = true) : JointInhabited .sn20 h := by
  cases h with
  | hn12 => exact j_wit_77
  | hn15 => exact j_wit_43
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_21 (h : StateHN) (hp : isJointPair .sn21 h = true) : JointInhabited .sn21 h := by
  cases h with
  | hn12 => exact j_wit_99
  | hn13 => exact j_wit_76
  | hn27 => exact j_wit_65
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_22 (h : StateHN) (hp : isJointPair .sn22 h = true) : JointInhabited .sn22 h := by
  cases h with
  | hn16 => exact j_wit_14
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn13 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_23 (h : StateHN) (hp : isJointPair .sn23 h = true) : JointInhabited .sn23 h := by
  cases h with
  | hn13 => exact j_wit_52
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_24 (h : StateHN) (hp : isJointPair .sn24 h = true) : JointInhabited .sn24 h := by
  cases h with
  | hn8 => exact j_wit_6
  | hn13 => exact j_wit_35
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_25 (h : StateHN) (hp : isJointPair .sn25 h = true) : JointInhabited .sn25 h := by
  cases h with
  | hn9 => exact j_wit_16
  | hn10 => exact j_wit_18
  | hn13 => exact j_wit_56
  | hn17 => exact j_wit_55
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_26 (h : StateHN) (hp : isJointPair .sn26 h = true) : JointInhabited .sn26 h := by
  cases h with
  | hn13 => exact j_wit_41
  | hn17 => exact j_wit_10
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_27 (h : StateHN) (hp : isJointPair .sn27 h = true) : JointInhabited .sn27 h := by
  cases h with
  | hn13 => exact j_wit_79
  | hn18 => exact j_wit_45
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_28 (h : StateHN) (hp : isJointPair .sn28 h = true) : JointInhabited .sn28 h := by
  cases h with
  | hn13 => exact j_wit_83
  | hn20 => exact j_wit_47
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_29 (h : StateHN) (hp : isJointPair .sn29 h = true) : JointInhabited .sn29 h := by
  cases h with
  | hn10 => exact j_wit_21
  | hn13 => exact j_wit_39
  | hn17 => exact j_wit_74
  | hn20 => exact j_wit_9
  | hn22 => exact j_wit_8
  | hn24 => exact j_wit_25
  | hn25 => exact j_wit_98
  | hn29 => exact j_wit_17
  | hn30 => exact j_wit_32
  | hn31 => exact j_wit_102
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn21 => cases hp
  | hn23 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_30 (h : StateHN) (hp : isJointPair .sn30 h = true) : JointInhabited .sn30 h := by
  cases h with
  | hn10 => exact j_wit_36
  | hn13 => exact j_wit_57
  | hn17 => exact j_wit_89
  | hn20 => exact j_wit_20
  | hn22 => exact j_wit_54
  | hn23 => exact j_wit_19
  | hn24 => exact j_wit_27
  | hn25 => exact j_wit_37
  | hn29 => exact j_wit_62
  | hn30 => exact j_wit_90
  | hn31 => exact j_wit_103
  | hn32 => exact j_wit_104
  | hn33 => exact j_wit_75
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn21 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_31 (h : StateHN) (hp : isJointPair .sn31 h = true) : JointInhabited .sn31 h := by
  cases h with
  | hn8 => exact j_wit_80
  | hn10 => exact j_wit_67
  | hn13 => exact j_wit_101
  | hn17 => exact j_wit_100
  | hn29 => exact j_wit_87
  | hn31 => exact j_wit_106
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn9 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn30 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_32 (h : StateHN) (hp : isJointPair .sn32 h = true) : JointInhabited .sn32 h := by
  cases h with
  | hn13 => exact j_wit_66
  | hn26 => exact j_wit_28
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_33 (h : StateHN) (hp : isJointPair .sn33 h = true) : JointInhabited .sn33 h := by
  cases h with
  | hn13 => exact j_wit_70
  | hn28 => exact j_wit_30
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_34 (h : StateHN) (hp : isJointPair .sn34 h = true) : JointInhabited .sn34 h := by
  cases h with
  | hn13 => exact j_wit_42
  | hn30 => exact j_wit_11
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_35 (h : StateHN) (hp : isJointPair .sn35 h = true) : JointInhabited .sn35 h := by
  cases h with
  | hn13 => exact j_wit_64
  | hn29 => exact j_wit_24
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn30 => cases hp
  | hn31 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_36 (h : StateHN) (hp : isJointPair .sn36 h = true) : JointInhabited .sn36 h := by
  cases h with
  | hn13 => exact j_wit_95
  | hn31 => exact j_wit_59
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn29 => cases hp
  | hn30 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_37 (h : StateHN) (hp : isJointPair .sn37 h = true) : JointInhabited .sn37 h := by
  cases h with
  | hn13 => exact j_wit_96
  | hn29 => exact j_wit_60
  | hn31 => exact j_wit_86
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn8 => cases hp
  | hn9 => cases hp
  | hn10 => cases hp
  | hn11 => cases hp
  | hn12 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn17 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn20 => cases hp
  | hn21 => cases hp
  | hn22 => cases hp
  | hn23 => cases hp
  | hn24 => cases hp
  | hn25 => cases hp
  | hn26 => cases hp
  | hn27 => cases hp
  | hn28 => cases hp
  | hn30 => cases hp
  | hn32 => cases hp
  | hn33 => cases hp
  | hn34 => cases hp
private theorem j_row_inh_38 (h : StateHN) (hp : isJointPair .sn38 h = true) : JointInhabited .sn38 h := by
  cases h with
  | hn8 => exact j_wit_110
  | hn9 => exact j_wit_97
  | hn10 => exact j_wit_50
  | hn12 => exact j_wit_91
  | hn13 => exact j_wit_58
  | hn17 => exact j_wit_93
  | hn20 => exact j_wit_49
  | hn21 => exact j_wit_85
  | hn22 => exact j_wit_92
  | hn23 => exact j_wit_22
  | hn24 => exact j_wit_33
  | hn25 => exact j_wit_68
  | hn27 => exact j_wit_111
  | hn29 => exact j_wit_63
  | hn30 => exact j_wit_94
  | hn31 => exact j_wit_109
  | hn33 => exact j_wit_107
  | hn34 => exact j_wit_26
  | hn0 => cases hp
  | hn1 => cases hp
  | hn2 => cases hp
  | hn3 => cases hp
  | hn4 => cases hp
  | hn5 => cases hp
  | hn6 => cases hp
  | hn7 => cases hp
  | hn11 => cases hp
  | hn14 => cases hp
  | hn15 => cases hp
  | hn16 => cases hp
  | hn18 => cases hp
  | hn19 => cases hp
  | hn26 => cases hp
  | hn28 => cases hp
  | hn32 => cases hp

theorem isJointPair_iff_inhabited (s : StateSN) (h : StateHN) :
    isJointPair s h = true ↔ JointInhabited s h := by
  constructor
  · intro hp
    cases s with
    | sn0 => exact j_row_inh_0 h hp
    | sn1 => exact j_row_inh_1 h hp
    | sn2 => exact j_row_inh_2 h hp
    | sn3 => exact j_row_inh_3 h hp
    | sn4 => exact j_row_inh_4 h hp
    | sn5 => exact j_row_inh_5 h hp
    | sn6 => exact j_row_inh_6 h hp
    | sn7 => exact j_row_inh_7 h hp
    | sn8 => exact j_row_inh_8 h hp
    | sn9 => exact j_row_inh_9 h hp
    | sn10 => exact j_row_inh_10 h hp
    | sn11 => exact j_row_inh_11 h hp
    | sn12 => exact j_row_inh_12 h hp
    | sn13 => exact j_row_inh_13 h hp
    | sn14 => exact j_row_inh_14 h hp
    | sn15 => exact j_row_inh_15 h hp
    | sn16 => exact j_row_inh_16 h hp
    | sn17 => exact j_row_inh_17 h hp
    | sn18 => exact j_row_inh_18 h hp
    | sn19 => exact j_row_inh_19 h hp
    | sn20 => exact j_row_inh_20 h hp
    | sn21 => exact j_row_inh_21 h hp
    | sn22 => exact j_row_inh_22 h hp
    | sn23 => exact j_row_inh_23 h hp
    | sn24 => exact j_row_inh_24 h hp
    | sn25 => exact j_row_inh_25 h hp
    | sn26 => exact j_row_inh_26 h hp
    | sn27 => exact j_row_inh_27 h hp
    | sn28 => exact j_row_inh_28 h hp
    | sn29 => exact j_row_inh_29 h hp
    | sn30 => exact j_row_inh_30 h hp
    | sn31 => exact j_row_inh_31 h hp
    | sn32 => exact j_row_inh_32 h hp
    | sn33 => exact j_row_inh_33 h hp
    | sn34 => exact j_row_inh_34 h hp
    | sn35 => exact j_row_inh_35 h hp
    | sn36 => exact j_row_inh_36 h hp
    | sn37 => exact j_row_inh_37 h hp
    | sn38 => exact j_row_inh_38 h hp
  · intro ⟨t, hv, hs, hh⟩
    rw [← hs, ← hh]
    exact eval_isJointPair hv

def sumStateSN (f : StateSN → Nat) : Nat := f .sn0 + f .sn1 + f .sn2 + f .sn3 + f .sn4 + f .sn5 + f .sn6 + f .sn7 + f .sn8 + f .sn9 + f .sn10 + f .sn11 + f .sn12 + f .sn13 + f .sn14 + f .sn15 + f .sn16 + f .sn17 + f .sn18 + f .sn19 + f .sn20 + f .sn21 + f .sn22 + f .sn23 + f .sn24 + f .sn25 + f .sn26 + f .sn27 + f .sn28 + f .sn29 + f .sn30 + f .sn31 + f .sn32 + f .sn33 + f .sn34 + f .sn35 + f .sn36 + f .sn37 + f .sn38
def sumStateHN (f : StateHN → Nat) : Nat := f .hn0 + f .hn1 + f .hn2 + f .hn3 + f .hn4 + f .hn5 + f .hn6 + f .hn7 + f .hn8 + f .hn9 + f .hn10 + f .hn11 + f .hn12 + f .hn13 + f .hn14 + f .hn15 + f .hn16 + f .hn17 + f .hn18 + f .hn19 + f .hn20 + f .hn21 + f .hn22 + f .hn23 + f .hn24 + f .hn25 + f .hn26 + f .hn27 + f .hn28 + f .hn29 + f .hn30 + f .hn31 + f .hn32 + f .hn33 + f .hn34

def countJointWhere (pred : StateSN → StateHN → Bool) : Nat :=
  sumStateSN (fun s => sumStateHN (fun h => if isJointPair s h && pred s h then 1 else 0))

def isSN38 : StateSN → Bool
  | .sn38 => true
  | _ => false

def isHN34 : StateHN → Bool
  | .hn34 => true
  | _ => false

theorem joint_algebra_exact_112_partition :
    (∀ s h, isJointPair s h = true ↔ JointInhabited s h) ∧
    countJointWhere (fun _ _ => true) = 112 ∧
    countJointWhere (fun s h => !isSN38 s && !isHN34 h) = 94 ∧
    countJointWhere (fun s h => isSN38 s && !isHN34 h) = 17 ∧
    countJointWhere (fun s h => isSN38 s && isHN34 h) = 1 ∧
    countJointWhere (fun s h => !isSN38 s && isHN34 h) = 0 :=
  ⟨isJointPair_iff_inhabited, rfl, rfl, rfl, rfl, rfl⟩



private theorem joint_sn_implies_hn_chk : checkAll1_StateSN (fun s => checkAll1_StateHN (fun h =>
    (!isJointPair s h || !decide (s ≠ .sn38) || decide (h ≠ .hn34)))) = true := rfl

theorem evalSN_ne_sn38_implies_evalHN_ne_hn34 {t : Term} (hv : noVars t = true) (hsn : evalSN t ≠ .sn38) :
    evalHN t ≠ .hn34 := by
  have hj := eval_isJointPair hv
  have hc := checkAll1_StateHN_sound _ (checkAll1_StateSN_sound _ joint_sn_implies_hn_chk (evalSN t)) (evalHN t)
  rw [hj, decide_eq_true hsn] at hc
  exact of_decide_eq_true hc

/-! ## 6. 3rd-Argument Head-Exclusion Theorem -/

def inHN0to5 : StateHN → Bool
  | .hn0 | .hn1 | .hn2 | .hn3 | .hn4 | .hn5 => true
  | _ => false

private theorem hn_aaa_dichotomy_chk : checkAll1_StateHN (fun z =>
    decide (deltaHN (deltaHN z .hn34) .hn34 = .hn34) || inHN0to5 z) = true := rfl

private theorem joint_hn0to5_sn_chk : checkAll1_StateSN (fun s => checkAll1_StateHN (fun h =>
    (!isJointPair s h || !inHN0to5 h || decide (s ≠ .sn38)))) = true := rfl

private theorem hn0to5_s1_inv_chk : checkAll1_StateHN (fun u =>
    (!inHN0to5 (deltaHN .hn0 u) || inHN0to5 u)) = true := rfl

private theorem hn0to5_s2_false_chk : checkAll2_StateHN (fun u v =>
    !inHN0to5 (deltaHN (deltaHN .hn0 u) v)) = true := rfl

def rightTower : Nat → Term
  | 0 => S
  | k + 1 => S ⋅ rightTower k

private theorem cnf_inHN0to5_is_rightTower (c : CNF) (h : inHN0to5 (evalHN c.toTerm) = true) :
    ∃ k, c.toTerm = rightTower k := by
  induction c with
  | s => exact ⟨0, rfl⟩
  | s1 u ih =>
    have hc := checkAll1_StateHN_sound _ hn0to5_s1_inv_chk (evalHN u.toTerm)
    change (!inHN0to5 (evalHN (S ⋅ u.toTerm)) || inHN0to5 (evalHN u.toTerm)) = true at hc
    change inHN0to5 (evalHN (S ⋅ u.toTerm)) = true at h
    rw [h] at hc
    obtain ⟨k, hk⟩ := ih hc
    exact ⟨k + 1, congrArg (S ⋅ ·) hk⟩
  | s2 u v _ _ =>
    have hc := checkAll2_StateHN_sound _ hn0to5_s2_false_chk (evalHN u.toTerm) (evalHN v.toTerm)
    change (!inHN0to5 (evalHN (S ⋅ u.toTerm ⋅ v.toTerm))) = true at hc
    change inHN0to5 (evalHN (S ⋅ u.toTerm ⋅ v.toTerm)) = true at h
    rw [h] at hc
    cases hc

private theorem rightTower_34_reduces (k : Nat) {a b : Term} (q : Nat)
    (hva : noVars a = true) (hvb : noVars b = true)
    (ha : evalHN a = .hn34) (hb : evalHN b = .hn34) :
    ∃ w r, Reduces (rightTower k ⋅ a ⋅ b ⋅ .var q) ((w ⋅ .var q) ⋅ r) ∧
      noVars w = true ∧ evalHN w = .hn34 := by
  induction k generalizing a b with
  | zero =>
    exact ⟨a, b ⋅ .var q, Reduces.next (Step.root a b (.var q)) (Reduces.refl _), hva, ha⟩
  | succ k ih =>
    have hv_ab : noVars (a ⋅ b) = true := (Bool.and_eq_true _ _).mpr ⟨hva, hvb⟩
    have hab34 : evalHN (a ⋅ b) = .hn34 := by
      change deltaHN (evalHN a) (evalHN b) = .hn34
      rw [ha]
      exact deltaHN_hn34_left (evalHN b)
    obtain ⟨w, r, hrest, hvw, hw34⟩ := ih hvb hv_ab hb hab34
    exact ⟨w, r, Reduces.next (Step.left (Step.root (rightTower k) a b)) hrest, hvw, hw34⟩

private theorem headLeaf_subst_var (σ : Nat → Term) {t : Term} {v : Nat}
    (h : headLeaf t = .var v) : headLeaf (subst σ t) = headLeaf (σ v) := by
  induction t with
  | s => cases h
  | var k =>
    injection h with hk
    subst hk
    rfl
  | app a _ iha _ =>
    exact iha h

private theorem hn34_double_app_headLeaf_s {w r d : Term} {q : Nat}
    (hvw : noVars w = true) (hw34 : evalHN w = .hn34)
    (hred : Reduces ((w ⋅ .var q) ⋅ r) d) : headLeaf d = S := by
  have hnhnf : ¬ HasHNF w := fun hh => ((barendregt_open_problem_10 hvw).1.mp hh) hw34
  have hno_w : ∀ p1 p2, ¬ Reduces w (S ⋅ p1 ⋅ p2) :=
    fun p1 p2 hr => hnhnf ⟨S ⋅ p1 ⋅ p2, hr, Nat.le_refl 2⟩
  have hno_wq : ∀ p1 p2, ¬ Reduces (w ⋅ .var q) (S ⋅ p1 ⋅ p2) := by
    intro p1 p2 hr
    obtain ⟨w', q', heq, hrw, _⟩ := reduces_app_no_sab hr w (.var q) hno_w rfl
    injection heq with hw' _
    exact hnhnf ⟨S ⋅ p1, hw' ▸ hrw, Nat.succ_le_succ (Nat.zero_le 1)⟩
  obtain ⟨wq', _, hd, hr_wq, _⟩ := reduces_app_no_sab hred (w ⋅ .var q) r hno_wq rfl
  obtain ⟨w', _, hwq', hrw, _⟩ := reduces_app_no_sab hr_wq w (.var q) hno_w rfl
  subst hd
  subst hwq'
  change headLeaf w' = S
  exact closed_headLeaf_eq_s (noVars_reduces hrw hvw)

/-- **3rd-Argument Head-Exclusion Theorem**:
    For any closed pure-`S` combinator `z` (`noVars z = true`) and variables `w, j, q` with
    `w ≠ q` and `j ≠ q`, no reduct `n` of `z ⋅ w ⋅ j ⋅ q` ever has `q` as its head (leftmost) leaf. -/
theorem third_arg_head_exclusion {z n : Term} {w j q : Nat}
    (hvz : noVars z = true) (hwq : w ≠ q) (hjq : j ≠ q)
    (hred : Reduces (z ⋅ .var w ⋅ .var j ⋅ .var q) n) :
    headLeaf n ≠ .var q := by
  intro hhead
  let σ : Nat → Term := fun k => if decide (k = w ∨ k = j) then AAA else .var k
  have hσw : σ w = AAA := by simp [σ]
  have hσj : σ j = AAA := by simp [σ]
  have hσq : σ q = .var q := by
    have hnot : ¬ (q = w ∨ q = j) := fun h =>
      match h with
      | Or.inl h1 => hwq h1.symm
      | Or.inr h2 => hjq h2.symm
    simp [σ, hnot]
  have hred_σ : Reduces (z ⋅ AAA ⋅ AAA ⋅ .var q) (subst σ n) := by
    have hr := subst_reduces σ hred
    simp only [subst, subst_noVars σ z hvz, hσw, hσj, hσq] at hr
    exact hr
  have hhead_σ : headLeaf (subst σ n) = .var q := by
    rw [headLeaf_subst_var σ hhead, hσq]
    rfl
  have hAAA_nv : noVars AAA = true := rfl
  have hAAA_34 : evalHN AAA = .hn34 := rfl
  have hdich := checkAll1_StateHN_sound _ hn_aaa_dichotomy_chk (evalHN z)
  cases hd1 : decide (deltaHN (deltaHN (evalHN z) .hn34) .hn34 = .hn34) with
  | true =>
    have hz34 : evalHN (z ⋅ AAA ⋅ AAA) = .hn34 := of_decide_eq_true hd1
    have hv_zaa : noVars (z ⋅ AAA ⋅ AAA) = true := by simp [noVars, hvz, hAAA_nv]
    have hnhnf : ¬ HasHNF (z ⋅ AAA ⋅ AAA) :=
      fun hh => ((barendregt_open_problem_10 hv_zaa).1.mp hh) hz34
    have hno : ∀ p1 p2, ¬ Reduces (z ⋅ AAA ⋅ AAA) (S ⋅ p1 ⋅ p2) :=
      fun p1 p2 hr => hnhnf ⟨S ⋅ p1 ⋅ p2, hr, Nat.le_refl 2⟩
    obtain ⟨f', _, hsub_eq, hrf, _⟩ :=
      reduces_app_no_sab hred_σ (z ⋅ AAA ⋅ AAA) (.var q) hno rfl
    have hhf : headLeaf (subst σ n) = S := by
      rw [hsub_eq]
      change headLeaf f' = S
      exact closed_headLeaf_eq_s (noVars_reduces hrf hv_zaa)
    rw [hhf] at hhead_σ
    cases hhead_σ
  | false =>
    rw [hd1, Bool.false_or] at hdich
    have hj := eval_isJointPair hvz
    have hsn_chk := checkAll1_StateHN_sound _ (checkAll1_StateSN_sound _ joint_hn0to5_sn_chk (evalSN z)) (evalHN z)
    simp only [hj, hdich, Bool.not_true, Bool.false_or] at hsn_chk
    have hz_sn : evalSN z ≠ .sn38 := of_decide_eq_true hsn_chk
    obtain ⟨cz, hred_cz⟩ := closed_evalSN_ne_sn38_reduces_cnf hvz hz_sn
    have hcz_0to5 : inHN0to5 (evalHN cz.toTerm) = true := by
      rw [← evalHN_reduces hred_cz]
      exact hdich
    obtain ⟨k, hcz_eq⟩ := cnf_inHN0to5_is_rightTower cz hcz_0to5
    have hred_zk : Reduces z (rightTower k) := hcz_eq ▸ hred_cz
    obtain ⟨w34, r_rest, hred_rt, hvw34, hw34⟩ :=
      rightTower_34_reduces k q hAAA_nv hAAA_nv hAAA_34 hAAA_34
    have hred_branch : Reduces (z ⋅ AAA ⋅ AAA ⋅ .var q) ((w34 ⋅ .var q) ⋅ r_rest) :=
      reduces_trans (reduces_left (reduces_left (reduces_left hred_zk AAA) AAA) (.var q)) hred_rt
    obtain ⟨d, hd_left, hd_right⟩ := church_rosser hred_σ hred_branch
    have hhd_q : headLeaf d = .var q := headLeaf_var_preserved_reduces hd_left hhead_σ
    have hhd_s : headLeaf d = S := hn34_double_app_headLeaf_s hvw34 hw34 hd_right
    rw [hhd_s] at hhd_q
    cases hhd_q

/-! ## 7. Theorem 8: Selector-Free Leftmost-Outermost (`stepLO`) Quadratic Two-Counter Loop -/

def iterateLO : Nat → Term → Term
  | 0, t => t
  | k + 1, t =>
    match stepLO t with
    | some t' => iterateLO k t'
    | none => t

theorem iterateLO_add (a b : Nat) (t : Term) :
    iterateLO (a + b) t = iterateLO b (iterateLO a t) := by
  induction a generalizing t with
  | zero => simp [iterateLO]
  | succ a ih =>
    rw [Nat.succ_add a b]
    simp only [iterateLO]
    cases hs : stepLO t with
    | none =>
      have hnone : ∀ k, iterateLO k t = t := by
        intro k
        induction k with
        | zero => rfl
        | succ k _ => simp [iterateLO, hs]
      cases a with
      | zero => simp [iterateLO, hnone b]
      | succ a0 =>
        rw [Nat.succ_add a0 b]
        simp only [iterateLO, hs, hnone a0, hnone (a0 + b), hnone b]
    | some t' => exact ih t'

def wrapLeftHNF : List Term → Term → Term
  | [], focus => focus
  | r :: rs, focus => S ⋅ wrapLeftHNF rs focus ⋅ r

theorem stepLO_wrapLeftHNF (ctx : List Term) {u u' : Term} (hu : stepLO u = some u') :
    stepLO (wrapLeftHNF ctx u) = some (wrapLeftHNF ctx u') := by
  induction ctx with
  | nil => exact hu
  | cons r rs ih =>
    simp only [wrapLeftHNF, stepLO, rootRedexOpt, S, ih]

def numeralC : Nat → Term
  | 0 => S ⋅ B_comb ⋅ B_comb
  | n + 1 => B_comb ⋅ numeralC n

def counterD (m n : Nat) : Term :=
  numeralC m ⋅ numeralC n ⋅ S

def tenLeafSeed : Term :=
  S ⋅ (S ⋅ B_comb) ⋅ (S ⋅ B_comb) ⋅ B_comb ⋅ S

private theorem counterD_zero_step (n : Nat) :
    stepLO (counterD 0 n) = some (counterD (n + 1) (n + 1)) := rfl

private theorem counterD_succ_4steps (k p : Nat) :
    let u0 := counterD (k + 1) (p + 1)
    let u1 := ((S ⋅ numeralC (p + 1)) ⋅ (numeralC k ⋅ numeralC (p + 1))) ⋅ S
    let u2 := (numeralC (p + 1) ⋅ S) ⋅ counterD k (p + 1)
    let u3 := (S ⋅ S ⋅ (numeralC p ⋅ S)) ⋅ counterD k (p + 1)
    let u4 := S ⋅ counterD k (p + 1) ⋅ ((numeralC p ⋅ S) ⋅ counterD k (p + 1))
    stepLO u0 = some u1 ∧ stepLO u1 = some u2 ∧ stepLO u2 = some u3 ∧ stepLO u3 = some u4 :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem counterD_countdown (k p : Nat) :
    ∀ (ctx : List Term),
      ∃ ctx' : List Term,
        ctx'.length = ctx.length + k ∧
        iterateLO (4 * k + 1) (wrapLeftHNF ctx (counterD k (p + 1))) =
          wrapLeftHNF ctx' (counterD (p + 2) (p + 2)) := by
  induction k with
  | zero =>
    intro ctx
    refine ⟨ctx, Nat.add_zero _, ?_⟩
    change iterateLO 1 (wrapLeftHNF ctx (counterD 0 (p + 1))) =
      wrapLeftHNF ctx (counterD (p + 2) (p + 2))
    simp only [iterateLO, stepLO_wrapLeftHNF ctx (counterD_zero_step (p + 1))]
  | succ k ih =>
    intro ctx
    have ⟨hs0, hs1, hs2, hs3⟩ := counterD_succ_4steps k p
    let r_frozen := (numeralC p ⋅ S) ⋅ counterD k (p + 1)
    have h4 : iterateLO 4 (wrapLeftHNF ctx (counterD (k + 1) (p + 1))) =
        wrapLeftHNF (ctx ++ [r_frozen]) (counterD k (p + 1)) := by
      -- Notice `wrapLeftHNF (ctx ++ [r]) focus = wrapLeftHNF ctx (S ⋅ focus ⋅ r)`!
      have happ : ∀ (c : List Term) (foc r : Term),
          wrapLeftHNF (c ++ [r]) foc = wrapLeftHNF c (S ⋅ foc ⋅ r) := by
        intro c foc r
        induction c with
        | nil => rfl
        | cons x xs ihc => simp only [List.cons_append, wrapLeftHNF, ihc]
      rw [happ]
      simp only [iterateLO,
        stepLO_wrapLeftHNF ctx hs0,
        stepLO_wrapLeftHNF ctx hs1,
        stepLO_wrapLeftHNF ctx hs2,
        stepLO_wrapLeftHNF ctx hs3]
      rfl
    have hlen_app : (ctx ++ [r_frozen]).length = ctx.length + 1 := List.length_append ..
    obtain ⟨ctx', hlen', hrest⟩ := ih (ctx ++ [r_frozen])
    refine ⟨ctx', ?_, ?_⟩
    · rw [hlen', hlen_app, Nat.add_assoc]
      rw [Nat.add_comm 1 k]
    · have h4k : 4 * (k + 1) + 1 = 4 + (4 * k + 1) := by
        rw [Nat.mul_add 4 k 1, Nat.mul_one]
        simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      rw [h4k, iterateLO_add 4 (4 * k + 1), h4, hrest]

private theorem quad_closed_form (k : Nat) :
    2 * (k + 1) * (k + 1) - (k + 1) + 1 = (k * k + k * k) + (k + k + k) + 2 := by
  have hexp : 2 * (k + 1) * (k + 1) = ((k * k + k * k) + (k + k + k) + 1) + (k + 1) := by
    simp only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add, Nat.mul_add, Nat.add_mul, Nat.mul_one]
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [hexp, Nat.add_sub_cancel]

private theorem quad_step_arith (m : Nat) :
    (2 * (m + 1) * (m + 1) - (m + 1) + 1) + (4 * (m + 1) + 1) =
    2 * (m + 2) * (m + 2) - (m + 2) + 1 := by
  rw [quad_closed_form m, quad_closed_form (m + 1)]
  simp only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add, Nat.mul_add, Nat.mul_one]
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private def triDepth : Nat → Nat
  | 0 => 0
  | m + 1 => triDepth m + (m + 1)

private theorem two_mul_triDepth (m : Nat) : 2 * triDepth m = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [triDepth, Nat.mul_add]
    rw [ih]
    simp only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add, Nat.mul_add, Nat.mul_one]
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem triDepth_eq_div (m : Nat) : triDepth m = m * (m + 1) / 2 := by
  rw [← two_mul_triDepth m]
  exact (Nat.mul_div_right (triDepth m) (by decide : 0 < 2)).symm

/-- **Theorem 8 (Selector-Free `stepLO` Quadratic Two-Counter Loop)**:
    Starting from the 10-leaf closed seed `S(S(SS))(S(SS))(SS)S`, unguided deterministic
    leftmost-outermost reduction `stepLO` reaches `D(n+1, n+1)` wrapped inside `n*(n+1)/2`
    frozen left-active 2-HNFs in `2*(n+1)^2 - (n+1) + 1` steps for every `n : Nat`
    (equivalently, `D(N, N)` at depth `N*(N-1)/2` in `2*N^2 - N + 1` steps for every `N ≥ 1`). -/
theorem stepLO_quadratic_two_counter (n : Nat) :
    ∃ ctx : List Term,
      ctx.length = n * (n + 1) / 2 ∧
      iterateLO (2 * (n + 1) * (n + 1) - (n + 1) + 1) tenLeafSeed =
        wrapLeftHNF ctx (counterD (n + 1) (n + 1)) := by
  induction n with
  | zero =>
    exact ⟨[], rfl, rfl⟩
  | succ m ih =>
    obtain ⟨ctx, hlen, hreach⟩ := ih
    obtain ⟨ctx', hlen', hstep⟩ := counterD_countdown (m + 1) m ctx
    refine ⟨ctx', ?_, ?_⟩
    · rw [hlen', hlen, ← triDepth_eq_div m, ← triDepth_eq_div (m + 1)]
      rfl
    · rw [← quad_step_arith m, iterateLO_add _ (4 * (m + 1) + 1), hreach, hstep]

theorem stepLO_quadratic_two_counter_pos (N : Nat) (hN : 1 ≤ N) :
    ∃ ctx : List Term,
      ctx.length = N * (N - 1) / 2 ∧
      iterateLO (2 * N * N - N + 1) tenLeafSeed =
        wrapLeftHNF ctx (counterD N N) := by
  cases N with
  | zero => cases hN
  | succ n =>
    obtain ⟨ctx, hlen, hreach⟩ := stepLO_quadratic_two_counter n
    rw [Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]
    exact ⟨ctx, hlen, hreach⟩

end FormalAlgebra

#print axioms FormalAlgebra.sn_iff_wn
#print axioms FormalAlgebra.deltaSN_s_law
#print axioms FormalAlgebra.waldmann_theorem_9
#print axioms FormalAlgebra.deltaHN_s_law
#print axioms FormalAlgebra.barendregt_open_problem_10
#print axioms FormalAlgebra.g_spine_dag_property
#print axioms FormalAlgebra.footnote4_rnf_iff
#print axioms FormalAlgebra.five_composite_args_hn34
#print axioms FormalAlgebra.five_composite_args_rnf
#print axioms FormalAlgebra.joint_algebra_exact_112_partition
#print axioms FormalAlgebra.evalSN_ne_sn38_implies_evalHN_ne_hn34
#print axioms FormalAlgebra.third_arg_head_exclusion
#print axioms FormalAlgebra.stepLO_quadratic_two_counter
#print axioms FormalAlgebra.stepLO_quadratic_two_counter_pos
