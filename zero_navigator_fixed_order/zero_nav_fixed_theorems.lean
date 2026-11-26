import Std
set_option linter.unusedSimpArgs false

namespace ZeroNavigatorFixedOrder

/-!
# Zero-Navigator Fixed-Order Dynamics, Obstructions, and Sharp Bounds in Pure `S` (`CL(S)`)

Machine-checked in Lean 4.33.1 with **zero `sorry`**, **zero `admit`**, **zero user-declared axioms**,
and **zero `Classical.choice`**.
-/

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true a b).mp h).1

theorem and_right {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true a b).mp h).2

/-! ## Section 1. Syntax, Multiway Rewriting, and Six Fixed Evaluation Strategies -/

inductive Term where
  | s : Term
  | var : Nat → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

infixl:70 " ⋅ " => Term.app

def S : Term := Term.s
def T_comb : Term := S ⋅ S
def B_comb : Term := S ⋅ T_comb
def A_comb : Term := S ⋅ S ⋅ S
def Zachos : Term := (S ⋅ T_comb ⋅ T_comb) ⋅ (S ⋅ T_comb ⋅ T_comb)

def appList : Term → List Term → Term
  | f, [] => f
  | f, w :: ws => appList (f ⋅ w) ws

inductive Step : Term → Term → Prop where
  | root (x y z : Term) : Step (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : Step a a' → Step (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Step b b' → Step (a ⋅ b) (a ⋅ b')

inductive Reduces : Term → Term → Prop where
  | refl (a : Term) : Reduces a a
  | next {a b c : Term} : Step a b → Reduces b c → Reduces a c

theorem Reduces.trans {a b c : Term} (h1 : Reduces a b) (h2 : Reduces b c) : Reduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact Reduces.next hs (ih h2)

theorem Reduces.cong_left {a a' b : Term} (h : Reduces a a') : Reduces (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (Step.left hs) ih

theorem Reduces.cong_right {a b b' : Term} (h : Reduces b b') : Reduces (a ⋅ b) (a ⋅ b') := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (Step.right hs) ih

def isClosed : Term → Bool
  | .s => true
  | .var _ => false
  | .app a b => isClosed a && isClosed b

theorem step_preserves_closed {a b : Term} (h : Step a b) : isClosed a = true → isClosed b = true := by
  induction h with
  | root x y z =>
    intro hc
    have h1 := and_left hc
    have hz := and_right hc
    have hy := and_right h1
    have hx := and_right (and_left h1)
    simp [isClosed, hx, hy, hz]
  | left _ ih =>
    intro hc; exact Bool.and_eq_true _ _ |>.mpr ⟨ih (and_left hc), and_right hc⟩
  | right _ ih =>
    intro hc; exact Bool.and_eq_true _ _ |>.mpr ⟨and_left hc, ih (and_right hc)⟩

theorem reduces_preserves_closed {a b : Term} (h : Reduces a b) : isClosed a = true → isClosed b = true := by
  induction h with
  | refl _ => intro hc; exact hc
  | next hs _ ih => intro hc; exact ih (step_preserves_closed hs hc)

/-- Right-spine length (`rs b + 1` so `Nat.succ_le_succ` applies definitionally!). -/
def rs : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app _ b => rs b + 1

theorem rs_mono_step {a b : Term} (h : Step a b) : rs a ≤ rs b := by
  induction h with
  | root x y z => exact Nat.le_succ (rs z + 1)
  | left _ _ => exact Nat.le_refl _
  | right _ ih => exact Nat.succ_le_succ ih

theorem rs_mono_reduces {a b : Term} (h : Reduces a b) : rs a ≤ rs b := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | next hs _ ih => exact Nat.le_trans (rs_mono_step hs) ih

def isRootRedex : Term → Bool
  | .app (.app (.app .s _) _) _ => true
  | _ => false

def redexCount : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app l r => (if isRootRedex (.app l r) then 1 else 0) + (redexCount l + redexCount r)

/-- 1. Leftmost-Outermost (`->_{lo}`) -/
def stepLO : Term → Option Term
  | .s => none
  | .var _ => none
  | .app (.app (.app .s x) y) z => some ((x ⋅ z) ⋅ (y ⋅ z))
  | .app l r =>
    match stepLO l with
    | some l' => some (l' ⋅ r)
    | none =>
      match stepLO r with
      | some r' => some (l ⋅ r')
      | none => none

/-- 2. Rightmost-Outermost (`->_{ro}`) -/
def stepRO : Term → Option Term
  | .s => none
  | .var _ => none
  | .app (.app (.app .s x) y) z => some ((x ⋅ z) ⋅ (y ⋅ z))
  | .app l r =>
    match stepRO r with
    | some r' => some (l ⋅ r')
    | none =>
      match stepRO l with
      | some l' => some (l' ⋅ r)
      | none => none

/-- 3. Leftmost-Innermost (`->_{li}`) -/
def stepLI : Term → Option Term
  | .s => none
  | .var _ => none
  | .app l r =>
    match stepLI l with
    | some l' => some (l' ⋅ r)
    | none =>
      match stepLI r with
      | some r' => some (l ⋅ r')
      | none =>
        match l with
        | .app (.app .s x) y => some ((x ⋅ r) ⋅ (y ⋅ r))
        | _ => none

/-- 4. Rightmost-Innermost (`->_{ri}`) -/
def stepRI : Term → Option Term
  | .s => none
  | .var _ => none
  | .app l r =>
    match stepRI r with
    | some r' => some (l ⋅ r')
    | none =>
      match stepRI l with
      | some l' => some (l' ⋅ r)
      | none =>
        match l with
        | .app (.app .s x) y => some ((x ⋅ r) ⋅ (y ⋅ r))
        | _ => none

/-- Minimum depth from the root to any redex (`none` if normal form). -/
def minRedexDepth : Term → Option Nat
  | .s => none
  | .var _ => none
  | .app (.app (.app .s _) _) _ => some 0
  | .app l r =>
    match minRedexDepth l, minRedexDepth r with
    | none, none => none
    | some dl, none => some (dl + 1)
    | none, some dr => some (dr + 1)
    | some dl, some dr => some ((if dl ≤ dr then dl else dr) + 1)

/-- 5. Breadth-First / Shallowest-Leftmost (`->_{bfs}`) -/
def stepBFS : Term → Option Term
  | .s => none
  | .var _ => none
  | .app (.app (.app .s x) y) z => some ((x ⋅ z) ⋅ (y ⋅ z))
  | .app l r =>
    match minRedexDepth l, minRedexDepth r with
    | none, none => none
    | some _, none => (stepBFS l).map (fun l' => l' ⋅ r)
    | none, some _ => (stepBFS r).map (fun r' => l ⋅ r')
    | some dl, some dr =>
      if dl ≤ dr then (stepBFS l).map (fun l' => l' ⋅ r)
      else (stepBFS r).map (fun r' => l ⋅ r')

/-- 6. Gross–Knuth Parallel Full-Development (`=>_{GK}`) -/
def stepGK : Term → Term
  | .s => .s
  | .var k => .var k
  | .app (.app (.app .s x) y) z =>
    let x' := stepGK x
    let y' := stepGK y
    let z' := stepGK z
    (x' ⋅ z') ⋅ (y' ⋅ z')
  | .app l r => (stepGK l) ⋅ (stepGK r)

def iterOpt (f : Term → Option Term) : Nat → Term → Option Term
  | 0, t => some t
  | n + 1, t =>
    match f t with
    | none => none
    | some t' => iterOpt f n t'

def iterGK : Nat → Term → Term
  | 0, t => t
  | n + 1, t => iterGK n (stepGK t)

/-- Clean 1-level unfolding lemmas on non-root-redex applications (`isRootRedex (l ⋅ r) = false`),
    preventing recursive `simp` over-unfolding! -/
theorem stepLO_not_root {l r : Term} (hrr : isRootRedex (l ⋅ r) = false) :
    stepLO (l ⋅ r) =
      match stepLO l with
      | some l' => some (l' ⋅ r)
      | none =>
        match stepLO r with
        | some r' => some (l ⋅ r')
        | none => none := by
  cases l with
  | s => rfl | var _ => rfl
  | app l1 _ => cases l1 with
    | s => rfl | var _ => rfl
    | app l11 _ => cases l11 with
      | s => cases hrr | var _ => rfl | app _ _ => rfl

theorem stepRO_not_root {l r : Term} (hrr : isRootRedex (l ⋅ r) = false) :
    stepRO (l ⋅ r) =
      match stepRO r with
      | some r' => some (l ⋅ r')
      | none =>
        match stepRO l with
        | some l' => some (l' ⋅ r)
        | none => none := by
  cases l with
  | s => rfl | var _ => rfl
  | app l1 _ => cases l1 with
    | s => rfl | var _ => rfl
    | app l11 _ => cases l11 with
      | s => cases hrr | var _ => rfl | app _ _ => rfl

theorem stepLI_not_root {l r : Term} (hrr : isRootRedex (l ⋅ r) = false) :
    stepLI (l ⋅ r) =
      match stepLI l with
      | some l' => some (l' ⋅ r)
      | none =>
        match stepLI r with
        | some r' => some (l ⋅ r')
        | none => none := by
  cases l with
  | s => rfl | var _ => rfl
  | app l1 _ => cases l1 with
    | s => rfl | var _ => rfl
    | app l11 _ => cases l11 with
      | s => cases hrr | var _ => rfl | app _ _ => rfl

theorem stepRI_not_root {l r : Term} (hrr : isRootRedex (l ⋅ r) = false) :
    stepRI (l ⋅ r) =
      match stepRI r with
      | some r' => some (l ⋅ r')
      | none =>
        match stepRI l with
        | some l' => some (l' ⋅ r)
        | none => none := by
  cases l with
  | s => rfl | var _ => rfl
  | app l1 _ => cases l1 with
    | s => rfl | var _ => rfl
    | app l11 _ => cases l11 with
      | s => cases hrr | var _ => rfl | app _ _ => rfl

theorem minRedexDepth_not_root {l r : Term} (hrr : isRootRedex (l ⋅ r) = false) :
    minRedexDepth (l ⋅ r) =
      match minRedexDepth l, minRedexDepth r with
      | none, none => none
      | some dl, none => some (dl + 1)
      | none, some dr => some (dr + 1)
      | some dl, some dr => some ((if dl ≤ dr then dl else dr) + 1) := by
  cases l with
  | s => rfl | var _ => rfl
  | app l1 _ => cases l1 with
    | s => rfl | var _ => rfl
    | app l11 _ => cases l11 with
      | s => cases hrr | var _ => rfl | app _ _ => rfl

theorem stepBFS_not_root {l r : Term} (hrr : isRootRedex (l ⋅ r) = false) :
    stepBFS (l ⋅ r) =
      match minRedexDepth l, minRedexDepth r with
      | none, none => none
      | some _, none => (stepBFS l).map (fun l' => l' ⋅ r)
      | none, some _ => (stepBFS r).map (fun r' => l ⋅ r')
      | some dl, some dr =>
        if dl ≤ dr then (stepBFS l).map (fun l' => l' ⋅ r)
        else (stepBFS r).map (fun r' => l ⋅ r') := by
  cases l with
  | s => rfl | var _ => rfl
  | app l1 _ => cases l1 with
    | s => rfl | var _ => rfl
    | app l11 _ => cases l11 with
      | s => cases hrr | var _ => rfl | app _ _ => rfl

theorem stepGK_not_root {l r : Term} (hrr : isRootRedex (l ⋅ r) = false) :
    stepGK (l ⋅ r) = (stepGK l) ⋅ (stepGK r) := by
  cases l with
  | s => rfl | var _ => rfl
  | app l1 _ => cases l1 with
    | s => rfl | var _ => rfl
    | app l11 _ => cases l11 with
      | s => cases hrr | var _ => rfl | app _ _ => rfl

theorem stepLI_root (x y z : Term) (hl : stepLI (.s ⋅ x ⋅ y) = none) (hz : stepLI z = none) :
    stepLI ((.s ⋅ x ⋅ y) ⋅ z) = some ((x ⋅ z) ⋅ (y ⋅ z)) := by
  conv => lhs; unfold stepLI
  rw [hl, hz]

theorem stepRI_root (x y z : Term) (hl : stepRI (.s ⋅ x ⋅ y) = none) (hz : stepRI z = none) :
    stepRI ((.s ⋅ x ⋅ y) ⋅ z) = some ((x ⋅ z) ⋅ (y ⋅ z)) := by
  conv => lhs; unfold stepRI
  rw [hz, hl]

theorem nat_add_eq_zero_left {a b : Nat} (h : a + b = 0) : a = 0 := by
  cases a with
  | zero => rfl
  | succ a' =>
    have h2 : Nat.succ (a' + b) = 0 := by rw [← Nat.succ_add]; exact h
    cases h2

theorem nat_add_eq_zero_right {a b : Nat} (h : a + b = 0) : b = 0 := by
  cases b with
  | zero => rfl
  | succ _ => cases h

theorem no_redex_evaluators_idle :
    ∀ (t : Term), redexCount t = 0 →
      stepLO t = none ∧ stepLI t = none ∧ stepRO t = none ∧
      stepRI t = none ∧ minRedexDepth t = none ∧ stepBFS t = none ∧ stepGK t = t
  | .s, _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | .var _, _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | .app l r, h => by
    unfold redexCount at h
    cases hrr : isRootRedex (l ⋅ r) with
    | true =>
      rw [hrr] at h
      have hbad : 1 + (redexCount l + redexCount r) = 0 := h
      cases nat_add_eq_zero_left hbad
    | false =>
      rw [hrr] at h
      have hsum : redexCount l + redexCount r = 0 := by simpa using h
      rcases no_redex_evaluators_idle l (nat_add_eq_zero_left hsum) with
        ⟨hlo_l, hli_l, hro_l, hri_l, hm_l, _, hgk_l⟩
      rcases no_redex_evaluators_idle r (nat_add_eq_zero_right hsum) with
        ⟨hlo_r, hli_r, hro_r, hri_r, hm_r, _, hgk_r⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [stepLO_not_root hrr, hlo_l, hlo_r]
      · rw [stepLI_not_root hrr, hli_l, hli_r]
      · rw [stepRO_not_root hrr, hro_r, hro_l]
      · rw [stepRI_not_root hrr, hri_r, hri_l]
      · rw [minRedexDepth_not_root hrr, hm_l, hm_r]
      · rw [stepBFS_not_root hrr, hm_l, hm_r]
      · rw [stepGK_not_root hrr, hgk_l, hgk_r]

theorem minRedexDepth_some_of_pos :
    ∀ (t : Term), redexCount t = 1 → ∃ d, minRedexDepth t = some d
  | .s, h => by cases h
  | .var _, h => by cases h
  | .app l r, h => by
    unfold redexCount at h
    cases hrr : isRootRedex (l ⋅ r) with
    | true =>
      cases l with
      | s => cases hrr | var _ => cases hrr
      | app l1 _ => cases l1 with
        | s => cases hrr | var _ => cases hrr
        | app l11 _ => cases l11 with
          | s => exact ⟨0, rfl⟩ | var _ => cases hrr | app _ _ => cases hrr
    | false =>
      rw [hrr] at h
      have hsum : redexCount l + redexCount r = 1 := by simpa using h
      cases hcl : redexCount l with
      | zero =>
        rw [hcl] at hsum
        have hcr : redexCount r = 1 := by simpa using hsum
        have hm_l := (no_redex_evaluators_idle l hcl).2.2.2.2.1
        rcases minRedexDepth_some_of_pos r hcr with ⟨dr, hm_r⟩
        rw [minRedexDepth_not_root hrr, hm_l, hm_r]
        exact ⟨dr + 1, rfl⟩
      | succ k =>
        have hk0 : k + redexCount r = 0 := by rw [hcl, Nat.succ_add] at hsum; injection hsum
        have hk := nat_add_eq_zero_left hk0
        have hcr := nat_add_eq_zero_right hk0
        subst hk
        have hm_r := (no_redex_evaluators_idle r hcr).2.2.2.2.1
        rcases minRedexDepth_some_of_pos l hcl with ⟨dl, hm_l⟩
        rw [minRedexDepth_not_root hrr, hm_l, hm_r]
        exact ⟨dl + 1, rfl⟩

/-- **Theorem 1.1 (Pure-Line 6-Strategy Coincidence):**
    Whenever `redexCount t = 1`, ALL SIX zero-navigator strategies (`stepLO`, `stepLI`,
    `stepRO`, `stepRI`, `stepBFS`, and `stepGK`) produce the exact same next term! -/
theorem pure_line_all_six_coincide :
    ∀ (t : Term), redexCount t = 1 →
      ∃ t', stepLO t = some t' ∧ stepLI t = some t' ∧ stepRO t = some t' ∧
            stepRI t = some t' ∧ stepBFS t = some t' ∧ stepGK t = t'
  | .s, h => by cases h
  | .var _, h => by cases h
  | .app l r, h => by
    unfold redexCount at h
    cases hrr : isRootRedex (l ⋅ r) with
    | true =>
      rw [hrr] at h
      have h1 : 1 + (redexCount l + redexCount r) = 1 + 0 := h
      have hsum : redexCount l + redexCount r = 0 := Nat.add_left_cancel h1
      have hl0 := nat_add_eq_zero_left hsum
      have hr0 := nat_add_eq_zero_right hsum
      have ihl := no_redex_evaluators_idle l hl0
      have ihr := no_redex_evaluators_idle r hr0
      cases l with
      | s => cases hrr | var _ => cases hrr
      | app l1 y => cases l1 with
        | s => cases hrr | var _ => cases hrr
        | app l11 x => cases l11 with
          | s =>
            have hl_sub : redexCount (.s ⋅ x) + redexCount y = 0 := by
              unfold redexCount at hl0
              have hnr1 : isRootRedex (.s ⋅ x ⋅ y) = false := rfl
              rw [hnr1] at hl0
              simpa using hl0
            have hsx0 := nat_add_eq_zero_left hl_sub
            have hy0 := nat_add_eq_zero_right hl_sub
            have hx0 : redexCount x = 0 := by
              unfold redexCount at hsx0
              have hnr2 : isRootRedex (.s ⋅ x) = false := rfl
              rw [hnr2] at hsx0
              have h0x : 0 + redexCount x = 0 := by simpa [redexCount] using hsx0
              simpa using h0x
            have hgk_x := (no_redex_evaluators_idle x hx0).2.2.2.2.2.2
            have hgk_y := (no_redex_evaluators_idle y hy0).2.2.2.2.2.2
            have hgk_r := ihr.2.2.2.2.2.2
            refine ⟨(x ⋅ r) ⋅ (y ⋅ r), rfl,
              stepLI_root x y r ihl.2.1 ihr.2.1,
              rfl,
              stepRI_root x y r ihl.2.2.2.1 ihr.2.2.2.1,
              rfl, ?_⟩
            show (stepGK x ⋅ stepGK r) ⋅ (stepGK y ⋅ stepGK r) = (x ⋅ r) ⋅ (y ⋅ r)
            rw [hgk_x, hgk_y, hgk_r]
          | var _ => cases hrr | app _ _ => cases hrr
    | false =>
      rw [hrr] at h
      have hsum : redexCount l + redexCount r = 1 := by simpa using h
      cases hcl : redexCount l with
      | zero =>
        rw [hcl] at hsum
        have hcr : redexCount r = 1 := by simpa using hsum
        rcases no_redex_evaluators_idle l hcl with ⟨hlo_l, hli_l, hro_l, hri_l, hm_l, _, hgk_l⟩
        rcases pure_line_all_six_coincide r hcr with ⟨r', hlo_r, hli_r, hro_r, hri_r, hbfs_r, hgk_r⟩
        rcases minRedexDepth_some_of_pos r hcr with ⟨dr, hm_r⟩
        refine ⟨l ⋅ r', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [stepLO_not_root hrr, hlo_l, hlo_r]
        · rw [stepLI_not_root hrr, hli_l, hli_r]
        · rw [stepRO_not_root hrr, hro_r]
        · rw [stepRI_not_root hrr, hri_r]
        · rw [stepBFS_not_root hrr, hm_l, hm_r, hbfs_r]; rfl
        · rw [stepGK_not_root hrr, hgk_l, hgk_r]
      | succ k =>
        have hk0 : k + redexCount r = 0 := by rw [hcl, Nat.succ_add] at hsum; injection hsum
        have hk := nat_add_eq_zero_left hk0
        have hcr := nat_add_eq_zero_right hk0
        subst hk
        rcases no_redex_evaluators_idle r hcr with ⟨hlo_r, hli_r, hro_r, hri_r, hm_r, _, hgk_r⟩
        rcases pure_line_all_six_coincide l hcl with ⟨l', hlo_l, hli_l, hro_l, hri_l, hbfs_l, hgk_l⟩
        rcases minRedexDepth_some_of_pos l hcl with ⟨dl, hm_l⟩
        refine ⟨l' ⋅ r, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [stepLO_not_root hrr, hlo_l]
        · rw [stepLI_not_root hrr, hli_l]
        · rw [stepRO_not_root hrr, hro_r, hro_l]
        · rw [stepRI_not_root hrr, hri_r, hri_l]
        · rw [stepBFS_not_root hrr, hm_l, hm_r, hbfs_l]; rfl
        · rw [stepGK_not_root hrr, hgk_l, hgk_r]

/-! ## Section 2. Unified 6-Strategy Super-Pushdown Theorem via `Zachos` Pure Line -/

def ZTerm : Nat → Term
  | 0 => S ⋅ T_comb ⋅ T_comb
  | k + 1 => T_comb ⋅ ZTerm k

def ZWrap : List Nat → Term → Term
  | [], core => core
  | m :: ms, core => S ⋅ ZTerm m ⋅ ZWrap ms core

theorem redexCount_ZTerm : ∀ (k : Nat), redexCount (ZTerm k) = 0
  | 0 => rfl
  | k + 1 => by
    show 0 + ((0 + (0 + 0)) + redexCount (ZTerm k)) = 0
    rw [redexCount_ZTerm k]

theorem redexCount_ZPair (k m : Nat) : redexCount (ZTerm k ⋅ ZTerm m) = 1 := by
  cases k with
  | zero =>
    show 1 + (0 + redexCount (ZTerm m)) = 1
    rw [redexCount_ZTerm m]
  | succ k' =>
    show 1 + ((0 + ((0 + (0 + 0)) + redexCount (ZTerm k'))) + redexCount (ZTerm m)) = 1
    rw [redexCount_ZTerm k', redexCount_ZTerm m]

theorem redexCount_ZWrap : ∀ (ms : List Nat) (core : Term),
    redexCount (ZWrap ms core) = redexCount core
  | [], _ => rfl
  | m :: ms, core => by
    show 0 + ((0 + (0 + redexCount (ZTerm m))) + redexCount (ZWrap ms core)) = redexCount core
    rw [redexCount_ZTerm m, redexCount_ZWrap ms core]
    simp

theorem stepLO_S_ZTerm (m : Nat) : stepLO (S ⋅ ZTerm m) = none := by
  have h0 : redexCount (S ⋅ ZTerm m) = 0 := by
    show 0 + (0 + redexCount (ZTerm m)) = 0
    rw [redexCount_ZTerm m]
  exact (no_redex_evaluators_idle _ h0).1

theorem stepLO_ZWrap : ∀ (ms : List Nat) (core core' : Term),
    stepLO core = some core' → stepLO (ZWrap ms core) = some (ZWrap ms core')
  | [], _, _, h => h
  | m :: ms, core, core', h => by
    have ih := stepLO_ZWrap ms core core' h
    have hsz := stepLO_S_ZTerm m
    have hnr : isRootRedex ((S ⋅ ZTerm m) ⋅ ZWrap ms core) = false := rfl
    unfold ZWrap
    rw [stepLO_not_root hnr, hsz, ih]

/-- Explicit 8-State Bottom-Up Finite Tree Automaton `BZachos` recognizing active `Z_0 ⋅ Z_n`! -/
inductive StateBZ where
  | bz0 | bz1 | bz2 | bz3 | bz4 | bz5 | bz6 | bz7
  deriving DecidableEq, Repr

def deltaBZ : StateBZ → StateBZ → StateBZ
  | .bz0, .bz0 => .bz1
  | .bz0, .bz1 => .bz2
  | .bz2, .bz1 => .bz3
  | .bz1, .bz3 => .bz4
  | .bz1, .bz4 => .bz4
  | .bz0, .bz3 => .bz5
  | .bz0, .bz4 => .bz5
  | .bz3, .bz3 => .bz6
  | .bz3, .bz4 => .bz6
  | .bz5, .bz6 => .bz6
  | _, _ => .bz7

def evalBZ : Term → StateBZ
  | .s => .bz0
  | .var _ => .bz7
  | .app a b => deltaBZ (evalBZ a) (evalBZ b)

theorem evalBZ_ZTerm_pos : ∀ (k : Nat), evalBZ (ZTerm (k + 1)) = .bz4
  | 0 => rfl
  | k + 1 => by
    have ih := evalBZ_ZTerm_pos k
    show deltaBZ (evalBZ T_comb) (evalBZ (ZTerm (k + 1))) = .bz4
    rw [ih]; rfl

theorem evalBZ_ZPair_zero (n : Nat) : evalBZ (ZTerm 0 ⋅ ZTerm n) = .bz6 := by
  cases n with
  | zero => rfl
  | succ k =>
    show deltaBZ (evalBZ (ZTerm 0)) (evalBZ (ZTerm (k + 1))) = .bz6
    rw [evalBZ_ZTerm_pos k]; rfl

theorem evalBZ_ZPair_succ (k m : Nat) : evalBZ (ZTerm (k + 1) ⋅ ZTerm m) = .bz7 := by
  show deltaBZ (evalBZ (ZTerm (k + 1))) (evalBZ (ZTerm m)) = .bz7
  rw [evalBZ_ZTerm_pos k]
  cases m with
  | zero => rfl
  | succ m' => rw [evalBZ_ZTerm_pos m']; rfl

theorem evalBZ_S_ZTerm (m : Nat) : evalBZ (S ⋅ ZTerm m) = .bz5 := by
  cases m with
  | zero => rfl
  | succ k =>
    show deltaBZ .bz0 (evalBZ (ZTerm (k + 1))) = .bz5
    rw [evalBZ_ZTerm_pos k]; rfl

theorem evalBZ_ZWrap_preserve : ∀ (ms : List Nat) (core : Term),
    (evalBZ core = .bz6 ∨ evalBZ core = .bz7) →
    evalBZ (ZWrap ms core) = evalBZ core
  | [], _, _ => rfl
  | m :: ms, core, hcore => by
    have ih := evalBZ_ZWrap_preserve ms core hcore
    show deltaBZ (evalBZ (S ⋅ ZTerm m)) (evalBZ (ZWrap ms core)) = evalBZ core
    rw [evalBZ_S_ZTerm m, ih]
    rcases hcore with h6 | h7
    · rw [h6]; rfl
    · rw [h7]; rfl


theorem pure_line_step_all_six {a b : Term} (hrc : redexCount a = 1) (hlo : stepLO a = some b) :
    stepLI a = some b ∧ stepRO a = some b ∧ stepRI a = some b ∧ stepBFS a = some b ∧ stepGK a = b := by
  rcases pure_line_all_six_coincide a hrc with ⟨t', h1, h2, h3, h4, h5, h6⟩
  rw [hlo] at h1
  injection h1 with ht
  subst ht
  exact ⟨h2, h3, h4, h5, h6⟩

def repNat : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, v => v :: repNat k v

theorem ZWrap_append : ∀ (xs ys : List Nat) (core : Term),
    ZWrap (xs ++ ys) core = ZWrap xs (ZWrap ys core)
  | [], _, _ => rfl
  | x :: xs, ys, core => by simp [ZWrap, ZWrap_append xs ys core]

theorem zachos_countdown_steps : ∀ (k m : Nat) (ms : List Nat),
    iterOpt stepLO k (ZWrap ms (ZTerm k ⋅ ZTerm m)) =
      some (ZWrap (ms ++ repNat k m) (ZTerm 0 ⋅ ZTerm m)) ∧
    (∀ j, j < k → ∃ tj,
      iterOpt stepLO j (ZWrap ms (ZTerm k ⋅ ZTerm m)) = some tj ∧
      redexCount tj = 1 ∧ evalBZ tj = .bz7)
  | 0, m, ms => by
    refine ⟨by simp [iterOpt, repNat], ?_⟩
    intro j hj; cases hj
  | k + 1, m, ms => by
    have hstep_core : stepLO (ZTerm (k + 1) ⋅ ZTerm m) = some (S ⋅ ZTerm m ⋅ (ZTerm k ⋅ ZTerm m)) := rfl
    have hstep_wrap : stepLO (ZWrap ms (ZTerm (k + 1) ⋅ ZTerm m)) =
        some (ZWrap (ms ++ [m]) (ZTerm k ⋅ ZTerm m)) := by
      have hw := stepLO_ZWrap ms _ _ hstep_core
      rw [ZWrap_append ms [m]]
      exact hw
    rcases zachos_countdown_steps k m (ms ++ [m]) with ⟨h_end, h_mid⟩
    have hrep_eq : (ms ++ [m]) ++ repNat k m = ms ++ repNat (k + 1) m := by
      rw [List.append_assoc]; rfl
    refine ⟨?_, ?_⟩
    · simp [iterOpt, hstep_wrap]
      rw [← hrep_eq]; exact h_end
    · intro j hj
      cases j with
      | zero =>
        refine ⟨ZWrap ms (ZTerm (k + 1) ⋅ ZTerm m), rfl, ?_, ?_⟩
        · rw [redexCount_ZWrap, redexCount_ZPair]
        · rw [evalBZ_ZWrap_preserve _ _ (Or.inr (evalBZ_ZPair_succ k m)), evalBZ_ZPair_succ]
      | succ j' =>
        have hj' : j' < k := Nat.lt_of_succ_lt_succ hj
        simp [iterOpt, hstep_wrap]
        exact h_mid j' hj'

theorem zachos_full_cycle (n : Nat) (ms : List Nat) :
    iterOpt stepLO (n + 2) (ZWrap ms (ZTerm 0 ⋅ ZTerm n)) =
      some (ZWrap (ms ++ repNat (n + 1) (n + 1)) (ZTerm 0 ⋅ ZTerm (n + 1))) ∧
    evalBZ (ZWrap ms (ZTerm 0 ⋅ ZTerm n)) = .bz6 ∧
    (∀ j, 1 ≤ j → j ≤ n + 1 → ∃ tj,
      iterOpt stepLO j (ZWrap ms (ZTerm 0 ⋅ ZTerm n)) = some tj ∧
      redexCount tj = 1 ∧ evalBZ tj = .bz7) := by
  have hstep0_core : stepLO (ZTerm 0 ⋅ ZTerm n) = some (ZTerm (n + 1) ⋅ ZTerm (n + 1)) := rfl
  have hstep0 : stepLO (ZWrap ms (ZTerm 0 ⋅ ZTerm n)) =
      some (ZWrap ms (ZTerm (n + 1) ⋅ ZTerm (n + 1))) :=
    stepLO_ZWrap ms _ _ hstep0_core
  rcases zachos_countdown_steps (n + 1) (n + 1) ms with ⟨h_end, h_mid⟩
  refine ⟨?_, ?_, ?_⟩
  · have h_iter_succ : ∀ (k : Nat) (u v : Term), stepLO u = some v → iterOpt stepLO (k + 1) u = iterOpt stepLO k v :=
      fun _ _ _ hs => by simp [iterOpt, hs]
    rw [h_iter_succ (n + 1) _ _ hstep0]
    exact h_end
  · rw [evalBZ_ZWrap_preserve _ _ (Or.inl (evalBZ_ZPair_zero n)), evalBZ_ZPair_zero]
  · intro j hj1 hjn
    cases j with
    | zero => cases hj1
    | succ j' =>
      have hj' : j' < n + 1 := hjn
      simp [iterOpt, hstep0]
      exact h_mid j' hj'

def quadTime : Nat → Nat
  | 0 => 0
  | n + 1 => quadTime n + (n + 2)

def zachosPrefix : Nat → List Nat
  | 0 => []
  | n + 1 => zachosPrefix n ++ repNat (n + 1) (n + 1)

theorem iterOpt_add (f : Term → Option Term) : ∀ (a b : Nat) (t u : Term),
    iterOpt f a t = some u → iterOpt f (a + b) t = iterOpt f b u
  | 0, b, t, u, h => by
    injection h with htu; subst htu; simp [Nat.zero_add]
  | a + 1, b, t, u, h => by
    simp [iterOpt] at h
    cases hft : f t with
    | none => rw [hft] at h; cases h
    | some t' =>
      rw [hft] at h
      rw [Nat.succ_add]
      simp [iterOpt, hft]
      exact iterOpt_add f a b t' u h

theorem pure_line_iter_all_six : ∀ (k : Nat) (t u : Term),
    iterOpt stepLO k t = some u →
    (∀ i, i < k → ∃ ti, iterOpt stepLO i t = some ti ∧ redexCount ti = 1) →
    iterOpt stepLI k t = some u ∧ iterOpt stepRO k t = some u ∧
    iterOpt stepRI k t = some u ∧ iterOpt stepBFS k t = some u ∧ iterGK k t = u
  | 0, t, u, h, _ => by
    injection h with htu; subst htu; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, t, u, h, hall => by
    rcases hall 0 (Nat.zero_lt_succ k) with ⟨t0, ht0, hrc0⟩
    injection ht0 with ht0_eq; subst ht0_eq
    simp [iterOpt] at h
    cases hlo : stepLO t with
    | none => rw [hlo] at h; cases h
    | some t1 =>
      rw [hlo] at h
      rcases pure_line_step_all_six hrc0 hlo with ⟨hli, hro, hri, hbfs, hgk⟩
      have hall' : ∀ i, i < k → ∃ ti, iterOpt stepLO i t1 = some ti ∧ redexCount ti = 1 := by
        intro i hi
        rcases hall (i + 1) (Nat.succ_lt_succ hi) with ⟨ti, hti, hrci⟩
        simp [iterOpt, hlo] at hti
        exact ⟨ti, hti, hrci⟩
      rcases pure_line_iter_all_six k t1 u h hall' with ⟨ih_li, ih_ro, ih_ri, ih_bfs, ih_gk⟩
      exact ⟨by simp [iterOpt, hli, ih_li], by simp [iterOpt, hro, ih_ro],
             by simp [iterOpt, hri, ih_ri], by simp [iterOpt, hbfs, ih_bfs],
             by simp [iterGK, hgk, ih_gk]⟩

/-- **Theorem 2.1 (Unified 6-Strategy Quadratic Automaton Trace Theorem on `Zachos`):** -/
theorem zachos_unified_quadratic_trace : ∀ (n : Nat),
    let target := ZWrap (zachosPrefix n) (ZTerm 0 ⋅ ZTerm n)
    iterOpt stepLO (quadTime n) Zachos = some target ∧
    iterOpt stepLI (quadTime n) Zachos = some target ∧
    iterOpt stepRO (quadTime n) Zachos = some target ∧
    iterOpt stepRI (quadTime n) Zachos = some target ∧
    iterOpt stepBFS (quadTime n) Zachos = some target ∧
    iterGK (quadTime n) Zachos = target ∧
    evalBZ target = .bz6 ∧
    (∀ i, i ≤ quadTime n → ∃ ti, iterOpt stepLO i Zachos = some ti ∧ redexCount ti = 1)
  | 0 => by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro i hi
    cases i with
    | zero => exact ⟨Zachos, rfl, rfl⟩
    | succ _ => cases hi
  | n + 1 => by
    rcases zachos_unified_quadratic_trace n with ⟨hlo_n, _, _, _, _, _, _, hall_n⟩
    rcases zachos_full_cycle n (zachosPrefix n) with ⟨hcyc_end, _, hcyc_mid⟩
    have hlo_next : iterOpt stepLO (quadTime (n + 1)) Zachos =
        some (ZWrap (zachosPrefix (n + 1)) (ZTerm 0 ⋅ ZTerm (n + 1))) := by
      unfold quadTime zachosPrefix
      rw [iterOpt_add stepLO (quadTime n) (n + 2) Zachos _ hlo_n]
      exact hcyc_end
    have hall_next : ∀ i, i ≤ quadTime (n + 1) → ∃ ti, iterOpt stepLO i Zachos = some ti ∧ redexCount ti = 1 := by
      intro i hi
      if hle : i ≤ quadTime n then
        exact hall_n i hle
      else
        have hgt : quadTime n < i := Nat.lt_of_not_ge hle
        let j := i - quadTime n
        have hij : i = quadTime n + j := (Nat.add_sub_of_le (Nat.le_of_lt hgt)).symm
        have hj1 : 1 ≤ j := Nat.sub_pos_of_lt hgt
        have hjn2 : j ≤ n + 2 := by
          have hi' : quadTime n + j ≤ quadTime n + (n + 2) := by rw [← hij]; exact hi
          exact Nat.le_of_add_le_add_left hi'
        if hjeq : j = n + 2 then
          rw [hij, hjeq]
          refine ⟨ZWrap (zachosPrefix (n + 1)) (ZTerm 0 ⋅ ZTerm (n + 1)), hlo_next, ?_⟩
          rw [redexCount_ZWrap, redexCount_ZPair]
        else
          have hjn1 : j ≤ n + 1 := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hjn2 hjeq)
          rcases hcyc_mid j hj1 hjn1 with ⟨tj, htj, hrcj, _⟩
          rw [hij, iterOpt_add stepLO (quadTime n) j Zachos _ hlo_n]
          exact ⟨tj, htj, hrcj⟩
    have hall_lt : ∀ i, i < quadTime (n + 1) → ∃ ti, iterOpt stepLO i Zachos = some ti ∧ redexCount ti = 1 :=
      fun i hi => hall_next i (Nat.le_of_lt hi)
    rcases pure_line_iter_all_six (quadTime (n + 1)) Zachos _ hlo_next hall_lt with
      ⟨hli_nx, hro_nx, hri_nx, hbfs_nx, hgk_nx⟩
    have hbz_nx : evalBZ (ZWrap (zachosPrefix (n + 1)) (ZTerm 0 ⋅ ZTerm (n + 1))) = .bz6 := by
      rw [evalBZ_ZWrap_preserve _ _ (Or.inl (evalBZ_ZPair_zero (n + 1))), evalBZ_ZPair_zero]
    exact ⟨hlo_next, hli_nx, hro_nx, hri_nx, hbfs_nx, hgk_nx, hbz_nx, hall_next⟩

/-! ## Section 3. Complete Fibonacci Classification of 2-HNFs & 3-Variable Head Exclusion -/

def hasSpineGe2 : Term → Bool
  | .app (.app _ _) _ => true
  | _ => false

def isGe3App : Term → Bool
  | .app (.app (.app _ _) _) _ => true
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

theorem no_dynamic_hnf1 (a b c w : Term) :
    ¬ Reduces (a ⋅ b ⋅ c) (S ⋅ w) ∧ ¬ Reduces (a ⋅ b ⋅ c) S := by
  constructor
  · intro h; cases spineGe2_preserved_reduces h rfl
  · intro h; cases spineGe2_preserved_reduces h rfl

theorem s_app_reduces_inv {a b : Term} (h : Reduces a b) :
    ∀ (x w : Term), a = S ⋅ x → b = S ⋅ w → Reduces x w := by
  induction h with
  | refl _ =>
    intro x w h1 h2
    have heq := h1.symm.trans h2
    injection heq with _ hxw; subst hxw; exact Reduces.refl _
  | @next _ _ _ hs _ ih =>
    intro x w hu hz; subst hu
    cases hs with
    | left hl => cases hl
    | @right _ _ x' hx' => exact Reduces.next hx' (ih x' w rfl hz)

theorem var_app_not_reduces_s_app {a b : Term} (h : Reduces a b) :
    ∀ (k : Nat) (x w : Term), a = Term.var k ⋅ x → b = S ⋅ w → False := by
  induction h with
  | refl _ =>
    intro k x w h1 h2
    have heq := h1.symm.trans h2; injection heq with hk _; cases hk
  | @next _ _ _ hs _ ih =>
    intro k x w hu hz; subst hu
    cases hs with
    | left hl => cases hl
    | @right _ _ x' _ => exact ih k x' w rfl hz

theorem app_reduces_to_hnf1_iff (f x w : Term) (h : Reduces (f ⋅ x) (S ⋅ w)) :
    f = S ∧ Reduces x w := by
  cases f with
  | s => exact ⟨rfl, s_app_reduces_inv h x w rfl rfl⟩
  | var k => exfalso; exact var_app_not_reduces_s_app h k x w rfl rfl
  | app f1 f2 => exfalso; exact (no_dynamic_hnf1 f1 f2 x w).1 h

def hasNoS : Term → Bool
  | .s => false
  | .var _ => true
  | .app a b => hasNoS a && hasNoS b

theorem hasNoS_irred {a b : Term} (h : Step a b) : hasNoS a = true → False := by
  induction h with
  | root x y z => intro hns; cases and_left (and_left (and_left hns))
  | left _ ih => intro hns; exact ih (and_left hns)
  | right _ ih => intro hns; exact ih (and_right hns)

theorem hasNoS_reduces_eq {a b : Term} (h : Reduces a b) (hns : hasNoS a = true) : b = a := by
  cases h with
  | refl _ => rfl
  | next hs _ => exfalso; exact hasNoS_irred hs hns

def inVisserAny : Term → Bool
  | .s => false
  | .var _ => true
  | .app _ r => inVisserAny r

def inVisserAny2 : Term → Bool
  | .app l r => inVisserAny l && inVisserAny r
  | _ => false

def inVisserAny3 : Term → Bool
  | .app l r => inVisserAny2 l && inVisserAny r
  | _ => false

theorem inVisserAny_step {a b : Term} (h : Step a b) :
    inVisserAny a = true → inVisserAny b = true := by
  induction h with
  | root _ _ _ => simp [inVisserAny]
  | left _ _ => simp [inVisserAny]
  | right _ ih => simp [inVisserAny]; exact ih

theorem inVisserAny2_step {a b : Term} (h : Step a b) :
    inVisserAny2 a = true → inVisserAny2 b = true := by
  cases h with
  | root x y z =>
    intro hv; simp [inVisserAny2, inVisserAny, and_right hv]
  | left hl =>
    intro hv; exact Bool.and_eq_true _ _ |>.mpr ⟨inVisserAny_step hl (and_left hv), and_right hv⟩
  | right hr =>
    intro hv; exact Bool.and_eq_true _ _ |>.mpr ⟨and_left hv, inVisserAny_step hr (and_right hv)⟩

theorem inVisserAny2_reduces {a b : Term} (h : Reduces a b) :
    inVisserAny2 a = true → inVisserAny2 b = true := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (inVisserAny2_step hs hv)

theorem inVisserAny3_step {a b : Term} (h : Step a b) :
    inVisserAny3 a = true → inVisserAny3 b = true := by
  cases h with
  | root x y z =>
    intro hv
    have hx : inVisserAny x = true := and_left (and_left hv)
    have hz : inVisserAny z = true := and_right hv
    simp [inVisserAny3, inVisserAny2, inVisserAny, hx, hz]
  | left hl =>
    intro hv; exact Bool.and_eq_true _ _ |>.mpr ⟨inVisserAny2_step hl (and_left hv), and_right hv⟩
  | right hr =>
    intro hv; exact Bool.and_eq_true _ _ |>.mpr ⟨and_left hv, inVisserAny_step hr (and_right hv)⟩

theorem inVisserAny3_reduces {a b : Term} (h : Reduces a b) :
    inVisserAny3 a = true → inVisserAny3 b = true := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (inVisserAny3_step hs hv)

/-- **Visser–van Oostrom Order ≤ 3 Theorem (`order_le_three_no_hnf2`):** -/
theorem order_le_three_no_hnf2 (u p q : Term) (vx vy vz : Nat) :
    ¬ Reduces (u ⋅ .var vx ⋅ .var vy ⋅ .var vz) (S ⋅ p ⋅ q) := by
  intro hred
  cases inVisserAny3_reduces hred rfl

inductive ReducesN : Nat → Term → Term → Prop where
  | refl (a : Term) : ReducesN 0 a a
  | next {n : Nat} {a b c : Term} : Step a b → ReducesN n b c → ReducesN (n + 1) a c

theorem reducesN_to_reduces {n : Nat} {a b : Term} (h : ReducesN n a b) : Reduces a b := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next hs ih

theorem reduces_to_reducesN {a b : Term} (h : Reduces a b) : ∃ n, ReducesN n a b := by
  induction h with
  | refl _ => exact ⟨0, ReducesN.refl _⟩
  | next hs _ ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, ReducesN.next hs hn⟩

theorem reducesN_app_noS_split {n : Nat} {a c : Term} (h : ReducesN n a c) :
    ∀ (f w : Term), hasNoS w = true → a = f ⋅ w →
      (∃ f', ReducesN n f f' ∧ c = f' ⋅ w) ∨
      (∃ x y n1 n2, n1 + n2 + 1 = n ∧ ReducesN n1 f (S ⋅ x ⋅ y) ∧ ReducesN n2 ((x ⋅ w) ⋅ (y ⋅ w)) c) := by
  induction h with
  | refl _ =>
    intro f w _ ha; subst ha; exact Or.inl ⟨f, ReducesN.refl f, rfl⟩
  | @next m u v z hs hrest ih =>
    intro f w hw ha; subst ha
    cases hs with
    | root x y _ =>
      refine Or.inr ⟨x, y, 0, m, ?_, ReducesN.refl _, hrest⟩
      rw [Nat.zero_add]
    | @left _ f1 _ hf =>
      rcases ih f1 w hw rfl with ⟨f', hf', hc⟩ | ⟨x, y, n1, n2, hsum, hxy, htail⟩
      · exact Or.inl ⟨f', ReducesN.next hf hf', hc⟩
      · refine Or.inr ⟨x, y, n1 + 1, n2, ?_, ReducesN.next hf hxy, htail⟩
        rw [Nat.succ_add, ← hsum]
    | @right _ _ _ hw_step =>
      exfalso; exact hasNoS_irred hw_step hw

def fibW (vx vy : Nat) : Nat → Term
  | 0 => .var vx
  | 1 => .var vy
  | m + 2 => fibW vx vy m ⋅ fibW vx vy (m + 1)

def rTower : Nat → Term
  | 0 => S
  | k + 1 => S ⋅ rTower k

theorem fibW_hasNoS (vx vy : Nat) : ∀ (m : Nat), hasNoS (fibW vx vy m) = true
  | 0 => rfl
  | 1 => rfl
  | m + 2 => by simp [fibW, hasNoS, fibW_hasNoS vx vy m, fibW_hasNoS vx vy (m + 1)]

theorem fibW_inVisserAny (vx vy : Nat) : ∀ (m : Nat), inVisserAny (fibW vx vy m) = true
  | 0 => rfl
  | 1 => rfl
  | m + 2 => by simp [fibW, inVisserAny, fibW_inVisserAny vx vy (m + 1)]

theorem fibW_reduces_forward (vx vy : Nat) : ∀ (k m : Nat),
    Reduces (rTower k ⋅ fibW vx vy m ⋅ fibW vx vy (m + 1)) (S ⋅ fibW vx vy (m + k) ⋅ fibW vx vy (m + k + 1))
  | 0, m => by simp [rTower, Nat.add_zero]; exact Reduces.refl _
  | k + 1, m => by
    have hstep : Step (rTower (k + 1) ⋅ fibW vx vy m ⋅ fibW vx vy (m + 1))
        (rTower k ⋅ fibW vx vy (m + 1) ⋅ fibW vx vy (m + 2)) :=
      Step.root (rTower k) (fibW vx vy m) (fibW vx vy (m + 1))
    have ih := fibW_reduces_forward vx vy k (m + 1)
    have eq1 : m + 1 + k = m + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [eq1] at ih
    exact Reduces.next hstep ih

theorem fib_hnf2_strong : ∀ (n : Nat),
    ∀ (u p q : Term) (vx vy m : Nat),
      isClosed u = true →
      ReducesN n (u ⋅ fibW vx vy m ⋅ fibW vx vy (m + 1)) (S ⋅ p ⋅ q) →
      ∃ k, Reduces u (rTower k) ∧ p = fibW vx vy (m + k) ∧ q = fibW vx vy (m + k + 1) := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih u p q vx vy m hclosed hred
  have hns1 := fibW_hasNoS vx vy (m + 1)
  rcases reducesN_app_noS_split hred (u ⋅ fibW vx vy m) (fibW vx vy (m + 1)) hns1 rfl with
    ⟨f', hf', hc⟩ | ⟨a, b, n1, n2, hsum, hab, htail⟩
  · injection hc with hsp hq
    have hred_f := reducesN_to_reduces hf'
    rw [← hsp] at hred_f
    rcases app_reduces_to_hnf1_iff u (fibW vx vy m) p hred_f with ⟨hu, hp_red⟩
    have hp_eq := hasNoS_reduces_eq hp_red (fibW_hasNoS vx vy m)
    refine ⟨0, ?_, ?_, ?_⟩
    · subst hu; exact Reduces.refl _
    · simp [Nat.add_zero]; exact hp_eq
    · simp [Nat.add_zero]; exact hq
  · have hns0 := fibW_hasNoS vx vy m
    rcases reducesN_app_noS_split hab u (fibW vx vy m) hns0 rfl with
      ⟨u', hu', hu_eq⟩ | ⟨x, y, _, _, _, _, hxy_tail⟩
    · injection hu_eq with hsa_eq hb_eq
      have hred_u : Reduces u (S ⋅ a) := hsa_eq ▸ reducesN_to_reduces hu'
      have hcl_a : isClosed a = true := and_right (reduces_preserves_closed hred_u hclosed)
      subst hb_eq
      have hn2_lt : n2 < n := by
        rw [← hsum]
        exact Nat.lt_succ_of_le (Nat.le_add_left n2 n1)
      rcases ih n2 hn2_lt a p q vx vy (m + 1) hcl_a htail with ⟨k', ha_red, hp, hq⟩
      have eq1 : m + 1 + k' = m + (k' + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k']
      rw [eq1] at hp hq
      refine ⟨k' + 1, ?_, hp, hq⟩
      exact Reduces.trans hred_u (Reduces.cong_right ha_red)
    · exfalso
      have hv_init : inVisserAny2 ((x ⋅ fibW vx vy m) ⋅ (y ⋅ fibW vx vy m)) = true := by
        simp [inVisserAny2, inVisserAny, fibW_inVisserAny vx vy m]
      have hv_sab := inVisserAny2_reduces (reducesN_to_reduces hxy_tail) hv_init
      have hva : inVisserAny a = true := by
        have hl := and_left hv_sab; simpa [inVisserAny] using hl
      have hv3_init : inVisserAny3 ((a ⋅ fibW vx vy (m + 1)) ⋅ (b ⋅ fibW vx vy (m + 1))) = true := by
        simp [inVisserAny3, inVisserAny2, inVisserAny, hva, fibW_inVisserAny vx vy (m + 1)]
      cases inVisserAny3_reduces (reducesN_to_reduces htail) hv3_init

/-- **Theorem 3.1 (Complete Fibonacci Classification of Parametric 2-HNFs in Pure `S`):** -/
theorem closed_two_var_reduces_hnf2_iff (u p q : Term) (vx vy : Nat) (hcl : isClosed u = true) :
    Reduces (u ⋅ .var vx ⋅ .var vy) (S ⋅ p ⋅ q) ↔
      ∃ k, Reduces u (rTower k) ∧ p = fibW vx vy k ∧ q = fibW vx vy (k + 1) := by
  constructor
  · intro h
    rcases reduces_to_reducesN h with ⟨n, hn⟩
    rcases fib_hnf2_strong n u p q vx vy 0 hcl hn with ⟨k, huk, hp, hq⟩
    simp [Nat.zero_add] at hp hq
    exact ⟨k, huk, hp, hq⟩
  · rintro ⟨k, huk, rfl, rfl⟩
    have hcong : Reduces (u ⋅ .var vx ⋅ .var vy) (rTower k ⋅ .var vx ⋅ .var vy) :=
      Reduces.cong_left (Reduces.cong_left huk)
    have hfwd := fibW_reduces_forward vx vy k 0
    simp [fibW, Nat.zero_add] at hfwd
    exact Reduces.trans hcong hfwd

def headLeaf : Term → Option Nat
  | .s => none
  | .var k => some k
  | .app a _ => headLeaf a

def isHNF : Term → Bool
  | .s => true
  | .var _ => true
  | .app .s _ => true
  | .app (.app .s _) _ => true
  | .app (.app (.app .s _) _) _ => false
  | .app a _ => isHNF a

theorem headLeaf_fibW_in_xy (vx vy : Nat) : ∀ (k : Nat),
    headLeaf (fibW vx vy k) = some vx ∨ headLeaf (fibW vx vy k) = some vy
  | 0 => Or.inl rfl
  | 1 => Or.inr rfl
  | k + 2 => headLeaf_fibW_in_xy vx vy k

def onlyVarsXY (vx vy : Nat) : Term → Bool
  | .s => true
  | .var k => decide (k = vx) || decide (k = vy)
  | .app a b => onlyVarsXY vx vy a && onlyVarsXY vx vy b

theorem onlyVarsXY_step {vx vy : Nat} {a b : Term} (h : Step a b) :
    onlyVarsXY vx vy a = true → onlyVarsXY vx vy b = true := by
  induction h with
  | root x y z =>
    intro hxy
    have h1 := and_left hxy
    have hz := and_right hxy
    have hy := and_right h1
    have hx := and_right (and_left h1)
    simp [onlyVarsXY, hx, hy, hz]
  | left _ ih => intro hxy; exact Bool.and_eq_true _ _ |>.mpr ⟨ih (and_left hxy), and_right hxy⟩
  | right _ ih => intro hxy; exact Bool.and_eq_true _ _ |>.mpr ⟨and_left hxy, ih (and_right hxy)⟩

theorem onlyVarsXY_reduces {vx vy : Nat} {a b : Term} (h : Reduces a b) :
    onlyVarsXY vx vy a = true → onlyVarsXY vx vy b = true := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (onlyVarsXY_step hs hv)

theorem closed_implies_onlyVarsXY (vx vy : Nat) : ∀ (u : Term),
    isClosed u = true → onlyVarsXY vx vy u = true
  | .s, _ => rfl
  | .var _, h => by cases h
  | .app a b, h => Bool.and_eq_true _ _ |>.mpr
      ⟨closed_implies_onlyVarsXY vx vy a (and_left h), closed_implies_onlyVarsXY vx vy b (and_right h)⟩

theorem headLeaf_not_s_of_isHNF_ge3 : ∀ (t : Term),
    isGe3App t = true → isHNF t = true → headLeaf t ≠ none
  | .app (.app (.app .s _) _) _, _, hhnf => by cases hhnf
  | .app (.app (.app (.var _) _) _) _, _, _ => by simp [headLeaf]
  | .app (.app (.app (.app a b) c) d) e, _, hhnf => by
    have hsub : isHNF (((a ⋅ b) ⋅ c) ⋅ d) = true := hhnf
    simpa [headLeaf] using headLeaf_not_s_of_isHNF_ge3 (((a ⋅ b) ⋅ c) ⋅ d) rfl hsub
  | .s, hge, _ => by cases hge
  | .var _, hge, _ => by cases hge
  | .app .s _, hge, _ => by cases hge
  | .app (.var _) _, hge, _ => by cases hge
  | .app (.app .s _) _, hge, _ => by cases hge
  | .app (.app (.var _) _) _, hge, _ => by cases hge

theorem headLeaf_in_xy_of_onlyVarsXY (vx vy : Nat) : ∀ (t : Term),
    onlyVarsXY vx vy t = true → headLeaf t ≠ none →
    headLeaf t = some vx ∨ headLeaf t = some vy
  | .s, _, hne => False.elim (hne rfl)
  | .var k, hxy, _ => by
    simp [onlyVarsXY] at hxy
    rcases hxy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | .app a _, hxy, hne => headLeaf_in_xy_of_onlyVarsXY vx vy a (and_left hxy) hne

/-- **Theorem 3.2 (3-Variable Head Exclusion Theorem):** -/
theorem three_var_hnf_head_in_xy (u h : Term) (vx vy vz : Nat)
    (hcl : isClosed u = true)
    (hred : Reduces (u ⋅ .var vx ⋅ .var vy ⋅ .var vz) h)
    (hhnf : isHNF h = true) :
    headLeaf h = some vx ∨ headLeaf h = some vy := by
  rcases reduces_to_reducesN hred with ⟨n, hn⟩
  rcases reducesN_app_noS_split hn (u ⋅ .var vx ⋅ .var vy) (.var vz) rfl rfl with
    ⟨f', hf', h_eq⟩ | ⟨p, q, _, _, _, hpq, htail⟩
  · subst h_eq
    have hred_f := reducesN_to_reduces hf'
    have hge2 : hasSpineGe2 f' = true := spineGe2_preserved_reduces hred_f rfl
    have hge3 : isGe3App (f' ⋅ .var vz) = true := by
      cases f' with
      | s => cases hge2 | var _ => cases hge2
      | app f1 _ => cases f1 with
        | s => cases hge2 | var _ => cases hge2 | app _ _ => rfl
    have hne : headLeaf f' ≠ none := headLeaf_not_s_of_isHNF_ge3 (f' ⋅ .var vz) hge3 hhnf
    have hxy0 : onlyVarsXY vx vy (u ⋅ .var vx ⋅ .var vy) = true := by
      simp [onlyVarsXY, closed_implies_onlyVarsXY vx vy u hcl]
    have hxy_f := onlyVarsXY_reduces hred_f hxy0
    exact headLeaf_in_xy_of_onlyVarsXY vx vy f' hxy_f hne
  · have hred_pq := reducesN_to_reduces hpq
    rcases (closed_two_var_reduces_hnf2_iff u p q vx vy hcl).mp hred_pq with ⟨k, _, rfl, rfl⟩
    have hnoS_rhs : hasNoS ((fibW vx vy k ⋅ .var vz) ⋅ (fibW vx vy (k + 1) ⋅ .var vz)) = true := by
      simp [hasNoS, fibW_hasNoS vx vy k, fibW_hasNoS vx vy (k + 1)]
    have hh_eq := hasNoS_reduces_eq (reducesN_to_reduces htail) hnoS_rhs
    subst hh_eq
    simpa [headLeaf] using headLeaf_fibW_in_xy vx vy k


/-! ## Section 4. `A_HN` (35 States), `INF_HEAD` Outer-Spine Blindness, and Sharp 5-Argument Horizon -/

inductive StateHN where
  | h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34

private def deltaHN_0 : StateHN → StateHN | .h0 => .h1 | .h1 => .h2 | .h2 => .h3 | .h3 => .h4 | .h4 => .h5 | .h5 => .h5 | .h6 => .h7 | .h7 => .h8 | .h8 => .h9 | .h9 => .h10 | .h10 => .h10 | .h11 => .h12 | .h12 => .h8 | .h13 => .h12 | .h14 => .h15 | .h15 => .h8 | .h16 => .h8 | .h17 => .h9 | .h18 => .h19 | .h19 => .h9 | .h20 => .h21 | .h21 => .h9 | .h22 => .h10 | .h23 => .h10 | .h24 => .h10 | .h25 => .h10 | .h26 => .h27 | .h27 => .h10 | .h28 => .h9 | .h29 => .h9 | .h30 => .h9 | .h31 => .h27 | .h32 => .h9 | .h33 => .h10 | .h34 => .h10
private def deltaHN_1 : StateHN → StateHN | .h0 => .h6 | .h1 => .h11 | .h2 => .h13 | .h3 => .h13 | .h4 => .h13 | .h5 => .h13 | .h6 => .h13 | .h7 => .h13 | .h8 => .h13 | .h9 => .h13 | .h10 => .h13 | .h11 => .h13 | .h12 => .h13 | .h13 => .h13 | .h14 => .h13 | .h15 => .h13 | .h16 => .h13 | .h17 => .h13 | .h18 => .h13 | .h19 => .h13 | .h20 => .h13 | .h21 => .h13 | .h22 => .h13 | .h23 => .h13 | .h24 => .h13 | .h25 => .h13 | .h26 => .h13 | .h27 => .h13 | .h28 => .h13 | .h29 => .h13 | .h30 => .h13 | .h31 => .h13 | .h32 => .h13 | .h33 => .h13 | .h34 => .h13
private def deltaHN_2 : StateHN → StateHN | .h0 => .h14 | .h1 => .h16 | .h2 => .h8 | .h3 => .h9 | .h4 => .h10 | .h5 => .h10 | .h6 => .h17 | .h7 => .h9 | .h8 => .h10 | .h9 => .h10 | .h10 => .h10 | .h11 => .h17 | .h12 => .h9 | .h13 => .h17 | .h14 => .h10 | .h15 => .h10 | .h16 => .h10 | .h17 => .h10 | .h18 => .h10 | .h19 => .h10 | .h20 => .h10 | .h21 => .h10 | .h22 => .h10 | .h23 => .h10 | .h24 => .h10 | .h25 => .h10 | .h26 => .h10 | .h27 => .h10 | .h28 => .h10 | .h29 => .h10 | .h30 => .h10 | .h31 => .h10 | .h32 => .h10 | .h33 => .h10 | .h34 => .h10
private def deltaHN_3 : StateHN → StateHN | .h0 => .h18 | .h1 => .h20 | .h2 => .h20 | .h3 => .h20 | .h4 => .h20 | .h5 => .h20 | .h6 => .h20 | .h7 => .h20 | .h8 => .h20 | .h9 => .h20 | .h10 => .h20 | .h11 => .h20 | .h12 => .h20 | .h13 => .h20 | .h14 => .h20 | .h15 => .h20 | .h16 => .h20 | .h17 => .h20 | .h18 => .h20 | .h19 => .h20 | .h20 => .h20 | .h21 => .h20 | .h22 => .h20 | .h23 => .h20 | .h24 => .h20 | .h25 => .h20 | .h26 => .h20 | .h27 => .h20 | .h28 => .h20 | .h29 => .h20 | .h30 => .h20 | .h31 => .h20 | .h32 => .h20 | .h33 => .h20 | .h34 => .h20
private def deltaHN_4 : StateHN → StateHN | .h0 => .h8 | .h1 => .h10 | .h2 => .h10 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | .h6 => .h10 | .h7 => .h10 | .h8 => .h10 | .h9 => .h10 | .h10 => .h10 | .h11 => .h10 | .h12 => .h10 | .h13 => .h10 | .h14 => .h10 | .h15 => .h10 | .h16 => .h10 | .h17 => .h10 | .h18 => .h10 | .h19 => .h10 | .h20 => .h10 | .h21 => .h10 | .h22 => .h10 | .h23 => .h10 | .h24 => .h10 | .h25 => .h10 | .h26 => .h10 | .h27 => .h10 | .h28 => .h10 | .h29 => .h10 | .h30 => .h10 | .h31 => .h10 | .h32 => .h10 | .h33 => .h10 | .h34 => .h10
private def deltaHN_5 (_ : StateHN) : StateHN := .h10
private def deltaHN_6 : StateHN → StateHN | .h0 => .h11 | .h1 => .h8 | .h2 => .h20 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | .h6 => .h22 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h22 | .h12 => .h23 | .h13 => .h22 | .h14 => .h24 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h25 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h25 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h25 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_7 : StateHN → StateHN | .h0 => .h26 | .h1 => .h28 | .h2 => .h29 | .h3 => .h22 | .h4 => .h24 | .h5 => .h24 | .h6 => .h30 | .h7 => .h22 | .h8 => .h24 | .h9 => .h24 | .h10 => .h24 | .h11 => .h30 | .h12 => .h22 | .h13 => .h30 | .h14 => .h24 | .h15 => .h24 | .h16 => .h24 | .h17 => .h24 | .h18 => .h24 | .h19 => .h24 | .h20 => .h24 | .h21 => .h24 | .h22 => .h24 | .h23 => .h24 | .h24 => .h24 | .h25 => .h24 | .h26 => .h24 | .h27 => .h24 | .h28 => .h24 | .h29 => .h24 | .h30 => .h24 | .h31 => .h24 | .h32 => .h24 | .h33 => .h24 | .h34 => .h24
private def deltaHN_8 : StateHN → StateHN | .h0 => .h24 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h23 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h23 | .h12 => .h23 | .h13 => .h23 | .h14 => .h23 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h23 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h23 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h23 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_9 : StateHN → StateHN | .h0 => .h25 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h23 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h23 | .h12 => .h23 | .h13 => .h23 | .h14 => .h23 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h23 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h23 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h23 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_10 (_ : StateHN) : StateHN := .h23
private def deltaHN_11 : StateHN → StateHN | .h0 => .h13 | .h1 => .h17 | .h2 => .h20 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | .h6 => .h30 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h29 | .h12 => .h23 | .h13 => .h29 | .h14 => .h24 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h25 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h25 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h25 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_12 : StateHN → StateHN | .h0 => .h31 | .h1 => .h29 | .h2 => .h29 | .h3 => .h22 | .h4 => .h24 | .h5 => .h24 | .h6 => .h29 | .h7 => .h22 | .h8 => .h24 | .h9 => .h24 | .h10 => .h24 | .h11 => .h29 | .h12 => .h22 | .h13 => .h29 | .h14 => .h24 | .h15 => .h24 | .h16 => .h24 | .h17 => .h24 | .h18 => .h24 | .h19 => .h24 | .h20 => .h24 | .h21 => .h24 | .h22 => .h24 | .h23 => .h24 | .h24 => .h24 | .h25 => .h24 | .h26 => .h24 | .h27 => .h24 | .h28 => .h24 | .h29 => .h24 | .h30 => .h24 | .h31 => .h24 | .h32 => .h24 | .h33 => .h24 | .h34 => .h24
private def deltaHN_13 : StateHN → StateHN | .h0 => .h13 | .h1 => .h10 | .h2 => .h20 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | .h6 => .h24 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h24 | .h12 => .h23 | .h13 => .h24 | .h14 => .h24 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h25 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h25 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h25 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_14 : StateHN → StateHN | .h0 => .h8 | .h1 => .h20 | .h2 => .h10 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | .h6 => .h23 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h23 | .h12 => .h23 | .h13 => .h23 | .h14 => .h23 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h23 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h23 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h23 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_15 (_ : StateHN) : StateHN := .h24
private def deltaHN_16 : StateHN → StateHN | .h0 => .h22 | .h1 => .h29 | .h2 => .h24 | .h3 => .h24 | .h4 => .h24 | .h5 => .h24 | .h6 => .h24 | .h7 => .h24 | .h8 => .h24 | .h9 => .h24 | .h10 => .h24 | .h11 => .h24 | .h12 => .h24 | .h13 => .h24 | .h14 => .h24 | .h15 => .h24 | .h16 => .h24 | .h17 => .h24 | .h18 => .h24 | .h19 => .h24 | .h20 => .h24 | .h21 => .h24 | .h22 => .h24 | .h23 => .h24 | .h24 => .h24 | .h25 => .h24 | .h26 => .h24 | .h27 => .h24 | .h28 => .h24 | .h29 => .h24 | .h30 => .h24 | .h31 => .h24 | .h32 => .h24 | .h33 => .h24 | .h34 => .h24
private def deltaHN_17 : StateHN → StateHN | .h0 => .h22 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h23 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h23 | .h12 => .h23 | .h13 => .h23 | .h14 => .h23 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h23 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h23 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h23 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_18 : StateHN → StateHN | .h0 => .h20 | .h1 => .h24 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h23 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h23 | .h12 => .h23 | .h13 => .h23 | .h14 => .h23 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h23 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h23 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h23 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_19 : StateHN → StateHN | .h0 => .h32 | .h1 => .h25 | .h2 => .h25 | .h3 => .h25 | .h4 => .h25 | .h5 => .h25 | .h6 => .h25 | .h7 => .h25 | .h8 => .h25 | .h9 => .h25 | .h10 => .h25 | .h11 => .h25 | .h12 => .h25 | .h13 => .h25 | .h14 => .h25 | .h15 => .h25 | .h16 => .h25 | .h17 => .h25 | .h18 => .h25 | .h19 => .h25 | .h20 => .h25 | .h21 => .h25 | .h22 => .h25 | .h23 => .h25 | .h24 => .h25 | .h25 => .h25 | .h26 => .h25 | .h27 => .h25 | .h28 => .h25 | .h29 => .h25 | .h30 => .h25 | .h31 => .h25 | .h32 => .h25 | .h33 => .h25 | .h34 => .h25
private def deltaHN_20 : StateHN → StateHN | .h0 => .h23 | .h1 => .h24 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h23 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h23 | .h12 => .h23 | .h13 => .h23 | .h14 => .h23 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h23 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h23 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h23 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_21 : StateHN → StateHN | .h0 => .h33 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h23 | .h7 => .h23 | .h8 => .h23 | .h9 => .h23 | .h10 => .h23 | .h11 => .h23 | .h12 => .h23 | .h13 => .h23 | .h14 => .h23 | .h15 => .h23 | .h16 => .h23 | .h17 => .h23 | .h18 => .h23 | .h19 => .h23 | .h20 => .h23 | .h21 => .h23 | .h22 => .h23 | .h23 => .h23 | .h24 => .h23 | .h25 => .h23 | .h26 => .h23 | .h27 => .h23 | .h28 => .h23 | .h29 => .h23 | .h30 => .h23 | .h31 => .h23 | .h32 => .h23 | .h33 => .h23 | .h34 => .h23
private def deltaHN_22 : StateHN → StateHN | .h0 => .h25 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_23 (_ : StateHN) : StateHN := .h34
private def deltaHN_24 : StateHN → StateHN | .h0 => .h23 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_25 : StateHN → StateHN | .h0 => .h23 | .h1 => .h34 | .h2 => .h34 | .h3 => .h34 | .h4 => .h34 | .h5 => .h34 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_26 : StateHN → StateHN | .h0 => .h17 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_27 (_ : StateHN) : StateHN := .h25
private def deltaHN_28 : StateHN → StateHN | .h0 => .h30 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_29 : StateHN → StateHN | .h0 => .h24 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_30 : StateHN → StateHN | .h0 => .h29 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_31 : StateHN → StateHN | .h0 => .h10 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_32 : StateHN → StateHN | .h0 => .h24 | .h1 => .h23 | .h2 => .h34 | .h3 => .h34 | .h4 => .h34 | .h5 => .h34 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_33 : StateHN → StateHN | .h0 => .h34 | .h1 => .h23 | .h2 => .h34 | .h3 => .h34 | .h4 => .h34 | .h5 => .h34 | .h6 => .h34 | .h7 => .h34 | .h8 => .h34 | .h9 => .h34 | .h10 => .h34 | .h11 => .h34 | .h12 => .h34 | .h13 => .h34 | .h14 => .h34 | .h15 => .h34 | .h16 => .h34 | .h17 => .h34 | .h18 => .h34 | .h19 => .h34 | .h20 => .h34 | .h21 => .h34 | .h22 => .h34 | .h23 => .h34 | .h24 => .h34 | .h25 => .h34 | .h26 => .h34 | .h27 => .h34 | .h28 => .h34 | .h29 => .h34 | .h30 => .h34 | .h31 => .h34 | .h32 => .h34 | .h33 => .h34 | .h34 => .h34
private def deltaHN_34 (_ : StateHN) : StateHN := .h34
def deltaHN : StateHN → StateHN → StateHN | .h0 => deltaHN_0 | .h1 => deltaHN_1 | .h2 => deltaHN_2 | .h3 => deltaHN_3 | .h4 => deltaHN_4 | .h5 => deltaHN_5 | .h6 => deltaHN_6 | .h7 => deltaHN_7 | .h8 => deltaHN_8 | .h9 => deltaHN_9 | .h10 => deltaHN_10 | .h11 => deltaHN_11 | .h12 => deltaHN_12 | .h13 => deltaHN_13 | .h14 => deltaHN_14 | .h15 => deltaHN_15 | .h16 => deltaHN_16 | .h17 => deltaHN_17 | .h18 => deltaHN_18 | .h19 => deltaHN_19 | .h20 => deltaHN_20 | .h21 => deltaHN_21 | .h22 => deltaHN_22 | .h23 => deltaHN_23 | .h24 => deltaHN_24 | .h25 => deltaHN_25 | .h26 => deltaHN_26 | .h27 => deltaHN_27 | .h28 => deltaHN_28 | .h29 => deltaHN_29 | .h30 => deltaHN_30 | .h31 => deltaHN_31 | .h32 => deltaHN_32 | .h33 => deltaHN_33 | .h34 => deltaHN_34

def idx_StateHN : StateHN → Nat
  | .h0 => 0 | .h1 => 1 | .h2 => 2 | .h3 => 3 | .h4 => 4 | .h5 => 5 | .h6 => 6 | .h7 => 7 | .h8 => 8 | .h9 => 9 | .h10 => 10 | .h11 => 11 | .h12 => 12 | .h13 => 13 | .h14 => 14 | .h15 => 15 | .h16 => 16 | .h17 => 17 | .h18 => 18 | .h19 => 19 | .h20 => 20 | .h21 => 21 | .h22 => 22 | .h23 => 23 | .h24 => 24 | .h25 => 25 | .h26 => 26 | .h27 => 27 | .h28 => 28 | .h29 => 29 | .h30 => 30 | .h31 => 31 | .h32 => 32 | .h33 => 33 | .h34 => 34

def ofIdx_StateHN : Nat → StateHN
  | 0 => .h0 | 1 => .h1 | 2 => .h2 | 3 => .h3 | 4 => .h4 | 5 => .h5 | 6 => .h6 | 7 => .h7 | 8 => .h8 | 9 => .h9 | 10 => .h10 | 11 => .h11 | 12 => .h12 | 13 => .h13 | 14 => .h14 | 15 => .h15 | 16 => .h16 | 17 => .h17 | 18 => .h18 | 19 => .h19 | 20 => .h20 | 21 => .h21 | 22 => .h22 | 23 => .h23 | 24 => .h24 | 25 => .h25 | 26 => .h26 | 27 => .h27 | 28 => .h28 | 29 => .h29 | 30 => .h30 | 31 => .h31 | 32 => .h32 | 33 => .h33 | _ => .h34

theorem ofIdx_idx_StateHN (a : StateHN) : ofIdx_StateHN (idx_StateHN a) = a := by
  cases a <;> rfl

def eq_StateHN (a b : StateHN) : Bool :=
  Nat.beq (idx_StateHN a) (idx_StateHN b)

theorem eq_StateHN_iff (a b : StateHN) : eq_StateHN a b = true ↔ a = b := by
  unfold eq_StateHN
  constructor
  · intro h
    have hidx : idx_StateHN a = idx_StateHN b := Nat.eq_of_beq_eq_true h
    have hcongr := congrArg ofIdx_StateHN hidx
    rw [ofIdx_idx_StateHN a, ofIdx_idx_StateHN b] at hcongr
    exact hcongr
  · intro h
    subst h
    exact Nat.beq_refl _

theorem eq_StateHN_false_of_ne {a b : StateHN} (h : a ≠ b) : eq_StateHN a b = false := by
  cases heq : eq_StateHN a b with
  | false => rfl
  | true => exact False.elim (h ((eq_StateHN_iff a b).mp heq))

instance : DecidableEq StateHN := fun a b =>
  if h : eq_StateHN a b = true then
    isTrue ((eq_StateHN_iff a b).mp h)
  else
    isFalse (fun hab => h ((eq_StateHN_iff a b).mpr hab))

def checkAll1_StateHN (p : StateHN → Bool) : Bool :=
  (((((p .h0 && p .h1) && (p .h2 && p .h3)) && ((p .h4 && p .h5) && (p .h6 && p .h7))) && (((p .h8 && p .h9) && (p .h10 && p .h11)) && ((p .h12 && p .h13) && (p .h14 && (p .h15 && p .h16))))) && ((((p .h17 && p .h18) && (p .h19 && p .h20)) && ((p .h21 && p .h22) && (p .h23 && (p .h24 && p .h25)))) && (((p .h26 && p .h27) && (p .h28 && p .h29)) && ((p .h30 && p .h31) && (p .h32 && (p .h33 && p .h34))))))

theorem checkAll1_StateHN_sound (p : StateHN → Bool)
    (h : checkAll1_StateHN p = true) (x : StateHN) : p x = true :=
  match x with
  | .h0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .h1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .h2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .h3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .h4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .h5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .h6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .h7 => (and_right (and_right (and_right (and_left (and_left h)))))
  | .h8 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .h9 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .h10 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .h11 => (and_right (and_right (and_left (and_right (and_left h)))))
  | .h12 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .h13 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .h14 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .h15 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .h16 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .h17 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .h18 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .h19 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .h20 => (and_right (and_right (and_left (and_left (and_right h)))))
  | .h21 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .h22 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .h23 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .h24 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .h25 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .h26 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .h27 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .h28 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .h29 => (and_right (and_right (and_left (and_right (and_right h)))))
  | .h30 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .h31 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .h32 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .h33 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .h34 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateHN (p : StateHN → StateHN → Bool) : Bool :=
  checkAll1_StateHN (fun x => checkAll1_StateHN (fun y => p x y))

theorem checkAll2_StateHN_sound (p : StateHN → StateHN → Bool)
    (h : checkAll2_StateHN p = true) (x y : StateHN) : p x y = true :=
  checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ h x) y

private theorem s_row_StateHN_0 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h0) y) z) (deltaHN (deltaHN .h0 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_1 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h1) y) z) (deltaHN (deltaHN .h1 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_2 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h2) y) z) (deltaHN (deltaHN .h2 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_3 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h3) y) z) (deltaHN (deltaHN .h3 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_4 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h4) y) z) (deltaHN (deltaHN .h4 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_5 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h5) y) z) (deltaHN (deltaHN .h5 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_6 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h6) y) z) (deltaHN (deltaHN .h6 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_7 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h7) y) z) (deltaHN (deltaHN .h7 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_8 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h8) y) z) (deltaHN (deltaHN .h8 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_9 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h9) y) z) (deltaHN (deltaHN .h9 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_10 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h10) y) z) (deltaHN (deltaHN .h10 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_11 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h11) y) z) (deltaHN (deltaHN .h11 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_12 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h12) y) z) (deltaHN (deltaHN .h12 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_13 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h13) y) z) (deltaHN (deltaHN .h13 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_14 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h14) y) z) (deltaHN (deltaHN .h14 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_15 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h15) y) z) (deltaHN (deltaHN .h15 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_16 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h16) y) z) (deltaHN (deltaHN .h16 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_17 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h17) y) z) (deltaHN (deltaHN .h17 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_18 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h18) y) z) (deltaHN (deltaHN .h18 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_19 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h19) y) z) (deltaHN (deltaHN .h19 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_20 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h20) y) z) (deltaHN (deltaHN .h20 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_21 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h21) y) z) (deltaHN (deltaHN .h21 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_22 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h22) y) z) (deltaHN (deltaHN .h22 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_23 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h23) y) z) (deltaHN (deltaHN .h23 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_24 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h24) y) z) (deltaHN (deltaHN .h24 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_25 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h25) y) z) (deltaHN (deltaHN .h25 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_26 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h26) y) z) (deltaHN (deltaHN .h26 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_27 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h27) y) z) (deltaHN (deltaHN .h27 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_28 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h28) y) z) (deltaHN (deltaHN .h28 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_29 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h29) y) z) (deltaHN (deltaHN .h29 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_30 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h30) y) z) (deltaHN (deltaHN .h30 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_31 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h31) y) z) (deltaHN (deltaHN .h31 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_32 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h32) y) z) (deltaHN (deltaHN .h32 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_33 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h33) y) z) (deltaHN (deltaHN .h33 z) (deltaHN y z))) = true := rfl
private theorem s_row_StateHN_34 : checkAll2_StateHN (fun y z => eq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h34) y) z) (deltaHN (deltaHN .h34 z) (deltaHN y z))) = true := rfl

theorem deltaHN_s_law (x y z : StateHN) :
    deltaHN (deltaHN (deltaHN .h0 x) y) z =
    deltaHN (deltaHN x z) (deltaHN y z) :=
  match x with
  | .h0 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_0 y z)
  | .h1 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_1 y z)
  | .h2 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_2 y z)
  | .h3 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_3 y z)
  | .h4 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_4 y z)
  | .h5 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_5 y z)
  | .h6 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_6 y z)
  | .h7 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_7 y z)
  | .h8 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_8 y z)
  | .h9 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_9 y z)
  | .h10 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_10 y z)
  | .h11 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_11 y z)
  | .h12 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_12 y z)
  | .h13 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_13 y z)
  | .h14 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_14 y z)
  | .h15 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_15 y z)
  | .h16 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_16 y z)
  | .h17 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_17 y z)
  | .h18 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_18 y z)
  | .h19 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_19 y z)
  | .h20 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_20 y z)
  | .h21 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_21 y z)
  | .h22 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_22 y z)
  | .h23 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_23 y z)
  | .h24 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_24 y z)
  | .h25 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_25 y z)
  | .h26 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_26 y z)
  | .h27 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_27 y z)
  | .h28 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_28 y z)
  | .h29 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_29 y z)
  | .h30 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_30 y z)
  | .h31 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_31 y z)
  | .h32 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_32 y z)
  | .h33 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_33 y z)
  | .h34 => (eq_StateHN_iff _ _).mp (checkAll2_StateHN_sound _ s_row_StateHN_34 y z)


def evalHN : Term → StateHN
  | .s => .h0
  | .var _ => .h0
  | .app a b => deltaHN (evalHN a) (evalHN b)

theorem evalHN_step_invariant {a b : Term} (h : Step a b) : evalHN a = evalHN b := by
  induction h with
  | root x y z => exact deltaHN_s_law (evalHN x) (evalHN y) (evalHN z)
  | left _ ih => simp [evalHN, ih]
  | right _ ih => simp [evalHN, ih]

theorem evalHN_reduces_invariant {a b : Term} (h : Reduces a b) : evalHN a = evalHN b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalHN_step_invariant hs).trans ih

theorem deltaHN_no_zero_bool :
    checkAll2_StateHN (fun x y => decide (deltaHN x y ≠ .h0)) = true := rfl

theorem deltaHN_no_zero (x y : StateHN) : deltaHN x y ≠ .h0 :=
  of_decide_eq_true (checkAll2_StateHN_sound _ deltaHN_no_zero_bool x y)

theorem evalHN_eq_h0_iff_s (t : Term) (hcl : isClosed t = true) :
    evalHN t = .h0 ↔ t = S := by
  cases t with
  | s => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | var _ => cases hcl
  | app a b =>
    constructor
    · intro h; exfalso; exact deltaHN_no_zero (evalHN a) (evalHN b) h
    · intro h; cases h

theorem deltaHN_inf_left_bool :
    checkAll1_StateHN (fun y => decide (deltaHN .h34 y = .h34)) = true := rfl

theorem deltaHN_inf_left (y : StateHN) : deltaHN .h34 y = .h34 :=
  of_decide_eq_true (checkAll1_StateHN_sound _ deltaHN_inf_left_bool y)

theorem hnf_not_h34_bool :
    (decide (StateHN.h0 ≠ .h34) &&
     checkAll1_StateHN (fun x => decide (deltaHN .h0 x ≠ .h34)) &&
     checkAll2_StateHN (fun x y => decide (deltaHN (deltaHN .h0 x) y ≠ .h34))) = true := rfl

theorem hnf1_not_h34 (x : StateHN) : deltaHN .h0 x ≠ .h34 :=
  of_decide_eq_true (checkAll1_StateHN_sound _ (and_right (and_left hnf_not_h34_bool)) x)

theorem hnf2_not_h34 (x y : StateHN) : deltaHN (deltaHN .h0 x) y ≠ .h34 :=
  of_decide_eq_true (checkAll2_StateHN_sound _ (and_right hnf_not_h34_bool) x y)

theorem stepLO_sound : ∀ (a b : Term), stepLO a = some b → Step a b
  | .s, _, h => by cases h
  | .var _, _, h => by cases h
  | .app l r, b, h => by
    cases hrr : isRootRedex (l ⋅ r) with
    | true =>
      cases l with
      | s => cases hrr | var _ => cases hrr
      | app l1 y => cases l1 with
        | s => cases hrr | var _ => cases hrr
        | app l11 x => cases l11 with
          | s => simp [stepLO] at h; subst h; exact Step.root x y r
          | var _ => cases hrr | app _ _ => cases hrr
    | false =>
      rw [stepLO_not_root hrr] at h
      cases hl : stepLO l with
      | some l' =>
        rw [hl] at h; injection h with hb; subst hb
        exact Step.left (stepLO_sound l l' hl)
      | none =>
        rw [hl] at h
        cases hr : stepLO r with
        | none => rw [hr] at h; cases h
        | some r' =>
          rw [hr] at h; injection h with hb; subst hb
          exact Step.right (stepLO_sound r r' hr)

theorem stepLO_app_of_ge3 {u u' : Term} (hge : isGe3App u = true) (hu : stepLO u = some u') (w : Term) :
    stepLO (u ⋅ w) = some (u' ⋅ w) := by
  have hrr : isRootRedex (u ⋅ w) = false := by
    cases u with
    | s => cases hge | var _ => cases hge
    | app l _ => cases l with
      | s => cases hge | var _ => cases hge
      | app l1 _ => cases l1 with
        | s => cases hge | var _ => rfl | app _ _ => rfl
  rw [stepLO_not_root hrr, hu]

theorem stepLO_appList_of_ge3 : ∀ (ws : List Term) {u u' : Term},
    isGe3App u = true → stepLO u = some u' →
    stepLO (appList u ws) = some (appList u' ws)
  | [], _, _, _, hu => hu
  | w :: rest, u, u', hge, hu =>
    stepLO_appList_of_ge3 rest (u := u ⋅ w) (u' := u' ⋅ w)
      (by cases u with
          | s => cases hge | var _ => cases hge
          | app l _ => cases l with
            | s => cases hge | var _ => cases hge | app _ _ => rfl)
      (stepLO_app_of_ge3 hge hu w)

theorem closed_ge3_has_stepLO : ∀ (a : Term) (b c d : Term),
    isClosed a = true → ∃ t', stepLO (((a ⋅ b) ⋅ c) ⋅ d) = some t'
  | .s, b, c, d, _ => ⟨(b ⋅ d) ⋅ (c ⋅ d), rfl⟩
  | .var _, _, _, _, hcl => by cases hcl
  | .app a1 a2, b, c, d, hcl => by
    rcases closed_ge3_has_stepLO a1 a2 b c (and_left hcl) with ⟨l', hl'⟩
    exact ⟨l' ⋅ d, stepLO_app_of_ge3 rfl hl' d⟩

theorem inf_head_has_ge3_and_stepLO (m : Term) (hcl : isClosed m = true) (hhn : evalHN m = .h34) :
    isGe3App m = true ∧ ∃ m', stepLO m = some m' ∧ isClosed m' = true ∧ evalHN m' = .h34 := by
  cases m with
  | s => cases hhn
  | var _ => cases hcl
  | app l r =>
    cases l with
    | s => exfalso; exact hnf1_not_h34 (evalHN r) hhn
    | var _ => cases and_left hcl
    | app l1 l2 =>
      cases l1 with
      | s => exfalso; exact hnf2_not_h34 (evalHN l2) (evalHN r) hhn
      | var _ => cases and_left (and_left hcl)
      | app a b =>
        have hcl_a : isClosed a = true := and_left (and_left (and_left hcl))
        rcases closed_ge3_has_stepLO a b l2 r hcl_a with ⟨m', hm'⟩
        have hs := stepLO_sound _ m' hm'
        refine ⟨rfl, m', hm', step_preserves_closed hs hcl, ?_⟩
        rw [← evalHN_step_invariant hs]; exact hhn

/-- **Theorem 4.1 (`INF_HEAD` Outer-Spine Blindness under Normal Order `->_{lo}`):** -/
theorem inf_head_tail_frozen_iterLO : ∀ (t : Nat) (m : Term),
    isClosed m = true → evalHN m = .h34 →
    ∃ m_t, iterOpt stepLO t m = some m_t ∧ isClosed m_t = true ∧ evalHN m_t = .h34 ∧
      (∀ ws : List Term, iterOpt stepLO t (appList m ws) = some (appList m_t ws))
  | 0, m, hcl, hhn => ⟨m, rfl, hcl, hhn, fun _ => rfl⟩
  | t + 1, m, hcl, hhn => by
    rcases inf_head_has_ge3_and_stepLO m hcl hhn with ⟨hge, m', hm', hcl', hhn'⟩
    rcases inf_head_tail_frozen_iterLO t m' hcl' hhn' with ⟨m_t, hmt, hcl_t, hhn_t, hws_t⟩
    refine ⟨m_t, by simp [iterOpt, hm', hmt], hcl_t, hhn_t, ?_⟩
    intro ws
    have h1 := stepLO_appList_of_ge3 ws hge hm'
    simp [iterOpt, h1, hws_t ws]

def hnRank : StateHN → Nat
  | .h0 => 4 | .h1 => 4 | .h2 => 3 | .h3 => 3 | .h4 => 2 | .h5 => 2 | .h6 => 3 | .h7 => 2 | .h8 => 1 | .h9 => 1 | .h10 => 1 | .h11 => 3 | .h12 => 2 | .h13 => 3 | .h14 => 3 | .h15 => 2 | .h16 => 2 | .h17 => 1 | .h18 => 2 | .h19 => 1 | .h20 => 2 | .h21 => 1 | .h22 => 1 | .h23 => 0 | .h24 => 1 | .h25 => 0 | .h26 => 1 | .h27 => 1 | .h28 => 1 | .h29 => 1 | .h30 => 1 | .h31 => 1 | .h32 => 1 | .h33 => 1 | .h34 => 0

theorem hnRank_properties_bool :
    (checkAll1_StateHN (fun u =>
       decide (u = .h34 ∨ (hnRank u ≤ 4 ∧
         (deltaHN u .h0 = .h34 ∨ hnRank (deltaHN u .h0) ≤ hnRank u)))) &&
     checkAll2_StateHN (fun u y =>
       decide (u = .h34 ∨ y = .h0 ∨ deltaHN u y = .h34 ∨ hnRank (deltaHN u y) < hnRank u))) = true := rfl

theorem hnRank_le_four {u : StateHN} (hu : u ≠ .h34) : hnRank u ≤ 4 := by
  have h := of_decide_eq_true (checkAll1_StateHN_sound _ (and_left hnRank_properties_bool) u)
  rcases h with rfl | ⟨hle, _⟩
  · exact False.elim (hu rfl)
  · exact hle

theorem hnRank_step_zero {u : StateHN} (hu : u ≠ .h34) :
    deltaHN u .h0 = .h34 ∨ hnRank (deltaHN u .h0) ≤ hnRank u := by
  have h := of_decide_eq_true (checkAll1_StateHN_sound _ (and_left hnRank_properties_bool) u)
  rcases h with rfl | ⟨_, hs0⟩
  · exact False.elim (hu rfl)
  · exact hs0

theorem hnRank_step_nonzero {u y : StateHN} (hu : u ≠ .h34) (hy : y ≠ .h0) :
    deltaHN u y = .h34 ∨ hnRank (deltaHN u y) < hnRank u := by
  have h := of_decide_eq_true (checkAll2_StateHN_sound _ (and_right hnRank_properties_bool) u y)
  rcases h with rfl | rfl | h34 | hlt
  · exact False.elim (hu rfl)
  · exact False.elim (hy rfl)
  · exact Or.inl h34
  · exact Or.inr hlt

def countCompound : List Term → Nat
  | [] => 0
  | w :: ws => countCompound ws + (if w == S then 0 else 1)

def allClosed : List Term → Bool
  | [] => true
  | w :: ws => isClosed w && allClosed ws

theorem hnRank_spine_bound : ∀ (ws : List Term) (f : Term),
    allClosed ws = true → evalHN (appList f ws) ≠ .h34 →
    countCompound ws ≤ hnRank (evalHN f) ∧ evalHN f ≠ .h34
  | [], f, _, hne => ⟨Nat.zero_le _, hne⟩
  | w :: rest, f, hcl_ws, hne => by
    rcases hnRank_spine_bound rest (f ⋅ w) (and_right hcl_ws) hne with ⟨hcnt_rest, hfw_ne⟩
    have hf_ne : evalHN f ≠ .h34 := by
      intro hf34
      have hbad : evalHN (f ⋅ w) = .h34 := by simp [evalHN, hf34, deltaHN_inf_left]
      exact hfw_ne hbad
    if hws : w = S then
      subst hws
      rcases hnRank_step_zero hf_ne with h34 | hle
      · exact False.elim (hfw_ne h34)
      · refine ⟨?_, hf_ne⟩
        simpa [countCompound] using Nat.le_trans hcnt_rest hle
    else
      have hcl_w : isClosed w = true := and_left hcl_ws
      have hy_ne : evalHN w ≠ .h0 := fun h0 => hws ((evalHN_eq_h0_iff_s w hcl_w).mp h0)
      rcases hnRank_step_nonzero hf_ne hy_ne with h34 | hlt
      · exact False.elim (hfw_ne h34)
      · refine ⟨?_, hf_ne⟩
        have hbeq : (w == S) = false := beq_false_of_ne hws
        simp [countCompound, hbeq]
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hcnt_rest hlt)

/-- **Theorem 4.2 (Sharp 5-Compound-Argument `INF_HEAD` Spine Horizon Theorem):** -/
theorem hn_spine_horizon_five (f : Term) (ws : List Term)
    (hcl : allClosed ws = true) (hge5 : 5 ≤ countCompound ws) :
    evalHN (appList f ws) = .h34 := by
  if h34 : evalHN (appList f ws) = .h34 then
    exact h34
  else
    rcases hnRank_spine_bound ws f hcl h34 with ⟨hcnt, hf_ne⟩
    have hle4 := Nat.le_trans hcnt (hnRank_le_four hf_ne)
    have hbad := Nat.lt_of_lt_of_le (by decide : 4 < 5) (Nat.le_trans hge5 hle4)
    exact False.elim (Nat.lt_irrefl 4 hbad)

theorem hn_spine_horizon_five_sharp :
    evalHN (appList S [T_comb, T_comb, T_comb, T_comb]) = .h23 ∧
    evalHN (appList S [T_comb, T_comb, T_comb, T_comb, T_comb]) = .h34 := by
  decide


/-! ## Section 5. `A_SN`, `->_{ro}` Trap, Gate Impossibility, and Complete Proof of Conjecture 2.2 -/

inductive StateSN where
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11 | s12 | s13 | s14 | s15 | s16 | s17 | s18 | s19 | s20 | s21 | s22 | s23 | s24 | s25 | s26 | s27 | s28 | s29 | s30 | s31 | s32 | s33 | s34 | s35 | s36 | s37 | s38

private def deltaSN_0 : StateSN → StateSN | .s0 => .s1 | .s1 => .s2 | .s2 => .s3 | .s3 => .s4 | .s4 => .s5 | .s5 => .s6 | .s6 => .s6 | .s7 => .s8 | .s8 => .s5 | .s9 => .s10 | .s10 => .s5 | .s11 => .s12 | .s12 => .s5 | .s13 => .s4 | .s14 => .s5 | .s15 => .s10 | .s16 => .s5 | .s17 => .s5 | .s18 => .s5 | .s19 => .s20 | .s20 => .s6 | .s21 => .s6 | .s22 => .s6 | .s23 => .s6 | .s24 => .s6 | .s25 => .s6 | .s26 => .s6 | .s27 => .s6 | .s28 => .s6 | .s29 => .s6 | .s30 => .s6 | .s31 => .s6 | .s32 => .s21 | .s33 => .s6 | .s34 => .s6 | .s35 => .s6 | .s36 => .s21 | .s37 => .s6 | .s38 => .s38
private def deltaSN_1 : StateSN → StateSN | .s0 => .s7 | .s1 => .s9 | .s2 => .s11 | .s3 => .s13 | .s4 => .s14 | .s5 => .s5 | .s6 => .s6 | .s7 => .s15 | .s8 => .s16 | .s9 => .s15 | .s10 => .s17 | .s11 => .s11 | .s12 => .s18 | .s13 => .s13 | .s14 => .s14 | .s15 => .s15 | .s16 => .s16 | .s17 => .s17 | .s18 => .s18 | .s19 => .s19 | .s20 => .s21 | .s21 => .s21 | .s22 => .s23 | .s23 => .s23 | .s24 => .s24 | .s25 => .s25 | .s26 => .s26 | .s27 => .s27 | .s28 => .s28 | .s29 => .s29 | .s30 => .s30 | .s31 => .s31 | .s32 => .s32 | .s33 => .s33 | .s34 => .s34 | .s35 => .s35 | .s36 => .s36 | .s37 => .s37 | .s38 => .s38
private def deltaSN_2 : StateSN → StateSN | .s0 => .s19 | .s1 => .s22 | .s2 => .s24 | .s3 => .s25 | .s4 => .s25 | .s5 => .s25 | .s6 => .s25 | .s7 => .s26 | .s8 => .s25 | .s9 => .s26 | .s10 => .s25 | .s11 => .s25 | .s12 => .s25 | .s13 => .s25 | .s14 => .s25 | .s15 => .s26 | .s16 => .s25 | .s17 => .s25 | .s18 => .s25 | .s19 => .s25 | .s20 => .s25 | .s21 => .s25 | .s22 => .s25 | .s23 => .s25 | .s24 => .s25 | .s25 => .s25 | .s26 => .s25 | .s27 => .s25 | .s28 => .s25 | .s29 => .s29 | .s30 => .s30 | .s31 => .s31 | .s32 => .s31 | .s33 => .s31 | .s34 => .s29 | .s35 => .s29 | .s36 => .s31 | .s37 => .s31 | .s38 => .s38
private def deltaSN_3 : StateSN → StateSN | .s0 => .s27 | .s1 => .s28 | .s2 => .s29 | .s3 => .s29 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s29 | .s12 => .s30 | .s13 => .s29 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s29 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s29 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s29 | .s37 => .s30 | .s38 => .s38
private def deltaSN_4 : StateSN → StateSN | .s0 => .s31 | .s1 => .s31 | .s2 => .s29 | .s3 => .s29 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s29 | .s12 => .s30 | .s13 => .s29 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s29 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s29 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s29 | .s37 => .s30 | .s38 => .s38
private def deltaSN_5 : StateSN → StateSN | .s0 => .s29 | .s1 => .s30 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s30 | .s8 => .s30 | .s9 => .s30 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s30 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_6 : StateSN → StateSN | .s0 => .s30 | .s1 => .s30 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s30 | .s8 => .s30 | .s9 => .s30 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s30 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_7 : StateSN → StateSN | .s0 => .s9 | .s1 => .s24 | .s2 => .s29 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_8 : StateSN → StateSN | .s0 => .s32 | .s1 => .s33 | .s2 => .s29 | .s3 => .s29 | .s4 => .s29 | .s5 => .s29 | .s6 => .s29 | .s7 => .s34 | .s8 => .s29 | .s9 => .s34 | .s10 => .s29 | .s11 => .s29 | .s12 => .s29 | .s13 => .s29 | .s14 => .s29 | .s15 => .s34 | .s16 => .s29 | .s17 => .s29 | .s18 => .s29 | .s19 => .s29 | .s20 => .s29 | .s21 => .s29 | .s22 => .s29 | .s23 => .s29 | .s24 => .s29 | .s25 => .s29 | .s26 => .s29 | .s27 => .s29 | .s28 => .s29 | .s29 => .s29 | .s30 => .s30 | .s31 => .s29 | .s32 => .s29 | .s33 => .s29 | .s34 => .s29 | .s35 => .s29 | .s36 => .s29 | .s37 => .s29 | .s38 => .s38
private def deltaSN_9 : StateSN → StateSN | .s0 => .s15 | .s1 => .s26 | .s2 => .s29 | .s3 => .s29 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s34 | .s8 => .s30 | .s9 => .s35 | .s10 => .s30 | .s11 => .s29 | .s12 => .s30 | .s13 => .s29 | .s14 => .s30 | .s15 => .s35 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_10 : StateSN → StateSN | .s0 => .s36 | .s1 => .s37 | .s2 => .s29 | .s3 => .s29 | .s4 => .s29 | .s5 => .s29 | .s6 => .s29 | .s7 => .s35 | .s8 => .s29 | .s9 => .s35 | .s10 => .s29 | .s11 => .s29 | .s12 => .s29 | .s13 => .s29 | .s14 => .s29 | .s15 => .s35 | .s16 => .s29 | .s17 => .s29 | .s18 => .s29 | .s19 => .s29 | .s20 => .s29 | .s21 => .s29 | .s22 => .s29 | .s23 => .s29 | .s24 => .s29 | .s25 => .s29 | .s26 => .s29 | .s27 => .s29 | .s28 => .s29 | .s29 => .s29 | .s30 => .s30 | .s31 => .s29 | .s32 => .s29 | .s33 => .s29 | .s34 => .s29 | .s35 => .s29 | .s36 => .s29 | .s37 => .s29 | .s38 => .s38
private def deltaSN_11 : StateSN → StateSN | .s0 => .s19 | .s1 => .s25 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_12 : StateSN → StateSN | .s0 => .s37 | .s1 => .s31 | .s2 => .s29 | .s3 => .s29 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s29 | .s12 => .s30 | .s13 => .s29 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s29 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s29 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s29 | .s37 => .s30 | .s38 => .s38
private def deltaSN_13 : StateSN → StateSN | .s0 => .s27 | .s1 => .s25 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_14 : StateSN → StateSN | .s0 => .s31 | .s1 => .s31 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_15 : StateSN → StateSN | .s0 => .s15 | .s1 => .s25 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_16 : StateSN → StateSN | .s0 => .s32 | .s1 => .s31 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_17 : StateSN → StateSN | .s0 => .s36 | .s1 => .s31 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_18 : StateSN → StateSN | .s0 => .s37 | .s1 => .s31 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_19 : StateSN → StateSN | .s0 => .s24 | .s1 => .s29 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s30 | .s8 => .s30 | .s9 => .s30 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s30 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_20 : StateSN → StateSN | .s0 => .s29 | .s1 => .s29 | .s2 => .s29 | .s3 => .s29 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s29 | .s12 => .s30 | .s13 => .s29 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_21 : StateSN → StateSN | .s0 => .s29 | .s1 => .s29 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s30 | .s30 => .s30 | .s31 => .s30 | .s32 => .s30 | .s33 => .s30 | .s34 => .s30 | .s35 => .s30 | .s36 => .s30 | .s37 => .s30 | .s38 => .s38
private def deltaSN_22 : StateSN → StateSN | .s0 => .s29 | .s1 => .s35 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s30 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_23 : StateSN → StateSN | .s0 => .s29 | .s1 => .s29 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s29 | .s8 => .s30 | .s9 => .s29 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s29 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s30 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_24 : StateSN → StateSN | .s0 => .s30 | .s1 => .s30 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s30 | .s8 => .s30 | .s9 => .s30 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s30 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s30 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_25 : StateSN → StateSN | .s0 => .s30 | .s1 => .s30 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s30 | .s8 => .s30 | .s9 => .s30 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s30 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s38 | .s20 => .s30 | .s21 => .s30 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_26 : StateSN → StateSN | .s0 => .s29 | .s1 => .s30 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s30 | .s8 => .s30 | .s9 => .s30 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s30 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s38 | .s20 => .s30 | .s21 => .s30 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_27 : StateSN → StateSN | .s0 => .s29 | .s1 => .s30 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s30 | .s8 => .s30 | .s9 => .s30 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s30 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s30 | .s20 => .s30 | .s21 => .s30 | .s22 => .s30 | .s23 => .s30 | .s24 => .s30 | .s25 => .s30 | .s26 => .s30 | .s27 => .s30 | .s28 => .s30 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_28 : StateSN → StateSN | .s0 => .s30 | .s1 => .s29 | .s2 => .s30 | .s3 => .s30 | .s4 => .s30 | .s5 => .s30 | .s6 => .s30 | .s7 => .s30 | .s8 => .s30 | .s9 => .s30 | .s10 => .s30 | .s11 => .s30 | .s12 => .s30 | .s13 => .s30 | .s14 => .s30 | .s15 => .s30 | .s16 => .s30 | .s17 => .s30 | .s18 => .s30 | .s19 => .s38 | .s20 => .s30 | .s21 => .s30 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_29 : StateSN → StateSN | .s0 => .s30 | .s1 => .s38 | .s2 => .s38 | .s3 => .s38 | .s4 => .s38 | .s5 => .s38 | .s6 => .s38 | .s7 => .s38 | .s8 => .s38 | .s9 => .s38 | .s10 => .s38 | .s11 => .s38 | .s12 => .s38 | .s13 => .s38 | .s14 => .s38 | .s15 => .s38 | .s16 => .s38 | .s17 => .s38 | .s18 => .s38 | .s19 => .s38 | .s20 => .s38 | .s21 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_30 (_ : StateSN) : StateSN := .s38
private def deltaSN_31 : StateSN → StateSN | .s0 => .s30 | .s1 => .s30 | .s2 => .s38 | .s3 => .s38 | .s4 => .s38 | .s5 => .s38 | .s6 => .s38 | .s7 => .s38 | .s8 => .s38 | .s9 => .s38 | .s10 => .s38 | .s11 => .s38 | .s12 => .s38 | .s13 => .s38 | .s14 => .s38 | .s15 => .s38 | .s16 => .s38 | .s17 => .s38 | .s18 => .s38 | .s19 => .s38 | .s20 => .s38 | .s21 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_32 : StateSN → StateSN | .s0 => .s26 | .s1 => .s30 | .s2 => .s38 | .s3 => .s38 | .s4 => .s38 | .s5 => .s38 | .s6 => .s38 | .s7 => .s38 | .s8 => .s38 | .s9 => .s38 | .s10 => .s38 | .s11 => .s38 | .s12 => .s38 | .s13 => .s38 | .s14 => .s38 | .s15 => .s38 | .s16 => .s38 | .s17 => .s38 | .s18 => .s38 | .s19 => .s38 | .s20 => .s38 | .s21 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_33 : StateSN → StateSN | .s0 => .s34 | .s1 => .s30 | .s2 => .s38 | .s3 => .s38 | .s4 => .s38 | .s5 => .s38 | .s6 => .s38 | .s7 => .s38 | .s8 => .s38 | .s9 => .s38 | .s10 => .s38 | .s11 => .s38 | .s12 => .s38 | .s13 => .s38 | .s14 => .s38 | .s15 => .s38 | .s16 => .s38 | .s17 => .s38 | .s18 => .s38 | .s19 => .s38 | .s20 => .s38 | .s21 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_34 : StateSN → StateSN | .s0 => .s35 | .s1 => .s38 | .s2 => .s38 | .s3 => .s38 | .s4 => .s38 | .s5 => .s38 | .s6 => .s38 | .s7 => .s38 | .s8 => .s38 | .s9 => .s38 | .s10 => .s38 | .s11 => .s38 | .s12 => .s38 | .s13 => .s38 | .s14 => .s38 | .s15 => .s38 | .s16 => .s38 | .s17 => .s38 | .s18 => .s38 | .s19 => .s38 | .s20 => .s38 | .s21 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_35 : StateSN → StateSN | .s0 => .s29 | .s1 => .s38 | .s2 => .s38 | .s3 => .s38 | .s4 => .s38 | .s5 => .s38 | .s6 => .s38 | .s7 => .s38 | .s8 => .s38 | .s9 => .s38 | .s10 => .s38 | .s11 => .s38 | .s12 => .s38 | .s13 => .s38 | .s14 => .s38 | .s15 => .s38 | .s16 => .s38 | .s17 => .s38 | .s18 => .s38 | .s19 => .s38 | .s20 => .s38 | .s21 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_36 : StateSN → StateSN | .s0 => .s25 | .s1 => .s30 | .s2 => .s38 | .s3 => .s38 | .s4 => .s38 | .s5 => .s38 | .s6 => .s38 | .s7 => .s38 | .s8 => .s38 | .s9 => .s38 | .s10 => .s38 | .s11 => .s38 | .s12 => .s38 | .s13 => .s38 | .s14 => .s38 | .s15 => .s38 | .s16 => .s38 | .s17 => .s38 | .s18 => .s38 | .s19 => .s38 | .s20 => .s38 | .s21 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_37 : StateSN → StateSN | .s0 => .s29 | .s1 => .s30 | .s2 => .s38 | .s3 => .s38 | .s4 => .s38 | .s5 => .s38 | .s6 => .s38 | .s7 => .s38 | .s8 => .s38 | .s9 => .s38 | .s10 => .s38 | .s11 => .s38 | .s12 => .s38 | .s13 => .s38 | .s14 => .s38 | .s15 => .s38 | .s16 => .s38 | .s17 => .s38 | .s18 => .s38 | .s19 => .s38 | .s20 => .s38 | .s21 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38
private def deltaSN_38 (_ : StateSN) : StateSN := .s38
def deltaSN : StateSN → StateSN → StateSN | .s0 => deltaSN_0 | .s1 => deltaSN_1 | .s2 => deltaSN_2 | .s3 => deltaSN_3 | .s4 => deltaSN_4 | .s5 => deltaSN_5 | .s6 => deltaSN_6 | .s7 => deltaSN_7 | .s8 => deltaSN_8 | .s9 => deltaSN_9 | .s10 => deltaSN_10 | .s11 => deltaSN_11 | .s12 => deltaSN_12 | .s13 => deltaSN_13 | .s14 => deltaSN_14 | .s15 => deltaSN_15 | .s16 => deltaSN_16 | .s17 => deltaSN_17 | .s18 => deltaSN_18 | .s19 => deltaSN_19 | .s20 => deltaSN_20 | .s21 => deltaSN_21 | .s22 => deltaSN_22 | .s23 => deltaSN_23 | .s24 => deltaSN_24 | .s25 => deltaSN_25 | .s26 => deltaSN_26 | .s27 => deltaSN_27 | .s28 => deltaSN_28 | .s29 => deltaSN_29 | .s30 => deltaSN_30 | .s31 => deltaSN_31 | .s32 => deltaSN_32 | .s33 => deltaSN_33 | .s34 => deltaSN_34 | .s35 => deltaSN_35 | .s36 => deltaSN_36 | .s37 => deltaSN_37 | .s38 => deltaSN_38

def idx_StateSN : StateSN → Nat
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4 | .s5 => 5 | .s6 => 6 | .s7 => 7 | .s8 => 8 | .s9 => 9 | .s10 => 10 | .s11 => 11 | .s12 => 12 | .s13 => 13 | .s14 => 14 | .s15 => 15 | .s16 => 16 | .s17 => 17 | .s18 => 18 | .s19 => 19 | .s20 => 20 | .s21 => 21 | .s22 => 22 | .s23 => 23 | .s24 => 24 | .s25 => 25 | .s26 => 26 | .s27 => 27 | .s28 => 28 | .s29 => 29 | .s30 => 30 | .s31 => 31 | .s32 => 32 | .s33 => 33 | .s34 => 34 | .s35 => 35 | .s36 => 36 | .s37 => 37 | .s38 => 38

def ofIdx_StateSN : Nat → StateSN
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | 3 => .s3 | 4 => .s4 | 5 => .s5 | 6 => .s6 | 7 => .s7 | 8 => .s8 | 9 => .s9 | 10 => .s10 | 11 => .s11 | 12 => .s12 | 13 => .s13 | 14 => .s14 | 15 => .s15 | 16 => .s16 | 17 => .s17 | 18 => .s18 | 19 => .s19 | 20 => .s20 | 21 => .s21 | 22 => .s22 | 23 => .s23 | 24 => .s24 | 25 => .s25 | 26 => .s26 | 27 => .s27 | 28 => .s28 | 29 => .s29 | 30 => .s30 | 31 => .s31 | 32 => .s32 | 33 => .s33 | 34 => .s34 | 35 => .s35 | 36 => .s36 | 37 => .s37 | _ => .s38

theorem ofIdx_idx_StateSN (a : StateSN) : ofIdx_StateSN (idx_StateSN a) = a := by
  cases a <;> rfl

def eq_StateSN (a b : StateSN) : Bool :=
  Nat.beq (idx_StateSN a) (idx_StateSN b)

theorem eq_StateSN_iff (a b : StateSN) : eq_StateSN a b = true ↔ a = b := by
  unfold eq_StateSN
  constructor
  · intro h
    have hidx : idx_StateSN a = idx_StateSN b := Nat.eq_of_beq_eq_true h
    have hcongr := congrArg ofIdx_StateSN hidx
    rw [ofIdx_idx_StateSN a, ofIdx_idx_StateSN b] at hcongr
    exact hcongr
  · intro h
    subst h
    exact Nat.beq_refl _

theorem eq_StateSN_false_of_ne {a b : StateSN} (h : a ≠ b) : eq_StateSN a b = false := by
  cases heq : eq_StateSN a b with
  | false => rfl
  | true => exact False.elim (h ((eq_StateSN_iff a b).mp heq))

instance : DecidableEq StateSN := fun a b =>
  if h : eq_StateSN a b = true then
    isTrue ((eq_StateSN_iff a b).mp h)
  else
    isFalse (fun hab => h ((eq_StateSN_iff a b).mpr hab))

def checkAll1_StateSN (p : StateSN → Bool) : Bool :=
  (((((p .s0 && p .s1) && (p .s2 && p .s3)) && ((p .s4 && p .s5) && (p .s6 && (p .s7 && p .s8)))) && (((p .s9 && p .s10) && (p .s11 && (p .s12 && p .s13))) && ((p .s14 && p .s15) && (p .s16 && (p .s17 && p .s18))))) && ((((p .s19 && p .s20) && (p .s21 && (p .s22 && p .s23))) && ((p .s24 && p .s25) && (p .s26 && (p .s27 && p .s28)))) && (((p .s29 && p .s30) && (p .s31 && (p .s32 && p .s33))) && ((p .s34 && p .s35) && (p .s36 && (p .s37 && p .s38))))))

theorem checkAll1_StateSN_sound (p : StateSN → Bool)
    (h : checkAll1_StateSN p = true) (x : StateSN) : p x = true :=
  match x with
  | .s0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .s1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .s2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .s3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .s4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .s5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .s6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .s7 => (and_left (and_right (and_right (and_right (and_left (and_left h))))))
  | .s8 => (and_right (and_right (and_right (and_right (and_left (and_left h))))))
  | .s9 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .s10 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .s11 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .s12 => (and_left (and_right (and_right (and_left (and_right (and_left h))))))
  | .s13 => (and_right (and_right (and_right (and_left (and_right (and_left h))))))
  | .s14 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .s15 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .s16 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .s17 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .s18 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .s19 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .s20 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .s21 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .s22 => (and_left (and_right (and_right (and_left (and_left (and_right h))))))
  | .s23 => (and_right (and_right (and_right (and_left (and_left (and_right h))))))
  | .s24 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .s25 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .s26 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .s27 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .s28 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .s29 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .s30 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .s31 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .s32 => (and_left (and_right (and_right (and_left (and_right (and_right h))))))
  | .s33 => (and_right (and_right (and_right (and_left (and_right (and_right h))))))
  | .s34 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .s35 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .s36 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .s37 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .s38 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateSN (p : StateSN → StateSN → Bool) : Bool :=
  checkAll1_StateSN (fun x => checkAll1_StateSN (fun y => p x y))

theorem checkAll2_StateSN_sound (p : StateSN → StateSN → Bool)
    (h : checkAll2_StateSN p = true) (x y : StateSN) : p x y = true :=
  checkAll1_StateSN_sound _ (checkAll1_StateSN_sound _ h x) y

private theorem s_row_StateSN_0 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s0) y) z) (deltaSN (deltaSN .s0 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_1 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s1) y) z) (deltaSN (deltaSN .s1 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_2 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s2) y) z) (deltaSN (deltaSN .s2 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_3 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s3) y) z) (deltaSN (deltaSN .s3 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_4 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s4) y) z) (deltaSN (deltaSN .s4 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_5 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s5) y) z) (deltaSN (deltaSN .s5 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_6 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s6) y) z) (deltaSN (deltaSN .s6 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_7 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s7) y) z) (deltaSN (deltaSN .s7 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_8 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s8) y) z) (deltaSN (deltaSN .s8 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_9 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s9) y) z) (deltaSN (deltaSN .s9 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_10 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s10) y) z) (deltaSN (deltaSN .s10 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_11 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s11) y) z) (deltaSN (deltaSN .s11 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_12 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s12) y) z) (deltaSN (deltaSN .s12 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_13 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s13) y) z) (deltaSN (deltaSN .s13 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_14 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s14) y) z) (deltaSN (deltaSN .s14 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_15 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s15) y) z) (deltaSN (deltaSN .s15 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_16 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s16) y) z) (deltaSN (deltaSN .s16 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_17 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s17) y) z) (deltaSN (deltaSN .s17 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_18 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s18) y) z) (deltaSN (deltaSN .s18 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_19 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s19) y) z) (deltaSN (deltaSN .s19 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_20 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s20) y) z) (deltaSN (deltaSN .s20 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_21 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s21) y) z) (deltaSN (deltaSN .s21 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_22 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s22) y) z) (deltaSN (deltaSN .s22 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_23 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s23) y) z) (deltaSN (deltaSN .s23 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_24 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s24) y) z) (deltaSN (deltaSN .s24 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_25 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s25) y) z) (deltaSN (deltaSN .s25 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_26 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s26) y) z) (deltaSN (deltaSN .s26 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_27 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s27) y) z) (deltaSN (deltaSN .s27 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_28 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s28) y) z) (deltaSN (deltaSN .s28 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_29 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s29) y) z) (deltaSN (deltaSN .s29 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_30 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s30) y) z) (deltaSN (deltaSN .s30 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_31 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s31) y) z) (deltaSN (deltaSN .s31 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_32 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s32) y) z) (deltaSN (deltaSN .s32 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_33 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s33) y) z) (deltaSN (deltaSN .s33 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_34 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s34) y) z) (deltaSN (deltaSN .s34 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_35 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s35) y) z) (deltaSN (deltaSN .s35 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_36 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s36) y) z) (deltaSN (deltaSN .s36 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_37 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s37) y) z) (deltaSN (deltaSN .s37 z) (deltaSN y z))) = true := rfl
private theorem s_row_StateSN_38 : checkAll2_StateSN (fun y z => eq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s38) y) z) (deltaSN (deltaSN .s38 z) (deltaSN y z))) = true := rfl

theorem deltaSN_s_law (x y z : StateSN) :
    deltaSN (deltaSN (deltaSN .s0 x) y) z =
    deltaSN (deltaSN x z) (deltaSN y z) :=
  match x with
  | .s0 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_0 y z)
  | .s1 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_1 y z)
  | .s2 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_2 y z)
  | .s3 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_3 y z)
  | .s4 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_4 y z)
  | .s5 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_5 y z)
  | .s6 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_6 y z)
  | .s7 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_7 y z)
  | .s8 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_8 y z)
  | .s9 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_9 y z)
  | .s10 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_10 y z)
  | .s11 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_11 y z)
  | .s12 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_12 y z)
  | .s13 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_13 y z)
  | .s14 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_14 y z)
  | .s15 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_15 y z)
  | .s16 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_16 y z)
  | .s17 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_17 y z)
  | .s18 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_18 y z)
  | .s19 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_19 y z)
  | .s20 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_20 y z)
  | .s21 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_21 y z)
  | .s22 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_22 y z)
  | .s23 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_23 y z)
  | .s24 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_24 y z)
  | .s25 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_25 y z)
  | .s26 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_26 y z)
  | .s27 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_27 y z)
  | .s28 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_28 y z)
  | .s29 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_29 y z)
  | .s30 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_30 y z)
  | .s31 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_31 y z)
  | .s32 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_32 y z)
  | .s33 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_33 y z)
  | .s34 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_34 y z)
  | .s35 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_35 y z)
  | .s36 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_36 y z)
  | .s37 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_37 y z)
  | .s38 => (eq_StateSN_iff _ _).mp (checkAll2_StateSN_sound _ s_row_StateSN_38 y z)


def evalSN : Term → StateSN
  | .s => .s0
  | .var _ => .s0
  | .app a b => deltaSN (evalSN a) (evalSN b)

theorem evalSN_step_invariant {a b : Term} (h : Step a b) : evalSN a = evalSN b := by
  induction h with
  | root x y z => exact deltaSN_s_law (evalSN x) (evalSN y) (evalSN z)
  | left _ ih => simp [evalSN, ih]
  | right _ ih => simp [evalSN, ih]

theorem evalSN_reduces_invariant {a b : Term} (h : Reduces a b) : evalSN a = evalSN b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalSN_step_invariant hs).trans ih

theorem deltaSN_nf_lt38_bool :
    (decide (StateSN.s0 ≠ .s38) &&
     checkAll1_StateSN (fun a => decide (a = .s38 ∨ deltaSN .s0 a ≠ .s38)) &&
     checkAll2_StateSN (fun x y => decide (x = .s38 ∨ y = .s38 ∨ deltaSN (deltaSN .s0 x) y ≠ .s38))) = true := rfl

theorem deltaSN_nf1_lt38 {a : StateSN} (ha : a ≠ .s38) : deltaSN .s0 a ≠ .s38 := by
  have h := of_decide_eq_true (checkAll1_StateSN_sound _ (and_right (and_left deltaSN_nf_lt38_bool)) a)
  rcases h with rfl | hok
  · exact False.elim (ha rfl)
  · exact hok

theorem deltaSN_nf2_lt38 {x y : StateSN} (hx : x ≠ .s38) (hy : y ≠ .s38) :
    deltaSN (deltaSN .s0 x) y ≠ .s38 := by
  have h := of_decide_eq_true (checkAll2_StateSN_sound _ (and_right deltaSN_nf_lt38_bool) x y)
  rcases h with rfl | rfl | hok
  · exact False.elim (hx rfl)
  · exact False.elim (hy rfl)
  · exact hok

def isNF : Term → Bool
  | .s => true
  | .var _ => false
  | .app .s a => isNF a
  | .app (.var _) _ => false
  | .app (.app .s x) y => isNF x && isNF y
  | .app (.app (.var _) _) _ => false
  | .app (.app (.app _ _) _) _ => false

def isNF2 : Term → Bool
  | .app (.app .s x) y => isNF x && isNF y
  | _ => false

theorem isNF2_implies_isNF (t : Term) (h : isNF2 t = true) : isNF t = true := by
  cases t with
  | s => cases h | var _ => cases h
  | app l _ => cases l with
    | s => cases h | var _ => cases h
    | app l1 _ => cases l1 with
      | s => exact h | var _ => cases h | app _ _ => cases h

theorem isNF_closed : ∀ (t : Term), isNF t = true → isClosed t = true
  | .s, _ => rfl
  | .var _, h => by cases h
  | .app .s a, h => isNF_closed a h
  | .app (.var _) _, h => by cases h
  | .app (.app .s x) y, h =>
    Bool.and_eq_true _ _ |>.mpr ⟨isNF_closed x (and_left h), isNF_closed y (and_right h)⟩
  | .app (.app (.var _) _) _, h => by cases h
  | .app (.app (.app _ _) _) _, h => by cases h

theorem isNF_evalSN_ne_inf : ∀ (t : Term), isNF t = true → evalSN t ≠ .s38
  | .s, _ => by decide
  | .var _, h => by cases h
  | .app .s a, h => deltaSN_nf1_lt38 (isNF_evalSN_ne_inf a h)
  | .app (.var _) _, h => by cases h
  | .app (.app .s x) y, h =>
    deltaSN_nf2_lt38 (isNF_evalSN_ne_inf x (and_left h)) (isNF_evalSN_ne_inf y (and_right h))
  | .app (.app (.var _) _) _, h => by cases h
  | .app (.app (.app _ _) _) _, h => by cases h

/-- ### Attack Line 3 Barrier A: Rightmost-Outermost (`->_{ro}`) Non-SN Right-Child Trap Theorem -/

theorem stepRO_sound : ∀ (a b : Term), stepRO a = some b → Step a b
  | .s, _, h => by cases h
  | .var _, _, h => by cases h
  | .app l r, b, h => by
    cases hrr : isRootRedex (l ⋅ r) with
    | true =>
      cases l with
      | s => cases hrr | var _ => cases hrr
      | app l1 y => cases l1 with
        | s => cases hrr | var _ => cases hrr
        | app l11 x => cases l11 with
          | s => simp [stepRO] at h; subst h; exact Step.root x y r
          | var _ => cases hrr | app _ _ => cases hrr
    | false =>
      rw [stepRO_not_root hrr] at h
      cases hr : stepRO r with
      | some r' =>
        rw [hr] at h; injection h with hb; subst hb
        exact Step.right (stepRO_sound r r' hr)
      | none =>
        rw [hr] at h
        cases hl : stepRO l with
        | none => rw [hl] at h; cases h
        | some l' =>
          rw [hl] at h; injection h with hb; subst hb
          exact Step.left (stepRO_sound l l' hl)

theorem isNF_of_stepRO_none : ∀ (t : Term), isClosed t = true → stepRO t = none → isNF t = true
  | .s, _, _ => rfl
  | .var _, hcl, _ => by cases hcl
  | .app l r, hcl, hro => by
    cases hrr : isRootRedex (l ⋅ r) with
    | true =>
      cases l with
      | s => cases hrr | var _ => cases hrr
      | app l1 _ => cases l1 with
        | s => cases hrr | var _ => cases hrr
        | app l11 _ => cases l11 with
          | s => cases hro | var _ => cases hrr | app _ _ => cases hrr
    | false =>
      rw [stepRO_not_root hrr] at hro
      cases hr : stepRO r with
      | some _ => rw [hr] at hro; cases hro
      | none =>
        rw [hr] at hro
        cases hl : stepRO l with
        | some _ => rw [hl] at hro; cases hro
        | none =>
          have hnf_l := isNF_of_stepRO_none l (and_left hcl) hl
          have hnf_r := isNF_of_stepRO_none r (and_right hcl) hr
          cases l with
          | s => exact hnf_r
          | var _ => cases hnf_l
          | app l1 y => cases l1 with
            | s => exact Bool.and_eq_true _ _ |>.mpr ⟨hnf_l, hnf_r⟩
            | var _ => cases hnf_l
            | app l11 _ => cases l11 with
              | s => cases hrr
              | var _ => cases hnf_l
              | app _ _ => cases hnf_l

theorem non_sn_has_stepRO (r : Term) (hcl : isClosed r = true) (hsn : evalSN r = .s38) :
    ∃ r', stepRO r = some r' ∧ isClosed r' = true ∧ evalSN r' = .s38 := by
  cases hr : stepRO r with
  | none => exfalso; exact isNF_evalSN_ne_inf r (isNF_of_stepRO_none r hcl hr) hsn
  | some r' =>
    have hs := stepRO_sound r r' hr
    refine ⟨r', rfl, step_preserves_closed hs hcl, ?_⟩
    rw [← evalSN_step_invariant hs]; exact hsn

/-- **Theorem 5.1 (Rightmost-Outermost Non-SN Right-Child Trap Theorem):** -/
theorem ro_right_non_sn_trap : ∀ (t : Nat) (l r : Term),
    isRootRedex (l ⋅ r) = false → isClosed r = true → evalSN r = .s38 →
    ∃ r_t, iterOpt stepRO t (l ⋅ r) = some (l ⋅ r_t) ∧ isClosed r_t = true ∧ evalSN r_t = .s38
  | 0, _, r, _, hcl, hsn => ⟨r, rfl, hcl, hsn⟩
  | t + 1, l, r, hnr, hcl, hsn => by
    rcases non_sn_has_stepRO r hcl hsn with ⟨r', hr', hcl', hsn'⟩
    have hstep_lr : stepRO (l ⋅ r) = some (l ⋅ r') := by rw [stepRO_not_root hnr, hr']
    have hnr' : isRootRedex (l ⋅ r') = false := by
      cases l with
      | s => rfl | var _ => rfl
      | app l1 _ => cases l1 with
        | s => rfl | var _ => rfl
        | app l11 _ => cases l11 with
          | s => cases hnr | var _ => rfl | app _ _ => rfl
    rcases ro_right_non_sn_trap t l r' hnr' hcl' hsn' with ⟨r_t, hrt, hcl_t, hsn_t⟩
    exact ⟨r_t, by simp [iterOpt, hstep_lr, hrt], hcl_t, hsn_t⟩

theorem deltaSN_no_direct_nand_or_xor_bool :
    checkAll2_StateSN (fun b0 b1 =>
      decide (b0 = b1 ∨
        (¬(deltaSN b0 b0 = b1 ∧ deltaSN b0 b1 = b1 ∧ deltaSN b1 b0 = b1 ∧ deltaSN b1 b1 = b0) ∧
         ¬(deltaSN b0 b0 = b0 ∧ deltaSN b0 b1 = b1 ∧ deltaSN b1 b0 = b1 ∧ deltaSN b1 b1 = b0)))) = true := rfl

theorem deltaSN_no_direct_nand_or_xor {b0 b1 : StateSN} (hne : b0 ≠ b1) :
    ¬(deltaSN b0 b0 = b1 ∧ deltaSN b0 b1 = b1 ∧ deltaSN b1 b0 = b1 ∧ deltaSN b1 b1 = b0) ∧
    ¬(deltaSN b0 b0 = b0 ∧ deltaSN b0 b1 = b1 ∧ deltaSN b1 b0 = b1 ∧ deltaSN b1 b1 = b0) := by
  have h := of_decide_eq_true (checkAll2_StateSN_sound _ deltaSN_no_direct_nand_or_xor_bool b0 b1)
  rcases h with rfl | hok
  · exact False.elim (hne rfl)
  · exact hok

/-! ### Complete Proof of Conjecture 2.2: Sharp 5-Step Consecutive Case-3 Ceiling (`->_{li}` & `->_{ri}`) -/

inductive Arity3 where
  | a0 | a1 | a2
  deriving DecidableEq, Repr

inductive ChildTag where
  | c0 | c1 | c2 | c3 | c4
  deriving DecidableEq, Repr

def tagOfSN : StateSN → ChildTag
  | .s0 => .c0 | .s1 => .c0 | .s2 => .c1 | .s3 => .c1 | .s4 => .c0 | .s5 => .c1 | .s6 => .c1 | .s7 => .c0 | .s8 => .c1 | .s9 => .c2 | .s10 => .c0 | .s11 => .c2 | .s12 => .c0 | .s13 => .c2 | .s14 => .c1 | .s15 => .c2 | .s16 => .c1 | .s17 => .c1 | .s18 => .c1 | .s19 => .c2 | .s20 => .c0 | .s21 => .c1 | .s22 => .c0 | .s23 => .c2 | .s24 => .c2 | .s25 => .c3 | .s26 => .c2 | .s27 => .c2 | .s28 => .c2 | .s29 => .c3 | .s30 => .c4 | .s31 => .c2 | .s32 => .c2 | .s33 => .c2 | .s34 => .c2 | .s35 => .c3 | .s36 => .c2 | .s37 => .c2 | .s38 => .c0

structure NFDesc where
  sl : Arity3
  st : StateSN
  tx : ChildTag
  ty : ChildTag

def nfDescOf : Term → NFDesc
  | .s => ⟨.a0, .s0, .c0, .c0⟩
  | .app .s a =>
    let sa := evalSN a
    ⟨.a1, deltaSN .s0 sa, tagOfSN sa, .c0⟩
  | .app (.app .s x) y =>
    let sx := evalSN x
    let sy := evalSN y
    ⟨.a2, deltaSN (deltaSN .s0 sx) sy, tagOfSN sx, tagOfSN sy⟩
  | _ => ⟨.a0, .s0, .c0, .c0⟩

def listBySt : StateSN → List NFDesc
  | .s0 => [⟨.a0, .s0, .c0, .c0⟩]
  | .s1 => [⟨.a1, .s1, .c0, .c0⟩]
  | .s2 => [⟨.a1, .s2, .c0, .c0⟩]
  | .s3 => [⟨.a1, .s3, .c1, .c0⟩]
  | .s4 => [⟨.a1, .s4, .c1, .c0⟩, ⟨.a1, .s4, .c2, .c0⟩]
  | .s5 => [⟨.a1, .s5, .c0, .c0⟩, ⟨.a1, .s5, .c1, .c0⟩, ⟨.a2, .s5, .c0, .c1⟩]
  | .s6 => [⟨.a1, .s6, .c0, .c0⟩, ⟨.a1, .s6, .c1, .c0⟩, ⟨.a1, .s6, .c2, .c0⟩, ⟨.a1, .s6, .c3, .c0⟩, ⟨.a1, .s6, .c4, .c0⟩, ⟨.a2, .s6, .c0, .c1⟩]
  | .s7 => [⟨.a2, .s7, .c0, .c0⟩]
  | .s8 => [⟨.a1, .s8, .c0, .c0⟩]
  | .s9 => [⟨.a2, .s9, .c0, .c0⟩]
  | .s10 => [⟨.a1, .s10, .c2, .c0⟩]
  | .s11 => [⟨.a2, .s11, .c0, .c1⟩, ⟨.a2, .s11, .c0, .c2⟩]
  | .s12 => [⟨.a1, .s12, .c2, .c0⟩]
  | .s13 => [⟨.a2, .s13, .c0, .c1⟩, ⟨.a2, .s13, .c0, .c2⟩]
  | .s14 => [⟨.a2, .s14, .c0, .c0⟩, ⟨.a2, .s14, .c0, .c1⟩]
  | .s15 => [⟨.a2, .s15, .c0, .c0⟩, ⟨.a2, .s15, .c0, .c2⟩]
  | .s16 => [⟨.a2, .s16, .c0, .c1⟩]
  | .s17 => [⟨.a2, .s17, .c0, .c0⟩, ⟨.a2, .s17, .c0, .c1⟩]
  | .s18 => [⟨.a2, .s18, .c0, .c0⟩, ⟨.a2, .s18, .c0, .c1⟩]
  | .s19 => [⟨.a2, .s19, .c0, .c0⟩, ⟨.a2, .s19, .c0, .c2⟩]
  | .s20 => [⟨.a1, .s20, .c2, .c0⟩]
  | .s21 => [⟨.a1, .s21, .c2, .c0⟩, ⟨.a2, .s21, .c0, .c0⟩, ⟨.a2, .s21, .c0, .c1⟩]
  | .s22 => [⟨.a2, .s22, .c0, .c0⟩]
  | .s23 => [⟨.a2, .s23, .c0, .c0⟩, ⟨.a2, .s23, .c0, .c2⟩]
  | .s24 => [⟨.a2, .s24, .c0, .c1⟩, ⟨.a2, .s24, .c0, .c2⟩]
  | .s25 => [⟨.a2, .s25, .c0, .c0⟩, ⟨.a2, .s25, .c0, .c1⟩, ⟨.a2, .s25, .c0, .c2⟩, ⟨.a2, .s25, .c0, .c3⟩]
  | .s26 => [⟨.a2, .s26, .c0, .c0⟩, ⟨.a2, .s26, .c0, .c2⟩]
  | .s27 => [⟨.a2, .s27, .c0, .c2⟩, ⟨.a2, .s27, .c1, .c0⟩]
  | .s28 => [⟨.a2, .s28, .c0, .c2⟩, ⟨.a2, .s28, .c1, .c0⟩]
  | .s29 => [⟨.a2, .s29, .c0, .c0⟩, ⟨.a2, .s29, .c0, .c1⟩, ⟨.a2, .s29, .c0, .c2⟩, ⟨.a2, .s29, .c0, .c3⟩, ⟨.a2, .s29, .c1, .c0⟩, ⟨.a2, .s29, .c1, .c1⟩, ⟨.a2, .s29, .c1, .c2⟩, ⟨.a2, .s29, .c2, .c0⟩, ⟨.a2, .s29, .c2, .c1⟩, ⟨.a2, .s29, .c2, .c2⟩, ⟨.a2, .s29, .c2, .c3⟩]
  | .s30 => [⟨.a2, .s30, .c0, .c0⟩, ⟨.a2, .s30, .c0, .c1⟩, ⟨.a2, .s30, .c0, .c2⟩, ⟨.a2, .s30, .c0, .c3⟩, ⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c1, .c0⟩, ⟨.a2, .s30, .c1, .c1⟩, ⟨.a2, .s30, .c1, .c2⟩, ⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c2, .c0⟩, ⟨.a2, .s30, .c2, .c1⟩, ⟨.a2, .s30, .c2, .c2⟩, ⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c0⟩, ⟨.a2, .s30, .c3, .c1⟩, ⟨.a2, .s30, .c3, .c2⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c0⟩, ⟨.a2, .s30, .c4, .c1⟩, ⟨.a2, .s30, .c4, .c2⟩, ⟨.a2, .s30, .c4, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩]
  | .s31 => [⟨.a2, .s31, .c0, .c2⟩, ⟨.a2, .s31, .c1, .c0⟩, ⟨.a2, .s31, .c2, .c0⟩]
  | .s32 => [⟨.a2, .s32, .c0, .c0⟩, ⟨.a2, .s32, .c0, .c2⟩]
  | .s33 => [⟨.a2, .s33, .c0, .c0⟩, ⟨.a2, .s33, .c0, .c2⟩]
  | .s34 => [⟨.a2, .s34, .c0, .c0⟩, ⟨.a2, .s34, .c0, .c2⟩]
  | .s35 => [⟨.a2, .s35, .c0, .c3⟩, ⟨.a2, .s35, .c2, .c0⟩, ⟨.a2, .s35, .c2, .c2⟩]
  | .s36 => [⟨.a2, .s36, .c0, .c2⟩, ⟨.a2, .s36, .c2, .c0⟩]
  | .s37 => [⟨.a2, .s37, .c0, .c2⟩, ⟨.a2, .s37, .c2, .c0⟩]
  | .s38 => []

private def emptyDescList (_ : StateSN) : List NFDesc := []

private def listAbsApp_d0 : StateSN → List NFDesc | .s0 => [⟨.a1, .s1, .c0, .c0⟩] | .s1 => [⟨.a1, .s2, .c0, .c0⟩] | .s2 => [⟨.a1, .s3, .c1, .c0⟩] | .s3 => [⟨.a1, .s4, .c1, .c0⟩] | .s4 => [⟨.a1, .s5, .c0, .c0⟩] | .s5 => [⟨.a1, .s6, .c1, .c0⟩] | .s6 => [⟨.a1, .s6, .c1, .c0⟩] | .s7 => [⟨.a1, .s8, .c0, .c0⟩] | .s8 => [⟨.a1, .s5, .c1, .c0⟩] | .s9 => [⟨.a1, .s10, .c2, .c0⟩] | .s10 => [⟨.a1, .s5, .c0, .c0⟩] | .s11 => [⟨.a1, .s12, .c2, .c0⟩] | .s12 => [⟨.a1, .s5, .c0, .c0⟩] | .s13 => [⟨.a1, .s4, .c2, .c0⟩] | .s14 => [⟨.a1, .s5, .c1, .c0⟩] | .s15 => [⟨.a1, .s10, .c2, .c0⟩] | .s16 => [⟨.a1, .s5, .c1, .c0⟩] | .s17 => [⟨.a1, .s5, .c1, .c0⟩] | .s18 => [⟨.a1, .s5, .c1, .c0⟩] | .s19 => [⟨.a1, .s20, .c2, .c0⟩] | .s20 => [⟨.a1, .s6, .c0, .c0⟩] | .s21 => [⟨.a1, .s6, .c1, .c0⟩] | .s22 => [⟨.a1, .s6, .c0, .c0⟩] | .s23 => [⟨.a1, .s6, .c2, .c0⟩] | .s24 => [⟨.a1, .s6, .c2, .c0⟩] | .s25 => [⟨.a1, .s6, .c3, .c0⟩] | .s26 => [⟨.a1, .s6, .c2, .c0⟩] | .s27 => [⟨.a1, .s6, .c2, .c0⟩] | .s28 => [⟨.a1, .s6, .c2, .c0⟩] | .s29 => [⟨.a1, .s6, .c3, .c0⟩] | .s30 => [⟨.a1, .s6, .c4, .c0⟩] | .s31 => [⟨.a1, .s6, .c2, .c0⟩] | .s32 => [⟨.a1, .s21, .c2, .c0⟩] | .s33 => [⟨.a1, .s6, .c2, .c0⟩] | .s34 => [⟨.a1, .s6, .c2, .c0⟩] | .s35 => [⟨.a1, .s6, .c3, .c0⟩] | .s36 => [⟨.a1, .s21, .c2, .c0⟩] | .s37 => [⟨.a1, .s6, .c2, .c0⟩] | .s38 => []
private def listAbsApp_d1 : StateSN → List NFDesc | .s0 => [⟨.a2, .s7, .c0, .c0⟩] | .s1 => [⟨.a2, .s9, .c0, .c0⟩] | .s2 => [⟨.a2, .s11, .c0, .c1⟩] | .s3 => [⟨.a2, .s13, .c0, .c1⟩] | .s4 => [⟨.a2, .s14, .c0, .c0⟩] | .s5 => [⟨.a2, .s5, .c0, .c1⟩] | .s6 => [⟨.a2, .s6, .c0, .c1⟩] | .s7 => [⟨.a2, .s15, .c0, .c0⟩] | .s8 => [⟨.a2, .s16, .c0, .c1⟩] | .s9 => [⟨.a2, .s15, .c0, .c2⟩] | .s10 => [⟨.a2, .s17, .c0, .c0⟩] | .s11 => [⟨.a2, .s11, .c0, .c2⟩] | .s12 => [⟨.a2, .s18, .c0, .c0⟩] | .s13 => [⟨.a2, .s13, .c0, .c2⟩] | .s14 => [⟨.a2, .s14, .c0, .c1⟩] | .s15 => [⟨.a2, .s15, .c0, .c2⟩] | .s16 => [⟨.a2, .s16, .c0, .c1⟩] | .s17 => [⟨.a2, .s17, .c0, .c1⟩] | .s18 => [⟨.a2, .s18, .c0, .c1⟩] | .s19 => [⟨.a2, .s19, .c0, .c2⟩] | .s20 => [⟨.a2, .s21, .c0, .c0⟩] | .s21 => [⟨.a2, .s21, .c0, .c1⟩] | .s22 => [⟨.a2, .s23, .c0, .c0⟩] | .s23 => [⟨.a2, .s23, .c0, .c2⟩] | .s24 => [⟨.a2, .s24, .c0, .c2⟩] | .s25 => [⟨.a2, .s25, .c0, .c3⟩] | .s26 => [⟨.a2, .s26, .c0, .c2⟩] | .s27 => [⟨.a2, .s27, .c0, .c2⟩] | .s28 => [⟨.a2, .s28, .c0, .c2⟩] | .s29 => [⟨.a2, .s29, .c0, .c3⟩] | .s30 => [⟨.a2, .s30, .c0, .c4⟩] | .s31 => [⟨.a2, .s31, .c0, .c2⟩] | .s32 => [⟨.a2, .s32, .c0, .c2⟩] | .s33 => [⟨.a2, .s33, .c0, .c2⟩] | .s34 => [⟨.a2, .s34, .c0, .c2⟩] | .s35 => [⟨.a2, .s35, .c0, .c3⟩] | .s36 => [⟨.a2, .s36, .c0, .c2⟩] | .s37 => [⟨.a2, .s37, .c0, .c2⟩] | .s38 => []
private def listAbsApp_d2 : StateSN → List NFDesc | .s0 => [⟨.a2, .s19, .c0, .c0⟩] | .s1 => [⟨.a2, .s22, .c0, .c0⟩] | .s2 => [⟨.a2, .s24, .c0, .c1⟩] | .s3 => [⟨.a2, .s25, .c0, .c1⟩] | .s4 => [⟨.a2, .s25, .c0, .c0⟩] | .s5 => [⟨.a2, .s25, .c0, .c1⟩] | .s6 => [⟨.a2, .s25, .c0, .c1⟩] | .s7 => [⟨.a2, .s26, .c0, .c0⟩] | .s8 => [⟨.a2, .s25, .c0, .c1⟩] | .s9 => [⟨.a2, .s26, .c0, .c2⟩] | .s10 => [⟨.a2, .s25, .c0, .c0⟩] | .s11 => [⟨.a2, .s25, .c0, .c2⟩] | .s12 => [⟨.a2, .s25, .c0, .c0⟩] | .s13 => [⟨.a2, .s25, .c0, .c2⟩] | .s14 => [⟨.a2, .s25, .c0, .c1⟩] | .s15 => [⟨.a2, .s26, .c0, .c2⟩] | .s16 => [⟨.a2, .s25, .c0, .c1⟩] | .s17 => [⟨.a2, .s25, .c0, .c1⟩] | .s18 => [⟨.a2, .s25, .c0, .c1⟩] | .s19 => [⟨.a2, .s25, .c0, .c2⟩] | .s20 => [⟨.a2, .s25, .c0, .c0⟩] | .s21 => [⟨.a2, .s25, .c0, .c1⟩] | .s22 => [⟨.a2, .s25, .c0, .c0⟩] | .s23 => [⟨.a2, .s25, .c0, .c2⟩] | .s24 => [⟨.a2, .s25, .c0, .c2⟩] | .s25 => [⟨.a2, .s25, .c0, .c3⟩] | .s26 => [⟨.a2, .s25, .c0, .c2⟩] | .s27 => [⟨.a2, .s25, .c0, .c2⟩] | .s28 => [⟨.a2, .s25, .c0, .c2⟩] | .s29 => [⟨.a2, .s29, .c0, .c3⟩] | .s30 => [⟨.a2, .s30, .c0, .c4⟩] | .s31 => [⟨.a2, .s31, .c0, .c2⟩] | .s32 => [⟨.a2, .s31, .c0, .c2⟩] | .s33 => [⟨.a2, .s31, .c0, .c2⟩] | .s34 => [⟨.a2, .s29, .c0, .c2⟩] | .s35 => [⟨.a2, .s29, .c0, .c3⟩] | .s36 => [⟨.a2, .s31, .c0, .c2⟩] | .s37 => [⟨.a2, .s31, .c0, .c2⟩] | .s38 => []
private def listAbsApp_d3 : StateSN → List NFDesc | .s0 => [⟨.a2, .s27, .c1, .c0⟩] | .s1 => [⟨.a2, .s28, .c1, .c0⟩] | .s2 => [⟨.a2, .s29, .c1, .c1⟩] | .s3 => [⟨.a2, .s29, .c1, .c1⟩] | .s4 => [⟨.a2, .s30, .c1, .c0⟩] | .s5 => [⟨.a2, .s30, .c1, .c1⟩] | .s6 => [⟨.a2, .s30, .c1, .c1⟩] | .s7 => [⟨.a2, .s29, .c1, .c0⟩] | .s8 => [⟨.a2, .s30, .c1, .c1⟩] | .s9 => [⟨.a2, .s29, .c1, .c2⟩] | .s10 => [⟨.a2, .s30, .c1, .c0⟩] | .s11 => [⟨.a2, .s29, .c1, .c2⟩] | .s12 => [⟨.a2, .s30, .c1, .c0⟩] | .s13 => [⟨.a2, .s29, .c1, .c2⟩] | .s14 => [⟨.a2, .s30, .c1, .c1⟩] | .s15 => [⟨.a2, .s29, .c1, .c2⟩] | .s16 => [⟨.a2, .s30, .c1, .c1⟩] | .s17 => [⟨.a2, .s30, .c1, .c1⟩] | .s18 => [⟨.a2, .s30, .c1, .c1⟩] | .s19 => [⟨.a2, .s29, .c1, .c2⟩] | .s20 => [⟨.a2, .s30, .c1, .c0⟩] | .s21 => [⟨.a2, .s30, .c1, .c1⟩] | .s22 => [⟨.a2, .s30, .c1, .c0⟩] | .s23 => [⟨.a2, .s30, .c1, .c2⟩] | .s24 => [⟨.a2, .s30, .c1, .c2⟩] | .s25 => [⟨.a2, .s30, .c1, .c3⟩] | .s26 => [⟨.a2, .s30, .c1, .c2⟩] | .s27 => [⟨.a2, .s30, .c1, .c2⟩] | .s28 => [⟨.a2, .s30, .c1, .c2⟩] | .s29 => [⟨.a2, .s30, .c1, .c3⟩] | .s30 => [⟨.a2, .s30, .c1, .c4⟩] | .s31 => [⟨.a2, .s30, .c1, .c2⟩] | .s32 => [⟨.a2, .s29, .c1, .c2⟩] | .s33 => [⟨.a2, .s30, .c1, .c2⟩] | .s34 => [⟨.a2, .s30, .c1, .c2⟩] | .s35 => [⟨.a2, .s30, .c1, .c3⟩] | .s36 => [⟨.a2, .s29, .c1, .c2⟩] | .s37 => [⟨.a2, .s30, .c1, .c2⟩] | .s38 => []
private def listAbsApp_d4 : StateSN → List NFDesc | .s0 => [⟨.a2, .s31, .c1, .c0⟩] | .s1 => [⟨.a2, .s31, .c1, .c0⟩] | .s2 => [⟨.a2, .s29, .c1, .c1⟩] | .s3 => [⟨.a2, .s29, .c1, .c1⟩] | .s4 => [⟨.a2, .s30, .c1, .c0⟩] | .s5 => [⟨.a2, .s30, .c1, .c1⟩] | .s6 => [⟨.a2, .s30, .c1, .c1⟩] | .s7 => [⟨.a2, .s29, .c1, .c0⟩] | .s8 => [⟨.a2, .s30, .c1, .c1⟩] | .s9 => [⟨.a2, .s29, .c1, .c2⟩] | .s10 => [⟨.a2, .s30, .c1, .c0⟩] | .s11 => [⟨.a2, .s29, .c1, .c2⟩] | .s12 => [⟨.a2, .s30, .c1, .c0⟩] | .s13 => [⟨.a2, .s29, .c1, .c2⟩] | .s14 => [⟨.a2, .s30, .c1, .c1⟩] | .s15 => [⟨.a2, .s29, .c1, .c2⟩] | .s16 => [⟨.a2, .s30, .c1, .c1⟩] | .s17 => [⟨.a2, .s30, .c1, .c1⟩] | .s18 => [⟨.a2, .s30, .c1, .c1⟩] | .s19 => [⟨.a2, .s29, .c1, .c2⟩] | .s20 => [⟨.a2, .s30, .c1, .c0⟩] | .s21 => [⟨.a2, .s30, .c1, .c1⟩] | .s22 => [⟨.a2, .s30, .c1, .c0⟩] | .s23 => [⟨.a2, .s30, .c1, .c2⟩] | .s24 => [⟨.a2, .s30, .c1, .c2⟩] | .s25 => [⟨.a2, .s30, .c1, .c3⟩] | .s26 => [⟨.a2, .s30, .c1, .c2⟩] | .s27 => [⟨.a2, .s30, .c1, .c2⟩] | .s28 => [⟨.a2, .s30, .c1, .c2⟩] | .s29 => [⟨.a2, .s30, .c1, .c3⟩] | .s30 => [⟨.a2, .s30, .c1, .c4⟩] | .s31 => [⟨.a2, .s30, .c1, .c2⟩] | .s32 => [⟨.a2, .s29, .c1, .c2⟩] | .s33 => [⟨.a2, .s30, .c1, .c2⟩] | .s34 => [⟨.a2, .s30, .c1, .c2⟩] | .s35 => [⟨.a2, .s30, .c1, .c3⟩] | .s36 => [⟨.a2, .s29, .c1, .c2⟩] | .s37 => [⟨.a2, .s30, .c1, .c2⟩] | .s38 => []
private def listAbsApp_d5 : StateSN → List NFDesc | .s0 => [⟨.a2, .s31, .c2, .c0⟩] | .s1 => [⟨.a2, .s31, .c2, .c0⟩] | .s2 => [⟨.a2, .s29, .c2, .c1⟩] | .s3 => [⟨.a2, .s29, .c2, .c1⟩] | .s4 => [⟨.a2, .s30, .c2, .c0⟩] | .s5 => [⟨.a2, .s30, .c2, .c1⟩] | .s6 => [⟨.a2, .s30, .c2, .c1⟩] | .s7 => [⟨.a2, .s29, .c2, .c0⟩] | .s8 => [⟨.a2, .s30, .c2, .c1⟩] | .s9 => [⟨.a2, .s29, .c2, .c2⟩] | .s10 => [⟨.a2, .s30, .c2, .c0⟩] | .s11 => [⟨.a2, .s29, .c2, .c2⟩] | .s12 => [⟨.a2, .s30, .c2, .c0⟩] | .s13 => [⟨.a2, .s29, .c2, .c2⟩] | .s14 => [⟨.a2, .s30, .c2, .c1⟩] | .s15 => [⟨.a2, .s29, .c2, .c2⟩] | .s16 => [⟨.a2, .s30, .c2, .c1⟩] | .s17 => [⟨.a2, .s30, .c2, .c1⟩] | .s18 => [⟨.a2, .s30, .c2, .c1⟩] | .s19 => [⟨.a2, .s29, .c2, .c2⟩] | .s20 => [⟨.a2, .s30, .c2, .c0⟩] | .s21 => [⟨.a2, .s30, .c2, .c1⟩] | .s22 => [⟨.a2, .s30, .c2, .c0⟩] | .s23 => [⟨.a2, .s30, .c2, .c2⟩] | .s24 => [⟨.a2, .s30, .c2, .c2⟩] | .s25 => [⟨.a2, .s30, .c2, .c3⟩] | .s26 => [⟨.a2, .s30, .c2, .c2⟩] | .s27 => [⟨.a2, .s30, .c2, .c2⟩] | .s28 => [⟨.a2, .s30, .c2, .c2⟩] | .s29 => [⟨.a2, .s30, .c2, .c3⟩] | .s30 => [⟨.a2, .s30, .c2, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c2⟩] | .s32 => [⟨.a2, .s29, .c2, .c2⟩] | .s33 => [⟨.a2, .s30, .c2, .c2⟩] | .s34 => [⟨.a2, .s30, .c2, .c2⟩] | .s35 => [⟨.a2, .s30, .c2, .c3⟩] | .s36 => [⟨.a2, .s29, .c2, .c2⟩] | .s37 => [⟨.a2, .s30, .c2, .c2⟩] | .s38 => []
private def listAbsApp_d6 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c0⟩] | .s1 => [⟨.a2, .s30, .c0, .c0⟩] | .s2 => [⟨.a2, .s30, .c0, .c1⟩] | .s3 => [⟨.a2, .s30, .c0, .c1⟩] | .s4 => [⟨.a2, .s30, .c0, .c0⟩] | .s5 => [⟨.a2, .s30, .c0, .c1⟩] | .s6 => [⟨.a2, .s30, .c0, .c1⟩] | .s7 => [⟨.a2, .s30, .c0, .c0⟩] | .s8 => [⟨.a2, .s30, .c0, .c1⟩] | .s9 => [⟨.a2, .s30, .c0, .c2⟩] | .s10 => [⟨.a2, .s30, .c0, .c0⟩] | .s11 => [⟨.a2, .s30, .c0, .c2⟩] | .s12 => [⟨.a2, .s30, .c0, .c0⟩] | .s13 => [⟨.a2, .s30, .c0, .c2⟩] | .s14 => [⟨.a2, .s30, .c0, .c1⟩] | .s15 => [⟨.a2, .s30, .c0, .c2⟩] | .s16 => [⟨.a2, .s30, .c0, .c1⟩] | .s17 => [⟨.a2, .s30, .c0, .c1⟩] | .s18 => [⟨.a2, .s30, .c0, .c1⟩] | .s19 => [⟨.a2, .s30, .c0, .c2⟩] | .s20 => [⟨.a2, .s30, .c0, .c0⟩] | .s21 => [⟨.a2, .s30, .c0, .c1⟩] | .s22 => [⟨.a2, .s30, .c0, .c0⟩] | .s23 => [⟨.a2, .s30, .c0, .c2⟩] | .s24 => [⟨.a2, .s30, .c0, .c2⟩] | .s25 => [⟨.a2, .s30, .c0, .c3⟩] | .s26 => [⟨.a2, .s30, .c0, .c2⟩] | .s27 => [⟨.a2, .s30, .c0, .c2⟩] | .s28 => [⟨.a2, .s30, .c0, .c2⟩] | .s29 => [⟨.a2, .s30, .c0, .c3⟩] | .s30 => [⟨.a2, .s30, .c0, .c4⟩] | .s31 => [⟨.a2, .s30, .c0, .c2⟩] | .s32 => [⟨.a2, .s30, .c0, .c2⟩] | .s33 => [⟨.a2, .s30, .c0, .c2⟩] | .s34 => [⟨.a2, .s30, .c0, .c2⟩] | .s35 => [⟨.a2, .s30, .c0, .c3⟩] | .s36 => [⟨.a2, .s30, .c0, .c2⟩] | .s37 => [⟨.a2, .s30, .c0, .c2⟩] | .s38 => []
private def listAbsApp_d7 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c1, .c0⟩] | .s1 => [⟨.a2, .s30, .c1, .c0⟩] | .s2 => [⟨.a2, .s30, .c1, .c1⟩] | .s3 => [⟨.a2, .s30, .c1, .c1⟩] | .s4 => [⟨.a2, .s30, .c1, .c0⟩] | .s5 => [⟨.a2, .s30, .c1, .c1⟩] | .s6 => [⟨.a2, .s30, .c1, .c1⟩] | .s7 => [⟨.a2, .s30, .c1, .c0⟩] | .s8 => [⟨.a2, .s30, .c1, .c1⟩] | .s9 => [⟨.a2, .s30, .c1, .c2⟩] | .s10 => [⟨.a2, .s30, .c1, .c0⟩] | .s11 => [⟨.a2, .s30, .c1, .c2⟩] | .s12 => [⟨.a2, .s30, .c1, .c0⟩] | .s13 => [⟨.a2, .s30, .c1, .c2⟩] | .s14 => [⟨.a2, .s30, .c1, .c1⟩] | .s15 => [⟨.a2, .s30, .c1, .c2⟩] | .s16 => [⟨.a2, .s30, .c1, .c1⟩] | .s17 => [⟨.a2, .s30, .c1, .c1⟩] | .s18 => [⟨.a2, .s30, .c1, .c1⟩] | .s19 => [⟨.a2, .s30, .c1, .c2⟩] | .s20 => [⟨.a2, .s30, .c1, .c0⟩] | .s21 => [⟨.a2, .s30, .c1, .c1⟩] | .s22 => [⟨.a2, .s30, .c1, .c0⟩] | .s23 => [⟨.a2, .s30, .c1, .c2⟩] | .s24 => [⟨.a2, .s30, .c1, .c2⟩] | .s25 => [⟨.a2, .s30, .c1, .c3⟩] | .s26 => [⟨.a2, .s30, .c1, .c2⟩] | .s27 => [⟨.a2, .s30, .c1, .c2⟩] | .s28 => [⟨.a2, .s30, .c1, .c2⟩] | .s29 => [⟨.a2, .s30, .c1, .c3⟩] | .s30 => [⟨.a2, .s30, .c1, .c4⟩] | .s31 => [⟨.a2, .s30, .c1, .c2⟩] | .s32 => [⟨.a2, .s30, .c1, .c2⟩] | .s33 => [⟨.a2, .s30, .c1, .c2⟩] | .s34 => [⟨.a2, .s30, .c1, .c2⟩] | .s35 => [⟨.a2, .s30, .c1, .c3⟩] | .s36 => [⟨.a2, .s30, .c1, .c2⟩] | .s37 => [⟨.a2, .s30, .c1, .c2⟩] | .s38 => []
private def listAbsApp_d8 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c0⟩] | .s1 => [⟨.a2, .s30, .c0, .c0⟩] | .s2 => [⟨.a2, .s30, .c0, .c1⟩] | .s3 => [⟨.a2, .s30, .c0, .c1⟩] | .s4 => [⟨.a2, .s30, .c0, .c0⟩] | .s5 => [⟨.a2, .s30, .c0, .c1⟩] | .s6 => [⟨.a2, .s30, .c0, .c1⟩] | .s7 => [⟨.a2, .s30, .c0, .c0⟩] | .s8 => [⟨.a2, .s30, .c0, .c1⟩] | .s9 => [⟨.a2, .s30, .c0, .c2⟩] | .s10 => [⟨.a2, .s30, .c0, .c0⟩] | .s11 => [⟨.a2, .s30, .c0, .c2⟩] | .s12 => [⟨.a2, .s30, .c0, .c0⟩] | .s13 => [⟨.a2, .s30, .c0, .c2⟩] | .s14 => [⟨.a2, .s30, .c0, .c1⟩] | .s15 => [⟨.a2, .s30, .c0, .c2⟩] | .s16 => [⟨.a2, .s30, .c0, .c1⟩] | .s17 => [⟨.a2, .s30, .c0, .c1⟩] | .s18 => [⟨.a2, .s30, .c0, .c1⟩] | .s19 => [⟨.a2, .s30, .c0, .c2⟩] | .s20 => [⟨.a2, .s30, .c0, .c0⟩] | .s21 => [⟨.a2, .s30, .c0, .c1⟩] | .s22 => [⟨.a2, .s30, .c0, .c0⟩] | .s23 => [⟨.a2, .s30, .c0, .c2⟩] | .s24 => [⟨.a2, .s30, .c0, .c2⟩] | .s25 => [⟨.a2, .s30, .c0, .c3⟩] | .s26 => [⟨.a2, .s30, .c0, .c2⟩] | .s27 => [⟨.a2, .s30, .c0, .c2⟩] | .s28 => [⟨.a2, .s30, .c0, .c2⟩] | .s29 => [⟨.a2, .s30, .c0, .c3⟩] | .s30 => [⟨.a2, .s30, .c0, .c4⟩] | .s31 => [⟨.a2, .s30, .c0, .c2⟩] | .s32 => [⟨.a2, .s30, .c0, .c2⟩] | .s33 => [⟨.a2, .s30, .c0, .c2⟩] | .s34 => [⟨.a2, .s30, .c0, .c2⟩] | .s35 => [⟨.a2, .s30, .c0, .c3⟩] | .s36 => [⟨.a2, .s30, .c0, .c2⟩] | .s37 => [⟨.a2, .s30, .c0, .c2⟩] | .s38 => []
private def listAbsApp_d9 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c1, .c0⟩] | .s1 => [⟨.a2, .s30, .c1, .c0⟩] | .s2 => [⟨.a2, .s30, .c1, .c1⟩] | .s3 => [⟨.a2, .s30, .c1, .c1⟩] | .s4 => [⟨.a2, .s30, .c1, .c0⟩] | .s5 => [⟨.a2, .s30, .c1, .c1⟩] | .s6 => [⟨.a2, .s30, .c1, .c1⟩] | .s7 => [⟨.a2, .s30, .c1, .c0⟩] | .s8 => [⟨.a2, .s30, .c1, .c1⟩] | .s9 => [⟨.a2, .s30, .c1, .c2⟩] | .s10 => [⟨.a2, .s30, .c1, .c0⟩] | .s11 => [⟨.a2, .s30, .c1, .c2⟩] | .s12 => [⟨.a2, .s30, .c1, .c0⟩] | .s13 => [⟨.a2, .s30, .c1, .c2⟩] | .s14 => [⟨.a2, .s30, .c1, .c1⟩] | .s15 => [⟨.a2, .s30, .c1, .c2⟩] | .s16 => [⟨.a2, .s30, .c1, .c1⟩] | .s17 => [⟨.a2, .s30, .c1, .c1⟩] | .s18 => [⟨.a2, .s30, .c1, .c1⟩] | .s19 => [⟨.a2, .s30, .c1, .c2⟩] | .s20 => [⟨.a2, .s30, .c1, .c0⟩] | .s21 => [⟨.a2, .s30, .c1, .c1⟩] | .s22 => [⟨.a2, .s30, .c1, .c0⟩] | .s23 => [⟨.a2, .s30, .c1, .c2⟩] | .s24 => [⟨.a2, .s30, .c1, .c2⟩] | .s25 => [⟨.a2, .s30, .c1, .c3⟩] | .s26 => [⟨.a2, .s30, .c1, .c2⟩] | .s27 => [⟨.a2, .s30, .c1, .c2⟩] | .s28 => [⟨.a2, .s30, .c1, .c2⟩] | .s29 => [⟨.a2, .s30, .c1, .c3⟩] | .s30 => [⟨.a2, .s30, .c1, .c4⟩] | .s31 => [⟨.a2, .s30, .c1, .c2⟩] | .s32 => [⟨.a2, .s30, .c1, .c2⟩] | .s33 => [⟨.a2, .s30, .c1, .c2⟩] | .s34 => [⟨.a2, .s30, .c1, .c2⟩] | .s35 => [⟨.a2, .s30, .c1, .c3⟩] | .s36 => [⟨.a2, .s30, .c1, .c2⟩] | .s37 => [⟨.a2, .s30, .c1, .c2⟩] | .s38 => []
private def listAbsApp_d10 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c0⟩] | .s1 => [⟨.a2, .s30, .c2, .c0⟩] | .s2 => [⟨.a2, .s30, .c2, .c1⟩] | .s3 => [⟨.a2, .s30, .c2, .c1⟩] | .s4 => [⟨.a2, .s30, .c2, .c0⟩] | .s5 => [⟨.a2, .s30, .c2, .c1⟩] | .s6 => [⟨.a2, .s30, .c2, .c1⟩] | .s7 => [⟨.a2, .s30, .c2, .c0⟩] | .s8 => [⟨.a2, .s30, .c2, .c1⟩] | .s9 => [⟨.a2, .s30, .c2, .c2⟩] | .s10 => [⟨.a2, .s30, .c2, .c0⟩] | .s11 => [⟨.a2, .s30, .c2, .c2⟩] | .s12 => [⟨.a2, .s30, .c2, .c0⟩] | .s13 => [⟨.a2, .s30, .c2, .c2⟩] | .s14 => [⟨.a2, .s30, .c2, .c1⟩] | .s15 => [⟨.a2, .s30, .c2, .c2⟩] | .s16 => [⟨.a2, .s30, .c2, .c1⟩] | .s17 => [⟨.a2, .s30, .c2, .c1⟩] | .s18 => [⟨.a2, .s30, .c2, .c1⟩] | .s19 => [⟨.a2, .s30, .c2, .c2⟩] | .s20 => [⟨.a2, .s30, .c2, .c0⟩] | .s21 => [⟨.a2, .s30, .c2, .c1⟩] | .s22 => [⟨.a2, .s30, .c2, .c0⟩] | .s23 => [⟨.a2, .s30, .c2, .c2⟩] | .s24 => [⟨.a2, .s30, .c2, .c2⟩] | .s25 => [⟨.a2, .s30, .c2, .c3⟩] | .s26 => [⟨.a2, .s30, .c2, .c2⟩] | .s27 => [⟨.a2, .s30, .c2, .c2⟩] | .s28 => [⟨.a2, .s30, .c2, .c2⟩] | .s29 => [⟨.a2, .s30, .c2, .c3⟩] | .s30 => [⟨.a2, .s30, .c2, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c2⟩] | .s32 => [⟨.a2, .s30, .c2, .c2⟩] | .s33 => [⟨.a2, .s30, .c2, .c2⟩] | .s34 => [⟨.a2, .s30, .c2, .c2⟩] | .s35 => [⟨.a2, .s30, .c2, .c3⟩] | .s36 => [⟨.a2, .s30, .c2, .c2⟩] | .s37 => [⟨.a2, .s30, .c2, .c2⟩] | .s38 => []
private def listAbsApp_d11 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c3, .c0⟩] | .s1 => [⟨.a2, .s30, .c3, .c0⟩] | .s2 => [⟨.a2, .s30, .c3, .c1⟩] | .s3 => [⟨.a2, .s30, .c3, .c1⟩] | .s4 => [⟨.a2, .s30, .c3, .c0⟩] | .s5 => [⟨.a2, .s30, .c3, .c1⟩] | .s6 => [⟨.a2, .s30, .c3, .c1⟩] | .s7 => [⟨.a2, .s30, .c3, .c0⟩] | .s8 => [⟨.a2, .s30, .c3, .c1⟩] | .s9 => [⟨.a2, .s30, .c3, .c2⟩] | .s10 => [⟨.a2, .s30, .c3, .c0⟩] | .s11 => [⟨.a2, .s30, .c3, .c2⟩] | .s12 => [⟨.a2, .s30, .c3, .c0⟩] | .s13 => [⟨.a2, .s30, .c3, .c2⟩] | .s14 => [⟨.a2, .s30, .c3, .c1⟩] | .s15 => [⟨.a2, .s30, .c3, .c2⟩] | .s16 => [⟨.a2, .s30, .c3, .c1⟩] | .s17 => [⟨.a2, .s30, .c3, .c1⟩] | .s18 => [⟨.a2, .s30, .c3, .c1⟩] | .s19 => [⟨.a2, .s30, .c3, .c2⟩] | .s20 => [⟨.a2, .s30, .c3, .c0⟩] | .s21 => [⟨.a2, .s30, .c3, .c1⟩] | .s22 => [⟨.a2, .s30, .c3, .c0⟩] | .s23 => [⟨.a2, .s30, .c3, .c2⟩] | .s24 => [⟨.a2, .s30, .c3, .c2⟩] | .s25 => [⟨.a2, .s30, .c3, .c3⟩] | .s26 => [⟨.a2, .s30, .c3, .c2⟩] | .s27 => [⟨.a2, .s30, .c3, .c2⟩] | .s28 => [⟨.a2, .s30, .c3, .c2⟩] | .s29 => [⟨.a2, .s30, .c3, .c3⟩] | .s30 => [⟨.a2, .s30, .c3, .c4⟩] | .s31 => [⟨.a2, .s30, .c3, .c2⟩] | .s32 => [⟨.a2, .s30, .c3, .c2⟩] | .s33 => [⟨.a2, .s30, .c3, .c2⟩] | .s34 => [⟨.a2, .s30, .c3, .c2⟩] | .s35 => [⟨.a2, .s30, .c3, .c3⟩] | .s36 => [⟨.a2, .s30, .c3, .c2⟩] | .s37 => [⟨.a2, .s30, .c3, .c2⟩] | .s38 => []
private def listAbsApp_d12 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c4, .c0⟩] | .s1 => [⟨.a2, .s30, .c4, .c0⟩] | .s2 => [⟨.a2, .s30, .c4, .c1⟩] | .s3 => [⟨.a2, .s30, .c4, .c1⟩] | .s4 => [⟨.a2, .s30, .c4, .c0⟩] | .s5 => [⟨.a2, .s30, .c4, .c1⟩] | .s6 => [⟨.a2, .s30, .c4, .c1⟩] | .s7 => [⟨.a2, .s30, .c4, .c0⟩] | .s8 => [⟨.a2, .s30, .c4, .c1⟩] | .s9 => [⟨.a2, .s30, .c4, .c2⟩] | .s10 => [⟨.a2, .s30, .c4, .c0⟩] | .s11 => [⟨.a2, .s30, .c4, .c2⟩] | .s12 => [⟨.a2, .s30, .c4, .c0⟩] | .s13 => [⟨.a2, .s30, .c4, .c2⟩] | .s14 => [⟨.a2, .s30, .c4, .c1⟩] | .s15 => [⟨.a2, .s30, .c4, .c2⟩] | .s16 => [⟨.a2, .s30, .c4, .c1⟩] | .s17 => [⟨.a2, .s30, .c4, .c1⟩] | .s18 => [⟨.a2, .s30, .c4, .c1⟩] | .s19 => [⟨.a2, .s30, .c4, .c2⟩] | .s20 => [⟨.a2, .s30, .c4, .c0⟩] | .s21 => [⟨.a2, .s30, .c4, .c1⟩] | .s22 => [⟨.a2, .s30, .c4, .c0⟩] | .s23 => [⟨.a2, .s30, .c4, .c2⟩] | .s24 => [⟨.a2, .s30, .c4, .c2⟩] | .s25 => [⟨.a2, .s30, .c4, .c3⟩] | .s26 => [⟨.a2, .s30, .c4, .c2⟩] | .s27 => [⟨.a2, .s30, .c4, .c2⟩] | .s28 => [⟨.a2, .s30, .c4, .c2⟩] | .s29 => [⟨.a2, .s30, .c4, .c3⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c4, .c2⟩] | .s32 => [⟨.a2, .s30, .c4, .c2⟩] | .s33 => [⟨.a2, .s30, .c4, .c2⟩] | .s34 => [⟨.a2, .s30, .c4, .c2⟩] | .s35 => [⟨.a2, .s30, .c4, .c3⟩] | .s36 => [⟨.a2, .s30, .c4, .c2⟩] | .s37 => [⟨.a2, .s30, .c4, .c2⟩] | .s38 => []
private def listAbsApp_d13 : StateSN → List NFDesc | .s0 => [⟨.a2, .s32, .c0, .c0⟩] | .s1 => [⟨.a2, .s33, .c0, .c0⟩] | .s2 => [⟨.a2, .s29, .c0, .c1⟩] | .s3 => [⟨.a2, .s29, .c0, .c1⟩] | .s4 => [⟨.a2, .s29, .c0, .c0⟩] | .s5 => [⟨.a2, .s29, .c0, .c1⟩] | .s6 => [⟨.a2, .s29, .c0, .c1⟩] | .s7 => [⟨.a2, .s34, .c0, .c0⟩] | .s8 => [⟨.a2, .s29, .c0, .c1⟩] | .s9 => [⟨.a2, .s34, .c0, .c2⟩] | .s10 => [⟨.a2, .s29, .c0, .c0⟩] | .s11 => [⟨.a2, .s29, .c0, .c2⟩] | .s12 => [⟨.a2, .s29, .c0, .c0⟩] | .s13 => [⟨.a2, .s29, .c0, .c2⟩] | .s14 => [⟨.a2, .s29, .c0, .c1⟩] | .s15 => [⟨.a2, .s34, .c0, .c2⟩] | .s16 => [⟨.a2, .s29, .c0, .c1⟩] | .s17 => [⟨.a2, .s29, .c0, .c1⟩] | .s18 => [⟨.a2, .s29, .c0, .c1⟩] | .s19 => [⟨.a2, .s29, .c0, .c2⟩] | .s20 => [⟨.a2, .s29, .c0, .c0⟩] | .s21 => [⟨.a2, .s29, .c0, .c1⟩] | .s22 => [⟨.a2, .s29, .c0, .c0⟩] | .s23 => [⟨.a2, .s29, .c0, .c2⟩] | .s24 => [⟨.a2, .s29, .c0, .c2⟩] | .s25 => [⟨.a2, .s29, .c0, .c3⟩] | .s26 => [⟨.a2, .s29, .c0, .c2⟩] | .s27 => [⟨.a2, .s29, .c0, .c2⟩] | .s28 => [⟨.a2, .s29, .c0, .c2⟩] | .s29 => [⟨.a2, .s29, .c0, .c3⟩] | .s30 => [⟨.a2, .s30, .c0, .c4⟩] | .s31 => [⟨.a2, .s29, .c0, .c2⟩] | .s32 => [⟨.a2, .s29, .c0, .c2⟩] | .s33 => [⟨.a2, .s29, .c0, .c2⟩] | .s34 => [⟨.a2, .s29, .c0, .c2⟩] | .s35 => [⟨.a2, .s29, .c0, .c3⟩] | .s36 => [⟨.a2, .s29, .c0, .c2⟩] | .s37 => [⟨.a2, .s29, .c0, .c2⟩] | .s38 => []
private def listAbsApp_d14 : StateSN → List NFDesc | .s0 => [⟨.a2, .s36, .c2, .c0⟩] | .s1 => [⟨.a2, .s37, .c2, .c0⟩] | .s2 => [⟨.a2, .s29, .c2, .c1⟩] | .s3 => [⟨.a2, .s29, .c2, .c1⟩] | .s4 => [⟨.a2, .s29, .c2, .c0⟩] | .s5 => [⟨.a2, .s29, .c2, .c1⟩] | .s6 => [⟨.a2, .s29, .c2, .c1⟩] | .s7 => [⟨.a2, .s35, .c2, .c0⟩] | .s8 => [⟨.a2, .s29, .c2, .c1⟩] | .s9 => [⟨.a2, .s35, .c2, .c2⟩] | .s10 => [⟨.a2, .s29, .c2, .c0⟩] | .s11 => [⟨.a2, .s29, .c2, .c2⟩] | .s12 => [⟨.a2, .s29, .c2, .c0⟩] | .s13 => [⟨.a2, .s29, .c2, .c2⟩] | .s14 => [⟨.a2, .s29, .c2, .c1⟩] | .s15 => [⟨.a2, .s35, .c2, .c2⟩] | .s16 => [⟨.a2, .s29, .c2, .c1⟩] | .s17 => [⟨.a2, .s29, .c2, .c1⟩] | .s18 => [⟨.a2, .s29, .c2, .c1⟩] | .s19 => [⟨.a2, .s29, .c2, .c2⟩] | .s20 => [⟨.a2, .s29, .c2, .c0⟩] | .s21 => [⟨.a2, .s29, .c2, .c1⟩] | .s22 => [⟨.a2, .s29, .c2, .c0⟩] | .s23 => [⟨.a2, .s29, .c2, .c2⟩] | .s24 => [⟨.a2, .s29, .c2, .c2⟩] | .s25 => [⟨.a2, .s29, .c2, .c3⟩] | .s26 => [⟨.a2, .s29, .c2, .c2⟩] | .s27 => [⟨.a2, .s29, .c2, .c2⟩] | .s28 => [⟨.a2, .s29, .c2, .c2⟩] | .s29 => [⟨.a2, .s29, .c2, .c3⟩] | .s30 => [⟨.a2, .s30, .c2, .c4⟩] | .s31 => [⟨.a2, .s29, .c2, .c2⟩] | .s32 => [⟨.a2, .s29, .c2, .c2⟩] | .s33 => [⟨.a2, .s29, .c2, .c2⟩] | .s34 => [⟨.a2, .s29, .c2, .c2⟩] | .s35 => [⟨.a2, .s29, .c2, .c3⟩] | .s36 => [⟨.a2, .s29, .c2, .c2⟩] | .s37 => [⟨.a2, .s29, .c2, .c2⟩] | .s38 => []
private def listAbsApp_d15 : StateSN → List NFDesc | .s0 => [⟨.a2, .s37, .c2, .c0⟩] | .s1 => [⟨.a2, .s31, .c2, .c0⟩] | .s2 => [⟨.a2, .s29, .c2, .c1⟩] | .s3 => [⟨.a2, .s29, .c2, .c1⟩] | .s4 => [⟨.a2, .s30, .c2, .c0⟩] | .s5 => [⟨.a2, .s30, .c2, .c1⟩] | .s6 => [⟨.a2, .s30, .c2, .c1⟩] | .s7 => [⟨.a2, .s29, .c2, .c0⟩] | .s8 => [⟨.a2, .s30, .c2, .c1⟩] | .s9 => [⟨.a2, .s29, .c2, .c2⟩] | .s10 => [⟨.a2, .s30, .c2, .c0⟩] | .s11 => [⟨.a2, .s29, .c2, .c2⟩] | .s12 => [⟨.a2, .s30, .c2, .c0⟩] | .s13 => [⟨.a2, .s29, .c2, .c2⟩] | .s14 => [⟨.a2, .s30, .c2, .c1⟩] | .s15 => [⟨.a2, .s29, .c2, .c2⟩] | .s16 => [⟨.a2, .s30, .c2, .c1⟩] | .s17 => [⟨.a2, .s30, .c2, .c1⟩] | .s18 => [⟨.a2, .s30, .c2, .c1⟩] | .s19 => [⟨.a2, .s29, .c2, .c2⟩] | .s20 => [⟨.a2, .s30, .c2, .c0⟩] | .s21 => [⟨.a2, .s30, .c2, .c1⟩] | .s22 => [⟨.a2, .s30, .c2, .c0⟩] | .s23 => [⟨.a2, .s30, .c2, .c2⟩] | .s24 => [⟨.a2, .s30, .c2, .c2⟩] | .s25 => [⟨.a2, .s30, .c2, .c3⟩] | .s26 => [⟨.a2, .s30, .c2, .c2⟩] | .s27 => [⟨.a2, .s30, .c2, .c2⟩] | .s28 => [⟨.a2, .s30, .c2, .c2⟩] | .s29 => [⟨.a2, .s30, .c2, .c3⟩] | .s30 => [⟨.a2, .s30, .c2, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c2⟩] | .s32 => [⟨.a2, .s29, .c2, .c2⟩] | .s33 => [⟨.a2, .s30, .c2, .c2⟩] | .s34 => [⟨.a2, .s30, .c2, .c2⟩] | .s35 => [⟨.a2, .s30, .c2, .c3⟩] | .s36 => [⟨.a2, .s29, .c2, .c2⟩] | .s37 => [⟨.a2, .s30, .c2, .c2⟩] | .s38 => []
private def listAbsApp_d16 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c2, .c0⟩] | .s1 => [⟨.a2, .s29, .c2, .c0⟩] | .s2 => [⟨.a2, .s29, .c2, .c1⟩] | .s3 => [⟨.a2, .s29, .c2, .c1⟩] | .s4 => [⟨.a2, .s30, .c2, .c0⟩] | .s5 => [⟨.a2, .s30, .c2, .c1⟩] | .s6 => [⟨.a2, .s30, .c2, .c1⟩] | .s7 => [⟨.a2, .s29, .c2, .c0⟩] | .s8 => [⟨.a2, .s30, .c2, .c1⟩] | .s9 => [⟨.a2, .s29, .c2, .c2⟩] | .s10 => [⟨.a2, .s30, .c2, .c0⟩] | .s11 => [⟨.a2, .s29, .c2, .c2⟩] | .s12 => [⟨.a2, .s30, .c2, .c0⟩] | .s13 => [⟨.a2, .s29, .c2, .c2⟩] | .s14 => [⟨.a2, .s30, .c2, .c1⟩] | .s15 => [⟨.a2, .s29, .c2, .c2⟩] | .s16 => [⟨.a2, .s30, .c2, .c1⟩] | .s17 => [⟨.a2, .s30, .c2, .c1⟩] | .s18 => [⟨.a2, .s30, .c2, .c1⟩] | .s19 => [⟨.a2, .s30, .c2, .c2⟩] | .s20 => [⟨.a2, .s30, .c2, .c0⟩] | .s21 => [⟨.a2, .s30, .c2, .c1⟩] | .s22 => [⟨.a2, .s30, .c2, .c0⟩] | .s23 => [⟨.a2, .s30, .c2, .c2⟩] | .s24 => [⟨.a2, .s30, .c2, .c2⟩] | .s25 => [⟨.a2, .s30, .c2, .c3⟩] | .s26 => [⟨.a2, .s30, .c2, .c2⟩] | .s27 => [⟨.a2, .s30, .c2, .c2⟩] | .s28 => [⟨.a2, .s30, .c2, .c2⟩] | .s29 => [⟨.a2, .s30, .c2, .c3⟩] | .s30 => [⟨.a2, .s30, .c2, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c2⟩] | .s32 => [⟨.a2, .s30, .c2, .c2⟩] | .s33 => [⟨.a2, .s30, .c2, .c2⟩] | .s34 => [⟨.a2, .s30, .c2, .c2⟩] | .s35 => [⟨.a2, .s30, .c2, .c3⟩] | .s36 => [⟨.a2, .s30, .c2, .c2⟩] | .s37 => [⟨.a2, .s30, .c2, .c2⟩] | .s38 => []
private def listAbsApp_d17 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c2, .c0⟩] | .s1 => [⟨.a2, .s29, .c2, .c0⟩] | .s2 => [⟨.a2, .s30, .c2, .c1⟩] | .s3 => [⟨.a2, .s30, .c2, .c1⟩] | .s4 => [⟨.a2, .s30, .c2, .c0⟩] | .s5 => [⟨.a2, .s30, .c2, .c1⟩] | .s6 => [⟨.a2, .s30, .c2, .c1⟩] | .s7 => [⟨.a2, .s29, .c2, .c0⟩] | .s8 => [⟨.a2, .s30, .c2, .c1⟩] | .s9 => [⟨.a2, .s29, .c2, .c2⟩] | .s10 => [⟨.a2, .s30, .c2, .c0⟩] | .s11 => [⟨.a2, .s30, .c2, .c2⟩] | .s12 => [⟨.a2, .s30, .c2, .c0⟩] | .s13 => [⟨.a2, .s30, .c2, .c2⟩] | .s14 => [⟨.a2, .s30, .c2, .c1⟩] | .s15 => [⟨.a2, .s29, .c2, .c2⟩] | .s16 => [⟨.a2, .s30, .c2, .c1⟩] | .s17 => [⟨.a2, .s30, .c2, .c1⟩] | .s18 => [⟨.a2, .s30, .c2, .c1⟩] | .s19 => [⟨.a2, .s30, .c2, .c2⟩] | .s20 => [⟨.a2, .s30, .c2, .c0⟩] | .s21 => [⟨.a2, .s30, .c2, .c1⟩] | .s22 => [⟨.a2, .s30, .c2, .c0⟩] | .s23 => [⟨.a2, .s30, .c2, .c2⟩] | .s24 => [⟨.a2, .s30, .c2, .c2⟩] | .s25 => [⟨.a2, .s30, .c2, .c3⟩] | .s26 => [⟨.a2, .s30, .c2, .c2⟩] | .s27 => [⟨.a2, .s30, .c2, .c2⟩] | .s28 => [⟨.a2, .s30, .c2, .c2⟩] | .s29 => [⟨.a2, .s30, .c2, .c3⟩] | .s30 => [⟨.a2, .s30, .c2, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c2⟩] | .s32 => [⟨.a2, .s30, .c2, .c2⟩] | .s33 => [⟨.a2, .s30, .c2, .c2⟩] | .s34 => [⟨.a2, .s30, .c2, .c2⟩] | .s35 => [⟨.a2, .s30, .c2, .c3⟩] | .s36 => [⟨.a2, .s30, .c2, .c2⟩] | .s37 => [⟨.a2, .s30, .c2, .c2⟩] | .s38 => []
private def listAbsApp_d18 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s30, .c0, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d19 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s30, .c0, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d20 : StateSN → List NFDesc | .s0 => [⟨.a2, .s9, .c0, .c0⟩] | .s1 => [⟨.a2, .s24, .c0, .c1⟩] | .s2 => [⟨.a2, .s29, .c1, .c1⟩] | .s3 => [⟨.a2, .s30, .c1, .c0⟩] | .s4 => [⟨.a2, .s30, .c0, .c1⟩] | .s5 => [⟨.a2, .s30, .c1, .c1⟩] | .s6 => [⟨.a2, .s30, .c1, .c1⟩] | .s7 => [⟨.a2, .s29, .c0, .c1⟩] | .s8 => [⟨.a2, .s30, .c1, .c1⟩] | .s9 => [⟨.a2, .s29, .c2, .c0⟩] | .s10 => [⟨.a2, .s30, .c0, .c1⟩] | .s11 => [⟨.a2, .s30, .c2, .c0⟩] | .s12 => [⟨.a2, .s30, .c0, .c1⟩] | .s13 => [⟨.a2, .s30, .c2, .c0⟩] | .s14 => [⟨.a2, .s30, .c1, .c1⟩] | .s15 => [⟨.a2, .s29, .c2, .c0⟩] | .s16 => [⟨.a2, .s30, .c1, .c1⟩] | .s17 => [⟨.a2, .s30, .c1, .c1⟩] | .s18 => [⟨.a2, .s30, .c1, .c1⟩] | .s19 => [⟨.a2, .s30, .c2, .c0⟩] | .s20 => [⟨.a2, .s30, .c0, .c1⟩] | .s21 => [⟨.a2, .s30, .c1, .c1⟩] | .s22 => [⟨.a2, .s30, .c0, .c1⟩] | .s23 => [⟨.a2, .s30, .c2, .c1⟩] | .s24 => [⟨.a2, .s30, .c2, .c1⟩] | .s25 => [⟨.a2, .s30, .c3, .c1⟩] | .s26 => [⟨.a2, .s30, .c2, .c1⟩] | .s27 => [⟨.a2, .s30, .c2, .c1⟩] | .s28 => [⟨.a2, .s30, .c2, .c1⟩] | .s29 => [⟨.a2, .s30, .c3, .c1⟩] | .s30 => [⟨.a2, .s30, .c4, .c1⟩] | .s31 => [⟨.a2, .s30, .c2, .c1⟩] | .s32 => [⟨.a2, .s30, .c2, .c1⟩] | .s33 => [⟨.a2, .s30, .c2, .c1⟩] | .s34 => [⟨.a2, .s30, .c2, .c1⟩] | .s35 => [⟨.a2, .s30, .c3, .c1⟩] | .s36 => [⟨.a2, .s30, .c2, .c1⟩] | .s37 => [⟨.a2, .s30, .c2, .c1⟩] | .s38 => []
private def listAbsApp_d21 : StateSN → List NFDesc | .s0 => [⟨.a2, .s15, .c0, .c0⟩] | .s1 => [⟨.a2, .s26, .c0, .c2⟩] | .s2 => [⟨.a2, .s29, .c1, .c2⟩] | .s3 => [⟨.a2, .s29, .c1, .c2⟩] | .s4 => [⟨.a2, .s30, .c0, .c1⟩] | .s5 => [⟨.a2, .s30, .c1, .c1⟩] | .s6 => [⟨.a2, .s30, .c1, .c1⟩] | .s7 => [⟨.a2, .s34, .c0, .c2⟩] | .s8 => [⟨.a2, .s30, .c1, .c1⟩] | .s9 => [⟨.a2, .s35, .c2, .c2⟩] | .s10 => [⟨.a2, .s30, .c0, .c1⟩] | .s11 => [⟨.a2, .s29, .c2, .c2⟩] | .s12 => [⟨.a2, .s30, .c0, .c1⟩] | .s13 => [⟨.a2, .s29, .c2, .c2⟩] | .s14 => [⟨.a2, .s30, .c1, .c1⟩] | .s15 => [⟨.a2, .s35, .c2, .c2⟩] | .s16 => [⟨.a2, .s30, .c1, .c1⟩] | .s17 => [⟨.a2, .s30, .c1, .c1⟩] | .s18 => [⟨.a2, .s30, .c1, .c1⟩] | .s19 => [⟨.a2, .s30, .c2, .c2⟩] | .s20 => [⟨.a2, .s30, .c0, .c1⟩] | .s21 => [⟨.a2, .s30, .c1, .c1⟩] | .s22 => [⟨.a2, .s30, .c0, .c2⟩] | .s23 => [⟨.a2, .s30, .c2, .c2⟩] | .s24 => [⟨.a2, .s30, .c2, .c2⟩] | .s25 => [⟨.a2, .s30, .c3, .c3⟩] | .s26 => [⟨.a2, .s30, .c2, .c2⟩] | .s27 => [⟨.a2, .s30, .c2, .c2⟩] | .s28 => [⟨.a2, .s30, .c2, .c2⟩] | .s29 => [⟨.a2, .s30, .c3, .c3⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c2⟩] | .s32 => [⟨.a2, .s30, .c2, .c2⟩] | .s33 => [⟨.a2, .s30, .c2, .c2⟩] | .s34 => [⟨.a2, .s30, .c2, .c2⟩] | .s35 => [⟨.a2, .s30, .c3, .c3⟩] | .s36 => [⟨.a2, .s30, .c2, .c2⟩] | .s37 => [⟨.a2, .s30, .c2, .c2⟩] | .s38 => []
private def listAbsApp_d22 : StateSN → List NFDesc | .s0 => [⟨.a2, .s19, .c0, .c2⟩] | .s1 => [⟨.a2, .s25, .c0, .c0⟩] | .s2 => [⟨.a2, .s30, .c1, .c2⟩] | .s3 => [⟨.a2, .s30, .c1, .c3⟩] | .s4 => [⟨.a2, .s30, .c0, .c3⟩] | .s5 => [⟨.a2, .s30, .c1, .c3⟩] | .s6 => [⟨.a2, .s30, .c1, .c3⟩] | .s7 => [⟨.a2, .s29, .c0, .c2⟩] | .s8 => [⟨.a2, .s30, .c1, .c3⟩] | .s9 => [⟨.a2, .s29, .c2, .c2⟩] | .s10 => [⟨.a2, .s30, .c0, .c3⟩] | .s11 => [⟨.a2, .s30, .c2, .c3⟩] | .s12 => [⟨.a2, .s30, .c0, .c3⟩] | .s13 => [⟨.a2, .s30, .c2, .c3⟩] | .s14 => [⟨.a2, .s30, .c1, .c3⟩] | .s15 => [⟨.a2, .s29, .c2, .c2⟩] | .s16 => [⟨.a2, .s30, .c1, .c3⟩] | .s17 => [⟨.a2, .s30, .c1, .c3⟩] | .s18 => [⟨.a2, .s30, .c1, .c3⟩] | .s19 => [⟨.a2, .s30, .c2, .c3⟩] | .s20 => [⟨.a2, .s30, .c0, .c3⟩] | .s21 => [⟨.a2, .s30, .c1, .c3⟩] | .s22 => [⟨.a2, .s30, .c0, .c3⟩] | .s23 => [⟨.a2, .s30, .c2, .c3⟩] | .s24 => [⟨.a2, .s30, .c2, .c3⟩] | .s25 => [⟨.a2, .s30, .c3, .c3⟩] | .s26 => [⟨.a2, .s30, .c2, .c3⟩] | .s27 => [⟨.a2, .s30, .c2, .c3⟩] | .s28 => [⟨.a2, .s30, .c2, .c3⟩] | .s29 => [⟨.a2, .s30, .c3, .c3⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c2⟩] | .s32 => [⟨.a2, .s30, .c2, .c2⟩] | .s33 => [⟨.a2, .s30, .c2, .c2⟩] | .s34 => [⟨.a2, .s30, .c2, .c3⟩] | .s35 => [⟨.a2, .s30, .c3, .c3⟩] | .s36 => [⟨.a2, .s30, .c2, .c2⟩] | .s37 => [⟨.a2, .s30, .c2, .c2⟩] | .s38 => []
private def listAbsApp_d23 : StateSN → List NFDesc | .s0 => [⟨.a2, .s19, .c0, .c2⟩] | .s1 => [⟨.a2, .s25, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d24 : StateSN → List NFDesc | .s0 => [⟨.a2, .s27, .c0, .c2⟩] | .s1 => [⟨.a2, .s25, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩] | .s3 => [⟨.a2, .s30, .c1, .c3⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c3⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c3⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c3⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c3⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c3⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d25 : StateSN → List NFDesc | .s0 => [⟨.a2, .s27, .c0, .c2⟩] | .s1 => [⟨.a2, .s25, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d26 : StateSN → List NFDesc | .s0 => [⟨.a2, .s31, .c0, .c2⟩] | .s1 => [⟨.a2, .s31, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩] | .s3 => [⟨.a2, .s30, .c1, .c3⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c3⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c3⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c3⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c3⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c3⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d27 : StateSN → List NFDesc | .s0 => [⟨.a2, .s31, .c0, .c2⟩] | .s1 => [⟨.a2, .s31, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d28 : StateSN → List NFDesc | .s0 => [⟨.a2, .s15, .c0, .c2⟩] | .s1 => [⟨.a2, .s25, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d29 : StateSN → List NFDesc | .s0 => [⟨.a2, .s15, .c0, .c2⟩] | .s1 => [⟨.a2, .s25, .c0, .c2⟩, ⟨.a2, .s25, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c2⟩, ⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d30 : StateSN → List NFDesc | .s0 => [⟨.a2, .s32, .c0, .c2⟩] | .s1 => [⟨.a2, .s31, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c3⟩, ⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c2⟩, ⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c2⟩, ⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c3⟩, ⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c3⟩, ⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c2⟩, ⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c3⟩, ⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c3⟩, ⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d31 : StateSN → List NFDesc | .s0 => [⟨.a2, .s36, .c0, .c2⟩] | .s1 => [⟨.a2, .s31, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩] | .s3 => [⟨.a2, .s30, .c1, .c3⟩] | .s4 => [⟨.a2, .s30, .c0, .c3⟩] | .s5 => [⟨.a2, .s30, .c1, .c3⟩] | .s6 => [⟨.a2, .s30, .c1, .c3⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c3⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c3⟩] | .s11 => [⟨.a2, .s30, .c2, .c3⟩] | .s12 => [⟨.a2, .s30, .c0, .c3⟩] | .s13 => [⟨.a2, .s30, .c2, .c3⟩] | .s14 => [⟨.a2, .s30, .c1, .c3⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c3⟩] | .s17 => [⟨.a2, .s30, .c1, .c3⟩] | .s18 => [⟨.a2, .s30, .c1, .c3⟩] | .s19 => [⟨.a2, .s30, .c2, .c3⟩] | .s20 => [⟨.a2, .s30, .c0, .c3⟩] | .s21 => [⟨.a2, .s30, .c1, .c3⟩] | .s22 => [⟨.a2, .s30, .c0, .c3⟩] | .s23 => [⟨.a2, .s30, .c2, .c3⟩] | .s24 => [⟨.a2, .s30, .c2, .c3⟩] | .s25 => [⟨.a2, .s30, .c3, .c3⟩] | .s26 => [⟨.a2, .s30, .c2, .c3⟩] | .s27 => [⟨.a2, .s30, .c2, .c3⟩] | .s28 => [⟨.a2, .s30, .c2, .c3⟩] | .s29 => [⟨.a2, .s30, .c3, .c3⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c3⟩] | .s32 => [⟨.a2, .s30, .c2, .c3⟩] | .s33 => [⟨.a2, .s30, .c2, .c3⟩] | .s34 => [⟨.a2, .s30, .c2, .c3⟩] | .s35 => [⟨.a2, .s30, .c3, .c3⟩] | .s36 => [⟨.a2, .s30, .c2, .c3⟩] | .s37 => [⟨.a2, .s30, .c2, .c3⟩] | .s38 => []
private def listAbsApp_d32 : StateSN → List NFDesc | .s0 => [⟨.a2, .s36, .c0, .c2⟩] | .s1 => [⟨.a2, .s31, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d33 : StateSN → List NFDesc | .s0 => [⟨.a2, .s37, .c0, .c2⟩] | .s1 => [⟨.a2, .s31, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩] | .s3 => [⟨.a2, .s30, .c1, .c3⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c3⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c3⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c3⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c3⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c3⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d34 : StateSN → List NFDesc | .s0 => [⟨.a2, .s37, .c0, .c2⟩] | .s1 => [⟨.a2, .s31, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d35 : StateSN → List NFDesc | .s0 => [⟨.a2, .s24, .c0, .c1⟩] | .s1 => [⟨.a2, .s29, .c1, .c2⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩] | .s3 => [⟨.a2, .s30, .c0, .c4⟩] | .s4 => [⟨.a2, .s30, .c1, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s30, .c1, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s30, .c0, .c4⟩] | .s10 => [⟨.a2, .s30, .c1, .c3⟩] | .s11 => [⟨.a2, .s30, .c0, .c4⟩] | .s12 => [⟨.a2, .s30, .c1, .c4⟩] | .s13 => [⟨.a2, .s30, .c0, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s30, .c0, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c0, .c4⟩] | .s20 => [⟨.a2, .s30, .c1, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c1, .c4⟩] | .s23 => [⟨.a2, .s30, .c1, .c4⟩] | .s24 => [⟨.a2, .s30, .c1, .c4⟩] | .s25 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s26 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s27 => [⟨.a2, .s30, .c1, .c4⟩] | .s28 => [⟨.a2, .s30, .c1, .c4⟩] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d36 : StateSN → List NFDesc | .s0 => [⟨.a2, .s24, .c0, .c2⟩] | .s1 => [⟨.a2, .s29, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s30, .c0, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d37 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩] | .s1 => [⟨.a2, .s29, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c3⟩] | .s3 => [⟨.a2, .s30, .c1, .c3⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c3⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c3⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d38 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩] | .s1 => [⟨.a2, .s29, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [⟨.a2, .s30, .c3, .c4⟩] | .s30 => [⟨.a2, .s30, .c4, .c4⟩] | .s31 => [⟨.a2, .s30, .c2, .c4⟩] | .s32 => [⟨.a2, .s30, .c2, .c4⟩] | .s33 => [⟨.a2, .s30, .c2, .c4⟩] | .s34 => [⟨.a2, .s30, .c2, .c4⟩] | .s35 => [⟨.a2, .s30, .c3, .c4⟩] | .s36 => [⟨.a2, .s30, .c2, .c4⟩] | .s37 => [⟨.a2, .s30, .c2, .c4⟩] | .s38 => []
private def listAbsApp_d39 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c1⟩] | .s1 => [⟨.a2, .s35, .c2, .c2⟩] | .s2 => [⟨.a2, .s30, .c2, .c3⟩] | .s3 => [⟨.a2, .s30, .c2, .c3⟩] | .s4 => [⟨.a2, .s30, .c1, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c2, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c1, .c3⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c1, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c3⟩, ⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c1, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d40 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩] | .s1 => [⟨.a2, .s29, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d41 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩] | .s1 => [⟨.a2, .s29, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s29, .c0, .c3⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s29, .c2, .c3⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s29, .c2, .c3⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d42 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c0⟩] | .s1 => [⟨.a2, .s30, .c0, .c2⟩] | .s2 => [⟨.a2, .s30, .c2, .c3⟩] | .s3 => [⟨.a2, .s30, .c3, .c4⟩] | .s4 => [⟨.a2, .s30, .c3, .c4⟩] | .s5 => [⟨.a2, .s30, .c3, .c4⟩] | .s6 => [⟨.a2, .s30, .c3, .c4⟩] | .s7 => [⟨.a2, .s30, .c2, .c4⟩] | .s8 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩] | .s10 => [⟨.a2, .s30, .c3, .c3⟩] | .s11 => [⟨.a2, .s30, .c3, .c4⟩] | .s12 => [⟨.a2, .s30, .c3, .c4⟩] | .s13 => [⟨.a2, .s30, .c3, .c4⟩] | .s14 => [⟨.a2, .s30, .c3, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩] | .s16 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s17 => [⟨.a2, .s30, .c3, .c4⟩] | .s18 => [⟨.a2, .s30, .c3, .c4⟩] | .s19 => [⟨.a2, .s30, .c3, .c4⟩] | .s20 => [⟨.a2, .s30, .c3, .c4⟩] | .s21 => [⟨.a2, .s30, .c3, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [⟨.a2, .s30, .c3, .c4⟩] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d43 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s30, .c0, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d44 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c1⟩, ⟨.a2, .s30, .c3, .c1⟩] | .s1 => [⟨.a2, .s30, .c2, .c2⟩, ⟨.a2, .s30, .c3, .c3⟩] | .s2 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s3 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s4 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s5 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s6 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s7 => [⟨.a2, .s30, .c3, .c4⟩] | .s8 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s9 => [⟨.a2, .s30, .c3, .c4⟩] | .s10 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s11 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s12 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s13 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s14 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s15 => [⟨.a2, .s30, .c3, .c4⟩] | .s16 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s17 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s18 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s19 => [] | .s20 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s21 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d45 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c1⟩, ⟨.a2, .s30, .c3, .c1⟩, ⟨.a2, .s30, .c4, .c1⟩] | .s1 => [⟨.a2, .s30, .c2, .c2⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s2 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s3 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s4 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s5 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s6 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s7 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s8 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s10 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s11 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s12 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s13 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s14 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s16 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s17 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s18 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s19 => [] | .s20 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s21 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d46 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c0⟩, ⟨.a2, .s30, .c2, .c1⟩, ⟨.a2, .s30, .c3, .c1⟩, ⟨.a2, .s30, .c4, .c1⟩] | .s1 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s2 => [⟨.a2, .s30, .c4, .c4⟩] | .s3 => [⟨.a2, .s30, .c4, .c4⟩] | .s4 => [⟨.a2, .s30, .c4, .c4⟩] | .s5 => [⟨.a2, .s30, .c4, .c4⟩] | .s6 => [⟨.a2, .s30, .c4, .c4⟩] | .s7 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s8 => [⟨.a2, .s30, .c4, .c4⟩] | .s9 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s10 => [⟨.a2, .s30, .c4, .c4⟩] | .s11 => [⟨.a2, .s30, .c4, .c4⟩] | .s12 => [⟨.a2, .s30, .c4, .c4⟩] | .s13 => [⟨.a2, .s30, .c4, .c4⟩] | .s14 => [⟨.a2, .s30, .c4, .c4⟩] | .s15 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s16 => [⟨.a2, .s30, .c4, .c4⟩] | .s17 => [⟨.a2, .s30, .c4, .c4⟩] | .s18 => [⟨.a2, .s30, .c4, .c4⟩] | .s19 => [] | .s20 => [⟨.a2, .s30, .c4, .c4⟩] | .s21 => [⟨.a2, .s30, .c4, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d47 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c1⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s7 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s19 => [] | .s20 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d48 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c2, .c0⟩] | .s1 => [⟨.a2, .s30, .c2, .c2⟩] | .s2 => [⟨.a2, .s30, .c3, .c3⟩] | .s3 => [⟨.a2, .s30, .c4, .c4⟩] | .s4 => [⟨.a2, .s30, .c4, .c4⟩] | .s5 => [⟨.a2, .s30, .c4, .c4⟩] | .s6 => [⟨.a2, .s30, .c4, .c4⟩] | .s7 => [⟨.a2, .s30, .c3, .c4⟩] | .s8 => [⟨.a2, .s30, .c4, .c4⟩] | .s9 => [⟨.a2, .s30, .c3, .c4⟩] | .s10 => [⟨.a2, .s30, .c4, .c4⟩] | .s11 => [⟨.a2, .s30, .c4, .c4⟩] | .s12 => [⟨.a2, .s30, .c4, .c4⟩] | .s13 => [⟨.a2, .s30, .c4, .c4⟩] | .s14 => [⟨.a2, .s30, .c4, .c4⟩] | .s15 => [⟨.a2, .s30, .c3, .c4⟩] | .s16 => [⟨.a2, .s30, .c4, .c4⟩] | .s17 => [⟨.a2, .s30, .c4, .c4⟩] | .s18 => [⟨.a2, .s30, .c4, .c4⟩] | .s19 => [] | .s20 => [⟨.a2, .s30, .c4, .c4⟩] | .s21 => [⟨.a2, .s30, .c4, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d49 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩, ⟨.a2, .s29, .c2, .c0⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c2, .c2⟩, ⟨.a2, .s30, .c3, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s7 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s19 => [] | .s20 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d50 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s30, .c0, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [⟨.a2, .s30, .c2, .c4⟩] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [⟨.a2, .s30, .c0, .c4⟩] | .s23 => [⟨.a2, .s30, .c2, .c4⟩] | .s24 => [⟨.a2, .s30, .c2, .c4⟩] | .s25 => [⟨.a2, .s30, .c3, .c4⟩] | .s26 => [⟨.a2, .s30, .c2, .c4⟩] | .s27 => [⟨.a2, .s30, .c2, .c4⟩] | .s28 => [⟨.a2, .s30, .c2, .c4⟩] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d51 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c1, .c2⟩] | .s1 => [⟨.a2, .s30, .c2, .c3⟩] | .s2 => [⟨.a2, .s30, .c3, .c4⟩] | .s3 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s4 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s5 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s6 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s7 => [⟨.a2, .s30, .c4, .c4⟩] | .s8 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s9 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s10 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s11 => [⟨.a2, .s30, .c4, .c4⟩] | .s12 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s13 => [⟨.a2, .s30, .c4, .c4⟩] | .s14 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s15 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s16 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s17 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s18 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s19 => [⟨.a2, .s30, .c4, .c4⟩] | .s20 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s21 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s22 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s23 => [⟨.a2, .s30, .c4, .c4⟩] | .s24 => [⟨.a2, .s30, .c4, .c4⟩] | .s25 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s26 => [⟨.a2, .s30, .c4, .c4⟩] | .s27 => [⟨.a2, .s30, .c4, .c4⟩] | .s28 => [⟨.a2, .s30, .c4, .c4⟩] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d52 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩] | .s1 => [⟨.a2, .s29, .c0, .c3⟩] | .s2 => [⟨.a2, .s30, .c1, .c4⟩] | .s3 => [⟨.a2, .s30, .c1, .c4⟩] | .s4 => [⟨.a2, .s30, .c0, .c4⟩] | .s5 => [⟨.a2, .s30, .c1, .c4⟩] | .s6 => [⟨.a2, .s30, .c1, .c4⟩] | .s7 => [⟨.a2, .s30, .c0, .c4⟩] | .s8 => [⟨.a2, .s30, .c1, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩] | .s10 => [⟨.a2, .s30, .c0, .c4⟩] | .s11 => [⟨.a2, .s30, .c2, .c4⟩] | .s12 => [⟨.a2, .s30, .c0, .c4⟩] | .s13 => [⟨.a2, .s30, .c2, .c4⟩] | .s14 => [⟨.a2, .s30, .c1, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩] | .s16 => [⟨.a2, .s30, .c1, .c4⟩] | .s17 => [⟨.a2, .s30, .c1, .c4⟩] | .s18 => [⟨.a2, .s30, .c1, .c4⟩] | .s19 => [] | .s20 => [⟨.a2, .s30, .c0, .c4⟩] | .s21 => [⟨.a2, .s30, .c1, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d53 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c1, .c4⟩] | .s1 => [⟨.a2, .s29, .c2, .c3⟩] | .s2 => [⟨.a2, .s30, .c3, .c4⟩] | .s3 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s4 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s5 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s6 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s7 => [⟨.a2, .s30, .c3, .c4⟩] | .s8 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s9 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s10 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s11 => [⟨.a2, .s30, .c4, .c4⟩] | .s12 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s13 => [⟨.a2, .s30, .c4, .c4⟩] | .s14 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s15 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s16 => [⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s17 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s18 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s19 => [] | .s20 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s21 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d54 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c2, .c2⟩, ⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d55 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c2⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d56 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c2⟩, ⟨.a2, .s30, .c3, .c1⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d57 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c3, .c1⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c1⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d58 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d59 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d60 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d61 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c2⟩, ⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c2, .c2⟩, ⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d62 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d63 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d64 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d65 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d66 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d67 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d68 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d69 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d70 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d71 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d72 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d73 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d74 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d75 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d76 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d77 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d78 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d79 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d80 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d81 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d82 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d83 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d84 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d85 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d86 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d87 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d88 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d89 : StateSN → List NFDesc | .s0 => [] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d90 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c2, .c1⟩, ⟨.a2, .s30, .c3, .c1⟩, ⟨.a2, .s30, .c4, .c1⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d91 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c2, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s1 => [⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d92 : StateSN → List NFDesc | .s0 => [⟨.a2, .s30, .c0, .c4⟩] | .s1 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d93 : StateSN → List NFDesc | .s0 => [⟨.a2, .s26, .c0, .c2⟩] | .s1 => [⟨.a2, .s30, .c2, .c3⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d94 : StateSN → List NFDesc | .s0 => [⟨.a2, .s26, .c0, .c2⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d95 : StateSN → List NFDesc | .s0 => [⟨.a2, .s34, .c0, .c2⟩] | .s1 => [⟨.a2, .s30, .c2, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d96 : StateSN → List NFDesc | .s0 => [⟨.a2, .s34, .c0, .c2⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d97 : StateSN → List NFDesc | .s0 => [⟨.a2, .s35, .c2, .c2⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d98 : StateSN → List NFDesc | .s0 => [⟨.a2, .s35, .c0, .c3⟩, ⟨.a2, .s35, .c2, .c2⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d99 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d100 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c2, .c3⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d101 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c2, .c3⟩] | .s1 => [] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d102 : StateSN → List NFDesc | .s0 => [⟨.a2, .s25, .c0, .c3⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d103 : StateSN → List NFDesc | .s0 => [⟨.a2, .s25, .c0, .c2⟩, ⟨.a2, .s25, .c0, .c3⟩] | .s1 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d104 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c3⟩] | .s1 => [⟨.a2, .s30, .c0, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_d105 : StateSN → List NFDesc | .s0 => [⟨.a2, .s29, .c0, .c2⟩, ⟨.a2, .s29, .c0, .c3⟩] | .s1 => [⟨.a2, .s30, .c1, .c4⟩, ⟨.a2, .s30, .c2, .c4⟩, ⟨.a2, .s30, .c3, .c3⟩, ⟨.a2, .s30, .c3, .c4⟩, ⟨.a2, .s30, .c4, .c4⟩] | .s2 => [] | .s3 => [] | .s4 => [] | .s5 => [] | .s6 => [] | .s7 => [] | .s8 => [] | .s9 => [] | .s10 => [] | .s11 => [] | .s12 => [] | .s13 => [] | .s14 => [] | .s15 => [] | .s16 => [] | .s17 => [] | .s18 => [] | .s19 => [] | .s20 => [] | .s21 => [] | .s22 => [] | .s23 => [] | .s24 => [] | .s25 => [] | .s26 => [] | .s27 => [] | .s28 => [] | .s29 => [] | .s30 => [] | .s31 => [] | .s32 => [] | .s33 => [] | .s34 => [] | .s35 => [] | .s36 => [] | .s37 => [] | .s38 => []
private def listAbsApp_s0 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a0, .c0, .c0 => listAbsApp_d0
  | _, _, _ => emptyDescList
private def listAbsApp_s1 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c0, .c0 => listAbsApp_d1
  | _, _, _ => emptyDescList
private def listAbsApp_s2 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c0, .c0 => listAbsApp_d2
  | _, _, _ => emptyDescList
private def listAbsApp_s3 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c1, .c0 => listAbsApp_d3
  | _, _, _ => emptyDescList
private def listAbsApp_s4 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c1, .c0 => listAbsApp_d4
  | .a1, .c2, .c0 => listAbsApp_d5
  | _, _, _ => emptyDescList
private def listAbsApp_s5 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c0, .c0 => listAbsApp_d6
  | .a1, .c1, .c0 => listAbsApp_d7
  | .a2, .c0, .c1 => listAbsApp_d18
  | _, _, _ => emptyDescList
private def listAbsApp_s6 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c0, .c0 => listAbsApp_d8
  | .a1, .c1, .c0 => listAbsApp_d9
  | .a1, .c2, .c0 => listAbsApp_d10
  | .a1, .c3, .c0 => listAbsApp_d11
  | .a1, .c4, .c0 => listAbsApp_d12
  | .a2, .c0, .c1 => listAbsApp_d19
  | _, _, _ => emptyDescList
private def listAbsApp_s7 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d20
  | _, _, _ => emptyDescList
private def listAbsApp_s8 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c0, .c0 => listAbsApp_d13
  | _, _, _ => emptyDescList
private def listAbsApp_s9 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d21
  | _, _, _ => emptyDescList
private def listAbsApp_s10 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c2, .c0 => listAbsApp_d14
  | _, _, _ => emptyDescList
private def listAbsApp_s11 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c1 => listAbsApp_d22
  | .a2, .c0, .c2 => listAbsApp_d23
  | _, _, _ => emptyDescList
private def listAbsApp_s12 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c2, .c0 => listAbsApp_d15
  | _, _, _ => emptyDescList
private def listAbsApp_s13 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c1 => listAbsApp_d24
  | .a2, .c0, .c2 => listAbsApp_d25
  | _, _, _ => emptyDescList
private def listAbsApp_s14 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d26
  | .a2, .c0, .c1 => listAbsApp_d27
  | _, _, _ => emptyDescList
private def listAbsApp_s15 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d28
  | .a2, .c0, .c2 => listAbsApp_d29
  | _, _, _ => emptyDescList
private def listAbsApp_s16 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c1 => listAbsApp_d30
  | _, _, _ => emptyDescList
private def listAbsApp_s17 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d31
  | .a2, .c0, .c1 => listAbsApp_d32
  | _, _, _ => emptyDescList
private def listAbsApp_s18 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d33
  | .a2, .c0, .c1 => listAbsApp_d34
  | _, _, _ => emptyDescList
private def listAbsApp_s19 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d35
  | .a2, .c0, .c2 => listAbsApp_d36
  | _, _, _ => emptyDescList
private def listAbsApp_s20 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c2, .c0 => listAbsApp_d16
  | _, _, _ => emptyDescList
private def listAbsApp_s21 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a1, .c2, .c0 => listAbsApp_d17
  | .a2, .c0, .c0 => listAbsApp_d37
  | .a2, .c0, .c1 => listAbsApp_d38
  | _, _, _ => emptyDescList
private def listAbsApp_s22 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d39
  | _, _, _ => emptyDescList
private def listAbsApp_s23 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d40
  | .a2, .c0, .c2 => listAbsApp_d41
  | _, _, _ => emptyDescList
private def listAbsApp_s24 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c1 => listAbsApp_d42
  | .a2, .c0, .c2 => listAbsApp_d43
  | _, _, _ => emptyDescList
private def listAbsApp_s25 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d44
  | .a2, .c0, .c1 => listAbsApp_d45
  | .a2, .c0, .c2 => listAbsApp_d46
  | .a2, .c0, .c3 => listAbsApp_d47
  | _, _, _ => emptyDescList
private def listAbsApp_s26 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d48
  | .a2, .c0, .c2 => listAbsApp_d49
  | _, _, _ => emptyDescList
private def listAbsApp_s27 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c2 => listAbsApp_d50
  | .a2, .c1, .c0 => listAbsApp_d51
  | _, _, _ => emptyDescList
private def listAbsApp_s28 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c2 => listAbsApp_d52
  | .a2, .c1, .c0 => listAbsApp_d53
  | _, _, _ => emptyDescList
private def listAbsApp_s29 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d54
  | .a2, .c0, .c1 => listAbsApp_d55
  | .a2, .c0, .c2 => listAbsApp_d56
  | .a2, .c0, .c3 => listAbsApp_d57
  | .a2, .c1, .c0 => listAbsApp_d58
  | .a2, .c1, .c1 => listAbsApp_d59
  | .a2, .c1, .c2 => listAbsApp_d60
  | .a2, .c2, .c0 => listAbsApp_d61
  | .a2, .c2, .c1 => listAbsApp_d62
  | .a2, .c2, .c2 => listAbsApp_d63
  | .a2, .c2, .c3 => listAbsApp_d64
  | _, _, _ => emptyDescList
private def listAbsApp_s30 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d65
  | .a2, .c0, .c1 => listAbsApp_d66
  | .a2, .c0, .c2 => listAbsApp_d67
  | .a2, .c0, .c3 => listAbsApp_d68
  | .a2, .c0, .c4 => listAbsApp_d69
  | .a2, .c1, .c0 => listAbsApp_d70
  | .a2, .c1, .c1 => listAbsApp_d71
  | .a2, .c1, .c2 => listAbsApp_d72
  | .a2, .c1, .c3 => listAbsApp_d73
  | .a2, .c1, .c4 => listAbsApp_d74
  | .a2, .c2, .c0 => listAbsApp_d75
  | .a2, .c2, .c1 => listAbsApp_d76
  | .a2, .c2, .c2 => listAbsApp_d77
  | .a2, .c2, .c3 => listAbsApp_d78
  | .a2, .c2, .c4 => listAbsApp_d79
  | .a2, .c3, .c0 => listAbsApp_d80
  | .a2, .c3, .c1 => listAbsApp_d81
  | .a2, .c3, .c2 => listAbsApp_d82
  | .a2, .c3, .c3 => listAbsApp_d83
  | .a2, .c3, .c4 => listAbsApp_d84
  | .a2, .c4, .c0 => listAbsApp_d85
  | .a2, .c4, .c1 => listAbsApp_d86
  | .a2, .c4, .c2 => listAbsApp_d87
  | .a2, .c4, .c3 => listAbsApp_d88
  | .a2, .c4, .c4 => listAbsApp_d89
  | _, _, _ => emptyDescList
private def listAbsApp_s31 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c2 => listAbsApp_d90
  | .a2, .c1, .c0 => listAbsApp_d91
  | .a2, .c2, .c0 => listAbsApp_d92
  | _, _, _ => emptyDescList
private def listAbsApp_s32 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d93
  | .a2, .c0, .c2 => listAbsApp_d94
  | _, _, _ => emptyDescList
private def listAbsApp_s33 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d95
  | .a2, .c0, .c2 => listAbsApp_d96
  | _, _, _ => emptyDescList
private def listAbsApp_s34 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c0 => listAbsApp_d97
  | .a2, .c0, .c2 => listAbsApp_d98
  | _, _, _ => emptyDescList
private def listAbsApp_s35 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c3 => listAbsApp_d99
  | .a2, .c2, .c0 => listAbsApp_d100
  | .a2, .c2, .c2 => listAbsApp_d101
  | _, _, _ => emptyDescList
private def listAbsApp_s36 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c2 => listAbsApp_d102
  | .a2, .c2, .c0 => listAbsApp_d103
  | _, _, _ => emptyDescList
private def listAbsApp_s37 : Arity3 → ChildTag → ChildTag → StateSN → List NFDesc
  | .a2, .c0, .c2 => listAbsApp_d104
  | .a2, .c2, .c0 => listAbsApp_d105
  | _, _, _ => emptyDescList
def listAbsApp (u : NFDesc) : StateSN → List NFDesc :=
  match u.st with
  | .s0 => listAbsApp_s0 u.sl u.tx u.ty
  | .s1 => listAbsApp_s1 u.sl u.tx u.ty
  | .s2 => listAbsApp_s2 u.sl u.tx u.ty
  | .s3 => listAbsApp_s3 u.sl u.tx u.ty
  | .s4 => listAbsApp_s4 u.sl u.tx u.ty
  | .s5 => listAbsApp_s5 u.sl u.tx u.ty
  | .s6 => listAbsApp_s6 u.sl u.tx u.ty
  | .s7 => listAbsApp_s7 u.sl u.tx u.ty
  | .s8 => listAbsApp_s8 u.sl u.tx u.ty
  | .s9 => listAbsApp_s9 u.sl u.tx u.ty
  | .s10 => listAbsApp_s10 u.sl u.tx u.ty
  | .s11 => listAbsApp_s11 u.sl u.tx u.ty
  | .s12 => listAbsApp_s12 u.sl u.tx u.ty
  | .s13 => listAbsApp_s13 u.sl u.tx u.ty
  | .s14 => listAbsApp_s14 u.sl u.tx u.ty
  | .s15 => listAbsApp_s15 u.sl u.tx u.ty
  | .s16 => listAbsApp_s16 u.sl u.tx u.ty
  | .s17 => listAbsApp_s17 u.sl u.tx u.ty
  | .s18 => listAbsApp_s18 u.sl u.tx u.ty
  | .s19 => listAbsApp_s19 u.sl u.tx u.ty
  | .s20 => listAbsApp_s20 u.sl u.tx u.ty
  | .s21 => listAbsApp_s21 u.sl u.tx u.ty
  | .s22 => listAbsApp_s22 u.sl u.tx u.ty
  | .s23 => listAbsApp_s23 u.sl u.tx u.ty
  | .s24 => listAbsApp_s24 u.sl u.tx u.ty
  | .s25 => listAbsApp_s25 u.sl u.tx u.ty
  | .s26 => listAbsApp_s26 u.sl u.tx u.ty
  | .s27 => listAbsApp_s27 u.sl u.tx u.ty
  | .s28 => listAbsApp_s28 u.sl u.tx u.ty
  | .s29 => listAbsApp_s29 u.sl u.tx u.ty
  | .s30 => listAbsApp_s30 u.sl u.tx u.ty
  | .s31 => listAbsApp_s31 u.sl u.tx u.ty
  | .s32 => listAbsApp_s32 u.sl u.tx u.ty
  | .s33 => listAbsApp_s33 u.sl u.tx u.ty
  | .s34 => listAbsApp_s34 u.sl u.tx u.ty
  | .s35 => listAbsApp_s35 u.sl u.tx u.ty
  | .s36 => listAbsApp_s36 u.sl u.tx u.ty
  | .s37 => listAbsApp_s37 u.sl u.tx u.ty
  | .s38 => emptyDescList

private def zeroRank (_ : StateSN) : Nat := 0

private def c3Rank_d0 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 0 | .s20 => 0 | .s21 => 0 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 3 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 3 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_s19 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d0
  | _, _, _ => zeroRank
private def c3Rank_d1 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 0 | .s20 => 0 | .s21 => 0 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 3 | .s27 => 0 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 3 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_s22 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d1
  | _, _, _ => zeroRank
private def c3Rank_d2 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 0 | .s20 => 0 | .s21 => 0 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 2 | .s27 => 0 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 2 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_s24 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c1 => c3Rank_d2
  | _, _, _ => zeroRank
private def c3Rank_d3 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 1 | .s20 => 0 | .s21 => 0 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 2 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 2 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d4 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 1 | .s20 => 0 | .s21 => 0 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 2 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 2 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d5 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 1 | .s20 => 0 | .s21 => 0 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 2 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 2 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_s25 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d3
  | .a2, .c0, .c1 => c3Rank_d4
  | .a2, .c0, .c2 => c3Rank_d5
  | _, _, _ => zeroRank
private def c3Rank_d6 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 1 | .s20 => 0 | .s21 => 0 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 2 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 2 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d7 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 1 | .s20 => 0 | .s21 => 0 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 2 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 2 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_s26 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d6
  | .a2, .c0, .c2 => c3Rank_d7
  | _, _, _ => zeroRank
private def c3Rank_d8 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 0 | .s20 => 0 | .s21 => 0 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 3 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 3 | .s35 => 3 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_s27 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c1, .c0 => c3Rank_d8
  | _, _, _ => zeroRank
private def c3Rank_d9 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 0 | .s3 => 0 | .s4 => 0 | .s5 => 0 | .s6 => 0 | .s7 => 0 | .s8 => 0 | .s9 => 0 | .s10 => 0 | .s11 => 0 | .s12 => 0 | .s13 => 0 | .s14 => 0 | .s15 => 0 | .s16 => 0 | .s17 => 0 | .s18 => 0 | .s19 => 2 | .s20 => 0 | .s21 => 0 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 3 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 3 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_s28 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c1, .c0 => c3Rank_d9
  | _, _, _ => zeroRank
private def c3Rank_d10 : StateSN → Nat | .s0 => 0 | .s1 => 4 | .s2 => 3 | .s3 => 5 | .s4 => 4 | .s5 => 3 | .s6 => 3 | .s7 => 4 | .s8 => 3 | .s9 => 3 | .s10 => 4 | .s11 => 3 | .s12 => 4 | .s13 => 3 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 3 | .s20 => 4 | .s21 => 3 | .s22 => 4 | .s23 => 3 | .s24 => 3 | .s25 => 3 | .s26 => 3 | .s27 => 3 | .s28 => 3 | .s29 => 3 | .s30 => 1 | .s31 => 3 | .s32 => 3 | .s33 => 3 | .s34 => 3 | .s35 => 3 | .s36 => 3 | .s37 => 3 | .s38 => 0
private def c3Rank_d11 : StateSN → Nat | .s0 => 0 | .s1 => 2 | .s2 => 3 | .s3 => 4 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 3 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 1 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_d12 : StateSN → Nat | .s0 => 0 | .s1 => 2 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 2 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 1 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_d13 : StateSN → Nat | .s0 => 0 | .s1 => 2 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 2 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 0 | .s20 => 2 | .s21 => 2 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_d14 : StateSN → Nat | .s0 => 0 | .s1 => 4 | .s2 => 5 | .s3 => 3 | .s4 => 4 | .s5 => 3 | .s6 => 3 | .s7 => 4 | .s8 => 3 | .s9 => 3 | .s10 => 4 | .s11 => 3 | .s12 => 4 | .s13 => 3 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 3 | .s20 => 4 | .s21 => 3 | .s22 => 4 | .s23 => 3 | .s24 => 3 | .s25 => 3 | .s26 => 3 | .s27 => 3 | .s28 => 3 | .s29 => 3 | .s30 => 1 | .s31 => 3 | .s32 => 3 | .s33 => 3 | .s34 => 3 | .s35 => 3 | .s36 => 3 | .s37 => 3 | .s38 => 0
private def c3Rank_d15 : StateSN → Nat | .s0 => 0 | .s1 => 3 | .s2 => 3 | .s3 => 2 | .s4 => 4 | .s5 => 2 | .s6 => 2 | .s7 => 4 | .s8 => 2 | .s9 => 3 | .s10 => 4 | .s11 => 2 | .s12 => 4 | .s13 => 2 | .s14 => 2 | .s15 => 3 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 4 | .s21 => 2 | .s22 => 4 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 3 | .s32 => 3 | .s33 => 3 | .s34 => 2 | .s35 => 1 | .s36 => 3 | .s37 => 3 | .s38 => 0
private def c3Rank_d16 : StateSN → Nat | .s0 => 0 | .s1 => 4 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 4 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 1 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_d17 : StateSN → Nat | .s0 => 0 | .s1 => 3 | .s2 => 3 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 2 | .s8 => 3 | .s9 => 2 | .s10 => 3 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 3 | .s17 => 2 | .s18 => 2 | .s19 => 1 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 1 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 1 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d18 : StateSN → Nat | .s0 => 0 | .s1 => 3 | .s2 => 3 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 3 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 1 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d19 : StateSN → Nat | .s0 => 0 | .s1 => 3 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 3 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 1 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 1 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 1 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d20 : StateSN → Nat | .s0 => 0 | .s1 => 2 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 2 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 0 | .s20 => 2 | .s21 => 2 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_s29 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d10
  | .a2, .c0, .c1 => c3Rank_d11
  | .a2, .c0, .c2 => c3Rank_d12
  | .a2, .c0, .c3 => c3Rank_d13
  | .a2, .c1, .c0 => c3Rank_d14
  | .a2, .c1, .c1 => c3Rank_d15
  | .a2, .c1, .c2 => c3Rank_d16
  | .a2, .c2, .c0 => c3Rank_d17
  | .a2, .c2, .c1 => c3Rank_d18
  | .a2, .c2, .c2 => c3Rank_d19
  | .a2, .c2, .c3 => c3Rank_d20
  | _, _, _ => zeroRank
private def c3Rank_d21 : StateSN → Nat | .s0 => 5 | .s1 => 4 | .s2 => 3 | .s3 => 3 | .s4 => 4 | .s5 => 3 | .s6 => 3 | .s7 => 4 | .s8 => 3 | .s9 => 3 | .s10 => 4 | .s11 => 3 | .s12 => 4 | .s13 => 3 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 3 | .s20 => 4 | .s21 => 3 | .s22 => 4 | .s23 => 3 | .s24 => 3 | .s25 => 2 | .s26 => 3 | .s27 => 3 | .s28 => 3 | .s29 => 2 | .s30 => 1 | .s31 => 3 | .s32 => 3 | .s33 => 3 | .s34 => 3 | .s35 => 2 | .s36 => 3 | .s37 => 3 | .s38 => 0
private def c3Rank_d22 : StateSN → Nat | .s0 => 4 | .s1 => 5 | .s2 => 3 | .s3 => 2 | .s4 => 4 | .s5 => 2 | .s6 => 2 | .s7 => 4 | .s8 => 2 | .s9 => 3 | .s10 => 4 | .s11 => 2 | .s12 => 4 | .s13 => 2 | .s14 => 2 | .s15 => 3 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 4 | .s21 => 2 | .s22 => 4 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 3 | .s32 => 3 | .s33 => 3 | .s34 => 2 | .s35 => 1 | .s36 => 3 | .s37 => 3 | .s38 => 0
private def c3Rank_d23 : StateSN → Nat | .s0 => 4 | .s1 => 4 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 4 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 1 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_d24 : StateSN → Nat | .s0 => 4 | .s1 => 2 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 2 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 0 | .s20 => 2 | .s21 => 2 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_d25 : StateSN → Nat | .s0 => 5 | .s1 => 4 | .s2 => 3 | .s3 => 5 | .s4 => 4 | .s5 => 3 | .s6 => 3 | .s7 => 4 | .s8 => 3 | .s9 => 3 | .s10 => 4 | .s11 => 3 | .s12 => 4 | .s13 => 3 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 3 | .s20 => 4 | .s21 => 3 | .s22 => 4 | .s23 => 3 | .s24 => 3 | .s25 => 3 | .s26 => 3 | .s27 => 3 | .s28 => 3 | .s29 => 3 | .s30 => 1 | .s31 => 3 | .s32 => 3 | .s33 => 3 | .s34 => 3 | .s35 => 3 | .s36 => 3 | .s37 => 3 | .s38 => 0
private def c3Rank_d26 : StateSN → Nat | .s0 => 4 | .s1 => 5 | .s2 => 3 | .s3 => 2 | .s4 => 4 | .s5 => 2 | .s6 => 2 | .s7 => 4 | .s8 => 2 | .s9 => 3 | .s10 => 4 | .s11 => 2 | .s12 => 4 | .s13 => 2 | .s14 => 2 | .s15 => 3 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 4 | .s21 => 2 | .s22 => 4 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 3 | .s32 => 3 | .s33 => 3 | .s34 => 2 | .s35 => 1 | .s36 => 3 | .s37 => 3 | .s38 => 0
private def c3Rank_d27 : StateSN → Nat | .s0 => 5 | .s1 => 4 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 4 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 1 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_d28 : StateSN → Nat | .s0 => 4 | .s1 => 2 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 2 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 0 | .s20 => 2 | .s21 => 2 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_d29 : StateSN → Nat | .s0 => 5 | .s1 => 3 | .s2 => 2 | .s3 => 1 | .s4 => 1 | .s5 => 1 | .s6 => 1 | .s7 => 3 | .s8 => 2 | .s9 => 3 | .s10 => 2 | .s11 => 1 | .s12 => 1 | .s13 => 1 | .s14 => 1 | .s15 => 3 | .s16 => 2 | .s17 => 1 | .s18 => 1 | .s19 => 1 | .s20 => 1 | .s21 => 1 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 1 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 1 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d30 : StateSN → Nat | .s0 => 3 | .s1 => 3 | .s2 => 2 | .s3 => 1 | .s4 => 1 | .s5 => 1 | .s6 => 1 | .s7 => 3 | .s8 => 1 | .s9 => 2 | .s10 => 1 | .s11 => 1 | .s12 => 1 | .s13 => 1 | .s14 => 1 | .s15 => 2 | .s16 => 1 | .s17 => 1 | .s18 => 1 | .s19 => 1 | .s20 => 1 | .s21 => 1 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 1 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 1 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d31 : StateSN → Nat | .s0 => 4 | .s1 => 3 | .s2 => 2 | .s3 => 1 | .s4 => 1 | .s5 => 1 | .s6 => 1 | .s7 => 2 | .s8 => 1 | .s9 => 2 | .s10 => 1 | .s11 => 1 | .s12 => 1 | .s13 => 1 | .s14 => 1 | .s15 => 2 | .s16 => 1 | .s17 => 1 | .s18 => 1 | .s19 => 1 | .s20 => 1 | .s21 => 1 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 1 | .s27 => 1 | .s28 => 1 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_d32 : StateSN → Nat | .s0 => 2 | .s1 => 2 | .s2 => 2 | .s3 => 1 | .s4 => 1 | .s5 => 1 | .s6 => 1 | .s7 => 2 | .s8 => 1 | .s9 => 2 | .s10 => 1 | .s11 => 1 | .s12 => 1 | .s13 => 1 | .s14 => 1 | .s15 => 2 | .s16 => 1 | .s17 => 1 | .s18 => 1 | .s19 => 0 | .s20 => 1 | .s21 => 1 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_d33 : StateSN → Nat | .s0 => 5 | .s1 => 3 | .s2 => 2 | .s3 => 1 | .s4 => 1 | .s5 => 1 | .s6 => 1 | .s7 => 1 | .s8 => 2 | .s9 => 1 | .s10 => 2 | .s11 => 1 | .s12 => 1 | .s13 => 1 | .s14 => 1 | .s15 => 1 | .s16 => 2 | .s17 => 1 | .s18 => 1 | .s19 => 0 | .s20 => 1 | .s21 => 1 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_d34 : StateSN → Nat | .s0 => 3 | .s1 => 2 | .s2 => 1 | .s3 => 1 | .s4 => 1 | .s5 => 1 | .s6 => 1 | .s7 => 1 | .s8 => 1 | .s9 => 1 | .s10 => 1 | .s11 => 1 | .s12 => 1 | .s13 => 1 | .s14 => 1 | .s15 => 1 | .s16 => 1 | .s17 => 1 | .s18 => 1 | .s19 => 0 | .s20 => 1 | .s21 => 1 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_d35 : StateSN → Nat | .s0 => 4 | .s1 => 2 | .s2 => 1 | .s3 => 1 | .s4 => 1 | .s5 => 1 | .s6 => 1 | .s7 => 1 | .s8 => 1 | .s9 => 1 | .s10 => 1 | .s11 => 1 | .s12 => 1 | .s13 => 1 | .s14 => 1 | .s15 => 1 | .s16 => 1 | .s17 => 1 | .s18 => 1 | .s19 => 0 | .s20 => 1 | .s21 => 1 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_d36 : StateSN → Nat | .s0 => 2 | .s1 => 1 | .s2 => 1 | .s3 => 1 | .s4 => 1 | .s5 => 1 | .s6 => 1 | .s7 => 1 | .s8 => 1 | .s9 => 1 | .s10 => 1 | .s11 => 1 | .s12 => 1 | .s13 => 1 | .s14 => 1 | .s15 => 1 | .s16 => 1 | .s17 => 1 | .s18 => 1 | .s19 => 0 | .s20 => 1 | .s21 => 1 | .s22 => 0 | .s23 => 0 | .s24 => 0 | .s25 => 0 | .s26 => 0 | .s27 => 0 | .s28 => 0 | .s29 => 0 | .s30 => 0 | .s31 => 0 | .s32 => 0 | .s33 => 0 | .s34 => 0 | .s35 => 0 | .s36 => 0 | .s37 => 0 | .s38 => 0
private def c3Rank_s30 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d21
  | .a2, .c0, .c1 => c3Rank_d22
  | .a2, .c0, .c2 => c3Rank_d23
  | .a2, .c0, .c3 => c3Rank_d24
  | .a2, .c1, .c0 => c3Rank_d25
  | .a2, .c1, .c1 => c3Rank_d26
  | .a2, .c1, .c2 => c3Rank_d27
  | .a2, .c1, .c3 => c3Rank_d28
  | .a2, .c2, .c0 => c3Rank_d29
  | .a2, .c2, .c1 => c3Rank_d30
  | .a2, .c2, .c2 => c3Rank_d31
  | .a2, .c2, .c3 => c3Rank_d32
  | .a2, .c3, .c0 => c3Rank_d33
  | .a2, .c3, .c1 => c3Rank_d34
  | .a2, .c3, .c2 => c3Rank_d35
  | .a2, .c3, .c3 => c3Rank_d36
  | _, _, _ => zeroRank
private def c3Rank_d37 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 3 | .s3 => 5 | .s4 => 4 | .s5 => 3 | .s6 => 3 | .s7 => 4 | .s8 => 3 | .s9 => 3 | .s10 => 4 | .s11 => 3 | .s12 => 4 | .s13 => 3 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 3 | .s20 => 4 | .s21 => 3 | .s22 => 4 | .s23 => 3 | .s24 => 3 | .s25 => 3 | .s26 => 3 | .s27 => 3 | .s28 => 3 | .s29 => 3 | .s30 => 1 | .s31 => 3 | .s32 => 3 | .s33 => 3 | .s34 => 3 | .s35 => 3 | .s36 => 3 | .s37 => 3 | .s38 => 0
private def c3Rank_d38 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 3 | .s3 => 3 | .s4 => 3 | .s5 => 3 | .s6 => 3 | .s7 => 3 | .s8 => 3 | .s9 => 3 | .s10 => 3 | .s11 => 2 | .s12 => 3 | .s13 => 2 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 2 | .s20 => 3 | .s21 => 3 | .s22 => 1 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 1 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 2 | .s33 => 1 | .s34 => 1 | .s35 => 1 | .s36 => 2 | .s37 => 1 | .s38 => 0
private def c3Rank_s31 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c1, .c0 => c3Rank_d37
  | .a2, .c2, .c0 => c3Rank_d38
  | _, _, _ => zeroRank
private def c3Rank_d39 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 3 | .s3 => 5 | .s4 => 3 | .s5 => 3 | .s6 => 3 | .s7 => 3 | .s8 => 3 | .s9 => 4 | .s10 => 3 | .s11 => 2 | .s12 => 3 | .s13 => 2 | .s14 => 3 | .s15 => 4 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 2 | .s20 => 3 | .s21 => 3 | .s22 => 3 | .s23 => 2 | .s24 => 2 | .s25 => 2 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 2 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 2 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_s32 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d39
  | _, _, _ => zeroRank
private def c3Rank_d40 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 3 | .s3 => 4 | .s4 => 3 | .s5 => 3 | .s6 => 3 | .s7 => 3 | .s8 => 3 | .s9 => 3 | .s10 => 3 | .s11 => 2 | .s12 => 3 | .s13 => 2 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 2 | .s20 => 3 | .s21 => 3 | .s22 => 3 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 1 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_s33 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d40
  | _, _, _ => zeroRank
private def c3Rank_d41 : StateSN → Nat | .s0 => 0 | .s1 => 2 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 2 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 1 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_d42 : StateSN → Nat | .s0 => 0 | .s1 => 3 | .s2 => 2 | .s3 => 4 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 3 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 2 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 2 | .s24 => 2 | .s25 => 1 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 1 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 1 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_s34 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c0, .c0 => c3Rank_d41
  | .a2, .c0, .c2 => c3Rank_d42
  | _, _, _ => zeroRank
private def c3Rank_d43 : StateSN → Nat | .s0 => 0 | .s1 => 2 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 2 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 1 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 1 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 1 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_d44 : StateSN → Nat | .s0 => 0 | .s1 => 3 | .s2 => 2 | .s3 => 2 | .s4 => 2 | .s5 => 2 | .s6 => 2 | .s7 => 3 | .s8 => 2 | .s9 => 2 | .s10 => 2 | .s11 => 2 | .s12 => 2 | .s13 => 2 | .s14 => 2 | .s15 => 2 | .s16 => 2 | .s17 => 2 | .s18 => 2 | .s19 => 1 | .s20 => 2 | .s21 => 2 | .s22 => 2 | .s23 => 1 | .s24 => 1 | .s25 => 1 | .s26 => 1 | .s27 => 1 | .s28 => 1 | .s29 => 1 | .s30 => 1 | .s31 => 1 | .s32 => 1 | .s33 => 1 | .s34 => 1 | .s35 => 1 | .s36 => 1 | .s37 => 1 | .s38 => 0
private def c3Rank_s35 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c2, .c0 => c3Rank_d43
  | .a2, .c2, .c2 => c3Rank_d44
  | _, _, _ => zeroRank
private def c3Rank_d45 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 3 | .s3 => 3 | .s4 => 3 | .s5 => 3 | .s6 => 3 | .s7 => 3 | .s8 => 3 | .s9 => 3 | .s10 => 3 | .s11 => 3 | .s12 => 3 | .s13 => 3 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 2 | .s20 => 3 | .s21 => 3 | .s22 => 3 | .s23 => 2 | .s24 => 2 | .s25 => 2 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 2 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 2 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_s36 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c2, .c0 => c3Rank_d45
  | _, _, _ => zeroRank
private def c3Rank_d46 : StateSN → Nat | .s0 => 0 | .s1 => 0 | .s2 => 3 | .s3 => 3 | .s4 => 3 | .s5 => 3 | .s6 => 3 | .s7 => 3 | .s8 => 3 | .s9 => 3 | .s10 => 3 | .s11 => 3 | .s12 => 3 | .s13 => 3 | .s14 => 3 | .s15 => 3 | .s16 => 3 | .s17 => 3 | .s18 => 3 | .s19 => 2 | .s20 => 3 | .s21 => 3 | .s22 => 3 | .s23 => 2 | .s24 => 2 | .s25 => 2 | .s26 => 2 | .s27 => 2 | .s28 => 2 | .s29 => 2 | .s30 => 1 | .s31 => 2 | .s32 => 2 | .s33 => 2 | .s34 => 2 | .s35 => 2 | .s36 => 2 | .s37 => 2 | .s38 => 0
private def c3Rank_s37 : Arity3 → ChildTag → ChildTag → StateSN → Nat
  | .a2, .c2, .c0 => c3Rank_d46
  | _, _, _ => zeroRank
def c3Rank (l : NFDesc) : StateSN → Nat :=
  match l.st with
  | .s19 => c3Rank_s19 l.sl l.tx l.ty
  | .s22 => c3Rank_s22 l.sl l.tx l.ty
  | .s24 => c3Rank_s24 l.sl l.tx l.ty
  | .s25 => c3Rank_s25 l.sl l.tx l.ty
  | .s26 => c3Rank_s26 l.sl l.tx l.ty
  | .s27 => c3Rank_s27 l.sl l.tx l.ty
  | .s28 => c3Rank_s28 l.sl l.tx l.ty
  | .s29 => c3Rank_s29 l.sl l.tx l.ty
  | .s30 => c3Rank_s30 l.sl l.tx l.ty
  | .s31 => c3Rank_s31 l.sl l.tx l.ty
  | .s32 => c3Rank_s32 l.sl l.tx l.ty
  | .s33 => c3Rank_s33 l.sl l.tx l.ty
  | .s34 => c3Rank_s34 l.sl l.tx l.ty
  | .s35 => c3Rank_s35 l.sl l.tx l.ty
  | .s36 => c3Rank_s36 l.sl l.tx l.ty
  | .s37 => c3Rank_s37 l.sl l.tx l.ty
  | _ => zeroRank


theorem nfDescOf_st_eq : ∀ (t : Term), isNF t = true → (nfDescOf t).st = evalSN t
  | .s, _ => rfl
  | .var _, h => by cases h
  | .app .s _, _ => rfl
  | .app (.var _) _, h => by cases h
  | .app (.app .s _) _, _ => rfl
  | .app (.app (.var _) _) _, h => by cases h
  | .app (.app (.app _ _) _) _, h => by cases h

theorem nfDescOf_sl2_iff_isNF2 : ∀ (t : Term), isNF t = true → ((nfDescOf t).sl = .a2 ↔ isNF2 t = true)
  | .s, _ => ⟨(fun h1 => by cases h1), (fun h2 => by cases h2)⟩
  | .var _, h => by cases h
  | .app .s _, _ => ⟨(fun h1 => by cases h1), (fun h2 => by cases h2)⟩
  | .app (.var _) _, h => by cases h
  | .app (.app .s _x) _y, hnf => ⟨(fun _ => hnf), (fun _ => rfl)⟩
  | .app (.app (.var _) _) _, h => by cases h
  | .app (.app (.app _ _) _) _, h => by cases h

/-- Pure `Nat.beq`-backed descriptor equality & list membership (`0` kernel `Decidable` overhead!). -/
def idxArity : Arity3 → Nat
  | .a0 => 0 | .a1 => 1 | .a2 => 2

def eqArity (a b : Arity3) : Bool :=
  Nat.beq (idxArity a) (idxArity b)

theorem eqArity_iff (a b : Arity3) : eqArity a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

def idxTag : ChildTag → Nat
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3 | .c4 => 4

def eqTag (a b : ChildTag) : Bool :=
  Nat.beq (idxTag a) (idxTag b)

theorem eqTag_iff (a b : ChildTag) : eqTag a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

def eqDesc (a b : NFDesc) : Bool :=
  eqArity a.sl b.sl && eq_StateSN a.st b.st && eqTag a.tx b.tx && eqTag a.ty b.ty

theorem eqDesc_eq_true_iff (a b : NFDesc) : eqDesc a b = true ↔ a = b := by
  cases a with
  | mk sl1 st1 tx1 ty1 =>
    cases b with
    | mk sl2 st2 tx2 ty2 =>
      unfold eqDesc
      constructor
      · intro h
        have h123 := and_left h
        have hty : ty1 = ty2 := (eqTag_iff ty1 ty2).mp (and_right h)
        have h12 := and_left h123
        have htx : tx1 = tx2 := (eqTag_iff tx1 tx2).mp (and_right h123)
        have hsl : sl1 = sl2 := (eqArity_iff sl1 sl2).mp (and_left h12)
        have hst : st1 = st2 := (eq_StateSN_iff st1 st2).mp (and_right h12)
        subst hsl; subst hst; subst htx; subst hty; rfl
      · intro heq; injection heq with h1 h2 h3 h4
        subst h1; subst h2; subst h3; subst h4
        have e1 : eqArity sl1 sl1 = true := (eqArity_iff sl1 sl1).mpr rfl
        have e2 : eq_StateSN st1 st1 = true := (eq_StateSN_iff st1 st1).mpr rfl
        have e3 : eqTag tx1 tx1 = true := (eqTag_iff tx1 tx1).mpr rfl
        have e4 : eqTag ty1 ty1 = true := (eqTag_iff ty1 ty1).mpr rfl
        simp [e1, e2, e3, e4]

def memDesc (d : NFDesc) : List NFDesc → Bool
  | [] => false
  | x :: xs => eqDesc d x || memDesc d xs

def allDesc (p : NFDesc → Bool) : List NFDesc → Bool
  | [] => true
  | x :: xs => p x && allDesc p xs

theorem allDesc_mem {p : NFDesc → Bool} {xs : List NFDesc} (hall : allDesc p xs = true)
    {a : NFDesc} (hm : memDesc a xs = true) : p a = true := by
  induction xs with
  | nil => cases hm
  | cons x rest ih =>
    unfold allDesc at hall
    unfold memDesc at hm
    cases heq : eqDesc a x with
    | true =>
      have hax := (eqDesc_eq_true_iff a x).mp heq
      subst hax; exact and_left hall
    | false =>
      rw [heq] at hm
      simp (config := { failIfUnchanged := false }) at hm
      exact ih (and_right hall) hm

theorem mem_listBySt_bool :
    (memDesc ⟨.a0, .s0, .c0, .c0⟩ (listBySt .s0) &&
     checkAll1_StateSN (fun a => eq_StateSN a .s38 ||
       memDesc ⟨.a1, deltaSN .s0 a, tagOfSN a, .c0⟩ (listBySt (deltaSN .s0 a))) &&
     checkAll2_StateSN (fun x y => eq_StateSN x .s38 || eq_StateSN y .s38 ||
       memDesc ⟨.a2, deltaSN (deltaSN .s0 x) y, tagOfSN x, tagOfSN y⟩ (listBySt (deltaSN (deltaSN .s0 x) y)))) = true := rfl

theorem nfDescOf_mem_listBySt : ∀ (t : Term), isNF t = true → memDesc (nfDescOf t) (listBySt (evalSN t)) = true
  | .s, _ => and_left (and_left mem_listBySt_bool)
  | .var _, h => by cases h
  | .app .s a, h => by
    have ha : eq_StateSN (evalSN a) .s38 = false := eq_StateSN_false_of_ne (isNF_evalSN_ne_inf a h)
    have hc := checkAll1_StateSN_sound _ (and_right (and_left mem_listBySt_bool)) (evalSN a)
    rw [ha] at hc; exact hc
  | .app (.var _) _, h => by cases h
  | .app (.app .s x) y, h => by
    have hx : eq_StateSN (evalSN x) .s38 = false := eq_StateSN_false_of_ne (isNF_evalSN_ne_inf x (and_left h))
    have hy : eq_StateSN (evalSN y) .s38 = false := eq_StateSN_false_of_ne (isNF_evalSN_ne_inf y (and_right h))
    have hc := checkAll2_StateSN_sound _ (and_right mem_listBySt_bool) (evalSN x) (evalSN y)
    rw [hx, hy] at hc; exact hc
  | .app (.app (.var _) _) _, h => by cases h
  | .app (.app (.app _ _) _) _, h => by cases h

theorem absApp_base_bool :
    (checkAll1_StateSN (fun z => eq_StateSN z .s38 ||
      memDesc ⟨.a1, deltaSN .s0 z, tagOfSN z, .c0⟩ (listAbsApp ⟨.a0, .s0, .c0, .c0⟩ z)) &&
     checkAll2_StateSN (fun a z => eq_StateSN a .s38 || eq_StateSN z .s38 ||
      memDesc ⟨.a2, deltaSN (deltaSN .s0 a) z, tagOfSN a, tagOfSN z⟩ (listAbsApp ⟨.a1, deltaSN .s0 a, tagOfSN a, .c0⟩ z))) = true := rfl

theorem absApp_base0 {z : StateSN} (hz : z ≠ .s38) :
    memDesc ⟨.a1, deltaSN .s0 z, tagOfSN z, .c0⟩ (listAbsApp ⟨.a0, .s0, .c0, .c0⟩ z) = true := by
  have hbz : eq_StateSN z .s38 = false := eq_StateSN_false_of_ne hz
  have hc := checkAll1_StateSN_sound _ (and_left absApp_base_bool) z
  rw [hbz] at hc; exact hc

theorem absApp_base1 {a z : StateSN} (ha : a ≠ .s38) (hz : z ≠ .s38) :
    memDesc ⟨.a2, deltaSN (deltaSN .s0 a) z, tagOfSN a, tagOfSN z⟩ (listAbsApp ⟨.a1, deltaSN .s0 a, tagOfSN a, .c0⟩ z) = true := by
  have hba : eq_StateSN a .s38 = false := eq_StateSN_false_of_ne ha
  have hbz : eq_StateSN z .s38 = false := eq_StateSN_false_of_ne hz
  have hc := checkAll2_StateSN_sound _ (and_right absApp_base_bool) a z
  rw [hba, hbz] at hc; exact hc

/-- Outer-`allDesc` + `Nat.beq` inductive closure checker:
    `listBySt x` and `listAbsApp da z` are pattern-matched ONCE per `(x, z)` in Lean's call-by-name kernel! -/
def checkInductiveXZ (x z : StateSN) : Bool :=
  if eq_StateSN x .s38 || eq_StateSN z .s38 || eq_StateSN (deltaSN x z) .s38 then true
  else
    allDesc (fun da =>
      allDesc (fun dp =>
        checkAll1_StateSN (fun y =>
          if eq_StateSN y .s38 then true
          else
            let u_st := deltaSN (deltaSN .s0 x) y
            let out_st := deltaSN u_st z
            let qz := deltaSN y z
            if eq_StateSN out_st .s38 || eq_StateSN qz .s38 then true
            else if eq_StateSN (deltaSN dp.st qz) out_st then
              allDesc (fun dres =>
                memDesc dres (listAbsApp ⟨.a2, u_st, tagOfSN x, tagOfSN y⟩ z))
                (listAbsApp dp qz)
            else true))
        (listAbsApp da z))
      (listBySt x)

private theorem abs_ind_xz_0 : checkAll1_StateSN (fun z => checkInductiveXZ .s0 z) = true := rfl
private theorem abs_ind_xz_1 : checkAll1_StateSN (fun z => checkInductiveXZ .s1 z) = true := rfl
private theorem abs_ind_xz_2 : checkAll1_StateSN (fun z => checkInductiveXZ .s2 z) = true := rfl
private theorem abs_ind_xz_3 : checkAll1_StateSN (fun z => checkInductiveXZ .s3 z) = true := rfl
private theorem abs_ind_xz_4 : checkAll1_StateSN (fun z => checkInductiveXZ .s4 z) = true := rfl
private theorem abs_ind_xz_5 : checkAll1_StateSN (fun z => checkInductiveXZ .s5 z) = true := rfl
private theorem abs_ind_xz_6 : checkAll1_StateSN (fun z => checkInductiveXZ .s6 z) = true := rfl
private theorem abs_ind_xz_7 : checkAll1_StateSN (fun z => checkInductiveXZ .s7 z) = true := rfl
private theorem abs_ind_xz_8 : checkAll1_StateSN (fun z => checkInductiveXZ .s8 z) = true := rfl
private theorem abs_ind_xz_9 : checkAll1_StateSN (fun z => checkInductiveXZ .s9 z) = true := rfl
private theorem abs_ind_xz_10 : checkAll1_StateSN (fun z => checkInductiveXZ .s10 z) = true := rfl
private theorem abs_ind_xz_11 : checkAll1_StateSN (fun z => checkInductiveXZ .s11 z) = true := rfl
private theorem abs_ind_xz_12 : checkAll1_StateSN (fun z => checkInductiveXZ .s12 z) = true := rfl
private theorem abs_ind_xz_13 : checkAll1_StateSN (fun z => checkInductiveXZ .s13 z) = true := rfl
private theorem abs_ind_xz_14 : checkAll1_StateSN (fun z => checkInductiveXZ .s14 z) = true := rfl
private theorem abs_ind_xz_15 : checkAll1_StateSN (fun z => checkInductiveXZ .s15 z) = true := rfl
private theorem abs_ind_xz_16 : checkAll1_StateSN (fun z => checkInductiveXZ .s16 z) = true := rfl
private theorem abs_ind_xz_17 : checkAll1_StateSN (fun z => checkInductiveXZ .s17 z) = true := rfl
private theorem abs_ind_xz_18 : checkAll1_StateSN (fun z => checkInductiveXZ .s18 z) = true := rfl
private theorem abs_ind_xz_19 : checkAll1_StateSN (fun z => checkInductiveXZ .s19 z) = true := rfl
private theorem abs_ind_xz_20 : checkAll1_StateSN (fun z => checkInductiveXZ .s20 z) = true := rfl
private theorem abs_ind_xz_21 : checkAll1_StateSN (fun z => checkInductiveXZ .s21 z) = true := rfl
private theorem abs_ind_xz_22 : checkAll1_StateSN (fun z => checkInductiveXZ .s22 z) = true := rfl
private theorem abs_ind_xz_23 : checkAll1_StateSN (fun z => checkInductiveXZ .s23 z) = true := rfl
private theorem abs_ind_xz_24 : checkAll1_StateSN (fun z => checkInductiveXZ .s24 z) = true := rfl
private theorem abs_ind_xz_25 : checkAll1_StateSN (fun z => checkInductiveXZ .s25 z) = true := rfl
private theorem abs_ind_xz_26 : checkAll1_StateSN (fun z => checkInductiveXZ .s26 z) = true := rfl
private theorem abs_ind_xz_27 : checkAll1_StateSN (fun z => checkInductiveXZ .s27 z) = true := rfl
private theorem abs_ind_xz_28 : checkAll1_StateSN (fun z => checkInductiveXZ .s28 z) = true := rfl
private theorem abs_ind_xz_29 : checkAll1_StateSN (fun z => checkInductiveXZ .s29 z) = true := rfl
private theorem abs_ind_xz_30 : checkAll1_StateSN (fun z => checkInductiveXZ .s30 z) = true := rfl
private theorem abs_ind_xz_31 : checkAll1_StateSN (fun z => checkInductiveXZ .s31 z) = true := rfl
private theorem abs_ind_xz_32 : checkAll1_StateSN (fun z => checkInductiveXZ .s32 z) = true := rfl
private theorem abs_ind_xz_33 : checkAll1_StateSN (fun z => checkInductiveXZ .s33 z) = true := rfl
private theorem abs_ind_xz_34 : checkAll1_StateSN (fun z => checkInductiveXZ .s34 z) = true := rfl
private theorem abs_ind_xz_35 : checkAll1_StateSN (fun z => checkInductiveXZ .s35 z) = true := rfl
private theorem abs_ind_xz_36 : checkAll1_StateSN (fun z => checkInductiveXZ .s36 z) = true := rfl
private theorem abs_ind_xz_37 : checkAll1_StateSN (fun z => checkInductiveXZ .s37 z) = true := rfl
private theorem abs_ind_xz_38 : checkAll1_StateSN (fun z => checkInductiveXZ .s38 z) = true := rfl

theorem checkInductiveXZ_all (x z : StateSN) : checkInductiveXZ x z = true :=
  match x with
  | .s0 => checkAll1_StateSN_sound _ abs_ind_xz_0 z
  | .s1 => checkAll1_StateSN_sound _ abs_ind_xz_1 z
  | .s2 => checkAll1_StateSN_sound _ abs_ind_xz_2 z
  | .s3 => checkAll1_StateSN_sound _ abs_ind_xz_3 z
  | .s4 => checkAll1_StateSN_sound _ abs_ind_xz_4 z
  | .s5 => checkAll1_StateSN_sound _ abs_ind_xz_5 z
  | .s6 => checkAll1_StateSN_sound _ abs_ind_xz_6 z
  | .s7 => checkAll1_StateSN_sound _ abs_ind_xz_7 z
  | .s8 => checkAll1_StateSN_sound _ abs_ind_xz_8 z
  | .s9 => checkAll1_StateSN_sound _ abs_ind_xz_9 z
  | .s10 => checkAll1_StateSN_sound _ abs_ind_xz_10 z
  | .s11 => checkAll1_StateSN_sound _ abs_ind_xz_11 z
  | .s12 => checkAll1_StateSN_sound _ abs_ind_xz_12 z
  | .s13 => checkAll1_StateSN_sound _ abs_ind_xz_13 z
  | .s14 => checkAll1_StateSN_sound _ abs_ind_xz_14 z
  | .s15 => checkAll1_StateSN_sound _ abs_ind_xz_15 z
  | .s16 => checkAll1_StateSN_sound _ abs_ind_xz_16 z
  | .s17 => checkAll1_StateSN_sound _ abs_ind_xz_17 z
  | .s18 => checkAll1_StateSN_sound _ abs_ind_xz_18 z
  | .s19 => checkAll1_StateSN_sound _ abs_ind_xz_19 z
  | .s20 => checkAll1_StateSN_sound _ abs_ind_xz_20 z
  | .s21 => checkAll1_StateSN_sound _ abs_ind_xz_21 z
  | .s22 => checkAll1_StateSN_sound _ abs_ind_xz_22 z
  | .s23 => checkAll1_StateSN_sound _ abs_ind_xz_23 z
  | .s24 => checkAll1_StateSN_sound _ abs_ind_xz_24 z
  | .s25 => checkAll1_StateSN_sound _ abs_ind_xz_25 z
  | .s26 => checkAll1_StateSN_sound _ abs_ind_xz_26 z
  | .s27 => checkAll1_StateSN_sound _ abs_ind_xz_27 z
  | .s28 => checkAll1_StateSN_sound _ abs_ind_xz_28 z
  | .s29 => checkAll1_StateSN_sound _ abs_ind_xz_29 z
  | .s30 => checkAll1_StateSN_sound _ abs_ind_xz_30 z
  | .s31 => checkAll1_StateSN_sound _ abs_ind_xz_31 z
  | .s32 => checkAll1_StateSN_sound _ abs_ind_xz_32 z
  | .s33 => checkAll1_StateSN_sound _ abs_ind_xz_33 z
  | .s34 => checkAll1_StateSN_sound _ abs_ind_xz_34 z
  | .s35 => checkAll1_StateSN_sound _ abs_ind_xz_35 z
  | .s36 => checkAll1_StateSN_sound _ abs_ind_xz_36 z
  | .s37 => checkAll1_StateSN_sound _ abs_ind_xz_37 z
  | .s38 => checkAll1_StateSN_sound _ abs_ind_xz_38 z

theorem absApp_sl2_closed {x y z : StateSN} {da dp dres : NFDesc}
    (hx : x ≠ .s38) (hy : y ≠ .s38) (hz : z ≠ .s38)
    (hout : deltaSN (deltaSN (deltaSN .s0 x) y) z ≠ .s38)
    (hxz : deltaSN x z ≠ .s38) (hyz : deltaSN y z ≠ .s38)
    (hda : memDesc da (listBySt x) = true)
    (hdp : memDesc dp (listAbsApp da z) = true)
    (heq_out : deltaSN dp.st (deltaSN y z) = deltaSN (deltaSN (deltaSN .s0 x) y) z)
    (hdres : memDesc dres (listAbsApp dp (deltaSN y z)) = true) :
    memDesc dres (listAbsApp ⟨.a2, deltaSN (deltaSN .s0 x) y, tagOfSN x, tagOfSN y⟩ z) = true := by
  have hc := checkInductiveXZ_all x z
  unfold checkInductiveXZ at hc
  rw [eq_StateSN_false_of_ne hx, eq_StateSN_false_of_ne hz, eq_StateSN_false_of_ne hxz] at hc
  simp (config := { failIfUnchanged := false }) at hc
  have hc_dp := allDesc_mem (allDesc_mem hc hda) hdp
  have hcy := checkAll1_StateSN_sound _ hc_dp y
  rw [eq_StateSN_false_of_ne hy, eq_StateSN_false_of_ne hout, eq_StateSN_false_of_ne hyz] at hcy
  simp (config := { failIfUnchanged := false }) at hcy
  have hbeq_out : eq_StateSN (deltaSN dp.st (deltaSN y z)) (deltaSN (deltaSN (deltaSN .s0 x) y) z) = true :=
    (eq_StateSN_iff _ _).mpr heq_out
  rw [hbeq_out] at hcy
  simp (config := { failIfUnchanged := false }) at hcy
  exact allDesc_mem hcy hdres

def normLI : Nat → Term → Option Term
  | 0, t => if isNF t then some t else none
  | fuel + 1, t =>
    match stepLI t with
    | none => if isNF t then some t else none
    | some t' => normLI fuel t'

def normRI : Nat → Term → Option Term
  | 0, t => if isNF t then some t else none
  | fuel + 1, t =>
    match stepRI t with
    | none => if isNF t then some t else none
    | some t' => normRI fuel t'

theorem stepLI_of_isNF : ∀ (t : Term), isNF t = true → stepLI t = none
  | .s, _ => rfl
  | .var _, h => by cases h
  | .app .s a, h => by
    have hnr : isRootRedex (.s ⋅ a) = false := rfl
    rw [stepLI_not_root hnr, stepLI_of_isNF a h]; rfl
  | .app (.var _) _, h => by cases h
  | .app (.app .s x) y, h => by
    have hx := stepLI_of_isNF x (and_left h)
    have hy := stepLI_of_isNF y (and_right h)
    have hnr1 : isRootRedex (.s ⋅ x) = false := rfl
    have hsx : stepLI (.s ⋅ x) = none := by rw [stepLI_not_root hnr1, hx]; rfl
    have hnr2 : isRootRedex (.s ⋅ x ⋅ y) = false := rfl
    rw [stepLI_not_root hnr2, hsx, hy]
  | .app (.app (.var _) _) _, h => by cases h
  | .app (.app (.app _ _) _) _, h => by cases h

theorem stepRI_of_isNF : ∀ (t : Term), isNF t = true → stepRI t = none
  | .s, _ => rfl
  | .var _, h => by cases h
  | .app .s a, h => by
    have hnr : isRootRedex (.s ⋅ a) = false := rfl
    rw [stepRI_not_root hnr, stepRI_of_isNF a h]; rfl
  | .app (.var _) _, h => by cases h
  | .app (.app .s x) y, h => by
    have hx := stepRI_of_isNF x (and_left h)
    have hy := stepRI_of_isNF y (and_right h)
    have hnr1 : isRootRedex (.s ⋅ x) = false := rfl
    have hsx : stepRI (.s ⋅ x) = none := by rw [stepRI_not_root hnr1, hx]; rfl
    have hnr2 : isRootRedex (.s ⋅ x ⋅ y) = false := rfl
    rw [stepRI_not_root hnr2, hy, hsx]
  | .app (.app (.var _) _) _, h => by cases h
  | .app (.app (.app _ _) _) _, h => by cases h

theorem stepLI_sound : ∀ (a b : Term), stepLI a = some b → Step a b
  | .s, _, h => by cases h
  | .var _, _, h => by cases h
  | .app l r, b, h => by
    unfold stepLI at h
    cases hl : stepLI l with
    | some l' => rw [hl] at h; injection h with hb; subst hb; exact Step.left (stepLI_sound l l' hl)
    | none =>
      rw [hl] at h
      cases hr : stepLI r with
      | some r' => rw [hr] at h; injection h with hb; subst hb; exact Step.right (stepLI_sound r r' hr)
      | none =>
        rw [hr] at h
        cases l with
        | s => cases h
        | var _ => cases h
        | app l1 y =>
          cases l1 with
          | s => cases h
          | var _ => cases h
          | app l11 x =>
            cases l11 with
            | s => injection h with hb; subst hb; exact Step.root x y r
            | var _ => cases h
            | app _ _ => cases h

theorem stepRI_sound : ∀ (a b : Term), stepRI a = some b → Step a b
  | .s, _, h => by cases h
  | .var _, _, h => by cases h
  | .app l r, b, h => by
    unfold stepRI at h
    cases hr : stepRI r with
    | some r' => rw [hr] at h; injection h with hb; subst hb; exact Step.right (stepRI_sound r r' hr)
    | none =>
      rw [hr] at h
      cases hl : stepRI l with
      | some l' => rw [hl] at h; injection h with hb; subst hb; exact Step.left (stepRI_sound l l' hl)
      | none =>
        rw [hl] at h
        cases l with
        | s => cases h
        | var _ => cases h
        | app l1 y =>
          cases l1 with
          | s => cases h
          | var _ => cases h
          | app l11 x =>
            cases l11 with
            | s => injection h with hb; subst hb; exact Step.root x y r
            | var _ => cases h
            | app _ _ => cases h

theorem isNF_of_stepLI_none : ∀ (t : Term), isClosed t = true → stepLI t = none → isNF t = true
  | .s, _, _ => rfl
  | .var _, hcl, _ => by cases hcl
  | .app l r, hcl, hli => by
    unfold stepLI at hli
    cases hl : stepLI l with
    | some _ => rw [hl] at hli; cases hli
    | none =>
      rw [hl] at hli
      cases hr : stepLI r with
      | some _ => rw [hr] at hli; cases hli
      | none =>
        rw [hr] at hli
        have hnf_l := isNF_of_stepLI_none l (and_left hcl) hl
        have hnf_r := isNF_of_stepLI_none r (and_right hcl) hr
        cases l with
        | s => exact hnf_r
        | var _ => cases hnf_l
        | app l1 y =>
          cases l1 with
          | s => exact Bool.and_eq_true _ _ |>.mpr ⟨hnf_l, hnf_r⟩
          | var _ => cases hnf_l
          | app l11 _ =>
            cases l11 with
            | s => cases hli
            | var _ => cases hnf_l
            | app _ _ => cases hnf_l

theorem isNF_of_stepRI_none : ∀ (t : Term), isClosed t = true → stepRI t = none → isNF t = true
  | .s, _, _ => rfl
  | .var _, hcl, _ => by cases hcl
  | .app l r, hcl, hri => by
    unfold stepRI at hri
    cases hr : stepRI r with
    | some _ => rw [hr] at hri; cases hri
    | none =>
      rw [hr] at hri
      cases hl : stepRI l with
      | some _ => rw [hl] at hri; cases hri
      | none =>
        rw [hl] at hri
        have hnf_l := isNF_of_stepRI_none l (and_left hcl) hl
        have hnf_r := isNF_of_stepRI_none r (and_right hcl) hr
        cases l with
        | s => exact hnf_r
        | var _ => cases hnf_l
        | app l1 y =>
          cases l1 with
          | s => exact Bool.and_eq_true _ _ |>.mpr ⟨hnf_l, hnf_r⟩
          | var _ => cases hnf_l
          | app l11 _ =>
            cases l11 with
            | s => cases hri
            | var _ => cases hnf_l
            | app _ _ => cases hnf_l

theorem normLI_reduces_and_isNF : ∀ (fuel : Nat) (t n : Term),
    normLI fuel t = some n → Reduces t n ∧ isNF n = true
  | 0, t, n, h => by
    unfold normLI at h
    cases hnf : isNF t with
    | false => rw [hnf] at h; cases h
    | true => rw [hnf] at h; injection h with htn; subst htn; exact ⟨Reduces.refl _, hnf⟩
  | fuel + 1, t, n, h => by
    unfold normLI at h
    cases hs : stepLI t with
    | none =>
      rw [hs] at h
      cases hnf : isNF t with
      | false => rw [hnf] at h; cases h
      | true => rw [hnf] at h; injection h with htn; subst htn; exact ⟨Reduces.refl _, hnf⟩
    | some t' =>
      rw [hs] at h
      rcases normLI_reduces_and_isNF fuel t' n h with ⟨hr, hnf⟩
      exact ⟨Reduces.next (stepLI_sound t t' hs) hr, hnf⟩

theorem normRI_reduces_and_isNF : ∀ (fuel : Nat) (t n : Term),
    normRI fuel t = some n → Reduces t n ∧ isNF n = true
  | 0, t, n, h => by
    unfold normRI at h
    cases hnf : isNF t with
    | false => rw [hnf] at h; cases h
    | true => rw [hnf] at h; injection h with htn; subst htn; exact ⟨Reduces.refl _, hnf⟩
  | fuel + 1, t, n, h => by
    unfold normRI at h
    cases hs : stepRI t with
    | none =>
      rw [hs] at h
      cases hnf : isNF t with
      | false => rw [hnf] at h; cases h
      | true => rw [hnf] at h; injection h with htn; subst htn; exact ⟨Reduces.refl _, hnf⟩
    | some t' =>
      rw [hs] at h
      rcases normRI_reduces_and_isNF fuel t' n h with ⟨hr, hnf⟩
      exact ⟨Reduces.next (stepRI_sound t t' hs) hr, hnf⟩

theorem normLI_of_isNF (fuel : Nat) {t : Term} (hnf : isNF t = true) : normLI fuel t = some t := by
  cases fuel with
  | zero => unfold normLI; rw [hnf]; rfl
  | succ f => unfold normLI; rw [stepLI_of_isNF t hnf, hnf]; rfl

theorem normRI_of_isNF (fuel : Nat) {t : Term} (hnf : isNF t = true) : normRI fuel t = some t := by
  cases fuel with
  | zero => unfold normRI; rw [hnf]; rfl
  | succ f => unfold normRI; rw [stepRI_of_isNF t hnf, hnf]; rfl

theorem normLI_unique_of_isNF : ∀ (fuel : Nat) {t n : Term},
    isNF t = true → normLI fuel t = some n → n = t := by
  intro fuel t n hnf h
  rw [normLI_of_isNF fuel hnf] at h
  injection h with hn; exact hn.symm

theorem normRI_unique_of_isNF : ∀ (fuel : Nat) {t n : Term},
    isNF t = true → normRI fuel t = some n → n = t := by
  intro fuel t n hnf h
  rw [normRI_of_isNF fuel hnf] at h
  injection h with hn; exact hn.symm

theorem isNF_app_inv {p q : Term} (h : isNF (p ⋅ q) = true) :
    isNF p = true ∧ isNF q = true := by
  cases p with
  | s => exact ⟨rfl, h⟩
  | var _ => cases h
  | app p1 _ => cases p1 with
    | s => exact ⟨and_left h, and_right h⟩
    | var _ => cases h
    | app _ _ => cases h

theorem normLI_app_decomp : ∀ (fuel : Nat) (p q n : Term),
    isClosed p = true → isClosed q = true → normLI fuel (p ⋅ q) = some n →
    ∃ p' q' f1 f2 f3, f1 ≤ fuel ∧ f2 ≤ fuel ∧ f3 ≤ fuel ∧
      normLI f1 p = some p' ∧ normLI f2 q = some q' ∧ normLI f3 (p' ⋅ q') = some n
  | 0, p, q, n, _, _, h => by
    unfold normLI at h
    cases hnf : isNF (p ⋅ q) with
    | false => rw [hnf] at h; cases h
    | true =>
      rw [hnf] at h; injection h with hn; subst hn
      rcases isNF_app_inv hnf with ⟨hp, hq⟩
      exact ⟨p, q, 0, 0, 0, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
        normLI_of_isNF 0 hp, normLI_of_isNF 0 hq, normLI_of_isNF 0 hnf⟩
  | fuel + 1, p, q, n, hcp, hcq, h => by
    have horig := h
    unfold normLI at h
    cases hp : stepLI p with
    | some p1 =>
      have hstep : stepLI (p ⋅ q) = some (p1 ⋅ q) := by
        conv => lhs; unfold stepLI
        rw [hp]
      rw [hstep] at h
      have hcp1 := step_preserves_closed (stepLI_sound p p1 hp) hcp
      rcases normLI_app_decomp fuel p1 q n hcp1 hcq h with
        ⟨p', q', f1, f2, f3, hf1, hf2, hf3, hn1, hn2, hn3⟩
      refine ⟨p', q', f1 + 1, f2, f3,
        Nat.succ_le_succ hf1, Nat.le_trans hf2 (Nat.le_succ _), Nat.le_trans hf3 (Nat.le_succ _),
        ?_, hn2, hn3⟩
      unfold normLI; rw [hp]; exact hn1
    | none =>
      have hnf_p := isNF_of_stepLI_none p hcp hp
      cases hq : stepLI q with
      | some q1 =>
        have hstep : stepLI (p ⋅ q) = some (p ⋅ q1) := by
          conv => lhs; unfold stepLI
          rw [hp, hq]
        rw [hstep] at h
        have hcq1 := step_preserves_closed (stepLI_sound q q1 hq) hcq
        rcases normLI_app_decomp fuel p q1 n hcp hcq1 h with
          ⟨p', q', f1, f2, f3, _, hf2, hf3, hn1, hn2, hn3⟩
        have hp_eq : p' = p := normLI_unique_of_isNF f1 hnf_p hn1
        rw [hp_eq] at hn3
        refine ⟨p, q', 0, f2 + 1, f3,
          Nat.zero_le _, Nat.succ_le_succ hf2, Nat.le_trans hf3 (Nat.le_succ _),
          normLI_of_isNF 0 hnf_p, ?_, hn3⟩
        unfold normLI; rw [hq]; exact hn2
      | none =>
        have hnf_q := isNF_of_stepLI_none q hcq hq
        exact ⟨p, q, 0, 0, fuel + 1, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _,
          normLI_of_isNF 0 hnf_p, normLI_of_isNF 0 hnf_q, horig⟩

theorem normRI_app_decomp : ∀ (fuel : Nat) (p q n : Term),
    isClosed p = true → isClosed q = true → normRI fuel (p ⋅ q) = some n →
    ∃ p' q' f1 f2 f3, f1 ≤ fuel ∧ f2 ≤ fuel ∧ f3 ≤ fuel ∧
      normRI f1 p = some p' ∧ normRI f2 q = some q' ∧ normRI f3 (p' ⋅ q') = some n
  | 0, p, q, n, _, _, h => by
    unfold normRI at h
    cases hnf : isNF (p ⋅ q) with
    | false => rw [hnf] at h; cases h
    | true =>
      rw [hnf] at h; injection h with hn; subst hn
      rcases isNF_app_inv hnf with ⟨hp, hq⟩
      exact ⟨p, q, 0, 0, 0, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
        normRI_of_isNF 0 hp, normRI_of_isNF 0 hq, normRI_of_isNF 0 hnf⟩
  | fuel + 1, p, q, n, hcp, hcq, h => by
    have horig := h
    unfold normRI at h
    cases hq : stepRI q with
    | some q1 =>
      have hstep : stepRI (p ⋅ q) = some (p ⋅ q1) := by
        conv => lhs; unfold stepRI
        rw [hq]
      rw [hstep] at h
      have hcq1 := step_preserves_closed (stepRI_sound q q1 hq) hcq
      rcases normRI_app_decomp fuel p q1 n hcp hcq1 h with
        ⟨p', q', f1, f2, f3, hf1, hf2, hf3, hn1, hn2, hn3⟩
      refine ⟨p', q', f1, f2 + 1, f3,
        Nat.le_trans hf1 (Nat.le_succ _), Nat.succ_le_succ hf2, Nat.le_trans hf3 (Nat.le_succ _),
        hn1, ?_, hn3⟩
      unfold normRI; rw [hq]; exact hn2
    | none =>
      have hnf_q := isNF_of_stepRI_none q hcq hq
      cases hp : stepRI p with
      | some p1 =>
        have hstep : stepRI (p ⋅ q) = some (p1 ⋅ q) := by
          conv => lhs; unfold stepRI
          rw [hq, hp]
        rw [hstep] at h
        have hcp1 := step_preserves_closed (stepRI_sound p p1 hp) hcp
        rcases normRI_app_decomp fuel p1 q n hcp1 hcq h with
          ⟨p', q', f1, f2, f3, hf1, _, hf3, hn1, hn2, hn3⟩
        have hq_eq : q' = q := normRI_unique_of_isNF f2 hnf_q hn2
        rw [hq_eq] at hn3
        refine ⟨p', q, f1 + 1, 0, f3,
          Nat.succ_le_succ hf1, Nat.zero_le _, Nat.le_trans hf3 (Nat.le_succ _),
          ?_, normRI_of_isNF 0 hnf_q, hn3⟩
        unfold normRI; rw [hp]; exact hn1
      | none =>
        have hnf_p := isNF_of_stepRI_none p hcp hp
        exact ⟨p, q, 0, 0, fuel + 1, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _,
          normRI_of_isNF 0 hnf_p, normRI_of_isNF 0 hnf_q, horig⟩

theorem normLI_absApp_sound : ∀ (fuel : Nat),
    ∀ (u z n : Term), isNF u = true → isNF z = true → normLI fuel (u ⋅ z) = some n →
      memDesc (nfDescOf n) (listAbsApp (nfDescOf u) (evalSN z)) = true := by
  intro fuel
  refine Nat.strongRecOn fuel ?_
  intro fuel ih u z n hu hz hnorm
  have hz_lt := isNF_evalSN_ne_inf z hz
  cases u with
  | s =>
    have hnf_uz : isNF (.s ⋅ z) = true := hz
    have hn_eq := normLI_unique_of_isNF fuel hnf_uz hnorm
    subst hn_eq
    exact absApp_base0 hz_lt
  | var _ => cases hu
  | app u1 y =>
    cases u1 with
    | s =>
      have hnf_uz : isNF (.s ⋅ y ⋅ z) = true := Bool.and_eq_true _ _ |>.mpr ⟨hu, hz⟩
      have hn_eq := normLI_unique_of_isNF fuel hnf_uz hnorm
      subst hn_eq
      exact absApp_base1 (isNF_evalSN_ne_inf y hu) hz_lt
    | var _ => cases hu
    | app u11 x =>
      cases u11 with
      | s =>
        have hx_nf : isNF x = true := and_left hu
        have hy_nf : isNF y = true := and_right hu
        cases fuel with
        | zero =>
          unfold normLI at hnorm
          have hfalse : isNF ((.s ⋅ x ⋅ y) ⋅ z) = false := rfl
          rw [hfalse] at hnorm; cases hnorm
        | succ fuel' =>
          have hstep_root : stepLI ((.s ⋅ x ⋅ y) ⋅ z) = some ((x ⋅ z) ⋅ (y ⋅ z)) :=
            stepLI_root x y z (stepLI_of_isNF (.s ⋅ x ⋅ y) hu) (stepLI_of_isNF z hz)
          have hnorm' : normLI fuel' ((x ⋅ z) ⋅ (y ⋅ z)) = some n := by
            unfold normLI at hnorm; rw [hstep_root] at hnorm; exact hnorm
          have hcxz : isClosed (x ⋅ z) = true :=
            Bool.and_eq_true _ _ |>.mpr ⟨isNF_closed x hx_nf, isNF_closed z hz⟩
          have hcyz : isClosed (y ⋅ z) = true :=
            Bool.and_eq_true _ _ |>.mpr ⟨isNF_closed y hy_nf, isNF_closed z hz⟩
          rcases normLI_app_decomp fuel' (x ⋅ z) (y ⋅ z) n hcxz hcyz hnorm' with
            ⟨px, qy, f1, f2, f3, hf1, _, hf3, hnpx, hnqy, hnn⟩
          rcases normLI_reduces_and_isNF f1 (x ⋅ z) px hnpx with ⟨hr_px, hnf_px⟩
          rcases normLI_reduces_and_isNF f2 (y ⋅ z) qy hnqy with ⟨hr_qy, hnf_qy⟩
          rcases normLI_reduces_and_isNF (fuel' + 1) ((.s ⋅ x ⋅ y) ⋅ z) n hnorm with ⟨hr_n, hnf_n⟩
          have hdp := ih f1 (Nat.lt_succ_of_le hf1) x z px hx_nf hz hnpx
          have hdres := ih f3 (Nat.lt_succ_of_le hf3) px qy n hnf_px hnf_qy hnn
          have hqy_st : evalSN qy = deltaSN (evalSN y) (evalSN z) :=
            (evalSN_reduces_invariant hr_qy).symm
          rw [hqy_st] at hdres
          have hpx_st : (nfDescOf px).st = evalSN px := nfDescOf_st_eq px hnf_px
          have hout_eq : deltaSN (nfDescOf px).st (deltaSN (evalSN y) (evalSN z)) =
              deltaSN (deltaSN (deltaSN .s0 (evalSN x)) (evalSN y)) (evalSN z) := by
            rw [hpx_st, ← evalSN_reduces_invariant hr_px]
            exact (deltaSN_s_law (evalSN x) (evalSN y) (evalSN z)).symm
          have hout_ne : deltaSN (deltaSN (deltaSN .s0 (evalSN x)) (evalSN y)) (evalSN z) ≠ .s38 := by
            change evalSN ((.s ⋅ x ⋅ y) ⋅ z) ≠ .s38
            rw [evalSN_reduces_invariant hr_n]
            exact isNF_evalSN_ne_inf n hnf_n
          exact absApp_sl2_closed
            (isNF_evalSN_ne_inf x hx_nf)
            (isNF_evalSN_ne_inf y hy_nf)
            hz_lt
            hout_ne
            (by change evalSN (x ⋅ z) ≠ .s38; rw [evalSN_reduces_invariant hr_px]; exact isNF_evalSN_ne_inf px hnf_px)
            (by rw [← hqy_st]; exact isNF_evalSN_ne_inf qy hnf_qy)
            (nfDescOf_mem_listBySt x hx_nf)
            hdp
            hout_eq
            hdres
      | var _ => cases hu
      | app _ _ => cases hu

theorem normRI_absApp_sound : ∀ (fuel : Nat),
    ∀ (u z n : Term), isNF u = true → isNF z = true → normRI fuel (u ⋅ z) = some n →
      memDesc (nfDescOf n) (listAbsApp (nfDescOf u) (evalSN z)) = true := by
  intro fuel
  refine Nat.strongRecOn fuel ?_
  intro fuel ih u z n hu hz hnorm
  have hz_lt := isNF_evalSN_ne_inf z hz
  cases u with
  | s =>
    have hnf_uz : isNF (.s ⋅ z) = true := hz
    have hn_eq := normRI_unique_of_isNF fuel hnf_uz hnorm
    subst hn_eq
    exact absApp_base0 hz_lt
  | var _ => cases hu
  | app u1 y =>
    cases u1 with
    | s =>
      have hnf_uz : isNF (.s ⋅ y ⋅ z) = true := Bool.and_eq_true _ _ |>.mpr ⟨hu, hz⟩
      have hn_eq := normRI_unique_of_isNF fuel hnf_uz hnorm
      subst hn_eq
      exact absApp_base1 (isNF_evalSN_ne_inf y hu) hz_lt
    | var _ => cases hu
    | app u11 x =>
      cases u11 with
      | s =>
        have hx_nf : isNF x = true := and_left hu
        have hy_nf : isNF y = true := and_right hu
        cases fuel with
        | zero =>
          unfold normRI at hnorm
          have hfalse : isNF ((.s ⋅ x ⋅ y) ⋅ z) = false := rfl
          rw [hfalse] at hnorm; cases hnorm
        | succ fuel' =>
          have hstep_root : stepRI ((.s ⋅ x ⋅ y) ⋅ z) = some ((x ⋅ z) ⋅ (y ⋅ z)) :=
            stepRI_root x y z (stepRI_of_isNF (.s ⋅ x ⋅ y) hu) (stepRI_of_isNF z hz)
          have hnorm' : normRI fuel' ((x ⋅ z) ⋅ (y ⋅ z)) = some n := by
            unfold normRI at hnorm; rw [hstep_root] at hnorm; exact hnorm
          have hcxz : isClosed (x ⋅ z) = true :=
            Bool.and_eq_true _ _ |>.mpr ⟨isNF_closed x hx_nf, isNF_closed z hz⟩
          have hcyz : isClosed (y ⋅ z) = true :=
            Bool.and_eq_true _ _ |>.mpr ⟨isNF_closed y hy_nf, isNF_closed z hz⟩
          rcases normRI_app_decomp fuel' (x ⋅ z) (y ⋅ z) n hcxz hcyz hnorm' with
            ⟨px, qy, f1, f2, f3, hf1, _, hf3, hnpx, hnqy, hnn⟩
          rcases normRI_reduces_and_isNF f1 (x ⋅ z) px hnpx with ⟨hr_px, hnf_px⟩
          rcases normRI_reduces_and_isNF f2 (y ⋅ z) qy hnqy with ⟨hr_qy, hnf_qy⟩
          rcases normRI_reduces_and_isNF (fuel' + 1) ((.s ⋅ x ⋅ y) ⋅ z) n hnorm with ⟨hr_n, hnf_n⟩
          have hdp := ih f1 (Nat.lt_succ_of_le hf1) x z px hx_nf hz hnpx
          have hdres := ih f3 (Nat.lt_succ_of_le hf3) px qy n hnf_px hnf_qy hnn
          have hqy_st : evalSN qy = deltaSN (evalSN y) (evalSN z) :=
            (evalSN_reduces_invariant hr_qy).symm
          rw [hqy_st] at hdres
          have hpx_st : (nfDescOf px).st = evalSN px := nfDescOf_st_eq px hnf_px
          have hout_eq : deltaSN (nfDescOf px).st (deltaSN (evalSN y) (evalSN z)) =
              deltaSN (deltaSN (deltaSN .s0 (evalSN x)) (evalSN y)) (evalSN z) := by
            rw [hpx_st, ← evalSN_reduces_invariant hr_px]
            exact (deltaSN_s_law (evalSN x) (evalSN y) (evalSN z)).symm
          have hout_ne : deltaSN (deltaSN (deltaSN .s0 (evalSN x)) (evalSN y)) (evalSN z) ≠ .s38 := by
            change evalSN ((.s ⋅ x ⋅ y) ⋅ z) ≠ .s38
            rw [evalSN_reduces_invariant hr_n]
            exact isNF_evalSN_ne_inf n hnf_n
          exact absApp_sl2_closed
            (isNF_evalSN_ne_inf x hx_nf)
            (isNF_evalSN_ne_inf y hy_nf)
            hz_lt
            hout_ne
            (by change evalSN (x ⋅ z) ≠ .s38; rw [evalSN_reduces_invariant hr_px]; exact isNF_evalSN_ne_inf px hnf_px)
            (by rw [← hqy_st]; exact isNF_evalSN_ne_inf qy hnf_qy)
            (nfDescOf_mem_listBySt x hx_nf)
            hdp
            hout_eq
            hdres
      | var _ => cases hu
      | app _ _ => cases hu

def natLeB : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => natLeB a b

theorem natLeB_sound : ∀ {a b : Nat}, natLeB a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => by cases h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (natLeB_sound h)

/-- Outer-`allDesc` + `Nat.beq` Case-3 rank checker:
    `listBySt x` and `listAbsApp da z` are reduced ONCE per `(x, z)` in Lean's call-by-name kernel! -/
def checkC3RankXZ (x z : StateSN) : Bool :=
  if eq_StateSN x .s38 || eq_StateSN z .s38 || eq_StateSN (deltaSN x z) .s38 then true
  else
    checkAll1_StateSN (fun y =>
      if eq_StateSN y .s38 then true
      else
        let l_st := deltaSN (deltaSN .s0 x) y
        if !eq_StateSN (deltaSN l_st z) .s38 || eq_StateSN (deltaSN y z) .s38 then true
        else
          let r_cur := c3Rank ⟨.a2, l_st, tagOfSN x, tagOfSN y⟩ z
          natLeB 1 r_cur && natLeB r_cur 5) &&
    allDesc (fun da =>
      allDesc (fun ln =>
        if !eqArity ln.sl .a2 then true
        else
          checkAll1_StateSN (fun y =>
            if eq_StateSN y .s38 then true
            else
              let l_st := deltaSN (deltaSN .s0 x) y
              let z_next := deltaSN y z
              if !eq_StateSN (deltaSN l_st z) .s38 || eq_StateSN z_next .s38 then true
              else if eq_StateSN (deltaSN ln.st z_next) .s38 then
                natLeB (c3Rank ln z_next + 1) (c3Rank ⟨.a2, l_st, tagOfSN x, tagOfSN y⟩ z)
              else true))
        (listAbsApp da z))
      (listBySt x)

private theorem c3_rank_xz_0 : checkAll1_StateSN (fun z => checkC3RankXZ .s0 z) = true := rfl
private theorem c3_rank_xz_1 : checkAll1_StateSN (fun z => checkC3RankXZ .s1 z) = true := rfl
private theorem c3_rank_xz_2 : checkAll1_StateSN (fun z => checkC3RankXZ .s2 z) = true := rfl
private theorem c3_rank_xz_3 : checkAll1_StateSN (fun z => checkC3RankXZ .s3 z) = true := rfl
private theorem c3_rank_xz_4 : checkAll1_StateSN (fun z => checkC3RankXZ .s4 z) = true := rfl
private theorem c3_rank_xz_5 : checkAll1_StateSN (fun z => checkC3RankXZ .s5 z) = true := rfl
private theorem c3_rank_xz_6 : checkAll1_StateSN (fun z => checkC3RankXZ .s6 z) = true := rfl
private theorem c3_rank_xz_7 : checkAll1_StateSN (fun z => checkC3RankXZ .s7 z) = true := rfl
private theorem c3_rank_xz_8 : checkAll1_StateSN (fun z => checkC3RankXZ .s8 z) = true := rfl
private theorem c3_rank_xz_9 : checkAll1_StateSN (fun z => checkC3RankXZ .s9 z) = true := rfl
private theorem c3_rank_xz_10 : checkAll1_StateSN (fun z => checkC3RankXZ .s10 z) = true := rfl
private theorem c3_rank_xz_11 : checkAll1_StateSN (fun z => checkC3RankXZ .s11 z) = true := rfl
private theorem c3_rank_xz_12 : checkAll1_StateSN (fun z => checkC3RankXZ .s12 z) = true := rfl
private theorem c3_rank_xz_13 : checkAll1_StateSN (fun z => checkC3RankXZ .s13 z) = true := rfl
private theorem c3_rank_xz_14 : checkAll1_StateSN (fun z => checkC3RankXZ .s14 z) = true := rfl
private theorem c3_rank_xz_15 : checkAll1_StateSN (fun z => checkC3RankXZ .s15 z) = true := rfl
private theorem c3_rank_xz_16 : checkAll1_StateSN (fun z => checkC3RankXZ .s16 z) = true := rfl
private theorem c3_rank_xz_17 : checkAll1_StateSN (fun z => checkC3RankXZ .s17 z) = true := rfl
private theorem c3_rank_xz_18 : checkAll1_StateSN (fun z => checkC3RankXZ .s18 z) = true := rfl
private theorem c3_rank_xz_19 : checkAll1_StateSN (fun z => checkC3RankXZ .s19 z) = true := rfl
private theorem c3_rank_xz_20 : checkAll1_StateSN (fun z => checkC3RankXZ .s20 z) = true := rfl
private theorem c3_rank_xz_21 : checkAll1_StateSN (fun z => checkC3RankXZ .s21 z) = true := rfl
private theorem c3_rank_xz_22 : checkAll1_StateSN (fun z => checkC3RankXZ .s22 z) = true := rfl
private theorem c3_rank_xz_23 : checkAll1_StateSN (fun z => checkC3RankXZ .s23 z) = true := rfl
private theorem c3_rank_xz_24 : checkAll1_StateSN (fun z => checkC3RankXZ .s24 z) = true := rfl
private theorem c3_rank_xz_25 : checkAll1_StateSN (fun z => checkC3RankXZ .s25 z) = true := rfl
private theorem c3_rank_xz_26 : checkAll1_StateSN (fun z => checkC3RankXZ .s26 z) = true := rfl
private theorem c3_rank_xz_27 : checkAll1_StateSN (fun z => checkC3RankXZ .s27 z) = true := rfl
private theorem c3_rank_xz_28 : checkAll1_StateSN (fun z => checkC3RankXZ .s28 z) = true := rfl
private theorem c3_rank_xz_29 : checkAll1_StateSN (fun z => checkC3RankXZ .s29 z) = true := rfl
private theorem c3_rank_xz_30 : checkAll1_StateSN (fun z => checkC3RankXZ .s30 z) = true := rfl
private theorem c3_rank_xz_31 : checkAll1_StateSN (fun z => checkC3RankXZ .s31 z) = true := rfl
private theorem c3_rank_xz_32 : checkAll1_StateSN (fun z => checkC3RankXZ .s32 z) = true := rfl
private theorem c3_rank_xz_33 : checkAll1_StateSN (fun z => checkC3RankXZ .s33 z) = true := rfl
private theorem c3_rank_xz_34 : checkAll1_StateSN (fun z => checkC3RankXZ .s34 z) = true := rfl
private theorem c3_rank_xz_35 : checkAll1_StateSN (fun z => checkC3RankXZ .s35 z) = true := rfl
private theorem c3_rank_xz_36 : checkAll1_StateSN (fun z => checkC3RankXZ .s36 z) = true := rfl
private theorem c3_rank_xz_37 : checkAll1_StateSN (fun z => checkC3RankXZ .s37 z) = true := rfl
private theorem c3_rank_xz_38 : checkAll1_StateSN (fun z => checkC3RankXZ .s38 z) = true := rfl

theorem checkC3RankXZ_all (x z : StateSN) : checkC3RankXZ x z = true :=
  match x with
  | .s0 => checkAll1_StateSN_sound _ c3_rank_xz_0 z
  | .s1 => checkAll1_StateSN_sound _ c3_rank_xz_1 z
  | .s2 => checkAll1_StateSN_sound _ c3_rank_xz_2 z
  | .s3 => checkAll1_StateSN_sound _ c3_rank_xz_3 z
  | .s4 => checkAll1_StateSN_sound _ c3_rank_xz_4 z
  | .s5 => checkAll1_StateSN_sound _ c3_rank_xz_5 z
  | .s6 => checkAll1_StateSN_sound _ c3_rank_xz_6 z
  | .s7 => checkAll1_StateSN_sound _ c3_rank_xz_7 z
  | .s8 => checkAll1_StateSN_sound _ c3_rank_xz_8 z
  | .s9 => checkAll1_StateSN_sound _ c3_rank_xz_9 z
  | .s10 => checkAll1_StateSN_sound _ c3_rank_xz_10 z
  | .s11 => checkAll1_StateSN_sound _ c3_rank_xz_11 z
  | .s12 => checkAll1_StateSN_sound _ c3_rank_xz_12 z
  | .s13 => checkAll1_StateSN_sound _ c3_rank_xz_13 z
  | .s14 => checkAll1_StateSN_sound _ c3_rank_xz_14 z
  | .s15 => checkAll1_StateSN_sound _ c3_rank_xz_15 z
  | .s16 => checkAll1_StateSN_sound _ c3_rank_xz_16 z
  | .s17 => checkAll1_StateSN_sound _ c3_rank_xz_17 z
  | .s18 => checkAll1_StateSN_sound _ c3_rank_xz_18 z
  | .s19 => checkAll1_StateSN_sound _ c3_rank_xz_19 z
  | .s20 => checkAll1_StateSN_sound _ c3_rank_xz_20 z
  | .s21 => checkAll1_StateSN_sound _ c3_rank_xz_21 z
  | .s22 => checkAll1_StateSN_sound _ c3_rank_xz_22 z
  | .s23 => checkAll1_StateSN_sound _ c3_rank_xz_23 z
  | .s24 => checkAll1_StateSN_sound _ c3_rank_xz_24 z
  | .s25 => checkAll1_StateSN_sound _ c3_rank_xz_25 z
  | .s26 => checkAll1_StateSN_sound _ c3_rank_xz_26 z
  | .s27 => checkAll1_StateSN_sound _ c3_rank_xz_27 z
  | .s28 => checkAll1_StateSN_sound _ c3_rank_xz_28 z
  | .s29 => checkAll1_StateSN_sound _ c3_rank_xz_29 z
  | .s30 => checkAll1_StateSN_sound _ c3_rank_xz_30 z
  | .s31 => checkAll1_StateSN_sound _ c3_rank_xz_31 z
  | .s32 => checkAll1_StateSN_sound _ c3_rank_xz_32 z
  | .s33 => checkAll1_StateSN_sound _ c3_rank_xz_33 z
  | .s34 => checkAll1_StateSN_sound _ c3_rank_xz_34 z
  | .s35 => checkAll1_StateSN_sound _ c3_rank_xz_35 z
  | .s36 => checkAll1_StateSN_sound _ c3_rank_xz_36 z
  | .s37 => checkAll1_StateSN_sound _ c3_rank_xz_37 z
  | .s38 => checkAll1_StateSN_sound _ c3_rank_xz_38 z

def Case3StepLI (l z l' z' : Term) : Prop :=
  ∃ x y f1 f2,
    l = S ⋅ x ⋅ y ∧ isNF x = true ∧ isNF y = true ∧ isNF z = true ∧
    evalSN (l ⋅ z) = .s38 ∧
    normLI f1 (x ⋅ z) = some l' ∧ isNF2 l' = true ∧
    normLI f2 (y ⋅ z) = some z' ∧
    evalSN (l' ⋅ z') = .s38

def Case3StepRI (l z l' z' : Term) : Prop :=
  ∃ x y f1 f2,
    l = S ⋅ x ⋅ y ∧ isNF x = true ∧ isNF y = true ∧ isNF z = true ∧
    evalSN (l ⋅ z) = .s38 ∧
    normRI f1 (x ⋅ z) = some l' ∧ isNF2 l' = true ∧
    normRI f2 (y ⋅ z) = some z' ∧
    evalSN (l' ⋅ z') = .s38

theorem case3_rank_bounds_and_decrease_li {l z l' z' : Term} (h : Case3StepLI l z l' z') :
    1 ≤ c3Rank (nfDescOf l) (evalSN z) ∧
    c3Rank (nfDescOf l) (evalSN z) ≤ 5 ∧
    (∀ l'' z'', Case3StepLI l' z' l'' z'' →
      c3Rank (nfDescOf l') (evalSN z') < c3Rank (nfDescOf l) (evalSN z)) := by
  rcases h with ⟨x, y, f1, f2, rfl, hx, hy, hz, hlz38, hnl', hnf2_l', hnz', hl'z'38⟩
  have hnf_l' := isNF2_implies_isNF l' hnf2_l'
  rcases normLI_reduces_and_isNF f1 (x ⋅ z) l' hnl' with ⟨hr_l', _⟩
  rcases normLI_reduces_and_isNF f2 (y ⋅ z) z' hnz' with ⟨hr_z', hnf_z'⟩
  have hx_lt := isNF_evalSN_ne_inf x hx
  have hy_lt := isNF_evalSN_ne_inf y hy
  have hz_lt := isNF_evalSN_ne_inf z hz
  have hxz_lt : deltaSN (evalSN x) (evalSN z) ≠ .s38 := by
    change evalSN (x ⋅ z) ≠ .s38; rw [evalSN_reduces_invariant hr_l']; exact isNF_evalSN_ne_inf l' hnf_l'
  have hyz_lt : deltaSN (evalSN y) (evalSN z) ≠ .s38 := by
    change evalSN (y ⋅ z) ≠ .s38; rw [evalSN_reduces_invariant hr_z']; exact isNF_evalSN_ne_inf z' hnf_z'
  have hc := checkC3RankXZ_all (evalSN x) (evalSN z)
  unfold checkC3RankXZ at hc
  rw [eq_StateSN_false_of_ne hx_lt, eq_StateSN_false_of_ne hz_lt, eq_StateSN_false_of_ne hxz_lt] at hc
  simp (config := { failIfUnchanged := false }) at hc
  have hb_part := checkAll1_StateSN_sound _ hc.1 (evalSN y)
  have hd_part := allDesc_mem (allDesc_mem hc.2 (nfDescOf_mem_listBySt x hx)) (normLI_absApp_sound f1 x z l' hx hz hnl')
  have hby := eq_StateSN_false_of_ne hy_lt
  have hblz : eq_StateSN (deltaSN (deltaSN (deltaSN .s0 (evalSN x)) (evalSN y)) (evalSN z)) .s38 = true :=
    (eq_StateSN_iff _ _).mpr hlz38
  have hbyz := eq_StateSN_false_of_ne hyz_lt
  rw [hby, hblz, hbyz] at hb_part
  simp (config := { failIfUnchanged := false }) at hb_part
  have hsl2 : (nfDescOf l').sl = .a2 := (nfDescOf_sl2_iff_isNF2 l' hnf_l').mpr hnf2_l'
  have hear2 : eqArity .a2 .a2 = true := rfl
  rw [hsl2, hear2] at hd_part
  simp (config := { failIfUnchanged := false }) at hd_part
  have hd_y := checkAll1_StateSN_sound _ hd_part (evalSN y)
  rw [hby, hblz, hbyz] at hd_y
  simp (config := { failIfUnchanged := false }) at hd_y
  have hln_st : (nfDescOf l').st = evalSN l' := nfDescOf_st_eq l' hnf_l'
  have hz'_st : evalSN z' = deltaSN (evalSN y) (evalSN z) := (evalSN_reduces_invariant hr_z').symm
  have hln_38 : eq_StateSN (deltaSN (nfDescOf l').st (deltaSN (evalSN y) (evalSN z))) .s38 = true := by
    rw [hln_st, ← hz'_st]; exact (eq_StateSN_iff _ _).mpr hl'z'38
  rw [hln_38] at hd_y
  simp (config := { failIfUnchanged := false }) at hd_y
  have hlt := natLeB_sound hd_y
  rw [← hz'_st] at hlt
  exact ⟨natLeB_sound hb_part.1, natLeB_sound hb_part.2, fun _ _ _ => hlt⟩

theorem case3_rank_bounds_and_decrease_ri {l z l' z' : Term} (h : Case3StepRI l z l' z') :
    1 ≤ c3Rank (nfDescOf l) (evalSN z) ∧
    c3Rank (nfDescOf l) (evalSN z) ≤ 5 ∧
    (∀ l'' z'', Case3StepRI l' z' l'' z'' →
      c3Rank (nfDescOf l') (evalSN z') < c3Rank (nfDescOf l) (evalSN z)) := by
  rcases h with ⟨x, y, f1, f2, rfl, hx, hy, hz, hlz38, hnl', hnf2_l', hnz', hl'z'38⟩
  have hnf_l' := isNF2_implies_isNF l' hnf2_l'
  rcases normRI_reduces_and_isNF f1 (x ⋅ z) l' hnl' with ⟨hr_l', _⟩
  rcases normRI_reduces_and_isNF f2 (y ⋅ z) z' hnz' with ⟨hr_z', hnf_z'⟩
  have hx_lt := isNF_evalSN_ne_inf x hx
  have hy_lt := isNF_evalSN_ne_inf y hy
  have hz_lt := isNF_evalSN_ne_inf z hz
  have hxz_lt : deltaSN (evalSN x) (evalSN z) ≠ .s38 := by
    change evalSN (x ⋅ z) ≠ .s38; rw [evalSN_reduces_invariant hr_l']; exact isNF_evalSN_ne_inf l' hnf_l'
  have hyz_lt : deltaSN (evalSN y) (evalSN z) ≠ .s38 := by
    change evalSN (y ⋅ z) ≠ .s38; rw [evalSN_reduces_invariant hr_z']; exact isNF_evalSN_ne_inf z' hnf_z'
  have hc := checkC3RankXZ_all (evalSN x) (evalSN z)
  unfold checkC3RankXZ at hc
  rw [eq_StateSN_false_of_ne hx_lt, eq_StateSN_false_of_ne hz_lt, eq_StateSN_false_of_ne hxz_lt] at hc
  simp (config := { failIfUnchanged := false }) at hc
  have hb_part := checkAll1_StateSN_sound _ hc.1 (evalSN y)
  have hd_part := allDesc_mem (allDesc_mem hc.2 (nfDescOf_mem_listBySt x hx)) (normRI_absApp_sound f1 x z l' hx hz hnl')
  have hby := eq_StateSN_false_of_ne hy_lt
  have hblz : eq_StateSN (deltaSN (deltaSN (deltaSN .s0 (evalSN x)) (evalSN y)) (evalSN z)) .s38 = true :=
    (eq_StateSN_iff _ _).mpr hlz38
  have hbyz := eq_StateSN_false_of_ne hyz_lt
  rw [hby, hblz, hbyz] at hb_part
  simp (config := { failIfUnchanged := false }) at hb_part
  have hsl2 : (nfDescOf l').sl = .a2 := (nfDescOf_sl2_iff_isNF2 l' hnf_l').mpr hnf2_l'
  have hear2 : eqArity .a2 .a2 = true := rfl
  rw [hsl2, hear2] at hd_part
  simp (config := { failIfUnchanged := false }) at hd_part
  have hd_y := checkAll1_StateSN_sound _ hd_part (evalSN y)
  rw [hby, hblz, hbyz] at hd_y
  simp (config := { failIfUnchanged := false }) at hd_y
  have hln_st : (nfDescOf l').st = evalSN l' := nfDescOf_st_eq l' hnf_l'
  have hz'_st : evalSN z' = deltaSN (evalSN y) (evalSN z) := (evalSN_reduces_invariant hr_z').symm
  have hln_38 : eq_StateSN (deltaSN (nfDescOf l').st (deltaSN (evalSN y) (evalSN z))) .s38 = true := by
    rw [hln_st, ← hz'_st]; exact (eq_StateSN_iff _ _).mpr hl'z'38
  rw [hln_38] at hd_y
  simp (config := { failIfUnchanged := false }) at hd_y
  have hlt := natLeB_sound hd_y
  rw [← hz'_st] at hlt
  exact ⟨natLeB_sound hb_part.1, natLeB_sound hb_part.2, fun _ _ _ => hlt⟩

/-- **Theorem 5.2 (Resolution of Conjecture 2.2 — Sharp 5-Step Consecutive Case-3 Ceiling):** -/
theorem no_six_consecutive_case3_li (l0 z0 l1 z1 l2 z2 l3 z3 l4 z4 l5 z5 l6 z6 : Term)
    (h1 : Case3StepLI l0 z0 l1 z1)
    (h2 : Case3StepLI l1 z1 l2 z2)
    (h3 : Case3StepLI l2 z2 l3 z3)
    (h4 : Case3StepLI l3 z3 l4 z4)
    (h5 : Case3StepLI l4 z4 l5 z5)
    (h6 : Case3StepLI l5 z5 l6 z6) : False := by
  rcases case3_rank_bounds_and_decrease_li h1 with ⟨_, hr0_le5, hdec01⟩
  rcases case3_rank_bounds_and_decrease_li h2 with ⟨_, _, hdec12⟩
  rcases case3_rank_bounds_and_decrease_li h3 with ⟨_, _, hdec23⟩
  rcases case3_rank_bounds_and_decrease_li h4 with ⟨_, _, hdec34⟩
  rcases case3_rank_bounds_and_decrease_li h5 with ⟨_, _, hdec45⟩
  rcases case3_rank_bounds_and_decrease_li h6 with ⟨hr5_ge1, _, _⟩
  have d01 := hdec01 l2 z2 h2
  have d12 := hdec12 l3 z3 h3
  have d23 := hdec23 l4 z4 h4
  have d34 := hdec34 l5 z5 h5
  have d45 := hdec45 l6 z6 h6
  have ge2 : 2 ≤ c3Rank (nfDescOf l4) (evalSN z4) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hr5_ge1 d45)
  have ge3 : 3 ≤ c3Rank (nfDescOf l3) (evalSN z3) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ge2 d34)
  have ge4 : 4 ≤ c3Rank (nfDescOf l2) (evalSN z2) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ge3 d23)
  have ge5 : 5 ≤ c3Rank (nfDescOf l1) (evalSN z1) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ge4 d12)
  have ge6 : 6 ≤ c3Rank (nfDescOf l0) (evalSN z0) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ge5 d01)
  have hbad := Nat.lt_of_lt_of_le (by decide : 5 < 6) (Nat.le_trans ge6 hr0_le5)
  exact Nat.lt_irrefl 5 hbad

theorem no_six_consecutive_case3_ri (l0 z0 l1 z1 l2 z2 l3 z3 l4 z4 l5 z5 l6 z6 : Term)
    (h1 : Case3StepRI l0 z0 l1 z1)
    (h2 : Case3StepRI l1 z1 l2 z2)
    (h3 : Case3StepRI l2 z2 l3 z3)
    (h4 : Case3StepRI l3 z3 l4 z4)
    (h5 : Case3StepRI l4 z4 l5 z5)
    (h6 : Case3StepRI l5 z5 l6 z6) : False := by
  rcases case3_rank_bounds_and_decrease_ri h1 with ⟨_, hr0_le5, hdec01⟩
  rcases case3_rank_bounds_and_decrease_ri h2 with ⟨_, _, hdec12⟩
  rcases case3_rank_bounds_and_decrease_ri h3 with ⟨_, _, hdec23⟩
  rcases case3_rank_bounds_and_decrease_ri h4 with ⟨_, _, hdec34⟩
  rcases case3_rank_bounds_and_decrease_ri h5 with ⟨_, _, hdec45⟩
  rcases case3_rank_bounds_and_decrease_ri h6 with ⟨hr5_ge1, _, _⟩
  have d01 := hdec01 l2 z2 h2
  have d12 := hdec12 l3 z3 h3
  have d23 := hdec23 l4 z4 h4
  have d34 := hdec34 l5 z5 h5
  have d45 := hdec45 l6 z6 h6
  have ge2 : 2 ≤ c3Rank (nfDescOf l4) (evalSN z4) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hr5_ge1 d45)
  have ge3 : 3 ≤ c3Rank (nfDescOf l3) (evalSN z3) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ge2 d34)
  have ge4 : 4 ≤ c3Rank (nfDescOf l2) (evalSN z2) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ge3 d23)
  have ge5 : 5 ≤ c3Rank (nfDescOf l1) (evalSN z1) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ge4 d12)
  have ge6 : 6 ≤ c3Rank (nfDescOf l0) (evalSN z0) := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ge5 d01)
  have hbad := Nat.lt_of_lt_of_le (by decide : 5 < 6) (Nat.le_trans ge6 hr0_le5)
  exact Nat.lt_irrefl 5 hbad

def W_L0 : Term := S ⋅ (S ⋅ (S ⋅ A_comb)) ⋅ S
def W_Z0 : Term := S
def W_L1 : Term := S ⋅ (S ⋅ A_comb) ⋅ S
def W_Z1 : Term := T_comb
def W_L2 : Term := S ⋅ A_comb ⋅ T_comb
def W_Z2 : Term := B_comb
def W_L3 : Term := S ⋅ B_comb ⋅ (S ⋅ B_comb)
def W_Z3 : Term := S ⋅ S ⋅ B_comb
def W_L4 : Term := S ⋅ T_comb ⋅ (S ⋅ S ⋅ B_comb)
def W_Z4 : Term := S ⋅ B_comb ⋅ (S ⋅ S ⋅ B_comb)
def W_L5 : Term := S ⋅ S ⋅ W_Z4
def W_Z5 : Term := S ⋅ W_Z4 ⋅ (S ⋅ T_comb ⋅ W_Z4)

theorem five_consecutive_case3_sharp :
    Case3StepLI W_L0 W_Z0 W_L1 W_Z1 ∧
    Case3StepLI W_L1 W_Z1 W_L2 W_Z2 ∧
    Case3StepLI W_L2 W_Z2 W_L3 W_Z3 ∧
    Case3StepLI W_L3 W_Z3 W_L4 W_Z4 ∧
    Case3StepLI W_L4 W_Z4 W_L5 W_Z5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨S ⋅ (S ⋅ A_comb), S, 0, 0, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨S ⋅ A_comb, S, 0, 0, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨A_comb, T_comb, 2, 0, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨B_comb, S ⋅ B_comb, 0, 0, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨T_comb, S ⋅ S ⋅ B_comb, 0, 2, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem z_rs_strict_inc_case3 {l z l' z' : Term} (h : Case3StepLI l z l' z') :
    rs z + 1 ≤ rs l' ∧ rs z + 1 ≤ rs z' := by
  rcases h with ⟨x, y, f1, f2, _, _, _, _, _, hnl', _, hnz', _⟩
  rcases normLI_reduces_and_isNF f1 (x ⋅ z) l' hnl' with ⟨hr_l', _⟩
  rcases normLI_reduces_and_isNF f2 (y ⋅ z) z' hnz' with ⟨hr_z', _⟩
  exact ⟨rs_mono_reduces hr_l', rs_mono_reduces hr_z'⟩

end ZeroNavigatorFixedOrder

#print axioms ZeroNavigatorFixedOrder.pure_line_all_six_coincide
#print axioms ZeroNavigatorFixedOrder.zachos_unified_quadratic_trace
#print axioms ZeroNavigatorFixedOrder.order_le_three_no_hnf2
#print axioms ZeroNavigatorFixedOrder.closed_two_var_reduces_hnf2_iff
#print axioms ZeroNavigatorFixedOrder.three_var_hnf_head_in_xy
#print axioms ZeroNavigatorFixedOrder.inf_head_tail_frozen_iterLO
#print axioms ZeroNavigatorFixedOrder.hn_spine_horizon_five
#print axioms ZeroNavigatorFixedOrder.hn_spine_horizon_five_sharp
#print axioms ZeroNavigatorFixedOrder.ro_right_non_sn_trap
#print axioms ZeroNavigatorFixedOrder.deltaSN_no_direct_nand_or_xor
#print axioms ZeroNavigatorFixedOrder.no_six_consecutive_case3_li
#print axioms ZeroNavigatorFixedOrder.no_six_consecutive_case3_ri
#print axioms ZeroNavigatorFixedOrder.five_consecutive_case3_sharp
#print axioms ZeroNavigatorFixedOrder.z_rs_strict_inc_case3
