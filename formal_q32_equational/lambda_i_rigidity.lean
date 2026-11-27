import formal_q32_equational.lam_beta_cr

/-!
# `λI` Leaf & Multiplicity Bounds, Spine Inversion, and Small-Term Rigidity (Theorem A)

Establishes for all pure-`S` terms `t : FormalAlgebra.Term`:
1. The `validSLam` invariant (`λI` non-erasure, subterm `Φ ≥ 1`, and single-`λ` binder
   multiplicity `≥ 2`) preserved under all `β`-reductions.
2. Exact leaf conservation/growth `leaves t + numLam B ≤ varLeaves B` and free-variable
   multiplicity monotonicity `countVar v t ≤ countFVar v B` along `toLam t →_β* B`.
3. Constructive `CL(S)` normalization of any pure-`S` term whose `λ`-translation has a `β`-NF.
4. Free-variable head spine inversion (`fvar_head_inversion`) and `S`-free exactness.
5. **Theorem A**: Global `λβ`-rigidity in `Ter(CL(S))` of `.var x`, `S`, `S S`, and `S S S`,
   plus isolated-normal-form verification and `λβ`-equivalence of Waldmann's `(8, 11)` closed
   pair and its new 2-variable open `(8, 11)` schematic generalization.

Zero `sorry`, zero `Classical.choice`, zero `native_decide`, zero custom axioms.
-/

namespace FormalQ32

open FormalAlgebra

/-! ## 1. Computable `β`-Normalizer and `IsBetaNF` Checker (Kernel `rfl`) -/

def isLam : Lam → Bool
  | .lam _ => true
  | _ => false

def isBetaNFBool : Lam → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .lam m => isBetaNFBool m
  | .app a b => !isLam a && isBetaNFBool a && isBetaNFBool b

theorem isBetaNF_of_bool {t : Lam} (h : isBetaNFBool t = true) : IsBetaNF t := by
  induction t with
  | bvar _ => intro _ hs; cases hs
  | fvar _ => intro _ hs; cases hs
  | lam m ih =>
    simp only [isBetaNFBool] at h
    intro t' hs
    cases hs with
    | lam hm => exact ih h _ hm
  | app a b iha ihb =>
    simp only [isBetaNFBool, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with ⟨⟨hnl, ha⟩, hb⟩
    intro t' hs
    cases hs with
    | root m _ => simp [isLam] at hnl
    | left ha' => exact iha ha _ ha'
    | right hb' => exact ihb hb _ hb'

theorem bool_of_isBetaNF {t : Lam} (h : IsBetaNF t) : isBetaNFBool t = true := by
  induction t with
  | bvar _ => rfl
  | fvar _ => rfl
  | lam m ih =>
    simp only [isBetaNFBool]
    exact ih (fun m' hm => h (.lam m') (.lam hm))
  | app a b iha ihb =>
    have hnl : isLam a = false := by
      cases a with
      | bvar _ => rfl
      | fvar _ => rfl
      | app _ _ => rfl
      | lam m => exfalso; exact h _ (.root m b)
    have ha : isBetaNFBool a = true := iha (fun a' ha' => h (a' ∘ₗ b) (.left ha'))
    have hb : isBetaNFBool b = true := ihb (fun b' hb' => h (a ∘ₗ b') (.right hb'))
    simp only [isBetaNFBool, hnl, ha, hb, Bool.not_false, Bool.and_self]

theorem isLam_preserved_betaStep {a b : Lam} (h : isLam a = true) (hs : BetaStep a b) :
    isLam b = true := by
  cases a with
  | bvar _ => cases h
  | fvar _ => cases h
  | app _ _ => cases h
  | lam _ => cases hs; rfl

theorem lam_preserved_betaReduces {m b : Lam} (hr : BetaReduces (.lam m) b) :
    ∃ m', b = .lam m' ∧ BetaReduces m m' := by
  generalize hlm : Lam.lam m = lm at hr
  induction hr generalizing m with
  | refl _ => exact ⟨m, hlm.symm, .refl m⟩
  | @next _ mid _ hs _ ih =>
    subst hlm
    cases hs with
    | @lam _ m1 hm1 =>
      obtain ⟨m', hbm', hm1'⟩ := ih rfl
      exact ⟨m', hbm', .next hm1 hm1'⟩

def betaStepOpt : Lam → Option Lam
  | .bvar _ => none
  | .fvar _ => none
  | .lam m =>
      match betaStepOpt m with
      | some m' => some (.lam m')
      | none => none
  | .app (.lam m) n => some (substB 0 n m)
  | .app a b =>
      match betaStepOpt a with
      | some a' => some (a' ∘ₗ b)
      | none =>
          match betaStepOpt b with
          | some b' => some (a ∘ₗ b')
          | none => none

private theorem betaStepOpt_non_lam (a b : Lam) (hnl : isLam a = false) :
    betaStepOpt (a ∘ₗ b) =
      match betaStepOpt a with
      | some a' => some (a' ∘ₗ b)
      | none =>
          match betaStepOpt b with
          | some b' => some (a ∘ₗ b')
          | none => none := by
  cases a with
  | bvar _ => rfl
  | fvar _ => rfl
  | app _ _ => rfl
  | lam _ => cases hnl

theorem betaStepOpt_some {t t' : Lam} (h : betaStepOpt t = some t') : BetaStep t t' := by
  induction t generalizing t' with
  | bvar _ => cases h
  | fvar _ => cases h
  | lam m ih =>
    simp only [betaStepOpt] at h
    cases hm : betaStepOpt m with
    | none => rw [hm] at h; cases h
    | some m' =>
      rw [hm] at h
      injection h with heq
      rw [← heq]
      exact .lam (ih hm)
  | app a b iha ihb =>
    cases a with
    | lam m =>
      simp only [betaStepOpt] at h
      injection h with heq
      rw [← heq]
      exact .root m b
    | bvar i =>
      rw [betaStepOpt_non_lam (.bvar i) b rfl] at h
      simp only [betaStepOpt] at h
      cases hb : betaStepOpt b with
      | none => rw [hb] at h; cases h
      | some b' => rw [hb] at h; injection h with heq; rw [← heq]; exact .right (ihb hb)
    | fvar v =>
      rw [betaStepOpt_non_lam (.fvar v) b rfl] at h
      simp only [betaStepOpt] at h
      cases hb : betaStepOpt b with
      | none => rw [hb] at h; cases h
      | some b' => rw [hb] at h; injection h with heq; rw [← heq]; exact .right (ihb hb)
    | app u w =>
      rw [betaStepOpt_non_lam (u ∘ₗ w) b rfl] at h
      cases ha : betaStepOpt (u ∘ₗ w) with
      | some a' => rw [ha] at h; injection h with heq; rw [← heq]; exact .left (iha ha)
      | none =>
        rw [ha] at h
        cases hb : betaStepOpt b with
        | none => rw [hb] at h; cases h
        | some b' => rw [hb] at h; injection h with heq; rw [← heq]; exact .right (ihb hb)

def betaSteps : Nat → Lam → Lam
  | 0, t => t
  | fuel + 1, t =>
      match betaStepOpt t with
      | some t' => betaSteps fuel t'
      | none => t

theorem betaSteps_reduces (fuel : Nat) (t : Lam) : BetaReduces t (betaSteps fuel t) := by
  induction fuel generalizing t with
  | zero => exact .refl t
  | succ f ih =>
    simp only [betaSteps]
    cases hs : betaStepOpt t with
    | none => exact .refl t
    | some t' => exact .next (betaStepOpt_some hs) (ih t')

/-! ## 2. `λI` Quantitative Invariants (`varLeaves`, `numLam`, `countFVar`, `validSLam`) -/

def varLeaves : Lam → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .lam m => varLeaves m
  | .app a b => varLeaves a + varLeaves b

def numLam : Lam → Nat
  | .bvar _ => 0
  | .fvar _ => 0
  | .lam m => 1 + numLam m
  | .app a b => numLam a + numLam b

def countBVar (idx : Nat) : Lam → Nat
  | .bvar i => if i = idx then 1 else 0
  | .fvar _ => 0
  | .lam m => countBVar (idx + 1) m
  | .app a b => countBVar idx a + countBVar idx b

def countFVar (v : Nat) : Lam → Nat
  | .bvar _ => 0
  | .fvar k => if k = v then 1 else 0
  | .lam m => countFVar v m
  | .app a b => countFVar v a + countFVar v b

def countVar (v : Nat) : Term → Nat
  | .s => 0
  | .var k => if k = v then 1 else 0
  | .app a b => countVar v a + countVar v b

def validSLam : Lam → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .lam m =>
      validSLam m &&
      decide (1 ≤ countBVar 0 m) &&
      decide (numLam m + 2 ≤ varLeaves m) &&
      (isLam m || decide (2 ≤ countBVar 0 m))
  | .app a b => validSLam a && validSLam b

theorem posPhi_of_validSLam {t : Lam} (h : validSLam t = true) :
    numLam t + 1 ≤ varLeaves t := by
  induction t with
  | bvar _ => exact Nat.le_refl 1
  | fvar _ => exact Nat.le_refl 1
  | lam m _ =>
    simp only [validSLam, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨_, _⟩, hphi⟩, _⟩
    simp only [numLam, varLeaves]
    rw [Nat.add_comm 1 (numLam m), Nat.add_assoc]
    exact hphi
  | app a b iha ihb =>
    simp only [validSLam, Bool.and_eq_true] at h
    have ha := iha h.1
    have hb := ihb h.2
    simp only [numLam, varLeaves]
    have hsum := Nat.add_le_add ha hb
    have hle : numLam a + numLam b + 1 ≤ (numLam a + 1) + (numLam b + 1) := by
      rw [Nat.add_assoc (numLam a) 1 (numLam b + 1), Nat.add_comm 1 (numLam b + 1),
          ← Nat.add_assoc (numLam a) (numLam b + 1) 1, ← Nat.add_assoc (numLam a) (numLam b) 1]
      exact Nat.le_succ _
    exact Nat.le_trans hle hsum

theorem varLeaves_shift (d c : Nat) (t : Lam) : varLeaves (shift d c t) = varLeaves t := by
  induction t generalizing c with
  | bvar _ => simp only [shift]; split <;> rfl
  | fvar _ => rfl
  | lam m ih => exact ih (c + 1)
  | app m n ihm ihn => simp only [shift, varLeaves, ihm c, ihn c]

theorem numLam_shift (d c : Nat) (t : Lam) : numLam (shift d c t) = numLam t := by
  induction t generalizing c with
  | bvar _ => simp only [shift]; split <;> rfl
  | fvar _ => rfl
  | lam m ih => simp only [shift, numLam, ih (c + 1)]
  | app m n ihm ihn => simp only [shift, numLam, ihm c, ihn c]

theorem isLam_shift (d c : Nat) (t : Lam) : isLam (shift d c t) = isLam t := by
  cases t with
  | bvar _ => simp only [shift]; split <;> rfl
  | fvar _ => rfl
  | lam _ => rfl
  | app _ _ => rfl

theorem countFVar_shift (v d c : Nat) (t : Lam) : countFVar v (shift d c t) = countFVar v t := by
  induction t generalizing c with
  | bvar _ => simp only [shift]; split <;> rfl
  | fvar _ => rfl
  | lam m ih => exact ih (c + 1)
  | app m n ihm ihn => simp only [shift, countFVar, ihm c, ihn c]

theorem countBVar_shift_lt {idx d c : Nat} (hlt : idx < c) (t : Lam) :
    countBVar idx (shift d c t) = countBVar idx t := by
  induction t generalizing idx c with
  | bvar i =>
    simp only [shift]
    by_cases hci : c ≤ i
    · have hne1 : i + d ≠ idx := Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt (Nat.le_trans hci (Nat.le_add_right i d)))
      have hne2 : i ≠ idx := Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt hci)
      simp only [if_pos hci, countBVar, if_neg hne1, if_neg hne2]
    · simp only [if_neg hci]
  | fvar _ => rfl
  | lam m ih => exact ih (Nat.add_lt_add_right hlt 1)
  | app m n ihm ihn => simp only [shift, countBVar, ihm hlt, ihn hlt]

theorem countBVar_shift_mid {idx k c : Nat} (hle : c ≤ idx) (hlt : idx < c + k) (u : Lam) :
    countBVar idx (shift k c u) = 0 := by
  induction u generalizing idx c with
  | bvar i =>
    simp only [shift]
    by_cases hci : c ≤ i
    · have hne : i + k ≠ idx := Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt (Nat.add_le_add_right hci k))
      simp only [if_pos hci, countBVar, if_neg hne]
    · have hne : i ≠ idx := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.not_le.mp hci) hle)
      simp only [if_neg hci, countBVar, if_neg hne]
  | fvar _ => rfl
  | lam m ih =>
    have hle' : c + 1 ≤ idx + 1 := Nat.add_le_add_right hle 1
    have hlt' : idx + 1 < (c + 1) + k := by
      rw [Nat.add_assoc c 1 k, Nat.add_comm 1 k, ← Nat.add_assoc c k 1]
      exact Nat.add_lt_add_right hlt 1
    exact ih hle' hlt'
  | app m n ihm ihn =>
    simp only [shift, countBVar, ihm hle hlt, ihn hle hlt]

theorem countBVar_shift_add {idx c : Nat} (k : Nat) (hci : c ≤ idx) (u : Lam) :
    countBVar (idx + k) (shift k c u) = countBVar idx u := by
  induction u generalizing idx c with
  | bvar i =>
    simp only [shift]
    by_cases hc_i : c ≤ i
    · simp only [if_pos hc_i, countBVar]
      by_cases heq : i = idx
      · subst heq; simp only [↓reduceIte]
      · have hne : i + k ≠ idx + k := fun hh => heq (Nat.add_right_cancel hh)
        simp only [if_neg heq, if_neg hne]
    · have hlt : i < c := Nat.not_le.mp hc_i
      have hne1 : i ≠ idx + k :=
        Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt (Nat.le_trans hci (Nat.le_add_right idx k)))
      have hne2 : i ≠ idx := Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt hci)
      simp only [if_neg hc_i, countBVar, if_neg hne1, if_neg hne2]
  | fvar _ => rfl
  | lam m ih =>
    have hci' : c + 1 ≤ idx + 1 := Nat.add_le_add_right hci 1
    have heq : (idx + k) + 1 = (idx + 1) + k := by
      rw [Nat.add_assoc idx k 1, Nat.add_comm k 1, ← Nat.add_assoc idx 1 k]
    simp only [shift, countBVar, heq, ih hci']
  | app m n ihm ihn =>
    simp only [shift, countBVar, ihm hci, ihn hci]

theorem varLeaves_substB_eq (k : Nat) (u m : Lam) :
    varLeaves (substB k u m) + countBVar k m = varLeaves m + countBVar k m * varLeaves u := by
  induction m generalizing k with
  | bvar i =>
    simp only [substB, countBVar]
    by_cases hik : i < k
    · have hne : i ≠ k := Nat.ne_of_lt hik
      simp only [if_pos hik, if_neg hne, varLeaves, Nat.zero_mul, Nat.add_zero]
    · simp only [if_neg hik]
      by_cases heq : i = k
      · subst heq
        simp only [↓reduceIte, varLeaves_shift, varLeaves, Nat.one_mul, Nat.add_comm]
      · simp only [if_neg heq, varLeaves, Nat.zero_mul, Nat.add_zero]
  | fvar _ => simp only [substB, varLeaves, countBVar, Nat.zero_mul, Nat.add_zero]
  | lam body ih => exact ih (k + 1)
  | app a b iha ihb =>
    simp only [substB, varLeaves, countBVar]
    have ha := iha k
    have hb := ihb k
    calc
      (varLeaves (substB k u a) + varLeaves (substB k u b)) + (countBVar k a + countBVar k b)
        = (varLeaves (substB k u a) + countBVar k a) + (varLeaves (substB k u b) + countBVar k b) := by
            rw [Nat.add_assoc (varLeaves (substB k u a)),
                ← Nat.add_assoc (varLeaves (substB k u b)),
                Nat.add_comm (varLeaves (substB k u b)) (countBVar k a),
                Nat.add_assoc (countBVar k a), ← Nat.add_assoc]
      _ = (varLeaves a + countBVar k a * varLeaves u) + (varLeaves b + countBVar k b * varLeaves u) := by
            rw [ha, hb]
      _ = (varLeaves a + varLeaves b) + (countBVar k a + countBVar k b) * varLeaves u := by
            rw [Nat.add_mul, Nat.add_assoc (varLeaves a),
                ← Nat.add_assoc (countBVar k a * varLeaves u),
                Nat.add_comm (countBVar k a * varLeaves u) (varLeaves b),
                Nat.add_assoc (varLeaves b), ← Nat.add_assoc]

theorem numLam_substB_eq (k : Nat) (u m : Lam) :
    numLam (substB k u m) = numLam m + countBVar k m * numLam u := by
  induction m generalizing k with
  | bvar i =>
    simp only [substB, countBVar, numLam]
    by_cases hik : i < k
    · have hne : i ≠ k := Nat.ne_of_lt hik
      simp only [if_pos hik, if_neg hne, numLam, Nat.zero_mul]
    · simp only [if_neg hik]
      by_cases heq : i = k
      · subst heq
        simp only [↓reduceIte, numLam_shift, Nat.one_mul, Nat.zero_add]
      · simp only [if_neg heq, numLam, Nat.zero_mul]
  | fvar _ => simp only [substB, numLam, countBVar, Nat.zero_mul, Nat.add_zero]
  | lam body ih =>
    simp only [substB, numLam, countBVar, ih (k + 1), Nat.add_assoc]
  | app a b iha ihb =>
    simp only [substB, numLam, countBVar, iha k, ihb k, Nat.add_mul]
    rw [Nat.add_assoc (numLam a), ← Nat.add_assoc (countBVar k a * numLam u),
        Nat.add_comm (countBVar k a * numLam u) (numLam b),
        Nat.add_assoc (numLam b), ← Nat.add_assoc]

theorem countFVar_substB_eq (v k : Nat) (u m : Lam) :
    countFVar v (substB k u m) = countFVar v m + countBVar k m * countFVar v u := by
  induction m generalizing k with
  | bvar i =>
    simp only [substB, countBVar, countFVar]
    by_cases hik : i < k
    · have hne : i ≠ k := Nat.ne_of_lt hik
      simp only [if_pos hik, if_neg hne, countFVar, Nat.zero_mul]
    · simp only [if_neg hik]
      by_cases heq : i = k
      · subst heq
        simp only [↓reduceIte, countFVar_shift, Nat.one_mul, Nat.zero_add]
      · simp only [if_neg heq, countFVar, Nat.zero_mul]
  | fvar _ => simp only [substB, countBVar, Nat.zero_mul, Nat.add_zero]
  | lam body ih => exact ih (k + 1)
  | app a b iha ihb =>
    simp only [substB, countFVar, countBVar, iha k, ihb k, Nat.add_mul]
    rw [Nat.add_assoc (countFVar v a), ← Nat.add_assoc (countBVar k a * countFVar v u),
        Nat.add_comm (countBVar k a * countFVar v u) (countFVar v b),
        Nat.add_assoc (countFVar v b), ← Nat.add_assoc]

theorem countBVar_substB_lt {idx k : Nat} (hlt : idx < k) (u t : Lam) :
    countBVar idx (substB k u t) = countBVar idx t := by
  induction t generalizing idx k with
  | bvar i =>
    simp only [substB]
    by_cases hik : i < k
    · simp only [if_pos hik]
    · simp only [if_neg hik]
      by_cases heq : i = k
      · subst heq
        have hne : i ≠ idx := Nat.ne_of_gt hlt
        simp only [↓reduceIte, countBVar, if_neg hne]
        exact countBVar_shift_mid (Nat.zero_le idx) (by rw [Nat.zero_add]; exact hlt) u
      · have hgt : k < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hik) (Ne.symm heq)
        have hpos : 1 ≤ i := Nat.lt_of_le_of_lt (Nat.zero_le k) hgt
        have hne1 : i - 1 ≠ idx := by
          cases i with
          | zero => cases hpos
          | succ i' =>
            simp only [Nat.succ_sub_one]
            exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hgt))
        have hne2 : i ≠ idx := Nat.ne_of_gt (Nat.lt_trans hlt hgt)
        simp only [if_neg heq, countBVar, if_neg hne1, if_neg hne2]
  | fvar _ => rfl
  | lam m ih => exact ih (Nat.add_lt_add_right hlt 1)
  | app a b iha ihb => simp only [substB, countBVar, iha hlt, ihb hlt]

theorem countBVar_substB_ge (idx k : Nat) (u t : Lam) :
    countBVar (idx + k) (substB k u t) =
      countBVar (idx + k + 1) t + countBVar k t * countBVar idx u := by
  induction t generalizing idx k with
  | bvar i =>
    simp only [substB, countBVar]
    by_cases hik : i < k
    · have hlt1 : i < idx + k := Nat.lt_of_lt_of_le hik (Nat.le_add_left k idx)
      have hne0 : i ≠ idx + k := Nat.ne_of_lt hlt1
      have hne1 : i ≠ idx + k + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt hlt1)
      have hnek : i ≠ k := Nat.ne_of_lt hik
      simp only [if_pos hik, countBVar, if_neg hne0, if_neg hne1, if_neg hnek, Nat.zero_mul]
    · simp only [if_neg hik]
      by_cases heq : i = k
      · subst heq
        have hne1 : i ≠ idx + i + 1 :=
          Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_add_left i idx))
        simp only [↓reduceIte, if_neg hne1, Nat.one_mul, Nat.zero_add]
        exact countBVar_shift_add i (Nat.zero_le idx) u
      · have hgt : k < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hik) (Ne.symm heq)
        simp only [if_neg heq, Nat.zero_mul, Nat.add_zero]
        cases i with
        | zero => cases hgt
        | succ i' =>
          simp only [Nat.succ_sub_one, countBVar]
          by_cases heq' : i' = idx + k
          · subst heq'; simp only [↓reduceIte]
          · have hne' : i' + 1 ≠ idx + k + 1 := fun hh => heq' (Nat.succ.inj hh)
            simp only [if_neg heq', if_neg hne']
  | fvar _ => simp only [substB, countBVar, Nat.zero_mul]
  | lam m ih =>
    have heq1 : (idx + k) + 1 = idx + (k + 1) := Nat.add_assoc idx k 1
    have heq2 : idx + (k + 1) + 1 = (idx + k + 1) + 1 := by
      rw [← Nat.add_assoc idx k 1]
    simp only [substB, countBVar, heq1, ih idx (k + 1), heq2]
  | app a b iha ihb =>
    simp only [substB, countBVar, iha idx k, ihb idx k, Nat.add_mul]
    rw [Nat.add_assoc (countBVar (idx + k + 1) a),
        ← Nat.add_assoc (countBVar k a * countBVar idx u),
        Nat.add_comm (countBVar k a * countBVar idx u) (countBVar (idx + k + 1) b),
        Nat.add_assoc (countBVar (idx + k + 1) b), ← Nat.add_assoc]

theorem validSLam_shift (d c : Nat) (t : Lam) : validSLam (shift d c t) = validSLam t := by
  induction t generalizing c with
  | bvar _ => simp only [shift]; split <;> rfl
  | fvar _ => rfl
  | lam m ih =>
    simp only [shift, validSLam, ih (c + 1),
               countBVar_shift_lt (Nat.zero_lt_succ c) m,
               numLam_shift, varLeaves_shift, isLam_shift]
  | app a b iha ihb => simp only [shift, validSLam, iha c, ihb c]

private theorem mul_succ_le_mul {a b : Nat} (c : Nat) (hle : a + 1 ≤ b) :
    c * a + c ≤ c * b := by
  have hm := Nat.mul_le_mul_left c hle
  rw [Nat.mul_add, Nat.mul_one] at hm
  exact hm

theorem validSLam_substB (k : Nat) {u m : Lam}
    (hu : validSLam u = true) (hm : validSLam m = true) :
    validSLam (substB k u m) = true := by
  induction m generalizing k with
  | bvar i =>
    simp only [substB]
    split
    · rfl
    · split
      · rw [validSLam_shift]; exact hu
      · rfl
  | fvar _ => rfl
  | app a b iha ihb =>
    simp only [substB, validSLam, Bool.and_eq_true] at hm ⊢
    exact ⟨iha k hm.1, ihb k hm.2⟩
  | lam body ih =>
    simp only [substB, validSLam, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hm ⊢
    rcases hm with ⟨⟨⟨hvb, hc1⟩, hphi⟩, hor⟩
    have hcb0 : countBVar 0 (substB (k + 1) u body) = countBVar 0 body :=
      countBVar_substB_lt (Nat.zero_lt_succ k) u body
    refine ⟨⟨⟨ih (k + 1) hvb, ?_⟩, ?_⟩, ?_⟩
    · rw [hcb0]; exact hc1
    · have hpu : numLam u + 1 ≤ varLeaves u := posPhi_of_validSLam hu
      have hv_eq := varLeaves_substB_eq (k + 1) u body
      have hn_eq := numLam_substB_eq (k + 1) u body
      let c := countBVar (k + 1) body
      have hcmul : c * numLam u + c ≤ c * varLeaves u := mul_succ_le_mul c hpu
      apply Nat.le_of_add_le_add_right (b := c)
      calc
        (numLam (substB (k + 1) u body) + 2) + c
          = (numLam body + 2) + (c * numLam u + c) := by
              rw [hn_eq]
              simp only [c]
              rw [Nat.add_assoc (numLam body) (countBVar (k + 1) body * numLam u) 2,
                  Nat.add_comm (countBVar (k + 1) body * numLam u) 2,
                  ← Nat.add_assoc (numLam body) 2 (countBVar (k + 1) body * numLam u),
                  Nat.add_assoc (numLam body + 2)]
        _ ≤ varLeaves body + c * varLeaves u := Nat.add_le_add hphi hcmul
        _ = varLeaves (substB (k + 1) u body) + c := hv_eq.symm
    · rcases hor with hlam | hc2
      · left
        cases body with
        | bvar _ => cases hlam
        | fvar _ => cases hlam
        | app _ _ => cases hlam
        | lam _ => rfl
      · right; rw [hcb0]; exact hc2

theorem phi_mono_betaStep {a b : Lam} (hv : validSLam a = true) (hs : BetaStep a b) :
    varLeaves a + numLam b ≤ varLeaves b + numLam a := by
  induction hs with
  | root m n =>
    simp only [validSLam, Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨⟨⟨_, hc1⟩, _⟩, _⟩, hvn⟩
    have hpn : numLam n + 1 ≤ varLeaves n := posPhi_of_validSLam hvn
    have hv_eq := varLeaves_substB_eq 0 n m
    have hn_eq := numLam_substB_eq 0 n m
    cases hc : countBVar 0 m with
    | zero => rw [hc] at hc1; cases hc1
    | succ d =>
      rw [hc] at hv_eq hn_eq
      have hdmul : d * numLam n + d ≤ d * varLeaves n := mul_succ_le_mul d hpn
      apply Nat.le_of_add_le_add_right (b := d + 1)
      have hmul_v : (d + 1) * varLeaves n = d * varLeaves n + varLeaves n := Nat.succ_mul d _
      have hmul_l : (d + 1) * numLam n = d * numLam n + numLam n := Nat.succ_mul d _
      rw [hmul_v] at hv_eq
      rw [hmul_l] at hn_eq
      simp only [varLeaves, numLam, hn_eq]
      calc
        ((varLeaves m + varLeaves n) + (numLam m + (d * numLam n + numLam n))) + (d + 1)
          = (varLeaves m + (d * numLam n + d) + varLeaves n) + ((1 + numLam m) + numLam n) := by
              omega
        _ ≤ (varLeaves m + d * varLeaves n + varLeaves n) + ((1 + numLam m) + numLam n) :=
              Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.add_le_add_left hdmul (varLeaves m)) (varLeaves n)) _
        _ = (varLeaves (substB 0 n m) + ((1 + numLam m) + numLam n)) + (d + 1) := by
              omega
  | lam _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    have h := ih hv.1.1.1
    simp only [varLeaves, numLam]
    omega
  | left _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    have h := ih hv.1
    simp only [varLeaves, numLam]
    omega
  | right _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    have h := ih hv.2
    simp only [varLeaves, numLam]
    omega

theorem countBVar_mono_betaStep {idx : Nat} {a b : Lam}
    (hv : validSLam a = true) (hs : BetaStep a b) :
    countBVar idx a ≤ countBVar idx b := by
  induction hs generalizing idx with
  | root m n =>
    simp only [validSLam, Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨⟨⟨_, hc1⟩, _⟩, _⟩, _⟩
    have hge := countBVar_substB_ge idx 0 n m
    simp only [Nat.add_zero] at hge
    simp only [countBVar, hge]
    apply Nat.add_le_add_left
    have h1 := Nat.mul_le_mul_right (countBVar idx n) hc1
    rw [Nat.one_mul] at h1
    exact h1
  | lam _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    exact ih hv.1.1.1
  | left _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    exact Nat.add_le_add_right (ih hv.1) _
  | right _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    exact Nat.add_le_add_left (ih hv.2) _

theorem countFVar_mono_betaStep {v : Nat} {a b : Lam}
    (hv : validSLam a = true) (hs : BetaStep a b) :
    countFVar v a ≤ countFVar v b := by
  induction hs with
  | root m n =>
    simp only [validSLam, Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨⟨⟨_, hc1⟩, _⟩, _⟩, _⟩
    simp only [countFVar, countFVar_substB_eq]
    apply Nat.add_le_add_left
    have h1 := Nat.mul_le_mul_right (countFVar v n) hc1
    rw [Nat.one_mul] at h1
    exact h1
  | lam _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    exact ih hv.1.1.1
  | left _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    exact Nat.add_le_add_right (ih hv.1) _
  | right _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv
    exact Nat.add_le_add_left (ih hv.2) _

theorem validSLam_betaStep {a b : Lam} (hv : validSLam a = true) (hs : BetaStep a b) :
    validSLam b = true := by
  induction hs with
  | root m n =>
    simp only [validSLam, Bool.and_eq_true] at hv
    exact validSLam_substB 0 hv.2 hv.1.1.1.1
  | @lam m m' hm ih =>
    simp only [validSLam, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hv ⊢
    rcases hv with ⟨⟨⟨hvm, hc1⟩, hphi⟩, hor⟩
    have hc_mono := countBVar_mono_betaStep (idx := 0) hvm hm
    have hphi_mono := phi_mono_betaStep hvm hm
    refine ⟨⟨⟨ih hvm, Nat.le_trans hc1 hc_mono⟩, ?_⟩, ?_⟩
    · omega
    · rcases hor with hlam | hc2
      · left; exact isLam_preserved_betaStep hlam hm
      · right; exact Nat.le_trans hc2 hc_mono
  | left _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv ⊢
    exact ⟨ih hv.1, hv.2⟩
  | right _ ih =>
    simp only [validSLam, Bool.and_eq_true] at hv ⊢
    exact ⟨hv.1, ih hv.2⟩

theorem validSLam_betaReduces {a b : Lam} (hv : validSLam a = true) (hr : BetaReduces a b) :
    validSLam b = true := by
  induction hr with
  | refl _ => exact hv
  | next hs _ ih => exact ih (validSLam_betaStep hv hs)

theorem phi_mono_betaReduces {a b : Lam} (hv : validSLam a = true) (hr : BetaReduces a b) :
    varLeaves a + numLam b ≤ varLeaves b + numLam a := by
  induction hr with
  | refl _ => exact Nat.le_refl _
  | @next a mid b hs hrest ih =>
    have h1 := phi_mono_betaStep hv hs
    have h2 := ih (validSLam_betaStep hv hs)
    omega

theorem countFVar_mono_betaReduces {v : Nat} {a b : Lam}
    (hv : validSLam a = true) (hr : BetaReduces a b) :
    countFVar v a ≤ countFVar v b := by
  induction hr with
  | refl _ => exact Nat.le_refl _
  | next hs _ ih =>
    exact Nat.le_trans (countFVar_mono_betaStep hv hs) (ih (validSLam_betaStep hv hs))

theorem validSLam_toLam (t : Term) : validSLam (toLam t) = true := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [toLam, validSLam, iha, ihb, Bool.and_self]

theorem varLeaves_toLam_eq (t : Term) : leaves t + numLam (toLam t) = varLeaves (toLam t) := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb =>
    simp only [leaves, toLam, numLam, varLeaves]
    omega

theorem countFVar_toLam_eq (v : Nat) (t : Term) : countFVar v (toLam t) = countVar v t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [toLam, countFVar, countVar, iha, ihb]

/-- **Exact `λI` Leaf Bound**: If `toLam t →_β* B`, then `leaves t + numLam B ≤ varLeaves B`. -/
theorem leaves_le_of_betaReduces {t : Term} {B : Lam} (hr : BetaReduces (toLam t) B) :
    leaves t + numLam B ≤ varLeaves B := by
  have hphi := phi_mono_betaReduces (validSLam_toLam t) hr
  have htl := varLeaves_toLam_eq t
  omega

/-- **Free-Variable Multiplicity Monotonicity**: `countVar v t ≤ countFVar v B` along `toLam t →_β* B`. -/
theorem countVar_le_of_betaReduces (v : Nat) {t : Term} {B : Lam}
    (hr : BetaReduces (toLam t) B) :
    countVar v t ≤ countFVar v B := by
  rw [← countFVar_toLam_eq v t]
  exact countFVar_mono_betaReduces (validSLam_toLam t) hr

theorem noVars_of_countFVar_zero {t : Term} {B : Lam}
    (hr : BetaReduces (toLam t) B) (hz : ∀ v, countFVar v B = 0) :
    noVars t = true := by
  induction t with
  | s => rfl
  | var v =>
    have hle := countVar_le_of_betaReduces v hr
    simp only [countVar, ↓reduceIte, hz v] at hle
    cases hle
  | app a b iha ihb =>
    -- Direct variable check using countVar_le_of_betaReduces on subterms
    have h0 : ∀ v, countVar v (a ⋅ b) = 0 := fun v =>
      Nat.eq_zero_of_le_zero (by rw [← hz v]; exact countVar_le_of_betaReduces v hr)
    clear hr iha ihb
    suffices haux : ∀ u : Term, (∀ v, countVar v u = 0) → noVars u = true from haux (a ⋅ b) h0
    intro u hu
    induction u with
    | s => rfl
    | var v =>
      have hv := hu v
      simp only [countVar, ↓reduceIte] at hv
      cases hv
    | app u1 u2 ih1 ih2 =>
      simp only [noVars, Bool.and_eq_true]
      exact ⟨ih1 (fun v => Nat.eq_zero_of_add_eq_zero_right (hu v)),
             ih2 (fun v => Nat.eq_zero_of_add_eq_zero_left (hu v))⟩

/-! ## 3. Constructive `CL(S)` Normalization from `λβ`-Normal Forms & Isolated `CL(S)` NFs -/

theorem sStep_or_nf (t : Term) : IsNormalForm t ∨ ∃ t', Step t t' := by
  induction t with
  | s => exact Or.inl (fun _ hs => by cases hs)
  | var _ => exact Or.inl (fun _ hs => by cases hs)
  | app a b iha ihb =>
    rcases iha with hnfa | ⟨a', ha'⟩
    · rcases ihb with hnfb | ⟨b', hb'⟩
      · cases a with
        | s =>
          exact Or.inl (fun _ hs => by
            cases hs with
            | left h => exact hnfa _ h
            | right h => exact hnfb _ h)
        | var _ =>
          exact Or.inl (fun _ hs => by
            cases hs with
            | left h => exact hnfa _ h
            | right h => exact hnfb _ h)
        | app a1 y =>
          cases a1 with
          | s =>
            exact Or.inl (fun _ hs => by
              cases hs with
              | left h => exact hnfa _ h
              | right h => exact hnfb _ h)
          | var _ =>
            exact Or.inl (fun _ hs => by
              cases hs with
              | left h => exact hnfa _ h
              | right h => exact hnfb _ h)
          | app a2 x =>
            cases a2 with
            | s => exact Or.inr ⟨(x ⋅ b) ⋅ (y ⋅ b), .root x y b⟩
            | var _ =>
              exact Or.inl (fun _ hs => by
                cases hs with
                | left h => exact hnfa _ h
                | right h => exact hnfb _ h)
            | app _ _ =>
              exact Or.inl (fun _ hs => by
                cases hs with
                | left h => exact hnfa _ h
                | right h => exact hnfb _ h)
      · exact Or.inr ⟨a ⋅ b', .right hb'⟩
    · exact Or.inr ⟨a' ⋅ b, .left ha'⟩

theorem step_preserves_betaNF_target {a b : Term} {B : Lam}
    (hs : Step a b) (hr : BetaReduces (toLam a) B) (hnfB : IsBetaNF B) :
    BetaReduces (toLam b) B := by
  have hab := step_to_betaReduces hs
  obtain ⟨d, hbd, hBd⟩ := betaReduces_confluence hab hr
  rw [← betaNF_reduces_eq hnfB hBd] at hbd
  exact hbd

private theorem exists_sNF_of_betaNF_aux :
    ∀ (rem : Nat),
      (∀ r' < rem, ∀ (t : Term) (B : Lam),
        BetaReduces (toLam t) B → IsBetaNF B → varLeaves B - leaves t = r' →
        ∃ nf, Reduces t nf ∧ IsNormalForm nf ∧ BetaReduces (toLam nf) B) →
      ∀ (w : Nat),
        ∀ (t : Term) (B : Lam),
          BetaReduces (toLam t) B → IsBetaNF B →
          varLeaves B - leaves t = rem → bergstraWeight t ≤ w →
          ∃ nf, Reduces t nf ∧ IsNormalForm nf ∧ BetaReduces (toLam nf) B := by
  intro rem ih_rem w
  induction w with
  | zero =>
    intro t _ _ _ _ hw
    exfalso
    have hpos := bergstraWeight_pos t
    omega
  | succ w' ih_w =>
    intro t B hr hnfB hrem hw
    rcases sStep_or_nf t with hnf | ⟨t', hs⟩
    · exact ⟨t, .refl t, hnf, hr⟩
    · have hr' : BetaReduces (toLam t') B := step_preserves_betaNF_target hs hr hnfB
      have hle_B : leaves t' ≤ varLeaves B := by
        have h := leaves_le_of_betaReduces hr'
        omega
      have hmono := leaves_mono_step hs
      exact if heq : leaves t = leaves t' then
        have hw_lt : bergstraWeight t' < bergstraWeight t :=
          equal_leaves_strict_weight_drop hs heq
        have hrem' : varLeaves B - leaves t' = rem := by rw [← heq]; exact hrem
        let ⟨nf, hred, hnf, hr_nf⟩ := ih_w t' B hr' hnfB hrem' (by omega)
        ⟨nf, .next hs hred, hnf, hr_nf⟩
      else
        have hlt_leaves : leaves t < leaves t' := Nat.lt_of_le_of_ne hmono heq
        have hrem_lt : varLeaves B - leaves t' < rem := by omega
        let ⟨nf, hred, hnf, hr_nf⟩ := ih_rem (varLeaves B - leaves t') hrem_lt t' B hr' hnfB rfl
        ⟨nf, .next hs hred, hnf, hr_nf⟩

private theorem exists_sNF_of_betaNF_outer (bound : Nat) :
    ∀ rem ≤ bound, ∀ (t : Term) (B : Lam),
      BetaReduces (toLam t) B → IsBetaNF B → varLeaves B - leaves t = rem →
      ∃ nf, Reduces t nf ∧ IsNormalForm nf ∧ BetaReduces (toLam nf) B := by
  induction bound with
  | zero =>
    intro rem hle t B hr hnfB hrem
    exact exists_sNF_of_betaNF_aux rem (fun r' hr' _ _ _ _ _ => False.elim (by omega))
      (bergstraWeight t) t B hr hnfB hrem (Nat.le_refl _)
  | succ b ihb =>
    intro rem hle t B hr hnfB hrem
    exact exists_sNF_of_betaNF_aux rem
      (fun r' hr' => ihb r' (by omega))
      (bergstraWeight t) t B hr hnfB hrem (Nat.le_refl _)

/-- **Constructive `CL(S)` Normalization Theorem**: Every `S`-term `t` whose `λ`-translation
    admits a `β`-normal form `B` constructively reduces in `CL(S)` to a `CL(S)` normal form `nf`
    whose `λ`-translation also `β`-reduces to `B`. -/
theorem exists_sNF_of_betaNF {t : Term} {B : Lam}
    (hr : BetaReduces (toLam t) B) (hnfB : IsBetaNF B) :
    ∃ nf, Reduces t nf ∧ IsNormalForm nf ∧ BetaReduces (toLam nf) B :=
  exists_sNF_of_betaNF_outer (varLeaves B - leaves t) (varLeaves B - leaves t)
    (Nat.le_refl _) t B hr hnfB rfl

theorem convS_of_reduces {a b : Term} (h : Reduces a b) : ConvS a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .trans (.step hs) ih

theorem convS_church_rosser {a b : Term} (h : ConvS a b) :
    ∃ d, Reduces a d ∧ Reduces b d := by
  induction h with
  | refl m => exact ⟨m, .refl m, .refl m⟩
  | step hs => exact ⟨_, .next hs (.refl _), .refl _⟩
  | symm _ ih =>
    obtain ⟨d, h1, h2⟩ := ih
    exact ⟨d, h2, h1⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨d1, had1, hbd1⟩ := ih1
    obtain ⟨d2, hbd2, hcd2⟩ := ih2
    obtain ⟨e, hd1e, hd2e⟩ := church_rosser hbd1 hbd2
    exact ⟨e, reduces_trans had1 hd1e, reduces_trans hcd2 hd2e⟩

theorem sNF_reduces_eq {a b : Term} (hnf : IsNormalForm a) (hr : Reduces a b) : a = b := by
  cases hr with
  | refl _ => rfl
  | next hs _ => exfalso; exact hnf _ hs

def isSRedexPrefix : Term → Bool
  | .app (.app .s _) _ => true
  | _ => false

def isSNFBool : Term → Bool
  | .s => true
  | .var _ => true
  | .app a b => !isSRedexPrefix a && isSNFBool a && isSNFBool b

theorem isNormalForm_of_bool {t : Term} (h : isSNFBool t = true) : IsNormalForm t := by
  induction t with
  | s => intro _ hs; cases hs
  | var _ => intro _ hs; cases hs
  | app a b iha ihb =>
    simp only [isSNFBool, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with ⟨⟨hnr, ha⟩, hb⟩
    intro t' hs
    cases hs with
    | root x y _ => simp [S, isSRedexPrefix] at hnr
    | left ha' => exact iha ha _ ha'
    | right hb' => exact ihb hb _ hb'

def rightArgOpt : Term → Option Term
  | .app _ r => some r
  | _ => none

def hasAntiRedex : Term → Bool
  | .s => false
  | .var _ => false
  | .app a b =>
      (match rightArgOpt a, rightArgOpt b with
       | some z1, some z2 => decide (z1 = z2)
       | _, _ => false) ||
      hasAntiRedex a || hasAntiRedex b

theorem no_step_into_of_no_antiRedex {u t : Term}
    (hno : hasAntiRedex t = false) : ¬ Step u t := by
  intro hs
  induction hs with
  | root x y z =>
    simp [hasAntiRedex, rightArgOpt] at hno
  | left _ ih =>
    simp only [hasAntiRedex, Bool.or_eq_false_iff] at hno
    exact ih hno.1.2
  | right _ ih =>
    simp only [hasAntiRedex, Bool.or_eq_false_iff] at hno
    exact ih hno.2

theorem reduces_into_eq_of_no_antiRedex {u t : Term}
    (hno : hasAntiRedex t = false) (hr : Reduces u t) : u = t := by
  induction hr with
  | refl _ => rfl
  | @next u1 u2 t' hs _ ih =>
    have heq : u2 = t' := ih hno
    subst heq
    exfalso
    exact no_step_into_of_no_antiRedex hno hs

def isIsolatedSNFBool (t : Term) : Bool :=
  isSNFBool t && !hasAntiRedex t

theorem convS_iff_eq_of_isolated {t u : Term} (hiso : isIsolatedSNFBool t = true) :
    ConvS t u ↔ u = t := by
  simp only [isIsolatedSNFBool, Bool.and_eq_true, Bool.not_eq_true'] at hiso
  rcases hiso with ⟨hsnf, hno⟩
  have hnf : IsNormalForm t := isNormalForm_of_bool hsnf
  constructor
  · intro hconv
    obtain ⟨d, htd, hud⟩ := convS_church_rosser hconv
    have hdt : t = d := sNF_reduces_eq hnf htd
    rw [← hdt] at hud
    exact reduces_into_eq_of_no_antiRedex hno hud
  · intro heq; rw [heq]; exact .refl t

/-! ## 4. `CL(S)` Normal Form Trichotomy & Free-Variable Head Spine Inversion -/

inductive SNFView : Term → Prop where
  | s0 : SNFView .s
  | s1 (p : Term) : IsNormalForm p → SNFView (.s ⋅ p)
  | s2 (p q : Term) : IsNormalForm p → IsNormalForm q → SNFView (.s ⋅ p ⋅ q)
  | varSpine (t : Term) (v : Nat) : IsNormalForm t → headLeaf t = .var v → SNFView t

theorem sNF_view {t : Term} (hnf : IsNormalForm t) : SNFView t := by
  induction t with
  | s => exact .s0
  | var v => exact .varSpine (.var v) v hnf rfl
  | app a b iha _ =>
    have ha : IsNormalForm a := fun a' ha' => hnf (a' ⋅ b) (.left ha')
    have hb : IsNormalForm b := fun b' hb' => hnf (a ⋅ b') (.right hb')
    rcases iha ha with _ | ⟨p, hp⟩ | ⟨p, q, _, _⟩ | ⟨_, v, _, hhd⟩
    · exact .s1 b hb
    · exact .s2 p b hp hb
    · exfalso; exact hnf _ (.root p q b)
    · exact .varSpine (a ⋅ b) v hnf hhd

def lamHead : Lam → Lam
  | .app a _ => lamHead a
  | t => t

def isNeutralHead : Lam → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .lam _ => false
  | .app a _ => isNeutralHead a

theorem isNeutralHead_not_lam {m : Lam} (h : isNeutralHead m = true) :
    ∀ body, m ≠ .lam body := by
  intro body heq
  subst heq
  cases h

theorem isNeutralHead_betaStep {a b : Lam}
    (h : isNeutralHead a = true) (hs : BetaStep a b) :
    isNeutralHead b = true ∧ lamHead b = lamHead a := by
  induction hs with
  | root m n => cases h
  | lam _ _ => cases h
  | left _ ih => exact ih h
  | right _ _ => exact ⟨h, rfl⟩

theorem isNeutralHead_betaReduces {a b : Lam}
    (h : isNeutralHead a = true) (hr : BetaReduces a b) :
    isNeutralHead b = true ∧ lamHead b = lamHead a := by
  induction hr with
  | refl _ => exact ⟨h, rfl⟩
  | @next _ mid _ hs _ ih =>
    obtain ⟨hmid, hhd1⟩ := isNeutralHead_betaStep h hs
    obtain ⟨hb, hhd2⟩ := ih hmid
    exact ⟨hb, hhd2.trans hhd1⟩

theorem neutral_app_betaReduces {a1 a2 B : Lam}
    (hneut : isNeutralHead a1 = true) (hr : BetaReduces (a1 ∘ₗ a2) B) :
    ∃ B1 B2, B = B1 ∘ₗ B2 ∧ BetaReduces a1 B1 ∧ BetaReduces a2 B2 := by
  generalize hap : a1 ∘ₗ a2 = a at hr
  induction hr generalizing a1 a2 with
  | refl _ => exact ⟨a1, a2, hap.symm, .refl a1, .refl a2⟩
  | @next _ mid _ hs _ ih =>
    subst hap
    cases hs with
    | root m _ => cases hneut
    | @left _ a1' _ ha1 =>
      have ⟨hneut', _⟩ := isNeutralHead_betaStep hneut ha1
      obtain ⟨B1, B2, hB, hr1, hr2⟩ := ih hneut' rfl
      exact ⟨B1, B2, hB, .next ha1 hr1, hr2⟩
    | @right _ _ a2' ha2 =>
      obtain ⟨B1, B2, hB, hr1, hr2⟩ := ih hneut rfl
      exact ⟨B1, B2, hB, hr1, .next ha2 hr2⟩

theorem isNeutralHead_toLam_of_headVar {t : Term} {v : Nat}
    (hhd : headLeaf t = .var v) :
    isNeutralHead (toLam t) = true ∧ lamHead (toLam t) = .fvar v := by
  induction t with
  | s => cases hhd
  | var w =>
    injection hhd with hw
    subst hw
    exact ⟨rfl, rfl⟩
  | app a _ iha _ => exact iha hhd

theorem not_isLam_betaNF_forces_varSpine {t : Term} {B : Lam}
    (hnf : IsNormalForm t) (hr : BetaReduces (toLam t) B)
    (hnfB : IsBetaNF B) (hnlam : isLam B = false) :
    ∃ v, headLeaf t = .var v := by
  rcases sNF_view hnf with _ | ⟨p, _⟩ | ⟨p, q, _, _⟩ | ⟨_, v, _, hhd⟩
  · have heq := betaNF_reduces_eq (isBetaNF_of_bool (t := lamS) rfl) hr
    rw [← heq] at hnlam
    cases hnlam
  · have h1 := betaReduces_single (lamS_app1 (bvarBound_toLam p))
    obtain ⟨d, hlamd, hBd⟩ := betaReduces_confluence h1 hr
    rw [← betaNF_reduces_eq hnfB hBd] at hlamd
    obtain ⟨_, hB, _⟩ := lam_preserved_betaReduces hlamd
    rw [hB] at hnlam
    cases hnlam
  · have h1 := lamS_app2 (bvarBound_toLam p) (bvarBound_toLam q)
    obtain ⟨d, hlamd, hBd⟩ := betaReduces_confluence h1 hr
    rw [← betaNF_reduces_eq hnfB hBd] at hlamd
    obtain ⟨_, hB, _⟩ := lam_preserved_betaReduces hlamd
    rw [hB] at hnlam
    cases hnlam
  · exact ⟨v, hhd⟩

/-- **Free-Variable Head Inversion (Atomic Case)**: Any `CL(S)` normal form whose `λ`-translation
    `β`-reduces to `.fvar w` is syntactically `.var w`. -/
theorem fvar_nf_eq_var {t : Term} {w : Nat}
    (hnf : IsNormalForm t) (hr : BetaReduces (toLam t) (.fvar w)) :
    t = .var w := by
  have hnfB : IsBetaNF (.fvar w) := isBetaNF_of_bool rfl
  obtain ⟨v, hhd⟩ := not_isLam_betaNF_forces_varSpine hnf hr hnfB rfl
  cases t with
  | s => cases hhd
  | var u =>
    have heq := betaNF_reduces_eq (isBetaNF_of_bool (t := .fvar u) rfl) hr
    injection heq with hwu
    rw [hwu]
  | app a b =>
    have ⟨hneut, _⟩ := isNeutralHead_toLam_of_headVar (t := a) hhd
    obtain ⟨B1, B2, hB, _, _⟩ := neutral_app_betaReduces hneut hr
    cases hB

/-- **Free-Variable Head Spine Inversion (Application Case)**: Any `CL(S)` normal form `t` whose
    `λ`-translation `β`-reduces to a `β`-normal application `B1 ∘ₗ B2` splits as `t = t1 ⋅ t2`
    with `toLam t1 →_β* B1` and `toLam t2 →_β* B2`. -/
theorem fvar_head_inversion {t : Term} {B1 B2 : Lam}
    (hnf : IsNormalForm t) (hr : BetaReduces (toLam t) (B1 ∘ₗ B2))
    (hnfB : IsBetaNF (B1 ∘ₗ B2)) :
    ∃ t1 t2, t = t1 ⋅ t2 ∧ IsNormalForm t1 ∧ IsNormalForm t2 ∧
      BetaReduces (toLam t1) B1 ∧ BetaReduces (toLam t2) B2 := by
  obtain ⟨v, hhd⟩ := not_isLam_betaNF_forces_varSpine hnf hr hnfB rfl
  cases t with
  | s => cases hhd
  | var u =>
    have heq := betaNF_reduces_eq (isBetaNF_of_bool (t := .fvar u) rfl) hr
    cases heq
  | app t1 t2 =>
    have ht1 : IsNormalForm t1 := fun a' ha' => hnf (a' ⋅ t2) (.left ha')
    have ht2 : IsNormalForm t2 := fun b' hb' => hnf (t1 ⋅ b') (.right hb')
    have ⟨hneut, _⟩ := isNeutralHead_toLam_of_headVar (t := t1) hhd
    obtain ⟨C1, C2, hC, hr1, hr2⟩ := neutral_app_betaReduces hneut hr
    injection hC with hC1 hC2
    subst hC1; subst hC2
    exact ⟨t1, t2, rfl, ht1, ht2, hr1, hr2⟩

def isSFree : Term → Bool
  | .s => false
  | .var _ => true
  | .app a b => isSFree a && isSFree b

theorem isBetaNF_toLam_of_isSFree {u : Term} (hsf : isSFree u = true) :
    IsBetaNF (toLam u) ∧ isNeutralHead (toLam u) = true := by
  induction u with
  | s => cases hsf
  | var v => exact ⟨isBetaNF_of_bool rfl, rfl⟩
  | app u1 u2 ih1 ih2 =>
    simp only [isSFree, Bool.and_eq_true] at hsf
    obtain ⟨hnf1, hneut1⟩ := ih1 hsf.1
    obtain ⟨hnf2, _⟩ := ih2 hsf.2
    have hnl : isLam (toLam u1) = false := by
      cases h : toLam u1 with
      | lam body => exfalso; exact isNeutralHead_not_lam hneut1 body h
      | _ => rfl
    have hb1 := bool_of_isBetaNF hnf1
    have hb2 := bool_of_isBetaNF hnf2
    refine ⟨isBetaNF_of_bool ?_, hneut1⟩
    simp only [toLam, isBetaNFBool, hnl, hb1, hb2, Bool.not_false, Bool.and_self]

theorem sFree_nf_eq {u t : Term} (hsf : isSFree u = true)
    (hnf : IsNormalForm t) (hr : BetaReduces (toLam t) (toLam u)) :
    t = u := by
  induction u generalizing t with
  | s => cases hsf
  | var w => exact fvar_nf_eq_var hnf hr
  | app u1 u2 ih1 ih2 =>
    have ⟨hnfU, _⟩ := isBetaNF_toLam_of_isSFree hsf
    simp only [isSFree, Bool.and_eq_true] at hsf
    obtain ⟨t1, t2, ht, hnf1, hnf2, hr1, hr2⟩ := fvar_head_inversion hnf hr hnfU
    rw [ht, ih1 hsf.1 hnf1 hr1, ih2 hsf.2 hnf2 hr2]

/-- **`S`-Free Global `λβ`-Rigidity**: Every `S`-free pure applicative term `u` is globally
    `λβ`-rigid in `Ter(CL(S))` (`ConvBeta (toLam u) (toLam t) → Reduces t u`). -/
theorem sFree_rigidity {u t : Term} (hsf : isSFree u = true)
    (hconv : ConvBeta (toLam u) (toLam t)) :
    Reduces t u := by
  have ⟨hnfU, _⟩ := isBetaNF_toLam_of_isSFree hsf
  have hr : BetaReduces (toLam t) (toLam u) := convBeta_to_nf hconv.symm hnfU
  obtain ⟨nf, hred, hnf, hr_nf⟩ := exists_sNF_of_betaNF hr hnfU
  rw [sFree_nf_eq hsf hnf hr_nf] at hred
  exact hred

/-! ## 5. Theorem A: Global `λβ`-Rigidity of `.var x`, `S`, `SS`, `SSS`, and Minimal `(8, 11)` Pairs -/

private theorem ne_of_distinct_betaNF {t : Term} {B B' : Lam}
    (hr1 : BetaReduces (toLam t) B) (hr2 : BetaReduces (toLam t) B')
    (hnfB : IsBetaNF B) (hnfB' : IsBetaNF B') (hne : B ≠ B') : False := by
  obtain ⟨d, hd1, hd2⟩ := betaReduces_confluence hr1 hr2
  have e1 := betaNF_reduces_eq hnfB hd1
  have e2 := betaNF_reduces_eq hnfB' hd2
  exact hne (e1.trans e2.symm)

private theorem closed_leaves_le_1 {t : Term} (hc : noVars t = true) (hl : leaves t ≤ 1) :
    t = .s := by
  cases t with
  | s => rfl
  | var _ => cases hc
  | app a b =>
    have ha := leaves_pos a
    have hb := leaves_pos b
    simp only [leaves] at hl
    omega

private theorem closed_leaves_le_2 {t : Term} (hc : noVars t = true) (hl : leaves t ≤ 2) :
    t = .s ∨ t = .s ⋅ .s := by
  cases t with
  | s => exact Or.inl rfl
  | var _ => cases hc
  | app a b =>
    simp only [noVars, Bool.and_eq_true] at hc
    simp only [leaves] at hl
    have ha := leaves_pos a
    have hb := leaves_pos b
    have ha1 : leaves a ≤ 1 := by omega
    have hb1 : leaves b ≤ 1 := by omega
    rw [closed_leaves_le_1 hc.1 ha1, closed_leaves_le_1 hc.2 hb1]
    exact Or.inr rfl

private theorem closed_leaves_le_3 {t : Term} (hc : noVars t = true) (hl : leaves t ≤ 3) :
    t = .s ∨ t = .s ⋅ .s ∨ t = (.s ⋅ .s) ⋅ .s ∨ t = .s ⋅ (.s ⋅ .s) := by
  cases t with
  | s => exact Or.inl rfl
  | var _ => cases hc
  | app a b =>
    simp only [noVars, Bool.and_eq_true] at hc
    simp only [leaves] at hl
    have ha := leaves_pos a
    have hb := leaves_pos b
    by_cases ha1 : leaves a ≤ 1
    · have hb2 : leaves b ≤ 2 := by omega
      rw [closed_leaves_le_1 hc.1 ha1]
      rcases closed_leaves_le_2 hc.2 hb2 with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
    · have ha2 : leaves a ≤ 2 := by omega
      have hb1 : leaves b ≤ 1 := by omega
      rw [closed_leaves_le_1 hc.2 hb1]
      rcases closed_leaves_le_2 hc.1 ha2 with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))

/-- **Theorem A.1 (`λβ`-Rigidity of Free Variables)**: `[.var x]_{=_{λβ}} ∩ Ter(CL(S)) = [.var x]_{=_S}`. -/
theorem theoremA_rigidity_var (x : Nat) (t : Term) :
    ConvBeta (toLam (.var x)) (toLam t) ↔ ConvS (.var x) t := by
  constructor
  · intro hconv
    exact (convS_of_reduces (sFree_rigidity (u := .var x) rfl hconv)).symm
  · exact convS_to_convBeta

/-- **Theorem A.2 (`λβ`-Rigidity of `S`)**: `[S]_{=_{λβ}} ∩ Ter(CL(S)) = [S]_{=_S}`. -/
theorem theoremA_rigidity_S (t : Term) :
    ConvBeta (toLam S) (toLam t) ↔ ConvS S t := by
  constructor
  · intro hconv
    have hnfB : IsBetaNF lamS := isBetaNF_of_bool rfl
    have hr : BetaReduces (toLam t) lamS := convBeta_to_nf hconv.symm hnfB
    obtain ⟨nf, hred, _, hr_nf⟩ := exists_sNF_of_betaNF hr hnfB
    have hle : leaves nf ≤ 1 := by
      have h := leaves_le_of_betaReduces hr_nf
      change leaves nf + 3 ≤ 4 at h
      omega
    have hc : noVars nf = true := noVars_of_countFVar_zero hr_nf (fun _ => rfl)
    rw [closed_leaves_le_1 hc hle] at hred
    exact (convS_of_reduces hred).symm
  · exact convS_to_convBeta

def noFVars : Lam → Bool
  | .bvar _ => true
  | .fvar _ => false
  | .lam m => noFVars m
  | .app a b => noFVars a && noFVars b

theorem countFVar_zero_of_noFVars {m : Lam} (h : noFVars m = true) (v : Nat) :
    countFVar v m = 0 := by
  induction m with
  | bvar _ => rfl
  | fvar _ => cases h
  | lam body ih => exact ih h
  | app a b iha ihb =>
    simp only [noFVars, Bool.and_eq_true] at h
    simp only [countFVar, iha h.1, ihb h.2]

private def nfLamSS : Lam := betaSteps 10 (toLam (S ⋅ S))
private def nfLamSSS : Lam := betaSteps 10 (toLam (S ⋅ S ⋅ S))
private def nfLamS_SS : Lam := betaSteps 10 (toLam (S ⋅ (S ⋅ S)))

private theorem countFVar_nfLamSS_zero (v : Nat) : countFVar v nfLamSS = 0 :=
  countFVar_zero_of_noFVars (m := nfLamSS) rfl v

private theorem countFVar_nfLamSSS_zero (v : Nat) : countFVar v nfLamSSS = 0 :=
  countFVar_zero_of_noFVars (m := nfLamSSS) rfl v

/-- **Theorem A.3 (`λβ`-Rigidity of `S ⋅ S`)**: `[S ⋅ S]_{=_{λβ}} ∩ Ter(CL(S)) = [S ⋅ S]_{=_S}`. -/
theorem theoremA_rigidity_SS (t : Term) :
    ConvBeta (toLam (S ⋅ S)) (toLam t) ↔ ConvS (S ⋅ S) t := by
  constructor
  · intro hconv
    have hnfB : IsBetaNF nfLamSS := isBetaNF_of_bool rfl
    have hrSS : BetaReduces (toLam (S ⋅ S)) nfLamSS := betaSteps_reduces 10 _
    have hconvB : ConvBeta (toLam t) nfLamSS :=
      .trans hconv.symm (betaReduces_to_conv hrSS)
    have hr : BetaReduces (toLam t) nfLamSS := convBeta_to_nf hconvB hnfB
    obtain ⟨nf, hred, _, hr_nf⟩ := exists_sNF_of_betaNF hr hnfB
    have hle : leaves nf ≤ 2 := by
      have h := leaves_le_of_betaReduces hr_nf
      change leaves nf + 3 ≤ 5 at h
      omega
    have hc : noVars nf = true := noVars_of_countFVar_zero hr_nf countFVar_nfLamSS_zero
    rcases closed_leaves_le_2 hc hle with rfl | rfl
    · exfalso
      exact ne_of_distinct_betaNF (BetaReduces.refl (toLam .s)) hr_nf
        (isBetaNF_of_bool (t := toLam .s) rfl) hnfB (by decide)
    · exact (convS_of_reduces hred).symm
  · exact convS_to_convBeta

/-- **Theorem A.4 (`λβ`-Rigidity of `S ⋅ S ⋅ S`)**: `[S ⋅ S ⋅ S]_{=_{λβ}} ∩ Ter(CL(S)) = [S ⋅ S ⋅ S]_{=_S}`. -/
theorem theoremA_rigidity_SSS (t : Term) :
    ConvBeta (toLam (S ⋅ S ⋅ S)) (toLam t) ↔ ConvS (S ⋅ S ⋅ S) t := by
  constructor
  · intro hconv
    have hnfB : IsBetaNF nfLamSSS := isBetaNF_of_bool rfl
    have hrSSS : BetaReduces (toLam (S ⋅ S ⋅ S)) nfLamSSS := betaSteps_reduces 10 _
    have hconvB : ConvBeta (toLam t) nfLamSSS :=
      .trans hconv.symm (betaReduces_to_conv hrSSS)
    have hr : BetaReduces (toLam t) nfLamSSS := convBeta_to_nf hconvB hnfB
    obtain ⟨nf, hred, _, hr_nf⟩ := exists_sNF_of_betaNF hr hnfB
    have hle : leaves nf ≤ 3 := by
      have h := leaves_le_of_betaReduces hr_nf
      change leaves nf + 3 ≤ 6 at h
      omega
    have hc : noVars nf = true := noVars_of_countFVar_zero hr_nf countFVar_nfLamSSS_zero
    rcases closed_leaves_le_3 hc hle with rfl | rfl | rfl | rfl
    · exfalso
      exact ne_of_distinct_betaNF (BetaReduces.refl (toLam .s)) hr_nf
        (isBetaNF_of_bool (t := toLam .s) rfl) hnfB (by decide)
    · exfalso
      exact ne_of_distinct_betaNF (betaSteps_reduces 10 (toLam (S ⋅ S))) hr_nf
        (isBetaNF_of_bool (t := nfLamSS) rfl) hnfB (by decide)
    · exact (convS_of_reduces hred).symm
    · exfalso
      exact ne_of_distinct_betaNF (betaSteps_reduces 10 (toLam (S ⋅ (S ⋅ S)))) hr_nf
        (isBetaNF_of_bool (t := nfLamS_SS) rfl) hnfB (by decide)
  · exact convS_to_convBeta

/-- New 2-variable `(8, 11)` schematic identity generalizing Waldmann's minimal closed collision. -/
def openWaldmannL (x y : Term) : Term :=
  S ⋅ (S ⋅ (S ⋅ S) ⋅ y) ⋅ (S ⋅ x ⋅ y)

def openWaldmannR (x y : Term) : Term :=
  S ⋅ (S ⋅ y ⋅ (S ⋅ x ⋅ y)) ⋅ (S ⋅ (S ⋅ S ⋅ x) ⋅ y)

/-- Waldmann's minimal closed `(8, 11)` collision pair (`x := S, y := S`). -/
def waldmannW1 : Term := openWaldmannL S S
def waldmannW2 : Term := openWaldmannR S S

/-- **Theorem A.5 (2-Variable Open `(8, 11)` Schematic Separation)**:
    `openWaldmannL (.var x) (.var y)` (8 leaves) and `openWaldmannR (.var x) (.var y)` (11 leaves)
    have `λβ`-convertible translations for all `x, y`, yet are isolated `CL(S)` normal forms
    and hence `¬ ConvS`. -/
theorem theoremA_open_8_11_separation (x y : Nat) :
    leaves (openWaldmannL (.var x) (.var y)) = 8 ∧
    leaves (openWaldmannR (.var x) (.var y)) = 11 ∧
    ConvBeta (toLam (openWaldmannL (.var x) (.var y))) (toLam (openWaldmannR (.var x) (.var y))) ∧
    ¬ ConvS (openWaldmannL (.var x) (.var y)) (openWaldmannR (.var x) (.var y)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have h01 : ConvBeta (toLam (openWaldmannL (.var 0) (.var 1)))
        (toLam (openWaldmannR (.var 0) (.var 1))) := by
      have hr1 := betaReduces_to_conv (betaSteps_reduces 25 (toLam (openWaldmannL (.var 0) (.var 1))))
      have hr2 := betaReduces_to_conv (betaSteps_reduces 25 (toLam (openWaldmannR (.var 0) (.var 1))))
      have heq : betaSteps 25 (toLam (openWaldmannL (.var 0) (.var 1))) =
                 betaSteps 25 (toLam (openWaldmannR (.var 0) (.var 1))) := rfl
      rw [heq] at hr1
      exact .trans hr1 hr2.symm
    let τ : Nat → Term := fun k => if k = 0 then .var x else .var y
    have hsub := convBeta_subst_term τ h01
    exact hsub
  · have hiso : isIsolatedSNFBool (openWaldmannL (.var x) (.var y)) = true := by
      simp [openWaldmannL, S, isIsolatedSNFBool, isSNFBool, isSRedexPrefix, hasAntiRedex, rightArgOpt]
    intro hconv
    have heq := (convS_iff_eq_of_isolated hiso).mp hconv
    have hl : leaves (openWaldmannR (.var x) (.var y)) = leaves (openWaldmannL (.var x) (.var y)) :=
      congrArg leaves heq
    change 11 = 8 at hl
    cases hl

/-- **Theorem A.6 (Waldmann's Closed `(8, 11)` Separation, `ConvS ⊊ ConvBeta`)**:
    `waldmannW1` (8 leaves, isolated `CL(S)` normal form) and `waldmannW2` (11 leaves, `CL(S)` normal form)
    satisfy `ConvBeta (toLam waldmannW1) (toLam waldmannW2)` and `¬ ConvS waldmannW1 waldmannW2`. -/
theorem theoremA_waldmann_8_11_separation :
    noVars waldmannW1 = true ∧
    noVars waldmannW2 = true ∧
    leaves waldmannW1 = 8 ∧
    leaves waldmannW2 = 11 ∧
    isIsolatedSNFBool waldmannW1 = true ∧
    isSNFBool waldmannW2 = true ∧
    ConvBeta (toLam waldmannW1) (toLam waldmannW2) ∧
    ¬ ConvS waldmannW1 waldmannW2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have h01 := (theoremA_open_8_11_separation 0 1).2.2.1
    exact convBeta_subst_term (fun _ => S) h01
  · intro hconv
    have heq := (convS_iff_eq_of_isolated (t := waldmannW1) rfl).mp hconv
    revert heq
    decide

end FormalQ32

