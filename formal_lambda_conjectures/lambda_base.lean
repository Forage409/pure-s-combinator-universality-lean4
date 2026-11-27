/-!
# Untyped Lambda Calculus (`Lam`), `λI` Non-Erasure, Parallel Reduction, and Church–Rosser

Self-contained constructive Lean 4.33.1 foundation (zero `Std` bloat, zero external imports)
for untyped de Bruijn `λ`-calculus with named free variables (`fvar`), supporting:
1. Exact de Bruijn shifting and capture-avoiding substitution algebra.
2. `λI`-calculus syntax (`isLambdaI`), variable conservation, and non-erasure.
3. Single-step (`BetaStep`), multi-step (`BetaPlus`, `BetaReduces`), and conversion (`BetaConv`).
4. Takahashi's parallel `β`-reduction (`ParBeta`), complete development (`cdLam`),
   and the constructive Church–Rosser theorem (`church_rosser_beta`).
-/

namespace FormalLambdaConjectures

/-! ## 1. Syntax of Untyped `λ`-Terms (Bound de Bruijn Indices + Free Variables) -/

inductive Lam where
  | bvar : Nat → Lam
  | fvar : Nat → Lam
  | app  : Lam → Lam → Lam
  | lam  : Lam → Lam
  deriving DecidableEq, Repr

infixl:70 " @@ " => Lam.app

def lamSize : Lam → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .app a b => 1 + (lamSize a + lamSize b)
  | .lam body => 1 + lamSize body

theorem lamSize_pos (m : Lam) : 1 ≤ lamSize m := by
  cases m <;> simp [lamSize]

/-! ## 2. Bound-Variable Shifting and Substitution -/

def shift (d c : Nat) : Lam → Lam
  | .bvar k => if c ≤ k then .bvar (k + d) else .bvar k
  | .fvar v => .fvar v
  | .app a b => shift d c a @@ shift d c b
  | .lam body => .lam (shift d (c + 1) body)

def subst (k : Nat) (s : Lam) : Lam → Lam
  | .bvar j =>
      if j < k then .bvar j
      else if j = k then shift k 0 s
      else .bvar (j - 1)
  | .fvar v => .fvar v
  | .app a b => subst k s a @@ subst k s b
  | .lam body => .lam (subst (k + 1) s body)

/-- Every bound de Bruijn index is `< depth` (at `depth = 0`, no dangling bound variables). -/
def bvarClosed (depth : Nat) : Lam → Bool
  | .bvar k => decide (k < depth)
  | .fvar _ => true
  | .app a b => bvarClosed depth a && bvarClosed depth b
  | .lam body => bvarClosed (depth + 1) body

def occursBVar (k : Nat) : Lam → Bool
  | .bvar j => decide (j = k)
  | .fvar _ => false
  | .app a b => occursBVar k a || occursBVar k b
  | .lam body => occursBVar (k + 1) body

def hasFVar (v : Nat) : Lam → Bool
  | .bvar _ => false
  | .fvar u => decide (u = v)
  | .app a b => hasFVar v a || hasFVar v b
  | .lam body => hasFVar v body

def maxFVarBound : Lam → Nat
  | .bvar _ => 0
  | .fvar u => u + 1
  | .app a b => Nat.max (maxFVarBound a) (maxFVarBound b)
  | .lam body => maxFVarBound body

theorem hasFVar_false_of_ge {v : Nat} {m : Lam} (h : maxFVarBound m ≤ v) :
    hasFVar v m = false := by
  induction m with
  | bvar _ => rfl
  | fvar u =>
    simp only [maxFVarBound] at h
    simp only [hasFVar, decide_eq_false_iff_not]
    intro huv
    subst huv
    exact Nat.lt_irrefl u h
  | app a b iha ihb =>
    simp only [maxFVarBound] at h
    have ha : maxFVarBound a ≤ v := Nat.le_trans (Nat.le_max_left _ _) h
    have hb : maxFVarBound b ≤ v := Nat.le_trans (Nat.le_max_right _ _) h
    simp [hasFVar, iha ha, ihb hb]
  | lam body ih =>
    exact ih h

/-- `λI`-calculus predicate: every `λ`-binder uses its bound variable `0` at least once. -/
def isLambdaI : Lam → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .app a b => isLambdaI a && isLambdaI b
  | .lam body => occursBVar 0 body && isLambdaI body

/-! ### Exact Shifting and Substitution Identities (Zero `Classical.choice`) -/

theorem shift_zero (m : Lam) (c : Nat) : shift 0 c m = m := by
  induction m generalizing c with
  | bvar k =>
    simp only [shift]
    by_cases h : c ≤ k
    · rw [if_pos h, Nat.add_zero]
    · rw [if_neg h]
  | fvar _ => rfl
  | app _ _ iha ihb => simp [shift, iha, ihb]
  | lam _ ih => simp [shift, ih]

theorem bvarClosed_mono {d₁ d₂ : Nat} (hd : d₁ ≤ d₂) (m : Lam) :
    bvarClosed d₁ m = true → bvarClosed d₂ m = true := by
  induction m generalizing d₁ d₂ with
  | bvar k =>
    simp only [bvarClosed, decide_eq_true_eq]
    intro hk
    exact Nat.lt_of_lt_of_le hk hd
  | fvar _ => intro _; rfl
  | app a b iha ihb =>
    simp only [bvarClosed, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    exact ⟨iha hd ha, ihb hd hb⟩
  | lam body ih =>
    simp only [bvarClosed]
    exact ih (Nat.add_le_add_right hd 1)

theorem shift_bvarClosed (d c : Nat) (m : Lam) (hc : bvarClosed c m = true) :
    shift d c m = m := by
  induction m generalizing c with
  | bvar k =>
    simp only [bvarClosed, decide_eq_true_eq] at hc
    simp only [shift, if_neg (Nat.not_le_of_lt hc)]
  | fvar _ => rfl
  | app a b iha ihb =>
    simp only [bvarClosed, Bool.and_eq_true] at hc
    simp [shift, iha c hc.1, ihb c hc.2]
  | lam body ih =>
    simp only [bvarClosed] at hc
    simp [shift, ih (c + 1) hc]

theorem subst_bvarClosed (k : Nat) (s m : Lam) (hc : bvarClosed k m = true) :
    subst k s m = m := by
  induction m generalizing k with
  | bvar j =>
    simp only [bvarClosed, decide_eq_true_eq] at hc
    simp only [subst, if_pos hc]
  | fvar _ => rfl
  | app a b iha ihb =>
    simp only [bvarClosed, Bool.and_eq_true] at hc
    simp [subst, iha k hc.1, ihb k hc.2]
  | lam body ih =>
    simp only [bvarClosed] at hc
    simp [subst, ih (k + 1) hc]

/-- Merging two shifts when `c₁ ≤ c₂` and `c₂ ≤ c₁ + d₁`. -/
theorem shift_merge (d₁ d₂ c₁ c₂ : Nat) (h1 : c₁ ≤ c₂) (h2 : c₂ ≤ c₁ + d₁) (m : Lam) :
    shift d₂ c₂ (shift d₁ c₁ m) = shift (d₁ + d₂) c₁ m := by
  induction m generalizing c₁ c₂ with
  | bvar j =>
    simp only [shift]
    by_cases hj1 : c₁ ≤ j
    · simp only [if_pos hj1]
      have hj2 : c₂ ≤ j + d₁ := Nat.le_trans h2 (Nat.add_le_add_right hj1 d₁)
      simp only [shift, if_pos hj2, Nat.add_assoc]
    · simp only [if_neg hj1]
      have hj2 : ¬ (c₂ ≤ j) := fun hc2 => hj1 (Nat.le_trans h1 hc2)
      simp only [shift, if_neg hj2]
  | fvar _ => rfl
  | app _ _ iha ihb =>
    simp [shift, iha c₁ c₂ h1 h2, ihb c₁ c₂ h1 h2]
  | lam _ ih =>
    have h1' : c₁ + 1 ≤ c₂ + 1 := Nat.add_le_add_right h1 1
    have h2' : c₂ + 1 ≤ (c₁ + 1) + d₁ := by
      rw [Nat.add_right_comm c₁ 1 d₁]
      exact Nat.add_le_add_right h2 1
    simp [shift, ih (c₁ + 1) (c₂ + 1) h1' h2']

/-- Commuting two shifts when `c₁ ≤ c₂`. -/
theorem shift_comm (d₁ d₂ c₁ c₂ : Nat) (h : c₁ ≤ c₂) (m : Lam) :
    shift d₂ (c₂ + d₁) (shift d₁ c₁ m) = shift d₁ c₁ (shift d₂ c₂ m) := by
  induction m generalizing c₁ c₂ with
  | bvar j =>
    simp only [shift]
    by_cases hj2 : c₂ ≤ j
    · have hj1 : c₁ ≤ j := Nat.le_trans h hj2
      have hj1' : c₁ ≤ j + d₂ := Nat.le_trans hj1 (Nat.le_add_right j d₂)
      have hj2' : c₂ + d₁ ≤ j + d₁ := Nat.add_le_add_right hj2 d₁
      rw [if_pos hj1, if_pos hj2]
      simp only [shift, if_pos hj2', if_pos hj1']
      rw [Nat.add_assoc j d₁ d₂, Nat.add_assoc j d₂ d₁, Nat.add_comm d₁ d₂]
    · rw [if_neg hj2]
      by_cases hj1 : c₁ ≤ j
      · have hj2' : ¬ (c₂ + d₁ ≤ j + d₁) := fun hle => hj2 (Nat.le_of_add_le_add_right hle)
        rw [if_pos hj1]
        simp only [shift, if_neg hj2', if_pos hj1]
      · rw [if_neg hj1]
        have hj2' : ¬ (c₂ + d₁ ≤ j) := fun hle => hj2 (Nat.le_trans (Nat.le_add_right c₂ d₁) hle)
        simp only [shift, if_neg hj2', if_neg hj1]
  | fvar _ => rfl
  | app _ _ iha ihb =>
    simp [shift, iha c₁ c₂ h, ihb c₁ c₂ h]
  | lam _ ih =>
    have h' : c₁ + 1 ≤ c₂ + 1 := Nat.add_le_add_right h 1
    have heq : (c₂ + 1) + d₁ = (c₂ + d₁) + 1 := Nat.add_right_comm c₂ 1 d₁
    simp only [shift]
    rw [← heq]
    exact congrArg Lam.lam (ih (c₁ + 1) (c₂ + 1) h')

/-- Substituting at `k` cancels `shift 1 k`. -/
theorem subst_shift_cancel (k : Nat) (s m : Lam) :
    subst k s (shift 1 k m) = m := by
  induction m generalizing k with
  | bvar j =>
    simp only [shift]
    by_cases hj : k ≤ j
    · rw [if_pos hj]
      have hnotlt : ¬ (j + 1 < k) := fun hlt => Nat.not_le_of_lt (Nat.lt_trans (Nat.lt_succ_self j) hlt) hj
      have hne : ¬ (j + 1 = k) := fun heq => Nat.not_le_of_lt (by rw [← heq]; exact Nat.lt_succ_self j) hj
      simp only [subst, if_neg hnotlt, if_neg hne, Nat.add_sub_cancel]
    · rw [if_neg hj]
      simp only [subst, if_pos (Nat.lt_of_not_ge hj)]
  | fvar _ => rfl
  | app _ _ iha ihb => simp [shift, subst, iha k, ihb k]
  | lam _ ih => simp [shift, subst, ih (k + 1)]

/-- Pushing `shift` into `subst` when shifting above `k` (`cutoff = k + e`). -/
theorem shift_subst_above (d k e : Nat) (s m : Lam) :
    shift d (k + e) (subst k s m) = subst k (shift d e s) (shift d (k + e + 1) m) := by
  induction m generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · have hlt2 : j < k + e := Nat.lt_of_lt_of_le hlt (Nat.le_add_right k e)
      have hnot1 : ¬ (k + e ≤ j) := Nat.not_le_of_lt hlt2
      have hnot2 : ¬ (k + e + 1 ≤ j) := Nat.not_le_of_lt (Nat.lt_succ_of_lt hlt2)
      rw [if_pos hlt]
      simp only [shift, if_neg hnot1, if_neg hnot2, subst, if_pos hlt]
    · rw [if_neg hlt]
      by_cases heq : j = k
      · subst heq
        have hnot2 : ¬ (j + e + 1 ≤ j) := by
          intro hle
          have h1 : j + 1 ≤ j := Nat.le_trans
            (by rw [Nat.add_right_comm j e 1]; exact Nat.le_add_right (j + 1) e) hle
          exact Nat.lt_irrefl j (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) h1)
        rw [if_pos rfl]
        simp only [shift, if_neg hnot2, subst, if_neg hlt, ↓reduceIte]
        have hcomm := shift_comm j d 0 e (Nat.zero_le e) s
        rw [Nat.add_comm e j] at hcomm
        exact hcomm
      · rw [if_neg heq]
        have hgt : k < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hgt)
        by_cases hjbig : k + e + 1 ≤ j
        · have hj1 : k + e ≤ j - 1 := Nat.sub_le_sub_right hjbig 1
          have hnotlt' : ¬ (j + d < k) := fun h' => hlt (Nat.lt_of_le_of_lt (Nat.le_add_right j d) h')
          have hne' : ¬ (j + d = k) := fun h' => by
            have hkge : j ≤ k := by rw [← h']; exact Nat.le_add_right j d
            exact Nat.not_le_of_lt hgt hkge
          have hsub_add : j - 1 + d = j + d - 1 := by
            cases j with
            | zero => cases hjpos
            | succ j0 =>
              simp only [Nat.succ_sub_one]
              rw [Nat.succ_add j0 d]
              rfl
          simp only [shift, if_pos hj1, if_pos hjbig, subst, if_neg hnotlt', if_neg hne', hsub_add]
        · have hj1 : ¬ (k + e ≤ j - 1) := by
            intro hle
            have hadd := Nat.add_le_add_right hle 1
            rw [Nat.sub_add_cancel hjpos] at hadd
            exact hjbig hadd
          simp only [shift, if_neg hj1, if_neg hjbig, subst, if_neg hlt, if_neg heq]
  | fvar _ => rfl
  | app _ _ iha ihb =>
    simp [subst, shift, iha k, ihb k]
  | lam body ih =>
    have heq1 : (k + 1) + e = (k + e) + 1 := Nat.add_right_comm k 1 e
    simp only [subst, shift]
    apply congrArg Lam.lam
    rw [← heq1]
    exact ih (k + 1)

/-- Pushing `subst` across `shift` when substituting above `c` (`index = c + d + e`). -/
theorem subst_shift_above (d c e : Nat) (u s : Lam) :
    subst (c + d + e) u (shift d c s) = shift d c (subst (c + e) u s) := by
  induction s generalizing c with
  | bvar j =>
    simp only [shift, subst]
    by_cases hjc : c ≤ j
    · rw [if_pos hjc]
      by_cases hlt : j < c + e
      · have hlt' : j + d < c + d + e := by
          rw [Nat.add_right_comm c d e]
          exact Nat.add_lt_add_right hlt d
        rw [if_pos hlt]
        simp only [subst, if_pos hlt', shift, if_pos hjc]
      · rw [if_neg hlt]
        have hnotlt' : ¬ (j + d < c + d + e) := by
          rw [Nat.add_right_comm c d e]
          exact fun h' => hlt (Nat.lt_of_add_lt_add_right h')
        by_cases heq : j = c + e
        · subst heq
          have heq' : (c + e) + d = c + d + e := Nat.add_right_comm c e d
          rw [if_pos rfl]
          simp only [subst, if_neg hnotlt', if_pos heq']
          have h2 : c ≤ 0 + (c + e) := by rw [Nat.zero_add]; exact Nat.le_add_right c e
          have hm := shift_merge (c + e) d 0 c (Nat.zero_le c) h2 u
          rw [heq'] at hm
          exact hm.symm
        · rw [if_neg heq]
          have hgt : c + e < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
          have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le (c + e)) hgt)
          have hne' : ¬ (j + d = c + d + e) := by
            intro h'
            rw [Nat.add_right_comm c d e] at h'
            exact heq (Nat.add_right_cancel h')
          have hjc1 : c ≤ j - 1 := by
            have hcj : c < j := Nat.lt_of_le_of_lt (Nat.le_add_right c e) hgt
            exact Nat.le_pred_of_lt hcj
          have hsub_add : j + d - 1 = j - 1 + d := by
            cases j with
            | zero => cases hjpos
            | succ j0 =>
              simp only [Nat.succ_sub_one, Nat.succ_add]
          simp only [subst, if_neg hnotlt', if_neg hne', shift, if_pos hjc1, hsub_add]
    · rw [if_neg hjc]
      have hltc : j < c := Nat.lt_of_not_ge hjc
      have hlt1 : j < c + e := Nat.lt_of_lt_of_le hltc (Nat.le_add_right c e)
      have hlt2 : j < c + d + e :=
        Nat.lt_of_lt_of_le hltc (Nat.le_trans (Nat.le_add_right c d) (Nat.le_add_right _ e))
      rw [if_pos hlt1]
      simp only [subst, if_pos hlt2, shift, if_neg hjc]
  | fvar _ => rfl
  | app _ _ iha ihb =>
    simp [shift, subst, iha c, ihb c]
  | lam body ih =>
    have heq1 : (c + 1) + d + e = (c + d + e) + 1 := by
      rw [Nat.add_right_comm c 1 d, Nat.add_right_comm (c + d) 1 e]
    have heq2 : (c + 1) + e = (c + e) + 1 := Nat.add_right_comm c 1 e
    simp only [shift, subst]
    rw [← heq1, ← heq2]
    exact congrArg Lam.lam (ih (c + 1))

/-- **Fundamental Substitution Lemma (`subst_subst`)**:
    `subst (k + e) u (subst k s m) = subst k (subst e u s) (subst (k + e + 1) u m)`. -/
theorem subst_subst (k e : Nat) (u s m : Lam) :
    subst (k + e) u (subst k s m) = subst k (subst e u s) (subst (k + e + 1) u m) := by
  induction m generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · have hlt1 : j < k + e := Nat.lt_of_lt_of_le hlt (Nat.le_add_right k e)
      have hlt2 : j < k + e + 1 := Nat.lt_succ_of_lt hlt1
      rw [if_pos hlt, if_pos hlt2]
      simp only [subst, if_pos hlt1, if_pos hlt]
    · rw [if_neg hlt]
      by_cases heq : j = k
      · subst heq
        have hlt2 : j < j + e + 1 := Nat.lt_succ_of_le (Nat.le_add_right j e)
        rw [if_pos rfl, if_pos hlt2]
        simp only [subst, if_neg hlt, ↓reduceIte]
        have hs := subst_shift_above j 0 e u s
        simpa [Nat.zero_add] using hs
      · rw [if_neg heq]
        have hgt : k < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hgt)
        by_cases hlt2 : j < k + e + 1
        · have hlt1 : j - 1 < k + e := by
            cases j with
            | zero => cases hjpos
            | succ j0 => exact Nat.lt_of_succ_lt_succ hlt2
          rw [if_pos hlt2]
          simp only [subst, if_pos hlt1, if_neg hlt, if_neg heq]
        · rw [if_neg hlt2]
          by_cases heq2 : j = k + e + 1
          · subst heq2
            have hsub1 : k + e + 1 - 1 = k + e := rfl
            rw [hsub1, if_pos rfl]
            have hnotlt1 : ¬ (k + e < k + e) := Nat.lt_irrefl _
            simp only [subst, if_neg hnotlt1, ↓reduceIte]
            have h2 : k ≤ 0 + (k + e) := by rw [Nat.zero_add]; exact Nat.le_add_right k e
            have hm := shift_merge (k + e) 1 0 k (Nat.zero_le k) h2 u
            rw [← hm, subst_shift_cancel]
          · rw [if_neg heq2]
            have hgt2 : k + e + 1 < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt2) (Ne.symm heq2)
            have hgt1 : k + e < j - 1 := by
              cases j with
              | zero => cases hjpos
              | succ j0 => exact Nat.lt_of_succ_lt_succ hgt2
            have hnotlt1 : ¬ (j - 1 < k + e) := Nat.not_lt_of_gt hgt1
            have hne1 : ¬ (j - 1 = k + e) := Ne.symm (Nat.ne_of_lt hgt1)
            have hgt_k : k < j - 1 := Nat.lt_of_le_of_lt (Nat.le_add_right k e) hgt1
            have hnotlt_k : ¬ (j - 1 < k) := Nat.not_lt_of_gt hgt_k
            have hne_k : ¬ (j - 1 = k) := Ne.symm (Nat.ne_of_lt hgt_k)
            simp only [subst, if_neg hnotlt1, if_neg hne1, if_neg hnotlt_k, if_neg hne_k]
  | fvar _ => rfl
  | app _ _ iha ihb =>
    simp [subst, iha k, ihb k]
  | lam body ih =>
    have heq1 : (k + 1) + e = (k + e) + 1 := Nat.add_right_comm k 1 e
    simp only [subst]
    apply congrArg Lam.lam
    rw [← heq1]
    exact ih (k + 1)

theorem subst0_subst (e : Nat) (u s m : Lam) :
    subst e u (subst 0 s m) = subst 0 (subst e u s) (subst (e + 1) u m) := by
  simpa [Nat.zero_add] using subst_subst 0 e u s m

/-! ## 3. Single-Step and Multi-Step `β`-Reduction -/

inductive BetaStep : Lam → Lam → Prop where
  | beta (body arg : Lam) : BetaStep (.app (.lam body) arg) (subst 0 arg body)
  | appL {a a' b : Lam} : BetaStep a a' → BetaStep (.app a b) (.app a' b)
  | appR {a b b' : Lam} : BetaStep b b' → BetaStep (.app a b) (.app a b')
  | lam  {b b' : Lam} : BetaStep b b' → BetaStep (.lam b) (.lam b')

inductive BetaPlus : Lam → Lam → Prop where
  | single {a b : Lam} : BetaStep a b → BetaPlus a b
  | head   {a b c : Lam} : BetaStep a b → BetaPlus b c → BetaPlus a c

inductive BetaReduces : Lam → Lam → Prop where
  | refl (a : Lam) : BetaReduces a a
  | next {a b c : Lam} : BetaStep a b → BetaReduces b c → BetaReduces a c

inductive BetaConv : Lam → Lam → Prop where
  | refl (a : Lam) : BetaConv a a
  | step {a b : Lam} : BetaStep a b → BetaConv a b
  | symm {a b : Lam} : BetaConv a b → BetaConv b a
  | trans {a b c : Lam} : BetaConv a b → BetaConv b c → BetaConv a c

def IsBetaNF (m : Lam) : Prop := ∀ m', ¬ BetaStep m m'
def HasBetaNF (m : Lam) : Prop := ∃ nf, BetaReduces m nf ∧ IsBetaNF nf
def StrongNormalizingBeta (m : Lam) : Prop := Acc (fun b a => BetaStep a b) m

theorem betaReduces_trans {a b c : Lam} (h1 : BetaReduces a b) (h2 : BetaReduces b c) :
    BetaReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact BetaReduces.next hs (ih h2)

theorem betaPlus_trans {a b c : Lam} (h1 : BetaPlus a b) (h2 : BetaPlus b c) :
    BetaPlus a c := by
  induction h1 with
  | single hs => exact BetaPlus.head hs h2
  | head hs _ ih => exact BetaPlus.head hs (ih h2)

theorem betaReduces_of_betaPlus {a b : Lam} (h : BetaPlus a b) : BetaReduces a b := by
  induction h with
  | single hs => exact BetaReduces.next hs (BetaReduces.refl _)
  | head hs _ ih => exact BetaReduces.next hs ih

theorem betaPlus_of_step_reduces {a b c : Lam} (h1 : BetaStep a b) (h2 : BetaReduces b c) :
    BetaPlus a c := by
  induction h2 generalizing a with
  | refl _ => exact BetaPlus.single h1
  | next hs _ ih => exact BetaPlus.head h1 (ih hs)

theorem betaReduces_appL {a a' : Lam} (h : BetaReduces a a') (b : Lam) :
    BetaReduces (a @@ b) (a' @@ b) := by
  induction h with
  | refl _ => exact BetaReduces.refl _
  | next hs _ ih => exact BetaReduces.next (BetaStep.appL hs) ih

theorem betaReduces_appR (a : Lam) {b b' : Lam} (h : BetaReduces b b') :
    BetaReduces (a @@ b) (a @@ b') := by
  induction h with
  | refl _ => exact BetaReduces.refl _
  | next hs _ ih => exact BetaReduces.next (BetaStep.appR hs) ih

theorem betaReduces_app {a a' b b' : Lam} (ha : BetaReduces a a') (hb : BetaReduces b b') :
    BetaReduces (a @@ b) (a' @@ b') :=
  betaReduces_trans (betaReduces_appL ha b) (betaReduces_appR a' hb)

theorem betaReduces_lam {b b' : Lam} (h : BetaReduces b b') :
    BetaReduces (.lam b) (.lam b') := by
  induction h with
  | refl _ => exact BetaReduces.refl _
  | next hs _ ih => exact BetaReduces.next (BetaStep.lam hs) ih

theorem betaPlus_appL {a a' : Lam} (h : BetaPlus a a') (b : Lam) :
    BetaPlus (a @@ b) (a' @@ b) := by
  induction h with
  | single hs => exact BetaPlus.single (BetaStep.appL hs)
  | head hs _ ih => exact BetaPlus.head (BetaStep.appL hs) ih

theorem betaPlus_appR (a : Lam) {b b' : Lam} (h : BetaPlus b b') :
    BetaPlus (a @@ b) (a @@ b') := by
  induction h with
  | single hs => exact BetaPlus.single (BetaStep.appR hs)
  | head hs _ ih => exact BetaPlus.head (BetaStep.appR hs) ih

theorem betaPlus_lam {b b' : Lam} (h : BetaPlus b b') :
    BetaPlus (.lam b) (.lam b') := by
  induction h with
  | single hs => exact BetaPlus.single (BetaStep.lam hs)
  | head hs _ ih => exact BetaPlus.head (BetaStep.lam hs) ih

theorem betaConv_of_reduces {a b : Lam} (h : BetaReduces a b) : BetaConv a b := by
  induction h with
  | refl _ => exact BetaConv.refl _
  | next hs _ ih => exact BetaConv.trans (BetaConv.step hs) ih

/-! ### Shifting & Substitution Compatibility with `BetaStep` -/

theorem betaStep_shift (d c : Nat) {a b : Lam} (h : BetaStep a b) :
    BetaStep (shift d c a) (shift d c b) := by
  induction h generalizing c with
  | beta body arg =>
    simp only [shift]
    have hs := shift_subst_above d 0 c arg body
    simp only [Nat.zero_add] at hs
    rw [hs]
    exact BetaStep.beta _ _
  | appL _ ih => exact BetaStep.appL (ih c)
  | appR _ ih => exact BetaStep.appR (ih c)
  | lam _ ih => exact BetaStep.lam (ih (c + 1))

theorem betaStep_subst_body (k : Nat) (s : Lam) {a b : Lam} (h : BetaStep a b) :
    BetaStep (subst k s a) (subst k s b) := by
  induction h generalizing k with
  | beta body arg =>
    simp only [subst]
    rw [subst0_subst k s arg body]
    exact BetaStep.beta _ _
  | appL _ ih => exact BetaStep.appL (ih k)
  | appR _ ih => exact BetaStep.appR (ih k)
  | lam _ ih => exact BetaStep.lam (ih (k + 1))

theorem betaReduces_subst_body (k : Nat) (s : Lam) {a b : Lam} (h : BetaReduces a b) :
    BetaReduces (subst k s a) (subst k s b) := by
  induction h with
  | refl _ => exact BetaReduces.refl _
  | next hs _ ih => exact BetaReduces.next (betaStep_subst_body k s hs) ih

theorem betaReduces_subst_arg (k : Nat) {s s' : Lam} (hs : BetaReduces s s') (m : Lam) :
    BetaReduces (subst k s m) (subst k s' m) := by
  induction m generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · simp only [if_pos hlt]; exact BetaReduces.refl _
    · simp only [if_neg hlt]
      by_cases heq : j = k
      · simp only [if_pos heq]
        induction hs with
        | refl _ => exact BetaReduces.refl _
        | next hstep _ ihs => exact BetaReduces.next (betaStep_shift k 0 hstep) ihs
      · simp only [if_neg heq]; exact BetaReduces.refl _
  | fvar _ => exact BetaReduces.refl _
  | app _ _ iha ihb => exact betaReduces_app (iha k) (ihb k)
  | lam _ ih => exact betaReduces_lam (ih (k + 1))

private theorem subst_eq_of_occurs_false (k : Nat) (s s' m : Lam)
    (hm : occursBVar k m = false) : subst k s m = subst k s' m := by
  induction m generalizing k with
  | bvar j =>
    simp only [occursBVar, decide_eq_false_iff_not] at hm
    simp only [subst]
    by_cases hlt : j < k
    · simp only [if_pos hlt]
    · simp only [if_neg hlt, if_neg hm]
  | fvar _ => rfl
  | app a b iha ihb =>
    simp only [occursBVar, Bool.or_eq_false_iff] at hm
    simp [subst, iha k hm.1, ihb k hm.2]
  | lam body ih =>
    simp only [occursBVar] at hm
    simp [subst, ih (k + 1) hm]

private theorem betaPlus_of_plus_reduces {a b c : Lam}
    (h1 : BetaPlus a b) (h2 : BetaReduces b c) : BetaPlus a c := by
  induction h2 generalizing a with
  | refl _ => exact h1
  | next hs _ ih => exact ih (betaPlus_trans h1 (.single hs))

theorem betaPlus_subst_arg_of_occurs (k : Nat) {s s' : Lam} (hs : BetaStep s s')
    {m : Lam} (hocc : occursBVar k m = true) :
    BetaPlus (subst k s m) (subst k s' m) := by
  induction m generalizing k with
  | bvar j =>
    simp only [occursBVar, decide_eq_true_eq] at hocc
    subst hocc
    simp only [subst, if_neg (Nat.lt_irrefl j), ↓reduceIte]
    exact BetaPlus.single (betaStep_shift j 0 hs)
  | fvar _ => cases hocc
  | app a b iha ihb =>
    simp only [occursBVar, Bool.or_eq_true] at hocc
    cases hka : occursBVar k a with
    | true =>
      have pa := betaPlus_appL (iha k hka) (subst k s b)
      have rb := betaReduces_appR (subst k s' a)
        (betaReduces_subst_arg k (BetaReduces.next hs (BetaReduces.refl _)) b)
      exact betaPlus_of_plus_reduces pa rb
    | false =>
      have hkb : occursBVar k b = true := by
        rcases hocc with ha' | hb'
        · rw [hka] at ha'; cases ha'
        · exact hb'
      simp only [subst]
      rw [← subst_eq_of_occurs_false k s s' a hka]
      exact betaPlus_appR (subst k s a) (ihb k hkb)
  | lam body ih =>
    simp only [occursBVar] at hocc
    exact betaPlus_lam (ih (k + 1) hocc)

/-! ### `λI` Preservation, Bound-Depth Closure, and Variable Conservation -/

theorem bvarClosed_shift (d c depth : Nat) (hcd : c ≤ depth) (m : Lam) :
    bvarClosed depth m = true → bvarClosed (depth + d) (shift d c m) = true := by
  induction m generalizing c depth with
  | bvar j =>
    simp only [bvarClosed, shift, decide_eq_true_eq]
    intro hj
    by_cases hcj : c ≤ j
    · rw [if_pos hcj]
      simp only [bvarClosed, decide_eq_true_eq]
      exact Nat.add_lt_add_right hj d
    · rw [if_neg hcj]
      simp only [bvarClosed, decide_eq_true_eq]
      exact Nat.lt_of_lt_of_le hj (Nat.le_add_right depth d)
  | fvar _ => intro _; rfl
  | app a b iha ihb =>
    simp only [bvarClosed, shift, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    exact ⟨iha c depth hcd ha, ihb c depth hcd hb⟩
  | lam body ih =>
    simp only [bvarClosed, shift]
    have heq : depth + d + 1 = (depth + 1) + d := Nat.add_right_comm depth d 1
    rw [heq]
    exact ih (c + 1) (depth + 1) (Nat.add_le_add_right hcd 1)

theorem bvarClosed_subst_gen (k d : Nat) {s m : Lam}
    (hs : bvarClosed d s = true) (hm : bvarClosed (k + d + 1) m = true) :
    bvarClosed (k + d) (subst k s m) = true := by
  induction m generalizing k with
  | bvar j =>
    simp only [bvarClosed, decide_eq_true_eq] at hm
    simp only [subst]
    by_cases hlt : j < k
    · rw [if_pos hlt]
      simp [bvarClosed, decide_eq_true (Nat.lt_of_lt_of_le hlt (Nat.le_add_right k d))]
    · rw [if_neg hlt]
      by_cases heq : j = k
      · subst heq
        rw [if_pos rfl]
        have hsh := bvarClosed_shift j 0 d (Nat.zero_le d) s hs
        rw [Nat.add_comm d j] at hsh
        exact hsh
      · rw [if_neg heq]
        have hgt : k < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hgt)
        have hlt' : j - 1 < k + d := by
          cases j with
          | zero => cases hjpos
          | succ j0 => exact Nat.lt_of_succ_lt_succ hm
        simp [bvarClosed, decide_eq_true hlt']
  | fvar _ => rfl
  | app m1 m2 ih1 ih2 =>
    simp only [bvarClosed, Bool.and_eq_true] at hm
    simp [subst, bvarClosed, ih1 k hm.1, ih2 k hm.2]
  | lam m1 ih1 =>
    simp only [bvarClosed] at hm
    have heq1 : (k + 1) + d = (k + d) + 1 := Nat.add_right_comm k 1 d
    have heq2 : (k + 1) + d + 1 = (k + d + 1) + 1 := by rw [heq1]
    rw [← heq2] at hm
    simpa [subst, bvarClosed, heq1] using ih1 (k + 1) hm

theorem bvarClosed_subst (k : Nat) {s m : Lam}
    (hs : bvarClosed 0 s = true) (hm : bvarClosed (k + 1) m = true) :
    bvarClosed k (subst k s m) = true := by
  simpa [Nat.add_zero] using bvarClosed_subst_gen k 0 hs hm

theorem bvarClosed_betaStep (depth : Nat) {a b : Lam} (h : BetaStep a b) :
    bvarClosed depth a = true → bvarClosed depth b = true := by
  induction h generalizing depth with
  | beta body arg =>
    simp only [bvarClosed, Bool.and_eq_true]
    intro ⟨hb, ha⟩
    have hb' : bvarClosed (0 + depth + 1) body = true := by simpa [Nat.zero_add] using hb
    simpa [Nat.zero_add] using bvarClosed_subst_gen 0 depth ha hb'
  | appL _ ih =>
    simp only [bvarClosed, Bool.and_eq_true]
    intro ⟨ha, hb⟩; exact ⟨ih depth ha, hb⟩
  | appR _ ih =>
    simp only [bvarClosed, Bool.and_eq_true]
    intro ⟨ha, hb⟩; exact ⟨ha, ih depth hb⟩
  | lam _ ih =>
    simp only [bvarClosed]
    exact ih (depth + 1)

theorem bvarClosed_betaReduces (depth : Nat) {a b : Lam} (h : BetaReduces a b) :
    bvarClosed depth a = true → bvarClosed depth b = true := by
  induction h with
  | refl _ => intro hc; exact hc
  | next hs _ ih => intro hc; exact ih (bvarClosed_betaStep depth hs hc)

theorem hasFVar_shift (v d c : Nat) (m : Lam) :
    hasFVar v (shift d c m) = hasFVar v m := by
  induction m generalizing c with
  | bvar k =>
    simp only [shift]
    by_cases h : c ≤ k
    · rw [if_pos h]; rfl
    · rw [if_neg h]
  | fvar _ => rfl
  | app _ _ iha ihb => simp [shift, hasFVar, iha c, ihb c]
  | lam _ ih => simp [shift, hasFVar, ih (c + 1)]

theorem hasFVar_false_subst {v : Nat} (k : Nat) {s m : Lam}
    (hs : hasFVar v s = false) (hm : hasFVar v m = false) :
    hasFVar v (subst k s m) = false := by
  induction m generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · rw [if_pos hlt]; rfl
    · rw [if_neg hlt]
      by_cases heq : j = k
      · rw [if_pos heq, hasFVar_shift]; exact hs
      · rw [if_neg heq]; rfl
  | fvar _ => exact hm
  | app a b iha ihb =>
    simp only [hasFVar, Bool.or_eq_false_iff] at hm
    simp [subst, hasFVar, iha k hm.1, ihb k hm.2]
  | lam body ih =>
    simp only [hasFVar] at hm
    exact ih (k + 1) hm

theorem hasFVar_false_betaStep {v : Nat} {a b : Lam} (h : BetaStep a b) :
    hasFVar v a = false → hasFVar v b = false := by
  induction h with
  | beta body arg =>
    simp only [hasFVar, Bool.or_eq_false_iff]
    intro ⟨hb, ha⟩
    exact hasFVar_false_subst 0 ha hb
  | appL _ ih =>
    simp only [hasFVar, Bool.or_eq_false_iff]
    intro ⟨ha, hb⟩; exact ⟨ih ha, hb⟩
  | appR _ ih =>
    simp only [hasFVar, Bool.or_eq_false_iff]
    intro ⟨ha, hb⟩; exact ⟨ha, ih hb⟩
  | lam _ ih =>
    simp only [hasFVar]
    exact ih

theorem hasFVar_false_betaReduces {v : Nat} {a b : Lam} (h : BetaReduces a b) :
    hasFVar v a = false → hasFVar v b = false := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (hasFVar_false_betaStep hs hv)

theorem occursBVar_shift_add (d c e : Nat) (m : Lam) :
    occursBVar (c + e + d) (shift d c m) = occursBVar (c + e) m := by
  induction m generalizing c with
  | bvar j =>
    simp only [shift]
    by_cases hj : c ≤ j
    · rw [if_pos hj]
      simp only [occursBVar]
      by_cases heq : j = c + e
      · subst heq; simp
      · have hne : ¬ (j + d = c + e + d) := fun h' => heq (Nat.add_right_cancel h')
        rw [decide_eq_false hne, decide_eq_false heq]
    · rw [if_neg hj]
      have hne1 : ¬ (j = c + e) := fun h' => hj (by rw [h']; exact Nat.le_add_right c e)
      have hne2 : ¬ (j = c + e + d) := fun h' => hj (by
        rw [h']; exact Nat.le_trans (Nat.le_add_right c e) (Nat.le_add_right _ d))
      simp only [occursBVar, decide_eq_false hne1, decide_eq_false hne2]
  | fvar _ => rfl
  | app _ _ iha ihb => simp [shift, occursBVar, iha c, ihb c]
  | lam _ ih =>
    have heq1 : (c + 1) + e + d = (c + e + d) + 1 := by
      rw [Nat.add_right_comm c 1 e, Nat.add_right_comm (c + e) 1 d]
    have heq2 : (c + 1) + e = (c + e) + 1 := Nat.add_right_comm c 1 e
    simp only [shift, occursBVar, ← heq1, ← heq2]
    exact ih (c + 1)

theorem occursBVar_shift_lt (d c k : Nat) (hk : k < c) (m : Lam) :
    occursBVar k (shift d c m) = occursBVar k m := by
  induction m generalizing c k with
  | bvar j =>
    simp only [shift]
    by_cases hj : c ≤ j
    · rw [if_pos hj]
      have hne1 : ¬ (j = k) := fun h' => Nat.not_le_of_lt hk (by rw [← h']; exact hj)
      have hne2 : ¬ (j + d = k) := fun h' => Nat.not_le_of_lt hk (by
        rw [← h']; exact Nat.le_trans hj (Nat.le_add_right j d))
      simp only [occursBVar, decide_eq_false hne1, decide_eq_false hne2]
    · rw [if_neg hj]
  | fvar _ => rfl
  | app _ _ iha ihb => simp [shift, occursBVar, iha c k hk, ihb c k hk]
  | lam _ ih =>
    simp [shift, occursBVar, ih (c + 1) (k + 1) (Nat.add_lt_add_right hk 1)]

theorem isLambdaI_shift (d c : Nat) (m : Lam) :
    isLambdaI (shift d c m) = isLambdaI m := by
  induction m generalizing c with
  | bvar k =>
    simp only [shift]
    by_cases h : c ≤ k
    · rw [if_pos h]; rfl
    · rw [if_neg h]
  | fvar _ => rfl
  | app _ _ iha ihb => simp [shift, isLambdaI, iha c, ihb c]
  | lam body ih =>
    simp only [shift, isLambdaI, ih (c + 1),
      occursBVar_shift_lt d (c + 1) 0 (Nat.zero_lt_succ c) body]

theorem occursBVar_subst_ge (k e : Nat) (s m : Lam) :
    occursBVar (k + e) (subst k s m) =
      (occursBVar (k + e + 1) m || (occursBVar k m && occursBVar e s)) := by
  induction m generalizing k with
  | bvar j =>
    simp only [subst, occursBVar]
    by_cases hlt : j < k
    · have hne1 : ¬ (j = k + e) := fun h' => Nat.not_le_of_lt hlt (by rw [h']; exact Nat.le_add_right k e)
      have hne2 : ¬ (j = k + e + 1) := fun h' => Nat.not_le_of_lt hlt (by
        rw [h']; exact Nat.le_trans (Nat.le_add_right k e) (Nat.le_succ _))
      have hne3 : ¬ (j = k) := Nat.ne_of_lt hlt
      rw [if_pos hlt]
      simp only [occursBVar, decide_eq_false hne1, decide_eq_false hne2, decide_eq_false hne3]
      rfl
    · rw [if_neg hlt]
      by_cases heq : j = k
      · subst heq
        have hne2 : ¬ (j = j + e + 1) := by
          intro h'
          have hle : j + 1 ≤ j := by
            have h1 : (j + 1) + e ≤ j := by
              rw [Nat.add_right_comm j 1 e]
              exact Nat.le_of_eq h'.symm
            exact Nat.le_trans (Nat.le_add_right (j + 1) e) h1
          exact Nat.lt_irrefl j (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hle)
        rw [if_pos rfl]
        simp only [decide_eq_false hne2, decide_true, Bool.false_or, Bool.true_and]
        have hs := occursBVar_shift_add j 0 e s
        rw [Nat.zero_add, Nat.add_comm e j] at hs
        exact hs
      · rw [if_neg heq]
        have hgt : k < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hgt)
        simp only [decide_eq_false heq, Bool.false_and, Bool.or_false, occursBVar]
        cases j with
        | zero => cases hjpos
        | succ j0 =>
          simp only [Nat.succ_sub_one]
          by_cases hj0 : j0 = k + e
          · subst hj0; simp
          · have hne' : ¬ (j0 + 1 = k + e + 1) := fun h' => hj0 (Nat.add_right_cancel h')
            rw [decide_eq_false hj0, decide_eq_false hne']
  | fvar _ => rfl
  | app a b iha ihb =>
    simp only [subst, occursBVar, iha k, ihb k]
    cases occursBVar (k + e + 1) a <;> cases occursBVar (k + e + 1) b <;>
      cases occursBVar k a <;> cases occursBVar k b <;> cases occursBVar e s <;> rfl
  | lam body ih =>
    have heq1 : (k + 1) + e = (k + e) + 1 := Nat.add_right_comm k 1 e
    simp only [subst, occursBVar]
    rw [← heq1]
    exact ih (k + 1)

theorem occursBVar_subst_of_lt {k j : Nat} (hjk : j < k) (s : Lam) {m : Lam}
    (hocc : occursBVar j m = true) : occursBVar j (subst k s m) = true := by
  induction m generalizing k j with
  | bvar i =>
    simp only [occursBVar, decide_eq_true_eq] at hocc
    subst hocc
    simp only [subst, if_pos hjk, occursBVar, decide_eq_true_eq]
  | fvar _ => cases hocc
  | app a b iha ihb =>
    simp only [subst, occursBVar, Bool.or_eq_true] at hocc ⊢
    rcases hocc with ha | hb
    · exact Or.inl (iha hjk ha)
    · exact Or.inr (ihb hjk hb)
  | lam body ih =>
    simp only [subst, occursBVar] at hocc ⊢
    exact ih (Nat.add_lt_add_right hjk 1) hocc

theorem isLambdaI_subst (k : Nat) {s m : Lam}
    (hs : isLambdaI s = true) (hm : isLambdaI m = true) :
    isLambdaI (subst k s m) = true := by
  induction m generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · rw [if_pos hlt]; rfl
    · rw [if_neg hlt]
      by_cases heq : j = k
      · rw [if_pos heq, isLambdaI_shift]; exact hs
      · rw [if_neg heq]; rfl
  | fvar _ => rfl
  | app a b iha ihb =>
    simp only [isLambdaI, Bool.and_eq_true] at hm
    simp [subst, isLambdaI, iha k hm.1, ihb k hm.2]
  | lam body ih =>
    simp only [isLambdaI, Bool.and_eq_true] at hm
    simp only [subst, isLambdaI, Bool.and_eq_true]
    exact ⟨occursBVar_subst_of_lt (Nat.zero_lt_succ k) s hm.1, ih (k + 1) hm.2⟩

/-- In `λI`-calculus, `BetaStep` preserves BOTH `isLambdaI` AND every free bound-variable occurrence! -/
theorem isLambdaI_and_occurs_betaStep {a b : Lam} (h : BetaStep a b) (hi : isLambdaI a = true) :
    isLambdaI b = true ∧ (∀ k, occursBVar k a = true → occursBVar k b = true) := by
  induction h with
  | beta body arg =>
    simp only [isLambdaI, Bool.and_eq_true] at hi
    obtain ⟨⟨hocc0, hbody⟩, harg⟩ := hi
    refine ⟨isLambdaI_subst 0 harg hbody, fun k hk => ?_⟩
    simp only [occursBVar, Bool.or_eq_true] at hk
    have hge := occursBVar_subst_ge 0 k arg body
    simp only [Nat.zero_add] at hge
    rw [hge]
    rcases hk with hkb | hka
    · simp [hkb]
    · simp [hocc0, hka]
  | appL _ ih =>
    simp only [isLambdaI, Bool.and_eq_true] at hi
    obtain ⟨ihi, ihocc⟩ := ih hi.1
    refine ⟨by simp [isLambdaI, ihi, hi.2], fun k hk => ?_⟩
    simp only [occursBVar, Bool.or_eq_true] at hk ⊢
    rcases hk with hka | hkb
    · exact Or.inl (ihocc k hka)
    · exact Or.inr hkb
  | appR _ ih =>
    simp only [isLambdaI, Bool.and_eq_true] at hi
    obtain ⟨ihi, ihocc⟩ := ih hi.2
    refine ⟨by simp [isLambdaI, hi.1, ihi], fun k hk => ?_⟩
    simp only [occursBVar, Bool.or_eq_true] at hk ⊢
    rcases hk with hka | hkb
    · exact Or.inl hka
    · exact Or.inr (ihocc k hkb)
  | lam _ ih =>
    simp only [isLambdaI, Bool.and_eq_true] at hi
    obtain ⟨ihi, ihocc⟩ := ih hi.2
    refine ⟨by simp [isLambdaI, ihocc 0 hi.1, ihi], fun k hk => ?_⟩
    simp only [occursBVar] at hk ⊢
    exact ihocc (k + 1) hk

theorem isLambdaI_betaStep {a b : Lam} (h : BetaStep a b) (hi : isLambdaI a = true) :
    isLambdaI b = true :=
  (isLambdaI_and_occurs_betaStep h hi).1

theorem isLambdaI_betaReduces {a b : Lam} (h : BetaReduces a b) (hi : isLambdaI a = true) :
    isLambdaI b = true := by
  induction h with
  | refl _ => exact hi
  | next hs _ ih => exact ih (isLambdaI_betaStep hs hi)

/-! ## 4. Takahashi's Parallel `β`-Reduction (`ParBeta`) and Church–Rosser (`λβ |= CR`) -/

inductive ParBeta : Lam → Lam → Prop where
  | bvar (k : Nat) : ParBeta (.bvar k) (.bvar k)
  | fvar (v : Nat) : ParBeta (.fvar v) (.fvar v)
  | app {a a' b b' : Lam} : ParBeta a a' → ParBeta b b' → ParBeta (a @@ b) (a' @@ b')
  | lam {b b' : Lam} : ParBeta b b' → ParBeta (.lam b) (.lam b')
  | beta {b b' a a' : Lam} : ParBeta b b' → ParBeta a a' →
      ParBeta ((.lam b) @@ a) (subst 0 a' b')

theorem parBeta_refl (m : Lam) : ParBeta m m := by
  induction m with
  | bvar k => exact .bvar k
  | fvar v => exact .fvar v
  | app _ _ iha ihb => exact .app iha ihb
  | lam _ ih => exact .lam ih

theorem betaStep_to_parBeta {a b : Lam} (h : BetaStep a b) : ParBeta a b := by
  induction h with
  | beta body arg => exact .beta (parBeta_refl body) (parBeta_refl arg)
  | appL _ ih => exact .app ih (parBeta_refl _)
  | appR _ ih => exact .app (parBeta_refl _) ih
  | lam _ ih => exact .lam ih

theorem parBeta_to_betaReduces {a b : Lam} (h : ParBeta a b) : BetaReduces a b := by
  induction h with
  | bvar _ => exact .refl _
  | fvar _ => exact .refl _
  | app _ _ iha ihb => exact betaReduces_app iha ihb
  | lam _ ih => exact betaReduces_lam ih
  | beta _ _ ihb iha =>
    exact betaReduces_trans
      (betaReduces_app (betaReduces_lam ihb) iha)
      (.next (.beta _ _) (.refl _))

theorem parBeta_shift (d c : Nat) {a b : Lam} (h : ParBeta a b) :
    ParBeta (shift d c a) (shift d c b) := by
  induction h generalizing c with
  | bvar k =>
    simp only [shift]
    by_cases hck : c ≤ k
    · rw [if_pos hck]; exact .bvar _
    · rw [if_neg hck]; exact .bvar _
  | fvar v => exact .fvar v
  | app _ _ iha ihb => exact .app (iha c) (ihb c)
  | lam _ ih => exact .lam (ih (c + 1))
  | @beta b₀ b₀' a₀ a₀' _ _ ihb iha =>
    simp only [shift]
    have hs := shift_subst_above d 0 c a₀' b₀'
    simp only [Nat.zero_add] at hs
    rw [hs]
    exact .beta (ihb (c + 1)) (iha c)

theorem parBeta_subst (k : Nat) {s s' m m' : Lam}
    (hs : ParBeta s s') (hm : ParBeta m m') :
    ParBeta (subst k s m) (subst k s' m') := by
  induction hm generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · simp only [if_pos hlt]; exact .bvar j
    · simp only [if_neg hlt]
      by_cases heq : j = k
      · simp only [if_pos heq]; exact parBeta_shift k 0 hs
      · simp only [if_neg heq]; exact .bvar (j - 1)
  | fvar v => exact .fvar v
  | app _ _ iha ihb => exact .app (iha k) (ihb k)
  | lam _ ih => exact .lam (ih (k + 1))
  | @beta b₀ b₀' a₀ a₀' _ _ ihb iha =>
    simp only [subst]
    rw [subst0_subst k s' a₀' b₀']
    exact .beta (ihb (k + 1)) (iha k)

/-- Takahashi's complete development for untyped `λ`-terms. -/
def cdLam : Lam → Lam
  | .bvar k => .bvar k
  | .fvar v => .fvar v
  | .lam b => .lam (cdLam b)
  | .app (.lam b) a => subst 0 (cdLam a) (cdLam b)
  | .app a b => cdLam a @@ cdLam b

private theorem cdLam_app_non_lam (a b : Lam) (hnot : ∀ p, a ≠ .lam p) :
    cdLam (a @@ b) = cdLam a @@ cdLam b := by
  cases a with
  | bvar _ => rfl
  | fvar _ => rfl
  | app _ _ => rfl
  | lam p => exfalso; exact hnot p rfl

theorem parBeta_triangle {m n : Lam} (h : ParBeta m n) : ParBeta n (cdLam m) := by
  induction h with
  | bvar k => exact .bvar k
  | fvar v => exact .fvar v
  | lam _ ih => exact .lam ih
  | beta _ _ ihb iha => exact parBeta_subst 0 iha ihb
  | @app a a' b b' ha _ iha ihb =>
    cases a with
    | bvar k =>
      cases ha
      exact .app (.bvar k) ihb
    | fvar v =>
      cases ha
      exact .app (.fvar v) ihb
    | app u w =>
      rw [cdLam_app_non_lam (u @@ w) b (fun p hp => by cases hp)]
      exact .app iha ihb
    | lam p =>
      cases ha with
      | @lam _ p' hp =>
        have ihp : ParBeta p' (cdLam p) := by
          change ParBeta (.lam p') (.lam (cdLam p)) at iha
          cases iha with
          | lam h' => exact h'
        exact .beta ihp ihb

theorem parBeta_diamond {a b c : Lam} (hab : ParBeta a b) (hac : ParBeta a c) :
    ∃ d, ParBeta b d ∧ ParBeta c d :=
  ⟨cdLam a, parBeta_triangle hab, parBeta_triangle hac⟩

inductive ParBetaStar : Lam → Lam → Prop where
  | refl (a : Lam) : ParBetaStar a a
  | next {a b c : Lam} : ParBeta a b → ParBetaStar b c → ParBetaStar a c

theorem parBetaStar_trans {a b c : Lam} (h1 : ParBetaStar a b) (h2 : ParBetaStar b c) :
    ParBetaStar a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem betaReduces_to_parBetaStar {a b : Lam} (h : BetaReduces a b) : ParBetaStar a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (betaStep_to_parBeta hs) ih

theorem parBetaStar_to_betaReduces {a b : Lam} (h : ParBetaStar a b) : BetaReduces a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact betaReduces_trans (parBeta_to_betaReduces hs) ih

private theorem parBeta_strip {a b c : Lam} (hab : ParBeta a b) (hac : ParBetaStar a c) :
    ∃ d, ParBetaStar b d ∧ ParBeta c d := by
  induction hac generalizing b with
  | refl _ => exact ⟨b, .refl b, hab⟩
  | next ha1 _ ih =>
    obtain ⟨m, ha1m, hbm⟩ := parBeta_diamond ha1 hab
    obtain ⟨d, hmd, hcd⟩ := ih ha1m
    exact ⟨d, .next hbm hmd, hcd⟩

private theorem parBetaStar_confluence {a b c : Lam}
    (hab : ParBetaStar a b) (hac : ParBetaStar a c) :
    ∃ d, ParBetaStar b d ∧ ParBetaStar c d := by
  induction hab generalizing c with
  | refl _ => exact ⟨c, hac, .refl c⟩
  | next ha1 _ ih =>
    obtain ⟨m, ha1m, hcm⟩ := parBeta_strip ha1 hac
    obtain ⟨d, hbd, hmd⟩ := ih ha1m
    exact ⟨d, hbd, .next hcm hmd⟩

/-- **Church–Rosser Confluence for `λβ`**: co-initial `β`-reductions have a common reduct. -/
theorem church_rosser_beta {a b c : Lam} (hab : BetaReduces a b) (hac : BetaReduces a c) :
    ∃ d, BetaReduces b d ∧ BetaReduces c d := by
  obtain ⟨d, hbd, hcd⟩ :=
    parBetaStar_confluence (betaReduces_to_parBetaStar hab) (betaReduces_to_parBetaStar hac)
  exact ⟨d, parBetaStar_to_betaReduces hbd, parBetaStar_to_betaReduces hcd⟩

/-- **Church–Rosser Theorem for `=β`**: `β`-convertible terms have a common reduct. -/
theorem church_rosser_betaConv {a b : Lam} (h : BetaConv a b) :
    ∃ d, BetaReduces a d ∧ BetaReduces b d := by
  induction h with
  | refl a => exact ⟨a, .refl a, .refl a⟩
  | step hs => exact ⟨_, .next hs (.refl _), .refl _⟩
  | symm _ ih =>
    obtain ⟨d, h1, h2⟩ := ih
    exact ⟨d, h2, h1⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨d1, ha1, hb1⟩ := ih1
    obtain ⟨d2, hb2, hc2⟩ := ih2
    obtain ⟨w, hw1, hw2⟩ := church_rosser_beta hb1 hb2
    exact ⟨w, betaReduces_trans ha1 hw1, betaReduces_trans hc2 hw2⟩

theorem betaNF_reduces_eq {a b : Lam} (hnf : IsBetaNF a) (hred : BetaReduces a b) : a = b := by
  cases hred with
  | refl _ => rfl
  | next hs _ => exfalso; exact hnf _ hs

theorem betaNF_unique {m nf₁ nf₂ : Lam}
    (h1 : BetaReduces m nf₁) (hnf1 : IsBetaNF nf₁)
    (h2 : BetaReduces m nf₂) (hnf2 : IsBetaNF nf₂) : nf₁ = nf₂ := by
  obtain ⟨d, hd1, hd2⟩ := church_rosser_beta h1 h2
  rw [betaNF_reduces_eq hnf1 hd1, betaNF_reduces_eq hnf2 hd2]

end FormalLambdaConjectures
