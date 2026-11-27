import formal_algebra.s_structural_laws

/-!
# Untyped `λβ`-Calculus, Translation of `CL(S)`, and Constructive Church–Rosser

Self-contained Lean 4.33.1 formalization of de Bruijn untyped `λ`-terms (with both bound
indices `bvar` and free variables `fvar` matching open `CL(S)` variables), pure `β`-reduction,
Takahashi parallel reduction and Church–Rosser (`ConvBeta`), and the standard translation
`toLam : FormalAlgebra.Term → Lam` mapping `S ↦ λa b c. (a c)(b c)`.

Zero `sorry`, zero `Classical.choice`, zero `native_decide`, zero custom axioms.
-/

namespace FormalQ32

open FormalAlgebra

/-! ## 1. Syntax of `λ`-Terms, Shifting, and Capture-Avoiding Substitution -/

inductive Lam where
  | bvar : Nat → Lam
  | fvar : Nat → Lam
  | lam  : Lam → Lam
  | app  : Lam → Lam → Lam
  deriving DecidableEq, Repr

infixl:70 " ∘ₗ " => Lam.app

def shift (d : Nat) (c : Nat) : Lam → Lam
  | .bvar i => if c ≤ i then .bvar (i + d) else .bvar i
  | .fvar k => .fvar k
  | .lam m => .lam (shift d (c + 1) m)
  | .app m n => .app (shift d c m) (shift d c n)

def substB (k : Nat) (u : Lam) : Lam → Lam
  | .bvar i =>
      if i < k then .bvar i
      else if i = k then shift k 0 u
      else .bvar (i - 1)
  | .fvar v => .fvar v
  | .lam m => .lam (substB (k + 1) u m)
  | .app m n => .app (substB k u m) (substB k u n)

/-- Free-variable substitution for closed-bvar ranges (`∀ v, bvarBound 0 (σ v) = true`). -/
def substFClosed (σ : Nat → Lam) : Lam → Lam
  | .bvar i => .bvar i
  | .fvar v => σ v
  | .lam m => .lam (substFClosed σ m)
  | .app m n => .app (substFClosed σ m) (substFClosed σ n)

def bvarBound (b : Nat) : Lam → Bool
  | .bvar i => decide (i < b)
  | .fvar _ => true
  | .lam m => bvarBound (b + 1) m
  | .app m n => bvarBound b m && bvarBound b n

/-! ## 2. Pure `β`-Reduction and Convertibility (`λβ`) -/

inductive BetaStep : Lam → Lam → Prop where
  | root (m n : Lam) : BetaStep (.app (.lam m) n) (substB 0 n m)
  | lam {m m' : Lam} : BetaStep m m' → BetaStep (.lam m) (.lam m')
  | left {m m' n : Lam} : BetaStep m m' → BetaStep (.app m n) (.app m' n)
  | right {m n n' : Lam} : BetaStep n n' → BetaStep (.app m n) (.app m n')

inductive BetaReduces : Lam → Lam → Prop where
  | refl (m : Lam) : BetaReduces m m
  | next {a b c : Lam} : BetaStep a b → BetaReduces b c → BetaReduces a c

inductive ConvBeta : Lam → Lam → Prop where
  | refl (m : Lam) : ConvBeta m m
  | step {a b : Lam} : BetaStep a b → ConvBeta a b
  | symm {a b : Lam} : ConvBeta a b → ConvBeta b a
  | trans {a b c : Lam} : ConvBeta a b → ConvBeta b c → ConvBeta a c

def IsBetaNF (m : Lam) : Prop := ∀ m', ¬ BetaStep m m'

theorem betaReduces_trans {a b c : Lam} (h1 : BetaReduces a b) (h2 : BetaReduces b c) :
    BetaReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem betaReduces_single {a b : Lam} (h : BetaStep a b) : BetaReduces a b :=
  .next h (.refl b)

theorem betaReduces_lam {m m' : Lam} (h : BetaReduces m m') :
    BetaReduces (.lam m) (.lam m') := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.lam hs) ih

theorem betaReduces_left {m m' : Lam} (h : BetaReduces m m') (n : Lam) :
    BetaReduces (m ∘ₗ n) (m' ∘ₗ n) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.left hs) ih

theorem betaReduces_right (m : Lam) {n n' : Lam} (h : BetaReduces n n') :
    BetaReduces (m ∘ₗ n) (m ∘ₗ n') := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.right hs) ih

theorem betaReduces_app {a a' b b' : Lam} (ha : BetaReduces a a') (hb : BetaReduces b b') :
    BetaReduces (a ∘ₗ b) (a' ∘ₗ b') :=
  betaReduces_trans (betaReduces_left ha b) (betaReduces_right a' hb)

theorem betaReduces_to_conv {a b : Lam} (h : BetaReduces a b) : ConvBeta a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .trans (.step hs) ih

theorem convBeta_lam {a b : Lam} (h : ConvBeta a b) : ConvBeta (.lam a) (.lam b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact .step (.lam hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convBeta_left {a a' : Lam} (h : ConvBeta a a') (b : Lam) :
    ConvBeta (a ∘ₗ b) (a' ∘ₗ b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact .step (.left hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convBeta_right (a : Lam) {b b' : Lam} (h : ConvBeta b b') :
    ConvBeta (a ∘ₗ b) (a ∘ₗ b') := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact .step (.right hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convBeta_app {a a' b b' : Lam} (ha : ConvBeta a a') (hb : ConvBeta b b') :
    ConvBeta (a ∘ₗ b) (a' ∘ₗ b') :=
  .trans (convBeta_left ha b) (convBeta_right a' hb)

theorem betaNF_reduces_eq {a b : Lam} (hnf : IsBetaNF a) (hr : BetaReduces a b) : a = b := by
  cases hr with
  | refl _ => rfl
  | next hs _ => exfalso; exact hnf _ hs

/-! ## 3. De Bruijn Shifting and Substitution Algebra -/

theorem shift_zero (c : Nat) (t : Lam) : shift 0 c t = t := by
  induction t generalizing c with
  | bvar i =>
    simp only [shift]
    split <;> rfl
  | fvar _ => rfl
  | lam m ih => simp only [shift, ih (c + 1)]
  | app m n ihm ihn => simp only [shift, ihm c, ihn c]

theorem shift_add_mid {a c d1 d2 : Nat} (hac : a ≤ c) (hci : c ≤ a + d1) (v : Lam) :
    shift (d1 + d2) a v = shift d2 c (shift d1 a v) := by
  induction v generalizing a c with
  | bvar j =>
    simp only [shift]
    by_cases haj : a ≤ j
    · have hcj : c ≤ j + d1 := Nat.le_trans hci (Nat.add_le_add_right haj d1)
      simp only [if_pos haj, shift, if_pos hcj, Nat.add_assoc]
    · have hcj : ¬ (c ≤ j) := fun hh => haj (Nat.le_trans hac hh)
      simp only [if_neg haj, shift, if_neg hcj]
  | fvar _ => rfl
  | lam m ih =>
    have hac' : a + 1 ≤ c + 1 := Nat.add_le_add_right hac 1
    have hci' : c + 1 ≤ (a + 1) + d1 := by
      rw [Nat.add_assoc a 1 d1, Nat.add_comm 1 d1, ← Nat.add_assoc a d1 1]
      exact Nat.add_le_add_right hci 1
    simp only [shift, ih hac' hci']
  | app m n ihm ihn =>
    simp only [shift, ihm hac hci, ihn hac hci]

theorem shift_shift {d1 d2 c1 c2 : Nat} (hc : c1 ≤ c2) (t : Lam) :
    shift d2 (c2 + d1) (shift d1 c1 t) = shift d1 c1 (shift d2 c2 t) := by
  induction t generalizing c1 c2 with
  | bvar i =>
    simp only [shift]
    by_cases h1 : c1 ≤ i
    · simp only [if_pos h1, shift]
      by_cases h2 : c2 ≤ i
      · have h2' : c2 + d1 ≤ i + d1 := Nat.add_le_add_right h2 d1
        have h1' : c1 ≤ i + d2 := Nat.le_trans h1 (Nat.le_add_right i d2)
        simp only [if_pos h2, if_pos h2', shift, if_pos h1']
        exact congrArg Lam.bvar (by
          rw [Nat.add_assoc i d1 d2, Nat.add_comm d1 d2, ← Nat.add_assoc i d2 d1])
      · have h2' : ¬ (c2 + d1 ≤ i + d1) := fun hh => h2 (Nat.le_of_add_le_add_right hh)
        simp only [if_neg h2, if_neg h2', shift, if_pos h1]
    · have h2 : ¬ (c2 ≤ i) := fun hh => h1 (Nat.le_trans hc hh)
      have h2' : ¬ (c2 + d1 ≤ i) := fun hh => h2 (Nat.le_trans (Nat.le_add_right c2 d1) hh)
      simp only [if_neg h1, if_neg h2, shift, if_neg h2']
  | fvar _ => rfl
  | lam m ih =>
    have hc' : c1 + 1 ≤ c2 + 1 := Nat.add_le_add_right hc 1
    have heq : (c2 + 1) + d1 = (c2 + d1) + 1 := by
      rw [Nat.add_assoc c2 1 d1, Nat.add_comm 1 d1, ← Nat.add_assoc c2 d1 1]
    simp only [shift, ← heq, ih hc']
  | app m n ihm ihn =>
    simp only [shift, ihm hc, ihn hc]

theorem shift_substB_ge {d c k : Nat} (hck : c ≤ k) (u t : Lam) :
    shift d c (substB k u t) = substB (k + d) u (shift d c t) := by
  induction t generalizing c k with
  | bvar i =>
    simp only [substB, shift]
    by_cases hci : c ≤ i
    · simp only [if_pos hci, substB]
      by_cases hik : i < k
      · have hik' : i + d < k + d := Nat.add_lt_add_right hik d
        simp only [if_pos hik, if_pos hik', shift, if_pos hci]
      · simp only [if_neg hik]
        have hik' : ¬ (i + d < k + d) := fun hh => hik (Nat.lt_of_add_lt_add_right hh)
        simp only [if_neg hik']
        by_cases heq : i = k
        · subst heq
          simp only [↓reduceIte]
          exact (shift_add_mid (a := 0) (c := c) (d1 := i) (d2 := d) (Nat.zero_le c)
            (by rw [Nat.zero_add]; exact hci) u).symm
        · have heq' : i + d ≠ k + d := fun hh => heq (Nat.add_right_cancel hh)
          simp only [if_neg heq, if_neg heq', shift]
          have hgt : k < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hik) (Ne.symm heq)
          have hci1 : c ≤ i - 1 := Nat.le_pred_of_lt (Nat.lt_of_le_of_lt hck hgt)
          have hpos : 1 ≤ i := Nat.lt_of_le_of_lt (Nat.zero_le k) hgt
          have hsub : i + d - 1 = (i - 1) + d := by
            cases i with
            | zero => cases hpos
            | succ i' => simp only [Nat.succ_add, Nat.succ_sub_one]
          simp only [if_pos hci1, hsub]
    · simp only [if_neg hci, substB]
      have hik : i < k := Nat.lt_of_lt_of_le (Nat.not_le.mp hci) hck
      have hik' : i < k + d := Nat.lt_of_lt_of_le hik (Nat.le_add_right k d)
      simp only [if_pos hik, if_pos hik', shift, if_neg hci]
  | fvar _ => rfl
  | lam m ih =>
    have hck' : c + 1 ≤ k + 1 := Nat.add_le_add_right hck 1
    have heq : (k + 1) + d = (k + d) + 1 := by
      rw [Nat.add_assoc k 1 d, Nat.add_comm 1 d, ← Nat.add_assoc k d 1]
    simp only [substB, shift, ih hck', heq]
  | app m n ihm ihn =>
    simp only [substB, shift, ihm hck, ihn hck]

theorem shift_substB_le {d c k : Nat} (hkc : k ≤ c) (u t : Lam) :
    shift d c (substB k u t) = substB k (shift d (c - k) u) (shift d (c + 1) t) := by
  induction t generalizing c k with
  | bvar i =>
    simp only [substB, shift]
    by_cases hik : i < k
    · have hic1 : ¬ (c + 1 ≤ i) := fun hh =>
        Nat.lt_irrefl i (Nat.lt_of_lt_of_le hik (Nat.le_trans hkc (Nat.le_trans (Nat.le_succ c) hh)))
      have hic : ¬ (c ≤ i) := fun hh =>
        Nat.lt_irrefl i (Nat.lt_of_lt_of_le hik (Nat.le_trans hkc hh))
      simp only [if_neg hic1, shift, if_neg hic, substB, if_pos hik]
    · simp only [if_neg hik]
      by_cases heq : i = k
      · subst heq
        have hic1 : ¬ (c + 1 ≤ i) := fun hh =>
          Nat.not_le_of_gt (Nat.lt_succ_of_le hkc) hh
        simp only [↓reduceIte, if_neg hic1, substB, Nat.lt_irrefl]
        have hsub : (c - i) + i = c := Nat.sub_add_cancel hkc
        have hsh := shift_shift (d1 := i) (d2 := d) (c1 := 0) (c2 := c - i) (Nat.zero_le _) u
        rw [hsub] at hsh
        exact hsh
      · simp only [if_neg heq]
        have hgt : k < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hik) (Ne.symm heq)
        have hpos : 1 ≤ i := Nat.lt_of_le_of_lt (Nat.zero_le k) hgt
        by_cases hic1 : c + 1 ≤ i
        · have hic_pred : c ≤ i - 1 := by
            cases i with
            | zero => cases hpos
            | succ i' => exact Nat.le_of_succ_le_succ hic1
          have hik' : ¬ (i + d < k) := fun hh =>
            Nat.lt_irrefl k (Nat.lt_of_lt_of_le hgt (Nat.le_trans (Nat.le_add_right i d) (Nat.le_of_lt hh)))
          have heq' : i + d ≠ k := fun hh =>
            Nat.ne_of_gt (Nat.lt_of_lt_of_le hgt (Nat.le_add_right i d)) hh
          have hsub : (i - 1) + d = i + d - 1 := by
            cases i with
            | zero => cases hpos
            | succ i' => simp only [Nat.succ_add, Nat.succ_sub_one]
          simp only [if_pos hic1, shift, if_pos hic_pred, substB, if_neg hik', if_neg heq', hsub]
        · have hic_pred : ¬ (c ≤ i - 1) := fun hh => hic1 (by
            cases i with
            | zero => cases hpos
            | succ i' => exact Nat.succ_le_succ hh)
          simp only [if_neg hic1, shift, if_neg hic_pred, substB, if_neg hik, if_neg heq]
  | fvar _ => rfl
  | lam m ih =>
    have hkc' : k + 1 ≤ c + 1 := Nat.add_le_add_right hkc 1
    have hsub : (c + 1) - (k + 1) = c - k := Nat.succ_sub_succ_eq_sub c k
    simp only [substB, shift, ih hkc', hsub]
  | app m n ihm ihn =>
    simp only [substB, shift, ihm hkc, ihn hkc]

theorem substB_shift_cancel (k : Nat) (u v : Lam) :
    substB k u (shift 1 k v) = v := by
  induction v generalizing k with
  | bvar i =>
    simp only [shift]
    by_cases hki : k ≤ i
    · have hik' : ¬ (i + 1 < k) := fun hh =>
        Nat.not_lt_of_ge (Nat.le_trans hki (Nat.le_succ i)) hh
      have heq' : i + 1 ≠ k := fun hh =>
        Nat.ne_of_gt (Nat.lt_succ_of_le hki) hh
      simp only [if_pos hki, substB, if_neg hik', if_neg heq', Nat.add_sub_cancel]
    · have hik : i < k := Nat.not_le.mp hki
      simp only [if_neg hki, substB, if_pos hik]
  | fvar _ => rfl
  | lam m ih => simp only [shift, substB, ih (k + 1)]
  | app m n ihm ihn => simp only [shift, substB, ihm k, ihn k]

theorem substB_substB {c k : Nat} (hck : c ≤ k) (u v t : Lam) :
    substB k v (substB c u t) = substB c (substB (k - c) v u) (substB (k + 1) v t) := by
  induction t generalizing c k with
  | bvar i =>
    simp only [substB]
    by_cases hic : i < c
    · have hik : i < k := Nat.lt_of_lt_of_le hic hck
      have hik1 : i < k + 1 := Nat.lt_succ_of_lt hik
      simp only [if_pos hic, substB, if_pos hik, if_pos hik1]
    · simp only [if_neg hic]
      by_cases heqc : i = c
      · subst heqc
        have hik1 : i < k + 1 := Nat.lt_succ_of_le hck
        simp only [↓reduceIte, if_pos hik1, substB, Nat.lt_irrefl]
        have hge := (shift_substB_ge (d := i) (c := 0) (k := k - i) (Nat.zero_le _) v u).symm
        rw [Nat.sub_add_cancel hck] at hge
        exact hge
      · simp only [if_neg heqc]
        have hgtc : c < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hic) (Ne.symm heqc)
        have hpos : 1 ≤ i := Nat.lt_of_le_of_lt (Nat.zero_le c) hgtc
        by_cases hik1 : i < k + 1
        · have hi_pred_k : i - 1 < k := by
            cases i with
            | zero => cases hpos
            | succ i' => exact Nat.lt_of_succ_lt_succ hik1
          simp only [if_pos hik1, substB, if_pos hi_pred_k, if_neg hic, if_neg heqc]
        · simp only [if_neg hik1]
          by_cases heqk1 : i = k + 1
          · subst heqk1
            simp only [↓reduceIte, Nat.add_sub_cancel, substB, Nat.lt_irrefl]
            have hmid := shift_add_mid (a := 0) (c := c) (d1 := k) (d2 := 1) (Nat.zero_le c)
              (by rw [Nat.zero_add]; exact hck) v
            rw [hmid, substB_shift_cancel]
          · simp only [if_neg heqk1]
            have hgtk1 : k + 1 < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hik1) (Ne.symm heqk1)
            cases i with
            | zero => cases hpos
            | succ i' =>
              have hki' : k < i' := Nat.lt_of_succ_lt_succ hgtk1
              have hci' : c < i' := Nat.lt_of_le_of_lt hck hki'
              have hnlt_k : ¬ (i' < k) := Nat.not_lt_of_gt hki'
              have hne_k : i' ≠ k := Nat.ne_of_gt hki'
              have hnlt_c : ¬ (i' < c) := Nat.not_lt_of_gt hci'
              have hne_c : i' ≠ c := Nat.ne_of_gt hci'
              simp only [Nat.succ_sub_one, substB, if_neg hnlt_k, if_neg hne_k,
                         if_neg hnlt_c, if_neg hne_c]
  | fvar _ => rfl
  | lam m ih =>
    have hck' : c + 1 ≤ k + 1 := Nat.add_le_add_right hck 1
    have hsub : (k + 1) - (c + 1) = k - c := Nat.succ_sub_succ_eq_sub k c
    simp only [substB, ih hck', hsub]
  | app m n ihm ihn =>
    simp only [substB, ihm hck, ihn hck]

/-! ## 4. Takahashi Parallel `β`-Reduction and Church–Rosser (`λβ |= CR`) -/

inductive ParBeta : Lam → Lam → Prop where
  | bvar (i : Nat) : ParBeta (.bvar i) (.bvar i)
  | fvar (v : Nat) : ParBeta (.fvar v) (.fvar v)
  | lam {m m' : Lam} : ParBeta m m' → ParBeta (.lam m) (.lam m')
  | app {a a' b b' : Lam} : ParBeta a a' → ParBeta b b' → ParBeta (a ∘ₗ b) (a' ∘ₗ b')
  | beta {m m' n n' : Lam} :
      ParBeta m m' → ParBeta n n' → ParBeta ((.lam m) ∘ₗ n) (substB 0 n' m')

theorem parBeta_refl (t : Lam) : ParBeta t t := by
  induction t with
  | bvar i => exact .bvar i
  | fvar v => exact .fvar v
  | lam _ ih => exact .lam ih
  | app _ _ iha ihb => exact .app iha ihb

theorem betaStep_to_parBeta {a b : Lam} (h : BetaStep a b) : ParBeta a b := by
  induction h with
  | root m n => exact .beta (parBeta_refl m) (parBeta_refl n)
  | lam _ ih => exact .lam ih
  | left _ ih => exact .app ih (parBeta_refl _)
  | right _ ih => exact .app (parBeta_refl _) ih

theorem parBeta_to_betaReduces {a b : Lam} (h : ParBeta a b) : BetaReduces a b := by
  induction h with
  | bvar i => exact .refl _
  | fvar v => exact .refl _
  | lam _ ih => exact betaReduces_lam ih
  | app _ _ iha ihb => exact betaReduces_app iha ihb
  | beta _ _ ihm ihn =>
    exact betaReduces_trans
      (betaReduces_app (betaReduces_lam ihm) ihn)
      (betaReduces_single (.root _ _))

theorem parBeta_shift (d c : Nat) {a b : Lam} (h : ParBeta a b) :
    ParBeta (shift d c a) (shift d c b) := by
  induction h generalizing c with
  | bvar i => exact parBeta_refl _
  | fvar v => exact .fvar v
  | lam _ ih => exact .lam (ih (c + 1))
  | app _ _ iha ihb => exact .app (iha c) (ihb c)
  | @beta m m' n n' _ _ ihm ihn =>
    simp only [shift]
    have hle := shift_substB_le (d := d) (c := c) (k := 0) (Nat.zero_le c) n' m'
    rw [Nat.sub_zero] at hle
    rw [hle]
    exact .beta (ihm (c + 1)) (ihn c)

theorem parBeta_substB (k : Nat) {m m' n n' : Lam}
    (hm : ParBeta m m') (hn : ParBeta n n') :
    ParBeta (substB k n m) (substB k n' m') := by
  induction hm generalizing k with
  | bvar i =>
    simp only [substB]
    split
    · exact .bvar i
    · split
      · exact parBeta_shift k 0 hn
      · exact .bvar (i - 1)
  | fvar v => exact .fvar v
  | lam _ ih => exact .lam (ih (k + 1))
  | app _ _ iha ihb => exact .app (iha k) (ihb k)
  | @beta body body' arg arg' _ _ ihbody iharg =>
    simp only [substB]
    have hss := substB_substB (c := 0) (k := k) (Nat.zero_le k) arg' n' body'
    rw [Nat.sub_zero] at hss
    rw [hss]
    exact .beta (ihbody (k + 1)) (iharg k)

def completeDevBeta : Lam → Lam
  | .app (.lam m) n => substB 0 (completeDevBeta n) (completeDevBeta m)
  | .app a b => .app (completeDevBeta a) (completeDevBeta b)
  | .lam m => .lam (completeDevBeta m)
  | .bvar i => .bvar i
  | .fvar v => .fvar v

private theorem completeDevBeta_non_lam (a b : Lam) (hnot : ∀ m, a ≠ .lam m) :
    completeDevBeta (a ∘ₗ b) = completeDevBeta a ∘ₗ completeDevBeta b := by
  cases a with
  | bvar _ => rfl
  | fvar _ => rfl
  | app _ _ => rfl
  | lam m => exfalso; exact hnot m rfl

theorem parBeta_triangle {a b : Lam} (h : ParBeta a b) : ParBeta b (completeDevBeta a) := by
  induction h with
  | bvar i => exact .bvar i
  | fvar v => exact .fvar v
  | lam _ ih => exact .lam ih
  | @beta m m' n n' _ _ ihm ihn =>
    exact parBeta_substB 0 ihm ihn
  | @app a a' b b' ha hb iha ihb =>
    cases a with
    | bvar i =>
      cases ha
      exact .app (.bvar i) ihb
    | fvar v =>
      cases ha
      exact .app (.fvar v) ihb
    | app u w =>
      rw [completeDevBeta_non_lam (u ∘ₗ w) b (fun m h => by cases h)]
      exact .app iha ihb
    | lam m =>
      change ParBeta (a' ∘ₗ b') (substB 0 (completeDevBeta b) (completeDevBeta m))
      cases ha with
      | @lam _ m' hm =>
        have ihm : ParBeta m' (completeDevBeta m) := by
          change ParBeta (.lam m') (.lam (completeDevBeta m)) at iha
          cases iha with
          | lam h => exact h
        exact .beta ihm ihb

theorem parBeta_diamond {a b c : Lam} (hab : ParBeta a b) (hac : ParBeta a c) :
    ∃ d, ParBeta b d ∧ ParBeta c d :=
  ⟨completeDevBeta a, parBeta_triangle hab, parBeta_triangle hac⟩

inductive ParBetaReduces : Lam → Lam → Prop where
  | refl (a : Lam) : ParBetaReduces a a
  | next {a b c : Lam} : ParBeta a b → ParBetaReduces b c → ParBetaReduces a c

private theorem parBetaReduces_trans {a b c : Lam}
    (h1 : ParBetaReduces a b) (h2 : ParBetaReduces b c) : ParBetaReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .next hs (ih h2)

private theorem betaReduces_to_par {a b : Lam} (h : BetaReduces a b) : ParBetaReduces a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (betaStep_to_parBeta hs) ih

private theorem par_to_betaReduces {a b : Lam} (h : ParBetaReduces a b) : BetaReduces a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact betaReduces_trans (parBeta_to_betaReduces hs) ih

private theorem parBeta_strip {a b c : Lam} (hab : ParBeta a b) (hac : ParBetaReduces a c) :
    ∃ d, ParBetaReduces b d ∧ ParBeta c d := by
  induction hac generalizing b with
  | refl _ => exact ⟨b, .refl b, hab⟩
  | @next _ a1 _ ha1 _ ih =>
    obtain ⟨m, ha1m, hbm⟩ := parBeta_diamond ha1 hab
    obtain ⟨d, hmd, hcd⟩ := ih ha1m
    exact ⟨d, .next hbm hmd, hcd⟩

private theorem parBetaReduces_confluence {a b c : Lam}
    (hab : ParBetaReduces a b) (hac : ParBetaReduces a c) :
    ∃ d, ParBetaReduces b d ∧ ParBetaReduces c d := by
  induction hab generalizing c with
  | refl _ => exact ⟨c, hac, .refl c⟩
  | @next _ b1 _ hb1 _ ih =>
    obtain ⟨m, hbm, hcm⟩ := parBeta_strip hb1 hac
    obtain ⟨d, hbd, hmd⟩ := ih hbm
    exact ⟨d, hbd, .next hcm hmd⟩

theorem betaReduces_confluence {a b c : Lam}
    (hab : BetaReduces a b) (hac : BetaReduces a c) :
    ∃ d, BetaReduces b d ∧ BetaReduces c d := by
  obtain ⟨d, hbd, hcd⟩ := parBetaReduces_confluence (betaReduces_to_par hab) (betaReduces_to_par hac)
  exact ⟨d, par_to_betaReduces hbd, par_to_betaReduces hcd⟩

/-- **Church–Rosser Theorem for `λβ`** (constructively proved via Takahashi developments). -/
theorem church_rosser_beta {a b : Lam} (h : ConvBeta a b) :
    ∃ c, BetaReduces a c ∧ BetaReduces b c := by
  induction h with
  | refl m => exact ⟨m, .refl m, .refl m⟩
  | step hs => exact ⟨_, betaReduces_single hs, .refl _⟩
  | symm _ ih =>
    obtain ⟨c, h1, h2⟩ := ih
    exact ⟨c, h2, h1⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨c1, hac1, hbc1⟩ := ih1
    obtain ⟨c2, hbc2, hdc2⟩ := ih2
    obtain ⟨e, hc1e, hc2e⟩ := betaReduces_confluence hbc1 hbc2
    exact ⟨e, betaReduces_trans hac1 hc1e, betaReduces_trans hdc2 hc2e⟩

theorem convBeta_to_nf {a b : Lam} (hconv : ConvBeta a b) (hnf : IsBetaNF b) :
    BetaReduces a b := by
  obtain ⟨c, hac, hbc⟩ := church_rosser_beta hconv
  rw [betaNF_reduces_eq hnf hbc]
  exact hac

/-! ## 5. Standard Translation `toLam : Term → Lam` and Lifting of `CL(S)` -/

/-- `S_λ = λa. λb. λc. (a c)(b c)`. -/
def lamS : Lam :=
  .lam (.lam (.lam (((.bvar 2) ∘ₗ (.bvar 0)) ∘ₗ ((.bvar 1) ∘ₗ (.bvar 0)))))

def toLam : Term → Lam
  | .s => lamS
  | .var k => .fvar k
  | .app a b => .app (toLam a) (toLam b)

theorem bvarBound_mono {b1 b2 : Nat} (hle : b1 ≤ b2) (t : Lam) :
    bvarBound b1 t = true → bvarBound b2 t = true := by
  induction t generalizing b1 b2 with
  | bvar i =>
    simp only [bvarBound, decide_eq_true_eq]
    intro hi
    exact Nat.lt_of_lt_of_le hi hle
  | fvar _ => intro _; rfl
  | lam m ih => exact ih (Nat.add_le_add_right hle 1)
  | app m n ihm ihn =>
    simp only [bvarBound, Bool.and_eq_true]
    intro ⟨hm, hn⟩
    exact ⟨ihm hle hm, ihn hle hn⟩

theorem shift_of_bvarBound {b c : Nat} (d : Nat) (t : Lam)
    (hb : bvarBound b t = true) (hbc : b ≤ c) : shift d c t = t := by
  induction t generalizing b c with
  | bvar i =>
    simp only [bvarBound, decide_eq_true_eq] at hb
    have hnot : ¬ (c ≤ i) := Nat.not_le_of_gt (Nat.lt_of_lt_of_le hb hbc)
    simp only [shift, if_neg hnot]
  | fvar _ => rfl
  | lam m ih =>
    simp only [bvarBound] at hb
    simp only [shift, ih hb (Nat.add_le_add_right hbc 1)]
  | app m n ihm ihn =>
    simp only [bvarBound, Bool.and_eq_true] at hb
    simp only [shift, ihm hb.1 hbc, ihn hb.2 hbc]

theorem substB_of_bvarBound {b k : Nat} (u t : Lam)
    (hb : bvarBound b t = true) (hbk : b ≤ k) : substB k u t = t := by
  induction t generalizing b k with
  | bvar i =>
    simp only [bvarBound, decide_eq_true_eq] at hb
    have hik : i < k := Nat.lt_of_lt_of_le hb hbk
    simp only [substB, if_pos hik]
  | fvar _ => rfl
  | lam m ih =>
    simp only [bvarBound] at hb
    simp only [substB, ih hb (Nat.add_le_add_right hbk 1)]
  | app m n ihm ihn =>
    simp only [bvarBound, Bool.and_eq_true] at hb
    simp only [substB, ihm hb.1 hbk, ihn hb.2 hbk]

theorem bvarBound_toLam (t : Term) : bvarBound 0 (toLam t) = true := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [toLam, bvarBound, iha, ihb, Bool.and_self]

theorem lamS_app1 {x : Lam} (hx : bvarBound 0 x = true) :
    BetaStep (lamS ∘ₗ x) (.lam (.lam ((x ∘ₗ .bvar 0) ∘ₗ (.bvar 1 ∘ₗ .bvar 0)))) := by
  have hstep := BetaStep.root (.lam (.lam (((.bvar 2) ∘ₗ (.bvar 0)) ∘ₗ ((.bvar 1) ∘ₗ (.bvar 0))))) x
  have hsh : shift 2 0 x = x := shift_of_bvarBound 2 x hx (Nat.le_refl 0)
  simp only [substB, show ¬ (2 < 2) from Nat.lt_irrefl 2, ↓reduceIte,
             show (0 < 2) from by decide, show (1 < 2) from by decide, hsh] at hstep
  exact hstep

theorem lamS_app2 {x y : Lam} (hx : bvarBound 0 x = true) (hy : bvarBound 0 y = true) :
    BetaReduces ((lamS ∘ₗ x) ∘ₗ y) (.lam ((x ∘ₗ .bvar 0) ∘ₗ (y ∘ₗ .bvar 0))) := by
  have h1 : BetaStep ((lamS ∘ₗ x) ∘ₗ y)
      ((.lam (.lam ((x ∘ₗ .bvar 0) ∘ₗ (.bvar 1 ∘ₗ .bvar 0)))) ∘ₗ y) :=
    .left (lamS_app1 hx)
  have h2 := BetaStep.root (.lam ((x ∘ₗ .bvar 0) ∘ₗ (.bvar 1 ∘ₗ .bvar 0))) y
  have hsubx : substB 1 y x = x := substB_of_bvarBound y x hx (Nat.zero_le 1)
  have hshy : shift 1 0 y = y := shift_of_bvarBound 1 y hy (Nat.le_refl 0)
  simp only [substB, hsubx, show (0 < 1) from by decide, ↓reduceIte,
             show ¬ (1 < 1) from Nat.lt_irrefl 1, hshy] at h2
  exact .next h1 (betaReduces_single h2)

theorem lamS_app3 {x y z : Lam}
    (hx : bvarBound 0 x = true) (hy : bvarBound 0 y = true) :
    BetaReduces (((lamS ∘ₗ x) ∘ₗ y) ∘ₗ z) ((x ∘ₗ z) ∘ₗ (y ∘ₗ z)) := by
  have h12 := betaReduces_left (lamS_app2 hx hy) z
  have h3 := BetaStep.root ((x ∘ₗ .bvar 0) ∘ₗ (y ∘ₗ .bvar 0)) z
  have hsubx : substB 0 z x = x := substB_of_bvarBound z x hx (Nat.le_refl 0)
  have hsuby : substB 0 z y = y := substB_of_bvarBound z y hy (Nat.le_refl 0)
  simp only [substB, hsubx, hsuby, Nat.lt_irrefl, ↓reduceIte, shift_zero] at h3
  exact betaReduces_trans h12 (betaReduces_single h3)

theorem step_to_betaReduces {a b : Term} (h : Step a b) :
    BetaReduces (toLam a) (toLam b) := by
  induction h with
  | root x y z => exact lamS_app3 (bvarBound_toLam x) (bvarBound_toLam y)
  | left _ ih => exact betaReduces_left ih _
  | right _ ih => exact betaReduces_right _ ih

theorem reduces_to_betaReduces {a b : Term} (h : Reduces a b) :
    BetaReduces (toLam a) (toLam b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact betaReduces_trans (step_to_betaReduces hs) ih

theorem convS_to_convBeta {a b : Term} (h : ConvS a b) :
    ConvBeta (toLam a) (toLam b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact betaReduces_to_conv (step_to_betaReduces hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-! ## 6. Compatibility of `toLam` and `ConvBeta` with Substitutions -/

theorem toLam_subst (τ : Nat → Term) (t : Term) :
    toLam (FormalAlgebra.subst τ t) = substFClosed (fun v => toLam (τ v)) (toLam t) := by
  induction t with
  | s => rfl
  | var v => rfl
  | app a b iha ihb => simp only [FormalAlgebra.subst, toLam, substFClosed, iha, ihb]

theorem substFClosed_shift {σ : Nat → Lam} (hσ : ∀ v, bvarBound 0 (σ v) = true)
    (d c : Nat) (t : Lam) :
    substFClosed σ (shift d c t) = shift d c (substFClosed σ t) := by
  induction t generalizing c with
  | bvar i =>
    simp only [shift, substFClosed]
    split <;> rfl
  | fvar v =>
    simp only [shift, substFClosed]
    exact (shift_of_bvarBound d (σ v) (hσ v) (Nat.zero_le c)).symm
  | lam m ih => simp only [shift, substFClosed, ih (c + 1)]
  | app m n ihm ihn => simp only [shift, substFClosed, ihm c, ihn c]

theorem substFClosed_substB {σ : Nat → Lam} (hσ : ∀ v, bvarBound 0 (σ v) = true)
    (k : Nat) (u t : Lam) :
    substFClosed σ (substB k u t) = substB k (substFClosed σ u) (substFClosed σ t) := by
  induction t generalizing k with
  | bvar i =>
    simp only [substB, substFClosed]
    split
    · rfl
    · split
      · exact substFClosed_shift hσ k 0 u
      · rfl
  | fvar v =>
    simp only [substB, substFClosed]
    exact (substB_of_bvarBound (substFClosed σ u) (σ v) (hσ v) (Nat.zero_le k)).symm
  | lam m ih => simp only [substB, substFClosed, ih (k + 1)]
  | app m n ihm ihn => simp only [substB, substFClosed, ihm k, ihn k]

theorem substFClosed_betaStep {σ : Nat → Lam} (hσ : ∀ v, bvarBound 0 (σ v) = true)
    {a b : Lam} (h : BetaStep a b) :
    BetaStep (substFClosed σ a) (substFClosed σ b) := by
  induction h with
  | root m n =>
    simp only [substFClosed, substFClosed_substB hσ 0 n m]
    exact .root _ _
  | lam _ ih => exact .lam ih
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem substFClosed_convBeta {σ : Nat → Lam} (hσ : ∀ v, bvarBound 0 (σ v) = true)
    {a b : Lam} (h : ConvBeta a b) :
    ConvBeta (substFClosed σ a) (substFClosed σ b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact .step (substFClosed_betaStep hσ hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convBeta_subst_term (τ : Nat → Term) {u v : Term}
    (h : ConvBeta (toLam u) (toLam v)) :
    ConvBeta (toLam (FormalAlgebra.subst τ u)) (toLam (FormalAlgebra.subst τ v)) := by
  rw [toLam_subst, toLam_subst]
  exact substFClosed_convBeta (fun k => bvarBound_toLam (τ k)) h

end FormalQ32
