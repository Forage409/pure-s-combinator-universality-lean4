import formal_lambda_conjectures.lambda_base

/-!
# Weak-Head Standardization and Church's Conservation Theorem on `λI` (`WN_β ↔ SN_β`)

Constructive Lean 4.33.1 proofs (zero `Classical.choice`, zero `sorry`, zero `native_decide`) of:
1. **Weak-Head Standardization** (`wh_standardization_lam`, `wh_standardization_bvar`,
   `wh_standardization_fvar`, `wh_standardization_app`, `wh_standardization_apps_bvar`,
   `wh_standardization_apps_fvar`): derived via structural induction on Takahashi's `ParBeta`.
2. **Spine Head-Expansion Lemma** (`sn_head_expansion`) and Weak-Head `SN` Pullback on `λI`
   (`whStep_sn_pullback_lambdaI`).
3. **Church's Theorem for `λI`-Calculus (`lambdaI_wn_implies_sn`, `lambdaI_wn_iff_sn`)**:
   Every weakly normalizing `λI`-term is strongly normalizing (`HasBetaNF m ↔ StrongNormalizingBeta m`),
   proved constructively by strong induction on `lamSize nf` combined with Weak-Head Standardization.
4. **Variable-Application Preservation of `HasBetaNF`** (`hasBetaNF_app_fvar`).
-/

namespace FormalLambdaConjectures

/-! ## 1. Weak-Head `β`-Reduction (`WHStep`, `WHReduces`) and Spine Applications (`apps`) -/

inductive WHStep : Lam → Lam → Prop where
  | beta (b a : Lam) : WHStep ((.lam b) @@ a) (subst 0 a b)
  | appL {a a' : Lam} (b : Lam) : WHStep a a' → WHStep (a @@ b) (a' @@ b)

inductive WHReduces : Lam → Lam → Prop where
  | refl (a : Lam) : WHReduces a a
  | next {a b c : Lam} : WHStep a b → WHReduces b c → WHReduces a c

def apps : Lam → List Lam → Lam
  | h, [] => h
  | h, a :: as => apps (h @@ a) as

theorem apps_append (h : Lam) (xs ys : List Lam) :
    apps h (xs ++ ys) = apps (apps h xs) ys := by
  induction xs generalizing h with
  | nil => rfl
  | cons x rest ih => exact ih (h @@ x)

theorem lamSize_le_apps (h : Lam) (cs : List Lam) : lamSize h ≤ lamSize (apps h cs) := by
  induction cs generalizing h with
  | nil => exact Nat.le_refl _
  | cons c rest ih =>
    have h1 : lamSize h ≤ lamSize (h @@ c) := by
      simp only [lamSize]
      exact Nat.le_trans (Nat.le_add_right (lamSize h) (lamSize c)) (Nat.le_add_left _ 1)
    exact Nat.le_trans h1 (ih (h @@ c))

theorem whStep_to_betaStep {a b : Lam} (h : WHStep a b) : BetaStep a b := by
  induction h with
  | beta b a => exact .beta b a
  | appL _ _ ih => exact .appL ih

theorem whReduces_to_betaReduces {a b : Lam} (h : WHReduces a b) : BetaReduces a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (whStep_to_betaStep hs) ih

theorem whReduces_trans {a b c : Lam} (h1 : WHReduces a b) (h2 : WHReduces b c) :
    WHReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem whReduces_appL {a a' : Lam} (h : WHReduces a a') (b : Lam) :
    WHReduces (a @@ b) (a' @@ b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.appL b hs) ih

theorem whReduces_apps {a a' : Lam} (h : WHReduces a a') (cs : List Lam) :
    WHReduces (apps a cs) (apps a' cs) := by
  induction cs generalizing a a' with
  | nil => exact h
  | cons c rest ih => exact ih (whReduces_appL h c)

theorem whStep_subst_body (k : Nat) (s : Lam) {a b : Lam} (h : WHStep a b) :
    WHStep (subst k s a) (subst k s b) := by
  induction h generalizing k with
  | beta body arg =>
    simp only [subst]
    rw [subst0_subst k s arg body]
    exact .beta _ _
  | appL c _ ih =>
    exact .appL (subst k s c) (ih k)

theorem whReduces_subst_body (k : Nat) (s : Lam) {a b : Lam} (h : WHReduces a b) :
    WHReduces (subst k s a) (subst k s b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (whStep_subst_body k s hs) ih

/-! ## 2. Takahashi's One-Step `ParBeta` Factorization & Weak-Head Standardization -/

theorem parBeta_wh_bvar {m n : Lam} (h : ParBeta m n) :
    ∀ k, n = .bvar k → WHReduces m (.bvar k) := by
  induction h with
  | bvar j =>
    intro k hk; injection hk with heq; subst heq; exact .refl _
  | fvar _ => intro _ hk; cases hk
  | app _ _ => intro _ hk; cases hk
  | lam _ => intro _ hk; cases hk
  | @beta u u' w w' _ _ ihu ihw =>
    intro k hk
    cases u' with
    | fvar _ => cases hk
    | app _ _ => cases hk
    | lam _ => cases hk
    | bvar j =>
      cases j with
      | zero =>
        simp only [subst, if_neg (Nat.lt_irrefl 0), ↓reduceIte, shift_zero] at hk
        have hu0 : WHReduces u (.bvar 0) := ihu 0 rfl
        have hsub : WHReduces (subst 0 w u) w := by
          have h1 := whReduces_subst_body 0 w hu0
          simpa [subst, shift_zero] using h1
        exact .next (.beta u w) (whReduces_trans hsub (ihw k hk))
      | succ j0 =>
        have hnotlt : ¬ (j0 + 1 < 0) := Nat.not_lt_zero _
        have hne : ¬ (j0 + 1 = 0) := Nat.succ_ne_zero j0
        simp only [subst, if_neg hnotlt, if_neg hne, Nat.add_sub_cancel] at hk
        injection hk with heq
        subst heq
        have hu1 : WHReduces u (.bvar (j0 + 1)) := ihu (j0 + 1) rfl
        have hsub : WHReduces (subst 0 w u) (.bvar j0) := by
          have h1 := whReduces_subst_body 0 w hu1
          simpa [subst, if_neg hnotlt, if_neg hne] using h1
        exact .next (.beta u w) hsub

theorem parBeta_wh_fvar {m n : Lam} (h : ParBeta m n) :
    ∀ v, n = .fvar v → WHReduces m (.fvar v) := by
  induction h with
  | bvar _ => intro _ hv; cases hv
  | fvar u => intro v hv; injection hv with heq; subst heq; exact .refl _
  | app _ _ => intro _ hv; cases hv
  | lam _ => intro _ hv; cases hv
  | @beta u u' w w' hu _ ihu ihw =>
    intro v hv
    cases u' with
    | app _ _ => cases hv
    | lam _ => cases hv
    | fvar u0 =>
      simp only [subst] at hv
      have hu0 : WHReduces u (.fvar v) := ihu v hv
      have hsub : WHReduces (subst 0 w u) (.fvar v) := by
        simpa [subst] using whReduces_subst_body 0 w hu0
      exact .next (.beta u w) hsub
    | bvar j =>
      cases j with
      | zero =>
        simp only [subst, if_neg (Nat.lt_irrefl 0), ↓reduceIte, shift_zero] at hv
        have hu0 : WHReduces u (.bvar 0) := parBeta_wh_bvar hu 0 rfl
        have hsub : WHReduces (subst 0 w u) w := by
          simpa [subst, shift_zero] using whReduces_subst_body 0 w hu0
        exact .next (.beta u w) (whReduces_trans hsub (ihw v hv))
      | succ j0 =>
        have hnotlt : ¬ (j0 + 1 < 0) := Nat.not_lt_zero _
        have hne : ¬ (j0 + 1 = 0) := Nat.succ_ne_zero j0
        simp only [subst, if_neg hnotlt, if_neg hne] at hv
        cases hv

theorem parBeta_wh_lam {m n : Lam} (h : ParBeta m n) :
    ∀ p', n = .lam p' → ∃ b, WHReduces m (.lam b) ∧ ParBeta b p' := by
  induction h with
  | bvar _ => intro _ hp; cases hp
  | fvar _ => intro _ hp; cases hp
  | app _ _ => intro _ hp; cases hp
  | @lam b b' hb _ =>
    intro p' hp
    injection hp with heq
    subst heq
    exact ⟨b, .refl _, hb⟩
  | @beta u u' w w' hu hw ihu ihw =>
    intro p' hp
    cases u' with
    | fvar _ => cases hp
    | app _ _ => cases hp
    | lam body' =>
      simp only [subst] at hp
      injection hp with heq
      subst heq
      obtain ⟨body₀, hu_wh, hbody_par⟩ := ihu body' rfl
      have hsub : WHReduces (subst 0 w u) (.lam (subst 1 w body₀)) := by
        simpa [subst] using whReduces_subst_body 0 w hu_wh
      exact ⟨subst 1 w body₀, .next (.beta u w) hsub, parBeta_subst 1 hw hbody_par⟩
    | bvar j =>
      cases j with
      | zero =>
        simp only [subst, if_neg (Nat.lt_irrefl 0), ↓reduceIte, shift_zero] at hp
        have hu0 : WHReduces u (.bvar 0) := parBeta_wh_bvar hu 0 rfl
        have hsub : WHReduces (subst 0 w u) w := by
          simpa [subst, shift_zero] using whReduces_subst_body 0 w hu0
        obtain ⟨q₀, hw_wh, hq_par⟩ := ihw p' hp
        exact ⟨q₀, .next (.beta u w) (whReduces_trans hsub hw_wh), hq_par⟩
      | succ j0 =>
        have hnotlt : ¬ (j0 + 1 < 0) := Nat.not_lt_zero _
        have hne : ¬ (j0 + 1 = 0) := Nat.succ_ne_zero j0
        simp only [subst, if_neg hnotlt, if_neg hne] at hp
        cases hp

theorem parBeta_wh_app {m n : Lam} (h : ParBeta m n) :
    ∀ a' b', n = a' @@ b' → ∃ a₀ b₀, WHReduces m (a₀ @@ b₀) ∧ ParBeta a₀ a' ∧ ParBeta b₀ b' := by
  induction h with
  | bvar _ => intro _ _ hn; cases hn
  | fvar _ => intro _ _ hn; cases hn
  | lam _ => intro _ _ hn; cases hn
  | @app a a₁ b b₁ ha hb _ _ =>
    intro a' b' hn
    injection hn with ha' hb'
    subst ha'; subst hb'
    exact ⟨a, b, .refl _, ha, hb⟩
  | @beta u u' w w' hu hw ihu ihw =>
    intro a' b' hn
    cases u' with
    | fvar _ => cases hn
    | lam _ => cases hn
    | app u₁' u₂' =>
      simp only [subst] at hn
      injection hn with ha' hb'
      subst ha'; subst hb'
      obtain ⟨u₁₀, u₂₀, hu_wh, hp1, hp2⟩ := ihu u₁' u₂' rfl
      have hsub : WHReduces (subst 0 w u) (subst 0 w u₁₀ @@ subst 0 w u₂₀) := by
        simpa [subst] using whReduces_subst_body 0 w hu_wh
      exact ⟨subst 0 w u₁₀, subst 0 w u₂₀, .next (.beta u w) hsub,
        parBeta_subst 0 hw hp1, parBeta_subst 0 hw hp2⟩
    | bvar j =>
      cases j with
      | zero =>
        simp only [subst, if_neg (Nat.lt_irrefl 0), ↓reduceIte, shift_zero] at hn
        have hu0 : WHReduces u (.bvar 0) := parBeta_wh_bvar hu 0 rfl
        have hsub : WHReduces (subst 0 w u) w := by
          simpa [subst, shift_zero] using whReduces_subst_body 0 w hu0
        obtain ⟨a₀, b₀, hw_wh, hp1, hp2⟩ := ihw a' b' hn
        exact ⟨a₀, b₀, .next (.beta u w) (whReduces_trans hsub hw_wh), hp1, hp2⟩
      | succ j0 =>
        have hnotlt : ¬ (j0 + 1 < 0) := Nat.not_lt_zero _
        have hne : ¬ (j0 + 1 = 0) := Nat.succ_ne_zero j0
        simp only [subst, if_neg hnotlt, if_neg hne] at hn
        cases hn

/-- Postponement of `ParBeta` across a single `WHStep`. -/
theorem parBeta_whStep_postpone {m m₁ m₂ : Lam}
    (hpar : ParBeta m m₁) (hwh : WHStep m₁ m₂) :
    ∃ m₀, WHReduces m m₀ ∧ ParBeta m₀ m₂ := by
  induction hwh generalizing m with
  | beta p' q' =>
    obtain ⟨a₀, b₀, hm_wh, ha_par, hb_par⟩ := parBeta_wh_app hpar (.lam p') q' rfl
    obtain ⟨p₀, ha_wh, hp_par⟩ := parBeta_wh_lam ha_par p' rfl
    have hchain : WHReduces m (subst 0 b₀ p₀) :=
      whReduces_trans hm_wh
        (whReduces_trans (whReduces_appL ha_wh b₀) (.next (.beta p₀ b₀) (.refl _)))
    exact ⟨subst 0 b₀ p₀, hchain, parBeta_subst 0 hb_par hp_par⟩
  | @appL l' l₂ r' _ ih =>
    obtain ⟨a₀, b₀, hm_wh, ha_par, hb_par⟩ := parBeta_wh_app hpar l' r' rfl
    obtain ⟨l₀, ha_wh, hl_par⟩ := ih ha_par
    exact ⟨l₀ @@ b₀, whReduces_trans hm_wh (whReduces_appL ha_wh b₀), .app hl_par hb_par⟩

theorem parBeta_whReduces_postpone {m m₁ m₂ : Lam}
    (hpar : ParBeta m m₁) (hwh : WHReduces m₁ m₂) :
    ∃ m₀, WHReduces m m₀ ∧ ParBeta m₀ m₂ := by
  induction hwh generalizing m with
  | refl _ => exact ⟨m, .refl m, hpar⟩
  | next hs _ ih =>
    obtain ⟨w, hmw, hwp⟩ := parBeta_whStep_postpone hpar hs
    obtain ⟨m₀, hwm₀, hp₀⟩ := ih hwp
    exact ⟨m₀, whReduces_trans hmw hwm₀, hp₀⟩

/-- **Weak-Head Standardization for Abstractions**:
    If `m →_β* λp`, then weak-head reduction alone reaches an abstraction `λb` with `b →_β* p`. -/
theorem wh_standardization_lam {m p : Lam} (h : BetaReduces m (.lam p)) :
    ∃ b, WHReduces m (.lam b) ∧ BetaReduces b p := by
  have hps := betaReduces_to_parBetaStar h
  suffices hgen : ∀ {x y : Lam}, ParBetaStar x y → ∀ p, y = .lam p →
      ∃ b, WHReduces x (.lam b) ∧ ParBetaStar b p by
    obtain ⟨b, hwh, hbs⟩ := hgen hps p rfl
    exact ⟨b, hwh, parBetaStar_to_betaReduces hbs⟩
  intro x y hxy
  induction hxy with
  | refl _ =>
    intro p0 hp0; subst hp0; exact ⟨p0, .refl _, .refl _⟩
  | next h1 _ ih =>
    intro p0 hp0
    obtain ⟨b₁, hwh1, hbs1⟩ := ih p0 hp0
    obtain ⟨m₀, hwh0, hpar0⟩ := parBeta_whReduces_postpone h1 hwh1
    obtain ⟨b₀, hwh_lam, hpar_b⟩ := parBeta_wh_lam hpar0 b₁ rfl
    exact ⟨b₀, whReduces_trans hwh0 hwh_lam, .next hpar_b hbs1⟩

theorem wh_standardization_bvar {m : Lam} {k : Nat} (h : BetaReduces m (.bvar k)) :
    WHReduces m (.bvar k) := by
  have hps := betaReduces_to_parBetaStar h
  suffices hgen : ∀ {x y : Lam}, ParBetaStar x y → y = .bvar k → WHReduces x (.bvar k) from
    hgen hps rfl
  intro x y hxy
  induction hxy with
  | refl _ => intro hy; subst hy; exact .refl _
  | next h1 _ ih =>
    intro hy
    obtain ⟨m₀, hwh0, hpar0⟩ := parBeta_whReduces_postpone h1 (ih hy)
    exact whReduces_trans hwh0 (parBeta_wh_bvar hpar0 k rfl)

theorem wh_standardization_fvar {m : Lam} {v : Nat} (h : BetaReduces m (.fvar v)) :
    WHReduces m (.fvar v) := by
  have hps := betaReduces_to_parBetaStar h
  suffices hgen : ∀ {x y : Lam}, ParBetaStar x y → y = .fvar v → WHReduces x (.fvar v) from
    hgen hps rfl
  intro x y hxy
  induction hxy with
  | refl _ => intro hy; subst hy; exact .refl _
  | next h1 _ ih =>
    intro hy
    obtain ⟨m₀, hwh0, hpar0⟩ := parBeta_whReduces_postpone h1 (ih hy)
    exact whReduces_trans hwh0 (parBeta_wh_fvar hpar0 v rfl)

theorem wh_standardization_app {m a' b' : Lam} (h : BetaReduces m (a' @@ b')) :
    ∃ a₀ b₀, WHReduces m (a₀ @@ b₀) ∧ BetaReduces a₀ a' ∧ BetaReduces b₀ b' := by
  have hps := betaReduces_to_parBetaStar h
  suffices hgen : ∀ {x y : Lam}, ParBetaStar x y → ∀ a' b', y = a' @@ b' →
      ∃ a₀ b₀, WHReduces x (a₀ @@ b₀) ∧ ParBetaStar a₀ a' ∧ ParBetaStar b₀ b' by
    obtain ⟨a₀, b₀, hwh, ha, hb⟩ := hgen hps a' b' rfl
    exact ⟨a₀, b₀, hwh, parBetaStar_to_betaReduces ha, parBetaStar_to_betaReduces hb⟩
  intro x y hxy
  induction hxy with
  | refl _ =>
    intro a' b' hy; subst hy; exact ⟨a', b', .refl _, .refl _, .refl _⟩
  | next h1 _ ih =>
    intro a' b' hy
    obtain ⟨a₁, b₁, hwh1, ha1, hb1⟩ := ih a' b' hy
    obtain ⟨m₀, hwh0, hpar0⟩ := parBeta_whReduces_postpone h1 hwh1
    obtain ⟨a₀, b₀, hwh_app, ha0, hb0⟩ := parBeta_wh_app hpar0 a₁ b₁ rfl
    exact ⟨a₀, b₀, whReduces_trans hwh0 hwh_app, .next ha0 ha1, .next hb0 hb1⟩

/-- Pairwise relation on argument lists (`Prop`-valued). -/
inductive Forall2Lam (R : Lam → Lam → Prop) : List Lam → List Lam → Prop where
  | nil : Forall2Lam R [] []
  | cons {x y : Lam} {xs ys : List Lam} :
      R x y → Forall2Lam R xs ys → Forall2Lam R (x :: xs) (y :: ys)

theorem forall2Lam_append {R : Lam → Lam → Prop} {xs₁ ys₁ xs₂ ys₂ : List Lam}
    (h1 : Forall2Lam R xs₁ ys₁) (h2 : Forall2Lam R xs₂ ys₂) :
    Forall2Lam R (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction h1 with
  | nil => exact h2
  | cons hr _ ih => exact .cons hr ih

private theorem list_rev_ind (P : List Lam → Prop) (hnil : P [])
    (hsnoc : ∀ xs x, P xs → P (xs ++ [x])) (l : List Lam) : P l := by
  suffices h : ∀ (r : List Lam), P r.reverse by simpa [List.reverse_reverse] using h l.reverse
  intro r
  induction r with
  | nil => exact hnil
  | cons x xs ih => simpa [List.reverse_cons] using hsnoc xs.reverse x ih

theorem wh_standardization_apps_bvar {k : Nat} (cs' : List Lam) :
    ∀ {m : Lam}, BetaReduces m (apps (.bvar k) cs') →
      ∃ cs₀, WHReduces m (apps (.bvar k) cs₀) ∧ Forall2Lam BetaReduces cs₀ cs' := by
  refine list_rev_ind
    (fun cs' => ∀ {m : Lam}, BetaReduces m (apps (.bvar k) cs') →
      ∃ cs₀, WHReduces m (apps (.bvar k) cs₀) ∧ Forall2Lam BetaReduces cs₀ cs') ?_ ?_ cs'
  · intro m hm
    exact ⟨[], wh_standardization_bvar hm, .nil⟩
  · intro init' last' ih m hm
    rw [apps_append] at hm
    simp only [apps] at hm
    obtain ⟨a₀, b₀, hwh_ab, ha_red, hb_red⟩ := wh_standardization_app hm
    obtain ⟨init₀, hwh_init, hfor_init⟩ := ih ha_red
    have htot : WHReduces m (apps (.bvar k) (init₀ ++ [b₀])) := by
      rw [apps_append]
      exact whReduces_trans hwh_ab (whReduces_appL hwh_init b₀)
    exact ⟨init₀ ++ [b₀], htot, forall2Lam_append hfor_init (.cons hb_red .nil)⟩

theorem wh_standardization_apps_fvar {v : Nat} (cs' : List Lam) :
    ∀ {m : Lam}, BetaReduces m (apps (.fvar v) cs') →
      ∃ cs₀, WHReduces m (apps (.fvar v) cs₀) ∧ Forall2Lam BetaReduces cs₀ cs' := by
  refine list_rev_ind
    (fun cs' => ∀ {m : Lam}, BetaReduces m (apps (.fvar v) cs') →
      ∃ cs₀, WHReduces m (apps (.fvar v) cs₀) ∧ Forall2Lam BetaReduces cs₀ cs') ?_ ?_ cs'
  · intro m hm
    exact ⟨[], wh_standardization_fvar hm, .nil⟩
  · intro init' last' ih m hm
    rw [apps_append] at hm
    simp only [apps] at hm
    obtain ⟨a₀, b₀, hwh_ab, ha_red, hb_red⟩ := wh_standardization_app hm
    obtain ⟨init₀, hwh_init, hfor_init⟩ := ih ha_red
    have htot : WHReduces m (apps (.fvar v) (init₀ ++ [b₀])) := by
      rw [apps_append]
      exact whReduces_trans hwh_ab (whReduces_appL hwh_init b₀)
    exact ⟨init₀ ++ [b₀], htot, forall2Lam_append hfor_init (.cons hb_red .nil)⟩

/-! ## 3. Strong Normalization Structural Lemmas & Head-Expansion on `λI` -/

theorem sn_reduces {a b : Lam} (ha : StrongNormalizingBeta a) (hred : BetaReduces a b) :
    StrongNormalizingBeta b := by
  induction hred with
  | refl _ => exact ha
  | next hs _ ih => exact ih (Acc.inv ha hs)

theorem sn_lam {b : Lam} (hb : StrongNormalizingBeta b) : StrongNormalizingBeta (.lam b) := by
  induction hb with
  | intro b _ ih =>
    refine Acc.intro (Lam.lam b) (fun y hy => ?_)
    cases hy with
    | lam hs => exact ih _ hs

theorem sn_of_lam {b : Lam} (h : StrongNormalizingBeta (.lam b)) : StrongNormalizingBeta b := by
  suffices hgen : ∀ x, StrongNormalizingBeta x → ∀ b, x = .lam b → StrongNormalizingBeta b from
    hgen (.lam b) h b rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    intro b hxb
    subst hxb
    exact Acc.intro b (fun b' hs => ih (.lam b') (BetaStep.lam hs) b' rfl)

theorem sn_of_appL {a b : Lam} (h : StrongNormalizingBeta (a @@ b)) : StrongNormalizingBeta a := by
  suffices hgen : ∀ x, StrongNormalizingBeta x → ∀ a b, x = a @@ b → StrongNormalizingBeta a from
    hgen (a @@ b) h a b rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    intro a b hxab
    subst hxab
    exact Acc.intro a (fun a' hs => ih (a' @@ b) (.appL hs) a' b rfl)

theorem sn_of_appR {a b : Lam} (h : StrongNormalizingBeta (a @@ b)) : StrongNormalizingBeta b := by
  suffices hgen : ∀ x, StrongNormalizingBeta x → ∀ a b, x = a @@ b → StrongNormalizingBeta b from
    hgen (a @@ b) h a b rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    intro a b hxab
    subst hxab
    exact Acc.intro b (fun b' hs => ih (a @@ b') (.appR hs) a b' rfl)

theorem sn_of_shift {d c : Nat} {a : Lam} (h : StrongNormalizingBeta (shift d c a)) :
    StrongNormalizingBeta a := by
  suffices hgen : ∀ x, StrongNormalizingBeta x → ∀ a, x = shift d c a → StrongNormalizingBeta a from
    hgen (shift d c a) h a rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    intro a hxa
    subst hxa
    exact Acc.intro a (fun a' hs => ih (shift d c a') (betaStep_shift d c hs) a' rfl)

theorem sn_of_subst_body {k : Nat} {s m : Lam} (h : StrongNormalizingBeta (subst k s m)) :
    StrongNormalizingBeta m := by
  suffices hgen : ∀ x, StrongNormalizingBeta x → ∀ m, x = subst k s m → StrongNormalizingBeta m from
    hgen (subst k s m) h m rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    intro m hxm
    subst hxm
    exact Acc.intro m (fun m' hs => ih (subst k s m') (betaStep_subst_body k s hs) m' rfl)

theorem sn_of_subst_arg_occurs {k : Nat} {s m : Lam}
    (hocc : occursBVar k m = true) (hsn : StrongNormalizingBeta (subst k s m)) :
    StrongNormalizingBeta s := by
  induction m generalizing k with
  | bvar j =>
    simp only [occursBVar, decide_eq_true_eq] at hocc
    subst hocc
    simp only [subst, if_neg (Nat.lt_irrefl j), ↓reduceIte] at hsn
    exact sn_of_shift hsn
  | fvar _ => cases hocc
  | app m₁ m₂ ih₁ ih₂ =>
    simp only [occursBVar, Bool.or_eq_true] at hocc
    simp only [subst] at hsn
    rcases hocc with h1 | h2
    · exact ih₁ h1 (sn_of_appL hsn)
    · exact ih₂ h2 (sn_of_appR hsn)
  | lam body ih =>
    simp only [occursBVar] at hocc
    simp only [subst] at hsn
    exact ih hocc (sn_of_lam hsn)

/-- Single-step reduction on an argument list `List Lam`. -/
inductive ListBetaStep : List Lam → List Lam → Prop where
  | head {c c' : Lam} (cs : List Lam) : BetaStep c c' → ListBetaStep (c :: cs) (c' :: cs)
  | tail (c : Lam) {cs cs' : List Lam} : ListBetaStep cs cs' → ListBetaStep (c :: cs) (c :: cs')

abbrev SNList (cs : List Lam) : Prop := Acc (fun ys xs => ListBetaStep xs ys) cs

theorem snList_nil : SNList [] :=
  Acc.intro [] (fun _ hs => by cases hs)

theorem snList_cons {c : Lam} {cs : List Lam}
    (hc : StrongNormalizingBeta c) (hcs : SNList cs) : SNList (c :: cs) := by
  induction hc generalizing cs with
  | intro c _ ihc =>
    induction hcs with
    | intro cs hcs_inv ihcs =>
      refine Acc.intro (c :: cs) (fun ys hstep => ?_)
      cases hstep with
      | head _ hs_c => exact ihc _ hs_c (Acc.intro cs hcs_inv)
      | tail _ hs_cs => exact ihcs _ hs_cs

theorem betaStep_apps_of_left {f f' : Lam} (hf : BetaStep f f') (cs : List Lam) :
    BetaStep (apps f cs) (apps f' cs) := by
  induction cs generalizing f f' with
  | nil => exact hf
  | cons c rest ih => exact ih (.appL hf)

theorem betaStep_apps_of_list (f : Lam) {cs cs' : List Lam} (hcs : ListBetaStep cs cs') :
    BetaStep (apps f cs) (apps f cs') := by
  induction hcs generalizing f with
  | head rest hc => exact betaStep_apps_of_left (.appR hc) rest
  | tail c _ ih => exact ih (f @@ c)

theorem betaReduces_apps_of_left {f f' : Lam} (hf : BetaReduces f f') (cs : List Lam) :
    BetaReduces (apps f cs) (apps f' cs) := by
  induction hf with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (betaStep_apps_of_left hs cs) ih

theorem sn_of_apps (f : Lam) (cs : List Lam) (h : StrongNormalizingBeta (apps f cs)) :
    StrongNormalizingBeta f ∧ SNList cs := by
  induction cs generalizing f with
  | nil => exact ⟨h, snList_nil⟩
  | cons c rest ih =>
    obtain ⟨hfc, hrest⟩ := ih (f @@ c) h
    exact ⟨sn_of_appL hfc, snList_cons (sn_of_appR hfc) hrest⟩

/-- Inversion of `BetaStep (apps f cs) y` when `f` is NOT a `λ`-abstraction. -/
theorem betaStep_apps_non_lam_inv (f : Lam) (hnot : ∀ p, f ≠ .lam p) (cs : List Lam) {y : Lam}
    (hs : BetaStep (apps f cs) y) :
    (∃ f', BetaStep f f' ∧ y = apps f' cs) ∨
    (∃ cs', ListBetaStep cs cs' ∧ y = apps f cs') := by
  induction cs generalizing f with
  | nil =>
    exact Or.inl ⟨y, hs, rfl⟩
  | cons c rest ih =>
    have hnot_app : ∀ p, (f @@ c) ≠ .lam p := fun _ hp => by cases hp
    rcases ih (f @@ c) hnot_app hs with ⟨g, hfg, hy⟩ | ⟨rest', hrest, hy⟩
    · cases hfg with
      | beta p _ => exfalso; exact hnot p rfl
      | appL hf => exact Or.inl ⟨_, hf, hy⟩
      | appR hc => exact Or.inr ⟨_ :: rest, .head rest hc, hy⟩
    · exact Or.inr ⟨c :: rest', .tail c hrest, hy⟩

theorem sn_apps_var_head (f : Lam) (hvar : (∃ k, f = .bvar k) ∨ (∃ v, f = .fvar v))
    {cs : List Lam} (hcs : SNList cs) : StrongNormalizingBeta (apps f cs) := by
  have hnot : ∀ p, f ≠ .lam p := by
    intro p hp
    rcases hvar with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases hp
  have hnostep : ∀ f', ¬ BetaStep f f' := by
    intro f' hf
    rcases hvar with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases hf
  induction hcs with
  | intro cs _ ih =>
    refine Acc.intro (apps f cs) (fun y hy => ?_)
    rcases betaStep_apps_non_lam_inv f hnot cs hy with ⟨f', hf', _⟩ | ⟨cs', hcs', rfl⟩
    · exfalso; exact hnostep f' hf'
    · exact ih cs' hcs'

/-- **Head-Expansion Lemma for `SN` (`BetaStep`)**:
    If `b`, `a`, `cs`, and `apps (subst 0 a b) cs` are all strongly normalizing,
    then `apps ((.lam b) @@ a) cs` is strongly normalizing. -/
theorem sn_head_expansion {b : Lam} (hb : StrongNormalizingBeta b) :
    ∀ {a : Lam}, StrongNormalizingBeta a →
      ∀ {cs : List Lam}, SNList cs →
        StrongNormalizingBeta (apps (subst 0 a b) cs) →
        StrongNormalizingBeta (apps ((.lam b) @@ a) cs) := by
  induction hb with
  | intro b _ ihb =>
    intro a ha
    induction ha with
    | intro a ha_inv iha =>
      intro cs hcs
      induction hcs with
      | intro cs hcs_inv ihcs =>
        intro hsub_sn
        refine Acc.intro (apps ((.lam b) @@ a) cs) (fun y hy => ?_)
        have hnot : ∀ p, ((.lam b) @@ a) ≠ .lam p := fun _ hp => by cases hp
        rcases betaStep_apps_non_lam_inv ((.lam b) @@ a) hnot cs hy with
          ⟨f', hf', rfl⟩ | ⟨cs', hcs', rfl⟩
        · cases hf' with
          | beta _ _ => exact hsub_sn
          | appL hlam =>
            cases hlam with
            | @lam _ b' hb' =>
              have hstep_sub : BetaStep (apps (subst 0 a b) cs) (apps (subst 0 a b') cs) :=
                betaStep_apps_of_left (betaStep_subst_body 0 a hb') cs
              exact ihb b' hb' (Acc.intro a ha_inv) (Acc.intro cs hcs_inv)
                (Acc.inv hsub_sn hstep_sub)
          | @appR _ _ a' ha' =>
            have hred_sub : BetaReduces (apps (subst 0 a b) cs) (apps (subst 0 a' b) cs) :=
              betaReduces_apps_of_left
                (betaReduces_subst_arg 0 (.next ha' (.refl _)) b) cs
            exact iha a' ha' (Acc.intro cs hcs_inv) (sn_reduces hsub_sn hred_sub)
        · have hstep_sub : BetaStep (apps (subst 0 a b) cs) (apps (subst 0 a b) cs') :=
            betaStep_apps_of_list (subst 0 a b) hcs'
          exact ihcs cs' hcs' (Acc.inv hsub_sn hstep_sub)

theorem whStep_eq_apps {x y : Lam} (h : WHStep x y) :
    ∃ b a cs, x = apps ((.lam b) @@ a) cs ∧ y = apps (subst 0 a b) cs := by
  induction h with
  | beta b a => exact ⟨b, a, [], rfl, rfl⟩
  | @appL l l' r _ ih =>
    obtain ⟨b, a, cs, hl, hl'⟩ := ih
    refine ⟨b, a, cs ++ [r], ?_, ?_⟩
    · rw [apps_append, ← hl]; rfl
    · rw [apps_append, ← hl']; rfl

theorem isLambdaI_of_apps_head (f : Lam) (cs : List Lam)
    (hi : isLambdaI (apps f cs) = true) : isLambdaI f = true := by
  induction cs generalizing f with
  | nil => exact hi
  | cons c rest ih =>
    have hfc := ih (f @@ c) hi
    simp only [isLambdaI, Bool.and_eq_true] at hfc
    exact hfc.1

theorem isLambdaI_apps_args (f : Lam) (cs : List Lam)
    (hi : isLambdaI (apps f cs) = true) : ∀ c ∈ cs, isLambdaI c = true := by
  induction cs generalizing f with
  | nil => intro _ hmem; cases hmem
  | cons c rest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with hdc | hrest
    · subst hdc
      have hfc := isLambdaI_of_apps_head (f @@ d) rest hi
      simp only [isLambdaI, Bool.and_eq_true] at hfc
      exact hfc.2
    · exact ih (f @@ c) hi d hrest

/-- Weak-Head `SN` Pullback on `λI`: if `x` is a `λI`-term, `x →_wh y`, and `y` is `SN`, then `x` is `SN`. -/
theorem whStep_sn_pullback_lambdaI {x y : Lam}
    (hi : isLambdaI x = true) (hwh : WHStep x y) (hsn : StrongNormalizingBeta y) :
    StrongNormalizingBeta x := by
  obtain ⟨b, a, cs, rfl, rfl⟩ := whStep_eq_apps hwh
  obtain ⟨hsub_sn, hcs_sn⟩ := sn_of_apps (subst 0 a b) cs hsn
  have hb_sn : StrongNormalizingBeta b := sn_of_subst_body hsub_sn
  have hhead_i := isLambdaI_of_apps_head ((.lam b) @@ a) cs hi
  simp only [isLambdaI, Bool.and_eq_true] at hhead_i
  have hocc0 : occursBVar 0 b = true := hhead_i.1.1
  have ha_sn : StrongNormalizingBeta a := sn_of_subst_arg_occurs hocc0 hsub_sn
  exact sn_head_expansion hb_sn ha_sn hcs_sn hsn

theorem whReduces_sn_pullback_lambdaI {x y : Lam}
    (hi : isLambdaI x = true) (hwh : WHReduces x y) (hsn : StrongNormalizingBeta y) :
    StrongNormalizingBeta x := by
  induction hwh with
  | refl _ => exact hsn
  | next hs _ ih =>
    have hi' : isLambdaI _ = true := isLambdaI_betaStep (whStep_to_betaStep hs) hi
    exact whStep_sn_pullback_lambdaI hi hs (ih hi' hsn)

/-! ## 4. Spine Decomposition of `IsBetaNF` and Church's Theorem on `λI` (`WN_β ↔ SN_β`) -/

theorem spine_decomp (m : Lam) :
    (∃ b, m = .lam b) ∨
    (∃ k cs, m = apps (.bvar k) cs) ∨
    (∃ v cs, m = apps (.fvar v) cs) ∨
    (∃ b a cs, m = apps ((.lam b) @@ a) cs) := by
  induction m with
  | bvar k => exact Or.inr (Or.inl ⟨k, [], rfl⟩)
  | fvar v => exact Or.inr (Or.inr (Or.inl ⟨v, [], rfl⟩))
  | lam b => exact Or.inl ⟨b, rfl⟩
  | app p q ihp _ =>
    rcases ihp with ⟨b, rfl⟩ | ⟨k, cs, rfl⟩ | ⟨v, cs, rfl⟩ | ⟨b, a, cs, rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨b, q, [], rfl⟩))
    · refine Or.inr (Or.inl ⟨k, cs ++ [q], ?_⟩)
      rw [apps_append]; rfl
    · refine Or.inr (Or.inr (Or.inl ⟨v, cs ++ [q], ?_⟩))
      rw [apps_append]; rfl
    · refine Or.inr (Or.inr (Or.inr ⟨b, a, cs ++ [q], ?_⟩))
      rw [apps_append]; rfl

theorem isBetaNF_of_lam {b : Lam} (h : IsBetaNF (.lam b)) : IsBetaNF b :=
  fun b' hs => h (.lam b') (BetaStep.lam hs)

theorem isBetaNF_apps_args (f : Lam) (cs : List Lam) (hnf : IsBetaNF (apps f cs)) :
    ∀ c ∈ cs, IsBetaNF c ∧ lamSize c < lamSize (apps f cs) := by
  induction cs generalizing f with
  | nil => intro _ hmem; cases hmem
  | cons c rest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with hdc | hrest
    · subst hdc
      refine ⟨fun c' hc' => hnf _ (betaStep_apps_of_left (.appR hc') rest), ?_⟩
      have hlt : lamSize d < lamSize (f @@ d) := by
        simp only [lamSize]
        have h1 : lamSize d ≤ lamSize f + lamSize d := Nat.le_add_left _ _
        exact Nat.lt_of_le_of_lt h1 (Nat.lt_add_of_pos_left (by decide : 0 < 1))
      exact Nat.lt_of_lt_of_le hlt (lamSize_le_apps (f @@ d) rest)
    · exact ih (f @@ c) hnf d hrest

private theorem snList_of_forall2 {cs₀ cs' : List Lam}
    (hf2 : Forall2Lam BetaReduces cs₀ cs')
    (hi0 : ∀ c ∈ cs₀, isLambdaI c = true)
    (hrec : ∀ c₀ c', c' ∈ cs' → isLambdaI c₀ = true → BetaReduces c₀ c' → StrongNormalizingBeta c₀) :
    SNList cs₀ := by
  induction hf2 with
  | nil => exact snList_nil
  | @cons x y xs ys hxy _ ih =>
    have hx_sn : StrongNormalizingBeta x :=
      hrec x y List.mem_cons_self (hi0 x List.mem_cons_self) hxy
    have hxs_sn : SNList xs :=
      ih (fun c hc => hi0 c (List.mem_cons_of_mem x hc))
         (fun c₀ c' hc' => hrec c₀ c' (List.mem_cons_of_mem y hc'))
    exact snList_cons hx_sn hxs_sn

/-- **Church's Conservation Theorem for `λI`-Calculus (`WN_β → SN_β`)**:
    Every `λI`-term `m` that reduces to a `β`-normal form is strongly normalizing! -/
theorem lambdaI_wn_implies_sn {m : Lam} (hi : isLambdaI m = true) (hwn : HasBetaNF m) :
    StrongNormalizingBeta m := by
  obtain ⟨nf, hred, hnf⟩ := hwn
  suffices hmain : ∀ (sz : Nat) (nf : Lam), lamSize nf ≤ sz → IsBetaNF nf →
      ∀ (m : Lam), isLambdaI m = true → BetaReduces m nf → StrongNormalizingBeta m from
    hmain (lamSize nf) nf (Nat.le_refl _) hnf m hi hred
  intro sz
  induction sz with
  | zero =>
    intro nf hle _ _ _ _
    exfalso
    exact Nat.not_le_of_lt (lamSize_pos nf) hle
  | succ sz ih =>
    intro nf hle hnf m hi hm_nf
    rcases spine_decomp nf with ⟨p', rfl⟩ | ⟨k, cs', rfl⟩ | ⟨v, cs', rfl⟩ | ⟨b, a, cs', rfl⟩
    · -- Case 1: `nf = .lam p'`
      obtain ⟨b₀, hwh, hb_red⟩ := wh_standardization_lam hm_nf
      have hi_lam : isLambdaI (.lam b₀) = true :=
        isLambdaI_betaReduces (whReduces_to_betaReduces hwh) hi
      simp only [isLambdaI, Bool.and_eq_true] at hi_lam
      have hsz_p : lamSize p' ≤ sz := Nat.le_of_succ_le_succ (by simpa [lamSize, Nat.add_comm] using hle)
      have hb_sn : StrongNormalizingBeta b₀ :=
        ih p' hsz_p (isBetaNF_of_lam hnf) b₀ hi_lam.2 hb_red
      exact whReduces_sn_pullback_lambdaI hi hwh (sn_lam hb_sn)
    · -- Case 2: `nf = apps (.bvar k) cs'`
      obtain ⟨cs₀, hwh, hf2⟩ := wh_standardization_apps_bvar cs' hm_nf
      have hi_apps : isLambdaI (apps (.bvar k) cs₀) = true :=
        isLambdaI_betaReduces (whReduces_to_betaReduces hwh) hi
      have hargs_nf := isBetaNF_apps_args (.bvar k) cs' hnf
      have hcs_sn : SNList cs₀ := snList_of_forall2 hf2
        (isLambdaI_apps_args (.bvar k) cs₀ hi_apps)
        (fun c₀ c' hc' hi0 hred0 => by
          obtain ⟨hnf_c, hlt_c⟩ := hargs_nf c' hc'
          have hle_c : lamSize c' ≤ sz := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt_c hle)
          exact ih c' hle_c hnf_c c₀ hi0 hred0)
      exact whReduces_sn_pullback_lambdaI hi hwh (sn_apps_var_head (.bvar k) (Or.inl ⟨k, rfl⟩) hcs_sn)
    · -- Case 3: `nf = apps (.fvar v) cs'`
      obtain ⟨cs₀, hwh, hf2⟩ := wh_standardization_apps_fvar cs' hm_nf
      have hi_apps : isLambdaI (apps (.fvar v) cs₀) = true :=
        isLambdaI_betaReduces (whReduces_to_betaReduces hwh) hi
      have hargs_nf := isBetaNF_apps_args (.fvar v) cs' hnf
      have hcs_sn : SNList cs₀ := snList_of_forall2 hf2
        (isLambdaI_apps_args (.fvar v) cs₀ hi_apps)
        (fun c₀ c' hc' hi0 hred0 => by
          obtain ⟨hnf_c, hlt_c⟩ := hargs_nf c' hc'
          have hle_c : lamSize c' ≤ sz := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt_c hle)
          exact ih c' hle_c hnf_c c₀ hi0 hred0)
      exact whReduces_sn_pullback_lambdaI hi hwh (sn_apps_var_head (.fvar v) (Or.inr ⟨v, rfl⟩) hcs_sn)
    · -- Case 4: `nf = apps ((.lam b) @@ a) cs'` — impossible since `nf` is a β-normal form!
      exfalso
      exact hnf _ (betaStep_apps_of_left (.beta b a) cs')

/-! ### Constructive `SN → WN` via Normal-Order Step (`stepNO`) -/

def stepNO : Lam → Option Lam
  | .bvar _ => none
  | .fvar _ => none
  | .lam b => (stepNO b).map .lam
  | .app (.lam b) a => some (subst 0 a b)
  | .app a b =>
    match stepNO a with
    | some a' => some (a' @@ b)
    | none => (stepNO b).map (a @@ ·)

theorem stepNO_sound : ∀ {m m' : Lam}, stepNO m = some m' → BetaStep m m'
  | .bvar _, _, h => by cases h
  | .fvar _, _, h => by cases h
  | .lam b, _, h => by
    simp only [stepNO] at h
    cases hb : stepNO b with
    | none => rw [hb] at h; cases h
    | some b' =>
      rw [hb] at h; injection h with heq; subst heq
      exact .lam (stepNO_sound hb)
  | .app (.lam b) a, _, h => by
    simp only [stepNO] at h
    injection h with heq; subst heq
    exact .beta b a
  | .app (.bvar k) b, _, h => by
    simp only [stepNO] at h
    cases hb : stepNO b with
    | none => rw [hb] at h; cases h
    | some b' =>
      rw [hb] at h; injection h with heq; subst heq
      exact .appR (stepNO_sound hb)
  | .app (.fvar v) b, _, h => by
    simp only [stepNO] at h
    cases hb : stepNO b with
    | none => rw [hb] at h; cases h
    | some b' =>
      rw [hb] at h; injection h with heq; subst heq
      exact .appR (stepNO_sound hb)
  | .app (.app u w) b, _, h => by
    simp only [stepNO] at h
    cases ha : stepNO (u @@ w) with
    | some a' =>
      rw [ha] at h; injection h with heq; subst heq
      exact .appL (stepNO_sound ha)
    | none =>
      rw [ha] at h
      cases hb : stepNO b with
      | none => rw [hb] at h; cases h
      | some b' =>
        rw [hb] at h; injection h with heq; subst heq
        exact .appR (stepNO_sound hb)

theorem stepNO_none_isBetaNF : ∀ {m : Lam}, stepNO m = none → IsBetaNF m
  | .bvar _, _, _, hs => by cases hs
  | .fvar _, _, _, hs => by cases hs
  | .lam b, h, _, hs => by
    simp only [stepNO] at h
    cases hb : stepNO b with
    | some _ => rw [hb] at h; cases h
    | none =>
      cases hs with
      | lam hsb => exact stepNO_none_isBetaNF hb _ hsb
  | .app (.lam b) a, h, _, _ => by
    simp only [stepNO] at h; cases h
  | .app (.bvar k) b, h, _, hs => by
    simp only [stepNO] at h
    cases hb : stepNO b with
    | some _ => rw [hb] at h; cases h
    | none =>
      cases hs with
      | appL hsa => cases hsa
      | appR hsb => exact stepNO_none_isBetaNF hb _ hsb
  | .app (.fvar v) b, h, _, hs => by
    simp only [stepNO] at h
    cases hb : stepNO b with
    | some _ => rw [hb] at h; cases h
    | none =>
      cases hs with
      | appL hsa => cases hsa
      | appR hsb => exact stepNO_none_isBetaNF hb _ hsb
  | .app (.app u w) b, h, _, hs => by
    simp only [stepNO] at h
    cases ha : stepNO (u @@ w) with
    | some _ => rw [ha] at h; cases h
    | none =>
      rw [ha] at h
      cases hb : stepNO b with
      | some _ => rw [hb] at h; cases h
      | none =>
        cases hs with
        | appL hsa => exact stepNO_none_isBetaNF ha _ hsa
        | appR hsb => exact stepNO_none_isBetaNF hb _ hsb

/-- Constructive `SN → WN` for all untyped `λ`-terms! -/
theorem sn_implies_wn_beta {m : Lam} (hsn : StrongNormalizingBeta m) : HasBetaNF m := by
  induction hsn with
  | intro m _ ih =>
    cases hs : stepNO m with
    | none => exact ⟨m, .refl m, stepNO_none_isBetaNF hs⟩
    | some m' =>
      obtain ⟨nf, hred, hnf⟩ := ih m' (stepNO_sound hs)
      exact ⟨nf, .next (stepNO_sound hs) hred, hnf⟩

/-- **Church's Theorem (`WN_β ↔ SN_β`) for `λI`-Calculus** (100% constructive!). -/
theorem lambdaI_wn_iff_sn {m : Lam} (hi : isLambdaI m = true) :
    HasBetaNF m ↔ StrongNormalizingBeta m :=
  ⟨lambdaI_wn_implies_sn hi, sn_implies_wn_beta⟩

/-! ## 5. Variable-Application Preserves `HasBetaNF` (All Untyped `λ`-Terms) -/

private theorem subst_fvar_eq_lam_inv {k v : Nat} {a p : Lam}
    (h : subst k (.fvar v) a = .lam p) : ∃ a₀, a = .lam a₀ := by
  cases a with
  | bvar j =>
    simp only [subst] at h
    by_cases hlt : j < k
    · rw [if_pos hlt] at h; cases h
    · rw [if_neg hlt] at h
      by_cases heq : j = k
      · rw [if_pos heq] at h; cases h
      · rw [if_neg heq] at h; cases h
  | fvar _ => cases h
  | app _ _ => cases h
  | lam a₀ => exact ⟨a₀, rfl⟩

theorem isBetaNF_subst_fvar (k v : Nat) {m : Lam} (hm : IsBetaNF m) :
    IsBetaNF (subst k (.fvar v) m) := by
  induction m generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · simp only [if_pos hlt]; intro _ hs; cases hs
    · simp only [if_neg hlt]
      by_cases heq : j = k
      · simp only [if_pos heq, shift]; intro _ hs; cases hs
      · simp only [if_neg heq]; intro _ hs; cases hs
  | fvar u =>
    intro _ hs; cases hs
  | lam b ih =>
    intro y hy
    cases hy with
    | lam hsb => exact ih (k + 1) (isBetaNF_of_lam hm) _ hsb
  | app a b iha ihb =>
    have ha_nf : IsBetaNF a := fun a' hs => hm _ (.appL hs)
    have hb_nf : IsBetaNF b := fun b' hs => hm _ (.appR hs)
    intro y hy
    simp only [subst] at hy
    generalize hxa : subst k (.fvar v) a = xa at hy
    cases hy with
    | appL hsa => rw [← hxa] at hsa; exact iha k ha_nf _ hsa
    | appR hsb => exact ihb k hb_nf _ hsb
    | @beta p _ =>
      obtain ⟨a₀, rfl⟩ := subst_fvar_eq_lam_inv hxa
      exact hm _ (.beta a₀ b)

/-- Applying any normalizing `λ`-term `m` to a free variable `.fvar v` preserves `HasBetaNF`. -/
theorem hasBetaNF_app_fvar {m : Lam} (h : HasBetaNF m) (v : Nat) :
    HasBetaNF (m @@ .fvar v) := by
  obtain ⟨nf, hred, hnf⟩ := h
  have h1 : BetaReduces (m @@ .fvar v) (nf @@ .fvar v) := betaReduces_appL hred (.fvar v)
  cases nf with
  | lam b =>
    refine ⟨subst 0 (.fvar v) b,
      betaReduces_trans h1 (.next (.beta b (.fvar v)) (.refl _)),
      isBetaNF_subst_fvar 0 v (isBetaNF_of_lam hnf)⟩
  | bvar k =>
    refine ⟨.bvar k @@ .fvar v, h1, fun y hy => ?_⟩
    cases hy with
    | appL hsa => cases hsa
    | appR hsb => cases hsb
  | fvar u =>
    refine ⟨.fvar u @@ .fvar v, h1, fun y hy => ?_⟩
    cases hy with
    | appL hsa => cases hsa
    | appR hsb => cases hsb
  | app p q =>
    refine ⟨(p @@ q) @@ .fvar v, h1, fun y hy => ?_⟩
    cases hy with
    | appL hsa => exact hnf _ hsa
    | appR hsb => cases hsb

end FormalLambdaConjectures
