import formal_lambda_conjectures.conjectures_42_43_and_repair

/-!
# Structural Analysis of Question 34 (*Dance of the Starlings*, 2017, p. 95):
# Single-Constant Combinatory Reduction, Unique `λI` Absorbing Sink, and Congruence Incomparability

Constructive Lean 4.33.1 formalization (zero `Classical.choice`, zero `sorry`, zero `native_decide`)
establishing four foundational structural theorems on **Question 34** of Barendregt, Endrullis,
Klop, and Waldmann (2017, p. 95), concerning the set
`L_34 := { M ∈ Ter(CL(S)) closed | (M)_λ is λβ-normalizing }`:

1. **Exact Collapse to Single-Constant Combinatory Saturation (`question_34_iff_single_constant_saturation`)**:
   By left-linearity of `S x y z → (x z)(y z)`, all free variables generated during hereditary
   saturation are dynamically indistinguishable inert atoms. Collapsing every variable to `.var 0`
   (`collapseVars`) yields `DeepCLNorm t ↔ DeepNorm1 (collapseVars t)` (`deepCLNorm_iff_deepNorm1`),
   and hence on closed pure-`S` combinators (`noVars m = true`):
   `StrongNormalizingBeta (toLam m) ↔ HasBetaNF (toLam m) ↔ DeepNorm1 m`,
   reducing Question 34 completely from untyped de Bruijn `λI`-calculus to single-constant
   combinatory logic `CL(S, x_0)` with zero `λ`-abstractions or variable-freshness side conditions.

2. **Verified Fuel-Bounded Evaluator (`checkDeepNorm1`, `snBeta_toLam_of_checkDeepNorm1`)**:
   Total executable checker `checkDeepNorm1 : Nat → Term → Bool` with constructive soundness proof
   certifying `(M)_λ ∈ SN_β` by pure kernel computation.

3. **Universal `λI` Context Non-Erasure & Unique Absorbing Myhill–Nerode Sink (`question_34_unique_absorbing_sink`)**:
   Because `(M)_λ` is a `λI`-term (`isLambdaI_toLam`), plugging any `λβ`-diverging combinator into
   **any** pure-`S` context `C[·]` preserves `λβ`-divergence (`not_snBeta_plugQ34Ctx`). Consequently,
   all `λβ`-diverging closed pure-`S` terms — whether `CL(S)`-diverging (`A A A`) or `CL(S)`-normalizing
   (`W_9`, `N_10`, `W_waldmann`, `M_14`, `M_15`) — collapse into **one single absorbing Myhill–Nerode
   equivalence class** under `≡_34`.

4. **Mutual Incomparability with `CL(S)` Algebras & Order-2 Normal-Form Fiber Shattering
   (`question_34_incomparable_with_cl_sn`, `question_34_q6_four_way_nf_shattering`)**:
   - `W_9 ≡_34 (A A A)` despite `HasNormalForm W_9` and `¬ StrongNormalizing (A A A)` (`≡_34 ⊈ ≡_SN`);
   - Conversely, the four closed order-2 normal forms `S(S(SA))`, `V`, `S V`, and `S(S(SAA))` — all
     lying in the **same** state `q_6` of Waldmann's 39-state `S`-algebra `A_SN` (with `S(S(SA))` and
     `S V` even sharing the exact same `(q_6, h_9, p_6)` state in `A_SN × A_HN × A_P`) — are
     **pairwise Myhill–Nerode inequivalent** under `≡_34` (`≡_{SN × HN × P} ⊈ ≡_34`).
-/

namespace FormalLambdaConjectures

/-! ## 1. Variable-Erasure Homomorphism `collapseVars` (`Ter(CL(S)) → CL(S, x_0)`) -/

/-- Collapses every variable `.var v` to the single canonical inert atom `.var 0`. -/
def collapseVars : Term → Term
  | .s => .s
  | .var _ => .var 0
  | .app a b => collapseVars a ⋅ collapseVars b

theorem collapseVars_eq_self_of_noVars : ∀ {t : Term}, noVars t = true → collapseVars t = t
  | .s, _ => rfl
  | .var _, h => by cases h
  | .app a b, h => by
    simp only [noVars, Bool.and_eq_true] at h
    simp [collapseVars, collapseVars_eq_self_of_noVars h.1, collapseVars_eq_self_of_noVars h.2]

private theorem collapseVars_eq_s_iff {t : Term} : collapseVars t = .s ↔ t = .s := by
  cases t <;> simp [collapseVars]

private theorem collapseVars_eq_var0_iff {t : Term} :
    collapseVars t = .var 0 ↔ ∃ v, t = .var v := by
  cases t with
  | s => simp [collapseVars]
  | var v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => rfl⟩
  | app _ _ => simp [collapseVars]

private theorem collapseVars_eq_app_iff {t p q : Term} :
    collapseVars t = p ⋅ q ↔ ∃ a b, t = a ⋅ b ∧ collapseVars a = p ∧ collapseVars b = q := by
  cases t with
  | s => simp [collapseVars]
  | var _ => simp [collapseVars]
  | app a b =>
    simp only [collapseVars, Term.app.injEq]
    exact ⟨fun ⟨ha, hb⟩ => ⟨a, b, ⟨rfl, rfl⟩, ha, hb⟩,
           fun ⟨_, _, ⟨rfl, rfl⟩, ha, hb⟩ => ⟨ha, hb⟩⟩

theorem headLeaf_collapseVars_of_var {t : Term} {v : Nat}
    (h : headLeaf t = .var v) : headLeaf (collapseVars t) = .var 0 := by
  induction t with
  | s => cases h
  | var _ => rfl
  | app _ _ ih _ => exact ih h

theorem headLeaf_collapseVars_var0_inv {t : Term}
    (h : headLeaf (collapseVars t) = .var 0) : ∃ v, headLeaf t = .var v := by
  induction t with
  | s => cases h
  | var v => exact ⟨v, rfl⟩
  | app _ _ ih _ => exact ih h

theorem isPartialS_collapseVars_iff {t : Term} :
    IsPartialS (collapseVars t) ↔ IsPartialS t := by
  constructor
  · intro hp
    rcases hp with hs | ⟨x', hx'⟩ | ⟨x', y', hxy'⟩
    · exact Or.inl (collapseVars_eq_s_iff.mp hs)
    · obtain ⟨a, x, rfl, ha, _⟩ := collapseVars_eq_app_iff.mp hx'
      rw [collapseVars_eq_s_iff.mp ha]
      exact Or.inr (Or.inl ⟨x, rfl⟩)
    · obtain ⟨ab, y, rfl, hab, _⟩ := collapseVars_eq_app_iff.mp hxy'
      obtain ⟨a, x, rfl, ha, _⟩ := collapseVars_eq_app_iff.mp hab
      rw [collapseVars_eq_s_iff.mp ha]
      exact Or.inr (Or.inr ⟨x, y, rfl⟩)
  · intro hp
    rcases hp with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨collapseVars x, rfl⟩)
    · exact Or.inr (Or.inr ⟨collapseVars x, collapseVars y, rfl⟩)

/-- Forward `CL(S)` step preservation under `collapseVars`. -/
theorem step_collapseVars {t t' : Term} (h : Step t t') :
    Step (collapseVars t) (collapseVars t') := by
  induction h with
  | root x y z => exact .root (collapseVars x) (collapseVars y) (collapseVars z)
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Backward `CL(S)` step lifting across `collapseVars` (by left-linearity of `S x y z → (x z)(y z)`). -/
theorem step_of_collapseVars {t u' : Term} (h : Step (collapseVars t) u') :
    ∃ t', Step t t' ∧ collapseVars t' = u' := by
  suffices hgen : ∀ {u u' : Term}, Step u u' → ∀ t, collapseVars t = u →
      ∃ t', Step t t' ∧ collapseVars t' = u' from
    hgen h t rfl
  intro u u' hs
  induction hs with
  | root x' y' z' =>
    intro t ht
    obtain ⟨ab, z, rfl, hab, rfl⟩ := collapseVars_eq_app_iff.mp ht
    obtain ⟨a, y, rfl, ha, rfl⟩ := collapseVars_eq_app_iff.mp hab
    obtain ⟨s0, x, rfl, hs0, rfl⟩ := collapseVars_eq_app_iff.mp ha
    rw [collapseVars_eq_s_iff.mp hs0]
    exact ⟨(x ⋅ z) ⋅ (y ⋅ z), .root x y z, rfl⟩
  | @left a0 a0' b0 _ ih =>
    intro t ht
    obtain ⟨a, b, rfl, ha, rfl⟩ := collapseVars_eq_app_iff.mp ht
    obtain ⟨a', hsa, rfl⟩ := ih a ha
    exact ⟨a' ⋅ b, .left hsa, rfl⟩
  | @right a0 b0 b0' _ ih =>
    intro t ht
    obtain ⟨a, b, rfl, rfl, hb⟩ := collapseVars_eq_app_iff.mp ht
    obtain ⟨b', hsb, rfl⟩ := ih b hb
    exact ⟨a ⋅ b', .right hsb, rfl⟩

/-! ## 2. Single-Constant Hereditary Saturation (`DeepNorm1`) & Question 34 Reduction -/

/-- **Single-Constant Hereditary Saturation (`DeepNorm1`)**:
    Uses ONLY `.s`, `.var 0`, and `⋅`, with **no** fresh-variable condition on `saturate`. -/
inductive DeepNorm1 : Term → Prop where
  | step {t t' : Term} : Step t t' → DeepNorm1 t' → DeepNorm1 t
  | var0 : DeepNorm1 (.var 0)
  | varApp {a b : Term} :
      headLeaf a = .var 0 → DeepNorm1 a → DeepNorm1 b → DeepNorm1 (a ⋅ b)
  | saturate {t : Term} :
      IsPartialS t → DeepNorm1 (t ⋅ .var 0) → DeepNorm1 t

/-- **Exact Collapse Theorem (`deepCLNorm_iff_deepNorm1`)**:
    Multi-variable fresh saturation `DeepCLNorm t` is 100% equivalent to single-constant
    saturation `DeepNorm1 (collapseVars t)`. -/
theorem deepCLNorm_iff_deepNorm1 (t : Term) :
    DeepCLNorm t ↔ DeepNorm1 (collapseVars t) := by
  constructor
  · intro hd
    induction hd with
    | step hs _ ih => exact .step (step_collapseVars hs) ih
    | var _ => exact .var0
    | varApp _ hhead _ _ iha ihb =>
      exact .varApp (headLeaf_collapseVars_of_var hhead) iha ihb
    | saturate _ hpart _ _ ihz =>
      exact .saturate (isPartialS_collapseVars_iff.mpr hpart) ihz
  · intro hd1
    suffices hgen : ∀ {u : Term}, DeepNorm1 u → ∀ t, collapseVars t = u → DeepCLNorm t from
      hgen hd1 t rfl
    intro u hdu
    induction hdu with
    | step hsu _ ih =>
      intro t ht
      rw [← ht] at hsu
      obtain ⟨t', hst, hcol'⟩ := step_of_collapseVars hsu
      exact .step hst (ih t' hcol')
    | var0 =>
      intro t ht
      obtain ⟨v, rfl⟩ := collapseVars_eq_var0_iff.mp ht
      exact .var v
    | varApp hhead _ _ iha ihb =>
      intro t ht
      obtain ⟨a0, b0, rfl, ha0, hb0⟩ := collapseVars_eq_app_iff.mp ht
      rw [← ha0] at hhead
      obtain ⟨v, hv⟩ := headLeaf_collapseVars_var0_inv hhead
      exact .varApp v hv (iha a0 ha0) (ihb b0 hb0)
    | @saturate u0 hpart _ ih =>
      intro t ht
      rw [← ht] at hpart
      have hpart_t : IsPartialS t := isPartialS_collapseVars_iff.mp hpart
      let z := maxVarBound t
      have hz : hasVar z t = false := hasVar_false_of_ge (Nat.le_refl _)
      have hcol_z : collapseVars (t ⋅ .var z) = u0 ⋅ .var 0 := by
        simp [collapseVars, ht]
      exact .saturate z hpart_t hz (ih (t ⋅ .var z) hcol_z)

/-- **THEOREM (Exact Single-Constant Reduction of Question 34)**:
    For every closed pure-`S` combinator `m` (`noVars m = true`),
    `(m)_λ` is `λβ`-normalizing (`StrongNormalizingBeta (toLam m)` / `HasBetaNF (toLam m)`)
    **if and only if** `DeepNorm1 m` holds in single-constant `CL(S, x_0)`. -/
theorem question_34_iff_single_constant_saturation {m : Term} (hm : noVars m = true) :
    (StrongNormalizingBeta (toLam m) ↔ DeepNorm1 m) ∧
    (HasBetaNF (toLam m) ↔ DeepNorm1 m) := by
  have hwn_sn : HasBetaNF (toLam m) ↔ StrongNormalizingBeta (toLam m) :=
    lambdaI_wn_iff_sn (isLambdaI_toLam m)
  have hdn : HasBetaNF (toLam m) ↔ DeepNorm1 m := by
    rw [← repaired_conjecture_42, deepCLNorm_iff_deepNorm1, collapseVars_eq_self_of_noVars hm]
  exact ⟨hwn_sn.symm.trans hdn, hdn⟩

/-! ## 3. Verified Executable Checker `checkDeepNorm1` -/

def isPartialSBool : Term → Bool
  | .s => true
  | .app .s _ => true
  | .app (.app .s _) _ => true
  | _ => false

theorem isPartialSBool_sound {t : Term} (h : isPartialSBool t = true) : IsPartialS t := by
  cases t with
  | s => exact Or.inl rfl
  | var _ => cases h
  | app a b =>
    cases a with
    | s => exact Or.inr (Or.inl ⟨b, rfl⟩)
    | var _ => cases h
    | app a1 x =>
      cases a1 with
      | s => exact Or.inr (Or.inr ⟨x, b, rfl⟩)
      | var _ => cases h
      | app _ _ => cases h

def checkDeepNorm1 : Nat → Term → Bool
  | 0, _ => false
  | fuel + 1, t =>
    match stepCLOpt t with
    | some t' => checkDeepNorm1 fuel t'
    | none =>
      if isPartialSBool t then
        checkDeepNorm1 fuel (t ⋅ .var 0)
      else
        match t with
        | .var 0 => true
        | .app a b => decide (headLeaf a = .var 0) && checkDeepNorm1 fuel a && checkDeepNorm1 fuel b
        | _ => false

theorem checkDeepNorm1_sound {fuel : Nat} {t : Term} (h : checkDeepNorm1 fuel t = true) :
    DeepNorm1 t := by
  induction fuel generalizing t with
  | zero => cases h
  | succ fuel ih =>
    simp only [checkDeepNorm1] at h
    cases hs : stepCLOpt t with
    | some t' =>
      rw [hs] at h
      exact .step (stepCLOpt_sound hs) (ih h)
    | none =>
      rw [hs] at h
      cases hp : isPartialSBool t with
      | true =>
        rw [hp, if_pos rfl] at h
        exact .saturate (isPartialSBool_sound hp) (ih h)
      | false =>
        rw [hp, if_neg (by decide)] at h
        cases t with
        | s => cases hp
        | var v =>
          cases v with
          | zero => exact .var0
          | succ _ => cases h
        | app a b =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact .varApp h.1.1 (ih h.1.2) (ih h.2)

theorem snBeta_toLam_of_checkDeepNorm1 {m : Term} (hm : noVars m = true)
    {fuel : Nat} (hchk : checkDeepNorm1 fuel m = true) :
    StrongNormalizingBeta (toLam m) :=
  (question_34_iff_single_constant_saturation hm).1.mpr (checkDeepNorm1_sound hchk)

/-! ## 4. Universal `λI` Absorbing Sink & Mutual Congruence Incomparability -/

/-- One-hole pure-`S` contexts for Myhill–Nerode equivalence `≡_34`. -/
inductive Q34Ctx where
  | hole  : Q34Ctx
  | left  : Q34Ctx → Term → Q34Ctx
  | right : Term → Q34Ctx → Q34Ctx
  deriving DecidableEq, Repr

def plugQ34Ctx : Q34Ctx → Term → Term
  | .hole, u => u
  | .left c r, u => plugQ34Ctx c u ⋅ r
  | .right l c, u => l ⋅ plugQ34Ctx c u

def noVarsCtx34 : Q34Ctx → Bool
  | .hole => true
  | .left c r => noVarsCtx34 c && noVars r
  | .right l c => noVars l && noVarsCtx34 c

/-- Myhill–Nerode congruence of Question 34 over closed pure-`S` contexts. -/
def NerodeEq34 (u v : Term) : Prop :=
  ∀ c : Q34Ctx, noVarsCtx34 c = true →
    (StrongNormalizingBeta (toLam (plugQ34Ctx c u)) ↔
     StrongNormalizingBeta (toLam (plugQ34Ctx c v)))

theorem snBeta_of_appL {a b : Lam} (h : StrongNormalizingBeta (a @@ b)) :
    StrongNormalizingBeta a := by
  suffices hg : ∀ z, StrongNormalizingBeta z → ∀ a b, z = a @@ b → StrongNormalizingBeta a from
    hg (a @@ b) h a b rfl
  intro z hz; induction hz with
  | intro _ _ ih =>
    intro a0 b0 heq; subst heq
    exact Acc.intro a0 (fun a1 hs => ih _ (.appL hs) a1 b0 rfl)

theorem snBeta_of_appR {a b : Lam} (h : StrongNormalizingBeta (a @@ b)) :
    StrongNormalizingBeta b := by
  suffices hg : ∀ z, StrongNormalizingBeta z → ∀ a b, z = a @@ b → StrongNormalizingBeta b from
    hg (a @@ b) h a b rfl
  intro z hz; induction hz with
  | intro _ _ ih =>
    intro a0 b0 heq; subst heq
    exact Acc.intro b0 (fun b1 hs => ih _ (.appR hs) a0 b1 rfl)

/-- Plugging into ANY pure-`S` context reflects `StrongNormalizingBeta (toLam ·)`. -/
theorem snBeta_of_plugQ34Ctx (c : Q34Ctx) {u : Term}
    (h : StrongNormalizingBeta (toLam (plugQ34Ctx c u))) :
    StrongNormalizingBeta (toLam u) := by
  induction c with
  | hole => exact h
  | left c _ ih => exact ih (snBeta_of_appL h)
  | right _ c ih => exact ih (snBeta_of_appR h)

theorem not_snBeta_plugQ34Ctx (c : Q34Ctx) {u : Term}
    (hdiv : ¬ StrongNormalizingBeta (toLam u)) :
    ¬ StrongNormalizingBeta (toLam (plugQ34Ctx c u)) :=
  fun h => hdiv (snBeta_of_plugQ34Ctx c h)

/-- **Universal `λI` Absorbing Sink Theorem (`question_34_unique_absorbing_sink`)**:
    Any two `λβ`-diverging pure-`S` terms `u, v` are Myhill–Nerode equivalent (`NerodeEq34 u v`)
    under **all** pure-`S` contexts! -/
theorem question_34_unique_absorbing_sink {u v : Term}
    (hu : ¬ StrongNormalizingBeta (toLam u))
    (hv : ¬ StrongNormalizingBeta (toLam v)) :
    NerodeEq34 u v := by
  intro c _
  exact ⟨fun h => False.elim (not_snBeta_plugQ34Ctx c hu h),
         fun h => False.elim (not_snBeta_plugQ34Ctx c hv h)⟩

private theorem not_snBeta_of_no_betaNF {t : Term} (h : ¬ HasBetaNF (toLam t)) :
    ¬ StrongNormalizingBeta (toLam t) :=
  fun hsn => h ((lambdaI_wn_iff_sn (isLambdaI_toLam t)).mpr hsn)

private def iterT_any (g : Term) : Nat → Term
  | 0 => V_comb ⋅ g
  | n + 1 => T_comb ⋅ iterT_any g n

private def famT_any (g : Term) (n : Nat) : Term :=
  (V_comb ⋅ g) ⋅ iterT_any g n

private theorem iterT_any_pass (g : Term) (m : Nat) (y : Term) :
    ∃ c, Reduces (iterT_any g m ⋅ y) c ∧ SubtermCL ((V_comb ⋅ g) ⋅ y) c := by
  induction m with
  | zero => exact ⟨_, .refl _, .refl _⟩
  | succ m ih =>
    obtain ⟨c, hrc, hsc⟩ := ih
    exact ⟨(S ⋅ y) ⋅ c,
      .next (.root S (iterT_any g m) y) (reduces_right _ hrc),
      .right hsc⟩

private theorem stepPlus_of_step_reduces {a b c : Term} (h1 : Step a b) (h2 : Reduces b c) :
    StepPlus a c := by
  induction h2 generalizing a with
  | refl => exact .single h1
  | @next _ mid _ hs _ ih => exact .head h1 (ih hs)

/-- For ANY pure-`S` term `g` (in particular closed `g = S`), `W_waldmann ⋅ g` is non-`SN` in `CL(S)`. -/
theorem w_waldmann_app_not_sn_cl (g : Term) : ¬ StrongNormalizing (W_waldmann ⋅ g) := by
  have hspiral : ∀ n, StepToSubtermCL (famT_any g n) (famT_any g (n + 1)) := by
    intro n
    let u := iterT_any g n
    let u1 := iterT_any g (n + 1)
    have h1 : Step (famT_any g n) ((Z_comb ⋅ u) ⋅ (g ⋅ u)) := .root Z_comb g u
    have h2 : Step ((Z_comb ⋅ u) ⋅ (g ⋅ u)) ((u1 ⋅ u1) ⋅ (g ⋅ u)) :=
      .left (.root T_comb T_comb u)
    obtain ⟨c, hrc, hsc⟩ := iterT_any_pass g (n + 1) u1
    exact ⟨c ⋅ (g ⋅ u),
      .head h1 (stepPlus_of_step_reduces h2 (reduces_left hrc (g ⋅ u))),
      .left hsc⟩
  have hnsn0 := not_sn_of_subterm_spiral (famT_any g) hspiral
  have hr : Reduces (W_waldmann ⋅ g) (famT_any g 0) :=
    .next (.root V_comb V_comb g) (.refl _)
  exact not_sn_of_reduces_subterm hr (.refl _) hnsn0

/-! ## 5. Mutual Congruence Incomparability & Four-Way Order-2 Normal-Form Fiber Shattering -/

/-- Four closed order-2 `CL(S)` normal forms (all residing in state `q_6` of Waldmann's `A_SN`,
    with `q34_u0` and `q34_u2` even sharing the exact same `(q_6, h_9, p_6)` state in
    `A_SN × A_HN × A_P`!):
    - `q34_u0 := S (S (S A))` (`6` leaves)
    - `q34_u1 := V = S (S T T)` (`6` leaves)
    - `q34_u2 := S V` (`7` leaves)
    - `q34_u3 := S (S (S A A))` (`9` leaves) -/
def q34_u0 : Term := S ⋅ (S ⋅ (S ⋅ A_comb))
def q34_u1 : Term := V_comb
def q34_u2 : Term := S ⋅ V_comb
def q34_u3 : Term := S ⋅ (S ⋅ (S ⋅ A_comb ⋅ A_comb))

/-- Four elementary closed pure-`S` separating contexts:
    - `q34_c0 = []`
    - `q34_c1 = [] ⋅ S`
    - `q34_c2 = [] ⋅ V`
    - `q34_c3 = S ⋅ V ⋅ []` -/
def q34_c0 : Q34Ctx := .hole
def q34_c1 : Q34Ctx := .left .hole S
def q34_c2 : Q34Ctx := .left .hole V_comb
def q34_c3 : Q34Ctx := .right (S ⋅ V_comb) .hole

theorem q34_four_witnesses_closed_nf :
    (noVars q34_u0 = true ∧ IsNormalForm q34_u0) ∧
    (noVars q34_u1 = true ∧ IsNormalForm q34_u1) ∧
    (noVars q34_u2 = true ∧ IsNormalForm q34_u2) ∧
    (noVars q34_u3 = true ∧ IsNormalForm q34_u3) :=
  ⟨⟨rfl, stepCLOpt_none_isNormalForm rfl⟩,
   ⟨rfl, stepCLOpt_none_isNormalForm rfl⟩,
   ⟨rfl, stepCLOpt_none_isNormalForm rfl⟩,
   ⟨rfl, stepCLOpt_none_isNormalForm rfl⟩⟩

theorem q34_four_witnesses_all_snBeta :
    StrongNormalizingBeta (toLam q34_u0) ∧
    StrongNormalizingBeta (toLam q34_u1) ∧
    StrongNormalizingBeta (toLam q34_u2) ∧
    StrongNormalizingBeta (toLam q34_u3) :=
  ⟨snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 60) rfl,
   snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 60) rfl,
   snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 60) rfl,
   snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 60) rfl⟩

/-- **Four-Way Shattering Inside Waldmann's `q_6` Order-2 Normal-Form Fiber
    (`question_34_q6_four_way_nf_shattering`)**:
    `q34_u0`, `q34_u1`, `q34_u2`, `q34_u3` (plus `N10` for the 5th sink class) are
    **pairwise Myhill–Nerode inequivalent** under `NerodeEq34`! -/
theorem question_34_q6_four_way_nf_shattering :
    ¬ NerodeEq34 q34_u0 q34_u1 ∧
    ¬ NerodeEq34 q34_u0 q34_u2 ∧
    ¬ NerodeEq34 q34_u0 q34_u3 ∧
    ¬ NerodeEq34 q34_u1 q34_u2 ∧
    ¬ NerodeEq34 q34_u1 q34_u3 ∧
    ¬ NerodeEq34 q34_u2 q34_u3 ∧
    (∀ u ∈ [q34_u0, q34_u1, q34_u2, q34_u3], ¬ NerodeEq34 u N10) := by
  have hc0 : noVarsCtx34 q34_c0 = true := rfl
  have hc1 : noVarsCtx34 q34_c1 = true := rfl
  have hc2 : noVarsCtx34 q34_c2 = true := rfl
  have hc3 : noVarsCtx34 q34_c3 = true := rfl
  -- Positive (`1`) entries certified by `checkDeepNorm1`:
  have h_u0_c1 : StrongNormalizingBeta (toLam (plugQ34Ctx q34_c1 q34_u0)) :=
    snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 80) rfl
  have h_u0_c2 : StrongNormalizingBeta (toLam (plugQ34Ctx q34_c2 q34_u0)) :=
    snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 120) rfl
  have h_u0_c3 : StrongNormalizingBeta (toLam (plugQ34Ctx q34_c3 q34_u0)) :=
    snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 300) rfl
  have h_u1_c1 : StrongNormalizingBeta (toLam (plugQ34Ctx q34_c1 q34_u1)) :=
    snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 80) rfl
  have h_u1_c2 : StrongNormalizingBeta (toLam (plugQ34Ctx q34_c2 q34_u1)) :=
    snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 120) rfl
  have h_u2_c1 : StrongNormalizingBeta (toLam (plugQ34Ctx q34_c1 q34_u2)) :=
    snBeta_toLam_of_checkDeepNorm1 rfl (fuel := 80) rfl
  -- Negative (`0`) entries definitionally equal to `W_waldmann` or `N10`:
  have h_u1_c3_neg : ¬ StrongNormalizingBeta (toLam (plugQ34Ctx q34_c3 q34_u1)) :=
    not_snBeta_of_no_betaNF w_waldmann_toLam_no_betaNF
  have h_u2_c2_neg : ¬ StrongNormalizingBeta (toLam (plugQ34Ctx q34_c2 q34_u2)) :=
    not_snBeta_of_no_betaNF w_waldmann_toLam_no_betaNF
  have h_u3_c1_neg : ¬ StrongNormalizingBeta (toLam (plugQ34Ctx q34_c1 q34_u3)) :=
    not_snBeta_of_no_betaNF n10_toLam_no_betaNF
  have h_n10_neg : ¬ StrongNormalizingBeta (toLam N10) :=
    not_snBeta_of_no_betaNF n10_toLam_no_betaNF
  obtain ⟨hs0, hs1, hs2, hs3⟩ := q34_four_witnesses_all_snBeta
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq; exact h_u1_c3_neg ((heq q34_c3 hc3).mp h_u0_c3)
  · intro heq; exact h_u2_c2_neg ((heq q34_c2 hc2).mp h_u0_c2)
  · intro heq; exact h_u3_c1_neg ((heq q34_c1 hc1).mp h_u0_c1)
  · intro heq; exact h_u2_c2_neg ((heq q34_c2 hc2).mp h_u1_c2)
  · intro heq; exact h_u3_c1_neg ((heq q34_c1 hc1).mp h_u1_c1)
  · intro heq; exact h_u3_c1_neg ((heq q34_c1 hc1).mp h_u2_c1)
  · intro u hu heq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact h_n10_neg ((heq q34_c0 hc0).mp hs0)
    · exact h_n10_neg ((heq q34_c0 hc0).mp hs1)
    · exact h_n10_neg ((heq q34_c0 hc0).mp hs2)
    · exact h_n10_neg ((heq q34_c0 hc0).mp hs3)

/-- **Mutual Congruence Incomparability (`question_34_incomparable_with_cl_sn`)**:
    1. `W9` (`CL(S)`-normalizing, `9` leaves) and `W_waldmann ⋅ S` (`CL(S)`-diverging, `14` leaves)
       are **equivalent** under `NerodeEq34` (`≡_34 ⊈ ≡_SN`);
    2. Conversely, `q34_u0 = S(S(SA))` and `q34_u2 = S V` are both closed `CL(S)` normal forms
       sharing the exact same `(q_6, h_9, p_6)` state in `A_SN × A_HN × A_P`, yet are
       **inequivalent** under `NerodeEq34` (`≡_{SN × HN × P} ⊈ ≡_34`). -/
theorem question_34_incomparable_with_cl_sn :
    (noVars W9 = true ∧ noVars (W_waldmann ⋅ S) = true ∧
     HasNormalForm W9 ∧ ¬ StrongNormalizing (W_waldmann ⋅ S) ∧
     NerodeEq34 W9 (W_waldmann ⋅ S)) ∧
    (noVars q34_u0 = true ∧ noVars q34_u2 = true ∧
     IsNormalForm q34_u0 ∧ IsNormalForm q34_u2 ∧
     ¬ NerodeEq34 q34_u0 q34_u2) := by
  have hw9_div : ¬ StrongNormalizingBeta (toLam W9) :=
    not_snBeta_of_no_betaNF w9_toLam_no_betaNF
  have hwws_div : ¬ StrongNormalizingBeta (toLam (W_waldmann ⋅ S)) :=
    fun hsn => w_waldmann_app_not_sn_cl S (sn_cl_of_sn_toLam hsn)
  exact ⟨⟨rfl, rfl, w9_hasNormalForm, w_waldmann_app_not_sn_cl S,
          question_34_unique_absorbing_sink hw9_div hwws_div⟩,
         ⟨rfl, rfl, stepCLOpt_none_isNormalForm rfl, stepCLOpt_none_isNormalForm rfl,
          question_34_q6_four_way_nf_shattering.2.1⟩⟩

end FormalLambdaConjectures


