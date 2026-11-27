import formal_lambda_conjectures.lambda_standardization_conservation

/-!
# Constructive Resolution of Conjecture 40 (*Dance of the Starlings*, 2017, p. 102):
# Exact Preservation of Term Order from Combinatory Logic (`CL(S)` & Full `CL({S,K,I})`) to `λ`-Calculus

Proves **Conjecture 40** of Barendregt, Endrullis, Klop, and Waldmann (2017, p. 102) in full generality
(zero `Classical.choice`, zero `sorry`, zero `native_decide`):
1. **Pure-`S` Combinatory Logic (`Term`, `Step`, `Reduces`, `toLam`)** and
   **Full Combinatory Logic `CL({S, K, I})` (`CLTerm`, `CLStep`, `CLReduces`, `clToLam`)**,
   with forward simulation (`Step a b → BetaPlus (toLam a) (toLam b)` and
   `CLStep a b → BetaPlus (clToLam a) (clToLam b)`).
2. **Definition 35 (`LamOrder`)** in `λ`-calculus (`order = 0` iff never reduces to `λx. P`,
   `order = n + 1` iff reduces to `λx. P` of order `n`), proved unique, `=β`-invariant,
   and step-down compatible under application to fresh variables (`lamOrder_succ_iff_app_fvar`).
3. **Definition 37 (`CLOrder` & Curry–Feys Unconsumed-Arguments Equivalence)** in both `CL({S,K,I})`
   and pure `CL(S)`.
4. **Key Bridge Theorem (`cl_reduces_partial_iff_lam_reduces_abs`)**:
   `M` reduces in `CL` to a partial combinator application (`I, K, K A, S, S A, S A B`)
   if and only if `(M)_λ` reduces in `λβ` to an abstraction `λx. P`!
5. **Conjecture 40 (`conjecture_40_full_cl`, `conjecture_40_infinite_order`, `conjecture_40_pure_s`)**:
   - For all `M ∈ Ter(CL({S,K,I}))` and `n ∈ ℕ`: `CLOrder M n ↔ LamOrder (clToLam M) n`,
     and `HasInfiniteCLOrder M ↔ HasInfiniteLamOrder (clToLam M)`.
   - For all `M ∈ Ter(CL(S))` and `n ∈ ℕ`: `PureSCLOrder M n ↔ LamOrder (toLam M) n`,
     and both are bounded by `3` (`n ≤ 3`, via Visser–van Oostrom!).
-/

namespace FormalLambdaConjectures

/-! ## 1. Pure-`S` Combinatory Logic (`Term`) and Exact `λ`-Translation (`toLam`) -/

inductive Term where
  | s   : Term
  | var : Nat → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

infixl:70 " ⋅ " => Term.app

def S : Term := Term.s
def T_comb : Term := S ⋅ S
def A_comb : Term := S ⋅ S ⋅ S

def leaves : Term → Nat
  | .s => 1
  | .var _ => 1
  | .app a b => leaves a + leaves b

def noVars : Term → Bool
  | .s => true
  | .var _ => false
  | .app a b => noVars a && noVars b

def hasVar (v : Nat) : Term → Bool
  | .s => false
  | .var u => decide (u = v)
  | .app a b => hasVar v a || hasVar v b

def maxVarBound : Term → Nat
  | .s => 0
  | .var u => u + 1
  | .app a b => Nat.max (maxVarBound a) (maxVarBound b)

theorem hasVar_false_of_ge {v : Nat} {t : Term} (h : maxVarBound t ≤ v) :
    hasVar v t = false := by
  induction t with
  | s => rfl
  | var u =>
    simp only [maxVarBound] at h
    simp only [hasVar, decide_eq_false_iff_not]
    intro huv; subst huv; exact Nat.lt_irrefl u h
  | app a b iha ihb =>
    simp only [maxVarBound] at h
    simp [hasVar,
      iha (Nat.le_trans (Nat.le_max_left _ _) h),
      ihb (Nat.le_trans (Nat.le_max_right _ _) h)]

def spineLen : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app a _ => 1 + spineLen a

def headLeaf : Term → Term
  | .s => .s
  | .var v => .var v
  | .app a _ => headLeaf a

inductive Step : Term → Term → Prop where
  | root (x y z : Term) : Step (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : Step a a' → Step (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Step b b' → Step (a ⋅ b) (a ⋅ b')

inductive StepPlus : Term → Term → Prop where
  | single {a b : Term} : Step a b → StepPlus a b
  | head {a b c : Term} : Step a b → StepPlus b c → StepPlus a c

inductive Reduces : Term → Term → Prop where
  | refl (a : Term) : Reduces a a
  | next {a b c : Term} : Step a b → Reduces b c → Reduces a c

def IsNormalForm (t : Term) : Prop := ∀ t', ¬ Step t t'
def HasNormalForm (t : Term) : Prop := ∃ nf, Reduces t nf ∧ IsNormalForm nf
def StrongNormalizing (t : Term) : Prop := Acc (fun b a => Step a b) t

theorem reduces_trans {a b c : Term} (h1 : Reduces a b) (h2 : Reduces b c) : Reduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem stepPlus_trans {a b c : Term} (h1 : StepPlus a b) (h2 : StepPlus b c) : StepPlus a c := by
  induction h1 with
  | single hs => exact .head hs h2
  | head hs _ ih => exact .head hs (ih h2)

theorem reduces_of_stepPlus {a b : Term} (h : StepPlus a b) : Reduces a b := by
  induction h with
  | single hs => exact .next hs (.refl _)
  | head hs _ ih => exact .next hs ih

theorem reduces_left {a a' : Term} (h : Reduces a a') (b : Term) : Reduces (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.left hs) ih

theorem reduces_right (a : Term) {b b' : Term} (h : Reduces b b') : Reduces (a ⋅ b) (a ⋅ b') := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.right hs) ih

theorem reduces_app {a a' b b' : Term} (ha : Reduces a a') (hb : Reduces b b') :
    Reduces (a ⋅ b) (a' ⋅ b') :=
  reduces_trans (reduces_left ha b) (reduces_right a' hb)

theorem stepPlus_left {a a' : Term} (h : StepPlus a a') (b : Term) : StepPlus (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | single hs => exact .single (.left hs)
  | head hs _ ih => exact .head (.left hs) ih

theorem stepPlus_right (a : Term) {b b' : Term} (h : StepPlus b b') : StepPlus (a ⋅ b) (a ⋅ b') := by
  induction h with
  | single hs => exact .single (.right hs)
  | head hs _ ih => exact .head (.right hs) ih

theorem hasVar_false_step {v : Nat} {a b : Term} (h : Step a b) :
    hasVar v a = false → hasVar v b = false := by
  induction h with
  | root x y z =>
    simp only [S, hasVar, Bool.or_eq_false_iff]
    intro ⟨⟨⟨_, hx⟩, hy⟩, hz⟩
    exact ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
  | left _ ih =>
    simp only [hasVar, Bool.or_eq_false_iff]
    intro ⟨ha, hb⟩; exact ⟨ih ha, hb⟩
  | right _ ih =>
    simp only [hasVar, Bool.or_eq_false_iff]
    intro ⟨ha, hb⟩; exact ⟨ha, ih hb⟩

theorem hasVar_false_reduces {v : Nat} {a b : Term} (h : Reduces a b) :
    hasVar v a = false → hasVar v b = false := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (hasVar_false_step hs hv)

/-! ### Exact Homomorphic Translation `(·)_λ` (`S ↦ λx y z. (x z)(y z)`) -/

def lamS : Lam := .lam (.lam (.lam ((.bvar 2 @@ .bvar 0) @@ (.bvar 1 @@ .bvar 0))))
def lamK : Lam := .lam (.lam (.bvar 1))
def lamI : Lam := .lam (.bvar 0)

def toLam : Term → Lam
  | .s => lamS
  | .var v => .fvar v
  | .app a b => toLam a @@ toLam b

theorem bvarClosed_toLam (t : Term) : bvarClosed 0 (toLam t) = true := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp [toLam, bvarClosed, iha, ihb]

theorem isLambdaI_toLam (t : Term) : isLambdaI (toLam t) = true := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp [toLam, isLambdaI, iha, ihb]

theorem hasFVar_toLam (v : Nat) (t : Term) : hasFVar v (toLam t) = hasVar v t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp [toLam, hasFVar, hasVar, iha, ihb]

theorem maxFVarBound_toLam (t : Term) : maxFVarBound (toLam t) = maxVarBound t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp [toLam, maxFVarBound, maxVarBound, iha, ihb]

/-- Exact 1-, 2-, and 3-step weak-head reductions of `lamS`, `lamK`, `lamI` on `bvarClosed 0` arguments. -/
theorem lamS_wh1 {x : Lam} (hx : bvarClosed 0 x = true) :
    WHStep (lamS @@ x) (.lam (.lam ((x @@ .bvar 0) @@ (.bvar 1 @@ .bvar 0)))) := by
  have h1 : subst 0 x (.lam (.lam ((.bvar 2 @@ .bvar 0) @@ (.bvar 1 @@ .bvar 0)))) =
      .lam (.lam ((x @@ .bvar 0) @@ (.bvar 1 @@ .bvar 0))) := by
    simp only [subst, shift_bvarClosed 2 0 x hx]
    rfl
  rw [← h1]
  exact WHStep.beta _ x

theorem lamS_wh2 {x y : Lam} (hx : bvarClosed 0 x = true) (hy : bvarClosed 0 y = true) :
    ∃ mid, WHStep ((lamS @@ x) @@ y) mid ∧
      WHStep mid (.lam ((x @@ .bvar 0) @@ (y @@ .bvar 0))) := by
  refine ⟨.lam (.lam ((x @@ .bvar 0) @@ (.bvar 1 @@ .bvar 0))) @@ y,
    WHStep.appL y (lamS_wh1 hx), ?_⟩
  have hx1 : bvarClosed 1 x = true := bvarClosed_mono (Nat.zero_le 1) x hx
  have h2 : subst 0 y (.lam ((x @@ .bvar 0) @@ (.bvar 1 @@ .bvar 0))) =
      .lam ((x @@ .bvar 0) @@ (y @@ .bvar 0)) := by
    simp only [subst, subst_bvarClosed 1 y x hx1, shift_bvarClosed 1 0 y hy]
    rfl
  rw [← h2]
  exact WHStep.beta _ y

theorem lamS_wh3 {x y z : Lam}
    (hx : bvarClosed 0 x = true) (hy : bvarClosed 0 y = true) (_hz : bvarClosed 0 z = true) :
    ∃ m₁ m₂, WHStep (((lamS @@ x) @@ y) @@ z) m₁ ∧
      WHStep m₁ m₂ ∧
      WHStep m₂ ((x @@ z) @@ (y @@ z)) ∧
      (∀ p, m₁ ≠ .lam p) ∧ (∀ p, m₂ ≠ .lam p) := by
  obtain ⟨mid, hs1, hs2⟩ := lamS_wh2 hx hy
  refine ⟨mid @@ z, (.lam ((x @@ .bvar 0) @@ (y @@ .bvar 0))) @@ z,
    WHStep.appL z hs1, WHStep.appL z hs2, ?_,
    (fun _ hp => by cases hp), (fun _ hp => by cases hp)⟩
  have h3 : subst 0 z ((x @@ .bvar 0) @@ (y @@ .bvar 0)) = (x @@ z) @@ (y @@ z) := by
    simp only [subst, subst_bvarClosed 0 z x hx, subst_bvarClosed 0 z y hy, shift_zero]
    rfl
  rw [← h3]
  exact WHStep.beta _ z

theorem lamK_wh2 {x y : Lam} (hx : bvarClosed 0 x = true) :
    ∃ m₁, WHStep ((lamK @@ x) @@ y) m₁ ∧ WHStep m₁ x ∧ (∀ p, m₁ ≠ .lam p) := by
  have h1 : subst 0 x (.lam (.bvar 1)) = .lam x := by
    simp only [subst, shift_bvarClosed 1 0 x hx]
    rfl
  have hx0 : subst 0 y x = x := subst_bvarClosed 0 y x hx
  refine ⟨(.lam x) @@ y, ?_, ?_, fun _ hp => by cases hp⟩
  · rw [← h1]; exact WHStep.appL y (WHStep.beta _ x)
  · have hs2 : WHStep ((.lam x) @@ y) (subst 0 y x) := WHStep.beta x y
    rw [hx0] at hs2
    exact hs2

theorem lamI_wh1 (x : Lam) : WHStep (lamI @@ x) x := by
  have h1 : subst 0 x (.bvar 0) = x := by simp [subst, shift_zero]
  have hs : WHStep (lamI @@ x) (subst 0 x (.bvar 0)) := WHStep.beta (.bvar 0) x
  rw [h1] at hs
  exact hs

/-- Forward simulation: every single `CL(S)` step induces `≥ 1` `β`-steps (`BetaPlus`)! -/
theorem step_to_betaPlus {a b : Term} (h : Step a b) : BetaPlus (toLam a) (toLam b) := by
  induction h with
  | root x y z =>
    obtain ⟨m₁, m₂, hs1, hs2, hs3, _, _⟩ :=
      lamS_wh3 (bvarClosed_toLam x) (bvarClosed_toLam y) (bvarClosed_toLam z)
    exact .head (whStep_to_betaStep hs1)
      (.head (whStep_to_betaStep hs2) (.single (whStep_to_betaStep hs3)))
  | left _ ih => exact betaPlus_appL ih _
  | right _ ih => exact betaPlus_appR _ ih

theorem step_to_betaReduces {a b : Term} (h : Step a b) : BetaReduces (toLam a) (toLam b) :=
  betaReduces_of_betaPlus (step_to_betaPlus h)

theorem reduces_to_betaReduces {a b : Term} (h : Reduces a b) : BetaReduces (toLam a) (toLam b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact betaReduces_trans (step_to_betaReduces hs) ih

theorem stepPlus_to_betaPlus {a b : Term} (h : StepPlus a b) : BetaPlus (toLam a) (toLam b) := by
  induction h with
  | single hs => exact step_to_betaPlus hs
  | head hs _ ih => exact betaPlus_trans (step_to_betaPlus hs) ih

theorem acc_betaPlus {x : Lam} (h : StrongNormalizingBeta x) :
    Acc (fun b a => BetaPlus a b) x := by
  induction h with
  | intro x _ ih =>
    refine Acc.intro x (fun y hy => ?_)
    cases hy with
    | single hs => exact ih _ hs
    | @head _ mid _ h1 hrest => exact Acc.inv (ih mid h1) hrest

/-- If `toLam t` is strongly normalizing in `λβ`, then `t` is strongly normalizing in `CL(S)`. -/
theorem sn_cl_of_sn_toLam {t : Term} (hsn : StrongNormalizingBeta (toLam t)) :
    StrongNormalizing t := by
  have hacc := acc_betaPlus hsn
  suffices hgen : ∀ x, Acc (fun b a => BetaPlus a b) x → ∀ t, x = toLam t → StrongNormalizing t from
    hgen (toLam t) hacc t rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    intro t hxt
    subst hxt
    exact Acc.intro t (fun t' hs => ih (toLam t') (step_to_betaPlus hs) t' rfl)

/-! ## 2. Full Combinatory Logic `CL({S, K, I})` (`CLTerm`) -/

inductive CLTerm where
  | s   : CLTerm
  | k   : CLTerm
  | i   : CLTerm
  | var : Nat → CLTerm
  | app : CLTerm → CLTerm → CLTerm
  deriving DecidableEq, Repr

def ofPureS : Term → CLTerm
  | .s => .s
  | .var v => .var v
  | .app a b => .app (ofPureS a) (ofPureS b)

def clToLam : CLTerm → Lam
  | .s => lamS
  | .k => lamK
  | .i => lamI
  | .var v => .fvar v
  | .app a b => clToLam a @@ clToLam b

theorem clToLam_ofPureS (t : Term) : clToLam (ofPureS t) = toLam t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp [ofPureS, clToLam, toLam, iha, ihb]

theorem bvarClosed_clToLam (m : CLTerm) : bvarClosed 0 (clToLam m) = true := by
  induction m with
  | s => rfl
  | k => rfl
  | i => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp [clToLam, bvarClosed, iha, ihb]

def clHasVar (v : Nat) : CLTerm → Bool
  | .s => false
  | .k => false
  | .i => false
  | .var u => decide (u = v)
  | .app a b => clHasVar v a || clHasVar v b

def clMaxVarBound : CLTerm → Nat
  | .s => 0
  | .k => 0
  | .i => 0
  | .var u => u + 1
  | .app a b => Nat.max (clMaxVarBound a) (clMaxVarBound b)

theorem clHasVar_false_of_ge {v : Nat} {m : CLTerm} (h : clMaxVarBound m ≤ v) :
    clHasVar v m = false := by
  induction m with
  | s => rfl
  | k => rfl
  | i => rfl
  | var u =>
    simp only [clMaxVarBound] at h
    simp only [clHasVar, decide_eq_false_iff_not]
    intro huv; subst huv; exact Nat.lt_irrefl u h
  | app a b iha ihb =>
    simp only [clMaxVarBound] at h
    simp [clHasVar,
      iha (Nat.le_trans (Nat.le_max_left _ _) h),
      ihb (Nat.le_trans (Nat.le_max_right _ _) h)]

theorem hasFVar_clToLam (v : Nat) (m : CLTerm) : hasFVar v (clToLam m) = clHasVar v m := by
  induction m with
  | s => rfl
  | k => rfl
  | i => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp [clToLam, hasFVar, clHasVar, iha, ihb]

inductive CLStep : CLTerm → CLTerm → Prop where
  | s_root (x y z : CLTerm) : CLStep (.app (.app (.app .s x) y) z) (.app (.app x z) (.app y z))
  | k_root (x y : CLTerm)   : CLStep (.app (.app .k x) y) x
  | i_root (x : CLTerm)     : CLStep (.app .i x) x
  | left  {a a' b : CLTerm} : CLStep a a' → CLStep (.app a b) (.app a' b)
  | right {a b b' : CLTerm} : CLStep b b' → CLStep (.app a b) (.app a b')

inductive CLReduces : CLTerm → CLTerm → Prop where
  | refl (a : CLTerm) : CLReduces a a
  | next {a b c : CLTerm} : CLStep a b → CLReduces b c → CLReduces a c

theorem clReduces_trans {a b c : CLTerm} (h1 : CLReduces a b) (h2 : CLReduces b c) :
    CLReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem clReduces_left {a a' : CLTerm} (h : CLReduces a a') (b : CLTerm) :
    CLReduces (.app a b) (.app a' b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.left hs) ih

theorem clHasVar_false_step {v : Nat} {a b : CLTerm} (h : CLStep a b) :
    clHasVar v a = false → clHasVar v b = false := by
  induction h with
  | s_root x y z =>
    simp only [clHasVar, Bool.or_eq_false_iff]
    intro ⟨⟨⟨_, hx⟩, hy⟩, hz⟩
    exact ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
  | k_root x y =>
    simp only [clHasVar, Bool.or_eq_false_iff]
    intro ⟨⟨_, hx⟩, _⟩; exact hx
  | i_root x =>
    simp only [clHasVar, Bool.or_eq_false_iff]
    intro ⟨_, hx⟩; exact hx
  | left _ ih =>
    simp only [clHasVar, Bool.or_eq_false_iff]
    intro ⟨ha, hb⟩; exact ⟨ih ha, hb⟩
  | right _ ih =>
    simp only [clHasVar, Bool.or_eq_false_iff]
    intro ⟨ha, hb⟩; exact ⟨ha, ih hb⟩

theorem clHasVar_false_reduces {v : Nat} {a b : CLTerm} (h : CLReduces a b) :
    clHasVar v a = false → clHasVar v b = false := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (clHasVar_false_step hs hv)

theorem clStep_to_betaPlus {a b : CLTerm} (h : CLStep a b) : BetaPlus (clToLam a) (clToLam b) := by
  induction h with
  | s_root x y z =>
    obtain ⟨m₁, m₂, hs1, hs2, hs3, _, _⟩ :=
      lamS_wh3 (bvarClosed_clToLam x) (bvarClosed_clToLam y) (bvarClosed_clToLam z)
    exact .head (whStep_to_betaStep hs1)
      (.head (whStep_to_betaStep hs2) (.single (whStep_to_betaStep hs3)))
  | k_root x y =>
    obtain ⟨m₁, hs1, hs2, _⟩ := lamK_wh2 (y := clToLam y) (bvarClosed_clToLam x)
    exact .head (whStep_to_betaStep hs1) (.single (whStep_to_betaStep hs2))
  | i_root x =>
    exact .single (whStep_to_betaStep (lamI_wh1 (clToLam x)))
  | left _ ih => exact betaPlus_appL ih _
  | right _ ih => exact betaPlus_appR _ ih

theorem clReduces_to_betaReduces {a b : CLTerm} (h : CLReduces a b) :
    BetaReduces (clToLam a) (clToLam b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact betaReduces_trans (betaReduces_of_betaPlus (clStep_to_betaPlus hs)) ih

theorem ofPureS_step_iff {a b : Term} :
    Step a b → CLStep (ofPureS a) (ofPureS b) := by
  intro h
  induction h with
  | root x y z => exact .s_root _ _ _
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

private theorem clStep_ofPureS_inv {a : Term} {b' : CLTerm}
    (h : CLStep (ofPureS a) b') : ∃ b, b' = ofPureS b ∧ Step a b := by
  induction a generalizing b' with
  | s => cases h
  | var _ => cases h
  | app a1 a2 ih1 ih2 =>
    simp only [ofPureS] at h
    generalize hxa : CLTerm.app (ofPureS a1) (ofPureS a2) = xa at h
    cases h with
    | left hl =>
      injection hxa with h1 h2; subst h2; rw [← h1] at hl
      obtain ⟨b1, rfl, hs1⟩ := ih1 hl
      exact ⟨b1 ⋅ a2, rfl, .left hs1⟩
    | right hr =>
      injection hxa with h1 h2; subst h1; rw [← h2] at hr
      obtain ⟨b2, rfl, hs2⟩ := ih2 hr
      exact ⟨a1 ⋅ b2, rfl, .right hs2⟩
    | k_root _ _ =>
      injection hxa with h1 _
      cases a1 with
      | s => cases h1
      | var _ => cases h1
      | app a11 _ =>
        simp only [ofPureS] at h1
        injection h1 with h11 _
        cases a11 <;> cases h11
    | i_root _ =>
      injection hxa with h1 _
      cases a1 <;> cases h1
    | s_root x0 y0 _ =>
      injection hxa with h1 hz
      cases a1 with
      | s => cases h1
      | var _ => cases h1
      | app a11 y =>
        simp only [ofPureS] at h1
        injection h1 with h2 hy
        cases a11 with
        | s => cases h2
        | var _ => cases h2
        | app a111 x =>
          simp only [ofPureS] at h2
          injection h2 with h3 hx
          cases a111 with
          | var _ => cases h3
          | app _ _ => cases h3
          | s =>
            subst hx; subst hy; subst hz
            exact ⟨(x ⋅ a2) ⋅ (y ⋅ a2), rfl, .root x y a2⟩

theorem clReduces_ofPureS_iff {a b : Term} :
    CLReduces (ofPureS a) (ofPureS b) ↔ Reduces a b := by
  constructor
  · intro h
    suffices hgen : ∀ {x y : CLTerm}, CLReduces x y → ∀ a, x = ofPureS a →
        ∃ b₀, y = ofPureS b₀ ∧ Reduces a b₀ by
      obtain ⟨b₀, heq, hred⟩ := hgen h a rfl
      have hinj : ∀ {u w : Term}, ofPureS u = ofPureS w → u = w := by
        intro u
        induction u with
        | s => intro w hw; cases w <;> simp [ofPureS] at hw; rfl
        | var v => intro w hw; cases w <;> simp [ofPureS] at hw; subst hw; rfl
        | app u1 u2 ih1 ih2 =>
          intro w hw; cases w with
          | s => cases hw
          | var _ => cases hw
          | app w1 w2 =>
            simp only [ofPureS] at hw
            injection hw with h1 h2
            rw [ih1 h1, ih2 h2]
      have hbb0 : b = b₀ := hinj heq
      subst hbb0
      exact hred
    intro x y hxy
    induction hxy with
    | refl _ => intro a ha; exact ⟨a, ha, .refl a⟩
    | next hs _ ih =>
      intro a ha; subst ha
      obtain ⟨a1, rfl, hs1⟩ := clStep_ofPureS_inv hs
      obtain ⟨b₀, hy, hred⟩ := ih a1 rfl
      exact ⟨b₀, hy, .next hs1 hred⟩
  · intro h
    induction h with
    | refl _ => exact .refl _
    | next hs _ ih => exact .next (ofPureS_step_iff hs) ih

/-! ## 3. Key Bridge Theorem: Partial Combinator Reducts `↔` `λ`-Abstraction Reducts -/

def IsPartialComb (t : CLTerm) : Prop :=
  t = .i ∨ t = .k ∨ (∃ a, t = .app .k a) ∨
  t = .s ∨ (∃ a, t = .app .s a) ∨ (∃ a b, t = .app (.app .s a) b)

def IsPartialS (t : Term) : Prop :=
  t = S ∨ (∃ a, t = S ⋅ a) ∨ (∃ a b, t = S ⋅ a ⋅ b)

theorem isPartialS_iff_ofPureS (t : Term) : IsPartialS t ↔ IsPartialComb (ofPureS t) := by
  constructor
  · intro h
    rcases h with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ofPureS a, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ofPureS a, ofPureS b, rfl⟩))))
  · intro h
    cases t with
    | s => exact Or.inl rfl
    | var _ =>
      rcases h with h | h | ⟨_, h⟩ | h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
    | app t1 t2 =>
      cases t1 with
      | s => exact Or.inr (Or.inl ⟨t2, rfl⟩)
      | var _ =>
        rcases h with h | h | ⟨_, h⟩ | h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> simp [ofPureS] at h
      | app t11 t12 =>
        cases t11 with
        | s => exact Or.inr (Or.inr ⟨t12, t2, rfl⟩)
        | var _ =>
          rcases h with h | h | ⟨_, h⟩ | h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> simp [ofPureS] at h
        | app _ _ =>
          rcases h with h | h | ⟨_, h⟩ | h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> simp [ofPureS] at h

def clApps : CLTerm → List CLTerm → CLTerm
  | h, [] => h
  | h, c :: cs => clApps (.app h c) cs

theorem clApps_append (h : CLTerm) (xs ys : List CLTerm) :
    clApps h (xs ++ ys) = clApps (clApps h xs) ys := by
  induction xs generalizing h with
  | nil => rfl
  | cons x rest ih => exact ih (.app h x)

theorem clToLam_clApps (h : CLTerm) (cs : List CLTerm) :
    clToLam (clApps h cs) = apps (clToLam h) (cs.map clToLam) := by
  induction cs generalizing h with
  | nil => rfl
  | cons c rest ih => exact ih (.app h c)

theorem clStep_clApps_of_left {f f' : CLTerm} (hf : CLStep f f') (cs : List CLTerm) :
    CLStep (clApps f cs) (clApps f' cs) := by
  induction cs generalizing f f' with
  | nil => exact hf
  | cons c rest ih => exact ih (.left hf)

theorem cl_spine_decomp (m : CLTerm) :
    (∃ v cs, m = clApps (.var v) cs) ∨
    IsPartialComb m ∨
    (∃ x cs, m = clApps (.app .i x) cs) ∨
    (∃ x y cs, m = clApps (.app (.app .k x) y) cs) ∨
    (∃ x y z cs, m = clApps (.app (.app (.app .s x) y) z) cs) := by
  induction m with
  | s => exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | k => exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
  | i => exact Or.inr (Or.inl (Or.inl rfl))
  | var v => exact Or.inl ⟨v, [], rfl⟩
  | app p q ihp _ =>
    rcases ihp with ⟨v, cs, rfl⟩ | hpart | ⟨x, cs, rfl⟩ | ⟨x, y, cs, rfl⟩ | ⟨x, y, z, cs, rfl⟩
    · refine Or.inl ⟨v, cs ++ [q], ?_⟩; rw [clApps_append]; rfl
    · rcases hpart with rfl | rfl | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨q, [], rfl⟩))
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, q, [], rfl⟩)))
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))))
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, q, rfl⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, q, [], rfl⟩)))
    · refine Or.inr (Or.inr (Or.inl ⟨x, cs ++ [q], ?_⟩)); rw [clApps_append]; rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, cs ++ [q], ?_⟩))); rw [clApps_append]; rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨x, y, z, cs ++ [q], ?_⟩))); rw [clApps_append]; rfl

theorem whStep_not_lam (b y : Lam) : ¬ WHStep (.lam b) y := fun h => by cases h

theorem whStep_det {x y₁ y₂ : Lam} (h1 : WHStep x y₁) (h2 : WHStep x y₂) : y₁ = y₂ := by
  induction h1 generalizing y₂ with
  | beta b a =>
    cases h2 with
    | beta _ _ => rfl
    | appL _ hw => exfalso; exact whStep_not_lam b _ hw
  | @appL l l' c hl ih =>
    cases h2 with
    | beta b _ => exfalso; exact whStep_not_lam b _ hl
    | appL _ hw2 => exact congrArg (· @@ c) (ih hw2)

theorem whStep_apps_left {a a' : Lam} (h : WHStep a a') (cs : List Lam) :
    WHStep (apps a cs) (apps a' cs) := by
  induction cs generalizing a a' with
  | nil => exact h
  | cons c rest ih => exact ih (.appL c h)

theorem apps_app_ne_lam (u w : Lam) (cs : List Lam) (p : Lam) : apps (u @@ w) cs ≠ .lam p := by
  induction cs generalizing u w with
  | nil => intro h; cases h
  | cons c rest ih => exact ih (u @@ w) c

theorem apps_fvar_ne_lam (v : Nat) (cs : List Lam) (p : Lam) : apps (.fvar v) cs ≠ .lam p := by
  cases cs with
  | nil => intro h; cases h
  | cons c rest => exact apps_app_ne_lam (.fvar v) c rest p

theorem whStep_apps_fvar_false (v : Nat) (cs : List Lam) (y : Lam) :
    ¬ WHStep (apps (.fvar v) cs) y := by
  suffices hgen : ∀ f, (∀ p, f ≠ .lam p) → (∀ y, ¬ WHStep f y) →
      ∀ cs z, ¬ WHStep (apps f cs) z from
    hgen (.fvar v) (fun _ h => by cases h) (fun _ h => by cases h) cs y
  intro f hnot hnostep cs
  induction cs generalizing f with
  | nil => exact hnostep
  | cons c rest ih =>
    refine ih (f @@ c) (fun _ h => by cases h) (fun z hz => ?_)
    cases hz with
    | beta p _ => exact hnot p rfl
    | appL _ hw => exact hnostep _ hw

inductive WHReducesN : Nat → Lam → Lam → Prop where
  | zero (a : Lam) : WHReducesN 0 a a
  | succ {n : Nat} {a b c : Lam} : WHStep a b → WHReducesN n b c → WHReducesN (n + 1) a c

theorem whReduces_to_whReducesN {a b : Lam} (h : WHReduces a b) : ∃ n, WHReducesN n a b := by
  induction h with
  | refl a => exact ⟨0, .zero a⟩
  | next hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .succ hs hn⟩

private theorem whReducesN_advance {k : Nat} {x x₁ p : Lam}
    (hs : WHStep x x₁) (hne : ∀ q, x ≠ .lam q) (hr : WHReducesN k x (.lam p)) :
    ∃ k', k = k' + 1 ∧ WHReducesN k' x₁ (.lam p) := by
  cases hr with
  | zero => exfalso; exact hne p rfl
  | @succ k' _ x₂ _ hs' hrest =>
    rw [whStep_det hs hs']
    exact ⟨k', rfl, hrest⟩

/-- **Key Bridge Theorem (`CL({S, K, I}) ↔ λβ`)**:
    `m` reduces in `CL` to a partial combinator application (`I, K, K A, S, S A, S A B`)
    if and only if `clToLam m` reduces in `λβ` to an abstraction `λp`. -/
theorem cl_reduces_partial_iff_lam_reduces_abs (m : CLTerm) :
    (∃ h, CLReduces m h ∧ IsPartialComb h) ↔ (∃ p, BetaReduces (clToLam m) (.lam p)) := by
  constructor
  · intro ⟨h, hred, hpart⟩
    have hm_h : BetaReduces (clToLam m) (clToLam h) := clReduces_to_betaReduces hred
    rcases hpart with rfl | rfl | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · exact ⟨_, hm_h⟩
    · exact ⟨_, hm_h⟩
    · have hk1 : BetaStep (lamK @@ clToLam a) (.lam (clToLam a)) := by
        have hsub : subst 0 (clToLam a) (.lam (.bvar 1)) = .lam (clToLam a) := by
          simp only [subst, shift_bvarClosed 1 0 _ (bvarClosed_clToLam a)]
          rfl
        rw [← hsub]; exact .beta _ _
      exact ⟨_, betaReduces_trans hm_h (.next hk1 (.refl _))⟩
    · exact ⟨_, hm_h⟩
    · exact ⟨_, betaReduces_trans hm_h
        (.next (whStep_to_betaStep (lamS_wh1 (bvarClosed_clToLam a))) (.refl _))⟩
    · obtain ⟨mid, hs1, hs2⟩ := lamS_wh2 (bvarClosed_clToLam a) (bvarClosed_clToLam b)
      exact ⟨_, betaReduces_trans hm_h
        (.next (whStep_to_betaStep hs1) (.next (whStep_to_betaStep hs2) (.refl _)))⟩
  · intro ⟨p, hbeta⟩
    obtain ⟨b₀, hwh, _⟩ := wh_standardization_lam hbeta
    obtain ⟨k, hk⟩ := whReduces_to_whReducesN hwh
    suffices hmain : ∀ (bound : Nat) (k : Nat), k ≤ bound →
        ∀ (m : CLTerm) (b : Lam), WHReducesN k (clToLam m) (.lam b) →
          ∃ h, CLReduces m h ∧ IsPartialComb h from
      hmain k k (Nat.le_refl k) m b₀ hk
    intro bound
    induction bound with
    | zero =>
      intro k hk0 m b hwn
      cases Nat.eq_zero_of_le_zero hk0
      generalize hxm : clToLam m = xm at hwn
      cases hwn with
      | zero =>
        cases m with
        | s => exact ⟨.s, .refl _, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        | k => exact ⟨.k, .refl _, Or.inr (Or.inl rfl)⟩
        | i => exact ⟨.i, .refl _, Or.inl rfl⟩
        | var _ => cases hxm
        | app _ _ => cases hxm
    | succ bound ih =>
      intro k hkle m b hwn
      rcases cl_spine_decomp m with
        ⟨v, cs, rfl⟩ | hpart | ⟨x, cs, rfl⟩ | ⟨x, y, cs, rfl⟩ | ⟨x, y, z, cs, rfl⟩
      · exfalso
        rw [clToLam_clApps] at hwn
        simp only [clToLam] at hwn
        generalize hxv : apps (.fvar v) (cs.map clToLam) = xv at hwn
        generalize hbl : Lam.lam b = bl at hwn
        cases hwn with
        | zero => subst hbl; exact apps_fvar_ne_lam v (cs.map clToLam) b hxv
        | succ hs _ => rw [← hxv] at hs; exact whStep_apps_fvar_false v (cs.map clToLam) _ hs
      · exact ⟨m, .refl m, hpart⟩
      · -- `m = clApps (.app .i x) cs`
        rw [clToLam_clApps] at hwn
        have hs1 : WHStep (apps (lamI @@ clToLam x) (cs.map clToLam))
            (apps (clToLam x) (cs.map clToLam)) :=
          whStep_apps_left (lamI_wh1 (clToLam x)) (cs.map clToLam)
        obtain ⟨k1, rfl, hwn1⟩ :=
          whReducesN_advance hs1 (apps_app_ne_lam lamI (clToLam x) (cs.map clToLam)) hwn
        rw [← clToLam_clApps x cs] at hwn1
        obtain ⟨h, hred, hp⟩ := ih k1 (Nat.le_of_succ_le_succ hkle) (clApps x cs) b hwn1
        exact ⟨h, .next (clStep_clApps_of_left (.i_root x) cs) hred, hp⟩
      · -- `m = clApps (.app (.app .k x) y) cs`
        rw [clToLam_clApps] at hwn
        obtain ⟨m₁, hks1, hks2, hne1⟩ := lamK_wh2 (y := clToLam y) (bvarClosed_clToLam x)
        have hs1 := whStep_apps_left hks1 (cs.map clToLam)
        have hs2 := whStep_apps_left hks2 (cs.map clToLam)
        obtain ⟨k1, rfl, hwn1⟩ :=
          whReducesN_advance hs1 (apps_app_ne_lam (lamK @@ clToLam x) (clToLam y) _) hwn
        have hne_m1 : ∀ q, apps m₁ (cs.map clToLam) ≠ .lam q := by
          cases m₁ with
          | lam q0 => exfalso; exact hne1 q0 rfl
          | app u w => exact apps_app_ne_lam u w _
          | bvar _ => intro q hq; cases cs <;> simp [apps] at hq; exact False.elim (by cases apps_app_ne_lam _ _ _ _ hq)
          | fvar v => exact apps_fvar_ne_lam v _
        obtain ⟨k2, rfl, hwn2⟩ := whReducesN_advance hs2 hne_m1 hwn1
        rw [← clToLam_clApps x cs] at hwn2
        have hle2 : k2 ≤ bound := Nat.le_of_lt (Nat.lt_of_succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hkle))
        obtain ⟨h, hred, hp⟩ := ih k2 hle2 (clApps x cs) b hwn2
        exact ⟨h, .next (clStep_clApps_of_left (.k_root x y) cs) hred, hp⟩
      · -- `m = clApps (.app (.app (.app .s x) y) z) cs`
        rw [clToLam_clApps] at hwn
        obtain ⟨m₁, m₂, hss1, hss2, hss3, hne1, hne2⟩ :=
          lamS_wh3 (bvarClosed_clToLam x) (bvarClosed_clToLam y) (bvarClosed_clToLam z)
        have hs1 := whStep_apps_left hss1 (cs.map clToLam)
        have hs2 := whStep_apps_left hss2 (cs.map clToLam)
        have hs3 := whStep_apps_left hss3 (cs.map clToLam)
        obtain ⟨k1, rfl, hwn1⟩ :=
          whReducesN_advance hs1 (apps_app_ne_lam _ (clToLam z) _) hwn
        have hne_m1 : ∀ q, apps m₁ (cs.map clToLam) ≠ .lam q := by
          cases m₁ with
          | lam q0 => exfalso; exact hne1 q0 rfl
          | app u w => exact apps_app_ne_lam u w _
          | fvar v => exact apps_fvar_ne_lam v _
          | bvar i =>
            cases cs with
            | nil => intro _ hq; cases hq
            | cons _ _ => exact apps_app_ne_lam (.bvar i) _ _
        obtain ⟨k2, rfl, hwn2⟩ := whReducesN_advance hs2 hne_m1 hwn1
        have hne_m2 : ∀ q, apps m₂ (cs.map clToLam) ≠ .lam q := by
          cases m₂ with
          | lam q0 => exfalso; exact hne2 q0 rfl
          | app u w => exact apps_app_ne_lam u w _
          | fvar v => exact apps_fvar_ne_lam v _
          | bvar i =>
            cases cs with
            | nil => intro _ hq; cases hq
            | cons _ _ => exact apps_app_ne_lam (.bvar i) _ _
        obtain ⟨k3, rfl, hwn3⟩ := whReducesN_advance hs3 hne_m2 hwn2
        have hwn3' : WHReducesN k3 (clToLam (clApps (.app (.app x z) (.app y z)) cs)) (.lam b) := by
          rw [clToLam_clApps]; exact hwn3
        have hle3 : k3 ≤ bound := by
          have h1 : k3 + 1 ≤ k3 + 2 := Nat.le_succ _
          have h2 : k3 + 2 ≤ bound := Nat.le_of_succ_le_succ hkle
          exact Nat.le_trans (Nat.le_succ k3) (Nat.le_trans h1 h2)
        obtain ⟨h, hred, hp⟩ := ih k3 hle3 (clApps (.app (.app x z) (.app y z)) cs) b hwn3'
        exact ⟨h, .next (clStep_clApps_of_left (.s_root x y z) cs) hred, hp⟩

/-- Pure-`S` specialization of the Key Bridge Theorem. -/
theorem pureS_reduces_partial_iff_lam_reduces_abs (t : Term) :
    (∃ h, Reduces t h ∧ IsPartialS h) ↔ (∃ p, BetaReduces (toLam t) (.lam p)) := by
  rw [← clToLam_ofPureS t, ← cl_reduces_partial_iff_lam_reduces_abs (ofPureS t)]
  constructor
  · intro ⟨h, hred, hp⟩
    exact ⟨ofPureS h, clReduces_ofPureS_iff.mpr hred, (isPartialS_iff_ofPureS h).mp hp⟩
  · intro ⟨h', hred', hp'⟩
    -- Every reduct of `ofPureS t` has the form `ofPureS h`:
    suffices hclosed : ∀ {x y : CLTerm}, CLReduces x y → ∀ a, x = ofPureS a →
        ∃ b, y = ofPureS b ∧ Reduces a b by
      obtain ⟨h, rfl, hred⟩ := hclosed hred' t rfl
      exact ⟨h, hred, (isPartialS_iff_ofPureS h).mpr hp'⟩
    intro x y hxy
    induction hxy with
    | refl _ => intro a ha; exact ⟨a, ha, .refl a⟩
    | next hs _ ih =>
      intro a ha; subst ha
      obtain ⟨a1, rfl, hs1⟩ := clStep_ofPureS_inv hs
      obtain ⟨b, hy, hred⟩ := ih a1 rfl
      exact ⟨b, hy, .next hs1 hred⟩

/-! ## 4. Definition 35 (`LamOrder`), Free-Variable Closing (`closeFVar`), and Step-Down -/

/-- **Definition 35 of Barendregt et al. (2017, pp. 98–99)**: Order of a `λ`-term. -/
inductive LamOrder : Lam → Nat → Prop where
  | zero {m : Lam} : (∀ p, ¬ BetaReduces m (.lam p)) → LamOrder m 0
  | succ {m p : Lam} {n : Nat} : BetaReduces m (.lam p) → LamOrder p n → LamOrder m (n + 1)

def HasInfiniteLamOrder (m : Lam) : Prop := ∀ n, ¬ LamOrder m n

private theorem betaReduces_lam_inv {p w : Lam} (h : BetaReduces (.lam p) w) :
    ∃ p', w = .lam p' ∧ BetaReduces p p' := by
  suffices hgen : ∀ {x y : Lam}, BetaReduces x y → ∀ p, x = .lam p →
      ∃ p', y = .lam p' ∧ BetaReduces p p' from
    hgen h p rfl
  intro x y hxy
  induction hxy with
  | refl _ => intro p hx; exact ⟨p, hx, .refl p⟩
  | next hs _ ih =>
    intro p hx; subst hx
    cases hs with
    | @lam _ p1 hp1 =>
      obtain ⟨p', hy, hred⟩ := ih p1 rfl
      exact ⟨p', hy, .next hp1 hred⟩

theorem lamOrder_conv {a b : Lam} {n : Nat} (hconv : BetaConv a b) (ha : LamOrder a n) :
    LamOrder b n := by
  induction ha generalizing b with
  | @zero m hno =>
    refine .zero (fun q hbq => ?_)
    have hc : BetaConv m (.lam q) := .trans hconv (betaConv_of_reduces hbq)
    obtain ⟨w, hmw, hqw⟩ := church_rosser_betaConv hc
    obtain ⟨q', rfl, _⟩ := betaReduces_lam_inv hqw
    exact hno q' hmw
  | @succ m p n0 hmp _ ih =>
    have hc : BetaConv (.lam p) b := .trans (.symm (betaConv_of_reduces hmp)) hconv
    obtain ⟨w, hpw, hbw⟩ := church_rosser_betaConv hc
    obtain ⟨q, rfl, hpq⟩ := betaReduces_lam_inv hpw
    exact .succ hbw (ih (betaConv_of_reduces hpq))

theorem lamOrder_unique {m : Lam} {n₁ n₂ : Nat}
    (h1 : LamOrder m n₁) (h2 : LamOrder m n₂) : n₁ = n₂ := by
  induction h1 generalizing n₂ with
  | zero hno =>
    cases h2 with
    | zero _ => rfl
    | succ hmp _ => exfalso; exact hno _ hmp
  | @succ _ p n0 hmp _ ih =>
    cases h2 with
    | zero hno => exfalso; exact hno p hmp
    | @succ _ q _ hmq hq =>
      obtain ⟨w, hpw, hqw⟩ := church_rosser_beta hmp hmq
      obtain ⟨r, rfl, hpr⟩ := betaReduces_lam_inv hpw
      obtain ⟨r2, heq, hqr⟩ := betaReduces_lam_inv hqw
      injection heq with hrr2; subst hrr2
      have hconv_qp : BetaConv q p :=
        .trans (betaConv_of_reduces hqr) (.symm (betaConv_of_reduces hpr))
      exact congrArg Nat.succ (ih (lamOrder_conv hconv_qp hq))

/-- Closing a free variable `z` into bound de Bruijn index `k` (inverse of `subst k (.fvar z)`). -/
def closeFVar (k z : Nat) : Lam → Lam
  | .bvar j => if j < k then .bvar j else .bvar (j + 1)
  | .fvar u => if u = z then .bvar k else .fvar u
  | .app a b => closeFVar k z a @@ closeFVar k z b
  | .lam body => .lam (closeFVar (k + 1) z body)

theorem closeFVar_subst_fvar_cancel (k z : Nat) {p : Lam} (hz : hasFVar z p = false) :
    closeFVar k z (subst k (.fvar z) p) = p := by
  induction p generalizing k with
  | bvar j =>
    simp only [subst]
    by_cases hlt : j < k
    · simp only [if_pos hlt, closeFVar]
    · simp only [if_neg hlt]
      by_cases heq : j = k
      · subst heq
        simp only [↓reduceIte, shift, closeFVar]
      · simp only [if_neg heq, closeFVar]
        have hgt : k < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hgt)
        have hnotlt' : ¬ (j - 1 < k) := by
          cases j with
          | zero => cases hjpos
          | succ j0 =>
            simp only [Nat.succ_sub_one]
            exact fun h' => Nat.not_le_of_lt h' (Nat.le_of_lt_succ hgt)
        simp only [if_neg hnotlt', Nat.sub_add_cancel hjpos]
  | fvar u =>
    simp only [hasFVar, decide_eq_false_iff_not] at hz
    simp only [subst, closeFVar, if_neg hz]
  | app _ _ iha ihb =>
    simp only [hasFVar, Bool.or_eq_false_iff] at hz
    simp [subst, closeFVar, iha k hz.1, ihb k hz.2]
  | lam _ ih =>
    simp only [hasFVar] at hz
    simp [subst, closeFVar, ih (k + 1) hz]

theorem closeFVar_shift (d c k z : Nat) (a : Lam) :
    closeFVar (c + d + k) z (shift d c a) = shift d c (closeFVar (c + k) z a) := by
  induction a generalizing c with
  | bvar j =>
    simp only [shift, closeFVar]
    by_cases hjc : c ≤ j
    · simp only [if_pos hjc]
      by_cases hlt : j < c + k
      · have hlt' : j + d < c + d + k := by
          rw [Nat.add_right_comm c d k]
          exact Nat.add_lt_add_right hlt d
        simp only [if_pos hlt, closeFVar, if_pos hlt', shift, if_pos hjc]
      · have hnotlt' : ¬ (j + d < c + d + k) := by
          rw [Nat.add_right_comm c d k]
          exact fun h' => hlt (Nat.lt_of_add_lt_add_right h')
        have hjc1 : c ≤ j + 1 := Nat.le_trans hjc (Nat.le_succ j)
        have hadd : j + d + 1 = j + 1 + d := Nat.add_right_comm j d 1
        simp only [if_neg hlt, closeFVar, if_neg hnotlt', shift, if_pos hjc1, hadd]
    · have hltc : j < c := Nat.lt_of_not_ge hjc
      have hlt1 : j < c + k := Nat.lt_of_lt_of_le hltc (Nat.le_add_right c k)
      have hlt2 : j < c + d + k :=
        Nat.lt_of_lt_of_le hltc (Nat.le_trans (Nat.le_add_right c d) (Nat.le_add_right _ k))
      simp only [if_neg hjc, closeFVar, if_pos hlt1, if_pos hlt2, shift]
  | fvar u =>
    simp only [shift, closeFVar]
    by_cases huz : u = z
    · simp only [if_pos huz, shift, if_pos (Nat.le_add_right c k)]
      rw [Nat.add_right_comm c k d]
    · simp only [if_neg huz, shift]
  | app _ _ iha ihb =>
    simp [shift, closeFVar, iha c, ihb c]
  | lam _ ih =>
    have heq1 : (c + 1) + d + k = (c + d + k) + 1 := by
      rw [Nat.add_right_comm c 1 d, Nat.add_right_comm (c + d) 1 k]
    have heq2 : (c + 1) + k = (c + k) + 1 := Nat.add_right_comm c 1 k
    simp only [shift, closeFVar, ← heq1, ← heq2]
    exact congrArg Lam.lam (ih (c + 1))

theorem closeFVar_subst (e k z : Nat) (arg body : Lam) :
    closeFVar (e + k) z (subst e arg body) =
      subst e (closeFVar k z arg) (closeFVar (e + k + 1) z body) := by
  induction body generalizing e with
  | bvar j =>
    simp only [subst, closeFVar]
    by_cases hlt : j < e
    · have hlt1 : j < e + k := Nat.lt_of_lt_of_le hlt (Nat.le_add_right e k)
      have hlt2 : j < e + k + 1 := Nat.lt_succ_of_lt hlt1
      simp only [if_pos hlt, if_pos hlt2, closeFVar, if_pos hlt1, subst]
    · simp only [if_neg hlt]
      by_cases heq : j = e
      · subst heq
        have hlt2 : j < j + k + 1 := Nat.lt_succ_of_le (Nat.le_add_right j k)
        simp only [↓reduceIte, if_pos hlt2, subst, if_neg hlt]
        simpa [Nat.zero_add] using closeFVar_shift j 0 k z arg
      · simp only [if_neg heq]
        have hgt : e < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le e) hgt)
        by_cases hlt2 : j < e + k + 1
        · have hlt1 : j - 1 < e + k := by
            cases j with
            | zero => cases hjpos
            | succ j0 => exact Nat.lt_of_succ_lt_succ hlt2
          simp only [if_pos hlt2, closeFVar, if_pos hlt1, subst, if_neg hlt, if_neg heq]
        · have hnotlt1 : ¬ (j - 1 < e + k) := by
            cases j with
            | zero => cases hjpos
            | succ j0 =>
              simp only [Nat.succ_sub_one]
              exact fun h' => hlt2 (Nat.succ_lt_succ h')
          have hnotlt' : ¬ (j + 1 < e) := fun h' => hlt (Nat.lt_trans (Nat.lt_succ_self j) h')
          have hne' : ¬ (j + 1 = e) := fun h' => Nat.not_le_of_lt hgt (by rw [← h']; exact Nat.le_succ j)
          simp only [if_neg hlt2, closeFVar, if_neg hnotlt1, subst, if_neg hnotlt', if_neg hne',
            Nat.sub_add_cancel hjpos, Nat.add_sub_cancel]
  | fvar u =>
    simp only [subst, closeFVar]
    by_cases huz : u = z
    · have hnotlt : ¬ (e + k + 1 < e) := fun h' =>
        Nat.not_le_of_lt h' (Nat.le_trans (Nat.le_add_right e k) (Nat.le_succ _))
      have hne : ¬ (e + k + 1 = e) := fun h' =>
        Nat.not_le_of_lt (Nat.lt_succ_of_le (Nat.le_add_right e k)) (Nat.le_of_eq h')
      simp only [if_pos huz, subst, if_neg hnotlt, if_neg hne, Nat.add_sub_cancel]
    · simp only [if_neg huz, subst]
  | app _ _ iha ihb =>
    simp [subst, closeFVar, iha e, ihb e]
  | lam _ ih =>
    have heq1 : (e + 1) + k = (e + k) + 1 := Nat.add_right_comm e 1 k
    simp only [subst, closeFVar]
    apply congrArg Lam.lam
    rw [← heq1]
    exact ih (e + 1)

theorem betaStep_closeFVar (k z : Nat) {a b : Lam} (h : BetaStep a b) :
    BetaStep (closeFVar k z a) (closeFVar k z b) := by
  induction h generalizing k with
  | beta body arg =>
    simp only [closeFVar]
    have hc := closeFVar_subst 0 k z arg body
    simp only [Nat.zero_add] at hc
    rw [hc]
    exact .beta _ _
  | appL _ ih => exact .appL (ih k)
  | appR _ ih => exact .appR (ih k)
  | lam _ ih => exact .lam (ih (k + 1))

theorem betaReduces_closeFVar (k z : Nat) {a b : Lam} (h : BetaReduces a b) :
    BetaReduces (closeFVar k z a) (closeFVar k z b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (betaStep_closeFVar k z hs) ih

theorem lamOrder_open_fresh {z : Nat} :
    ∀ (n k : Nat) {p : Lam}, hasFVar z p = false →
      (LamOrder p n ↔ LamOrder (subst k (.fvar z) p) n) := by
  intro n
  induction n with
  | zero =>
    intro k p hz
    constructor
    · intro hp0
      cases hp0 with
      | zero hno =>
        refine .zero (fun q' hred' => ?_)
        have hc := betaReduces_closeFVar k z hred'
        rw [closeFVar_subst_fvar_cancel k z hz] at hc
        exact hno (closeFVar (k + 1) z q') hc
    · intro hsub0
      cases hsub0 with
      | zero hno =>
        refine .zero (fun q hred => ?_)
        exact hno (subst (k + 1) (.fvar z) q) (betaReduces_subst_body k (.fvar z) hred)
  | succ n ih =>
    intro k p hz
    constructor
    · intro hpn
      cases hpn with
      | @succ _ q _ hpq hq =>
        have hzq : hasFVar z q = false := by
          simpa [hasFVar] using hasFVar_false_betaReduces hpq hz
        exact .succ (betaReduces_subst_body k (.fvar z) hpq) ((ih (k + 1) hzq).mp hq)
    · intro hsubn
      cases hsubn with
      | @succ _ q' _ hpq' hq' =>
        have hc : BetaReduces p (.lam (closeFVar (k + 1) z q')) := by
          have h1 := betaReduces_closeFVar k z hpq'
          rw [closeFVar_subst_fvar_cancel k z hz] at h1
          exact h1
        let q := closeFVar (k + 1) z q'
        have hzq : hasFVar z q = false := by
          simpa [hasFVar] using hasFVar_false_betaReduces hc hz
        have hp_subq : BetaReduces (subst k (.fvar z) p) (.lam (subst (k + 1) (.fvar z) q)) :=
          betaReduces_subst_body k (.fvar z) hc
        obtain ⟨w, hw1, hw2⟩ := church_rosser_beta hpq' hp_subq
        obtain ⟨r1, rfl, hq'_r⟩ := betaReduces_lam_inv hw1
        obtain ⟨r2, heq, hsubq_r⟩ := betaReduces_lam_inv hw2
        injection heq with hr12; subst hr12
        have hconv : BetaConv q' (subst (k + 1) (.fvar z) q) :=
          .trans (betaConv_of_reduces hq'_r) (.symm (betaConv_of_reduces hsubq_r))
        have hsubq_ord : LamOrder (subst (k + 1) (.fvar z) q) n := lamOrder_conv hconv hq'
        exact .succ hc ((ih (k + 1) hzq).mpr hsubq_ord)

/-- **Example 36(iv) of Barendregt et al. (p. 99)**:
    If `m` reduces to an abstraction and `z` is fresh for `m`, then
    `m` has order `n + 1` iff `m z` has order `n`! -/
theorem lamOrder_succ_iff_app_fvar {m : Lam} {z n : Nat}
    (hz : hasFVar z m = false) (habs : ∃ p, BetaReduces m (.lam p)) :
    LamOrder m (n + 1) ↔ LamOrder (m @@ .fvar z) n := by
  obtain ⟨p, hmp⟩ := habs
  have hzp : hasFVar z p = false := by
    simpa [hasFVar] using hasFVar_false_betaReduces hmp hz
  have hm_sub : BetaReduces (m @@ .fvar z) (subst 0 (.fvar z) p) :=
    betaReduces_trans (betaReduces_appL hmp (.fvar z)) (.next (.beta p (.fvar z)) (.refl _))
  constructor
  · intro hm_ord
    cases hm_ord with
    | @succ _ p₁ _ hmp₁ hp₁ =>
      obtain ⟨w, hw1, hw2⟩ := church_rosser_beta hmp₁ hmp
      obtain ⟨r1, rfl, hp1_r⟩ := betaReduces_lam_inv hw1
      obtain ⟨r2, heq, hp_r⟩ := betaReduces_lam_inv hw2
      injection heq with hr12; subst hr12
      have hp_ord : LamOrder p n :=
        lamOrder_conv (.trans (betaConv_of_reduces hp1_r) (.symm (betaConv_of_reduces hp_r))) hp₁
      have hsub_ord : LamOrder (subst 0 (.fvar z) p) n := (lamOrder_open_fresh n 0 hzp).mp hp_ord
      exact lamOrder_conv (.symm (betaConv_of_reduces hm_sub)) hsub_ord
  · intro happ_ord
    have hsub_ord : LamOrder (subst 0 (.fvar z) p) n :=
      lamOrder_conv (betaConv_of_reduces hm_sub) happ_ord
    exact .succ hmp ((lamOrder_open_fresh n 0 hzp).mpr hsub_ord)

/-! ## 5. Curry–Feys Definition 37 & Proof of Conjecture 40 (Full `CL` and Pure `CL(S)`) -/

/-- **Curry–Feys Unconsumed Dummy Variables (Definition 37 at order `0`)**:
    For every list of dummy variables `ys` not occurring in `m`, every reduct of `m y₁ ... yᵣ`
    has the form `n' y₁ ... yᵣ` with `m →* n'`. -/
def NeverConsumesDummyVars (m : CLTerm) : Prop :=
  ∀ (ys : List Nat), (∀ y ∈ ys, clHasVar y m = false) →
    ∀ {n : CLTerm}, CLReduces (clApps m (ys.map .var)) n →
      ∃ n', n = clApps n' (ys.map .var) ∧ CLReduces m n'

private theorem cl_unconsumed_step_arg {a b : CLTerm} (hred : CLReduces a b) :
    ∀ (f : CLTerm) (u : Nat),
      ¬ CLReduces f .i →
      (∀ p, ¬ CLReduces f (.app .k p)) →
      (∀ p q, ¬ CLReduces f (.app (.app .s p) q)) →
      a = .app f (.var u) →
      ∃ f', b = .app f' (.var u) ∧ CLReduces f f' := by
  induction hred with
  | refl _ =>
    intro f u _ _ _ ha; exact ⟨f, ha, .refl f⟩
  | @next _ a1 _ hs _ ih =>
    intro f u hnoi hnok hnos ha
    subst ha
    cases hs with
    | i_root _ => exfalso; exact hnoi (.refl _)
    | k_root _ _ => exfalso; exact hnok _ (.refl _)
    | s_root _ _ _ => exfalso; exact hnos _ _ (.refl _)
    | @left _ f1 _ hf =>
      obtain ⟨f', hb, hf'⟩ := ih f1 u
        (fun hr => hnoi (.next hf hr))
        (fun p hr => hnok p (.next hf hr))
        (fun p q hr => hnos p q (.next hf hr))
        rfl
      exact ⟨f', hb, .next hf hf'⟩
    | right hr => cases hr

/-- Equivalence between Curry–Feys Definition 37 (order `0`) and absence of partial combinator reducts! -/
theorem neverConsumesDummyVars_iff_no_partial (m : CLTerm) :
    NeverConsumesDummyVars m ↔ (∀ h, CLReduces m h → ¬ IsPartialComb h) := by
  constructor
  · intro hcf h hred hpart
    let v0 := clMaxVarBound m
    have hv0 : clHasVar v0 m = false := clHasVar_false_of_ge (Nat.le_refl _)
    have hv1 : clHasVar (v0 + 1) m = false := clHasVar_false_of_ge (Nat.le_succ v0)
    have hv2 : clHasVar (v0 + 2) m = false := clHasVar_false_of_ge (Nat.le_add_right v0 2)
    rcases hpart with rfl | rfl | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · -- `h = .i`: `m v0 →* .var v0`
      have hr : CLReduces (clApps m ([v0].map .var)) (.var v0) :=
        clReduces_trans (clReduces_left hred (.var v0)) (.next (.i_root _) (.refl _))
      obtain ⟨n', hn', _⟩ := hcf [v0] (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hnil; exact hv0; cases hnil) hr
      cases hn'
    · -- `h = .k`: `m v0 (v0+1) →* .var v0`
      have hr : CLReduces (clApps m ([v0, v0 + 1].map .var)) (.var v0) :=
        clReduces_trans (clReduces_left (clReduces_left hred _) _) (.next (.k_root _ _) (.refl _))
      obtain ⟨n', hn', _⟩ := hcf [v0, v0 + 1] (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy1
        · exact hv0
        · rcases List.mem_cons.mp hy1 with rfl | hnil; exact hv1; cases hnil) hr
      cases hn'
    · -- `h = .app .k a`: `m v0 →* a`, where `clHasVar v0 a = false`!
      have hr : CLReduces (clApps m ([v0].map .var)) a :=
        clReduces_trans (clReduces_left hred _) (.next (.k_root _ _) (.refl _))
      obtain ⟨n', hn', _⟩ := hcf [v0] (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hnil; exact hv0; cases hnil) hr
      have hva : clHasVar v0 (.app .k a) = false := clHasVar_false_reduces hred hv0
      simp only [clHasVar, Bool.false_or] at hva
      rw [hn'] at hva
      simp [clApps, clHasVar] at hva
    · -- `h = .s`: `m v0 (v0+1) (v0+2) →* (v0 (v0+2)) ((v0+1) (v0+2))`
      have hr : CLReduces (clApps m ([v0, v0 + 1, v0 + 2].map .var))
          (.app (.app (.var v0) (.var (v0 + 2))) (.app (.var (v0 + 1)) (.var (v0 + 2)))) :=
        clReduces_trans (clReduces_left (clReduces_left (clReduces_left hred _) _) _)
          (.next (.s_root _ _ _) (.refl _))
      obtain ⟨n', hn', _⟩ := hcf [v0, v0 + 1, v0 + 2] (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy1
        · exact hv0
        · rcases List.mem_cons.mp hy1 with rfl | hy2
          · exact hv1
          · rcases List.mem_cons.mp hy2 with rfl | hnil; exact hv2; cases hnil) hr
      simp only [List.map, clApps] at hn'
      injection hn' with _ hright
      cases hright
    · -- `h = .app .s a`: `m v0 (v0+1) →* (a (v0+1)) (v0 (v0+1))`
      have hr : CLReduces (clApps m ([v0, v0 + 1].map .var))
          (.app (.app a (.var (v0 + 1))) (.app (.var v0) (.var (v0 + 1)))) :=
        clReduces_trans (clReduces_left (clReduces_left hred _) _) (.next (.s_root _ _ _) (.refl _))
      obtain ⟨n', hn', _⟩ := hcf [v0, v0 + 1] (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy1
        · exact hv0
        · rcases List.mem_cons.mp hy1 with rfl | hnil; exact hv1; cases hnil) hr
      simp only [List.map, clApps] at hn'
      injection hn' with _ hright
      cases hright
    · -- `h = .app (.app .s a) b`: `m v0 →* (a v0) (b v0)`
      have hr : CLReduces (clApps m ([v0].map .var)) (.app (.app a (.var v0)) (.app b (.var v0))) :=
        clReduces_trans (clReduces_left hred _) (.next (.s_root _ _ _) (.refl _))
      obtain ⟨n', hn', _⟩ := hcf [v0] (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hnil; exact hv0; cases hnil) hr
      simp only [List.map, clApps] at hn'
      injection hn' with _ hright
      cases hright
  · intro hno ys _
    -- Prove for ALL `ys : List Nat` by reverse list induction!
    suffices hgen : ∀ (zs : List CLTerm), (∀ z ∈ zs, ∃ u, z = .var u) →
        ∀ {n : CLTerm}, CLReduces (clApps m zs) n → ∃ n', n = clApps n' zs ∧ CLReduces m n' by
      intro n hn
      exact hgen (ys.map .var) (fun z hz => by
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hz
        exact ⟨u, rfl⟩) hn
    intro zs
    have hrev : ∀ (r : List CLTerm),
        ((∀ z ∈ r.reverse, ∃ u, z = .var u) →
          ∀ {n : CLTerm}, CLReduces (clApps m r.reverse) n →
            ∃ n', n = clApps n' r.reverse ∧ CLReduces m n') := by
      intro r
      induction r with
      | nil =>
        intro _ n hn
        exact ⟨n, rfl, hn⟩
      | cons last rev_init ih =>
        intro hvars n hn
        simp only [List.reverse_cons] at hvars hn ⊢
        obtain ⟨u, rfl⟩ := hvars last (by simp)
        have hvars_init : ∀ z ∈ rev_init.reverse, ∃ u, z = .var u :=
          fun z hz => hvars z (by simp [hz])
        rw [clApps_append] at hn
        simp only [clApps] at hn
        generalize hinit : rev_init.reverse = init at ih hvars_init hn ⊢
        have hnoi : ¬ CLReduces (clApps m init) .i := by
          intro hr; obtain ⟨m', heq, hm'⟩ := ih hvars_init hr
          cases init with
          | nil =>
            simp only [clApps] at heq
            subst heq
            exact hno .i hm' (Or.inl rfl)
          | cons c1 rest1 =>
            have : ∀ (f a : CLTerm) (as : List CLTerm), clApps (.app f a) as ≠ .i := by
              intro f a as; induction as generalizing f a with
              | nil => intro h; cases h
              | cons d ds ihd => exact ihd (.app f a) d
            exact this m' c1 rest1 heq.symm
        have hnok : ∀ p, ¬ CLReduces (clApps m init) (.app .k p) := by
          intro p hr; obtain ⟨m', heq, hm'⟩ := ih hvars_init hr
          cases init with
          | nil =>
            simp only [clApps] at heq
            subst heq
            exact hno (.app .k p) hm' (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
          | cons c1 rest1 =>
            cases rest1 with
            | nil =>
              simp only [clApps] at heq
              injection heq with hm'k _
              subst hm'k
              exact hno .k hm' (Or.inr (Or.inl rfl))
            | cons c2 rest2 =>
              have : ∀ (f a b : CLTerm) (as : List CLTerm), clApps (.app (.app f a) b) as ≠ .app .k p := by
                intro f a b as; induction as generalizing f a b with
                | nil => intro h; injection h with h1 _; cases h1
                | cons d ds ihd => exact ihd (.app f a) b d
              exact this m' c1 c2 rest2 heq.symm
        have hnos : ∀ p q, ¬ CLReduces (clApps m init) (.app (.app .s p) q) := by
          intro p q hr; obtain ⟨m', heq, hm'⟩ := ih hvars_init hr
          cases init with
          | nil =>
            simp only [clApps] at heq
            subst heq
            exact hno (.app (.app .s p) q) hm'
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, q, rfl⟩)))))
          | cons c1 rest1 =>
            cases rest1 with
            | nil =>
              simp only [clApps] at heq
              injection heq with hm's _
              subst hm's
              exact hno (.app .s p) hm'
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))))
            | cons c2 rest2 =>
              cases rest2 with
              | nil =>
                simp only [clApps] at heq
                injection heq with h1 _
                injection h1 with hm's _
                subst hm's
                exact hno .s hm' (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              | cons c3 rest3 =>
                have : ∀ (f a b c : CLTerm) (as : List CLTerm),
                    clApps (.app (.app (.app f a) b) c) as ≠ .app (.app .s p) q := by
                  intro f a b c as; induction as generalizing f a b c with
                  | nil => intro h; injection h with h1 _; injection h1 with h2 _; cases h2
                  | cons d ds ihd => exact ihd (.app f a) b c d
                exact this m' c1 c2 c3 rest3 heq.symm
        obtain ⟨f', hnf', hf'⟩ := cl_unconsumed_step_arg hn (clApps m init) u hnoi hnok hnos rfl
        obtain ⟨n', hf'n', hmn'⟩ := ih hvars_init hf'
        refine ⟨n', ?_, hmn'⟩
        rw [clApps_append, ← hf'n']
        exact hnf'
    simpa [List.reverse_reverse] using hrev zs.reverse

/-- **Order of a `CL` Term (`CLOrder`, Definition 37 of Barendregt et al., p. 99)**:
    - Order `0`: `NeverConsumesDummyVars m` (equivalently, never reduces to a partial combinator).
    - Order `n + 1`: `m` reduces to a partial combinator, and for fresh `z`, `m z` has order `n`. -/
inductive CLOrder : CLTerm → Nat → Prop where
  | zero {m : CLTerm} : NeverConsumesDummyVars m → CLOrder m 0
  | succ {m : CLTerm} {n : Nat} (z : Nat) :
      clHasVar z m = false →
      (∃ h, CLReduces m h ∧ IsPartialComb h) →
      CLOrder (.app m (.var z)) n →
      CLOrder m (n + 1)

def HasInfiniteCLOrder (m : CLTerm) : Prop := ∀ n, ¬ CLOrder m n

/-- **THEOREM (Conjecture 40 of Barendregt, Endrullis, Klop, and Waldmann 2017, p. 102 — Full `CL`)**:
    For every Combinatory Logic term `M ∈ Ter(CL({S, K, I}))` and every `n ∈ ℕ`,
    `order_CL(M) = n ⇐⇒ order_λ((M)_λ) = n`! -/
theorem conjecture_40_full_cl (m : CLTerm) (n : Nat) :
    CLOrder m n ↔ LamOrder (clToLam m) n := by
  induction n generalizing m with
  | zero =>
    constructor
    · intro hc0
      cases hc0 with
      | zero hcf =>
        have hno := (neverConsumesDummyVars_iff_no_partial m).mp hcf
        refine .zero (fun p hbeta => ?_)
        obtain ⟨h, hred, hp⟩ := (cl_reduces_partial_iff_lam_reduces_abs m).mpr ⟨p, hbeta⟩
        exact hno h hred hp
    · intro hl0
      cases hl0 with
      | zero hno_lam =>
        refine .zero ((neverConsumesDummyVars_iff_no_partial m).mpr (fun h hred hp => ?_))
        obtain ⟨p, hbeta⟩ := (cl_reduces_partial_iff_lam_reduces_abs m).mp ⟨h, hred, hp⟩
        exact hno_lam p hbeta
  | succ n ih =>
    constructor
    · intro hcn
      cases hcn with
      | succ z hz hpart hmz =>
        have habs := (cl_reduces_partial_iff_lam_reduces_abs m).mp hpart
        have hz_lam : hasFVar z (clToLam m) = false := by rw [hasFVar_clToLam]; exact hz
        have hlam_mz : LamOrder (clToLam m @@ .fvar z) n := (ih (.app m (.var z))).mp hmz
        exact (lamOrder_succ_iff_app_fvar hz_lam habs).mpr hlam_mz
    · intro hln
      have habs : ∃ p, BetaReduces (clToLam m) (.lam p) := by
        cases hln with
        | succ hmp _ => exact ⟨_, hmp⟩
      have hpart := (cl_reduces_partial_iff_lam_reduces_abs m).mpr habs
      let z := clMaxVarBound m
      have hz : clHasVar z m = false := clHasVar_false_of_ge (Nat.le_refl _)
      have hz_lam : hasFVar z (clToLam m) = false := by rw [hasFVar_clToLam]; exact hz
      have hlam_mz : LamOrder (clToLam (.app m (.var z))) n :=
        (lamOrder_succ_iff_app_fvar hz_lam habs).mp hln
      exact .succ z hz hpart ((ih (.app m (.var z))).mpr hlam_mz)

theorem clOrder_unique {m : CLTerm} {n₁ n₂ : Nat}
    (h1 : CLOrder m n₁) (h2 : CLOrder m n₂) : n₁ = n₂ :=
  lamOrder_unique ((conjecture_40_full_cl m n₁).mp h1) ((conjecture_40_full_cl m n₂).mp h2)

/-- **Infinite-Order Preservation (Conjecture 40 for `order = ∞`)**:
    `M` has infinite order in `CL({S, K, I})` iff `(M)_λ` has infinite order in `λβ`. -/
theorem conjecture_40_infinite_order (m : CLTerm) :
    HasInfiniteCLOrder m ↔ HasInfiniteLamOrder (clToLam m) := by
  constructor
  · intro hinf n hln; exact hinf n ((conjecture_40_full_cl m n).mpr hln)
  · intro hinf n hcn; exact hinf n ((conjecture_40_full_cl m n).mp hcn)

/-! ### Pure `CL(S)` Order (`PureSCLOrder`) and Visser–van Oostrom Ceiling (`order ≤ 3`) -/

inductive PureSCLOrder : Term → Nat → Prop where
  | zero {m : Term} : (∀ h, Reduces m h → ¬ IsPartialS h) → PureSCLOrder m 0
  | succ {m : Term} {n : Nat} (z : Nat) :
      hasVar z m = false →
      (∃ h, Reduces m h ∧ IsPartialS h) →
      PureSCLOrder (m ⋅ .var z) n →
      PureSCLOrder m (n + 1)

/-- **THEOREM (Conjecture 40 on Pure-`S` Terms `Ter(CL(S))`)**:
    For every `M ∈ Ter(CL(S))` and `n ∈ ℕ`, `PureSCLOrder M n ↔ LamOrder (toLam M) n`. -/
theorem conjecture_40_pure_s (m : Term) (n : Nat) :
    PureSCLOrder m n ↔ LamOrder (toLam m) n := by
  induction n generalizing m with
  | zero =>
    constructor
    · intro hs0
      cases hs0 with
      | zero hno =>
        refine .zero (fun p hbeta => ?_)
        obtain ⟨h, hred, hp⟩ := (pureS_reduces_partial_iff_lam_reduces_abs m).mpr ⟨p, hbeta⟩
        exact hno h hred hp
    · intro hl0
      cases hl0 with
      | zero hno_lam =>
        refine .zero (fun h hred hp => ?_)
        obtain ⟨p, hbeta⟩ := (pureS_reduces_partial_iff_lam_reduces_abs m).mp ⟨h, hred, hp⟩
        exact hno_lam p hbeta
  | succ n ih =>
    constructor
    · intro hsn
      cases hsn with
      | succ z hz hpart hmz =>
        have habs := (pureS_reduces_partial_iff_lam_reduces_abs m).mp hpart
        have hz_lam : hasFVar z (toLam m) = false := by rw [hasFVar_toLam]; exact hz
        exact (lamOrder_succ_iff_app_fvar hz_lam habs).mpr ((ih (m ⋅ .var z)).mp hmz)
    · intro hln
      have habs : ∃ p, BetaReduces (toLam m) (.lam p) := by
        cases hln with
        | succ hmp _ => exact ⟨_, hmp⟩
      have hpart := (pureS_reduces_partial_iff_lam_reduces_abs m).mpr habs
      let z := maxVarBound m
      have hz : hasVar z m = false := hasVar_false_of_ge (Nat.le_refl _)
      have hz_lam : hasFVar z (toLam m) = false := by rw [hasFVar_toLam]; exact hz
      exact .succ z hz hpart
        ((ih (m ⋅ .var z)).mpr ((lamOrder_succ_iff_app_fvar hz_lam habs).mp hln))

/-! ### Visser–van Oostrom `order ≤ 3` Bound on `CL(S)` and `(Ter(CL(S)))_λ` -/

private def inVisserT : Term → Bool
  | .s => false
  | .var _ => true
  | .app _ r => inVisserT r

private def inVisserT2 : Term → Bool
  | .app p q => inVisserT p && inVisserT q
  | _ => false

private def inVisserT3 : Term → Bool
  | .app (.app p q) r => inVisserT p && inVisserT q && inVisserT r
  | _ => false

private theorem inVisserT_step {a b : Term} (h : Step a b) :
    inVisserT a = true → inVisserT b = true := by
  induction h with
  | root _ _ _ => simp [inVisserT]
  | left _ _ => simp [inVisserT]
  | right _ ih => simp [inVisserT]; exact ih

private theorem inVisserT2_step {a b : Term} (h : Step a b) :
    inVisserT2 a = true → inVisserT2 b = true := by
  cases h with
  | root _ _ _ => simp [inVisserT2, inVisserT]
  | left hl =>
    simp only [inVisserT2, Bool.and_eq_true]
    intro ⟨h1, h2⟩; exact ⟨inVisserT_step hl h1, h2⟩
  | right hr =>
    simp only [inVisserT2, Bool.and_eq_true]
    intro ⟨h1, h2⟩; exact ⟨h1, inVisserT_step hr h2⟩

private theorem inVisserT3_step {a b : Term} (h : Step a b) :
    inVisserT3 a = true → inVisserT3 b = true := by
  cases h with
  | root _ _ _ =>
    simp only [inVisserT3, inVisserT, Bool.and_eq_true]
    intro ⟨⟨hx, _⟩, hz⟩; exact ⟨⟨hx, hz⟩, hz⟩
  | @left l l' r hl =>
    cases l with
    | s => cases hl
    | var _ => cases hl
    | app p q =>
      simp only [inVisserT3, Bool.and_eq_true]
      intro ⟨⟨hp, hq⟩, hr⟩
      have h2 : inVisserT2 l' = true := inVisserT2_step hl (by simp [inVisserT2, hp, hq])
      cases l' with
      | s => cases h2
      | var _ => cases h2
      | app p' q' =>
        simp only [inVisserT2, Bool.and_eq_true] at h2
        exact (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr h2, hr⟩
  | @right l _ _ hr =>
    cases l with
    | s => intro h3; cases h3
    | var _ => intro h3; cases h3
    | app p q =>
      simp only [inVisserT3, Bool.and_eq_true]
      intro ⟨hpq, hr0⟩; exact ⟨hpq, inVisserT_step hr hr0⟩

private theorem inVisserT3_reduces {a b : Term} (h : Reduces a b) :
    inVisserT3 a = true → inVisserT3 b = true := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (inVisserT3_step hs hv)

theorem m_xyz_order_zero (m : Term) (x y z : Nat) :
    PureSCLOrder (m ⋅ .var x ⋅ .var y ⋅ .var z) 0 := by
  refine .zero (fun h hred hpart => ?_)
  have hend : inVisserT3 h = true := inVisserT3_reduces hred rfl
  rcases hpart with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;> cases hend

theorem pureS_order_le_three {m : Term} {n : Nat} (h : PureSCLOrder m n) : n ≤ 3 := by
  cases h with
  | zero _ => exact Nat.zero_le 3
  | succ x _ _ h1 =>
    cases h1 with
    | zero _ => exact by decide
    | succ y _ _ h2 =>
      cases h2 with
      | zero _ => exact by decide
      | succ z _ _ h3 =>
        have h0 := m_xyz_order_zero m x y z
        have heq : _ = 0 :=
          lamOrder_unique ((conjecture_40_pure_s _ _).mp h3) ((conjecture_40_pure_s _ 0).mp h0)
        subst heq
        exact Nat.le_refl 3

theorem toLam_order_le_three {m : Term} {n : Nat} (h : LamOrder (toLam m) n) : n ≤ 3 :=
  pureS_order_le_three ((conjecture_40_pure_s m n).mpr h)

end FormalLambdaConjectures
