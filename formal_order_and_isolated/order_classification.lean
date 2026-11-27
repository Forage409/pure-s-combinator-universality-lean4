import formal_algebra.all_algebra_open_problems
import formal_census_and_minimality.minimality_theorems

/-!
# Exact Order `{0, 1, 2, 3}` Classification and Minimal `S`-Algebras for `CL(S)`

Constructive, axiom-free Lean 4.33.1 formalization (`namespace FormalOrderAndIsolated`) resolving
the exact regularity and minimal `S`-algebra classification of the Order `{0, 1, 2, 3}` hierarchy
from Section 5.5 and Appendix A.3 of Barendregt, Endrullis, Klop, and Waldmann (2018),
*Dance of the Starlings*:

1. **Universal Open Solvability Algebra (`evalHNOpen`, `.var _ ↦ .hn34`)**:
   - Maps every variable `.var k` to `.hn34` in the 35-state `S`-algebra `A_HN`, proving that for
     **every** open or closed pure-`S` term `t`, `t` reduces to an `S`-headed HNF (`S`, `S ⋅ a`, or `S ⋅ a ⋅ b`)
     **iff** `evalHNOpen t ≠ .hn34` (`open_hasSHeadHNF_iff`).
2. **Curry–Feys Order (`Definition 37`) & Single-Variable Consumption (`Definition 21`)**:
   - Formalizes `IsDummyTail`, `HasOrderAtMost`, and `HasExactOrder`, proving for **every** open or
     closed pure-`S` term `m` that `HasExactOrder m k ↔ orderOfStateHN (evalHNOpen m) = k` with
     `k ∈ {0, 1, 2, 3}` (`visser_van_oostrom_exact_order_exhaustion`), and invariance under `=S`.
   - Partitions `StateHN` (`35 = 1 + 11 + 17 + 6`) via the nilpotent operator `tauHN q = deltaHN q .hn34`
     (`tauHN^3 q = .hn34` for all `q`).
3. **Uniqueness of Order 3 (`rightComb`) & Sharp Minimal Order Witnesses**:
   - `closed_order3_iff_rightComb`: A closed pure-`S` combinator `t` has Order `3` **iff**
     `t = rightComb (leaves t)` (`S`, `S(S)`, `S(S(S))`, ...)!
   - Exact minimal pure-`S` witnesses: Order `3` at size `1` (`S`), Order `2` uniquely at size `3`
     (`S ⋅ S ⋅ S`, resolving the p. 90 prose slip vs. Example 41(ii)), Order `1` uniquely at size `5`
     (`S ⋅ (S ⋅ S ⋅ S) ⋅ S`), and Order `0` at size `8` (`15` witnesses).
4. **Exact Myhill–Nerode Minimal `S`-Algebras (`35`, `35`, `12`, `3` States)**:
   - Full `Order : Ter_closed → {0, 1, 2, 3}`, `{Order = 0}`, `{Order = 1}`, and `{Order ≥ 1}`
     have exact minimal deterministic bottom-up tree automaton size **35** (`StateHN`).
   - `{Order = 2}` and `{Order ≥ 2}` share the exact **12-state** minimal quotient `S`-algebra `StateOrd2`.
   - `{Order = 3}` has the exact **3-state** minimal quotient `S`-algebra `StateOrd3` (`.rcS | .rcTower | .nonRC`).

Verified with zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`, and zero `Classical.choice`.
-/

namespace FormalOrderAndIsolated

open FormalAlgebra

abbrev Term := FormalAlgebra.Term
abbrev S : Term := FormalAlgebra.S
abbrev Step := FormalAlgebra.Step
abbrev StepPlus := FormalAlgebra.StepPlus
abbrev Reduces := FormalAlgebra.Reduces
abbrev ConvS := FormalAlgebra.ConvS
abbrev HeadStep := FormalAlgebra.HeadStep
abbrev HeadReduces := FormalAlgebra.HeadReduces
abbrev leaves := FormalAlgebra.leaves
abbrev noVars := FormalAlgebra.noVars
abbrev hasVar := FormalAlgebra.hasVar
abbrev subst := FormalAlgebra.subst
abbrev spineLen := FormalAlgebra.spineLen
abbrev headLeaf := FormalAlgebra.headLeaf
abbrev IsNormalForm := FormalAlgebra.IsNormalForm
abbrev HasNormalForm := FormalAlgebra.HasNormalForm
abbrev StrongNormalizing := FormalAlgebra.StrongNormalizing
abbrev HasHNF := FormalAlgebra.HasHNF
abbrev Ctx := FormalAlgebra.Ctx
abbrev plugCtx := FormalAlgebra.plugCtx
abbrev bergstraWeight := FormalAlgebra.bergstraWeight

local infixl:70 (priority := high) " ⋅ " => FormalAlgebra.Term.app

/-! ## 1. Open `S`-Headed HNFs and Universal Open Solvability via `evalHNOpen` (`.var _ ↦ .hn34`) -/

/-- An open or closed `CL(S)` term is an `S`-headed HNF iff it is `S`, `S ⋅ a`, or `S ⋅ a ⋅ b`. -/
def IsSHeadHNF (t : Term) : Prop :=
  t = S ∨ (∃ a, t = S ⋅ a) ∨ (∃ a b, t = S ⋅ a ⋅ b)

/-- `t` reduces in 0 or more steps to an `S`-headed HNF (`S`, `S ⋅ a`, or `S ⋅ a ⋅ b`). -/
def HasSHeadHNF (t : Term) : Prop :=
  ∃ u, Reduces t u ∧ IsSHeadHNF u

/-- Open extension of `evalHN` mapping `S ↦ .hn0` and every variable `.var k ↦ .hn34`. -/
def evalHNOpen : Term → StateHN
  | .s => .hn0
  | .var _ => .hn34
  | .app a b => deltaHN (evalHNOpen a) (evalHNOpen b)

theorem evalHNOpen_eq_evalHN {t : Term} (hv : noVars t = true) :
    evalHNOpen t = evalHN t := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    have hvb := ((Bool.and_eq_true _ _).mp hv).2
    simp only [evalHNOpen, evalHN, iha hva, ihb hvb]

theorem evalHNOpen_step {a b : Term} (h : Step a b) :
    evalHNOpen a = evalHNOpen b := by
  induction h with
  | root x y z => exact deltaHN_s_law (evalHNOpen x) (evalHNOpen y) (evalHNOpen z)
  | left _ ih => simp only [evalHNOpen, ih]
  | right _ ih => simp only [evalHNOpen, ih]

theorem evalHNOpen_reduces {a b : Term} (h : Reduces a b) :
    evalHNOpen a = evalHNOpen b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalHNOpen_step hs).trans ih

theorem evalHNOpen_conv {a b : Term} (h : ConvS a b) :
    evalHNOpen a = evalHNOpen b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalHNOpen_step hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem evalHNOpen_of_headLeaf_var {t : Term} {k : Nat} (hhd : headLeaf t = .var k) :
    evalHNOpen t = .hn34 := by
  induction t with
  | s => cases hhd
  | var _ => rfl
  | app a b iha _ =>
    change deltaHN (evalHNOpen a) (evalHNOpen b) = .hn34
    rw [iha hhd]
    exact deltaHN_hn34_left (evalHNOpen b)

theorem evalHNOpen_ne_hn34_of_isSHeadHNF {u : Term} (hu : IsSHeadHNF u) :
    evalHNOpen u ≠ .hn34 := by
  rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · decide
  · exact deltaHN_s1_ne_hn34 (evalHNOpen a)
  · exact deltaHN_s2_ne_hn34 (evalHNOpen a) (evalHNOpen b)

theorem headStepOpt_none_open {t : Term} (h : headStepOpt t = none) :
    (∃ k, headLeaf t = .var k) ∨ IsSHeadHNF t := by
  induction t with
  | s => exact Or.inr (Or.inl rfl)
  | var k => exact Or.inl ⟨k, rfl⟩
  | app a b iha _ =>
    simp only [headStepOpt] at h
    cases hr : rootRedexOpt a b with
    | some _ => rw [hr] at h; cases h
    | none =>
      rw [hr] at h
      cases ha : headStepOpt a with
      | some _ => rw [ha] at h; cases h
      | none =>
        rcases iha ha with ⟨k, hvar⟩ | rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
        · exact Or.inl ⟨k, hvar⟩
        · exact Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨x, b, rfl⟩))
        · exfalso; exact rootRedexOpt_none hr x y rfl

/-- Canonical 8-leaf closed `.hn34` combinator substituting variables in `muHN` termination proofs. -/
def closedW34 : Term := S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S ⋅ S)) ⋅ S

private theorem evalHN_closedW34 : evalHN closedW34 = .hn34 := rfl

def substW34 (t : Term) : Term := subst (fun _ => closedW34) t

private theorem evalHN_substW34 (t : Term) : evalHN (substW34 t) = evalHNOpen t := by
  induction t with
  | s => rfl
  | var _ => exact evalHN_closedW34
  | app a b iha ihb =>
    change deltaHN (evalHN (substW34 a)) (evalHN (substW34 b)) = deltaHN (evalHNOpen a) (evalHNOpen b)
    rw [iha, ihb]

private theorem subst_headStep (σ : Nat → Term) {a b : Term} (h : HeadStep a b) :
    HeadStep (subst σ a) (subst σ b) := by
  induction h with
  | root x y z => exact HeadStep.root (subst σ x) (subst σ y) (subst σ z)
  | left _ ih => exact HeadStep.left ih

def headNormalizeOpenAux : Nat → Term → Term
  | 0, t => t
  | fuel + 1, t =>
    match headStepOpt t with
    | none => t
    | some t' => headNormalizeOpenAux fuel t'

private theorem headNormalizeOpenAux_spec :
    ∀ (fuel : Nat) {t : Term},
      evalHNOpen t ≠ .hn34 →
      muHN (substW34 t) < fuel →
      HeadReduces t (headNormalizeOpenAux fuel t) ∧ IsSHeadHNF (headNormalizeOpenAux fuel t) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ hlt
    cases hlt
  | succ fuel ih =>
    intro t hval hlt
    simp only [headNormalizeOpenAux]
    cases hh : headStepOpt t with
    | none =>
      rcases headStepOpt_none_open hh with ⟨k, hvar⟩ | hshead
      · exfalso
        exact hval (evalHNOpen_of_headLeaf_var hvar)
      · exact ⟨HeadReduces.refl t, hshead⟩
    | some t' =>
      have hs : HeadStep t t' := headStepOpt_some hh
      have hval' : evalHNOpen t' ≠ .hn34 := by
        rw [← evalHNOpen_step (headStep_to_step hs)]
        exact hval
      have hval_sub : evalHN (substW34 t) ≠ .hn34 := by
        rw [evalHN_substW34]
        exact hval
      have hdrop : muHN (substW34 t') + 1 ≤ muHN (substW34 t) :=
        muHN_headStep_drop (subst_headStep (fun _ => closedW34) hs) hval_sub
      have hlt' : muHN (substW34 t') < fuel :=
        Nat.lt_of_succ_lt_succ (Nat.lt_of_le_of_lt hdrop hlt)
      obtain ⟨hred, hshead⟩ := ih hval' hlt'
      exact ⟨HeadReduces.next hs hred, hshead⟩

def headNormalizeOpen (t : Term) : Term :=
  headNormalizeOpenAux (muHN (substW34 t) + 1) t

/-- **Universal Open Solvability Theorem (`CL(S)`)**:
    For **every** open or closed pure-`S` term `t`, `t` reduces to `S`, `S ⋅ a`, or `S ⋅ a ⋅ b`
    **iff** `evalHNOpen t ≠ .hn34`. -/
theorem open_hasSHeadHNF_iff (t : Term) :
    HasSHeadHNF t ↔ evalHNOpen t ≠ .hn34 := by
  constructor
  · intro ⟨u, hred, hu⟩
    rw [evalHNOpen_reduces hred]
    exact evalHNOpen_ne_hn34_of_isSHeadHNF hu
  · intro hval
    obtain ⟨hred, hu⟩ := headNormalizeOpenAux_spec (muHN (substW34 t) + 1) hval (Nat.lt_succ_self _)
    exact ⟨headNormalizeOpen t, headReduces_to_reduces hred, hu⟩

theorem closed_hasSHeadHNF_iff_hasHNF {t : Term} (hv : noVars t = true) :
    HasSHeadHNF t ↔ HasHNF t := by
  constructor
  · intro ⟨u, hred, hu⟩
    rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · exact ⟨S, hred, Nat.zero_le 2⟩
    · exact ⟨S ⋅ a, hred, Nat.succ_le_succ (Nat.zero_le 1)⟩
    · exact ⟨S ⋅ a ⋅ b, hred, Nat.le_refl 2⟩
  · intro ⟨h, hred, hsl⟩
    exact ⟨h, hred, closed_spineLen_le_2_shapes (noVars_reduces hred hv) hsl⟩

/-! ## 2. Curry–Feys Order (`Definition 37`), Single-Variable Consumption (`Definition 21`),
    and the Nilpotent Operator `tauHN` on `StateHN` -/

/-- Left-associated application of `t` to a list of variable indices `[v_1, ..., v_r]`. -/
def appVars : Term → List Nat → Term
  | t, [] => t
  | t, v :: vs => appVars (t ⋅ .var v) vs

theorem appVars_append (t : Term) (xs ys : List Nat) :
    appVars t (xs ++ ys) = appVars (appVars t xs) ys := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => exact ih (t ⋅ .var x)

theorem reduces_appVars {a b : Term} (h : Reduces a b) (vs : List Nat) :
    Reduces (appVars a vs) (appVars b vs) := by
  induction vs generalizing a b with
  | nil => exact h
  | cons v vs ih => exact ih (reduces_left h (.var v))

/-- Strict upper bound `maxVarPlus1 t` on all variable indices occurring in `t`. -/
def maxVarPlus1 : Term → Nat
  | .s => 0
  | .var k => k + 1
  | .app a b => Nat.max (maxVarPlus1 a) (maxVarPlus1 b)

theorem hasVar_false_of_maxVarPlus1_le {v : Nat} {t : Term} (h : maxVarPlus1 t ≤ v) :
    hasVar v t = false := by
  induction t with
  | s => rfl
  | var k =>
    change k + 1 ≤ v at h
    change decide (k = v) = false
    exact decide_eq_false (fun heq => by subst heq; exact Nat.not_succ_le_self k h)
  | app a b iha ihb =>
    simp only [maxVarPlus1, Nat.max_le] at h
    change (hasVar v a || hasVar v b) = false
    rw [iha h.1, ihb h.2]
    rfl

def freshVarsFrom (base : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => base :: freshVarsFrom (base + 1) k

theorem freshVarsFrom_length (base k : Nat) : (freshVarsFrom base k).length = k := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih => simp only [freshVarsFrom, List.length_cons, ih]

theorem mem_freshVarsFrom_ge {base k v : Nat} (hm : v ∈ freshVarsFrom base k) : base ≤ v := by
  induction k generalizing base with
  | zero => cases hm
  | succ k ih =>
    rcases List.mem_cons.mp hm with rfl | htail
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (ih htail)

def freshVars (t : Term) (k : Nat) : List Nat :=
  freshVarsFrom (maxVarPlus1 t) k

theorem freshVars_spec (t : Term) (k : Nat) :
    (freshVars t k).length = k ∧ ∀ v ∈ freshVars t k, hasVar v t = false := by
  refine ⟨freshVarsFrom_length _ k, fun v hv => ?_⟩
  exact hasVar_false_of_maxVarPlus1_le (mem_freshVarsFrom_ge hv)

/-- **Curry–Feys Order-0 / Dummy-Tail Predicate (`Definition 37` of *Dance of the Starlings*, p. 99)**:
    Any non-empty sequence of fresh variables `ys` appended to `f` plays a purely dummy role in every
    reduction of `appVars f ys`. -/
def IsDummyTail (f : Term) : Prop :=
  ∀ (ys : List Nat) (n : Term),
    ys ≠ [] →
    (∀ y ∈ ys, hasVar y f = false) →
    Reduces (appVars f ys) n →
    ∃ f', n = appVars f' ys ∧ Reduces f f' ∧ (∀ y ∈ ys, hasVar y f' = false)

private theorem reduces_var_eq {u : Nat} {b : Term} (h : Reduces (.var u) b) : b = .var u := by
  cases h with
  | refl _ => rfl
  | next hs _ => cases hs

theorem unconsumed_var_of_no_sab {f : Term} (hno : ∀ p q, ¬ Reduces f (S ⋅ p ⋅ q))
    (u : Nat) {n : Term} (hred : Reduces (f ⋅ .var u) n) :
    ∃ f', n = f' ⋅ .var u ∧ Reduces f f' := by
  obtain ⟨f', b', heq, hrf, hru⟩ := reduces_app_no_sab hred f (.var u) hno rfl
  rw [reduces_var_eq hru] at heq
  exact ⟨f', heq, hrf⟩

theorem reduces_appVars_of_evalHNOpen_eq_hn34 {f : Term} (hf : evalHNOpen f = .hn34) :
    ∀ (ys : List Nat) {n : Term},
      Reduces (appVars f ys) n → ∃ f', n = appVars f' ys ∧ Reduces f f' := by
  intro ys
  induction ys generalizing f with
  | nil =>
    intro n hred
    exact ⟨n, rfl, hred⟩
  | cons y rest ih =>
    intro n hred
    have hfy : evalHNOpen (f ⋅ .var y) = .hn34 := by
      change deltaHN (evalHNOpen f) .hn34 = .hn34
      rw [hf]
      exact deltaHN_hn34_left .hn34
    obtain ⟨g', hn, hrg⟩ := ih hfy hred
    have hno : ∀ p q, ¬ Reduces f (S ⋅ p ⋅ q) := by
      intro p q hr
      have heq := evalHNOpen_reduces hr
      rw [hf] at heq
      exact deltaHN_s2_ne_hn34 (evalHNOpen p) (evalHNOpen q) heq.symm
    obtain ⟨f', hg', hrf⟩ := unconsumed_var_of_no_sab hno y hrg
    rw [hg'] at hn
    exact ⟨f', hn, hrf⟩

private theorem leaves_last_arg_ne {a b : Term} {v : Nat}
    (h : (a ⋅ b) = (f' ⋅ .var v)) : leaves b = 1 := by
  injection h with _ hb
  rw [hb]
  rfl

/-- **Fundamental Order-0 Equivalence (`CL(S)`)**:
    For **every** open or closed pure-`S` term `f`, Curry–Feys dummy-tail invariance holds
    **iff** `f` never reduces to `S`, `S ⋅ a`, or `S ⋅ a ⋅ b`, **iff** `evalHNOpen f = .hn34`! -/
theorem isDummyTail_iff_evalHNOpen_eq_hn34 (f : Term) :
    IsDummyTail f ↔ evalHNOpen f = .hn34 := by
  constructor
  · intro hdummy
    exact if h34 : evalHNOpen f = .hn34 then h34
    else by
      exfalso
      obtain ⟨u, hred, hu⟩ := (open_hasSHeadHNF_iff f).mpr h34
      let b0 := maxVarPlus1 f
      have hf0 : hasVar b0 f = false := hasVar_false_of_maxVarPlus1_le (Nat.le_refl b0)
      have hf1 : hasVar (b0 + 1) f = false := hasVar_false_of_maxVarPlus1_le (Nat.le_succ b0)
      have hf2 : hasVar (b0 + 2) f = false := hasVar_false_of_maxVarPlus1_le (Nat.le_succ_of_le (Nat.le_succ b0))
      rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
      · have step3 : Reduces (appVars f [b0, b0 + 1, b0 + 2])
            ((FormalAlgebra.Term.var b0 ⋅ FormalAlgebra.Term.var (b0 + 2)) ⋅
             (FormalAlgebra.Term.var (b0 + 1) ⋅ FormalAlgebra.Term.var (b0 + 2))) :=
          FormalAlgebra.reduces_trans (reduces_appVars hred [b0, b0 + 1, b0 + 2])
            (FormalAlgebra.Reduces.next
              (FormalAlgebra.Step.root (.var b0) (.var (b0 + 1)) (.var (b0 + 2)))
              (FormalAlgebra.Reduces.refl _))
        have hfresh : ∀ y ∈ [b0, b0 + 1, b0 + 2], hasVar y f = false := by
          intro y hy
          cases hy with
          | head _ => exact hf0
          | tail _ h1 =>
            cases h1 with
            | head _ => exact hf1
            | tail _ h2 =>
              cases h2 with
              | head _ => exact hf2
              | tail _ h3 => cases h3
        obtain ⟨f', heq, _, _⟩ := hdummy [b0, b0 + 1, b0 + 2] _ (fun h => by cases h) hfresh step3
        injection heq with _ hright
        cases hright
      · have step2 : Reduces (appVars f [b0, b0 + 1])
            ((a ⋅ FormalAlgebra.Term.var (b0 + 1)) ⋅
             (FormalAlgebra.Term.var b0 ⋅ FormalAlgebra.Term.var (b0 + 1))) :=
          FormalAlgebra.reduces_trans (reduces_appVars hred [b0, b0 + 1])
            (FormalAlgebra.Reduces.next
              (FormalAlgebra.Step.root a (.var b0) (.var (b0 + 1)))
              (FormalAlgebra.Reduces.refl _))
        have hfresh : ∀ y ∈ [b0, b0 + 1], hasVar y f = false := by
          intro y hy
          cases hy with
          | head _ => exact hf0
          | tail _ h1 =>
            cases h1 with
            | head _ => exact hf1
            | tail _ h2 => cases h2
        obtain ⟨f', heq, _, _⟩ := hdummy [b0, b0 + 1] _ (fun h => by cases h) hfresh step2
        injection heq with _ hright
        cases hright
      · have step1 : Reduces (appVars f [b0])
            ((a ⋅ FormalAlgebra.Term.var b0) ⋅ (b ⋅ FormalAlgebra.Term.var b0)) :=
          FormalAlgebra.reduces_trans (reduces_appVars hred [b0])
            (FormalAlgebra.Reduces.next
              (FormalAlgebra.Step.root a b (.var b0))
              (FormalAlgebra.Reduces.refl _))
        have hfresh : ∀ y ∈ [b0], hasVar y f = false := by
          intro y hy
          cases hy with
          | head _ => exact hf0
          | tail _ h1 => cases h1
        obtain ⟨f', heq, _, _⟩ := hdummy [b0] _ (fun h => by cases h) hfresh step1
        injection heq with _ hright
        have hpos : 1 ≤ leaves b := leaves_pos b
        have hl : leaves (b ⋅ FormalAlgebra.Term.var b0) = leaves (FormalAlgebra.Term.var b0) :=
          congrArg leaves hright
        change leaves b + 1 = 1 at hl
        have hbad : 2 ≤ 1 := by
          have h2 : 2 ≤ leaves b + 1 := Nat.add_le_add_right hpos 1
          rw [hl] at h2
          exact h2
        cases hbad with
        | step h0 => cases h0
  · intro h34 ys n _ hfresh hred
    obtain ⟨f', hn, hrf⟩ := reduces_appVars_of_evalHNOpen_eq_hn34 h34 ys hred
    exact ⟨f', hn, hrf, fun y hy => hasVar_false_reduces hrf (hfresh y hy)⟩

theorem isDummyTail_iff_not_hasSHeadHNF (f : Term) :
    IsDummyTail f ↔ ¬ HasSHeadHNF f := by
  rw [isDummyTail_iff_evalHNOpen_eq_hn34, open_hasSHeadHNF_iff]
  exact ⟨fun h hne => hne h, fun hnn => if h : evalHNOpen f = .hn34 then h else False.elim (hnn h)⟩

/-- Right-translation by `.hn34` on `StateHN` (`tauHN q = deltaHN q .hn34`). -/
def tauHN (q : StateHN) : StateHN :=
  deltaHN q .hn34

def iterTauHN : Nat → StateHN → StateHN
  | 0, q => q
  | k + 1, q => iterTauHN k (tauHN q)

theorem evalHNOpen_appVars (t : Term) (vs : List Nat) :
    evalHNOpen (appVars t vs) = iterTauHN vs.length (evalHNOpen t) := by
  induction vs generalizing t with
  | nil => rfl
  | cons v vs ih =>
    change evalHNOpen (appVars (t ⋅ .var v) vs) = iterTauHN (vs.length + 1) (evalHNOpen t)
    rw [ih (t ⋅ .var v)]
    rfl

private theorem tauHN_nilpotent_3_chk :
    checkAll1_StateHN (fun q => decide (iterTauHN 3 q = .hn34)) = true := rfl

/-- **Algebraic Nilpotency Theorem (`tauHN^3 = .hn34`)**:
    Three applications of `tauHN` send **every** state of `A_HN` to `.hn34`. -/
theorem tauHN_nilpotent_3 (q : StateHN) : iterTauHN 3 q = .hn34 :=
  of_decide_eq_true (checkAll1_StateHN_sound _ tauHN_nilpotent_3_chk q)

theorem iterTauHN_ge_3 {k : Nat} (hk : 3 ≤ k) (q : StateHN) : iterTauHN k q = .hn34 := by
  have ⟨d, hd⟩ : ∃ d, k = 3 + d := ⟨k - 3, (Nat.add_sub_of_le hk).symm⟩
  subst hd
  induction d with
  | zero => exact tauHN_nilpotent_3 q
  | succ d ih =>
    have hstep : ∀ m s, iterTauHN (m + 1) s = tauHN (iterTauHN m s) := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m0 ihm => intro s; exact ihm (tauHN s)
    rw [Nat.add_succ 3 d, hstep (3 + d) q, ih (Nat.le_add_right 3 d)]
    exact deltaHN_hn34_left .hn34

/-- `m` has order `≤ k` (Curry–Feys Definition 37) iff after offering `k` fresh variables `xs`,
    any further fresh variable tail is purely dummy. -/
def HasOrderAtMost (m : Term) (k : Nat) : Prop :=
  ∀ (xs : List Nat),
    xs.length = k →
    (∀ x ∈ xs, hasVar x m = false) →
    IsDummyTail (appVars m xs)

/-- `m` has exact order `k` iff `k` is the least natural number with `HasOrderAtMost m k`. -/
def HasExactOrder (m : Term) (k : Nat) : Prop :=
  HasOrderAtMost m k ∧ ∀ j, j < k → ¬ HasOrderAtMost m j

theorem hasOrderAtMost_iff_iterTauHN (m : Term) (k : Nat) :
    HasOrderAtMost m k ↔ iterTauHN k (evalHNOpen m) = .hn34 := by
  constructor
  · intro hord
    have ⟨hlen, hfr⟩ := freshVars_spec m k
    have hd := hord (freshVars m k) hlen hfr
    rw [isDummyTail_iff_evalHNOpen_eq_hn34, evalHNOpen_appVars, hlen] at hd
    exact hd
  · intro htau xs hlen _
    rw [isDummyTail_iff_evalHNOpen_eq_hn34, evalHNOpen_appVars, hlen]
    exact htau

/-- **Exact Order Partition of `StateHN` (`35 = 1 + 11 + 17 + 6`)**:
    - Order `0` (`1` state): `.hn34`
    - Order `1` (`11` states): `.hn22..26`, `.hn28..33`
    - Order `2` (`17` states): `.hn6..21`, `.hn27`
    - Order `3` (`6` states): `.hn0..5` -/
def orderOfStateHN : StateHN → Nat
  | .hn34 => 0
  | .hn22 | .hn23 | .hn24 | .hn25 | .hn26 | .hn28 | .hn29 | .hn30 | .hn31 | .hn32 | .hn33 => 1
  | .hn6 | .hn7 | .hn8 | .hn9 | .hn10 | .hn11 | .hn12 | .hn13
  | .hn14 | .hn15 | .hn16 | .hn17 | .hn18 | .hn19 | .hn20 | .hn21 | .hn27 => 2
  | .hn0 | .hn1 | .hn2 | .hn3 | .hn4 | .hn5 => 3

private theorem orderOfStateHN_spec_chk : checkAll1_StateHN (fun q =>
    decide (orderOfStateHN q ≤ 3) &&
    decide ((iterTauHN 0 q = .hn34 ↔ orderOfStateHN q ≤ 0) ∧
            (iterTauHN 1 q = .hn34 ↔ orderOfStateHN q ≤ 1) ∧
            (iterTauHN 2 q = .hn34 ↔ orderOfStateHN q ≤ 2) ∧
            (iterTauHN 3 q = .hn34 ↔ orderOfStateHN q ≤ 3))) = true := rfl

theorem orderOfStateHN_le_3 (q : StateHN) : orderOfStateHN q ≤ 3 := by
  have h := checkAll1_StateHN_sound _ orderOfStateHN_spec_chk q
  exact of_decide_eq_true (and_left h)

theorem iterTauHN_eq_hn34_iff_order_le (q : StateHN) (k : Nat) :
    iterTauHN k q = .hn34 ↔ orderOfStateHN q ≤ k := by
  have ⟨h0, h1, h2, h3⟩ := of_decide_eq_true (and_right (checkAll1_StateHN_sound _ orderOfStateHN_spec_chk q))
  match k with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | m + 4 =>
    have hk3 : 3 ≤ m + 4 := Nat.le_add_left 3 (m + 1)
    exact ⟨fun _ => Nat.le_trans (orderOfStateHN_le_3 q) hk3, fun _ => iterTauHN_ge_3 hk3 q⟩

theorem hasOrderAtMost_iff_orderOfStateHN_le (m : Term) (k : Nat) :
    HasOrderAtMost m k ↔ orderOfStateHN (evalHNOpen m) ≤ k := by
  rw [hasOrderAtMost_iff_iterTauHN, iterTauHN_eq_hn34_iff_order_le]

/-- **Main Exact Order Classification Theorem (`CL(S)`)**:
    For **every** open or closed pure-`S` term `m` and every `k : Nat`,
    `HasExactOrder m k ↔ orderOfStateHN (evalHNOpen m) = k`! -/
theorem hasExactOrder_iff_orderOfStateHN (m : Term) (k : Nat) :
    HasExactOrder m k ↔ orderOfStateHN (evalHNOpen m) = k := by
  unfold HasExactOrder
  simp only [hasOrderAtMost_iff_orderOfStateHN_le]
  constructor
  · intro ⟨hle, hmin⟩
    exact if heq : orderOfStateHN (evalHNOpen m) = k then heq
    else False.elim (hmin (orderOfStateHN (evalHNOpen m)) (Nat.lt_of_le_of_ne hle heq) (Nat.le_refl _))
  · intro heq
    subst heq
    exact ⟨Nat.le_refl _, fun j hj hle => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hj hle)⟩

/-- Closed-term specialization using `evalHN` directly. -/
theorem closed_hasExactOrder_iff {m : Term} (hv : noVars m = true) (k : Nat) :
    HasExactOrder m k ↔ orderOfStateHN (evalHN m) = k := by
  rw [hasExactOrder_iff_orderOfStateHN, evalHNOpen_eq_evalHN hv]

private theorem order_exhaust_state (q : StateHN) :
    orderOfStateHN q = 0 ∨ orderOfStateHN q = 1 ∨ orderOfStateHN q = 2 ∨ orderOfStateHN q = 3 := by
  cases q <;> decide

/-- **Visser–van Oostrom Exact Exhaustion Theorem (`order(m) ∈ {0, 1, 2, 3}`)**:
    Every open or closed pure-`S` term `m` has a unique exact finite order, and it lies in `{0, 1, 2, 3}`. -/
theorem visser_van_oostrom_exact_order_exhaustion (m : Term) :
    HasExactOrder m 0 ∨ HasExactOrder m 1 ∨ HasExactOrder m 2 ∨ HasExactOrder m 3 := by
  simp only [hasExactOrder_iff_orderOfStateHN]
  exact order_exhaust_state (evalHNOpen m)

/-- Order is strictly invariant under `CL(S)` convertibility (`=S`). -/
theorem convS_preserves_exactOrder {m n : Term} (hc : ConvS m n) (k : Nat) :
    HasExactOrder m k ↔ HasExactOrder n k := by
  rw [hasExactOrder_iff_orderOfStateHN, hasExactOrder_iff_orderOfStateHN, evalHNOpen_conv hc]

/-- **Reconciliation with Barendregt Definition 21 (Single-Variable Consumption)** on closed pure-`S` terms:
    - Order `0`: `¬ HasHNF m`
    - Order `1`: `HasHNF m ∧ m ≠ S ∧ ¬ ∃ a b, m ⋅ x0 →* S ⋅ a ⋅ b`
    - Order `2`: `(m ≠ S ∧ ∃ a b, m ⋅ x0 →* S ⋅ a ⋅ b) ∧ ¬ ∃ a b, m ⋅ x0 ⋅ x1 →* S ⋅ a ⋅ b`
    - Order `3`: `∃ a b, m ⋅ x0 ⋅ x1 →* S ⋅ a ⋅ b` -/
theorem closed_order_operational_characterization {m : Term} (hv : noVars m = true) (x0 x1 : Nat) :
    (HasExactOrder m 0 ↔ ¬ HasHNF m) ∧
    (HasExactOrder m 1 ↔ HasHNF m ∧ m ≠ S ∧ ¬ ∃ a b, Reduces (m ⋅ .var x0) (S ⋅ a ⋅ b)) ∧
    (HasExactOrder m 2 ↔ (m ≠ S ∧ ∃ a b, Reduces (m ⋅ .var x0) (S ⋅ a ⋅ b)) ∧
        ¬ ∃ a b, Reduces (m ⋅ .var x0 ⋅ .var x1) (S ⋅ a ⋅ b)) ∧
    (HasExactOrder m 3 ↔ ∃ a b, Reduces (m ⋅ .var x0 ⋅ .var x1) (S ⋅ a ⋅ b)) := by
  have hev : evalHNOpen m = evalHN m := evalHNOpen_eq_evalHN hv
  have hsab1 : (∃ a b, Reduces (m ⋅ .var x0) (S ⋅ a ⋅ b)) ↔
      (m ≠ S ∧ tauHN (evalHN m) ≠ .hn34) := by
    constructor
    · intro ⟨a, b, hr⟩
      have hneS : m ≠ S := by
        intro hmS; subst hmS
        obtain ⟨f', heq, hrf⟩ := unconsumed_var_of_no_sab
          (fun p q hs => by cases hs with | next h0 _ => cases h0) x0 hr
        injection heq with h1 h2
        cases hrf with
        | refl _ => cases h1
        | next hs _ => cases hs
      have h34 : evalHNOpen (m ⋅ .var x0) ≠ .hn34 :=
        (open_hasSHeadHNF_iff _).mp ⟨S ⋅ a ⋅ b, hr, Or.inr (Or.inr ⟨a, b, rfl⟩)⟩
      change deltaHN (evalHNOpen m) .hn34 ≠ .hn34 at h34
      rw [hev] at h34
      exact ⟨hneS, h34⟩
    · intro ⟨hneS, htau⟩
      have hopen : evalHNOpen (m ⋅ .var x0) ≠ .hn34 := by
        change deltaHN (evalHNOpen m) .hn34 ≠ .hn34
        rw [hev]; exact htau
      obtain ⟨u, hru, hu⟩ := (open_hasSHeadHNF_iff _).mpr hopen
      have hm_app : ∃ p q, m = p ⋅ q := by
        cases m with
        | s => exfalso; exact hneS rfl
        | var _ => cases hv
        | app p q => exact ⟨p, q, rfl⟩
      obtain ⟨p, q, rfl⟩ := hm_app
      rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
      · exfalso; exact (no_dynamic_hnf1 p q (.var x0) S).2 hru
      · exfalso; exact (no_dynamic_hnf1 p q (.var x0) a).1 hru
      · exact ⟨a, b, hru⟩
  have hsab2 : (∃ a b, Reduces (m ⋅ .var x0 ⋅ .var x1) (S ⋅ a ⋅ b)) ↔
      iterTauHN 2 (evalHN m) ≠ .hn34 := by
    constructor
    · intro ⟨a, b, hr⟩
      have h34 : evalHNOpen (m ⋅ .var x0 ⋅ .var x1) ≠ .hn34 :=
        (open_hasSHeadHNF_iff _).mp ⟨S ⋅ a ⋅ b, hr, Or.inr (Or.inr ⟨a, b, rfl⟩)⟩
      change iterTauHN 2 (evalHNOpen m) ≠ .hn34 at h34
      rw [hev] at h34
      exact h34
    · intro htau2
      have hopen : evalHNOpen (m ⋅ .var x0 ⋅ .var x1) ≠ .hn34 := by
        change iterTauHN 2 (evalHNOpen m) ≠ .hn34
        rw [hev]; exact htau2
      obtain ⟨u, hru, hu⟩ := (open_hasSHeadHNF_iff _).mpr hopen
      rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
      · exfalso; exact (no_dynamic_hnf1 m (.var x0) (.var x1) S).2 hru
      · exfalso; exact (no_dynamic_hnf1 m (.var x0) (.var x1) a).1 hru
      · exact ⟨a, b, hru⟩
  have hhnf : HasHNF m ↔ evalHN m ≠ .hn34 := (barendregt_open_problem_10 hv).1
  have hmS_ne : m ≠ S ↔ evalHN m ≠ .hn0 :=
    ⟨fun hne h0 => hne ((evalHN_eq_hn0_iff hv).mp h0), fun hne0 hm => hne0 (hm ▸ rfl)⟩
  rw [closed_hasExactOrder_iff hv 0, closed_hasExactOrder_iff hv 1,
      closed_hasExactOrder_iff hv 2, closed_hasExactOrder_iff hv 3,
      hsab1, hsab2, hhnf, hmS_ne]
  cases evalHN m <;> decide

/-! ## 3. Exact Uniqueness Law for Order 3 (`rightComb`) and Sharp Minimal Order Witnesses -/

/-- The unique right-comb pure-`S` tower of `n` leaves (`rightComb 1 = S`, `rightComb (k+2) = S ⋅ rightComb (k+1)`). -/
def rightComb : Nat → Term
  | 0 => S
  | 1 => S
  | k + 2 => S ⋅ rightComb (k + 1)

theorem noVars_rightComb (n : Nat) : noVars (rightComb n) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m => exact (Bool.and_eq_true _ _).mpr ⟨rfl, ih⟩

theorem leaves_rightComb {n : Nat} (hn : 1 ≤ n) : leaves (rightComb n) = n := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m =>
      change 1 + leaves (rightComb (m + 1)) = m + 2
      rw [ih (Nat.succ_le_succ (Nat.zero_le m))]
      omega

private theorem deltaHN_ord3_iff_chk : checkAll2_StateHN (fun a b =>
    decide (orderOfStateHN (deltaHN a b) = 3 ↔ (a = .hn0 ∧ orderOfStateHN b = 3))) = true := rfl

/-- **Key Structural Factorization of `{.hn0 .. .hn5}` in `A_HN`**:
    `deltaHN a b` has Order 3 **iff** `a = .hn0` and `b` has Order 3! -/
theorem deltaHN_ord3_iff (a b : StateHN) :
    orderOfStateHN (deltaHN a b) = 3 ↔ (a = .hn0 ∧ orderOfStateHN b = 3) :=
  of_decide_eq_true (checkAll2_StateHN_sound _ deltaHN_ord3_iff_chk a b)

theorem evalHN_rightComb_ord3 (n : Nat) : orderOfStateHN (evalHN (rightComb n)) = 3 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m =>
      change orderOfStateHN (deltaHN .hn0 (evalHN (rightComb (m + 1)))) = 3
      exact (deltaHN_ord3_iff .hn0 _).mpr ⟨rfl, ih⟩

/-- **Stunning Exact Uniqueness Law for Order 3 (`CL(S)`)**:
    A closed pure-`S` combinator `t` has Order `3` **iff** `t = rightComb (leaves t)`! -/
theorem closed_order3_iff_rightComb {t : Term} (hv : noVars t = true) :
    HasExactOrder t 3 ↔ t = rightComb (leaves t) := by
  rw [closed_hasExactOrder_iff hv 3]
  constructor
  · induction t with
    | s => intro _; rfl
    | var _ => cases hv
    | app a b iha ihb =>
      have hva := ((Bool.and_eq_true _ _).mp hv).1
      have hvb := ((Bool.and_eq_true _ _).mp hv).2
      intro h3
      have ⟨ha0, hb3⟩ := (deltaHN_ord3_iff (evalHN a) (evalHN b)).mp h3
      have haS : a = S := (evalHN_eq_hn0_iff hva).mp ha0
      have hb_rc : b = rightComb (leaves b) := ihb hvb hb3
      subst haS
      have hlb : 1 ≤ leaves b := leaves_pos b
      cases h : leaves b with
      | zero =>
        have hpos : 1 ≤ leaves b := leaves_pos b
        rw [h] at hpos; cases hpos
      | succ m =>
        change S ⋅ b = rightComb (1 + leaves b)
        rw [h] at hb_rc
        rw [h, Nat.add_comm 1 (m + 1), hb_rc]
        rfl
  · intro heq
    rw [heq]
    exact evalHN_rightComb_ord3 (leaves t)

/-- Concrete landmark examples and exact minimal witnesses across Orders `3, 2, 1, 0`! -/
theorem order_canonical_witnesses :
    HasExactOrder S 3 ∧
    HasExactOrder (S ⋅ S) 3 ∧
    HasExactOrder (S ⋅ (S ⋅ S)) 3 ∧
    HasExactOrder (S ⋅ S ⋅ S) 2 ∧
    HasExactOrder (S ⋅ S ⋅ S ⋅ S) 2 ∧
    HasExactOrder (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ S)) 2 ∧
    HasExactOrder (S ⋅ (S ⋅ S ⋅ S) ⋅ S) 1 ∧
    HasExactOrder closedW34 0 ∧
    HasExactOrder AAA 0 := by
  simp only [hasExactOrder_iff_orderOfStateHN]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Sharp Minimal Witness Theorem for Order 2 (`n = 3`) and Order 1 (`n = 5`)**:
    - Every closed pure-`S` term of size `≤ 2` has Order `3`.
    - At size `3`, `S ⋅ S ⋅ S` is the **unique** closed pure-`S` term of Order `2` (and none have Order `≤ 1`).
    - Every closed pure-`S` term of size `≤ 4` has Order `≥ 2` (zero terms of Order `0` or `1`!).
    - At size `5` (`14` terms), **`S ⋅ (S ⋅ S ⋅ S) ⋅ S` is the UNIQUE closed pure-`S` combinator of Order `1`**! -/
theorem minimal_order_thresholds_1_to_5 :
    (∀ t, noVars t = true → leaves t ≤ 2 → HasExactOrder t 3) ∧
    (∀ t, noVars t = true → leaves t = 3 → (HasExactOrder t 2 ↔ t = S ⋅ S ⋅ S)) ∧
    (∀ t, noVars t = true → leaves t ≤ 4 → ¬ HasExactOrder t 1 ∧ ¬ HasExactOrder t 0) ∧
    (∀ t, noVars t = true → leaves t = 5 → (HasExactOrder t 1 ↔ t = S ⋅ (S ⋅ S ⋅ S) ⋅ S)) := by
  have c_le2 : FormalMinimality.listAll (fun t => decide (orderOfStateHN (evalHN t) = 3))
      (FormalMinimality.treesOfLeaves 1 ++ FormalMinimality.treesOfLeaves 2) = true := rfl
  have c_eq3 : FormalMinimality.filterList (fun t => decide (orderOfStateHN (evalHN t) = 2))
      (FormalMinimality.treesOfLeaves 3) = [S ⋅ S ⋅ S] := rfl
  have c_le4 : FormalMinimality.listAll (fun t => decide (2 ≤ orderOfStateHN (evalHN t)))
      (FormalMinimality.treesOfLeaves 1 ++ FormalMinimality.treesOfLeaves 2 ++
       FormalMinimality.treesOfLeaves 3 ++ FormalMinimality.treesOfLeaves 4) = true := rfl
  have c_eq5 : FormalMinimality.filterList (fun t => decide (orderOfStateHN (evalHN t) = 1))
      (FormalMinimality.treesOfLeaves 5) = [S ⋅ (S ⋅ S ⋅ S) ⋅ S] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t hv hl
    rw [closed_hasExactOrder_iff hv 3]
    have hpos : 1 ≤ leaves t := leaves_pos t
    have hmem : t ∈ FormalMinimality.treesOfLeaves 1 ++ FormalMinimality.treesOfLeaves 2 := by
      match hlt : leaves t with
      | 0 => rw [hlt] at hpos; cases hpos
      | 1 => exact List.mem_append_left _ (FormalMinimality.treesOfLeaves_complete hv hlt)
      | 2 => exact List.mem_append_right _ (FormalMinimality.treesOfLeaves_complete hv hlt)
      | m + 3 =>
        rw [hlt] at hl
        exfalso
        exact Nat.not_succ_le_zero m (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hl))
    exact of_decide_eq_true (FormalMinimality.listAll_sound c_le2 hmem)
  · intro t hv hl
    rw [closed_hasExactOrder_iff hv 2]
    have hm := FormalMinimality.treesOfLeaves_complete hv hl
    have hiff := FormalMinimality.mem_witnesses_iff_of_filter_eq c_eq3 hm
    constructor
    · intro h2
      have hw := hiff.mp (decide_eq_true h2)
      cases hw with
      | head _ => rfl
      | tail _ hnil => cases hnil
    · intro rfl; rfl
  · intro t hv hl
    rw [closed_hasExactOrder_iff hv 1, closed_hasExactOrder_iff hv 0]
    have hpos : 1 ≤ leaves t := leaves_pos t
    have hmem : t ∈ (FormalMinimality.treesOfLeaves 1 ++ FormalMinimality.treesOfLeaves 2 ++
        FormalMinimality.treesOfLeaves 3 ++ FormalMinimality.treesOfLeaves 4) := by
      match hlt : leaves t with
      | 0 => rw [hlt] at hpos; cases hpos
      | 1 => exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (FormalMinimality.treesOfLeaves_complete hv hlt)))
      | 2 => exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (FormalMinimality.treesOfLeaves_complete hv hlt)))
      | 3 => exact List.mem_append_left _ (List.mem_append_right _
          (FormalMinimality.treesOfLeaves_complete hv hlt))
      | 4 => exact List.mem_append_right _ (FormalMinimality.treesOfLeaves_complete hv hlt)
      | m + 5 =>
        rw [hlt] at hl
        exfalso
        exact Nat.not_succ_le_zero m
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hl))))
    have hge2 : 2 ≤ orderOfStateHN (evalHN t) :=
      of_decide_eq_true (FormalMinimality.listAll_sound c_le4 hmem)
    refine ⟨?_, ?_⟩
    · intro h1; rw [h1] at hge2; cases hge2 with | step h0 => cases h0
    · intro h0; rw [h0] at hge2; cases hge2
  · intro t hv hl
    rw [closed_hasExactOrder_iff hv 1]
    have hm := FormalMinimality.treesOfLeaves_complete hv hl
    have hiff := FormalMinimality.mem_witnesses_iff_of_filter_eq c_eq5 hm
    constructor
    · intro h1
      have hw := hiff.mp (decide_eq_true h1)
      cases hw with
      | head _ => rfl
      | tail _ hnil => cases hnil
    · intro rfl; rfl

/-! ## 4. Exact Myhill–Nerode Minimal `S`-Algebras (`35`, `35`, `12`, `3` States) -/

/-- Minimal closed witnesses inhabiting all 35 states of `StateHN`. -/
def witnessHN : StateHN → Term
  | .hn0 => S
  | .hn1 => S ⋅ S
  | .hn2 => S ⋅ (S ⋅ S)
  | .hn3 => S ⋅ (S ⋅ (S ⋅ S))
  | .hn4 => S ⋅ (S ⋅ (S ⋅ (S ⋅ S)))
  | .hn5 => S ⋅ (S ⋅ (S ⋅ (S ⋅ (S ⋅ S))))
  | .hn6 => S ⋅ S ⋅ S
  | .hn7 => S ⋅ (S ⋅ S ⋅ S)
  | .hn8 => S ⋅ S ⋅ S ⋅ (S ⋅ S)
  | .hn9 => S ⋅ (S ⋅ S ⋅ S ⋅ (S ⋅ S))
  | .hn10 => S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)))
  | .hn11 => S ⋅ S ⋅ (S ⋅ S)
  | .hn12 => S ⋅ (S ⋅ S ⋅ (S ⋅ S))
  | .hn13 => S ⋅ S ⋅ (S ⋅ (S ⋅ S))
  | .hn14 => S ⋅ (S ⋅ S) ⋅ S
  | .hn15 => S ⋅ (S ⋅ (S ⋅ S) ⋅ S)
  | .hn16 => S ⋅ (S ⋅ S) ⋅ (S ⋅ S)
  | .hn17 => S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ S)
  | .hn18 => S ⋅ (S ⋅ (S ⋅ S)) ⋅ S
  | .hn19 => S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ S)
  | .hn20 => S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S))
  | .hn21 => S ⋅ (S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)))
  | .hn22 => S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S)
  | .hn23 => S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S ⋅ S))
  | .hn24 => S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S
  | .hn25 => S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S) ⋅ S
  | .hn26 => S ⋅ (S ⋅ S ⋅ S) ⋅ S
  | .hn27 => S ⋅ (S ⋅ (S ⋅ S ⋅ S) ⋅ S)
  | .hn28 => S ⋅ (S ⋅ S ⋅ S) ⋅ (S ⋅ S)
  | .hn29 => S ⋅ (S ⋅ S ⋅ S) ⋅ (S ⋅ (S ⋅ S))
  | .hn30 => S ⋅ S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ S)
  | .hn31 => S ⋅ (S ⋅ S ⋅ (S ⋅ S)) ⋅ S
  | .hn32 => S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ S) ⋅ S
  | .hn33 => S ⋅ (S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S))) ⋅ S
  | .hn34 => S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S ⋅ S)) ⋅ S

private theorem witnessHN_spec_chk : checkAll1_StateHN (fun q =>
    noVars (witnessHN q) && decide (evalHN (witnessHN q) = q)) = true := rfl

theorem witnessHN_spec (q : StateHN) :
    noVars (witnessHN q) = true ∧ evalHN (witnessHN q) = q := by
  have h := checkAll1_StateHN_sound _ witnessHN_spec_chk q
  exact ⟨and_left h, of_decide_eq_true (and_right h)⟩

/-- Exact **12-state** minimal `S`-algebra `StateOrd2` deciding `{Order = 2}` and `{Order ≥ 2}`! -/
inductive StateOrd2 where
  | o0 | o1 | o2 | o3 | o4 | o5 | o6 | o7 | o8 | o9 | o10 | o11
  deriving DecidableEq, Repr

def checkAll1_StateOrd2 (p : StateOrd2 → Bool) : Bool :=
  ((p .o0 && p .o1) && (p .o2 && p .o3)) &&
  ((p .o4 && p .o5) && (p .o6 && p .o7)) &&
  ((p .o8 && p .o9) && (p .o10 && p .o11))

theorem checkAll1_StateOrd2_sound (p : StateOrd2 → Bool)
    (h : checkAll1_StateOrd2 p = true) (x : StateOrd2) : p x = true :=
  match x with
  | .o0 => and_left (and_left (and_left (and_left h)))
  | .o1 => and_right (and_left (and_left (and_left h)))
  | .o2 => and_left (and_right (and_left (and_left h)))
  | .o3 => and_right (and_right (and_left (and_left h)))
  | .o4 => and_left (and_left (and_right (and_left h)))
  | .o5 => and_right (and_left (and_right (and_left h)))
  | .o6 => and_left (and_right (and_right (and_left h)))
  | .o7 => and_right (and_right (and_right (and_left h)))
  | .o8 => and_left (and_left (and_right h))
  | .o9 => and_right (and_left (and_right h))
  | .o10 => and_left (and_right (and_right h))
  | .o11 => and_right (and_right (and_right h))

def checkAll2_StateOrd2 (p : StateOrd2 → StateOrd2 → Bool) : Bool :=
  checkAll1_StateOrd2 (fun x => checkAll1_StateOrd2 (fun y => p x y))

theorem checkAll2_StateOrd2_sound (p : StateOrd2 → StateOrd2 → Bool)
    (h : checkAll2_StateOrd2 p = true) (x y : StateOrd2) : p x y = true :=
  checkAll1_StateOrd2_sound _ (checkAll1_StateOrd2_sound _ h x) y

def deltaOrd2 : StateOrd2 → StateOrd2 → StateOrd2
  | .o0, y => match y with | .o0 => .o1 | .o1 => .o3 | .o2 => .o4 | .o3 => .o8 | .o8 => .o11 | .o11 => .o11 | _ => .o5
  | .o1, _ => .o2
  | .o2, y => match y with | .o0 => .o2 | .o1 => .o5 | .o3 => .o5 | .o8 => .o5 | .o11 => .o5 | _ => .o6
  | .o3, y => match y with | .o0 => .o7 | _ => .o5
  | .o4, y => match y with | .o0 => .o9 | _ => .o6
  | .o5, _ => .o6
  | .o6, _ => .o6
  | .o7, y => match y with | .o0 => .o5 | .o1 => .o5 | .o3 => .o5 | .o8 => .o5 | .o11 => .o5 | _ => .o6
  | .o8, y => match y with | .o0 => .o10 | _ => .o5
  | .o9, y => match y with | .o0 => .o5 | _ => .o6
  | .o10, y => match y with | .o0 => .o5 | _ => .o6
  | .o11, _ => .o5

def evalOrd2 : Term → StateOrd2
  | .s => .o0
  | .var _ => .o6
  | .app a b => deltaOrd2 (evalOrd2 a) (evalOrd2 b)

def projOrd2 : StateHN → StateOrd2
  | .hn0 => .o0 | .hn1 => .o1 | .hn2 => .o3 | .hn3 => .o8 | .hn4 => .o11 | .hn5 => .o11
  | .hn6 => .o2 | .hn7 => .o4 | .hn8 => .o5 | .hn9 => .o5 | .hn10 => .o5 | .hn11 => .o2
  | .hn12 => .o4 | .hn13 => .o2 | .hn14 => .o7 | .hn15 => .o5 | .hn16 => .o5 | .hn17 => .o5
  | .hn18 => .o10 | .hn19 => .o5 | .hn20 => .o5 | .hn21 => .o5 | .hn22 => .o6 | .hn23 => .o6
  | .hn24 => .o6 | .hn25 => .o6 | .hn26 => .o9 | .hn27 => .o5 | .hn28 => .o6 | .hn29 => .o6
  | .hn30 => .o6 | .hn31 => .o9 | .hn32 => .o6 | .hn33 => .o6 | .hn34 => .o6

def isOrd2Eq2 : StateOrd2 → Bool
  | .o2 | .o4 | .o5 | .o7 | .o10 => true
  | _ => false

def isOrd2Ge2 : StateOrd2 → Bool
  | .o6 | .o9 => false
  | _ => true

private theorem deltaOrd2_s_law_chk :
    checkAll1_StateOrd2 (fun x => checkAll2_StateOrd2 (fun y z =>
      decide (deltaOrd2 (deltaOrd2 (deltaOrd2 .o0 x) y) z = deltaOrd2 (deltaOrd2 x z) (deltaOrd2 y z)))) = true := rfl

theorem deltaOrd2_s_law (x y z : StateOrd2) :
    deltaOrd2 (deltaOrd2 (deltaOrd2 .o0 x) y) z = deltaOrd2 (deltaOrd2 x z) (deltaOrd2 y z) :=
  of_decide_eq_true (checkAll2_StateOrd2_sound _ (checkAll1_StateOrd2_sound _ deltaOrd2_s_law_chk x) y z)

private theorem projOrd2_hom_chk : checkAll2_StateHN (fun a b =>
    decide (projOrd2 (deltaHN a b) = deltaOrd2 (projOrd2 a) (projOrd2 b))) = true := rfl

private theorem projOrd2_order_chk : checkAll1_StateHN (fun q =>
    decide ((isOrd2Eq2 (projOrd2 q) = true ↔ orderOfStateHN q = 2) ∧
            (isOrd2Ge2 (projOrd2 q) = true ↔ 2 ≤ orderOfStateHN q))) = true := rfl

theorem evalOrd2_eq_projOrd2_open (t : Term) :
    evalOrd2 t = projOrd2 (evalHNOpen t) := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb =>
    simp only [evalOrd2, evalHNOpen, iha, ihb]
    exact (of_decide_eq_true (checkAll2_StateHN_sound _ projOrd2_hom_chk (evalHNOpen a) (evalHNOpen b))).symm

/-- **Exact Soundness & Completeness of the 12-State `S`-Algebra `StateOrd2`** (open and closed!): -/
theorem stateOrd2_decides_order2_and_ge2 (m : Term) :
    (HasExactOrder m 2 ↔ isOrd2Eq2 (evalOrd2 m) = true) ∧
    ((HasExactOrder m 2 ∨ HasExactOrder m 3) ↔ isOrd2Ge2 (evalOrd2 m) = true) := by
  rw [hasExactOrder_iff_orderOfStateHN m 2, hasExactOrder_iff_orderOfStateHN m 3,
      evalOrd2_eq_projOrd2_open m]
  cases evalHNOpen m <;> decide

def witnessOrd2 : StateOrd2 → Term
  | .o0 => S
  | .o1 => S ⋅ S
  | .o2 => S ⋅ S ⋅ S
  | .o3 => S ⋅ (S ⋅ S)
  | .o4 => S ⋅ (S ⋅ S ⋅ S)
  | .o5 => S ⋅ (S ⋅ S) ⋅ (S ⋅ S)
  | .o6 => S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S)
  | .o7 => S ⋅ (S ⋅ S) ⋅ S
  | .o8 => S ⋅ (S ⋅ (S ⋅ S))
  | .o9 => S ⋅ (S ⋅ S ⋅ S) ⋅ S
  | .o10 => S ⋅ (S ⋅ (S ⋅ S)) ⋅ S
  | .o11 => S ⋅ (S ⋅ (S ⋅ (S ⋅ S)))

private theorem witnessOrd2_spec_chk : checkAll1_StateOrd2 (fun q =>
    noVars (witnessOrd2 q) && decide (evalOrd2 (witnessOrd2 q) = q)) = true := rfl

theorem witnessOrd2_spec (q : StateOrd2) :
    noVars (witnessOrd2 q) = true ∧ evalOrd2 (witnessOrd2 q) = q := by
  have h := checkAll1_StateOrd2_sound _ witnessOrd2_spec_chk q
  exact ⟨and_left h, of_decide_eq_true (and_right h)⟩

/-- Exact **3-state** minimal `S`-algebra `StateOrd3` deciding `{Order = 3}`! -/
inductive StateOrd3 where
  | rcS | rcTower | nonRC
  deriving DecidableEq, Repr

def deltaOrd3 : StateOrd3 → StateOrd3 → StateOrd3
  | .rcS, .rcS => .rcTower
  | .rcS, .rcTower => .rcTower
  | _, _ => .nonRC

def evalOrd3 : Term → StateOrd3
  | .s => .rcS
  | .var _ => .nonRC
  | .app a b => deltaOrd3 (evalOrd3 a) (evalOrd3 b)

theorem deltaOrd3_s_law (x y z : StateOrd3) :
    deltaOrd3 (deltaOrd3 (deltaOrd3 .rcS x) y) z = deltaOrd3 (deltaOrd3 x z) (deltaOrd3 y z) := by
  cases x <;> cases y <;> cases z <;> rfl

def projOrd3 : StateHN → StateOrd3
  | .hn0 => .rcS
  | .hn1 | .hn2 | .hn3 | .hn4 | .hn5 => .rcTower
  | _ => .nonRC

private theorem projOrd3_hom_chk : checkAll2_StateHN (fun a b =>
    decide (projOrd3 (deltaHN a b) = deltaOrd3 (projOrd3 a) (projOrd3 b))) = true := rfl

theorem evalOrd3_eq_projOrd3_open (t : Term) :
    evalOrd3 t = projOrd3 (evalHNOpen t) := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb =>
    simp only [evalOrd3, evalHNOpen, iha, ihb]
    exact (of_decide_eq_true (checkAll2_StateHN_sound _ projOrd3_hom_chk (evalHNOpen a) (evalHNOpen b))).symm

theorem stateOrd3_decides_order3 (m : Term) :
    HasExactOrder m 3 ↔ evalOrd3 m ≠ .nonRC := by
  rw [evalOrd3_eq_projOrd3_open m, hasExactOrder_iff_orderOfStateHN]
  have hchk : checkAll1_StateHN (fun q => decide (orderOfStateHN q = 3 ↔ projOrd3 q ≠ .nonRC)) = true := rfl
  exact of_decide_eq_true (checkAll1_StateHN_sound _ hchk (evalHNOpen m))

def witnessOrd3 : StateOrd3 → Term
  | .rcS => S
  | .rcTower => S ⋅ S
  | .nonRC => S ⋅ S ⋅ S

theorem witnessOrd3_spec (q : StateOrd3) :
    noVars (witnessOrd3 q) = true ∧ evalOrd3 (witnessOrd3 q) = q := by
  cases q <;> exact ⟨rfl, rfl⟩

/-! ### Constructive Myhill–Nerode Context Distinguishability & Universal Cardinality Lower Bounds -/

def noVarsCtx : Ctx → Bool
  | .hole => true
  | .left c r => noVarsCtx c && noVars r
  | .right l c => noVars l && noVarsCtx c

theorem noVars_plugCtx {c : Ctx} {t : Term} (hc : noVarsCtx c = true) (ht : noVars t = true) :
    noVars (plugCtx c t) = true := by
  induction c with
  | hole => exact ht
  | left c r ih =>
    have ⟨hc', hr⟩ := (Bool.and_eq_true _ _).mp hc
    exact (Bool.and_eq_true _ _).mpr ⟨ih hc', hr⟩
  | right l c ih =>
    have ⟨hl, hc'⟩ := (Bool.and_eq_true _ _).mp hc
    exact (Bool.and_eq_true _ _).mpr ⟨hl, ih hc'⟩

def evalGen {Q : Type} (d : Q → Q → Q) (q0 : Q) : Term → Q
  | .s => q0
  | .var _ => q0
  | .app a b => d (evalGen d q0 a) (evalGen d q0 b)

theorem evalGen_plugCtx_congr {Q : Type} (d : Q → Q → Q) (q0 : Q) (c : Ctx) {t1 t2 : Term}
    (heq : evalGen d q0 t1 = evalGen d q0 t2) :
    evalGen d q0 (plugCtx c t1) = evalGen d q0 (plugCtx c t2) := by
  induction c with
  | hole => exact heq
  | left c r ih =>
    change d (evalGen d q0 (plugCtx c t1)) (evalGen d q0 r) =
      d (evalGen d q0 (plugCtx c t2)) (evalGen d q0 r)
    rw [ih]
  | right l c ih =>
    change d (evalGen d q0 l) (evalGen d q0 (plugCtx c t1)) =
      d (evalGen d q0 l) (evalGen d q0 (plugCtx c t2))
    rw [ih]

/-- Build an explicit closed `Ctx` from a sequence of `(isLeft, witnessTerm)` steps! -/
def opsToCtxAcc {S0 : Type} (wit : S0 → Term) : List (Bool × S0) → Ctx → Ctx
  | [], acc => acc
  | (true, s) :: rest, acc => opsToCtxAcc wit rest (.left acc (wit s))
  | (false, s) :: rest, acc => opsToCtxAcc wit rest (.right (wit s) acc)

def seqToCtx {S0 : Type} (wit : S0 → Term) (seq : List (Bool × S0)) : Ctx :=
  opsToCtxAcc wit seq .hole

private theorem noVarsCtx_opsToCtxAcc {S0 : Type} {wit : S0 → Term}
    (hwit : ∀ s, noVars (wit s) = true) (seq : List (Bool × S0)) :
    ∀ {acc : Ctx}, noVarsCtx acc = true → noVarsCtx (opsToCtxAcc wit seq acc) = true := by
  induction seq with
  | nil => intro _ h; exact h
  | cons hd rest ih =>
    intro acc hacc
    cases hd with
    | mk b s =>
      cases b with
      | true =>
        exact ih (acc := .left acc (wit s)) ((Bool.and_eq_true _ _).mpr ⟨hacc, hwit s⟩)
      | false =>
        exact ih (acc := .right (wit s) acc) ((Bool.and_eq_true _ _).mpr ⟨hwit s, hacc⟩)

theorem noVarsCtx_seqToCtx {S0 : Type} {wit : S0 → Term}
    (hwit : ∀ s, noVars (wit s) = true) (seq : List (Bool × S0)) :
    noVarsCtx (seqToCtx wit seq) = true :=
  noVarsCtx_opsToCtxAcc hwit seq rfl

def applySeqAlg {S0 : Type} (d : S0 → S0 → S0) : List (Bool × S0) → S0 → S0
  | [], q => q
  | (true, s) :: rest, q => applySeqAlg d rest (d q s)
  | (false, s) :: rest, q => applySeqAlg d rest (d s q)

private theorem eval_opsToCtxAcc_eq {S0 : Type} (ev : Term → S0) (d : S0 → S0 → S0)
    (wit : S0 → Term) (hev_app : ∀ a b, ev (a ⋅ b) = d (ev a) (ev b))
    (hwit : ∀ s, ev (wit s) = s) :
    ∀ (seq : List (Bool × S0)) (acc : Ctx) (t : Term),
      ev (plugCtx (opsToCtxAcc wit seq acc) t) = applySeqAlg d seq (ev (plugCtx acc t)) := by
  intro seq
  induction seq with
  | nil => intro _ _; rfl
  | cons hd rest ih =>
    intro acc t
    cases hd with
    | mk b s =>
      cases b with
      | true =>
        change ev (plugCtx (opsToCtxAcc wit rest (.left acc (wit s))) t) =
          applySeqAlg d rest (d (ev (plugCtx acc t)) s)
        rw [ih (.left acc (wit s)) t]
        change applySeqAlg d rest (ev (plugCtx acc t ⋅ wit s)) = _
        rw [hev_app, hwit]
      | false =>
        change ev (plugCtx (opsToCtxAcc wit rest (.right (wit s) acc)) t) =
          applySeqAlg d rest (d s (ev (plugCtx acc t)))
        rw [ih (.right (wit s) acc) t]
        change applySeqAlg d rest (ev (wit s ⋅ plugCtx acc t)) = _
        rw [hev_app, hwit]

theorem eval_seqToCtx_eq {S0 : Type} (ev : Term → S0) (d : S0 → S0 → S0)
    (wit : S0 → Term) (hev_app : ∀ a b, ev (a ⋅ b) = d (ev a) (ev b))
    (hwit : ∀ s, ev (wit s) = s) (seq : List (Bool × S0)) (t : Term) :
    ev (plugCtx (seqToCtx wit seq) t) = applySeqAlg d seq (ev t) :=
  eval_opsToCtxAcc_eq ev d wit hev_app hwit seq .hole t

def distSeqsHN_ord0 : List (List (Bool × StateHN)) := [
  [(true, .hn1), (true, .hn0)],
  [(true, .hn0), (true, .hn2)],
  [(true, .hn0), (true, .hn0), (true, .hn0), (true, .hn0)],
  [(false, .hn22)],
  [(true, .hn6)],
  [(true, .hn0), (true, .hn0), (true, .hn0)],
  [(true, .hn2)],
  [(true, .hn0), (true, .hn6)],
  [(true, .hn0), (true, .hn0)],
  [],
  [(true, .hn6), (true, .hn0), (true, .hn1)],
  [(true, .hn0)],
  [(false, .hn32)],
  [(true, .hn1)],
  [(false, .hn25)],
  [(true, .hn0), (true, .hn1)],
  [(true, .hn0), (true, .hn0), (true, .hn6)],
  [(true, .hn1), (true, .hn0), (true, .hn0)]
]

def distSeqsHN_ord1 : List (List (Bool × StateHN)) := [
  [(true, .hn6)],
  [(true, .hn0), (true, .hn0)],
  [(true, .hn0), (true, .hn0), (true, .hn0)],
  [(true, .hn0)],
  [(true, .hn1), (true, .hn0)],
  [(true, .hn6), (true, .hn0), (true, .hn1)],
  [(true, .hn0), (true, .hn1)],
  [],
  [(true, .hn2)],
  [(true, .hn1), (true, .hn0), (true, .hn0)],
  [(true, .hn0), (true, .hn0), (true, .hn0), (true, .hn0)],
  [(false, .hn32)],
  [(true, .hn1)]
]

def distSeqsOrd2_eq2 : List (List (Bool × StateOrd2)) := [
  [(true, .o1)],
  [],
  [(true, .o0), (true, .o0)],
  [(true, .o0)],
  [(true, .o0), (true, .o1)],
  [(true, .o1), (true, .o0)]
]

def distSeqsOrd2_ge2 : List (List (Bool × StateOrd2)) := [
  [(true, .o0), (true, .o0)],
  [(true, .o2)],
  [(true, .o0)],
  [(true, .o1), (true, .o0)],
  [],
  [(false, .o9)],
  [(true, .o1)],
  [(true, .o0), (true, .o1)]
]

private theorem dist_hn_ord0_chk : checkAll2_StateHN (fun p q =>
    decide (p = q) || FormalMinimality.listAny (fun seq =>
      decide ((orderOfStateHN (applySeqAlg deltaHN seq p) == 0) !=
              (orderOfStateHN (applySeqAlg deltaHN seq q) == 0))) distSeqsHN_ord0) = true := rfl

private theorem dist_hn_ord1_chk : checkAll2_StateHN (fun p q =>
    decide (p = q) || FormalMinimality.listAny (fun seq =>
      decide ((orderOfStateHN (applySeqAlg deltaHN seq p) == 1) !=
              (orderOfStateHN (applySeqAlg deltaHN seq q) == 1))) distSeqsHN_ord1) = true := rfl

private theorem dist_ord2_eq2_chk : checkAll2_StateOrd2 (fun p q =>
    decide (p = q) || FormalMinimality.listAny (fun seq =>
      decide (isOrd2Eq2 (applySeqAlg deltaOrd2 seq p) !=
              isOrd2Eq2 (applySeqAlg deltaOrd2 seq q))) distSeqsOrd2_eq2) = true := rfl

private theorem dist_ord2_ge2_chk : checkAll2_StateOrd2 (fun p q =>
    decide (p = q) || FormalMinimality.listAny (fun seq =>
      decide (isOrd2Ge2 (applySeqAlg deltaOrd2 seq p) !=
              isOrd2Ge2 (applySeqAlg deltaOrd2 seq q))) distSeqsOrd2_ge2) = true := rfl

private theorem bne_to_ne {a b : Bool} (h : (a != b) = true) : a ≠ b := by
  intro heq; subst heq; cases a <;> cases h

/-- **Pairwise Myhill–Nerode Context Distinguishability of All 35 States of `A_HN`**
    under BOTH `{Order = 0}` and `{Order = 1}` (hence also `{Order ≥ 1}` and 4-valued `Order`)! -/
theorem stateHN_pairwise_distinguishable_ord0_and_ord1 {p q : StateHN} (hne : p ≠ q) :
    (∃ c : Ctx, noVarsCtx c = true ∧
      (HasExactOrder (plugCtx c (witnessHN p)) 0 ↔ ¬ HasExactOrder (plugCtx c (witnessHN q)) 0)) ∧
    (∃ c : Ctx, noVarsCtx c = true ∧
      (HasExactOrder (plugCtx c (witnessHN p)) 1 ↔ ¬ HasExactOrder (plugCtx c (witnessHN q)) 1)) := by
  have h0 := checkAll2_StateHN_sound _ dist_hn_ord0_chk p q
  have h1 := checkAll2_StateHN_sound _ dist_hn_ord1_chk p q
  rw [decide_eq_false hne, Bool.false_or] at h0 h1
  obtain ⟨seq0, _, hb0⟩ := (FormalMinimality.listAny_iff _ _).mp h0
  obtain ⟨seq1, _, hb1⟩ := (FormalMinimality.listAny_iff _ _).mp h1
  have hne0 := bne_to_ne (of_decide_eq_true hb0)
  have hne1 := bne_to_ne (of_decide_eq_true hb1)
  refine ⟨⟨seqToCtx witnessHN seq0, noVarsCtx_seqToCtx (fun s => (witnessHN_spec s).1) seq0, ?_⟩,
          ⟨seqToCtx witnessHN seq1, noVarsCtx_seqToCtx (fun s => (witnessHN_spec s).1) seq1, ?_⟩⟩
  · have hvP := noVars_plugCtx (noVarsCtx_seqToCtx (fun s => (witnessHN_spec s).1) seq0) (witnessHN_spec p).1
    have hvQ := noVars_plugCtx (noVarsCtx_seqToCtx (fun s => (witnessHN_spec s).1) seq0) (witnessHN_spec q).1
    rw [closed_hasExactOrder_iff hvP 0, closed_hasExactOrder_iff hvQ 0,
        eval_seqToCtx_eq evalHN deltaHN witnessHN (fun _ _ => rfl) (fun s => (witnessHN_spec s).2) seq0,
        eval_seqToCtx_eq evalHN deltaHN witnessHN (fun _ _ => rfl) (fun s => (witnessHN_spec s).2) seq0,
        (witnessHN_spec p).2, (witnessHN_spec q).2]
    cases hp0 : (orderOfStateHN (applySeqAlg deltaHN seq0 p) == 0) <;>
    cases hq0 : (orderOfStateHN (applySeqAlg deltaHN seq0 q) == 0)
    · rw [hp0, hq0] at hne0; exact False.elim (hne0 rfl)
    · have hp_ne : orderOfStateHN (applySeqAlg deltaHN seq0 p) ≠ 0 := by
        intro he; rw [he] at hp0; cases hp0
      have hq_eq : orderOfStateHN (applySeqAlg deltaHN seq0 q) = 0 := of_decide_eq_true hq0
      exact ⟨fun h => False.elim (hp_ne h), fun hnot => False.elim (hnot hq_eq)⟩
    · have hp_eq : orderOfStateHN (applySeqAlg deltaHN seq0 p) = 0 := of_decide_eq_true hp0
      have hq_ne : orderOfStateHN (applySeqAlg deltaHN seq0 q) ≠ 0 := by
        intro he; rw [he] at hq0; cases hq0
      exact ⟨fun _ => hq_ne, fun _ => hp_eq⟩
    · rw [hp0, hq0] at hne0; exact False.elim (hne0 rfl)
  · have hvP := noVars_plugCtx (noVarsCtx_seqToCtx (fun s => (witnessHN_spec s).1) seq1) (witnessHN_spec p).1
    have hvQ := noVars_plugCtx (noVarsCtx_seqToCtx (fun s => (witnessHN_spec s).1) seq1) (witnessHN_spec q).1
    rw [closed_hasExactOrder_iff hvP 1, closed_hasExactOrder_iff hvQ 1,
        eval_seqToCtx_eq evalHN deltaHN witnessHN (fun _ _ => rfl) (fun s => (witnessHN_spec s).2) seq1,
        eval_seqToCtx_eq evalHN deltaHN witnessHN (fun _ _ => rfl) (fun s => (witnessHN_spec s).2) seq1,
        (witnessHN_spec p).2, (witnessHN_spec q).2]
    cases hp1 : (orderOfStateHN (applySeqAlg deltaHN seq1 p) == 1) <;>
    cases hq1 : (orderOfStateHN (applySeqAlg deltaHN seq1 q) == 1)
    · rw [hp1, hq1] at hne1; exact False.elim (hne1 rfl)
    · have hp_ne : orderOfStateHN (applySeqAlg deltaHN seq1 p) ≠ 1 := by
        intro he; rw [he] at hp1; cases hp1
      have hq_eq : orderOfStateHN (applySeqAlg deltaHN seq1 q) = 1 := of_decide_eq_true hq1
      exact ⟨fun h => False.elim (hp_ne h), fun hnot => False.elim (hnot hq_eq)⟩
    · have hp_eq : orderOfStateHN (applySeqAlg deltaHN seq1 p) = 1 := of_decide_eq_true hp1
      have hq_ne : orderOfStateHN (applySeqAlg deltaHN seq1 q) ≠ 1 := by
        intro he; rw [he] at hq1; cases hq1
      exact ⟨fun _ => hq_ne, fun _ => hp_eq⟩
    · rw [hp1, hq1] at hne1; exact False.elim (hne1 rfl)

/-- **Pairwise Myhill–Nerode Context Distinguishability of All 12 States of `StateOrd2`**
    under BOTH `{Order = 2}` and `{Order ≥ 2}`! -/
theorem stateOrd2_pairwise_distinguishable {p q : StateOrd2} (hne : p ≠ q) :
    (∃ c : Ctx, noVarsCtx c = true ∧
      (HasExactOrder (plugCtx c (witnessOrd2 p)) 2 ↔ ¬ HasExactOrder (plugCtx c (witnessOrd2 q)) 2)) ∧
    (∃ c : Ctx, noVarsCtx c = true ∧
      ((HasExactOrder (plugCtx c (witnessOrd2 p)) 2 ∨ HasExactOrder (plugCtx c (witnessOrd2 p)) 3) ↔
       ¬ (HasExactOrder (plugCtx c (witnessOrd2 q)) 2 ∨ HasExactOrder (plugCtx c (witnessOrd2 q)) 3))) := by
  have h2 := checkAll2_StateOrd2_sound _ dist_ord2_eq2_chk p q
  have hg := checkAll2_StateOrd2_sound _ dist_ord2_ge2_chk p q
  rw [decide_eq_false hne, Bool.false_or] at h2 hg
  obtain ⟨seq2, _, hb2⟩ := (FormalMinimality.listAny_iff _ _).mp h2
  obtain ⟨seqg, _, hbg⟩ := (FormalMinimality.listAny_iff _ _).mp hg
  have hne2 := bne_to_ne (of_decide_eq_true hb2)
  have hneg := bne_to_ne (of_decide_eq_true hbg)
  refine ⟨⟨seqToCtx witnessOrd2 seq2, noVarsCtx_seqToCtx (fun s => (witnessOrd2_spec s).1) seq2, ?_⟩,
          ⟨seqToCtx witnessOrd2 seqg, noVarsCtx_seqToCtx (fun s => (witnessOrd2_spec s).1) seqg, ?_⟩⟩
  · rw [(stateOrd2_decides_order2_and_ge2 _).1, (stateOrd2_decides_order2_and_ge2 _).1,
        eval_seqToCtx_eq evalOrd2 deltaOrd2 witnessOrd2 (fun _ _ => rfl) (fun s => (witnessOrd2_spec s).2) seq2,
        eval_seqToCtx_eq evalOrd2 deltaOrd2 witnessOrd2 (fun _ _ => rfl) (fun s => (witnessOrd2_spec s).2) seq2,
        (witnessOrd2_spec p).2, (witnessOrd2_spec q).2]
    cases hp : isOrd2Eq2 (applySeqAlg deltaOrd2 seq2 p) <;>
    cases hq : isOrd2Eq2 (applySeqAlg deltaOrd2 seq2 q)
    · rw [hp, hq] at hne2; exact False.elim (hne2 rfl)
    · exact ⟨fun h => False.elim (Bool.false_ne_true h), fun hnot => False.elim (hnot rfl)⟩
    · exact ⟨fun _ h => Bool.false_ne_true h, fun _ => rfl⟩
    · rw [hp, hq] at hne2; exact False.elim (hne2 rfl)
  · rw [(stateOrd2_decides_order2_and_ge2 _).2, (stateOrd2_decides_order2_and_ge2 _).2,
        eval_seqToCtx_eq evalOrd2 deltaOrd2 witnessOrd2 (fun _ _ => rfl) (fun s => (witnessOrd2_spec s).2) seqg,
        eval_seqToCtx_eq evalOrd2 deltaOrd2 witnessOrd2 (fun _ _ => rfl) (fun s => (witnessOrd2_spec s).2) seqg,
        (witnessOrd2_spec p).2, (witnessOrd2_spec q).2]
    cases hp : isOrd2Ge2 (applySeqAlg deltaOrd2 seqg p) <;>
    cases hq : isOrd2Ge2 (applySeqAlg deltaOrd2 seqg q)
    · rw [hp, hq] at hneg; exact False.elim (hneg rfl)
    · exact ⟨fun h => False.elim (Bool.false_ne_true h), fun hnot => False.elim (hnot rfl)⟩
    · exact ⟨fun _ h => Bool.false_ne_true h, fun _ => rfl⟩
    · rw [hp, hq] at hneg; exact False.elim (hneg rfl)

/-- **Pairwise Myhill–Nerode Context Distinguishability of All 3 States of `StateOrd3`** under `{Order = 3}`! -/
theorem stateOrd3_pairwise_distinguishable {p q : StateOrd3} (hne : p ≠ q) :
    ∃ c : Ctx, noVarsCtx c = true ∧
      (HasExactOrder (plugCtx c (witnessOrd3 p)) 3 ↔ ¬ HasExactOrder (plugCtx c (witnessOrd3 q)) 3) := by
  let c_hole : Ctx := .hole
  let c_leftS : Ctx := .left .hole S
  cases p <;> cases q
  · exfalso; exact hne rfl
  · refine ⟨c_leftS, rfl, ?_⟩
    simp only [c_leftS, plugCtx, witnessOrd3, stateOrd3_decides_order3]
    decide
  · refine ⟨c_hole, rfl, ?_⟩
    simp only [c_hole, plugCtx, witnessOrd3, stateOrd3_decides_order3]
    decide
  · refine ⟨c_leftS, rfl, ?_⟩
    simp only [c_leftS, plugCtx, witnessOrd3, stateOrd3_decides_order3]
    decide
  · exfalso; exact hne rfl
  · refine ⟨c_hole, rfl, ?_⟩
    simp only [c_hole, plugCtx, witnessOrd3, stateOrd3_decides_order3]
    decide
  · refine ⟨c_hole, rfl, ?_⟩
    simp only [c_hole, plugCtx, witnessOrd3, stateOrd3_decides_order3]
    decide
  · refine ⟨c_hole, rfl, ?_⟩
    simp only [c_hole, plugCtx, witnessOrd3, stateOrd3_decides_order3]
    decide
  · exfalso; exact hne rfl

/-! ### Constructive Pigeonhole Lower-Bound Machinery for Arbitrary Finite Tree Automata -/

private def removeFirst {Q : Type} [DecidableEq Q] (x : Q) : List Q → List Q
  | [] => []
  | y :: ys => if x = y then ys else y :: removeFirst x ys

private theorem length_removeFirst_lt {Q : Type} [DecidableEq Q] {x : Q} {ys : List Q}
    (hmem : x ∈ ys) : (removeFirst x ys).length < ys.length := by
  induction ys with
  | nil => cases hmem
  | cons y ys ih =>
    simp only [removeFirst]
    cases hd : decide (x = y) with
    | true =>
      rw [if_pos (of_decide_eq_true hd)]
      exact Nat.lt_succ_self ys.length
    | false =>
      have hne := of_decide_eq_false hd
      rw [if_neg hne]
      rcases List.mem_cons.mp hmem with heq | htail
      · exfalso; exact hne heq
      · exact Nat.succ_lt_succ (ih htail)

private theorem mem_removeFirst_of_ne {Q : Type} [DecidableEq Q] {z x : Q} {ys : List Q}
    (hz : z ∈ ys) (hne : z ≠ x) : z ∈ removeFirst x ys := by
  induction ys with
  | nil => cases hz
  | cons y ys ih =>
    simp only [removeFirst]
    cases hd : decide (x = y) with
    | true =>
      have hxy := of_decide_eq_true hd
      rw [if_pos hxy]
      rcases List.mem_cons.mp hz with rfl | htail
      · exfalso; exact hne hxy.symm
      · exact htail
    | false =>
      rw [if_neg (of_decide_eq_false hd)]
      rcases List.mem_cons.mp hz with rfl | htail
      · exact .head _
      · exact .tail _ (ih htail)

theorem nodup_subset_length_le {Q : Type} [DecidableEq Q] :
    ∀ {xs ys : List Q}, FormalMinimality.NoDupList xs → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length := by
  intro xs
  induction xs with
  | nil => intro _ _ _; exact Nat.zero_le _
  | cons x xs ih =>
    intro ys ⟨hx_not, hxs_nd⟩ hsub
    have hx_mem : x ∈ ys := hsub x (.head _)
    have hlt := length_removeFirst_lt hx_mem
    have hle := ih hxs_nd (fun z hz =>
      mem_removeFirst_of_ne (hsub z (.tail _ hz)) (fun heq => by subst heq; exact hx_not hz))
    change xs.length + 1 ≤ ys.length
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hle hlt)

theorem map_nodup_of_inj {α Q : Type} {f : α → Q} {xs : List α}
    (hnd : FormalMinimality.NoDupList xs) (hinj : ∀ a b, a ≠ b → f a ≠ f b) :
    FormalMinimality.NoDupList (xs.map f) := by
  induction xs with
  | nil => exact trivial
  | cons x xs ih =>
    have ⟨hx_not, hxs_nd⟩ := hnd
    refine ⟨?_, ih hxs_nd⟩
    intro hmem
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
    exact hinj y x (fun h => hx_not (h ▸ hy)) heq

def allStatesHNList : List StateHN :=
  [.hn0, .hn1, .hn2, .hn3, .hn4, .hn5, .hn6, .hn7, .hn8, .hn9,
   .hn10, .hn11, .hn12, .hn13, .hn14, .hn15, .hn16, .hn17, .hn18, .hn19,
   .hn20, .hn21, .hn22, .hn23, .hn24, .hn25, .hn26, .hn27, .hn28, .hn29,
   .hn30, .hn31, .hn32, .hn33, .hn34]

def allStatesOrd2List : List StateOrd2 :=
  [.o0, .o1, .o2, .o3, .o4, .o5, .o6, .o7, .o8, .o9, .o10, .o11]

def allStatesOrd3List : List StateOrd3 :=
  [.rcS, .rcTower, .nonRC]

private theorem nodup_allStatesHNList : FormalMinimality.NoDupList allStatesHNList :=
  FormalMinimality.noDupDec_sound (rfl : FormalMinimality.noDupDec allStatesHNList = true)

private theorem nodup_allStatesOrd2List : FormalMinimality.NoDupList allStatesOrd2List :=
  FormalMinimality.noDupDec_sound (rfl : FormalMinimality.noDupDec allStatesOrd2List = true)

private theorem nodup_allStatesOrd3List : FormalMinimality.NoDupList allStatesOrd3List :=
  FormalMinimality.noDupDec_sound (rfl : FormalMinimality.noDupDec allStatesOrd3List = true)

/-- **Universal 35-State Myhill–Nerode Minimality Theorem** for `{Order = 0}`, `{Order = 1}`, and `Order`:
    Any bottom-up deterministic tree automaton `(Q, d, q0)` on closed pure-`S` terms whose state set
    is covered by `univQ : List Q` and that decides `HasExactOrder t 0` (or `HasExactOrder t 1`, or
    4-valued `HasExactOrder`) MUST satisfy **`35 ≤ univQ.length`**! -/
theorem minimal_automaton_lower_bound_35 {Q : Type} [DecidableEq Q]
    (univQ : List Q) (hcov : ∀ q : Q, q ∈ univQ)
    (d : Q → Q → Q) (q0 : Q) :
    ((∃ acc0 : Q → Bool, ∀ t, noVars t = true → (acc0 (evalGen d q0 t) = true ↔ HasExactOrder t 0)) →
      35 ≤ univQ.length) ∧
    ((∃ acc1 : Q → Bool, ∀ t, noVars t = true → (acc1 (evalGen d q0 t) = true ↔ HasExactOrder t 1)) →
      35 ≤ univQ.length) ∧
    ((∃ out4 : Q → Nat, ∀ t k, noVars t = true → (out4 (evalGen d q0 t) = k ↔ HasExactOrder t k)) →
      35 ≤ univQ.length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨acc0, hspec⟩
    have hinj : ∀ a b : StateHN, a ≠ b → evalGen d q0 (witnessHN a) ≠ evalGen d q0 (witnessHN b) := by
      intro a b hne heq
      obtain ⟨⟨c, hc, hdist⟩, _⟩ := stateHN_pairwise_distinguishable_ord0_and_ord1 hne
      have hva := noVars_plugCtx hc (witnessHN_spec a).1
      have hvb := noVars_plugCtx hc (witnessHN_spec b).1
      have hcongr := evalGen_plugCtx_congr d q0 c heq
      rw [← hspec _ hva, ← hspec _ hvb, hcongr] at hdist
      cases acc0 (evalGen d q0 (plugCtx c (witnessHN b))) <;> simp at hdist
    have hnd := map_nodup_of_inj nodup_allStatesHNList hinj
    have hlen := nodup_subset_length_le hnd (fun x _ => hcov x)
    rw [List.length_map] at hlen
    exact hlen
  · intro ⟨acc1, hspec⟩
    have hinj : ∀ a b : StateHN, a ≠ b → evalGen d q0 (witnessHN a) ≠ evalGen d q0 (witnessHN b) := by
      intro a b hne heq
      obtain ⟨_, ⟨c, hc, hdist⟩⟩ := stateHN_pairwise_distinguishable_ord0_and_ord1 hne
      have hva := noVars_plugCtx hc (witnessHN_spec a).1
      have hvb := noVars_plugCtx hc (witnessHN_spec b).1
      have hcongr := evalGen_plugCtx_congr d q0 c heq
      rw [← hspec _ hva, ← hspec _ hvb, hcongr] at hdist
      cases acc1 (evalGen d q0 (plugCtx c (witnessHN b))) <;> simp at hdist
    have hnd := map_nodup_of_inj nodup_allStatesHNList hinj
    have hlen := nodup_subset_length_le hnd (fun x _ => hcov x)
    rw [List.length_map] at hlen
    exact hlen
  · intro ⟨out4, hspec⟩
    have hinj : ∀ a b : StateHN, a ≠ b → evalGen d q0 (witnessHN a) ≠ evalGen d q0 (witnessHN b) := by
      intro a b hne heq
      obtain ⟨⟨c, hc, hdist⟩, _⟩ := stateHN_pairwise_distinguishable_ord0_and_ord1 hne
      have hva := noVars_plugCtx hc (witnessHN_spec a).1
      have hvb := noVars_plugCtx hc (witnessHN_spec b).1
      have hcongr := evalGen_plugCtx_congr d q0 c heq
      rw [← hspec _ 0 hva, ← hspec _ 0 hvb, hcongr] at hdist
      exact if h0 : out4 (evalGen d q0 (plugCtx c (witnessHN b))) = 0 then
        (hdist.mp h0) h0
      else
        h0 (hdist.mpr h0)
    have hnd := map_nodup_of_inj nodup_allStatesHNList hinj
    have hlen := nodup_subset_length_le hnd (fun x _ => hcov x)
    rw [List.length_map] at hlen
    exact hlen

/-- **Universal 12-State Myhill–Nerode Minimality Theorem** for `{Order = 2}` and `{Order ≥ 2}`! -/
theorem minimal_automaton_lower_bound_12 {Q : Type} [DecidableEq Q]
    (univQ : List Q) (hcov : ∀ q : Q, q ∈ univQ)
    (d : Q → Q → Q) (q0 : Q) :
    ((∃ acc2 : Q → Bool, ∀ t, noVars t = true → (acc2 (evalGen d q0 t) = true ↔ HasExactOrder t 2)) →
      12 ≤ univQ.length) ∧
    ((∃ accGe2 : Q → Bool, ∀ t, noVars t = true →
        (accGe2 (evalGen d q0 t) = true ↔ (HasExactOrder t 2 ∨ HasExactOrder t 3))) →
      12 ≤ univQ.length) := by
  refine ⟨?_, ?_⟩
  · intro ⟨acc2, hspec⟩
    have hinj : ∀ a b : StateOrd2, a ≠ b → evalGen d q0 (witnessOrd2 a) ≠ evalGen d q0 (witnessOrd2 b) := by
      intro a b hne heq
      obtain ⟨⟨c, hc, hdist⟩, _⟩ := stateOrd2_pairwise_distinguishable hne
      have hva := noVars_plugCtx hc (witnessOrd2_spec a).1
      have hvb := noVars_plugCtx hc (witnessOrd2_spec b).1
      have hcongr := evalGen_plugCtx_congr d q0 c heq
      rw [← hspec _ hva, ← hspec _ hvb, hcongr] at hdist
      cases acc2 (evalGen d q0 (plugCtx c (witnessOrd2 b))) <;> simp at hdist
    have hnd := map_nodup_of_inj nodup_allStatesOrd2List hinj
    have hlen := nodup_subset_length_le hnd (fun x _ => hcov x)
    rw [List.length_map] at hlen
    exact hlen
  · intro ⟨accGe2, hspec⟩
    have hinj : ∀ a b : StateOrd2, a ≠ b → evalGen d q0 (witnessOrd2 a) ≠ evalGen d q0 (witnessOrd2 b) := by
      intro a b hne heq
      obtain ⟨_, ⟨c, hc, hdist⟩⟩ := stateOrd2_pairwise_distinguishable hne
      have hva := noVars_plugCtx hc (witnessOrd2_spec a).1
      have hvb := noVars_plugCtx hc (witnessOrd2_spec b).1
      have hcongr := evalGen_plugCtx_congr d q0 c heq
      rw [← hspec _ hva, ← hspec _ hvb, hcongr] at hdist
      cases accGe2 (evalGen d q0 (plugCtx c (witnessOrd2 b))) <;> simp at hdist
    have hnd := map_nodup_of_inj nodup_allStatesOrd2List hinj
    have hlen := nodup_subset_length_le hnd (fun x _ => hcov x)
    rw [List.length_map] at hlen
    exact hlen

/-- **Universal 3-State Myhill–Nerode Minimality Theorem** for `{Order = 3}`! -/
theorem minimal_automaton_lower_bound_3 {Q : Type} [DecidableEq Q]
    (univQ : List Q) (hcov : ∀ q : Q, q ∈ univQ)
    (d : Q → Q → Q) (q0 : Q)
    (h3 : ∃ acc3 : Q → Bool, ∀ t, noVars t = true → (acc3 (evalGen d q0 t) = true ↔ HasExactOrder t 3)) :
    3 ≤ univQ.length := by
  obtain ⟨acc3, hspec⟩ := h3
  have hinj : ∀ a b : StateOrd3, a ≠ b → evalGen d q0 (witnessOrd3 a) ≠ evalGen d q0 (witnessOrd3 b) := by
    intro a b hne heq
    obtain ⟨c, hc, hdist⟩ := stateOrd3_pairwise_distinguishable hne
    have hva := noVars_plugCtx hc (witnessOrd3_spec a).1
    have hvb := noVars_plugCtx hc (witnessOrd3_spec b).1
    have hcongr := evalGen_plugCtx_congr d q0 c heq
    rw [← hspec _ hva, ← hspec _ hvb, hcongr] at hdist
    cases acc3 (evalGen d q0 (plugCtx c (witnessOrd3 b))) <;> simp at hdist
  have hnd := map_nodup_of_inj nodup_allStatesOrd3List hinj
  have hlen := nodup_subset_length_le hnd (fun x _ => hcov x)
  rw [List.length_map] at hlen
  exact hlen

end FormalOrderAndIsolated

#print axioms FormalOrderAndIsolated.open_hasSHeadHNF_iff
#print axioms FormalOrderAndIsolated.isDummyTail_iff_evalHNOpen_eq_hn34
#print axioms FormalOrderAndIsolated.hasExactOrder_iff_orderOfStateHN
#print axioms FormalOrderAndIsolated.visser_van_oostrom_exact_order_exhaustion
#print axioms FormalOrderAndIsolated.closed_order_operational_characterization
#print axioms FormalOrderAndIsolated.closed_order3_iff_rightComb
#print axioms FormalOrderAndIsolated.minimal_order_thresholds_1_to_5
#print axioms FormalOrderAndIsolated.stateOrd2_decides_order2_and_ge2
#print axioms FormalOrderAndIsolated.stateOrd3_decides_order3
#print axioms FormalOrderAndIsolated.minimal_automaton_lower_bound_35
#print axioms FormalOrderAndIsolated.minimal_automaton_lower_bound_12
#print axioms FormalOrderAndIsolated.minimal_automaton_lower_bound_3
