import formal_algebra.all_algebra_open_problems
import intrinsic_research.intrinsic_theorems

/-!
# Analytic & Algebraic Combinatorics of Pure-`S` Phase Transitions (`CL(S)`)

Constructive, axiom-free Lean 4.33.1 formalization (`namespace FormalAsymptotics`) of the
macroscopic asymptotic laws governing pure-`S` combinator space as leaf count `n → ∞`:
1. **Duplicate-Free Sound & Complete Catalan Tree Enumeration (`treesOfSize`) & Exact DP Equivalence**:
   - `catalanTrees` (`countTrees`), `countSN`, `countHN`, `countNonHN`, and `countAcceptP` defined via
     their exact bottom-up dynamic programming recurrences and proved equal to `(treesOfSize n).length`
     and `((treesOfSize n).filter ...).length`, with fast memoized verification through `n = 20`.
2. **Exact Algebraic Ideal Dichotomy & Universal Hierarchy (`SN ⊆ AcceptP ⊆ HN`)**:
   - `sn38_two_sided_ideal` & `sn38_subterm_absorbing`: `.sn38` is a strict two-sided absorbing sink in `A_SN`.
   - `p37_two_sided_ideal` & `p37_subterm_absorbing`: `.p37` is a strict two-sided absorbing sink in `A_P`.
   - `hn34_left_ideal_not_right_ideal` & `s_app_always_hasHNF`: `.hn34` is left-absorbing but NOT
     right-absorbing (`deltaHN .hn0 .hn34 = .hn10 ≠ .hn34`), shielding arbitrary right subtrees in `S ⋅ r`
     and `S ⋅ a ⋅ b`.
   - `universal_count_hierarchy`: `countSN n ≤ countAcceptP n ≤ countHN n ≤ catalanTrees n` for all `n`.
3. **Universal Positive Two-Sided Density Bounds for `HasHNF`**:
   - Lower bounds: `catalanTrees (n - 1) ≤ countHN n` (`∀ n ≥ 2`), `catalanTrees (n - 1) + catalanTrees (n - 2) ≤ countHN n`
     (`∀ n ≥ 2`), and `2 * catalanTrees (n - 1) ≤ countHN n` (`∀ n ≥ 3`, establishing density `> 1/2 > 1/4`).
   - Upper bound: `catalanTrees (n - 8) ≤ countNonHN n` and `countHN n + catalanTrees (n - 8) ≤ catalanTrees n`
     (`∀ n ≥ 9`, via left-absorption of the 8-leaf `.hn34` witness `S(SSS)S(SSS)`).
4. **Universal Constructive Exponential Decay Bounds on `#SN(n)` and `#AcceptP(n)` (`∀ n ≥ 1`)**:
   - Certified integer generating-function majorant at `z = 37/125` (`125/37 ≈ 3.37838 < 7/2 < 4`)
     combined with the universal Catalan exponential lower bound `7^n ≤ 58 * 2^n * catalanTrees n`:
     `100000 * 259^n * countSN n ≤ 100000 * 259^n * countAcceptP n ≤ 5142860 * 250^n * catalanTrees n` (`∀ n ≥ 1`).

Verified with zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`, and zero `Classical.choice`.
-/

namespace FormalAsymptotics

open FormalAlgebra (StateSN StateHN CNF Step Reduces S leaves noVars spineLen
  HasHNF StrongNormalizing deltaSN deltaHN evalSN evalHN
  checkAll1_StateSN checkAll1_StateSN_sound checkAll1_StateHN checkAll1_StateHN_sound
  deltaSN_sn38_left deltaSN_sn38_right deltaHN_hn34_left deltaHN_s1_ne_hn34 deltaHN_s2_ne_hn34
  closed_evalSN_ne_sn38_reduces_cnf waldmann_theorem_9 leaves_pos imp_bool)
open IntrinsicTheorems (StateP delta_StateP checkAll1_StateP checkAll1_StateP_sound)

abbrev Term := FormalAlgebra.Term
local notation "S" => FormalAlgebra.Term.s
local infixl:70 " ⋆ " => FormalAlgebra.Term.app

private theorem bool_eq_true_or_false (b : Bool) : b = true ∨ b = false :=
  match b with
  | true => Or.inl rfl
  | false => Or.inr rfl

private theorem pow_pos_of_pos {b : Nat} (hb : 0 < b) (n : Nat) : 0 < b ^ n := by
  induction n with
  | zero => rw [Nat.pow_zero]; exact Nat.zero_lt_one
  | succ k ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih hb

/-! ## 1. Syntax Bijection (`FormalAlgebra.Term ↔ IntrinsicTheorems.Term`), `evalPTerm`, and Subterms -/

def toIntrinsic : Term → IntrinsicTheorems.Term
  | .s => .s
  | .var k => .var k
  | .app a b => .app (toIntrinsic a) (toIntrinsic b)

def ofIntrinsic : IntrinsicTheorems.Term → Term
  | .s => .s
  | .var k => .var k
  | .app a b => .app (ofIntrinsic a) (ofIntrinsic b)

theorem ofIntrinsic_toIntrinsic (t : Term) : ofIntrinsic (toIntrinsic t) = t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp only [toIntrinsic, ofIntrinsic, iha, ihb]

theorem toIntrinsic_ofIntrinsic (u : IntrinsicTheorems.Term) : toIntrinsic (ofIntrinsic u) = u := by
  induction u with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp only [ofIntrinsic, toIntrinsic, iha, ihb]

theorem toIntrinsic_step {a b : Term} (h : Step a b) :
    IntrinsicTheorems.Step (toIntrinsic a) (toIntrinsic b) := by
  induction h with
  | root x y z => exact IntrinsicTheorems.Step.root (toIntrinsic x) (toIntrinsic y) (toIntrinsic z)
  | left _ ih => exact IntrinsicTheorems.Step.left ih
  | right _ ih => exact IntrinsicTheorems.Step.right ih

theorem toIntrinsic_reduces {a b : Term} (h : Reduces a b) :
    IntrinsicTheorems.Reduces (toIntrinsic a) (toIntrinsic b) := by
  induction h with
  | refl _ => exact IntrinsicTheorems.Reduces.refl _
  | next hs _ ih => exact IntrinsicTheorems.Reduces.next (toIntrinsic_step hs) ih

def evalPTerm (t : Term) : StateP :=
  IntrinsicTheorems.evalP (toIntrinsic t)

theorem evalPTerm_s : evalPTerm .s = .p0 := rfl
theorem evalPTerm_var (_k : Nat) : evalPTerm (.var _k) = .p0 := rfl
theorem evalPTerm_app (a b : Term) : evalPTerm (.app a b) = delta_StateP (evalPTerm a) (evalPTerm b) := rfl

theorem evalPTerm_step {a b : Term} (h : Step a b) : evalPTerm a = evalPTerm b :=
  IntrinsicTheorems.evalP_step_invariant (toIntrinsic_step h)

theorem evalPTerm_reduces {a b : Term} (h : Reduces a b) : evalPTerm a = evalPTerm b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalPTerm_step hs).trans ih

/-- Constructive subterm relation on `FormalAlgebra.Term`. -/
inductive hasSubterm (u : Term) : Term → Prop where
  | refl : hasSubterm u u
  | left {a b : Term} : hasSubterm u a → hasSubterm u (.app a b)
  | right {a b : Term} : hasSubterm u b → hasSubterm u (.app a b)

/-- Constructive subterm relation on `IntrinsicTheorems.Term`. -/
inductive hasSubtermIntrinsic (u : IntrinsicTheorems.Term) : IntrinsicTheorems.Term → Prop where
  | refl : hasSubtermIntrinsic u u
  | left {a b : IntrinsicTheorems.Term} : hasSubtermIntrinsic u a → hasSubtermIntrinsic u (.app a b)
  | right {a b : IntrinsicTheorems.Term} : hasSubtermIntrinsic u b → hasSubtermIntrinsic u (.app a b)

theorem noVars_of_hasSubterm {u t : Term} (hsub : hasSubterm u t) (hv : noVars t = true) :
    noVars u = true := by
  induction hsub with
  | refl => exact hv
  | @left a b _ ih => exact ih ((Bool.and_eq_true (noVars a) (noVars b)).mp hv).1
  | @right a b _ ih => exact ih ((Bool.and_eq_true (noVars a) (noVars b)).mp hv).2

/-! ## 2. Algebraic Ideal Dichotomy Theorems (`A_SN`, `A_P`, `A_HN`) & Universal Hierarchy -/

/-- **Two-Sided Absorbing Ideal Law for `A_SN`**: `.sn38` is a strict two-sided sink. -/
theorem sn38_two_sided_ideal (q : FormalAlgebra.StateSN) :
    FormalAlgebra.deltaSN .sn38 q = .sn38 ∧ FormalAlgebra.deltaSN q .sn38 = .sn38 :=
  ⟨deltaSN_sn38_left q, deltaSN_sn38_right q⟩

/-- Any pure-`S` term containing a `.sn38` subterm anywhere inside it evaluates to `.sn38`. -/
theorem sn38_subterm_absorbing {u t : Term} (hsub : hasSubterm u t) (hu : evalSN u = .sn38) :
    evalSN t = .sn38 := by
  induction hsub with
  | refl => exact hu
  | @left a b _ ih =>
    change deltaSN (evalSN a) (evalSN b) = .sn38
    rw [ih]
    exact deltaSN_sn38_left (evalSN b)
  | @right a b _ ih =>
    change deltaSN (evalSN a) (evalSN b) = .sn38
    rw [ih]
    exact deltaSN_sn38_right (evalSN a)

/-- Constructive semantic lift: any closed pure-`S` term containing a non-`SN` subterm is non-`SN`. -/
theorem non_sn_subterm_contagion {u t : Term} (hv : noVars t = true)
    (hsub : hasSubterm u t) (hnsn : ¬ StrongNormalizing u) : ¬ StrongNormalizing t := by
  intro hsnt
  have hvu := noVars_of_hasSubterm hsub hv
  have hne_t : evalSN t ≠ .sn38 := (waldmann_theorem_9 hv).1.mp hsnt
  cases hu38 : decide (evalSN u = .sn38) with
  | true =>
    exact hne_t (sn38_subterm_absorbing hsub (of_decide_eq_true hu38))
  | false =>
    have hne_u : evalSN u ≠ .sn38 := of_decide_eq_false hu38
    exact hnsn ((waldmann_theorem_9 hvu).1.mpr hne_u)

/-- **Two-Sided Absorbing Ideal Law for `A_P`**: `.p37` is a strict two-sided sink. -/
theorem p37_two_sided_ideal (q : IntrinsicTheorems.StateP) :
    IntrinsicTheorems.delta_StateP .p37 q = .p37 ∧ IntrinsicTheorems.delta_StateP q .p37 = .p37 :=
  IntrinsicTheorems.deltaP_sink q

/-- Any `IntrinsicTheorems.Term` containing a `.p37` subterm anywhere inside it evaluates to `.p37`. -/
theorem p37_subterm_absorbing {u t : IntrinsicTheorems.Term}
    (hsub : hasSubtermIntrinsic u t) (hu : IntrinsicTheorems.evalP u = .p37) :
    IntrinsicTheorems.evalP t = .p37 := by
  induction hsub with
  | refl => exact hu
  | @left a b _ ih =>
    change delta_StateP (IntrinsicTheorems.evalP a) (IntrinsicTheorems.evalP b) = .p37
    rw [ih]
    exact (IntrinsicTheorems.deltaP_sink _).1
  | @right a b _ ih =>
    change delta_StateP (IntrinsicTheorems.evalP a) (IntrinsicTheorems.evalP b) = .p37
    rw [ih]
    exact (IntrinsicTheorems.deltaP_sink _).2

/-- Equivalent subterm sink theorem on `FormalAlgebra.Term` via `evalPTerm`. -/
theorem p37_subterm_absorbing_term {u t : Term}
    (hsub : hasSubterm u t) (hu : evalPTerm u = .p37) :
    evalPTerm t = .p37 := by
  induction hsub with
  | refl => exact hu
  | @left a b _ ih =>
    change delta_StateP (evalPTerm a) (evalPTerm b) = .p37
    rw [ih]
    exact (IntrinsicTheorems.deltaP_sink _).1
  | @right a b _ ih =>
    change delta_StateP (evalPTerm a) (evalPTerm b) = .p37
    rw [ih]
    exact (IntrinsicTheorems.deltaP_sink _).2

/-- **Left-Only Ideal Shielding Law for `A_HN`**:
    `.hn34` is strictly left-absorbing (`∀ q, deltaHN .hn34 q = .hn34`), NOT right-absorbing
    (`deltaHN .hn0 .hn34 = .hn10 ≠ .hn34`). -/
theorem hn34_left_ideal_not_right_ideal :
    (∀ q : FormalAlgebra.StateHN, FormalAlgebra.deltaHN .hn34 q = .hn34) ∧
    FormalAlgebra.deltaHN .hn0 .hn34 ≠ .hn34 :=
  ⟨deltaHN_hn34_left, by decide⟩

/-- Every application `S ⋅ r` is immediately a 1-HNF (`spineLen = 1 ≤ 2`), even when `r` has no HNF! -/
theorem s_app_always_hasHNF (r : FormalAlgebra.Term) (_hr : FormalAlgebra.noVars r = true) :
    FormalAlgebra.HasHNF (.app .s r) :=
  ⟨.app .s r, FormalAlgebra.Reduces.refl _, Nat.succ_le_succ (Nat.zero_le 1)⟩

/-- Every application `S ⋅ a ⋅ b` is immediately a 2-HNF (`spineLen = 2 ≤ 2`), shielding both `a` and `b`. -/
theorem s_app2_always_hasHNF (a b : FormalAlgebra.Term) :
    FormalAlgebra.HasHNF (.app (.app .s a) b) ∧ FormalAlgebra.evalHN (.app (.app .s a) b) ≠ .hn34 :=
  ⟨⟨.app (.app .s a) b, FormalAlgebra.Reduces.refl _, Nat.le_refl 2⟩,
   deltaHN_s2_ne_hn34 (evalHN a) (evalHN b)⟩

/-- Constructive proof of `SN ⊆ AcceptP` for closed pure-`S` terms via `CNF` normalization. -/
private theorem cnf_evalPTerm_isAccP (c : CNF) : IntrinsicTheorems.isAccP (evalPTerm c.toTerm) = true := by
  induction c with
  | s => rfl
  | s1 u ih =>
    change IntrinsicTheorems.isAccP (delta_StateP .p0 (evalPTerm u.toTerm)) = true
    rw [IntrinsicTheorems.deltaP_hnf1_iff]
    exact ih
  | s2 u v ihu ihv =>
    change IntrinsicTheorems.isAccP (delta_StateP (delta_StateP .p0 (evalPTerm u.toTerm)) (evalPTerm v.toTerm)) = true
    rw [IntrinsicTheorems.deltaP_hnf2_iff, ihu, ihv]
    rfl

theorem evalSN_ne_sn38_implies_evalPTerm_ne_p37 {t : Term}
    (hv : noVars t = true) (hsn : evalSN t ≠ .sn38) : evalPTerm t ≠ .p37 := by
  obtain ⟨c, hred⟩ := closed_evalSN_ne_sn38_reduces_cnf hv hsn
  have hacc : IntrinsicTheorems.isAccP (evalPTerm t) = true := by
    rw [evalPTerm_reduces hred]
    exact cnf_evalPTerm_isAccP c
  intro hp37
  rw [hp37] at hacc
  cases hacc

def isReachPH : StateP → StateHN → Bool
  | .p0, y => match y with | .hn0 => true | _ => false
  | .p1, y => match y with | .hn1 => true | _ => false
  | .p2, y => match y with | .hn2 => true | _ => false
  | .p3, y => match y with | .hn6 => true | _ => false
  | .p4, y => match y with | .hn3 => true | _ => false
  | .p5, y => match y with | .hn7 => true | _ => false
  | .p6, y => match y with | .hn11 => true | _ => false
  | .p7, y => match y with | .hn13 => true | .hn14 => true | _ => false
  | .p8, y => match y with | .hn4 => true | .hn12 => true | _ => false
  | .p9, y => match y with | .hn5 => true | .hn8 => true | .hn12 => true | .hn13 => true | _ => false
  | .p10, y => match y with | .hn12 => true | _ => false
  | .p11, y => match y with | .hn12 => true | .hn15 => true | _ => false
  | .p12, y => match y with | .hn13 => true | _ => false
  | .p13, y => match y with | .hn13 => true | _ => false
  | .p14, y => match y with | .hn16 => true | _ => false
  | .p15, y => match y with | .hn8 => true | .hn13 => true | _ => false
  | .p16, y => match y with | .hn13 => true | .hn18 => true | _ => false
  | .p17, y => match y with | .hn13 => true | .hn26 => true | _ => false
  | .p18, y => match y with | .hn5 => true | .hn8 => true | .hn9 => true | .hn10 => true | .hn12 => true | .hn13 => true | .hn19 => true | .hn21 => true | .hn27 => true | _ => false
  | .p19, y => match y with | .hn12 => true | _ => false
  | .p20, y => match y with | .hn12 => true | .hn13 => true | .hn27 => true | _ => false
  | .p21, y => match y with | .hn13 => true | _ => false
  | .p22, y => match y with | .hn13 => true | _ => false
  | .p23, y => match y with | .hn13 => true | .hn17 => true | _ => false
  | .p24, y => match y with | .hn10 => true | .hn13 => true | .hn17 => true | .hn20 => true | .hn22 => true | .hn24 => true | .hn25 => true | .hn29 => true | .hn30 => true | .hn31 => true | _ => false
  | .p25, y => match y with | .hn13 => true | .hn20 => true | _ => false
  | .p26, y => match y with | .hn13 => true | .hn28 => true | _ => false
  | .p27, y => match y with | .hn8 => true | .hn10 => true | .hn13 => true | .hn17 => true | .hn20 => true | .hn29 => true | .hn31 => true | _ => false
  | .p28, y => match y with | .hn13 => true | .hn31 => true | _ => false
  | .p29, y => match y with | .hn10 => true | .hn13 => true | .hn17 => true | .hn20 => true | .hn22 => true | .hn23 => true | .hn24 => true | .hn25 => true | .hn29 => true | .hn30 => true | .hn31 => true | .hn32 => true | .hn33 => true | _ => false
  | .p30, y => match y with | .hn13 => true | _ => false
  | .p31, y => match y with | .hn13 => true | _ => false
  | .p32, y => match y with | .hn13 => true | _ => false
  | .p33, y => match y with | .hn9 => true | .hn10 => true | .hn13 => true | .hn17 => true | _ => false
  | .p34, y => match y with | .hn13 => true | .hn30 => true | _ => false
  | .p35, y => match y with | .hn13 => true | .hn29 => true | .hn31 => true | _ => false
  | .p36, y => match y with | .hn13 => true | .hn29 => true | _ => false
  | .p37, y => match y with | .hn8 => true | .hn9 => true | .hn10 => true | .hn12 => true | .hn13 => true | .hn17 => true | .hn20 => true | .hn21 => true | .hn22 => true | .hn23 => true | .hn24 => true | .hn25 => true | .hn27 => true | .hn29 => true | .hn30 => true | .hn31 => true | .hn33 => true | .hn34 => true | _ => false
  | .p38, y => match y with | .hn13 => true | _ => false

private theorem ph_closed_row_0 : checkAll1_StateHN (fun h1 => (!isReachPH .p0 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p0 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_1 : checkAll1_StateHN (fun h1 => (!isReachPH .p1 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p1 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_2 : checkAll1_StateHN (fun h1 => (!isReachPH .p2 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p2 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_3 : checkAll1_StateHN (fun h1 => (!isReachPH .p3 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p3 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_4 : checkAll1_StateHN (fun h1 => (!isReachPH .p4 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p4 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_5 : checkAll1_StateHN (fun h1 => (!isReachPH .p5 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p5 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_6 : checkAll1_StateHN (fun h1 => (!isReachPH .p6 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p6 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_7 : checkAll1_StateHN (fun h1 => (!isReachPH .p7 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p7 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_8 : checkAll1_StateHN (fun h1 => (!isReachPH .p8 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p8 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_9 : checkAll1_StateHN (fun h1 => (!isReachPH .p9 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p9 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_10 : checkAll1_StateHN (fun h1 => (!isReachPH .p10 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p10 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_11 : checkAll1_StateHN (fun h1 => (!isReachPH .p11 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p11 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_12 : checkAll1_StateHN (fun h1 => (!isReachPH .p12 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p12 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_13 : checkAll1_StateHN (fun h1 => (!isReachPH .p13 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p13 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_14 : checkAll1_StateHN (fun h1 => (!isReachPH .p14 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p14 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_15 : checkAll1_StateHN (fun h1 => (!isReachPH .p15 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p15 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_16 : checkAll1_StateHN (fun h1 => (!isReachPH .p16 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p16 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_17 : checkAll1_StateHN (fun h1 => (!isReachPH .p17 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p17 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_18 : checkAll1_StateHN (fun h1 => (!isReachPH .p18 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p18 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_19 : checkAll1_StateHN (fun h1 => (!isReachPH .p19 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p19 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_20 : checkAll1_StateHN (fun h1 => (!isReachPH .p20 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p20 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_21 : checkAll1_StateHN (fun h1 => (!isReachPH .p21 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p21 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_22 : checkAll1_StateHN (fun h1 => (!isReachPH .p22 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p22 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_23 : checkAll1_StateHN (fun h1 => (!isReachPH .p23 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p23 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_24 : checkAll1_StateHN (fun h1 => (!isReachPH .p24 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p24 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_25 : checkAll1_StateHN (fun h1 => (!isReachPH .p25 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p25 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_26 : checkAll1_StateHN (fun h1 => (!isReachPH .p26 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p26 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_27 : checkAll1_StateHN (fun h1 => (!isReachPH .p27 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p27 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_28 : checkAll1_StateHN (fun h1 => (!isReachPH .p28 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p28 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_29 : checkAll1_StateHN (fun h1 => (!isReachPH .p29 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p29 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_30 : checkAll1_StateHN (fun h1 => (!isReachPH .p30 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p30 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_31 : checkAll1_StateHN (fun h1 => (!isReachPH .p31 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p31 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_32 : checkAll1_StateHN (fun h1 => (!isReachPH .p32 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p32 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_33 : checkAll1_StateHN (fun h1 => (!isReachPH .p33 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p33 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_34 : checkAll1_StateHN (fun h1 => (!isReachPH .p34 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p34 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_35 : checkAll1_StateHN (fun h1 => (!isReachPH .p35 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p35 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_36 : checkAll1_StateHN (fun h1 => (!isReachPH .p36 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p36 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_37 : checkAll1_StateHN (fun h1 => (!isReachPH .p37 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p37 pb) (deltaHN h1 h2)))))) = true := rfl
private theorem ph_closed_row_38 : checkAll1_StateHN (fun h1 => (!isReachPH .p38 h1 || checkAll1_StateP (fun pb => checkAll1_StateHN (fun h2 => (!isReachPH pb h2 || isReachPH (delta_StateP .p38 pb) (deltaHN h1 h2)))))) = true := rfl

theorem isReachPH_closed {pa pb : StateP} {h1 h2 : StateHN}
    (hp1 : isReachPH pa h1 = true) (hp2 : isReachPH pb h2 = true) :
    isReachPH (delta_StateP pa pb) (deltaHN h1 h2) = true := by
  have hr : (!isReachPH pa h1 || checkAll1_StateP (fun pb' => checkAll1_StateHN (fun h2' => (!isReachPH pb' h2' || isReachPH (delta_StateP pa pb') (deltaHN h1 h2'))))) = true :=
    match pa with
    | .p0 => checkAll1_StateHN_sound _ ph_closed_row_0 h1
    | .p1 => checkAll1_StateHN_sound _ ph_closed_row_1 h1
    | .p2 => checkAll1_StateHN_sound _ ph_closed_row_2 h1
    | .p3 => checkAll1_StateHN_sound _ ph_closed_row_3 h1
    | .p4 => checkAll1_StateHN_sound _ ph_closed_row_4 h1
    | .p5 => checkAll1_StateHN_sound _ ph_closed_row_5 h1
    | .p6 => checkAll1_StateHN_sound _ ph_closed_row_6 h1
    | .p7 => checkAll1_StateHN_sound _ ph_closed_row_7 h1
    | .p8 => checkAll1_StateHN_sound _ ph_closed_row_8 h1
    | .p9 => checkAll1_StateHN_sound _ ph_closed_row_9 h1
    | .p10 => checkAll1_StateHN_sound _ ph_closed_row_10 h1
    | .p11 => checkAll1_StateHN_sound _ ph_closed_row_11 h1
    | .p12 => checkAll1_StateHN_sound _ ph_closed_row_12 h1
    | .p13 => checkAll1_StateHN_sound _ ph_closed_row_13 h1
    | .p14 => checkAll1_StateHN_sound _ ph_closed_row_14 h1
    | .p15 => checkAll1_StateHN_sound _ ph_closed_row_15 h1
    | .p16 => checkAll1_StateHN_sound _ ph_closed_row_16 h1
    | .p17 => checkAll1_StateHN_sound _ ph_closed_row_17 h1
    | .p18 => checkAll1_StateHN_sound _ ph_closed_row_18 h1
    | .p19 => checkAll1_StateHN_sound _ ph_closed_row_19 h1
    | .p20 => checkAll1_StateHN_sound _ ph_closed_row_20 h1
    | .p21 => checkAll1_StateHN_sound _ ph_closed_row_21 h1
    | .p22 => checkAll1_StateHN_sound _ ph_closed_row_22 h1
    | .p23 => checkAll1_StateHN_sound _ ph_closed_row_23 h1
    | .p24 => checkAll1_StateHN_sound _ ph_closed_row_24 h1
    | .p25 => checkAll1_StateHN_sound _ ph_closed_row_25 h1
    | .p26 => checkAll1_StateHN_sound _ ph_closed_row_26 h1
    | .p27 => checkAll1_StateHN_sound _ ph_closed_row_27 h1
    | .p28 => checkAll1_StateHN_sound _ ph_closed_row_28 h1
    | .p29 => checkAll1_StateHN_sound _ ph_closed_row_29 h1
    | .p30 => checkAll1_StateHN_sound _ ph_closed_row_30 h1
    | .p31 => checkAll1_StateHN_sound _ ph_closed_row_31 h1
    | .p32 => checkAll1_StateHN_sound _ ph_closed_row_32 h1
    | .p33 => checkAll1_StateHN_sound _ ph_closed_row_33 h1
    | .p34 => checkAll1_StateHN_sound _ ph_closed_row_34 h1
    | .p35 => checkAll1_StateHN_sound _ ph_closed_row_35 h1
    | .p36 => checkAll1_StateHN_sound _ ph_closed_row_36 h1
    | .p37 => checkAll1_StateHN_sound _ ph_closed_row_37 h1
    | .p38 => checkAll1_StateHN_sound _ ph_closed_row_38 h1
  have hr' := imp_bool hp1 hr
  have hc := checkAll1_StateHN_sound _ (checkAll1_StateP_sound _ hr' pb) h2
  exact imp_bool hp2 hc

theorem eval_isReachPH {t : Term} (hv : noVars t = true) :
    isReachPH (evalPTerm t) (evalHN t) = true := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    exact isReachPH_closed (iha ((Bool.and_eq_true _ _).mp hv).1) (ihb ((Bool.and_eq_true _ _).mp hv).2)

private theorem ph_acc_implies_hn_chk : checkAll1_StateP (fun p => checkAll1_StateHN (fun h =>
    (!isReachPH p h || !decide (p ≠ .p37) || decide (h ≠ .hn34)))) = true := rfl

theorem evalPTerm_ne_p37_implies_evalHN_ne_hn34 {t : Term}
    (hv : noVars t = true) (hp : evalPTerm t ≠ .p37) : evalHN t ≠ .hn34 := by
  have hr := eval_isReachPH hv
  have hc := checkAll1_StateHN_sound _ (checkAll1_StateP_sound _ ph_acc_implies_hn_chk (evalPTerm t)) (evalHN t)
  rw [hr, decide_eq_true hp] at hc
  exact of_decide_eq_true hc

/-! ## 3. Duplicate-Free Catalan Enumeration (`treesOfSize`) and Exact DP Functions -/

def listFlatMap {α β : Type} : List α → (α → List β) → List β
  | [], _ => []
  | x :: xs, f => f x ++ listFlatMap xs f

def sumList {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | x :: xs, f => f x + sumList xs f

def countList {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + countList p xs

inductive NodupList {α : Type} : List α → Prop where
  | nil : NodupList []
  | cons {x : α} {xs : List α} : x ∉ xs → NodupList xs → NodupList (x :: xs)

theorem sumList_zero {α : Type} (xs : List α) : sumList xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [sumList, ih]

theorem sumList_map {α β : Type} (xs : List α) (g : α → β) (f : β → Nat) :
    sumList (xs.map g) f = sumList xs (fun x => f (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, sumList, ih]

theorem sumList_append {α : Type} (xs ys : List α) (f : α → Nat) :
    sumList (xs ++ ys) f = sumList xs f + sumList ys f := by
  induction xs with
  | nil => simp only [List.nil_append, sumList, Nat.zero_add]
  | cons x xs ih => simp only [List.cons_append, sumList, ih, Nat.add_assoc]

theorem countList_eq_filter_length {α : Type} (p : α → Bool) (xs : List α) :
    countList p xs = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [countList, List.filter]
    rcases bool_eq_true_or_false (p x) with hp | hp
    · rw [hp]
      change 1 + countList p xs = (x :: List.filter p xs).length
      simp only [List.length_cons, ih]
      omega
    · rw [hp]
      change 0 + countList p xs = (List.filter p xs).length
      rw [Nat.zero_add, ih]

theorem countList_eq_sumList {α : Type} (p : α → Bool) (xs : List α) :
    countList p xs = sumList xs (fun x => if p x then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [countList, sumList, ih]

theorem countList_append {α : Type} (p : α → Bool) (xs ys : List α) :
    countList p (xs ++ ys) = countList p xs + countList p ys := by
  induction xs with
  | nil => simp only [List.nil_append, countList, Nat.zero_add]
  | cons x xs ih => simp only [List.cons_append, countList, ih, Nat.add_assoc]

theorem countList_map {α β : Type} (p : β → Bool) (f : α → β) (xs : List α) :
    countList p (xs.map f) = countList (fun x => p (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, countList, ih]

theorem countList_listFlatMap {α β : Type} (p : β → Bool) (xs : List α) (f : α → List β) :
    countList p (listFlatMap xs f) = sumList xs (fun x => countList p (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listFlatMap, sumList, countList_append, ih]

theorem countList_mono {α : Type} {p q : α → Bool} (xs : List α)
    (himp : ∀ x ∈ xs, p x = true → q x = true) :
    countList p xs ≤ countList q xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [countList]
    have ih' := ih (fun y hy => himp y (List.Mem.tail _ hy))
    rcases bool_eq_true_or_false (p x) with hp | hp
    · rw [hp, himp x (List.Mem.head _) hp]
      exact Nat.add_le_add (Nat.le_refl 1) ih'
    · rw [hp]
      change 0 + countList p xs ≤ (if q x then 1 else 0) + countList q xs
      exact Nat.add_le_add (Nat.zero_le _) ih'

theorem countList_le_length {α : Type} (p : α → Bool) (xs : List α) :
    countList p xs ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [countList, List.length_cons]
    rcases bool_eq_true_or_false (p x) with hp | hp <;> rw [hp]
    · change 1 + countList p xs ≤ xs.length + 1; omega
    · change 0 + countList p xs ≤ xs.length + 1; omega

theorem countList_complement {α : Type} (p : α → Bool) (xs : List α) :
    countList p xs + countList (fun x => !p x) xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [countList, List.length_cons]
    rcases bool_eq_true_or_false (p x) with hp | hp
    · have h1 : (if p x = true then 1 else 0) = 1 := by rw [hp]; rfl
      have h2 : (if (!p x) = true then 1 else 0) = 0 := by rw [hp]; rfl
      rw [h1, h2]
      omega
    · have h1 : (if p x = true then 1 else 0) = 0 := by rw [hp]; rfl
      have h2 : (if (!p x) = true then 1 else 0) = 1 := by rw [hp]; rfl
      rw [h1, h2]
      omega

theorem length_listFlatMap {α β : Type} (xs : List α) (f : α → List β) :
    (listFlatMap xs f).length = sumList xs (fun x => (f x).length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listFlatMap, sumList, List.length_append, ih]

theorem listFlatMap_congr {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ x ∈ xs, f x = g x) : listFlatMap xs f = listFlatMap xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [listFlatMap]
    rw [h x (List.Mem.head _), ih (fun y hy => h y (List.Mem.tail _ hy))]

theorem listFlatMap_append {α β : Type} (xs ys : List α) (g : α → List β) :
    listFlatMap (xs ++ ys) g = listFlatMap xs g ++ listFlatMap ys g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, listFlatMap, List.append_assoc, ih]

theorem countList_all_true {α : Type} {p : α → Bool} (xs : List α)
    (hall : ∀ x ∈ xs, p x = true) : countList p xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [countList, List.length_cons]
    have hx : p x = true := hall x (List.Mem.head _)
    have hite : (if p x = true then 1 else 0) = 1 := if_pos hx
    rw [hite, ih (fun y hy => hall y (List.Mem.tail _ hy)), Nat.add_comm]

theorem mem_listFlatMap_iff {α β : Type} {y : β} {xs : List α} {f : α → List β} :
    y ∈ listFlatMap xs f ↔ ∃ x ∈ xs, y ∈ f x := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro ⟨_, hx, _⟩; cases hx
  | cons a xs ih =>
    simp only [listFlatMap, List.mem_append, ih]
    constructor
    · intro h
      rcases h with ha | ⟨x, hx, hy⟩
      · exact ⟨a, List.Mem.head _, ha⟩
      · exact ⟨x, List.Mem.tail _ hx, hy⟩
    · intro ⟨x, hx, hy⟩
      cases hx with
      | head _ => exact Or.inl hy
      | tail _ hx' => exact Or.inr ⟨x, hx', hy⟩

theorem sumList_congr {α : Type} {xs : List α} {f g : α → Nat}
    (h : ∀ x ∈ xs, f x = g x) : sumList xs f = sumList xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumList]
    rw [h x (List.Mem.head _), ih (fun y hy => h y (List.Mem.tail _ hy))]

theorem sumList_le_sumList {α : Type} {xs : List α} {f g : α → Nat}
    (h : ∀ x ∈ xs, f x ≤ g x) : sumList xs f ≤ sumList xs g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [sumList]
    exact Nat.add_le_add (h x (List.Mem.head _)) (ih (fun y hy => h y (List.Mem.tail _ hy)))

theorem sumList_add_distrib {α : Type} (xs : List α) (f g : α → Nat) :
    sumList xs (fun x => f x + g x) = sumList xs f + sumList xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumList, ih]; omega

theorem sumList_mul_left {α : Type} (c : Nat) (xs : List α) (f : α → Nat) :
    sumList xs (fun x => c * f x) = c * sumList xs f := by
  induction xs with
  | nil => simp only [sumList, Nat.mul_zero]
  | cons x xs ih => simp only [sumList, ih, Nat.mul_add]

theorem sumList_mul_right {α : Type} (c : Nat) (xs : List α) (f : α → Nat) :
    sumList xs (fun x => f x * c) = sumList xs f * c := by
  induction xs with
  | nil => simp only [sumList, Nat.zero_mul]
  | cons x xs ih => simp only [sumList, ih, Nat.add_mul]

theorem mem_le_sumList {α : Type} {x : α} {xs : List α} (hx : x ∈ xs) (f : α → Nat) :
    f x ≤ sumList xs f := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
    simp only [sumList]
    rcases List.mem_cons.mp hx with rfl | hm
    · exact Nat.le_add_right (f x) _
    · exact Nat.le_trans (ih hm) (Nat.le_add_left _ (f a))

theorem nodup_append {α : Type} {xs ys : List α}
    (hxs : NodupList xs) (hys : NodupList ys)
    (hdisj : ∀ z, z ∈ xs → z ∈ ys → False) : NodupList (xs ++ ys) := by
  induction hxs with
  | nil => exact hys
  | @cons x rest hx _ ih =>
    refine NodupList.cons ?_ (ih (fun z hz hy => hdisj z (List.Mem.tail _ hz) hy))
    intro hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · exact hx h1
    · exact hdisj x (List.Mem.head _) h2

theorem nodup_map {α β : Type} {f : α → β} {xs : List α}
    (hinj : ∀ u v, f u = f v → u = v) (hxs : NodupList xs) : NodupList (xs.map f) := by
  induction hxs with
  | nil => exact NodupList.nil
  | @cons x rest hx _ ih =>
    refine NodupList.cons ?_ ih
    intro hmem
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
    have hxy := hinj y x heq
    subst hxy
    exact hx hy

theorem nodup_listFlatMap {α β : Type} {xs : List α} {f : α → List β}
    (hxs : NodupList xs)
    (hf : ∀ x ∈ xs, NodupList (f x))
    (hsep : ∀ x1 ∈ xs, ∀ x2 ∈ xs, ∀ z, z ∈ f x1 → z ∈ f x2 → x1 = x2) :
    NodupList (listFlatMap xs f) := by
  induction hxs with
  | nil => exact NodupList.nil
  | @cons x rest hx _ ih =>
    refine nodup_append (hf x (List.Mem.head _))
      (ih (fun y hy => hf y (List.Mem.tail _ hy))
          (fun x1 hx1 x2 hx2 z hz1 hz2 =>
            hsep x1 (List.Mem.tail _ hx1) x2 (List.Mem.tail _ hx2) z hz1 hz2)) ?_
    intro z hz1 hz2
    obtain ⟨y, hy, hzy⟩ := mem_listFlatMap_iff.mp hz2
    have heq := hsep x (List.Mem.head _) y (List.Mem.tail _ hy) z hz1 hzy
    subst heq
    exact hx hy

/-- Ordered splits `(1, n-1), (2, n-2), ..., (n-1, 1)` for `n ≥ 2`. -/
def splitsAux : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | k + 1, a => (a, k + 1) :: splitsAux k (a + 1)

def splits : Nat → List (Nat × Nat)
  | 0 => []
  | 1 => []
  | m + 2 => splitsAux (m + 1) 1

theorem mem_splitsAux_iff (K a x y : Nat) :
    (x, y) ∈ splitsAux K a ↔ a ≤ x ∧ 1 ≤ y ∧ x + y = a + K := by
  induction K generalizing a with
  | zero =>
    simp only [splitsAux]
    constructor
    · intro h; cases h
    · intro ⟨_, _, _⟩; omega
  | succ k ih =>
    simp only [splitsAux, List.mem_cons, Prod.mk.injEq, ih (a + 1)]
    constructor
    · intro h
      rcases h with ⟨hx, hy⟩ | ⟨h1, h2, h3⟩
      · exact ⟨by omega, by omega, by omega⟩
      · exact ⟨by omega, h2, by omega⟩
    · intro ⟨h1, h2, h3⟩
      exact if hxa : x = a then
        Or.inl ⟨hxa, by omega⟩
      else
        Or.inr ⟨by omega, h2, by omega⟩

theorem mem_splits_iff {m x y : Nat} :
    (x, y) ∈ splits (m + 2) ↔ 1 ≤ x ∧ 1 ≤ y ∧ x + y = m + 2 := by
  simp only [splits, mem_splitsAux_iff]
  constructor
  · intro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩
  · intro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩

theorem nodup_splitsAux (K a : Nat) : NodupList (splitsAux K a) := by
  induction K generalizing a with
  | zero => exact NodupList.nil
  | succ k ih =>
    refine NodupList.cons ?_ (ih (a + 1))
    intro hmem
    have ⟨hge, _, _⟩ := (mem_splitsAux_iff k (a + 1) a (k + 1)).mp hmem
    omega

theorem nodup_splits (n : Nat) : NodupList (splits n) := by
  cases n with
  | zero => exact NodupList.nil
  | succ n0 =>
    cases n0 with
    | zero => exact NodupList.nil
    | succ m => exact nodup_splitsAux (m + 1) 1

/-- Pure `Nat.rec` structural fuel recursion (`fuel` first!) for zero-axiom compilation. -/
def treesAux : Nat → Nat → List Term
  | 0, 0 => []
  | 0, 1 => [S]
  | 0, _ + 2 => []
  | fuel + 1, n =>
    let sub := treesAux fuel
    match n with
    | 0 => []
    | 1 => [S]
    | m + 2 =>
      listFlatMap (splits (m + 2)) (fun p =>
        listFlatMap (sub p.1) (fun l =>
          (sub p.2).map (fun r => l ⋆ r)))

def treesOfSize (n : Nat) : List Term := treesAux n n

def catalanAux : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, _ + 2 => 0
  | fuel + 1, n =>
    let sub := catalanAux fuel
    match n with
    | 0 => 0
    | 1 => 1
    | m + 2 => sumList (splits (m + 2)) (fun p => sub p.1 * sub p.2)

def catalanTrees (n : Nat) : Nat := catalanAux n n
abbrev countTrees (n : Nat) : Nat := catalanTrees n

private theorem treesAux_zero (f : Nat) : treesAux f 0 = [] := by cases f <;> rfl
private theorem treesAux_one  (f : Nat) : treesAux f 1 = [S] := by cases f <;> rfl
private theorem treesAux_step (f m : Nat) :
    treesAux (f + 1) (m + 2) =
      listFlatMap (splits (m + 2)) (fun p =>
        listFlatMap (treesAux f p.1) (fun l =>
          (treesAux f p.2).map (fun r => l ⋆ r))) := rfl

private theorem catalanAux_zero (f : Nat) : catalanAux f 0 = 0 := by cases f <;> rfl
private theorem catalanAux_one  (f : Nat) : catalanAux f 1 = 1 := by cases f <;> rfl
private theorem catalanAux_step (f m : Nat) :
    catalanAux (f + 1) (m + 2) =
      sumList (splits (m + 2)) (fun p => catalanAux f p.1 * catalanAux f p.2) := rfl

theorem treesAux_eq_of_le (fuel1 : Nat) :
    ∀ (fuel2 n : Nat), n ≤ fuel1 → n ≤ fuel2 → treesAux fuel1 n = treesAux fuel2 n := by
  induction fuel1 with
  | zero =>
    intro fuel2 n h1 _
    have hn0 : n = 0 := by omega
    subst hn0
    rw [treesAux_zero, treesAux_zero]
  | succ f1 ih =>
    intro fuel2 n h1 h2
    cases n with
    | zero => rw [treesAux_zero, treesAux_zero]
    | succ n0 =>
      cases n0 with
      | zero => rw [treesAux_one, treesAux_one]
      | succ m =>
        cases fuel2 with
        | zero => omega
        | succ f2 =>
          rw [treesAux_step, treesAux_step]
          refine listFlatMap_congr (fun ⟨x, y⟩ hp => ?_)
          dsimp only
          have ⟨_, _, _⟩ := mem_splits_iff.mp hp
          rw [ih f2 x (by omega) (by omega), ih f2 y (by omega) (by omega)]

theorem catalanAux_eq_of_le (fuel1 : Nat) :
    ∀ (fuel2 n : Nat), n ≤ fuel1 → n ≤ fuel2 → catalanAux fuel1 n = catalanAux fuel2 n := by
  induction fuel1 with
  | zero =>
    intro fuel2 n h1 _
    have hn0 : n = 0 := by omega
    subst hn0
    rw [catalanAux_zero, catalanAux_zero]
  | succ f1 ih =>
    intro fuel2 n h1 h2
    cases n with
    | zero => rw [catalanAux_zero, catalanAux_zero]
    | succ n0 =>
      cases n0 with
      | zero => rw [catalanAux_one, catalanAux_one]
      | succ m =>
        cases fuel2 with
        | zero => omega
        | succ f2 =>
          rw [catalanAux_step, catalanAux_step]
          refine sumList_congr (fun ⟨x, y⟩ hp => ?_)
          dsimp only
          have ⟨_, _, _⟩ := mem_splits_iff.mp hp
          rw [ih f2 x (by omega) (by omega), ih f2 y (by omega) (by omega)]

theorem catalanTrees_zero : catalanTrees 0 = 0 := rfl
theorem catalanTrees_one : catalanTrees 1 = 1 := rfl

theorem catalanTrees_recurrence (m : Nat) :
    catalanTrees (m + 2) = sumList (splits (m + 2)) (fun p => catalanTrees p.1 * catalanTrees p.2) := by
  change catalanAux ((m + 1) + 1) (m + 2) = _
  rw [catalanAux_step]
  refine sumList_congr (fun ⟨x, y⟩ hp => ?_)
  dsimp only
  have ⟨_, _, _⟩ := mem_splits_iff.mp hp
  rw [catalanAux_eq_of_le (m + 1) x x (by omega) (Nat.le_refl x),
      catalanAux_eq_of_le (m + 1) y y (by omega) (Nat.le_refl y)]
  rfl

theorem treesOfSize_recurrence (m : Nat) :
    treesOfSize (m + 2) = listFlatMap (splits (m + 2)) (fun p =>
      listFlatMap (treesOfSize p.1) (fun l =>
        (treesOfSize p.2).map (fun r => l ⋆ r))) := by
  change treesAux ((m + 1) + 1) (m + 2) = _
  rw [treesAux_step]
  refine listFlatMap_congr (fun ⟨x, y⟩ hp => ?_)
  dsimp only [treesOfSize]
  have ⟨_, _, _⟩ := mem_splits_iff.mp hp
  rw [treesAux_eq_of_le (m + 1) x x (by omega) (Nat.le_refl x),
      treesAux_eq_of_le (m + 1) y y (by omega) (Nat.le_refl y)]

private theorem length_app_block (ls rs : List Term) :
    (listFlatMap ls (fun l => rs.map (fun r => l ⋆ r))).length = ls.length * rs.length := by
  induction ls with
  | nil => simp only [listFlatMap, List.length_nil, Nat.zero_mul]
  | cons l ls ih =>
    simp only [listFlatMap, List.length_append, List.length_map, List.length_cons, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem catalanAux_eq_length (fuel : Nat) :
    ∀ (n : Nat), catalanAux fuel n = (treesAux fuel n).length := by
  induction fuel with
  | zero =>
    intro n
    cases n with
    | zero => rfl
    | succ n0 => cases n0 <;> rfl
  | succ f ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n0 =>
      cases n0 with
      | zero => rfl
      | succ m =>
        rw [catalanAux_step, treesAux_step, length_listFlatMap]
        refine sumList_congr (fun p _ => ?_)
        rw [length_app_block, ih p.1, ih p.2]

theorem catalanTrees_eq_treesOfSize_length (n : Nat) :
    catalanTrees n = (treesOfSize n).length :=
  catalanAux_eq_length n n

theorem treesAux_sound (fuel : Nat) :
    ∀ (n : Nat) {t : Term}, t ∈ treesAux fuel n → noVars t = true ∧ leaves t = n := by
  induction fuel with
  | zero =>
    intro n t h
    cases n with
    | zero => cases h
    | succ n0 =>
      cases n0 with
      | zero =>
        rcases List.mem_cons.mp h with rfl | h'
        · exact ⟨rfl, rfl⟩
        · cases h'
      | succ _ => cases h
  | succ f ih =>
    intro n t h
    cases n with
    | zero => cases h
    | succ n0 =>
      cases n0 with
      | zero =>
        rcases List.mem_cons.mp h with rfl | h'
        · exact ⟨rfl, rfl⟩
        · cases h'
      | succ m =>
        rw [treesAux_step] at h
        obtain ⟨⟨x, y⟩, hp, h1⟩ := mem_listFlatMap_iff.mp h
        dsimp only at h1
        obtain ⟨l, hl, h2⟩ := mem_listFlatMap_iff.mp h1
        obtain ⟨r, hr, heq⟩ := List.mem_map.mp h2
        subst heq
        have ⟨_, _, hxy⟩ := mem_splits_iff.mp hp
        have ⟨hvl, hll⟩ := ih x hl
        have ⟨hvr, hlr⟩ := ih y hr
        refine ⟨(Bool.and_eq_true (noVars l) (noVars r)).mpr ⟨hvl, hvr⟩, ?_⟩
        change leaves l + leaves r = m + 2
        rw [hll, hlr, hxy]

theorem treesOfSize_sound {n : Nat} {t : Term} (h : t ∈ treesOfSize n) :
    noVars t = true ∧ leaves t = n :=
  treesAux_sound n n h

theorem treesAux_complete (fuel : Nat) :
    ∀ {t : Term}, noVars t = true → leaves t ≤ fuel → t ∈ treesAux fuel (leaves t) := by
  induction fuel with
  | zero =>
    intro t _ hle
    have hp := leaves_pos t
    omega
  | succ f ih =>
    intro t hv hle
    cases t with
    | s => exact List.Mem.head _
    | var _ => cases hv
    | app a b =>
      have hva := ((Bool.and_eq_true (noVars a) (noVars b)).mp hv).1
      have hvb := ((Bool.and_eq_true (noVars a) (noVars b)).mp hv).2
      have ha := leaves_pos a
      have hb := leaves_pos b
      change leaves a + leaves b ≤ f + 1 at hle
      have hsum : ∃ m, leaves a + leaves b = m + 2 := ⟨leaves a + leaves b - 2, by omega⟩
      obtain ⟨m, hm⟩ := hsum
      change (a ⋆ b) ∈ treesAux (f + 1) (leaves a + leaves b)
      rw [hm, treesAux_step]
      refine mem_listFlatMap_iff.mpr ⟨(leaves a, leaves b), mem_splits_iff.mpr ⟨ha, hb, hm⟩, ?_⟩
      dsimp only
      refine mem_listFlatMap_iff.mpr ⟨a, ih hva (by omega), ?_⟩
      exact List.mem_map.mpr ⟨b, ih hvb (by omega), rfl⟩

theorem treesOfSize_complete {n : Nat} {t : Term} (hv : noVars t = true) (hl : leaves t = n) :
    t ∈ treesOfSize n := by
  subst hl
  exact treesAux_complete (leaves t) hv (Nat.le_refl _)

theorem treesAux_nodup (fuel : Nat) :
    ∀ (n : Nat), NodupList (treesAux fuel n) := by
  induction fuel with
  | zero =>
    intro n
    cases n with
    | zero => exact NodupList.nil
    | succ n0 =>
      cases n0 with
      | zero => exact NodupList.cons (fun h => by cases h) NodupList.nil
      | succ _ => exact NodupList.nil
  | succ f ih =>
    intro n
    cases n with
    | zero => exact NodupList.nil
    | succ n0 =>
      cases n0 with
      | zero => exact NodupList.cons (fun h => by cases h) NodupList.nil
      | succ m =>
        rw [treesAux_step]
        refine nodup_listFlatMap (nodup_splits (m + 2)) (fun p _ => ?_) (fun p1 _ p2 _ z hz1 hz2 => ?_)
        · refine nodup_listFlatMap (ih p.1) (fun l _ => ?_) (fun l1 _ l2 _ z hz1 hz2 => ?_)
          · exact nodup_map (fun _ _ heq => (FormalAlgebra.Term.app.inj heq).2) (ih p.2)
          · obtain ⟨r1, _, heq1⟩ := List.mem_map.mp hz1
            obtain ⟨r2, _, heq2⟩ := List.mem_map.mp hz2
            exact (FormalAlgebra.Term.app.inj (heq1.trans heq2.symm)).1
        · obtain ⟨l1, hl1, hr1_mem⟩ := mem_listFlatMap_iff.mp hz1
          obtain ⟨r1, hr1, heq1⟩ := List.mem_map.mp hr1_mem
          obtain ⟨l2, hl2, hr2_mem⟩ := mem_listFlatMap_iff.mp hz2
          obtain ⟨r2, hr2, heq2⟩ := List.mem_map.mp hr2_mem
          have ⟨hleq, hreq⟩ := FormalAlgebra.Term.app.inj (heq1.trans heq2.symm)
          subst hleq; subst hreq
          have ⟨_, hll1⟩ := treesAux_sound f p1.1 hl1
          have ⟨_, hll2⟩ := treesAux_sound f p2.1 hl2
          have ⟨_, hlr1⟩ := treesAux_sound f p1.2 hr1
          have ⟨_, hlr2⟩ := treesAux_sound f p2.2 hr2
          cases p1; cases p2
          simp only [Prod.mk.injEq]
          exact ⟨hll1.symm.trans hll2, hlr1.symm.trans hlr2⟩

theorem treesOfSize_nodup (n : Nat) : NodupList (treesOfSize n) :=
  treesAux_nodup n n

/-! ## 4. Generic Finite `S`-Algebra DP Engine & Exact Equivalence with `treesOfSize` Filtering -/

def dpStateAux {Q : Type} [DecidableEq Q] (allQ : List Q) (delta : Q → Q → Q) (q0 : Q) :
    Nat → Nat → Q → Nat
  | 0, 0, _ => 0
  | 0, 1, q => if q = q0 then 1 else 0
  | 0, _ + 2, _ => 0
  | fuel + 1, n, q =>
    let sub := dpStateAux allQ delta q0 fuel
    match n with
    | 0 => 0
    | 1 => if q = q0 then 1 else 0
    | m + 2 =>
      sumList (splits (m + 2)) (fun p =>
        sumList allQ (fun a =>
          sumList allQ (fun b =>
            if delta a b = q then sub p.1 a * sub p.2 b else 0)))

def dpState {Q : Type} [DecidableEq Q] (allQ : List Q) (delta : Q → Q → Q) (q0 : Q)
    (n : Nat) (q : Q) : Nat :=
  dpStateAux allQ delta q0 n n q

private theorem dpStateAux_zero {Q : Type} [DecidableEq Q] (allQ : List Q) (delta : Q → Q → Q) (q0 : Q)
    (f : Nat) (q : Q) : dpStateAux allQ delta q0 f 0 q = 0 := by cases f <;> rfl

private theorem dpStateAux_one {Q : Type} [DecidableEq Q] (allQ : List Q) (delta : Q → Q → Q) (q0 : Q)
    (f : Nat) (q : Q) : dpStateAux allQ delta q0 f 1 q = (if q = q0 then 1 else 0) := by cases f <;> rfl

private theorem dpStateAux_step {Q : Type} [DecidableEq Q] (allQ : List Q) (delta : Q → Q → Q) (q0 : Q)
    (f m : Nat) (q : Q) :
    dpStateAux allQ delta q0 (f + 1) (m + 2) q =
      sumList (splits (m + 2)) (fun p =>
        sumList allQ (fun a =>
          sumList allQ (fun b =>
            if delta a b = q then dpStateAux allQ delta q0 f p.1 a * dpStateAux allQ delta q0 f p.2 b else 0))) := rfl

theorem dpStateAux_eq_of_le {Q : Type} [DecidableEq Q] (allQ : List Q) (delta : Q → Q → Q) (q0 : Q)
    (fuel1 : Nat) :
    ∀ (fuel2 n : Nat) (q : Q), n ≤ fuel1 → n ≤ fuel2 →
      dpStateAux allQ delta q0 fuel1 n q = dpStateAux allQ delta q0 fuel2 n q := by
  induction fuel1 with
  | zero =>
    intro fuel2 n q h1 _
    have hn0 : n = 0 := by omega
    subst hn0
    rw [dpStateAux_zero, dpStateAux_zero]
  | succ f1 ih =>
    intro fuel2 n q h1 h2
    cases n with
    | zero => rw [dpStateAux_zero, dpStateAux_zero]
    | succ n0 =>
      cases n0 with
      | zero => rw [dpStateAux_one, dpStateAux_one]
      | succ m =>
        cases fuel2 with
        | zero => omega
        | succ f2 =>
          rw [dpStateAux_step, dpStateAux_step]
          refine sumList_congr (fun ⟨x, y⟩ hp => ?_)
          dsimp only
          have ⟨_, _, _⟩ := mem_splits_iff.mp hp
          refine sumList_congr (fun a _ => sumList_congr (fun b _ => ?_))
          rw [ih f2 x a (by omega) (by omega), ih f2 y b (by omega) (by omega)]

theorem dpState_recurrence {Q : Type} [DecidableEq Q] (allQ : List Q) (delta : Q → Q → Q) (q0 : Q)
    (m : Nat) (q : Q) :
    dpState allQ delta q0 (m + 2) q =
      sumList (splits (m + 2)) (fun p =>
        sumList allQ (fun a =>
          sumList allQ (fun b =>
            if delta a b = q then
              dpState allQ delta q0 p.1 a * dpState allQ delta q0 p.2 b
            else 0))) := by
  change dpStateAux allQ delta q0 ((m + 1) + 1) (m + 2) q = _
  rw [dpStateAux_step]
  refine sumList_congr (fun ⟨x, y⟩ hp => ?_)
  dsimp only
  have ⟨_, _, _⟩ := mem_splits_iff.mp hp
  refine sumList_congr (fun a _ => sumList_congr (fun b _ => ?_))
  rw [dpStateAux_eq_of_le allQ delta q0 (m + 1) x x a (by omega) (Nat.le_refl x),
      dpStateAux_eq_of_le allQ delta q0 (m + 1) y y b (by omega) (Nat.le_refl y)]
  rfl

private theorem sumList_delta_one {Q : Type} [DecidableEq Q] {allQ : List Q}
    (hnodup : NodupList allQ) (f : Q → Nat) {q : Q} (hq : q ∈ allQ) :
    sumList allQ (fun a => if a = q then f a else 0) = f q := by
  induction hnodup with
  | nil => cases hq
  | @cons z zs hz _ ih =>
    simp only [sumList]
    rcases List.mem_cons.mp hq with heq_qz | hq'
    · subst heq_qz
      rw [if_pos rfl]
      have h0 : ∀ a ∈ zs, (if a = q then f a else 0) = 0 := by
        intro a ha
        cases hax : decide (a = q) with
        | true => exfalso; exact hz ((of_decide_eq_true hax) ▸ ha)
        | false => rw [if_neg (of_decide_eq_false hax)]
      rw [sumList_congr h0, sumList_zero, Nat.add_zero]
    · have hne : z ≠ q := fun heq => hz (heq ▸ hq')
      rw [if_neg hne, Nat.zero_add, ih hq']

private theorem sumList_partition_by_eval {α Q : Type} [DecidableEq Q]
    {allQ : List Q} (hnodup : NodupList allQ) (hcomp : ∀ q : Q, q ∈ allQ)
    (ev : α → Q) (w : Q → Nat) (xs : List α) :
    sumList xs (fun x => w (ev x)) =
      sumList allQ (fun a => countList (fun x => decide (ev x = a)) xs * w a) := by
  induction xs with
  | nil =>
    simp only [sumList, countList]
    have h0 : ∀ a ∈ allQ, 0 * w a = 0 := fun _ _ => Nat.zero_mul _
    rw [sumList_congr h0, sumList_zero]
  | cons x xs ih =>
    simp only [sumList, countList]
    have hsplit : ∀ a ∈ allQ,
        ((if decide (ev x = a) then 1 else 0) + countList (fun y => decide (ev y = a)) xs) * w a =
        (if a = ev x then w a else 0) + countList (fun y => decide (ev y = a)) xs * w a := by
      intro a _
      rw [Nat.add_mul]
      cases h : decide (ev x = a) with
      | true =>
        have heq := (of_decide_eq_true h).symm
        change 1 * w a + countList (fun y => decide (ev y = a)) xs * w a = _
        rw [Nat.one_mul, if_pos heq]
      | false =>
        have hne : a ≠ ev x := fun heq => of_decide_eq_false h heq.symm
        change 0 * w a + countList (fun y => decide (ev y = a)) xs * w a = _
        rw [Nat.zero_mul, if_neg hne]
    rw [sumList_congr hsplit, sumList_add_distrib, sumList_delta_one hnodup w (hcomp (ev x)), ih]

theorem dpStateAux_eq_countList {Q : Type} [DecidableEq Q]
    {allQ : List Q} (hnodup : NodupList allQ) (hcomp : ∀ q : Q, q ∈ allQ)
    (delta : Q → Q → Q) (q0 : Q) (ev : Term → Q)
    (hevs : ev S = q0) (hevapp : ∀ l r, ev (l ⋆ r) = delta (ev l) (ev r))
    (fuel : Nat) :
    ∀ (n : Nat) (q : Q),
      dpStateAux allQ delta q0 fuel n q =
        countList (fun t => decide (ev t = q)) (treesAux fuel n) := by
  induction fuel with
  | zero =>
    intro n q
    cases n with
    | zero => rfl
    | succ n0 =>
      cases n0 with
      | zero =>
        simp only [dpStateAux, treesAux, countList, hevs, Nat.add_zero]
        cases h : decide (q = q0) with
        | true =>
          have heq := of_decide_eq_true h
          subst heq
          rw [if_pos rfl, decide_eq_true rfl]
          rfl
        | false =>
          have hne := of_decide_eq_false h
          have hne' : q0 ≠ q := fun heq => hne heq.symm
          rw [if_neg hne, decide_eq_false hne']
          rfl
      | succ _ => rfl
  | succ f ih =>
    intro n q
    cases n with
    | zero => rfl
    | succ n0 =>
      cases n0 with
      | zero =>
        simp only [dpStateAux, treesAux, countList, hevs, Nat.add_zero]
        cases h : decide (q = q0) with
        | true =>
          have heq := of_decide_eq_true h
          subst heq
          rw [if_pos rfl, decide_eq_true rfl]
          rfl
        | false =>
          have hne := of_decide_eq_false h
          have hne' : q0 ≠ q := fun heq => hne heq.symm
          rw [if_neg hne, decide_eq_false hne']
          rfl
      | succ m =>
        rw [dpStateAux_step, treesAux_step, countList_listFlatMap]
        refine sumList_congr (fun ⟨x, y⟩ _ => ?_)
        dsimp only
        have inner_eq : ∀ l : Term,
            countList (fun t => decide (ev t = q)) ((treesAux f y).map (fun r => l ⋆ r)) =
            sumList allQ (fun b => countList (fun r => decide (ev r = b)) (treesAux f y) *
              (if delta (ev l) b = q then 1 else 0)) := by
          intro l
          rw [countList_map, countList_eq_sumList]
          have hrew : ∀ r ∈ treesAux f y,
              (if decide (ev (l ⋆ r) = q) then 1 else 0) =
              (if delta (ev l) (ev r) = q then 1 else 0) := by
            intro r _
            rw [hevapp]
            cases h : decide (delta (ev l) (ev r) = q) with
            | true => rw [if_pos (of_decide_eq_true h)]; rfl
            | false => rw [if_neg (of_decide_eq_false h)]; rfl
          rw [sumList_congr hrew]
          exact sumList_partition_by_eval hnodup hcomp ev (fun b => if delta (ev l) b = q then 1 else 0) (treesAux f y)
        have houter := sumList_congr (xs := treesAux f x) (fun l _ => inner_eq l)
        rw [countList_listFlatMap, houter,
            sumList_partition_by_eval hnodup hcomp ev
              (fun a => sumList allQ (fun b => countList (fun r => decide (ev r = b)) (treesAux f y) *
                (if delta a b = q then 1 else 0)))
              (treesAux f x)]
        refine sumList_congr (fun a _ => ?_)
        rw [← sumList_mul_left]
        refine sumList_congr (fun b _ => ?_)
        try dsimp only
        rw [ih x a, ih y b]
        cases h : decide (delta a b = q) with
        | true => simp only [if_pos (of_decide_eq_true h), Nat.mul_one]
        | false => simp only [if_neg (of_decide_eq_false h), Nat.mul_zero]

theorem dpState_eq_countList {Q : Type} [DecidableEq Q]
    {allQ : List Q} (hnodup : NodupList allQ) (hcomp : ∀ q : Q, q ∈ allQ)
    (delta : Q → Q → Q) (q0 : Q) (ev : Term → Q)
    (hevs : ev S = q0) (hevapp : ∀ l r, ev (l ⋆ r) = delta (ev l) (ev r))
    (n : Nat) (q : Q) :
    dpState allQ delta q0 n q = countList (fun t => decide (ev t = q)) (treesOfSize n) :=
  dpStateAux_eq_countList hnodup hcomp delta q0 ev hevs hevapp n n q

/-! ### Concrete State Lists & DP Counters (`countSN`, `countHN`, `countNonHN`, `countAcceptP`) -/

def allStatesSN : List StateSN := [.sn0, .sn1, .sn2, .sn3, .sn4, .sn5, .sn6, .sn7, .sn8, .sn9, .sn10, .sn11, .sn12, .sn13, .sn14, .sn15, .sn16, .sn17, .sn18, .sn19, .sn20, .sn21, .sn22, .sn23, .sn24, .sn25, .sn26, .sn27, .sn28, .sn29, .sn30, .sn31, .sn32, .sn33, .sn34, .sn35, .sn36, .sn37, .sn38]
def accStatesSN : List StateSN := [.sn0, .sn1, .sn2, .sn3, .sn4, .sn5, .sn6, .sn7, .sn8, .sn9, .sn10, .sn11, .sn12, .sn13, .sn14, .sn15, .sn16, .sn17, .sn18, .sn19, .sn20, .sn21, .sn22, .sn23, .sn24, .sn25, .sn26, .sn27, .sn28, .sn29, .sn30, .sn31, .sn32, .sn33, .sn34, .sn35, .sn36, .sn37]
def allStatesHN : List StateHN := [.hn0, .hn1, .hn2, .hn3, .hn4, .hn5, .hn6, .hn7, .hn8, .hn9, .hn10, .hn11, .hn12, .hn13, .hn14, .hn15, .hn16, .hn17, .hn18, .hn19, .hn20, .hn21, .hn22, .hn23, .hn24, .hn25, .hn26, .hn27, .hn28, .hn29, .hn30, .hn31, .hn32, .hn33, .hn34]
def accStatesHN : List StateHN := [.hn0, .hn1, .hn2, .hn3, .hn4, .hn5, .hn6, .hn7, .hn8, .hn9, .hn10, .hn11, .hn12, .hn13, .hn14, .hn15, .hn16, .hn17, .hn18, .hn19, .hn20, .hn21, .hn22, .hn23, .hn24, .hn25, .hn26, .hn27, .hn28, .hn29, .hn30, .hn31, .hn32, .hn33]
def allStatesP  : List StateP  := [.p0, .p1, .p2, .p3, .p4, .p5, .p6, .p7, .p8, .p9, .p10, .p11, .p12, .p13, .p14, .p15, .p16, .p17, .p18, .p19, .p20, .p21, .p22, .p23, .p24, .p25, .p26, .p27, .p28, .p29, .p30, .p31, .p32, .p33, .p34, .p35, .p36, .p37, .p38]
def accStatesP  : List StateP  := [.p0, .p1, .p2, .p3, .p4, .p5, .p6, .p7, .p8, .p9, .p10, .p11, .p12, .p13, .p14, .p15, .p16, .p17, .p18, .p19, .p20, .p21, .p22, .p23, .p24, .p25, .p26, .p27, .p28, .p29, .p30, .p31, .p32, .p33, .p34, .p35, .p36, .p38]

def nodupBool {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !(decide (x ∈ xs)) && nodupBool xs

theorem nodupBool_sound {α : Type} [DecidableEq α] {xs : List α} (h : nodupBool xs = true) :
    NodupList xs := by
  induction xs with
  | nil => exact NodupList.nil
  | cons x xs ih =>
    have ⟨h1, h2⟩ := (Bool.and_eq_true (!decide (x ∈ xs)) (nodupBool xs)).mp h
    have hdec : decide (x ∈ xs) = false := by
      cases hd : decide (x ∈ xs) with
      | false => rfl
      | true => rw [hd] at h1; cases h1
    exact NodupList.cons (of_decide_eq_false hdec) (ih h2)

theorem nodup_allStatesSN : NodupList allStatesSN := nodupBool_sound rfl
theorem nodup_accStatesSN : NodupList accStatesSN := nodupBool_sound rfl
theorem nodup_allStatesHN : NodupList allStatesHN := nodupBool_sound rfl
theorem nodup_accStatesHN : NodupList accStatesHN := nodupBool_sound rfl
theorem nodup_allStatesP  : NodupList allStatesP  := nodupBool_sound rfl
theorem nodup_accStatesP  : NodupList accStatesP  := nodupBool_sound rfl

private theorem mem_allStatesSN_chk : checkAll1_StateSN (fun q => decide (q ∈ allStatesSN)) = true := rfl
private theorem mem_allStatesHN_chk : checkAll1_StateHN (fun q => decide (q ∈ allStatesHN)) = true := rfl
private theorem mem_allStatesP_chk  : checkAll1_StateP  (fun q => decide (q ∈ allStatesP))  = true := rfl

theorem complete_allStatesSN (q : StateSN) : q ∈ allStatesSN :=
  of_decide_eq_true (checkAll1_StateSN_sound _ mem_allStatesSN_chk q)

theorem complete_allStatesHN (q : StateHN) : q ∈ allStatesHN :=
  of_decide_eq_true (checkAll1_StateHN_sound _ mem_allStatesHN_chk q)

theorem complete_allStatesP (q : StateP) : q ∈ allStatesP :=
  of_decide_eq_true (checkAll1_StateP_sound _ mem_allStatesP_chk q)

def dpSN (n : Nat) (q : StateSN) : Nat := dpState allStatesSN deltaSN .sn0 n q
def dpHN (n : Nat) (q : StateHN) : Nat := dpState allStatesHN deltaHN .hn0 n q
def dpP  (n : Nat) (q : StateP)  : Nat := dpState allStatesP delta_StateP .p0 n q

def countSN (n : Nat) : Nat := sumList accStatesSN (fun q => dpSN n q)
def countHN (n : Nat) : Nat := sumList accStatesHN (fun q => dpHN n q)
def countNonHN (n : Nat) : Nat := dpHN n .hn34
def countAcceptP (n : Nat) : Nat := sumList accStatesP (fun q => dpP n q)

private theorem accStatesSN_iff_chk : checkAll1_StateSN (fun q => decide ((q ∈ accStatesSN) ↔ (q ≠ .sn38))) = true := rfl
private theorem accStatesHN_iff_chk : checkAll1_StateHN (fun q => decide ((q ∈ accStatesHN) ↔ (q ≠ .hn34))) = true := rfl
private theorem accStatesP_iff_chk  : checkAll1_StateP  (fun q => decide ((q ∈ accStatesP)  ↔ (q ≠ .p37)))  = true := rfl

private theorem sum_subset_eq_countList {Q : Type} [DecidableEq Q]
    {subQ : List Q} (hnodup : NodupList subQ)
    (pred : Q → Bool) (hpred : ∀ q : Q, (q ∈ subQ) ↔ pred q = true)
    (ev : Term → Q) (xs : List Term) :
    sumList subQ (fun q => countList (fun t => decide (ev t = q)) xs) =
      countList (fun t => pred (ev t)) xs := by
  induction xs with
  | nil =>
    simp only [countList]
    exact sumList_zero subQ
  | cons x xs ih =>
    simp only [countList]
    rw [sumList_add_distrib, ih]
    rcases bool_eq_true_or_false (pred (ev x)) with hp | hp
    · have hmem : ev x ∈ subQ := (hpred (ev x)).mpr hp
      have h1 : ∀ q ∈ subQ, (if decide (ev x = q) then 1 else 0) = (if q = ev x then 1 else 0) := by
        intro q _
        cases h : decide (ev x = q) with
        | true => rw [if_pos (of_decide_eq_true h).symm]; rfl
        | false =>
          have hne : q ≠ ev x := fun heq => of_decide_eq_false h heq.symm
          rw [if_neg hne]; rfl
      have hval : sumList subQ (fun q => if decide (ev x = q) then 1 else 0) = 1 :=
        (sumList_congr h1).trans (sumList_delta_one hnodup (fun _ => 1) hmem)
      have hite : (if pred (ev x) = true then 1 else 0) = 1 := by rw [hp]; rfl
      rw [hval, hite]
    · have hnot : ev x ∉ subQ := fun hm => by rw [(hpred (ev x)).mp hm] at hp; cases hp
      have h0 : ∀ q ∈ subQ, (if decide (ev x = q) then 1 else 0) = 0 := by
        intro q hq
        cases h : decide (ev x = q) with
        | true => exfalso; exact hnot ((of_decide_eq_true h) ▸ hq)
        | false => rfl
      have hval : sumList subQ (fun q => if decide (ev x = q) then 1 else 0) = 0 :=
        (sumList_congr h0).trans (sumList_zero subQ)
      have hite : (if pred (ev x) = true then 1 else 0) = 0 := by rw [hp]; rfl
      rw [hval, hite]

theorem countSN_eq_countList (n : Nat) :
    countSN n = countList (fun t => decide (evalSN t ≠ .sn38)) (treesOfSize n) := by
  unfold countSN dpSN
  have h1 : sumList accStatesSN (fun q => dpState allStatesSN deltaSN .sn0 n q) =
      sumList accStatesSN (fun q => countList (fun t => decide (evalSN t = q)) (treesOfSize n)) :=
    sumList_congr (fun q _ => dpState_eq_countList nodup_allStatesSN complete_allStatesSN deltaSN .sn0 evalSN rfl (fun _ _ => rfl) n q)
  rw [h1]
  refine sum_subset_eq_countList nodup_accStatesSN (fun q => decide (q ≠ .sn38)) (fun q => ?_) evalSN (treesOfSize n)
  have hc := of_decide_eq_true (checkAll1_StateSN_sound _ accStatesSN_iff_chk q)
  exact ⟨fun hm => decide_eq_true (hc.mp hm), fun hd => hc.mpr (of_decide_eq_true hd)⟩

theorem countSN_eq_filter_length (n : Nat) :
    countSN n = ((treesOfSize n).filter (fun t => decide (evalSN t ≠ .sn38))).length :=
  (countSN_eq_countList n).trans (countList_eq_filter_length _ _)

theorem countHN_eq_countList (n : Nat) :
    countHN n = countList (fun t => decide (evalHN t ≠ .hn34)) (treesOfSize n) := by
  unfold countHN dpHN
  have h1 : sumList accStatesHN (fun q => dpState allStatesHN deltaHN .hn0 n q) =
      sumList accStatesHN (fun q => countList (fun t => decide (evalHN t = q)) (treesOfSize n)) :=
    sumList_congr (fun q _ => dpState_eq_countList nodup_allStatesHN complete_allStatesHN deltaHN .hn0 evalHN rfl (fun _ _ => rfl) n q)
  rw [h1]
  refine sum_subset_eq_countList nodup_accStatesHN (fun q => decide (q ≠ .hn34)) (fun q => ?_) evalHN (treesOfSize n)
  have hc := of_decide_eq_true (checkAll1_StateHN_sound _ accStatesHN_iff_chk q)
  exact ⟨fun hm => decide_eq_true (hc.mp hm), fun hd => hc.mpr (of_decide_eq_true hd)⟩

theorem countHN_eq_filter_length (n : Nat) :
    countHN n = ((treesOfSize n).filter (fun t => decide (evalHN t ≠ .hn34))).length :=
  (countHN_eq_countList n).trans (countList_eq_filter_length _ _)

theorem countNonHN_eq_countList (n : Nat) :
    countNonHN n = countList (fun t => decide (evalHN t = .hn34)) (treesOfSize n) :=
  dpState_eq_countList nodup_allStatesHN complete_allStatesHN deltaHN .hn0 evalHN rfl (fun _ _ => rfl) n .hn34

theorem countNonHN_eq_filter_length (n : Nat) :
    countNonHN n = ((treesOfSize n).filter (fun t => decide (evalHN t = .hn34))).length :=
  (countNonHN_eq_countList n).trans (countList_eq_filter_length _ _)

theorem countAcceptP_eq_countList (n : Nat) :
    countAcceptP n = countList (fun t => decide (evalPTerm t ≠ .p37)) (treesOfSize n) := by
  unfold countAcceptP dpP
  have h1 : sumList accStatesP (fun q => dpState allStatesP delta_StateP .p0 n q) =
      sumList accStatesP (fun q => countList (fun t => decide (evalPTerm t = q)) (treesOfSize n)) :=
    sumList_congr (fun q _ => dpState_eq_countList nodup_allStatesP complete_allStatesP delta_StateP .p0 evalPTerm rfl (fun _ _ => rfl) n q)
  rw [h1]
  refine sum_subset_eq_countList nodup_accStatesP (fun q => decide (q ≠ .p37)) (fun q => ?_) evalPTerm (treesOfSize n)
  have hc := of_decide_eq_true (checkAll1_StateP_sound _ accStatesP_iff_chk q)
  exact ⟨fun hm => decide_eq_true (hc.mp hm), fun hd => hc.mpr (of_decide_eq_true hd)⟩

theorem countAcceptP_eq_filter_length (n : Nat) :
    countAcceptP n = ((treesOfSize n).filter (fun t => decide (evalPTerm t ≠ .p37))).length :=
  (countAcceptP_eq_countList n).trans (countList_eq_filter_length _ _)

theorem countHN_add_countNonHN (n : Nat) :
    countHN n + countNonHN n = catalanTrees n := by
  rw [countHN_eq_countList, countNonHN_eq_countList, catalanTrees_eq_treesOfSize_length]
  have heq : countList (fun t => decide (evalHN t = .hn34)) (treesOfSize n) =
      countList (fun t => !decide (evalHN t ≠ .hn34)) (treesOfSize n) := by
    rw [countList_eq_sumList, countList_eq_sumList]
    refine sumList_congr (fun t _ => ?_)
    cases h : decide (evalHN t = .hn34) with
    | true => rw [of_decide_eq_true h]; rfl
    | false => rw [decide_eq_true (of_decide_eq_false h)]; rfl
  rw [heq]
  exact countList_complement _ _

/-- **Universal Counting Hierarchy (`#SN(n) ≤ #AcceptP(n) ≤ #HN(n) ≤ C_{n-1}` for all `n`)**. -/
theorem universal_count_hierarchy (n : Nat) :
    countSN n ≤ countAcceptP n ∧ countAcceptP n ≤ countHN n ∧ countHN n ≤ catalanTrees n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [countSN_eq_countList, countAcceptP_eq_countList]
    refine countList_mono (treesOfSize n) (fun t ht hsn => ?_)
    have ⟨hv, _⟩ := treesOfSize_sound ht
    exact decide_eq_true (evalSN_ne_sn38_implies_evalPTerm_ne_p37 hv (of_decide_eq_true hsn))
  · rw [countAcceptP_eq_countList, countHN_eq_countList]
    refine countList_mono (treesOfSize n) (fun t ht hp => ?_)
    have ⟨hv, _⟩ := treesOfSize_sound ht
    exact decide_eq_true (evalPTerm_ne_p37_implies_evalHN_ne_hn34 hv (of_decide_eq_true hp))
  · rw [countHN_eq_countList, catalanTrees_eq_treesOfSize_length]
    exact countList_le_length _ _

/-! ## 5. Universal Positive Density Lower & Upper Bounds for `HasHNF` (`countHN`) -/

private theorem head_block_1_hn (m : Nat) :
    countList (fun t => decide (evalHN t ≠ .hn34))
      (listFlatMap (treesOfSize 1) (fun l => (treesOfSize (m + 1)).map (fun r => l ⋆ r))) =
    catalanTrees (m + 1) := by
  have h1 : treesOfSize 1 = [S] := rfl
  have hall : countList (fun x => decide (evalHN (S ⋆ x) ≠ .hn34)) (treesOfSize (m + 1)) =
      (treesOfSize (m + 1)).length :=
    countList_all_true (treesOfSize (m + 1)) (fun r _ => decide_eq_true (deltaHN_s1_ne_hn34 (evalHN r)))
  rw [h1, listFlatMap, listFlatMap, List.append_nil, countList_map, hall, catalanTrees_eq_treesOfSize_length]

private theorem countList_s2_block (as bs : List Term) :
    countList (fun t => decide (evalHN t ≠ .hn34))
      (listFlatMap (as.map (fun a => S ⋆ a)) (fun l => bs.map (fun b => l ⋆ b))) =
    as.length * bs.length := by
  induction as with
  | nil => simp only [List.map_nil, listFlatMap, countList, List.length_nil, Nat.zero_mul]
  | cons a as ih =>
    simp only [List.map_cons, listFlatMap, countList_append, List.length_cons, ih]
    have hb_eq : countList (fun x => decide (evalHN ((S ⋆ a) ⋆ x) ≠ .hn34)) bs = bs.length :=
      countList_all_true bs (fun b _ => decide_eq_true (deltaHN_s2_ne_hn34 (evalHN a) (evalHN b)))
    rw [countList_map, hb_eq, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Universal `1/4` lower bound: `catalanTrees (n - 1) ≤ countHN n` for all `n ≥ 2` via `r ↦ S ⋅ r`. -/
theorem countHN_ge_catalan_pred (n : Nat) (hn : 2 ≤ n) :
    catalanTrees (n - 1) ≤ countHN n := by
  have ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  subst hm
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub, countHN_eq_countList, treesOfSize_recurrence]
  have hsp : splits (m + 2) = (1, m + 1) :: splitsAux m 2 := rfl
  rw [hsp, listFlatMap, countList_append, head_block_1_hn m]
  exact Nat.le_add_right _ _

theorem catalanTrees_mono_succ (k : Nat) (hk : 1 ≤ k) :
    catalanTrees k ≤ catalanTrees (k + 1) := by
  have h1 := countHN_ge_catalan_pred (k + 1) (by omega)
  have h2 := (universal_count_hierarchy (k + 1)).2.2
  have hsub : k + 1 - 1 = k := by omega
  rw [hsub] at h1
  exact Nat.le_trans h1 h2

private theorem splitsAux_shift (K a : Nat) :
    splitsAux K (a + 1) = (splitsAux K a).map (fun p => (p.1 + 1, p.2)) := by
  induction K generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [splitsAux, List.map_cons]
    congr 1
    exact ih (a + 1)

/-- Sharp syntactic HNF lower bound: `2 * catalanTrees (n - 1) ≤ countHN n` for all `n ≥ 3` (`> 1/2`!). -/
theorem countHN_ge_two_mul_catalan_pred (n : Nat) (hn : 3 ≤ n) :
    2 * catalanTrees (n - 1) ≤ countHN n := by
  have ⟨d, hd⟩ : ∃ d, n = d + 3 := ⟨n - 3, by omega⟩
  subst hd
  have hsub : d + 3 - 1 = d + 2 := by omega
  have hd3 : d + 3 = (d + 1) + 2 := by omega
  rw [hsub, countHN_eq_countList, hd3, treesOfSize_recurrence (d + 1)]
  have hsp : splits ((d + 1) + 2) = (1, d + 2) :: (splits (d + 2)).map (fun p => (p.1 + 1, p.2)) := by
    change (1, d + 2) :: splitsAux (d + 1) 2 = (1, d + 2) :: (splitsAux (d + 1) 1).map _
    rw [splitsAux_shift (d + 1) 1]
  rw [hsp, listFlatMap, countList_append, head_block_1_hn (d + 1), countList_listFlatMap, sumList_map]
  have h2hnf : ∀ p ∈ splits (d + 2),
      catalanTrees p.1 * catalanTrees p.2 ≤
        countList (fun t => decide (evalHN t ≠ .hn34))
          (listFlatMap (treesOfSize (p.1 + 1)) (fun l => (treesOfSize p.2).map (fun r => l ⋆ r))) := by
    intro ⟨j, rsz⟩ hp
    dsimp only
    have ⟨hj1, _, _⟩ := mem_splits_iff.mp hp
    have ⟨j0, hj0⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
    subst hj0
    have hj2 : j0 + 1 + 1 = j0 + 2 := rfl
    rw [hj2, treesOfSize_recurrence j0]
    have hspj : splits (j0 + 2) = (1, j0 + 1) :: splitsAux j0 2 := rfl
    have hfirst : treesOfSize 1 = [S] := rfl
    rw [hspj, listFlatMap]
    dsimp only
    rw [hfirst, listFlatMap, listFlatMap, List.append_nil, listFlatMap_append, countList_append,
        countList_s2_block, ← catalanTrees_eq_treesOfSize_length (j0 + 1), ← catalanTrees_eq_treesOfSize_length rsz]
    exact Nat.le_add_right _ _
  have hsum_ge := sumList_le_sumList h2hnf
  rw [← catalanTrees_recurrence d] at hsum_ge
  change 2 * catalanTrees (d + 2) ≤
    catalanTrees (d + 2) +
      sumList (splits (d + 2)) (fun p =>
        countList (fun t => decide (evalHN t ≠ .hn34))
          (listFlatMap (treesOfSize (p.1 + 1)) (fun l => (treesOfSize p.2).map (fun r => l ⋆ r))))
  omega

theorem countHN_ge_pred_add_pred2 (n : Nat) (hn : 2 ≤ n) :
    catalanTrees (n - 1) + catalanTrees (n - 2) ≤ countHN n := by
  cases n with
  | zero => omega
  | succ n1 =>
    cases n1 with
    | zero => omega
    | succ m =>
      cases m with
      | zero => decide
      | succ d =>
        change catalanTrees ((d + 3) - 1) + catalanTrees ((d + 3) - 2) ≤ countHN (d + 3)
        have h2 := countHN_ge_two_mul_catalan_pred (d + 3) (by omega)
        have hm := catalanTrees_mono_succ (d + 1) (by omega)
        have hs1 : (d + 3) - 1 = d + 2 := by omega
        have hs2 : (d + 3) - 2 = d + 1 := by omega
        have hs3 : (d + 1) + 1 = d + 2 := rfl
        rw [hs3] at hm
        rw [hs1] at h2
        rw [hs1, hs2]
        omega

/-- Minimal 8-leaf pure-`S` combinator with no HNF (`evalHN = .hn34`): `S(SSS)S(SSS)`. -/
def minHN34_8 : Term := S ⋆ (S ⋆ S ⋆ S) ⋆ S ⋆ (S ⋆ S ⋆ S)

theorem minHN34_8_props :
    noVars minHN34_8 = true ∧ leaves minHN34_8 = 8 ∧ evalHN minHN34_8 = .hn34 :=
  ⟨rfl, rfl, rfl⟩

/-- Minimal 7-leaf non-SN / non-AcceptP witness (`S(SS)SSSS`) & 9-leaf Zachos precursor (`S(S(SS))(S(SS))(SS)`). -/
def minNonSN_7 : Term := S ⋆ (S ⋆ S) ⋆ S ⋆ S ⋆ S ⋆ S
def zachosPrecursor_9 : Term := S ⋆ (S ⋆ (S ⋆ S)) ⋆ (S ⋆ (S ⋆ S)) ⋆ (S ⋆ S)

theorem minimal_phase_onset_witnesses :
    (leaves minNonSN_7 = 7 ∧ evalSN minNonSN_7 = .sn38 ∧ evalPTerm minNonSN_7 = .p37 ∧ evalHN minNonSN_7 ≠ .hn34) ∧
    (leaves minHN34_8 = 8 ∧ evalHN minHN34_8 = .hn34) ∧
    (leaves zachosPrecursor_9 = 9 ∧ evalPTerm zachosPrecursor_9 ≠ .p37 ∧ evalSN zachosPrecursor_9 = .sn38) := by
  decide

/-- Universal upper bound on `#HN(n)` (`∀ n ≥ 9, catalanTrees (n - 8) ≤ countNonHN n`):
    left-application `minHN34_8 ⋅ r` forces `.hn34` for all `C_{n-9}` right subtrees `r`! -/
theorem countNonHN_ge_catalan_sub8 (n : Nat) (hn : 9 ≤ n) :
    catalanTrees (n - 8) ≤ countNonHN n := by
  have ⟨d, hd⟩ : ∃ d, n = d + 9 := ⟨n - 9, by omega⟩
  subst hd
  have hsub : d + 9 - 8 = d + 1 := by omega
  have hd9 : d + 9 = (d + 7) + 2 := by omega
  rw [hsub, countNonHN_eq_countList, hd9, treesOfSize_recurrence (d + 7), countList_listFlatMap]
  have hsp8 : (8, d + 1) ∈ splits ((d + 7) + 2) := mem_splits_iff.mpr ⟨by omega, by omega, by omega⟩
  have hmem_w : minHN34_8 ∈ treesOfSize 8 :=
    treesOfSize_complete minHN34_8_props.1 minHN34_8_props.2.1
  have h_at_w : countList (fun t => decide (evalHN t = .hn34))
      ((treesOfSize (d + 1)).map (fun r => minHN34_8 ⋆ r)) = catalanTrees (d + 1) := by
    rw [countList_map, catalanTrees_eq_treesOfSize_length (d + 1)]
    refine countList_all_true (treesOfSize (d + 1)) (fun r _ => decide_eq_true ?_)
    change deltaHN (evalHN minHN34_8) (evalHN r) = .hn34
    rw [minHN34_8_props.2.2]
    exact deltaHN_hn34_left (evalHN r)
  have hblock8 : catalanTrees (d + 1) ≤
      countList (fun t => decide (evalHN t = .hn34))
        (listFlatMap (treesOfSize 8) (fun l => (treesOfSize (d + 1)).map (fun r => l ⋆ r))) := by
    rw [countList_listFlatMap, ← h_at_w]
    exact mem_le_sumList hmem_w
      (fun l => countList (fun t => decide (evalHN t = .hn34)) ((treesOfSize (d + 1)).map (fun r => l ⋆ r)))
  exact Nat.le_trans hblock8
    (mem_le_sumList hsp8
      (fun p => countList (fun t => decide (evalHN t = .hn34))
        (listFlatMap (treesOfSize p.1) (fun l => (treesOfSize p.2).map (fun r => l ⋆ r)))))

/-- **Combined Universal Positive Two-Sided Density Theorem for `HasHNF` (`∀ n ≥ 9`)**:
    `catalanTrees (n - 1) ≤ 2 * catalanTrees (n - 1) ≤ countHN n ≤ catalanTrees n - catalanTrees (n - 8)`! -/
theorem hn_universal_two_sided_density_bounds (n : Nat) (hn : 9 ≤ n) :
    catalanTrees (n - 1) ≤ countHN n ∧
    2 * catalanTrees (n - 1) ≤ countHN n ∧
    countHN n + catalanTrees (n - 8) ≤ catalanTrees n := by
  refine ⟨countHN_ge_catalan_pred n (by omega), countHN_ge_two_mul_catalan_pred n (by omega), ?_⟩
  have hnon := countNonHN_ge_catalan_sub8 n hn
  have htot := countHN_add_countNonHN n
  omega

/-! ## 6. Fast Memoized Census Verification (`n = 1..20`) & Universal Exponential Decay Bounds -/

def getNatAt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getNatAt xs k

theorem getNatAt_append_left {xs ys : List Nat} {k : Nat} (hk : k < xs.length) :
    getNatAt (xs ++ ys) k = getNatAt xs k := by
  induction xs generalizing k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k0 =>
      simp only [List.cons_append, getNatAt]
      exact ih (by simp only [List.length_cons] at hk; omega)

theorem getNatAt_append_singleton {xs : List Nat} (v : Nat) :
    getNatAt (xs ++ [v]) xs.length = v := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, List.length_cons, getNatAt, ih]

def fastCatalanTable : Nat → List Nat
  | 0 => [0]
  | k + 1 =>
    let prev := fastCatalanTable k
    match k with
    | 0 => [0, 1]
    | m + 1 =>
      prev ++ [sumList (splits (m + 2)) (fun p => getNatAt prev p.1 * getNatAt prev p.2)]

def fastCatalan (n : Nat) : Nat := getNatAt (fastCatalanTable n) n

private theorem fastCatalanTable_step (m : Nat) :
    fastCatalanTable (m + 2) =
      fastCatalanTable (m + 1) ++
        [sumList (splits (m + 2)) (fun p =>
          getNatAt (fastCatalanTable (m + 1)) p.1 * getNatAt (fastCatalanTable (m + 1)) p.2)] := rfl

private theorem fastCatalanTable_len (n : Nat) : (fastCatalanTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m =>
      change (fastCatalanTable (m + 2)).length = (m + 1) + 1 + 1
      rw [fastCatalanTable_step m, List.length_append, List.length_cons, List.length_nil, ih]

private theorem fastCatalanTable_spec (n : Nat) :
    ∀ (k : Nat), k ≤ n → getNatAt (fastCatalanTable n) k = catalanTrees k := by
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  | succ n0 ih =>
    intro k hk
    cases n0 with
    | zero =>
      cases k with
      | zero => rfl
      | succ k0 =>
        have hk0' : k0 = 0 := by omega
        subst hk0'; rfl
    | succ m =>
      change getNatAt (fastCatalanTable (m + 2)) k = catalanTrees k
      rw [fastCatalanTable_step m]
      exact if hlt : k ≤ m + 1 then by
        rw [getNatAt_append_left (by rw [fastCatalanTable_len (m + 1)]; omega)]
        exact ih k hlt
      else by
        have hkeq : k = m + 2 := by omega
        subst hkeq
        have hlen : (fastCatalanTable (m + 1)).length = m + 2 := fastCatalanTable_len (m + 1)
        rw [← hlen, getNatAt_append_singleton, hlen, catalanTrees_recurrence m]
        refine sumList_congr (fun ⟨x, y⟩ hp => ?_)
        dsimp only
        have ⟨_, _, _⟩ := mem_splits_iff.mp hp
        rw [ih x (by omega), ih y (by omega)]

theorem fastCatalan_eq (n : Nat) : fastCatalan n = catalanTrees n :=
  fastCatalanTable_spec n n (Nat.le_refl n)

private theorem catalan_base_1_to_14 (n : Nat) (h1 : 1 ≤ n) (h14 : n ≤ 14) :
    7 ^ n ≤ 58 * 2 ^ n * fastCatalan n := by
  match n with
  | 1 => decide | 2 => decide | 3 => decide | 4 => decide | 5 => decide
  | 6 => decide | 7 => decide | 8 => decide | 9 => decide | 10 => decide
  | 11 => decide | 12 => decide | 13 => decide | 14 => decide
  | 0 => omega
  | _ + 15 => omega

private theorem splitsAux_split (k1 k2 a : Nat) :
    splitsAux (k1 + k2) a =
      (splitsAux k1 a).map (fun p => (p.1, p.2 + k2)) ++ splitsAux k2 (a + k1) := by
  induction k1 generalizing a with
  | zero => simp only [Nat.zero_add, Nat.add_zero, splitsAux, List.map_nil, List.nil_append]
  | succ k ih =>
    have h1 : k + 1 + k2 = (k + k2) + 1 := by omega
    rw [h1]
    simp only [splitsAux, List.map_cons, List.cons_append]
    have hp : (a, k + k2 + 1) = (a, k + 1 + k2) := by congr 1; omega
    rw [hp, ih (a + 1)]
    have h2 : a + 1 + k = a + (k + 1) := by omega
    rw [h2]

private theorem catalan_1_to_7_vals :
    catalanTrees 1 = 1 ∧ catalanTrees 2 = 1 ∧ catalanTrees 3 = 2 ∧ catalanTrees 4 = 5 ∧
    catalanTrees 5 = 14 ∧ catalanTrees 6 = 42 ∧ catalanTrees 7 = 132 := by
  rw [← fastCatalan_eq 1, ← fastCatalan_eq 2, ← fastCatalan_eq 3, ← fastCatalan_eq 4,
      ← fastCatalan_eq 5, ← fastCatalan_eq 6, ← fastCatalan_eq 7]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem pow_shift_const (b n k : Nat) : b ^ (n + k) = (b ^ k) * (b ^ n) := by
  rw [Nat.pow_add, Nat.mul_comm]

private theorem factor_const_58 (c1 c2 P C : Nat) :
    58 * (c1 * P) * (c2 * C) = (c1 * c2) * (58 * P * C) := by
  calc
    58 * (c1 * P) * (c2 * C) = c1 * (58 * P) * (c2 * C) := by rw [Nat.mul_left_comm 58 c1 P]
    _ = c1 * ((58 * P) * (c2 * C)) := by rw [Nat.mul_assoc]
    _ = c1 * (c2 * ((58 * P) * C)) := by rw [Nat.mul_left_comm (58 * P) c2 C]
    _ = (c1 * c2) * (58 * P * C) := by rw [← Nat.mul_assoc]

private theorem catalanTrees_exp_lower_strong (N : Nat) :
    ∀ (n : Nat), 1 ≤ n → n ≤ N → 7 ^ n ≤ 58 * 2 ^ n * catalanTrees n := by
  induction N with
  | zero => intro _ h1 hle; omega
  | succ N0 ihN =>
    intro n h1 hle
    exact if hlt : n ≤ N0 then
      ihN n h1 hlt
    else by
      have hne : n = N0 + 1 := by omega
      subst hne
      exact if h14 : N0 + 1 ≤ 14 then by
        rw [← fastCatalan_eq (N0 + 1)]
        exact catalan_base_1_to_14 (N0 + 1) h1 h14
      else by
        have ⟨m, hm⟩ : ∃ m, N0 + 1 = m + 15 := ⟨N0 - 14, by omega⟩
        have ih : ∀ k, 1 ≤ k → k ≤ m + 14 → 7 ^ k ≤ 58 * 2 ^ k * catalanTrees k :=
          fun k hk1 hkm => ihN k hk1 (by omega)
        rw [hm, catalanTrees_recurrence (m + 13)]
        have hdecomp : splits (m + 15) =
            (splitsAux 7 1).map (fun p => (p.1, p.2 + (m + 7))) ++
            ((splitsAux m 8).map (fun p => (p.1, p.2 + 7)) ++ splitsAux 7 (8 + m)) := by
          change splitsAux (m + 14) 1 = _
          have heq14 : m + 14 = 7 + (m + 7) := by omega
          rw [heq14, splitsAux_split 7 (m + 7) 1, splitsAux_split m 7 8]
        rw [hdecomp, sumList_append, sumList_append]
        have ⟨c1, c2, c3, c4, c5, c6, c7⟩ := catalan_1_to_7_vals
        have hhead7 : sumList ((splitsAux 7 1).map (fun p => (p.1, p.2 + (m + 7))))
            (fun p => catalanTrees p.1 * catalanTrees p.2) =
            1 * catalanTrees (m + 14) + 1 * catalanTrees (m + 13) + 2 * catalanTrees (m + 12) +
            5 * catalanTrees (m + 11) + 14 * catalanTrees (m + 10) + 42 * catalanTrees (m + 9) +
            132 * catalanTrees (m + 8) := by
          simp only [splitsAux, List.map, sumList, c1, c2, c3, c4, c5, c6, c7]
          have e1 : 7 + (m + 7) = m + 14 := by omega
          have e2 : 6 + (m + 7) = m + 13 := by omega
          have e3 : 5 + (m + 7) = m + 12 := by omega
          have e4 : 4 + (m + 7) = m + 11 := by omega
          have e5 : 3 + (m + 7) = m + 10 := by omega
          have e6 : 2 + (m + 7) = m + 9 := by omega
          have e7 : 1 + (m + 7) = m + 8 := by omega
          rw [e1, e2, e3, e4, e5, e6, e7]
          omega
        have htail7 : sumList (splitsAux 7 (8 + m))
            (fun p => catalanTrees p.1 * catalanTrees p.2) =
            catalanTrees (m + 8) * 132 + catalanTrees (m + 9) * 42 + catalanTrees (m + 10) * 14 +
            catalanTrees (m + 11) * 5 + catalanTrees (m + 12) * 2 + catalanTrees (m + 13) * 1 +
            catalanTrees (m + 14) * 1 := by
          have f0 : 8 + m = m + 8 := by omega
          rw [f0]
          simp only [splitsAux, sumList]
          change catalanTrees (m + 8) * catalanTrees 7 +
            (catalanTrees (m + 9) * catalanTrees 6 +
              (catalanTrees (m + 10) * catalanTrees 5 +
                (catalanTrees (m + 11) * catalanTrees 4 +
                  (catalanTrees (m + 12) * catalanTrees 3 +
                    (catalanTrees (m + 13) * catalanTrees 2 +
                      (catalanTrees (m + 14) * catalanTrees 1 + 0)))))) = _
          rw [c1, c2, c3, c4, c5, c6, c7]
          omega
        rw [hhead7, htail7]
        have b1 := ih (m + 14) (by omega) (by omega)
        have b2 := ih (m + 13) (by omega) (by omega)
        have b3 := ih (m + 12) (by omega) (by omega)
        have b4 := ih (m + 11) (by omega) (by omega)
        have b5 := ih (m + 10) (by omega) (by omega)
        have b6 := ih (m + 9) (by omega) (by omega)
        have b7 := ih (m + 8) (by omega) (by omega)
        have q7_15 : 7 ^ (m + 15) = 823543 * 7 ^ (m + 8) := by
          rw [show m + 15 = (m + 8) + 7 by omega, pow_shift_const]
        have q7_14 : 7 ^ (m + 14) = 117649 * 7 ^ (m + 8) := by
          rw [show m + 14 = (m + 8) + 6 by omega, pow_shift_const]
        have q7_13 : 7 ^ (m + 13) = 16807 * 7 ^ (m + 8) := by
          rw [show m + 13 = (m + 8) + 5 by omega, pow_shift_const]
        have q7_12 : 7 ^ (m + 12) = 2401 * 7 ^ (m + 8) := by
          rw [show m + 12 = (m + 8) + 4 by omega, pow_shift_const]
        have q7_11 : 7 ^ (m + 11) = 343 * 7 ^ (m + 8) := by
          rw [show m + 11 = (m + 8) + 3 by omega, pow_shift_const]
        have q7_10 : 7 ^ (m + 10) = 49 * 7 ^ (m + 8) := by
          rw [show m + 10 = (m + 8) + 2 by omega, pow_shift_const]
        have q7_9  : 7 ^ (m + 9)  = 7 * 7 ^ (m + 8) := by
          rw [show m + 9 = (m + 8) + 1 by omega, pow_shift_const]
        rw [q7_14] at b1
        rw [q7_13] at b2
        rw [q7_12] at b3
        rw [q7_11] at b4
        rw [q7_10] at b5
        rw [q7_9]  at b6
        have r1 : 58 * 2 ^ (m + 15) * (2 * catalanTrees (m + 14)) =
            4 * (58 * 2 ^ (m + 14) * catalanTrees (m + 14)) := by
          rw [show m + 15 = (m + 14) + 1 by omega, pow_shift_const]
          exact factor_const_58 (2 ^ 1) 2 (2 ^ (m + 14)) (catalanTrees (m + 14))
        have r2 : 58 * 2 ^ (m + 15) * (2 * catalanTrees (m + 13)) =
            8 * (58 * 2 ^ (m + 13) * catalanTrees (m + 13)) := by
          rw [show m + 15 = (m + 13) + 2 by omega, pow_shift_const]
          exact factor_const_58 (2 ^ 2) 2 (2 ^ (m + 13)) (catalanTrees (m + 13))
        have r3 : 58 * 2 ^ (m + 15) * (4 * catalanTrees (m + 12)) =
            32 * (58 * 2 ^ (m + 12) * catalanTrees (m + 12)) := by
          rw [show m + 15 = (m + 12) + 3 by omega, pow_shift_const]
          exact factor_const_58 (2 ^ 3) 4 (2 ^ (m + 12)) (catalanTrees (m + 12))
        have r4 : 58 * 2 ^ (m + 15) * (10 * catalanTrees (m + 11)) =
            160 * (58 * 2 ^ (m + 11) * catalanTrees (m + 11)) := by
          rw [show m + 15 = (m + 11) + 4 by omega, pow_shift_const]
          exact factor_const_58 (2 ^ 4) 10 (2 ^ (m + 11)) (catalanTrees (m + 11))
        have r5 : 58 * 2 ^ (m + 15) * (28 * catalanTrees (m + 10)) =
            896 * (58 * 2 ^ (m + 10) * catalanTrees (m + 10)) := by
          rw [show m + 15 = (m + 10) + 5 by omega, pow_shift_const]
          exact factor_const_58 (2 ^ 5) 28 (2 ^ (m + 10)) (catalanTrees (m + 10))
        have r6 : 58 * 2 ^ (m + 15) * (84 * catalanTrees (m + 9)) =
            5376 * (58 * 2 ^ (m + 9) * catalanTrees (m + 9)) := by
          rw [show m + 15 = (m + 9) + 6 by omega, pow_shift_const]
          exact factor_const_58 (2 ^ 6) 84 (2 ^ (m + 9)) (catalanTrees (m + 9))
        have r7 : 58 * 2 ^ (m + 15) * (264 * catalanTrees (m + 8)) =
            33792 * (58 * 2 ^ (m + 8) * catalanTrees (m + 8)) := by
          rw [show m + 15 = (m + 8) + 7 by omega, pow_shift_const]
          exact factor_const_58 (2 ^ 7) 264 (2 ^ (m + 8)) (catalanTrees (m + 8))
        have hsum_7 : 7 ^ (m + 15) ≤
            58 * 2 ^ (m + 15) *
              (2 * catalanTrees (m + 14) + 2 * catalanTrees (m + 13) + 4 * catalanTrees (m + 12) +
               10 * catalanTrees (m + 11) + 28 * catalanTrees (m + 10) + 84 * catalanTrees (m + 9) +
               264 * catalanTrees (m + 8)) := by
          rw [q7_15]
          simp only [Nat.mul_add, r1, r2, r3, r4, r5, r6, r7]
          omega
        exact Nat.le_trans hsum_7 (Nat.mul_le_mul_left (58 * 2 ^ (m + 15)) (by omega))

theorem catalanTrees_universal_exp_lower (n : Nat) (hn : 1 ≤ n) :
    7 ^ n ≤ 58 * 2 ^ n * catalanTrees n :=
  catalanTrees_exp_lower_strong n n hn (Nat.le_refl n)

/-! ### Generating-Function Majorant Certificate at `z = 37/125` (`Q/P = 125/37 < 7/2`) -/

def range1To : Nat → List Nat
  | 0 => []
  | m + 1 => range1To m ++ [m + 1]

def scaledGenSum {Q : Type} (dp : Nat → Q → Nat) (P Qn M : Nat) (q : Q) : Nat :=
  sumList (range1To M) (fun k => dp k q * (P ^ k) * (Qn ^ (M - k)))

theorem last_le_scaledGenSum {Q : Type} (dp : Nat → Q → Nat) (P Qn : Nat)
    (n : Nat) (hn : 1 ≤ n) (q : Q) :
    dp n q * (P ^ n) ≤ scaledGenSum dp P Qn n q := by
  have ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  unfold scaledGenSum
  simp only [range1To, sumList_append, sumList, Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  exact Nat.le_add_left _ _

private theorem mem_range1To_bounds {M k : Nat} (hk : k ∈ range1To M) : 1 ≤ k ∧ k ≤ M := by
  induction M with
  | zero => cases hk
  | succ m ih =>
    simp only [range1To, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h1 | h2
    · have ⟨a, b⟩ := ih h1; exact ⟨a, by omega⟩
    · subst h2; exact ⟨by omega, by omega⟩

private theorem sum_splitsAux_eq_range1To (K : Nat) :
    ∀ (h : Nat → Nat → Nat) (a : Nat),
      sumList (splitsAux K a) (fun p => h p.1 p.2) =
      sumList (range1To K) (fun i => h (a + i - 1) (K + 1 - i)) := by
  induction K with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro h a
    have hsp := splitsAux_split k 1 a
    rw [hsp, sumList_append, sumList_map]
    have htail : sumList (splitsAux 1 (a + k)) (fun p => h p.1 p.2) = h (a + k) 1 := by
      simp only [splitsAux, sumList, Nat.add_zero]
    have hrng : sumList (range1To (k + 1)) (fun i => h (a + i - 1) (k + 1 + 1 - i)) =
        sumList (range1To k) (fun i => h (a + i - 1) (k + 1 + 1 - i)) +
        h (a + (k + 1) - 1) (k + 1 + 1 - (k + 1)) := by
      simp only [range1To, sumList_append, sumList, Nat.add_zero]
    rw [htail, hrng, ih (fun x y => h x (y + 1)) a]
    have h1 : sumList (range1To k) (fun i => h (a + i - 1) (k + 1 - i + 1)) =
        sumList (range1To k) (fun i => h (a + i - 1) (k + 1 + 1 - i)) := by
      refine sumList_congr (fun i hi => ?_)
      have ⟨_, _⟩ := mem_range1To_bounds hi
      have e2 : k + 1 - i + 1 = k + 1 + 1 - i := by omega
      rw [e2]
    have h2 : h (a + k) 1 = h (a + (k + 1) - 1) (k + 1 + 1 - (k + 1)) := by
      have e1 : a + (k + 1) - 1 = a + k := by omega
      have e2 : k + 1 + 1 - (k + 1) = 1 := by omega
      rw [e1, e2]
    rw [h1, h2]

private theorem sum_range1To_mono_len (f : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
    sumList (range1To a) f ≤ sumList (range1To b) f := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; exact Nat.le_refl 0
  | succ b0 ih =>
    exact if hlt : a ≤ b0 then by
      simp only [range1To, sumList_append]
      exact Nat.le_trans (ih hlt) (Nat.le_add_right _ _)
    else by
      have haeq : a = b0 + 1 := by omega
      subst haeq; exact Nat.le_refl _

private theorem triangular_splits_eq_antidiag (h : Nat → Nat → Nat) (M : Nat) :
    sumList (range1To M) (fun m => sumList (splits (m + 1)) (fun p => h p.1 p.2)) =
    sumList (range1To M) (fun k => sumList (range1To (M + 1 - k)) (fun j => h k j)) := by
  induction M with
  | zero => rfl
  | succ M0 ih =>
    simp only [range1To, sumList_append, sumList, Nat.add_zero]
    rw [ih]
    have hlast : sumList (splits (M0 + 2)) (fun p => h p.1 p.2) =
        sumList (range1To M0) (fun k => h k (M0 + 2 - k)) + h (M0 + 1) 1 := by
      change sumList (splitsAux (M0 + 1) 1) _ = _
      rw [sum_splitsAux_eq_range1To (M0 + 1) h 1]
      simp only [range1To, sumList_append, sumList, Nat.add_zero]
      have p1 : sumList (range1To M0) (fun k => h (1 + k - 1) (M0 + 1 + 1 - k)) =
          sumList (range1To M0) (fun k => h k (M0 + 2 - k)) := by
        refine sumList_congr (fun k hk => ?_)
        have ⟨_, _⟩ := mem_range1To_bounds hk
        have e1 : 1 + k - 1 = k := by omega
        have e2 : M0 + 1 + 1 - k = M0 + 2 - k := by omega
        rw [e1, e2]
      have p2 : h (1 + (M0 + 1) - 1) (M0 + 1 + 1 - (M0 + 1)) = h (M0 + 1) 1 := by
        have e1 : 1 + (M0 + 1) - 1 = M0 + 1 := by omega
        have e2 : M0 + 1 + 1 - (M0 + 1) = 1 := by omega
        rw [e1, e2]
      rw [p1, p2]
    rw [hlast, ← Nat.add_assoc, ← sumList_add_distrib]
    have p3 : sumList (range1To M0) (fun x => sumList (range1To (M0 + 1 - x)) (fun j => h x j) + h x (M0 + 2 - x)) =
        sumList (range1To M0) (fun k => sumList (range1To (M0 + 1 + 1 - k)) (fun j => h k j)) := by
      refine sumList_congr (fun k hk => ?_)
      have ⟨_, _⟩ := mem_range1To_bounds hk
      have hlen : M0 + 1 + 1 - k = (M0 + 1 - k) + 1 := by omega
      have hlen2 : M0 + 1 - k + 1 = M0 + 2 - k := by omega
      rw [hlen]
      simp only [range1To, sumList_append, sumList, Nat.add_zero, hlen2]
    have p4 : h (M0 + 1) 1 = sumList (range1To (M0 + 1 + 1 - (M0 + 1))) (fun j => h (M0 + 1) j) := by
      have hsub1 : M0 + 1 + 1 - (M0 + 1) = 1 := by omega
      rw [hsub1]
      rfl
    rw [p3, p4]

private theorem triangular_splits_le_square (h : Nat → Nat → Nat) (M : Nat) :
    sumList (range1To M) (fun m => sumList (splits (m + 1)) (fun p => h p.1 p.2)) ≤
      sumList (range1To M) (fun k => sumList (range1To M) (fun j => h k j)) := by
  rw [triangular_splits_eq_antidiag h M]
  refine sumList_le_sumList (fun k hk => ?_)
  have ⟨_, _⟩ := mem_range1To_bounds hk
  exact sum_range1To_mono_len (h k) (by omega)

private theorem sumList_comm {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumList xs (fun x => sumList ys (fun y => f x y)) =
      sumList ys (fun y => sumList xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    simp only [sumList]
    exact (sumList_zero ys).symm
  | cons x xs ih =>
    simp only [sumList, ih, ← sumList_add_distrib]

private theorem sum_sub_of_zero_outside {Q : Type} [DecidableEq Q]
    {xs : List Q} (hnd : NodupList xs) (accQ : List Q) :
    ∀ (f : Q → Nat), (∀ z ∈ xs, f z = 0 ∨ z ∈ accQ) → sumList xs f ≤ sumList accQ f := by
  induction hnd with
  | nil => intro _ _; exact Nat.zero_le _
  | @cons z zs hz _ ihz =>
    intro f hcond
    simp only [sumList]
    rcases hcond z (List.Mem.head _) with hfz0 | hz_acc
    · rw [hfz0, Nat.zero_add]
      exact ihz f (fun w hw => hcond w (List.Mem.tail _ hw))
    · let f_z : Q → Nat := fun w => if w = z then f w else 0
      let f_rest : Q → Nat := fun w => if w = z then 0 else f w
      have hrest_eq : sumList zs f = sumList zs f_rest :=
        sumList_congr (fun w hw => by simp only [f_rest, if_neg (fun heq : w = z => hz (heq ▸ hw))])
      have hrest_le := ihz f_rest (fun w hw =>
        match hcond w (List.Mem.tail _ hw) with
        | Or.inl h0 =>
          Or.inl (by
            simp only [f_rest]
            cases hd : decide (w = z) with
            | true => rw [if_pos (of_decide_eq_true hd)]
            | false => rw [if_neg (of_decide_eq_false hd), h0])
        | Or.inr hm => Or.inr hm)
      have hfz_le : f z ≤ sumList accQ f_z := by
        have := mem_le_sumList hz_acc f_z
        simp only [f_z, ite_true] at this
        exact this
      have hcomb := Nat.add_le_add hfz_le (hrest_eq ▸ hrest_le)
      have hpt : ∀ w ∈ accQ, f_z w + f_rest w = f w := by
        intro w _
        simp only [f_z, f_rest]
        cases hd : decide (w = z) with
        | true => rw [if_pos (of_decide_eq_true hd), if_pos (of_decide_eq_true hd), Nat.add_zero]
        | false => rw [if_neg (of_decide_eq_false hd), if_neg (of_decide_eq_false hd), Nat.zero_add]
      rw [← sumList_add_distrib, sumList_congr hpt] at hcomb
      exact hcomb

private theorem range1To_succ_cons (K : Nat) :
    range1To (K + 1) = 1 :: (range1To K).map (fun r => r + 1) := by
  induction K with
  | zero => rfl
  | succ k0 ih =>
    calc
      range1To (k0 + 2) = range1To (k0 + 1) ++ [k0 + 2] := rfl
      _ = (1 :: (range1To k0).map (fun r => r + 1)) ++ [k0 + 2] := by rw [ih]
      _ = 1 :: ((range1To k0).map (fun r => r + 1) ++ [(k0 + 1) + 1]) := rfl
      _ = 1 :: ((range1To k0 ++ [k0 + 1]).map (fun r => r + 1)) := by
        rw [List.map_append, List.map_cons, List.map_nil]
      _ = 1 :: (range1To (k0 + 1)).map (fun r => r + 1) := rfl

theorem dpState_exp_majorant {Q : Type} [DecidableEq Q]
    (allQ accQ : List Q)
    (delta : Q → Q → Q) (q0 sink : Q)
    (hsink : ∀ x, delta sink x = sink ∧ delta x sink = sink)
    (hacc : ∀ x : Q, x ≠ sink → x ∈ accQ)
    (hnot_sink : ∀ x ∈ accQ, x ≠ sink)
    (hnodup_all : NodupList allQ)
    (W : Q → Nat) (P Qn D : Nat) (hD : 0 < D) (hQn : 0 < Qn)
    (hbase : ∀ q ∈ accQ, D * (if q = q0 then 1 else 0) * P ≤ W q * Qn)
    (hstep : ∀ q ∈ accQ,
      D * D * (if q = q0 then 1 else 0) * P +
        Qn * sumList accQ (fun a => sumList accQ (fun b => if delta a b = q then W a * W b else 0)) ≤
      D * W q * Qn) :
    ∀ (M : Nat), 1 ≤ M → ∀ q ∈ accQ,
      D * scaledGenSum (dpState allQ delta q0) P Qn M q ≤ W q * (Qn ^ M) := by
  intro M hM
  have ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  subst hm
  induction m with
  | zero =>
    intro q hq
    unfold scaledGenSum
    simp only [range1To, sumList_append, sumList, dpState, dpStateAux, Nat.sub_self,
      Nat.pow_one, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
    rw [← Nat.mul_assoc]
    exact hbase q hq
  | succ m0 ih =>
    intro q hq
    have hq_ne := hnot_sink q hq
    let dp := dpState allQ delta q0
    let M1 := m0 + 1
    have ih' := ih (by omega)
    have hsplit_M : scaledGenSum dp P Qn (M1 + 1) q =
        dp 1 q * P * (Qn ^ M1) +
        sumList (range1To M1) (fun r => dp (r + 1) q * (P ^ (r + 1)) * (Qn ^ (M1 - r))) := by
      unfold scaledGenSum
      rw [range1To_succ_cons M1]
      simp only [sumList, sumList_map, Nat.pow_one]
      have e1 : M1 + 1 - 1 = M1 := by omega
      have e2 : sumList (range1To M1) (fun x => dp (x + 1) q * P ^ (x + 1) * Qn ^ (M1 + 1 - (x + 1))) =
          sumList (range1To M1) (fun r => dp (r + 1) q * P ^ (r + 1) * Qn ^ (M1 - r)) := by
        refine sumList_congr (fun r _ => ?_)
        have esub : M1 + 1 - (r + 1) = M1 - r := by omega
        rw [esub]
      rw [e1, e2]
    have hall_to_acc : ∀ (x y : Nat),
        sumList allQ (fun a => sumList allQ (fun b =>
          if delta a b = q then dp x a * dp y b else 0)) ≤
        sumList accQ (fun a => sumList accQ (fun b =>
          if delta a b = q then dp x a * dp y b else 0)) := by
      intro x y
      have hinner : ∀ a : Q,
          sumList allQ (fun b => if delta a b = q then dp x a * dp y b else 0) ≤
          (if a = sink then 0 else sumList accQ (fun b => if delta a b = q then dp x a * dp y b else 0)) := by
        intro a
        cases ha_s : decide (a = sink) with
        | true =>
          rw [of_decide_eq_true ha_s, if_pos rfl]
          have h0 : ∀ b ∈ allQ, (if delta sink b = q then dp x sink * dp y b else 0) = 0 :=
            fun b _ => by rw [(hsink b).1, if_neg hq_ne.symm]
          rw [sumList_congr h0, sumList_zero]
          exact Nat.le_refl 0
        | false =>
          rw [if_neg (of_decide_eq_false ha_s)]
          exact sum_sub_of_zero_outside hnodup_all accQ _ (fun b _ =>
            if hbs : b = sink then
              Or.inl (by subst hbs; rw [(hsink a).2, if_neg hq_ne.symm])
            else Or.inr (hacc b hbs))
      have h1 := sumList_le_sumList (xs := allQ) (fun a _ => hinner a)
      have h2 := sum_sub_of_zero_outside hnodup_all accQ
        (fun a => if a = sink then 0 else sumList accQ (fun b => if delta a b = q then dp x a * dp y b else 0))
        (fun a _ => if has : a = sink then Or.inl (by rw [if_pos has]) else Or.inr (hacc a has))
      have h3 : sumList accQ (fun a => if a = sink then 0 else sumList accQ (fun b => if delta a b = q then dp x a * dp y b else 0)) ≤
          sumList accQ (fun a => sumList accQ (fun b => if delta a b = q then dp x a * dp y b else 0)) :=
        sumList_le_sumList (fun a _ => by
          cases hd : decide (a = sink) with
          | true => rw [if_pos (of_decide_eq_true hd)]; exact Nat.zero_le _
          | false => rw [if_neg (of_decide_eq_false hd)]; exact Nat.le_refl _)
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)

    have hmul_M : (Qn ^ m0) * scaledGenSum dp P Qn (M1 + 1) q ≤
        dp 1 q * P * (Qn ^ (2 * M1 - 1)) +
        sumList accQ (fun a => sumList accQ (fun b =>
          if delta a b = q then scaledGenSum dp P Qn M1 a * scaledGenSum dp P Qn M1 b else 0)) := by
      rw [hsplit_M, Nat.mul_add]
      have hfirst_eq : (Qn ^ m0) * (dp 1 q * P * (Qn ^ M1)) = dp 1 q * P * (Qn ^ (2 * M1 - 1)) := by
        have he : m0 + M1 = 2 * M1 - 1 := by omega
        rw [← Nat.mul_assoc, Nat.mul_comm (Qn ^ m0) (dp 1 q * P), Nat.mul_assoc, ← Nat.pow_add, he]
      rw [hfirst_eq]
      refine Nat.add_le_add_left ?_ _
      rw [← sumList_mul_left]
      let termF : Nat → Nat → Nat := fun x y =>
        sumList accQ (fun a => sumList accQ (fun b =>
          if delta a b = q then
            (dp x a * (P ^ x) * (Qn ^ (M1 - x))) * (dp y b * (P ^ y) * (Qn ^ (M1 - y)))
          else 0))
      have hterm_le : ∀ r ∈ range1To M1,
          (Qn ^ m0) * (dp (r + 1) q * (P ^ (r + 1)) * (Qn ^ (M1 - r))) ≤
          sumList (splits (r + 1)) (fun p => termF p.1 p.2) := by
        intro r hr
        have ⟨hr1, _⟩ := mem_range1To_bounds hr
        have ⟨r0, hr0⟩ : ∃ r0, r = r0 + 1 := ⟨r - 1, by omega⟩
        subst hr0
        have hdprec : dp (r0 + 2) q = sumList (splits (r0 + 2)) (fun p =>
            sumList allQ (fun a => sumList allQ (fun b =>
              if delta a b = q then dp p.1 a * dp p.2 b else 0))) :=
          dpState_recurrence allQ delta q0 r0 q
        rw [hdprec, ← sumList_mul_right, ← sumList_mul_right, ← sumList_mul_left]
        refine sumList_le_sumList (fun ⟨x, y⟩ hp => ?_)
        have ⟨_, _, hxy⟩ := mem_splits_iff.mp hp
        have hmul_ab := Nat.mul_le_mul_left (Qn ^ m0)
          (Nat.mul_le_mul_right (Qn ^ (M1 - (r0 + 1)))
            (Nat.mul_le_mul_right (P ^ (r0 + 2)) (hall_to_acc x y)))
        refine Nat.le_trans hmul_ab ?_
        dsimp only [termF]
        rw [← sumList_mul_right, ← sumList_mul_right, ← sumList_mul_left]
        refine sumList_le_sumList (fun a _ => ?_)
        try dsimp only
        rw [← sumList_mul_right, ← sumList_mul_right, ← sumList_mul_left]
        refine sumList_le_sumList (fun b _ => ?_)
        try dsimp only
        cases hd : decide (delta a b = q) with
        | false =>
          simp only [if_neg (of_decide_eq_false hd), Nat.zero_mul, Nat.mul_zero]
          exact Nat.le_refl 0
        | true =>
          simp only [if_pos (of_decide_eq_true hd)]
          have hp_eq : P ^ (r0 + 2) = (P ^ x) * (P ^ y) := by rw [← hxy, Nat.pow_add]
          have hq_eq : (Qn ^ m0) * (Qn ^ (M1 - (r0 + 1))) = (Qn ^ (M1 - x)) * (Qn ^ (M1 - y)) := by
            rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
          have heq_prod :
              (Qn ^ m0) * (dp x a * dp y b * (P ^ (r0 + 2)) * (Qn ^ (M1 - (r0 + 1)))) =
              (dp x a * (P ^ x) * (Qn ^ (M1 - x))) * (dp y b * (P ^ y) * (Qn ^ (M1 - y))) := by
            calc
              (Qn ^ m0) * (dp x a * dp y b * (P ^ (r0 + 2)) * (Qn ^ (M1 - (r0 + 1))))
                = (dp x a * dp y b) * (P ^ (r0 + 2)) * ((Qn ^ m0) * (Qn ^ (M1 - (r0 + 1)))) := by
                  simp only [Nat.mul_assoc, Nat.mul_left_comm]
              _ = (dp x a * dp y b) * ((P ^ x) * (P ^ y)) * ((Qn ^ (M1 - x)) * (Qn ^ (M1 - y))) := by
                  rw [hp_eq, hq_eq]
              _ = (dp x a * (P ^ x) * (Qn ^ (M1 - x))) * (dp y b * (P ^ y) * (Qn ^ (M1 - y))) := by
                  simp only [Nat.mul_assoc, Nat.mul_left_comm]
          rw [heq_prod]
          exact Nat.le_refl _
      have hsum_tri := Nat.le_trans (sumList_le_sumList hterm_le) (triangular_splits_le_square termF M1)
      refine Nat.le_trans hsum_tri ?_
      have hswap_eq : sumList (range1To M1) (fun x => sumList (range1To M1) (fun y => termF x y)) =
          sumList accQ (fun a => sumList accQ (fun b =>
            if delta a b = q then scaledGenSum dp P Qn M1 a * scaledGenSum dp P Qn M1 b else 0)) := by
        dsimp only [termF]
        have h1 : ∀ x, sumList (range1To M1) (fun y => sumList accQ (fun a => sumList accQ (fun b =>
            if delta a b = q then (dp x a * (P ^ x) * (Qn ^ (M1 - x))) * (dp y b * (P ^ y) * (Qn ^ (M1 - y))) else 0))) =
            sumList accQ (fun a => sumList accQ (fun b => sumList (range1To M1) (fun y =>
              if delta a b = q then (dp x a * (P ^ x) * (Qn ^ (M1 - x))) * (dp y b * (P ^ y) * (Qn ^ (M1 - y))) else 0))) := by
          intro x
          rw [sumList_comm (range1To M1) accQ]
          refine sumList_congr (fun a _ => sumList_comm (range1To M1) accQ _)
        rw [sumList_congr (fun x _ => h1 x), sumList_comm (range1To M1) accQ]
        refine sumList_congr (fun a _ => ?_)
        rw [sumList_comm (range1To M1) accQ]
        refine sumList_congr (fun b _ => ?_)
        try dsimp only
        cases hd : decide (delta a b = q) with
        | false =>
          have hf := of_decide_eq_false hd
          have hz_in : ∀ x ∈ range1To M1,
              sumList (range1To M1) (fun y =>
                if delta a b = q then (dp x a * P ^ x * Qn ^ (M1 - x)) * (dp y b * P ^ y * Qn ^ (M1 - y)) else 0) = 0 := by
            intro x _
            rw [sumList_congr (fun _ _ => if_neg hf), sumList_zero]
          rw [if_neg hf, sumList_congr hz_in, sumList_zero]
        | true =>
          have ht := of_decide_eq_true hd
          rw [if_pos ht]
          have hfact : ∀ x ∈ range1To M1,
              sumList (range1To M1) (fun y =>
                if delta a b = q then (dp x a * P ^ x * Qn ^ (M1 - x)) * (dp y b * P ^ y * Qn ^ (M1 - y)) else 0) =
              (dp x a * (P ^ x) * (Qn ^ (M1 - x))) * scaledGenSum dp P Qn M1 b := by
            intro x _
            rw [sumList_congr (fun _ _ => if_pos ht)]
            exact sumList_mul_left _ _ _
          rw [sumList_congr hfact, sumList_mul_right]
          rfl
      rw [hswap_eq]
      exact Nat.le_refl _

    have hd2 := Nat.mul_le_mul_left (D * D) hmul_M
    rw [Nat.mul_add, ← sumList_mul_left] at hd2
    have hquad_bound :
        sumList accQ (fun a => (D * D) * sumList accQ (fun b =>
          if delta a b = q then scaledGenSum dp P Qn M1 a * scaledGenSum dp P Qn M1 b else 0)) ≤
        sumList accQ (fun a => sumList accQ (fun b =>
          if delta a b = q then (W a * W b) * (Qn ^ (2 * M1)) else 0)) := by
      refine sumList_le_sumList (fun a ha => ?_)
      try dsimp only
      rw [← sumList_mul_left]
      refine sumList_le_sumList (fun b hb => ?_)
      try dsimp only
      cases hd : decide (delta a b = q) with
      | false =>
        simp only [if_neg (of_decide_eq_false hd), Nat.mul_zero]
        exact Nat.le_refl 0
      | true =>
        simp only [if_pos (of_decide_eq_true hd)]
        have iha := ih' a ha
        have ihb := ih' b hb
        have hprod := Nat.mul_le_mul iha ihb
        have hL : (D * scaledGenSum dp P Qn M1 a) * (D * scaledGenSum dp P Qn M1 b) =
            (D * D) * (scaledGenSum dp P Qn M1 a * scaledGenSum dp P Qn M1 b) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        have hR : (W a * (Qn ^ M1)) * (W b * (Qn ^ M1)) = (W a * W b) * (Qn ^ (2 * M1)) := by
          have he : M1 + M1 = 2 * M1 := by omega
          rw [show (W a * (Qn ^ M1)) * (W b * (Qn ^ M1)) = (W a * W b) * ((Qn ^ M1) * (Qn ^ M1)) by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]]
          rw [← Nat.pow_add, he]
        change (D * D) * (scaledGenSum dp P Qn M1 a * scaledGenSum dp P Qn M1 b) ≤
          (W a * W b) * (Qn ^ (2 * M1))
        rw [← hL, ← hR]
        exact hprod
    have hd2' := Nat.le_trans hd2 (Nat.add_le_add_left hquad_bound _)
    have hpow_split : Qn ^ (2 * M1) = Qn * (Qn ^ (2 * M1 - 1)) := by
      have he : 2 * M1 = (2 * M1 - 1) + 1 := by omega
      calc
        Qn ^ (2 * M1) = Qn ^ ((2 * M1 - 1) + 1) := congrArg (fun k => Qn ^ k) he
        _ = Qn * (Qn ^ (2 * M1 - 1)) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hquad_pull :
        sumList accQ (fun a => sumList accQ (fun b =>
          if delta a b = q then (W a * W b) * (Qn ^ (2 * M1)) else 0)) =
        (Qn * sumList accQ (fun a => sumList accQ (fun b => if delta a b = q then W a * W b else 0))) *
          (Qn ^ (2 * M1 - 1)) := by
      rw [← sumList_mul_left, ← sumList_mul_right]
      refine sumList_congr (fun a _ => ?_)
      try dsimp only
      rw [← sumList_mul_left, ← sumList_mul_right]
      refine sumList_congr (fun b _ => ?_)
      try dsimp only
      cases hd : decide (delta a b = q) with
      | false =>
        simp only [if_neg (of_decide_eq_false hd), Nat.mul_zero, Nat.zero_mul]
      | true =>
        simp only [if_pos (of_decide_eq_true hd), hpow_split]
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hdp1 : dp 1 q = (if q = q0 then 1 else 0) := rfl
    rw [hquad_pull, hdp1] at hd2'
    have hfirst_pull : (D * D) * ((if q = q0 then 1 else 0) * P * (Qn ^ (2 * M1 - 1))) =
        (D * D * (if q = q0 then 1 else 0) * P) * (Qn ^ (2 * M1 - 1)) := by
      simp only [Nat.mul_assoc]
    rw [hfirst_pull, ← Nat.add_mul] at hd2'
    have hcert := Nat.mul_le_mul_right (Qn ^ (2 * M1 - 1)) (hstep q hq)
    have hfinal := Nat.le_trans hd2' hcert
    have hL_eq : (D * (Qn ^ m0)) * (D * scaledGenSum dp P Qn (M1 + 1) q) =
        (D * D) * ((Qn ^ m0) * scaledGenSum dp P Qn (M1 + 1) q) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    have hR_eq : (D * (Qn ^ m0)) * (W q * (Qn ^ (M1 + 1))) =
        (D * W q * Qn) * (Qn ^ (2 * M1 - 1)) := by
      have hp_eq : (Qn ^ m0) * (Qn ^ (M1 + 1)) = Qn * (Qn ^ (2 * M1 - 1)) := by
        rw [← Nat.pow_add, ← Nat.pow_succ', show m0 + (M1 + 1) = (2 * M1 - 1) + 1 by omega]
      calc
        (D * (Qn ^ m0)) * (W q * (Qn ^ (M1 + 1)))
          = D * W q * ((Qn ^ m0) * (Qn ^ (M1 + 1))) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm]
        _ = D * W q * (Qn * (Qn ^ (2 * M1 - 1))) := by rw [hp_eq]
        _ = (D * W q * Qn) * (Qn ^ (2 * M1 - 1)) := by simp only [Nat.mul_assoc]
    rw [← hL_eq, ← hR_eq] at hfinal
    exact Nat.le_of_mul_le_mul_left hfinal (Nat.mul_pos hD (pow_pos_of_pos hQn m0))

/-! ### Explicit Integer Weight Certificates for `A_SN` (`sum = 88611`) and `A_P` (`sum = 88670`) -/

def weightSN : StateSN → Nat
  | .sn0 => 29600
  | .sn1 => 8762
  | .sn2 => 2594
  | .sn3 => 768
  | .sn4 => 250
  | .sn5 => 691
  | .sn6 => 12160
  | .sn7 => 2594
  | .sn8 => 768
  | .sn9 => 1536
  | .sn10 => 847
  | .sn11 => 250
  | .sn12 => 74
  | .sn13 => 74
  | .sn14 => 25
  | .sn15 => 1325
  | .sn16 => 74
  | .sn17 => 82
  | .sn18 => 8
  | .sn19 => 923
  | .sn20 => 274
  | .sn21 => 214
  | .sn22 => 228
  | .sn23 => 22
  | .sn24 => 623
  | .sn25 => 823
  | .sn26 => 392
  | .sn27 => 274
  | .sn28 => 74
  | .sn29 => 2015
  | .sn30 => 19072
  | .sn31 => 165
  | .sn32 => 274
  | .sn33 => 74
  | .sn34 => 114
  | .sn35 => 158
  | .sn36 => 302
  | .sn37 => 108
  | .sn38 => 0

def weightP : StateP → Nat
  | .p0 => 29600
  | .p1 => 8762
  | .p2 => 2594
  | .p3 => 2594
  | .p4 => 768
  | .p5 => 768
  | .p6 => 1536
  | .p7 => 923
  | .p8 => 250
  | .p9 => 691
  | .p10 => 847
  | .p11 => 274
  | .p12 => 250
  | .p13 => 1325
  | .p14 => 228
  | .p15 => 623
  | .p16 => 274
  | .p17 => 274
  | .p18 => 12179
  | .p19 => 74
  | .p20 => 214
  | .p21 => 74
  | .p22 => 74
  | .p23 => 392
  | .p24 => 1993
  | .p25 => 74
  | .p26 => 74
  | .p27 => 188
  | .p28 => 302
  | .p29 => 19110
  | .p30 => 25
  | .p31 => 82
  | .p32 => 22
  | .p33 => 824
  | .p34 => 114
  | .p35 => 108
  | .p36 => 158
  | .p37 => 0
  | .p38 => 8

private theorem cert_sn_base_chk :
    (accStatesSN.all (fun q => decide (100000 * (if q = .sn0 then 1 else 0) * 37 ≤ weightSN q * 125))) = true := rfl

private theorem cert_sn_step_chk :
    (accStatesSN.all (fun q => decide (
      100000 * 100000 * (if q = .sn0 then 1 else 0) * 37 +
        125 * sumList accStatesSN (fun a => sumList accStatesSN (fun b =>
          if deltaSN a b = q then weightSN a * weightSN b else 0)) ≤
      100000 * weightSN q * 125))) = true := rfl

private theorem cert_p_base_chk :
    (accStatesP.all (fun q => decide (100000 * (if q = .p0 then 1 else 0) * 37 ≤ weightP q * 125))) = true := rfl

private theorem cert_p_step_chk :
    (accStatesP.all (fun q => decide (
      100000 * 100000 * (if q = .p0 then 1 else 0) * 37 +
        125 * sumList accStatesP (fun a => sumList accStatesP (fun b =>
          if delta_StateP a b = q then weightP a * weightP b else 0)) ≤
      100000 * weightP q * 125))) = true := rfl

private theorem list_all_mem {α : Type} {p : α → Bool} {xs : List α} (h : xs.all p = true) :
    ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => intro _ hm; cases hm
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    intro x hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact h.1
    · exact ih h.2 x hm'

private theorem sum_weightSN_eq : sumList accStatesSN weightSN = 88611 := rfl
private theorem sum_weightP_eq  : sumList accStatesP  weightP  = 88670 := rfl

theorem countSN_universal_exp_upper (n : Nat) (hn : 1 ≤ n) :
    100000 * (37 ^ n) * countSN n ≤ 88611 * (125 ^ n) := by
  unfold countSN dpSN
  have hstate : ∀ q ∈ accStatesSN,
      100000 * (dpState allStatesSN deltaSN .sn0 n q * (37 ^ n)) ≤ weightSN q * (125 ^ n) := by
    intro q hq
    have h1 := Nat.mul_le_mul_left 100000 (last_le_scaledGenSum (dpState allStatesSN deltaSN .sn0) 37 125 n hn q)
    have h2 := dpState_exp_majorant allStatesSN accStatesSN deltaSN .sn0 .sn38
      sn38_two_sided_ideal
      (fun x hx => (of_decide_eq_true (checkAll1_StateSN_sound _ accStatesSN_iff_chk x)).mpr hx)
      (fun x hx => (of_decide_eq_true (checkAll1_StateSN_sound _ accStatesSN_iff_chk x)).mp hx)
      nodup_allStatesSN weightSN 37 125 100000 (by decide) (by decide)
      (fun x hx => of_decide_eq_true (list_all_mem cert_sn_base_chk x hx))
      (fun x hx => of_decide_eq_true (list_all_mem cert_sn_step_chk x hx))
      n hn q hq
    exact Nat.le_trans h1 h2
  have hsum := sumList_le_sumList hstate
  rw [sumList_mul_left, sumList_mul_right, sumList_mul_right, sum_weightSN_eq] at hsum
  calc
    100000 * (37 ^ n) * sumList accStatesSN (fun q => dpState allStatesSN deltaSN .sn0 n q)
      = 100000 * (sumList accStatesSN (fun q => dpState allStatesSN deltaSN .sn0 n q) * (37 ^ n)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm]
    _ ≤ 88611 * (125 ^ n) := hsum

theorem countAcceptP_universal_exp_upper (n : Nat) (hn : 1 ≤ n) :
    100000 * (37 ^ n) * countAcceptP n ≤ 88670 * (125 ^ n) := by
  unfold countAcceptP dpP
  have hstate : ∀ q ∈ accStatesP,
      100000 * (dpState allStatesP delta_StateP .p0 n q * (37 ^ n)) ≤ weightP q * (125 ^ n) := by
    intro q hq
    have h1 := Nat.mul_le_mul_left 100000 (last_le_scaledGenSum (dpState allStatesP delta_StateP .p0) 37 125 n hn q)
    have h2 := dpState_exp_majorant allStatesP accStatesP delta_StateP .p0 .p37
      p37_two_sided_ideal
      (fun x hx => (of_decide_eq_true (checkAll1_StateP_sound _ accStatesP_iff_chk x)).mpr hx)
      (fun x hx => (of_decide_eq_true (checkAll1_StateP_sound _ accStatesP_iff_chk x)).mp hx)
      nodup_allStatesP weightP 37 125 100000 (by decide) (by decide)
      (fun x hx => of_decide_eq_true (list_all_mem cert_p_base_chk x hx))
      (fun x hx => of_decide_eq_true (list_all_mem cert_p_step_chk x hx))
      n hn q hq
    exact Nat.le_trans h1 h2
  have hsum := sumList_le_sumList hstate
  rw [sumList_mul_left, sumList_mul_right, sumList_mul_right, sum_weightP_eq] at hsum
  calc
    100000 * (37 ^ n) * sumList accStatesP (fun q => dpState allStatesP delta_StateP .p0 n q)
      = 100000 * (sumList accStatesP (fun q => dpState allStatesP delta_StateP .p0 n q) * (37 ^ n)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm]
    _ ≤ 88670 * (125 ^ n) := hsum

private theorem mul_pow (a b n : Nat) : (a * b) ^ n = (a ^ n) * (b ^ n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [Nat.pow_succ, ih]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- **Main Universal Exponential Decay Theorem (`∀ n ≥ 1`)**:
    Both `#SN(n) / C_{n-1}` and `#AcceptP(n) / C_{n-1}` decay strictly exponentially to `0`
    at rate at most `(250 / 259)^n`! -/
theorem sn_and_acceptP_exponential_decay_to_zero (n : Nat) (hn : 1 ≤ n) :
    100000 * (259 ^ n) * countSN n ≤ 5139438 * (250 ^ n) * catalanTrees n ∧
    100000 * (259 ^ n) * countAcceptP n ≤ 5142860 * (250 ^ n) * catalanTrees n := by
  have hcat := catalanTrees_universal_exp_lower n hn
  have hsn  := countSN_universal_exp_upper n hn
  have hp   := countAcceptP_universal_exp_upper n hn
  have h259 : 259 ^ n = (7 ^ n) * (37 ^ n) := mul_pow 7 37 n
  have h250 : 250 ^ n = (2 ^ n) * (125 ^ n) := mul_pow 2 125 n
  constructor
  · have m1 := Nat.mul_le_mul_left (7 ^ n) hsn
    have m2 := Nat.mul_le_mul_left (88611 * (125 ^ n)) hcat
    rw [h259, h250]
    have eL : (7 ^ n) * (100000 * (37 ^ n) * countSN n) = 100000 * ((7 ^ n) * (37 ^ n)) * countSN n := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have eM : (7 ^ n) * (88611 * (125 ^ n)) = (88611 * (125 ^ n)) * (7 ^ n) := Nat.mul_comm _ _
    have eR : (88611 * (125 ^ n)) * (58 * (2 ^ n) * catalanTrees n) =
        5139438 * ((2 ^ n) * (125 ^ n)) * catalanTrees n := by
      have hc : 88611 * 58 = 5139438 := rfl
      calc
        (88611 * (125 ^ n)) * (58 * (2 ^ n) * catalanTrees n)
          = (88611 * 58) * ((2 ^ n) * (125 ^ n)) * catalanTrees n := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = 5139438 * ((2 ^ n) * (125 ^ n)) * catalanTrees n := by rw [hc]
    rw [← eL, ← eR]
    exact Nat.le_trans m1 (eM ▸ m2)
  · have m1 := Nat.mul_le_mul_left (7 ^ n) hp
    have m2 := Nat.mul_le_mul_left (88670 * (125 ^ n)) hcat
    rw [h259, h250]
    have eL : (7 ^ n) * (100000 * (37 ^ n) * countAcceptP n) = 100000 * ((7 ^ n) * (37 ^ n)) * countAcceptP n := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have eM : (7 ^ n) * (88670 * (125 ^ n)) = (88670 * (125 ^ n)) * (7 ^ n) := Nat.mul_comm _ _
    have eR : (88670 * (125 ^ n)) * (58 * (2 ^ n) * catalanTrees n) =
        5142860 * ((2 ^ n) * (125 ^ n)) * catalanTrees n := by
      have hc : 88670 * 58 = 5142860 := rfl
      calc
        (88670 * (125 ^ n)) * (58 * (2 ^ n) * catalanTrees n)
          = (88670 * 58) * ((2 ^ n) * (125 ^ n)) * catalanTrees n := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = 5142860 * ((2 ^ n) * (125 ^ n)) * catalanTrees n := by rw [hc]
    rw [← eL, ← eR]
    exact Nat.le_trans m1 (eM ▸ m2)

/-- Exact Catalan check through `n = 20` (`C_{19} = 1,767,263,190`). -/
theorem catalanTrees_exact_1_to_20 :
    catalanTrees 1 = 1 ∧ catalanTrees 2 = 1 ∧ catalanTrees 3 = 2 ∧ catalanTrees 4 = 5 ∧
    catalanTrees 5 = 14 ∧ catalanTrees 6 = 42 ∧ catalanTrees 7 = 132 ∧ catalanTrees 8 = 429 ∧
    catalanTrees 9 = 1430 ∧ catalanTrees 10 = 4862 ∧ catalanTrees 15 = 2674440 ∧
    catalanTrees 20 = 1767263190 := by
  rw [← fastCatalan_eq 1, ← fastCatalan_eq 2, ← fastCatalan_eq 3, ← fastCatalan_eq 4,
      ← fastCatalan_eq 5, ← fastCatalan_eq 6, ← fastCatalan_eq 7, ← fastCatalan_eq 8,
      ← fastCatalan_eq 9, ← fastCatalan_eq 10, ← fastCatalan_eq 15, ← fastCatalan_eq 20]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FormalAsymptotics

/-! ## 7. Complete `#print axioms` Verification on Every Landmark Theorem -/

#print axioms FormalAsymptotics.ofIntrinsic_toIntrinsic
#print axioms FormalAsymptotics.toIntrinsic_ofIntrinsic
#print axioms FormalAsymptotics.evalPTerm_reduces
#print axioms FormalAsymptotics.sn38_two_sided_ideal
#print axioms FormalAsymptotics.sn38_subterm_absorbing
#print axioms FormalAsymptotics.non_sn_subterm_contagion
#print axioms FormalAsymptotics.p37_two_sided_ideal
#print axioms FormalAsymptotics.p37_subterm_absorbing
#print axioms FormalAsymptotics.p37_subterm_absorbing_term
#print axioms FormalAsymptotics.hn34_left_ideal_not_right_ideal
#print axioms FormalAsymptotics.s_app_always_hasHNF
#print axioms FormalAsymptotics.s_app2_always_hasHNF
#print axioms FormalAsymptotics.evalSN_ne_sn38_implies_evalPTerm_ne_p37
#print axioms FormalAsymptotics.evalPTerm_ne_p37_implies_evalHN_ne_hn34
#print axioms FormalAsymptotics.catalanTrees_recurrence
#print axioms FormalAsymptotics.catalanTrees_eq_treesOfSize_length
#print axioms FormalAsymptotics.treesOfSize_sound
#print axioms FormalAsymptotics.treesOfSize_complete
#print axioms FormalAsymptotics.treesOfSize_nodup
#print axioms FormalAsymptotics.countSN_eq_filter_length
#print axioms FormalAsymptotics.countHN_eq_filter_length
#print axioms FormalAsymptotics.countNonHN_eq_filter_length
#print axioms FormalAsymptotics.countAcceptP_eq_filter_length
#print axioms FormalAsymptotics.countHN_add_countNonHN
#print axioms FormalAsymptotics.universal_count_hierarchy
#print axioms FormalAsymptotics.countHN_ge_catalan_pred
#print axioms FormalAsymptotics.countHN_ge_two_mul_catalan_pred
#print axioms FormalAsymptotics.countHN_ge_pred_add_pred2
#print axioms FormalAsymptotics.countNonHN_ge_catalan_sub8
#print axioms FormalAsymptotics.hn_universal_two_sided_density_bounds
#print axioms FormalAsymptotics.minimal_phase_onset_witnesses
#print axioms FormalAsymptotics.catalanTrees_universal_exp_lower
#print axioms FormalAsymptotics.countSN_universal_exp_upper
#print axioms FormalAsymptotics.countAcceptP_universal_exp_upper
#print axioms FormalAsymptotics.sn_and_acceptP_exponential_decay_to_zero
#print axioms FormalAsymptotics.catalanTrees_exact_1_to_20
