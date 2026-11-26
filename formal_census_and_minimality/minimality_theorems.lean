import formal_algebra.all_algebra_open_problems
import intrinsic_research.intrinsic_theorems

/-!
# Exact Pure-S Small-Term Census, Minimal Witness Optimality, and Confluence / Diamond Thresholds

Machine-checked in Lean 4.33.1 with zero `sorry`, zero `admit`, zero user-declared `axiom`,
zero `native_decide`, and zero `Classical.choice` (`#print axioms` uses at most `[propext]`).

## Main Contributions (`namespace FormalMinimality`)
1. **Universal 4-Tier Hierarchy over All Closed Pure-`S` Terms (`CL(S)`)**:
   - `sn_implies_productive`: `noVars t = true → StrongNormalizing t → evalP t ≠ .p37`
   - `productive_implies_hasHNF`: `noVars t = true → evalP t ≠ .p37 → HasHNF t`
   establishing `StrongNormalizing t ⟹ evalP t ≠ .p37 ⟹ HasHNF t` across all leaf sizes.
2. **Total Constructive Catalan Tree Enumeration (`treesOfLeaves : Nat → List Term`)**:
   - Soundness, completeness (`∀ t, noVars t = true → leaves t = n → t ∈ treesOfLeaves n`),
     `NoDupList (treesOfLeaves n)`, and cumulative enumeration `treesUpToLeaves`.
3. **Exact Sharpness & Minimal Witness Theorems**:
   - **Sizes `≤ 3` & Size `4`:** Every closed pure-`S` term with `leaves t ≤ 3` is in Normal Form;
     at `leaves t = 4`, `¬ IsNormalForm t ↔ t = S ⋅ S ⋅ S ⋅ S`.
   - **Theorem A (`leaves ≤ 6`, all `65` terms):** Every closed pure-`S` term with `leaves t ≤ 6`
     satisfies `StrongNormalizing t ∧ HasNormalForm t ∧ HasHNF t ∧ evalP t ≠ .p37`.
   - **Theorem B (`leaves = 7`, all `132` terms — Minimal Non-`SN` Threshold):**
     Every closed pure-`S` term of size `7` has `HasHNF t`, and `¬ StrongNormalizing t` holds **iff**
     `t = S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S` or `t = S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S` (which steps in 1 step to the first).
   - **Theorem C (`leaves = 8`, all `429` terms — Minimal Non-`HN` Threshold & `Productive ↔ SN` up to Size `8`):**
     No closed pure-`S` term of size `≤ 7` has `¬ HasHNF t`; at size `8`, `¬ HasHNF t` holds **iff**
     `t ∈ minimalNonHN8` (exact 15 witnesses). Moreover, **zero** closed pure-`S` terms of size `≤ 8`
     (`626` terms, including 8-leaf `Wolfram2 = S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)`, which has `evalP = .p37`)
     satisfy `¬ StrongNormalizing t ∧ evalP t ≠ .p37`, so `evalP t ≠ .p37 ↔ StrongNormalizing t` for all `leaves t ≤ 8`.
   - **Theorem D (`leaves = 9`, all `1,430` terms — Unique Minimal Productive Non-Halting Combinator):**
     `9` leaves is the global minimum leaf size of a productive non-`SN` pure-`S` combinator, and at size `9`
     `¬ StrongNormalizing t ∧ evalP t ≠ .p37` holds **iff** `t = S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)`
     (unique among all `2,056` closed pure-`S` terms of size `≤ 9`, reducing in 1 root step to Zachos's 10-leaf term).
   - **Theorem E (`leaves = 9` RNF-without-HNF & Minimal Non-Convertible `⊥`-Pairs):**
     No closed pure-`S` term of size `≤ 8` satisfies `IsRootNormalForm t ∧ ¬ HasHNF t`; at size `9`,
     `IsRootNormalForm t ∧ ¬ HasHNF t ↔ ∃ u ∈ minimalNonHN8, t = u ⋅ S` (15 witnesses), yielding 8-vs-9 and 9-vs-9
     non-convertible head-divergent pairs via `State36`.
   - **Theorem F (Confluence, Deterministic Reduction for `leaves ≤ 6`, & Minimal Diamond Thresholds at `leaves = 7`):**
     Every closed pure-`S` term with `leaves t ≤ 6` has at most one 1-step reduct (`Step t b → Step t c → b = c`);
     at `leaves t = 7`, multiway forks occur **iff** `t ∈ [SSS(SSSS), SS(SSSS)S, S(SSSS)SS]`, and the strict 1-step
     `Step` diamond fails **uniquely** at `t = S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S)` (`1` of `197` terms of size `≤ 7`),
     while Takahashi's `ParStep` satisfies the universal 1-step diamond (`parStep_diamond`) and full `church_rosser`.
-/

namespace FormalMinimality

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

open FormalAlgebra
open IntrinsicTheorems (StateP delta_StateP delta_StateP_s_law isAccP deltaP_sink
  deltaP_hnf1_iff deltaP_hnf2_iff checkAll1_StateP checkAll1_StateP_sound
  State36 delta_State36 delta_State36_s_law)

abbrev Term := FormalAlgebra.Term
abbrev S : Term := FormalAlgebra.S
abbrev Step := FormalAlgebra.Step
abbrev Reduces := FormalAlgebra.Reduces
abbrev leaves := FormalAlgebra.leaves
local infixl:70 (priority := high) " ⋅ " => FormalAlgebra.Term.app

/-! ## 0. Constructive List & Boolean Helpers (Zero `Classical.choice`) -/

def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

theorem listAll_sound {α : Type} {p : α → Bool} {xs : List α}
    (h : listAll p xs = true) {x : α} (hx : x ∈ xs) : p x = true := by
  induction hx with
  | head _ => exact FormalAlgebra.and_left h
  | tail _ _ ih => exact ih (FormalAlgebra.and_right h)

theorem listAll_iff {α : Type} (p : α → Bool) (xs : List α) :
    listAll p xs = true ↔ ∀ x, x ∈ xs → p x = true := by
  induction xs with
  | nil =>
    exact ⟨(fun _ _ hm => by cases hm), fun _ => rfl⟩
  | cons x xs ih =>
    constructor
    · intro h y hy
      exact listAll_sound h hy
    · intro hall
      simp only [listAll, hall x (.head xs), ih.mpr (fun y hy => hall y (.tail x hy)), Bool.and_self]

def listAny {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || listAny p xs

theorem listAny_iff {α : Type} (p : α → Bool) (xs : List α) :
    listAny p xs = true ↔ ∃ x, x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
    exact ⟨(fun h => by cases h), (fun ⟨_, hm, _⟩ => by cases hm)⟩
  | cons x xs ih =>
    constructor
    · intro h
      cases hp : p x with
      | true => exact ⟨x, .head xs, hp⟩
      | false =>
        rw [listAny, hp, Bool.false_or] at h
        obtain ⟨y, hy, hpy⟩ := ih.mp h
        exact ⟨y, .tail x hy, hpy⟩
    · intro ⟨y, hy, hpy⟩
      cases hy with
      | head _ =>
        simp only [listAny, hpy, Bool.true_or]
      | tail _ htail =>
        simp only [listAny, ih.mpr ⟨y, htail, hpy⟩, Bool.or_true]

def listMemDec {α : Type} [DecidableEq α] (a : α) : List α → Bool
  | [] => false
  | x :: xs => decide (a = x) || listMemDec a xs

theorem listMemDec_iff {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    listMemDec a xs = true ↔ a ∈ xs := by
  induction xs with
  | nil =>
    exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | cons x xs ih =>
    constructor
    · intro h
      cases hd : decide (a = x) with
      | true =>
        have heq := of_decide_eq_true hd
        subst heq
        exact .head xs
      | false =>
        rw [listMemDec, hd, Bool.false_or] at h
        exact .tail x (ih.mp h)
    · intro hm
      cases hm with
      | head _ =>
        rw [listMemDec, decide_eq_true (rfl : a = a), Bool.true_or]
      | tail _ htail =>
        rw [listMemDec, ih.mpr htail, Bool.or_true]

def filterList {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: filterList p xs else filterList p xs

theorem mem_filterList_iff {α : Type} (p : α → Bool) (xs : List α) (a : α) :
    a ∈ filterList p xs ↔ a ∈ xs ∧ p a = true := by
  induction xs with
  | nil =>
    exact ⟨(fun h => by cases h), (fun ⟨h, _⟩ => by cases h)⟩
  | cons x xs ih =>
    simp only [filterList]
    cases hp : p x with
    | true =>
      rw [if_pos rfl]
      constructor
      · intro hm
        cases hm with
        | head _ => exact ⟨.head xs, hp⟩
        | tail _ ht =>
          have ⟨h1, h2⟩ := ih.mp ht
          exact ⟨.tail x h1, h2⟩
      · intro ⟨hm, ha⟩
        cases hm with
        | head _ => exact .head _
        | tail _ ht => exact .tail x (ih.mpr ⟨ht, ha⟩)
    | false =>
      have hnot : ¬ (false = true) := fun h => by cases h
      rw [if_neg hnot]
      constructor
      · intro hm
        have ⟨h1, h2⟩ := ih.mp hm
        exact ⟨.tail x h1, h2⟩
      · intro ⟨hm, ha⟩
        cases hm with
        | head _ =>
          rw [hp] at ha
          cases ha
        | tail _ ht => exact ih.mpr ⟨ht, ha⟩

theorem mem_witnesses_iff_of_filter_eq {α : Type} {p : α → Bool} {univ wits : List α}
    (hfilt : filterList p univ = wits) {x : α} (hx : x ∈ univ) :
    p x = true ↔ x ∈ wits := by
  rw [← hfilt, mem_filterList_iff]
  exact ⟨fun hp => ⟨hx, hp⟩, fun ⟨_, hp⟩ => hp⟩

def NoDupList {α : Type} : List α → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ NoDupList xs

def noDupDec {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !listMemDec x xs && noDupDec xs

theorem noDupDec_sound {α : Type} [DecidableEq α] {xs : List α}
    (h : noDupDec xs = true) : NoDupList xs := by
  induction xs with
  | nil => exact trivial
  | cons x xs ih =>
    have h1 := FormalAlgebra.and_left h
    have h2 := FormalAlgebra.and_right h
    refine ⟨fun hm => ?_, ih h2⟩
    rw [(listMemDec_iff x xs).mpr hm] at h1
    cases h1

private theorem mem_singleton_iff {α : Type} (a x : α) :
    a ∈ [x] ↔ a = x := by
  constructor
  · intro hm
    cases hm with
    | head _ => rfl
    | tail _ ht => cases ht
  · intro heq
    subst heq
    exact .head []

private theorem mem_pair_iff {α : Type} (a x y : α) :
    a ∈ [x, y] ↔ a = x ∨ a = y := by
  constructor
  · intro hm
    cases hm with
    | head _ => exact Or.inl rfl
    | tail _ ht => exact Or.inr ((mem_singleton_iff a y).mp ht)
  · intro h
    rcases h with rfl | rfl
    · exact .head _
    · exact .tail _ (.head [])

private theorem mem_triple_iff {α : Type} (a x y z : α) :
    a ∈ [x, y, z] ↔ a = x ∨ a = y ∨ a = z := by
  constructor
  · intro hm
    cases hm with
    | head _ => exact Or.inl rfl
    | tail _ ht => exact Or.inr ((mem_pair_iff a y z).mp ht)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head []))

/-! ## 1. Productivity & Question-31 S-Algebras (`evalP`, `eval36`) on `FormalAlgebra.Term`
    and the Universal 4-Tier Hierarchy (`StrongNormalizing ⟹ Productive ⟹ HasHNF`) -/

def toIntrinsicTerm : Term → IntrinsicTheorems.Term
  | .s => .s
  | .var k => .var k
  | .app a b => .app (toIntrinsicTerm a) (toIntrinsicTerm b)

def evalP : Term → StateP
  | .s => .p0
  | .var _ => .p0
  | .app a b => delta_StateP (evalP a) (evalP b)

def eval36 : Term → State36
  | .s => .q0
  | .var _ => .q0
  | .app a b => delta_State36 (eval36 a) (eval36 b)

theorem evalP_eq_intrinsic (t : Term) :
    evalP t = IntrinsicTheorems.evalP (toIntrinsicTerm t) := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [evalP, toIntrinsicTerm, IntrinsicTheorems.evalP, iha, ihb]

theorem eval36_eq_intrinsic (t : Term) :
    eval36 t = IntrinsicTheorems.eval36 (toIntrinsicTerm t) := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [eval36, toIntrinsicTerm, IntrinsicTheorems.eval36, iha, ihb]

theorem evalP_step {a b : Term} (h : Step a b) : evalP a = evalP b := by
  induction h with
  | root x y z => exact delta_StateP_s_law (evalP x) (evalP y) (evalP z)
  | left _ ih => simp only [evalP, ih]
  | right _ ih => simp only [evalP, ih]

theorem evalP_reduces {a b : Term} (h : Reduces a b) : evalP a = evalP b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalP_step hs).trans ih

theorem evalP_conv {a b : Term} (h : ConvS a b) : evalP a = evalP b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalP_step hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem eval36_step {a b : Term} (h : Step a b) : eval36 a = eval36 b := by
  induction h with
  | root x y z => exact delta_State36_s_law (eval36 x) (eval36 y) (eval36 z)
  | left _ ih => simp only [eval36, ih]
  | right _ ih => simp only [eval36, ih]

theorem eval36_reduces {a b : Term} (h : Reduces a b) : eval36 a = eval36 b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (eval36_step hs).trans ih

theorem eval36_conv {a b : Term} (h : ConvS a b) : eval36 a = eval36 b := by
  induction h with
  | refl _ => rfl
  | step hs => exact eval36_step hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem not_sn_iff_evalSN_eq_sn38 {t : Term} (hv : noVars t = true) :
    ¬ StrongNormalizing t ↔ evalSN t = .sn38 := by
  constructor
  · intro hnsn
    exact if h38 : evalSN t = .sn38 then h38
    else False.elim (hnsn ((waldmann_theorem_9 hv).1.mpr h38))
  · intro h38 hsn
    exact ((waldmann_theorem_9 hv).1.mp hsn) h38

theorem not_hasHNF_iff_evalHN_eq_hn34 {t : Term} (hv : noVars t = true) :
    ¬ HasHNF t ↔ evalHN t = .hn34 := by
  constructor
  · intro hnhn
    exact if h34 : evalHN t = .hn34 then h34
    else False.elim (hnhn ((barendregt_open_problem_10 hv).1.mpr h34))
  · intro h34 hhn
    exact ((barendregt_open_problem_10 hv).1.mp hhn) h34

private theorem isAccP_iff_ne_p37 (x : StateP) : isAccP x = true ↔ x ≠ .p37 := by
  cases x <;> decide

theorem closed_nf_evalP_ne_p37 {t : Term} (hv : noVars t = true) (hnf : IsNormalForm t) :
    evalP t ≠ .p37 := by
  suffices hacc : isAccP (evalP t) = true from (isAccP_iff_ne_p37 (evalP t)).mp hacc
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    have hnone : headStepOpt (a ⋅ b) = none := by
      cases hh : headStepOpt (a ⋅ b) with
      | none => rfl
      | some w => exfalso; exact hnf w (headStep_to_step (headStepOpt_some hh))
    have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hv).1
    have hvb : noVars b = true := ((Bool.and_eq_true _ _).mp hv).2
    have hnfa : IsNormalForm a := fun a' hs => hnf (a' ⋅ b) (FormalAlgebra.Step.left hs)
    have hnfb : IsNormalForm b := fun b' hs => hnf (a ⋅ b') (FormalAlgebra.Step.right hs)
    rcases headStepOpt_none_closed hv hnone with heq | ⟨x, heq⟩ | ⟨x, y, heq⟩
    · cases heq
    · injection heq with ha _
      rw [ha]
      change isAccP (delta_StateP .p0 (evalP b)) = true
      rw [deltaP_hnf1_iff]
      exact ihb hvb hnfb
    · injection heq with ha _
      have hacc_a : isAccP (evalP a) = true := iha hva hnfa
      rw [ha] at hacc_a
      change isAccP (delta_StateP .p0 (evalP x)) = true at hacc_a
      rw [deltaP_hnf1_iff] at hacc_a
      rw [ha]
      change isAccP (delta_StateP (delta_StateP .p0 (evalP x)) (evalP b)) = true
      rw [deltaP_hnf2_iff, hacc_a, ihb hvb hnfb]
      rfl

/-- **Universal Hierarchy Law 1 (`SN ⟹ Productive`)**:
    Every strongly normalizing closed pure-`S` term `t` (of any size) has `evalP t ≠ .p37`. -/
theorem sn_implies_productive {t : Term} (hv : noVars t = true) (hsn : StrongNormalizing t) :
    evalP t ≠ .p37 := by
  obtain ⟨nf, hred, hnf⟩ := sn_implies_wn hsn
  rw [evalP_reduces hred]
  exact closed_nf_evalP_ne_p37 (noVars_reduces hred hv) hnf

theorem evalSN_ne_sn38_implies_evalP_ne_p37 {t : Term} (hv : noVars t = true) (hsn : evalSN t ≠ .sn38) :
    evalP t ≠ .p37 :=
  sn_implies_productive hv ((waldmann_theorem_9 hv).1.mpr hsn)

/-- Exact 113-pair reachable relation in `StateHN × StateP` proving `evalHN t = .hn34 → evalP t = .p37`. -/
def hnRowStates : StateHN → List StateP
  | .hn0 => [.p0]
  | .hn1 => [.p1]
  | .hn2 => [.p2]
  | .hn3 => [.p4]
  | .hn4 => [.p8]
  | .hn5 => [.p9, .p18]
  | .hn6 => [.p3]
  | .hn7 => [.p5]
  | .hn8 => [.p9, .p15, .p18, .p27, .p37]
  | .hn9 => [.p18, .p33, .p37]
  | .hn10 => [.p18, .p24, .p27, .p29, .p33, .p37]
  | .hn11 => [.p6]
  | .hn12 => [.p8, .p9, .p10, .p11, .p18, .p19, .p20, .p37]
  | .hn13 => [.p7, .p9, .p12, .p13, .p15, .p16, .p17, .p18, .p20, .p21, .p22, .p23, .p24, .p25, .p26, .p27, .p28, .p29, .p30, .p31, .p32, .p33, .p34, .p35, .p36, .p37, .p38]
  | .hn14 => [.p7]
  | .hn15 => [.p11]
  | .hn16 => [.p14]
  | .hn17 => [.p23, .p24, .p27, .p29, .p33, .p37]
  | .hn18 => [.p16]
  | .hn19 => [.p18]
  | .hn20 => [.p24, .p25, .p27, .p29, .p37]
  | .hn21 => [.p18, .p37]
  | .hn22 => [.p24, .p29, .p37]
  | .hn23 => [.p29, .p37]
  | .hn24 => [.p24, .p29, .p37]
  | .hn25 => [.p24, .p29, .p37]
  | .hn26 => [.p17]
  | .hn27 => [.p18, .p20, .p37]
  | .hn28 => [.p26]
  | .hn29 => [.p24, .p27, .p29, .p35, .p36, .p37]
  | .hn30 => [.p24, .p29, .p34, .p37]
  | .hn31 => [.p24, .p27, .p28, .p29, .p35, .p37]
  | .hn32 => [.p29]
  | .hn33 => [.p29, .p37]
  | .hn34 => [.p37]

def inHNRow (h : StateHN) (p : StateP) : Bool :=
  listMemDec p (hnRowStates h)

private def checkHNPairRow (h1 : StateHN) : Bool :=
  checkAll1_StateHN fun h2 =>
    listAll (fun q1 =>
      listAll (fun q2 => inHNRow (deltaHN h1 h2) (delta_StateP q1 q2)) (hnRowStates h2))
      (hnRowStates h1)

private theorem hn_p_closed_all : checkAll1_StateHN checkHNPairRow = true := rfl

private theorem inHNRow_closed {h1 h2 : StateHN} {q1 q2 : StateP}
    (hp1 : inHNRow h1 q1 = true) (hp2 : inHNRow h2 q2 = true) :
    inHNRow (deltaHN h1 h2) (delta_StateP q1 q2) = true := by
  have hr1 := checkAll1_StateHN_sound _ hn_p_closed_all h1
  have hr2 := checkAll1_StateHN_sound _ hr1 h2
  have hm1 := (listMemDec_iff q1 (hnRowStates h1)).mp hp1
  have hm2 := (listMemDec_iff q2 (hnRowStates h2)).mp hp2
  exact listAll_sound (listAll_sound hr2 hm1) hm2

theorem eval_inHNRow {t : Term} (hv : noVars t = true) :
    inHNRow (evalHN t) (evalP t) = true := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    have hvb := ((Bool.and_eq_true _ _).mp hv).2
    exact inHNRow_closed (iha hva) (ihb hvb)

theorem evalHN_eq_hn34_implies_evalP_eq_p37 {t : Term} (hv : noVars t = true)
    (hhn : evalHN t = .hn34) : evalP t = .p37 := by
  have h := eval_inHNRow hv
  rw [hhn] at h
  have hm := (listMemDec_iff (evalP t) [.p37]).mp h
  exact (mem_singleton_iff (evalP t) .p37).mp hm

/-- **Universal Hierarchy Law 2 (`Productive ⟹ HasHNF`)**:
    Every productive closed pure-`S` term `t` (`evalP t ≠ .p37`) has a Head Normal Form (`HasHNF t`). -/
theorem productive_implies_hasHNF {t : Term} (hv : noVars t = true) (hp : evalP t ≠ .p37) :
    HasHNF t := by
  apply (barendregt_open_problem_10 hv).1.mpr
  intro h34
  exact hp (evalHN_eq_hn34_implies_evalP_eq_p37 hv h34)

/-! ## 2. Total Constructive Catalan Tree Enumeration (`treesOfLeaves : Nat → List Term`)
    with Soundness, Completeness, and `NoDupList` -/

def splits : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | k + 1, i => (i, k + 1) :: splits k (i + 1)

theorem mem_splits_iff (k i a b : Nat) :
    (a, b) ∈ splits k i ↔ i ≤ a ∧ 1 ≤ b ∧ a + b = i + k := by
  induction k generalizing i with
  | zero =>
    constructor
    · intro h; cases h
    · intro ⟨hia, hb1, heq⟩
      have hbad : i + 1 ≤ i := by
        have h1 : i + 1 ≤ a + b := Nat.add_le_add hia hb1
        rw [heq, Nat.add_zero] at h1
        exact h1
      exact False.elim (Nat.not_succ_le_self i hbad)
  | succ k ih =>
    constructor
    · intro hm
      cases hm with
      | head _ =>
        exact ⟨Nat.le_refl a, Nat.succ_le_succ (Nat.zero_le k), rfl⟩
      | tail _ htail =>
        obtain ⟨hia1, hb1, heq⟩ := (ih (i + 1)).mp htail
        refine ⟨Nat.le_of_succ_le hia1, hb1, ?_⟩
        rw [heq, Nat.add_assoc i 1 k, Nat.add_comm 1 k]
    · intro ⟨hia, hb1, heq⟩
      exact if haeq : a = i then by
        subst haeq
        have hbeq : b = k + 1 := Nat.add_left_cancel heq
        subst hbeq
        exact .head _
      else by
        have hia1 : i + 1 ≤ a := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hia (Ne.symm haeq))
        have heq1 : a + b = (i + 1) + k := by
          rw [heq, Nat.add_assoc i 1 k, Nat.add_comm 1 k]
        exact .tail _ ((ih (i + 1)).mpr ⟨hia1, hb1, heq1⟩)

def consApps (l : Term) : List Term → List Term → List Term
  | [], acc => acc
  | r :: rs, acc => (l ⋅ r) :: consApps l rs acc

theorem mem_consApps_iff (l : Term) (ys acc : List Term) (t : Term) :
    t ∈ consApps l ys acc ↔ (∃ r, r ∈ ys ∧ t = l ⋅ r) ∨ t ∈ acc := by
  induction ys with
  | nil =>
    exact ⟨fun h => Or.inr h, (fun h => match h with | Or.inl ⟨_, hm, _⟩ => by cases hm | Or.inr h => h)⟩
  | cons r rs ih =>
    constructor
    · intro hm
      cases hm with
      | head _ => exact Or.inl ⟨r, .head rs, rfl⟩
      | tail _ ht =>
        rcases ih.mp ht with ⟨r', hr', heq⟩ | hacc
        · exact Or.inl ⟨r', .tail r hr', heq⟩
        · exact Or.inr hacc
    · intro h
      rcases h with ⟨r', hr', heq⟩ | hacc
      · cases hr' with
        | head _ => subst heq; exact .head _
        | tail _ hrt => exact .tail _ (ih.mpr (Or.inl ⟨r', hrt, heq⟩))
      · exact .tail _ (ih.mpr (Or.inr hacc))

def appCartAcc : List Term → List Term → List Term → List Term
  | [], _, acc => acc
  | l :: ls, ys, acc => consApps l ys (appCartAcc ls ys acc)

theorem mem_appCartAcc_iff (xs ys acc : List Term) (t : Term) :
    t ∈ appCartAcc xs ys acc ↔ (∃ l, l ∈ xs ∧ ∃ r, r ∈ ys ∧ t = l ⋅ r) ∨ t ∈ acc := by
  induction xs with
  | nil =>
    exact ⟨fun h => Or.inr h, (fun h => match h with | Or.inl ⟨_, hm, _⟩ => by cases hm | Or.inr h => h)⟩
  | cons l ls ih =>
    simp only [appCartAcc, mem_consApps_iff, ih]
    constructor
    · intro h
      rcases h with ⟨r, hr, heq⟩ | (⟨l', hl', r, hr, heq⟩ | hacc)
      · exact Or.inl ⟨l, .head ls, r, hr, heq⟩
      · exact Or.inl ⟨l', .tail l hl', r, hr, heq⟩
      · exact Or.inr hacc
    · intro h
      rcases h with ⟨l', hl', r, hr, heq⟩ | hacc
      · cases hl' with
        | head _ => exact Or.inl ⟨r, hr, heq⟩
        | tail _ hlt => exact Or.inr (Or.inl ⟨l', hlt, r, hr, heq⟩)
      · exact Or.inr (Or.inr hacc)

def lookupLevel : List (List Term) → Nat → List Term
  | [], _ => []
  | x :: _, 0 => x
  | _ :: xs, k + 1 => lookupLevel xs k

def nextLevelAux (table : List (List Term)) : List (Nat × Nat) → List Term
  | [] => []
  | p :: ps => appCartAcc (lookupLevel table p.1) (lookupLevel table p.2) (nextLevelAux table ps)

theorem mem_nextLevelAux_iff (table : List (List Term)) (ps : List (Nat × Nat)) (t : Term) :
    t ∈ nextLevelAux table ps ↔
      ∃ p, p ∈ ps ∧ ∃ l, l ∈ lookupLevel table p.1 ∧ ∃ r, r ∈ lookupLevel table p.2 ∧ t = l ⋅ r := by
  induction ps with
  | nil =>
    exact ⟨(fun h => by cases h), (fun ⟨_, hm, _⟩ => by cases hm)⟩
  | cons p ps ih =>
    simp only [nextLevelAux, mem_appCartAcc_iff, ih]
    constructor
    · intro h
      rcases h with ⟨l, hl, r, hr, heq⟩ | ⟨p', hp', l, hl, r, hr, heq⟩
      · exact ⟨p, .head ps, l, hl, r, hr, heq⟩
      · exact ⟨p', .tail p hp', l, hl, r, hr, heq⟩
    · intro ⟨p', hp', l, hl, r, hr, heq⟩
      cases hp' with
      | head _ => exact Or.inl ⟨l, hl, r, hr, heq⟩
      | tail _ hpt => exact Or.inr ⟨p', hpt, l, hl, r, hr, heq⟩

def nextLevel (table : List (List Term)) (m : Nat) : List Term :=
  nextLevelAux table (splits (m + 1) 1)

def extendTable (prev : List (List Term)) (m : Nat) : List (List Term) :=
  prev ++ [nextLevel prev m]

def treesTable : Nat → List (List Term)
  | 0 => [[]]
  | 1 => [[], [S]]
  | m + 2 => extendTable (treesTable (m + 1)) m

/-- Total bottom-up Catalan enumeration of all closed pure-`S` binary trees with exactly `n` leaves. -/
def treesOfLeaves (n : Nat) : List Term :=
  lookupLevel (treesTable n) n

private theorem treesTable_length (n : Nat) : (treesTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m =>
      simp only [treesTable, extendTable, List.length_append, List.length, ih]

private theorem lookupLevel_append_left {xs : List (List Term)} (ys : List (List Term))
    {k : Nat} (hk : k < xs.length) :
    lookupLevel (xs ++ ys) k = lookupLevel xs k := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x xs' ih =>
    cases k with
    | zero => rfl
    | succ k' => exact ih (Nat.lt_of_succ_lt_succ hk)

private theorem lookupLevel_append_end (xs : List (List Term)) (y : List Term) :
    lookupLevel (xs ++ [y]) xs.length = y := by
  induction xs with
  | nil => rfl
  | cons _ xs' ih => exact ih

private theorem lookupLevel_treesTable_le {n k : Nat} (hk : k ≤ n) :
    lookupLevel (treesTable n) k = treesOfLeaves k := by
  induction n with
  | zero =>
    cases Nat.eq_zero_of_le_zero hk
    rfl
  | succ n0 ih =>
    cases n0 with
    | zero =>
      cases k with
      | zero => rfl
      | succ k0 =>
        cases k0 with
        | zero => rfl
        | succ k1 =>
          exfalso
          exact Nat.not_succ_le_zero k1 (Nat.le_of_succ_le_succ hk)
    | succ m =>
      exact if heq : k = m + 2 then by
        subst heq
        rfl
      else by
        have hle : k ≤ m + 1 := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hk heq)
        have hlt : k < (treesTable (m + 1)).length := by
          rw [treesTable_length]
          exact Nat.lt_succ_of_le hle
        change lookupLevel (treesTable (m + 1) ++ [nextLevel (treesTable (m + 1)) m]) k = treesOfLeaves k
        rw [lookupLevel_append_left _ hlt]
        exact ih hle

private theorem treesOfLeaves_succ_succ (m : Nat) :
    treesOfLeaves (m + 2) = nextLevel (treesTable (m + 1)) m := by
  change lookupLevel (treesTable (m + 1) ++ [nextLevel (treesTable (m + 1)) m]) (m + 2) = _
  have hlen : (treesTable (m + 1)).length = m + 2 := treesTable_length (m + 1)
  rw [← hlen]
  exact lookupLevel_append_end _ _

theorem mem_treesOfLeaves_succ_succ_iff (m : Nat) (t : Term) :
    t ∈ treesOfLeaves (m + 2) ↔
      ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ a + b = m + 2 ∧
        ∃ l, l ∈ treesOfLeaves a ∧ ∃ r, r ∈ treesOfLeaves b ∧ t = l ⋅ r := by
  rw [treesOfLeaves_succ_succ, nextLevel, mem_nextLevelAux_iff]
  constructor
  · intro ⟨⟨a, b⟩, hp, l, hl, r, hr, heq⟩
    have ⟨ha1, hb1, hab⟩ := (mem_splits_iff (m + 1) 1 a b).mp hp
    have hab' : a + b = m + 2 := by
      rw [hab, Nat.add_comm 1 (m + 1)]
    have ha_le : a ≤ m + 1 := by
      have : a + 1 ≤ m + 2 := hab' ▸ Nat.add_le_add_left hb1 a
      exact Nat.le_of_succ_le_succ this
    have hb_le : b ≤ m + 1 := by
      have : 1 + b ≤ 1 + (m + 1) := hab ▸ Nat.add_le_add_right ha1 b
      exact Nat.le_of_add_le_add_left this
    rw [lookupLevel_treesTable_le ha_le] at hl
    rw [lookupLevel_treesTable_le hb_le] at hr
    exact ⟨a, b, ha1, hb1, hab', l, hl, r, hr, heq⟩
  · intro ⟨a, b, ha1, hb1, hab', l, hl, r, hr, heq⟩
    have hab : a + b = 1 + (m + 1) := by
      rw [Nat.add_comm 1 (m + 1)]
      exact hab'
    have ha_le : a ≤ m + 1 := by
      have : a + 1 ≤ m + 2 := hab' ▸ Nat.add_le_add_left hb1 a
      exact Nat.le_of_succ_le_succ this
    have hb_le : b ≤ m + 1 := by
      have : 1 + b ≤ 1 + (m + 1) := hab ▸ Nat.add_le_add_right ha1 b
      exact Nat.le_of_add_le_add_left this
    refine ⟨(a, b), (mem_splits_iff (m + 1) 1 a b).mpr ⟨ha1, hb1, hab⟩, l, ?_, r, ?_, heq⟩
    · rw [lookupLevel_treesTable_le ha_le]; exact hl
    · rw [lookupLevel_treesTable_le hb_le]; exact hr

private theorem treesOfLeaves_sound_aux :
    ∀ (B n : Nat), n ≤ B → ∀ {t : Term}, t ∈ treesOfLeaves n → noVars t = true ∧ leaves t = n := by
  intro B
  induction B with
  | zero =>
    intro n hn t ht
    cases Nat.eq_zero_of_le_zero hn
    cases ht
  | succ B ih =>
    intro n hn t ht
    cases n with
    | zero => cases ht
    | succ n0 =>
      cases n0 with
      | zero =>
        cases ht with
        | head _ => exact ⟨rfl, rfl⟩
        | tail _ h2 => cases h2
      | succ m =>
        obtain ⟨a, b, ha1, hb1, hab, l, hl, r, hr, rfl⟩ := (mem_treesOfLeaves_succ_succ_iff m t).mp ht
        have haB : a ≤ B := by
          have : a + 1 ≤ m + 2 := hab ▸ Nat.add_le_add_left hb1 a
          exact Nat.le_trans (Nat.le_of_succ_le_succ this) (Nat.le_of_succ_le_succ hn)
        have hbB : b ≤ B := by
          have : 1 + b ≤ m + 2 := hab ▸ Nat.add_le_add_right ha1 b
          rw [Nat.add_comm 1 b] at this
          exact Nat.le_trans (Nat.le_of_succ_le_succ this) (Nat.le_of_succ_le_succ hn)
        have ⟨hvl, hll⟩ := ih a haB hl
        have ⟨hvr, hlr⟩ := ih b hbB hr
        refine ⟨(Bool.and_eq_true _ _).mpr ⟨hvl, hvr⟩, ?_⟩
        change leaves l + leaves r = m + 2
        rw [hll, hlr, hab]

theorem treesOfLeaves_sound {n : Nat} {t : Term} (ht : t ∈ treesOfLeaves n) :
    noVars t = true ∧ leaves t = n :=
  treesOfLeaves_sound_aux n n (Nat.le_refl n) ht

/-- **Completeness of `treesOfLeaves`**: Every closed pure-`S` term `t` with `leaves t = n` belongs to `treesOfLeaves n`. -/
theorem treesOfLeaves_complete {n : Nat} {t : Term} (hv : noVars t = true) (hl : leaves t = n) :
    t ∈ treesOfLeaves n := by
  subst hl
  induction t with
  | s => exact .head []
  | var _ => cases hv
  | app l r ihl ihr =>
    have hvl := ((Bool.and_eq_true _ _).mp hv).1
    have hvr := ((Bool.and_eq_true _ _).mp hv).2
    have hge2 : 2 ≤ leaves l + leaves r := Nat.add_le_add (leaves_pos l) (leaves_pos r)
    cases hsum : leaves l + leaves r with
    | zero => rw [hsum] at hge2; cases hge2
    | succ s0 =>
      cases s0 with
      | zero =>
        rw [hsum] at hge2
        cases hge2 with
        | step h0 => cases h0
      | succ m =>
        change l ⋅ r ∈ treesOfLeaves (leaves l + leaves r)
        rw [hsum]
        exact (mem_treesOfLeaves_succ_succ_iff m (l ⋅ r)).mpr
          ⟨leaves l, leaves r, leaves_pos l, leaves_pos r, hsum, l, ihl hvl, r, ihr hvr, rfl⟩

/-- **Exact Membership Equivalence for `treesOfLeaves n`**. -/
theorem mem_treesOfLeaves_iff (n : Nat) (t : Term) :
    t ∈ treesOfLeaves n ↔ noVars t = true ∧ leaves t = n :=
  ⟨treesOfLeaves_sound, fun ⟨hv, hl⟩ => treesOfLeaves_complete hv hl⟩

private theorem nodup_consApps {l : Term} {ys acc : List Term}
    (hys : NoDupList ys) (hacc : NoDupList acc)
    (hdisj : ∀ t, t ∈ acc → ∀ r, r ∈ ys → t ≠ l ⋅ r) :
    NoDupList (consApps l ys acc) := by
  induction ys with
  | nil => exact hacc
  | cons r rs ih =>
    have ⟨hr_not, hrs_nd⟩ := hys
    refine ⟨?_, ih hrs_nd (fun t ht r' hr' => hdisj t ht r' (.tail r hr'))⟩
    intro hm
    rcases (mem_consApps_iff l rs acc (l ⋅ r)).mp hm with ⟨r', hr', heq⟩ | hmem_acc
    · injection heq with _ hrr
      subst hrr
      exact hr_not hr'
    · exact hdisj (l ⋅ r) hmem_acc r (.head rs) rfl

private theorem nodup_appCartAcc {xs ys acc : List Term}
    (hxs : NoDupList xs) (hys : NoDupList ys) (hacc : NoDupList acc)
    (hdisj : ∀ t, t ∈ acc → ∀ l, l ∈ xs → ∀ r, r ∈ ys → t ≠ l ⋅ r) :
    NoDupList (appCartAcc xs ys acc) := by
  induction xs with
  | nil => exact hacc
  | cons l ls ih =>
    have ⟨hl_not, hls_nd⟩ := hxs
    have hsub := ih hls_nd (fun t ht l' hl' r hr => hdisj t ht l' (.tail l hl') r hr)
    refine nodup_consApps hys hsub (fun t ht r hr heq => ?_)
    rcases (mem_appCartAcc_iff ls ys acc t).mp ht with ⟨l', hl', r', _, heq'⟩ | ht_acc
    · rw [heq] at heq'
      injection heq' with hll _
      subst hll
      exact hl_not hl'
    · exact hdisj t ht_acc l (.head ls) r hr heq

private theorem nodup_nextLevelAux (table : List (List Term)) :
    ∀ (k i : Nat),
      (∀ a, i ≤ a → a < i + k → NoDupList (lookupLevel table a) ∧
        ∀ u, u ∈ lookupLevel table a → leaves u = a) →
      (∀ b, 1 ≤ b → b ≤ k → NoDupList (lookupLevel table b)) →
      NoDupList (nextLevelAux table (splits k i)) := by
  intro k
  induction k with
  | zero =>
    intro _ _ _
    exact trivial
  | succ k ih =>
    intro i hA hB
    have hi_lt : i < i + (k + 1) := Nat.lt_add_of_pos_right (Nat.zero_lt_succ k)
    have ⟨hnd_l, hleaves_l⟩ := hA i (Nat.le_refl i) hi_lt
    have hnd_r : NoDupList (lookupLevel table (k + 1)) :=
      hB (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) (Nat.le_refl (k + 1))
    have hsub : NoDupList (nextLevelAux table (splits k (i + 1))) := by
      refine ih (i + 1) (fun a ha1 halt => ?_) (fun b hb1 hbk => hB b hb1 (Nat.le_succ_of_le hbk))
      have halt' : a < i + (k + 1) := by
        rw [Nat.add_assoc i 1 k, Nat.add_comm 1 k] at halt
        exact halt
      exact hA a (Nat.le_of_succ_le ha1) halt'
    refine nodup_appCartAcc hnd_l hnd_r hsub (fun t ht l hl r _ heq => ?_)
    obtain ⟨⟨a', b'⟩, hp', l', hl', r', _, heq'⟩ := (mem_nextLevelAux_iff table (splits k (i + 1)) t).mp ht
    have ⟨hia1, hb1, hab'⟩ := (mem_splits_iff k (i + 1) a' b').mp hp'
    have ha'_lt : a' < i + (k + 1) := by
      have hlt1 : a' < a' + b' := Nat.lt_add_of_pos_right hb1
      rw [hab', Nat.add_assoc i 1 k, Nat.add_comm 1 k] at hlt1
      exact hlt1
    have hleaves_l' := (hA a' (Nat.le_of_succ_le hia1) ha'_lt).2 l' hl'
    rw [heq] at heq'
    injection heq' with hll _
    subst hll
    have heq_leaves : i = a' := (hleaves_l l hl).symm.trans hleaves_l'
    subst heq_leaves
    exact Nat.not_succ_le_self i hia1

private theorem nodup_treesOfLeaves_aux :
    ∀ (B n : Nat), n ≤ B → NoDupList (treesOfLeaves n) := by
  intro B
  induction B with
  | zero =>
    intro n hn
    cases Nat.eq_zero_of_le_zero hn
    exact trivial
  | succ B ih =>
    intro n hn
    cases n with
    | zero => exact trivial
    | succ n0 =>
      cases n0 with
      | zero => exact ⟨(fun h => by cases h), trivial⟩
      | succ m =>
        rw [treesOfLeaves_succ_succ, nextLevel]
        have hmB : m + 1 ≤ B := Nat.le_of_succ_le_succ hn
        refine nodup_nextLevelAux (treesTable (m + 1)) (m + 1) 1 (fun a _ halt => ?_) (fun b _ hble => ?_)
        · have hale : a ≤ m + 1 := by
            rw [Nat.add_comm 1 (m + 1)] at halt
            exact Nat.le_of_lt_succ halt
          rw [lookupLevel_treesTable_le hale]
          exact ⟨ih a (Nat.le_trans hale hmB), fun u hu => (treesOfLeaves_sound hu).2⟩
        · rw [lookupLevel_treesTable_le hble]
          exact ih b (Nat.le_trans hble hmB)

/-- **Duplicate-Freeness of `treesOfLeaves n`**: Every closed pure-`S` term of size `n` appears *exactly once*. -/
theorem nodup_treesOfLeaves (n : Nat) : NoDupList (treesOfLeaves n) :=
  nodup_treesOfLeaves_aux n n (Nat.le_refl n)

/-- Cumulative enumeration of all closed pure-`S` terms with `leaves t ≤ n`. -/
def treesUpToLeaves : Nat → List Term
  | 0 => []
  | n + 1 => treesUpToLeaves n ++ treesOfLeaves (n + 1)

theorem mem_treesUpToLeaves_iff (n : Nat) (t : Term) :
    t ∈ treesUpToLeaves n ↔ noVars t = true ∧ leaves t ≤ n := by
  induction n with
  | zero =>
    constructor
    · intro h; cases h
    · intro ⟨_, hle⟩
      exfalso
      exact Nat.not_succ_le_zero 0 (Nat.le_trans (leaves_pos t) hle)
  | succ n ih =>
    simp only [treesUpToLeaves, List.mem_append, ih, mem_treesOfLeaves_iff]
    constructor
    · intro h
      rcases h with ⟨hv, hle⟩ | ⟨hv, heq⟩
      · exact ⟨hv, Nat.le_succ_of_le hle⟩
      · exact ⟨hv, heq ▸ Nat.le_refl (n + 1)⟩
    · intro ⟨hv, hle⟩
      exact if heq : leaves t = n + 1 then
        Or.inr ⟨hv, heq⟩
      else
        Or.inl ⟨hv, Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hle heq)⟩

/-- Exact Catalan tree counts for `n = 1 .. 9` (`1, 1, 2, 5, 14, 42, 132, 429, 1430`). -/
theorem catalan_small_counts :
    (treesOfLeaves 1).length = 1 ∧
    (treesOfLeaves 2).length = 1 ∧
    (treesOfLeaves 3).length = 2 ∧
    (treesOfLeaves 4).length = 5 ∧
    (treesOfLeaves 5).length = 14 ∧
    (treesOfLeaves 6).length = 42 ∧
    (treesOfLeaves 7).length = 132 ∧
    (treesOfLeaves 8).length = 429 ∧
    (treesOfLeaves 9).length = 1430 ∧
    (treesUpToLeaves 6).length = 65 ∧
    (treesUpToLeaves 7).length = 197 ∧
    (treesUpToLeaves 8).length = 626 ∧
    (treesUpToLeaves 9).length = 2056 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Computable 1-Step Rewriting Enumerator (`oneStepReducts`) & Sizes `1 .. 4` Normal-Form Sharpness -/

def rootStepList (a b : Term) : List Term :=
  match a with
  | .app (.app .s x) y => [(x ⋅ b) ⋅ (y ⋅ b)]
  | _ => []

def mapLeftApp (b : Term) : List Term → List Term
  | [] => []
  | a' :: as => (a' ⋅ b) :: mapLeftApp b as

def mapRightApp (a : Term) : List Term → List Term
  | [] => []
  | b' :: bs => (a ⋅ b') :: mapRightApp a bs

def oneStepReducts : Term → List Term
  | .s => []
  | .var _ => []
  | .app a b => rootStepList a b ++ (mapLeftApp b (oneStepReducts a) ++ mapRightApp a (oneStepReducts b))

private theorem mem_rootStepList_iff (a b u : Term) :
    u ∈ rootStepList a b ↔ ∃ x y, a = S ⋅ x ⋅ y ∧ u = (x ⋅ b) ⋅ (y ⋅ b) := by
  cases a with
  | s => exact ⟨(fun h => by cases h), (fun ⟨_, _, h, _⟩ => by cases h)⟩
  | var _ => exact ⟨(fun h => by cases h), (fun ⟨_, _, h, _⟩ => by cases h)⟩
  | app a1 y =>
    cases a1 with
    | s => exact ⟨(fun h => by cases h), (fun ⟨_, _, h, _⟩ => by cases h)⟩
    | var _ => exact ⟨(fun h => by cases h), (fun ⟨_, _, h, _⟩ => by cases h)⟩
    | app a2 x =>
      cases a2 with
      | s =>
        constructor
        · intro hm
          cases hm with
          | head _ => exact ⟨x, y, rfl, rfl⟩
          | tail _ ht => cases ht
        · intro ⟨x', y', ha, hu⟩
          injection ha with h1 hy
          injection h1 with _ hx
          subst hx; subst hy; subst hu
          exact .head []
      | var _ =>
        exact ⟨(fun h => by cases h),
          (fun ⟨_, _, h, _⟩ => by injection h with h1 _; injection h1 with h2 _; cases h2)⟩
      | app _ _ =>
        exact ⟨(fun h => by cases h),
          (fun ⟨_, _, h, _⟩ => by injection h with h1 _; injection h1 with h2 _; cases h2)⟩

private theorem mem_mapLeftApp_iff (b : Term) (as : List Term) (u : Term) :
    u ∈ mapLeftApp b as ↔ ∃ a', a' ∈ as ∧ u = a' ⋅ b := by
  induction as with
  | nil => exact ⟨(fun h => by cases h), (fun ⟨_, hm, _⟩ => by cases hm)⟩
  | cons a' as ih =>
    constructor
    · intro hm
      cases hm with
      | head _ => exact ⟨a', .head as, rfl⟩
      | tail _ ht =>
        obtain ⟨a'', ha'', hu⟩ := ih.mp ht
        exact ⟨a'', .tail a' ha'', hu⟩
    · intro ⟨a'', ha'', hu⟩
      cases ha'' with
      | head _ => subst hu; exact .head _
      | tail _ ht => exact .tail _ (ih.mpr ⟨a'', ht, hu⟩)

private theorem mem_mapRightApp_iff (a : Term) (bs : List Term) (u : Term) :
    u ∈ mapRightApp a bs ↔ ∃ b', b' ∈ bs ∧ u = a ⋅ b' := by
  induction bs with
  | nil => exact ⟨(fun h => by cases h), (fun ⟨_, hm, _⟩ => by cases hm)⟩
  | cons b' bs ih =>
    constructor
    · intro hm
      cases hm with
      | head _ => exact ⟨b', .head bs, rfl⟩
      | tail _ ht =>
        obtain ⟨b'', hb'', hu⟩ := ih.mp ht
        exact ⟨b'', .tail b' hb'', hu⟩
    · intro ⟨b'', hb'', hu⟩
      cases hb'' with
      | head _ => subst hu; exact .head _
      | tail _ ht => exact .tail _ (ih.mpr ⟨b'', ht, hu⟩)

private theorem oneStepReducts_sound : ∀ (t u : Term), u ∈ oneStepReducts t → Step t u
  | .s, _, h => by cases h
  | .var _, _, h => by cases h
  | .app a b, u, h => by
    simp only [oneStepReducts, List.mem_append, mem_rootStepList_iff,
      mem_mapLeftApp_iff, mem_mapRightApp_iff] at h
    rcases h with ⟨x, y, rfl, rfl⟩ | (⟨a', ha', rfl⟩ | ⟨b', hb', rfl⟩)
    · exact FormalAlgebra.Step.root x y b
    · exact FormalAlgebra.Step.left (oneStepReducts_sound a a' ha')
    · exact FormalAlgebra.Step.right (oneStepReducts_sound b b' hb')

/-- **Exact Completeness & Soundness of `oneStepReducts`**: `u ∈ oneStepReducts t ↔ Step t u`. -/
theorem mem_oneStepReducts_iff (t u : Term) : u ∈ oneStepReducts t ↔ Step t u := by
  refine ⟨oneStepReducts_sound t u, fun hs => ?_⟩
  induction hs with
  | root x y z =>
    simp only [oneStepReducts, List.mem_append, mem_rootStepList_iff]
    exact Or.inl ⟨x, y, rfl, rfl⟩
  | @left a a' b _ ih =>
    simp only [oneStepReducts, List.mem_append, mem_mapLeftApp_iff]
    exact Or.inr (Or.inl ⟨a', ih, rfl⟩)
  | @right a b b' _ ih =>
    simp only [oneStepReducts, List.mem_append, mem_mapRightApp_iff]
    exact Or.inr (Or.inr ⟨b', ih, rfl⟩)

def isNormalFormBool (t : Term) : Bool :=
  match oneStepReducts t with
  | [] => true
  | _ :: _ => false

theorem isNormalFormBool_iff (t : Term) : isNormalFormBool t = true ↔ IsNormalForm t := by
  unfold isNormalFormBool
  cases hrs : oneStepReducts t with
  | nil =>
    refine ⟨fun _ u hs => ?_, fun _ => rfl⟩
    have hm := (mem_oneStepReducts_iff t u).mpr hs
    rw [hrs] at hm
    cases hm
  | cons u us =>
    refine ⟨(fun h => by cases h), fun hnf => ?_⟩
    have hs := (mem_oneStepReducts_iff t u).mp (hrs ▸ .head us)
    exact False.elim (hnf u hs)

private theorem size_le_3_nf_chk : listAll isNormalFormBool (treesUpToLeaves 3) = true := rfl
private theorem size_4_not_nf_eq :
    filterList (fun t => !isNormalFormBool t) (treesOfLeaves 4) = [S ⋅ S ⋅ S ⋅ S] := rfl

theorem size_le_3_all_normalForm {t : Term} (hv : noVars t = true) (hl : leaves t ≤ 3) :
    IsNormalForm t :=
  (isNormalFormBool_iff t).mp
    (listAll_sound size_le_3_nf_chk ((mem_treesUpToLeaves_iff 3 t).mpr ⟨hv, hl⟩))

theorem size_4_reducible_iff {t : Term} (hv : noVars t = true) (hl : leaves t = 4) :
    ¬ IsNormalForm t ↔ t = S ⋅ S ⋅ S ⋅ S := by
  have hm := treesOfLeaves_complete hv hl
  have hiff := mem_witnesses_iff_of_filter_eq size_4_not_nf_eq hm
  rw [mem_singleton_iff] at hiff
  rw [← hiff]
  cases hb : isNormalFormBool t with
  | true =>
    exact ⟨fun hnot => False.elim (hnot ((isNormalFormBool_iff t).mp hb)), (fun h => by cases h)⟩
  | false =>
    exact ⟨fun _ => rfl, (fun _ hnf => by rw [(isNormalFormBool_iff t).mpr hnf] at hb; cases hb)⟩

/-! ## 4. Theorem A: Universal Strong Normalization, Head Normalization & Productivity for `leaves ≤ 6` -/

private theorem size_le_6_sn_chk :
    listAll (fun t => decide (evalSN t ≠ .sn38)) (treesUpToLeaves 6) = true := rfl

/-- **Theorem A (`leaves ≤ 6` Universal Normalization & Productivity)**:
    Every closed pure-`S` term `t` with `leaves t ≤ 6` (all `1 + 1 + 2 + 5 + 14 + 42 = 65` terms)
    is Strongly Normalizing (`StrongNormalizing t`), Weakly Normalizing (`HasNormalForm t`),
    Head-Normalizing (`HasHNF t`), and Productive (`evalP t ≠ .p37`). -/
theorem theorem_A_universal_sn_le_6 {t : Term} (hv : noVars t = true) (hl : leaves t ≤ 6) :
    StrongNormalizing t ∧ HasNormalForm t ∧ HasHNF t ∧ evalP t ≠ .p37 := by
  have hm := (mem_treesUpToLeaves_iff 6 t).mpr ⟨hv, hl⟩
  have hne38 : evalSN t ≠ .sn38 := of_decide_eq_true (listAll_sound size_le_6_sn_chk hm)
  have hsn : StrongNormalizing t := (waldmann_theorem_9 hv).1.mpr hne38
  have hwn : HasNormalForm t := (waldmann_theorem_9 hv).2.mpr hne38
  have hp : evalP t ≠ .p37 := sn_implies_productive hv hsn
  have hhn : HasHNF t := productive_implies_hasHNF hv hp
  exact ⟨hsn, hwn, hhn, hp⟩

/-! ## 5. Theorem B: Exact Classification of Size `7` (`132` Terms) — Minimal Non-`SN` Threshold -/

def minNonSN7_a : Term := S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S
def minNonSN7_b : Term := S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S

theorem minNonSN7_witness_facts :
    minNonSN7_a ≠ minNonSN7_b ∧
    noVars minNonSN7_a = true ∧ leaves minNonSN7_a = 7 ∧
    noVars minNonSN7_b = true ∧ leaves minNonSN7_b = 7 ∧
    Step minNonSN7_b minNonSN7_a ∧
    evalSN minNonSN7_a = .sn38 ∧ evalHN minNonSN7_a = .hn23 ∧ evalP minNonSN7_a = .p37 ∧
    evalSN minNonSN7_b = .sn38 ∧ evalHN minNonSN7_b = .hn23 ∧ evalP minNonSN7_b = .p37 :=
  ⟨by decide, rfl, rfl, rfl, rfl,
   FormalAlgebra.Step.left (FormalAlgebra.Step.left (FormalAlgebra.Step.root (S ⋅ S) S S)),
   rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem size_7_all_hn_chk :
    listAll (fun t => decide (evalHN t ≠ .hn34)) (treesOfLeaves 7) = true := rfl

private theorem size_7_nonsn_eq :
    filterList (fun t => decide (evalSN t = .sn38)) (treesOfLeaves 7) =
      [minNonSN7_a, minNonSN7_b] := rfl

private theorem size_7_nonprod_eq :
    filterList (fun t => decide (evalP t = .p37)) (treesOfLeaves 7) =
      [minNonSN7_a, minNonSN7_b] := rfl

/-- **Theorem B (Exact Classification of Size `7` — Minimal Non-`SN` Threshold)**:
    Out of all `132` closed pure-`S` terms with `leaves t = 7`, **every single one** has a
    Head Normal Form (`HasHNF t`), and `¬ StrongNormalizing t` (as well as `evalP t = .p37`)
    holds **if and only if** `t = S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S` or `t = S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S`. -/
theorem theorem_B_exact_size_7_classification {t : Term} (hv : noVars t = true) (hl : leaves t = 7) :
    HasHNF t ∧
    (¬ StrongNormalizing t ↔
      (t = S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S ∨ t = S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S)) ∧
    (evalP t = .p37 ↔
      (t = S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S ∨ t = S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S)) := by
  have hm := treesOfLeaves_complete hv hl
  have hhn : HasHNF t :=
    (barendregt_open_problem_10 hv).1.mpr (of_decide_eq_true (listAll_sound size_7_all_hn_chk hm))
  have hsn_iff : ¬ StrongNormalizing t ↔ (t = minNonSN7_a ∨ t = minNonSN7_b) := by
    rw [not_sn_iff_evalSN_eq_sn38 hv]
    have hf := mem_witnesses_iff_of_filter_eq size_7_nonsn_eq hm
    rw [mem_pair_iff] at hf
    exact ⟨fun h => hf.mp (decide_eq_true h), fun h => of_decide_eq_true (hf.mpr h)⟩
  have hp_iff : evalP t = .p37 ↔ (t = minNonSN7_a ∨ t = minNonSN7_b) := by
    have hf := mem_witnesses_iff_of_filter_eq size_7_nonprod_eq hm
    rw [mem_pair_iff] at hf
    exact ⟨fun h => hf.mp (decide_eq_true h), fun h => of_decide_eq_true (hf.mpr h)⟩
  exact ⟨hhn, hsn_iff, hp_iff⟩

theorem minimal_non_sn_leaves_ge_7 {t : Term} (hv : noVars t = true) (hnsn : ¬ StrongNormalizing t) :
    7 ≤ leaves t := by
  exact if hge : 7 ≤ leaves t then hge
  else False.elim (hnsn (theorem_A_universal_sn_le_6 hv (Nat.le_of_lt_succ (Nat.lt_of_not_le hge))).1)

theorem le_7_non_sn_iff {t : Term} (hv : noVars t = true) (hl : leaves t ≤ 7) :
    ¬ StrongNormalizing t ↔
      (t = S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S ∨ t = S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S) := by
  constructor
  · intro hnsn
    have hge7 := minimal_non_sn_leaves_ge_7 hv hnsn
    have heq7 : leaves t = 7 := Nat.le_antisymm hl hge7
    exact (theorem_B_exact_size_7_classification hv heq7).2.1.mp hnsn
  · intro h
    rcases h with rfl | rfl
    · exact (not_sn_iff_evalSN_eq_sn38 rfl).mpr rfl
    · exact (not_sn_iff_evalSN_eq_sn38 rfl).mpr rfl

/-! ## 6. Theorem C: Exact Classification of Size `8` (`429` Terms) — Minimal Non-`HN` Threshold
    and Universal `Productive ↔ SN` Equivalence for `leaves ≤ 8` -/

/-- The exact 15 minimal closed pure-`S` combinators without a Head Normal Form (`leaves = 8`). -/
def minimalNonHN8 : List Term :=
  [ S ⋅ (S ⋅ S ⋅ S) ⋅ S ⋅ (S ⋅ S ⋅ S),
    S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S ⋅ S)) ⋅ S,
    S ⋅ (S ⋅ S) ⋅ S ⋅ (S ⋅ S ⋅ S) ⋅ S,
    S ⋅ (S ⋅ (S ⋅ S ⋅ S)) ⋅ (S ⋅ S) ⋅ S,
    S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ (S ⋅ S) ⋅ S,
    S ⋅ (S ⋅ S ⋅ S) ⋅ S ⋅ (S ⋅ S) ⋅ S,
    S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S,
    S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ S ⋅ S,
    S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅ S ⋅ S,
    S ⋅ (S ⋅ S) ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S,
    S ⋅ (S ⋅ (S ⋅ S ⋅ S)) ⋅ S ⋅ S ⋅ S,
    S ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S ⋅ S ⋅ S,
    S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S,
    S ⋅ (S ⋅ (S ⋅ S)) ⋅ S ⋅ S ⋅ S ⋅ S,
    S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S ⋅ S ]

def Wolfram2_comb : Term := S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)

theorem wolfram2_exact_classification :
    noVars Wolfram2_comb = true ∧
    leaves Wolfram2_comb = 8 ∧
    ¬ StrongNormalizing Wolfram2_comb ∧
    HasHNF Wolfram2_comb ∧
    evalSN Wolfram2_comb = .sn38 ∧
    evalHN Wolfram2_comb = .hn24 ∧
    evalP Wolfram2_comb = .p37 := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · exact (not_sn_iff_evalSN_eq_sn38 rfl).mpr rfl
  · exact (barendregt_open_problem_10 rfl).1.mpr (by decide)

theorem no_non_hn_le_7 {t : Term} (hv : noVars t = true) (hl : leaves t ≤ 7) :
    HasHNF t := by
  exact if heq7 : leaves t = 7 then
    (theorem_B_exact_size_7_classification hv heq7).1
  else
    (theorem_A_universal_sn_le_6 hv (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hl heq7))).2.2.1

theorem minimal_non_hn_leaves_ge_8 {t : Term} (hv : noVars t = true) (hnhn : ¬ HasHNF t) :
    8 ≤ leaves t := by
  exact if hge : 8 ≤ leaves t then hge
  else False.elim (hnhn (no_non_hn_le_7 hv (Nat.le_of_lt_succ (Nat.lt_of_not_le hge))))

private theorem minimalNonHN8_nodup_chk : noDupDec minimalNonHN8 = true := rfl

private theorem size_8_non_hn_filter_eq :
    filterList (fun t => decide (evalHN t = .hn34)) (treesOfLeaves 8) = minimalNonHN8 := rfl

private theorem le_8_no_prod_nonsn_chk :
    listAll (fun t => decide ¬ (evalSN t = .sn38 ∧ evalP t ≠ .p37)) (treesUpToLeaves 8) = true := rfl

/-- **Theorem C (Exact Classification of Size `8` — Minimal Non-`HN` Threshold & Zero Productive Non-`SN` up to Size `8`)**:
    1. Every closed pure-`S` term with `leaves t ≤ 7` (`197` terms) has `HasHNF t`;
    2. Out of all `429` closed pure-`S` terms with `leaves t = 8`, `¬ HasHNF t` (`evalHN t = .hn34`)
       holds **if and only if** `t ∈ minimalNonHN8` (exact `15` distinct witnesses);
    3. Across all `626` closed pure-`S` terms with `leaves t ≤ 8`, **zero** terms satisfy
       `¬ StrongNormalizing t ∧ evalP t ≠ .p37` (`evalSN t = .sn38 ∧ evalP t ≠ .p37`), so
       **Productivity is equivalent to Strong Normalization (`evalP t ≠ .p37 ↔ StrongNormalizing t`) for all `leaves t ≤ 8`**. -/
theorem theorem_C_exact_size_8_classification :
    minimalNonHN8.length = 15 ∧
    NoDupList minimalNonHN8 ∧
    (∀ {t : Term}, noVars t = true → leaves t ≤ 7 → HasHNF t) ∧
    (∀ {t : Term}, noVars t = true → leaves t = 8 → (¬ HasHNF t ↔ t ∈ minimalNonHN8)) ∧
    (∀ {t : Term}, noVars t = true → leaves t ≤ 8 → ¬ (¬ StrongNormalizing t ∧ evalP t ≠ .p37)) ∧
    (∀ {t : Term}, noVars t = true → leaves t ≤ 8 → (evalP t ≠ .p37 ↔ StrongNormalizing t)) := by
  refine ⟨rfl, noDupDec_sound minimalNonHN8_nodup_chk, @no_non_hn_le_7, ?_, ?_, ?_⟩
  · intro t hv hl
    rw [not_hasHNF_iff_evalHN_eq_hn34 hv]
    have hm := treesOfLeaves_complete hv hl
    have hf := mem_witnesses_iff_of_filter_eq size_8_non_hn_filter_eq hm
    exact ⟨fun h => hf.mp (decide_eq_true h), fun h => of_decide_eq_true (hf.mpr h)⟩
  · intro t hv hl ⟨hnsn, hp⟩
    have hm := (mem_treesUpToLeaves_iff 8 t).mpr ⟨hv, hl⟩
    have hnot : ¬ (evalSN t = .sn38 ∧ evalP t ≠ .p37) :=
      of_decide_eq_true (listAll_sound le_8_no_prod_nonsn_chk hm)
    exact hnot ⟨(not_sn_iff_evalSN_eq_sn38 hv).mp hnsn, hp⟩
  · intro t hv hl
    refine ⟨fun hp => ?_, sn_implies_productive hv⟩
    exact if h38 : evalSN t = .sn38 then by
      exfalso
      have hm := (mem_treesUpToLeaves_iff 8 t).mpr ⟨hv, hl⟩
      have hnot : ¬ (evalSN t = .sn38 ∧ evalP t ≠ .p37) :=
        of_decide_eq_true (listAll_sound le_8_no_prod_nonsn_chk hm)
      exact hnot ⟨h38, hp⟩
    else
      (waldmann_theorem_9 hv).1.mpr h38

theorem size_8_exact_counts :
    (treesOfLeaves 8).length = 429 ∧
    (filterList (fun t => decide (evalSN t ≠ .sn38)) (treesOfLeaves 8)).length = 388 ∧
    (filterList (fun t => decide (evalSN t = .sn38)) (treesOfLeaves 8)).length = 41 ∧
    (filterList (fun t => decide (evalHN t ≠ .hn34)) (treesOfLeaves 8)).length = 414 ∧
    (filterList (fun t => decide (evalHN t = .hn34)) (treesOfLeaves 8)).length = 15 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 7. Theorem D: Size `9` (`1,430` Terms) — Unique Minimal Productive Non-Halting Pure-`S` Combinator -/

/-- The unique 9-leaf productive non-`SN` pure-`S` combinator `S(S(SS))(S(SS))(SS)`,
    reducing in 1 root step to Zachos's 10-leaf Böhm-tree generator `(S(SS)(SS))(S(SS)(SS))`. -/
def minProdNonSN9 : Term := S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)
def Zachos10 : Term := (S ⋅ (S ⋅ S) ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S))

theorem minProdNonSN9_witness_facts :
    noVars minProdNonSN9 = true ∧
    leaves minProdNonSN9 = 9 ∧
    ¬ StrongNormalizing minProdNonSN9 ∧
    HasHNF minProdNonSN9 ∧
    evalSN minProdNonSN9 = .sn38 ∧
    evalHN minProdNonSN9 = .hn24 ∧
    evalP minProdNonSN9 = .p29 ∧
    Step minProdNonSN9 Zachos10 ∧
    leaves Zachos10 = 10 := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, FormalAlgebra.Step.root (S ⋅ (S ⋅ S)) (S ⋅ (S ⋅ S)) (S ⋅ S), rfl⟩
  · exact (not_sn_iff_evalSN_eq_sn38 rfl).mpr rfl
  · exact (barendregt_open_problem_10 rfl).1.mpr (by decide)

private theorem size_9_prod_nonsn_filter_eq :
    filterList (fun t => decide (evalSN t = .sn38 ∧ evalP t ≠ .p37)) (treesOfLeaves 9) =
      [minProdNonSN9] := rfl

theorem minimal_productive_non_sn_leaves_ge_9 {t : Term}
    (hv : noVars t = true) (hnsn : ¬ StrongNormalizing t) (hp : evalP t ≠ .p37) :
    9 ≤ leaves t := by
  exact if hge : 9 ≤ leaves t then hge
  else False.elim (theorem_C_exact_size_8_classification.2.2.2.2.1 hv
    (Nat.le_of_lt_succ (Nat.lt_of_not_le hge)) ⟨hnsn, hp⟩)

/-- **Theorem D (Unique Minimal Productive Non-Halting Pure-`S` Combinator — Size `9`)**:
    1. Every closed pure-`S` term `t` that is non-`SN` yet productive (`¬ StrongNormalizing t ∧ evalP t ≠ .p37`)
       has at least `9` leaves (`9 ≤ leaves t`);
    2. Out of all `1,430` closed pure-`S` terms with `leaves t = 9` (and all `2,056` closed pure-`S` terms
       with `leaves t ≤ 9`), `¬ StrongNormalizing t ∧ evalP t ≠ .p37` holds **if and only if**
       `t = S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)` (`minProdNonSN9`), which steps in 1 root step to `Zachos10`. -/
theorem theorem_D_minimal_productive_non_sn_size_9 :
    (∀ {t : Term}, noVars t = true → ¬ StrongNormalizing t → evalP t ≠ .p37 → 9 ≤ leaves t) ∧
    (∀ {t : Term}, noVars t = true → leaves t = 9 →
      ((¬ StrongNormalizing t ∧ evalP t ≠ .p37) ↔ t = S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))) ∧
    (∀ {t : Term}, noVars t = true → leaves t ≤ 9 →
      ((¬ StrongNormalizing t ∧ evalP t ≠ .p37) ↔ t = S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))) := by
  have hsize9 : ∀ {t : Term}, noVars t = true → leaves t = 9 →
      ((¬ StrongNormalizing t ∧ evalP t ≠ .p37) ↔ t = minProdNonSN9) := by
    intro t hv hl
    rw [not_sn_iff_evalSN_eq_sn38 hv]
    have hm := treesOfLeaves_complete hv hl
    have hf := mem_witnesses_iff_of_filter_eq size_9_prod_nonsn_filter_eq hm
    rw [mem_singleton_iff] at hf
    exact ⟨fun h => hf.mp (decide_eq_true h), fun h => of_decide_eq_true (hf.mpr h)⟩
  refine ⟨@minimal_productive_non_sn_leaves_ge_9, hsize9, ?_⟩
  intro t hv hl
  constructor
  · intro ⟨hnsn, hp⟩
    have hge9 := minimal_productive_non_sn_leaves_ge_9 hv hnsn hp
    have heq9 : leaves t = 9 := Nat.le_antisymm hl hge9
    exact (hsize9 hv heq9).mp ⟨hnsn, hp⟩
  · intro heq
    subst heq
    exact ⟨minProdNonSN9_witness_facts.2.2.1, by decide⟩

theorem size_9_exact_counts :
    (treesOfLeaves 9).length = 1430 ∧
    (filterList (fun t => decide (evalSN t ≠ .sn38)) (treesOfLeaves 9)).length = 1154 ∧
    (filterList (fun t => decide (evalP t ≠ .p37)) (treesOfLeaves 9)).length = 1155 ∧
    (filterList (fun t => decide (evalSN t = .sn38 ∧ evalP t ≠ .p37)) (treesOfLeaves 9)).length = 1 ∧
    (filterList (fun t => decide (evalHN t = .hn34)) (treesOfLeaves 9)).length = 136 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 8. Theorem E: Minimal RNF-without-HNF Threshold (`leaves = 9`, `15` Witnesses)
    and Minimal Non-Convertible Head-Divergent (`BT = ⊥`) Pairs -/

theorem no_rnf_without_hnf_le_8 {t : Term} (hv : noVars t = true) (hl : leaves t ≤ 8)
    (hrnf : IsRootNormalForm t) : HasHNF t := by
  rcases (footnote4_rnf_iff hv).mp hrnf with hsl | ⟨a, b, rfl, ha34⟩
  · exact ⟨t, FormalAlgebra.Reduces.refl t, hsl⟩
  · exfalso
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    have hnhn_a : ¬ HasHNF a := (not_hasHNF_iff_evalHN_eq_hn34 hva).mpr ha34
    have hge8 : 8 ≤ leaves a := minimal_non_hn_leaves_ge_8 hva hnhn_a
    have hge9 : 9 ≤ leaves (a ⋅ b) := Nat.add_le_add hge8 (leaves_pos b)
    exact Nat.not_succ_le_self 8 (Nat.le_trans hge9 hl)

/-- **Exact Size-9 RNF-without-HNF Classification**:
    No closed pure-`S` term with `leaves t ≤ 8` is an RNF without HNF, and at `leaves t = 9`,
    `IsRootNormalForm t ∧ ¬ HasHNF t` holds **iff** `t = u ⋅ S` for one of the 15 terms `u ∈ minimalNonHN8`. -/
theorem size_9_rnf_without_hnf_iff {t : Term} (hv : noVars t = true) (hl : leaves t = 9) :
    (IsRootNormalForm t ∧ ¬ HasHNF t) ↔ ∃ u, u ∈ minimalNonHN8 ∧ t = u ⋅ S := by
  constructor
  · intro ⟨hrnf, hnhn⟩
    rcases (footnote4_rnf_iff hv).mp hrnf with hsl | ⟨a, b, rfl, ha34⟩
    · exfalso; exact hnhn ⟨t, FormalAlgebra.Reduces.refl t, hsl⟩
    · have hva := ((Bool.and_eq_true _ _).mp hv).1
      have hvb := ((Bool.and_eq_true _ _).mp hv).2
      have hnhn_a : ¬ HasHNF a := (not_hasHNF_iff_evalHN_eq_hn34 hva).mpr ha34
      have hge8 : 8 ≤ leaves a := minimal_non_hn_leaves_ge_8 hva hnhn_a
      have hb_pos : 1 ≤ leaves b := leaves_pos b
      change leaves a + leaves b = 9 at hl
      have ha_le8 : leaves a ≤ 8 := by
        have : leaves a + 1 ≤ 9 := hl ▸ Nat.add_le_add_left hb_pos (leaves a)
        exact Nat.le_of_succ_le_succ this
      have ha8 : leaves a = 8 := Nat.le_antisymm ha_le8 hge8
      have hb1 : leaves b = 1 := by
        rw [ha8] at hl
        exact Nat.add_left_cancel hl
      have hb_eq_s : b = S := by
        cases b with
        | s => rfl
        | var _ => cases hvb
        | app b1 b2 =>
          have h2 : 2 ≤ leaves b1 + leaves b2 := Nat.add_le_add (leaves_pos b1) (leaves_pos b2)
          change leaves b1 + leaves b2 = 1 at hb1
          rw [hb1] at h2
          cases h2 with
          | step h0 => cases h0
      subst hb_eq_s
      exact ⟨a, (theorem_C_exact_size_8_classification.2.2.2.1 hva ha8).mp hnhn_a, rfl⟩
  · intro ⟨u, hu_mem, htu⟩
    subst htu
    have hva : noVars u = true := ((Bool.and_eq_true _ _).mp hv).1
    have hu8 : leaves u = 8 := by
      change leaves u + 1 = 9 at hl
      exact Nat.succ.inj hl
    have hnhn_u : ¬ HasHNF u := (theorem_C_exact_size_8_classification.2.2.2.1 hva hu8).mpr hu_mem
    have hu34 : evalHN u = .hn34 := (not_hasHNF_iff_evalHN_eq_hn34 hva).mp hnhn_u
    have hrnf : IsRootNormalForm (u ⋅ S) := (footnote4_rnf_iff hv).mpr (Or.inr ⟨u, S, rfl, hu34⟩)
    have hus34 : evalHN (u ⋅ S) = .hn34 := by
      change deltaHN (evalHN u) .hn0 = .hn34
      rw [hu34]
      exact deltaHN_hn34_left .hn0
    exact ⟨hrnf, (not_hasHNF_iff_evalHN_eq_hn34 hv).mpr hus34⟩

private theorem minimalNonHN8_all_q34_chk :
    listAll (fun u => decide (eval36 u = .q34 ∧ eval36 (u ⋅ S) = .q35)) minimalNonHN8 = true := rfl

theorem minimal_q31_non_convertible_bot_pairs :
    (∀ u, u ∈ minimalNonHN8 → ¬ ConvS u (u ⋅ S)) ∧
    leaves (R_gadget S) = 8 ∧
    leaves (R_gadget S ⋅ S) = 9 ∧
    leaves AAA = 9 ∧
    ¬ HasHNF (R_gadget S) ∧
    ¬ HasHNF (R_gadget S ⋅ S) ∧
    ¬ HasHNF AAA ∧
    ¬ ConvS (R_gadget S) (R_gadget S ⋅ S) ∧
    ¬ ConvS AAA (R_gadget S ⋅ S) := by
  have hall : ∀ u, u ∈ minimalNonHN8 → ¬ ConvS u (u ⋅ S) := by
    intro u hu hconv
    have ⟨hq34, hq35⟩ := of_decide_eq_true (listAll_sound minimalNonHN8_all_q34_chk hu)
    have heq := eval36_conv hconv
    rw [hq34, hq35] at heq
    cases heq
  refine ⟨hall, rfl, rfl, rfl, ?_, ?_, ?_, hall (R_gadget S) (.head _), ?_⟩
  · exact (not_hasHNF_iff_evalHN_eq_hn34 rfl).mpr rfl
  · exact (not_hasHNF_iff_evalHN_eq_hn34 rfl).mpr rfl
  · exact (not_hasHNF_iff_evalHN_eq_hn34 rfl).mpr rfl
  · intro hconv
    have heq := eval36_conv hconv
    have h1 : eval36 AAA = .q34 := rfl
    have h2 : eval36 (R_gadget S ⋅ S) = .q35 := rfl
    rw [h1, h2] at heq
    cases heq

/-! ## 9. Theorem F: Confluence, Deterministic Rewriting for `leaves ≤ 6`,
    Minimal Multiway Forks at `leaves = 7`, and the Unique Minimal Strict 1-Step Diamond Counterexample -/

def HasMultiwayFork (t : Term) : Prop :=
  ∃ b c, b ≠ c ∧ Step t b ∧ Step t c

def StrictStepDiamondAt (t : Term) : Prop :=
  ∀ b c, Step t b → Step t c → b ≠ c → ∃ d, Step b d ∧ Step c d

def WeakDiamondAt (t : Term) : Prop :=
  ∀ b c, Step t b → Step t c → ∃ d, Reduces b d ∧ Reduces c d

def ConfluentAt (t : Term) : Prop :=
  ∀ b c, Reduces t b → Reduces t c → ∃ d, Reduces b d ∧ Reduces c d

def hasMultiwayForkBool (t : Term) : Bool :=
  let rs := oneStepReducts t
  listAny (fun b => listAny (fun c => decide (b ≠ c)) rs) rs

theorem hasMultiwayForkBool_iff (t : Term) :
    hasMultiwayForkBool t = true ↔ HasMultiwayFork t := by
  unfold hasMultiwayForkBool HasMultiwayFork
  simp only [listAny_iff]
  constructor
  · intro ⟨b, hb, c, hc, hne⟩
    exact ⟨b, c, of_decide_eq_true hne,
      (mem_oneStepReducts_iff t b).mp hb, (mem_oneStepReducts_iff t c).mp hc⟩
  · intro ⟨b, c, hne, hsb, hsc⟩
    exact ⟨b, (mem_oneStepReducts_iff t b).mpr hsb,
      c, (mem_oneStepReducts_iff t c).mpr hsc, decide_eq_true hne⟩

def strictStepDiamondBool (t : Term) : Bool :=
  let rs := oneStepReducts t
  listAll (fun b =>
    listAll (fun c =>
      !decide (b ≠ c) || listAny (fun d => listMemDec d (oneStepReducts c)) (oneStepReducts b))
      rs) rs

theorem strictStepDiamondBool_iff (t : Term) :
    strictStepDiamondBool t = true ↔ StrictStepDiamondAt t := by
  unfold strictStepDiamondBool StrictStepDiamondAt
  simp only [listAll_iff]
  constructor
  · intro hall b c hsb hsc hne
    have hb := (mem_oneStepReducts_iff t b).mpr hsb
    have hc := (mem_oneStepReducts_iff t c).mpr hsc
    have hrow := hall b hb c hc
    rw [decide_eq_true hne] at hrow
    simp only [Bool.not_true, Bool.false_or] at hrow
    obtain ⟨d, hdb, hdc_dec⟩ := (listAny_iff _ _).mp hrow
    exact ⟨d, (mem_oneStepReducts_iff b d).mp hdb,
      (mem_oneStepReducts_iff c d).mp ((listMemDec_iff d (oneStepReducts c)).mp hdc_dec)⟩
  · intro hdiam b hb c hc
    cases hd : decide (b ≠ c) with
    | false => rfl
    | true =>
      simp only [Bool.not_true, Bool.false_or]
      obtain ⟨d, hbd, hcd⟩ := hdiam b c
        ((mem_oneStepReducts_iff t b).mp hb) ((mem_oneStepReducts_iff t c).mp hc) (of_decide_eq_true hd)
      exact (listAny_iff _ _).mpr ⟨d, (mem_oneStepReducts_iff b d).mpr hbd,
        (listMemDec_iff d (oneStepReducts c)).mpr ((mem_oneStepReducts_iff c d).mpr hcd)⟩

private theorem le_6_no_fork_chk :
    listAll (fun t => !hasMultiwayForkBool t) (treesUpToLeaves 6) = true := rfl

private theorem size_7_forks_eq :
    filterList hasMultiwayForkBool (treesOfLeaves 7) =
      [ S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S),
        S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S) ⋅ S,
        S ⋅ (S ⋅ S ⋅ S ⋅ S) ⋅ S ⋅ S ] := rfl

private theorem le_7_not_strict_diamond_eq :
    filterList (fun t => !strictStepDiamondBool t) (treesUpToLeaves 7) =
      [ S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S) ] := rfl

/-- **Deterministic 1-Step Rewriting for `leaves ≤ 6`**:
    Every closed pure-`S` term with `leaves t ≤ 6` (`65` terms) has at most one 1-step reduct. -/
theorem step_deterministic_le_6 {t b c : Term}
    (hv : noVars t = true) (hl : leaves t ≤ 6) (hb : Step t b) (hc : Step t c) : b = c := by
  exact if heq : b = c then heq
  else by
    exfalso
    have hm := (mem_treesUpToLeaves_iff 6 t).mpr ⟨hv, hl⟩
    have hnf := listAll_sound le_6_no_fork_chk hm
    rw [(hasMultiwayForkBool_iff t).mpr ⟨b, c, heq, hb, hc⟩] at hnf
    cases hnf

/-- **Exact Size-7 Multiway Fork Classification (`3` Witnesses)**. -/
theorem size_7_multiway_fork_iff {t : Term} (hv : noVars t = true) (hl : leaves t = 7) :
    HasMultiwayFork t ↔
      (t = S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S) ∨
       t = S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S) ⋅ S ∨
       t = S ⋅ (S ⋅ S ⋅ S ⋅ S) ⋅ S ⋅ S) := by
  rw [← hasMultiwayForkBool_iff]
  have hm := treesOfLeaves_complete hv hl
  have hf := mem_witnesses_iff_of_filter_eq size_7_forks_eq hm
  rw [mem_triple_iff] at hf
  exact hf

/-- **Unique Minimal Strict 1-Step `Step` Diamond Counterexample (`leaves ≤ 7`)**:
    Across all `197` closed pure-`S` terms with `leaves t ≤ 7`, `StrictStepDiamondAt t` fails
    **if and only if** `t = S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S)`. -/
theorem le_7_not_strict_step_diamond_iff {t : Term} (hv : noVars t = true) (hl : leaves t ≤ 7) :
    ¬ StrictStepDiamondAt t ↔ t = S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S) := by
  have hm := (mem_treesUpToLeaves_iff 7 t).mpr ⟨hv, hl⟩
  have hf := mem_witnesses_iff_of_filter_eq le_7_not_strict_diamond_eq hm
  rw [mem_singleton_iff] at hf
  rw [← hf]
  cases hb : strictStepDiamondBool t with
  | true =>
    exact ⟨fun hnot => False.elim (hnot ((strictStepDiamondBool_iff t).mp hb)), (fun h => by cases h)⟩
  | false =>
    exact ⟨fun _ => rfl, (fun _ hd => by rw [(strictStepDiamondBool_iff t).mpr hd] at hb; cases hb)⟩

/-- **Theorem F (Unified Confluence, Parallel 1-Step Diamond, and Small-Term Multiway Sharpness)**:
    Combines universal `ParStep` 1-step triangle/diamond (`completeDev`), universal Newman local confluence
    and Church–Rosser confluence (`church_rosser`), deterministic `Step` for `leaves ≤ 6`, exact 3-term
    multiway fork onset at `leaves = 7`, and unique minimal failure of strict 1-step `Step` diamond at
    `S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S)` (whose two 1-step `Step` reducts join in 1 `ParStep` at `completeDev`). -/
theorem theorem_F_confluence_and_diamond_thresholds :
    (∀ t b c : Term, ParStep t b → ParStep t c → ParStep b (completeDev t) ∧ ParStep c (completeDev t)) ∧
    (∀ t : Term, WeakDiamondAt t ∧ ConfluentAt t) ∧
    (∀ {t b c : Term}, noVars t = true → leaves t ≤ 6 → Step t b → Step t c → b = c) ∧
    (∀ {t : Term}, noVars t = true → leaves t = 7 →
      (HasMultiwayFork t ↔
        (t = S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S) ∨
         t = S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S) ⋅ S ∨
         t = S ⋅ (S ⋅ S ⋅ S ⋅ S) ⋅ S ⋅ S))) ∧
    (∀ {t : Term}, noVars t = true → leaves t ≤ 7 →
      (¬ StrictStepDiamondAt t ↔ t = S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S ⋅ S))) := by
  refine ⟨fun t _ _ hb hc => ⟨parStep_triangle hb, parStep_triangle hc⟩,
          fun t => ⟨fun b c hb hc => ?_, fun _ _ hb hc => church_rosser hb hc⟩,
          @step_deterministic_le_6,
          @size_7_multiway_fork_iff,
          @le_7_not_strict_step_diamond_iff⟩
  exact ⟨completeDev t,
    parStep_to_reduces (parStep_triangle (step_to_parStep hb)),
    parStep_to_reduces (parStep_triangle (step_to_parStep hc))⟩

end FormalMinimality

/-! ## Axiom Audit (Verifying Zero `Classical.choice` & Zero Custom Axioms) -/

#print axioms FormalMinimality.sn_implies_productive
#print axioms FormalMinimality.productive_implies_hasHNF
#print axioms FormalMinimality.treesOfLeaves_complete
#print axioms FormalMinimality.mem_treesOfLeaves_iff
#print axioms FormalMinimality.nodup_treesOfLeaves
#print axioms FormalMinimality.mem_oneStepReducts_iff
#print axioms FormalMinimality.size_le_3_all_normalForm
#print axioms FormalMinimality.size_4_reducible_iff
#print axioms FormalMinimality.theorem_A_universal_sn_le_6
#print axioms FormalMinimality.theorem_B_exact_size_7_classification
#print axioms FormalMinimality.le_7_non_sn_iff
#print axioms FormalMinimality.theorem_C_exact_size_8_classification
#print axioms FormalMinimality.wolfram2_exact_classification
#print axioms FormalMinimality.theorem_D_minimal_productive_non_sn_size_9
#print axioms FormalMinimality.no_rnf_without_hnf_le_8
#print axioms FormalMinimality.size_9_rnf_without_hnf_iff
#print axioms FormalMinimality.minimal_q31_non_convertible_bot_pairs
#print axioms FormalMinimality.theorem_F_confluence_and_diamond_thresholds
