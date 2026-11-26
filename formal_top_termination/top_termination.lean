import Std

/-!
# Waldmann's Top-Termination Theorem (Theorem 29) and Its Corollaries for Pure `S` (`CL(S)`)

100% self-contained, constructive Lean 4.33.1 formalization of **Theorem 29** of
Barendregt, Endrullis, Klop, and Waldmann (2018), *"Dance of the Starlings"* (p. 92;
originally proved by Johannes Waldmann, *"The Combinator S"*, *Information and Computation*
159:2–21, 2000), together with its structural and algorithmic corollaries:

1. **Global Multiway Potential Theorem (`nuHN_step_le` & `topTerminating_of_evalHN_ne_hn34`)**:
   The 35-state Head Normalization `S`-algebra `A_HN` paired with the truncated integer
   potential `nuHN` is weakly decreasing under **all** contextual `S`-steps (even inside
   right arguments and `.hn34` subterms) and strictly decreases by `≥ 1` on every head
   (in particular, root) contraction whenever `evalHN t ≠ .hn34`.
2. **Waldmann's Top-Termination Theorem (`waldmann_theorem_29_top_termination`)**:
   Every pure `S`-term `t` (both **closed and open**) is constructively top-terminating
   (`Acc (fun b a => RelRootStep a b) t`), i.e., `SN(→_root / →_nonroot)` holds globally.
3. **Infinite Reduction Sequence Formulations (`no_infinite_root_reduction_sequence` &
   `no_infinite_indexed_root_steps`)**:
   No infinite `S`-reduction sequence `t_0 → t_1 → t_2 → ...` can perform root contractions
   infinitely often.
4. **Absence of Mute Pure `S`-Terms (`no_mute_pure_s_terms`, Theorem 29(i))**:
   No closed or open pure `S`-term is mute (root-active).
5. **Constructive Root Normal Form Theorem & Total Normalizer (`toRNF`, `toRNF_spec`,
   `every_closed_sterm_has_rnf`, Theorem 29(ii) & Footnote 4)**:
   Every closed pure `S`-term reduces in finitely many head steps to a Root Normal Form,
   computed by a total, postulate-free Lean function `toRNF : Term → Term`.
6. **Acyclicity & Exact `AAA` Multiway Root Census (`no_cycle_pure_s`,
   `aaa_exact_3_root_steps_all_multiway`)**:
   Pure `S`-reduction admits no cycles, and `AAA = (SSS)(SSS)(SSS)` executes at most `3`
   root contractions along every multiway reduction path, reaching RNF in 6 deterministic steps.

100% constructive kernel proof with zero `Classical.choice` (`#print axioms` uses at most `[propext]`).
-/

namespace FormalTopTermination

/-! ## 0. Boolean & Constructive Closure Helpers (Zero `Classical.choice`) -/

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true a b).mp h).1

theorem and_right {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true a b).mp h).2

theorem imp_bool {a b : Bool} (ha : a = true) (h : (!a || b) = true) : b = true := by
  rw [ha] at h
  exact h

theorem imp_decide {p : Prop} [Decidable p] {b : Bool} (hp : p) (h : (!decide p || b) = true) : b = true := by
  rw [decide_eq_true hp] at h
  exact h

private abbrev natBle (a b : Nat) : Bool := decide (a ≤ b)

private theorem natBle_sound {a b : Nat} (h : natBle a b = true) : a ≤ b :=
  of_decide_eq_true h

private theorem le_of_one_add_le_one_add {a b : Nat} (h : 1 + a ≤ 1 + b) : a ≤ b := by
  rw [Nat.add_comm 1 a, Nat.add_comm 1 b] at h
  exact Nat.le_of_succ_le_succ h

private theorem sub_lt_sub_of_lt : ∀ {B a b : Nat}, a < b → b ≤ B → B - b < B - a
  | 0, _, _, h1, h2 => by
    cases Nat.eq_zero_of_le_zero h2
    cases h1
  | B + 1, 0, b + 1, _, _ => by
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    exact Nat.lt_succ_of_le (Nat.sub_le B b)
  | B + 1, a + 1, b + 1, h1, h2 => by
    simp only [Nat.succ_sub_succ_eq_sub]
    exact sub_lt_sub_of_lt (Nat.lt_of_succ_lt_succ h1) (Nat.le_of_succ_le_succ h2)

/-! ## 1. Pure `S` Syntax, Root vs Non-Root Reduction, Invariants, and Church–Rosser -/

inductive Term where
  | s : Term
  | var : Nat → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

infixl:70 " ⋅ " => Term.app

def S : Term := Term.s
def B_comb : Term := S ⋅ S
def A_comb : Term := S ⋅ S ⋅ S
def AAA : Term := A_comb ⋅ A_comb ⋅ A_comb

def rightTower : Nat → Term
  | 0 => S
  | k + 1 => S ⋅ rightTower k

def noVars : Term → Bool
  | .s => true
  | .var _ => false
  | .app a b => noVars a && noVars b

def subst (σ : Nat → Term) : Term → Term
  | .s => .s
  | .var k => σ k
  | .app a b => subst σ a ⋅ subst σ b

def closeTerm (t : Term) : Term :=
  subst (fun _ => S) t

theorem noVars_closeTerm (t : Term) : noVars (closeTerm t) = true := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => exact (Bool.and_eq_true _ _).mpr ⟨iha, ihb⟩

def leaves : Term → Nat
  | .s => 1
  | .var _ => 1
  | .app a b => leaves a + leaves b

def rs : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app _ b => 1 + rs b

def spineLen : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app a _ => 1 + spineLen a

def headLeaf : Term → Term
  | .s => .s
  | .var k => .var k
  | .app a _ => headLeaf a

def hasSpineGe2 : Term → Bool
  | .app (.app _ _) _ => true
  | _ => false

def sPrefix : Term → Nat
  | .app .s r => 1 + sPrefix r
  | _ => 0

inductive Step : Term → Term → Prop where
  | root (x y z : Term) : Step (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : Step a a' → Step (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Step b b' → Step (a ⋅ b) (a ⋅ b')

inductive RootStep : Term → Term → Prop where
  | mk (x y z : Term) : RootStep (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))

inductive NonRootStep : Term → Term → Prop where
  | left {a a' b : Term} : Step a a' → NonRootStep (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Step b b' → NonRootStep (a ⋅ b) (a ⋅ b')

inductive StepPlus : Term → Term → Prop where
  | single {a b : Term} : Step a b → StepPlus a b
  | head {a b c : Term} : Step a b → StepPlus b c → StepPlus a c

inductive Reduces : Term → Term → Prop where
  | refl (a : Term) : Reduces a a
  | next {a b c : Term} : Step a b → Reduces b c → Reduces a c

inductive NonRootReduces : Term → Term → Prop where
  | refl (a : Term) : NonRootReduces a a
  | next {a b c : Term} : NonRootStep a b → NonRootReduces b c → NonRootReduces a c

inductive HeadStep : Term → Term → Prop where
  | root (x y z : Term) : HeadStep (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : HeadStep a a' → HeadStep (a ⋅ b) (a' ⋅ b)

inductive HeadReduces : Term → Term → Prop where
  | refl (a : Term) : HeadReduces a a
  | next {a b c : Term} : HeadStep a b → HeadReduces b c → HeadReduces a c

inductive ConvS : Term → Term → Prop where
  | refl (a : Term) : ConvS a a
  | step {a b : Term} : Step a b → ConvS a b
  | symm {a b : Term} : ConvS a b → ConvS b a
  | trans {a b c : Term} : ConvS a b → ConvS b c → ConvS a c

/-- One root contraction preceded by zero or more non-root steps (`→_nonroot^* · →_root`). -/
def RelRootStep (a b : Term) : Prop :=
  ∃ m, NonRootReduces a m ∧ RootStep m b

/-- Constructive Top-Termination (`SN(→_root / →_nonroot)`). -/
def TopTerminating (t : Term) : Prop :=
  Acc (fun b a => RelRootStep a b) t

def IsNormalForm (t : Term) : Prop := ∀ t', ¬ Step t t'
def IsClosedHNF (t : Term) : Prop := noVars t = true ∧ spineLen t ≤ 2
def HasHNF (t : Term) : Prop := ∃ h, Reduces t h ∧ spineLen h ≤ 2

/-- Root Normal Form (Barendregt et al. 2018, Definition 46(ii), p. 104):
    `t` cannot reduce to any root redex `S ⋅ x ⋅ y ⋅ z`. -/
def IsRootNormalForm (t : Term) : Prop :=
  ¬ ∃ x y z, Reduces t (S ⋅ x ⋅ y ⋅ z)

def HasRootNormalForm (t : Term) : Prop :=
  ∃ r, Reduces t r ∧ IsRootNormalForm r

/-- Mute / root-active term (Barendregt et al. 2018, p. 100 & p. 104):
    every reduct `u` of `t` can further reduce to a root redex. -/
def IsMute (t : Term) : Prop :=
  ∀ u, Reduces t u → ∃ x y z, Reduces u (S ⋅ x ⋅ y ⋅ z)

/-! ### Basic Step, Spine, Leaf, and Right-Spine Lemmas -/

theorem rootStep_to_step {a b : Term} (h : RootStep a b) : Step a b := by
  cases h with
  | mk x y z => exact Step.root x y z

theorem rootStep_to_headStep {a b : Term} (h : RootStep a b) : HeadStep a b := by
  cases h with
  | mk x y z => exact HeadStep.root x y z

theorem nonRootStep_to_step {a b : Term} (h : NonRootStep a b) : Step a b := by
  cases h with
  | left hs => exact Step.left hs
  | right hs => exact Step.right hs

theorem step_iff_root_or_nonRoot {a b : Term} :
    Step a b ↔ RootStep a b ∨ NonRootStep a b := by
  constructor
  · intro hs
    cases hs with
    | root x y z => exact Or.inl (.mk x y z)
    | left hl => exact Or.inr (.left hl)
    | right hr => exact Or.inr (.right hr)
  · intro h
    rcases h with hr | hnr
    · exact rootStep_to_step hr
    · exact nonRootStep_to_step hnr

theorem headStep_to_step {a b : Term} (h : HeadStep a b) : Step a b := by
  induction h with
  | root x y z => exact Step.root x y z
  | left _ ih => exact Step.left ih

theorem reduces_trans {a b c : Term} (h1 : Reduces a b) (h2 : Reduces b c) : Reduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact Reduces.next hs (ih h2)

theorem headReduces_trans {a b c : Term} (h1 : HeadReduces a b) (h2 : HeadReduces b c) : HeadReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact HeadReduces.next hs (ih h2)

theorem headReduces_to_reduces {a b : Term} (h : HeadReduces a b) : Reduces a b := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (headStep_to_step hs) ih

theorem headReduces_left {a a' : Term} (h : HeadReduces a a') (b : Term) : HeadReduces (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | refl _ => exact HeadReduces.refl _
  | next hs _ ih => exact HeadReduces.next (HeadStep.left hs) ih

theorem nonRootReduces_trans {a b c : Term} (h1 : NonRootReduces a b) (h2 : NonRootReduces b c) :
    NonRootReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact NonRootReduces.next hs (ih h2)

theorem nonRootReduces_to_reduces {a b : Term} (h : NonRootReduces a b) : Reduces a b := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (nonRootStep_to_step hs) ih

theorem relRootStep_to_reduces {a b : Term} (h : RelRootStep a b) : Reduces a b := by
  obtain ⟨m, hnr, hr⟩ := h
  exact reduces_trans (nonRootReduces_to_reduces hnr) (Reduces.next (rootStep_to_step hr) (Reduces.refl _))

theorem relRootStep_prepend {a b c : Term} (h1 : NonRootReduces a b) (h2 : RelRootStep b c) :
    RelRootStep a c := by
  obtain ⟨m, hbm, hmc⟩ := h2
  exact ⟨m, nonRootReduces_trans h1 hbm, hmc⟩

theorem reduces_split_first_root {a b : Term} (h : Reduces a b) :
    NonRootReduces a b ∨ ∃ c, RelRootStep a c ∧ Reduces c b := by
  induction h with
  | refl x => exact Or.inl (.refl x)
  | @next x y z hs hrest ih =>
    rcases step_iff_root_or_nonRoot.mp hs with hr | hnr
    · exact Or.inr ⟨y, ⟨x, .refl x, hr⟩, hrest⟩
    · rcases ih with hnr_rest | ⟨c, hrel, hcz⟩
      · exact Or.inl (.next hnr hnr_rest)
      · exact Or.inr ⟨c, relRootStep_prepend (.next hnr (.refl y)) hrel, hcz⟩

theorem reduces_left {a a' : Term} (h : Reduces a a') (b : Term) : Reduces (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (Step.left hs) ih

theorem reduces_right {b b' : Term} (a : Term) (h : Reduces b b') : Reduces (a ⋅ b) (a ⋅ b') := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (Step.right hs) ih

theorem reduces_app {a a' b b' : Term} (ha : Reduces a a') (hb : Reduces b b') :
    Reduces (a ⋅ b) (a' ⋅ b') :=
  reduces_trans (reduces_left ha b) (reduces_right a' hb)

theorem nonRootReduces_app_inv {m n : Term} (h : NonRootReduces m n) :
    ∀ a b, m = a ⋅ b → ∃ a' b', n = a' ⋅ b' ∧ Reduces a a' ∧ Reduces b b' := by
  induction h with
  | refl _ =>
    intro a b hm
    exact ⟨a, b, hm, Reduces.refl a, Reduces.refl b⟩
  | @next _ m1 _ hs _ ih =>
    intro a b hm
    subst hm
    cases hs with
    | @left _ a1 _ ha1 =>
      obtain ⟨a', b', hn, hra, hrb⟩ := ih a1 b rfl
      exact ⟨a', b', hn, Reduces.next ha1 hra, hrb⟩
    | @right _ _ b1 hb1 =>
      obtain ⟨a', b', hn, hra, hrb⟩ := ih a b1 rfl
      exact ⟨a', b', hn, hra, Reduces.next hb1 hrb⟩

theorem relRootStep_app_inv {a b u : Term} (h : RelRootStep (a ⋅ b) u) :
    ∃ x y z, Reduces a (S ⋅ x ⋅ y) ∧ Reduces b z ∧ u = (x ⋅ z) ⋅ (y ⋅ z) := by
  obtain ⟨m, hnr, hr⟩ := h
  obtain ⟨a', b', hm, hra, hrb⟩ := nonRootReduces_app_inv hnr a b rfl
  cases hr with
  | mk x y z =>
    injection hm with ha' hb'
    subst ha'; subst hb'
    exact ⟨x, y, z, hra, hrb, rfl⟩

theorem relRootStep_s_false {u : Term} (h : RelRootStep S u) : False := by
  obtain ⟨m, hnr, hr⟩ := h
  cases hnr with
  | refl _ => cases hr
  | next hs _ => cases hs

theorem relRootStep_var_false {k : Nat} {u : Term} (h : RelRootStep (.var k) u) : False := by
  obtain ⟨m, hnr, hr⟩ := h
  cases hnr with
  | refl _ => cases hr
  | next hs _ => cases hs

theorem noVars_step {a b : Term} (h : Step a b) : noVars a = true → noVars b = true := by
  induction h with
  | root x y z =>
    simp only [S, noVars, Bool.and_eq_true]
    intro ⟨⟨⟨_, hx⟩, hy⟩, hz⟩
    exact ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
  | left _ ih =>
    simp only [noVars, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    exact ⟨ih ha, hb⟩
  | right _ ih =>
    simp only [noVars, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    exact ⟨ha, ih hb⟩

theorem noVars_reduces {a b : Term} (h : Reduces a b) : noVars a = true → noVars b = true := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (noVars_step hs hv)

theorem subst_step (σ : Nat → Term) {a b : Term} (h : Step a b) : Step (subst σ a) (subst σ b) := by
  induction h with
  | root x y z => exact Step.root (subst σ x) (subst σ y) (subst σ z)
  | left _ ih => exact Step.left ih
  | right _ ih => exact Step.right ih

theorem subst_nonRootStep (σ : Nat → Term) {a b : Term} (h : NonRootStep a b) :
    NonRootStep (subst σ a) (subst σ b) := by
  cases h with
  | left hs => exact NonRootStep.left (subst_step σ hs)
  | right hs => exact NonRootStep.right (subst_step σ hs)

theorem subst_nonRootReduces (σ : Nat → Term) {a b : Term} (h : NonRootReduces a b) :
    NonRootReduces (subst σ a) (subst σ b) := by
  induction h with
  | refl _ => exact NonRootReduces.refl _
  | next hs _ ih => exact NonRootReduces.next (subst_nonRootStep σ hs) ih

theorem subst_rootStep (σ : Nat → Term) {a b : Term} (h : RootStep a b) :
    RootStep (subst σ a) (subst σ b) := by
  cases h with
  | mk x y z => exact RootStep.mk (subst σ x) (subst σ y) (subst σ z)

theorem relRootStep_closeTerm {a b : Term} (h : RelRootStep a b) :
    RelRootStep (closeTerm a) (closeTerm b) := by
  obtain ⟨m, hnr, hr⟩ := h
  exact ⟨closeTerm m, subst_nonRootReduces _ hnr, subst_rootStep _ hr⟩

/-! ### Leaves, Right-Spine Monotonicity (`rs`), and `sPrefix` Exact Invariance -/

theorem leaves_pos (t : Term) : 1 ≤ leaves t := by
  induction t with
  | s => exact Nat.le_refl 1
  | var _ => exact Nat.le_refl 1
  | app _ _ _ ihb => exact Nat.le_trans ihb (Nat.le_add_left _ _)

private theorem leaves_root_le (x y z : Nat) (hz : 1 ≤ z) :
    1 + x + y + z ≤ (x + z) + (y + z) := by
  have h1x : 1 + x ≤ x + z := by
    rw [Nat.add_comm x z]
    exact Nat.add_le_add_right hz x
  rw [Nat.add_assoc (1 + x) y z]
  exact Nat.add_le_add_right h1x (y + z)

theorem leaves_mono_step {a b : Term} (h : Step a b) : leaves a ≤ leaves b := by
  induction h with
  | root x y z => exact leaves_root_le (leaves x) (leaves y) (leaves z) (leaves_pos z)
  | left _ ih => exact Nat.add_le_add_right ih _
  | right _ ih => exact Nat.add_le_add_left ih _

theorem step_ne_s {a b : Term} (h : Step a b) : b ≠ .s := by
  intro hb
  subst hb
  have hle := leaves_mono_step h
  cases a with
  | s => cases h
  | var _ => cases h
  | app l r =>
    have h2 : 2 ≤ leaves l + leaves r := Nat.add_le_add (leaves_pos l) (leaves_pos r)
    exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_trans h2 hle))

private theorem rootStep_disjoint_aux {a b x y z : Term} (hnr : NonRootStep a b)
    (ha : a = S ⋅ x ⋅ y ⋅ z) (hb : b = (x ⋅ z) ⋅ (y ⋅ z)) : False := by
  cases hnr with
  | @left l l' r _ =>
    injection ha with _ hr_eq
    rw [hr_eq] at hb
    injection hb with _ hrz
    have hbad : 0 + leaves z = leaves y + leaves z := by
      rw [Nat.zero_add]
      exact congrArg leaves hrz
    have hy0 : 0 = leaves y := Nat.add_right_cancel hbad
    have hpos := leaves_pos y
    rw [← hy0] at hpos
    cases hpos
  | @right l r r' _ =>
    injection ha with hl_eq _
    rw [hl_eq] at hb
    injection hb with hlz _
    injection hlz with hsx _
    have hbad : 1 + leaves x = 0 + leaves x := by
      rw [Nat.zero_add]
      exact congrArg leaves hsx
    have h10 : 1 = 0 := Nat.add_right_cancel hbad
    cases h10

theorem rootStep_disjoint_nonRootStep {a b : Term} (hr : RootStep a b) (hnr : NonRootStep a b) : False := by
  cases hr with
  | mk x y z => exact rootStep_disjoint_aux hnr rfl rfl

theorem rs_mono_step {a b : Term} (h : Step a b) : rs a ≤ rs b := by
  induction h with
  | root x y z =>
    change 1 + rs z ≤ 1 + (1 + rs z)
    exact Nat.le_add_left (1 + rs z) 1
  | left _ _ => exact Nat.le_refl _
  | right _ ih => exact Nat.add_le_add_left ih 1

theorem rs_mono_reduces {a b : Term} (h : Reduces a b) : rs a ≤ rs b := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | next hs _ ih => exact Nat.le_trans (rs_mono_step hs) ih

theorem rs_mono_nonRootReduces {a b : Term} (h : NonRootReduces a b) : rs a ≤ rs b :=
  rs_mono_reduces (nonRootReduces_to_reduces h)

theorem rs_rootStep_eq {a b : Term} (h : RootStep a b) : rs b = rs a + 1 := by
  cases h with
  | mk x y z =>
    change 1 + (1 + rs z) = (1 + rs z) + 1
    exact Nat.add_comm 1 (1 + rs z)

theorem rs_relRootStep_lt {a b : Term} (h : RelRootStep a b) : rs a + 1 ≤ rs b := by
  obtain ⟨m, hnr, hr⟩ := h
  rw [rs_rootStep_eq hr]
  exact Nat.add_le_add_right (rs_mono_nonRootReduces hnr) 1

private theorem sPrefix_non_s_app {l r : Term} (hl : l ≠ .s) : sPrefix (l ⋅ r) = 0 := by
  cases l with
  | s => exfalso; exact hl rfl
  | var _ => rfl
  | app _ _ => rfl

theorem sPrefix_step {a b : Term} (h : Step a b) : sPrefix b = sPrefix a := by
  induction h with
  | root x y z => rfl
  | @left l l' r hl _ =>
    have hl_ne : l ≠ .s := by intro heq; subst heq; cases hl
    have hl'_ne : l' ≠ .s := step_ne_s hl
    rw [sPrefix_non_s_app hl_ne, sPrefix_non_s_app hl'_ne]
  | @right l r r' _ ih =>
    cases l with
    | s => exact congrArg (1 + ·) ih
    | var _ => rfl
    | app _ _ => rfl

theorem sPrefix_reduces {a b : Term} (h : Reduces a b) : sPrefix b = sPrefix a := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact ih.trans (sPrefix_step hs)

/-! ### Spine Preservation, No Dynamic 1-HNF, and Last-Root-Step Dichotomy -/

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
  · intro h; have hge := spineGe2_preserved_reduces h rfl; cases hge
  · intro h; have hge := spineGe2_preserved_reduces h rfl; cases hge

theorem s_app_reduces_inv {a b : Term} (h : Reduces a b) :
    ∀ x w, a = S ⋅ x → b = S ⋅ w → Reduces x w := by
  induction h with
  | refl _ =>
    intro x w h1 h2
    have heq := h1.symm.trans h2
    injection heq with _ hxw
    subst hxw
    exact Reduces.refl _
  | @next _ _ _ hs _ ih =>
    intro x w ha hb
    subst ha
    cases hs with
    | left hl => cases hl
    | @right _ _ x' hx' => exact Reduces.next hx' (ih x' w rfl hb)

theorem s_app_reduces_any {m n : Term} (h : Reduces m n) :
    ∀ x, m = S ⋅ x → ∃ x', n = S ⋅ x' ∧ Reduces x x' := by
  induction h with
  | refl _ => intro x hm; exact ⟨x, hm, Reduces.refl x⟩
  | @next _ _ _ hs _ ih =>
    intro x hm
    subst hm
    cases hs with
    | left hl => cases hl
    | @right _ _ x1 hx1 =>
      obtain ⟨x', hn, hrx⟩ := ih x1 rfl
      exact ⟨x', hn, Reduces.next hx1 hrx⟩

theorem s2_app_reduces_any {m n : Term} (h : Reduces m n) :
    ∀ x y, m = S ⋅ x ⋅ y → ∃ x' y', n = S ⋅ x' ⋅ y' ∧ Reduces x x' ∧ Reduces y y' := by
  induction h with
  | refl _ => intro x y hm; exact ⟨x, y, hm, Reduces.refl x, Reduces.refl y⟩
  | @next _ _ _ hs _ ih =>
    intro x y hm
    subst hm
    cases hs with
    | @left _ l1 _ hl =>
      cases hl with
      | left hll => cases hll
      | @right _ _ x1 hx1 =>
        obtain ⟨x', y', hn, hrx, hry⟩ := ih x1 y rfl
        exact ⟨x', y', hn, Reduces.next hx1 hrx, hry⟩
    | @right _ _ y1 hy1 =>
      obtain ⟨x', y', hn, hrx, hry⟩ := ih x y1 rfl
      exact ⟨x', y', hn, hrx, Reduces.next hy1 hry⟩

theorem var_app_not_reduces_s_app {a b : Term} (h : Reduces a b) :
    ∀ k x w, a = Term.var k ⋅ x → b = S ⋅ w → False := by
  induction h with
  | refl _ =>
    intro k x w h1 h2
    have heq := h1.symm.trans h2
    injection heq with hk _
    cases hk
  | @next _ _ _ hs _ ih =>
    intro k x w ha hb
    subst ha
    cases hs with
    | left hl => cases hl
    | @right _ _ x' _ => exact ih k x' w rfl hb

theorem app_reduces_to_hnf1_iff (f x w : Term) (h : Reduces (f ⋅ x) (S ⋅ w)) :
    f = S ∧ Reduces x w := by
  cases f with
  | s => exact ⟨rfl, s_app_reduces_inv h x w rfl rfl⟩
  | var k => exfalso; exact var_app_not_reduces_s_app h k x w rfl rfl
  | app f1 f2 => exfalso; exact (no_dynamic_hnf1 f1 f2 x w).1 h

private theorem s_not_reduces_app {a b : Term} (h : Reduces a b) :
    ∀ u v, a = .s → b = u ⋅ v → False := by
  induction h with
  | refl _ => intro u v h1 h2; cases h1.symm.trans h2
  | next hs _ _ => intro _ _ h1 _; subst h1; cases hs

private theorem var_not_reduces_app {a b : Term} (h : Reduces a b) :
    ∀ k u v, a = .var k → b = u ⋅ v → False := by
  induction h with
  | refl _ => intro k u v h1 h2; cases h1.symm.trans h2
  | next hs _ _ => intro _ _ _ h1 _; subst h1; cases hs

theorem reduces_to_s1_inv {t w : Term} (h : Reduces t (S ⋅ w)) :
    ∃ p, t = S ⋅ p ∧ Reduces p w := by
  cases t with
  | s => exfalso; exact s_not_reduces_app h S w rfl rfl
  | var k => exfalso; exact var_not_reduces_app h k S w rfl rfl
  | app f p =>
    have ⟨hf, hp⟩ := app_reduces_to_hnf1_iff f p w h
    subst hf
    exact ⟨p, rfl, hp⟩

/-- **Last-Root-Step Dichotomy Lemma**:
    Whenever `a ⋅ b →* S ⋅ x ⋅ y`, either zero root contractions occur (`a →* S ⋅ x` and `b →* y`),
    or there is a last root contraction `(S ⋅ S ⋅ v) ⋅ w → (S ⋅ w) ⋅ (v ⋅ w)` along the path with
    `a ⋅ b →* (S ⋅ S ⋅ v) ⋅ w`, `w →* x`, and `v ⋅ w →* y`. -/
theorem app_reduces_s2_dichotomy {m n : Term} (h : Reduces m n) :
    ∀ a b x y, m = a ⋅ b → n = S ⋅ x ⋅ y →
      (Reduces a (S ⋅ x) ∧ Reduces b y) ∨
      (∃ v w, Reduces (a ⋅ b) ((S ⋅ S ⋅ v) ⋅ w) ∧ Reduces w x ∧ Reduces (v ⋅ w) y) := by
  induction h with
  | refl _ =>
    intro a b x y hm hn
    have heq := hm.symm.trans hn
    injection heq with ha hb
    subst ha; subst hb
    exact Or.inl ⟨Reduces.refl _, Reduces.refl _⟩
  | @next _ m1 _ hs _ ih =>
    intro a b x y hm hn
    subst hm
    cases hs with
    | @left _ a1 _ ha1 =>
      rcases ih a1 b x y rfl hn with ⟨hra, hrb⟩ | ⟨v, w, hm1, hw, hvw⟩
      · exact Or.inl ⟨Reduces.next ha1 hra, hrb⟩
      · exact Or.inr ⟨v, w, Reduces.next (Step.left ha1) hm1, hw, hvw⟩
    | @right _ _ b1 hb1 =>
      rcases ih a b1 x y rfl hn with ⟨hra, hrb⟩ | ⟨v, w, hm1, hw, hvw⟩
      · exact Or.inl ⟨hra, Reduces.next hb1 hrb⟩
      · exact Or.inr ⟨v, w, Reduces.next (Step.right hb1) hm1, hw, hvw⟩
    | @root p q _ =>
      rcases ih (p ⋅ b) (q ⋅ b) x y rfl hn with ⟨hpb, hqb⟩ | ⟨v, w, hm1, hw, hvw⟩
      · have ⟨hp, hbx⟩ := app_reduces_to_hnf1_iff p b x hpb
        subst hp
        exact Or.inr ⟨q, b, Reduces.refl _, hbx, hqb⟩
      · exact Or.inr ⟨v, w, Reduces.next (Step.root p q b) hm1, hw, hvw⟩

/-! ### Takahashi Parallel Reduction and Church–Rosser (`CL(S) |= CR`) -/

inductive ParStep : Term → Term → Prop where
  | s : ParStep .s .s
  | var (k : Nat) : ParStep (.var k) (.var k)
  | app {a a' b b' : Term} : ParStep a a' → ParStep b b' → ParStep (a ⋅ b) (a' ⋅ b')
  | beta {x x' y y' z z' : Term} :
      ParStep x x' → ParStep y y' → ParStep z z' →
      ParStep (S ⋅ x ⋅ y ⋅ z) ((x' ⋅ z') ⋅ (y' ⋅ z'))

theorem parStep_refl (t : Term) : ParStep t t := by
  induction t with
  | s => exact ParStep.s
  | var k => exact ParStep.var k
  | app _ _ iha ihb => exact ParStep.app iha ihb

theorem step_to_parStep {a b : Term} (h : Step a b) : ParStep a b := by
  induction h with
  | root x y z => exact ParStep.beta (parStep_refl x) (parStep_refl y) (parStep_refl z)
  | left _ ih => exact ParStep.app ih (parStep_refl _)
  | right _ ih => exact ParStep.app (parStep_refl _) ih

theorem parStep_to_reduces {a b : Term} (h : ParStep a b) : Reduces a b := by
  induction h with
  | s => exact Reduces.refl .s
  | var k => exact Reduces.refl (.var k)
  | app _ _ iha ihb => exact reduces_app iha ihb
  | beta _ _ _ ihx ihy ihz =>
    have h1 := reduces_app (reduces_app (reduces_right S ihx) ihy) ihz
    exact reduces_trans h1 (Reduces.next (Step.root _ _ _) (Reduces.refl _))

def completeDev : Term → Term
  | .app (.app (.app .s x) y) z =>
      (completeDev x ⋅ completeDev z) ⋅ (completeDev y ⋅ completeDev z)
  | .app a b => completeDev a ⋅ completeDev b
  | .s => .s
  | .var k => .var k

private theorem completeDev_non_redex (a b : Term) (hnot : ∀ x y, a ≠ S ⋅ x ⋅ y) :
    completeDev (a ⋅ b) = completeDev a ⋅ completeDev b := by
  cases a with
  | s => rfl
  | var _ => rfl
  | app a1 y =>
    cases a1 with
    | s => rfl
    | var _ => rfl
    | app a2 x =>
      cases a2 with
      | s => exfalso; exact hnot x y rfl
      | var _ => rfl
      | app _ _ => rfl

theorem parStep_triangle {a b : Term} (h : ParStep a b) : ParStep b (completeDev a) := by
  induction h with
  | s => exact ParStep.s
  | var k => exact ParStep.var k
  | @beta x x' y y' z z' _ _ _ ihx ihy ihz =>
    change ParStep ((x' ⋅ z') ⋅ (y' ⋅ z'))
      ((completeDev x ⋅ completeDev z) ⋅ (completeDev y ⋅ completeDev z))
    exact ParStep.app (ParStep.app ihx ihz) (ParStep.app ihy ihz)
  | @app a a' b b' ha _ iha ihb =>
    cases a with
    | s => cases ha; exact ParStep.app ParStep.s ihb
    | var k => cases ha; exact ParStep.app (ParStep.var k) ihb
    | app a1 y =>
      cases a1 with
      | s =>
        cases ha with
        | @app _ _ _ y' hs _ =>
          cases hs
          have ihy : ParStep y' (completeDev y) := by
            change ParStep (Term.s ⋅ y') (Term.s ⋅ completeDev y) at iha
            cases iha with | app _ ihy' => exact ihy'
          exact ParStep.app (ParStep.app ParStep.s ihy) ihb
      | var k =>
        rw [completeDev_non_redex (.var k ⋅ y) b (fun _ _ h => by injection h with h1 _; cases h1)]
        exact ParStep.app iha ihb
      | app a2 x =>
        cases a2 with
        | var k =>
          rw [completeDev_non_redex (.var k ⋅ x ⋅ y) b (fun _ _ h => by
            injection h with h1 _; injection h1 with h2 _; cases h2)]
          exact ParStep.app iha ihb
        | app u v =>
          rw [completeDev_non_redex (u ⋅ v ⋅ x ⋅ y) b (fun _ _ h => by
            injection h with h1 _; injection h1 with h2 _; cases h2)]
          exact ParStep.app iha ihb
        | s =>
          change ParStep (a' ⋅ b') ((completeDev x ⋅ completeDev b) ⋅ (completeDev y ⋅ completeDev b))
          cases ha with
          | @app _ _ _ y' ha1 _ =>
            cases ha1 with
            | @app _ _ _ x' hs _ =>
              cases hs
              have ⟨ihx, ihy⟩ : ParStep x' (completeDev x) ∧ ParStep y' (completeDev y) := by
                change ParStep (S ⋅ x' ⋅ y') (S ⋅ completeDev x ⋅ completeDev y) at iha
                cases iha with
                | app hsx ihy' =>
                  cases hsx with | app _ ihx' => exact ⟨ihx', ihy'⟩
              exact ParStep.beta ihx ihy ihb

inductive ParReduces : Term → Term → Prop where
  | refl (a : Term) : ParReduces a a
  | next {a b c : Term} : ParStep a b → ParReduces b c → ParReduces a c

private theorem reduces_to_parReduces {a b : Term} (h : Reduces a b) : ParReduces a b := by
  induction h with
  | refl _ => exact ParReduces.refl _
  | next hs _ ih => exact ParReduces.next (step_to_parStep hs) ih

private theorem parReduces_to_reduces {a b : Term} (h : ParReduces a b) : Reduces a b := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact reduces_trans (parStep_to_reduces hs) ih

private theorem parStep_strip {a b c : Term} (hab : ParStep a b) (hac : ParReduces a c) :
    ∃ d, ParReduces b d ∧ ParStep c d := by
  induction hac generalizing b with
  | refl _ => exact ⟨b, ParReduces.refl b, hab⟩
  | @next _ a1 _ ha1 _ ih =>
    have ha1m := parStep_triangle ha1
    have hbm := parStep_triangle hab
    obtain ⟨d, hmd, hcd⟩ := ih ha1m
    exact ⟨d, ParReduces.next hbm hmd, hcd⟩

private theorem parReduces_confluence {a b c : Term} (hab : ParReduces a b) (hac : ParReduces a c) :
    ∃ d, ParReduces b d ∧ ParReduces c d := by
  induction hab generalizing c with
  | refl _ => exact ⟨c, hac, ParReduces.refl c⟩
  | @next _ a1 _ ha1 _ ih =>
    obtain ⟨m, ha1m, hcm⟩ := parStep_strip ha1 hac
    obtain ⟨d, hbd, hmd⟩ := ih ha1m
    exact ⟨d, hbd, ParReduces.next hcm hmd⟩

/-- **Church–Rosser Theorem (`CL(S) |= CR`)** for all pure `S`-terms. -/
theorem church_rosser {a b c : Term} (hab : Reduces a b) (hac : Reduces a c) :
    ∃ d, Reduces b d ∧ Reduces c d := by
  obtain ⟨d, hbd, hcd⟩ := parReduces_confluence (reduces_to_parReduces hab) (reduces_to_parReduces hac)
  exact ⟨d, parReduces_to_reduces hbd, parReduces_to_reduces hcd⟩

theorem s2_common_reduct {m x1 y1 x2 y2 : Term}
    (h1 : Reduces m (S ⋅ x1 ⋅ y1)) (h2 : Reduces m (S ⋅ x2 ⋅ y2)) :
    ∃ dx dy, Reduces x1 dx ∧ Reduces x2 dx ∧ Reduces y1 dy ∧ Reduces y2 dy := by
  obtain ⟨d, hd1, hd2⟩ := church_rosser h1 h2
  obtain ⟨dx, dy, hd_eq, hx1, hy1⟩ := s2_app_reduces_any hd1 x1 y1 rfl
  obtain ⟨dx', dy', hd_eq', hx2, hy2⟩ := s2_app_reduces_any hd2 x2 y2 rfl
  have heq := hd_eq.symm.trans hd_eq'
  injection heq with hxeq hyeq
  injection hxeq with _ hdx
  subst hdx; subst hyeq
  exact ⟨dx, dy, hx1, hx2, hy1, hy2⟩

/-! ## 2. Exact 35-State Head Normalization Algebra `A_HN` & Global Multiway Potential `nuHN` -/

inductive StateHN where
  | hn0 | hn1 | hn2 | hn3 | hn4 | hn5 | hn6 | hn7 | hn8 | hn9 | hn10 | hn11 | hn12 | hn13 | hn14 | hn15 | hn16 | hn17 | hn18 | hn19 | hn20 | hn21 | hn22 | hn23 | hn24 | hn25 | hn26 | hn27 | hn28 | hn29 | hn30 | hn31 | hn32 | hn33 | hn34
  deriving DecidableEq, Repr

def stateHNToNat : StateHN → Nat
  | .hn0 => 0
  | .hn1 => 1
  | .hn2 => 2
  | .hn3 => 3
  | .hn4 => 4
  | .hn5 => 5
  | .hn6 => 6
  | .hn7 => 7
  | .hn8 => 8
  | .hn9 => 9
  | .hn10 => 10
  | .hn11 => 11
  | .hn12 => 12
  | .hn13 => 13
  | .hn14 => 14
  | .hn15 => 15
  | .hn16 => 16
  | .hn17 => 17
  | .hn18 => 18
  | .hn19 => 19
  | .hn20 => 20
  | .hn21 => 21
  | .hn22 => 22
  | .hn23 => 23
  | .hn24 => 24
  | .hn25 => 25
  | .hn26 => 26
  | .hn27 => 27
  | .hn28 => 28
  | .hn29 => 29
  | .hn30 => 30
  | .hn31 => 31
  | .hn32 => 32
  | .hn33 => 33
  | .hn34 => 34

def deltaHN : StateHN → StateHN → StateHN
  | .hn0, y => match y with | .hn0 => .hn1 | .hn1 => .hn2 | .hn2 => .hn3 | .hn3 => .hn4 | .hn4 => .hn5 | .hn5 => .hn5 | .hn6 => .hn7 | .hn7 => .hn8 | .hn8 => .hn9 | .hn11 => .hn12 | .hn12 => .hn8 | .hn13 => .hn12 | .hn14 => .hn15 | .hn15 => .hn8 | .hn16 => .hn8 | .hn17 => .hn9 | .hn18 => .hn19 | .hn19 => .hn9 | .hn20 => .hn21 | .hn21 => .hn9 | .hn26 => .hn27 | .hn28 => .hn9 | .hn29 => .hn9 | .hn30 => .hn9 | .hn31 => .hn27 | .hn32 => .hn9 | _ => .hn10
  | .hn1, y => match y with | .hn0 => .hn6 | .hn1 => .hn11 | _ => .hn13
  | .hn2, y => match y with | .hn0 => .hn14 | .hn1 => .hn16 | .hn2 => .hn8 | .hn3 => .hn9 | .hn6 => .hn17 | .hn7 => .hn9 | .hn11 => .hn17 | .hn12 => .hn9 | .hn13 => .hn17 | _ => .hn10
  | .hn3, y => match y with | .hn0 => .hn18 | _ => .hn20
  | .hn4, y => match y with | .hn0 => .hn8 | _ => .hn10
  | .hn5, _ => .hn10
  | .hn6, y => match y with | .hn0 => .hn11 | .hn1 => .hn8 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn22 | .hn11 => .hn22 | .hn13 => .hn22 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn7, y => match y with | .hn0 => .hn26 | .hn1 => .hn28 | .hn2 => .hn29 | .hn3 => .hn22 | .hn6 => .hn30 | .hn7 => .hn22 | .hn11 => .hn30 | .hn12 => .hn22 | .hn13 => .hn30 | _ => .hn24
  | .hn8, y => match y with | .hn0 => .hn24 | _ => .hn23
  | .hn9, y => match y with | .hn0 => .hn25 | _ => .hn23
  | .hn10, _ => .hn23
  | .hn11, y => match y with | .hn0 => .hn13 | .hn1 => .hn17 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn30 | .hn11 => .hn29 | .hn13 => .hn29 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn12, y => match y with | .hn0 => .hn31 | .hn1 => .hn29 | .hn2 => .hn29 | .hn3 => .hn22 | .hn6 => .hn29 | .hn7 => .hn22 | .hn11 => .hn29 | .hn12 => .hn22 | .hn13 => .hn29 | _ => .hn24
  | .hn13, y => match y with | .hn0 => .hn13 | .hn1 => .hn10 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn24 | .hn11 => .hn24 | .hn13 => .hn24 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn14, y => match y with | .hn0 => .hn8 | .hn1 => .hn20 | .hn2 => .hn10 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | _ => .hn23
  | .hn15, _ => .hn24
  | .hn16, y => match y with | .hn0 => .hn22 | .hn1 => .hn29 | _ => .hn24
  | .hn17, y => match y with | .hn0 => .hn22 | _ => .hn23
  | .hn18, y => match y with | .hn0 => .hn20 | .hn1 => .hn24 | _ => .hn23
  | .hn19, y => match y with | .hn0 => .hn32 | _ => .hn25
  | .hn20, y => match y with | .hn1 => .hn24 | _ => .hn23
  | .hn21, y => match y with | .hn0 => .hn33 | _ => .hn23
  | .hn22, y => match y with | .hn0 => .hn25 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn23, _ => .hn34
  | .hn24, y => match y with | .hn0 => .hn23 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn25, y => match y with | .hn0 => .hn23 | _ => .hn34
  | .hn26, y => match y with | .hn0 => .hn17 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn27, _ => .hn25
  | .hn28, y => match y with | .hn0 => .hn30 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn29, y => match y with | .hn0 => .hn24 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn30, y => match y with | .hn0 => .hn29 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn31, y => match y with | .hn0 => .hn10 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn32, y => match y with | .hn0 => .hn24 | .hn1 => .hn23 | _ => .hn34
  | .hn33, y => match y with | .hn1 => .hn23 | _ => .hn34
  | .hn34, _ => .hn34

def checkAll1_StateHN (p : StateHN → Bool) : Bool :=
  (((((p .hn0 && p .hn1) && (p .hn2 && p .hn3)) && ((p .hn4 && p .hn5) && (p .hn6 && p .hn7))) && (((p .hn8 && p .hn9) && (p .hn10 && p .hn11)) && ((p .hn12 && p .hn13) && (p .hn14 && (p .hn15 && p .hn16))))) && ((((p .hn17 && p .hn18) && (p .hn19 && p .hn20)) && ((p .hn21 && p .hn22) && (p .hn23 && (p .hn24 && p .hn25)))) && (((p .hn26 && p .hn27) && (p .hn28 && p .hn29)) && ((p .hn30 && p .hn31) && (p .hn32 && (p .hn33 && p .hn34))))))

theorem checkAll1_StateHN_sound (p : StateHN → Bool)
    (h : checkAll1_StateHN p = true) (x : StateHN) : p x = true :=
  match x with
  | .hn0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .hn1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .hn2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .hn3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .hn4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .hn5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .hn6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .hn7 => (and_right (and_right (and_right (and_left (and_left h)))))
  | .hn8 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .hn9 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .hn10 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .hn11 => (and_right (and_right (and_left (and_right (and_left h)))))
  | .hn12 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .hn13 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .hn14 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .hn15 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .hn16 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .hn17 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .hn18 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .hn19 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .hn20 => (and_right (and_right (and_left (and_left (and_right h)))))
  | .hn21 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .hn22 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .hn23 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .hn24 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .hn25 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .hn26 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .hn27 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .hn28 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .hn29 => (and_right (and_right (and_left (and_right (and_right h)))))
  | .hn30 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .hn31 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .hn32 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .hn33 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .hn34 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateHN (p : StateHN → StateHN → Bool) : Bool :=
  checkAll1_StateHN (fun x => checkAll1_StateHN (fun y => p x y))

theorem checkAll2_StateHN_sound (p : StateHN → StateHN → Bool)
    (h : checkAll2_StateHN p = true) (x y : StateHN) : p x y = true :=
  checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ h x) y

private theorem s_row_StateHN_0 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn0; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn0 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_1 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn1; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn1 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_2 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn2; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn2 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_3 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn3; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn3 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_4 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn4; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn4 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_5 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn5; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn5 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_6 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn6; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn6 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_7 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn7; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn7 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_8 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn8; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn8 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_9 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn9; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn9 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_10 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn10; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn10 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_11 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn11; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn11 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_12 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn12; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn12 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_13 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn13; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn13 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_14 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn14; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn14 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_15 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn15; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn15 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_16 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn16; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn16 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_17 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn17; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn17 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_18 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn18; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn18 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_19 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn19; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn19 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_20 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn20; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn20 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_21 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn21; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn21 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_22 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn22; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn22 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_23 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn23; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn23 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_24 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn24; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn24 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_25 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn25; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn25 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_26 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn26; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn26 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_27 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn27; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn27 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_28 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn28; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn28 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_29 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn29; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn29 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_30 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn30; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn30 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_31 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn31; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn31 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_32 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn32; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn32 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_33 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn33; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn33 z) (deltaHN y z)))) = true := rfl
private theorem s_row_StateHN_34 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn34; let s2 := deltaHN s1 y; checkAll1_StateHN (fun z => decide (deltaHN s2 z = deltaHN (deltaHN .hn34 z) (deltaHN y z)))) = true := rfl

theorem deltaHN_s_law (x y z : StateHN) :
    deltaHN (deltaHN (deltaHN .hn0 x) y) z = deltaHN (deltaHN x z) (deltaHN y z) := by
  cases x with
  | hn0 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_0 y) z)
  | hn1 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_1 y) z)
  | hn2 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_2 y) z)
  | hn3 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_3 y) z)
  | hn4 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_4 y) z)
  | hn5 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_5 y) z)
  | hn6 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_6 y) z)
  | hn7 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_7 y) z)
  | hn8 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_8 y) z)
  | hn9 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_9 y) z)
  | hn10 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_10 y) z)
  | hn11 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_11 y) z)
  | hn12 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_12 y) z)
  | hn13 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_13 y) z)
  | hn14 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_14 y) z)
  | hn15 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_15 y) z)
  | hn16 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_16 y) z)
  | hn17 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_17 y) z)
  | hn18 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_18 y) z)
  | hn19 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_19 y) z)
  | hn20 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_20 y) z)
  | hn21 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_21 y) z)
  | hn22 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_22 y) z)
  | hn23 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_23 y) z)
  | hn24 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_24 y) z)
  | hn25 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_25 y) z)
  | hn26 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_26 y) z)
  | hn27 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_27 y) z)
  | hn28 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_28 y) z)
  | hn29 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_29 y) z)
  | hn30 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_30 y) z)
  | hn31 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_31 y) z)
  | hn32 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_32 y) z)
  | hn33 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_33 y) z)
  | hn34 => exact of_decide_eq_true (checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ s_row_StateHN_34 y) z)

private theorem deltaHN_hn34_left_chk : checkAll1_StateHN (fun y => decide (deltaHN .hn34 y = .hn34)) = true := rfl
private theorem deltaHN_ne_hn0_chk : checkAll2_StateHN (fun x y => decide (deltaHN x y ≠ .hn0)) = true := rfl
private theorem deltaHN_s1_ne34_chk : checkAll1_StateHN (fun x => decide (deltaHN .hn0 x ≠ .hn34)) = true := rfl
private theorem deltaHN_s2_ne34_chk : checkAll2_StateHN (fun x y => decide (deltaHN (deltaHN .hn0 x) y ≠ .hn34)) = true := rfl

theorem deltaHN_hn34_left (y : StateHN) : deltaHN .hn34 y = .hn34 :=
  of_decide_eq_true (checkAll1_StateHN_sound _ deltaHN_hn34_left_chk y)

theorem deltaHN_ne_hn34_left {x y : StateHN} (h : deltaHN x y ≠ .hn34) : x ≠ .hn34 := by
  intro hx; subst hx; exact h (deltaHN_hn34_left y)

theorem deltaHN_ne_hn0 (x y : StateHN) : deltaHN x y ≠ .hn0 :=
  of_decide_eq_true (checkAll2_StateHN_sound _ deltaHN_ne_hn0_chk x y)

theorem deltaHN_s1_ne_hn34 (x : StateHN) : deltaHN .hn0 x ≠ .hn34 :=
  of_decide_eq_true (checkAll1_StateHN_sound _ deltaHN_s1_ne34_chk x)

theorem deltaHN_s2_ne_hn34 (x y : StateHN) : deltaHN (deltaHN .hn0 x) y ≠ .hn34 :=
  of_decide_eq_true (checkAll2_StateHN_sound _ deltaHN_s2_ne34_chk x y)

def evalHN : Term → StateHN
  | .s => .hn0
  | .var _ => .hn0
  | .app a b => deltaHN (evalHN a) (evalHN b)

theorem evalHN_step {a b : Term} (h : Step a b) : evalHN a = evalHN b := by
  induction h with
  | root x y z => exact deltaHN_s_law (evalHN x) (evalHN y) (evalHN z)
  | left _ ih => simp only [evalHN, ih]
  | right _ ih => simp only [evalHN, ih]

theorem evalHN_reduces {a b : Term} (h : Reduces a b) : evalHN a = evalHN b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalHN_step hs).trans ih

theorem evalHN_conv {a b : Term} (h : ConvS a b) : evalHN a = evalHN b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalHN_step hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem evalHN_eq_hn0_iff {t : Term} (hv : noVars t = true) : evalHN t = .hn0 ↔ t = S := by
  cases t with
  | s => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | var _ => cases hv
  | app a b =>
    exact ⟨fun h => False.elim (deltaHN_ne_hn0 (evalHN a) (evalHN b) h), fun h => by cases h⟩

def hnA : StateHN → StateHN → Nat
  | .hn0, y => match y with | .hn9 => 0 | .hn10 => 0 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn1, y => match y with | .hn0 => 2 | .hn1 => 2 | .hn2 => 1 | .hn6 => 1 | .hn7 => 1 | .hn11 => 1 | _ => 0
  | .hn2, y => match y with | .hn0 => 2 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn3, y => match y with | .hn0 => 4 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 2 | .hn11 => 1 | .hn13 => 1 | .hn18 => 1 | _ => 0
  | .hn4, y => match y with | .hn0 => 6 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | .hn28 => 1 | _ => 0
  | .hn5, y => match y with | .hn0 => 15 | .hn1 => 7 | .hn3 => 2 | .hn6 => 4 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn6, y => match y with | .hn0 => 3 | .hn1 => 2 | .hn2 => 2 | .hn6 => 2 | .hn9 => 0 | .hn10 => 0 | .hn11 => 2 | .hn13 => 2 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn7, y => match y with | .hn0 => 5 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 1 | .hn12 => 1 | .hn13 => 1 | .hn14 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn8, y => match y with | .hn0 => 12 | .hn1 => 6 | .hn2 => 2 | .hn3 => 2 | .hn6 => 5 | .hn7 => 1 | .hn11 => 3 | .hn13 => 2 | .hn18 => 2 | _ => 0
  | .hn9, y => match y with | .hn0 => 16 | .hn1 => 6 | .hn2 => 2 | .hn3 => 1 | .hn6 => 4 | .hn7 => 1 | .hn11 => 3 | .hn13 => 2 | .hn18 => 1 | _ => 0
  | .hn10, y => match y with | .hn0 => 30 | .hn1 => 15 | .hn2 => 3 | .hn3 => 2 | .hn6 => 7 | .hn7 => 3 | .hn11 => 4 | .hn13 => 2 | .hn18 => 1 | .hn28 => 1 | _ => 0
  | .hn11, y => match y with | .hn0 => 3 | .hn1 => 5 | .hn2 => 2 | .hn6 => 2 | .hn7 => 3 | .hn9 => 0 | .hn10 => 0 | .hn11 => 3 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn12, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn13, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn6 => 4 | .hn9 => 0 | .hn10 => 0 | .hn11 => 2 | .hn13 => 2 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn14, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn6 => 2 | .hn7 => 2 | .hn11 => 2 | .hn12 => 1 | .hn13 => 1 | .hn14 => 1 | .hn15 => 1 | .hn16 => 1 | .hn18 => 1 | .hn20 => 1 | _ => 0
  | .hn15, y => match y with | .hn0 => 6 | .hn1 => 5 | .hn2 => 1 | .hn3 => 2 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn16, y => match y with | .hn0 => 6 | .hn1 => 8 | .hn2 => 3 | .hn6 => 3 | .hn7 => 3 | .hn11 => 3 | _ => 0
  | .hn17, y => match y with | .hn0 => 10 | .hn1 => 7 | .hn2 => 3 | .hn6 => 3 | .hn7 => 1 | .hn11 => 4 | .hn13 => 1 | _ => 0
  | .hn18, y => match y with | .hn0 => 6 | .hn1 => 6 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn19, y => match y with | .hn0 => 9 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | .hn28 => 1 | _ => 0
  | .hn20, y => match y with | .hn0 => 8 | .hn1 => 9 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 3 | .hn11 => 3 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn21, y => match y with | .hn0 => 7 | _ => 0
  | .hn22, y => match y with | .hn0 => 9 | .hn1 => 7 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn23, _ => 0
  | .hn24, y => match y with | .hn0 => 18 | .hn1 => 12 | .hn2 => 7 | .hn3 => 4 | .hn4 => 2 | .hn5 => 1 | _ => 0
  | .hn25, y => match y with | .hn0 => 27 | _ => 0
  | .hn26, y => match y with | .hn0 => 8 | .hn1 => 4 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn27, y => match y with | .hn0 => 15 | .hn1 => 7 | .hn3 => 1 | .hn6 => 4 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn28, y => match y with | .hn0 => 7 | .hn1 => 8 | .hn2 => 4 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn29, y => match y with | .hn0 => 12 | .hn1 => 13 | .hn2 => 4 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn30, y => match y with | .hn0 => 12 | .hn1 => 2 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn31, y => match y with | .hn0 => 8 | .hn1 => 8 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn32, y => match y with | .hn0 => 15 | .hn1 => 13 | _ => 0
  | .hn33, y => match y with | .hn1 => 16 | _ => 0
  | .hn34, _ => 0

def hnB : StateHN → StateHN → Nat
  | .hn0, y => match y with | .hn0 => 2 | .hn1 => 3 | .hn2 => 3 | .hn3 => 4 | .hn4 => 3 | .hn5 => 4 | .hn6 => 4 | .hn8 => 2 | .hn11 => 3 | .hn13 => 2 | .hn14 => 5 | .hn15 => 2 | .hn18 => 5 | _ => 0
  | .hn1, y => match y with | .hn0 => 4 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn7 => 1 | _ => 0
  | .hn2, y => match y with | .hn0 => 9 | .hn1 => 3 | .hn2 => 2 | .hn3 => 4 | .hn4 => 2 | .hn5 => 2 | .hn6 => 3 | .hn7 => 4 | .hn9 => 2 | .hn11 => 2 | .hn12 => 3 | _ => 1
  | .hn3, y => match y with | .hn0 => 12 | .hn1 => 4 | .hn2 => 2 | .hn5 => 1 | .hn18 => 4 | _ => 0
  | .hn4, y => match y with | .hn0 => 19 | .hn1 => 1 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn7 => 1 | .hn11 => 1 | _ => 0
  | .hn5, y => match y with | .hn0 => 11 | .hn1 => 3 | .hn2 => 1 | .hn3 => 3 | .hn4 => 1 | .hn7 => 2 | _ => 0
  | .hn6, y => match y with | .hn0 => 4 | .hn1 => 6 | .hn2 => 6 | .hn3 => 4 | .hn4 => 3 | .hn5 => 6 | .hn6 => 9 | .hn8 => 4 | .hn11 => 9 | .hn12 => 1 | .hn13 => 4 | .hn14 => 5 | .hn15 => 2 | .hn16 => 1 | .hn18 => 5 | .hn20 => 1 | .hn31 => 1 | _ => 0
  | .hn7, y => match y with | .hn0 => 14 | .hn1 => 4 | .hn2 => 3 | .hn3 => 2 | .hn4 => 3 | .hn5 => 2 | .hn6 => 6 | .hn7 => 0 | .hn8 => 2 | .hn9 => 2 | .hn12 => 0 | .hn13 => 0 | .hn14 => 2 | .hn30 => 0 | .hn31 => 0 | .hn32 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn8, y => match y with | .hn0 => 22 | .hn1 => 4 | .hn2 => 5 | .hn3 => 2 | .hn4 => 1 | .hn5 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 1 | _ => 0
  | .hn9, y => match y with | .hn0 => 30 | .hn1 => 7 | .hn2 => 3 | .hn6 => 3 | .hn11 => 1 | .hn18 => 3 | _ => 0
  | .hn10, y => match y with | .hn0 => 68 | .hn1 => 8 | .hn2 => 3 | .hn3 => 3 | .hn4 => 1 | .hn5 => 1 | .hn6 => 4 | .hn7 => 1 | .hn8 => 1 | .hn11 => 2 | .hn18 => 4 | _ => 0
  | .hn11, y => match y with | .hn0 => 7 | .hn1 => 7 | .hn2 => 5 | .hn3 => 7 | .hn4 => 6 | .hn5 => 7 | .hn6 => 5 | .hn7 => 3 | .hn8 => 4 | .hn11 => 4 | .hn13 => 3 | .hn14 => 5 | .hn15 => 3 | .hn18 => 6 | _ => 1
  | .hn12, y => match y with | .hn0 => 15 | .hn1 => 9 | .hn2 => 2 | .hn3 => 5 | .hn4 => 3 | .hn5 => 2 | .hn6 => 1 | .hn7 => 6 | .hn8 => 2 | .hn9 => 1 | .hn11 => 1 | .hn12 => 3 | .hn14 => 2 | .hn15 => 1 | .hn16 => 1 | .hn18 => 2 | .hn19 => 2 | _ => 0
  | .hn13, y => match y with | .hn0 => 6 | .hn1 => 7 | .hn2 => 4 | .hn3 => 4 | .hn4 => 4 | .hn5 => 5 | .hn6 => 9 | .hn8 => 3 | .hn11 => 4 | .hn13 => 3 | .hn14 => 5 | .hn15 => 3 | .hn18 => 6 | _ => 1
  | .hn14, y => match y with | .hn0 => 11 | .hn1 => 3 | .hn2 => 2 | .hn3 => 4 | .hn4 => 4 | .hn5 => 7 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn13 => 1 | .hn14 => 4 | .hn15 => 1 | .hn16 => 1 | .hn18 => 3 | _ => 0
  | .hn15, y => match y with | .hn0 => 6 | .hn1 => 1 | .hn2 => 1 | .hn3 => 8 | _ => 0
  | .hn16, y => match y with | .hn0 => 18 | .hn1 => 7 | .hn2 => 4 | .hn3 => 3 | .hn4 => 2 | .hn5 => 2 | .hn6 => 1 | .hn7 => 3 | _ => 0
  | .hn17, y => match y with | .hn0 => 20 | .hn1 => 8 | .hn2 => 6 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn6 => 5 | .hn7 => 1 | .hn11 => 3 | .hn13 => 1 | _ => 0
  | .hn18, y => match y with | .hn0 => 13 | .hn1 => 4 | .hn2 => 2 | _ => 0
  | .hn19, y => match y with | .hn0 => 23 | .hn1 => 2 | .hn2 => 1 | .hn3 => 4 | .hn7 => 3 | .hn11 => 3 | _ => 0
  | .hn20, y => match y with | .hn0 => 23 | .hn1 => 2 | .hn2 => 2 | .hn3 => 4 | .hn4 => 2 | .hn5 => 2 | .hn6 => 4 | .hn7 => 3 | .hn8 => 2 | .hn9 => 2 | .hn10 => 1 | .hn11 => 1 | .hn12 => 3 | .hn14 => 1 | .hn15 => 1 | .hn16 => 2 | .hn17 => 1 | .hn18 => 1 | _ => 0
  | .hn21, y => match y with | .hn0 => 17 | _ => 0
  | .hn22, y => match y with | .hn0 => 20 | .hn1 => 6 | .hn2 => 5 | .hn3 => 5 | .hn4 => 3 | .hn5 => 6 | _ => 0
  | .hn23, _ => 0
  | .hn24, y => match y with | .hn0 => 30 | .hn1 => 9 | .hn2 => 6 | .hn3 => 7 | .hn4 => 6 | .hn5 => 7 | _ => 0
  | .hn25, y => match y with | .hn0 => 50 | _ => 0
  | .hn26, y => match y with | .hn0 => 10 | .hn1 => 4 | .hn2 => 5 | _ => 0
  | .hn27, y => match y with | .hn0 => 8 | _ => 0
  | .hn28, y => match y with | .hn0 => 12 | .hn1 => 5 | .hn2 => 4 | .hn3 => 2 | .hn4 => 1 | .hn5 => 3 | _ => 0
  | .hn29, y => match y with | .hn0 => 23 | .hn1 => 9 | .hn2 => 6 | .hn3 => 7 | .hn4 => 6 | .hn5 => 7 | _ => 0
  | .hn30, y => match y with | .hn0 => 12 | .hn1 => 5 | .hn2 => 5 | .hn3 => 4 | .hn4 => 3 | .hn5 => 5 | _ => 0
  | .hn31, y => match y with | .hn0 => 9 | .hn1 => 8 | .hn2 => 2 | _ => 0
  | .hn32, y => match y with | .hn0 => 14 | .hn1 => 10 | _ => 0
  | .hn33, y => match y with | .hn1 => 17 | _ => 0
  | .hn34, _ => 0

private theorem hnA_col34_zero_chk : checkAll1_StateHN (fun u => decide (hnA u .hn34 = 0)) = true := rfl

theorem hnA_col34_zero (u : StateHN) : hnA u .hn34 = 0 :=
  of_decide_eq_true (checkAll1_StateHN_sound _ hnA_col34_zero_chk u)

private theorem hn_cert_row_0 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn0; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn0; let b0 := hnB .hn0 .hn0; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn0 z) (deltaHN y z)) as1) && (natBle (hnA .hn0 z + hnA (deltaHN .hn0 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn0 z + hnA (deltaHN .hn0 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn0 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_1 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn1; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn1; let b0 := hnB .hn0 .hn1; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn1 z) (deltaHN y z)) as1) && (natBle (hnA .hn1 z + hnA (deltaHN .hn1 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn1 z + hnA (deltaHN .hn1 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn1 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_2 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn2; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn2; let b0 := hnB .hn0 .hn2; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn2 z) (deltaHN y z)) as1) && (natBle (hnA .hn2 z + hnA (deltaHN .hn2 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn2 z + hnA (deltaHN .hn2 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn2 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_3 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn3; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn3; let b0 := hnB .hn0 .hn3; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn3 z) (deltaHN y z)) as1) && (natBle (hnA .hn3 z + hnA (deltaHN .hn3 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn3 z + hnA (deltaHN .hn3 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn3 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_4 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn4; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn4; let b0 := hnB .hn0 .hn4; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn4 z) (deltaHN y z)) as1) && (natBle (hnA .hn4 z + hnA (deltaHN .hn4 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn4 z + hnA (deltaHN .hn4 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn4 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_5 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn5; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn5; let b0 := hnB .hn0 .hn5; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn5 z) (deltaHN y z)) as1) && (natBle (hnA .hn5 z + hnA (deltaHN .hn5 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn5 z + hnA (deltaHN .hn5 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn5 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_6 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn6; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn6; let b0 := hnB .hn0 .hn6; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn6 z) (deltaHN y z)) as1) && (natBle (hnA .hn6 z + hnA (deltaHN .hn6 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn6 z + hnA (deltaHN .hn6 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn6 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_7 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn7; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn7; let b0 := hnB .hn0 .hn7; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn7 z) (deltaHN y z)) as1) && (natBle (hnA .hn7 z + hnA (deltaHN .hn7 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn7 z + hnA (deltaHN .hn7 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn7 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_8 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn8; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn8; let b0 := hnB .hn0 .hn8; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn8 z) (deltaHN y z)) as1) && (natBle (hnA .hn8 z + hnA (deltaHN .hn8 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn8 z + hnA (deltaHN .hn8 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn8 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_9 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn9; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn9; let b0 := hnB .hn0 .hn9; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn9 z) (deltaHN y z)) as1) && (natBle (hnA .hn9 z + hnA (deltaHN .hn9 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn9 z + hnA (deltaHN .hn9 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn9 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_10 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn10; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn10; let b0 := hnB .hn0 .hn10; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn10 z) (deltaHN y z)) as1) && (natBle (hnA .hn10 z + hnA (deltaHN .hn10 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn10 z + hnA (deltaHN .hn10 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn10 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_11 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn11; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn11; let b0 := hnB .hn0 .hn11; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn11 z) (deltaHN y z)) as1) && (natBle (hnA .hn11 z + hnA (deltaHN .hn11 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn11 z + hnA (deltaHN .hn11 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn11 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_12 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn12; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn12; let b0 := hnB .hn0 .hn12; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn12 z) (deltaHN y z)) as1) && (natBle (hnA .hn12 z + hnA (deltaHN .hn12 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn12 z + hnA (deltaHN .hn12 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn12 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_13 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn13; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn13; let b0 := hnB .hn0 .hn13; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn13 z) (deltaHN y z)) as1) && (natBle (hnA .hn13 z + hnA (deltaHN .hn13 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn13 z + hnA (deltaHN .hn13 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn13 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_14 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn14; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn14; let b0 := hnB .hn0 .hn14; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn14 z) (deltaHN y z)) as1) && (natBle (hnA .hn14 z + hnA (deltaHN .hn14 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn14 z + hnA (deltaHN .hn14 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn14 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_15 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn15; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn15; let b0 := hnB .hn0 .hn15; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn15 z) (deltaHN y z)) as1) && (natBle (hnA .hn15 z + hnA (deltaHN .hn15 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn15 z + hnA (deltaHN .hn15 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn15 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_16 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn16; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn16; let b0 := hnB .hn0 .hn16; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn16 z) (deltaHN y z)) as1) && (natBle (hnA .hn16 z + hnA (deltaHN .hn16 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn16 z + hnA (deltaHN .hn16 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn16 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_17 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn17; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn17; let b0 := hnB .hn0 .hn17; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn17 z) (deltaHN y z)) as1) && (natBle (hnA .hn17 z + hnA (deltaHN .hn17 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn17 z + hnA (deltaHN .hn17 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn17 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_18 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn18; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn18; let b0 := hnB .hn0 .hn18; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn18 z) (deltaHN y z)) as1) && (natBle (hnA .hn18 z + hnA (deltaHN .hn18 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn18 z + hnA (deltaHN .hn18 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn18 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_19 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn19; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn19; let b0 := hnB .hn0 .hn19; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn19 z) (deltaHN y z)) as1) && (natBle (hnA .hn19 z + hnA (deltaHN .hn19 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn19 z + hnA (deltaHN .hn19 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn19 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_20 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn20; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn20; let b0 := hnB .hn0 .hn20; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn20 z) (deltaHN y z)) as1) && (natBle (hnA .hn20 z + hnA (deltaHN .hn20 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn20 z + hnA (deltaHN .hn20 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn20 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_21 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn21; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn21; let b0 := hnB .hn0 .hn21; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn21 z) (deltaHN y z)) as1) && (natBle (hnA .hn21 z + hnA (deltaHN .hn21 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn21 z + hnA (deltaHN .hn21 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn21 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_22 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn22; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn22; let b0 := hnB .hn0 .hn22; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn22 z) (deltaHN y z)) as1) && (natBle (hnA .hn22 z + hnA (deltaHN .hn22 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn22 z + hnA (deltaHN .hn22 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn22 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_23 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn23; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn23; let b0 := hnB .hn0 .hn23; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn23 z) (deltaHN y z)) as1) && (natBle (hnA .hn23 z + hnA (deltaHN .hn23 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn23 z + hnA (deltaHN .hn23 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn23 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_24 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn24; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn24; let b0 := hnB .hn0 .hn24; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn24 z) (deltaHN y z)) as1) && (natBle (hnA .hn24 z + hnA (deltaHN .hn24 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn24 z + hnA (deltaHN .hn24 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn24 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_25 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn25; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn25; let b0 := hnB .hn0 .hn25; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn25 z) (deltaHN y z)) as1) && (natBle (hnA .hn25 z + hnA (deltaHN .hn25 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn25 z + hnA (deltaHN .hn25 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn25 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_26 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn26; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn26; let b0 := hnB .hn0 .hn26; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn26 z) (deltaHN y z)) as1) && (natBle (hnA .hn26 z + hnA (deltaHN .hn26 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn26 z + hnA (deltaHN .hn26 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn26 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_27 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn27; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn27; let b0 := hnB .hn0 .hn27; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn27 z) (deltaHN y z)) as1) && (natBle (hnA .hn27 z + hnA (deltaHN .hn27 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn27 z + hnA (deltaHN .hn27 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn27 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_28 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn28; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn28; let b0 := hnB .hn0 .hn28; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn28 z) (deltaHN y z)) as1) && (natBle (hnA .hn28 z + hnA (deltaHN .hn28 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn28 z + hnA (deltaHN .hn28 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn28 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_29 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn29; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn29; let b0 := hnB .hn0 .hn29; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn29 z) (deltaHN y z)) as1) && (natBle (hnA .hn29 z + hnA (deltaHN .hn29 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn29 z + hnA (deltaHN .hn29 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn29 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_30 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn30; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn30; let b0 := hnB .hn0 .hn30; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn30 z) (deltaHN y z)) as1) && (natBle (hnA .hn30 z + hnA (deltaHN .hn30 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn30 z + hnA (deltaHN .hn30 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn30 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_31 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn31; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn31; let b0 := hnB .hn0 .hn31; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn31 z) (deltaHN y z)) as1) && (natBle (hnA .hn31 z + hnA (deltaHN .hn31 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn31 z + hnA (deltaHN .hn31 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn31 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_32 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn32; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn32; let b0 := hnB .hn0 .hn32; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn32 z) (deltaHN y z)) as1) && (natBle (hnA .hn32 z + hnA (deltaHN .hn32 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn32 z + hnA (deltaHN .hn32 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn32 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_33 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn33; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn33; let b0 := hnB .hn0 .hn33; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn33 z) (deltaHN y z)) as1) && (natBle (hnA .hn33 z + hnA (deltaHN .hn33 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn33 z + hnA (deltaHN .hn33 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn33 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl
private theorem hn_cert_row_34 : checkAll1_StateHN (fun y => let s1 := deltaHN .hn0 .hn34; let s2 := deltaHN s1 y; let a0 := hnA .hn0 .hn34; let b0 := hnB .hn0 .hn34; let as1 := hnA s1 y; let bs1 := hnB s1 y; checkAll1_StateHN (fun z => (!decide (deltaHN s2 z ≠ .hn34) || ((natBle 1 a0 && natBle (hnA (deltaHN .hn34 z) (deltaHN y z)) as1) && (natBle (hnA .hn34 z + hnA (deltaHN .hn34 z) (deltaHN y z) * hnA y z) (hnA s2 z) && natBle (hnB .hn34 z + hnA (deltaHN .hn34 z) (deltaHN y z) * hnB y z + hnB (deltaHN .hn34 z) (deltaHN y z) + 1) (b0 + bs1 + hnB s2 z)))))) = true := rfl

private theorem hn_cert_bounds {x y z : StateHN}
    (hvalid : deltaHN (deltaHN (deltaHN .hn0 x) y) z ≠ .hn34) :
    1 ≤ hnA .hn0 x ∧
    hnA (deltaHN x z) (deltaHN y z) ≤ hnA (deltaHN .hn0 x) y ∧
    hnA x z + hnA (deltaHN x z) (deltaHN y z) * hnA y z ≤ hnA (deltaHN (deltaHN .hn0 x) y) z ∧
    hnB x z + hnA (deltaHN x z) (deltaHN y z) * hnB y z + hnB (deltaHN x z) (deltaHN y z) + 1 ≤
      hnB .hn0 x + hnB (deltaHN .hn0 x) y + hnB (deltaHN (deltaHN .hn0 x) y) z := by
  have h : (!decide (deltaHN (deltaHN (deltaHN .hn0 x) y) z ≠ .hn34) || ((natBle 1 (hnA .hn0 x) && natBle (hnA (deltaHN x z) (deltaHN y z)) (hnA (deltaHN .hn0 x) y)) && (natBle (hnA x z + hnA (deltaHN x z) (deltaHN y z) * hnA y z) (hnA (deltaHN (deltaHN .hn0 x) y) z) && natBle (hnB x z + hnA (deltaHN x z) (deltaHN y z) * hnB y z + hnB (deltaHN x z) (deltaHN y z) + 1) (hnB .hn0 x + hnB (deltaHN .hn0 x) y + hnB (deltaHN (deltaHN .hn0 x) y) z)))) = true :=
    match x with
    | .hn0 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_0 y) z
    | .hn1 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_1 y) z
    | .hn2 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_2 y) z
    | .hn3 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_3 y) z
    | .hn4 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_4 y) z
    | .hn5 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_5 y) z
    | .hn6 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_6 y) z
    | .hn7 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_7 y) z
    | .hn8 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_8 y) z
    | .hn9 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_9 y) z
    | .hn10 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_10 y) z
    | .hn11 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_11 y) z
    | .hn12 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_12 y) z
    | .hn13 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_13 y) z
    | .hn14 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_14 y) z
    | .hn15 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_15 y) z
    | .hn16 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_16 y) z
    | .hn17 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_17 y) z
    | .hn18 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_18 y) z
    | .hn19 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_19 y) z
    | .hn20 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_20 y) z
    | .hn21 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_21 y) z
    | .hn22 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_22 y) z
    | .hn23 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_23 y) z
    | .hn24 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_24 y) z
    | .hn25 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_25 y) z
    | .hn26 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_26 y) z
    | .hn27 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_27 y) z
    | .hn28 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_28 y) z
    | .hn29 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_29 y) z
    | .hn30 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_30 y) z
    | .hn31 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_31 y) z
    | .hn32 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_32 y) z
    | .hn33 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_33 y) z
    | .hn34 => checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ hn_cert_row_34 y) z
  have h' := imp_decide hvalid h
  have hL := and_left h'
  have hR := and_right h'
  exact ⟨natBle_sound (and_left hL), natBle_sound (and_right hL), natBle_sound (and_left hR), natBle_sound (and_right hR)⟩

private theorem cert_algebra_lemma
    (mx my mz a0 as1 as2 ax ay auv b0 bs1 bs2 bx by_ buv : Nat)
    (h1 : 1 ≤ a0)
    (h2 : auv ≤ as1)
    (h3 : ax + auv * ay ≤ as2)
    (h4 : bx + auv * by_ + buv + 1 ≤ b0 + bs1 + bs2) :
    ((mx + ax * mz + bx) + auv * (my + ay * mz + by_) + buv) + 1 ≤
    (((0 + a0 * mx + b0) + as1 * my + bs1) + as2 * mz + bs2) := by
  have p1 : mx ≤ a0 * mx := by
    have hm := Nat.mul_le_mul_right mx h1
    rw [Nat.one_mul mx] at hm
    exact hm
  have p2 : auv * my ≤ as1 * my := Nat.mul_le_mul_right my h2
  have p3 : ax * mz + (auv * ay) * mz ≤ as2 * mz := by
    rw [← Nat.add_mul ax (auv * ay) mz]
    exact Nat.mul_le_mul_right mz h3
  have hsum : (mx + auv * my) + ((ax * mz + (auv * ay) * mz) + (bx + auv * by_ + buv + 1)) ≤
      (a0 * mx + as1 * my) + (as2 * mz + (b0 + bs1 + bs2)) :=
    Nat.add_le_add (Nat.add_le_add p1 p2) (Nat.add_le_add p3 h4)
  have hL : ((mx + ax * mz + bx) + auv * (my + ay * mz + by_) + buv) + 1 =
      (mx + auv * my) + ((ax * mz + (auv * ay) * mz) + (bx + auv * by_ + buv + 1)) := by
    rw [Nat.mul_add auv (my + ay * mz) by_, Nat.mul_add auv my (ay * mz), ← Nat.mul_assoc auv ay mz]
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hR : (((0 + a0 * mx + b0) + as1 * my + bs1) + as2 * mz + bs2) =
      (a0 * mx + as1 * my) + (as2 * mz + (b0 + bs1 + bs2)) := by
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [hL, hR]
  exact hsum

/-- **Global Multiway Potential `nuHN`**:
    Truncated to `0` on `.hn34` nodes so that `nuHN` is weakly decreasing under **every**
    contextual `Step` (left, right, or root, open or closed) and strictly decreases by `≥ 1`
    on every `HeadStep` whenever `evalHN m ≠ .hn34`. -/
def nuHN : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app l r =>
    if decide (deltaHN (evalHN l) (evalHN r) = .hn34) then 0
    else nuHN l + hnA (evalHN l) (evalHN r) * nuHN r + hnB (evalHN l) (evalHN r)

private theorem nuHN_app_ne34 {l r : Term} (h : evalHN (l ⋅ r) ≠ .hn34) :
    nuHN (l ⋅ r) = nuHN l + hnA (evalHN l) (evalHN r) * nuHN r + hnB (evalHN l) (evalHN r) := by
  change deltaHN (evalHN l) (evalHN r) ≠ .hn34 at h
  change (if decide (deltaHN (evalHN l) (evalHN r) = .hn34) then 0 else _) = _
  rw [decide_eq_false h]
  rfl

private theorem nuHN_app_eq34 {l r : Term} (h : evalHN (l ⋅ r) = .hn34) :
    nuHN (l ⋅ r) = 0 := by
  change deltaHN (evalHN l) (evalHN r) = .hn34 at h
  change (if decide (deltaHN (evalHN l) (evalHN r) = .hn34) then 0 else _) = 0
  rw [decide_eq_true h]
  rfl

private theorem hnA_mul_nuHN_app (u : StateHN) (y z : Term) :
    hnA u (evalHN (y ⋅ z)) * nuHN (y ⋅ z) =
      hnA u (evalHN (y ⋅ z)) * (nuHN y + hnA (evalHN y) (evalHN z) * nuHN z + hnB (evalHN y) (evalHN z)) := by
  cases hd : decide (evalHN (y ⋅ z) = .hn34) with
  | true =>
    have h34 : evalHN (y ⋅ z) = .hn34 := of_decide_eq_true hd
    rw [nuHN_app_eq34 h34, h34, hnA_col34_zero u, Nat.zero_mul, Nat.zero_mul]
  | false =>
    have hne : evalHN (y ⋅ z) ≠ .hn34 := of_decide_eq_false hd
    rw [nuHN_app_ne34 hne]

theorem nuHN_root_drop (x y z : Term) (hval : evalHN (S ⋅ x ⋅ y ⋅ z) ≠ .hn34) :
    nuHN ((x ⋅ z) ⋅ (y ⋅ z)) + 1 ≤ nuHN (S ⋅ x ⋅ y ⋅ z) := by
  have hs1 : evalHN (S ⋅ x) ≠ .hn34 := deltaHN_s1_ne_hn34 (evalHN x)
  have hs2 : evalHN (S ⋅ x ⋅ y) ≠ .hn34 := deltaHN_s2_ne_hn34 (evalHN x) (evalHN y)
  have hrhs : evalHN ((x ⋅ z) ⋅ (y ⋅ z)) ≠ .hn34 := by
    rw [← evalHN_step (Step.root x y z)]
    exact hval
  have hu : evalHN (x ⋅ z) ≠ .hn34 := deltaHN_ne_hn34_left hrhs
  rw [nuHN_app_ne34 hval, nuHN_app_ne34 hs2, nuHN_app_ne34 hs1,
      nuHN_app_ne34 hrhs, nuHN_app_ne34 hu, hnA_mul_nuHN_app]
  have ⟨c1, c2, c3, c4⟩ := hn_cert_bounds hval
  exact cert_algebra_lemma
    (nuHN x) (nuHN y) (nuHN z)
    (hnA .hn0 (evalHN x))
    (hnA (deltaHN .hn0 (evalHN x)) (evalHN y))
    (hnA (deltaHN (deltaHN .hn0 (evalHN x)) (evalHN y)) (evalHN z))
    (hnA (evalHN x) (evalHN z))
    (hnA (evalHN y) (evalHN z))
    (hnA (deltaHN (evalHN x) (evalHN z)) (deltaHN (evalHN y) (evalHN z)))
    (hnB .hn0 (evalHN x))
    (hnB (deltaHN .hn0 (evalHN x)) (evalHN y))
    (hnB (deltaHN (deltaHN .hn0 (evalHN x)) (evalHN y)) (evalHN z))
    (hnB (evalHN x) (evalHN z))
    (hnB (evalHN y) (evalHN z))
    (hnB (deltaHN (evalHN x) (evalHN z)) (deltaHN (evalHN y) (evalHN z)))
    c1 c2 c3 c4

theorem nuHN_headStep_drop {m m' : Term} (hs : HeadStep m m') (hval : evalHN m ≠ .hn34) :
    nuHN m' + 1 ≤ nuHN m := by
  induction hs with
  | root x y z => exact nuHN_root_drop x y z hval
  | @left l l' r hl ih =>
    have hl_val : evalHN l ≠ .hn34 := deltaHN_ne_hn34_left hval
    have hval' : evalHN (l' ⋅ r) ≠ .hn34 := by
      rw [← evalHN_step (headStep_to_step (.left hl))]
      exact hval
    have hdrop := ih hl_val
    have heq_l : evalHN l' = evalHN l := (evalHN_step (headStep_to_step hl)).symm
    rw [nuHN_app_ne34 hval, nuHN_app_ne34 hval', heq_l]
    have h1 := Nat.add_le_add_right hdrop (hnA (evalHN l) (evalHN r) * nuHN r + hnB (evalHN l) (evalHN r))
    have hL : (nuHN l' + hnA (evalHN l) (evalHN r) * nuHN r + hnB (evalHN l) (evalHN r)) + 1 =
        (nuHN l' + 1) + (hnA (evalHN l) (evalHN r) * nuHN r + hnB (evalHN l) (evalHN r)) := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [hL, Nat.add_assoc (nuHN l)]
    exact h1

/-- **Global Multiway Monotonicity of `nuHN`**:
    For **every** contextual `Step m m'` (root, left, or right; open or closed; `.hn34` or `< 34`),
    `nuHN m' ≤ nuHN m`. -/
theorem nuHN_step_le {m m' : Term} (hs : Step m m') : nuHN m' ≤ nuHN m := by
  induction hs with
  | root x y z =>
    cases hd : decide (evalHN (S ⋅ x ⋅ y ⋅ z) = .hn34) with
    | true =>
      have h34 : evalHN (S ⋅ x ⋅ y ⋅ z) = .hn34 := of_decide_eq_true hd
      have h34' : evalHN ((x ⋅ z) ⋅ (y ⋅ z)) = .hn34 := (evalHN_step (Step.root x y z)).symm.trans h34
      rw [nuHN_app_eq34 h34, nuHN_app_eq34 h34']
      exact Nat.le_refl 0
    | false =>
      have hne : evalHN (S ⋅ x ⋅ y ⋅ z) ≠ .hn34 := of_decide_eq_false hd
      exact Nat.le_of_lt (nuHN_root_drop x y z hne)
  | @left l l' r hl ihl =>
    cases hd : decide (evalHN (l ⋅ r) = .hn34) with
    | true =>
      have h34 : evalHN (l ⋅ r) = .hn34 := of_decide_eq_true hd
      have h34' : evalHN (l' ⋅ r) = .hn34 := (evalHN_step (Step.left hl)).symm.trans h34
      rw [nuHN_app_eq34 h34, nuHN_app_eq34 h34']
      exact Nat.le_refl 0
    | false =>
      have hne : evalHN (l ⋅ r) ≠ .hn34 := of_decide_eq_false hd
      have hne' : evalHN (l' ⋅ r) ≠ .hn34 := by rw [← evalHN_step (Step.left hl)]; exact hne
      have heq_l : evalHN l' = evalHN l := (evalHN_step hl).symm
      rw [nuHN_app_ne34 hne, nuHN_app_ne34 hne', heq_l]
      exact Nat.add_le_add_right (Nat.add_le_add_right ihl _) _
  | @right l r r' hr ihr =>
    cases hd : decide (evalHN (l ⋅ r) = .hn34) with
    | true =>
      have h34 : evalHN (l ⋅ r) = .hn34 := of_decide_eq_true hd
      have h34' : evalHN (l ⋅ r') = .hn34 := (evalHN_step (Step.right hr)).symm.trans h34
      rw [nuHN_app_eq34 h34, nuHN_app_eq34 h34']
      exact Nat.le_refl 0
    | false =>
      have hne : evalHN (l ⋅ r) ≠ .hn34 := of_decide_eq_false hd
      have hne' : evalHN (l ⋅ r') ≠ .hn34 := by rw [← evalHN_step (Step.right hr)]; exact hne
      have heq_r : evalHN r' = evalHN r := (evalHN_step hr).symm
      rw [nuHN_app_ne34 hne, nuHN_app_ne34 hne', heq_r]
      exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ ihr) _) _

theorem nuHN_reduces_le {a b : Term} (h : Reduces a b) : nuHN b ≤ nuHN a := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | next hs _ ih => exact Nat.le_trans ih (nuHN_step_le hs)

theorem nuHN_relRootStep_drop {a b : Term} (h : RelRootStep a b) (hval : evalHN a ≠ .hn34) :
    nuHN b + 1 ≤ nuHN a := by
  obtain ⟨m, hnr, hr⟩ := h
  have hle : nuHN m ≤ nuHN a := nuHN_reduces_le (nonRootReduces_to_reduces hnr)
  have hm_val : evalHN m ≠ .hn34 := by
    rw [← evalHN_reduces (nonRootReduces_to_reduces hnr)]
    exact hval
  exact Nat.le_trans (nuHN_headStep_drop (rootStep_to_headStep hr) hm_val) hle

private theorem topTerminating_ne34_aux :
    ∀ (k : Nat) {t : Term}, evalHN t ≠ .hn34 → nuHN t ≤ k → TopTerminating t
  | 0, t, hval, hle =>
    Acc.intro t (fun b hrel => by
      have hdrop := nuHN_relRootStep_drop hrel hval
      exfalso
      exact Nat.not_succ_le_zero 0 (Nat.le_trans (Nat.le_trans (Nat.le_add_left 1 (nuHN b)) hdrop) hle))
  | k + 1, t, hval, hle =>
    Acc.intro t (fun b hrel => by
      have hdrop := nuHN_relRootStep_drop hrel hval
      have hb_val : evalHN b ≠ .hn34 := by
        rw [← evalHN_reduces (relRootStep_to_reduces hrel)]
        exact hval
      have hb_le : nuHN b ≤ k := Nat.le_of_succ_le_succ (Nat.le_trans hdrop hle)
      exact topTerminating_ne34_aux k hb_val hb_le)

/-- **Top-Termination of All Non-`.hn34` Pure `S`-Terms (Open or Closed)**:
    Every pure `S`-term `t` with `evalHN t ≠ .hn34` executes at most `nuHN t` root contractions. -/
theorem topTerminating_of_evalHN_ne_hn34 {t : Term} (hval : evalHN t ≠ .hn34) : TopTerminating t :=
  topTerminating_ne34_aux (nuHN t) hval (Nat.le_refl _)

/-! ### Deterministic Head Normalizer, Open Problem 10, and Footnote 4 -/

def rootRedexOpt (a b : Term) : Option Term :=
  match a with
  | .app (.app .s x) y => some ((x ⋅ b) ⋅ (y ⋅ b))
  | _ => none

theorem rootRedexOpt_some {a b r : Term} (h : rootRedexOpt a b = some r) :
    ∃ x y, a = S ⋅ x ⋅ y ∧ r = (x ⋅ b) ⋅ (y ⋅ b) := by
  cases a with
  | s => cases h
  | var _ => cases h
  | app a1 y =>
    cases a1 with
    | s => cases h
    | var _ => cases h
    | app a2 x =>
      cases a2 with
      | s => injection h with hr; exact ⟨x, y, rfl, hr.symm⟩
      | var _ => cases h
      | app _ _ => cases h

theorem rootRedexOpt_none {a b : Term} (h : rootRedexOpt a b = none) :
    ∀ x y, a ≠ S ⋅ x ⋅ y := by
  intro x y heq; subst heq; cases h

def headStepOpt : Term → Option Term
  | .s => none
  | .var _ => none
  | .app a b =>
    match rootRedexOpt a b with
    | some r => some r
    | none =>
      match headStepOpt a with
      | some a' => some (a' ⋅ b)
      | none => none

theorem headStepOpt_some {t t' : Term} (h : headStepOpt t = some t') : HeadStep t t' := by
  induction t generalizing t' with
  | s => cases h
  | var _ => cases h
  | app a b iha _ =>
    simp only [headStepOpt] at h
    cases hr : rootRedexOpt a b with
    | some r =>
      rw [hr] at h; injection h with heq; subst heq
      obtain ⟨x, y, ha, hreq⟩ := rootRedexOpt_some hr
      subst ha; subst hreq
      exact HeadStep.root x y b
    | none =>
      rw [hr] at h
      cases ha : headStepOpt a with
      | some a' =>
        rw [ha] at h; injection h with heq; subst heq
        exact HeadStep.left (iha ha)
      | none => rw [ha] at h; cases h

theorem headStepOpt_none_closed {t : Term} (hv : noVars t = true) (h : headStepOpt t = none) :
    t = S ∨ (∃ x, t = S ⋅ x) ∨ (∃ x y, t = S ⋅ x ⋅ y) := by
  induction t with
  | s => exact Or.inl rfl
  | var _ => cases hv
  | app a b iha _ =>
    simp only [noVars, Bool.and_eq_true] at hv
    simp only [headStepOpt] at h
    cases hr : rootRedexOpt a b with
    | some r => rw [hr] at h; cases h
    | none =>
      rw [hr] at h
      cases ha : headStepOpt a with
      | some a' => rw [ha] at h; cases h
      | none =>
        rcases iha hv.1 ha with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
        · exact Or.inr (Or.inl ⟨b, rfl⟩)
        · exact Or.inr (Or.inr ⟨x, b, rfl⟩)
        · exfalso; exact rootRedexOpt_none hr x y rfl

theorem closed_spineLen_le_2_shapes {t : Term} (hv : noVars t = true) (hsl : spineLen t ≤ 2) :
    t = S ∨ (∃ x, t = S ⋅ x) ∨ (∃ x y, t = S ⋅ x ⋅ y) := by
  cases t with
  | s => exact Or.inl rfl
  | var _ => cases hv
  | app a b =>
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    cases a with
    | s => exact Or.inr (Or.inl ⟨b, rfl⟩)
    | var _ => cases hva
    | app a1 y =>
      have hva1 := ((Bool.and_eq_true _ _).mp hva).1
      cases a1 with
      | s => exact Or.inr (Or.inr ⟨y, b, rfl⟩)
      | var _ => cases hva1
      | app a2 _ =>
        have h3 : 3 ≤ 1 + (1 + (1 + spineLen a2)) :=
          Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.zero_le _) 1) 1) 1
        exfalso
        exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_trans h3 hsl)))

theorem headStepOpt_none_spineLen {t : Term} (hv : noVars t = true) (h : headStepOpt t = none) :
    spineLen t ≤ 2 := by
  rcases headStepOpt_none_closed hv h with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · exact Nat.zero_le 2
  · exact Nat.succ_le_succ (Nat.zero_le 1)
  · exact Nat.le_refl 2

theorem closed_hnf_evalHN_ne_hn34 {h : Term} (hv : noVars h = true) (hsl : spineLen h ≤ 2) :
    evalHN h ≠ .hn34 := by
  rcases closed_spineLen_le_2_shapes hv hsl with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · decide
  · exact deltaHN_s1_ne_hn34 (evalHN x)
  · exact deltaHN_s2_ne_hn34 (evalHN x) (evalHN y)

def headNormalizeAux : Nat → Term → Term
  | 0, t => t
  | fuel + 1, t =>
    match headStepOpt t with
    | none => t
    | some t' => headNormalizeAux fuel t'

private theorem headNormalizeAux_spec :
    ∀ (fuel : Nat) {t : Term},
      noVars t = true → evalHN t ≠ .hn34 → nuHN t < fuel →
      HeadReduces t (headNormalizeAux fuel t) ∧ IsClosedHNF (headNormalizeAux fuel t) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ hlt; cases hlt
  | succ fuel ih =>
    intro t hv hval hlt
    simp only [headNormalizeAux]
    cases hh : headStepOpt t with
    | none => exact ⟨HeadReduces.refl t, hv, headStepOpt_none_spineLen hv hh⟩
    | some t' =>
      have hs : HeadStep t t' := headStepOpt_some hh
      have hv' : noVars t' = true := noVars_step (headStep_to_step hs) hv
      have hval' : evalHN t' ≠ .hn34 := by rw [← evalHN_step (headStep_to_step hs)]; exact hval
      have hdrop : nuHN t' + 1 ≤ nuHN t := nuHN_headStep_drop hs hval
      have hlt' : nuHN t' < fuel := Nat.lt_of_succ_lt_succ (Nat.lt_of_le_of_lt hdrop hlt)
      obtain ⟨hred, hhnf⟩ := ih hv' hval' hlt'
      exact ⟨HeadReduces.next hs hred, hhnf⟩

def headNormalize (t : Term) : Term :=
  headNormalizeAux (nuHN t + 1) t

theorem headNormalize_reduces_hnf {t : Term} (hv : noVars t = true) (hval : evalHN t ≠ .hn34) :
    HeadReduces t (headNormalize t) ∧ IsClosedHNF (headNormalize t) :=
  headNormalizeAux_spec (nuHN t + 1) hv hval (Nat.lt_succ_self (nuHN t))

theorem closed_hasHNF_iff {t : Term} (hv : noVars t = true) :
    HasHNF t ↔ evalHN t ≠ .hn34 := by
  constructor
  · intro ⟨h, hred, hsl⟩
    rw [evalHN_reduces hred]
    exact closed_hnf_evalHN_ne_hn34 (noVars_reduces hred hv) hsl
  · intro hval
    obtain ⟨hred, _, hsl⟩ := headNormalize_reduces_hnf hv hval
    exact ⟨headNormalize t, headReduces_to_reduces hred, hsl⟩

theorem closed_headLeaf_eq_s {t : Term} (hv : noVars t = true) : headLeaf t = S := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a _ iha _ => exact iha ((Bool.and_eq_true _ _).mp hv).1

private theorem spineLen_le_2_step_eq {a b : Term} (hs : Step a b)
    (hhead : headLeaf a = S) (hsl : spineLen a ≤ 2) :
    spineLen b = spineLen a ∧ headLeaf b = S := by
  induction hs with
  | root _ _ _ =>
    change 3 ≤ 2 at hsl
    cases hsl with | step h1 => cases h1 with | step h2 => cases h2
  | @left l _ _ _ ih =>
    have hll : spineLen l ≤ 2 := Nat.le_trans (Nat.le_add_left (spineLen l) 1) hsl
    have ⟨hsp, hhd⟩ := ih hhead hll
    exact ⟨congrArg (1 + ·) hsp, hhd⟩
  | right _ _ => exact ⟨rfl, hhead⟩

private theorem spineLen_le_2_reduces_eq {a b : Term} (hr : Reduces a b)
    (hhead : headLeaf a = S) (hsl : spineLen a ≤ 2) : spineLen b = spineLen a := by
  induction hr with
  | refl _ => rfl
  | next hs _ ih =>
    have ⟨hsp, hhd⟩ := spineLen_le_2_step_eq hs hhead hsl
    exact (ih hhd (hsp.symm ▸ hsl)).trans hsp

theorem reduces_app_no_sab {m n : Term} (hred : Reduces m n) :
    ∀ a b, (∀ p q, ¬ Reduces a (S ⋅ p ⋅ q)) → m = a ⋅ b →
      ∃ a' b', n = a' ⋅ b' ∧ Reduces a a' ∧ Reduces b b' := by
  induction hred with
  | refl _ => intro a b _ hm; exact ⟨a, b, hm, Reduces.refl a, Reduces.refl b⟩
  | @next _ _ _ hs _ ih =>
    intro a b hno hm; subst hm
    cases hs with
    | root p q _ => exfalso; exact hno p q (Reduces.refl _)
    | @left _ a1 _ ha1 =>
      have hno1 : ∀ p q, ¬ Reduces a1 (S ⋅ p ⋅ q) := fun p q hr => hno p q (Reduces.next ha1 hr)
      obtain ⟨a', b', hn, hra, hrb⟩ := ih a1 b hno1 rfl
      exact ⟨a', b', hn, Reduces.next ha1 hra, hrb⟩
    | @right _ _ b1 hb1 =>
      obtain ⟨a', b', hn, hra, hrb⟩ := ih a b1 hno rfl
      exact ⟨a', b', hn, hra, Reduces.next hb1 hrb⟩

/-- **Universal Left-`.hn34` Root Normal Form Theorem**:
    For **any** pure `S`-terms `a, b` (open or closed!), if `evalHN a = .hn34`, then `a ⋅ b`
    is already in Root Normal Form (`IsRootNormalForm (a ⋅ b)`). -/
theorem left_hn34_isRootNormalForm {a b : Term} (ha34 : evalHN a = .hn34) :
    IsRootNormalForm (a ⋅ b) := by
  intro ⟨x, y, z, hred⟩
  have hno : ∀ p q, ¬ Reduces a (S ⋅ p ⋅ q) := by
    intro p q hr
    have heq := evalHN_reduces hr
    rw [ha34] at heq
    exact deltaHN_s2_ne_hn34 (evalHN p) (evalHN q) heq.symm
  obtain ⟨a', _, heq, hra, _⟩ := reduces_app_no_sab hred a b hno rfl
  injection heq with ha' _
  exact hno x y (ha' ▸ hra)

/-- **Footnote 4 of Barendregt et al. (2018, p. 103 — Exact Decidability of RNF)**:
    A closed pure `S`-term `t` is in Root Normal Form iff `spineLen t ≤ 2` or
    `t = a ⋅ b` with `evalHN a = .hn34`. -/
theorem footnote4_rnf_iff {t : Term} (hv : noVars t = true) :
    IsRootNormalForm t ↔ (spineLen t ≤ 2 ∨ ∃ a b, t = a ⋅ b ∧ evalHN a = .hn34) := by
  constructor
  · intro hrnf
    exact if hsl : spineLen t ≤ 2 then Or.inl hsl
    else by
      cases t with
      | s => exfalso; exact hsl (Nat.zero_le 2)
      | var _ => cases hv
      | app a b =>
        have hva := ((Bool.and_eq_true _ _).mp hv).1
        exact if ha34 : evalHN a = .hn34 then Or.inr ⟨a, b, rfl, ha34⟩
        else by
          exfalso
          obtain ⟨hred_a, hv_h, hsl_h⟩ := headNormalize_reduces_hnf hva ha34
          have ha_ge2 : hasSpineGe2 a = true := by
            cases a with
            | s => exfalso; exact hsl (Nat.succ_le_succ (Nat.zero_le 1))
            | var _ => cases hva
            | app a1 _ =>
              cases a1 with
              | s => exfalso; exact hsl (Nat.le_refl 2)
              | var _ => cases ((Bool.and_eq_true _ _).mp hva).1
              | app _ _ => rfl
          have hh_ge2 : hasSpineGe2 (headNormalize a) = true :=
            spineGe2_preserved_reduces (headReduces_to_reduces hred_a) ha_ge2
          rcases closed_spineLen_le_2_shapes hv_h hsl_h with heq | ⟨x, heq⟩ | ⟨x, y, heq⟩
          · rw [heq] at hh_ge2; cases hh_ge2
          · rw [heq] at hh_ge2; cases hh_ge2
          · exact hrnf ⟨x, y, b, reduces_left (headReduces_to_reduces hred_a |> (heq ▸ ·)) b⟩
  · intro hcond
    rcases hcond with hsl | ⟨a, b, rfl, ha34⟩
    · intro ⟨x, y, z, hred⟩
      have hsp := spineLen_le_2_reduces_eq hred (closed_headLeaf_eq_s hv) hsl
      have h3le2 : 3 ≤ 2 := by
        have : spineLen (S ⋅ x ⋅ y ⋅ z) = 3 := rfl
        rw [← this, hsp]
        exact hsl
      cases h3le2 with | step h1 => cases h1 with | step h2 => cases h2
    · exact left_hn34_isRootNormalForm ha34

def isRNFClosedBool (t : Term) : Bool :=
  decide (spineLen t ≤ 2) ||
  match t with
  | .app a _ => decide (evalHN a = .hn34)
  | _ => true

theorem isRNFClosedBool_iff {t : Term} (hv : noVars t = true) :
    isRNFClosedBool t = true ↔ IsRootNormalForm t := by
  rw [footnote4_rnf_iff hv]
  unfold isRNFClosedBool
  cases t with
  | s => simp [spineLen]
  | var _ => cases hv
  | app a b =>
    cases hd1 : decide (spineLen (a ⋅ b) ≤ 2) with
    | true =>
      simp only [Bool.true_or, true_iff]
      exact Or.inl (of_decide_eq_true hd1)
    | false =>
      have hnot : ¬ spineLen (a ⋅ b) ≤ 2 := of_decide_eq_false hd1
      simp only [Bool.false_or]
      constructor
      · intro hd2
        exact Or.inr ⟨a, b, rfl, of_decide_eq_true hd2⟩
      · intro h
        rcases h with hsl | ⟨a', _, heq, ha34⟩
        · exfalso; exact hnot hsl
        · injection heq with ha _; subst ha; exact decide_eq_true ha34

theorem rnf_topTerminating {t : Term} (hrnf : IsRootNormalForm t) : TopTerminating t :=
  Acc.intro t (fun b ⟨m, hnr, hr⟩ => by
    cases hr with
    | mk x y z => exact False.elim (hrnf ⟨x, y, z, nonRootReduces_to_reduces hnr⟩))

theorem left_hn34_topTerminating {a b : Term} (ha34 : evalHN a = .hn34) : TopTerminating (a ⋅ b) :=
  rnf_topTerminating (left_hn34_isRootNormalForm ha34)

/-! ## 3. Right-Spine Automata Strata (`inGe1HN..inGe5HN`), `rightTower` Algebra, and Symbolic Collapse -/

def inGe1HN : StateHN → Bool
  | .hn1 | .hn2 | .hn3 | .hn4 | .hn5 | .hn6 | .hn7 | .hn8 | .hn9 | .hn10 | .hn11 | .hn12 | .hn13 | .hn14 | .hn15 | .hn16 | .hn17 | .hn18 | .hn19 | .hn20 | .hn21 | .hn22 | .hn23 | .hn24 | .hn25 | .hn26 | .hn27 | .hn28 | .hn29 | .hn30 | .hn31 | .hn32 | .hn33 | .hn34 => true
  | _ => false

def inGe2HN : StateHN → Bool
  | .hn2 | .hn3 | .hn4 | .hn5 | .hn7 | .hn8 | .hn9 | .hn10 | .hn11 | .hn12 | .hn13 | .hn15 | .hn16 | .hn17 | .hn19 | .hn20 | .hn21 | .hn22 | .hn23 | .hn24 | .hn25 | .hn27 | .hn28 | .hn29 | .hn30 | .hn34 => true
  | _ => false

def inGe3HN : StateHN → Bool
  | .hn3 | .hn4 | .hn5 | .hn8 | .hn9 | .hn10 | .hn12 | .hn13 | .hn17 | .hn20 | .hn21 | .hn22 | .hn23 | .hn24 | .hn25 | .hn29 | .hn30 | .hn34 => true
  | _ => false

def inGe4HN : StateHN → Bool
  | .hn4 | .hn5 | .hn8 | .hn9 | .hn10 | .hn12 | .hn13 | .hn17 | .hn20 | .hn21 | .hn22 | .hn23 | .hn24 | .hn25 | .hn29 | .hn30 | .hn34 => true
  | _ => false

def inGe5HN : StateHN → Bool
  | .hn5 | .hn8 | .hn9 | .hn10 | .hn12 | .hn13 | .hn17 | .hn20 | .hn21 | .hn22 | .hn23 | .hn24 | .hn25 | .hn29 | .hn30 | .hn34 => true
  | _ => false

private theorem ge1_chk : checkAll2_StateHN (fun x y => inGe1HN (deltaHN x y)) = true := rfl
private theorem ge2_chk : checkAll2_StateHN (fun x y => !inGe1HN y || inGe2HN (deltaHN x y)) = true := rfl
private theorem ge3_chk : checkAll2_StateHN (fun x y => !inGe2HN y || inGe3HN (deltaHN x y)) = true := rfl
private theorem ge4_chk : checkAll2_StateHN (fun x y => !inGe3HN y || inGe4HN (deltaHN x y)) = true := rfl
private theorem ge5_chk : checkAll2_StateHN (fun x y => !inGe4HN y || inGe5HN (deltaHN x y)) = true := rfl

theorem rs_ge5_evalHN {t : Term} (h : 5 ≤ rs t) : inGe5HN (evalHN t) = true := by
  cases t with
  | s => cases h
  | var _ => cases h
  | app a1 t1 =>
    cases t1 with
    | s => exfalso; exact Nat.not_succ_le_zero 3 (Nat.le_of_succ_le_succ h)
    | var _ => exfalso; exact Nat.not_succ_le_zero 3 (Nat.le_of_succ_le_succ h)
    | app a2 t2 =>
      cases t2 with
      | s => exfalso; exact Nat.not_succ_le_zero 2 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))
      | var _ => exfalso; exact Nat.not_succ_le_zero 2 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))
      | app a3 t3 =>
        cases t3 with
        | s => exfalso; exact Nat.not_succ_le_zero 1 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h)))
        | var _ => exfalso; exact Nat.not_succ_le_zero 1 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h)))
        | app a4 t4 =>
          cases t4 with
          | s => exfalso; exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))))
          | var _ => exfalso; exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))))
          | app a5 t5 =>
            have c1 := checkAll2_StateHN_sound _ ge1_chk (evalHN a5) (evalHN t5)
            have c2 := imp_bool c1 (checkAll2_StateHN_sound _ ge2_chk (evalHN a4) (evalHN (a5 ⋅ t5)))
            have c3 := imp_bool c2 (checkAll2_StateHN_sound _ ge3_chk (evalHN a3) (evalHN (a4 ⋅ (a5 ⋅ t5))))
            have c4 := imp_bool c3 (checkAll2_StateHN_sound _ ge4_chk (evalHN a2) (evalHN (a3 ⋅ (a4 ⋅ (a5 ⋅ t5)))))
            exact imp_bool c4 (checkAll2_StateHN_sound _ ge5_chk (evalHN a1) (evalHN (a2 ⋅ (a3 ⋅ (a4 ⋅ (a5 ⋅ t5))))))

def inHN0to5 : StateHN → Bool
  | .hn0 | .hn1 | .hn2 | .hn3 | .hn4 | .hn5 => true
  | _ => false

def inSCC1L : StateHN → Bool
  | .hn23 | .hn24 | .hn25 => true
  | _ => false

def inSCC1R : StateHN → Bool
  | .hn10 | .hn23 | .hn24 | .hn34 => true
  | _ => false

def checkGe5HN (p : StateHN → Bool) : Bool :=
  p .hn5 && (p .hn8 && (p .hn9 && (p .hn10 && (p .hn12 && (p .hn13 && (p .hn17 && (p .hn20 &&
  (p .hn21 && (p .hn22 && (p .hn23 && (p .hn24 && (p .hn25 && (p .hn29 && (p .hn30 && p .hn34))))))))))))))

theorem checkGe5HN_sound (p : StateHN → Bool) (h : checkGe5HN p = true) (q : StateHN) (hq : inGe5HN q = true) :
    p q = true := by
  cases q with
  | hn5 => exact and_left h
  | hn8 => exact and_left (and_right h)
  | hn9 => exact and_left (and_right (and_right h))
  | hn10 => exact and_left (and_right (and_right (and_right h)))
  | hn12 => exact and_left (and_right (and_right (and_right (and_right h))))
  | hn13 => exact and_left (and_right (and_right (and_right (and_right (and_right h)))))
  | hn17 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right h))))))
  | hn20 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right (and_right h)))))))
  | hn21 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right h))))))))
  | hn22 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right h)))))))))
  | hn23 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right h))))))))))
  | hn24 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right h)))))))))))
  | hn25 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right h))))))))))))
  | hn29 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right h)))))))))))))
  | hn30 => exact and_left (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right h))))))))))))))
  | hn34 => exact and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right (and_right h))))))))))))))
  | _ => cases hq

def checkSCC1R (p : StateHN → Bool) : Bool :=
  p .hn10 && (p .hn23 && (p .hn24 && p .hn34))

theorem checkSCC1R_sound (p : StateHN → Bool) (h : checkSCC1R p = true) (q : StateHN) (hq : inSCC1R q = true) :
    p q = true := by
  cases q with
  | hn10 => exact and_left h
  | hn23 => exact and_left (and_right h)
  | hn24 => exact and_left (and_right (and_right h))
  | hn34 => exact and_right (and_right (and_right h))
  | _ => cases hq

def inZ23_34 : StateHN → Bool
  | .hn23 | .hn34 => true
  | _ => false

private theorem hn0to5_app_chk : checkAll2_StateHN (fun x y =>
    (!inHN0to5 (deltaHN x y) || (decide (x = .hn0) && inHN0to5 y))) = true := rfl

theorem closed_inHN0to5_eq_rightTower {t : Term} (hv : noVars t = true) (h : inHN0to5 (evalHN t) = true) :
    ∃ k, t = rightTower k := by
  induction t with
  | s => exact ⟨0, rfl⟩
  | var _ => cases hv
  | app a b _ ihb =>
    have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
    have hc := imp_bool h (checkAll2_StateHN_sound _ hn0to5_app_chk (evalHN a) (evalHN b))
    have ha0 : evalHN a = .hn0 := of_decide_eq_true (and_left hc)
    have ha_s : a = S := (evalHN_eq_hn0_iff hva).mp ha0
    obtain ⟨k, hb_eq⟩ := ihb hvb (and_right hc)
    exact ⟨k + 1, by rw [ha_s, hb_eq]; rfl⟩

theorem rightTower_isNormalForm (k : Nat) : IsNormalForm (rightTower k) := by
  induction k with
  | zero => intro _ hs; cases hs
  | succ k ih =>
    intro _ hs
    cases hs with
    | left hl => cases hl
    | right hr => exact ih _ hr

theorem rightTower_reduces_eq {k : Nat} {u : Term} (h : Reduces (rightTower k) u) :
    u = rightTower k := by
  cases h with
  | refl _ => rfl
  | next hs _ => exfalso; exact rightTower_isNormalForm k _ hs

private theorem z23_34_left_hn34_chk : checkAll2_StateHN (fun z y =>
    (!inZ23_34 z || decide (deltaHN z y = .hn34))) = true := rfl

theorem z23_34_left_hn34 {z y : StateHN} (hz : inZ23_34 z = true) : deltaHN z y = .hn34 :=
  of_decide_eq_true (imp_bool hz (checkAll2_StateHN_sound _ z23_34_left_hn34_chk z y))

private theorem z23_34_m3_chk : checkAll2_StateHN (fun b z =>
    (!inZ23_34 z || inZ23_34 (deltaHN (deltaHN b z) .hn34))) = true := rfl

private theorem inZ23_34_cases {z : StateHN} (hz : inZ23_34 z = true) : z = .hn23 ∨ z = .hn34 := by
  cases z <;> first | exact Or.inl rfl | exact Or.inr rfl | cases hz

private theorem z23_sab_a_chk : checkAll2_StateHN (fun a b =>
    !decide (deltaHN (deltaHN a .hn23) (deltaHN b .hn23) ≠ .hn34) || inHN0to5 a) = true := rfl

private theorem z34_sab_a_chk : checkAll2_StateHN (fun a b =>
    !decide (deltaHN (deltaHN a .hn34) (deltaHN b .hn34) ≠ .hn34) || inHN0to5 a) = true := rfl

theorem z23_34_sab_forces_a_0to5 {a b z : StateHN}
    (hz : inZ23_34 z = true) (hne : deltaHN (deltaHN a z) (deltaHN b z) ≠ .hn34) :
    inHN0to5 a = true := by
  rcases inZ23_34_cases hz with rfl | rfl
  · exact imp_decide hne (checkAll2_StateHN_sound _ z23_sab_a_chk a b)
  · exact imp_decide hne (checkAll2_StateHN_sound _ z34_sab_a_chk a b)

private theorem z23_34_m1_non0to5_chk : checkAll1_StateHN (fun b =>
    inHN0to5 b ||
    (decide (deltaHN (deltaHN b .hn23) .hn23 = .hn34) &&
     decide (deltaHN (deltaHN b .hn23) .hn34 = .hn34) &&
     decide (deltaHN (deltaHN b .hn34) .hn23 = .hn34) &&
     decide (deltaHN (deltaHN b .hn34) .hn34 = .hn34))) = true := rfl

theorem z23_34_m1_non0to5_hn34 {b z z1 : StateHN}
    (hz : inZ23_34 z = true) (hz1 : inZ23_34 z1 = true) (hb : inHN0to5 b = false) :
    deltaHN (deltaHN b z) z1 = .hn34 := by
  have hc := checkAll1_StateHN_sound _ z23_34_m1_non0to5_chk b
  rw [hb, Bool.false_or] at hc
  have h123 := and_left hc
  have h12 := and_left h123
  rcases inZ23_34_cases hz with rfl | rfl <;> rcases inZ23_34_cases hz1 with rfl | rfl
  · exact of_decide_eq_true (and_left h12)
  · exact of_decide_eq_true (and_right h12)
  · exact of_decide_eq_true (and_right h123)
  · exact of_decide_eq_true (and_right hc)

private theorem rightTower_succ_both_z23_34 :
    ∀ (k : Nat) {c w : Term},
      inZ23_34 (evalHN c) = true → inZ23_34 (evalHN w) = true →
      ∃ u v, Reduces ((S ⋅ rightTower (k + 1) ⋅ c) ⋅ w) (S ⋅ u ⋅ v) ∧ evalHN u = .hn34 := by
  intro k
  induction k with
  | zero =>
    intro c w hc _
    refine ⟨c ⋅ w, w ⋅ (c ⋅ w), ?_, z23_34_left_hn34 hc⟩
    exact Reduces.next (Step.root (S ⋅ S) c w)
      (Reduces.next (Step.root S w (c ⋅ w)) (Reduces.refl _))
  | succ k ih =>
    intro c w hc hw
    have hcw34 : evalHN (c ⋅ w) = .hn34 := z23_34_left_hn34 hc
    have hcw_z : inZ23_34 (evalHN (c ⋅ w)) = true := by rw [hcw34]; rfl
    obtain ⟨u, v, hrest, hu34⟩ := ih hw hcw_z
    exact ⟨u, v, Reduces.next (Step.root (rightTower (k + 2)) c w) hrest, hu34⟩

theorem rightTower_both_z23_34 (k : Nat) {c w : Term}
    (hc : inZ23_34 (evalHN c) = true) (hw : inZ23_34 (evalHN w) = true) :
    ∃ u v, Reduces ((S ⋅ rightTower k ⋅ c) ⋅ w) (S ⋅ u ⋅ v) ∧ inZ23_34 (evalHN u) = true := by
  cases k with
  | zero =>
    exact ⟨w, c ⋅ w, Reduces.next (Step.root S c w) (Reduces.refl _), hw⟩
  | succ k =>
    obtain ⟨u, v, hred, hu34⟩ := rightTower_succ_both_z23_34 k hc hw
    exact ⟨u, v, hred, by rw [hu34]; rfl⟩

theorem rightTower_ne1_z23_34 (m : Nat) (hne1 : m ≠ 1) (b z : Term)
    (hz : inZ23_34 (evalHN z) = true) :
    ∃ u v, Reduces ((S ⋅ rightTower m ⋅ b) ⋅ z) (S ⋅ u ⋅ v) ∧ inZ23_34 (evalHN u) = true := by
  match m with
  | 0 =>
    exact ⟨z, b ⋅ z, Reduces.next (Step.root S b z) (Reduces.refl _), hz⟩
  | 1 =>
    exfalso; exact hne1 rfl
  | 2 =>
    have hu34 : evalHN (z ⋅ (b ⋅ z)) = .hn34 := z23_34_left_hn34 hz
    refine ⟨z ⋅ (b ⋅ z), (b ⋅ z) ⋅ (z ⋅ (b ⋅ z)), ?_, by rw [hu34]; rfl⟩
    exact Reduces.next (Step.root (S ⋅ (S ⋅ S)) b z)
      (Reduces.next (Step.root (S ⋅ S) z (b ⋅ z))
        (Reduces.next (Step.root S (b ⋅ z) (z ⋅ (b ⋅ z))) (Reduces.refl _)))
  | k + 3 =>
    let w1 := b ⋅ z
    let w2 := z ⋅ w1
    let w3 := w1 ⋅ w2
    have hw2_34 : evalHN w2 = .hn34 := z23_34_left_hn34 hz
    have hc' : inZ23_34 (evalHN w2) = true := by rw [hw2_34]; rfl
    have hw' : inZ23_34 (evalHN w3) = true := by
      change inZ23_34 (deltaHN (deltaHN (evalHN b) (evalHN z)) (evalHN w2)) = true
      rw [hw2_34]
      exact imp_bool hz (checkAll2_StateHN_sound _ z23_34_m3_chk (evalHN b) (evalHN z))
    obtain ⟨u, v, hrest, hu⟩ := rightTower_both_z23_34 k hc' hw'
    have h3 : Reduces ((S ⋅ rightTower (k + 3) ⋅ b) ⋅ z) ((S ⋅ rightTower k ⋅ w2) ⋅ w3) :=
      Reduces.next (Step.root (rightTower (k + 3)) b z)
        (Reduces.next (Step.root (rightTower (k + 2)) z w1)
          (Reduces.next (Step.root (rightTower (k + 1)) w1 w2) (Reduces.refl _)))
    exact ⟨u, v, reduces_trans h3 hrest, hu⟩

/-! ## 4. Four-Phase Constructive Proof of Waldmann's Top-Termination Theorem (Theorem 29) -/

def transientRank (ql qr : StateHN) : Nat :=
  if inSCC1L ql && inSCC1R qr then 0
  else match qr with
    | .hn12 | .hn13 => 2
    | _ => 1

def trStepOk (x y z : StateHN) : Bool :=
  let s2 := deltaHN (deltaHN .hn0 x) y
  let u := deltaHN x z
  let v := deltaHN y z
  let r0 := transientRank s2 z
  let r1 := transientRank u v
  if r0 == 0 then decide (r1 = 0) else decide (r1 < r0)

private theorem tr_row_0 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn0; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn0 z ≠ .hn34) || trStepOk .hn0 y z)))) = true := rfl
private theorem tr_row_1 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn1; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn1 z ≠ .hn34) || trStepOk .hn1 y z)))) = true := rfl
private theorem tr_row_2 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn2; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn2 z ≠ .hn34) || trStepOk .hn2 y z)))) = true := rfl
private theorem tr_row_3 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn3; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn3 z ≠ .hn34) || trStepOk .hn3 y z)))) = true := rfl
private theorem tr_row_4 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn4; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn4 z ≠ .hn34) || trStepOk .hn4 y z)))) = true := rfl
private theorem tr_row_5 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn5; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn5 z ≠ .hn34) || trStepOk .hn5 y z)))) = true := rfl
private theorem tr_row_6 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn6; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn6 z ≠ .hn34) || trStepOk .hn6 y z)))) = true := rfl
private theorem tr_row_7 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn7; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn7 z ≠ .hn34) || trStepOk .hn7 y z)))) = true := rfl
private theorem tr_row_8 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn8; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn8 z ≠ .hn34) || trStepOk .hn8 y z)))) = true := rfl
private theorem tr_row_9 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn9; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn9 z ≠ .hn34) || trStepOk .hn9 y z)))) = true := rfl
private theorem tr_row_10 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn10; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn10 z ≠ .hn34) || trStepOk .hn10 y z)))) = true := rfl
private theorem tr_row_11 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn11; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn11 z ≠ .hn34) || trStepOk .hn11 y z)))) = true := rfl
private theorem tr_row_12 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn12; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn12 z ≠ .hn34) || trStepOk .hn12 y z)))) = true := rfl
private theorem tr_row_13 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn13; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn13 z ≠ .hn34) || trStepOk .hn13 y z)))) = true := rfl
private theorem tr_row_14 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn14; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn14 z ≠ .hn34) || trStepOk .hn14 y z)))) = true := rfl
private theorem tr_row_15 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn15; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn15 z ≠ .hn34) || trStepOk .hn15 y z)))) = true := rfl
private theorem tr_row_16 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn16; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn16 z ≠ .hn34) || trStepOk .hn16 y z)))) = true := rfl
private theorem tr_row_17 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn17; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn17 z ≠ .hn34) || trStepOk .hn17 y z)))) = true := rfl
private theorem tr_row_18 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn18; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn18 z ≠ .hn34) || trStepOk .hn18 y z)))) = true := rfl
private theorem tr_row_19 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn19; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn19 z ≠ .hn34) || trStepOk .hn19 y z)))) = true := rfl
private theorem tr_row_20 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn20; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn20 z ≠ .hn34) || trStepOk .hn20 y z)))) = true := rfl
private theorem tr_row_21 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn21; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn21 z ≠ .hn34) || trStepOk .hn21 y z)))) = true := rfl
private theorem tr_row_22 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn22; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn22 z ≠ .hn34) || trStepOk .hn22 y z)))) = true := rfl
private theorem tr_row_23 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn23; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn23 z ≠ .hn34) || trStepOk .hn23 y z)))) = true := rfl
private theorem tr_row_24 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn24; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn24 z ≠ .hn34) || trStepOk .hn24 y z)))) = true := rfl
private theorem tr_row_25 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn25; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn25 z ≠ .hn34) || trStepOk .hn25 y z)))) = true := rfl
private theorem tr_row_26 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn26; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn26 z ≠ .hn34) || trStepOk .hn26 y z)))) = true := rfl
private theorem tr_row_27 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn27; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn27 z ≠ .hn34) || trStepOk .hn27 y z)))) = true := rfl
private theorem tr_row_28 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn28; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn28 z ≠ .hn34) || trStepOk .hn28 y z)))) = true := rfl
private theorem tr_row_29 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn29; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn29 z ≠ .hn34) || trStepOk .hn29 y z)))) = true := rfl
private theorem tr_row_30 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn30; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn30 z ≠ .hn34) || trStepOk .hn30 y z)))) = true := rfl
private theorem tr_row_31 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn31; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn31 z ≠ .hn34) || trStepOk .hn31 y z)))) = true := rfl
private theorem tr_row_32 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn32; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn32 z ≠ .hn34) || trStepOk .hn32 y z)))) = true := rfl
private theorem tr_row_33 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn33; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn33 z ≠ .hn34) || trStepOk .hn33 y z)))) = true := rfl
private theorem tr_row_34 : checkGe5HN (fun y => let s1 := deltaHN .hn0 .hn34; let s2 := deltaHN s1 y; checkGe5HN (fun z => (!decide (deltaHN s2 z = .hn34) || (!decide (deltaHN .hn34 z ≠ .hn34) || trStepOk .hn34 y z)))) = true := rfl

private theorem trStepOk_sound {x y z : StateHN}
    (hy : inGe5HN y = true) (hz : inGe5HN z = true)
    (h34 : deltaHN (deltaHN (deltaHN .hn0 x) y) z = .hn34)
    (hu : deltaHN x z ≠ .hn34) :
    trStepOk x y z = true := by
  have hc : (!decide (deltaHN (deltaHN (deltaHN .hn0 x) y) z = .hn34) || (!decide (deltaHN x z ≠ .hn34) || trStepOk x y z)) = true :=
    match x with
    | .hn0 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_0 y hy) z hz
    | .hn1 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_1 y hy) z hz
    | .hn2 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_2 y hy) z hz
    | .hn3 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_3 y hy) z hz
    | .hn4 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_4 y hy) z hz
    | .hn5 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_5 y hy) z hz
    | .hn6 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_6 y hy) z hz
    | .hn7 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_7 y hy) z hz
    | .hn8 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_8 y hy) z hz
    | .hn9 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_9 y hy) z hz
    | .hn10 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_10 y hy) z hz
    | .hn11 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_11 y hy) z hz
    | .hn12 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_12 y hy) z hz
    | .hn13 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_13 y hy) z hz
    | .hn14 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_14 y hy) z hz
    | .hn15 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_15 y hy) z hz
    | .hn16 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_16 y hy) z hz
    | .hn17 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_17 y hy) z hz
    | .hn18 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_18 y hy) z hz
    | .hn19 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_19 y hy) z hz
    | .hn20 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_20 y hy) z hz
    | .hn21 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_21 y hy) z hz
    | .hn22 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_22 y hy) z hz
    | .hn23 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_23 y hy) z hz
    | .hn24 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_24 y hy) z hz
    | .hn25 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_25 y hy) z hz
    | .hn26 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_26 y hy) z hz
    | .hn27 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_27 y hy) z hz
    | .hn28 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_28 y hy) z hz
    | .hn29 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_29 y hy) z hz
    | .hn30 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_30 y hy) z hz
    | .hn31 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_31 y hy) z hz
    | .hn32 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_32 y hy) z hz
    | .hn33 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_33 y hy) z hz
    | .hn34 => checkGe5HN_sound _ (checkGe5HN_sound _ tr_row_34 y hy) z hz
  exact imp_decide hu (imp_decide h34 hc)

private theorem t2_row_0 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn0) w; let vw := deltaHN .hn0 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_1 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn1) w; let vw := deltaHN .hn1 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_2 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn2) w; let vw := deltaHN .hn2 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_3 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn3) w; let vw := deltaHN .hn3 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_4 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn4) w; let vw := deltaHN .hn4 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_5 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn5) w; let vw := deltaHN .hn5 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_6 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn6) w; let vw := deltaHN .hn6 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_7 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn7) w; let vw := deltaHN .hn7 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_8 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn8) w; let vw := deltaHN .hn8 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_9 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn9) w; let vw := deltaHN .hn9 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_10 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn10) w; let vw := deltaHN .hn10 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_11 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn11) w; let vw := deltaHN .hn11 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_12 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn12) w; let vw := deltaHN .hn12 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_13 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn13) w; let vw := deltaHN .hn13 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_14 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn14) w; let vw := deltaHN .hn14 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_15 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn15) w; let vw := deltaHN .hn15 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_16 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn16) w; let vw := deltaHN .hn16 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_17 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn17) w; let vw := deltaHN .hn17 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_18 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn18) w; let vw := deltaHN .hn18 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_19 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn19) w; let vw := deltaHN .hn19 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_20 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn20) w; let vw := deltaHN .hn20 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_21 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn21) w; let vw := deltaHN .hn21 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_22 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn22) w; let vw := deltaHN .hn22 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_23 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn23) w; let vw := deltaHN .hn23 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_24 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn24) w; let vw := deltaHN .hn24 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_25 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn25) w; let vw := deltaHN .hn25 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_26 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn26) w; let vw := deltaHN .hn26 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_27 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn27) w; let vw := deltaHN .hn27 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_28 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn28) w; let vw := deltaHN .hn28 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_29 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn29) w; let vw := deltaHN .hn29 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_30 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn30) w; let vw := deltaHN .hn30 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_31 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn31) w; let vw := deltaHN .hn31 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_32 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn32) w; let vw := deltaHN .hn32 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_33 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn33) w; let vw := deltaHN .hn33 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl
private theorem t2_row_34 : checkGe5HN (fun w => let s2w := deltaHN (deltaHN .hn1 .hn34) w; let vw := deltaHN .hn34 w; checkSCC1R (fun z => (!inSCC1L s2w || inZ23_34 (deltaHN vw z)))) = true := rfl

private theorem scc1R_collapse_direct_chk : checkSCC1R (fun y =>
    checkSCC1R (fun z => inZ23_34 (deltaHN y z))) = true := rfl

private theorem p3_u_23_23_chk : checkAll1_StateHN (fun q =>
    !decide (deltaHN (deltaHN q .hn23) .hn23 = .hn34) || (!decide (deltaHN q .hn23 ≠ .hn34) || inSCC1L (deltaHN q .hn23))) = true := rfl
private theorem p3_u_23_34_chk : checkAll1_StateHN (fun q =>
    !decide (deltaHN (deltaHN q .hn23) .hn34 = .hn34) || (!decide (deltaHN q .hn23 ≠ .hn34) || inSCC1L (deltaHN q .hn23))) = true := rfl
private theorem p3_u_34_23_chk : checkAll1_StateHN (fun q =>
    !decide (deltaHN (deltaHN q .hn34) .hn23 = .hn34) || (!decide (deltaHN q .hn34 ≠ .hn34) || inSCC1L (deltaHN q .hn34))) = true := rfl
private theorem p3_u_34_34_chk : checkAll1_StateHN (fun q =>
    !decide (deltaHN (deltaHN q .hn34) .hn34 = .hn34) || (!decide (deltaHN q .hn34 ≠ .hn34) || inSCC1L (deltaHN q .hn34))) = true := rfl

/-- **Lemma T2 (1-Step `R`-Collapse from `SCC 1` into `{.hn23, .hn34}`)**:
    Whenever `x1 ⋅ z1 →* S ⋅ x2 ⋅ y2` with `inSCC1L (evalHN (x1 ⋅ z1)) = true`,
    `inSCC1R (evalHN z1) = true`, `5 ≤ rs z1`, and `inSCC1R (evalHN z2) = true`,
    the new right child `y2 ⋅ z2` satisfies `inZ23_34 (evalHN (y2 ⋅ z2)) = true`. -/
theorem lemma_T2_r_collapse {x1 z1 x2 y2 z2 : Term}
    (hred : Reduces (x1 ⋅ z1) (S ⋅ x2 ⋅ y2))
    (hsccL : inSCC1L (evalHN (x1 ⋅ z1)) = true)
    (hz1_scc : inSCC1R (evalHN z1) = true)
    (hz1_rs : 5 ≤ rs z1)
    (hz2_scc : inSCC1R (evalHN z2) = true) :
    inZ23_34 (evalHN (y2 ⋅ z2)) = true := by
  rcases app_reduces_s2_dichotomy hred x1 z1 x2 y2 rfl rfl with ⟨_, hz1y2⟩ | ⟨v, w, hm, _, hvw⟩
  · have hy2_scc : inSCC1R (evalHN y2) = true := by
      rw [← evalHN_reduces hz1y2]
      exact hz1_scc
    change inZ23_34 (deltaHN (evalHN y2) (evalHN z2)) = true
    exact checkSCC1R_sound _ (checkSCC1R_sound _ scc1R_collapse_direct_chk (evalHN y2) hy2_scc) (evalHN z2) hz2_scc
  · have hrs_m : 1 + rs z1 ≤ 1 + rs w := rs_mono_reduces hm
    have hw_rs : 5 ≤ rs w := Nat.le_trans hz1_rs (le_of_one_add_le_one_add hrs_m)
    have hw_ge5 : inGe5HN (evalHN w) = true := rs_ge5_evalHN hw_rs
    have h_v_w_sccL : inSCC1L (deltaHN (deltaHN .hn1 (evalHN v)) (evalHN w)) = true := by
      have heq : evalHN (x1 ⋅ z1) = deltaHN (deltaHN .hn1 (evalHN v)) (evalHN w) := evalHN_reduces hm
      rw [← heq]
      exact hsccL
    have hy2_eq : evalHN y2 = deltaHN (evalHN v) (evalHN w) := (evalHN_reduces hvw).symm
    have hc : (!inSCC1L (deltaHN (deltaHN .hn1 (evalHN v)) (evalHN w)) || inZ23_34 (deltaHN (deltaHN (evalHN v) (evalHN w)) (evalHN z2))) = true :=
      match evalHN v with
    | .hn0 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_0 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn1 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_1 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn2 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_2 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn3 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_3 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn4 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_4 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn5 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_5 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn6 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_6 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn7 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_7 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn8 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_8 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn9 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_9 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn10 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_10 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn11 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_11 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn12 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_12 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn13 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_13 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn14 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_14 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn15 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_15 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn16 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_16 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn17 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_17 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn18 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_18 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn19 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_19 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn20 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_20 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn21 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_21 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn22 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_22 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn23 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_23 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn24 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_24 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn25 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_25 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn26 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_26 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn27 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_27 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn28 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_28 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn29 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_29 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn30 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_30 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn31 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_31 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn32 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_32 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn33 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_33 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    | .hn34 => checkSCC1R_sound _ (checkGe5HN_sound _ t2_row_34 (evalHN w) hw_ge5) (evalHN z2) hz2_scc
    change inZ23_34 (deltaHN (evalHN y2) (evalHN z2)) = true
    rw [hy2_eq]
    exact imp_bool h_v_w_sccL hc

/-- Phase 3 invariant on `(x ⋅ z) ⋅ r`. -/
structure P3State (x z r : Term) : Prop where
  hv_x : noVars x = true
  hv_z : noVars z = true
  hv_r : noVars r = true
  rs_z : 5 ≤ rs z
  rs_r : 5 ≤ rs r
  z_23_34 : inZ23_34 (evalHN z) = true
  r_23_34 : inZ23_34 (evalHN r) = true
  tot_34 : evalHN ((x ⋅ z) ⋅ r) = .hn34

private theorem inZ23_34_implies_inSCC1R {q : StateHN} (h : inZ23_34 q = true) : inSCC1R q = true := by
  cases q <;> cases h <;> rfl

private theorem p3_xz_in_scc1L {x z r : Term} (hp : P3State x z r) (hne : evalHN (x ⋅ z) ≠ .hn34) :
    inSCC1L (evalHN (x ⋅ z)) = true := by
  have htot : deltaHN (deltaHN (evalHN x) (evalHN z)) (evalHN r) = .hn34 := hp.tot_34
  have hxz : deltaHN (evalHN x) (evalHN z) ≠ .hn34 := hne
  change inSCC1L (deltaHN (evalHN x) (evalHN z)) = true
  rcases inZ23_34_cases hp.z_23_34 with hzeq | hzeq <;>
    rcases inZ23_34_cases hp.r_23_34 with hreq | hreq
  · rw [hzeq] at htot hxz ⊢; rw [hreq] at htot
    exact imp_decide hxz (imp_decide htot (checkAll1_StateHN_sound _ p3_u_23_23_chk (evalHN x)))
  · rw [hzeq] at htot hxz ⊢; rw [hreq] at htot
    exact imp_decide hxz (imp_decide htot (checkAll1_StateHN_sound _ p3_u_23_34_chk (evalHN x)))
  · rw [hzeq] at htot hxz ⊢; rw [hreq] at htot
    exact imp_decide hxz (imp_decide htot (checkAll1_StateHN_sound _ p3_u_34_23_chk (evalHN x)))
  · rw [hzeq] at htot hxz ⊢; rw [hreq] at htot
    exact imp_decide hxz (imp_decide htot (checkAll1_StateHN_sound _ p3_u_34_34_chk (evalHN x)))

private theorem p3_step_preserves {x z r x1 y1 z1 : Term} (hp : P3State x z r)
    (hred_l : Reduces (x ⋅ z) (S ⋅ x1 ⋅ y1)) (hred_r : Reduces r z1) :
    P3State x1 z1 (y1 ⋅ z1) := by
  have hv_xz : noVars (x ⋅ z) = true := (Bool.and_eq_true _ _).mpr ⟨hp.hv_x, hp.hv_z⟩
  have hv_sxy := noVars_reduces hred_l hv_xz
  have hv_sx := ((Bool.and_eq_true _ _).mp hv_sxy).1
  have hv_y1 := ((Bool.and_eq_true _ _).mp hv_sxy).2
  have hv_x1 := ((Bool.and_eq_true _ _).mp hv_sx).2
  have hv_z1 := noVars_reduces hred_r hp.hv_r
  have hv_r1 : noVars (y1 ⋅ z1) = true := (Bool.and_eq_true _ _).mpr ⟨hv_y1, hv_z1⟩
  have hrs_z1 : 5 ≤ rs z1 := Nat.le_trans hp.rs_r (rs_mono_reduces hred_r)
  have hrs_r1 : 5 ≤ rs (y1 ⋅ z1) := Nat.le_trans hrs_z1 (Nat.le_add_left (rs z1) 1)
  have hz1_23_34 : inZ23_34 (evalHN z1) = true := by
    rw [← evalHN_reduces hred_r]; exact hp.r_23_34
  have hxz_ne34 : evalHN (x ⋅ z) ≠ .hn34 := by
    rw [evalHN_reduces hred_l]
    exact deltaHN_s2_ne_hn34 (evalHN x1) (evalHN y1)
  have hsccL := p3_xz_in_scc1L hp hxz_ne34
  have hr1_23_34 : inZ23_34 (evalHN (y1 ⋅ z1)) = true :=
    lemma_T2_r_collapse hred_l hsccL (inZ23_34_implies_inSCC1R hp.z_23_34) hp.rs_z (inZ23_34_implies_inSCC1R hz1_23_34)
  have htot1 : evalHN ((x1 ⋅ z1) ⋅ (y1 ⋅ z1)) = .hn34 :=
    (evalHN_step (Step.root x1 y1 z1)).symm.trans ((evalHN_reduces (reduces_app hred_l hred_r)).symm.trans hp.tot_34)
  exact ⟨hv_x1, hv_z1, hv_r1, hrs_z1, hrs_r1, hz1_23_34, hr1_23_34, htot1⟩

/-- Case C of Phase 3 (`hasSpineGe2 x = true`): at most 2 more `RelRootStep`s before `.hn34`. -/
private theorem phase3_spineGe2_acc {x z r : Term} (hp : P3State x z r) (hsp2 : hasSpineGe2 x = true) :
    TopTerminating ((x ⋅ z) ⋅ r) := by
  refine Acc.intro ((x ⋅ z) ⋅ r) (fun b1 hrel1 => ?_)
  obtain ⟨x1, y1, z1, hred_l1, hred_r1, hb1⟩ := relRootStep_app_inv hrel1
  subst hb1
  have hp1 : P3State x1 z1 (y1 ⋅ z1) := p3_step_preserves hp hred_l1 hred_r1
  have hxz_ne34 : evalHN (x ⋅ z) ≠ .hn34 := by
    rw [evalHN_reduces hred_l1]
    exact deltaHN_s2_ne_hn34 (evalHN x1) (evalHN y1)
  have hx_ne34 : evalHN x ≠ .hn34 := deltaHN_ne_hn34_left hxz_ne34
  obtain ⟨hred_xh, hv_xh, hsl_xh⟩ := headNormalize_reduces_hnf hp.hv_x hx_ne34
  have hxh_ge2 : hasSpineGe2 (headNormalize x) = true :=
    spineGe2_preserved_reduces (headReduces_to_reduces hred_xh) hsp2
  rcases closed_spineLen_le_2_shapes hv_xh hsl_xh with heq | ⟨u0, heq⟩ | ⟨a0, b0, heq⟩
  · rw [heq] at hxh_ge2; cases hxh_ge2
  · rw [heq] at hxh_ge2; cases hxh_ge2
  · have hred_x_sab : Reduces x (S ⋅ a0 ⋅ b0) := heq ▸ headReduces_to_reduces hred_xh
    have hv_sab : noVars (S ⋅ a0 ⋅ b0) = true := heq ▸ hv_xh
    have hv_b0 : noVars b0 = true := ((Bool.and_eq_true _ _).mp hv_sab).2
    have hv_a0 : noVars a0 = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv_sab).1).2
    have habz_ne34 : deltaHN (deltaHN (evalHN a0) (evalHN z)) (deltaHN (evalHN b0) (evalHN z)) ≠ .hn34 := by
      rw [← deltaHN_s_law]
      change evalHN ((S ⋅ a0 ⋅ b0) ⋅ z) ≠ .hn34
      rw [← evalHN_reduces (reduces_left hred_x_sab z)]
      exact hxz_ne34
    have ha0_0to5 : inHN0to5 (evalHN a0) = true := z23_34_sab_forces_a_0to5 hp.z_23_34 habz_ne34
    obtain ⟨m, rfl⟩ := closed_inHN0to5_eq_rightTower hv_a0 ha0_0to5
    exact if hm1 : m = 1 then by
      subst hm1
      -- `m = 1`: `(S ⋅ (S ⋅ S) ⋅ b0) ⋅ z →2 S ⋅ (b0 ⋅ z) ⋅ (z ⋅ (b0 ⋅ z))`
      have hbranch1 : Reduces (x ⋅ z) (S ⋅ (b0 ⋅ z) ⋅ (z ⋅ (b0 ⋅ z))) :=
        reduces_trans (reduces_left hred_x_sab z)
          (Reduces.next (Step.root (S ⋅ S) b0 z)
            (Reduces.next (Step.root S z (b0 ⋅ z)) (Reduces.refl _)))
      obtain ⟨dx, _, hdx_x1, hdx_bz, _, _⟩ := s2_common_reduct hred_l1 hbranch1
      have hx1_eq_bz : evalHN x1 = evalHN (b0 ⋅ z) :=
        (evalHN_reduces hdx_x1).trans (evalHN_reduces hdx_bz).symm
      cases hb0_chk : inHN0to5 (evalHN b0) with
      | false =>
        have hx1z1_34 : evalHN (x1 ⋅ z1) = .hn34 := by
          change deltaHN (evalHN x1) (evalHN z1) = .hn34
          rw [hx1_eq_bz]
          exact z23_34_m1_non0to5_hn34 hp.z_23_34 hp1.z_23_34 hb0_chk
        exact left_hn34_topTerminating hx1z1_34
      | true =>
        obtain ⟨r0, rfl⟩ := closed_inHN0to5_eq_rightTower hv_b0 hb0_chk
        cases r0 with
        | zero =>
          -- `b0 = S`: `S ⋅ z →* dx`, so `dx = S ⋅ z'`, forcing `x1 = S ⋅ p1` with `inZ23_34 (evalHN p1)`!
          obtain ⟨z', hdx_eq, hzz'⟩ := s_app_reduces_any hdx_bz z rfl
          subst hdx_eq
          obtain ⟨p1, rfl, hp1z'⟩ := reduces_to_s1_inv hdx_x1
          have hp1_23_34 : inZ23_34 (evalHN p1) = true := by
            rw [evalHN_reduces hp1z', ← evalHN_reduces hzz']
            exact hp.z_23_34
          refine Acc.intro ((S ⋅ p1 ⋅ z1) ⋅ (y1 ⋅ z1)) (fun b2 hrel2 => ?_)
          obtain ⟨x2, _, z2, hred_l2, hred_r2, hb2⟩ := relRootStep_app_inv hrel2
          subst hb2
          obtain ⟨x2', _, heq2, hp1x2, _⟩ := s2_app_reduces_any hred_l2 p1 z1 rfl
          injection heq2 with hsx2 _
          injection hsx2 with _ hx2eq
          subst hx2eq
          have hx2_23_34 : inZ23_34 (evalHN x2) = true := by
            rw [← evalHN_reduces hp1x2]; exact hp1_23_34
          exact left_hn34_topTerminating (z23_34_left_hn34 hx2_23_34)
        | succ k0 =>
          -- `b0 = S ⋅ rightTower k0`: `S ⋅ rightTower k0 ⋅ z →* dx`, so `dx = S ⋅ rightTower k0 ⋅ z'`!
          obtain ⟨a', z', hdx_eq, hra', hzz'⟩ := s2_app_reduces_any hdx_bz (rightTower k0) z rfl
          rw [rightTower_reduces_eq hra'] at hdx_eq
          subst hdx_eq
          have hz'_23_34 : inZ23_34 (evalHN z') = true := by
            rw [← evalHN_reduces hzz']; exact hp.z_23_34
          refine Acc.intro ((x1 ⋅ z1) ⋅ (y1 ⋅ z1)) (fun b2 hrel2 => ?_)
          obtain ⟨x2, y2, z2, hred_l2, _, hb2⟩ := relRootStep_app_inv hrel2
          subst hb2
          obtain ⟨u2, v2, hrt2, hu2_23_34⟩ := rightTower_both_z23_34 k0 hz'_23_34 hp1.z_23_34
          have hbranch2 : Reduces (x1 ⋅ z1) (S ⋅ u2 ⋅ v2) :=
            reduces_trans (reduces_left hdx_x1 z1) hrt2
          obtain ⟨dx2, _, hx2_dx2, hu2_dx2, _, _⟩ := s2_common_reduct hred_l2 hbranch2
          have hx2_23_34 : inZ23_34 (evalHN x2) = true := by
            rw [evalHN_reduces hx2_dx2, ← evalHN_reduces hu2_dx2]
            exact hu2_23_34
          exact left_hn34_topTerminating (z23_34_left_hn34 hx2_23_34)
    else by
      -- `m ≠ 1`: `rightTower_ne1_z23_34` directly gives `inZ23_34 (evalHN x1) = true`, so `b1` is RNF!
      obtain ⟨u1, v1, hrt1, hu1_23_34⟩ := rightTower_ne1_z23_34 m hm1 b0 z hp.z_23_34
      have hbranch1 : Reduces (x ⋅ z) (S ⋅ u1 ⋅ v1) :=
        reduces_trans (reduces_left hred_x_sab z) hrt1
      obtain ⟨dx1, _, hx1_dx1, hu1_dx1, _, _⟩ := s2_common_reduct hred_l1 hbranch1
      have hx1_23_34 : inZ23_34 (evalHN x1) = true := by
        rw [evalHN_reduces hx1_dx1, ← evalHN_reduces hu1_dx1]
        exact hu1_23_34
      exact left_hn34_topTerminating (z23_34_left_hn34 hx1_23_34)

/-- Phase 3 complete: induction on `k ≥ sPrefix x` peels `S ⋅` prefixes down to `hasSpineGe2`. -/
private theorem phase3_acc_aux :
    ∀ (k : Nat) {x z r : Term}, P3State x z r → sPrefix x ≤ k → TopTerminating ((x ⋅ z) ⋅ r) := by
  intro k
  induction k with
  | zero =>
    intro x z r hp hle
    cases x with
    | s =>
      refine Acc.intro ((S ⋅ z) ⋅ r) (fun b hrel => ?_)
      obtain ⟨x1, y1, _, hred_l, _, _⟩ := relRootStep_app_inv hrel
      obtain ⟨z', heq, _⟩ := s_app_reduces_any hred_l z rfl
      injection heq with hs _
      cases hs
    | var _ => cases hp.hv_x
    | app x1 x2 =>
      cases x1 with
      | s =>
        exfalso
        exact Nat.not_succ_le_zero 0 (Nat.le_trans (Nat.le_add_right 1 (sPrefix x2)) hle)
      | var _ => cases ((Bool.and_eq_true _ _).mp hp.hv_x).1
      | app _ _ =>
        exact phase3_spineGe2_acc hp rfl
  | succ k ih =>
    intro x z r hp hle
    cases x with
    | s =>
      refine Acc.intro ((S ⋅ z) ⋅ r) (fun b hrel => ?_)
      obtain ⟨x1, y1, _, hred_l, _, _⟩ := relRootStep_app_inv hrel
      obtain ⟨z', heq, _⟩ := s_app_reduces_any hred_l z rfl
      injection heq with hs _
      cases hs
    | var _ => cases hp.hv_x
    | app x1 p =>
      cases x1 with
      | s =>
        have hp_le : sPrefix p ≤ k := by
          rw [Nat.add_comm k 1] at hle
          exact le_of_one_add_le_one_add hle
        refine Acc.intro (((S ⋅ p) ⋅ z) ⋅ r) (fun b1 hrel1 => ?_)
        obtain ⟨x', y', z', hred_l, hred_r, hb1⟩ := relRootStep_app_inv hrel1
        subst hb1
        have hp1 : P3State x' z' (y' ⋅ z') := p3_step_preserves hp hred_l hred_r
        obtain ⟨x'', y'', heq, hpx', _⟩ := s2_app_reduces_any hred_l p z rfl
        injection heq with hsx _
        injection hsx with _ hxeq
        subst hxeq
        have hx'_le : sPrefix x' ≤ k := by
          rw [sPrefix_reduces hpx']
          exact hp_le
        exact ih hp1 hx'_le
      | var _ => cases ((Bool.and_eq_true _ _).mp hp.hv_x).1
      | app _ _ =>
        exact phase3_spineGe2_acc hp rfl

theorem phase3_acc {x z r : Term} (hp : P3State x z r) : TopTerminating ((x ⋅ z) ⋅ r) :=
  phase3_acc_aux (sPrefix x) hp (Nat.le_refl _)

private theorem transientRank_eq_zero_iff (ql qr : StateHN) :
    transientRank ql qr = 0 ↔ (inSCC1L ql = true ∧ inSCC1R qr = true) := by
  unfold transientRank
  cases hb : (inSCC1L ql && inSCC1R qr) with
  | true =>
    change 0 = 0 ↔ _
    exact ⟨fun _ => (Bool.and_eq_true _ _).mp hb, fun _ => rfl⟩
  | false =>
    change (match qr with | .hn12 | .hn13 => 2 | _ => 1) = 0 ↔ _
    constructor
    · intro h; cases qr <;> cases h
    · intro ⟨h1, h2⟩
      have ht : (inSCC1L ql && inSCC1R qr) = true := (Bool.and_eq_true _ _).mpr ⟨h1, h2⟩
      rw [hb] at ht; cases ht

/-- Helper: in `SCC 1`, any valid root step stays in `SCC 1` (unless `evalHN (x ⋅ z) = .hn34`). -/
private theorem scc1_preserved {x y z : StateHN}
    (hy : inGe5HN y = true) (hz : inGe5HN z = true)
    (hsccL : inSCC1L (deltaHN (deltaHN .hn0 x) y) = true)
    (hsccR : inSCC1R z = true)
    (h34 : deltaHN (deltaHN (deltaHN .hn0 x) y) z = .hn34)
    (hu : deltaHN x z ≠ .hn34) :
    inSCC1L (deltaHN x z) = true ∧ inSCC1R (deltaHN y z) = true := by
  have hok := trStepOk_sound hy hz h34 hu
  dsimp only [trStepOk] at hok
  have hr0 : transientRank (deltaHN (deltaHN .hn0 x) y) z = 0 :=
    (transientRank_eq_zero_iff _ _).mpr ⟨hsccL, hsccR⟩
  rw [hr0] at hok
  change decide (transientRank (deltaHN x z) (deltaHN y z) = 0) = true at hok
  exact (transientRank_eq_zero_iff _ _).mp (of_decide_eq_true hok)

/-- Phase 2 complete: 3-step bridge from arbitrary `(l, r)` in `SCC 1` into `P3State`! -/
theorem phase2_scc1_acc {l r : Term}
    (hvl : noVars l = true) (hvr : noVars r = true)
    (hrsl : 6 ≤ rs l) (hrsr : 6 ≤ rs r)
    (hsccL : inSCC1L (evalHN l) = true) (hsccR : inSCC1R (evalHN r) = true)
    (h34 : evalHN (l ⋅ r) = .hn34) :
    TopTerminating (l ⋅ r) := by
  -- Bridge Step 1: `(l ⋅ r) ▷ (x1 ⋅ z1) ⋅ (y1 ⋅ z1)`
  refine Acc.intro (l ⋅ r) (fun b1 hrel1 => ?_)
  obtain ⟨x1, y1, z1, hred_l1, hred_r1, hb1⟩ := relRootStep_app_inv hrel1
  subst hb1
  cases hd1 : decide (evalHN (x1 ⋅ z1) = .hn34) with
  | true => exact left_hn34_topTerminating (of_decide_eq_true hd1)
  | false =>
    have hu1 : evalHN (x1 ⋅ z1) ≠ .hn34 := of_decide_eq_false hd1
    have hv_sxy1 := noVars_reduces hred_l1 hvl
    have hv_x1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv_sxy1).1).2
    have hv_y1 := ((Bool.and_eq_true _ _).mp hv_sxy1).2
    have hv_z1 := noVars_reduces hred_r1 hvr
    have hrs_y1 : 5 ≤ rs y1 := le_of_one_add_le_one_add (Nat.le_trans hrsl (rs_mono_reduces hred_l1))
    have hrs_z1 : 6 ≤ rs z1 := Nat.le_trans hrsr (rs_mono_reduces hred_r1)
    have hrs_z1_5 : 5 ≤ rs z1 := Nat.le_trans (by decide : 5 ≤ 6) hrs_z1
    have hs2_1_eq : deltaHN (deltaHN .hn0 (evalHN x1)) (evalHN y1) = evalHN l := (evalHN_reduces hred_l1).symm
    have hz1_eq : evalHN z1 = evalHN r := (evalHN_reduces hred_r1).symm
    have h34_1 : deltaHN (deltaHN (deltaHN .hn0 (evalHN x1)) (evalHN y1)) (evalHN z1) = .hn34 := by
      rw [hs2_1_eq, hz1_eq]; exact h34
    have ⟨hsccL1, hsccR1⟩ := scc1_preserved (rs_ge5_evalHN hrs_y1) (rs_ge5_evalHN hrs_z1_5)
      (hs2_1_eq.symm ▸ hsccL) (hz1_eq.symm ▸ hsccR) h34_1 hu1
    have htot1 : evalHN ((x1 ⋅ z1) ⋅ (y1 ⋅ z1)) = .hn34 :=
      (evalHN_step (Step.root x1 y1 z1)).symm.trans h34_1
    -- Bridge Step 2: `((x1 ⋅ z1) ⋅ (y1 ⋅ z1)) ▷ (x2 ⋅ z2) ⋅ (y2 ⋅ z2)` where `inZ23_34 (evalHN (y2 ⋅ z2))`!
    refine Acc.intro ((x1 ⋅ z1) ⋅ (y1 ⋅ z1)) (fun b2 hrel2 => ?_)
    obtain ⟨x2, y2, z2, hred_l2, hred_r2, hb2⟩ := relRootStep_app_inv hrel2
    subst hb2
    cases hd2 : decide (evalHN (x2 ⋅ z2) = .hn34) with
    | true => exact left_hn34_topTerminating (of_decide_eq_true hd2)
    | false =>
      have hu2 : evalHN (x2 ⋅ z2) ≠ .hn34 := of_decide_eq_false hd2
      have hv_sxy2 := noVars_reduces hred_l2 ((Bool.and_eq_true _ _).mpr ⟨hv_x1, hv_z1⟩)
      have hv_x2 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv_sxy2).1).2
      have hv_y2 := ((Bool.and_eq_true _ _).mp hv_sxy2).2
      have hv_z2 := noVars_reduces hred_r2 ((Bool.and_eq_true _ _).mpr ⟨hv_y1, hv_z1⟩)
      have hrs_y2 : 5 ≤ rs y2 := le_of_one_add_le_one_add (Nat.le_trans (Nat.add_le_add_left hrs_z1_5 1) (rs_mono_reduces hred_l2))
      have hrs_z2 : 6 ≤ rs z2 := Nat.le_trans (Nat.add_le_add_left hrs_z1_5 1) (rs_mono_reduces hred_r2)
      have hrs_z2_5 : 5 ≤ rs z2 := Nat.le_trans (by decide : 5 ≤ 6) hrs_z2
      have hs2_2_eq : deltaHN (deltaHN .hn0 (evalHN x2)) (evalHN y2) = evalHN (x1 ⋅ z1) := (evalHN_reduces hred_l2).symm
      have hz2_eq : evalHN z2 = evalHN (y1 ⋅ z1) := (evalHN_reduces hred_r2).symm
      have h34_2 : deltaHN (deltaHN (deltaHN .hn0 (evalHN x2)) (evalHN y2)) (evalHN z2) = .hn34 := by
        rw [hs2_2_eq, hz2_eq]; exact htot1
      have ⟨hsccL2, _⟩ := scc1_preserved (rs_ge5_evalHN hrs_y2) (rs_ge5_evalHN hrs_z2_5)
        (hs2_2_eq.symm ▸ hsccL1) (hz2_eq.symm ▸ hsccR1) h34_2 hu2
      have hr2_23_34 : inZ23_34 (evalHN (y2 ⋅ z2)) = true :=
        lemma_T2_r_collapse hred_l2 hsccL1 (hz1_eq.symm ▸ hsccR) hrs_z1_5 (hz2_eq.symm ▸ hsccR1)
      have htot2 : evalHN ((x2 ⋅ z2) ⋅ (y2 ⋅ z2)) = .hn34 :=
        (evalHN_step (Step.root x2 y2 z2)).symm.trans h34_2
      -- Bridge Step 3: `((x2 ⋅ z2) ⋅ (y2 ⋅ z2)) ▷ (x3 ⋅ z3) ⋅ (y3 ⋅ z3)` enters `P3State`!
      refine Acc.intro ((x2 ⋅ z2) ⋅ (y2 ⋅ z2)) (fun b3 hrel3 => ?_)
      obtain ⟨x3, y3, z3, hred_l3, hred_r3, hb3⟩ := relRootStep_app_inv hrel3
      subst hb3
      have hv_sxy3 := noVars_reduces hred_l3 ((Bool.and_eq_true _ _).mpr ⟨hv_x2, hv_z2⟩)
      have hv_x3 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv_sxy3).1).2
      have hv_y3 := ((Bool.and_eq_true _ _).mp hv_sxy3).2
      have hv_z3 := noVars_reduces hred_r3 ((Bool.and_eq_true _ _).mpr ⟨hv_y2, hv_z2⟩)
      have hrs_z3_5 : 5 ≤ rs z3 := Nat.le_trans (Nat.le_trans hrs_z2_5 (Nat.le_add_left (rs z2) 1)) (rs_mono_reduces hred_r3)
      have hrs_r3_5 : 5 ≤ rs (y3 ⋅ z3) := Nat.le_trans hrs_z3_5 (Nat.le_add_left (rs z3) 1)
      have hz3_23_34 : inZ23_34 (evalHN z3) = true := by
        rw [← evalHN_reduces hred_r3]; exact hr2_23_34
      have hr3_23_34 : inZ23_34 (evalHN (y3 ⋅ z3)) = true :=
        lemma_T2_r_collapse hred_l3 hsccL2 (hz2_eq.symm ▸ hsccR1) hrs_z2_5 (inZ23_34_implies_inSCC1R hz3_23_34)
      have htot3 : evalHN ((x3 ⋅ z3) ⋅ (y3 ⋅ z3)) = .hn34 :=
        (evalHN_step (Step.root x3 y3 z3)).symm.trans ((evalHN_reduces (reduces_app hred_l3 hred_r3)).symm.trans htot2)
      exact phase3_acc ⟨hv_x3, hv_z3, (Bool.and_eq_true _ _).mpr ⟨hv_y3, hv_z3⟩,
        hrs_z3_5, hrs_r3_5, hz3_23_34, hr3_23_34, htot3⟩

/-- Phase 1 complete: transient DAG (`transientRank ≤ 2`) into `SCC 1` once `6 ≤ rs l ∧ 6 ≤ rs r`. -/
private theorem phase1_transient_aux :
    ∀ (rk : Nat) {l r : Term},
      noVars l = true → noVars r = true →
      6 ≤ rs l → 6 ≤ rs r →
      evalHN (l ⋅ r) = .hn34 →
      transientRank (evalHN l) (evalHN r) ≤ rk →
      TopTerminating (l ⋅ r) := by
  intro rk
  induction rk with
  | zero =>
    intro l r hvl hvr hrsl hrsr h34 hrk
    have hr0 : transientRank (evalHN l) (evalHN r) = 0 := Nat.eq_zero_of_le_zero hrk
    have ⟨hsccL, hsccR⟩ := (transientRank_eq_zero_iff _ _).mp hr0
    exact phase2_scc1_acc hvl hvr hrsl hrsr hsccL hsccR h34
  | succ rk ih =>
    intro l r hvl hvr hrsl hrsr h34 hrk
    exact if hr0 : transientRank (evalHN l) (evalHN r) = 0 then
      ih hvl hvr hrsl hrsr h34 (hr0 ▸ Nat.zero_le rk)
    else by
      refine Acc.intro (l ⋅ r) (fun b1 hrel1 => ?_)
      obtain ⟨x1, y1, z1, hred_l1, hred_r1, hb1⟩ := relRootStep_app_inv hrel1
      subst hb1
      cases hd1 : decide (evalHN (x1 ⋅ z1) = .hn34) with
      | true => exact left_hn34_topTerminating (of_decide_eq_true hd1)
      | false =>
        have hu1 : evalHN (x1 ⋅ z1) ≠ .hn34 := of_decide_eq_false hd1
        have hv_sxy1 := noVars_reduces hred_l1 hvl
        have hv_x1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv_sxy1).1).2
        have hv_y1 := ((Bool.and_eq_true _ _).mp hv_sxy1).2
        have hv_z1 := noVars_reduces hred_r1 hvr
        have hrs_y1 : 5 ≤ rs y1 := le_of_one_add_le_one_add (Nat.le_trans hrsl (rs_mono_reduces hred_l1))
        have hrs_z1 : 6 ≤ rs z1 := Nat.le_trans hrsr (rs_mono_reduces hred_r1)
        have hrs_z1_5 : 5 ≤ rs z1 := Nat.le_trans (by decide : 5 ≤ 6) hrs_z1
        have hs2_eq : deltaHN (deltaHN .hn0 (evalHN x1)) (evalHN y1) = evalHN l := (evalHN_reduces hred_l1).symm
        have hz1_eq : evalHN z1 = evalHN r := (evalHN_reduces hred_r1).symm
        have h34_1 : deltaHN (deltaHN (deltaHN .hn0 (evalHN x1)) (evalHN y1)) (evalHN z1) = .hn34 := by
          rw [hs2_eq, hz1_eq]; exact h34
        have hok := trStepOk_sound (rs_ge5_evalHN hrs_y1) (rs_ge5_evalHN hrs_z1_5) h34_1 hu1
        dsimp only [trStepOk] at hok
        rw [hs2_eq, hz1_eq] at hok
        have hbeq_f : (transientRank (evalHN l) (evalHN r) == 0) = false := beq_false_of_ne hr0
        rw [hbeq_f] at hok
        have hlt1 : transientRank (deltaHN (evalHN x1) (evalHN r)) (deltaHN (evalHN y1) (evalHN r)) < transientRank (evalHN l) (evalHN r) :=
          of_decide_eq_true hok
        have hlt : transientRank (evalHN (x1 ⋅ z1)) (evalHN (y1 ⋅ z1)) < transientRank (evalHN l) (evalHN r) := by
          change transientRank (deltaHN (evalHN x1) (evalHN z1)) (deltaHN (evalHN y1) (evalHN z1)) < _
          rw [hz1_eq]
          exact hlt1
        have htot1 : evalHN ((x1 ⋅ z1) ⋅ (y1 ⋅ z1)) = .hn34 :=
          (evalHN_step (Step.root x1 y1 z1)).symm.trans h34_1
        exact ih ((Bool.and_eq_true _ _).mpr ⟨hv_x1, hv_z1⟩) ((Bool.and_eq_true _ _).mpr ⟨hv_y1, hv_z1⟩)
          (Nat.add_le_add_left hrs_z1_5 1) (Nat.add_le_add_left hrs_z1_5 1) htot1
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hrk))

theorem phase1_rs_ge6_both_acc {l r : Term}
    (hvl : noVars l = true) (hvr : noVars r = true)
    (hrsl : 6 ≤ rs l) (hrsr : 6 ≤ rs r) (h34 : evalHN (l ⋅ r) = .hn34) :
    TopTerminating (l ⋅ r) :=
  phase1_transient_aux (transientRank (evalHN l) (evalHN r)) hvl hvr hrsl hrsr h34 (Nat.le_refl _)

/-- Phase 0 complete: `rs t ≥ 6` enters `6 ≤ rs l ∧ 6 ≤ rs r` in 1 step, and `6 - rs t` inducts down to 0. -/
private theorem phase0_rs_ge6_acc {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) (hrs : 6 ≤ rs t) :
    TopTerminating t := by
  refine Acc.intro t (fun b hrel => ?_)
  cases t with
  | s => exfalso; exact relRootStep_s_false hrel
  | var _ => cases hv
  | app l r =>
    have ⟨hvl, hvr⟩ := (Bool.and_eq_true _ _).mp hv
    obtain ⟨x, y, z, hred_l, hred_r, hb⟩ := relRootStep_app_inv hrel
    subst hb
    have hv_sxy := noVars_reduces hred_l hvl
    have hv_x := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv_sxy).1).2
    have hv_y := ((Bool.and_eq_true _ _).mp hv_sxy).2
    have hv_z := noVars_reduces hred_r hvr
    have hrs_z5 : 5 ≤ rs z := le_of_one_add_le_one_add (Nat.le_trans hrs (Nat.add_le_add_left (rs_mono_reduces hred_r) 1))
    have htot : evalHN ((x ⋅ z) ⋅ (y ⋅ z)) = .hn34 := by
      rw [← evalHN_reduces (relRootStep_to_reduces hrel)]
      exact h34
    exact phase1_rs_ge6_both_acc
      ((Bool.and_eq_true _ _).mpr ⟨hv_x, hv_z⟩)
      ((Bool.and_eq_true _ _).mpr ⟨hv_y, hv_z⟩)
      (Nat.add_le_add_left hrs_z5 1)
      (Nat.add_le_add_left hrs_z5 1)
      htot

private theorem phase0_aux :
    ∀ (k : Nat) {t : Term}, noVars t = true → evalHN t = .hn34 → 6 - rs t ≤ k → TopTerminating t := by
  intro k
  induction k with
  | zero =>
    intro t hv h34 hle
    exact if hrs6 : 6 ≤ rs t then phase0_rs_ge6_acc hv h34 hrs6
    else by
      have hlt : rs t < 6 := Nat.lt_of_not_ge hrs6
      have hpos : 0 < 6 - rs t := sub_lt_sub_of_lt hlt (Nat.le_refl 6)
      exfalso
      exact Nat.not_succ_le_zero 0 (Nat.le_trans hpos hle)
  | succ k ih =>
    intro t hv h34 hle
    exact if hrs6 : 6 ≤ rs t then phase0_rs_ge6_acc hv h34 hrs6
    else by
      refine Acc.intro t (fun b hrel => ?_)
      have hv_b : noVars b = true := noVars_reduces (relRootStep_to_reduces hrel) hv
      have h34_b : evalHN b = .hn34 := (evalHN_reduces (relRootStep_to_reduces hrel)).symm.trans h34
      exact if hrs_b6 : 6 ≤ rs b then phase0_rs_ge6_acc hv_b h34_b hrs_b6
      else by
        have hlt_b : rs b ≤ 6 := Nat.le_of_lt (Nat.lt_of_not_ge hrs_b6)
        have hinc : rs t < rs b := rs_relRootStep_lt hrel
        have hsub : 6 - rs b < 6 - rs t := sub_lt_sub_of_lt hinc hlt_b
        exact ih hv_b h34_b (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hsub hle))

theorem waldmann_top_termination_closed {t : Term} (hv : noVars t = true) : TopTerminating t := by
  cases hd : decide (evalHN t = .hn34) with
  | true => exact phase0_aux (6 - rs t) hv (of_decide_eq_true hd) (Nat.le_refl _)
  | false => exact topTerminating_of_evalHN_ne_hn34 (of_decide_eq_false hd)

private theorem acc_pullback_closeTerm {u : Term} (hacc : TopTerminating u) :
    ∀ t, closeTerm t = u → TopTerminating t := by
  induction hacc with
  | intro u _ ih =>
    intro t heq
    subst heq
    exact Acc.intro t (fun t' hrel => ih (closeTerm t') (relRootStep_closeTerm hrel) t' rfl)

/-- **WALDMANN'S TOP-TERMINATION THEOREM (Theorem 29 of Barendregt–Endrullis–Klop–Waldmann 2018;
    Waldmann 2000, *"The Combinator S"*, *Information and Computation* 159:2–21)**:
    Every pure `S`-term `t` (closed or open) is constructively top-terminating
    (`Acc (fun b a => RelRootStep a b) t`). -/
theorem waldmann_theorem_29_top_termination (t : Term) : TopTerminating t :=
  acc_pullback_closeTerm (waldmann_top_termination_closed (noVars_closeTerm t)) t rfl

/-! ## 5. Infinite-Sequence Formulations, Absence of Mute Terms, Total RNF Normalizer, and Corollaries -/

/-- `HasRootReduces a b`: `a` reduces to `b` via a reduction containing at least one root step. -/
def HasRootReduces (a b : Term) : Prop :=
  ∃ m1 m2, Reduces a m1 ∧ RootStep m1 m2 ∧ Reduces m2 b

theorem hasRootReduces_to_relRoot {a b : Term} (h : HasRootReduces a b) :
    ∃ c, RelRootStep a c ∧ Reduces c b := by
  obtain ⟨m1, m2, ham1, hr, hm2b⟩ := h
  rcases reduces_split_first_root ham1 with hnr | ⟨c, hrel, hcm1⟩
  · exact ⟨m2, ⟨m1, hnr, hr⟩, hm2b⟩
  · exact ⟨c, hrel, reduces_trans hcm1 (Reduces.next (rootStep_to_step hr) hm2b)⟩

private theorem acc_hasRootReduces_aux {x : Term} (hacc : TopTerminating x) :
    ∀ y, Reduces x y → Acc (fun b a => HasRootReduces a b) y := by
  induction hacc with
  | intro x _ ih =>
    intro y hxy
    refine Acc.intro y (fun z hyz => ?_)
    obtain ⟨c, hrel_yc, hcz⟩ := hasRootReduces_to_relRoot hyz
    have hxz : HasRootReduces x z := by
      obtain ⟨m, hnr, hr⟩ := hrel_yc
      exact ⟨m, c, reduces_trans hxy (nonRootReduces_to_reduces hnr), hr, hcz⟩
    obtain ⟨c0, hrel_xc0, hc0z⟩ := hasRootReduces_to_relRoot hxz
    exact ih c0 hrel_xc0 z hc0z

theorem hasRootReduces_wellFounded (t : Term) : Acc (fun b a => HasRootReduces a b) t :=
  acc_hasRootReduces_aux (waldmann_theorem_29_top_termination t) t (Reduces.refl t)

theorem step_seq_reduces (f : Nat → Term) (hf : ∀ n, Step (f n) (f (n + 1))) :
    ∀ {i j : Nat}, i ≤ j → Reduces (f i) (f j) := by
  intro i j hij
  induction j with
  | zero =>
    cases Nat.eq_zero_of_le_zero hij
    exact Reduces.refl (f 0)
  | succ j ih =>
    exact if heq : i = j + 1 then heq ▸ Reduces.refl _
    else
      have hle : i ≤ j := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hij heq)
      reduces_trans (ih hle) (Reduces.next (hf j) (Reduces.refl _))

private theorem no_inf_root_aux (f : Nat → Term) (hf : ∀ n, Step (f n) (f (n + 1)))
    (hinf : ∀ M, ∃ n, M ≤ n ∧ RootStep (f n) (f (n + 1))) :
    ∀ {x : Term}, Acc (fun b a => HasRootReduces a b) x → ∀ N, x = f N → False := by
  intro x hacc
  induction hacc with
  | intro x _ ih =>
    intro N hx
    subst hx
    obtain ⟨n, hNn, hroot⟩ := hinf N
    have hhr : HasRootReduces (f N) (f (n + 1)) :=
      ⟨f n, f (n + 1), step_seq_reduces f hf hNn, hroot, Reduces.refl _⟩
    exact ih (f (n + 1)) hhr (n + 1) rfl

/-- **Theorem 29 (Infinite Reduction Sequence Formulation)**:
    For every infinite `S`-reduction sequence `f 0 → f 1 → f 2 → ...` (open or closed),
    it is impossible that root contractions occur infinitely often (`∀ M, ∃ n ≥ M, RootStep (f n) (f (n + 1))`). -/
theorem no_infinite_root_reduction_sequence (f : Nat → Term)
    (hf : ∀ n, Step (f n) (f (n + 1))) :
    ¬ (∀ M, ∃ n, M ≤ n ∧ RootStep (f n) (f (n + 1))) :=
  fun hinf => no_inf_root_aux f hf hinf (hasRootReduces_wellFounded (f 0)) 0 rfl

/-- **Theorem 29 (Strictly Increasing Subsequence Formulation)**:
    No infinite `S`-reduction sequence `f` admits a strictly increasing index sequence `idx`
    such that every step `f (idx k) → f (idx k + 1)` is a root contraction. -/
theorem no_infinite_indexed_root_steps (f : Nat → Term) (hf : ∀ n, Step (f n) (f (n + 1)))
    (idx : Nat → Nat) (hinc : ∀ k, idx k < idx (k + 1)) :
    ¬ (∀ k, RootStep (f (idx k)) (f (idx k + 1))) := by
  intro hroots
  have hge_id : ∀ k, k ≤ idx k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hinc k))
  exact no_infinite_root_reduction_sequence f hf (fun M => ⟨idx M, hge_id M, hroots M⟩)

/-! ### Corollary (i): There Are No Mute Pure `S`-Terms (Open or Closed) -/

private theorem isMute_reduces {a b : Term} (hm : IsMute a) (hab : Reduces a b) : IsMute b :=
  fun u hbu => hm u (reduces_trans hab hbu)

/-- **Theorem 29, Corollary (i) (No Mute `S`-Terms)**:
    No pure `S`-term `t` (closed or open) is mute (root-active). -/
theorem no_mute_pure_s_terms (t : Term) : ¬ IsMute t := by
  have hacc := waldmann_theorem_29_top_termination t
  induction hacc with
  | intro u _ ih =>
    intro hm
    obtain ⟨x, y, z, hred⟩ := hm u (Reduces.refl u)
    rcases reduces_split_first_root hred with hnr | ⟨c, hrel, _⟩
    · have hrel_root : RelRootStep u ((x ⋅ z) ⋅ (y ⋅ z)) := ⟨S ⋅ x ⋅ y ⋅ z, hnr, .mk x y z⟩
      exact ih _ hrel_root (isMute_reduces hm (relRootStep_to_reduces hrel_root))
    · exact ih c hrel (isMute_reduces hm (relRootStep_to_reduces hrel))

/-! ### Corollary (ii): Computable Total Root Normalizer `toRNF` for Closed Pure `S`-Terms -/

inductive RNFStepCert (t : Term) : Type where
  | done : IsRootNormalForm t → RNFStepCert t
  | step (t' : Term) : noVars t' = true → HeadReduces t t' → RelRootStep t t' → RNFStepCert t

private def extractS2 : (h : Term) → noVars h = true → spineLen h ≤ 2 → hasSpineGe2 h = true →
    Σ' x y, h = S ⋅ x ⋅ y
  | .app (.app .s x) y, _, _, _ => ⟨x, y, rfl⟩
  | .s, _, _, hge => False.elim (Bool.noConfusion hge)
  | .var _, hv, _, _ => False.elim (Bool.noConfusion hv)
  | .app .s _, _, _, hge => False.elim (Bool.noConfusion hge)
  | .app (.var _) _, hv, _, _ =>
    False.elim (Bool.noConfusion (((Bool.and_eq_true _ _).mp hv).1))
  | .app (.app (.var _) _) _, hv, _, _ =>
    False.elim (Bool.noConfusion (((Bool.and_eq_true _ _).mp (((Bool.and_eq_true _ _).mp hv).1)).1))
  | .app (.app (.app a2 _) _) _, _, hsl, _ =>
    False.elim (by
      have h3 : 3 ≤ 1 + (1 + (1 + spineLen a2)) :=
        Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.zero_le _) 1) 1) 1
      exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_trans h3 hsl))))

def rnfStepCert (t : Term) (hv : noVars t = true) : RNFStepCert t :=
  if hrnf : isRNFClosedBool t = true then
    .done ((isRNFClosedBool_iff hv).mp hrnf)
  else
    have hnot_rnf : ¬ IsRootNormalForm t := fun h => hrnf ((isRNFClosedBool_iff hv).mpr h)
    match t, hv, hnot_rnf with
    | .s, hv, hnot => False.elim (hnot ((isRNFClosedBool_iff hv).mp rfl))
    | .var _, hv, _ => False.elim (Bool.noConfusion hv)
    | .app a b, hv, hnot =>
      have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hv).1
      have ha_ne34 : evalHN a ≠ .hn34 := fun ha34 => hnot (left_hn34_isRootNormalForm ha34)
      have ha_sp2 : hasSpineGe2 a = true := by
        cases a with
        | s => exfalso; exact hnot ((footnote4_rnf_iff hv).mpr (Or.inl (Nat.succ_le_succ (Nat.zero_le 1))))
        | var _ => cases hva
        | app a1 _ =>
          cases a1 with
          | s => exfalso; exact hnot ((footnote4_rnf_iff hv).mpr (Or.inl (Nat.le_refl 2)))
          | var _ => cases ((Bool.and_eq_true _ _).mp hva).1
          | app _ _ => rfl
      have hnorm := headNormalize_reduces_hnf hva ha_ne34
      have hha_ge2 : hasSpineGe2 (headNormalize a) = true :=
        spineGe2_preserved_reduces (headReduces_to_reduces hnorm.1) ha_sp2
      let ⟨x, y, hm⟩ := extractS2 (headNormalize a) hnorm.2.1 hnorm.2.2 hha_ge2
      have hred_ab : HeadReduces (a ⋅ b) ((x ⋅ b) ⋅ (y ⋅ b)) :=
        headReduces_trans (headReduces_left (hm ▸ hnorm.1) b)
          (HeadReduces.next (HeadStep.root x y b) (HeadReduces.refl _))
      have hnr : NonRootReduces (a ⋅ b) ((S ⋅ x ⋅ y) ⋅ b) := by
        have hra : Reduces a (S ⋅ x ⋅ y) := hm ▸ headReduces_to_reduces hnorm.1
        have hlift : ∀ {u v}, Reduces u v → NonRootReduces (u ⋅ b) (v ⋅ b) := by
          intro u v hr
          induction hr with
          | refl _ => exact NonRootReduces.refl _
          | next hs _ ih => exact NonRootReduces.next (.left hs) ih
        exact hlift hra
      have hv_res : noVars ((x ⋅ b) ⋅ (y ⋅ b)) = true :=
        noVars_reduces (headReduces_to_reduces hred_ab) hv
      .step ((x ⋅ b) ⋅ (y ⋅ b)) hv_res hred_ab ⟨(S ⋅ x ⋅ y) ⋅ b, hnr, .mk x y b⟩

/-- **Computable Total Root Normalizer `toRNF`**:
    Defined by structural recursion on `waldmann_theorem_29_top_termination` (`Acc.rec` singleton
    elimination — zero `Classical.choice`, zero fuel guessing!). -/
def toRNFAux (t : Term) (hacc : TopTerminating t) : Term :=
  Acc.rec
    (motive := fun _ _ => Term)
    (fun x _ ih =>
      if hv : noVars x = true then
        match rnfStepCert x hv with
        | .done _ => x
        | .step x' _ _ hrel => ih x' hrel
      else x)
    hacc

def toRNF (t : Term) : Term :=
  toRNFAux t (waldmann_theorem_29_top_termination t)

private theorem toRNFAux_spec {t : Term} (hacc : TopTerminating t) (hv : noVars t = true) :
    HeadReduces t (toRNFAux t hacc) ∧ IsRootNormalForm (toRNFAux t hacc) ∧ noVars (toRNFAux t hacc) = true := by
  induction hacc with
  | intro x _ ih =>
    change HeadReduces x (if hv0 : noVars x = true then _ else x) ∧
      IsRootNormalForm (if hv0 : noVars x = true then _ else x) ∧
      noVars (if hv0 : noVars x = true then _ else x) = true
    rw [dif_pos hv]
    cases rnfStepCert x hv with
    | done hrnf => exact ⟨HeadReduces.refl x, hrnf, hv⟩
    | step x' hv' hhead hrel =>
      obtain ⟨hred_rest, hrnf, hv_res⟩ := ih x' hrel hv'
      exact ⟨headReduces_trans hhead hred_rest, hrnf, hv_res⟩

/-- **Theorem 29, Corollary (ii) (`toRNF_spec` & `every_closed_sterm_has_rnf`)**:
    Every closed pure `S`-term reduces via deterministic head steps to a Root Normal Form! -/
theorem toRNF_spec {t : Term} (hv : noVars t = true) :
    HeadReduces t (toRNF t) ∧ IsRootNormalForm (toRNF t) ∧ noVars (toRNF t) = true :=
  toRNFAux_spec (waldmann_theorem_29_top_termination t) hv

theorem every_closed_sterm_has_rnf {t : Term} (hv : noVars t = true) :
    HasRootNormalForm t := by
  obtain ⟨hred, hrnf, _⟩ := toRNF_spec hv
  exact ⟨toRNF t, headReduces_to_reduces hred, hrnf⟩

/-! ### Corollary (iii): Acyclicity of Pure `S`-Reduction via Minimal Cycle + Right-Spine Growth
    (Barendregt et al. 2018, Alternative Proof of Theorem 13 / Corollary 49, pp. 87–88, 104) -/

private theorem stepPlus_to_reduces {x y : Term} (h : StepPlus x y) : Reduces x y := by
  induction h with
  | single hs1 => exact Reduces.next hs1 (Reduces.refl _)
  | head hs1 _ ih => exact Reduces.next hs1 ih

private theorem stepPlus_of_step_reduces {a b c : Term} (h1 : Step a b) (h2 : Reduces b c) : StepPlus a c := by
  induction h2 generalizing a with
  | refl _ => exact StepPlus.single h1
  | next hs _ ih => exact StepPlus.head h1 (ih hs)

private theorem nonRootPlus_sub_cycle {a b : Term} (h : StepPlus (a ⋅ b) (a ⋅ b)) :
    StepPlus a a ∨ StepPlus b b ∨ rs (a ⋅ b) < rs (a ⋅ b) := by
  cases h with
  | single hs =>
    rcases step_iff_root_or_nonRoot.mp hs with hr | hnr0
    · refine Or.inr (Or.inr ?_)
      have heq : rs (a ⋅ b) = rs (a ⋅ b) + 1 := rs_rootStep_eq hr
      have hlt : rs (a ⋅ b) < rs (a ⋅ b) + 1 := Nat.lt_succ_self (rs (a ⋅ b))
      rw [← heq] at hlt
      exact hlt
    · cases hnr0 with
      | left hl => exact Or.inl (.single hl)
      | right hr => exact Or.inr (Or.inl (.single hr))
  | @head _ m _ hs hrest =>
    have hred_rest : Reduces m (a ⋅ b) := stepPlus_to_reduces hrest
    rcases step_iff_root_or_nonRoot.mp hs with hr | hnr0
    · refine Or.inr (Or.inr ?_)
      have h1 : rs (a ⋅ b) + 1 = rs m := (rs_rootStep_eq hr).symm
      have h2 : rs m ≤ rs (a ⋅ b) := rs_mono_reduces hred_rest
      rw [← h1] at h2
      exact Nat.lt_of_succ_le h2
    · rcases reduces_split_first_root hred_rest with hnr_rest | ⟨c, hrel, hcab⟩
      · cases hnr0 with
        | @left _ a1 _ ha1 =>
          obtain ⟨a2, b2, heq2, hra2, _⟩ := nonRootReduces_app_inv hnr_rest a1 b rfl
          injection heq2 with ha2 _
          subst ha2
          exact Or.inl (stepPlus_of_step_reduces ha1 hra2)
        | @right _ _ b1 hb1 =>
          obtain ⟨a2, b2, heq2, _, hrb2⟩ := nonRootReduces_app_inv hnr_rest a b1 rfl
          injection heq2 with _ hb2
          subst hb2
          exact Or.inr (Or.inl (stepPlus_of_step_reduces hb1 hrb2))
      · refine Or.inr (Or.inr ?_)
        have h1 : rs (a ⋅ b) ≤ rs m := rs_mono_step (nonRootStep_to_step hnr0)
        have h2 : rs m + 1 ≤ rs c := rs_relRootStep_lt hrel
        have h3 : rs c ≤ rs (a ⋅ b) := rs_mono_reduces hcab
        exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h1 h2) h3

/-- **Acyclicity of Pure `S`-Terms (`no_cycle_pure_s`, Theorem 13 / Corollary 49)**:
    Proved directly via Barendregt et al. (2018, pp. 87–88)'s minimal-counterexample +
    right-spine root-increment argument! -/
theorem no_cycle_pure_s (t : Term) : ¬ StepPlus t t := by
  induction t with
  | s =>
    intro h
    cases h with
    | single hs => cases hs
    | head hs _ => cases hs
  | var _ =>
    intro h
    cases h with
    | single hs => cases hs
    | head hs _ => cases hs
  | app a b iha ihb =>
    intro hcyc
    rcases nonRootPlus_sub_cycle hcyc with ha | hb | hrs
    · exact iha ha
    · exact ihb hb
    · exact Nat.lt_irrefl _ hrs

/-! ### Corollary (iv): Complete Multiway Root Analysis of `AAA = (SSS)(SSS)(SSS)` -/

def AAA_1 : Term := ((S ⋅ A_comb) ⋅ (S ⋅ A_comb)) ⋅ A_comb
def AAA_2 : Term := (A_comb ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb)
def AAA_3 : Term := ((S ⋅ A_comb) ⋅ (S ⋅ A_comb)) ⋅ ((S ⋅ A_comb) ⋅ A_comb)
def AAA_4 : Term := (A_comb ⋅ ((S ⋅ A_comb) ⋅ A_comb)) ⋅ ((S ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb))
def AAA_5 : Term := ((S ⋅ ((S ⋅ A_comb) ⋅ A_comb)) ⋅ (S ⋅ ((S ⋅ A_comb) ⋅ A_comb))) ⋅ ((S ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb))
def AAA_6 : Term := (((S ⋅ A_comb) ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb))) ⋅ ((S ⋅ ((S ⋅ A_comb) ⋅ A_comb)) ⋅ ((S ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb)))

private theorem A_comb_nf : IsNormalForm A_comb := by
  intro _ hs
  cases hs with
  | left hl =>
    cases hl with
    | left hll => cases hll
    | right hlr => cases hlr
  | right hr => cases hr

private theorem SA_nf : IsNormalForm (S ⋅ A_comb) := by
  intro _ hs
  cases hs with
  | left hl => cases hl
  | right hr => exact A_comb_nf _ hr

private theorem SAA_nf : IsNormalForm ((S ⋅ A_comb) ⋅ A_comb) := by
  intro _ hs
  cases hs with
  | left hl => exact SA_nf _ hl
  | right hr => exact A_comb_nf _ hr

private theorem SASA_nf : IsNormalForm ((S ⋅ A_comb) ⋅ (S ⋅ A_comb)) := by
  intro _ hs
  cases hs with
  | left hl => exact SA_nf _ hl
  | right hr => exact SA_nf _ hr

private theorem SA_SAA_nf : IsNormalForm ((S ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb)) := by
  intro _ hs
  cases hs with
  | left hl => exact SA_nf _ hl
  | right hr => exact SAA_nf _ hr

private theorem S_SAA_nf : IsNormalForm (S ⋅ ((S ⋅ A_comb) ⋅ A_comb)) := by
  intro _ hs
  cases hs with
  | left hl => cases hl
  | right hr => exact SAA_nf _ hr

private theorem S_SAA_2_nf : IsNormalForm ((S ⋅ ((S ⋅ A_comb) ⋅ A_comb)) ⋅ (S ⋅ ((S ⋅ A_comb) ⋅ A_comb))) := by
  intro _ hs
  cases hs with
  | left hl => exact S_SAA_nf _ hl
  | right hr => exact S_SAA_nf _ hr

private theorem step_AAA_0 : ∀ u, Step AAA u → u = AAA_1 ∧ NonRootStep AAA u := by
  intro u hs
  cases hs with
  | @left _ l' _ hl =>
    cases hl with
    | root _ _ _ => exact ⟨rfl, .left (.root S S A_comb)⟩
    | left hll => exfalso; exact A_comb_nf _ hll
    | right hlr => exfalso; exact A_comb_nf _ hlr
  | right hr => exfalso; exact A_comb_nf _ hr

private theorem step_AAA_1 : ∀ u, Step AAA_1 u → u = AAA_2 ∧ RootStep AAA_1 u := by
  intro u hs
  cases hs with
  | root _ _ _ => exact ⟨rfl, .mk A_comb (S ⋅ A_comb) A_comb⟩
  | left hl => exfalso; exact SASA_nf _ hl
  | right hr => exfalso; exact A_comb_nf _ hr

private theorem step_AAA_2 : ∀ u, Step AAA_2 u → u = AAA_3 ∧ NonRootStep AAA_2 u := by
  intro u hs
  cases hs with
  | @left _ l' _ hl =>
    cases hl with
    | root _ _ _ => exact ⟨rfl, .left (.root S S A_comb)⟩
    | left hll => exfalso; exact A_comb_nf _ hll
    | right hlr => exfalso; exact A_comb_nf _ hlr
  | right hr => exfalso; exact SAA_nf _ hr

private theorem step_AAA_3 : ∀ u, Step AAA_3 u → u = AAA_4 ∧ RootStep AAA_3 u := by
  intro u hs
  cases hs with
  | root _ _ _ => exact ⟨rfl, .mk A_comb (S ⋅ A_comb) ((S ⋅ A_comb) ⋅ A_comb)⟩
  | left hl => exfalso; exact SASA_nf _ hl
  | right hr => exfalso; exact SAA_nf _ hr

private theorem step_AAA_4 : ∀ u, Step AAA_4 u → u = AAA_5 ∧ NonRootStep AAA_4 u := by
  intro u hs
  cases hs with
  | @left _ l' _ hl =>
    cases hl with
    | root _ _ _ => exact ⟨rfl, .left (.root S S ((S ⋅ A_comb) ⋅ A_comb))⟩
    | left hll => exfalso; exact A_comb_nf _ hll
    | right hlr => exfalso; exact SAA_nf _ hlr
  | right hr => exfalso; exact SA_SAA_nf _ hr

private theorem step_AAA_5 : ∀ u, Step AAA_5 u → u = AAA_6 ∧ RootStep AAA_5 u := by
  intro u hs
  cases hs with
  | root _ _ _ => exact ⟨rfl, .mk ((S ⋅ A_comb) ⋅ A_comb) (S ⋅ ((S ⋅ A_comb) ⋅ A_comb)) ((S ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb))⟩
  | left hl => exfalso; exact S_SAA_2_nf _ hl
  | right hr => exfalso; exact SA_SAA_nf _ hr

theorem AAA_6_isRootNormalForm : IsRootNormalForm AAA_6 :=
  left_hn34_isRootNormalForm (by rfl : evalHN (((S ⋅ A_comb) ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb))) = .hn34)

/-- Inductive count of `RelRootStep`s from `t`: `RootStepsN k a b` means `k` root contractions occur. -/
inductive RootStepsN : Nat → Term → Term → Prop where
  | zero (a : Term) : RootStepsN 0 a a
  | succ {k : Nat} {a b c : Term} : RelRootStep a b → RootStepsN k b c → RootStepsN (k + 1) a c

private theorem unique_relRootStep_AAA_0 {b : Term} (h : RelRootStep AAA b) : b = AAA_2 := by
  obtain ⟨m, hnr, hr⟩ := h
  cases hnr with
  | refl _ => cases hr
  | @next _ m1 _ hs1 hnr1 =>
    have ⟨hm1, _⟩ := step_AAA_0 m1 (nonRootStep_to_step hs1)
    subst hm1
    cases hnr1 with
    | refl _ =>
      have ⟨hb, _⟩ := step_AAA_1 b (rootStep_to_step hr)
      exact hb
    | @next _ m2 _ hs2 _ =>
      have ⟨_, hr2⟩ := step_AAA_1 m2 (nonRootStep_to_step hs2)
      exfalso; exact rootStep_disjoint_nonRootStep hr2 hs2

private theorem unique_relRootStep_AAA_2 {b : Term} (h : RelRootStep AAA_2 b) : b = AAA_4 := by
  obtain ⟨m, hnr, hr⟩ := h
  cases hnr with
  | refl _ => cases hr
  | @next _ m1 _ hs1 hnr1 =>
    have ⟨hm1, _⟩ := step_AAA_2 m1 (nonRootStep_to_step hs1)
    subst hm1
    cases hnr1 with
    | refl _ =>
      have ⟨hb, _⟩ := step_AAA_3 b (rootStep_to_step hr)
      exact hb
    | @next _ m2 _ hs2 _ =>
      have ⟨_, hr2⟩ := step_AAA_3 m2 (nonRootStep_to_step hs2)
      exfalso; exact rootStep_disjoint_nonRootStep hr2 hs2

private theorem unique_relRootStep_AAA_4 {b : Term} (h : RelRootStep AAA_4 b) : b = AAA_6 := by
  obtain ⟨m, hnr, hr⟩ := h
  cases hnr with
  | refl _ => cases hr
  | @next _ m1 _ hs1 hnr1 =>
    have ⟨hm1, _⟩ := step_AAA_4 m1 (nonRootStep_to_step hs1)
    subst hm1
    cases hnr1 with
    | refl _ =>
      have ⟨hb, _⟩ := step_AAA_5 b (rootStep_to_step hr)
      exact hb
    | @next _ m2 _ hs2 _ =>
      have ⟨_, hr2⟩ := step_AAA_5 m2 (nonRootStep_to_step hs2)
      exfalso; exact rootStep_disjoint_nonRootStep hr2 hs2

/-- **Exact Multiway Root Census of `AAA`**:
    `AAA = (SSS)(SSS)(SSS)` reaches its exact Root Normal Form `AAA_6` in 6 deterministic steps
    containing **3** root contractions (`RootStepsN 3 AAA AAA_6`), and **no multiway reduction
    from `AAA` can ever perform 4 root contractions**! -/
theorem aaa_exact_3_root_steps_all_multiway :
    RootStepsN 3 AAA AAA_6 ∧ IsRootNormalForm AAA_6 ∧ (∀ k u, RootStepsN k AAA u → k ≤ 3) := by
  have hr1 : RelRootStep AAA AAA_2 :=
    ⟨AAA_1, .next (.left (.root S S A_comb)) (.refl _), .mk A_comb (S ⋅ A_comb) A_comb⟩
  have hr2 : RelRootStep AAA_2 AAA_4 :=
    ⟨AAA_3, .next (.left (.root S S A_comb)) (.refl _), .mk A_comb (S ⋅ A_comb) ((S ⋅ A_comb) ⋅ A_comb)⟩
  have hr3 : RelRootStep AAA_4 AAA_6 :=
    ⟨AAA_5, .next (.left (.root S S ((S ⋅ A_comb) ⋅ A_comb))) (.refl _),
      .mk ((S ⋅ A_comb) ⋅ A_comb) (S ⋅ ((S ⋅ A_comb) ⋅ A_comb)) ((S ⋅ A_comb) ⋅ ((S ⋅ A_comb) ⋅ A_comb))⟩
  refine ⟨.succ hr1 (.succ hr2 (.succ hr3 (.zero AAA_6))), AAA_6_isRootNormalForm, ?_⟩
  intro k u hk
  cases hk with
  | zero _ => exact Nat.zero_le 3
  | @succ k1 _ b1 _ h1 hk1 =>
    rw [unique_relRootStep_AAA_0 h1] at hk1
    cases hk1 with
    | zero _ => exact Nat.succ_le_succ (Nat.zero_le 2)
    | @succ k2 _ b2 _ h2 hk2 =>
      rw [unique_relRootStep_AAA_2 h2] at hk2
      cases hk2 with
      | zero _ => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))
      | @succ k3 _ b3 _ h3 hk3 =>
        rw [unique_relRootStep_AAA_4 h3] at hk3
        cases hk3 with
        | zero _ => exact Nat.le_refl 3
        | @succ _ _ b4 _ h4 _ =>
          obtain ⟨m, hnr, hr⟩ := h4
          cases hr with
          | mk x y z =>
            exfalso
            exact AAA_6_isRootNormalForm ⟨x, y, z, nonRootReduces_to_reduces hnr⟩

end FormalTopTermination

#print axioms FormalTopTermination.nuHN_step_le
#print axioms FormalTopTermination.topTerminating_of_evalHN_ne_hn34
#print axioms FormalTopTermination.footnote4_rnf_iff
#print axioms FormalTopTermination.waldmann_top_termination_closed
#print axioms FormalTopTermination.waldmann_theorem_29_top_termination
#print axioms FormalTopTermination.no_infinite_root_reduction_sequence
#print axioms FormalTopTermination.no_infinite_indexed_root_steps
#print axioms FormalTopTermination.no_mute_pure_s_terms
#print axioms FormalTopTermination.toRNF_spec
#print axioms FormalTopTermination.every_closed_sterm_has_rnf
#print axioms FormalTopTermination.no_cycle_pure_s
#print axioms FormalTopTermination.aaa_exact_3_root_steps_all_multiway
