import Std

/-!
# Structural Laws of Pure S (`CL(S)`): Church–Rosser, Conservation (`WN ↔ SN`), Bergstra Acyclicity, Visser–van Oostrom Order `≤ 3`, and Waldmann's No-Spiral Theorem

Self-contained Lean 4.33.1 formalization with zero `sorry`, zero custom axioms,
and zero `Classical.choice` (`#print axioms` uses at most `[propext, Quot.sound]`).
-/

namespace FormalAlgebra

/-! ## 0. Constructive Transitive Closure and Arithmetic Helpers (Zero `Classical.choice`) -/

inductive TransGen {α : Type} (R : α → α → Prop) : α → α → Prop where
  | single {a b : α} : R a b → TransGen R a b
  | tail {a b c : α} : TransGen R a b → R b c → TransGen R a c

inductive ReflTransGen {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : ReflTransGen R a a
  | head {a b c : α} : R a b → ReflTransGen R b c → ReflTransGen R a c

theorem transGen_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : TransGen R a b) (h2 : TransGen R b c) : TransGen R a c := by
  induction h2 with
  | single hs => exact .tail h1 hs
  | tail _ hs ih => exact .tail ih hs

theorem transGen_head {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : R a b) (h2 : TransGen R b c) : TransGen R a c :=
  transGen_trans (.single h1) h2

theorem transGen_of_transGen_reflTransGen {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : TransGen R a b) (h2 : ReflTransGen R b c) : TransGen R a c := by
  induction h2 generalizing a with
  | refl _ => exact h1
  | head hs _ ih => exact ih (.tail h1 hs)

theorem acc_transGen {α : Type} {R : α → α → Prop} {x : α}
    (h : Acc (fun b a => R a b) x) : Acc (fun b a => TransGen R a b) x := by
  induction h with
  | intro x _ ih =>
    refine Acc.intro x (fun y hy => ?_)
    induction hy with
    | @single y' hxy => exact ih y' hxy
    | @tail z y' _ hzy ih_z => exact Acc.inv ih_z (.single hzy)

theorem acc_of_transGen {α : Type} {R : α → α → Prop} {x : α}
    (h : Acc (fun b a => TransGen R a b) x) : Acc (fun b a => R a b) x := by
  induction h with
  | intro x _ ih => exact Acc.intro x (fun y hy => ih y (.single hy))

theorem acc_irrefl {α : Type} {R : α → α → Prop} {x : α} (h : Acc R x) : ¬ R x x := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

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

/-! ## 1. Syntax, Contexts, Substitution, and Rewriting Relations -/

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

def noVars : Term → Bool
  | .s => true
  | .var _ => false
  | .app a b => noVars a && noVars b

def hasVar (v : Nat) : Term → Bool
  | .s => false
  | .var k => decide (k = v)
  | .app a b => hasVar v a || hasVar v b

def subst (σ : Nat → Term) : Term → Term
  | .s => .s
  | .var k => σ k
  | .app a b => subst σ a ⋅ subst σ b

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

inductive ConvS : Term → Term → Prop where
  | refl (a : Term) : ConvS a a
  | step {a b : Term} : Step a b → ConvS a b
  | symm {a b : Term} : ConvS a b → ConvS b a
  | trans {a b c : Term} : ConvS a b → ConvS b c → ConvS a c

inductive HeadStep : Term → Term → Prop where
  | root (x y z : Term) : HeadStep (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : HeadStep a a' → HeadStep (a ⋅ b) (a' ⋅ b)

inductive HeadReduces : Term → Term → Prop where
  | refl (a : Term) : HeadReduces a a
  | next {a b c : Term} : HeadStep a b → HeadReduces b c → HeadReduces a c

def IsNormalForm (t : Term) : Prop := ∀ t', ¬ Step t t'
def HasNormalForm (t : Term) : Prop := ∃ nf, Reduces t nf ∧ IsNormalForm nf
def StrongNormalizing (t : Term) : Prop := Acc (fun b a => Step a b) t

def IsClosedHNF (t : Term) : Prop := noVars t = true ∧ spineLen t ≤ 2
def HasHNF (t : Term) : Prop := ∃ h, Reduces t h ∧ spineLen h ≤ 2
def IsRootNormalForm (t : Term) : Prop := ¬ ∃ x y z, Reduces t (S ⋅ x ⋅ y ⋅ z)

/-! ### Basic Rewriting Lemmas -/

theorem reduces_trans {a b c : Term} (h1 : Reduces a b) (h2 : Reduces b c) : Reduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact Reduces.next hs (ih h2)

theorem stepPlus_trans {a b c : Term} (h1 : StepPlus a b) (h2 : StepPlus b c) : StepPlus a c := by
  induction h1 with
  | single hs => exact StepPlus.head hs h2
  | head hs _ ih => exact StepPlus.head hs (ih h2)

theorem stepPlus_of_step_reduces {a b c : Term} (h1 : Step a b) (h2 : Reduces b c) : StepPlus a c := by
  induction h2 generalizing a with
  | refl _ => exact StepPlus.single h1
  | next hs _ ih => exact StepPlus.head h1 (ih hs)

theorem reduces_of_stepPlus {a b : Term} (h : StepPlus a b) : Reduces a b := by
  induction h with
  | single hs => exact Reduces.next hs (Reduces.refl _)
  | head hs _ ih => exact Reduces.next hs ih

theorem reduces_eq_or_stepPlus {a b : Term} (h : Reduces a b) : a = b ∨ StepPlus a b := by
  cases h with
  | refl _ => exact Or.inl rfl
  | next hs hrest => exact Or.inr (stepPlus_of_step_reduces hs hrest)

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

theorem stepPlus_left {a a' : Term} (h : StepPlus a a') (b : Term) : StepPlus (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | single hs => exact StepPlus.single (Step.left hs)
  | head hs _ ih => exact StepPlus.head (Step.left hs) ih

theorem stepPlus_right {b b' : Term} (a : Term) (h : StepPlus b b') : StepPlus (a ⋅ b) (a ⋅ b') := by
  induction h with
  | single hs => exact StepPlus.single (Step.right hs)
  | head hs _ ih => exact StepPlus.head (Step.right hs) ih

theorem headStep_to_step {a b : Term} (h : HeadStep a b) : Step a b := by
  induction h with
  | root x y z => exact Step.root x y z
  | left _ ih => exact Step.left ih

theorem headReduces_to_reduces {a b : Term} (h : HeadReduces a b) : Reduces a b := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (headStep_to_step hs) ih

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

theorem hasVar_false_step {v : Nat} {a b : Term} (h : Step a b) :
    hasVar v a = false → hasVar v b = false := by
  induction h with
  | root x y z =>
    simp only [S, hasVar, Bool.or_eq_false_iff]
    intro ⟨⟨⟨_, hx⟩, hy⟩, hz⟩
    exact ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
  | left _ ih =>
    simp only [hasVar, Bool.or_eq_false_iff]
    intro ⟨ha, hb⟩
    exact ⟨ih ha, hb⟩
  | right _ ih =>
    simp only [hasVar, Bool.or_eq_false_iff]
    intro ⟨ha, hb⟩
    exact ⟨ha, ih hb⟩

theorem hasVar_false_reduces {v : Nat} {a b : Term} (h : Reduces a b) :
    hasVar v a = false → hasVar v b = false := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (hasVar_false_step hs hv)

theorem subst_step (σ : Nat → Term) {a b : Term} (h : Step a b) :
    Step (subst σ a) (subst σ b) := by
  induction h with
  | root x y z => exact Step.root (subst σ x) (subst σ y) (subst σ z)
  | left _ ih => exact Step.left ih
  | right _ ih => exact Step.right ih

theorem subst_reduces (σ : Nat → Term) {a b : Term} (h : Reduces a b) :
    Reduces (subst σ a) (subst σ b) := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (subst_step σ hs) ih

theorem subst_noVars (σ : Nat → Term) (t : Term) (h : noVars t = true) : subst σ t = t := by
  induction t with
  | s => rfl
  | var _ => cases h
  | app a b iha ihb =>
    simp only [noVars, Bool.and_eq_true] at h
    simp only [subst, iha h.1, ihb h.2]

theorem headLeaf_var_preserved_step {a b : Term} {v : Nat}
    (h : Step a b) (hhead : headLeaf a = .var v) : headLeaf b = .var v := by
  induction h with
  | root x y z => simp [S, headLeaf] at hhead
  | left _ ih => exact ih hhead
  | right _ _ => exact hhead

theorem headLeaf_var_preserved_reduces {a b : Term} {v : Nat}
    (h : Reduces a b) (hhead : headLeaf a = .var v) : headLeaf b = .var v := by
  induction h with
  | refl _ => exact hhead
  | next hs _ ih => exact ih (headLeaf_var_preserved_step hs hhead)

/-! ## 2. Bergstra's Acyclicity Theorem (Theorem 13 of Barendregt et al. 2018) -/

def bergstraWeight : Term → Nat
  | .s => 1
  | .var _ => 1
  | .app a b => 2 * bergstraWeight a + bergstraWeight b

theorem bergstraWeight_pos (t : Term) : 1 ≤ bergstraWeight t := by
  induction t with
  | s => exact Nat.le_refl 1
  | var _ => exact Nat.le_refl 1
  | app _ _ _ ihb => exact Nat.le_trans ihb (Nat.le_add_left _ _)

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

theorem leaves_mono_reduces {a b : Term} (h : Reduces a b) : leaves a ≤ leaves b := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | next hs _ ih => exact Nat.le_trans (leaves_mono_step hs) ih

theorem leaves_eq_one_weight (t : Term) (h : leaves t = 1) : bergstraWeight t = 1 := by
  cases t with
  | s => rfl
  | var _ => rfl
  | app a b =>
    have h2 : 2 ≤ leaves a + leaves b := Nat.add_le_add (leaves_pos a) (leaves_pos b)
    change leaves a + leaves b = 1 at h
    rw [h] at h2
    cases h2 with
    | step h20 => cases h20

private theorem leaves_root_eq_one (x y z : Nat) (heq : 1 + x + y + z = (x + z) + (y + z)) :
    z = 1 := by
  rw [Nat.add_assoc (1 + x) y z] at heq
  have h1 : 1 + x = x + z := Nat.add_right_cancel heq
  rw [Nat.add_comm 1 x] at h1
  exact (Nat.add_left_cancel h1).symm

private theorem weight_root_lt (wx wy : Nat) :
    2 * (2 * wx + 1) + (2 * wy + 1) < 2 * (2 * (2 * 1 + wx) + wy) + 1 := by
  have hL : 2 * (2 * wx + 1) + (2 * wy + 1) = (4 * wx + 2 * wy) + 3 := by
    rw [Nat.mul_add 2 (2 * wx) 1, ← Nat.mul_assoc 2 2 wx]
    change (4 * wx + 2) + (2 * wy + 1) = (4 * wx + 2 * wy) + 3
    rw [Nat.add_assoc (4 * wx) 2 (2 * wy + 1), ← Nat.add_assoc 2 (2 * wy) 1,
        Nat.add_comm 2 (2 * wy), Nat.add_assoc (2 * wy) 2 1, ← Nat.add_assoc (4 * wx) (2 * wy) 3]
  have hR : 2 * (2 * (2 * 1 + wx) + wy) + 1 = (4 * wx + 2 * wy) + 9 := by
    change 2 * (2 * (2 + wx) + wy) + 1 = (4 * wx + 2 * wy) + 9
    rw [Nat.mul_add 2 2 wx, Nat.mul_add 2 (4 + 2 * wx) wy, Nat.mul_add 2 4 (2 * wx),
        ← Nat.mul_assoc 2 2 wx]
    change ((8 + 4 * wx) + 2 * wy) + 1 = (4 * wx + 2 * wy) + 9
    rw [Nat.add_comm 8 (4 * wx), Nat.add_assoc (4 * wx) 8 (2 * wy), Nat.add_comm 8 (2 * wy),
        ← Nat.add_assoc (4 * wx) (2 * wy) 8, Nat.add_assoc (4 * wx + 2 * wy) 8 1]
  rw [hL, hR]
  exact Nat.add_lt_add_left (by decide : 3 < 9) (4 * wx + 2 * wy)

theorem equal_leaves_strict_weight_drop {a b : Term} (h : Step a b)
    (heq : leaves a = leaves b) : bergstraWeight b < bergstraWeight a := by
  induction h with
  | root x y z =>
    have hz1 : leaves z = 1 := leaves_root_eq_one (leaves x) (leaves y) (leaves z) heq
    have hwz : bergstraWeight z = 1 := leaves_eq_one_weight z hz1
    change 2 * (2 * bergstraWeight x + bergstraWeight z) + (2 * bergstraWeight y + bergstraWeight z) <
      2 * (2 * (2 * 1 + bergstraWeight x) + bergstraWeight y) + bergstraWeight z
    rw [hwz]
    exact weight_root_lt (bergstraWeight x) (bergstraWeight y)
  | @left l l' r _ ih =>
    have hleq : leaves l = leaves l' := Nat.add_right_cancel heq
    have hw := ih hleq
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hw (by decide : 0 < 2)) (bergstraWeight r)
  | @right l r r' _ ih =>
    have hreq : leaves r = leaves r' := Nat.add_left_cancel heq
    have hw := ih hreq
    exact Nat.add_lt_add_left hw (2 * bergstraWeight l)

private theorem stepPlus_leaves_and_weight {a b : Term} (h : StepPlus a b) :
    leaves a < leaves b ∨ (leaves a = leaves b ∧ bergstraWeight b < bergstraWeight a) := by
  induction h with
  | @single a b hs =>
    have hle := leaves_mono_step hs
    exact if heq : leaves a = leaves b then
      Or.inr ⟨heq, equal_leaves_strict_weight_drop hs heq⟩
    else
      Or.inl (Nat.lt_of_le_of_ne hle heq)
  | @head a m b hs _ ih =>
    have hle1 := leaves_mono_step hs
    rcases ih with hlt2 | ⟨heq2, hw2⟩
    · exact Or.inl (Nat.lt_of_le_of_lt hle1 hlt2)
    · exact if heq1 : leaves a = leaves m then
        Or.inr ⟨heq1.trans heq2, Nat.lt_trans hw2 (equal_leaves_strict_weight_drop hs heq1)⟩
      else
        Or.inl (by rw [← heq2]; exact Nat.lt_of_le_of_ne hle1 heq1)

/-- **Bergstra's Theorem 13 (1975)**: No pure-S term (closed or open) admits a cyclic reduction `t →+ t`. -/
theorem bergstra_no_cycle (t : Term) : ¬ StepPlus t t := by
  intro hcyc
  rcases stepPlus_leaves_and_weight hcyc with hlt | ⟨_, hw⟩
  · exact Nat.lt_irrefl _ hlt
  · exact Nat.lt_irrefl _ hw

/-! ## 3. Takahashi Parallel Reduction, Church–Rosser (`CL(S) |= CR`), and Conservation (`WN ↔ SN`) -/

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

/-- Takahashi's complete development function for pure `S`. -/
def completeDev : Term → Term
  | .app (.app (.app .s x) y) z =>
      (completeDev x ⋅ completeDev z) ⋅ (completeDev y ⋅ completeDev z)
  | .app a b => completeDev a ⋅ completeDev b
  | .s => .s
  | .var k => .var k

private theorem completeDev_non_redex (a b : Term)
    (hnot : ∀ x y, a ≠ S ⋅ x ⋅ y) :
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
  | @app a a' b b' ha hb iha ihb =>
    cases a with
    | s =>
      cases ha
      exact ParStep.app ParStep.s ihb
    | var k =>
      cases ha
      exact ParStep.app (ParStep.var k) ihb
    | app a1 y =>
      cases a1 with
      | s =>
        cases ha with
        | @app _ _ _ y' hs _ =>
          cases hs
          have ihy : ParStep y' (completeDev y) := by
            change ParStep (Term.s ⋅ y') (Term.s ⋅ completeDev y) at iha
            cases iha with
            | app _ ihy' => exact ihy'
          exact ParStep.app (ParStep.app ParStep.s ihy) ihb
      | var k =>
        rw [completeDev_non_redex (.var k ⋅ y) b (fun x y' h => by injection h with h1 _; cases h1)]
        exact ParStep.app iha ihb
      | app a2 x =>
        cases a2 with
        | var k =>
          rw [completeDev_non_redex (.var k ⋅ x ⋅ y) b (fun x' y' h => by
            injection h with h1 _; injection h1 with h2 _; cases h2)]
          exact ParStep.app iha ihb
        | app u v =>
          rw [completeDev_non_redex (u ⋅ v ⋅ x ⋅ y) b (fun x' y' h => by
            injection h with h1 _; injection h1 with h2 _; cases h2)]
          exact ParStep.app iha ihb
        | s =>
          change ParStep (a' ⋅ b') ((completeDev x ⋅ completeDev b) ⋅ (completeDev y ⋅ completeDev b))
          cases ha with
          | @app _ a1' _ y' ha1 _ =>
            cases ha1 with
            | @app _ _ _ x' hs _ =>
              cases hs
              have ⟨ihx, ihy⟩ : ParStep x' (completeDev x) ∧ ParStep y' (completeDev y) := by
                change ParStep (S ⋅ x' ⋅ y') (S ⋅ completeDev x ⋅ completeDev y) at iha
                cases iha with
                | app hsx ihy' =>
                  cases hsx with
                  | app _ ihx' => exact ⟨ihx', ihy'⟩
              exact ParStep.beta ihx ihy ihb

theorem parStep_diamond {a b c : Term} (hab : ParStep a b) (hac : ParStep a c) :
    ∃ d, ParStep b d ∧ ParStep c d :=
  ⟨completeDev a, parStep_triangle hab, parStep_triangle hac⟩

inductive ParReduces : Term → Term → Prop where
  | refl (a : Term) : ParReduces a a
  | next {a b c : Term} : ParStep a b → ParReduces b c → ParReduces a c

private theorem parReduces_trans {a b c : Term} (h1 : ParReduces a b) (h2 : ParReduces b c) :
    ParReduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact ParReduces.next hs (ih h2)

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
    obtain ⟨m, ha1m, hbm⟩ := parStep_diamond ha1 hab
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

/-- **Church–Rosser Theorem (`CL(S) |= CR`)**: Pure `S` reduction is confluent. -/
theorem church_rosser {a b c : Term} (hab : Reduces a b) (hac : Reduces a c) :
    ∃ d, Reduces b d ∧ Reduces c d := by
  obtain ⟨d, hbd, hcd⟩ := parReduces_confluence (reduces_to_parReduces hab) (reduces_to_parReduces hac)
  exact ⟨d, parReduces_to_reduces hbd, parReduces_to_reduces hcd⟩

/-! ### Church's Conservation Theorem (`WN ↔ SN` for Non-Erasing Orthogonal Pure S) -/

/-- Weighted parallel reduction (`Prop`-valued so `Step` eliminates into it constructively). -/
inductive WeightedPar : Nat → Term → Term → Prop where
  | s : WeightedPar 0 .s .s
  | var (k : Nat) : WeightedPar 0 (.var k) (.var k)
  | app {wa wb : Nat} {a a' b b' : Term} :
      WeightedPar wa a a' → WeightedPar wb b b' →
      WeightedPar (wa + wb) (a ⋅ b) (a' ⋅ b')
  | beta {wx wy wz : Nat} {x x' y y' z z' : Term} :
      WeightedPar wx x x' → WeightedPar wy y y' → WeightedPar wz z z' →
      WeightedPar (1 + wx + wy + 2 * wz) (S ⋅ x ⋅ y ⋅ z) ((x' ⋅ z') ⋅ (y' ⋅ z'))

private theorem weightedPar_refl (t : Term) : WeightedPar 0 t t := by
  induction t with
  | s => exact .s
  | var k => exact .var k
  | app _ _ iha ihb => exact .app iha ihb

private theorem weightedPar_of_step {a b : Term} (h : Step a b) : ∃ w, WeightedPar w a b := by
  induction h with
  | root x y z => exact ⟨1, .beta (weightedPar_refl x) (weightedPar_refl y) (weightedPar_refl z)⟩
  | left _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨w + 0, .app hw (weightedPar_refl _)⟩
  | right _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨0 + w, .app (weightedPar_refl _) hw⟩

private theorem wpar_beta_lt (wx wy wz : Nat) :
    (wx + wz) + (wy + wz) < 1 + wx + wy + 2 * wz := by
  have heq : (wx + wz) + (wy + wz) = wx + wy + 2 * wz := by
    rw [← Nat.add_assoc (wx + wz) wy wz, Nat.add_assoc wx wz wy, Nat.add_comm wz wy,
        ← Nat.add_assoc wx wy wz, Nat.add_assoc (wx + wy) wz wz, ← Nat.two_mul wz]
  rw [heq, Nat.add_assoc 1 wx wy, Nat.add_assoc 1 (wx + wy) (2 * wz), Nat.add_comm 1 (wx + wy + 2 * wz)]
  exact Nat.lt_succ_self _

private theorem weightedPar_project {w : Nat} {m n m1 : Term}
    (d : WeightedPar w m n) (hs : Step m m1) :
    (∃ w1, w1 < w ∧ WeightedPar w1 m1 n) ∨
    (∃ w1 n1, StepPlus n n1 ∧ WeightedPar w1 m1 n1) := by
  induction d generalizing m1 with
  | s => cases hs
  | var _ => cases hs
  | @beta wx wy wz x x' y y' z z' dx dy dz ihx ihy ihz =>
    cases hs with
    | root _ _ _ =>
      exact Or.inl ⟨(wx + wz) + (wy + wz), wpar_beta_lt wx wy wz, .app (.app dx dz) (.app dy dz)⟩
    | @left _ l1 _ hl =>
      cases hl with
      | @left _ sx1 _ hsx =>
        cases hsx with
        | left hs0 => cases hs0
        | @right _ _ x1 hx =>
          rcases ihx hx with ⟨wx1, hw, dx1⟩ | ⟨wx1, x1', hplus, dx1⟩
          · refine Or.inl ⟨1 + wx1 + wy + 2 * wz, ?_, .beta dx1 dy dz⟩
            exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.add_lt_add_left hw 1) wy) (2 * wz)
          · exact Or.inr ⟨1 + wx1 + wy + 2 * wz, (x1' ⋅ z') ⋅ (y' ⋅ z'),
              stepPlus_left (stepPlus_left hplus z') (y' ⋅ z'), .beta dx1 dy dz⟩
      | @right _ _ y1 hy =>
        rcases ihy hy with ⟨wy1, hw, dy1⟩ | ⟨wy1, y1', hplus, dy1⟩
        · refine Or.inl ⟨1 + wx + wy1 + 2 * wz, ?_, .beta dx dy1 dz⟩
          exact Nat.add_lt_add_right (Nat.add_lt_add_left hw (1 + wx)) (2 * wz)
        · exact Or.inr ⟨1 + wx + wy1 + 2 * wz, (x' ⋅ z') ⋅ (y1' ⋅ z'),
            stepPlus_right (x' ⋅ z') (stepPlus_left hplus z'), .beta dx dy1 dz⟩
    | @right _ _ z1 hz =>
      rcases ihz hz with ⟨wz1, hw, dz1⟩ | ⟨wz1, z1', hplus, dz1⟩
      · refine Or.inl ⟨1 + wx + wy + 2 * wz1, ?_, .beta dx dy dz1⟩
        exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hw (by decide : 0 < 2)) (1 + wx + wy)
      · have hp1 : StepPlus ((x' ⋅ z') ⋅ (y' ⋅ z')) ((x' ⋅ z1') ⋅ (y' ⋅ z')) :=
          stepPlus_left (stepPlus_right x' hplus) (y' ⋅ z')
        have hp2 : StepPlus ((x' ⋅ z1') ⋅ (y' ⋅ z')) ((x' ⋅ z1') ⋅ (y' ⋅ z1')) :=
          stepPlus_right (x' ⋅ z1') (stepPlus_right y' hplus)
        exact Or.inr ⟨1 + wx + wy + 2 * wz1, (x' ⋅ z1') ⋅ (y' ⋅ z1'),
          stepPlus_trans hp1 hp2, .beta dx dy dz1⟩
  | @app wa wb a a' b b' da db iha ihb =>
    cases hs with
    | @left _ a1 _ ha =>
      rcases iha ha with ⟨wa1, hw, da1⟩ | ⟨wa1, a1', hplus, da1⟩
      · exact Or.inl ⟨wa1 + wb, Nat.add_lt_add_right hw wb, .app da1 db⟩
      · exact Or.inr ⟨wa1 + wb, a1' ⋅ b', stepPlus_left hplus b', .app da1 db⟩
    | @right _ _ b1 hb =>
      rcases ihb hb with ⟨wb1, hw, db1⟩ | ⟨wb1, b1', hplus, db1⟩
      · exact Or.inl ⟨wa + wb1, Nat.add_lt_add_left hw wa, .app da db1⟩
      · exact Or.inr ⟨wa + wb1, a' ⋅ b1', stepPlus_right a' hplus, .app da db1⟩
    | @root x y _ =>
      cases da with
      | @app _ _ _ _ _ y' dsx dy =>
        cases dsx with
        | @app _ _ _ _ _ x' ds dx =>
          cases ds
          exact Or.inr ⟨_, (x' ⋅ b') ⋅ (y' ⋅ b'),
            StepPlus.single (Step.root x' y' b'),
            .app (.app dx db) (.app dy db)⟩

private theorem stepPlus_to_transGen {a b : Term} (h : StepPlus a b) :
    TransGen Step a b := by
  induction h with
  | single hs => exact .single hs
  | head hs _ ih => exact transGen_head hs ih

private theorem sn_pullback_weightedPar :
    ∀ {n : Term}, Acc (fun b a => TransGen Step a b) n →
      ∀ (k : Nat) {w : Nat} {m : Term}, WeightedPar w m n → w ≤ k → StrongNormalizing m := by
  intro n hn
  induction hn with
  | intro n _ ihn =>
    intro k
    induction k with
    | zero =>
      intro w m d hk
      refine Acc.intro m (fun m1 hs => ?_)
      rcases weightedPar_project d hs with ⟨w1, hw, _⟩ | ⟨w1, n1, hplus, d1⟩
      · cases Nat.eq_zero_of_le_zero hk
        cases hw
      · exact ihn n1 (stepPlus_to_transGen hplus) w1 d1 (Nat.le_refl _)
    | succ k ihk =>
      intro w m d hk
      refine Acc.intro m (fun m1 hs => ?_)
      rcases weightedPar_project d hs with ⟨w1, hw, d1⟩ | ⟨w1, n1, hplus, d1⟩
      · exact ihk d1 (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw hk))
      · exact ihn n1 (stepPlus_to_transGen hplus) w1 d1 (Nat.le_refl _)

/-- **Conservation Theorem for `CL(S)`**: If `m → n` and `n` is strongly normalizing, then `m` is strongly normalizing. -/
theorem conservation_step {m n : Term} (hs : Step m n) (hsn : StrongNormalizing n) :
    StrongNormalizing m := by
  obtain ⟨w, hw⟩ := weightedPar_of_step hs
  exact sn_pullback_weightedPar (acc_transGen hsn) w hw (Nat.le_refl w)

theorem normalForm_is_sn {nf : Term} (hnf : IsNormalForm nf) : StrongNormalizing nf :=
  Acc.intro nf (fun y hy => False.elim (hnf y hy))

/-- **Church's Theorem for Pure `S` (`WN → SN`)** (100% constructive!). -/
theorem wn_implies_sn {t : Term} (hwn : HasNormalForm t) : StrongNormalizing t := by
  obtain ⟨nf, hred, hnf⟩ := hwn
  induction hred with
  | refl _ => exact normalForm_is_sn hnf
  | next hs _ ih => exact conservation_step hs (ih hnf)

/-! ## 4. Visser–van Oostrom Order Theorem (`ord(M) ≤ 3`, Theorem 22 of Barendregt et al. 2018)
    and No Dynamic 1-HNF / Right-Spine Contamination -/

def hasSpineGe2 : Term → Bool
  | .app (.app _ _) _ => true
  | _ => false

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

/-- Visser–van Oostrom's class `T`: terms whose right spine ends in a variable. -/
def inVisserAny : Term → Bool
  | .s => false
  | .var _ => true
  | .app _ r => inVisserAny r

def inVisserAny2 : Term → Bool
  | .app l r => inVisserAny l && inVisserAny r
  | _ => false

def inVisserAny3 : Term → Bool
  | .app (.app p q) r => inVisserAny p && inVisserAny q && inVisserAny r
  | _ => false

theorem inVisserAny_step {a b : Term} (h : Step a b) :
    inVisserAny a = true → inVisserAny b = true := by
  induction h with
  | root x y z => simp [inVisserAny]
  | left _ _ => simp [inVisserAny]
  | right _ ih => simp [inVisserAny]; exact ih

theorem inVisserAny2_step {a b : Term} (h : Step a b) :
    inVisserAny2 a = true → inVisserAny2 b = true := by
  cases h with
  | root x y z => simp [inVisserAny2, inVisserAny]
  | left hl =>
    simp only [inVisserAny2, Bool.and_eq_true]
    intro ⟨h1, h2⟩
    exact ⟨inVisserAny_step hl h1, h2⟩
  | right hr =>
    simp only [inVisserAny2, Bool.and_eq_true]
    intro ⟨h1, h2⟩
    exact ⟨h1, inVisserAny_step hr h2⟩

theorem inVisserAny3_step {a b : Term} (h : Step a b) :
    inVisserAny3 a = true → inVisserAny3 b = true := by
  cases h with
  | @root x y z =>
    simp only [inVisserAny3, inVisserAny, Bool.and_eq_true]
    intro ⟨⟨hx, _⟩, hz⟩
    exact ⟨⟨hx, hz⟩, hz⟩
  | @left l l' r hl =>
    cases l with
    | s => cases hl
    | var _ => cases hl
    | app p q =>
      simp only [inVisserAny3, Bool.and_eq_true]
      intro ⟨⟨hp, hq⟩, hr⟩
      have h2 : inVisserAny2 l' = true := inVisserAny2_step hl (by simp [inVisserAny2, hp, hq])
      cases l' with
      | s => cases h2
      | var _ => cases h2
      | app p' q' =>
        simp only [inVisserAny2, Bool.and_eq_true] at h2
        exact (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr h2, hr⟩
  | @right l r r' hr =>
    cases l with
    | s => intro h3; cases h3
    | var _ => intro h3; cases h3
    | app p q =>
      simp only [inVisserAny3, Bool.and_eq_true]
      intro ⟨hpq, hr0⟩
      exact ⟨hpq, inVisserAny_step hr hr0⟩

theorem inVisserAny3_reduces {a b : Term} (h : Reduces a b) :
    inVisserAny3 a = true → inVisserAny3 b = true := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (inVisserAny3_step hs hv)

/-- **Visser–van Oostrom Lemma**: For any `S`-term `m` (closed or open) and variables `x, y, z`,
    `m ⋅ (.var x) ⋅ (.var y) ⋅ (.var z)` never reduces to an arity-2 `S`-prefix `S ⋅ a ⋅ b`. -/
theorem visser_van_oostrom_no_sab (m : Term) (x y z : Nat) (a b : Term) :
    ¬ Reduces (m ⋅ .var x ⋅ .var y ⋅ .var z) (S ⋅ a ⋅ b) := by
  intro hred
  have hinit : inVisserAny3 (m ⋅ .var x ⋅ .var y ⋅ .var z) = true := rfl
  have hend := inVisserAny3_reduces hred hinit
  cases hend

private theorem unconsumed_arg_reduces {a b : Term} (h : Reduces a b) :
    ∀ (f : Term) (u : Nat),
      (∀ p q, ¬ Reduces f (S ⋅ p ⋅ q)) →
      a = f ⋅ .var u →
      ∃ f', b = f' ⋅ .var u ∧ Reduces f f' := by
  induction h with
  | refl a0 =>
    intro f u _ ha
    exact ⟨f, ha, Reduces.refl f⟩
  | @next a a1 b hs _ ih =>
    intro f u hno ha
    subst ha
    cases hs with
    | root p q _ =>
      exfalso
      exact hno p q (Reduces.refl _)
    | @left _ f1 _ hf =>
      have hno1 : ∀ p q, ¬ Reduces f1 (S ⋅ p ⋅ q) :=
        fun p q hr => hno p q (Reduces.next hf hr)
      obtain ⟨f', hb, hf'⟩ := ih f1 u hno1 rfl
      exact ⟨f', hb, Reduces.next hf hf'⟩
    | @right _ _ u' hu =>
      cases hu

/-- **Visser–van Oostrom Order Theorem (`ord(M) ≤ 3`, Theorem 22 of Barendregt et al. 2018)**:
    For any pure-`S` term `m` and any 4 variables `x0, x1, x2, x3`, the 4th variable `x3` is never
    consumed in any reduction of `m x0 x1 x2 x3`: every reduct has the form `n' ⋅ (.var x3)` where
    `m x0 x1 x2 →* n'`, and if `x3` does not occur in `m, x0, x1, x2`, then `x3` never occurs in `n'`. -/
theorem visser_van_oostrom_order_le_3 (m : Term) (x0 x1 x2 x3 : Nat) {n : Term}
    (hred : Reduces (m ⋅ .var x0 ⋅ .var x1 ⋅ .var x2 ⋅ .var x3) n) :
    ∃ n', n = n' ⋅ .var x3 ∧
      Reduces (m ⋅ .var x0 ⋅ .var x1 ⋅ .var x2) n' ∧
      (hasVar x3 (m ⋅ .var x0 ⋅ .var x1 ⋅ .var x2) = false → hasVar x3 n' = false) := by
  obtain ⟨n', hn, hred'⟩ := unconsumed_arg_reduces hred
    (m ⋅ .var x0 ⋅ .var x1 ⋅ .var x2) x3 (visser_van_oostrom_no_sab m x0 x1 x2) rfl
  exact ⟨n', hn, hred', hasVar_false_reduces hred'⟩

/-! ## 5. Waldmann's No-Spiral Theorem (Theorem 14 of Barendregt et al. 2018) -/

inductive Ctx where
  | hole : Ctx
  | left : Ctx → Term → Ctx
  | right : Term → Ctx → Ctx
  deriving DecidableEq, Repr

def plugCtx : Ctx → Term → Term
  | .hole, t => t
  | .left c r, t => plugCtx c t ⋅ r
  | .right l c, t => l ⋅ plugCtx c t

/-- Right-spine length `ρ(t) = 1 + rs(t)` (`ρ(S) = ρ(x) = 1`, `ρ(a ⋅ b) = 1 + ρ(b)`). -/
def rho (t : Term) : Nat := 1 + rs t

theorem rho_mono_step {a b : Term} (h : Step a b) : rho a ≤ rho b := by
  induction h with
  | root x y z =>
    exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_add_left (rs z) 1) 1) 1
  | @left _ a' r _ _ => exact Nat.le_refl (rho (a' ⋅ r))
  | right _ ih => exact Nat.add_le_add_left ih 1

/-- Right-spine-labeled pure-S terms (both unflipped and flipped bounded labels). -/
inductive LTerm where
  | s : LTerm
  | var : Nat → LTerm
  | app : Nat → LTerm → LTerm → LTerm
  deriving DecidableEq, Repr

def toLTerm : Term → LTerm
  | .s => .s
  | .var k => .var k
  | .app a b => .app (rho b) (toLTerm a) (toLTerm b)

def maxLabel : LTerm → Nat
  | .s => 0
  | .var _ => 0
  | .app k a b => Nat.max k (Nat.max (maxLabel a) (maxLabel b))

def flipLabels (B : Nat) : LTerm → LTerm
  | .s => .s
  | .var k => .var k
  | .app k a b => .app (B - k) (flipLabels B a) (flipLabels B b)

/-- Combined rewrite + subterm step on `B`-flipped labeled terms (`d = B - k`). -/
inductive StepRB : LTerm → LTerm → Prop where
  | left {d : Nat} {a a' b : LTerm} : StepRB a a' → StepRB (.app d a b) (.app d a' b)
  | right {d : Nat} {a b b' : LTerm} : StepRB b b' → StepRB (.app d a b) (.app d a b')
  | subL (d : Nat) (a b : LTerm) : StepRB (.app d a b) a
  | subR (d : Nat) (a b : LTerm) : StepRB (.app d a b) b
  | lift {d d' : Nat} (a b : LTerm) : d' < d → StepRB (.app d a b) (.app d' a b)
  | beta {d d' d1 d2 : Nat} (x y z : LTerm) :
      d' < d → StepRB (.app d (.app d2 (.app d1 .s x) y) z) (.app d' (.app d x z) (.app d y z))

private theorem stepRB_left_trans {d : Nat} {a a' : LTerm} (h : TransGen StepRB a a') (b : LTerm) :
    TransGen StepRB (.app d a b) (.app d a' b) := by
  induction h with
  | single hs => exact .single (.left hs)
  | tail _ hs ih => exact .tail ih (.left hs)

private theorem stepRB_right_trans {d : Nat} (a : LTerm) {b b' : LTerm} (h : TransGen StepRB b b') :
    TransGen StepRB (.app d a b) (.app d a b') := by
  induction h with
  | single hs => exact .single (.right hs)
  | tail _ hs ih => exact .tail ih (.right hs)

private theorem stepRB_app_acc :
    ∀ (d : Nat),
      (∀ d' < d, ∀ u v,
        Acc (fun y x => TransGen StepRB x y) u →
        Acc (fun y x => TransGen StepRB x y) v →
        Acc (fun y x => TransGen StepRB x y) (.app d' u v)) →
      ∀ (a : LTerm), Acc (fun y x => TransGen StepRB x y) a →
      ∀ (b : LTerm), Acc (fun y x => TransGen StepRB x y) b →
      Acc (fun y x => StepRB x y) (.app d a b) := by
  intro d ih_d a ha
  induction ha with
  | intro a h_prev_a ih_a =>
    intro b hb
    induction hb with
    | intro b h_prev_b ih_b =>
      have ha_acc : Acc (fun y x => TransGen StepRB x y) a := Acc.intro a h_prev_a
      have hb_acc : Acc (fun y x => TransGen StepRB x y) b := Acc.intro b h_prev_b
      refine Acc.intro (LTerm.app d a b) (fun w hw => ?_)
      cases hw with
      | left ha' => exact ih_a _ (.single ha') b hb_acc
      | right hb' => exact ih_b _ (.single hb')
      | subL _ _ _ => exact acc_of_transGen ha_acc
      | subR _ _ _ => exact acc_of_transGen hb_acc
      | lift _ _ hlt => exact acc_of_transGen (ih_d _ hlt a b ha_acc hb_acc)
      | @beta _ d' d1 d2 x y _ hlt =>
        have hax : TransGen StepRB (LTerm.app d2 (LTerm.app d1 .s x) y) x :=
          transGen_head (.subL d2 (.app d1 .s x) y) (.single (.subR d1 .s x))
        have hay : TransGen StepRB (LTerm.app d2 (LTerm.app d1 .s x) y) y :=
          .single (.subR d2 (.app d1 .s x) y)
        have h_xb : Acc (fun y0 x0 => TransGen StepRB x0 y0) (.app d x b) :=
          acc_transGen (ih_a x hax b hb_acc)
        have h_yb : Acc (fun y0 x0 => TransGen StepRB x0 y0) (.app d y b) :=
          acc_transGen (ih_a y hay b hb_acc)
        exact acc_of_transGen (ih_d d' hlt (.app d x b) (.app d y b) h_xb h_yb)

private theorem stepRB_app_all (k : Nat) :
    ∀ d, d ≤ k → ∀ u v,
      Acc (fun y x => TransGen StepRB x y) u →
      Acc (fun y x => TransGen StepRB x y) v →
      Acc (fun y x => TransGen StepRB x y) (.app d u v) := by
  induction k with
  | zero =>
    intro d hd u v hu hv
    refine acc_transGen (stepRB_app_acc d (fun d' hlt => ?_) u hu v hv)
    cases Nat.eq_zero_of_le_zero hd
    cases hlt
  | succ k ihk =>
    intro d hd u v hu hv
    exact acc_transGen (stepRB_app_acc d
      (fun d' hlt => ihk d' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hd))) u hu v hv)

private theorem stepRB_acc_plus (t : LTerm) :
    Acc (fun y x => TransGen StepRB x y) t := by
  induction t with
  | s => exact acc_transGen (Acc.intro LTerm.s (fun _ hy => by cases hy))
  | var k => exact acc_transGen (Acc.intro (LTerm.var k) (fun _ hy => by cases hy))
  | app d u v ihu ihv => exact stepRB_app_all d d (Nat.le_refl d) u v ihu ihv

private theorem maxLabel_le_iff {k : Nat} {a b : LTerm} {B : Nat} :
    maxLabel (.app k a b) ≤ B ↔ k ≤ B ∧ maxLabel a ≤ B ∧ maxLabel b ≤ B := by
  simp only [maxLabel, Nat.max_le]

private theorem step_to_stepRB (B : Nat) {a b : Term} (hs : Step a b)
    (ha : maxLabel (toLTerm a) ≤ B) (hb : maxLabel (toLTerm b) ≤ B) :
    TransGen StepRB (flipLabels B (toLTerm a)) (flipLabels B (toLTerm b)) := by
  induction hs with
  | root x y z =>
    have hb' : rho (y ⋅ z) ≤ B := (maxLabel_le_iff.mp hb).1
    have hlt_rho : rho z < rho (y ⋅ z) := by
      change rho z < 1 + rho z
      rw [Nat.add_comm 1 (rho z)]
      exact Nat.lt_succ_self (rho z)
    have hlt : B - rho (y ⋅ z) < B - rho z := sub_lt_sub_of_lt hlt_rho hb'
    exact .single (.beta (flipLabels B (toLTerm x)) (flipLabels B (toLTerm y)) (flipLabels B (toLTerm z)) hlt)
  | @left l l' r _ ih =>
    have hal := (maxLabel_le_iff.mp ha).2.1
    have hbl := (maxLabel_le_iff.mp hb).2.1
    exact stepRB_left_trans (ih hal hbl) (flipLabels B (toLTerm r))
  | @right l r r' hr ih =>
    have har := (maxLabel_le_iff.mp ha).2.2
    have hbr := (maxLabel_le_iff.mp hb).2.2
    have hk_b := (maxLabel_le_iff.mp hb).1
    have hmono := rho_mono_step hr
    have ih_r := ih har hbr
    exact if heq : rho r = rho r' then by
      simp only [toLTerm, flipLabels, heq]
      exact stepRB_right_trans (flipLabels B (toLTerm l)) ih_r
    else
      have hlt : B - rho r' < B - rho r :=
        sub_lt_sub_of_lt (Nat.lt_of_le_of_ne hmono heq) hk_b
      have h1 : StepRB (.app (B - rho r) (flipLabels B (toLTerm l)) (flipLabels B (toLTerm r)))
          (.app (B - rho r') (flipLabels B (toLTerm l)) (flipLabels B (toLTerm r))) :=
        .lift _ _ hlt
      transGen_head h1 (stepRB_right_trans (flipLabels B (toLTerm l)) ih_r)

private theorem stepPlus_exists_bound {a b : Term} (h : StepPlus a b) :
    ∃ B0, ∀ B, B0 ≤ B →
      maxLabel (toLTerm a) ≤ B ∧ maxLabel (toLTerm b) ≤ B ∧
      TransGen StepRB (flipLabels B (toLTerm a)) (flipLabels B (toLTerm b)) := by
  induction h with
  | @single a b hs =>
    refine ⟨Nat.max (maxLabel (toLTerm a)) (maxLabel (toLTerm b)), fun B hB => ?_⟩
    have ha : maxLabel (toLTerm a) ≤ B := Nat.le_trans (Nat.le_max_left _ _) hB
    have hb : maxLabel (toLTerm b) ≤ B := Nat.le_trans (Nat.le_max_right _ _) hB
    exact ⟨ha, hb, step_to_stepRB B hs ha hb⟩
  | @head a m b hs _ ih =>
    obtain ⟨B1, hB1⟩ := ih
    refine ⟨Nat.max (maxLabel (toLTerm a)) B1, fun B hB => ?_⟩
    have ha : maxLabel (toLTerm a) ≤ B := Nat.le_trans (Nat.le_max_left _ _) hB
    have h1 : B1 ≤ B := Nat.le_trans (Nat.le_max_right _ _) hB
    obtain ⟨hm, hb, hmb⟩ := hB1 B h1
    exact ⟨ha, hb, transGen_trans (step_to_stepRB B hs ha hm) hmb⟩

private theorem plugCtx_to_stepRB (B : Nat) (c : Ctx) (m : Term) :
    ReflTransGen StepRB (flipLabels B (toLTerm (plugCtx c m))) (flipLabels B (toLTerm m)) := by
  induction c with
  | hole => exact .refl _
  | left c' r ih =>
    exact .head (.subL (B - rho r) (flipLabels B (toLTerm (plugCtx c' m))) (flipLabels B (toLTerm r))) ih
  | right l c' ih =>
    exact .head (.subR (B - rho (plugCtx c' m)) (flipLabels B (toLTerm l)) (flipLabels B (toLTerm (plugCtx c' m)))) ih

/-- **Waldmann's No-Spiral Theorem (Theorem 14 of Barendregt, Endrullis, Klop, and Waldmann 2018)**:
    No pure-`S` term `m` (closed or open) admits a non-empty reduction `m →+ C[m]` into a term
    containing `m` as a subterm (for any 1-hole context `c`, empty or non-empty). -/
theorem waldmann_no_spiral (c : Ctx) (m : Term) : ¬ StepPlus m (plugCtx c m) := by
  intro hspiral
  obtain ⟨B0, hB0⟩ := stepPlus_exists_bound hspiral
  have ⟨_, _, htr⟩ := hB0 B0 (Nat.le_refl B0)
  have hsub := plugCtx_to_stepRB B0 c m
  have hcyc := transGen_of_transGen_reflTransGen htr hsub
  exact acc_irrefl (stepRB_acc_plus (flipLabels B0 (toLTerm m))) hcyc

/-- Proper-subterm formulation of No-Spiral: if `c ≠ .hole`, `m` never reduces (even in 0 or more steps)
    to `C[m]`, since `m = C[m]` is impossible by positive leaf count of context siblings. -/
theorem plugCtx_leaves_gt {c : Ctx} (hc : c ≠ .hole) (m : Term) :
    leaves m < leaves (plugCtx c m) := by
  induction c with
  | hole => exfalso; exact hc rfl
  | left c' r ih =>
    have hr := leaves_pos r
    exact if hc' : c' = .hole then by
      subst hc'
      change leaves m < leaves m + leaves r
      exact Nat.lt_add_of_pos_right hr
    else
      Nat.lt_of_lt_of_le (ih hc') (Nat.le_add_right _ _)
  | right l c' ih =>
    have hl := leaves_pos l
    exact if hc' : c' = .hole then by
      subst hc'
      change leaves m < leaves l + leaves m
      rw [Nat.add_comm (leaves l) (leaves m)]
      exact Nat.lt_add_of_pos_right hl
    else
      Nat.lt_of_lt_of_le (ih hc') (Nat.le_add_left _ _)

theorem waldmann_no_proper_spiral {c : Ctx} (hc : c ≠ .hole) (m : Term) :
    ¬ Reduces m (plugCtx c m) := by
  intro hred
  rcases reduces_eq_or_stepPlus hred with heq | hplus
  · have hlt := plugCtx_leaves_gt hc m
    rw [← heq] at hlt
    exact Nat.lt_irrefl _ hlt
  · exact waldmann_no_spiral c m hplus

end FormalAlgebra

#print axioms FormalAlgebra.bergstra_no_cycle
#print axioms FormalAlgebra.church_rosser
#print axioms FormalAlgebra.conservation_step
#print axioms FormalAlgebra.wn_implies_sn
#print axioms FormalAlgebra.visser_van_oostrom_no_sab
#print axioms FormalAlgebra.visser_van_oostrom_order_le_3
#print axioms FormalAlgebra.waldmann_no_spiral
#print axioms FormalAlgebra.waldmann_no_proper_spiral
