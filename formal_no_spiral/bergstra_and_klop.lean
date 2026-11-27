import Std

/-!
# Bergstra's Acyclicity Theorem (Theorem 13), Constructive Unbounded Growth (Remark 16a), and Klop's Flat `{S, K}` Strong Normalization Theorem (Theorem 18)

100% constructive Lean 4.33.1 formalization of Section 5.4 (pp. 86–90) of
Barendregt, Endrullis, Klop, and Waldmann (2018), *"Dance of the Starlings"*:

1. **Pure `S` Syntax, Contexts, Substitutions, and Reductions** (both closed and open `S`-terms).
2. **Bergstra's Theorem 13 (1975, p. 87)**:
   `bergstra_no_cycle : ∀ (M : Term), ¬ StepPlus M M` — proved constructively for all open and
   closed pure-`S` terms via `(leaves, bergstraWeight)`.
3. **Alternative Right-Spine & Minimal-Counterexample Proof of Theorem 13 (pp. 87–88)**:
   `bergstra_no_cycle_via_right_spine` — constructive proof via right-spine monotonicity (`rs`)
   and non-root decomposition.
4. **Remark 16, Part 1 (p. 89 — Constructive Unbounded Term Length)**:
   `infinite_reduction_unbounded_leaves : ∀ f, (∀ n, Step (f n) (f (n + 1))) → ∀ B, ∃ N, B < leaves (f N)`
   with an **explicit computable witness `N`** (zero `Classical.choice`, zero Pigeonhole)!
5. **Klop's Theorem 18 (1976, p. 89 — Strong Normalization of `SP` and Flat `{S, K}`-Terms)**:
   `klop_theorem_18_flat_sk_sn` and `klop_sp_strong_normalizing` — 100% constructive `Acc` proof
   via explicit lexicographic `(skLeaves, bergstraWeight ∘ eraseKToS)` descent.

Strict verification rules: zero `sorry`, zero `Classical.choice`, zero `native_decide`, zero custom axioms.
-/

namespace FormalNoSpiral

/-! ## 0. Constructive Transitive Closure and Well-Foundedness Helpers (Zero `Classical.choice`) -/

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

theorem reflTransGen_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : ReflTransGen R a b) (h2 : ReflTransGen R b c) : ReflTransGen R a c := by
  induction h1 with
  | refl _ => exact h2
  | head hs _ ih => exact .head hs (ih h2)

theorem transGen_of_transGen_reflTransGen {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : TransGen R a b) (h2 : ReflTransGen R b c) : TransGen R a c := by
  induction h2 generalizing a with
  | refl _ => exact h1
  | head hs _ ih => exact ih (.tail h1 hs)

theorem transGen_of_reflTransGen_transGen {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : ReflTransGen R a b) (h2 : TransGen R b c) : TransGen R a c := by
  induction h1 with
  | refl _ => exact h2
  | head hs _ ih => exact transGen_head hs (ih h2)

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

theorem sub_lt_sub_of_lt : ∀ {B a b : Nat}, a < b → b ≤ B → B - b < B - a
  | 0, _, _, h1, h2 => by
    cases Nat.eq_zero_of_le_zero h2
    cases h1
  | B + 1, 0, b + 1, _, _ => by
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    exact Nat.lt_succ_of_le (Nat.sub_le B b)
  | B + 1, a + 1, b + 1, h1, h2 => by
    simp only [Nat.succ_sub_succ_eq_sub]
    exact sub_lt_sub_of_lt (Nat.lt_of_succ_lt_succ h1) (Nat.le_of_succ_le_succ h2)

/-! ## 1. Pure `S` Syntax, Contexts, Substitutions, and Reductions -/

inductive Term where
  | s : Term
  | var : Nat → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

infixl:70 " ⋅ " => Term.app

def S : Term := Term.s

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

def closeTerm (t : Term) : Term :=
  subst (fun _ => .s) t

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

def rightLeaf : Term → Term
  | .s => .s
  | .var k => .var k
  | .app _ b => rightLeaf b

/-- 1-hole pure-`S` contexts (`Definition 11`, p. 86). -/
inductive Ctx where
  | hole : Ctx
  | left : Ctx → Term → Ctx
  | right : Term → Ctx → Ctx
  deriving DecidableEq, Repr

def plugCtx : Ctx → Term → Term
  | .hole, t => t
  | .left c r, t => plugCtx c t ⋅ r
  | .right l c, t => l ⋅ plugCtx c t

def compCtx : Ctx → Ctx → Ctx
  | .hole, d => d
  | .left c r, d => .left (compCtx c d) r
  | .right l c, d => .right l (compCtx c d)

def substCtx (σ : Nat → Term) : Ctx → Ctx
  | .hole => .hole
  | .left c r => .left (substCtx σ c) (subst σ r)
  | .right l c => .right (subst σ l) (substCtx σ c)

def closeCtx (c : Ctx) : Ctx :=
  substCtx (fun _ => .s) c

theorem plugCtx_comp (c d : Ctx) (t : Term) :
    plugCtx (compCtx c d) t = plugCtx c (plugCtx d t) := by
  induction c with
  | hole => rfl
  | left c' r ih => simp only [compCtx, plugCtx, ih]
  | right l c' ih => simp only [compCtx, plugCtx, ih]

theorem subst_plugCtx (σ : Nat → Term) (c : Ctx) (t : Term) :
    subst σ (plugCtx c t) = plugCtx (substCtx σ c) (subst σ t) := by
  induction c with
  | hole => rfl
  | left c' r ih => simp only [plugCtx, substCtx, subst, ih]
  | right l c' ih => simp only [plugCtx, substCtx, subst, ih]

theorem closeTerm_plugCtx (c : Ctx) (t : Term) :
    closeTerm (plugCtx c t) = plugCtx (closeCtx c) (closeTerm t) :=
  subst_plugCtx (fun _ => .s) c t

theorem noVars_closeTerm (t : Term) : noVars (closeTerm t) = true := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => exact (Bool.and_eq_true _ _).mpr ⟨iha, ihb⟩

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

/-! ### Basic Rewriting, Leaf, Spine, and Substitution Lemmas -/

theorem stepPlus_trans {a b c : Term} (h1 : StepPlus a b) (h2 : StepPlus b c) : StepPlus a c := by
  induction h1 with
  | single hs => exact .head hs h2
  | head hs _ ih => exact .head hs (ih h2)

theorem reduces_trans {a b c : Term} (h1 : Reduces a b) (h2 : Reduces b c) : Reduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem stepPlus_of_step_reduces {a b c : Term} (h1 : Step a b) (h2 : Reduces b c) : StepPlus a c := by
  induction h2 generalizing a with
  | refl _ => exact .single h1
  | next hs _ ih => exact .head h1 (ih hs)

theorem stepPlus_of_reduces_stepPlus {a b c : Term} (h1 : Reduces a b) (h2 : StepPlus b c) : StepPlus a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact .head hs (ih h2)

theorem reduces_of_stepPlus {a b : Term} (h : StepPlus a b) : Reduces a b := by
  induction h with
  | single hs => exact .next hs (.refl _)
  | head hs _ ih => exact .next hs ih

theorem reduces_eq_or_stepPlus {a b : Term} (h : Reduces a b) : a = b ∨ StepPlus a b := by
  cases h with
  | refl _ => exact Or.inl rfl
  | next hs hrest => exact Or.inr (stepPlus_of_step_reduces hs hrest)

theorem stepPlus_left {a a' : Term} (h : StepPlus a a') (b : Term) : StepPlus (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | single hs => exact .single (.left hs)
  | head hs _ ih => exact .head (.left hs) ih

theorem stepPlus_right {b b' : Term} (a : Term) (h : StepPlus b b') : StepPlus (a ⋅ b) (a ⋅ b') := by
  induction h with
  | single hs => exact .single (.right hs)
  | head hs _ ih => exact .head (.right hs) ih

theorem plugCtx_step (c : Ctx) {a b : Term} (h : Step a b) : Step (plugCtx c a) (plugCtx c b) := by
  induction c with
  | hole => exact h
  | left c' _ ih => exact .left ih
  | right _ c' ih => exact .right ih

theorem plugCtx_stepPlus (c : Ctx) {a b : Term} (h : StepPlus a b) :
    StepPlus (plugCtx c a) (plugCtx c b) := by
  induction h with
  | single hs => exact .single (plugCtx_step c hs)
  | head hs _ ih => exact .head (plugCtx_step c hs) ih

theorem plugCtx_reduces (c : Ctx) {a b : Term} (h : Reduces a b) :
    Reduces (plugCtx c a) (plugCtx c b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (plugCtx_step c hs) ih

theorem subst_step (σ : Nat → Term) {a b : Term} (h : Step a b) :
    Step (subst σ a) (subst σ b) := by
  induction h with
  | root x y z => exact .root (subst σ x) (subst σ y) (subst σ z)
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem subst_stepPlus (σ : Nat → Term) {a b : Term} (h : StepPlus a b) :
    StepPlus (subst σ a) (subst σ b) := by
  induction h with
  | single hs => exact .single (subst_step σ hs)
  | head hs _ ih => exact .head (subst_step σ hs) ih

theorem subst_reduces (σ : Nat → Term) {a b : Term} (h : Reduces a b) :
    Reduces (subst σ a) (subst σ b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (subst_step σ hs) ih

theorem leaves_pos (t : Term) : 1 ≤ leaves t := by
  induction t with
  | s => exact Nat.le_refl 1
  | var _ => exact Nat.le_refl 1
  | app _ _ _ ihb => exact Nat.le_trans ihb (Nat.le_add_left _ _)

theorem leaves_subst_ge (σ : Nat → Term) (t : Term) : leaves t ≤ leaves (subst σ t) := by
  induction t with
  | s => exact Nat.le_refl 1
  | var k => exact leaves_pos (σ k)
  | app a b iha ihb => exact Nat.add_le_add iha ihb

theorem leaves_plugCtx_ge (c : Ctx) (t : Term) : leaves t ≤ leaves (plugCtx c t) := by
  induction c with
  | hole => exact Nat.le_refl _
  | left c' r ih => exact Nat.le_trans ih (Nat.le_add_right _ (leaves r))
  | right l c' ih => exact Nat.le_trans ih (Nat.le_add_left _ (leaves l))

theorem plugCtx_leaves_gt {c : Ctx} (hc : c ≠ .hole) (t : Term) :
    leaves t < leaves (plugCtx c t) := by
  induction c with
  | hole => exfalso; exact hc rfl
  | left c' r ih =>
    have hr := leaves_pos r
    exact if hc' : c' = .hole then by
      subst hc'
      change leaves t < leaves t + leaves r
      exact Nat.lt_add_of_pos_right hr
    else
      Nat.lt_of_lt_of_le (ih hc') (Nat.le_add_right _ _)
  | right l c' ih =>
    have hl := leaves_pos l
    exact if hc' : c' = .hole then by
      subst hc'
      change leaves t < leaves l + leaves t
      rw [Nat.add_comm (leaves l) (leaves t)]
      exact Nat.lt_add_of_pos_right hl
    else
      Nat.lt_of_lt_of_le (ih hc') (Nat.le_add_left _ _)

/-! ## 2. Bergstra's Acyclicity Theorem (Theorem 13 of Barendregt et al. 2018, p. 87) -/

/-- Bergstra's weight `‖M‖`: `‖S‖ = ‖x‖ = 1` and `‖M ⋅ N‖ = 2‖M‖ + ‖N‖`. -/
def bergstraWeight : Term → Nat
  | .s => 1
  | .var _ => 1
  | .app a b => 2 * bergstraWeight a + bergstraWeight b

theorem bergstraWeight_pos (t : Term) : 1 ≤ bergstraWeight t := by
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

theorem stepPlus_leaves_and_weight {a b : Term} (h : StepPlus a b) :
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

/-- **Bergstra's Acyclicity Theorem (Theorem 13, 1975, *Dance of the Starlings* p. 87)**:
    For every pure-`S` term `M` (open or closed), there is no cyclic reduction `M →+ M`. -/
theorem bergstra_no_cycle (M : Term) : ¬ StepPlus M M := by
  intro hcyc
  rcases stepPlus_leaves_and_weight hcyc with hlt | ⟨_, hw⟩
  · exact Nat.lt_irrefl _ hlt
  · exact Nat.lt_irrefl _ hw

/-! ### Alternative Constructive Proof of Theorem 13 via Right-Spine Length `rs` (pp. 87–88) -/

theorem rs_mono_step {a b : Term} (h : Step a b) : rs a ≤ rs b := by
  induction h with
  | root x y z =>
    change 1 + rs z ≤ 1 + (1 + rs z)
    exact Nat.add_le_add_left (Nat.le_add_left (rs z) 1) 1
  | left _ _ => exact Nat.le_refl _
  | right _ ih => exact Nat.add_le_add_left ih 1

theorem rs_mono_reduces {a b : Term} (h : Reduces a b) : rs a ≤ rs b := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | next hs _ ih => exact Nat.le_trans (rs_mono_step hs) ih

inductive RootStep : Term → Term → Prop where
  | mk (x y z : Term) : RootStep (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))

inductive NonRootStep : Term → Term → Prop where
  | left {a a' b : Term} : Step a a' → NonRootStep (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Step b b' → NonRootStep (a ⋅ b) (a ⋅ b')

inductive NonRootReduces : Term → Term → Prop where
  | refl (a : Term) : NonRootReduces a a
  | next {a b c : Term} : NonRootStep a b → NonRootReduces b c → NonRootReduces a c

theorem step_iff_root_or_nonRoot {a b : Term} :
    Step a b ↔ RootStep a b ∨ NonRootStep a b := by
  constructor
  · intro hs
    cases hs with
    | root x y z => exact Or.inl (.mk x y z)
    | left hl => exact Or.inr (.left hl)
    | right hr => exact Or.inr (.right hr)
  · intro h
    rcases h with ⟨x, y, z⟩ | hnr
    · exact .root x y z
    · cases hnr with
      | left hl => exact .left hl
      | right hr => exact .right hr

theorem nonRootStep_to_step {a b : Term} (h : NonRootStep a b) : Step a b := by
  cases h with
  | left hl => exact .left hl
  | right hr => exact .right hr

theorem nonRootReduces_to_reduces {a b : Term} (h : NonRootReduces a b) : Reduces a b := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (nonRootStep_to_step hs) ih

inductive NonRootPlus : Term → Term → Prop where
  | single {a b : Term} : NonRootStep a b → NonRootPlus a b
  | head {a b c : Term} : NonRootStep a b → NonRootPlus b c → NonRootPlus a c

theorem nonRootPlus_to_nonRootReduces {a b : Term} (h : NonRootPlus a b) : NonRootReduces a b := by
  induction h with
  | single hs => exact .next hs (.refl _)
  | head hs _ ih => exact .next hs ih

theorem nonRootPlus_app_inv {m n : Term} (h : NonRootPlus m n) :
    ∀ a b, m = a ⋅ b →
      ∃ a' b', n = a' ⋅ b' ∧ Reduces a a' ∧ Reduces b b' ∧ (StepPlus a a' ∨ StepPlus b b') := by
  induction h with
  | @single _ _ hs =>
    intro a b hm
    subst hm
    cases hs with
    | @left _ a1 _ ha1 =>
      exact ⟨a1, b, rfl, .next ha1 (.refl _), .refl _, Or.inl (.single ha1)⟩
    | @right _ _ b1 hb1 =>
      exact ⟨a, b1, rfl, .refl _, .next hb1 (.refl _), Or.inr (.single hb1)⟩
  | @head _ m1 _ hs _ ih =>
    intro a b hm
    subst hm
    cases hs with
    | @left _ a1 _ ha1 =>
      obtain ⟨a', b', hn, hra, hrb, _⟩ := ih a1 b rfl
      exact ⟨a', b', hn, .next ha1 hra, hrb, Or.inl (stepPlus_of_step_reduces ha1 hra)⟩
    | @right _ _ b1 hb1 =>
      obtain ⟨a', b', hn, hra, hrb, _⟩ := ih a b1 rfl
      exact ⟨a', b', hn, hra, .next hb1 hrb, Or.inr (stepPlus_of_step_reduces hb1 hrb)⟩

theorem stepPlus_nonRoot_or_root {a b : Term} (h : StepPlus a b) :
    NonRootPlus a b ∨ ∃ x y z, Reduces a (S ⋅ x ⋅ y ⋅ z) ∧ Reduces ((x ⋅ z) ⋅ (y ⋅ z)) b := by
  induction h with
  | @single _ _ hs =>
    rcases step_iff_root_or_nonRoot.mp hs with ⟨x, y, z⟩ | hnr
    · exact Or.inr ⟨x, y, z, .refl _, .refl _⟩
    · exact Or.inl (.single hnr)
  | @head _ _ _ hs hrest ih =>
    rcases step_iff_root_or_nonRoot.mp hs with ⟨x, y, z⟩ | hnr
    · exact Or.inr ⟨x, y, z, .refl _, reduces_of_stepPlus hrest⟩
    · rcases ih with hnr_plus | ⟨x, y, z, hm, hb⟩
      · exact Or.inl (.head hnr hnr_plus)
      · exact Or.inr ⟨x, y, z, .next (nonRootStep_to_step hnr) hm, hb⟩

/-- **Alternative Spine-Minimality Proof of Theorem 13 (*Dance of the Starlings*, pp. 87–88)**:
    Purely structural induction on `M` + right-spine strict growth `rs` on root contractions
    (completely independent of `bergstraWeight`). -/
theorem bergstra_no_cycle_via_right_spine (M : Term) : ¬ StepPlus M M := by
  induction M with
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
    rcases stepPlus_nonRoot_or_root hcyc with hnr | ⟨x, y, z, h1, h2⟩
    · obtain ⟨a', b', heq, _, _, hplus⟩ := nonRootPlus_app_inv hnr a b rfl
      injection heq with ha' hb'
      subst ha'; subst hb'
      rcases hplus with ha_cyc | hb_cyc
      · exact iha ha_cyc
      · exact ihb hb_cyc
    · have hrs1 : rs (a ⋅ b) ≤ 1 + rs z := rs_mono_reduces h1
      have hrs2 : 1 + (1 + rs z) ≤ rs (a ⋅ b) := rs_mono_reduces h2
      have hlt : 1 + rs z < 1 + (1 + rs z) := by
        rw [Nat.add_comm 1 (1 + rs z)]
        exact Nat.lt_succ_self (1 + rs z)
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hrs1 (Nat.lt_of_lt_of_le hlt hrs2))

/-! ## 3. Remark 16, Part 1 (p. 89): Constructive Unbounded Term Length in Infinite Reductions -/

private theorem leaves_grow_within_weight (f : Nat → Term) (hf : ∀ n, Step (f n) (f (n + 1))) :
    ∀ (w k : Nat), bergstraWeight (f k) ≤ w → leaves (f k) < leaves (f (k + w)) := by
  intro w
  induction w with
  | zero =>
    intro k hw
    exfalso
    exact Nat.not_succ_le_zero 0 (Nat.le_trans (bergstraWeight_pos (f k)) hw)
  | succ w ih =>
    intro k hw
    have hs := hf k
    have hle := leaves_mono_step hs
    exact if heq : leaves (f k) = leaves (f (k + 1)) then by
      have hw_drop : bergstraWeight (f (k + 1)) < bergstraWeight (f k) :=
        equal_leaves_strict_weight_drop hs heq
      have hw_le : bergstraWeight (f (k + 1)) ≤ w :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw_drop hw)
      have hrec := ih (k + 1) hw_le
      have hidx : (k + 1) + w = k + (w + 1) := by
        rw [Nat.add_assoc k 1 w, Nat.add_comm 1 w]
      rw [heq, ← hidx]
      exact hrec
    else by
      have hlt1 : leaves (f k) < leaves (f (k + 1)) := Nat.lt_of_le_of_ne hle heq
      have hmono : ∀ d, leaves (f (k + 1)) ≤ leaves (f (k + 1 + d)) := by
        intro d
        induction d with
        | zero => exact Nat.le_refl _
        | succ d ihd =>
          exact Nat.le_trans ihd (leaves_mono_step (hf (k + 1 + d)))
      have hidx : k + 1 + w = k + (w + 1) := by
        rw [Nat.add_assoc k 1 w, Nat.add_comm 1 w]
      rw [← hidx]
      exact Nat.lt_of_lt_of_le hlt1 (hmono w)

/-- Explicit computable index at which `f` exceeds leaf count `B`. -/
def witnessStepForBound (f : Nat → Term) : Nat → Nat
  | 0 => bergstraWeight (f 0)
  | B + 1 =>
      let prev := witnessStepForBound f B
      prev + bergstraWeight (f prev)

theorem witnessStepForBound_gt (f : Nat → Term) (hf : ∀ n, Step (f n) (f (n + 1))) (B : Nat) :
    B < leaves (f (witnessStepForBound f B)) := by
  induction B with
  | zero =>
    have h1 : 1 ≤ leaves (f 0) := leaves_pos (f 0)
    have hlt : leaves (f 0) < leaves (f (0 + bergstraWeight (f 0))) :=
      leaves_grow_within_weight f hf (bergstraWeight (f 0)) 0 (Nat.le_refl _)
    rw [Nat.zero_add] at hlt
    exact Nat.lt_trans (Nat.lt_of_lt_of_le Nat.zero_lt_one h1) hlt
  | succ B ih =>
    let prev := witnessStepForBound f B
    have hle : B + 1 ≤ leaves (f prev) := Nat.succ_le_of_lt ih
    have hlt : leaves (f prev) < leaves (f (prev + bergstraWeight (f prev))) :=
      leaves_grow_within_weight f hf (bergstraWeight (f prev)) prev (Nat.le_refl _)
    exact Nat.lt_of_le_of_lt hle hlt

/-- **Remark 16, Part 1 (*Dance of the Starlings*, p. 89 — Constructive Unbounded Term Size)**:
    In every infinite pure-`S` reduction `f 0 → f 1 → f 2 → ...` (open or closed),
    term length (`leaves`) grows beyond every natural bound `B` at an explicitly computable index `N`. -/
theorem infinite_reduction_unbounded_leaves (f : Nat → Term)
    (hf : ∀ n, Step (f n) (f (n + 1))) (B : Nat) :
    ∃ N, B < leaves (f N) :=
  ⟨witnessStepForBound f B, witnessStepForBound_gt f hf B⟩

/-! ## 4. Klop's Theorem 18 (1976, p. 89): Flat `{S, K}`-Terms and Class `SP` Are Strongly Normalizing -/

/-- `{S, K}` combinatory logic terms (`Section 5.4`, p. 89). -/
inductive SKTerm where
  | s : SKTerm
  | k : SKTerm
  | app : SKTerm → SKTerm → SKTerm
  deriving DecidableEq, Repr

inductive SKStep : SKTerm → SKTerm → Prop where
  | s_root (x y z : SKTerm) :
      SKStep (.app (.app (.app .s x) y) z) (.app (.app x z) (.app y z))
  | k_root (x y : SKTerm) :
      SKStep (.app (.app .k x) y) x
  | left {a a' b : SKTerm} : SKStep a a' → SKStep (.app a b) (.app a' b)
  | right {a b b' : SKTerm} : SKStep b b' → SKStep (.app a b) (.app a b')

def StrongNormalizingSK (t : SKTerm) : Prop :=
  Acc (fun b a => SKStep a b) t

def skLeaves : SKTerm → Nat
  | .s => 1
  | .k => 1
  | .app a b => skLeaves a + skLeaves b

theorem skLeaves_pos (t : SKTerm) : 1 ≤ skLeaves t := by
  induction t with
  | s => exact Nat.le_refl 1
  | k => exact Nat.le_refl 1
  | app _ _ _ ihb => exact Nat.le_trans ihb (Nat.le_add_left _ _)

/-- Replace every `K` leaf by `S` (Klop's projection from `{S, K}` to pure `S`, p. 89). -/
def eraseKToS : SKTerm → Term
  | .s => .s
  | .k => .s
  | .app a b => eraseKToS a ⋅ eraseKToS b

theorem leaves_eraseKToS (t : SKTerm) : leaves (eraseKToS t) = skLeaves t := by
  induction t with
  | s => rfl
  | k => rfl
  | app a b iha ihb => simp only [eraseKToS, leaves, skLeaves, iha, ihb]

/-- Flat `{S, K}`-terms (no visible brackets in left-associative notation, p. 89). -/
inductive IsFlatSK : SKTerm → Prop where
  | s : IsFlatSK .s
  | k : IsFlatSK .k
  | app_s {m : SKTerm} : IsFlatSK m → IsFlatSK (.app m .s)
  | app_k {m : SKTerm} : IsFlatSK m → IsFlatSK (.app m .k)

/-- Klop's reduction-closed superclass `SP` (Theorem 18, p. 89):
    (i) `S, K ∈ SP`;
    (ii) `M ∈ SP ⇒ M S, M K ∈ SP`;
    (iii) `M ∈ SP ⇒ K K M, K S M, S K M, S S M ∈ SP`. -/
inductive InSP : SKTerm → Prop where
  | s : InSP .s
  | k : InSP .k
  | app_s {m : SKTerm} : InSP m → InSP (.app m .s)
  | app_k {m : SKTerm} : InSP m → InSP (.app m .k)
  | kkm {m : SKTerm} : InSP m → InSP (.app (.app .k .k) m)
  | ksm {m : SKTerm} : InSP m → InSP (.app (.app .k .s) m)
  | skm {m : SKTerm} : InSP m → InSP (.app (.app .s .k) m)
  | ssm {m : SKTerm} : InSP m → InSP (.app (.app .s .s) m)

theorem flatSK_subset_inSP {t : SKTerm} (h : IsFlatSK t) : InSP t := by
  induction h with
  | s => exact .s
  | k => exact .k
  | app_s _ ih => exact .app_s ih
  | app_k _ ih => exact .app_k ih

/-- Every `SP` term of the form `a ⋅ b` either has `b ∈ {S, K}` with `a ∈ SP`,
    or is one of `K K m, K S m, S K m, S S m` with `m ∈ SP`. -/
theorem inSP_step_closed_and_ranked {a b : SKTerm} (hsp : InSP a) (hs : SKStep a b) :
    InSP b ∧
      (skLeaves b < skLeaves a ∨
        (skLeaves b = skLeaves a ∧ Step (eraseKToS a) (eraseKToS b))) := by
  induction hs with
  | @k_root x y =>
    cases hsp with
    | app_s hx =>
      cases hx with
      | app_s _ => exact ⟨.s, Or.inl (by change 1 < (1 + 1) + 1; decide)⟩
      | app_k _ => exact ⟨.k, Or.inl (by change 1 < (1 + 1) + 1; decide)⟩
    | app_k hx =>
      cases hx with
      | app_s _ => exact ⟨.s, Or.inl (by change 1 < (1 + 1) + 1; decide)⟩
      | app_k _ => exact ⟨.k, Or.inl (by change 1 < (1 + 1) + 1; decide)⟩
    | kkm hm =>
      refine ⟨.k, Or.inl ?_⟩
      change 1 < (1 + 1) + skLeaves y
      exact Nat.lt_of_lt_of_le (by decide : 1 < 2) (Nat.le_add_right 2 (skLeaves y))
    | ksm hm =>
      refine ⟨.s, Or.inl ?_⟩
      change 1 < (1 + 1) + skLeaves y
      exact Nat.lt_of_lt_of_le (by decide : 1 < 2) (Nat.le_add_right 2 (skLeaves y))
  | @s_root x y z =>
    -- Look at `(.app (.app (.app .s x) y) z) ∈ SP`:
    -- None of `kkm, ksm, skm, ssm` match because their left-left is `.k` or `.s` (not `.app .s x`).
    -- Thus `z` MUST come from `app_s` (`z = .s`) or `app_k` (`z = .k`), and `(.app (.app .s x) y) ∈ SP`!
    cases hsp with
    | app_s hxy =>
      -- `z = .s`, `hxy : InSP (.app (.app .s x) y)`
      have hex : skLeaves (.app (.app x .s) (.app y .s)) = skLeaves (.app (.app (.app .s x) y) .s) := by
        change (skLeaves x + 1) + (skLeaves y + 1) = ((1 + skLeaves x) + skLeaves y) + 1
        rw [Nat.add_comm 1 (skLeaves x), Nat.add_assoc (skLeaves x + 1) (skLeaves y) 1]
      have hstepS : Step (eraseKToS (.app (.app (.app .s x) y) .s))
          (eraseKToS (.app (.app x .s) (.app y .s))) :=
        Step.root (eraseKToS x) (eraseKToS y) .s
      cases hxy with
      | app_s hsx =>
        -- `y = .s`, `hsx : InSP (.app .s x)` -> `x ∈ {.s, .k}`
        cases hsx with
        | app_s _ => exact ⟨.ssm (.app_s .s), Or.inr ⟨hex, hstepS⟩⟩
        | app_k _ => exact ⟨.ksm (.app_s .s), Or.inr ⟨hex, hstepS⟩⟩
      | app_k hsx =>
        -- `y = .k`, `hsx : InSP (.app .s x)` -> `x ∈ {.s, .k}`
        cases hsx with
        | app_s _ => exact ⟨.ssm (.app_s .k), Or.inr ⟨hex, hstepS⟩⟩
        | app_k _ => exact ⟨.ksm (.app_s .k), Or.inr ⟨hex, hstepS⟩⟩
      | skm hm =>
        -- `x = .k`, `y = m ∈ SP`, RHS is `(.k ⋅ .s) ⋅ (m ⋅ .s)` = `ksm (app_s hm)`!
        exact ⟨.ksm (.app_s hm), Or.inr ⟨hex, hstepS⟩⟩
      | ssm hm =>
        -- `x = .s`, `y = m ∈ SP`, RHS is `(.s ⋅ .s) ⋅ (m ⋅ .s)` = `ssm (app_s hm)`!
        exact ⟨.ssm (.app_s hm), Or.inr ⟨hex, hstepS⟩⟩
    | app_k hxy =>
      -- `z = .k`, `hxy : InSP (.app (.app .s x) y)`
      have hex : skLeaves (.app (.app x .k) (.app y .k)) = skLeaves (.app (.app (.app .s x) y) .k) := by
        change (skLeaves x + 1) + (skLeaves y + 1) = ((1 + skLeaves x) + skLeaves y) + 1
        rw [Nat.add_comm 1 (skLeaves x), Nat.add_assoc (skLeaves x + 1) (skLeaves y) 1]
      have hstepS : Step (eraseKToS (.app (.app (.app .s x) y) .k))
          (eraseKToS (.app (.app x .k) (.app y .k))) :=
        Step.root (eraseKToS x) (eraseKToS y) .s
      cases hxy with
      | app_s hsx =>
        cases hsx with
        | app_s _ => exact ⟨.skm (.app_k .s), Or.inr ⟨hex, hstepS⟩⟩
        | app_k _ => exact ⟨.kkm (.app_k .s), Or.inr ⟨hex, hstepS⟩⟩
      | app_k hsx =>
        cases hsx with
        | app_s _ => exact ⟨.skm (.app_k .k), Or.inr ⟨hex, hstepS⟩⟩
        | app_k _ => exact ⟨.kkm (.app_k .k), Or.inr ⟨hex, hstepS⟩⟩
      | skm hm =>
        exact ⟨.kkm (.app_k hm), Or.inr ⟨hex, hstepS⟩⟩
      | ssm hm =>
        exact ⟨.skm (.app_k hm), Or.inr ⟨hex, hstepS⟩⟩
  | @left l l' r hl ih =>
    cases hsp with
    | app_s hsp_l =>
      obtain ⟨hsp_l', hrk⟩ := ih hsp_l
      refine ⟨.app_s hsp_l', ?_⟩
      rcases hrk with hlt | ⟨heq, hsS⟩
      · exact Or.inl (Nat.add_lt_add_right hlt 1)
      · exact Or.inr ⟨congrArg (· + 1) heq, .left hsS⟩
    | app_k hsp_l =>
      obtain ⟨hsp_l', hrk⟩ := ih hsp_l
      refine ⟨.app_k hsp_l', ?_⟩
      rcases hrk with hlt | ⟨heq, hsS⟩
      · exact Or.inl (Nat.add_lt_add_right hlt 1)
      · exact Or.inr ⟨congrArg (· + 1) heq, .left hsS⟩
    | kkm _ =>
      cases hl with
      | left h0 => cases h0
      | right h0 => cases h0
    | ksm _ =>
      cases hl with
      | left h0 => cases h0
      | right h0 => cases h0
    | skm _ =>
      cases hl with
      | left h0 => cases h0
      | right h0 => cases h0
    | ssm _ =>
      cases hl with
      | left h0 => cases h0
      | right h0 => cases h0
  | @right l r r' hr ih =>
    cases hsp with
    | app_s _ => cases hr
    | app_k _ => cases hr
    | kkm hm =>
      obtain ⟨hm', hrk⟩ := ih hm
      refine ⟨.kkm hm', ?_⟩
      rcases hrk with hlt | ⟨heq, hsS⟩
      · exact Or.inl (Nat.add_lt_add_left hlt 2)
      · exact Or.inr ⟨congrArg (2 + ·) heq, .right hsS⟩
    | ksm hm =>
      obtain ⟨hm', hrk⟩ := ih hm
      refine ⟨.ksm hm', ?_⟩
      rcases hrk with hlt | ⟨heq, hsS⟩
      · exact Or.inl (Nat.add_lt_add_left hlt 2)
      · exact Or.inr ⟨congrArg (2 + ·) heq, .right hsS⟩
    | skm hm =>
      obtain ⟨hm', hrk⟩ := ih hm
      refine ⟨.skm hm', ?_⟩
      rcases hrk with hlt | ⟨heq, hsS⟩
      · exact Or.inl (Nat.add_lt_add_left hlt 2)
      · exact Or.inr ⟨congrArg (2 + ·) heq, .right hsS⟩
    | ssm hm =>
      obtain ⟨hm', hrk⟩ := ih hm
      refine ⟨.ssm hm', ?_⟩
      rcases hrk with hlt | ⟨heq, hsS⟩
      · exact Or.inl (Nat.add_lt_add_left hlt 2)
      · exact Or.inr ⟨congrArg (2 + ·) heq, .right hsS⟩

private theorem klop_sp_sn_inner (L : Nat) (ihL : ∀ L' < L, ∀ t, InSP t → skLeaves t = L' → StrongNormalizingSK t) :
    ∀ (W : Nat) (t : SKTerm), InSP t → skLeaves t = L → bergstraWeight (eraseKToS t) ≤ W →
      StrongNormalizingSK t := by
  intro W
  induction W with
  | zero =>
    intro t _ _ hW
    exfalso
    exact Nat.not_succ_le_zero 0 (Nat.le_trans (bergstraWeight_pos (eraseKToS t)) hW)
  | succ W ihW =>
    intro t hsp hL hW
    refine Acc.intro t (fun t' hs => ?_)
    obtain ⟨hsp', hrk⟩ := inSP_step_closed_and_ranked hsp hs
    rcases hrk with hlt | ⟨heq, hsS⟩
    · rw [hL] at hlt
      exact ihL (skLeaves t') hlt t' hsp' rfl
    · have heqS : leaves (eraseKToS t) = leaves (eraseKToS t') := by
        rw [leaves_eraseKToS, leaves_eraseKToS, heq]
      have hw_drop : bergstraWeight (eraseKToS t') < bergstraWeight (eraseKToS t) :=
        equal_leaves_strict_weight_drop hsS heqS
      have hw_le : bergstraWeight (eraseKToS t') ≤ W :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw_drop hW)
      exact ihW t' hsp' (heq.trans hL) hw_le

private theorem klop_sp_sn_by_leaves :
    ∀ (B : Nat) (t : SKTerm), InSP t → skLeaves t ≤ B → StrongNormalizingSK t := by
  intro B
  induction B with
  | zero =>
    intro t _ hB
    exfalso
    exact Nat.not_succ_le_zero 0 (Nat.le_trans (skLeaves_pos t) hB)
  | succ B ihB =>
    intro t hsp hB
    exact if heq : skLeaves t = B + 1 then
      klop_sp_sn_inner (B + 1)
        (fun L' hlt t' hsp' hL' => ihB t' hsp' (by rw [hL']; exact Nat.le_of_lt_succ hlt))
        (bergstraWeight (eraseKToS t)) t hsp heq (Nat.le_refl _)
    else
      ihB t hsp (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hB heq))

/-- **Klop's Superclass Theorem (Theorem 18 proof, *Dance of the Starlings* p. 89)**:
    Every `{S, K}`-term in `SP` is constructively strongly normalizing (`Acc`). -/
theorem klop_sp_strong_normalizing {t : SKTerm} (h : InSP t) : StrongNormalizingSK t :=
  klop_sp_sn_by_leaves (skLeaves t) t h (Nat.le_refl _)

/-- **Klop's Theorem 18 (1976, *Dance of the Starlings* p. 89)**:
    Every flat `{S, K}`-term is constructively strongly normalizing (`Acc`). -/
theorem klop_theorem_18_flat_sk_sn {t : SKTerm} (h : IsFlatSK t) : StrongNormalizingSK t :=
  klop_sp_strong_normalizing (flatSK_subset_inSP h)

end FormalNoSpiral

#print axioms FormalNoSpiral.bergstra_no_cycle
#print axioms FormalNoSpiral.bergstra_no_cycle_via_right_spine
#print axioms FormalNoSpiral.infinite_reduction_unbounded_leaves
#print axioms FormalNoSpiral.klop_sp_strong_normalizing
#print axioms FormalNoSpiral.klop_theorem_18_flat_sk_sn
