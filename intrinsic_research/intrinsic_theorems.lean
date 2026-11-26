import Std

namespace IntrinsicTheorems

/-!
# Intrinsic Structure, Productivity, Normal-Order Barriers, and Non-Convertibility in Pure S (`CL(S)`)

Machine-checked in Lean 4.33.1 with zero `sorry` and zero user-declared axioms.
-/

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true a b).mp h).1

theorem and_right {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true a b).mp h).2

inductive Term where
  | s : Term
  | var : Nat → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

infixl:70 " ⋅ " => Term.app

def S : Term := Term.s
def T_comb : Term := S ⋅ S
def A_comb : Term := S ⋅ S ⋅ S
def AAA : Term := A_comb ⋅ A_comb ⋅ A_comb
def Zachos : Term := (S ⋅ T_comb ⋅ T_comb) ⋅ (S ⋅ T_comb ⋅ T_comb)
def Wolfram2 : Term := S ⋅ S ⋅ S ⋅ (S ⋅ T_comb) ⋅ T_comb

inductive Step : Term → Term → Prop where
  | root (x y z : Term) : Step (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : Step a a' → Step (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Step b b' → Step (a ⋅ b) (a ⋅ b')

inductive Reduces : Term → Term → Prop where
  | refl (a : Term) : Reduces a a
  | next {a b c : Term} : Step a b → Reduces b c → Reduces a c

inductive ConvS : Term → Term → Prop where
  | refl (a : Term) : ConvS a a
  | step {a b : Term} : Step a b → ConvS a b
  | symm {a b : Term} : ConvS a b → ConvS b a
  | trans {a b c : Term} : ConvS a b → ConvS b c → ConvS a c

/-! ## 1. Right-Spine Monotonicity -/

def rs : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app _ b => 1 + rs b

theorem rs_mono_step {a b : Term} (h : Step a b) : rs a ≤ rs b := by
  induction h with
  | root x y z => simp [rs]
  | left _ _ => simp [rs]
  | right _ ih => simp [rs]; omega

theorem rs_mono_reduces {a b : Term} (h : Reduces a b) : rs a ≤ rs b := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | next hs _ ih => exact Nat.le_trans (rs_mono_step hs) ih

/-! ## 2. No Dynamic 1-HNF Lemma -/

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
    | app l1 l2 => intro _; rfl

theorem spineGe2_preserved_reduces {a b : Term} (h : Reduces a b) :
    hasSpineGe2 a = true → hasSpineGe2 b = true := by
  induction h with
  | refl _ => intro hge; exact hge
  | next hs _ ih => intro hge; exact ih (spineGe2_preserved_step hs hge)

theorem no_dynamic_hnf1 (a b c w : Term) :
    ¬ Reduces (a ⋅ b ⋅ c) (S ⋅ w) ∧ ¬ Reduces (a ⋅ b ⋅ c) S := by
  constructor
  · intro h
    have hge := spineGe2_preserved_reduces h rfl
    cases hge
  · intro h
    have hge := spineGe2_preserved_reduces h rfl
    cases hge

theorem s_app_reduces_inv {a b : Term} (h : Reduces a b) :
    ∀ (x w : Term), a = S ⋅ x → b = S ⋅ w → Reduces x w := by
  induction h with
  | refl u =>
    intro x w h1 h2
    have hxw : x = w := by
      have heq := h1.symm.trans h2
      injection heq with _ hxw
    subst hxw
    exact Reduces.refl _
  | @next u v z hs _ ih =>
    intro x w hu hz
    subst hu
    cases hs with
    | left hl => cases hl
    | @right _ _ x' hx' => exact Reduces.next hx' (ih x' w rfl hz)

theorem var_app_not_reduces_s_app {a b : Term} (h : Reduces a b) :
    ∀ (k : Nat) (x w : Term), a = Term.var k ⋅ x → b = S ⋅ w → False := by
  induction h with
  | refl u =>
    intro k x w h1 h2
    have heq := h1.symm.trans h2
    injection heq with hk _
    cases hk
  | @next u v z hs _ ih =>
    intro k x w hu hz
    subst hu
    cases hs with
    | left hl => cases hl
    | @right _ _ x' _ => exact ih k x' w rfl hz

theorem app_reduces_to_hnf1_iff (f x w : Term) (h : Reduces (f ⋅ x) (S ⋅ w)) :
    f = S ∧ Reduces x w := by
  cases f with
  | s => exact ⟨rfl, s_app_reduces_inv h x w rfl rfl⟩
  | var k => exfalso; exact var_app_not_reduces_s_app h k x w rfl rfl
  | app f1 f2 => exfalso; exact (no_dynamic_hnf1 f1 f2 x w).1 h

/-! ## 3. Visser Variable-Tail Closure & The Visser–Right-Spine Contamination Theorem -/

def inVisser (v : Nat) : Term → Bool
  | .s => false
  | .var k => decide (k = v)
  | .app _ r => inVisser v r

def inVisser2 (v : Nat) : Term → Bool
  | .app l r => inVisser v l && inVisser v r
  | _ => false

theorem inVisser_step {v : Nat} {a b : Term} (h : Step a b) :
    inVisser v a = true → inVisser v b = true := by
  induction h with
  | root x y z => simp [inVisser]
  | left _ _ => simp [inVisser]
  | right _ ih => simp [inVisser]; exact ih

theorem inVisser2_step {v : Nat} {a b : Term} (h : Step a b) :
    inVisser2 v a = true → inVisser2 v b = true := by
  cases h with
  | root x y z => simp [inVisser2, inVisser]
  | left hl =>
    simp [inVisser2]
    intro h1 h2
    exact ⟨inVisser_step hl h1, h2⟩
  | right hr =>
    simp [inVisser2]
    intro h1 h2
    exact ⟨h1, inVisser_step hr h2⟩

theorem inVisser2_reduces {v : Nat} {a b : Term} (h : Reduces a b) :
    inVisser2 v a = true → inVisser2 v b = true := by
  induction h with
  | refl _ => intro hv; exact hv
  | next hs _ ih => intro hv; exact ih (inVisser2_step hs hv)

theorem var_reduces_aux {a b : Term} (h : Reduces a b) :
    ∀ (k : Nat), a = .var k → b = .var k := by
  induction h with
  | refl _ => intro k ha; exact ha
  | next hs _ _ => intro k ha; subst ha; cases hs

theorem contamination_aux {a b : Term} (h : Reduces a b) :
    ∀ (m p q : Term), a = m ⋅ (.var 2) → b = S ⋅ p ⋅ q →
      (Reduces m (S ⋅ p) ∧ q = .var 2) ∨ (inVisser 2 p = true ∧ inVisser 2 q = true) := by
  induction h with
  | refl u =>
    intro m p q ha hb
    have heq := ha.symm.trans hb
    injection heq with hm hq
    subst hm
    exact Or.inl ⟨Reduces.refl _, hq.symm⟩
  | @next u v z hs hrest ih =>
    intro m p q ha hb
    subst ha
    cases hs with
    | root x y _ =>
      have hv2 : inVisser2 2 ((x ⋅ .var 2) ⋅ (y ⋅ .var 2)) = true := by
        simp [inVisser2, inVisser]
      have hv_end := inVisser2_reduces hrest hv2
      subst hb
      simp [inVisser2, inVisser] at hv_end
      exact Or.inr hv_end
    | @left _ m' _ hm =>
      rcases ih m' p q rfl hb with ⟨hm', hq⟩ | hvis
      · exact Or.inl ⟨Reduces.next hm hm', hq⟩
      · exact Or.inr hvis
    | @right _ _ z' hz' =>
      cases hz'

theorem visser_right_spine_contamination (n p q : Term)
    (h : Reduces (n ⋅ (.var 1) ⋅ (.var 2)) (S ⋅ p ⋅ q)) :
    (n = S ∧ p = .var 1 ∧ q = .var 2) ∨ (inVisser 2 p = true ∧ inVisser 2 q = true) := by
  rcases contamination_aux h (n ⋅ .var 1) p q rfl rfl with ⟨hmp, hq⟩ | hvis
  · have ⟨hn, hp1⟩ := app_reduces_to_hnf1_iff n (.var 1) p hmp
    exact Or.inl ⟨hn, var_reduces_aux hp1 1 rfl, hq⟩
  · exact Or.inr hvis

/-! ## 4. Exact 39-State Productivity S-Algebra `A_P` (Question 5 of Barendregt et al. 2018) -/

inductive StateP where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p25 | p26 | p27 | p28 | p29 | p30 | p31 | p32 | p33 | p34 | p35 | p36 | p37 | p38
  deriving DecidableEq, Repr

def delta_StateP : StateP → StateP → StateP
  | .p0, y => match y with | .p0 => .p1 | .p1 => .p2 | .p2 => .p4 | .p3 => .p5 | .p4 => .p8 | .p5 => .p9 | .p6 => .p10 | .p7 => .p11 | .p8 => .p9 | .p10 => .p9 | .p12 => .p19 | .p13 => .p10 | .p17 => .p20 | .p19 => .p9 | .p21 => .p8 | .p22 => .p9 | .p28 => .p20 | .p30 => .p9 | .p31 => .p9 | .p37 => .p37 | .p38 => .p9 | _ => .p18
  | .p1, y => match y with | .p0 => .p3 | .p1 => .p6 | .p2 => .p12 | .p4 => .p21 | .p5 => .p22 | .p7 => .p7 | .p8 => .p30 | .p9 => .p9 | .p10 => .p31 | .p11 => .p20 | .p12 => .p12 | .p14 => .p32 | .p15 => .p15 | .p16 => .p16 | .p17 => .p17 | .p18 => .p18 | .p19 => .p38 | .p20 => .p20 | .p21 => .p21 | .p22 => .p22 | .p23 => .p23 | .p24 => .p24 | .p25 => .p25 | .p26 => .p26 | .p27 => .p27 | .p28 => .p28 | .p29 => .p29 | .p30 => .p30 | .p31 => .p31 | .p32 => .p32 | .p33 => .p33 | .p34 => .p34 | .p35 => .p35 | .p36 => .p36 | .p37 => .p37 | .p38 => .p38 | _ => .p13
  | .p2, y => match y with | .p0 => .p7 | .p1 => .p14 | .p2 => .p15 | .p3 => .p23 | .p6 => .p23 | .p13 => .p23 | .p17 => .p27 | .p24 => .p24 | .p26 => .p27 | .p27 => .p27 | .p28 => .p27 | .p29 => .p29 | .p34 => .p24 | .p35 => .p27 | .p36 => .p24 | .p37 => .p37 | _ => .p33
  | .p3, y => match y with | .p0 => .p6 | .p1 => .p15 | .p2 => .p24 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p4, y => match y with | .p0 => .p16 | .p1 => .p25 | .p2 => .p27 | .p3 => .p24 | .p4 => .p24 | .p6 => .p24 | .p7 => .p24 | .p12 => .p24 | .p13 => .p24 | .p17 => .p24 | .p21 => .p24 | .p28 => .p24 | .p37 => .p37 | _ => .p29
  | .p5, y => match y with | .p0 => .p17 | .p1 => .p26 | .p3 => .p34 | .p6 => .p34 | .p13 => .p34 | .p29 => .p29 | .p37 => .p37 | _ => .p24
  | .p6, y => match y with | .p0 => .p13 | .p1 => .p23 | .p2 => .p24 | .p3 => .p34 | .p4 => .p24 | .p6 => .p36 | .p12 => .p24 | .p13 => .p36 | .p21 => .p24 | .p37 => .p37 | _ => .p29
  | .p7, y => match y with | .p0 => .p15 | .p1 => .p24 | .p17 => .p37 | .p24 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p8, y => match y with | .p0 => .p27 | .p1 => .p27 | .p2 => .p24 | .p3 => .p24 | .p4 => .p24 | .p6 => .p24 | .p7 => .p24 | .p12 => .p24 | .p13 => .p24 | .p17 => .p24 | .p21 => .p24 | .p28 => .p24 | .p37 => .p37 | _ => .p29
  | .p9, y => match y with | .p0 => .p24 | .p37 => .p37 | _ => .p29
  | .p10, y => match y with | .p0 => .p28 | .p1 => .p35 | .p3 => .p36 | .p6 => .p36 | .p13 => .p36 | .p29 => .p29 | .p37 => .p37 | _ => .p24
  | .p11, y => match y with | .p0 => .p24 | .p1 => .p24 | .p2 => .p24 | .p3 => .p24 | .p4 => .p24 | .p6 => .p24 | .p12 => .p24 | .p13 => .p24 | .p21 => .p24 | .p37 => .p37 | _ => .p29
  | .p12, y => match y with | .p0 => .p7 | .p1 => .p33 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p13, y => match y with | .p0 => .p13 | .p1 => .p33 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p14, y => match y with | .p0 => .p24 | .p1 => .p36 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p15 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p15, y => match y with | .p14 => .p37 | .p15 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p32 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p16, y => match y with | .p0 => .p24 | .p17 => .p37 | .p24 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p17, y => match y with | .p0 => .p23 | .p1 => .p29 | _ => .p37
  | .p18, y => match y with | .p37 => .p37 | _ => .p29
  | .p19, y => match y with | .p0 => .p35 | .p1 => .p27 | .p2 => .p24 | .p3 => .p24 | .p4 => .p24 | .p6 => .p24 | .p7 => .p24 | .p12 => .p24 | .p13 => .p24 | .p17 => .p24 | .p21 => .p24 | .p28 => .p24 | .p37 => .p37 | _ => .p29
  | .p20, y => match y with | .p0 => .p24 | .p1 => .p24 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p21, y => match y with | .p0 => .p16 | .p1 => .p33 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p22, y => match y with | .p0 => .p17 | .p1 => .p27 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p23, y => match y with | .p0 => .p24 | .p7 => .p37 | .p14 => .p37 | .p15 => .p37 | .p16 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p32 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p24, y => match y with | .p0 => .p29 | _ => .p37
  | .p25, y => match y with | .p1 => .p24 | .p7 => .p37 | .p14 => .p37 | .p15 => .p37 | .p16 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p32 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p26, y => match y with | .p0 => .p34 | .p1 => .p29 | _ => .p37
  | .p27, y => match y with | .p0 => .p29 | .p1 => .p29 | _ => .p37
  | .p28, y => match y with | .p0 => .p33 | .p1 => .p29 | _ => .p37
  | .p29, _ => .p37
  | .p30, y => match y with | .p0 => .p27 | .p1 => .p27 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p31, y => match y with | .p0 => .p28 | .p1 => .p27 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p32, y => match y with | .p0 => .p24 | .p1 => .p24 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p15 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p33, y => match y with | .p7 => .p37 | .p14 => .p37 | .p15 => .p37 | .p16 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p32 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p34, y => match y with | .p0 => .p36 | _ => .p37
  | .p35, y => match y with | .p0 => .p24 | .p1 => .p29 | _ => .p37
  | .p36, y => match y with | .p0 => .p24 | _ => .p37
  | .p37, _ => .p37
  | .p38, y => match y with | .p0 => .p35 | .p1 => .p27 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29

def checkAll1_StateP (p : StateP → Bool) : Bool :=
  (((((p .p0 && p .p1) && (p .p2 && p .p3)) && ((p .p4 && p .p5) && (p .p6 && (p .p7 && p .p8)))) && (((p .p9 && p .p10) && (p .p11 && (p .p12 && p .p13))) && ((p .p14 && p .p15) && (p .p16 && (p .p17 && p .p18))))) && ((((p .p19 && p .p20) && (p .p21 && (p .p22 && p .p23))) && ((p .p24 && p .p25) && (p .p26 && (p .p27 && p .p28)))) && (((p .p29 && p .p30) && (p .p31 && (p .p32 && p .p33))) && ((p .p34 && p .p35) && (p .p36 && (p .p37 && p .p38))))))

theorem checkAll1_StateP_sound (p : StateP → Bool)
    (h : checkAll1_StateP p = true) (x : StateP) : p x = true :=
  match x with
  | .p0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .p1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .p2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .p3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .p4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .p5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .p6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .p7 => (and_left (and_right (and_right (and_right (and_left (and_left h))))))
  | .p8 => (and_right (and_right (and_right (and_right (and_left (and_left h))))))
  | .p9 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .p10 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .p11 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .p12 => (and_left (and_right (and_right (and_left (and_right (and_left h))))))
  | .p13 => (and_right (and_right (and_right (and_left (and_right (and_left h))))))
  | .p14 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .p15 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .p16 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .p17 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .p18 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .p19 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .p20 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .p21 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .p22 => (and_left (and_right (and_right (and_left (and_left (and_right h))))))
  | .p23 => (and_right (and_right (and_right (and_left (and_left (and_right h))))))
  | .p24 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .p25 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .p26 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .p27 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .p28 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .p29 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .p30 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .p31 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .p32 => (and_left (and_right (and_right (and_left (and_right (and_right h))))))
  | .p33 => (and_right (and_right (and_right (and_left (and_right (and_right h))))))
  | .p34 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .p35 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .p36 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .p37 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .p38 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateP (p : StateP → StateP → Bool) : Bool :=
  checkAll1_StateP (fun x => checkAll1_StateP (fun y => p x y))

theorem checkAll2_StateP_sound (p : StateP → StateP → Bool)
    (h : checkAll2_StateP p = true) (x y : StateP) : p x y = true :=
  checkAll1_StateP_sound _ (checkAll1_StateP_sound _ h x) y

private theorem s_row_StateP_0 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p0) y) z = delta_StateP (delta_StateP .p0 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_1 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p1) y) z = delta_StateP (delta_StateP .p1 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_2 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p2) y) z = delta_StateP (delta_StateP .p2 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_3 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p3) y) z = delta_StateP (delta_StateP .p3 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_4 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p4) y) z = delta_StateP (delta_StateP .p4 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_5 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p5) y) z = delta_StateP (delta_StateP .p5 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_6 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p6) y) z = delta_StateP (delta_StateP .p6 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_7 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p7) y) z = delta_StateP (delta_StateP .p7 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_8 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p8) y) z = delta_StateP (delta_StateP .p8 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_9 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p9) y) z = delta_StateP (delta_StateP .p9 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_10 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p10) y) z = delta_StateP (delta_StateP .p10 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_11 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p11) y) z = delta_StateP (delta_StateP .p11 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_12 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p12) y) z = delta_StateP (delta_StateP .p12 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_13 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p13) y) z = delta_StateP (delta_StateP .p13 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_14 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p14) y) z = delta_StateP (delta_StateP .p14 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_15 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p15) y) z = delta_StateP (delta_StateP .p15 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_16 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p16) y) z = delta_StateP (delta_StateP .p16 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_17 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p17) y) z = delta_StateP (delta_StateP .p17 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_18 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p18) y) z = delta_StateP (delta_StateP .p18 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_19 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p19) y) z = delta_StateP (delta_StateP .p19 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_20 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p20) y) z = delta_StateP (delta_StateP .p20 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_21 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p21) y) z = delta_StateP (delta_StateP .p21 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_22 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p22) y) z = delta_StateP (delta_StateP .p22 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_23 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p23) y) z = delta_StateP (delta_StateP .p23 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_24 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p24) y) z = delta_StateP (delta_StateP .p24 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_25 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p25) y) z = delta_StateP (delta_StateP .p25 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_26 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p26) y) z = delta_StateP (delta_StateP .p26 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_27 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p27) y) z = delta_StateP (delta_StateP .p27 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_28 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p28) y) z = delta_StateP (delta_StateP .p28 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_29 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p29) y) z = delta_StateP (delta_StateP .p29 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_30 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p30) y) z = delta_StateP (delta_StateP .p30 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_31 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p31) y) z = delta_StateP (delta_StateP .p31 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_32 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p32) y) z = delta_StateP (delta_StateP .p32 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_33 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p33) y) z = delta_StateP (delta_StateP .p33 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_34 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p34) y) z = delta_StateP (delta_StateP .p34 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_35 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p35) y) z = delta_StateP (delta_StateP .p35 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_36 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p36) y) z = delta_StateP (delta_StateP .p36 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_37 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p37) y) z = delta_StateP (delta_StateP .p37 z) (delta_StateP y z))) = true := rfl
private theorem s_row_StateP_38 : checkAll2_StateP (fun y z => decide (delta_StateP (delta_StateP (delta_StateP .p0 .p38) y) z = delta_StateP (delta_StateP .p38 z) (delta_StateP y z))) = true := rfl

theorem delta_StateP_s_law (x y z : StateP) :
    delta_StateP (delta_StateP (delta_StateP .p0 x) y) z =
    delta_StateP (delta_StateP x z) (delta_StateP y z) :=
  match x with
  | .p0 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_0 y z)
  | .p1 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_1 y z)
  | .p2 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_2 y z)
  | .p3 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_3 y z)
  | .p4 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_4 y z)
  | .p5 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_5 y z)
  | .p6 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_6 y z)
  | .p7 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_7 y z)
  | .p8 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_8 y z)
  | .p9 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_9 y z)
  | .p10 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_10 y z)
  | .p11 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_11 y z)
  | .p12 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_12 y z)
  | .p13 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_13 y z)
  | .p14 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_14 y z)
  | .p15 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_15 y z)
  | .p16 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_16 y z)
  | .p17 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_17 y z)
  | .p18 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_18 y z)
  | .p19 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_19 y z)
  | .p20 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_20 y z)
  | .p21 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_21 y z)
  | .p22 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_22 y z)
  | .p23 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_23 y z)
  | .p24 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_24 y z)
  | .p25 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_25 y z)
  | .p26 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_26 y z)
  | .p27 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_27 y z)
  | .p28 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_28 y z)
  | .p29 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_29 y z)
  | .p30 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_30 y z)
  | .p31 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_31 y z)
  | .p32 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_32 y z)
  | .p33 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_33 y z)
  | .p34 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_34 y z)
  | .p35 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_35 y z)
  | .p36 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_36 y z)
  | .p37 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_37 y z)
  | .p38 => of_decide_eq_true (checkAll2_StateP_sound _ s_row_StateP_38 y z)


def isAccP (x : StateP) : Bool := x != .p37

theorem deltaP_sink_bool :
    checkAll1_StateP (fun x =>
      decide (delta_StateP .p37 x = .p37 ∧ delta_StateP x .p37 = .p37)) = true := rfl

theorem deltaP_sink (x : StateP) :
    delta_StateP .p37 x = .p37 ∧ delta_StateP x .p37 = .p37 :=
  of_decide_eq_true (checkAll1_StateP_sound _ deltaP_sink_bool x)

theorem deltaP_hnf1_iff_bool :
    checkAll1_StateP (fun x => decide (isAccP (delta_StateP .p0 x) = isAccP x)) = true := rfl

theorem deltaP_hnf1_iff (x : StateP) : isAccP (delta_StateP .p0 x) = isAccP x :=
  of_decide_eq_true (checkAll1_StateP_sound _ deltaP_hnf1_iff_bool x)

theorem deltaP_hnf2_iff_bool :
    checkAll2_StateP (fun x y =>
      decide (isAccP (delta_StateP (delta_StateP .p0 x) y) = (isAccP x && isAccP y))) = true := rfl

theorem deltaP_hnf2_iff (x y : StateP) :
    isAccP (delta_StateP (delta_StateP .p0 x) y) = (isAccP x && isAccP y) :=
  of_decide_eq_true (checkAll2_StateP_sound _ deltaP_hnf2_iff_bool x y)

def evalP : Term → StateP
  | .s => .p0
  | .var _ => .p0
  | .app a b => delta_StateP (evalP a) (evalP b)

theorem evalP_step_invariant {a b : Term} (h : Step a b) : evalP a = evalP b := by
  induction h with
  | root x y z => exact delta_StateP_s_law (evalP x) (evalP y) (evalP z)
  | left _ ih => simp [evalP, ih]
  | right _ ih => simp [evalP, ih]

theorem evalP_conv_invariant {a b : Term} (h : ConvS a b) : evalP a = evalP b := by
  induction h with
  | refl _ => rfl
  | step hs => exact evalP_step_invariant hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem zachos_productive_state : evalP Zachos = .p29 ∧ isAccP (evalP Zachos) = true := by
  decide

theorem wolfram2_nonproductive_state : evalP Wolfram2 = .p37 ∧ isAccP (evalP Wolfram2) = false := by
  decide

/-! ## 5. Exact 36-State S-Algebra `A_36` & Resolution of Barendregt et al. (2018) Question 31 -/

inductive State36 where
  | q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20 | q21 | q22 | q23 | q24 | q25 | q26 | q27 | q28 | q29 | q30 | q31 | q32 | q33 | q34 | q35
  deriving DecidableEq, Repr

def delta_State36 : State36 → State36 → State36
  | .q0, y => match y with | .q0 => .q1 | .q1 => .q2 | .q2 => .q3 | .q3 => .q4 | .q4 => .q5 | .q5 => .q5 | .q6 => .q7 | .q7 => .q8 | .q8 => .q9 | .q11 => .q12 | .q12 => .q8 | .q13 => .q12 | .q14 => .q15 | .q15 => .q8 | .q16 => .q8 | .q17 => .q9 | .q18 => .q19 | .q19 => .q9 | .q20 => .q21 | .q21 => .q9 | .q26 => .q27 | .q28 => .q9 | .q29 => .q9 | .q30 => .q9 | .q31 => .q27 | .q32 => .q9 | _ => .q10
  | .q1, y => match y with | .q0 => .q6 | .q1 => .q11 | _ => .q13
  | .q2, y => match y with | .q0 => .q14 | .q1 => .q16 | .q2 => .q8 | .q3 => .q9 | .q6 => .q17 | .q7 => .q9 | .q11 => .q17 | .q12 => .q9 | .q13 => .q17 | _ => .q10
  | .q3, y => match y with | .q0 => .q18 | _ => .q20
  | .q4, y => match y with | .q0 => .q8 | _ => .q10
  | .q5, _ => .q10
  | .q6, y => match y with | .q0 => .q11 | .q1 => .q8 | .q2 => .q20 | .q3 => .q10 | .q4 => .q10 | .q5 => .q10 | .q6 => .q22 | .q11 => .q22 | .q13 => .q22 | .q14 => .q24 | .q18 => .q25 | .q26 => .q25 | .q31 => .q25 | _ => .q23
  | .q7, y => match y with | .q0 => .q26 | .q1 => .q28 | .q2 => .q29 | .q3 => .q22 | .q6 => .q30 | .q7 => .q22 | .q11 => .q30 | .q12 => .q22 | .q13 => .q30 | _ => .q24
  | .q8, y => match y with | .q0 => .q24 | _ => .q23
  | .q9, y => match y with | .q0 => .q25 | _ => .q23
  | .q10, _ => .q23
  | .q11, y => match y with | .q0 => .q13 | .q1 => .q17 | .q2 => .q20 | .q3 => .q10 | .q4 => .q10 | .q5 => .q10 | .q6 => .q30 | .q11 => .q29 | .q13 => .q29 | .q14 => .q24 | .q18 => .q25 | .q26 => .q25 | .q31 => .q25 | _ => .q23
  | .q12, y => match y with | .q0 => .q31 | .q1 => .q29 | .q2 => .q29 | .q3 => .q22 | .q6 => .q29 | .q7 => .q22 | .q11 => .q29 | .q12 => .q22 | .q13 => .q29 | _ => .q24
  | .q13, y => match y with | .q0 => .q13 | .q1 => .q10 | .q2 => .q20 | .q3 => .q10 | .q4 => .q10 | .q5 => .q10 | .q6 => .q24 | .q11 => .q24 | .q13 => .q24 | .q14 => .q24 | .q18 => .q25 | .q26 => .q25 | .q31 => .q25 | _ => .q23
  | .q14, y => match y with | .q0 => .q8 | .q1 => .q20 | .q2 => .q10 | .q3 => .q10 | .q4 => .q10 | .q5 => .q10 | _ => .q23
  | .q15, _ => .q24
  | .q16, y => match y with | .q0 => .q22 | .q1 => .q29 | _ => .q24
  | .q17, y => match y with | .q0 => .q22 | _ => .q23
  | .q18, y => match y with | .q0 => .q20 | .q1 => .q24 | _ => .q23
  | .q19, y => match y with | .q0 => .q32 | _ => .q25
  | .q20, y => match y with | .q1 => .q24 | _ => .q23
  | .q21, y => match y with | .q0 => .q33 | _ => .q23
  | .q22, y => match y with | .q0 => .q25 | .q1 => .q23 | .q2 => .q23 | .q3 => .q23 | .q4 => .q23 | .q5 => .q23 | _ => .q34
  | .q23, _ => .q34
  | .q24, y => match y with | .q0 => .q23 | .q1 => .q23 | .q2 => .q23 | .q3 => .q23 | .q4 => .q23 | .q5 => .q23 | _ => .q34
  | .q25, y => match y with | .q0 => .q23 | _ => .q34
  | .q26, y => match y with | .q0 => .q17 | .q1 => .q23 | .q2 => .q23 | .q3 => .q23 | .q4 => .q23 | .q5 => .q23 | _ => .q34
  | .q27, _ => .q25
  | .q28, y => match y with | .q0 => .q30 | .q1 => .q23 | .q2 => .q23 | .q3 => .q23 | .q4 => .q23 | .q5 => .q23 | _ => .q34
  | .q29, y => match y with | .q0 => .q24 | .q1 => .q23 | .q2 => .q23 | .q3 => .q23 | .q4 => .q23 | .q5 => .q23 | _ => .q34
  | .q30, y => match y with | .q0 => .q29 | .q1 => .q23 | .q2 => .q23 | .q3 => .q23 | .q4 => .q23 | .q5 => .q23 | _ => .q34
  | .q31, y => match y with | .q0 => .q10 | .q1 => .q23 | .q2 => .q23 | .q3 => .q23 | .q4 => .q23 | .q5 => .q23 | _ => .q34
  | .q32, y => match y with | .q0 => .q24 | .q1 => .q23 | _ => .q34
  | .q33, y => match y with | .q1 => .q23 | _ => .q34
  | .q34, y => match y with | .q0 => .q35 | _ => .q34
  | .q35, y => match y with | .q0 => .q35 | _ => .q34

def checkAll1_State36 (p : State36 → Bool) : Bool :=
  (((((p .q0 && p .q1) && (p .q2 && p .q3)) && ((p .q4 && p .q5) && (p .q6 && (p .q7 && p .q8)))) && (((p .q9 && p .q10) && (p .q11 && p .q12)) && ((p .q13 && p .q14) && (p .q15 && (p .q16 && p .q17))))) && ((((p .q18 && p .q19) && (p .q20 && p .q21)) && ((p .q22 && p .q23) && (p .q24 && (p .q25 && p .q26)))) && (((p .q27 && p .q28) && (p .q29 && p .q30)) && ((p .q31 && p .q32) && (p .q33 && (p .q34 && p .q35))))))

theorem checkAll1_State36_sound (p : State36 → Bool)
    (h : checkAll1_State36 p = true) (x : State36) : p x = true :=
  match x with
  | .q0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .q1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .q2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .q3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .q4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .q5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .q6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .q7 => (and_left (and_right (and_right (and_right (and_left (and_left h))))))
  | .q8 => (and_right (and_right (and_right (and_right (and_left (and_left h))))))
  | .q9 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .q10 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .q11 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .q12 => (and_right (and_right (and_left (and_right (and_left h)))))
  | .q13 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .q14 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .q15 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .q16 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .q17 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .q18 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .q19 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .q20 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .q21 => (and_right (and_right (and_left (and_left (and_right h)))))
  | .q22 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .q23 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .q24 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .q25 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .q26 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .q27 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .q28 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .q29 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .q30 => (and_right (and_right (and_left (and_right (and_right h)))))
  | .q31 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .q32 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .q33 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .q34 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .q35 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_State36 (p : State36 → State36 → Bool) : Bool :=
  checkAll1_State36 (fun x => checkAll1_State36 (fun y => p x y))

theorem checkAll2_State36_sound (p : State36 → State36 → Bool)
    (h : checkAll2_State36 p = true) (x y : State36) : p x y = true :=
  checkAll1_State36_sound _ (checkAll1_State36_sound _ h x) y

private theorem s_row_State36_0 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q0) y) z = delta_State36 (delta_State36 .q0 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_1 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q1) y) z = delta_State36 (delta_State36 .q1 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_2 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q2) y) z = delta_State36 (delta_State36 .q2 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_3 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q3) y) z = delta_State36 (delta_State36 .q3 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_4 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q4) y) z = delta_State36 (delta_State36 .q4 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_5 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q5) y) z = delta_State36 (delta_State36 .q5 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_6 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q6) y) z = delta_State36 (delta_State36 .q6 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_7 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q7) y) z = delta_State36 (delta_State36 .q7 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_8 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q8) y) z = delta_State36 (delta_State36 .q8 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_9 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q9) y) z = delta_State36 (delta_State36 .q9 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_10 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q10) y) z = delta_State36 (delta_State36 .q10 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_11 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q11) y) z = delta_State36 (delta_State36 .q11 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_12 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q12) y) z = delta_State36 (delta_State36 .q12 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_13 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q13) y) z = delta_State36 (delta_State36 .q13 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_14 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q14) y) z = delta_State36 (delta_State36 .q14 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_15 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q15) y) z = delta_State36 (delta_State36 .q15 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_16 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q16) y) z = delta_State36 (delta_State36 .q16 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_17 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q17) y) z = delta_State36 (delta_State36 .q17 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_18 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q18) y) z = delta_State36 (delta_State36 .q18 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_19 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q19) y) z = delta_State36 (delta_State36 .q19 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_20 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q20) y) z = delta_State36 (delta_State36 .q20 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_21 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q21) y) z = delta_State36 (delta_State36 .q21 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_22 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q22) y) z = delta_State36 (delta_State36 .q22 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_23 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q23) y) z = delta_State36 (delta_State36 .q23 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_24 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q24) y) z = delta_State36 (delta_State36 .q24 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_25 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q25) y) z = delta_State36 (delta_State36 .q25 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_26 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q26) y) z = delta_State36 (delta_State36 .q26 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_27 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q27) y) z = delta_State36 (delta_State36 .q27 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_28 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q28) y) z = delta_State36 (delta_State36 .q28 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_29 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q29) y) z = delta_State36 (delta_State36 .q29 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_30 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q30) y) z = delta_State36 (delta_State36 .q30 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_31 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q31) y) z = delta_State36 (delta_State36 .q31 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_32 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q32) y) z = delta_State36 (delta_State36 .q32 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_33 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q33) y) z = delta_State36 (delta_State36 .q33 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_34 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q34) y) z = delta_State36 (delta_State36 .q34 z) (delta_State36 y z))) = true := rfl
private theorem s_row_State36_35 : checkAll2_State36 (fun y z => decide (delta_State36 (delta_State36 (delta_State36 .q0 .q35) y) z = delta_State36 (delta_State36 .q35 z) (delta_State36 y z))) = true := rfl

theorem delta_State36_s_law (x y z : State36) :
    delta_State36 (delta_State36 (delta_State36 .q0 x) y) z =
    delta_State36 (delta_State36 x z) (delta_State36 y z) :=
  match x with
  | .q0 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_0 y z)
  | .q1 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_1 y z)
  | .q2 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_2 y z)
  | .q3 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_3 y z)
  | .q4 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_4 y z)
  | .q5 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_5 y z)
  | .q6 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_6 y z)
  | .q7 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_7 y z)
  | .q8 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_8 y z)
  | .q9 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_9 y z)
  | .q10 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_10 y z)
  | .q11 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_11 y z)
  | .q12 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_12 y z)
  | .q13 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_13 y z)
  | .q14 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_14 y z)
  | .q15 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_15 y z)
  | .q16 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_16 y z)
  | .q17 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_17 y z)
  | .q18 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_18 y z)
  | .q19 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_19 y z)
  | .q20 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_20 y z)
  | .q21 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_21 y z)
  | .q22 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_22 y z)
  | .q23 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_23 y z)
  | .q24 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_24 y z)
  | .q25 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_25 y z)
  | .q26 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_26 y z)
  | .q27 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_27 y z)
  | .q28 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_28 y z)
  | .q29 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_29 y z)
  | .q30 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_30 y z)
  | .q31 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_31 y z)
  | .q32 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_32 y z)
  | .q33 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_33 y z)
  | .q34 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_34 y z)
  | .q35 => of_decide_eq_true (checkAll2_State36_sound _ s_row_State36_35 y z)


def eval36 : Term → State36
  | .s => .q0
  | .var _ => .q0
  | .app a b => delta_State36 (eval36 a) (eval36 b)

theorem eval36_step_invariant {a b : Term} (h : Step a b) : eval36 a = eval36 b := by
  induction h with
  | root x y z => exact delta_State36_s_law (eval36 x) (eval36 y) (eval36 z)
  | left _ ih => simp [eval36, ih]
  | right _ ih => simp [eval36, ih]

theorem eval36_conv_invariant {a b : Term} (h : ConvS a b) : eval36 a = eval36 b := by
  induction h with
  | refl _ => rfl
  | step hs => exact eval36_step_invariant hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem aaa_eval36_ne_aaas : eval36 AAA = .q34 ∧ eval36 (AAA ⋅ S) = .q35 := by
  decide

/-- Resolution of Question 31 of Barendregt, Endrullis, Klop, and Waldmann (2018):
    `AAA` and `AAA ⋅ S` (which both have no HNF, hence equal Böhm tree `⊥` and equal clocked Böhm tree `⊥`)
    are strictly non-convertible in `CL(S)`! -/
theorem aaa_not_conv_aaas : ¬ ConvS AAA (AAA ⋅ S) := by
  intro hconv
  have heq := eval36_conv_invariant hconv
  have ⟨h1, h2⟩ := aaa_eval36_ne_aaas
  rw [h1, h2] at heq
  contradiction

end IntrinsicTheorems

#print axioms IntrinsicTheorems.rs_mono_reduces
#print axioms IntrinsicTheorems.no_dynamic_hnf1
#print axioms IntrinsicTheorems.visser_right_spine_contamination
#print axioms IntrinsicTheorems.evalP_conv_invariant
#print axioms IntrinsicTheorems.zachos_productive_state
#print axioms IntrinsicTheorems.wolfram2_nonproductive_state
#print axioms IntrinsicTheorems.aaa_not_conv_aaas
