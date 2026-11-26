/-!
# Simplified, Automaton-Free Book Proofs of Questions 31 and 7
# (*Dance of the Starlings*, Barendregt, Endrullis, Klop, and Waldmann, 2017)

Completely self-contained in pure Lean 4 (zero external imports, zero automata,
zero finite multiplication tables, zero `sorry`, zero `Classical.choice`, zero `native_decide`).

## What This File Proves

1. **Shared 3-Constructor Invariant `Heavy` (`H`) and `InU` (`H · H · H`):**
   - `H := A | S · H | H · H` (where `A = S S S`), and `U := { p ⋅ q ⋅ r | p, q, r ∈ H }`.
   - `U` is closed under ALL single-step reductions `Step`, avoids every head normal form
     (`spineLen t ≥ 3`), and every term in `U` has a redex (hence is non-SN and has no HNF).

2. **Question 31 (Strengthened to an Infinite Family — Zero 36-State Table!):**
   - Using `U` (`¬ HasHNF AAA`), right-child persistence (`rightIsApp`), trailing-`S` freeze,
     and Takahashi's 40-line Church–Rosser theorem for `CL(S)`:
     *For every term `m` with `¬ HasHNF m` and compound right child (`rightIsApp m = true`),
      the infinitely many terms `m · S^k` (`k ∈ ℕ`) are pairwise non-convertible in `CL(S)`.*
   - In particular, for all `j ≠ k`, `AAA · S^j ≠_S AAA · S^k`, and taking `j = 0, k = 1`:
     **`AAA ≠_S AAAS`** (resolving Question 31 without any finite `S`-algebra table!).

3. **Question 7 (Automaton-Free Infinite Colour-Change Chain — Both Leaf Refinement and Atomic `S → S S` Splits!):**
   - Using the EXACT same `U` invariant (`R(S) = S A S A → (A A)(S A) → (S A)(S A)(S A) ∈ U`),
     `¬ StrongNormalizing (R(S))` takes 3 lines (zero 35-state `A_HN` table!), while
     `StrongNormalizing (R(S S))` is proved directly from its 6-state reduction DAG.
   - Proves BOTH:
     (a) `question_7_infinite_flipflop`: replacing one `S`-leaf at every step alternates
         SN (Green) / non-SN (Red) at EVERY step (`flipTerm (2k)` SN, `flipTerm (2k+1)` non-SN);
     (b) `question_7_atomic_leaf_splits`: even restricting to atomic 1-leaf splits `S → S ⋅ S`
         (`leaves (atomTerm n) = n + 1`), the chain flips Green → Red at `10k + 8 → 10k + 9`
         and Red → Green at `10k + 9 → 10k + 10` infinitely often!
-/

namespace SimplifiedQ31Q7

/-! ## Section 1: Pure-`S` Combinatory Logic (`CL(S)`) -/

inductive Term where
  | s : Term
  | var : Nat → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

infixl:70 " ⋅ " => Term.app

def S : Term := Term.s
def A : Term := S ⋅ S ⋅ S
def AAA : Term := A ⋅ A ⋅ A

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

def spineLen : Term → Nat
  | .app a _ => 1 + spineLen a
  | _ => 0

def leaves : Term → Nat
  | .s => 1
  | .var _ => 1
  | .app a b => leaves a + leaves b

def noVars : Term → Bool
  | .s => true
  | .var _ => false
  | .app a b => noVars a && noVars b

def StrongNormalizing (t : Term) : Prop :=
  Acc (fun b a => Step a b) t

def HasHNF (t : Term) : Prop :=
  ∃ h, Reduces t h ∧ spineLen h ≤ 2

theorem reduces_trans {a b c : Term} (h1 : Reduces a b) (h2 : Reduces b c) : Reduces a c := by
  induction h1 with
  | refl _ => exact h2
  | next hs _ ih => exact Reduces.next hs (ih h2)

theorem reduces_left {a a' b : Term} (h : Reduces a a') : Reduces (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (Step.left hs) ih

theorem reduces_right {a b b' : Term} (h : Reduces b b') : Reduces (a ⋅ b) (a ⋅ b') := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hs _ ih => exact Reduces.next (Step.right hs) ih

/-! ## Section 2: Takahashi's Proof of Church–Rosser (Confluence) for `CL(S)` -/

inductive Par : Term → Term → Prop where
  | refl (t : Term) : Par t t
  | app {a a' b b' : Term} : Par a a' → Par b b' → Par (a ⋅ b) (a' ⋅ b')
  | s_rule {x x' y y' z z' : Term} :
      Par x x' → Par y y' → Par z z' → Par (S ⋅ x ⋅ y ⋅ z) ((x' ⋅ z') ⋅ (y' ⋅ z'))

/-- Complete development: contract all currently visible redexes simultaneously. -/
def cd : Term → Term
  | .app (.app (.app .s x) y) z => (cd x ⋅ cd z) ⋅ (cd y ⋅ cd z)
  | .app a b => cd a ⋅ cd b
  | .s => .s
  | .var n => .var n

private theorem par_s_inv {u : Term} (h : Par S u) : u = S := by
  cases h; rfl

private theorem par_s_app_inv {x u : Term} (h : Par (S ⋅ x) u) :
    ∃ x', u = S ⋅ x' ∧ Par x x' := by
  cases h with
  | refl _ => exact ⟨x, rfl, Par.refl x⟩
  | app ha hb =>
    have hs := par_s_inv ha
    subst hs
    exact ⟨_, rfl, hb⟩

private theorem par_s_app_app_inv {x y u : Term} (h : Par (S ⋅ x ⋅ y) u) :
    ∃ x' y', u = S ⋅ x' ⋅ y' ∧ Par x x' ∧ Par y y' := by
  cases h with
  | refl _ => exact ⟨x, y, rfl, Par.refl x, Par.refl y⟩
  | app ha hb =>
    obtain ⟨x', hax, hx⟩ := par_s_app_inv ha
    subst hax
    exact ⟨x', _, rfl, hx, hb⟩

theorem par_refl_cd (t : Term) : Par t (cd t) := by
  match t with
  | .s => exact Par.refl .s
  | .var n => exact Par.refl (.var n)
  | .app (.app (.app .s x) y) z =>
    exact Par.s_rule (par_refl_cd x) (par_refl_cd y) (par_refl_cd z)
  | .app .s b =>
    exact Par.app (Par.refl .s) (par_refl_cd b)
  | .app (.var n) b =>
    exact Par.app (Par.refl (.var n)) (par_refl_cd b)
  | .app (.app .s x) b =>
    exact Par.app (Par.app (Par.refl .s) (par_refl_cd x)) (par_refl_cd b)
  | .app (.app (.var n) x) b =>
    exact Par.app (Par.app (Par.refl (.var n)) (par_refl_cd x)) (par_refl_cd b)
  | .app (.app (.app (.var n) x) y) z =>
    exact Par.app (par_refl_cd ((.var n ⋅ x) ⋅ y)) (par_refl_cd z)
  | .app (.app (.app (.app a1 a2) x) y) z =>
    exact Par.app (par_refl_cd (((a1 ⋅ a2) ⋅ x) ⋅ y)) (par_refl_cd z)

/-- Takahashi's Triangle Lemma: every parallel reduct `u` of `t` reduces in parallel to `cd t`. -/
theorem par_triangle {t u : Term} (h : Par t u) : Par u (cd t) := by
  match t, u, h with
  | t, _, Par.refl _ => exact par_refl_cd t
  | _, _, Par.s_rule hx hy hz =>
    exact Par.app (Par.app (par_triangle hx) (par_triangle hz))
      (Par.app (par_triangle hy) (par_triangle hz))
  | .app (.app (.app .s x) y) b, _, Par.app ha hb =>
    obtain ⟨x', y', ha', hx, hy⟩ := par_s_app_app_inv ha
    subst ha'
    exact Par.s_rule (par_triangle hx) (par_triangle hy) (par_triangle hb)
  | .app .s b, _, Par.app ha hb => exact Par.app (par_triangle ha) (par_triangle hb)
  | .app (.var _) b, _, Par.app ha hb => exact Par.app (par_triangle ha) (par_triangle hb)
  | .app (.app .s _) b, _, Par.app ha hb => exact Par.app (par_triangle ha) (par_triangle hb)
  | .app (.app (.var _) _) b, _, Par.app ha hb => exact Par.app (par_triangle ha) (par_triangle hb)
  | .app (.app (.app (.var _) _) _) b, _, Par.app ha hb => exact Par.app (par_triangle ha) (par_triangle hb)
  | .app (.app (.app (.app _ _) _) _) b, _, Par.app ha hb => exact Par.app (par_triangle ha) (par_triangle hb)
termination_by sizeOf t

theorem par_diamond {t u v : Term} (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w :=
  ⟨cd t, par_triangle hu, par_triangle hv⟩

theorem step_to_par {a b : Term} (h : Step a b) : Par a b := by
  induction h with
  | root x y z => exact Par.s_rule (Par.refl x) (Par.refl y) (Par.refl z)
  | left _ ih => exact Par.app ih (Par.refl _)
  | right _ ih => exact Par.app (Par.refl _) ih

theorem par_to_reduces {a b : Term} (h : Par a b) : Reduces a b := by
  induction h with
  | refl _ => exact Reduces.refl _
  | app _ _ iha ihb => exact reduces_trans (reduces_left iha) (reduces_right ihb)
  | @s_rule x x' y y' z z' _ _ _ ihx ihy ihz =>
    have h1 : Reduces (S ⋅ x ⋅ y ⋅ z) (S ⋅ x' ⋅ y' ⋅ z') :=
      reduces_trans (reduces_left (reduces_trans (reduces_left (reduces_right ihx)) (reduces_right ihy)))
        (reduces_right ihz)
    exact reduces_trans h1 (Reduces.next (Step.root x' y' z') (Reduces.refl _))

inductive ParStar : Term → Term → Prop where
  | refl (a : Term) : ParStar a a
  | next {a b c : Term} : Par a b → ParStar b c → ParStar a c

private theorem parStar_strip {a b c : Term} (hab : Par a b) (hac : ParStar a c) :
    ∃ d, ParStar b d ∧ Par c d := by
  induction hac generalizing b with
  | refl _ => exact ⟨b, ParStar.refl b, hab⟩
  | next ha1 _ ih =>
    obtain ⟨w, hbw, hw1⟩ := par_diamond hab ha1
    obtain ⟨d, hwd, hcd⟩ := ih hw1
    exact ⟨d, ParStar.next hbw hwd, hcd⟩

private theorem parStar_confluence {a b c : Term} (hab : ParStar a b) (hac : ParStar a c) :
    ∃ d, ParStar b d ∧ ParStar c d := by
  induction hab generalizing c with
  | refl _ => exact ⟨c, hac, ParStar.refl c⟩
  | next ha1 _ ih =>
    obtain ⟨w, h1w, hcw⟩ := parStar_strip ha1 hac
    obtain ⟨d, hbd, hwd⟩ := ih h1w
    exact ⟨d, hbd, ParStar.next hcw hwd⟩

private theorem parStar_to_reduces {a b : Term} (h : ParStar a b) : Reduces a b := by
  induction h with
  | refl _ => exact Reduces.refl _
  | next hp _ ih => exact reduces_trans (par_to_reduces hp) ih

private theorem parStar_trans {a b c : Term} (h1 : ParStar a b) (h2 : ParStar b c) : ParStar a c := by
  induction h1 with
  | refl _ => exact h2
  | next hp _ ih => exact ParStar.next hp (ih h2)

/-- **Church–Rosser Theorem for `CL(S)`**: convertible terms have a common reduct. -/
theorem church_rosser {a b : Term} (h : ConvS a b) : ∃ w, Reduces a w ∧ Reduces b w := by
  have hps : ∃ w, ParStar a w ∧ ParStar b w := by
    induction h with
    | refl a => exact ⟨a, ParStar.refl a, ParStar.refl a⟩
    | step hs => exact ⟨_, ParStar.next (step_to_par hs) (ParStar.refl _), ParStar.refl _⟩
    | symm _ ih =>
      obtain ⟨w, h1, h2⟩ := ih
      exact ⟨w, h2, h1⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨w1, ha1, hb1⟩ := ih1
      obtain ⟨w2, hb2, hc2⟩ := ih2
      obtain ⟨w, hw1, hw2⟩ := parStar_confluence hb1 hb2
      exact ⟨w, parStar_trans ha1 hw1, parStar_trans hc2 hw2⟩
  obtain ⟨w, h1, h2⟩ := hps
  exact ⟨w, parStar_to_reduces h1, parStar_to_reduces h2⟩

/-! ## Section 3: The 3-Constructor `Heavy` Invariant (`H`) and `U = H · H · H` -/

/-- The 3-constructor set `H := A | S · H | H · H` (Waldmann's `QQQ` generator). -/
inductive Heavy : Term → Prop where
  | a : Heavy A
  | s_app {x : Term} : Heavy x → Heavy (S ⋅ x)
  | app {x y : Term} : Heavy x → Heavy y → Heavy (x ⋅ y)

/-- `U := { p ⋅ q ⋅ r | p, q, r ∈ H }`. Every term in `U` is closed, has spine ≥ 3,
    is closed under ALL reductions, has no HNF, and is not strongly normalizing. -/
def InU (t : Term) : Prop :=
  ∃ p q r, Heavy p ∧ Heavy q ∧ Heavy r ∧ t = p ⋅ q ⋅ r

theorem heavy_ne_s {t : Term} (h : Heavy t) : t ≠ S := by
  cases h <;> intro heq <;> cases heq

theorem heavy_s_app_inv {x : Term} (h : Heavy (S ⋅ x)) : Heavy x := by
  cases h with
  | s_app hx => exact hx
  | app hx _ => exact False.elim (heavy_ne_s hx rfl)

theorem heavy_s_app_app_cases {x y : Term} (h : Heavy (S ⋅ x ⋅ y)) :
    (x = S ∧ y = S) ∨ (Heavy x ∧ Heavy y) := by
  cases h with
  | a => exact Or.inl ⟨rfl, rfl⟩
  | app h1 h2 => exact Or.inr ⟨heavy_s_app_inv h1, h2⟩

private theorem step_A_false {t : Term} (h : Step A t) : False := by
  cases h with
  | left hl => cases hl with | left hll => cases hll | right hlr => cases hlr
  | right hr => cases hr

theorem heavy_step {t t' : Term} (ht : Heavy t) (hs : Step t t') : Heavy t' := by
  induction ht generalizing t' with
  | a => exact False.elim (step_A_false hs)
  | s_app hx ih =>
    cases hs with
    | left hl => cases hl
    | right hr => exact Heavy.s_app (ih hr)
  | @app u v hu hv ihu ihv =>
    cases hs with
    | @root x y z =>
      -- Here `u = S ⋅ x ⋅ y` and `v = z`.
      rcases heavy_s_app_app_cases hu with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
      · exact Heavy.app (Heavy.s_app hv) (Heavy.s_app hv)
      · exact Heavy.app (Heavy.app hx hv) (Heavy.app hy hv)
    | left hl => exact Heavy.app (ihu hl) hv
    | right hr => exact Heavy.app hu (ihv hr)

theorem inU_step {t t' : Term} (hu : InU t) (hs : Step t t') : InU t' := by
  obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hu
  cases hs with
  | @root x y z =>
    -- Here `p ⋅ q = S ⋅ x ⋅ y`, so `p = S ⋅ x` and `q = y`, hence `Heavy x`.
    have hx : Heavy x := heavy_s_app_inv hp
    exact ⟨x, r, q ⋅ r, hx, hr, Heavy.app hq hr, rfl⟩
  | left hl =>
    cases hl with
    | @root x y z =>
      -- Here `p = S ⋅ x ⋅ y` and `q = z`.
      rcases heavy_s_app_app_cases hp with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
      · exact ⟨S ⋅ q, S ⋅ q, r, Heavy.s_app hq, Heavy.s_app hq, hr, rfl⟩
      · exact ⟨x ⋅ q, y ⋅ q, r, Heavy.app hx hq, Heavy.app hy hq, hr, rfl⟩
    | left hll => exact ⟨_, q, r, heavy_step hp hll, hq, hr, rfl⟩
    | right hlr => exact ⟨p, _, r, hp, heavy_step hq hlr, hr, rfl⟩
  | right hrr => exact ⟨p, q, _, hp, hq, heavy_step hr hrr, rfl⟩

theorem inU_reduces {t t' : Term} (hu : InU t) (hred : Reduces t t') : InU t' := by
  induction hred with
  | refl _ => exact hu
  | next hs _ ih => exact ih (inU_step hu hs)

theorem heavy_spine_pos {t : Term} (h : Heavy t) : 1 ≤ spineLen t := by
  cases h with
  | a => exact Nat.le_add_left 1 1
  | s_app _ => exact Nat.le_refl 1
  | app _ _ => exact Nat.le_add_right 1 _

theorem inU_spine_ge3 {t : Term} (hu : InU t) : 3 ≤ spineLen t := by
  obtain ⟨p, q, r, hp, _, _, rfl⟩ := hu
  have hp1 : 1 ≤ spineLen p := heavy_spine_pos hp
  change 3 ≤ 1 + (1 + spineLen p)
  omega

/-- Every term in `U` has NO head normal form (`¬ HasHNF t`). -/
theorem inU_not_hasHNF {t : Term} (hu : InU t) : ¬ HasHNF t := by
  rintro ⟨h, hred, hsp⟩
  have hge := inU_spine_ge3 (inU_reduces hu hred)
  omega

theorem heavy_noVars {t : Term} (h : Heavy t) : noVars t = true := by
  induction h with
  | a => rfl
  | s_app _ ih => simp [noVars, S, ih]
  | app _ _ ih1 ih2 => simp [noVars, ih1, ih2]

private theorem closed_spine_ge3_has_step :
    ∀ t : Term, noVars t = true → 3 ≤ spineLen t → ∃ t', Step t t'
  | .s, _, hsp => by simp [spineLen] at hsp
  | .var _, hnv, _ => by cases hnv
  | .app (.app (.app .s x) y) z, _, _ => ⟨(x ⋅ z) ⋅ (y ⋅ z), Step.root x y z⟩
  | .app (.app (.app (.var _) _) _) _, hnv, _ => by simp [noVars] at hnv
  | .app (.app (.app (.app a b) x) y) z, hnv, _ => by
    have hnvL : noVars (((a ⋅ b) ⋅ x) ⋅ y) = true := ((Bool.and_eq_true _ _).mp hnv).1
    have hspL : 3 ≤ spineLen (((a ⋅ b) ⋅ x) ⋅ y) := by simp [spineLen]; omega
    obtain ⟨l', hl'⟩ := closed_spine_ge3_has_step (((a ⋅ b) ⋅ x) ⋅ y) hnvL hspL
    exact ⟨l' ⋅ z, Step.left hl'⟩
  | .app .s _, _, hsp => by simp [spineLen] at hsp
  | .app (.var _) _, _, hsp => by simp [spineLen] at hsp
  | .app (.app .s _) _, _, hsp => by simp [spineLen] at hsp
  | .app (.app (.var _) _) _, _, hsp => by simp [spineLen] at hsp

/-- Every term in `U` is non-strongly-normalizing (`¬ StrongNormalizing t`). -/
theorem inU_not_sn {t : Term} (hu : InU t) : ¬ StrongNormalizing t := by
  intro hsn
  induction hsn with
  | intro u _ ih =>
    obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hu
    have hnv : noVars (p ⋅ q ⋅ r) = true := by
      simp [noVars, heavy_noVars hp, heavy_noVars hq, heavy_noVars hr]
    have hsp : 3 ≤ spineLen (p ⋅ q ⋅ r) := inU_spine_ge3 ⟨p, q, r, hp, hq, hr, rfl⟩
    obtain ⟨u', hst⟩ := closed_spine_ge3_has_step (p ⋅ q ⋅ r) hnv hsp
    exact ih u' hst (inU_step ⟨p, q, r, hp, hq, hr, rfl⟩ hst)

/-! ## Section 4: Book Proof of Question 31 (Infinite Non-Convertible Family `AAA · S^k`) -/

def isApp : Term → Bool
  | .app _ _ => true
  | _ => false

def rightIsApp : Term → Bool
  | .app _ (.app _ _) => true
  | _ => false

def trailingS : Term → Nat
  | .app a .s => 1 + trailingS a
  | _ => 0

def appS (m : Term) : Nat → Term
  | 0 => m
  | k + 1 => appS m k ⋅ S

theorem isApp_step {a b : Term} (ha : isApp a = true) (h : Step a b) : isApp b = true := by
  cases h <;> rfl

/-- **Right-Child Persistence**: once the right child of a term is an application,
    no reduction step can ever turn the right child into `S`. -/
theorem rightIsApp_step {a b : Term} (ha : rightIsApp a = true) (h : Step a b) :
    rightIsApp b = true := by
  cases h with
  | root _ _ _ => rfl
  | @left l l' r _ =>
    cases r with
    | app _ _ => rfl
    | s => cases ha
    | var _ => cases ha
  | @right l r r' hr =>
    have hrapp : isApp r = true := by
      cases r with
      | app _ _ => rfl
      | s => cases ha
      | var _ => cases ha
    have hr' : isApp r' = true := isApp_step hrapp hr
    cases r' with
    | app _ _ => rfl
    | s => cases hr'
    | var _ => cases hr'

theorem rightIsApp_reduces {a b : Term} (ha : rightIsApp a = true) (h : Reduces a b) :
    rightIsApp b = true := by
  induction h with
  | refl _ => exact ha
  | next hs _ ih => exact ih (rightIsApp_step ha hs)

theorem trailingS_eq_zero_of_rightIsApp {t : Term} (h : rightIsApp t = true) : trailingS t = 0 := by
  cases t with
  | app _ r =>
    cases r with
    | app _ _ => rfl
    | s => cases h
    | var _ => cases h
  | _ => cases h

theorem trailingS_appS (m : Term) (hm : rightIsApp m = true) :
    ∀ k, trailingS (appS m k) = k
  | 0 => trailingS_eq_zero_of_rightIsApp hm
  | k + 1 => by
    change 1 + trailingS (appS m k) = k + 1
    rw [trailingS_appS m hm k]
    omega

/-- **Trailing-`S` Freeze**: if `m` has no HNF, then appending `k` copies of `S`
    never triggers a root redex on any of those `k` outer applications. -/
private theorem appS_eq_s_app_app_contra {m x y : Term} (hno : ¬ HasHNF m) :
    ∀ (k : Nat) (m' : Term), Reduces m m' → appS m' k = S ⋅ x ⋅ y → False
  | 0, m', hred, heq => by
    dsimp [appS] at heq
    exact hno ⟨m', hred, by rw [heq]; simp [spineLen, S]⟩
  | 1, m', hred, heq => by
    dsimp [appS] at heq
    injection heq with h1 _
    exact hno ⟨m', hred, by rw [h1]; simp [spineLen, S]⟩
  | 2, m', hred, heq => by
    dsimp [appS] at heq
    injection heq with h1 _
    injection h1 with h2 _
    exact hno ⟨m', hred, by rw [h2]; simp [spineLen, S]⟩
  | k + 3, m', _, heq => by
    dsimp [appS] at heq
    injection heq with h1 _
    injection h1 with h2 _
    cases h2

private theorem reduces_appS {a b : Term} (h : Reduces a b) : ∀ k, Reduces (appS a k) (appS b k)
  | 0 => h
  | k + 1 => reduces_left (reduces_appS h k)

theorem no_hnf_appS_reduces {m : Term} (hno : ¬ HasHNF m) :
    ∀ (k : Nat) (w : Term), Reduces (appS m k) w → ∃ m', Reduces m m' ∧ w = appS m' k
  | 0, w, hred => ⟨w, hred, rfl⟩
  | k + 1, w, hred => by
    suffices ∀ u w, Reduces u w → ∀ m', Reduces m m' → u = appS m' (k + 1) →
        ∃ m'', Reduces m m'' ∧ w = appS m'' (k + 1) by
      exact this (appS m (k + 1)) w hred m (Reduces.refl m) rfl
    intro u w hred'
    induction hred' with
    | refl _ =>
      intro m' hm' hu
      exact ⟨m', hm', hu⟩
    | @next u v w hs _ ih =>
      intro m' hm' hu
      cases hs with
      | @root x y z =>
        dsimp [appS] at hu
        injection hu with hleft _
        exact False.elim (appS_eq_s_app_app_contra hno k m' hm' hleft.symm)
      | @left a a' b hl =>
        dsimp [appS] at hu
        injection hu with hleft hright
        subst hleft; subst hright
        have hmk : Reduces (appS m k) a' :=
          reduces_trans (reduces_appS hm' k) (Reduces.next hl (Reduces.refl a'))
        obtain ⟨m'', hm'', ha'⟩ := no_hnf_appS_reduces hno k a' hmk
        exact ih m'' hm'' (congrArg (· ⋅ S) ha')
      | @right a b b' hr =>
        dsimp [appS] at hu
        injection hu with _ hright
        subst hright
        cases hr

/-- **General Right-Compound Unsolvable Separation Theorem**:
    For ANY term `m` with `¬ HasHNF m` and compound right child (`rightIsApp m = true`),
    all terms `m · S^k` (`k ∈ ℕ`) lie in pairwise distinct `S`-conversion classes! -/
theorem unsolvable_rightApp_infinite_classes {m : Term}
    (hno : ¬ HasHNF m) (hr : rightIsApp m = true) {j k : Nat} (hjk : j ≠ k) :
    ¬ ConvS (appS m j) (appS m k) := by
  intro hconv
  obtain ⟨w, hwj, hwk⟩ := church_rosser hconv
  obtain ⟨m1, hm1, rfl⟩ := no_hnf_appS_reduces hno j w hwj
  obtain ⟨m2, hm2, heq⟩ := no_hnf_appS_reduces hno k (appS m1 j) hwk
  have tj : trailingS (appS m1 j) = j := trailingS_appS m1 (rightIsApp_reduces hr hm1) j
  have tk : trailingS (appS m2 k) = k := trailingS_appS m2 (rightIsApp_reduces hr hm2) k
  rw [heq] at tj
  exact hjk (tj.symm.trans tk)

theorem aaa_not_hasHNF : ¬ HasHNF AAA :=
  inU_not_hasHNF ⟨A, A, A, Heavy.a, Heavy.a, Heavy.a, rfl⟩

/-- **Strengthened Resolution of Question 31 (Barendregt et al., 2017, p. 93)**:
    All terms `AAA · S^k` (`k ∈ ℕ`) are pairwise non-convertible in `CL(S)` —
    proved without any finite `S`-algebra table! -/
theorem question_31_infinite_family {j k : Nat} (hjk : j ≠ k) :
    ¬ ConvS (appS AAA j) (appS AAA k) :=
  unsolvable_rightApp_infinite_classes aaa_not_hasHNF rfl hjk

/-- **Direct Resolution of Question 31**: `AAA ≠_S AAA ⋅ S`. -/
theorem question_31_aaa_ne_aaas : ¬ ConvS AAA (AAA ⋅ S) :=
  question_31_infinite_family (by decide : 0 ≠ 1)

/-! ## Section 5: Automaton-Free Book Proof of Question 7 (Infinite Colour-Change Chain) -/

def R (x : Term) : Term := x ⋅ A ⋅ S ⋅ A

/-- **3-Line Automaton-Free Proof of `¬ StrongNormalizing (R S)`**:
    `R S = S A S A → (A A)(S A) → ((S A)(S A))(S A) ∈ U`! -/
theorem r_s_not_sn : ¬ StrongNormalizing (R S) := by
  intro hsn
  have h1 : Step (R S) ((A ⋅ A) ⋅ (S ⋅ A)) := Step.root A S A
  have h2 : Step ((A ⋅ A) ⋅ (S ⋅ A)) (((S ⋅ A) ⋅ (S ⋅ A)) ⋅ (S ⋅ A)) :=
    Step.left (Step.root S S A)
  have hsn2 : StrongNormalizing (((S ⋅ A) ⋅ (S ⋅ A)) ⋅ (S ⋅ A)) :=
    Acc.inv (Acc.inv hsn h1) h2
  have hu : InU (((S ⋅ A) ⋅ (S ⋅ A)) ⋅ (S ⋅ A)) :=
    ⟨S ⋅ A, S ⋅ A, S ⋅ A, Heavy.s_app Heavy.a, Heavy.s_app Heavy.a, Heavy.s_app Heavy.a, rfl⟩
  exact inU_not_sn hu hsn2

-- Direct 6-state multiway DAG proof of `StrongNormalizing (R (S ⋅ S))` (zero automata):
private def B : Term := S ⋅ S
private def g0 : Term := R B
private def g1 : Term := (B ⋅ (A ⋅ S)) ⋅ A
private def g2 : Term := (S ⋅ A) ⋅ ((A ⋅ S) ⋅ A)
private def g3 : Term := (B ⋅ (B ⋅ B)) ⋅ A
private def g4 : Term := (S ⋅ A) ⋅ ((B ⋅ B) ⋅ A)
private def g5 : Term := (S ⋅ A) ⋅ ((S ⋅ A) ⋅ (B ⋅ A))

private theorem step_B_f {t : Term} (h : Step B t) : False := by
  cases h with | left hl => cases hl | right hr => cases hr
private theorem step_SA_f {t : Term} (h : Step (S ⋅ A) t) : False := by
  cases h with | left hl => cases hl | right hr => exact step_A_false hr
private theorem step_BA_f {t : Term} (h : Step (B ⋅ A) t) : False := by
  cases h with | left hl => exact step_B_f hl | right hr => exact step_A_false hr
private theorem step_BB_f {t : Term} (h : Step (B ⋅ B) t) : False := by
  cases h with | left hl => exact step_B_f hl | right hr => exact step_B_f hr

private theorem g5_sn : StrongNormalizing g5 :=
  Acc.intro g5 fun _ hw => False.elim <| by
    cases hw with
    | left hl => exact step_SA_f hl
    | right hr => cases hr with | left hrl => exact step_SA_f hrl | right hrr => exact step_BA_f hrr

private theorem g4_sn : StrongNormalizing g4 :=
  Acc.intro g4 fun _ hw => by
    cases hw with
    | left hl => exact False.elim (step_SA_f hl)
    | right hr =>
      cases hr with
      | root _ _ _ => exact g5_sn
      | left hrl => exact False.elim (step_BB_f hrl)
      | right hrr => exact False.elim (step_A_false hrr)

private theorem g3_sn : StrongNormalizing g3 :=
  Acc.intro g3 fun _ hw => by
    cases hw with
    | root _ _ _ => exact g4_sn
    | left hl =>
      cases hl with
      | left hll => exact False.elim (step_B_f hll)
      | right hlr => exact False.elim (step_BB_f hlr)
    | right hr => exact False.elim (step_A_false hr)

private theorem g2_sn : StrongNormalizing g2 :=
  Acc.intro g2 fun _ hw => by
    cases hw with
    | left hl => exact False.elim (step_SA_f hl)
    | right hr =>
      cases hr with
      | left hrl =>
        cases hrl with
        | root _ _ _ => exact g4_sn
        | left hrll => exact False.elim (step_A_false hrll)
        | right hrlr => cases hrlr
      | right hrr => exact False.elim (step_A_false hrr)

private theorem g1_sn : StrongNormalizing g1 :=
  Acc.intro g1 fun _ hw => by
    cases hw with
    | root _ _ _ => exact g2_sn
    | left hl =>
      cases hl with
      | left hll => exact False.elim (step_B_f hll)
      | right hlr =>
        cases hlr with
        | root _ _ _ => exact g3_sn
        | left hlrl => exact False.elim (step_A_false hlrl)
        | right hlrr => cases hlrr
    | right hr => exact False.elim (step_A_false hr)

theorem r_ss_sn : StrongNormalizing (R (S ⋅ S)) :=
  Acc.intro g0 fun _ hw => by
    cases hw with
    | left hl =>
      cases hl with
      | root _ _ _ => exact g1_sn
      | left hll => exact False.elim (step_BA_f hll)
      | right hlr => cases hlr
    | right hr => exact False.elim (step_A_false hr)

theorem s_sn : StrongNormalizing S := Acc.intro S (fun _ h => by cases h)

theorem hnf2_sn {u v : Term} (hu : StrongNormalizing u) (hv : StrongNormalizing v) :
    StrongNormalizing (S ⋅ u ⋅ v) := by
  induction hu generalizing v with
  | intro u _ ihu =>
    induction hv with
    | intro v hprev ihv =>
      refine Acc.intro (S ⋅ u ⋅ v) (fun w hw => ?_)
      cases hw with
      | left hl =>
        cases hl with
        | left hll => cases hll
        | right hlr => exact ihu _ hlr (Acc.intro v hprev)
      | right hr => exact ihv _ hr

theorem sn_left {a b : Term} (h : StrongNormalizing (a ⋅ b)) : StrongNormalizing a := by
  generalize hw : a ⋅ b = w at h
  induction h generalizing a b with
  | intro _ _ ih => subst hw; exact Acc.intro a (fun a' ha' => ih (a' ⋅ b) (Step.left ha') rfl)

theorem sn_right {a b : Term} (h : StrongNormalizing (a ⋅ b)) : StrongNormalizing b := by
  generalize hw : a ⋅ b = w at h
  induction h generalizing a b with
  | intro _ _ ih => subst hw; exact Acc.intro b (fun b' hb' => ih (a ⋅ b') (Step.right hb') rfl)

/-- Replacing a single `S`-leaf by any composite closed `S`-term `m`. -/
inductive Refines : Term → Term → Prop where
  | leaf {m : Term} : noVars m = true → m ≠ S → Refines S m
  | left {a a' b : Term} : Refines a a' → Refines (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Refines b b' → Refines (a ⋅ b) (a ⋅ b')

/-- Atomic 1-leaf split: replacing a single `S`-leaf by `S ⋅ S` (adds exactly 1 leaf!). -/
inductive AtomicSplit : Term → Term → Prop where
  | split : AtomicSplit S (S ⋅ S)
  | left {a a' b : Term} : AtomicSplit a a' → AtomicSplit (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : AtomicSplit b b' → AtomicSplit (a ⋅ b) (a ⋅ b')

theorem atomicSplit_leaves {a b : Term} (h : AtomicSplit a b) : leaves b = leaves a + 1 := by
  induction h with
  | split => rfl
  | left _ ih => simp [leaves, ih]; omega
  | right _ ih => simp [leaves, ih]; omega

def flipChain : Nat → Term → Term
  | 0, tail => tail
  | k + 1, tail => S ⋅ R (S ⋅ S) ⋅ flipChain k tail

def flipTerm (n : Nat) : Term :=
  if n % 2 = 0 then flipChain (n / 2) S else flipChain (n / 2) (S ⋅ R S ⋅ S)

private theorem flipChain_snoc (k : Nat) :
    flipChain (k + 1) S = flipChain k (S ⋅ R (S ⋅ S) ⋅ S) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (S ⋅ R (S ⋅ S) ⋅ ·) ih

private theorem flipChain_refines (k : Nat) {t1 t2 : Term} (hr : Refines t1 t2) :
    Refines (flipChain k t1) (flipChain k t2) := by
  induction k with
  | zero => exact hr
  | succ k ih => exact Refines.right ih

private theorem flipChain_atomic (k : Nat) {t1 t2 : Term} (hr : AtomicSplit t1 t2) :
    AtomicSplit (flipChain k t1) (flipChain k t2) := by
  induction k with
  | zero => exact hr
  | succ k ih => exact AtomicSplit.right ih

private theorem flipChain_sn (k : Nat) {tail : Term} (ht : StrongNormalizing tail) :
    StrongNormalizing (flipChain k tail) := by
  induction k with
  | zero => exact ht
  | succ k ih => exact hnf2_sn r_ss_sn ih

private theorem flipChain_not_sn (k : Nat) {tail : Term} (ht : ¬ StrongNormalizing tail) :
    ¬ StrongNormalizing (flipChain k tail) := by
  induction k with
  | zero => exact ht
  | succ k ih => exact fun hsn => ih (sn_right hsn)

private theorem flipChain_noVars (k : Nat) {tail : Term} (ht : noVars tail = true) :
    noVars (flipChain k tail) = true := by
  induction k with
  | zero => exact ht
  | succ k ih => simp [flipChain, noVars, R, A, S, ih]

private theorem nat_even_or_odd (n : Nat) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inl ⟨k + 1, by omega⟩

/-- **Automaton-Free Solution to Question 7 (Single-Leaf Refinement Alternation)**:
    Starts at `S`, refines one `S`-leaf at every step, and strictly alternates
    SN (`2k`, Green) and non-SN (`2k + 1`, Red) forever! -/
theorem question_7_infinite_flipflop :
    flipTerm 0 = S ∧
    (∀ n, noVars (flipTerm n) = true) ∧
    (∀ n, Refines (flipTerm n) (flipTerm (n + 1))) ∧
    (∀ k, StrongNormalizing (flipTerm (2 * k))) ∧
    (∀ k, ¬ StrongNormalizing (flipTerm (2 * k + 1))) := by
  have heven : ∀ k, flipTerm (2 * k) = flipChain k S := fun k => by
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k) / 2 = k := by omega
    simp [flipTerm, h1, h2]
  have hodd : ∀ k, flipTerm (2 * k + 1) = flipChain k (S ⋅ R S ⋅ S) := fun k => by
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    simp [flipTerm, h1, h2]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases nat_even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [heven]; exact flipChain_noVars k rfl
    · rw [hodd]; exact flipChain_noVars k rfl
  · intro n
    rcases nat_even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [heven, hodd]
      exact flipChain_refines k (Refines.leaf rfl (fun h => by cases h))
    · have hnext : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [hodd, hnext, heven, flipChain_snoc k]
      exact flipChain_refines k
        (Refines.left (Refines.right (Refines.left (Refines.left (Refines.left
          (Refines.leaf rfl (fun h => by cases h)))))))
  · intro k
    rw [heven]
    exact flipChain_sn k s_sn
  · intro k
    rw [hodd]
    exact flipChain_not_sn k (fun hsn => r_s_not_sn (sn_right (sn_left hsn)))

/-- 10-step atomic `S → S ⋅ S` bridge from `S` through `S ⋅ R S ⋅ S` (step 9, Red!)
    to `S ⋅ R (S ⋅ S) ⋅ S` (step 10, Green!). -/
def atomPhase : Nat → Term
  | 0 => S
  | 1 => S ⋅ S
  | 2 => S ⋅ S ⋅ S
  | 3 => S ⋅ (S ⋅ S) ⋅ S
  | 4 => S ⋅ (S ⋅ S ⋅ S) ⋅ S
  | 5 => S ⋅ (S ⋅ S ⋅ S ⋅ S) ⋅ S
  | 6 => S ⋅ (S ⋅ S ⋅ S ⋅ (S ⋅ S)) ⋅ S
  | 7 => S ⋅ (S ⋅ S ⋅ S ⋅ A) ⋅ S
  | 8 => S ⋅ (S ⋅ (S ⋅ S) ⋅ S ⋅ A) ⋅ S
  | _ => S ⋅ R S ⋅ S

def atomTerm (n : Nat) : Term :=
  flipChain (n / 10) (atomPhase (n % 10))

private theorem atomPhase_step (r : Nat) (hr : r < 9) :
    AtomicSplit (atomPhase r) (atomPhase (r + 1)) := by
  match r with
  | 0 => exact AtomicSplit.split
  | 1 => exact AtomicSplit.left AtomicSplit.split
  | 2 => exact AtomicSplit.left (AtomicSplit.right AtomicSplit.split)
  | 3 => exact AtomicSplit.left (AtomicSplit.right (AtomicSplit.left AtomicSplit.split))
  | 4 => exact AtomicSplit.left (AtomicSplit.right (AtomicSplit.left (AtomicSplit.left AtomicSplit.split)))
  | 5 => exact AtomicSplit.left (AtomicSplit.right (AtomicSplit.right AtomicSplit.split))
  | 6 => exact AtomicSplit.left (AtomicSplit.right (AtomicSplit.right (AtomicSplit.left AtomicSplit.split)))
  | 7 => exact AtomicSplit.left (AtomicSplit.right (AtomicSplit.left (AtomicSplit.left (AtomicSplit.right AtomicSplit.split))))
  | 8 => exact AtomicSplit.left (AtomicSplit.right (AtomicSplit.left (AtomicSplit.left (AtomicSplit.right (AtomicSplit.left AtomicSplit.split)))))

private theorem nf_is_sn {t : Term} (h : ∀ u, ¬ Step t u) : StrongNormalizing t :=
  Acc.intro t (fun u hu => False.elim (h u hu))

private theorem nf_s_app {x : Term} (hx : ∀ u, ¬ Step x u) : ∀ u, ¬ Step (S ⋅ x) u := by
  intro u hu
  cases hu with
  | left hl => cases hl
  | right hr => exact hx _ hr

private theorem nf_s_app_app {x y : Term} (hx : ∀ u, ¬ Step x u) (hy : ∀ u, ¬ Step y u) :
    ∀ u, ¬ Step (S ⋅ x ⋅ y) u := by
  intro u hu
  cases hu with
  | left hl => exact nf_s_app hx _ hl
  | right hr => exact hy _ hr

private theorem nf_A_app_sn {x : Term} (hx : ∀ u, ¬ Step x u) : StrongNormalizing (A ⋅ x) := by
  refine Acc.intro (A ⋅ x) (fun w hw => ?_)
  cases hw with
  | root _ _ _ =>
    exact nf_is_sn (nf_s_app_app hx (nf_s_app hx))
  | left hl => exact False.elim (step_A_false hl)
  | right hr => exact False.elim (hx _ hr)

-- Direct 4-state linear chain proof of `StrongNormalizing (S ⋅ B ⋅ S ⋅ A)`:
private theorem p3_nf : ∀ u, ¬ Step ((S ⋅ (S ⋅ A)) ⋅ ((S ⋅ (S ⋅ A)) ⋅ (S ⋅ (S ⋅ A)))) u :=
  have h1 : ∀ u, ¬ Step (S ⋅ (S ⋅ A)) u := nf_s_app (nf_s_app @step_A_false)
  nf_s_app_app (nf_s_app @step_A_false) (nf_s_app_app (nf_s_app @step_A_false) h1)

private theorem p2_sn : StrongNormalizing ((S ⋅ (S ⋅ A)) ⋅ (A ⋅ (S ⋅ A))) :=
  Acc.intro _ fun _ hw => by
    cases hw with
    | left hl => exact False.elim (nf_s_app (nf_s_app @step_A_false) _ hl)
    | right hr =>
      cases hr with
      | root _ _ _ => exact nf_is_sn p3_nf
      | left hrl => exact False.elim (step_A_false hrl)
      | right hrr => exact False.elim (step_SA_f hrr)

private theorem p1_sn : StrongNormalizing ((B ⋅ A) ⋅ (S ⋅ A)) :=
  Acc.intro _ fun _ hw => by
    cases hw with
    | root _ _ _ => exact p2_sn
    | left hl => exact False.elim (step_BA_f hl)
    | right hr => exact False.elim (step_SA_f hr)

private theorem p0_sn : StrongNormalizing (S ⋅ B ⋅ S ⋅ A) :=
  Acc.intro _ fun _ hw => by
    cases hw with
    | root _ _ _ => exact p1_sn
    | left hl =>
      cases hl with
      | left hll =>
        cases hll with
        | left hlll => cases hlll
        | right hllr => exact False.elim (step_B_f hllr)
      | right hlr => cases hlr
    | right hr => exact False.elim (step_A_false hr)

private theorem atomPhase_sn (r : Nat) (hr : r < 9) : StrongNormalizing (atomPhase r) := by
  have hs_nf : ∀ u, ¬ Step S u := fun _ h => by cases h
  match r with
  | 0 => exact s_sn
  | 1 => exact nf_is_sn @step_B_f
  | 2 => exact nf_is_sn @step_A_false
  | 3 => exact hnf2_sn (nf_is_sn @step_B_f) s_sn
  | 4 => exact hnf2_sn (nf_is_sn @step_A_false) s_sn
  | 5 => exact hnf2_sn (nf_A_app_sn hs_nf) s_sn
  | 6 => exact hnf2_sn (nf_A_app_sn @step_B_f) s_sn
  | 7 => exact hnf2_sn (nf_A_app_sn @step_A_false) s_sn
  | 8 => exact hnf2_sn p0_sn s_sn

/-- **Strongest Form of Question 7 (Exact Colour Pattern Under Atomic 1-Leaf Splits `S → S ⋅ S`)**:
    Starts at `S`, replaces ONE leaf `S` by `S ⋅ S` at every single step
    (`leaves (atomTerm n) = n + 1`), and satisfies the EXACT characterization
    `StrongNormalizing (atomTerm n) ↔ n % 10 ≠ 9` (9 Green, 1 Red, 9 Green, 1 Red, ...)! -/
theorem question_7_atomic_leaf_splits :
    atomTerm 0 = S ∧
    (∀ n, AtomicSplit (atomTerm n) (atomTerm (n + 1))) ∧
    (∀ n, leaves (atomTerm n) = n + 1) ∧
    (∀ n, StrongNormalizing (atomTerm n) ↔ n % 10 ≠ 9) := by
  have hatom : ∀ n, AtomicSplit (atomTerm n) (atomTerm (n + 1)) := by
    intro n
    by_cases h9 : n % 10 < 9
    · have hd : (n + 1) / 10 = n / 10 := by omega
      have hm : (n + 1) % 10 = n % 10 + 1 := by omega
      simp only [atomTerm, hd, hm]
      exact flipChain_atomic (n / 10) (atomPhase_step (n % 10) h9)
    · have hm9 : n % 10 = 9 := by omega
      have hd : (n + 1) / 10 = n / 10 + 1 := by omega
      have hm0 : (n + 1) % 10 = 0 := by omega
      simp only [atomTerm, hm9, hd, hm0, atomPhase, flipChain_snoc]
      exact flipChain_atomic (n / 10)
        (AtomicSplit.left (AtomicSplit.right (AtomicSplit.left (AtomicSplit.left (AtomicSplit.left
          AtomicSplit.split)))))
  refine ⟨rfl, hatom, ?_, ?_⟩
  · intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [atomicSplit_leaves (hatom n), ih]
  · intro n
    constructor
    · intro hsn h9
      simp only [atomTerm, h9, atomPhase] at hsn
      exact flipChain_not_sn (n / 10) (fun h => r_s_not_sn (sn_right (sn_left h))) hsn
    · intro hne
      have hlt : n % 10 < 9 := by omega
      exact flipChain_sn (n / 10) (atomPhase_sn (n % 10) hlt)

end SimplifiedQ31Q7

#print axioms SimplifiedQ31Q7.church_rosser
#print axioms SimplifiedQ31Q7.question_31_infinite_family
#print axioms SimplifiedQ31Q7.question_31_aaa_ne_aaas
#print axioms SimplifiedQ31Q7.question_7_infinite_flipflop
#print axioms SimplifiedQ31Q7.question_7_atomic_leaf_splits
