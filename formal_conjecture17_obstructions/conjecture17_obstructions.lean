import formal_top_termination.top_termination

/-!
# Structural Obstructions and Sharp Impossibility Theorems for Conjecture 17 (*Dance of the Starlings*, 2017, p. 89)

**Conjecture 17** (Barendregt, Endrullis, Klop, and Waldmann, 2017, *Dance of the Starlings*, Section 5.4,
Definition 11(iii) & Conjecture 17, pp. 86, 89):
> *"There are no open spiralling S-terms at all."*
> That is, for no pure-`S` term `M` (possibly containing variables), 1-hole pure-`S` context `C[□]`,
> and substitution `σ : Nat → Term` does `M →_S^+ C[M^σ]` hold.

100% constructive Lean 4.33.1 formalization (`zero sorry`, `zero Classical.choice`, `zero native_decide`)
of six sharp families of structural obstructions and impossibility theorems:

1. **Non-Normalization & Universal Substitution Projection (`open_spiral_not_sn`,
   `open_spiral_subst_not_sn`, `open_spiral_closeTerm_not_sn`)**
2. **Complete Absence of Open Cycles `M →^+ M^σ` & Minimal Counterexample Root/Head Structure
   (`no_open_cycle`, `minimal_open_spiral_has_root_and_s_head`)**
3. **The Right-Spine Orbit Obstruction Theorem (`no_open_spiral_bounded_rs`,
   `waldmann_no_spiral_theorem_14`, `no_open_spiral_zero_rs_subst`, `no_open_spiral_s_tailed_subst`,
   `one_var_open_spiral_forces_right_tail_ext`)**
4. **Variable-Multiplicity & Right-Tail Depth Coupling (`rightTail_step_inv`,
   `step_rs_maxRS_coupling`, `no_open_spiral_left_only_vars`,
   `no_one_var_nonduplicating_varfree_ctx`)**
5. **Universal Short-Loop Impossibility for All Terms (`no_one_step_open_spiral`,
   `no_two_step_open_spiral`)**
6. **Contrarian Parametric Near-Miss in Pure `CL(S)` (`waldmann_open_parametric_near_miss`)**
-/

namespace Conjecture17Obstructions

open FormalTopTermination

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false

/-! ## 0. Constructive Closure, Contexts, Iterated Substitution, and Subterms -/

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

/-- Constructive refutation of any `Nat`-indexed chain in an `Acc` relation (`zero Classical.choice`). -/
theorem acc_no_infinite_chain {α : Type} {R : α → α → Prop} :
    ∀ x, Acc R x → ∀ (f : Nat → α), f 0 = x → (∀ n, R (f (n + 1)) (f n)) → False := by
  intro x hacc
  induction hacc with
  | intro x _ ih =>
    intro f h0 hstep
    have h1 : R (f 1) x := h0 ▸ hstep 0
    exact ih (f 1) h1 (fun n => f (n + 1)) rfl (fun n => hstep (n + 1))

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

/-- 1-hole pure-`S` contexts `C[□]`. -/
inductive Ctx where
  | hole : Ctx
  | left : Ctx → Term → Ctx
  | right : Term → Ctx → Ctx
  deriving DecidableEq, Repr

def plugCtx : Ctx → Term → Term
  | .hole, t => t
  | .left c r, t => plugCtx c t ⋅ r
  | .right l c, t => l ⋅ plugCtx c t

def substCtx (τ : Nat → Term) : Ctx → Ctx
  | .hole => .hole
  | .left c r => .left (substCtx τ c) (subst τ r)
  | .right l c => .right (subst τ l) (substCtx τ c)

theorem subst_plugCtx (τ : Nat → Term) (c : Ctx) (t : Term) :
    subst τ (plugCtx c t) = plugCtx (substCtx τ c) (subst τ t) := by
  induction c with
  | hole => rfl
  | left _ _ ih => simp only [plugCtx, substCtx, subst, ih]
  | right _ _ ih => simp only [plugCtx, substCtx, subst, ih]

/-- Iterated substitution `σ^n` (`iterSubst σ 0 = var`, `iterSubst σ (n+1) v = (σ v)^{σ^n}`). -/
def iterSubst (σ : Nat → Term) : Nat → Nat → Term
  | 0, v => .var v
  | n + 1, v => subst (iterSubst σ n) (σ v)

theorem subst_var_id (t : Term) : subst Term.var t = t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [subst, iha, ihb]

theorem subst_iterSubst (σ : Nat → Term) (n : Nat) (t : Term) :
    subst (iterSubst σ n) (subst σ t) = subst (iterSubst σ (n + 1)) t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [subst, iha, ihb]

/-- Definition 11(iii) of Barendregt et al. (2017, p. 86): Open spiralling reduction `m →_S^+ C[m^σ]`. -/
def OpenSpirals (m : Term) (c : Ctx) (σ : Nat → Term) : Prop :=
  StepPlus m (plugCtx c (subst σ m))

def IsOpenSpiralling (m : Term) : Prop :=
  ∃ c σ, OpenSpirals m c σ

def StrongNormalizing (t : Term) : Prop :=
  Acc (fun b a => Step a b) t

def hasVar (v : Nat) : Term → Bool
  | .s => false
  | .var k => decide (k = v)
  | .app a b => hasVar v a || hasVar v b

/-- Syntactic subterm relation `Subterm u t` (`∃ c, t = plugCtx c u`). -/
inductive Subterm (u : Term) : Term → Prop where
  | refl : Subterm u u
  | left {a b : Term} : Subterm u a → Subterm u (a ⋅ b)
  | right {a b : Term} : Subterm u b → Subterm u (a ⋅ b)

theorem subterm_iff_plugCtx {u t : Term} : Subterm u t ↔ ∃ c, t = plugCtx c u := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨.hole, rfl⟩
    | @left a b _ ih =>
      obtain ⟨c, rfl⟩ := ih
      exact ⟨.left c b, rfl⟩
    | @right a b _ ih =>
      obtain ⟨c, rfl⟩ := ih
      exact ⟨.right a c, rfl⟩
  · rintro ⟨c, rfl⟩
    induction c with
    | hole => exact .refl
    | left _ _ ih => exact .left ih
    | right _ _ ih => exact .right ih

theorem subterm_trans {u v w : Term} (h1 : Subterm u v) (h2 : Subterm v w) : Subterm u w := by
  induction h2 with
  | refl => exact h1
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem leaves_pos : ∀ t : Term, 1 ≤ leaves t
  | .s => Nat.le_refl 1
  | .var _ => Nat.le_refl 1
  | .app a b => Nat.le_trans (leaves_pos a) (Nat.le_add_right _ _)

theorem leaves_le_subst (σ : Nat → Term) : ∀ t : Term, leaves t ≤ leaves (subst σ t)
  | .s => Nat.le_refl 1
  | .var v => leaves_pos (σ v)
  | .app a b => Nat.add_le_add (leaves_le_subst σ a) (leaves_le_subst σ b)

theorem subterm_leaves_le {u t : Term} (h : Subterm u t) : leaves u ≤ leaves t := by
  induction h with
  | refl => exact Nat.le_refl _
  | left _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)
  | right _ ih => exact Nat.le_trans ih (Nat.le_add_left _ _)

theorem hasVar_subterm {v : Nat} {u t : Term} (hsub : Subterm u t) (hv : hasVar v u = true) :
    hasVar v t = true := by
  induction hsub with
  | refl => exact hv
  | left _ ih => simp only [hasVar, ih, Bool.true_or]
  | right _ ih => simp only [hasVar, ih, Bool.or_true]

theorem hasVar_subst_of_mem {v w : Nat} {t : Term} {τ : Nat → Term}
    (hv : hasVar v t = true) (hw : hasVar w (τ v) = true) :
    hasVar w (subst τ t) = true := by
  induction t with
  | s => cases hv
  | var k =>
    have hk : k = v := of_decide_eq_true hv
    subst hk
    exact hw
  | app a b iha ihb =>
    rcases (Bool.or_eq_true _ _).mp hv with ha | hb
    · simp only [subst, hasVar, iha ha, Bool.true_or]
    · simp only [subst, hasVar, ihb hb, Bool.or_true]

theorem hasVar_of_hasVar_subst {w : Nat} {t : Term} {τ : Nat → Term}
    (hw : hasVar w (subst τ t) = true) :
    ∃ v, hasVar v t = true ∧ hasVar w (τ v) = true := by
  induction t with
  | s => cases hw
  | var k => exact ⟨k, decide_eq_true rfl, hw⟩
  | app a b iha ihb =>
    rcases (Bool.or_eq_true _ _).mp hw with ha | hb
    · obtain ⟨v, hv, hτ⟩ := iha ha
      exact ⟨v, by simp only [hasVar, hv, Bool.true_or], hτ⟩
    · obtain ⟨v, hv, hτ⟩ := ihb hb
      exact ⟨v, by simp only [hasVar, hv, Bool.or_true], hτ⟩

theorem step_hasVar_subset {v : Nat} {a b : Term} (hs : Step a b) (hb : hasVar v b = true) :
    hasVar v a = true := by
  induction hs with
  | root x y z =>
    simp only [S, hasVar, Bool.false_or] at hb ⊢
    rcases (Bool.or_eq_true _ _).mp hb with hxz | hyz
    · rcases (Bool.or_eq_true _ _).mp hxz with hx | hz
      · simp only [hx, Bool.true_or]
      · simp only [hz, Bool.or_true]
    · rcases (Bool.or_eq_true _ _).mp hyz with hy | hz
      · simp only [hy, Bool.or_true, Bool.true_or]
      · simp only [hz, Bool.or_true]
  | left _ ih =>
    rcases (Bool.or_eq_true _ _).mp hb with hl | hr
    · simp only [hasVar, ih hl, Bool.true_or]
    · simp only [hasVar, hr, Bool.or_true]
  | right _ ih =>
    rcases (Bool.or_eq_true _ _).mp hb with hl | hr
    · simp only [hasVar, hl, Bool.true_or]
    · simp only [hasVar, ih hr, Bool.or_true]

theorem reduces_hasVar_subset {v : Nat} {a b : Term} (hr : Reduces a b) (hb : hasVar v b = true) :
    hasVar v a = true := by
  induction hr with
  | refl _ => exact hb
  | next hs _ ih => exact step_hasVar_subset hs (ih hb)

/-! ## 1. Substitution Preservation & Non-Normalization Obstructions -/

theorem step_subst (τ : Nat → Term) {a b : Term} (h : Step a b) :
    Step (subst τ a) (subst τ b) := by
  induction h with
  | root x y z => exact Step.root (subst τ x) (subst τ y) (subst τ z)
  | left _ ih => exact Step.left ih
  | right _ ih => exact Step.right ih

theorem rootStep_subst (τ : Nat → Term) {a b : Term} (h : RootStep a b) :
    RootStep (subst τ a) (subst τ b) := by
  cases h with
  | mk x y z => exact RootStep.mk (subst τ x) (subst τ y) (subst τ z)

theorem stepPlus_subst (τ : Nat → Term) {a b : Term} (h : StepPlus a b) :
    StepPlus (subst τ a) (subst τ b) := by
  induction h with
  | single hs => exact .single (step_subst τ hs)
  | head hs _ ih => exact .head (step_subst τ hs) ih

theorem reduces_subst (τ : Nat → Term) {a b : Term} (h : Reduces a b) :
    Reduces (subst τ a) (subst τ b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (step_subst τ hs) ih

theorem hasRootReduces_subst (τ : Nat → Term) {a b : Term} (h : HasRootReduces a b) :
    HasRootReduces (subst τ a) (subst τ b) := by
  obtain ⟨m1, m2, h1, hr, h2⟩ := h
  exact ⟨subst τ m1, subst τ m2, reduces_subst τ h1, rootStep_subst τ hr, reduces_subst τ h2⟩

theorem step_plugCtx (c : Ctx) {a b : Term} (h : Step a b) :
    Step (plugCtx c a) (plugCtx c b) := by
  induction c with
  | hole => exact h
  | left _ _ ih => exact Step.left ih
  | right _ _ ih => exact Step.right ih

theorem stepPlus_plugCtx (c : Ctx) {a b : Term} (h : StepPlus a b) :
    StepPlus (plugCtx c a) (plugCtx c b) := by
  induction h with
  | single hs => exact .single (step_plugCtx c hs)
  | head hs _ ih => exact .head (step_plugCtx c hs) ih

theorem stepPlus_to_transGen {a b : Term} (h : StepPlus a b) : TransGen Step a b := by
  induction h with
  | single hs => exact .single hs
  | head hs _ ih => exact transGen_head hs ih

def spiralIterTerm (c : Ctx) (σ : Nat → Term) (m : Term) : Nat → Term
  | 0 => m
  | n + 1 => plugCtx c (subst σ (spiralIterTerm c σ m n))

theorem spiralIterTerm_stepPlus {m : Term} {c : Ctx} {σ : Nat → Term}
    (h : OpenSpirals m c σ) :
    ∀ n, StepPlus (spiralIterTerm c σ m n) (spiralIterTerm c σ m (n + 1))
  | 0 => h
  | n + 1 => stepPlus_plugCtx c (stepPlus_subst σ (spiralIterTerm_stepPlus h n))

/-- **Obstruction 1A (`open_spiral_not_sn`)**:
    No strongly normalizing pure-`S` term can open-spiral. -/
theorem open_spiral_not_sn {m : Term} {c : Ctx} {σ : Nat → Term}
    (h : OpenSpirals m c σ) : ¬ StrongNormalizing m := by
  intro hsn
  have hacc : Acc (fun b a => TransGen Step a b) m := acc_transGen hsn
  exact acc_no_infinite_chain m hacc (spiralIterTerm c σ m) rfl
    (fun n => stepPlus_to_transGen (spiralIterTerm_stepPlus h n))

theorem sn_pullback_subst (τ : Nat → Term) {u : Term} (hsn : StrongNormalizing u) :
    ∀ m, subst τ m = u → StrongNormalizing m := by
  induction hsn with
  | intro u _ ih =>
    intro m heq
    subst heq
    exact Acc.intro m (fun m' hs => ih (subst τ m') (step_subst τ hs) m' rfl)

/-- **Obstruction 1B (`open_spiral_subst_not_sn`)**:
    If `m` open-spirals (`m →^+ C[m^σ]`), then **every** substitution instance `subst τ m`
    (for every `τ : Nat → Term`, open or closed) is non-normalizing. -/
theorem open_spiral_subst_not_sn {m : Term} {c : Ctx} {σ : Nat → Term}
    (h : OpenSpirals m c σ) (τ : Nat → Term) : ¬ StrongNormalizing (subst τ m) :=
  fun hsn => open_spiral_not_sn h (sn_pullback_subst τ hsn m rfl)

/-- **Obstruction 1C (`open_spiral_closeTerm_not_sn`)**:
    If `m` open-spirals, its closed projection `closeTerm m = m[v := S]` is non-normalizing. -/
theorem open_spiral_closeTerm_not_sn {m : Term} {c : Ctx} {σ : Nat → Term}
    (h : OpenSpirals m c σ) : ¬ StrongNormalizing (closeTerm m) :=
  open_spiral_subst_not_sn h (fun _ => S)

/-! ## 2. Complete Absence of Open Cycles (`C = □`) & Minimal Counterexample Structure -/

theorem stepPlus_to_reduces {a b : Term} (h : StepPlus a b) : Reduces a b := by
  induction h with
  | single hs => exact .next hs (.refl _)
  | head hs _ ih => exact .next hs ih

theorem stepPlus_of_step_reduces {a b c : Term} (h1 : Step a b) (h2 : Reduces b c) :
    StepPlus a c := by
  induction h2 generalizing a with
  | refl _ => exact .single h1
  | next hs _ ih => exact .head h1 (ih hs)

theorem reduces_eq_or_stepPlus {a b : Term} (h : Reduces a b) : a = b ∨ StepPlus a b := by
  cases h with
  | refl _ => exact Or.inl rfl
  | next hs hrest => exact Or.inr (stepPlus_of_step_reduces hs hrest)

theorem stepPlus_split_root_or_nonRoot {a b : Term} (h : StepPlus a b) :
    HasRootReduces a b ∨ ∃ m1, NonRootStep a m1 ∧ NonRootReduces m1 b := by
  cases h with
  | single hs =>
    rcases step_iff_root_or_nonRoot.mp hs with hr | hnr
    · exact Or.inl ⟨a, b, .refl a, hr, .refl b⟩
    · exact Or.inr ⟨b, hnr, .refl b⟩
  | @head _ m1 _ hs hrest =>
    have hred_rest := stepPlus_to_reduces hrest
    rcases step_iff_root_or_nonRoot.mp hs with hr | hnr
    · exact Or.inl ⟨a, m1, .refl a, hr, hred_rest⟩
    · rcases reduces_split_first_root hred_rest with hnr_rest | ⟨c0, hrel, hc0b⟩
      · exact Or.inr ⟨m1, hnr, hnr_rest⟩
      · obtain ⟨m2, hnr2, hr2⟩ := hrel
        exact Or.inl ⟨m2, c0, .next (nonRootStep_to_step hnr) (nonRootReduces_to_reduces hnr2), hr2, hc0b⟩

private theorem open_cycle_extract_root (σ : Nat → Term) :
    ∀ m : Term, StepPlus m (subst σ m) → ∃ u, HasRootReduces u (subst σ u)
  | .s, h => by cases h with | single hs => cases hs | head hs _ => cases hs
  | .var _, h => by cases h with | single hs => cases hs | head hs _ => cases hs
  | .app a b, h => by
    rcases stepPlus_split_root_or_nonRoot h with hroot | ⟨m1, hnr1, hnr_rest⟩
    · exact ⟨a ⋅ b, hroot⟩
    · cases hnr1 with
      | @left _ a1 _ ha1 =>
        obtain ⟨a', b', heq, hra, _⟩ := nonRootReduces_app_inv hnr_rest a1 b rfl
        injection heq with ha' _
        subst ha'
        exact open_cycle_extract_root σ a (stepPlus_of_step_reduces ha1 hra)
      | @right _ _ b1 hb1 =>
        obtain ⟨a', b', heq, _, hrb⟩ := nonRootReduces_app_inv hnr_rest a b1 rfl
        injection heq with _ hb'
        subst hb'
        exact open_cycle_extract_root σ b (stepPlus_of_step_reduces hb1 hrb)

/-- **Theorem 2A (`no_open_cycle`, Complete Resolution of Open Cycles `C = □`)**:
    No pure-`S` term `m` (with any number of variables) and no substitution `σ` can ever satisfy
    `m →_S^+ m^σ`! Proved by extracting a subterm with a root step and iterating `σ^n` against
    Waldmann's Top-Termination Theorem (`hasRootReduces_wellFounded`). -/
theorem no_open_cycle (m : Term) (σ : Nat → Term) : ¬ StepPlus m (subst σ m) := by
  intro hcyc
  obtain ⟨u, hroot⟩ := open_cycle_extract_root σ m hcyc
  have hchain : ∀ n, HasRootReduces (subst (iterSubst σ n) u) (subst (iterSubst σ (n + 1)) u) := by
    intro n
    have hstep := hasRootReduces_subst (iterSubst σ n) hroot
    rw [subst_iterSubst σ n u] at hstep
    exact hstep
  have h0 : subst (iterSubst σ 0) u = u := subst_var_id u
  have hacc := hasRootReduces_wellFounded u
  exact acc_no_infinite_chain u hacc (fun n => subst (iterSubst σ n) u) h0 hchain

theorem no_open_spiral_hole (m : Term) (σ : Nat → Term) : ¬ OpenSpirals m .hole σ :=
  no_open_cycle m σ

theorem headLeaf_step_var {v : Nat} {a b : Term} (hs : Step a b) (hh : headLeaf a = .var v) :
    headLeaf b = .var v := by
  induction hs with
  | root _ _ _ => cases hh
  | left _ ihl => exact ihl hh
  | right _ _ => exact hh

theorem headLeaf_var_no_rootStep {v : Nat} {a b : Term} :
    Reduces a b → headLeaf a = .var v → headLeaf b = .var v ∧ (∀ x y z, b ≠ S ⋅ x ⋅ y ⋅ z) := by
  intro hred
  induction hred with
  | refl a0 =>
    intro hh
    refine ⟨hh, fun x y z heq => ?_⟩
    subst heq
    cases hh
  | next hs _ ih =>
    intro hh
    exact ih (headLeaf_step_var hs hh)

/-- **Theorem 2B (`minimal_open_spiral_has_root_and_s_head`)**:
    If `m` is a leaf-minimal open spiralling term (`∀ u, leaves u < leaves m → ¬ IsOpenSpiralling u`),
    then `m →^+ C[m^σ]` **must** perform at least one root contraction (`HasRootReduces`) and
    must have `headLeaf m = .s` (never a variable at its head!). -/
theorem minimal_open_spiral_has_root_and_s_head {m : Term} {c : Ctx} {σ : Nat → Term}
    (h : OpenSpirals m c σ)
    (hmin : ∀ u, leaves u < leaves m → ¬ IsOpenSpiralling u) :
    HasRootReduces m (plugCtx c (subst σ m)) ∧ headLeaf m = .s := by
  have hroot : HasRootReduces m (plugCtx c (subst σ m)) := by
    rcases stepPlus_split_root_or_nonRoot h with hr | ⟨m1, hnr1, hnr_rest⟩
    · exact hr
    · exfalso
      cases m with
      | s => cases hnr1
      | var _ => cases hnr1
      | app a b =>
        have hnr_all : NonRootReduces (a ⋅ b) (plugCtx c (subst σ (a ⋅ b))) := .next hnr1 hnr_rest
        obtain ⟨a', b', heq, hra, hrb⟩ := nonRootReduces_app_inv hnr_all a b rfl
        have hsub : Subterm (subst σ a ⋅ subst σ b) (a' ⋅ b') := by
          rw [← heq]
          exact subterm_iff_plugCtx.mpr ⟨c, rfl⟩
        cases hsub with
        | refl =>
          have hcyc : StepPlus (a ⋅ b) (subst σ (a ⋅ b)) := by
            unfold OpenSpirals at h
            rw [heq] at h
            exact h
          exact no_open_cycle (a ⋅ b) σ hcyc
        | left hsub_a =>
          have hsub_a' : Subterm (subst σ a) a' := subterm_trans (.left .refl) hsub_a
          obtain ⟨ca, hca⟩ := subterm_iff_plugCtx.mp hsub_a'
          rcases reduces_eq_or_stepPlus hra with rfl | hpa
          · have hle := subterm_leaves_le hsub_a
            have hge := Nat.add_le_add (leaves_le_subst σ a) (leaves_le_subst σ b)
            have hbp := leaves_pos b
            simp only [leaves] at hle
            omega
          · have hosp : OpenSpirals a ca σ := by unfold OpenSpirals; rw [← hca]; exact hpa
            exact hmin a (by have := leaves_pos b; change leaves a < leaves a + leaves b; omega) ⟨ca, σ, hosp⟩
        | right hsub_b =>
          have hsub_b' : Subterm (subst σ b) b' := subterm_trans (.right .refl) hsub_b
          obtain ⟨cb, hcb⟩ := subterm_iff_plugCtx.mp hsub_b'
          rcases reduces_eq_or_stepPlus hrb with rfl | hpb
          · have hle := subterm_leaves_le hsub_b
            have hge := Nat.add_le_add (leaves_le_subst σ a) (leaves_le_subst σ b)
            have hap := leaves_pos a
            simp only [leaves] at hle
            omega
          · have hosp : OpenSpirals b cb σ := by unfold OpenSpirals; rw [← hcb]; exact hpb
            exact hmin b (by have := leaves_pos a; change leaves b < leaves a + leaves b; omega) ⟨cb, σ, hosp⟩
  refine ⟨hroot, ?_⟩
  have hleaf : ∀ t, headLeaf t = .s ∨ ∃ k, headLeaf t = .var k := by
    intro t
    induction t with
    | s => exact Or.inl rfl
    | var k => exact Or.inr ⟨k, rfl⟩
    | app a _ iha => exact iha
  rcases hleaf m with hs0 | ⟨v, hh⟩
  · exact hs0
  · exfalso
    obtain ⟨m1, m2, hm1, hr, _⟩ := hroot
    cases hr with
    | mk x y z => exact (headLeaf_var_no_rootStep hm1 hh).2 x y z rfl

private theorem s_head_spine_le_2_preserved {a b : Term} (hs : Step a b)
    (hh : headLeaf a = .s) (hsp : spineLen a ≤ 2) :
    headLeaf b = .s ∧ spineLen b ≤ 2 := by
  cases a with
  | s => cases hs
  | var _ => cases hh
  | app l r =>
    cases l with
    | s =>
      cases hs with
      | left hl => cases hl
      | right _ => exact ⟨rfl, Nat.le_trans (Nat.le_succ 1) (Nat.le_refl 2)⟩
    | var _ => cases hh
    | app l0 r0 =>
      cases l0 with
      | s =>
        cases hs with
        | left hl =>
          cases hl with
          | left hll => cases hll
          | right _ => exact ⟨rfl, Nat.le_refl 2⟩
        | right _ => exact ⟨rfl, Nat.le_refl 2⟩
      | var _ => cases hh
      | app _ _ =>
        exfalso
        change 1 + (1 + (1 + spineLen _)) ≤ 2 at hsp
        omega

/-- **Theorem 2C (`minimal_open_spiral_spineLen_ge_3`)**:
    Every leaf-minimal open spiralling pure-`S` term `m` satisfies `headLeaf m = .s` AND
    **`3 ≤ spineLen m`** (`m` must have at least 3 arguments along its left spine: `S ⋅ a_1 ⋅ a_2 ⋅ a_3 ⋅ ...`)! -/
theorem minimal_open_spiral_spineLen_ge_3 {m : Term} {c : Ctx} {σ : Nat → Term}
    (h : OpenSpirals m c σ)
    (hmin : ∀ u, leaves u < leaves m → ¬ IsOpenSpiralling u) :
    headLeaf m = .s ∧ 3 ≤ spineLen m := by
  obtain ⟨hroot, hh⟩ := minimal_open_spiral_has_root_and_s_head h hmin
  refine ⟨hh, ?_⟩
  by_cases hge : 3 ≤ spineLen m
  · exact hge
  · exfalso
    have hle2 : spineLen m ≤ 2 := by omega
    obtain ⟨m1, m2, hm1, hr, _⟩ := hroot
    have preserved : ∀ {u v : Term}, Reduces u v → headLeaf u = .s → spineLen u ≤ 2 →
        headLeaf v = .s ∧ spineLen v ≤ 2 := by
      intro u v hred
      induction hred with
      | refl _ => intro h1 h2; exact ⟨h1, h2⟩
      | next hs _ ih =>
        intro h1 h2
        obtain ⟨h1', h2'⟩ := s_head_spine_le_2_preserved hs h1 h2
        exact ih h1' h2'
    obtain ⟨_, hsp_m1⟩ := preserved hm1 hh hle2
    cases hr with
    | mk x y z =>
      change 1 + (1 + (1 + 0)) ≤ 2 at hsp_m1
      omega

/-! ## 3. The Right-Spine Orbit Obstruction Theorem (`no_open_spiral_bounded_rs`) -/

/-- Rightmost leaf of `t` (`none` if the right spine ends in `S`, `some v` if it ends in `.var v`). -/
def rightTail : Term → Option Nat
  | .s => none
  | .var v => some v
  | .app _ b => rightTail b

theorem rightTail_hasVar : ∀ {t : Term} {v : Nat}, rightTail t = some v → hasVar v t = true
  | .s, _, h => by cases h
  | .var k, v, h => by
    injection h with hk
    subst hk
    exact decide_eq_true rfl
  | .app a b, v, h => by
    have ih := rightTail_hasVar (t := b) h
    simp only [hasVar, ih, Bool.or_true]

theorem rs_subst (τ : Nat → Term) : ∀ t : Term,
    rs (subst τ t) = match rightTail t with
      | none => rs t
      | some v => rs t + rs (τ v)
  | .s => rfl
  | .var v => by simp only [subst, rightTail, rs, Nat.zero_add]
  | .app a b => by
    simp only [subst, rightTail, rs, rs_subst τ b]
    cases rightTail b with
    | none => rfl
    | some v => exact (Nat.add_assoc 1 (rs b) (rs (τ v))).symm

theorem rightTail_subst (τ : Nat → Term) : ∀ t : Term,
    rightTail (subst τ t) = match rightTail t with
      | none => none
      | some v => rightTail (τ v)
  | .s => rfl
  | .var _ => rfl
  | .app _ b => rightTail_subst τ b

/-- Right-spine length `ρ(t) = 1 + rs(t)`. -/
def rho (t : Term) : Nat := 1 + rs t

theorem rho_mono_step {a b : Term} (h : Step a b) : rho a ≤ rho b := by
  induction h with
  | root x y z =>
    change 1 + (1 + rs z) ≤ 1 + (1 + (1 + rs z))
    omega
  | left _ _ => exact Nat.le_refl _
  | right _ ih => change 1 + rho _ ≤ 1 + rho _; omega

/-- Right-spine-labeled pure-`S` terms for Waldmann's bounded-label RPO. -/
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
      omega
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

private theorem plugCtx_to_stepRB (B : Nat) (c : Ctx) (m : Term) :
    ReflTransGen StepRB (flipLabels B (toLTerm (plugCtx c m))) (flipLabels B (toLTerm m)) := by
  induction c with
  | hole => exact .refl _
  | left c' r ih =>
    exact .head (.subL (B - rho r) (flipLabels B (toLTerm (plugCtx c' m))) (flipLabels B (toLTerm r))) ih
  | right l c' ih =>
    exact .head (.subR (B - rho (plugCtx c' m)) (flipLabels B (toLTerm l)) (flipLabels B (toLTerm (plugCtx c' m)))) ih

private theorem rho_subst_le {τ : Nat → Term} {R : Nat} {b : Term}
    (hR : ∀ v, hasVar v b = true → rs (τ v) ≤ R) :
    rho (subst τ b) ≤ rho b + R := by
  unfold rho
  rw [rs_subst τ b]
  cases ht : rightTail b with
  | none => dsimp only; omega
  | some v =>
    have hv := hR v (rightTail_hasVar ht)
    change 1 + (rs b + rs (τ v)) ≤ (1 + rs b) + R
    rw [← Nat.add_assoc 1 (rs b) (rs (τ v))]
    exact Nat.add_le_add_left hv (1 + rs b)

private theorem maxLabel_subst_le {τ : Nat → Term} {R L : Nat} :
    ∀ t : Term,
      (∀ v, hasVar v t = true → rs (τ v) ≤ R ∧ maxLabel (toLTerm (τ v)) ≤ L) →
      maxLabel (toLTerm (subst τ t)) ≤ Nat.max (maxLabel (toLTerm t) + R) L
  | .s, _ => Nat.zero_le _
  | .var v, h => Nat.le_trans (h v (decide_eq_true rfl)).2 (Nat.le_max_right _ _)
  | .app a b, h => by
    have ha_h : ∀ v, hasVar v a = true → rs (τ v) ≤ R ∧ maxLabel (toLTerm (τ v)) ≤ L :=
      fun v hv => h v (by simp only [hasVar, hv, Bool.true_or])
    have hb_h : ∀ v, hasVar v b = true → rs (τ v) ≤ R ∧ maxLabel (toLTerm (τ v)) ≤ L :=
      fun v hv => h v (by simp only [hasVar, hv, Bool.or_true])
    have iha := maxLabel_subst_le a ha_h
    have ihb := maxLabel_subst_le b hb_h
    have hrho := rho_subst_le (fun v hv => (hb_h v hv).1)
    simp only [subst, toLTerm, maxLabel, Nat.max_le]
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.le_trans hrho (Nat.le_trans (Nat.add_le_add_right (Nat.le_max_left _ _) R) (Nat.le_max_left _ _))
    · refine Nat.le_trans iha (Nat.max_le.mpr ⟨?_, Nat.le_max_right _ _⟩)
      exact Nat.le_trans (Nat.add_le_add_right (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) R) (Nat.le_max_left _ _)
    · refine Nat.le_trans ihb (Nat.max_le.mpr ⟨?_, Nat.le_max_right _ _⟩)
      exact Nat.le_trans (Nat.add_le_add_right (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) R) (Nat.le_max_left _ _)

private theorem stepPlus_subst_stepRB {a b : Term} (h : StepPlus a b) :
    ∃ B0, ∀ (τ : Nat → Term) (R L B : Nat),
      (∀ v, hasVar v a = true → rs (τ v) ≤ R ∧ maxLabel (toLTerm (τ v)) ≤ L) →
      Nat.max (B0 + R) L ≤ B →
      TransGen StepRB (flipLabels B (toLTerm (subst τ a))) (flipLabels B (toLTerm (subst τ b))) := by
  induction h with
  | @single a b hs =>
    refine ⟨Nat.max (maxLabel (toLTerm a)) (maxLabel (toLTerm b)), fun τ R L B hτ hB => ?_⟩
    have hτ_b : ∀ v, hasVar v b = true → rs (τ v) ≤ R ∧ maxLabel (toLTerm (τ v)) ≤ L :=
      fun v hv => hτ v (step_hasVar_subset hs hv)
    have ha1 := maxLabel_subst_le a hτ
    have hb1 := maxLabel_subst_le b hτ_b
    have haB : maxLabel (toLTerm (subst τ a)) ≤ B := by
      refine Nat.le_trans ha1 (Nat.le_trans ?_ hB)
      exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.add_le_add_right (Nat.le_max_left _ _) R) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    have hbB : maxLabel (toLTerm (subst τ b)) ≤ B := by
      refine Nat.le_trans hb1 (Nat.le_trans ?_ hB)
      exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.add_le_add_right (Nat.le_max_right _ _) R) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    exact step_to_stepRB B (step_subst τ hs) haB hbB
  | @head a m1 b hs _ ih =>
    obtain ⟨B1, hB1⟩ := ih
    refine ⟨Nat.max (maxLabel (toLTerm a)) (Nat.max (maxLabel (toLTerm m1)) B1), fun τ R L B hτ hB => ?_⟩
    have hτ_m1 : ∀ v, hasVar v m1 = true → rs (τ v) ≤ R ∧ maxLabel (toLTerm (τ v)) ≤ L :=
      fun v hv => hτ v (step_hasVar_subset hs hv)
    have haB : maxLabel (toLTerm (subst τ a)) ≤ B := by
      refine Nat.le_trans (maxLabel_subst_le a hτ) (Nat.le_trans ?_ hB)
      exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.add_le_add_right (Nat.le_max_left _ _) R) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    have hm1B : maxLabel (toLTerm (subst τ m1)) ≤ B := by
      refine Nat.le_trans (maxLabel_subst_le m1 hτ_m1) (Nat.le_trans ?_ hB)
      have hm1_le : maxLabel (toLTerm m1) ≤ Nat.max (maxLabel (toLTerm a)) (Nat.max (maxLabel (toLTerm m1)) B1) :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.add_le_add_right hm1_le R) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    have hB1_le : Nat.max (B1 + R) L ≤ B := by
      refine Nat.le_trans ?_ hB
      have hle : B1 ≤ Nat.max (maxLabel (toLTerm a)) (Nat.max (maxLabel (toLTerm m1)) B1) :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.add_le_add_right hle R) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    exact transGen_trans (step_to_stepRB B (step_subst τ hs) haB hm1B) (hB1 τ R L B hτ_m1 hB1_le)

private def maxSigmaLabel (σ : Nat → Term) : Term → Nat
  | .s => 0
  | .var v => maxLabel (toLTerm (σ v))
  | .app a b => Nat.max (maxSigmaLabel σ a) (maxSigmaLabel σ b)

private theorem maxSigmaLabel_bound (σ : Nat → Term) :
    ∀ {t : Term} {v : Nat}, hasVar v t = true → maxLabel (toLTerm (σ v)) ≤ maxSigmaLabel σ t
  | .s, _, hv => by cases hv
  | .var k, v, hv => by
    have hk : k = v := of_decide_eq_true hv
    subst hk
    exact Nat.le_refl _
  | .app a b, v, hv => by
    rcases (Bool.or_eq_true _ _).mp hv with ha | hb
    · exact Nat.le_trans (maxSigmaLabel_bound σ ha) (Nat.le_max_left _ _)
    · exact Nat.le_trans (maxSigmaLabel_bound σ hb) (Nat.le_max_right _ _)

private theorem open_spiral_vars_closed {m : Term} {c : Ctx} {σ : Nat → Term}
    (h : OpenSpirals m c σ) {v w : Nat}
    (hv : hasVar v m = true) (hw : hasVar w (σ v) = true) :
    hasVar w m = true := by
  have hsub : Subterm (subst σ m) (plugCtx c (subst σ m)) := subterm_iff_plugCtx.mpr ⟨c, rfl⟩
  have hw1 : hasVar w (subst σ m) = true := hasVar_subst_of_mem hv hw
  have hw2 : hasVar w (plugCtx c (subst σ m)) = true := hasVar_subterm hsub hw1
  exact reduces_hasVar_subset (stepPlus_to_reduces h) hw2

private theorem iterSubst_vars_and_maxLabel {m : Term} {c : Ctx} {σ : Nat → Term}
    (h : OpenSpirals m c σ) {R : Nat}
    (hR : ∀ n w, hasVar w m = true → rs (iterSubst σ n w) ≤ R) :
    ∀ n v, hasVar v m = true →
      (∀ w, hasVar w (iterSubst σ n v) = true → hasVar w m = true) ∧
      maxLabel (toLTerm (iterSubst σ n v)) ≤ maxSigmaLabel σ m + R
  | 0, v, hv => ⟨fun w hw => by
      have hk : v = w := of_decide_eq_true hw
      subst hk; exact hv,
    Nat.zero_le _⟩
  | n + 1, v, hv => by
    refine ⟨fun w hw => ?_, ?_⟩
    · obtain ⟨u, hu, hwu⟩ := hasVar_of_hasVar_subst hw
      have hum : hasVar u m = true := open_spiral_vars_closed h hv hu
      exact (iterSubst_vars_and_maxLabel h hR n u hum).1 w hwu
    · change maxLabel (toLTerm (subst (iterSubst σ n) (σ v))) ≤ maxSigmaLabel σ m + R
      have hbound := maxLabel_subst_le (σ v) (R := R) (L := maxSigmaLabel σ m + R) (fun u hu => by
        have hum := open_spiral_vars_closed h hv hu
        exact ⟨hR n u hum, (iterSubst_vars_and_maxLabel h hR n u hum).2⟩)
      refine Nat.le_trans hbound (Nat.max_le.mpr ⟨?_, Nat.le_refl _⟩)
      exact Nat.add_le_add_right (maxSigmaLabel_bound σ hv) R

/-- **Theorem 3A (`no_open_spiral_bounded_rs`, The Right-Spine Orbit Obstruction Theorem)**:
    If there exists a uniform bound `R` such that `rs (iterSubst σ n v) ≤ R` for all `n : Nat`
    and all variables `v` occurring in `m`, then **`m` cannot open-spiral via `(c, σ)`**! -/
theorem no_open_spiral_bounded_rs {m : Term} {c : Ctx} {σ : Nat → Term} {R : Nat}
    (hR : ∀ n v, hasVar v m = true → rs (iterSubst σ n v) ≤ R) :
    ¬ OpenSpirals m c σ := by
  intro h
  obtain ⟨B0, hB0⟩ := stepPlus_subst_stepRB h
  let L := maxSigmaLabel σ m + R
  let B := Nat.max (B0 + R) L
  have hstep_n : ∀ n,
      TransGen StepRB
        (flipLabels B (toLTerm (subst (iterSubst σ n) m)))
        (flipLabels B (toLTerm (subst (iterSubst σ (n + 1)) m))) := by
    intro n
    have hτ : ∀ v, hasVar v m = true → rs (iterSubst σ n v) ≤ R ∧ maxLabel (toLTerm (iterSubst σ n v)) ≤ L :=
      fun v hv => ⟨hR n v hv, (iterSubst_vars_and_maxLabel h hR n v hv).2⟩
    have htr := hB0 (iterSubst σ n) R L B hτ (Nat.le_refl B)
    rw [subst_plugCtx (iterSubst σ n) c (subst σ m), subst_iterSubst σ n m] at htr
    have hctx := plugCtx_to_stepRB B (substCtx (iterSubst σ n) c) (subst (iterSubst σ (n + 1)) m)
    exact transGen_of_transGen_reflTransGen htr hctx
  have hacc := stepRB_acc_plus (flipLabels B (toLTerm (subst (iterSubst σ 0) m)))
  exact acc_no_infinite_chain _ hacc (fun n => flipLabels B (toLTerm (subst (iterSubst σ n) m))) rfl hstep_n

/-- **Corollary 3B (`waldmann_no_spiral_theorem_14`)**:
    Recovering Waldmann's No-Spiral Theorem (`Theorem 14` of Barendregt et al. 2017, p. 88)
    as the `R = 0`, `σ = var` special case of `no_open_spiral_bounded_rs`. -/
theorem waldmann_no_spiral_theorem_14 (m : Term) (c : Ctx) :
    ¬ StepPlus m (plugCtx c m) := by
  intro h
  have iter_id : ∀ n v, iterSubst Term.var n v = .var v := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro v; change subst (iterSubst Term.var n) (.var v) = .var v; exact ih v
  have h0 : OpenSpirals m c Term.var := by
    unfold OpenSpirals
    rw [subst_var_id m]
    exact h
  exact no_open_spiral_bounded_rs (R := 0) (fun n v _ => by rw [iter_id n v]; exact Nat.le_refl 0) h0

/-- **Corollary 3C (`no_open_spiral_zero_rs_subst`)**:
    No substitution `σ` with `rs (σ v) = 0` on `vars(m)` (including all variable renamings,
    permutations, and `S`-erasures `v ↦ S`) can ever witness an open spiral `m →^+ C[m^σ]`. -/
theorem no_open_spiral_zero_rs_subst {m : Term} {c : Ctx} {σ : Nat → Term}
    (h0 : ∀ v, hasVar v m = true → rs (σ v) = 0) :
    ¬ OpenSpirals m c σ := by
  intro h
  have hiter0 : ∀ n v, hasVar v m = true → rs (iterSubst σ n v) = 0 := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro v hv
      change rs (subst (iterSubst σ n) (σ v)) = 0
      rw [rs_subst (iterSubst σ n) (σ v)]
      cases ht : rightTail (σ v) with
      | none => exact h0 v hv
      | some w =>
        dsimp only
        have hwm : hasVar w m = true := open_spiral_vars_closed h hv (rightTail_hasVar ht)
        rw [h0 v hv, ih w hwm]
  exact no_open_spiral_bounded_rs (R := 0) (fun n v hv => Nat.le_of_eq (hiter0 n v hv)) h

private def maxSigmaRS (σ : Nat → Term) : Term → Nat
  | .s => 0
  | .var v => rs (σ v)
  | .app a b => Nat.max (maxSigmaRS σ a) (maxSigmaRS σ b)

private theorem maxSigmaRS_bound (σ : Nat → Term) :
    ∀ {t : Term} {v : Nat}, hasVar v t = true → rs (σ v) ≤ maxSigmaRS σ t
  | .s, _, hv => by cases hv
  | .var k, v, hv => by
    have hk : k = v := of_decide_eq_true hv
    subst hk; exact Nat.le_refl _
  | .app a b, v, hv => by
    rcases (Bool.or_eq_true _ _).mp hv with ha | hb
    · exact Nat.le_trans (maxSigmaRS_bound σ ha) (Nat.le_max_left _ _)
    · exact Nat.le_trans (maxSigmaRS_bound σ hb) (Nat.le_max_right _ _)

/-- **Corollary 3D (`no_open_spiral_s_tailed_subst`)**:
    If for every variable `v` occurring in `m`, `σ v` ends its right spine in `S` (or has `rs (σ v) = 0`),
    i.e., `rightTail (σ v) = none ∨ rs (σ v) = 0` — which includes **all closed substitutions**,
    `x ↦ x ⋅ S`, `x ↦ S ⋅ x ⋅ S`, `x ↦ A`, `x ↦ Z`, etc. — then **`m →^+ C[m^σ]` is impossible**! -/
theorem no_open_spiral_non_extending_subst {m : Term} {c : Ctx} {σ : Nat → Term}
    (h_ne : ∀ v, hasVar v m = true → rightTail (σ v) = none ∨ rs (σ v) = 0) :
    ¬ OpenSpirals m c σ := by
  intro h
  have hbound : ∀ n v, hasVar v m = true → rs (iterSubst σ n v) ≤ maxSigmaRS σ m := by
    intro n
    induction n with
    | zero => intro _ _; exact Nat.zero_le _
    | succ n ih =>
      intro v hv
      change rs (subst (iterSubst σ n) (σ v)) ≤ maxSigmaRS σ m
      rw [rs_subst (iterSubst σ n) (σ v)]
      rcases h_ne v hv with hnone | hzero
      · rw [hnone]
        exact maxSigmaRS_bound σ hv
      · cases ht : rightTail (σ v) with
        | none => exact maxSigmaRS_bound σ hv
        | some w =>
          dsimp only
          have hwm : hasVar w m = true := open_spiral_vars_closed h hv (rightTail_hasVar ht)
          rw [hzero, Nat.zero_add]
          exact ih w hwm
  exact no_open_spiral_bounded_rs hbound h

theorem no_open_spiral_s_tailed_subst {m : Term} {c : Ctx} {σ : Nat → Term}
    (hs : ∀ v, hasVar v m = true → rightTail (σ v) = none) :
    ¬ OpenSpirals m c σ :=
  no_open_spiral_non_extending_subst (fun v hv => Or.inl (hs v hv))

/-- **Corollary 3E (`one_var_open_spiral_forces_right_tail_ext`)**:
    For any pure-`S` term `m` in at most one variable `x` (`∀ v, hasVar v m = true → v = x`),
    any hypothetical open spiral `m →^+ C[m^σ]` **forces**:
    1. `hasVar x m = true` (`m` is genuinely open in `x`),
    2. `rightTail (σ x) = some x` (`σ(x)` ends its right spine in `x`), and
    3. `1 ≤ rs (σ x)` (`σ(x)` strictly extends `x` on the left of its right spine). -/
theorem one_var_open_spiral_forces_right_tail_ext {m : Term} {c : Ctx} {σ : Nat → Term} {x : Nat}
    (hone : ∀ v, hasVar v m = true → v = x)
    (h : OpenSpirals m c σ) :
    hasVar x m = true ∧ rightTail (σ x) = some x ∧ 1 ≤ rs (σ x) := by
  have hxm : hasVar x m = true := by
    cases hxm_b : hasVar x m with
    | true => rfl
    | false =>
      exfalso
      refine no_open_spiral_zero_rs_subst (fun v hv => ?_) h
      have hvx := hone v hv
      subst hvx
      rw [hxm_b] at hv
      cases hv
  have hrs_pos : 1 ≤ rs (σ x) := by
    cases hrs0 : rs (σ x) with
    | zero =>
      exfalso
      refine no_open_spiral_zero_rs_subst (fun v hv => ?_) h
      rw [hone v hv]
      exact hrs0
    | succ k => omega
  have htail : rightTail (σ x) = some x := by
    cases ht : rightTail (σ x) with
    | none =>
      exfalso
      refine no_open_spiral_s_tailed_subst (fun v hv => ?_) h
      rw [hone v hv]
      exact ht
    | some w =>
      have hwm : hasVar w m = true := open_spiral_vars_closed h hxm (rightTail_hasVar ht)
      rw [hone w hwm]
  exact ⟨hxm, htail, hrs_pos⟩

/-! ## 4. Variable Multiplicity & Right-Tail Depth Coupling (`maxRS`, Left-Only Vars, Linear 1-Var) -/

def countVar (x : Nat) : Term → Nat
  | .s => 0
  | .var k => if k = x then 1 else 0
  | .app a b => countVar x a + countVar x b

def countVarCtx (x : Nat) : Ctx → Nat
  | .hole => 0
  | .left c r => countVarCtx x c + countVar x r
  | .right l c => countVar x l + countVarCtx x c

theorem countVar_plugCtx (x : Nat) (c : Ctx) (t : Term) :
    countVar x (plugCtx c t) = countVarCtx x c + countVar x t := by
  induction c with
  | hole => simp only [plugCtx, countVarCtx, Nat.zero_add]
  | left _ r ih => simp only [plugCtx, countVar, countVarCtx, ih]; omega
  | right l _ ih => simp only [plugCtx, countVar, countVarCtx, ih]; omega

theorem countVar_pos_of_hasVar {x : Nat} : ∀ {t : Term}, hasVar x t = true → 1 ≤ countVar x t
  | .s, h => by cases h
  | .var k, h => by
    have hk : k = x := of_decide_eq_true h
    subst hk
    simp only [countVar, ↓reduceIte, Nat.le_refl]
  | .app a b, h => by
    rcases (Bool.or_eq_true _ _).mp h with ha | hb
    · have := countVar_pos_of_hasVar ha; simp only [countVar]; omega
    · have := countVar_pos_of_hasVar hb; simp only [countVar]; omega

theorem countVar_eq_zero_of_hasVar_false {x : Nat} : ∀ {t : Term}, hasVar x t = false → countVar x t = 0
  | .s, _ => rfl
  | .var k, h => by
    have hne : k ≠ x := of_decide_eq_false h
    simp only [countVar, hne, ↓reduceIte]
  | .app a b, h => by
    simp only [hasVar] at h
    cases ha : hasVar x a with
    | true => rw [ha] at h; cases h
    | false =>
      cases hb : hasVar x b with
      | true => rw [ha, hb] at h; cases h
      | false => simp only [countVar, countVar_eq_zero_of_hasVar_false ha, countVar_eq_zero_of_hasVar_false hb]

/-- Maximum right-spine length among all subterms of `t` whose rightmost leaf is `.var x`. -/
def maxRS (x : Nat) : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app a b =>
    max (if rightTail b = some x then 1 + rs b else 0) (max (maxRS x a) (maxRS x b))

theorem maxRS_subterm_le (x : Nat) {u t : Term} (h : Subterm u t) : maxRS x u ≤ maxRS x t := by
  induction h with
  | refl => exact Nat.le_refl _
  | left _ ih => simp only [maxRS]; omega
  | right _ ih => simp only [maxRS]; omega

theorem rs_le_maxRS_of_rightTail {x : Nat} : ∀ {t : Term}, rightTail t = some x → rs t ≤ maxRS x t
  | .s, h => by cases h
  | .var _, _ => Nat.le_refl 0
  | .app a b, h => by
    change 1 + rs b ≤ maxRS x (a ⋅ b)
    have hb : rightTail b = some x := h
    simp only [maxRS, hb, ↓reduceIte]
    omega

/-- **Exact Invariance of `rightTail` (`rightTail_step_inv`)**:
    Pure-`S` reduction preserves the rightmost leaf of every term identically. -/
theorem rightTail_step_inv {a b : Term} (hs : Step a b) : rightTail b = rightTail a := by
  induction hs with
  | root _ _ _ => rfl
  | left _ _ => rfl
  | right _ ih => exact ih

theorem maxRS_zero_step (x : Nat) {a b : Term} (hs : Step a b) (ha : maxRS x a = 0) :
    maxRS x b = 0 := by
  induction hs with
  | root p q r =>
    simp only [S, maxRS] at ha ⊢
    have h_rt : (if rightTail r = some x then 1 + rs r else 0) = 0 := by omega
    have h_p : maxRS x p = 0 := by omega
    have h_q : maxRS x q = 0 := by omega
    have h_r : maxRS x r = 0 := by omega
    have hnot : rightTail r ≠ some x := by
      intro heq; rw [heq] at h_rt; simp at h_rt
    simp only [rightTail, hnot, ↓reduceIte, h_p, h_q, h_r]
    omega
  | left _ ih =>
    simp only [maxRS] at ha ⊢
    have hl : maxRS x _ = 0 := ih (by omega)
    omega
  | @right l r r' hr ih =>
    simp only [maxRS] at ha ⊢
    have hrt_eq : rightTail r' = rightTail r := rightTail_step_inv hr
    rw [hrt_eq]
    have h_rt : (if rightTail r = some x then 1 + rs r else 0) = 0 := by omega
    have hnot : rightTail r ≠ some x := by
      intro heq; rw [heq] at h_rt; simp at h_rt
    have hr0 : maxRS x r' = 0 := ih (by omega)
    simp only [hnot, ↓reduceIte] at ha ⊢
    omega

theorem maxRS_zero_reduces (x : Nat) {a b : Term} (hr : Reduces a b) (ha : maxRS x a = 0) :
    maxRS x b = 0 := by
  induction hr with
  | refl _ => exact ha
  | next hs _ ih => exact ih (maxRS_zero_step x hs ha)

private theorem subterm_sigma_of_hasVar (σ : Nat → Term) :
    ∀ {t : Term} {v : Nat}, hasVar v t = true → Subterm (σ v) (subst σ t)
  | .s, _, hv => by cases hv
  | .var k, v, hv => by
    have hk : k = v := of_decide_eq_true hv
    subst hk; exact .refl
  | .app a b, v, hv => by
    rcases (Bool.or_eq_true _ _).mp hv with ha | hb
    · exact .left (subterm_sigma_of_hasVar σ ha)
    · exact .right (subterm_sigma_of_hasVar σ hb)

/-- **Theorem 4A (`no_open_spiral_left_only_vars`)**:
    For **arbitrary many variables**, if every variable in `m` occurs only in left/function positions
    (`∀ w, maxRS w m = 0`, i.e., `m` contains no subterm of the form `a ⋅ .var w`),
    then **`m` cannot open-spiral for ANY context `c` and ANY substitution `σ`**! -/
theorem no_open_spiral_left_only_vars {m : Term} {c : Ctx} {σ : Nat → Term}
    (hleft : ∀ w, maxRS w m = 0) :
    ¬ OpenSpirals m c σ := by
  intro h
  refine no_open_spiral_non_extending_subst (fun v hv => ?_) h
  cases ht : rightTail (σ v) with
  | none => exact Or.inl rfl
  | some w =>
    refine Or.inr ?_
    have h0_end : maxRS w (plugCtx c (subst σ m)) = 0 :=
      maxRS_zero_reduces w (stepPlus_to_reduces h) (hleft w)
    have hsub_all : Subterm (σ v) (plugCtx c (subst σ m)) :=
      subterm_trans (subterm_sigma_of_hasVar σ hv) (subterm_iff_plugCtx.mpr ⟨c, rfl⟩)
    have hle1 : rs (σ v) ≤ maxRS w (σ v) := rs_le_maxRS_of_rightTail ht
    have hle2 : maxRS w (σ v) ≤ maxRS w (plugCtx c (subst σ m)) := maxRS_subterm_le w hsub_all
    omega

/-- **Theorem 4B (`step_rs_maxRS_coupling`, Master Variable-Multiplicity / Right-Spine Coupling)**:
    Across every pure-`S` step `a →_S b` and every variable `x`:
    1. `countVar x a ≤ countVar x b`,
    2. `rightTail a = some x → rs b + countVar x a ≤ rs a + countVar x b`, and
    3. `maxRS x b + countVar x a ≤ maxRS x a + countVar x b`. -/
theorem step_rs_maxRS_coupling (x : Nat) {a b : Term} (hs : Step a b) :
    countVar x a ≤ countVar x b ∧
    (rightTail a = some x → rs b + countVar x a ≤ rs a + countVar x b) ∧
    maxRS x b + countVar x a ≤ maxRS x a + countVar x b := by
  induction hs with
  | root p q r =>
    have hcv_lhs : countVar x (S ⋅ p ⋅ q ⋅ r) = countVar x p + countVar x q + countVar x r := by
      simp only [S, countVar, Nat.zero_add]
    have hcv_rhs : countVar x ((p ⋅ r) ⋅ (q ⋅ r)) = countVar x p + countVar x r + (countVar x q + countVar x r) := rfl
    refine ⟨by omega, ?_, ?_⟩
    · intro hrt
      have hrt_r : rightTail r = some x := hrt
      have hpos : 1 ≤ countVar x r := countVar_pos_of_hasVar (rightTail_hasVar hrt_r)
      change (1 + (1 + rs r)) + countVar x (S ⋅ p ⋅ q ⋅ r) ≤ (1 + rs r) + countVar x ((p ⋅ r) ⋅ (q ⋅ r))
      omega
    · rw [hcv_lhs, hcv_rhs]
      by_cases hrt_r : rightTail r = some x
      · have hpos : 1 ≤ countVar x r := countVar_pos_of_hasVar (rightTail_hasVar hrt_r)
        simp only [maxRS, S, rightTail, hrt_r, ↓reduceIte, rs]
        omega
      · simp only [maxRS, S, rightTail, hrt_r, ↓reduceIte]
        omega
  | @left l l' r _ ih =>
    obtain ⟨ih1, _, ih3⟩ := ih
    refine ⟨by simp only [countVar]; omega, ?_, ?_⟩
    · intro _
      simp only [rs, countVar]
      omega
    · simp only [maxRS, countVar]
      omega
  | @right l r r' hr ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hrt_eq : rightTail r' = rightTail r := rightTail_step_inv hr
    refine ⟨by simp only [countVar]; omega, ?_, ?_⟩
    · intro hrt
      have h2 := ih2 hrt
      simp only [rs, countVar]
      omega
    · by_cases hrt_r : rightTail r = some x
      · have h2 := ih2 hrt_r
        simp only [maxRS, countVar, hrt_eq, hrt_r, ↓reduceIte]
        omega
      · simp only [maxRS, countVar, hrt_eq, hrt_r, ↓reduceIte]
        omega

theorem reduces_maxRS_countVar_coupling (x : Nat) {a b : Term} (hr : Reduces a b) :
    maxRS x b + countVar x a ≤ maxRS x a + countVar x b := by
  induction hr with
  | refl _ => exact Nat.le_refl _
  | next hs _ ih =>
    have ⟨_, _, h3⟩ := step_rs_maxRS_coupling x hs
    omega

private theorem countVar_one_var_subst {x : Nat} :
    ∀ {t : Term} {σ : Nat → Term},
      (∀ v, hasVar v t = true → v = x) →
      countVar x (subst σ t) = countVar x t * countVar x (σ x)
  | .s, _, _ => by simp only [subst, countVar, Nat.zero_mul]
  | .var k, σ, hone => by
    have hk : k = x := hone k (decide_eq_true rfl)
    subst hk
    simp only [subst, countVar, ↓reduceIte, Nat.one_mul]
  | .app a b, σ, hone => by
    have iha := countVar_one_var_subst (t := a) (σ := σ) (fun v hv => hone v (by simp only [hasVar, hv, Bool.true_or]))
    have ihb := countVar_one_var_subst (t := b) (σ := σ) (fun v hv => hone v (by simp only [hasVar, hv, Bool.or_true]))
    simp only [subst, countVar, iha, ihb, Nat.add_mul]

private theorem maxRS_eq_zero_of_hasVar_false {x : Nat} : ∀ {t : Term}, hasVar x t = false → maxRS x t = 0
  | .s, _ => rfl
  | .var _, _ => rfl
  | .app l r, h => by
    simp only [hasVar] at h
    have hl : hasVar x l = false := by cases h1 : hasVar x l <;> simp_all
    have hr : hasVar x r = false := by cases h1 : hasVar x r <;> simp_all
    have hnot : rightTail r ≠ some x := fun heq => by
      rw [rightTail_hasVar heq] at hr; cases hr
    simp only [maxRS, hnot, ↓reduceIte, maxRS_eq_zero_of_hasVar_false hl, maxRS_eq_zero_of_hasVar_false hr]
    omega

private theorem maxRS_subst_ge_of_rightTail {x : Nat} {σ : Nat → Term}
    (ht : rightTail (σ x) = some x) :
    ∀ {t : Term}, hasVar x t = true → maxRS x t + rs (σ x) ≤ maxRS x (subst σ t)
  | .s, hv => by cases hv
  | .var k, hv => by
    have hk : k = x := of_decide_eq_true hv
    subst hk
    simp only [maxRS, subst, Nat.zero_add]
    exact rs_le_maxRS_of_rightTail ht
  | .app a b, hv => by
    have sub_a : Subterm (subst σ a) (subst σ (a ⋅ b)) := .left .refl
    have sub_b : Subterm (subst σ b) (subst σ (a ⋅ b)) := .right .refl
    have h_root : (if rightTail b = some x then 1 + rs b else 0) + rs (σ x) ≤ maxRS x (subst σ (a ⋅ b)) ∨
        rightTail b ≠ some x := by
      by_cases hrb : rightTail b = some x
      · refine Or.inl ?_
        have hrt_sb : rightTail (subst σ b) = some x := by
          rw [rightTail_subst σ b, hrb]; exact ht
        have hrs_sb : rs (subst σ b) = rs b + rs (σ x) := by
          rw [rs_subst σ b, hrb]
        simp only [hrb, ↓reduceIte]
        have hle : 1 + rs (subst σ b) ≤ maxRS x (subst σ a ⋅ subst σ b) := by
          simp only [maxRS, hrt_sb, ↓reduceIte]; omega
        change _ ≤ maxRS x (subst σ a ⋅ subst σ b)
        omega
      · exact Or.inr hrb
    have ha_case : maxRS x a = 0 ∨ maxRS x a + rs (σ x) ≤ maxRS x (subst σ (a ⋅ b)) := by
      cases hxa : hasVar x a with
      | true => exact Or.inr (Nat.le_trans (maxRS_subst_ge_of_rightTail ht hxa) (maxRS_subterm_le x sub_a))
      | false => exact Or.inl (maxRS_eq_zero_of_hasVar_false hxa)
    have hb_case : maxRS x b = 0 ∨ maxRS x b + rs (σ x) ≤ maxRS x (subst σ (a ⋅ b)) := by
      cases hxb : hasVar x b with
      | true => exact Or.inr (Nat.le_trans (maxRS_subst_ge_of_rightTail ht hxb) (maxRS_subterm_le x sub_b))
      | false => exact Or.inl (maxRS_eq_zero_of_hasVar_false hxb)
    have hrs_le : rs (σ x) ≤ maxRS x (subst σ (a ⋅ b)) := by
      rcases (Bool.or_eq_true _ _).mp hv with hxa | hxb
      · have := maxRS_subst_ge_of_rightTail ht hxa
        have := maxRS_subterm_le x sub_a
        omega
      · have := maxRS_subst_ge_of_rightTail ht hxb
        have := maxRS_subterm_le x sub_b
        omega
    simp only [maxRS]
    rcases h_root with hr1 | hr2
    · rcases ha_case with ha0 | ha1 <;> rcases hb_case with hb0 | hb1 <;> omega
    · simp only [hr2, ↓reduceIte]
      rcases ha_case with ha0 | ha1 <;> rcases hb_case with hb0 | hb1 <;> omega

/-- **Theorem 4C (`no_one_var_nonduplicating_varfree_ctx`)**:
    For **any** 1-variable open pure-`S` term `m(x)` (`∀ v, hasVar v m = true → v = x`),
    **any** non-`x`-duplicating substitution `σ` (`countVar x (σ x) ≤ 1`, including `x ↦ S x`,
    `x ↦ T x = S S x`, `x ↦ A x`, `x ↦ V x`, `x ↦ S`, `x ↦ x`), and **any** `x`-free context `c`
    (`countVarCtx x c = 0`, including all closed contexts and `.hole`),
    **`m(x) →_S^+ C[m(σ(x))]` is impossible**! -/
theorem no_one_var_nonduplicating_varfree_ctx {m : Term} {c : Ctx} {σ : Nat → Term} {x : Nat}
    (hone : ∀ v, hasVar v m = true → v = x)
    (hlin : countVar x (σ x) ≤ 1)
    (hctx : countVarCtx x c = 0) :
    ¬ OpenSpirals m c σ := by
  intro h
  obtain ⟨hxm, htail, hrs_pos⟩ := one_var_open_spiral_forces_right_tail_ext hone h
  have hcoup := reduces_maxRS_countVar_coupling x (stepPlus_to_reduces h)
  have hmax1 : maxRS x m + rs (σ x) ≤ maxRS x (subst σ m) :=
    maxRS_subst_ge_of_rightTail htail hxm
  have hmax2 : maxRS x (subst σ m) ≤ maxRS x (plugCtx c (subst σ m)) :=
    maxRS_subterm_le x (subterm_iff_plugCtx.mpr ⟨c, rfl⟩)
  have hcv_end : countVar x (plugCtx c (subst σ m)) ≤ countVar x m := by
    rw [countVar_plugCtx x c (subst σ m), hctx, Nat.zero_add, countVar_one_var_subst hone]
    exact Nat.le_trans (Nat.mul_le_mul_left (countVar x m) hlin) (Nat.le_of_eq (Nat.mul_one _))
  omega

private theorem countVar_subst_diagonal_le {x : Nat} {σ : Nat → Term} :
    ∀ {t : Term},
      countVar x (σ x) ≤ 1 →
      (∀ u, hasVar u t = true → u ≠ x → hasVar x (σ u) = false) →
      countVar x (subst σ t) ≤ countVar x t
  | .s, _, _ => Nat.le_refl 0
  | .var k, hlin, hdiag => by
    by_cases hkx : k = x
    · subst hkx
      simp only [subst, countVar, ↓reduceIte]
      exact hlin
    · have hx0 : hasVar x (σ k) = false := hdiag k (decide_eq_true rfl) hkx
      simp only [subst, countVar, hkx, ↓reduceIte, countVar_eq_zero_of_hasVar_false hx0, Nat.le_refl]
  | .app a b, hlin, hdiag => by
    have iha := countVar_subst_diagonal_le (t := a) hlin
      (fun u hu hne => hdiag u (by simp only [hasVar, hu, Bool.true_or]) hne)
    have ihb := countVar_subst_diagonal_le (t := b) hlin
      (fun u hu hne => hdiag u (by simp only [hasVar, hu, Bool.or_true]) hne)
    simp only [subst, countVar]
    omega

/-- **Theorem 4D (`no_diagonal_nonduplicating_varfree_ctx`, Multi-Variable Generalization)**:
    For **arbitrary many variables**, if `c` contains none of `m`'s variables
    (`∀ v, hasVar v m = true → countVarCtx v c = 0`) and `σ` is diagonally non-duplicating on
    `vars(m)` (`countVar v (σ v) ≤ 1` and `σ u` does not mention `v` for `u ≠ v` — covering all
    multi-variable counter-increment substitutions `(x_1, ..., x_k) ↦ (F_1 x_1, ..., F_k x_k)` such
    as `(x, y) ↦ (T x, T y)`!), then **`m →_S^+ C[m^σ]` is impossible**! -/
theorem no_diagonal_nonduplicating_varfree_ctx {m : Term} {c : Ctx} {σ : Nat → Term}
    (hlin : ∀ v, hasVar v m = true → countVar v (σ v) ≤ 1)
    (hdiag : ∀ u v, hasVar u m = true → hasVar v m = true → u ≠ v → hasVar v (σ u) = false)
    (hctx : ∀ v, hasVar v m = true → countVarCtx v c = 0) :
    ¬ OpenSpirals m c σ := by
  intro h
  refine no_open_spiral_non_extending_subst (fun v hv => ?_) h
  cases ht : rightTail (σ v) with
  | none => exact Or.inl rfl
  | some w =>
    refine Or.inr ?_
    have hwm : hasVar w m = true := open_spiral_vars_closed h hv (rightTail_hasVar ht)
    by_cases hvw : v = w
    · subst hvw
      have hcoup := reduces_maxRS_countVar_coupling v (stepPlus_to_reduces h)
      have hmax1 : maxRS v m + rs (σ v) ≤ maxRS v (subst σ m) :=
        maxRS_subst_ge_of_rightTail ht hv
      have hmax2 : maxRS v (subst σ m) ≤ maxRS v (plugCtx c (subst σ m)) :=
        maxRS_subterm_le v (subterm_iff_plugCtx.mpr ⟨c, rfl⟩)
      have hcv_sub : countVar v (subst σ m) ≤ countVar v m :=
        countVar_subst_diagonal_le (hlin v hv) (fun u hu hne => hdiag u v hu hv hne)
      have hcv_end : countVar v (plugCtx c (subst σ m)) ≤ countVar v m := by
        rw [countVar_plugCtx v c (subst σ m), hctx v hv, Nat.zero_add]
        exact hcv_sub
      omega
    · exfalso
      have hfalse : hasVar w (σ v) = false := hdiag v w hv hwm hvw
      rw [rightTail_hasVar ht] at hfalse
      cases hfalse

/-! ## 5. Universal Short-Loop Impossibility (`k = 1` and `k = 2` Steps for All Terms) -/

private theorem subterm_eq_or_children {w a b : Term} (h : Subterm w (a ⋅ b)) :
    w = a ⋅ b ∨ Subterm w a ∨ Subterm w b := by
  cases h with
  | refl => exact Or.inl rfl
  | left hl => exact Or.inr (Or.inl hl)
  | right hr => exact Or.inr (Or.inr hr)

private theorem no_one_step_subterm (σ : Nat → Term) {m n : Term} (hs : Step m n) :
    ¬ Subterm (subst σ m) n := by
  induction hs with
  | root x y z =>
    intro hsub
    have hlm := leaves_le_subst σ (S ⋅ x ⋅ y ⋅ z)
    have hx := leaves_pos x
    have hy := leaves_pos y
    have hz := leaves_pos z
    rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
    · injection heq with hl _
      injection hl with hll _
      have hxl := leaves_le_subst σ x
      have heq_l : leaves (S ⋅ subst σ x) = leaves x := congrArg leaves hll
      simp only [S, leaves] at heq_l
      omega
    · have hle := subterm_leaves_le hsub_l
      simp only [S, leaves] at hlm hle
      omega
    · have hle := subterm_leaves_le hsub_r
      simp only [S, leaves] at hlm hle
      omega
  | @left a a' b _ ih =>
    intro hsub
    rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
    · injection heq with ha' _
      exact ih (ha' ▸ .refl)
    · exact ih (subterm_trans (.left .refl) hsub_l)
    · have hle := subterm_leaves_le hsub_r
      have hge := leaves_le_subst σ (a ⋅ b)
      have ha := leaves_pos a
      simp only [leaves] at hge
      omega
  | @right a b b' _ ih =>
    intro hsub
    rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
    · injection heq with _ hb'
      exact ih (hb' ▸ .refl)
    · have hle := subterm_leaves_le hsub_l
      have hge := leaves_le_subst σ (a ⋅ b)
      have hb := leaves_pos b
      simp only [leaves] at hge
      omega
    · exact ih (subterm_trans (.right .refl) hsub_r)

/-- **Theorem 5A (`no_one_step_open_spiral`)**:
    For **all** pure-`S` terms `m`, contexts `c`, and substitutions `σ` (arbitrary size and variables),
    no 1-step open spiral `m →^1 C[m^σ]` exists! -/
theorem no_one_step_open_spiral (m : Term) (c : Ctx) (σ : Nat → Term) :
    ¬ Step m (plugCtx c (subst σ m)) :=
  fun hs => no_one_step_subterm σ hs (subterm_iff_plugCtx.mpr ⟨c, rfl⟩)

private theorem two_step_way_A (σ : Nat → Term) (u q r : Term) :
    ¬ Subterm (subst σ (S ⋅ (S ⋅ u) ⋅ q ⋅ r)) ((u ⋅ (q ⋅ r)) ⋅ (r ⋅ (q ⋅ r))) := by
  intro hsub
  have hlm := leaves_le_subst σ (S ⋅ (S ⋅ u) ⋅ q ⋅ r)
  have hu := leaves_pos u; have hq := leaves_pos q; have hrp := leaves_pos r
  rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
  · injection heq with hl _
    injection hl with hll _
    have hul := leaves_le_subst σ u
    have heq_l : leaves (S ⋅ (S ⋅ subst σ u)) = leaves u := congrArg leaves hll
    simp only [S, leaves] at heq_l; omega
  · rcases subterm_eq_or_children hsub_l with heq_l | h_u | h_qr
    · injection heq_l with hll _
      have hul := leaves_le_subst σ u
      have hql := leaves_le_subst σ q
      have heq2 : leaves ((S ⋅ (S ⋅ subst σ u)) ⋅ subst σ q) = leaves u := congrArg leaves hll
      simp only [S, leaves] at heq2; omega
    · have hle := subterm_leaves_le h_u; simp only [S, leaves] at hlm hle; omega
    · have hle := subterm_leaves_le h_qr; simp only [S, leaves] at hlm hle; omega
  · rcases subterm_eq_or_children hsub_r with heq_r | h_r | h_qr
    · injection heq_r with hr_eq hrs_eq
      -- Survivor 1: `(S ⋅ (S ⋅ u^σ)) ⋅ q^σ = r` and `r^σ = q ⋅ r`!
      have hrs2 : subst σ ((S ⋅ (S ⋅ subst σ u)) ⋅ subst σ q) = q ⋅ r :=
        (congrArg (subst σ) hr_eq).trans hrs_eq
      simp only [S, subst] at hrs2
      injection hrs2 with hq_eq hr_q2
      have hr_s : subst σ (subst σ (Term.s ⋅ (Term.s ⋅ subst σ (subst σ u)))) = r :=
        (congrArg (fun t => subst σ (subst σ t)) hq_eq).trans hr_q2
      simp only [subst] at hr_s
      have hclash := hr_s.trans hr_eq.symm
      injection hclash with hbad _
      cases hbad
    · have hle := subterm_leaves_le h_r; simp only [S, leaves] at hlm hle; omega
    · have hle := subterm_leaves_le h_qr; simp only [S, leaves] at hlm hle; omega

private theorem two_step_way_B2a (σ : Nat → Term) (y p r : Term) :
    ¬ Subterm (subst σ (S ⋅ S ⋅ y ⋅ p ⋅ r)) ((p ⋅ r) ⋅ ((y ⋅ p) ⋅ r)) := by
  intro hsub
  have hlm := leaves_le_subst σ (S ⋅ S ⋅ y ⋅ p ⋅ r)
  have hy := leaves_pos y; have hp := leaves_pos p; have hrp := leaves_pos r
  rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
  · -- Survivor 2: `(((S ⋅ S) ⋅ y^σ) ⋅ p^σ) ⋅ r^σ = (p ⋅ r) ⋅ ((y ⋅ p) ⋅ r)`
    injection heq with hl hrs_eq
    injection hl with hp_eq hps_eq
    have hr_val : (S ⋅ S) ⋅ subst σ (subst σ y) = r :=
      (congrArg (subst σ) hp_eq).trans hps_eq
    have hrs_val : (S ⋅ S) ⋅ subst σ (subst σ (subst σ y)) = (y ⋅ p) ⋅ r :=
      (congrArg (subst σ) hr_val).trans hrs_eq
    injection hrs_val with hyp_eq _
    injection hyp_eq with _ hsp
    have hclash := hp_eq.trans hsp.symm
    cases hclash
  · have hle := subterm_leaves_le hsub_l; simp only [S, leaves] at hlm hle; omega
  · rcases subterm_eq_or_children hsub_r with heq_r | h_yp | h_r
    · injection heq_r with hyp _
      injection hyp with hy_eq _
      have hyl := leaves_le_subst σ y
      have heq2 : leaves ((S ⋅ S) ⋅ subst σ y) = leaves y := congrArg leaves hy_eq
      simp only [S, leaves] at heq2; omega
    · have hle := subterm_leaves_le h_yp; simp only [S, leaves] at hlm hle; omega
    · have hle := subterm_leaves_le h_r; simp only [S, leaves] at hlm hle; omega

private theorem two_step_way_C1 (σ : Nat → Term) (x1 x2 q r : Term) :
    ¬ Subterm (subst σ (S ⋅ (S ⋅ x1 ⋅ x2) ⋅ q ⋅ r)) (((x1 ⋅ r) ⋅ (x2 ⋅ r)) ⋅ (q ⋅ r)) := by
  intro hsub
  have hlm := leaves_le_subst σ (S ⋅ (S ⋅ x1 ⋅ x2) ⋅ q ⋅ r)
  have hx1 := leaves_pos x1; have hx2 := leaves_pos x2; have hq := leaves_pos q; have hrp := leaves_pos r
  rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
  · -- Survivor 3: root match
    injection heq with hl hrs_eq
    injection hl with hx1r hqs_eq
    injection hx1r with hs_x1 hr_eq
    have hrs_val : (S ⋅ subst σ (subst σ x1)) ⋅ subst σ (subst σ x2) = q ⋅ r :=
      (congrArg (subst σ) hr_eq).trans hrs_eq
    injection hrs_val with hq_val _
    have hx1_s : subst σ (subst σ x1) = S := by subst hs_x1; rfl
    rw [hx1_s] at hq_val
    have hqs_ss : subst σ q = S ⋅ S := by rw [← hq_val]; rfl
    have hx2r_ss : S ⋅ S = x2 ⋅ r := hqs_ss.symm.trans hqs_eq
    injection hx2r_ss with _ hs_r
    have hclash := hr_eq.trans hs_r.symm
    cases hclash
  · rcases subterm_eq_or_children hsub_l with heq_l | h_x1r | h_x2r
    · injection heq_l with hl1 _
      injection hl1 with hx1_eq _
      have hx1l := leaves_le_subst σ x1; have hx2l := leaves_le_subst σ x2
      have heq2 : leaves (S ⋅ ((S ⋅ subst σ x1) ⋅ subst σ x2)) = leaves x1 := congrArg leaves hx1_eq
      simp only [S, leaves] at heq2; omega
    · have hle := subterm_leaves_le h_x1r; simp only [S, leaves] at hlm hle; omega
    · have hle := subterm_leaves_le h_x2r; simp only [S, leaves] at hlm hle; omega
  · have hle := subterm_leaves_le hsub_r; simp only [S, leaves] at hlm hle; omega

private theorem two_step_way_C2 (σ : Nat → Term) (p x1 x2 r : Term) :
    ¬ Subterm (subst σ (S ⋅ p ⋅ (S ⋅ x1 ⋅ x2) ⋅ r)) ((p ⋅ r) ⋅ ((x1 ⋅ r) ⋅ (x2 ⋅ r))) := by
  intro hsub
  have hlm := leaves_le_subst σ (S ⋅ p ⋅ (S ⋅ x1 ⋅ x2) ⋅ r)
  have hp := leaves_pos p; have hx1 := leaves_pos x1; have hx2 := leaves_pos x2; have hrp := leaves_pos r
  rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
  · injection heq with hl _
    injection hl with hp_eq _
    have hpl := leaves_le_subst σ p
    have heq2 : leaves (S ⋅ subst σ p) = leaves p := congrArg leaves hp_eq
    simp only [S, leaves] at heq2; omega
  · have hle := subterm_leaves_le hsub_l; simp only [S, leaves] at hlm hle; omega
  · rcases subterm_eq_or_children hsub_r with heq_r | h_x1r | h_x2r
    · -- Survivor 4: match `(x1 ⋅ r) ⋅ (x2 ⋅ r)`
      injection heq_r with hl hrs_eq
      injection hl with _ hr_eq
      have hrs_val : (S ⋅ subst σ (subst σ x1)) ⋅ subst σ (subst σ x2) = x2 ⋅ r :=
        (congrArg (subst σ) hr_eq).trans hrs_eq
      injection hrs_val with hx2_eq hr_x2
      have hr_s : S ⋅ subst σ (subst σ (subst σ (subst σ x1))) = r :=
        (congrArg (fun t => subst σ (subst σ t)) hx2_eq).trans hr_x2
      have hclash := hr_s.trans hr_eq.symm
      injection hclash with hbad _
      cases hbad
    · have hle := subterm_leaves_le h_x1r; simp only [S, leaves] at hlm hle; omega
    · have hle := subterm_leaves_le h_x2r; simp only [S, leaves] at hlm hle; omega

private theorem two_step_internal_P (σ : Nat → Term) {p p' q r : Term} (hp : Step p p') :
    ¬ Subterm (subst σ (S ⋅ p ⋅ q ⋅ r)) ((p' ⋅ r) ⋅ (q ⋅ r)) := by
  intro hsub
  have hlm := leaves_le_subst σ (S ⋅ p ⋅ q ⋅ r)
  have hp_pos := leaves_pos p; have hq_pos := leaves_pos q; have hr_pos := leaves_pos r
  rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
  · injection heq with hl _
    injection hl with hp' _
    exact no_one_step_subterm σ hp (hp' ▸ .right .refl)
  · rcases subterm_eq_or_children hsub_l with heq_l | h_p' | h_r
    · injection heq_l with hp' _
      exact no_one_step_subterm σ hp (hp' ▸ .left (.right .refl))
    · exact no_one_step_subterm σ hp (subterm_trans (.left (.left (.right .refl))) h_p')
    · have hle := subterm_leaves_le h_r; simp only [S, leaves] at hlm hle; omega
  · have hle := subterm_leaves_le hsub_r; simp only [S, leaves] at hlm hle; omega

private theorem two_step_internal_Q (σ : Nat → Term) {p q q' r : Term} (hq : Step q q') :
    ¬ Subterm (subst σ (S ⋅ p ⋅ q ⋅ r)) ((p ⋅ r) ⋅ (q' ⋅ r)) := by
  intro hsub
  have hlm := leaves_le_subst σ (S ⋅ p ⋅ q ⋅ r)
  have hp_pos := leaves_pos p; have hq_pos := leaves_pos q; have hr_pos := leaves_pos r
  rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
  · injection heq with hl _
    injection hl with hp_eq _
    have hpl := leaves_le_subst σ p
    have heq2 : leaves (S ⋅ subst σ p) = leaves p := congrArg leaves hp_eq
    simp only [S, leaves] at heq2; omega
  · have hle := subterm_leaves_le hsub_l; simp only [S, leaves] at hlm hle; omega
  · rcases subterm_eq_or_children hsub_r with heq_r | h_q' | h_r
    · injection heq_r with hq' _
      exact no_one_step_subterm σ hq (hq' ▸ .right .refl)
    · exact no_one_step_subterm σ hq (subterm_trans (.left (.right .refl)) h_q')
    · have hle := subterm_leaves_le h_r; simp only [S, leaves] at hlm hle; omega

private theorem two_step_internal_R_both (σ : Nat → Term) {p q r r1 r2 : Term}
    (hr1 : r1 = r ∨ Step r r1) (hr2 : r2 = r ∨ Step r r2) :
    ¬ Subterm (subst σ (S ⋅ p ⋅ q ⋅ r)) ((p ⋅ r1) ⋅ (q ⋅ r2)) := by
  intro hsub
  have hlm := leaves_le_subst σ (S ⋅ p ⋅ q ⋅ r)
  have hp_pos := leaves_pos p; have hq_pos := leaves_pos q; have hr_pos := leaves_pos r
  rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
  · injection heq with hl _
    injection hl with hp_eq _
    have hpl := leaves_le_subst σ p
    have heq2 : leaves (S ⋅ subst σ p) = leaves p := congrArg leaves hp_eq
    simp only [S, leaves] at heq2; omega
  · rcases subterm_eq_or_children hsub_l with heq_l | h_p | h_r1
    · injection heq_l with hp_eq _
      have hpl := leaves_le_subst σ p; have hql := leaves_le_subst σ q
      have heq2 : leaves ((S ⋅ subst σ p) ⋅ subst σ q) = leaves p := congrArg leaves hp_eq
      simp only [S, leaves] at heq2; omega
    · have hle := subterm_leaves_le h_p; simp only [S, leaves] at hlm hle; omega
    · rcases hr1 with rfl | hs_r1
      · have hle := subterm_leaves_le h_r1; simp only [S, leaves] at hlm hle; omega
      · exact no_one_step_subterm σ hs_r1 (subterm_trans (.right .refl) h_r1)
  · rcases subterm_eq_or_children hsub_r with heq_r | h_q | h_r2
    · injection heq_r with hq_eq _
      have hpl := leaves_le_subst σ p; have hql := leaves_le_subst σ q
      have heq2 : leaves ((S ⋅ subst σ p) ⋅ subst σ q) = leaves q := congrArg leaves hq_eq
      simp only [S, leaves] at heq2; omega
    · have hle := subterm_leaves_le h_q; simp only [S, leaves] at hlm hle; omega
    · rcases hr2 with rfl | hs_r2
      · have hle := subterm_leaves_le h_r2; simp only [S, leaves] at hlm hle; omega
      · exact no_one_step_subterm σ hs_r2 (subterm_trans (.right .refl) h_r2)

private theorem no_two_step_subterm_bounded (σ : Nat → Term) :
    ∀ K : Nat, ∀ m m1 n : Term, leaves m ≤ K →
      Step m m1 → Step m1 n → ¬ Subterm (subst σ m) n
  | 0, m, _, _, hK, _, _ => by
    have := leaves_pos m; omega
  | K + 1, m, m1, n, hK, hs1, hs2 => by
    intro hsub
    rcases step_iff_root_or_nonRoot.mp hs1 with hr1 | hnr1
    · -- Step 1 is a RootStep: `m = S ⋅ p ⋅ q ⋅ r`, `m1 = (p ⋅ r) ⋅ (q ⋅ r)`
      cases hr1 with
      | mk p q r =>
        cases hs2 with
        | root u v _ =>
          -- `(p ⋅ r) = S ⋅ u ⋅ v` => `p = S ⋅ u`, `r = v` (Way A!)
          exact two_step_way_A σ u q r hsub
        | @left _ l' _ hl2 =>
          cases hl2 with
          | root x1 x2 _ => exact two_step_way_C1 σ x1 x2 q r hsub
          | left hp => exact two_step_internal_P σ hp hsub
          | right hr => exact two_step_internal_R_both σ (Or.inr hr) (Or.inl rfl) hsub
        | @right _ _ r'' hr2 =>
          cases hr2 with
          | root x1 x2 _ => exact two_step_way_C2 σ p x1 x2 r hsub
          | left hq => exact two_step_internal_Q σ hq hsub
          | right hr => exact two_step_internal_R_both σ (Or.inl rfl) (Or.inr hr) hsub
    · -- Step 1 is a NonRootStep! Check whether Step 2 is RootStep or NonRootStep!
      rcases step_iff_root_or_nonRoot.mp hs2 with hr2 | hnr2
      · -- Step 1 NonRootStep, Step 2 RootStep: `m1 = S ⋅ p' ⋅ q' ⋅ r'`, `n = (p' ⋅ r') ⋅ (q' ⋅ r')`
        cases hr2 with
        | mk p' q' r' =>
          cases hnr1 with
          | @right _ _ _ hr_step =>
            exact two_step_internal_R_both σ (Or.inr hr_step) (Or.inr hr_step) hsub
          | @left _ _ _ hl_step =>
            cases hl_step with
            | root x y z =>
              -- `(x ⋅ z) ⋅ (y ⋅ z) = (S ⋅ p') ⋅ q'` => `x = S, z = p'` (Way B2a!)
              exact two_step_way_B2a σ y p' r' hsub
            | right hq_step => exact two_step_internal_Q σ hq_step hsub
            | left hll_step =>
              cases hll_step with
              | right hp_step => exact two_step_internal_P σ hp_step hsub
              | left hs_step => cases hs_step
      · -- Both Step 1 and Step 2 are NonRootSteps on `m = a ⋅ b`!
        cases hnr1 with
        | @left a a1 b ha1 =>
          have ha_le : leaves a ≤ K := by
            have := leaves_pos b; simp only [leaves] at hK; omega
          have hb_le : leaves b ≤ K := by
            have := leaves_pos a; simp only [leaves] at hK; omega
          cases hnr2 with
          | @left _ a2 _ ha2 =>
            rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
            · injection heq with ha2_eq _
              exact no_two_step_subterm_bounded σ K a a1 a2 ha_le ha1 ha2 (ha2_eq ▸ .refl)
            · exact no_two_step_subterm_bounded σ K a a1 a2 ha_le ha1 ha2 (subterm_trans (.left .refl) hsub_l)
            · have hle := subterm_leaves_le hsub_r
              have hge := leaves_le_subst σ (a ⋅ b)
              have hap := leaves_pos a; simp only [leaves] at hge; omega
          | @right _ _ b1 hb1 =>
            rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
            · injection heq with ha1_eq _
              exact no_one_step_subterm σ ha1 (ha1_eq ▸ .refl)
            · exact no_one_step_subterm σ ha1 (subterm_trans (.left .refl) hsub_l)
            · exact no_one_step_subterm σ hb1 (subterm_trans (.right .refl) hsub_r)
        | @right a b b1 hb1 =>
          have ha_le : leaves a ≤ K := by
            have := leaves_pos b; simp only [leaves] at hK; omega
          have hb_le : leaves b ≤ K := by
            have := leaves_pos a; simp only [leaves] at hK; omega
          cases hnr2 with
          | @left a a1 _ ha1 =>
            rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
            · injection heq with ha1_eq _
              exact no_one_step_subterm σ ha1 (ha1_eq ▸ .refl)
            · exact no_one_step_subterm σ ha1 (subterm_trans (.left .refl) hsub_l)
            · exact no_one_step_subterm σ hb1 (subterm_trans (.right .refl) hsub_r)
          | @right _ _ b2 hb2 =>
            rcases subterm_eq_or_children hsub with heq | hsub_l | hsub_r
            · injection heq with _ hb2_eq
              exact no_two_step_subterm_bounded σ K b b1 b2 hb_le hb1 hb2 (hb2_eq ▸ .refl)
            · have hle := subterm_leaves_le hsub_l
              have hge := leaves_le_subst σ (a ⋅ b)
              have hbp := leaves_pos b; simp only [leaves] at hge; omega
            · exact no_two_step_subterm_bounded σ K b b1 b2 hb_le hb1 hb2 (subterm_trans (.right .refl) hsub_r)

/-- **Theorem 5B (`no_two_step_open_spiral`)**:
    For **all** pure-`S` terms `m`, contexts `c`, and substitutions `σ` (arbitrary size and variables),
    no 2-step open spiral `m →^2 C[m^σ]` exists! -/
theorem no_two_step_open_spiral (m : Term) (c : Ctx) (σ : Nat → Term) :
    ¬ ∃ m1, Step m m1 ∧ Step m1 (plugCtx c (subst σ m)) := by
  rintro ⟨m1, hs1, hs2⟩
  exact no_two_step_subterm_bounded σ (leaves m) m m1 (plugCtx c (subst σ m))
    (Nat.le_refl _) hs1 hs2 (subterm_iff_plugCtx.mpr ⟨c, rfl⟩)

/-! ## 6. Contrarian Parametric Near-Miss in Pure `CL(S)` (`V x (V x) →^3 C[V x (T (V x))]`) -/

def Z_zachos : Term := S ⋅ B_comb ⋅ B_comb
def V_waldmann : Term := S ⋅ Z_zachos

/-- **Theorem 6 (`waldmann_open_parametric_near_miss`)**:
    In pure `CL(S)` (without `λ`-calculus), let `T = S S` (`B_comb`), `Z = S T T`, `V = S Z`.
    For any variable `x`, the open term `V x (V x)` reduces in **3 steps** to
    `S (T (V x)) (V x (T (V x))) (.var x ⋅ (V x))`, which contains **`V x (T (V x))`** as a proper
    subterm (`C_0[V x (T (V x))]`), demonstrating parametric `n ↦ n + 1` self-embedding in pure `S`! -/
theorem waldmann_open_parametric_near_miss (x : Nat) :
    let vx := V_waldmann ⋅ .var x
    let c0 := Ctx.left (Ctx.right (S ⋅ (B_comb ⋅ vx)) Ctx.hole) (.var x ⋅ vx)
    StepPlus (vx ⋅ vx) (plugCtx c0 (vx ⋅ (B_comb ⋅ vx))) := by
  intro vx c0
  have s1 : Step (vx ⋅ vx) ((Z_zachos ⋅ vx) ⋅ (.var x ⋅ vx)) :=
    Step.root Z_zachos (.var x) vx
  have s2 : Step ((Z_zachos ⋅ vx) ⋅ (.var x ⋅ vx)) (((B_comb ⋅ vx) ⋅ (B_comb ⋅ vx)) ⋅ (.var x ⋅ vx)) :=
    Step.left (Step.root B_comb B_comb vx)
  have s3 : Step (((B_comb ⋅ vx) ⋅ (B_comb ⋅ vx)) ⋅ (.var x ⋅ vx))
      ((S ⋅ (B_comb ⋅ vx) ⋅ (vx ⋅ (B_comb ⋅ vx))) ⋅ (.var x ⋅ vx)) :=
    Step.left (Step.root S vx (B_comb ⋅ vx))
  exact .head s1 (.head s2 (.single s3))

end Conjecture17Obstructions

#print axioms Conjecture17Obstructions.open_spiral_not_sn
#print axioms Conjecture17Obstructions.open_spiral_subst_not_sn
#print axioms Conjecture17Obstructions.open_spiral_closeTerm_not_sn
#print axioms Conjecture17Obstructions.no_open_cycle
#print axioms Conjecture17Obstructions.minimal_open_spiral_has_root_and_s_head
#print axioms Conjecture17Obstructions.minimal_open_spiral_spineLen_ge_3
#print axioms Conjecture17Obstructions.no_open_spiral_bounded_rs
#print axioms Conjecture17Obstructions.waldmann_no_spiral_theorem_14
#print axioms Conjecture17Obstructions.no_open_spiral_zero_rs_subst
#print axioms Conjecture17Obstructions.no_open_spiral_non_extending_subst
#print axioms Conjecture17Obstructions.no_open_spiral_s_tailed_subst
#print axioms Conjecture17Obstructions.one_var_open_spiral_forces_right_tail_ext
#print axioms Conjecture17Obstructions.no_open_spiral_left_only_vars
#print axioms Conjecture17Obstructions.step_rs_maxRS_coupling
#print axioms Conjecture17Obstructions.no_one_var_nonduplicating_varfree_ctx
#print axioms Conjecture17Obstructions.no_diagonal_nonduplicating_varfree_ctx
#print axioms Conjecture17Obstructions.no_one_step_open_spiral
#print axioms Conjecture17Obstructions.no_two_step_open_spiral
#print axioms Conjecture17Obstructions.waldmann_open_parametric_near_miss

