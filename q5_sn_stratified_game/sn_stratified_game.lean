import formal_algebra.sn_hn_algebras

/-!
# SN-Stratified Böhm-Game, Pure-`S` Head-Escape Sink Laws, Non-`SN` HNF Classification, and Leftmost-vs-Rightmost Böhm Asymmetry for Open Question 5

Self-contained Lean 4.33.1 formalization (building on `formal_algebra.sn_hn_algebras`) establishing
orthogonal structural foundations for **Open Question 5** of Barendregt, Endrullis, Klop, and
Waldmann (2018), *"Dance of the Starlings"* (decidability of productivity on closed `CL(S)` terms):

1. **Exact Böhm-Bottom (`HasBotWithin`, `HasBot`, `Productive`) & Two-Sided Conversion Invariance**:
   Full equivalence of `Productive` across `ConvS` (`Step`, `Reduces`, and backward reduction) via
   Church–Rosser (`productive_conv_invariant`).
2. **The Pure-`S` Head-Escape Theorem (`hasXSpine_headStep`, `pure_s_head_escape`) & Exact Sink Laws**:
   A 5-line structural spine invariant on open `{S, x_0}`-terms combined with Waldmann's `muHN`
   potential proves unconditionally for all closed pure-`S` terms:
   - **Left Sink Law (`hasBotWithin_app_left`)**: `HasBotWithin d y → HasBotWithin d (y ⋅ z)`
   - **Right Sink Law (`hasBotWithin_app_right`)**: `HasBotWithin d w → HasBotWithin (d + 1) (f ⋅ w)`
   reducing completeness of the 39-state automaton `A_P` strictly to Minimal Entry Pairs
   (`minimal_entry_reduction_theorem`).
3. **Exact 39-State Productivity Algebra `A_P`, Soundness (`evalP_ne_p37_implies_productive`),
   and 44-State `A_P × A_SN` Stratification**:
   - Soundness of `A_P` (`noVars t = true → evalP t ≠ .p37 → Productive t`).
   - **34-of-38 `SN` Theorem (`evalP_34_states_sn`)**: Every closed term outside `{.p18, .p24, .p29, .p33, .p37}`
     is strongly normalizing (`evalSN t ≠ .sn38`) and reduces to a Closed Normal Form (`CNF`).
   - **Non-`SN` HNF Rigidity Theorem (`nonSN_p18_p24_p33_reduces_hnf_no_root`,
     `unique_nonSN_productive_root_redex_state`)**: Every closed application `l ⋅ r` in `(.p18, .sn38)`,
     `(.p24, .sn38)`, or `(.p33, .sn38)` has `l` strongly normalizing with `isS2StateSN (evalSN l) = false`,
     so `l` reduces to `S` or `S ⋅ u` and `l ⋅ r` reduces without a single root contraction to an HNF.
     Hence `(.p29, .sn38)` is the **unique** non-`SN` productive state in `CL(S)` admitting a root redex.
4. **Exact Last-Head-Step Law (`last_headStep_s2_law`) & Böhm-Game Branch Asymmetry Theorem**:
   - Every head-normalization `t →_h^+ h` from `spineLen t ≥ 3` ends at `h = S ⋅ a ⋅ (y ⋅ a)`.
   - Deterministic `stepBohmRight` soundness (`iterBohmRight_sound`).
   - **Asymmetry of Pure-`S` Böhm Selection (`bohm_game_asymmetry_size8`)**: On the 8-leaf closed term
     `L_loop = S ⋅ T ⋅ S ⋅ T ⋅ T` (`evalP L_loop = .p37`), deterministic `stepBohmRight` reaches root
     divergence (`evalHN = .hn34`) in 4 steps (`HasBotWithin 4 L_loop`), whereas deterministic
     `stepBohmLeft` diverges forever along an unbounded tower `iterT 0 ⋅ iterT n` (`leaves → ∞`).

100% constructive kernel proof: zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`,
and zero `Classical.choice` (`#print axioms` uses at most `[propext]`).
-/

namespace Q5SNStratifiedGame

set_option linter.constructorNameAsVariable false

open FormalAlgebra

private theorem one_add_le {a b : Nat} (h : 1 + a ≤ 1 + b) : a ≤ b := by
  rw [Nat.add_comm 1 a, Nat.add_comm 1 b] at h
  exact Nat.le_of_succ_le_succ h

private theorem if_false_eq_true {α : Type} (x y : α) : (if false = true then x else y) = y := rfl
private theorem if_true_eq_true {α : Type} (x y : α) : (if true = true then x else y) = x := rfl

/-! ## 1. Böhm-Bottom (`HasBotWithin`, `HasBot`, `Productive`) and Church–Rosser Invariance -/

inductive HasBotWithin : Nat → Term → Prop where
  | bot_div {d : Nat} {t : Term} : ¬ HasHNF t → HasBotWithin d t
  | bot_s1 {d : Nat} {t a : Term} : Reduces t (S ⋅ a) → HasBotWithin d a → HasBotWithin (d + 1) t
  | bot_s2_l {d : Nat} {t a b : Term} : Reduces t (S ⋅ a ⋅ b) → HasBotWithin d a → HasBotWithin (d + 1) t
  | bot_s2_r {d : Nat} {t a b : Term} : Reduces t (S ⋅ a ⋅ b) → HasBotWithin d b → HasBotWithin (d + 1) t

def HasBot (t : Term) : Prop :=
  ∃ d, HasBotWithin d t

def Productive (t : Term) : Prop :=
  ¬ HasBot t

theorem hasBotWithin_mono {d1 d2 : Nat} {t : Term} (hle : d1 ≤ d2) (h : HasBotWithin d1 t) :
    HasBotWithin d2 t := by
  induction h generalizing d2 with
  | bot_div hno => exact .bot_div hno
  | @bot_s1 d0 _ a hred _ ih =>
    cases d2 with
    | zero => cases hle
    | succ d2' => exact .bot_s1 hred (ih (Nat.le_of_succ_le_succ hle))
  | @bot_s2_l d0 _ a b hred _ ih =>
    cases d2 with
    | zero => cases hle
    | succ d2' => exact .bot_s2_l hred (ih (Nat.le_of_succ_le_succ hle))
  | @bot_s2_r d0 _ a b hred _ ih =>
    cases d2 with
    | zero => cases hle
    | succ d2' => exact .bot_s2_r hred (ih (Nat.le_of_succ_le_succ hle))

theorem step_preserves_spineLen_le_2 {a b : Term} (hs : Step a b) (hsl : spineLen a ≤ 2) :
    spineLen b ≤ 2 := by
  cases hs with
  | root x y z =>
    exfalso
    change 1 + (1 + (1 + 0)) ≤ 1 + (1 + 0) at hsl
    exact Nat.not_succ_le_zero 0 (one_add_le (one_add_le hsl))
  | @left l l' r hl =>
    cases hl with
    | root x y z =>
      exfalso
      change 1 + (1 + (1 + (1 + 0))) ≤ 1 + (1 + 0) at hsl
      exact Nat.not_succ_le_zero 1 (one_add_le (one_add_le hsl))
    | @left ll ll' lr hll =>
      cases ll with
      | s => cases hll
      | var _ => cases hll
      | app u v =>
        exfalso
        change 1 + (1 + (1 + spineLen u)) ≤ 1 + (1 + 0) at hsl
        have hbad : 1 + spineLen u ≤ 0 := one_add_le (one_add_le hsl)
        rw [Nat.add_comm 1 (spineLen u)] at hbad
        exact Nat.not_succ_le_zero _ hbad
    | @right ll lr lr' _ =>
      exact hsl
  | right _ =>
    exact hsl

theorem reduces_preserves_spineLen_le_2 {a b : Term} (hred : Reduces a b) (hsl : spineLen a ≤ 2) :
    spineLen b ≤ 2 := by
  induction hred with
  | refl _ => exact hsl
  | next hs _ ih => exact ih (step_preserves_spineLen_le_2 hs hsl)

theorem s_reduces_eq {u : Term} (h : Reduces S u) : u = S := by
  cases h with
  | refl _ => rfl
  | next hs _ => cases hs

theorem s1_reduces_inv {m u : Term} {x : Term} (h : Reduces m u) (hm : m = S ⋅ x) :
    ∃ x', u = S ⋅ x' ∧ Reduces x x' := by
  induction h generalizing x with
  | refl _ => exact ⟨x, hm, Reduces.refl x⟩
  | @next _ v _ hs _ ih =>
    subst hm
    cases hs with
    | left hl => cases hl
    | @right _ _ x1 hx1 =>
      obtain ⟨x', hu, hx'⟩ := ih rfl
      exact ⟨x', hu, Reduces.next hx1 hx'⟩

theorem s2_reduces_inv {m u : Term} {x y : Term} (h : Reduces m u) (hm : m = S ⋅ x ⋅ y) :
    ∃ x' y', u = S ⋅ x' ⋅ y' ∧ Reduces x x' ∧ Reduces y y' := by
  induction h generalizing x y with
  | refl _ => exact ⟨x, y, hm, Reduces.refl x, Reduces.refl y⟩
  | @next _ v _ hs _ ih =>
    subst hm
    cases hs with
    | @left _ l' _ hl =>
      cases hl with
      | left hll => cases hll
      | @right _ _ x1 hx1 =>
        obtain ⟨x', y', hu, hx', hy'⟩ := ih rfl
        exact ⟨x', y', hu, Reduces.next hx1 hx', hy'⟩
    | @right _ _ y1 hy1 =>
      obtain ⟨x', y', hu, hx', hy'⟩ := ih rfl
      exact ⟨x', y', hu, hx', Reduces.next hy1 hy'⟩

theorem hasBotWithin_backward_reduces {d : Nat} {a b : Term}
    (hab : Reduces a b) (hb : HasBotWithin d b) : HasBotWithin d a := by
  cases hb with
  | bot_div hno =>
    refine .bot_div (fun ⟨h, hah, hsl⟩ => hno ?_)
    obtain ⟨u, hbu, hhu⟩ := church_rosser hab hah
    exact ⟨u, hbu, reduces_preserves_spineLen_le_2 hhu hsl⟩
  | bot_s1 hred ha =>
    exact .bot_s1 (reduces_trans hab hred) ha
  | bot_s2_l hred ha =>
    exact .bot_s2_l (reduces_trans hab hred) ha
  | bot_s2_r hred ha =>
    exact .bot_s2_r (reduces_trans hab hred) ha

theorem hasBotWithin_forward_reduces {d : Nat} {a b : Term}
    (hab : Reduces a b) (ha : HasBotWithin d a) : HasBotWithin d b := by
  induction ha generalizing b with
  | bot_div hno =>
    exact .bot_div (fun ⟨h, hbh, hsl⟩ => hno ⟨h, reduces_trans hab hbh, hsl⟩)
  | bot_s1 hred _ ih =>
    obtain ⟨u, hbu, hsu⟩ := church_rosser hab hred
    obtain ⟨x', rfl, hxx'⟩ := s1_reduces_inv hsu rfl
    exact .bot_s1 hbu (ih hxx')
  | bot_s2_l hred _ ih =>
    obtain ⟨u, hbu, hsu⟩ := church_rosser hab hred
    obtain ⟨x', y', rfl, hxx', _⟩ := s2_reduces_inv hsu rfl
    exact .bot_s2_l hbu (ih hxx')
  | bot_s2_r hred _ ih =>
    obtain ⟨u, hbu, hsu⟩ := church_rosser hab hred
    obtain ⟨x', y', rfl, _, hyy'⟩ := s2_reduces_inv hsu rfl
    exact .bot_s2_r hbu (ih hyy')

theorem hasBotWithin_conv_invariant {d : Nat} {a b : Term} (hconv : ConvS a b) :
    HasBotWithin d a ↔ HasBotWithin d b := by
  induction hconv with
  | refl _ => exact Iff.rfl
  | step hs =>
    have hred := Reduces.next hs (Reduces.refl _)
    exact ⟨hasBotWithin_forward_reduces hred, hasBotWithin_backward_reduces hred⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem productive_conv_invariant {a b : Term} (hconv : ConvS a b) :
    Productive a ↔ Productive b := by
  constructor
  · intro hpa ⟨d, hb⟩
    exact hpa ⟨d, (hasBotWithin_conv_invariant hconv).mpr hb⟩
  · intro hpb ⟨d, ha⟩
    exact hpb ⟨d, (hasBotWithin_conv_invariant hconv).mp ha⟩

theorem closed_evalHN_hn34_hasBot0 {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) :
    HasBotWithin 0 t :=
  .bot_div (fun hhnf => ((barendregt_open_problem_10 hv).1.mp hhnf) h34)

theorem closed_not_hasHNF_evalHN_hn34 {t : Term} (hv : noVars t = true) (hno : ¬ HasHNF t) :
    evalHN t = .hn34 :=
  if h34 : evalHN t = .hn34 then h34
  else False.elim (hno ((barendregt_open_problem_10 hv).1.mpr h34))

/-! ## 2. The Pure-`S` Head-Escape Theorem (`hasXSpine`) and Exact Sink Laws (`LeftSink` & `RightSink`) -/

def onlyVar0 : Term → Bool
  | .s => true
  | .var k => decide (k = 0)
  | .app a b => onlyVar0 a && onlyVar0 b

def hasXSpine : Term → Bool
  | .s => false
  | .var k => decide (k = 0)
  | .app a b => hasXSpine a || decide (headLeaf b = .var 0)

theorem noVars_implies_onlyVar0 {t : Term} (hv : noVars t = true) : onlyVar0 t = true := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    have ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp hv
    exact (Bool.and_eq_true _ _).mpr ⟨iha ha, ihb hb⟩

theorem onlyVar0_step {a b : Term} (hs : Step a b) : onlyVar0 a = true → onlyVar0 b = true := by
  induction hs with
  | root x y z =>
    simp only [S, onlyVar0, Bool.and_eq_true]
    intro ⟨⟨⟨_, hx⟩, hy⟩, hz⟩
    exact ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
  | left _ ih =>
    simp only [onlyVar0, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    exact ⟨ih ha, hb⟩
  | right _ ih =>
    simp only [onlyVar0, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    exact ⟨ha, ih hb⟩

theorem hasXSpine_of_headLeaf_var0 {t : Term} (h : headLeaf t = .var 0) : hasXSpine t = true := by
  induction t with
  | s => cases h
  | var k =>
    change headLeaf (.var k) = .var 0 at h
    injection h with hk
    subst hk
    rfl
  | app a b iha _ =>
    exact (Bool.or_eq_true _ _).mpr (Or.inl (iha h))

/-- **The 5-Line Structural Spine Miracle**:
    Every `HeadStep` preserves the presence of `.var 0` as the `headLeaf` of either the root
    or at least one spine argument! -/
theorem hasXSpine_headStep {a b : Term} (hs : HeadStep a b) :
    hasXSpine a = true → hasXSpine b = true := by
  induction hs with
  | root x y z =>
    intro h
    simp only [S, hasXSpine, Bool.false_or, Bool.or_eq_true] at h
    rcases h with (hx | hy) | hz
    · have hlx : headLeaf x = .var 0 := of_decide_eq_true hx
      exact hasXSpine_of_headLeaf_var0 (t := (x ⋅ z) ⋅ (y ⋅ z)) hlx
    · have hly : headLeaf y = .var 0 := of_decide_eq_true hy
      have hlyz : decide (headLeaf (y ⋅ z) = .var 0) = true := decide_eq_true hly
      exact (Bool.or_eq_true _ _).mpr (Or.inr hlyz)
    · have hx_z : hasXSpine (x ⋅ z) = true := (Bool.or_eq_true _ _).mpr (Or.inr hz)
      exact (Bool.or_eq_true _ _).mpr (Or.inl hx_z)
  | left _ ih =>
    intro h
    rcases (Bool.or_eq_true _ _).mp h with ha | hb
    · exact (Bool.or_eq_true _ _).mpr (Or.inl (ih ha))
    · exact (Bool.or_eq_true _ _).mpr (Or.inr hb)

theorem subst_closed_id (σ : Nat → Term) {t : Term} (hv : noVars t = true) : subst σ t = t := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    have ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp hv
    simp only [subst, iha ha, ihb hb]

theorem noVars_subst_closed {w : Term} (hw : noVars w = true) (u : Term) :
    noVars (subst (fun _ => w) u) = true := by
  induction u with
  | s => rfl
  | var _ => exact hw
  | app a b iha ihb => exact (Bool.and_eq_true _ _).mpr ⟨iha, ihb⟩

theorem subst_headStep (σ : Nat → Term) {a b : Term} (hs : HeadStep a b) :
    HeadStep (subst σ a) (subst σ b) := by
  induction hs with
  | root x y z => exact HeadStep.root (subst σ x) (subst σ y) (subst σ z)
  | left _ ih => exact HeadStep.left ih

theorem subst_headReduces (σ : Nat → Term) {a b : Term} (hr : HeadReduces a b) :
    HeadReduces (subst σ a) (subst σ b) := by
  induction hr with
  | refl _ => exact HeadReduces.refl _
  | next hs _ ih => exact HeadReduces.next (subst_headStep σ hs) ih

def openHeadNormAux : Nat → Term → Term
  | 0, u => u
  | fuel + 1, u =>
    match headStepOpt u with
    | none => u
    | some u' => openHeadNormAux fuel u'

private theorem openHeadNormAux_spec {w : Term} :
    ∀ (fuel : Nat) {u : Term},
      onlyVar0 u = true →
      hasXSpine u = true →
      evalHN (subst (fun _ => w) u) ≠ .hn34 →
      muHN (subst (fun _ => w) u) < fuel →
      let uStar := openHeadNormAux fuel u
      HeadReduces u uStar ∧ onlyVar0 uStar = true ∧ hasXSpine uStar = true ∧ headStepOpt uStar = none := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ hlt
    cases hlt
  | succ fuel ih =>
    intro u hov hxs hval hlt
    simp only [openHeadNormAux]
    cases hh : headStepOpt u with
    | none =>
      exact ⟨HeadReduces.refl u, hov, hxs, hh⟩
    | some u' =>
      have hs : HeadStep u u' := headStepOpt_some hh
      have hs_sub : HeadStep (subst (fun _ => w) u) (subst (fun _ => w) u') :=
        subst_headStep (fun _ => w) hs
      have hdrop : muHN (subst (fun _ => w) u') + 1 ≤ muHN (subst (fun _ => w) u) :=
        muHN_headStep_drop hs_sub hval
      have hval' : evalHN (subst (fun _ => w) u') ≠ .hn34 := by
        rw [← evalHN_step (headStep_to_step hs_sub)]
        exact hval
      have hov' : onlyVar0 u' = true := onlyVar0_step (headStep_to_step hs) hov
      have hxs' : hasXSpine u' = true := hasXSpine_headStep hs hxs
      have hlt' : muHN (subst (fun _ => w) u') < fuel :=
        Nat.lt_of_succ_lt_succ (Nat.lt_of_le_of_lt hdrop hlt)
      obtain ⟨hred, hov_s, hxs_s, hnone⟩ := ih hov' hxs' hval' hlt'
      exact ⟨HeadReduces.next hs hred, hov_s, hxs_s, hnone⟩

theorem open_hnf_dichotomy {u : Term} (hov : onlyVar0 u = true) (hnone : headStepOpt u = none) :
    headLeaf u = .var 0 ∨ u = S ∨ (∃ a, u = S ⋅ a) ∨ (∃ a b, u = S ⋅ a ⋅ b) := by
  induction u with
  | s => exact Or.inr (Or.inl rfl)
  | var k =>
    have hk : k = 0 := of_decide_eq_true hov
    subst hk
    exact Or.inl rfl
  | app a b iha _ =>
    have ⟨hova, _⟩ := (Bool.and_eq_true _ _).mp hov
    simp only [headStepOpt] at hnone
    cases hr : rootRedexOpt a b with
    | some _ => rw [hr] at hnone; cases hnone
    | none =>
      rw [hr] at hnone
      cases ha : headStepOpt a with
      | some _ => rw [ha] at hnone; cases hnone
      | none =>
        rcases iha hova ha with hl0 | rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
        · exact Or.inl hl0
        · exact Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨x, b, rfl⟩))
        · exfalso; exact rootRedexOpt_none hr x y rfl

/-- **Pure-`S` Head-Escape Theorem**:
    For every closed pure-`S` term `f` and closed `w` such that `evalHN (f ⋅ w) ≠ .hn34`,
    `f ⋅ .var 0` head-reduces to an open head-normal form `u*` whose head is either `.var 0` itself,
    `S ⋅ a` with `headLeaf a = .var 0`, or `S ⋅ a ⋅ b` with `headLeaf a = .var 0 ∨ headLeaf b = .var 0`. -/
theorem pure_s_head_escape {f w : Term} (hvf : noVars f = true)
    (hval : evalHN (f ⋅ w) ≠ .hn34) :
    ∃ uStar,
      HeadReduces (f ⋅ .var 0) uStar ∧
      (headLeaf uStar = .var 0 ∨
       (∃ a, uStar = S ⋅ a ∧ headLeaf a = .var 0) ∨
       (∃ a b, uStar = S ⋅ a ⋅ b ∧ (headLeaf a = .var 0 ∨ headLeaf b = .var 0))) := by
  let σ : Nat → Term := fun _ => w
  have hsub_eq : subst σ (f ⋅ .var 0) = f ⋅ w := by
    change subst σ f ⋅ w = f ⋅ w
    rw [subst_closed_id σ hvf]
  have hov0 : onlyVar0 (f ⋅ .var 0) = true :=
    (Bool.and_eq_true _ _).mpr ⟨noVars_implies_onlyVar0 hvf, rfl⟩
  have hxs0 : hasXSpine (f ⋅ .var 0) = true :=
    (Bool.or_eq_true _ _).mpr (Or.inr rfl)
  have hval_sub : evalHN (subst σ (f ⋅ .var 0)) ≠ .hn34 := by
    rw [hsub_eq]; exact hval
  obtain ⟨hred, hov_s, hxs_s, hnone⟩ :=
    openHeadNormAux_spec (w := w) (muHN (subst σ (f ⋅ .var 0)) + 1) hov0 hxs0 hval_sub (Nat.lt_succ_self _)
  refine ⟨openHeadNormAux (muHN (subst σ (f ⋅ .var 0)) + 1) (f ⋅ .var 0), hred, ?_⟩
  rcases open_hnf_dichotomy hov_s hnone with hl0 | heq_s | ⟨a, heq1⟩ | ⟨a, b, heq2⟩
  · exact Or.inl hl0
  · rw [heq_s] at hxs_s; cases hxs_s
  · rw [heq1] at hxs_s
    simp only [S, hasXSpine, Bool.false_or] at hxs_s
    exact Or.inr (Or.inl ⟨a, heq1, of_decide_eq_true hxs_s⟩)
  · rw [heq2] at hxs_s
    simp only [S, hasXSpine, Bool.false_or, Bool.or_eq_true] at hxs_s
    rcases hxs_s with ha | hb
    · exact Or.inr (Or.inr ⟨a, b, heq2, Or.inl (of_decide_eq_true ha)⟩)
    · exact Or.inr (Or.inr ⟨a, b, heq2, Or.inr (of_decide_eq_true hb)⟩)

private theorem headLeaf_var0_subst_bot {d : Nat}
    (hleft : ∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin d y → HasBotWithin d (y ⋅ z))
    {w : Term} (hvw : noVars w = true) (hbw : HasBotWithin d w) :
    ∀ (u : Term), headLeaf u = .var 0 → HasBotWithin d (subst (fun _ => w) u) := by
  intro u
  induction u with
  | s => intro h; cases h
  | var _ => intro _; exact hbw
  | app a b iha _ =>
    intro hl
    exact hleft (noVars_subst_closed hvw a) (noVars_subst_closed hvw b) (iha hl)

private theorem right_sink_from_left_sink {d : Nat}
    (hleft : ∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin d y → HasBotWithin d (y ⋅ z))
    {f w : Term} (hvf : noVars f = true) (hvw : noVars w = true) (hbw : HasBotWithin d w) :
    HasBotWithin (d + 1) (f ⋅ w) := by
  if h34 : evalHN (f ⋅ w) = .hn34 then
    have hvf_w : noVars (f ⋅ w) = true := (Bool.and_eq_true _ _).mpr ⟨hvf, hvw⟩
    exact hasBotWithin_mono (Nat.zero_le _) (closed_evalHN_hn34_hasBot0 hvf_w h34)
  else
    obtain ⟨uStar, hred_open, hcases⟩ := pure_s_head_escape hvf h34
    let σ : Nat → Term := fun _ => w
    have hred_closed : Reduces (f ⋅ w) (subst σ uStar) := by
      have hr := headReduces_to_reduces (subst_headReduces σ hred_open)
      have heq : subst σ (f ⋅ .var 0) = f ⋅ w := by
        change subst σ f ⋅ w = f ⋅ w
        rw [subst_closed_id σ hvf]
      rw [heq] at hr
      exact hr
    rcases hcases with hl0 | ⟨a, rfl, hla⟩ | ⟨a, b, rfl, hlab⟩
    · have hbd : HasBotWithin d (subst σ uStar) := headLeaf_var0_subst_bot hleft hvw hbw uStar hl0
      exact hasBotWithin_mono (Nat.le_succ d) (hasBotWithin_backward_reduces hred_closed hbd)
    · have hba : HasBotWithin d (subst σ a) := headLeaf_var0_subst_bot hleft hvw hbw a hla
      exact .bot_s1 hred_closed hba
    · rcases hlab with hla | hlb
      · have hba : HasBotWithin d (subst σ a) := headLeaf_var0_subst_bot hleft hvw hbw a hla
        exact .bot_s2_l hred_closed hba
      · have hbb : HasBotWithin d (subst σ b) := headLeaf_var0_subst_bot hleft hvw hbw b hlb
        exact .bot_s2_r hred_closed hbb

private theorem both_sink_laws :
    ∀ (d : Nat),
      (∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin d y → HasBotWithin d (y ⋅ z)) ∧
      (∀ {f w : Term}, noVars f = true → noVars w = true → HasBotWithin d w → HasBotWithin (d + 1) (f ⋅ w)) := by
  intro d
  induction d with
  | zero =>
    have hleft0 : ∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin 0 y → HasBotWithin 0 (y ⋅ z) := by
      intro y z hvy hvz hby
      cases hby with
      | bot_div hno =>
        have h34y : evalHN y = .hn34 := closed_not_hasHNF_evalHN_hn34 hvy hno
        have h34yz : evalHN (y ⋅ z) = .hn34 := by
          change deltaHN (evalHN y) (evalHN z) = .hn34
          rw [h34y]
          rfl
        exact closed_evalHN_hn34_hasBot0 ((Bool.and_eq_true _ _).mpr ⟨hvy, hvz⟩) h34yz
    exact ⟨hleft0, fun hvf hvw hbw => right_sink_from_left_sink hleft0 hvf hvw hbw⟩
  | succ d ih =>
    obtain ⟨ih_left, ih_right⟩ := ih
    have hleft_succ :
        ∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin (d + 1) y → HasBotWithin (d + 1) (y ⋅ z) := by
      intro y z hvy hvz hby
      have hvyz : noVars (y ⋅ z) = true := (Bool.and_eq_true _ _).mpr ⟨hvy, hvz⟩
      cases hby with
      | bot_div hno =>
        have h34y : evalHN y = .hn34 := closed_not_hasHNF_evalHN_hn34 hvy hno
        have h34yz : evalHN (y ⋅ z) = .hn34 := by
          change deltaHN (evalHN y) (evalHN z) = .hn34
          rw [h34y]; rfl
        exact hasBotWithin_mono (Nat.zero_le _) (closed_evalHN_hn34_hasBot0 hvyz h34yz)
      | @bot_s1 _ _ a hred hba =>
        exact .bot_s2_l (reduces_left hred z) hba
      | @bot_s2_l _ _ a b hred hba =>
        have hsab : noVars (S ⋅ a ⋅ b) = true := noVars_reduces hred hvy
        have ⟨hsa, hvb⟩ := (Bool.and_eq_true _ _).mp hsab
        have ⟨_, hva⟩ := (Bool.and_eq_true _ _).mp hsa
        have haz : HasBotWithin d (a ⋅ z) := ih_left hva hvz hba
        have haz_bz : HasBotWithin d ((a ⋅ z) ⋅ (b ⋅ z)) :=
          ih_left ((Bool.and_eq_true _ _).mpr ⟨hva, hvz⟩) ((Bool.and_eq_true _ _).mpr ⟨hvb, hvz⟩) haz
        have hstep_yz : Reduces (y ⋅ z) ((a ⋅ z) ⋅ (b ⋅ z)) :=
          reduces_trans (reduces_left hred z) (Reduces.next (Step.root a b z) (Reduces.refl _))
        exact hasBotWithin_mono (Nat.le_succ d) (hasBotWithin_backward_reduces hstep_yz haz_bz)
      | @bot_s2_r _ _ a b hred hbb =>
        have hsab : noVars (S ⋅ a ⋅ b) = true := noVars_reduces hred hvy
        have ⟨hsa, hvb⟩ := (Bool.and_eq_true _ _).mp hsab
        have ⟨_, hva⟩ := (Bool.and_eq_true _ _).mp hsa
        have hbz : HasBotWithin d (b ⋅ z) := ih_left hvb hvz hbb
        have haz_bz : HasBotWithin (d + 1) ((a ⋅ z) ⋅ (b ⋅ z)) :=
          ih_right ((Bool.and_eq_true _ _).mpr ⟨hva, hvz⟩) ((Bool.and_eq_true _ _).mpr ⟨hvb, hvz⟩) hbz
        have hstep_yz : Reduces (y ⋅ z) ((a ⋅ z) ⋅ (b ⋅ z)) :=
          reduces_trans (reduces_left hred z) (Reduces.next (Step.root a b z) (Reduces.refl _))
        exact hasBotWithin_backward_reduces hstep_yz haz_bz
    exact ⟨hleft_succ, fun hvf hvw hbw => right_sink_from_left_sink hleft_succ hvf hvw hbw⟩

/-- **Exact Left Sink Theorem (`HasBotWithin d y → HasBotWithin d (y ⋅ z)`)**. -/
theorem hasBotWithin_app_left {d : Nat} {y z : Term}
    (hvy : noVars y = true) (hvz : noVars z = true) (h : HasBotWithin d y) :
    HasBotWithin d (y ⋅ z) :=
  (both_sink_laws d).1 hvy hvz h

/-- **Exact Right Sink Theorem (`HasBotWithin d w → HasBotWithin (d + 1) (f ⋅ w)`)**. -/
theorem hasBotWithin_app_right {d : Nat} {f w : Term}
    (hvf : noVars f = true) (hvw : noVars w = true) (h : HasBotWithin d w) :
    HasBotWithin (d + 1) (f ⋅ w) :=
  (both_sink_laws d).2 hvf hvw h

theorem productive_subterm_closed {a b : Term}
    (hv : noVars (a ⋅ b) = true) (hp : Productive (a ⋅ b)) :
    Productive a ∧ Productive b := by
  have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
  refine ⟨fun ⟨d, ha⟩ => hp ⟨d, hasBotWithin_app_left hva hvb ha⟩,
          fun ⟨d, hb⟩ => hp ⟨d + 1, hasBotWithin_app_right hva hvb hb⟩⟩

/-! ## 3. Exact 39-State Algebra `A_P`, Soundness, and 44-State `A_P × A_SN` Stratification -/

inductive StateP where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p25 | p26 | p27 | p28 | p29 | p30 | p31 | p32 | p33 | p34 | p35 | p36 | p37 | p38
  deriving DecidableEq, Repr

def deltaP : StateP → StateP → StateP
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

private theorem s_row_StateP_0 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p0) y) z = deltaP (deltaP .p0 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_1 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p1) y) z = deltaP (deltaP .p1 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_2 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p2) y) z = deltaP (deltaP .p2 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_3 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p3) y) z = deltaP (deltaP .p3 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_4 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p4) y) z = deltaP (deltaP .p4 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_5 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p5) y) z = deltaP (deltaP .p5 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_6 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p6) y) z = deltaP (deltaP .p6 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_7 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p7) y) z = deltaP (deltaP .p7 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_8 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p8) y) z = deltaP (deltaP .p8 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_9 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p9) y) z = deltaP (deltaP .p9 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_10 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p10) y) z = deltaP (deltaP .p10 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_11 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p11) y) z = deltaP (deltaP .p11 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_12 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p12) y) z = deltaP (deltaP .p12 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_13 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p13) y) z = deltaP (deltaP .p13 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_14 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p14) y) z = deltaP (deltaP .p14 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_15 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p15) y) z = deltaP (deltaP .p15 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_16 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p16) y) z = deltaP (deltaP .p16 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_17 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p17) y) z = deltaP (deltaP .p17 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_18 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p18) y) z = deltaP (deltaP .p18 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_19 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p19) y) z = deltaP (deltaP .p19 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_20 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p20) y) z = deltaP (deltaP .p20 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_21 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p21) y) z = deltaP (deltaP .p21 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_22 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p22) y) z = deltaP (deltaP .p22 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_23 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p23) y) z = deltaP (deltaP .p23 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_24 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p24) y) z = deltaP (deltaP .p24 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_25 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p25) y) z = deltaP (deltaP .p25 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_26 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p26) y) z = deltaP (deltaP .p26 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_27 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p27) y) z = deltaP (deltaP .p27 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_28 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p28) y) z = deltaP (deltaP .p28 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_29 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p29) y) z = deltaP (deltaP .p29 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_30 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p30) y) z = deltaP (deltaP .p30 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_31 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p31) y) z = deltaP (deltaP .p31 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_32 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p32) y) z = deltaP (deltaP .p32 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_33 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p33) y) z = deltaP (deltaP .p33 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_34 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p34) y) z = deltaP (deltaP .p34 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_35 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p35) y) z = deltaP (deltaP .p35 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_36 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p36) y) z = deltaP (deltaP .p36 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_37 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p37) y) z = deltaP (deltaP .p37 z) (deltaP y z))) = true := rfl
private theorem s_row_StateP_38 : checkAll2_StateP (fun y z => decide (deltaP (deltaP (deltaP .p0 .p38) y) z = deltaP (deltaP .p38 z) (deltaP y z))) = true := rfl

theorem deltaP_s_law (x y z : StateP) :
    deltaP (deltaP (deltaP .p0 x) y) z = deltaP (deltaP x z) (deltaP y z) :=
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

private theorem deltaP_sink_chk :
    checkAll1_StateP (fun x => decide (deltaP .p37 x = .p37 ∧ deltaP x .p37 = .p37)) = true := rfl

theorem deltaP_sink (x : StateP) : deltaP .p37 x = .p37 ∧ deltaP x .p37 = .p37 :=
  of_decide_eq_true (checkAll1_StateP_sound _ deltaP_sink_chk x)

private theorem deltaP_hnf1_chk :
    checkAll1_StateP (fun x => decide (isAccP (deltaP .p0 x) = isAccP x)) = true := rfl

theorem deltaP_hnf1_iff (x : StateP) : isAccP (deltaP .p0 x) = isAccP x :=
  of_decide_eq_true (checkAll1_StateP_sound _ deltaP_hnf1_chk x)

private theorem deltaP_hnf2_chk :
    checkAll2_StateP (fun x y => decide (isAccP (deltaP (deltaP .p0 x) y) = (isAccP x && isAccP y))) = true := rfl

theorem deltaP_hnf2_iff (x y : StateP) :
    isAccP (deltaP (deltaP .p0 x) y) = (isAccP x && isAccP y) :=
  of_decide_eq_true (checkAll2_StateP_sound _ deltaP_hnf2_chk x y)

def evalP : Term → StateP
  | .s => .p0
  | .var _ => .p0
  | .app a b => deltaP (evalP a) (evalP b)

theorem evalP_step {a b : Term} (hs : Step a b) : evalP a = evalP b := by
  induction hs with
  | root x y z => exact deltaP_s_law (evalP x) (evalP y) (evalP z)
  | left _ ih => simp only [evalP, ih]
  | right _ ih => simp only [evalP, ih]

theorem evalP_reduces {a b : Term} (hr : Reduces a b) : evalP a = evalP b := by
  induction hr with
  | refl _ => rfl
  | next hs _ ih => exact (evalP_step hs).trans ih

theorem evalP_conv {a b : Term} (hc : ConvS a b) : evalP a = evalP b := by
  induction hc with
  | refl _ => rfl
  | step hs => exact evalP_step hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### 113-State `A_P × A_HN` Joint Invariant & Soundness of `A_P` -/

def isJointPH : StateP → StateHN → Bool
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

private def chkJointPHRow (p1 : StateP) : Bool :=
  checkAll1_StateHN (fun h1 =>
    !isJointPH p1 h1 ||
    checkAll1_StateP (fun p2 =>
      checkAll1_StateHN (fun h2 =>
        !isJointPH p2 h2 || isJointPH (deltaP p1 p2) (deltaHN h1 h2))))

private theorem jph_0 : chkJointPHRow .p0 = true := rfl
private theorem jph_1 : chkJointPHRow .p1 = true := rfl
private theorem jph_2 : chkJointPHRow .p2 = true := rfl
private theorem jph_3 : chkJointPHRow .p3 = true := rfl
private theorem jph_4 : chkJointPHRow .p4 = true := rfl
private theorem jph_5 : chkJointPHRow .p5 = true := rfl
private theorem jph_6 : chkJointPHRow .p6 = true := rfl
private theorem jph_7 : chkJointPHRow .p7 = true := rfl
private theorem jph_8 : chkJointPHRow .p8 = true := rfl
private theorem jph_9 : chkJointPHRow .p9 = true := rfl
private theorem jph_10 : chkJointPHRow .p10 = true := rfl
private theorem jph_11 : chkJointPHRow .p11 = true := rfl
private theorem jph_12 : chkJointPHRow .p12 = true := rfl
private theorem jph_13 : chkJointPHRow .p13 = true := rfl
private theorem jph_14 : chkJointPHRow .p14 = true := rfl
private theorem jph_15 : chkJointPHRow .p15 = true := rfl
private theorem jph_16 : chkJointPHRow .p16 = true := rfl
private theorem jph_17 : chkJointPHRow .p17 = true := rfl
private theorem jph_18 : chkJointPHRow .p18 = true := rfl
private theorem jph_19 : chkJointPHRow .p19 = true := rfl
private theorem jph_20 : chkJointPHRow .p20 = true := rfl
private theorem jph_21 : chkJointPHRow .p21 = true := rfl
private theorem jph_22 : chkJointPHRow .p22 = true := rfl
private theorem jph_23 : chkJointPHRow .p23 = true := rfl
private theorem jph_24 : chkJointPHRow .p24 = true := rfl
private theorem jph_25 : chkJointPHRow .p25 = true := rfl
private theorem jph_26 : chkJointPHRow .p26 = true := rfl
private theorem jph_27 : chkJointPHRow .p27 = true := rfl
private theorem jph_28 : chkJointPHRow .p28 = true := rfl
private theorem jph_29 : chkJointPHRow .p29 = true := rfl
private theorem jph_30 : chkJointPHRow .p30 = true := rfl
private theorem jph_31 : chkJointPHRow .p31 = true := rfl
private theorem jph_32 : chkJointPHRow .p32 = true := rfl
private theorem jph_33 : chkJointPHRow .p33 = true := rfl
private theorem jph_34 : chkJointPHRow .p34 = true := rfl
private theorem jph_35 : chkJointPHRow .p35 = true := rfl
private theorem jph_36 : chkJointPHRow .p36 = true := rfl
private theorem jph_37 : chkJointPHRow .p37 = true := rfl
private theorem jph_38 : chkJointPHRow .p38 = true := rfl

theorem isJointPH_closed {p1 p2 : StateP} {h1 h2 : StateHN}
    (hj1 : isJointPH p1 h1 = true) (hj2 : isJointPH p2 h2 = true) :
    isJointPH (deltaP p1 p2) (deltaHN h1 h2) = true := by
  have hrow : chkJointPHRow p1 = true :=
    match p1 with
    | .p0 => jph_0 | .p1 => jph_1 | .p2 => jph_2 | .p3 => jph_3 | .p4 => jph_4
    | .p5 => jph_5 | .p6 => jph_6 | .p7 => jph_7 | .p8 => jph_8 | .p9 => jph_9
    | .p10 => jph_10 | .p11 => jph_11 | .p12 => jph_12 | .p13 => jph_13 | .p14 => jph_14
    | .p15 => jph_15 | .p16 => jph_16 | .p17 => jph_17 | .p18 => jph_18 | .p19 => jph_19
    | .p20 => jph_20 | .p21 => jph_21 | .p22 => jph_22 | .p23 => jph_23 | .p24 => jph_24
    | .p25 => jph_25 | .p26 => jph_26 | .p27 => jph_27 | .p28 => jph_28 | .p29 => jph_29
    | .p30 => jph_30 | .p31 => jph_31 | .p32 => jph_32 | .p33 => jph_33 | .p34 => jph_34
    | .p35 => jph_35 | .p36 => jph_36 | .p37 => jph_37 | .p38 => jph_38
  have h1' := imp_bool hj1 (checkAll1_StateHN_sound _ hrow h1)
  have h2' := checkAll1_StateHN_sound _ (checkAll1_StateP_sound _ h1' p2) h2
  exact imp_bool hj2 h2'

theorem eval_isJointPH {t : Term} (hv : noVars t = true) :
    isJointPH (evalP t) (evalHN t) = true := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    have ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp hv
    exact isJointPH_closed (iha ha) (ihb hb)

private theorem jointPH_hn34_chk :
    checkAll1_StateP (fun p => !isJointPH p .hn34 || decide (p = .p37)) = true := rfl

theorem evalHN_eq_hn34_implies_evalP_eq_p37 {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) :
    evalP t = .p37 := by
  have hj : isJointPH (evalP t) .hn34 = true := by
    rw [← h34]; exact eval_isJointPH hv
  exact of_decide_eq_true (imp_bool hj (checkAll1_StateP_sound _ jointPH_hn34_chk (evalP t)))

theorem hasBotWithin_implies_evalP_p37 {d : Nat} {t : Term}
    (hv : noVars t = true) (hb : HasBotWithin d t) : evalP t = .p37 := by
  induction hb with
  | bot_div hno =>
    exact evalHN_eq_hn34_implies_evalP_eq_p37 hv (closed_not_hasHNF_evalHN_hn34 hv hno)
  | @bot_s1 _ u a hred _ ih =>
    have hva : noVars a = true := ((Bool.and_eq_true _ _).mp (noVars_reduces hred hv)).2
    have hpa : evalP a = .p37 := ih hva
    rw [evalP_reduces hred]
    change deltaP .p0 (evalP a) = .p37
    rw [hpa]; rfl
  | @bot_s2_l _ u a b hred _ ih =>
    have hvab := noVars_reduces hred hv
    have ⟨hsa, _⟩ := (Bool.and_eq_true _ _).mp hvab
    have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hsa).2
    have hpa : evalP a = .p37 := ih hva
    rw [evalP_reduces hred]
    change deltaP (deltaP .p0 (evalP a)) (evalP b) = .p37
    rw [hpa]
    exact (deltaP_sink (evalP b)).1
  | @bot_s2_r _ u a b hred _ ih =>
    have hvab := noVars_reduces hred hv
    have hvb : noVars b = true := ((Bool.and_eq_true _ _).mp hvab).2
    have hpb : evalP b = .p37 := ih hvb
    rw [evalP_reduces hred]
    change deltaP (deltaP .p0 (evalP a)) (evalP b) = .p37
    rw [hpb]
    exact (deltaP_sink (deltaP .p0 (evalP a))).2

/-- **Soundness of `A_P` (Direction 1 of Barendregt et al. Open Question 5)**:
    Every closed pure-`S` term `t` accepted by `A_P` (`evalP t ≠ .p37`) is productive! -/
theorem evalP_ne_p37_implies_productive {t : Term} (hv : noVars t = true) (hacc : evalP t ≠ .p37) :
    Productive t :=
  fun ⟨_, hb⟩ => hacc (hasBotWithin_implies_evalP_p37 hv hb)

/-- **Minimal Entry Reduction Theorem**:
    Completeness of `A_P` (`evalP t = .p37 → HasBot t` on all closed pure-`S` terms) is
    constructively equivalent to `HasBot (l ⋅ r)` purely on Minimal Entry Pairs
    (`evalP l ≠ .p37 ∧ evalP r ≠ .p37 ∧ deltaP (evalP l) (evalP r) = .p37`). -/
theorem minimal_entry_reduction_theorem :
    (∀ t, noVars t = true → evalP t = .p37 → HasBot t) ↔
    (∀ l r, noVars l = true → noVars r = true →
      evalP l ≠ .p37 → evalP r ≠ .p37 → deltaP (evalP l) (evalP r) = .p37 → HasBot (l ⋅ r)) := by
  constructor
  · intro hall l r hvl hvr _ _ hp
    exact hall (l ⋅ r) ((Bool.and_eq_true _ _).mpr ⟨hvl, hvr⟩) hp
  · intro hmep t hv hp
    induction t with
    | s => cases hp
    | var _ => cases hv
    | app l r ihl ihr =>
      have ⟨hvl, hvr⟩ := (Bool.and_eq_true _ _).mp hv
      if hpl : evalP l = .p37 then
        obtain ⟨d, hbl⟩ := ihl hvl hpl
        exact ⟨d, hasBotWithin_app_left hvl hvr hbl⟩
      else if hpr : evalP r = .p37 then
        obtain ⟨d, hbr⟩ := ihr hvr hpr
        exact ⟨d + 1, hasBotWithin_app_right hvl hvr hbr⟩
      else
        exact hmep l r hvl hvr hpl hpr hp

/-! ### 44-State `A_P × A_SN` Exact SN-Stratification & Non-`SN` HNF Rigidity -/

def isJointPS : StateP → StateSN → Bool
  | .p0, y => match y with | .sn0 => true | _ => false
  | .p1, y => match y with | .sn1 => true | _ => false
  | .p2, y => match y with | .sn2 => true | _ => false
  | .p3, y => match y with | .sn7 => true | _ => false
  | .p4, y => match y with | .sn3 => true | _ => false
  | .p5, y => match y with | .sn8 => true | _ => false
  | .p6, y => match y with | .sn9 => true | _ => false
  | .p7, y => match y with | .sn19 => true | _ => false
  | .p8, y => match y with | .sn4 => true | _ => false
  | .p9, y => match y with | .sn5 => true | _ => false
  | .p10, y => match y with | .sn10 => true | _ => false
  | .p11, y => match y with | .sn20 => true | _ => false
  | .p12, y => match y with | .sn11 => true | _ => false
  | .p13, y => match y with | .sn15 => true | _ => false
  | .p14, y => match y with | .sn22 => true | _ => false
  | .p15, y => match y with | .sn24 => true | _ => false
  | .p16, y => match y with | .sn27 => true | _ => false
  | .p17, y => match y with | .sn32 => true | _ => false
  | .p18, y => match y with | .sn6 => true | .sn38 => true | _ => false
  | .p19, y => match y with | .sn12 => true | _ => false
  | .p20, y => match y with | .sn21 => true | _ => false
  | .p21, y => match y with | .sn13 => true | _ => false
  | .p22, y => match y with | .sn16 => true | _ => false
  | .p23, y => match y with | .sn26 => true | _ => false
  | .p24, y => match y with | .sn29 => true | .sn38 => true | _ => false
  | .p25, y => match y with | .sn28 => true | _ => false
  | .p26, y => match y with | .sn33 => true | _ => false
  | .p27, y => match y with | .sn29 => true | .sn31 => true | _ => false
  | .p28, y => match y with | .sn36 => true | _ => false
  | .p29, y => match y with | .sn30 => true | .sn38 => true | _ => false
  | .p30, y => match y with | .sn14 => true | _ => false
  | .p31, y => match y with | .sn17 => true | _ => false
  | .p32, y => match y with | .sn23 => true | _ => false
  | .p33, y => match y with | .sn25 => true | .sn38 => true | _ => false
  | .p34, y => match y with | .sn34 => true | _ => false
  | .p35, y => match y with | .sn37 => true | _ => false
  | .p36, y => match y with | .sn35 => true | _ => false
  | .p37, y => match y with | .sn38 => true | _ => false
  | .p38, y => match y with | .sn18 => true | _ => false

private def chkJointPSRow (p1 : StateP) : Bool :=
  checkAll1_StateSN (fun s1 =>
    !isJointPS p1 s1 ||
    checkAll1_StateP (fun p2 =>
      checkAll1_StateSN (fun s2 =>
        !isJointPS p2 s2 || isJointPS (deltaP p1 p2) (deltaSN s1 s2))))

private theorem jps_0 : chkJointPSRow .p0 = true := rfl
private theorem jps_1 : chkJointPSRow .p1 = true := rfl
private theorem jps_2 : chkJointPSRow .p2 = true := rfl
private theorem jps_3 : chkJointPSRow .p3 = true := rfl
private theorem jps_4 : chkJointPSRow .p4 = true := rfl
private theorem jps_5 : chkJointPSRow .p5 = true := rfl
private theorem jps_6 : chkJointPSRow .p6 = true := rfl
private theorem jps_7 : chkJointPSRow .p7 = true := rfl
private theorem jps_8 : chkJointPSRow .p8 = true := rfl
private theorem jps_9 : chkJointPSRow .p9 = true := rfl
private theorem jps_10 : chkJointPSRow .p10 = true := rfl
private theorem jps_11 : chkJointPSRow .p11 = true := rfl
private theorem jps_12 : chkJointPSRow .p12 = true := rfl
private theorem jps_13 : chkJointPSRow .p13 = true := rfl
private theorem jps_14 : chkJointPSRow .p14 = true := rfl
private theorem jps_15 : chkJointPSRow .p15 = true := rfl
private theorem jps_16 : chkJointPSRow .p16 = true := rfl
private theorem jps_17 : chkJointPSRow .p17 = true := rfl
private theorem jps_18 : chkJointPSRow .p18 = true := rfl
private theorem jps_19 : chkJointPSRow .p19 = true := rfl
private theorem jps_20 : chkJointPSRow .p20 = true := rfl
private theorem jps_21 : chkJointPSRow .p21 = true := rfl
private theorem jps_22 : chkJointPSRow .p22 = true := rfl
private theorem jps_23 : chkJointPSRow .p23 = true := rfl
private theorem jps_24 : chkJointPSRow .p24 = true := rfl
private theorem jps_25 : chkJointPSRow .p25 = true := rfl
private theorem jps_26 : chkJointPSRow .p26 = true := rfl
private theorem jps_27 : chkJointPSRow .p27 = true := rfl
private theorem jps_28 : chkJointPSRow .p28 = true := rfl
private theorem jps_29 : chkJointPSRow .p29 = true := rfl
private theorem jps_30 : chkJointPSRow .p30 = true := rfl
private theorem jps_31 : chkJointPSRow .p31 = true := rfl
private theorem jps_32 : chkJointPSRow .p32 = true := rfl
private theorem jps_33 : chkJointPSRow .p33 = true := rfl
private theorem jps_34 : chkJointPSRow .p34 = true := rfl
private theorem jps_35 : chkJointPSRow .p35 = true := rfl
private theorem jps_36 : chkJointPSRow .p36 = true := rfl
private theorem jps_37 : chkJointPSRow .p37 = true := rfl
private theorem jps_38 : chkJointPSRow .p38 = true := rfl

theorem isJointPS_closed {p1 p2 : StateP} {s1 s2 : StateSN}
    (hj1 : isJointPS p1 s1 = true) (hj2 : isJointPS p2 s2 = true) :
    isJointPS (deltaP p1 p2) (deltaSN s1 s2) = true := by
  have hrow : chkJointPSRow p1 = true :=
    match p1 with
    | .p0 => jps_0 | .p1 => jps_1 | .p2 => jps_2 | .p3 => jps_3 | .p4 => jps_4
    | .p5 => jps_5 | .p6 => jps_6 | .p7 => jps_7 | .p8 => jps_8 | .p9 => jps_9
    | .p10 => jps_10 | .p11 => jps_11 | .p12 => jps_12 | .p13 => jps_13 | .p14 => jps_14
    | .p15 => jps_15 | .p16 => jps_16 | .p17 => jps_17 | .p18 => jps_18 | .p19 => jps_19
    | .p20 => jps_20 | .p21 => jps_21 | .p22 => jps_22 | .p23 => jps_23 | .p24 => jps_24
    | .p25 => jps_25 | .p26 => jps_26 | .p27 => jps_27 | .p28 => jps_28 | .p29 => jps_29
    | .p30 => jps_30 | .p31 => jps_31 | .p32 => jps_32 | .p33 => jps_33 | .p34 => jps_34
    | .p35 => jps_35 | .p36 => jps_36 | .p37 => jps_37 | .p38 => jps_38
  have h1' := imp_bool hj1 (checkAll1_StateSN_sound _ hrow s1)
  have h2' := checkAll1_StateSN_sound _ (checkAll1_StateP_sound _ h1' p2) s2
  exact imp_bool hj2 h2'

theorem eval_isJointPS {t : Term} (hv : noVars t = true) :
    isJointPS (evalP t) (evalSN t) = true := by
  induction t with
  | s => rfl
  | var _ => cases hv
  | app a b iha ihb =>
    have ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp hv
    exact isJointPS_closed (iha ha) (ihb hb)

def isNonSNAccStateP : StateP → Bool
  | .p18 => true | .p24 => true | .p29 => true | .p33 => true
  | _ => false

private theorem jointPS_34_sn_chk :
    checkAll1_StateP (fun p =>
      !isJointPS p .sn38 || (decide (p = .p37) || isNonSNAccStateP p)) = true := rfl

/-- **34-of-38 Strong Normalization Theorem**:
    Every closed pure-`S` term accepted by `A_P` outside `{.p18, .p24, .p29, .p33}` is
    100% Strongly Normalizing (`evalSN t ≠ .sn38`) and reduces to a Closed Normal Form (`CNF`)! -/
theorem evalP_34_states_sn {t : Term} (hv : noVars t = true)
    (hacc : evalP t ≠ .p37) (hnot4 : isNonSNAccStateP (evalP t) = false) :
    evalSN t ≠ .sn38 ∧ StrongNormalizing t ∧ ∃ c : CNF, Reduces t c.toTerm := by
  have hsn_ne : evalSN t ≠ .sn38 := by
    intro h38
    have hj : isJointPS (evalP t) .sn38 = true := by
      rw [← h38]; exact eval_isJointPS hv
    have hchk := imp_bool hj (checkAll1_StateP_sound _ jointPS_34_sn_chk (evalP t))
    rw [decide_eq_false hacc, Bool.false_or, hnot4] at hchk
    cases hchk
  exact ⟨hsn_ne, (waldmann_theorem_9 hv).1.mpr hsn_ne, closed_evalSN_ne_sn38_reduces_cnf hv hsn_ne⟩

def isP18_24_33 : StateP → Bool
  | .p18 => true | .p24 => true | .p33 => true
  | _ => false

private def chkNonSN18_24_33Row (p1 : StateP) : Bool :=
  checkAll1_StateSN (fun s1 =>
    !isJointPS p1 s1 ||
    checkAll1_StateP (fun p2 =>
      checkAll1_StateSN (fun s2 =>
        !isJointPS p2 s2 ||
        (!(isP18_24_33 (deltaP p1 p2) && decide (deltaSN s1 s2 = .sn38)) ||
         (decide (s1 ≠ .sn38) && !isS2StateSN s1)))))

private theorem nsn_0 : chkNonSN18_24_33Row .p0 = true := rfl
private theorem nsn_1 : chkNonSN18_24_33Row .p1 = true := rfl
private theorem nsn_2 : chkNonSN18_24_33Row .p2 = true := rfl
private theorem nsn_3 : chkNonSN18_24_33Row .p3 = true := rfl
private theorem nsn_4 : chkNonSN18_24_33Row .p4 = true := rfl
private theorem nsn_5 : chkNonSN18_24_33Row .p5 = true := rfl
private theorem nsn_6 : chkNonSN18_24_33Row .p6 = true := rfl
private theorem nsn_7 : chkNonSN18_24_33Row .p7 = true := rfl
private theorem nsn_8 : chkNonSN18_24_33Row .p8 = true := rfl
private theorem nsn_9 : chkNonSN18_24_33Row .p9 = true := rfl
private theorem nsn_10 : chkNonSN18_24_33Row .p10 = true := rfl
private theorem nsn_11 : chkNonSN18_24_33Row .p11 = true := rfl
private theorem nsn_12 : chkNonSN18_24_33Row .p12 = true := rfl
private theorem nsn_13 : chkNonSN18_24_33Row .p13 = true := rfl
private theorem nsn_14 : chkNonSN18_24_33Row .p14 = true := rfl
private theorem nsn_15 : chkNonSN18_24_33Row .p15 = true := rfl
private theorem nsn_16 : chkNonSN18_24_33Row .p16 = true := rfl
private theorem nsn_17 : chkNonSN18_24_33Row .p17 = true := rfl
private theorem nsn_18 : chkNonSN18_24_33Row .p18 = true := rfl
private theorem nsn_19 : chkNonSN18_24_33Row .p19 = true := rfl
private theorem nsn_20 : chkNonSN18_24_33Row .p20 = true := rfl
private theorem nsn_21 : chkNonSN18_24_33Row .p21 = true := rfl
private theorem nsn_22 : chkNonSN18_24_33Row .p22 = true := rfl
private theorem nsn_23 : chkNonSN18_24_33Row .p23 = true := rfl
private theorem nsn_24 : chkNonSN18_24_33Row .p24 = true := rfl
private theorem nsn_25 : chkNonSN18_24_33Row .p25 = true := rfl
private theorem nsn_26 : chkNonSN18_24_33Row .p26 = true := rfl
private theorem nsn_27 : chkNonSN18_24_33Row .p27 = true := rfl
private theorem nsn_28 : chkNonSN18_24_33Row .p28 = true := rfl
private theorem nsn_29 : chkNonSN18_24_33Row .p29 = true := rfl
private theorem nsn_30 : chkNonSN18_24_33Row .p30 = true := rfl
private theorem nsn_31 : chkNonSN18_24_33Row .p31 = true := rfl
private theorem nsn_32 : chkNonSN18_24_33Row .p32 = true := rfl
private theorem nsn_33 : chkNonSN18_24_33Row .p33 = true := rfl
private theorem nsn_34 : chkNonSN18_24_33Row .p34 = true := rfl
private theorem nsn_35 : chkNonSN18_24_33Row .p35 = true := rfl
private theorem nsn_36 : chkNonSN18_24_33Row .p36 = true := rfl
private theorem nsn_37 : chkNonSN18_24_33Row .p37 = true := rfl
private theorem nsn_38 : chkNonSN18_24_33Row .p38 = true := rfl

private theorem cnf_s2_isS2_chk :
    checkAll2_StateSN (fun a b =>
      decide (a ≠ .sn38 → b ≠ .sn38 → isS2StateSN (deltaSN (deltaSN .sn0 a) b) = true)) = true := rfl

/-- **Non-`SN` HNF Rigidity Theorem on `{.p18, .p24, .p33}`**:
    Whenever a closed application `l ⋅ r` has `evalSN (l ⋅ r) = .sn38` and `evalP (l ⋅ r) ∈ {.p18, .p24, .p33}`,
    its left operand `l` is Strongly Normalizing (`evalSN l ≠ .sn38`) and reduces to either `S` or `S ⋅ u.toTerm`
    (`u : CNF`), so `l ⋅ r` reduces **strictly inside `l`** (zero root contractions!) to an HNF! -/
theorem nonSN_p18_p24_p33_reduces_hnf_no_root {l r : Term}
    (hvl : noVars l = true) (hvr : noVars r = true)
    (hp : isP18_24_33 (evalP (l ⋅ r)) = true) (hs38 : evalSN (l ⋅ r) = .sn38) :
    (Reduces l S ∧ Reduces (l ⋅ r) (S ⋅ r)) ∨
    (∃ u : CNF, Reduces l (S ⋅ u.toTerm) ∧ Reduces (l ⋅ r) (S ⋅ u.toTerm ⋅ r)) := by
  have hj1 := eval_isJointPS hvl
  have hj2 := eval_isJointPS hvr
  have hrow : chkNonSN18_24_33Row (evalP l) = true :=
    match evalP l with
    | .p0 => nsn_0 | .p1 => nsn_1 | .p2 => nsn_2 | .p3 => nsn_3 | .p4 => nsn_4
    | .p5 => nsn_5 | .p6 => nsn_6 | .p7 => nsn_7 | .p8 => nsn_8 | .p9 => nsn_9
    | .p10 => nsn_10 | .p11 => nsn_11 | .p12 => nsn_12 | .p13 => nsn_13 | .p14 => nsn_14
    | .p15 => nsn_15 | .p16 => nsn_16 | .p17 => nsn_17 | .p18 => nsn_18 | .p19 => nsn_19
    | .p20 => nsn_20 | .p21 => nsn_21 | .p22 => nsn_22 | .p23 => nsn_23 | .p24 => nsn_24
    | .p25 => nsn_25 | .p26 => nsn_26 | .p27 => nsn_27 | .p28 => nsn_28 | .p29 => nsn_29
    | .p30 => nsn_30 | .p31 => nsn_31 | .p32 => nsn_32 | .p33 => nsn_33 | .p34 => nsn_34
    | .p35 => nsn_35 | .p36 => nsn_36 | .p37 => nsn_37 | .p38 => nsn_38
  have h1 := imp_bool hj1 (checkAll1_StateSN_sound _ hrow (evalSN l))
  have h2 := imp_bool hj2 (checkAll1_StateSN_sound _ (checkAll1_StateP_sound _ h1 (evalP r)) (evalSN r))
  have hcond : (isP18_24_33 (deltaP (evalP l) (evalP r)) && decide (deltaSN (evalSN l) (evalSN r) = .sn38)) = true :=
    (Bool.and_eq_true _ _).mpr ⟨hp, decide_eq_true hs38⟩
  have hres := imp_bool hcond h2
  have hsl_ne : evalSN l ≠ .sn38 := of_decide_eq_true (and_left hres)
  have hnot_s2 : (!isS2StateSN (evalSN l)) = true := and_right hres
  obtain ⟨c, hred_l⟩ := closed_evalSN_ne_sn38_reduces_cnf hvl hsl_ne
  cases c with
  | s =>
    exact Or.inl ⟨hred_l, reduces_left hred_l r⟩
  | s1 u =>
    exact Or.inr ⟨u, hred_l, reduces_left hred_l r⟩
  | s2 a b =>
    exfalso
    have heq_sn : evalSN l = deltaSN (deltaSN .sn0 (evalSN a.toTerm)) (evalSN b.toTerm) :=
      evalSN_reduces hred_l
    have his_s2 : isS2StateSN (evalSN l) = true := by
      rw [heq_sn]
      exact (of_decide_eq_true (checkAll2_StateSN_sound _ cnf_s2_isS2_chk (evalSN a.toTerm) (evalSN b.toTerm)))
        a.evalSN_ne_sn38 b.evalSN_ne_sn38
    rw [his_s2] at hnot_s2
    cases hnot_s2

/-- **Unique Non-`SN` Productive Root-Redex Theorem**:
    If any closed productive root redex `t = S ⋅ x ⋅ y ⋅ z` (`evalP t ≠ .p37`) is not Strongly
    Normalizing (`evalSN t = .sn38`), then `evalP t = .p29` necessarily! -/
theorem unique_nonSN_productive_root_redex_state {x y z : Term}
    (hv : noVars (S ⋅ x ⋅ y ⋅ z) = true)
    (hacc : evalP (S ⋅ x ⋅ y ⋅ z) ≠ .p37)
    (hs38 : evalSN (S ⋅ x ⋅ y ⋅ z) = .sn38) :
    evalP (S ⋅ x ⋅ y ⋅ z) = .p29 := by
  have ⟨hsxy, hvz⟩ := (Bool.and_eq_true _ _).mp hv
  if hp29 : evalP (S ⋅ x ⋅ y ⋅ z) = .p29 then
    exact hp29
  else
    exfalso
    if hp18_24_33 : isP18_24_33 (evalP (S ⋅ x ⋅ y ⋅ z)) = true then
      rcases nonSN_p18_p24_p33_reduces_hnf_no_root hsxy hvz hp18_24_33 hs38 with ⟨hred_s, _⟩ | ⟨u, hred_s1, _⟩
      · exact (no_dynamic_hnf1 S x y S).2 hred_s
      · exact (no_dynamic_hnf1 S x y u.toTerm).1 hred_s1
    else
      have hnot4 : isNonSNAccStateP (evalP (S ⋅ x ⋅ y ⋅ z)) = false := by
        cases hq : evalP (S ⋅ x ⋅ y ⋅ z) <;> rw [hq] at hp29 hp18_24_33 <;>
          first | rfl | exact False.elim (hp29 rfl) | exact False.elim (hp18_24_33 rfl)
      exact (evalP_34_states_sn hv hacc hnot4).1 hs38

/-! ## 4. Exact Last-Head-Step Law & Leftmost-vs-Rightmost Böhm-Game Asymmetry Theorem -/

theorem headStep_spineLen_ge_3 {a b : Term} (hs : HeadStep a b) : 3 ≤ spineLen a := by
  induction hs with
  | root x y z => exact Nat.le_refl 3
  | left _ ih => exact Nat.le_trans ih (Nat.le_add_left _ 1)

theorem headStep_spineLen_rhs_ge_2 {a b : Term} (hs : HeadStep a b) : 2 ≤ spineLen b := by
  induction hs with
  | root x y z =>
    change 2 ≤ 1 + (1 + spineLen x)
    rw [← Nat.add_assoc 1 1 (spineLen x)]
    exact Nat.le_add_right 2 (spineLen x)
  | left _ ih =>
    exact Nat.le_trans ih (Nat.le_add_left _ 1)

theorem closed_spineLen_zero_eq_s {t : Term} (hv : noVars t = true) (hsl : spineLen t = 0) :
    t = S := by
  cases t with
  | s => rfl
  | var _ => cases hv
  | app a b =>
    exfalso
    change 1 + spineLen a = 0 at hsl
    rw [Nat.add_comm 1 (spineLen a)] at hsl
    cases hsl

/-- **Exact Last-Head-Step Law of Pure `S`**:
    Every head-normalization `t →_h* h` starting from `spineLen t ≥ 3` (`noVars t = true`)
    ends at a `2`-HNF of the rigid symmetric form `h = S ⋅ a ⋅ (y ⋅ a)` (`HeadReduces t (S ⋅ S ⋅ y ⋅ a)`). -/
theorem last_headStep_s2_law {t h : Term}
    (hv : noVars t = true) (hsl : 3 ≤ spineLen t)
    (hred : HeadReduces t h) (hhnf : spineLen h ≤ 2) :
    ∃ y a, HeadReduces t (S ⋅ S ⋅ y ⋅ a) ∧ h = S ⋅ a ⋅ (y ⋅ a) := by
  induction hred with
  | refl _ =>
    exfalso
    have hbad : 1 + (1 + 1) ≤ 1 + (1 + 0) := Nat.le_trans hsl hhnf
    exact Nat.not_succ_le_zero 0 (one_add_le (one_add_le hbad))
  | @next u m _ hs hrest ih =>
    cases hrest with
    | refl _ =>
      cases hs with
      | root x y a =>
        change 1 + (1 + spineLen x) ≤ 1 + (1 + 0) at hhnf
        have hx0 : spineLen x = 0 :=
          Nat.eq_zero_of_le_zero (one_add_le (one_add_le hhnf))
        have ⟨hsxy, _⟩ := (Bool.and_eq_true _ _).mp hv
        have ⟨hsx, _⟩ := (Bool.and_eq_true _ _).mp hsxy
        have hvx : noVars x = true := ((Bool.and_eq_true _ _).mp hsx).2
        have hx_eq := closed_spineLen_zero_eq_s hvx hx0
        subst hx_eq
        exact ⟨y, a, HeadReduces.refl _, rfl⟩
      | @left l l' r hl =>
        exfalso
        have hge2 : 2 ≤ spineLen l' := headStep_spineLen_rhs_ge_2 hl
        have hge3 : 1 + (1 + 1) ≤ 1 + spineLen l' := Nat.add_le_add_left hge2 1
        have hbad : 1 + (1 + 1) ≤ 1 + (1 + 0) := Nat.le_trans hge3 hhnf
        exact Nat.not_succ_le_zero 0 (one_add_le (one_add_le hbad))
    | @next _ w _ hs2 hrest2 =>
      have hvm : noVars m = true := noVars_step (headStep_to_step hs) hv
      have hslm : 3 ≤ spineLen m := headStep_spineLen_ge_3 hs2
      obtain ⟨y, a, hm_to, hh_eq⟩ := ih hvm hslm hhnf
      exact ⟨y, a, HeadReduces.next hs hm_to, hh_eq⟩

/-! ### Deterministic Leftmost (`stepBohmLeft`) vs Rightmost (`stepBohmRight`) Böhm Strategies -/

theorem headStepOpt_complete {a b : Term} (hs : HeadStep a b) : headStepOpt a = some b := by
  induction hs with
  | root x y z => rfl
  | @left l l' r hl ih =>
    simp only [headStepOpt]
    cases hr : rootRedexOpt l r with
    | some u =>
      obtain ⟨x, y, hl_eq, _⟩ := rootRedexOpt_some hr
      subst hl_eq
      cases hl with
      | left hll =>
        cases hll with
        | left hlll => cases hlll
    | none =>
      rw [ih]

theorem headStep_det {a b1 b2 : Term} (h1 : HeadStep a b1) (h2 : HeadStep a b2) : b1 = b2 := by
  have e1 := headStepOpt_complete h1
  have e2 := headStepOpt_complete h2
  rw [e1] at e2
  injection e2

theorem headReduces_det_none {a h1 h2 : Term}
    (hr1 : HeadReduces a h1) (hn1 : headStepOpt h1 = none)
    (hr2 : HeadReduces a h2) (hn2 : headStepOpt h2 = none) : h1 = h2 := by
  induction hr1 with
  | refl _ =>
    cases hr2 with
    | refl _ => rfl
    | next hs2 _ =>
      rw [headStepOpt_complete hs2] at hn1
      cases hn1
  | @next _ m _ hs1 _ ih =>
    cases hr2 with
    | refl _ =>
      rw [headStepOpt_complete hs1] at hn2
      cases hn2
    | @next _ m2 _ hs2 hrest2 =>
      have hm_eq := headStep_det hs1 hs2
      subst hm_eq
      exact ih hn1 hrest2

theorem closed_hnf_headStepOpt_none {h : Term} (_ : noVars h = true) (hsl : spineLen h ≤ 2) :
    headStepOpt h = none := by
  cases hh : headStepOpt h with
  | none => rfl
  | some h' =>
    exfalso
    have hge3 := headStep_spineLen_ge_3 (headStepOpt_some hh)
    exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_trans hge3 hsl)))

theorem headNormalize_eq_of_headReduces_none {t h : Term}
    (hv : noVars t = true) (hval : evalHN t ≠ .hn34)
    (hred : HeadReduces t h) (hnone : headStepOpt h = none) :
    headNormalize t = h := by
  obtain ⟨hred_norm, hvh, hsl_norm⟩ := headNormalize_reduces_hnf hv hval
  exact headReduces_det_none hred_norm (closed_hnf_headStepOpt_none hvh hsl_norm) hred hnone

def selectBohmChildRight (h : Term) : Option Term :=
  match h with
  | .app .s a => if evalP a == .p37 then some a else none
  | .app (.app .s a) b =>
    if evalP b == .p37 then some b
    else if evalP a == .p37 then some a
    else none
  | _ => none

def selectBohmChildLeft (h : Term) : Option Term :=
  match h with
  | .app .s a => if evalP a == .p37 then some a else none
  | .app (.app .s a) b =>
    if evalP a == .p37 then some a
    else if evalP b == .p37 then some b
    else none
  | _ => none

def stepBohmRight (t : Term) : Option Term :=
  if evalHN t == .hn34 then none
  else selectBohmChildRight (headNormalize t)

def stepBohmLeft (t : Term) : Option Term :=
  if evalHN t == .hn34 then none
  else selectBohmChildLeft (headNormalize t)

def iterBohmRight : Nat → Term → Option Term
  | 0, t => some t
  | k + 1, t =>
    match stepBohmRight t with
    | none => none
    | some t' => iterBohmRight k t'

def iterBohmLeft : Nat → Term → Option Term
  | 0, t => some t
  | k + 1, t =>
    match stepBohmLeft t with
    | none => none
    | some t' => iterBohmLeft k t'

theorem iterBohmLeft_add (m n : Nat) (t : Term) :
    iterBohmLeft (m + n) t =
      match iterBohmLeft m t with
      | none => none
      | some u => iterBohmLeft n u := by
  induction m generalizing t with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [iterBohmLeft]
    cases stepBohmLeft t with
    | none => rfl
    | some t' => exact ih t'

theorem iterBohmRight_sound :
    ∀ (d : Nat) {t u : Term},
      noVars t = true →
      iterBohmRight d t = some u →
      evalHN u = .hn34 →
      HasBotWithin d t := by
  intro d
  induction d with
  | zero =>
    intro t u hv hiter h34
    injection hiter with htu
    subst htu
    exact closed_evalHN_hn34_hasBot0 hv h34
  | succ d ih =>
    intro t u hv hiter h34
    simp only [iterBohmRight, stepBohmRight] at hiter
    cases h_eq34 : (evalHN t == .hn34) with
    | true =>
      rw [h_eq34, if_true_eq_true] at hiter
      cases hiter
    | false =>
      rw [h_eq34, if_false_eq_true] at hiter
      have hne34 : evalHN t ≠ .hn34 := by
        intro heq; rw [heq] at h_eq34; cases h_eq34
      obtain ⟨hred, hvh, hsl⟩ := headNormalize_reduces_hnf hv hne34
      have hnone := closed_hnf_headStepOpt_none hvh hsl
      rcases headStepOpt_none_closed hvh hnone with heq_s | ⟨a, heq1⟩ | ⟨a, b, heq2⟩
      · rw [heq_s] at hiter; cases hiter
      · rw [heq1] at hiter hred hvh
        have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hvh).2
        change (match (if evalP a == .p37 then some a else none) with | none => none | some t' => iterBohmRight d t') = some u at hiter
        cases hpa : (evalP a == .p37) with
        | false => rw [hpa, if_false_eq_true] at hiter; cases hiter
        | true =>
          rw [hpa, if_true_eq_true] at hiter
          exact .bot_s1 (headReduces_to_reduces hred) (ih hva hiter h34)
      · rw [heq2] at hiter hred hvh
        have ⟨hsa, hvb⟩ := (Bool.and_eq_true _ _).mp hvh
        have hva : noVars a = true := ((Bool.and_eq_true _ _).mp hsa).2
        change (match (if evalP b == .p37 then some b else if evalP a == .p37 then some a else none) with | none => none | some t' => iterBohmRight d t') = some u at hiter
        cases hpb : (evalP b == .p37) with
        | true =>
          rw [hpb, if_true_eq_true] at hiter
          exact .bot_s2_r (headReduces_to_reduces hred) (ih hvb hiter h34)
        | false =>
          rw [hpb, if_false_eq_true] at hiter
          cases hpa : (evalP a == .p37) with
          | false => rw [hpa, if_false_eq_true] at hiter; cases hiter
          | true =>
            rw [hpa, if_true_eq_true] at hiter
            exact .bot_s2_l (headReduces_to_reduces hred) (ih hva hiter h34)

/-! ### Explicit 8-Leaf Witness `L_loop = S ⋅ T ⋅ S ⋅ T ⋅ T`: Rightmost Wins in 4 Steps, Leftmost Diverges Forever -/

def T_comb : Term := S ⋅ S
def W0_comb : Term := S ⋅ T_comb ⋅ T_comb
def K_base : Term := (T_comb ⋅ (S ⋅ T_comb)) ⋅ T_comb
def L_loop : Term := S ⋅ T_comb ⋅ S ⋅ T_comb ⋅ T_comb

def iterT : Nat → Term
  | 0 => K_base
  | n + 1 => T_comb ⋅ iterT n

theorem noVars_iterT (n : Nat) : noVars (iterT n) = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact (Bool.and_eq_true _ _).mpr ⟨rfl, ih⟩

theorem evalP_iterT (n : Nat) : evalP (iterT n) = .p33 := by
  induction n with
  | zero => rfl
  | succ _ ih =>
    change deltaP .p1 (evalP (iterT _)) = .p33
    rw [ih]; rfl

theorem evalHN_iterT_zero : evalHN (iterT 0) = .hn10 := rfl

theorem evalHN_iterT_succ : ∀ (n : Nat), evalHN (iterT (n + 1)) = .hn13
  | 0 => rfl
  | n + 1 => by
    have ih := evalHN_iterT_succ n
    change deltaHN .hn1 (evalHN (iterT (n + 1))) = .hn13
    rw [ih]; rfl

theorem leaves_iterT_ge (n : Nat) : n + 7 ≤ leaves (iterT n) := by
  induction n with
  | zero => exact Nat.le_refl 7
  | succ n ih =>
    change (n + 1) + 7 ≤ 2 + leaves (iterT n)
    have h1 : (n + 1) + 7 = 1 + (n + 7) := by
      rw [Nat.add_comm n 1, Nat.add_assoc 1 n 7]
    rw [h1]
    exact Nat.add_le_add (Nat.le_succ 1) ih

private theorem evalHN_iterT_app_ne_hn34 (m n : Nat) :
    evalHN (iterT m ⋅ iterT n) ≠ .hn34 := by
  cases m with
  | zero =>
    cases n with
    | zero => intro h; cases h
    | succ n' =>
      change deltaHN (evalHN (iterT 0)) (evalHN (iterT (n' + 1))) ≠ .hn34
      rw [evalHN_iterT_zero, evalHN_iterT_succ n']
      intro h; cases h
  | succ m' =>
    cases n with
    | zero =>
      change deltaHN (evalHN (iterT (m' + 1))) (evalHN (iterT 0)) ≠ .hn34
      rw [evalHN_iterT_succ m', evalHN_iterT_zero]
      intro h; cases h
    | succ n' =>
      change deltaHN (evalHN (iterT (m' + 1))) (evalHN (iterT (n' + 1))) ≠ .hn34
      rw [evalHN_iterT_succ m', evalHN_iterT_succ n']
      intro h; cases h

private theorem evalHN_W0_iterT_ne_hn34 (n : Nat) :
    evalHN (W0_comb ⋅ iterT n) ≠ .hn34 := by
  cases n with
  | zero => intro h; cases h
  | succ n' =>
    change deltaHN .hn16 (evalHN (iterT (n' + 1))) ≠ .hn34
    rw [evalHN_iterT_succ n']
    intro h; cases h

private theorem selectBohmChildLeft_s2 (a b : Term) :
    selectBohmChildLeft (S ⋅ a ⋅ b) =
      (if evalP a == .p37 then some a else if evalP b == .p37 then some b else none) := rfl

private theorem stepBohmLeft_iterT_succ (m n : Nat) :
    stepBohmLeft (iterT (m + 1) ⋅ iterT n) = some (iterT m ⋅ iterT n) := by
  have hv : noVars (iterT (m + 1) ⋅ iterT n) = true :=
    (Bool.and_eq_true _ _).mpr ⟨noVars_iterT (m + 1), noVars_iterT n⟩
  have hne34 : evalHN (iterT (m + 1) ⋅ iterT n) ≠ .hn34 := evalHN_iterT_app_ne_hn34 (m + 1) n
  have hred : HeadReduces (iterT (m + 1) ⋅ iterT n) (S ⋅ iterT n ⋅ (iterT m ⋅ iterT n)) :=
    HeadReduces.next (HeadStep.root S (iterT m) (iterT n)) (HeadReduces.refl _)
  have hnone : headStepOpt (S ⋅ iterT n ⋅ (iterT m ⋅ iterT n)) = none := rfl
  have hnorm := headNormalize_eq_of_headReduces_none hv hne34 hred hnone
  have hb34 : (evalHN (iterT (m + 1) ⋅ iterT n) == .hn34) = false := by
    cases h : (evalHN (iterT (m + 1) ⋅ iterT n) == .hn34) with
    | false => rfl
    | true => exfalso; exact hne34 (of_decide_eq_true h)
  unfold stepBohmLeft
  rw [hb34, if_false_eq_true, hnorm, selectBohmChildLeft_s2]
  have hp_left : (evalP (iterT n) == .p37) = false := by rw [evalP_iterT n]; rfl
  have hp_right : (evalP (iterT m ⋅ iterT n) == .p37) = true := by
    change (deltaP (evalP (iterT m)) (evalP (iterT n)) == .p37) = true
    rw [evalP_iterT m, evalP_iterT n]; rfl
  rw [hp_left, if_false_eq_true, hp_right, if_true_eq_true]

private theorem iterBohmLeft_unwind_iterT (m n : Nat) :
    iterBohmLeft m (iterT m ⋅ iterT n) = some (iterT 0 ⋅ iterT n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [iterBohmLeft, stepBohmLeft_iterT_succ m n]
    exact ih

private theorem stepBohmLeft_iterT0 (n : Nat) :
    stepBohmLeft (iterT 0 ⋅ iterT n) = some (W0_comb ⋅ iterT n) := by
  have hv : noVars (iterT 0 ⋅ iterT n) = true :=
    (Bool.and_eq_true _ _).mpr ⟨rfl, noVars_iterT n⟩
  have hne34 : evalHN (iterT 0 ⋅ iterT n) ≠ .hn34 := evalHN_iterT_app_ne_hn34 0 n
  have hs1 : HeadStep (iterT 0 ⋅ iterT n) ((S ⋅ T_comb ⋅ W0_comb) ⋅ iterT n) :=
    HeadStep.left (HeadStep.root S (S ⋅ T_comb) T_comb)
  have hs2 : HeadStep ((S ⋅ T_comb ⋅ W0_comb) ⋅ iterT n) ((T_comb ⋅ iterT n) ⋅ (W0_comb ⋅ iterT n)) :=
    HeadStep.root T_comb W0_comb (iterT n)
  have hs3 : HeadStep ((T_comb ⋅ iterT n) ⋅ (W0_comb ⋅ iterT n)) (S ⋅ (W0_comb ⋅ iterT n) ⋅ (iterT n ⋅ (W0_comb ⋅ iterT n))) :=
    HeadStep.root S (iterT n) (W0_comb ⋅ iterT n)
  have hred : HeadReduces (iterT 0 ⋅ iterT n) (S ⋅ (W0_comb ⋅ iterT n) ⋅ (iterT n ⋅ (W0_comb ⋅ iterT n))) :=
    HeadReduces.next hs1 (HeadReduces.next hs2 (HeadReduces.next hs3 (HeadReduces.refl _)))
  have hnone : headStepOpt (S ⋅ (W0_comb ⋅ iterT n) ⋅ (iterT n ⋅ (W0_comb ⋅ iterT n))) = none := rfl
  have hnorm := headNormalize_eq_of_headReduces_none hv hne34 hred hnone
  have hb34 : (evalHN (iterT 0 ⋅ iterT n) == .hn34) = false := by
    cases h : (evalHN (iterT 0 ⋅ iterT n) == .hn34) with
    | false => rfl
    | true => exfalso; exact hne34 (of_decide_eq_true h)
  unfold stepBohmLeft
  rw [hb34, if_false_eq_true, hnorm, selectBohmChildLeft_s2]
  have hp_left : (evalP (W0_comb ⋅ iterT n) == .p37) = true := by
    change (deltaP .p14 (evalP (iterT n)) == .p37) = true
    rw [evalP_iterT n]; rfl
  rw [hp_left, if_true_eq_true]

private theorem stepBohmLeft_W0 (n : Nat) :
    stepBohmLeft (W0_comb ⋅ iterT n) = some (iterT n ⋅ iterT (n + 1)) := by
  have hv : noVars (W0_comb ⋅ iterT n) = true :=
    (Bool.and_eq_true _ _).mpr ⟨rfl, noVars_iterT n⟩
  have hne34 : evalHN (W0_comb ⋅ iterT n) ≠ .hn34 := evalHN_W0_iterT_ne_hn34 n
  have hs1 : HeadStep (W0_comb ⋅ iterT n) ((T_comb ⋅ iterT n) ⋅ (T_comb ⋅ iterT n)) :=
    HeadStep.root T_comb T_comb (iterT n)
  have hs2 : HeadStep ((T_comb ⋅ iterT n) ⋅ (T_comb ⋅ iterT n)) (S ⋅ (T_comb ⋅ iterT n) ⋅ (iterT n ⋅ (T_comb ⋅ iterT n))) :=
    HeadStep.root S (iterT n) (T_comb ⋅ iterT n)
  have hred : HeadReduces (W0_comb ⋅ iterT n) (S ⋅ iterT (n + 1) ⋅ (iterT n ⋅ iterT (n + 1))) :=
    HeadReduces.next hs1 (HeadReduces.next hs2 (HeadReduces.refl _))
  have hnone : headStepOpt (S ⋅ iterT (n + 1) ⋅ (iterT n ⋅ iterT (n + 1))) = none := rfl
  have hnorm := headNormalize_eq_of_headReduces_none hv hne34 hred hnone
  have hb34 : (evalHN (W0_comb ⋅ iterT n) == .hn34) = false := by
    cases h : (evalHN (W0_comb ⋅ iterT n) == .hn34) with
    | false => rfl
    | true => exfalso; exact hne34 (of_decide_eq_true h)
  unfold stepBohmLeft
  rw [hb34, if_false_eq_true, hnorm, selectBohmChildLeft_s2]
  have hp_left : (evalP (iterT (n + 1)) == .p37) = false := by
    rw [evalP_iterT (n + 1)]; rfl
  have hp_right : (evalP (iterT n ⋅ iterT (n + 1)) == .p37) = true := by
    change (deltaP (evalP (iterT n)) (evalP (iterT (n + 1))) == .p37) = true
    rw [evalP_iterT n, evalP_iterT (n + 1)]; rfl
  rw [hp_left, if_false_eq_true, hp_right, if_true_eq_true]

private theorem iterBohmLeft_two_steps (n : Nat) :
    iterBohmLeft 2 (iterT 0 ⋅ iterT n) = some (iterT n ⋅ iterT (n + 1)) := by
  simp only [iterBohmLeft, stepBohmLeft_iterT0 n, stepBohmLeft_W0 n]

private theorem iterBohmLeft_one_cycle (n : Nat) :
    iterBohmLeft (n + 2) (iterT 0 ⋅ iterT n) = some (iterT 0 ⋅ iterT (n + 1)) := by
  rw [Nat.add_comm n 2, iterBohmLeft_add 2 n, iterBohmLeft_two_steps n]
  exact iterBohmLeft_unwind_iterT n (n + 1)

def leftCycleSteps : Nat → Nat
  | 0 => 1
  | k + 1 => leftCycleSteps k + (k + 3)

theorem leftCycleSteps_gt (k : Nat) : k < leftCycleSteps k := by
  induction k with
  | zero => exact Nat.succ_pos 0
  | succ k ih =>
    change k + 1 < leftCycleSteps k + (k + 3)
    have h1 : k + 1 ≤ leftCycleSteps k := ih
    exact Nat.lt_of_le_of_lt h1 (Nat.lt_add_of_pos_right (Nat.succ_pos (k + 2)))

theorem iterBohmLeft_L_loop_checkpoints (k : Nat) :
    iterBohmLeft (leftCycleSteps k) L_loop = some (iterT 0 ⋅ iterT (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold leftCycleSteps
    rw [iterBohmLeft_add (leftCycleSteps k) (k + 3), ih]
    exact iterBohmLeft_one_cycle (k + 1)

private def L_loop_right_end : Term :=
  (W0_comb ⋅ iterT 1) ⋅ (W0_comb ⋅ (W0_comb ⋅ iterT 1))

private theorem L_loop_right_terminates_4 :
    iterBohmRight 4 L_loop = some L_loop_right_end ∧ evalHN L_loop_right_end = .hn34 :=
  ⟨rfl, rfl⟩

/-- **Böhm-Game Branch Asymmetry Theorem on Pure `S` (`bohm_game_asymmetry_size8`)**:
    On the 8-leaf closed pure-`S` term `L_loop = S ⋅ T ⋅ S ⋅ T ⋅ T` (`evalP L_loop = .p37`):
    1. `stepBohmRight` reaches root divergence (`evalHN = .hn34`) in `4` steps, constructively
       certifying `HasBotWithin 4 L_loop` (`¬ Productive L_loop`).
    2. `stepBohmLeft` never terminates: for every `m : Nat`, `iterBohmLeft m L_loop` produces
       a non-root-diverging term (`evalHN ≠ .hn34`), visiting `iterT 0 ⋅ iterT (k + 1)` with
       unboundedly growing leaf count `k + 15 ≤ leaves`. -/
theorem bohm_game_asymmetry_size8 :
    leaves L_loop = 8 ∧
    evalP L_loop = .p37 ∧
    HasBotWithin 4 L_loop ∧
    (∀ m : Nat, ∃ u, iterBohmLeft m L_loop = some u ∧ evalHN u ≠ .hn34) ∧
    (∀ k : Nat, ∃ u, iterBohmLeft (leftCycleSteps k) L_loop = some u ∧ k + 15 ≤ leaves u) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact iterBohmRight_sound 4 rfl L_loop_right_terminates_4.1 L_loop_right_terminates_4.2
  · intro m
    have hlt : m + 1 ≤ leftCycleSteps m := leftCycleSteps_gt m
    let r := leftCycleSteps m - (m + 1)
    have hr : leftCycleSteps m = m + (r + 1) := by
      have hsub : (m + 1) + r = leftCycleSteps m := Nat.add_sub_of_le hlt
      rw [← hsub, Nat.add_assoc m 1 r, Nat.add_comm 1 r]
    have hchk := iterBohmLeft_L_loop_checkpoints m
    rw [hr, iterBohmLeft_add m (r + 1)] at hchk
    cases hm : iterBohmLeft m L_loop with
    | none => rw [hm] at hchk; cases hchk
    | some u =>
      rw [hm] at hchk
      refine ⟨u, rfl, ?_⟩
      intro h34
      simp only [iterBohmLeft, stepBohmLeft] at hchk
      have hb34 : (evalHN u == .hn34) = true := by rw [h34]; rfl
      rw [hb34, if_true_eq_true] at hchk
      cases hchk
  · intro k
    refine ⟨iterT 0 ⋅ iterT (k + 1), iterBohmLeft_L_loop_checkpoints k, ?_⟩
    change k + 15 ≤ 7 + leaves (iterT (k + 1))
    have hge : (k + 1) + 7 ≤ leaves (iterT (k + 1)) := leaves_iterT_ge (k + 1)
    have h1 : 7 + ((k + 1) + 7) = k + 15 := by
      rw [Nat.add_assoc k 1 7]
      change 7 + (k + 8) = k + 15
      rw [Nat.add_comm 7 (k + 8), Nat.add_assoc k 8 7]
    rw [← h1]
    exact Nat.add_le_add_left hge 7

end Q5SNStratifiedGame

#print axioms Q5SNStratifiedGame.productive_conv_invariant
#print axioms Q5SNStratifiedGame.pure_s_head_escape
#print axioms Q5SNStratifiedGame.hasBotWithin_app_left
#print axioms Q5SNStratifiedGame.hasBotWithin_app_right
#print axioms Q5SNStratifiedGame.evalP_ne_p37_implies_productive
#print axioms Q5SNStratifiedGame.minimal_entry_reduction_theorem
#print axioms Q5SNStratifiedGame.evalP_34_states_sn
#print axioms Q5SNStratifiedGame.nonSN_p18_p24_p33_reduces_hnf_no_root
#print axioms Q5SNStratifiedGame.unique_nonSN_productive_root_redex_state
#print axioms Q5SNStratifiedGame.last_headStep_s2_law
#print axioms Q5SNStratifiedGame.iterBohmRight_sound
#print axioms Q5SNStratifiedGame.bohm_game_asymmetry_size8

