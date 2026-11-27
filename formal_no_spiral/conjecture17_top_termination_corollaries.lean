import formal_no_spiral.conjecture17_open_spirals
import formal_top_termination.top_termination

/-!
# Attack on Conjecture 17, Part III (*Dance of the Starlings*, 2018, Section 5.4, p. 89): Unconditional Empty-Context & Head/Left-Spine Non-Spiralling via Top-Termination (`Theorem 29`)

100% constructive Lean 4.33.1 formalization proving unconditional open-non-spiralling theorems
that hold **for ALL substitutions `σ` (even WITH positive right-spine self-loops!)**:

1. **`conjecture17_empty_context`**:
   For ALL `M` and ALL `σ`, `¬ StepPlus M (subst σ M)` (`C = .hole`).
2. **`conjecture17_var_head_leftCtx`**:
   For ALL variable-headed `M` (`headLeaf M = .var v`), ALL `LeftCtx`, and ALL `σ`,
   `¬ StepPlus M (plugLeftCtx L (subst σ M))`.
3. **`conjecture17_hnf_leftCtx`**:
   For ALL `A_HN`-accepting open/closed `M` (`evalHN (toTT M) ≠ .hn34`), ALL `LeftCtx`, and ALL `σ`,
   `¬ StepPlus M (plugLeftCtx L (subst σ M))`.
-/

namespace FormalNoSpiral

/-! ## 1. Isomorphism to `FormalTopTermination.Term` and Unconditional Empty-Context Non-Spiralling -/

def toTT : Term → FormalTopTermination.Term
  | .s => .s
  | .var k => .var k
  | .app a b => .app (toTT a) (toTT b)

private theorem toTT_step {a b : Term} (h : Step a b) :
    FormalTopTermination.Step (toTT a) (toTT b) := by
  induction h with
  | root x y z => exact .root (toTT x) (toTT y) (toTT z)
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

private theorem toTT_reduces {a b : Term} (h : Reduces a b) :
    FormalTopTermination.Reduces (toTT a) (toTT b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (toTT_step hs) ih

private theorem toTT_subst (σ : Nat → Term) (t : Term) :
    toTT (subst σ t) = FormalTopTermination.subst (fun k => toTT (σ k)) (toTT t) := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [subst, toTT, FormalTopTermination.subst, iha, ihb]

def iterSubst (σ : Nat → Term) : Nat → Term → Term
  | 0, t => t
  | k + 1, t => subst σ (iterSubst σ k t)

private theorem subst_reduces_tt (σ_tt : Nat → FormalTopTermination.Term)
    {a b : FormalTopTermination.Term} (h : FormalTopTermination.Reduces a b) :
    FormalTopTermination.Reduces
      (FormalTopTermination.subst σ_tt a) (FormalTopTermination.subst σ_tt b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (FormalTopTermination.subst_step σ_tt hs) ih

private theorem hasRootReduces_subst_tt (σ_tt : Nat → FormalTopTermination.Term)
    {a b : FormalTopTermination.Term} (h : FormalTopTermination.HasRootReduces a b) :
    FormalTopTermination.HasRootReduces
      (FormalTopTermination.subst σ_tt a) (FormalTopTermination.subst σ_tt b) := by
  obtain ⟨m1, m2, h1, hr, h2⟩ := h
  exact ⟨_, _, subst_reduces_tt σ_tt h1, FormalTopTermination.subst_rootStep σ_tt hr, subst_reduces_tt σ_tt h2⟩

private theorem no_root_subst_loop_tt (σ_tt : Nat → FormalTopTermination.Term)
    {m : FormalTopTermination.Term}
    (h : FormalTopTermination.HasRootReduces m (FormalTopTermination.subst σ_tt m)) : False := by
  let iterTT : Nat → FormalTopTermination.Term → FormalTopTermination.Term :=
    fun k t => Nat.recOn k t (fun _ acc => FormalTopTermination.subst σ_tt acc)
  have hstep : ∀ k, FormalTopTermination.HasRootReduces (iterTT k m) (iterTT (k + 1) m) := by
    intro k
    induction k with
    | zero => exact h
    | succ _ ih => exact hasRootReduces_subst_tt σ_tt ih
  have haux : ∀ {x : FormalTopTermination.Term},
      Acc (fun b a => FormalTopTermination.HasRootReduces a b) x →
      ∀ k, x = iterTT k m → False := by
    intro x hacc
    induction hacc with
    | intro x _ ih =>
      intro k hx
      subst hx
      exact ih (iterTT (k + 1) m) (hstep k) (k + 1) rfl
  exact haux (FormalTopTermination.hasRootReduces_wellFounded m) 0 rfl

private theorem no_empty_ctx_spiral_by_leaves (σ : Nat → Term) :
    ∀ (L : Nat) (M : Term), leaves M ≤ L → ¬ StepPlus M (subst σ M) := by
  intro L
  induction L with
  | zero =>
    intro M hL _
    exfalso
    exact Nat.not_succ_le_zero 0 (Nat.le_trans (leaves_pos M) hL)
  | succ L ihL =>
    intro M hL hsp
    exact if hle : leaves M ≤ L then
      ihL M hle hsp
    else by
      rcases stepPlus_nonRoot_or_root hsp with hnr | ⟨x, y, z, h1, h2⟩
      · cases M with
        | s => cases hnr with | single hs => cases hs | head hs _ => cases hs
        | var _ => cases hnr with | single hs => cases hs | head hs _ => cases hs
        | app a b =>
          obtain ⟨a', b', heq, _, _, hplus⟩ := nonRootPlus_app_inv hnr a b rfl
          injection heq with ha' hb'
          subst ha'; subst hb'
          rcases hplus with ha_sp | hb_sp
          · have ha_le : leaves a ≤ L :=
              Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (strictSubterm_leaves_lt (strictSubterm_left a b)) hL)
            exact ihL a ha_le ha_sp
          · have hb_le : leaves b ≤ L :=
              Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (strictSubterm_leaves_lt (strictSubterm_right a b)) hL)
            exact ihL b hb_le hb_sp
      · let σ_tt : Nat → FormalTopTermination.Term := fun k => toTT (σ k)
        have hhr : FormalTopTermination.HasRootReduces (toTT M) (FormalTopTermination.subst σ_tt (toTT M)) := by
          rw [← toTT_subst σ M]
          exact ⟨toTT (.app (.app (.app .s x) y) z), toTT (.app (.app x z) (.app y z)),
            toTT_reduces h1, .mk (toTT x) (toTT y) (toTT z), toTT_reduces h2⟩
        exact no_root_subst_loop_tt σ_tt hhr

/-- **THEOREM 17.3 (`conjecture17_empty_context` — Unconditional Substitution Non-Spiralling)**:
    For EVERY pure-`S` term `M` and EVERY substitution `σ` (with NO restriction on `σ`!),
    `¬ StepPlus M (subst σ M)`. -/
theorem conjecture17_empty_context (M : Term) (σ : Nat → Term) :
    ¬ StepPlus M (subst σ M) :=
  no_empty_ctx_spiral_by_leaves σ (leaves M) M (Nat.le_refl _)

/-! ## 2. Left-Spine Contexts (`LeftCtx`) & Unconditional Head-Non-Spiralling Theorems -/

inductive LeftCtx where
  | hole : LeftCtx
  | appL : LeftCtx → Term → LeftCtx
  deriving DecidableEq, Repr

def LeftCtx.plug : LeftCtx → Term → Term
  | .hole, t => t
  | .appL l r, t => .app (LeftCtx.plug l t) r

def LeftCtx.comp : LeftCtx → LeftCtx → LeftCtx
  | .hole, d => d
  | .appL c r, d => .appL (LeftCtx.comp c d) r

def leftCtxDepth : LeftCtx → Nat
  | .hole => 0
  | .appL l _ => 1 + leftCtxDepth l

def substLeftCtx (σ : Nat → Term) : LeftCtx → LeftCtx
  | .hole => .hole
  | .appL l r => .appL (substLeftCtx σ l) (subst σ r)

theorem leftCtx_comp_plug (c d : LeftCtx) (u : Term) :
    LeftCtx.plug (LeftCtx.comp c d) u = LeftCtx.plug c (LeftCtx.plug d u) := by
  induction c with
  | hole => rfl
  | appL c' r ih => simp only [LeftCtx.comp, LeftCtx.plug, ih]

theorem spineLen_plugLeftCtx (l : LeftCtx) (t : Term) :
    spineLen (LeftCtx.plug l t) = spineLen t + leftCtxDepth l := by
  induction l with
  | hole => simp only [LeftCtx.plug, leftCtxDepth, Nat.add_zero]
  | appL l' _ ih =>
    change 1 + spineLen (LeftCtx.plug l' t) = spineLen t + (1 + leftCtxDepth l')
    rw [ih, ← Nat.add_assoc 1 (spineLen t) (leftCtxDepth l'),
        Nat.add_comm 1 (spineLen t), Nat.add_assoc (spineLen t) 1 (leftCtxDepth l')]

theorem spineLen_subst_ge (σ : Nat → Term) (t : Term) :
    spineLen t ≤ spineLen (subst σ t) := by
  induction t with
  | s => exact Nat.zero_le _
  | var _ => exact Nat.zero_le _
  | app _ _ iha _ => exact Nat.add_le_add_left iha 1

theorem subst_plugLeftCtx (σ : Nat → Term) (l : LeftCtx) (t : Term) :
    subst σ (LeftCtx.plug l t) = LeftCtx.plug (substLeftCtx σ l) (subst σ t) := by
  induction l with
  | hole => rfl
  | appL _ _ ih => simp only [LeftCtx.plug, substLeftCtx, subst, ih]

private theorem eq_zero_of_le_and_add_eq {a b d : Nat} (hle : a ≤ b) (heq : b + d = a) : d = 0 := by
  have h1 : a + d ≤ a + 0 := by
    rw [Nat.add_zero]
    have h2 : a + d ≤ b + d := Nat.add_le_add_right hle d
    rw [heq] at h2
    exact h2
  exact Nat.le_zero.mp (Nat.le_of_add_le_add_left h1)

theorem headLeaf_var_spine_step {a b : Term} {v : Nat}
    (hs : Step a b) (hhead : headLeaf a = .var v) :
    headLeaf b = .var v ∧ spineLen b = spineLen a := by
  induction hs with
  | root _ _ _ => cases hhead
  | left _ ih =>
    obtain ⟨hh, hsp⟩ := ih hhead
    exact ⟨hh, congrArg (1 + ·) hsp⟩
  | right _ _ => exact ⟨hhead, rfl⟩

theorem headLeaf_var_spine_reduces {a b : Term} {v : Nat}
    (hr : Reduces a b) (hhead : headLeaf a = .var v) :
    headLeaf b = .var v ∧ spineLen b = spineLen a := by
  induction hr with
  | refl _ => exact ⟨hhead, rfl⟩
  | next hs _ ih =>
    obtain ⟨hh1, hsp1⟩ := headLeaf_var_spine_step hs hhead
    obtain ⟨hh2, hsp2⟩ := ih hh1
    exact ⟨hh2, hsp2.trans hsp1⟩

/-- **THEOREM 17.4 (`conjecture17_var_head_leftCtx` — Unconditional Variable-Headed Left-Non-Spiralling)**:
    No variable-headed pure-`S` term `M` (`headLeaf M = .var v`) can open-spiral along the left spine
    under ANY `LeftCtx` and ANY substitution `σ`! -/
theorem conjecture17_var_head_leftCtx (M : Term) (v : Nat) (L : LeftCtx) (σ : Nat → Term)
    (hhead : headLeaf M = .var v) :
    ¬ StepPlus M (LeftCtx.plug L (subst σ M)) := by
  intro hsp
  have ⟨_, hsp_eq⟩ := headLeaf_var_spine_reduces (reduces_of_stepPlus hsp) hhead
  rw [spineLen_plugLeftCtx] at hsp_eq
  have hd0 : leftCtxDepth L = 0 :=
    eq_zero_of_le_and_add_eq (spineLen_subst_ge σ M) hsp_eq
  cases L with
  | hole => exact conjecture17_empty_context M σ hsp
  | appL l' _ =>
    change 1 + leftCtxDepth l' = 0 at hd0
    rw [Nat.add_comm 1 (leftCtxDepth l')] at hd0
    exact Nat.succ_ne_zero _ hd0

inductive HeadStep : Term → Term → Prop where
  | root (x y z : Term) : HeadStep (.app (.app (.app .s x) y) z) (.app (.app x z) (.app y z))
  | left {a a' b : Term} : HeadStep a a' → HeadStep (.app a b) (.app a' b)

inductive InternalStep : Term → Term → Prop where
  | right {a b b' : Term} : Step b b' → InternalStep (.app a b) (.app a b')
  | left {a a' b : Term} : InternalStep a a' → InternalStep (.app a b) (.app a' b)

theorem step_iff_head_or_internal {a b : Term} :
    Step a b ↔ HeadStep a b ∨ InternalStep a b := by
  constructor
  · intro hs
    induction hs with
    | root x y z => exact Or.inl (.root x y z)
    | left _ ih =>
      rcases ih with hh | hi
      · exact Or.inl (.left hh)
      · exact Or.inr (.left hi)
    | right hr => exact Or.inr (.right hr)
  · intro h
    rcases h with hh | hi
    · induction hh with
      | root x y z => exact .root x y z
      | left _ ih => exact .left ih
    · induction hi with
      | right hr => exact .right hr
      | left _ ih => exact .left ih

theorem internalStep_spineLen {a b : Term} (h : InternalStep a b) : spineLen b = spineLen a := by
  induction h with
  | right _ => rfl
  | left _ ih => exact congrArg (1 + ·) ih

theorem plugLeftCtx_headStep (l : LeftCtx) {a b : Term} (h : HeadStep a b) :
    HeadStep (LeftCtx.plug l a) (LeftCtx.plug l b) := by
  induction l with
  | hole => exact h
  | appL _ _ ih => exact .left ih

theorem plugLeftCtx_reduces (l : LeftCtx) {a b : Term} (h : Reduces a b) :
    Reduces (LeftCtx.plug l a) (LeftCtx.plug l b) := by
  induction l with
  | hole => exact h
  | appL _ r ih => exact plugCtx_reduces (.left .hole r) ih

theorem subst_headStep (σ : Nat → Term) {a b : Term} (h : HeadStep a b) :
    HeadStep (subst σ a) (subst σ b) := by
  induction h with
  | root x y z => exact .root (subst σ x) (subst σ y) (subst σ z)
  | left _ ih => exact .left ih

private theorem stepPlus_internal_or_head {a b : Term} (h : StepPlus a b) :
    spineLen b = spineLen a ∨ ∃ m1 m2, Reduces a m1 ∧ HeadStep m1 m2 ∧ Reduces m2 b := by
  induction h with
  | @single a b hs =>
    rcases step_iff_head_or_internal.mp hs with hh | hi
    · exact Or.inr ⟨a, b, .refl a, hh, .refl b⟩
    · exact Or.inl (internalStep_spineLen hi)
  | @head a u _ hs hrest ih =>
    rcases step_iff_head_or_internal.mp hs with hh | hi
    · exact Or.inr ⟨a, u, .refl a, hh, reduces_of_stepPlus hrest⟩
    · rcases ih with hsp_eq | ⟨m1, m2, h1, hh, h2⟩
      · exact Or.inl (hsp_eq.trans (internalStep_spineLen hi))
      · exact Or.inr ⟨m1, m2, .next hs h1, hh, h2⟩

private theorem toTT_headStep {a b : Term} (h : HeadStep a b) :
    FormalTopTermination.HeadStep (toTT a) (toTT b) := by
  induction h with
  | root x y z => exact .root (toTT x) (toTT y) (toTT z)
  | left _ ih => exact .left ih

private theorem nuHN_drop_one_head {a b : Term}
    (m1 m2 : Term) (h1 : Reduces a m1) (hh : HeadStep m1 m2) (h2 : Reduces m2 b)
    (hne : FormalTopTermination.evalHN (toTT a) ≠ .hn34) :
    FormalTopTermination.evalHN (toTT b) ≠ .hn34 ∧
      FormalTopTermination.nuHN (toTT b) + 1 ≤ FormalTopTermination.nuHN (toTT a) := by
  have h1_tt := toTT_reduces h1
  have hh_tt := toTT_headStep hh
  have h2_tt := toTT_reduces h2
  have h_all : FormalTopTermination.Reduces (toTT a) (toTT b) :=
    FormalTopTermination.reduces_trans h1_tt
      (.next (FormalTopTermination.headStep_to_step hh_tt) h2_tt)
  have hne_m1 : FormalTopTermination.evalHN (toTT m1) ≠ .hn34 := by
    rw [← FormalTopTermination.evalHN_reduces h1_tt]; exact hne
  have hne_b : FormalTopTermination.evalHN (toTT b) ≠ .hn34 := by
    rw [← FormalTopTermination.evalHN_reduces h_all]; exact hne
  have hle1 : FormalTopTermination.nuHN (toTT m1) ≤ FormalTopTermination.nuHN (toTT a) :=
    FormalTopTermination.nuHN_reduces_le h1_tt
  have hdrop : FormalTopTermination.nuHN (toTT m2) + 1 ≤ FormalTopTermination.nuHN (toTT m1) :=
    FormalTopTermination.nuHN_headStep_drop hh_tt hne_m1
  have hle2 : FormalTopTermination.nuHN (toTT b) ≤ FormalTopTermination.nuHN (toTT m2) :=
    FormalTopTermination.nuHN_reduces_le h2_tt
  exact ⟨hne_b, Nat.le_trans (Nat.add_le_add_right hle2 1) (Nat.le_trans hdrop hle1)⟩

/-- **THEOREM 17.5 (`conjecture17_hnf_leftCtx` — Unconditional Left-Non-Spiralling for All `A_HN`-Accepting Terms)**:
    For EVERY pure-`S` term `M` (open or closed) with `evalHN (toTT M) ≠ .hn34`, EVERY `LeftCtx` `L`,
    and EVERY substitution `σ` (even with positive right-spine self-loops!),
    `¬ StepPlus M (LeftCtx.plug L (subst σ M))`! -/
theorem conjecture17_hnf_leftCtx (M : Term) (L : LeftCtx) (σ : Nat → Term)
    (hne : FormalTopTermination.evalHN (toTT M) ≠ .hn34) :
    ¬ StepPlus M (LeftCtx.plug L (subst σ M)) := by
  intro hsp
  rcases stepPlus_internal_or_head hsp with hsp_eq | ⟨m1, m2, h1, hh, h2⟩
  · rw [spineLen_plugLeftCtx] at hsp_eq
    have hd0 : leftCtxDepth L = 0 :=
      eq_zero_of_le_and_add_eq (spineLen_subst_ge σ M) hsp_eq
    cases L with
    | hole => exact conjecture17_empty_context M σ hsp
    | appL l' _ =>
      change 1 + leftCtxDepth l' = 0 at hd0
      rw [Nat.add_comm 1 (leftCtxDepth l')] at hd0
      exact Nat.succ_ne_zero _ hd0
  · have h_unroll : ∀ (fuel : Nat) (k : Nat) (K : LeftCtx),
        FormalTopTermination.evalHN (toTT (LeftCtx.plug K (iterSubst σ k M))) ≠ .hn34 →
        FormalTopTermination.nuHN (toTT (LeftCtx.plug K (iterSubst σ k M))) < fuel → False := by
      intro fuel
      induction fuel with
      | zero => intro _ _ _ hlt; cases hlt
      | succ fuel ih =>
        intro k K hne_k hlt_k
        have h_iter_step : ∀ j,
            ∃ p1 p2,
              Reduces (iterSubst σ j M) p1 ∧
              HeadStep p1 p2 ∧
              Reduces p2 (iterSubst σ j (LeftCtx.plug L (subst σ M))) := by
          intro j
          induction j with
          | zero => exact ⟨m1, m2, h1, hh, h2⟩
          | succ _ ihj =>
            obtain ⟨p1, p2, hp1, hhp, hp2⟩ := ihj
            exact ⟨subst σ p1, subst σ p2,
              subst_reduces σ hp1, subst_headStep σ hhp, subst_reduces σ hp2⟩
        obtain ⟨p1, p2, hp1, hhp, hp2⟩ := h_iter_step k
        have h_shape : ∀ (t : Term) (j : Nat),
            ∃ Lj : LeftCtx, iterSubst σ j (LeftCtx.plug L t) = LeftCtx.plug Lj (iterSubst σ j t) := by
          intro t j
          induction j with
          | zero => exact ⟨L, rfl⟩
          | succ j ihj =>
            obtain ⟨Lj, hLj⟩ := ihj
            refine ⟨substLeftCtx σ Lj, ?_⟩
            change subst σ (iterSubst σ j (LeftCtx.plug L t)) = _
            rw [hLj, subst_plugLeftCtx]
            rfl
        obtain ⟨Lk, hLk⟩ := h_shape (subst σ M) k
        have hit_eq : iterSubst σ k (subst σ M) = iterSubst σ (k + 1) M := by
          clear hLk hne_k hlt_k hp1 hhp hp2
          induction k with
          | zero => rfl
          | succ k0 ihk0 =>
            change subst σ (iterSubst σ k0 (subst σ M)) = subst σ (iterSubst σ (k0 + 1) M)
            rw [ihk0]
        rw [hit_eq] at hLk
        rw [hLk] at hp2
        have hK1 : Reduces (LeftCtx.plug K (iterSubst σ k M)) (LeftCtx.plug K p1) :=
          plugLeftCtx_reduces K hp1
        have hKh : HeadStep (LeftCtx.plug K p1) (LeftCtx.plug K p2) :=
          plugLeftCtx_headStep K hhp
        have hK2 : Reduces (LeftCtx.plug K p2) (LeftCtx.plug (LeftCtx.comp K Lk) (iterSubst σ (k + 1) M)) := by
          rw [leftCtx_comp_plug]
          exact plugLeftCtx_reduces K hp2
        obtain ⟨hne_next, hdrop⟩ := nuHN_drop_one_head (LeftCtx.plug K p1) (LeftCtx.plug K p2)
          hK1 hKh hK2 hne_k
        have hlt_next : FormalTopTermination.nuHN (toTT (LeftCtx.plug (LeftCtx.comp K Lk) (iterSubst σ (k + 1) M))) < fuel :=
          Nat.lt_of_succ_lt_succ (Nat.lt_of_le_of_lt hdrop hlt_k)
        exact ih (k + 1) (LeftCtx.comp K Lk) hne_next hlt_next
    exact h_unroll (FormalTopTermination.nuHN (toTT M) + 1) 0 .hole hne (Nat.lt_succ_self _)

end FormalNoSpiral
