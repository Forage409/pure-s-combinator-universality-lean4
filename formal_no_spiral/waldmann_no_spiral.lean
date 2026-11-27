import formal_no_spiral.bergstra_and_klop

/-!
# Waldmann's No-Spiral Theorem (Theorem 14), Bounded Labelled System `R_m`, No Reducing Fixpoint Combinator (Remark 15), and Unbounded Contracted Redex Size (Remark 16b)

100% constructive Lean 4.33.1 formalization of Section 5.4 (pp. 88–89) of
Barendregt, Endrullis, Klop, and Waldmann (2018), *"Dance of the Starlings"*:

1. **Waldmann's Right-Spine-Labelled Rewrite System `R_m` (pp. 88–89)**:
   - Rule `(5.2)` (`StepR52 m`): `((S ⋅_a x) ⋅_b y) ⋅_c z → (x ⋅_c z) ⋅_{1+c} (y ⋅_c z)` (labels `≤ m`).
   - Rule `(5.3)` (`StepR53 m`): `x ⋅_n y → x ⋅_{n+1} y` (`n + 1 ≤ m`).
   - Equation `(5.4)` (`waldmann_eq_5_4_simulation`): `M →_S N ⟹ toLTerm M →_(5.2) →*_(5.3) toLTerm N`.
2. **Constructive Strong Normalization of `R_m` (`waldmann_Rm_strong_normalizing`)**:
   Proved 100% constructively (`Acc`, zero Kruskal, zero `Classical.choice`) via nested `Acc`
   induction over the finite linear precedence `⋅_1 ≻ ⋅_2 ≻ ... ≻ ⋅_m` (`StepRB`).
3. **Waldmann's Theorem 14 (`waldmann_no_spiral` & `waldmann_no_proper_spiral`)**:
   For every pure-`S` term `M` (open or closed) and every 1-hole context `C`:
   `¬ StepPlus M (plugCtx C M)` (and `C ≠ .hole → ¬ Reduces M (plugCtx C M)`), together with
   the explicit `closeTerm` open-to-closed reduction (`waldmann_open_from_closed`).
4. **Remark 15 (p. 89 — No Reducing Fixed-Point Combinator in `CL(S)`)**:
   `no_reducing_fixpoint_combinator` — no pure-`S` term `Y` satisfies `Y ⋅ X →+ X ⋅ (Y ⋅ X)`
   (or even `Reduces (Y ⋅ X) (X ⋅ (Y ⋅ X))`).
5. **Remark 16, Part 2 (p. 89 — Unbounded Labels & Unbounded Contracted Redex Size)**:
   - `infinite_reduction_unbounded_rm_labels`: no infinite `S`-reduction has bounded `R_m` labels.
   - `infinite_reduction_unbounded_redex_leaves`: in every infinite `S`-reduction, the sizes
     (`leaves`) of the contracted redexes cannot be bounded by any `B : Nat`!
-/

namespace FormalNoSpiral

/-! ## 1. Right-Spine Length `ρ` and Waldmann's Labelled Terms `LTerm` (pp. 88–89) -/

/-- Right-spine length `ρ(t) = 1 + rs(t)` (`ρ(S) = ρ(x) = 1`, `ρ(M ⋅ N) = 1 + ρ(N)`). -/
def rho (t : Term) : Nat := 1 + rs t

theorem rho_pos (t : Term) : 1 ≤ rho t :=
  Nat.le_trans (Nat.le_refl 1) (Nat.le_add_right 1 (rs t))

theorem rho_le_leaves (t : Term) : rho t ≤ leaves t := by
  induction t with
  | s => exact Nat.le_refl 1
  | var _ => exact Nat.le_refl 1
  | app a b _ ihb =>
    change 1 + rho b ≤ leaves a + leaves b
    exact Nat.add_le_add (leaves_pos a) ihb

theorem rho_mono_step {a b : Term} (h : Step a b) : rho a ≤ rho b :=
  Nat.add_le_add_left (rs_mono_step h) 1

/-- Application-labelled `S`-terms (`S`, variables, and `u ⋅_k v` with `k : Nat`). -/
inductive LTerm where
  | s : LTerm
  | var : Nat → LTerm
  | app : Nat → LTerm → LTerm → LTerm
  deriving DecidableEq, Repr

def eraseLabels : LTerm → Term
  | .s => .s
  | .var k => .var k
  | .app _ a b => eraseLabels a ⋅ eraseLabels b

/-- Canonical right-spine labelling `M ↦ M̅` (`M ⋅ N ↦ M̅ ⋅_{ρ(N)} N̅`, p. 88). -/
def toLTerm : Term → LTerm
  | .s => .s
  | .var k => .var k
  | .app a b => .app (rho b) (toLTerm a) (toLTerm b)

theorem eraseLabels_toLTerm (t : Term) : eraseLabels (toLTerm t) = t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [toLTerm, eraseLabels, iha, ihb]

def maxLabel : LTerm → Nat
  | .s => 0
  | .var _ => 0
  | .app k a b => Nat.max k (Nat.max (maxLabel a) (maxLabel b))

theorem maxLabel_app_le_iff {k : Nat} {a b : LTerm} {m : Nat} :
    maxLabel (.app k a b) ≤ m ↔ k ≤ m ∧ maxLabel a ≤ m ∧ maxLabel b ≤ m := by
  simp only [maxLabel, Nat.max_le]

/-! ## 2. Explicit Bounded Labelled Rewrite System `R_m` (`(5.2)`, `(5.3)`, `(5.4)`, pp. 88–89) -/

/-- Rule `(5.2)` of `R_m` (with all labels involved bounded by `m`):
    `((S ⋅_a x) ⋅_b y) ⋅_c z → (x ⋅_c z) ⋅_{1 + c} (y ⋅_c z)`. -/
inductive StepR52 (m : Nat) : LTerm → LTerm → Prop where
  | root {a b c : Nat} (x y z : LTerm) :
      a ≤ m → b ≤ m → 1 + c ≤ m →
      maxLabel x ≤ m → maxLabel y ≤ m → maxLabel z ≤ m →
      StepR52 m (.app c (.app b (.app a .s x) y) z) (.app (1 + c) (.app c x z) (.app c y z))
  | left {k : Nat} {a a' b : LTerm} :
      k ≤ m → maxLabel b ≤ m → StepR52 m a a' → StepR52 m (.app k a b) (.app k a' b)
  | right {k : Nat} {a b b' : LTerm} :
      k ≤ m → maxLabel a ≤ m → StepR52 m b b' → StepR52 m (.app k a b) (.app k a b')

/-- Rule `(5.3)` of `R_m` (label-lifting up to bound `m`):
    `x ⋅_n y → x ⋅_{n + 1} y` for `n + 1 ≤ m`. -/
inductive StepR53 (m : Nat) : LTerm → LTerm → Prop where
  | lift {n : Nat} (a b : LTerm) :
      n + 1 ≤ m → maxLabel a ≤ m → maxLabel b ≤ m →
      StepR53 m (.app n a b) (.app (n + 1) a b)
  | left {k : Nat} {a a' b : LTerm} :
      k ≤ m → maxLabel b ≤ m → StepR53 m a a' → StepR53 m (.app k a b) (.app k a' b)
  | right {k : Nat} {a b b' : LTerm} :
      k ≤ m → maxLabel a ≤ m → StepR53 m b b' → StepR53 m (.app k a b) (.app k a b')

/-- Combined rewrite relation of Waldmann's bounded system `R_m = (5.2) ∪ (5.3)` (p. 89). -/
inductive StepRm (m : Nat) : LTerm → LTerm → Prop where
  | r52 {a b : LTerm} : StepR52 m a b → StepRm m a b
  | r53 {a b : LTerm} : StepR53 m a b → StepRm m a b

theorem stepR52_preserves_maxLabel {m : Nat} {t t' : LTerm} (h : StepR52 m t t') :
    maxLabel t ≤ m ∧ maxLabel t' ≤ m := by
  induction h with
  | @root a b c x y z ha hb hc hx hy hz =>
    have hc0 : c ≤ m := Nat.le_trans (Nat.le_add_left c 1) hc
    refine ⟨?_, ?_⟩
    · exact maxLabel_app_le_iff.mpr ⟨hc0, maxLabel_app_le_iff.mpr ⟨hb, maxLabel_app_le_iff.mpr ⟨ha, Nat.zero_le m, hx⟩, hy⟩, hz⟩
    · exact maxLabel_app_le_iff.mpr ⟨hc, maxLabel_app_le_iff.mpr ⟨hc0, hx, hz⟩, maxLabel_app_le_iff.mpr ⟨hc0, hy, hz⟩⟩
  | left hk hb _ ih =>
    exact ⟨maxLabel_app_le_iff.mpr ⟨hk, ih.1, hb⟩, maxLabel_app_le_iff.mpr ⟨hk, ih.2, hb⟩⟩
  | right hk ha _ ih =>
    exact ⟨maxLabel_app_le_iff.mpr ⟨hk, ha, ih.1⟩, maxLabel_app_le_iff.mpr ⟨hk, ha, ih.2⟩⟩

theorem stepR53_preserves_maxLabel {m : Nat} {t t' : LTerm} (h : StepR53 m t t') :
    maxLabel t ≤ m ∧ maxLabel t' ≤ m := by
  induction h with
  | @lift n a b hn ha hb =>
    have hn0 : n ≤ m := Nat.le_of_succ_le hn
    exact ⟨maxLabel_app_le_iff.mpr ⟨hn0, ha, hb⟩, maxLabel_app_le_iff.mpr ⟨hn, ha, hb⟩⟩
  | left hk hb _ ih =>
    exact ⟨maxLabel_app_le_iff.mpr ⟨hk, ih.1, hb⟩, maxLabel_app_le_iff.mpr ⟨hk, ih.2, hb⟩⟩
  | right hk ha _ ih =>
    exact ⟨maxLabel_app_le_iff.mpr ⟨hk, ha, ih.1⟩, maxLabel_app_le_iff.mpr ⟨hk, ha, ih.2⟩⟩

private theorem stepR53_left_star {m k : Nat} {a a' b : LTerm}
    (hk : k ≤ m) (hb : maxLabel b ≤ m) (h : ReflTransGen (StepR53 m) a a') :
    ReflTransGen (StepR53 m) (.app k a b) (.app k a' b) := by
  induction h with
  | refl _ => exact .refl _
  | head hs _ ih => exact .head (.left hk hb hs) ih

private theorem stepR53_right_star {m k : Nat} {a b b' : LTerm}
    (hk : k ≤ m) (ha : maxLabel a ≤ m) (h : ReflTransGen (StepR53 m) b b') :
    ReflTransGen (StepR53 m) (.app k a b) (.app k a b') := by
  induction h with
  | refl _ => exact .refl _
  | head hs _ ih => exact .head (.right hk ha hs) ih

private theorem stepR53_lift_range {m : Nat} (a b : LTerm) (ha : maxLabel a ≤ m) (hb : maxLabel b ≤ m) :
    ∀ (d n : Nat), n + d ≤ m → ReflTransGen (StepR53 m) (.app n a b) (.app (n + d) a b) := by
  intro d
  induction d with
  | zero =>
    intro n _
    simp only [Nat.add_zero]
    exact .refl _
  | succ d ih =>
    intro n hnd
    have hn1 : n + 1 ≤ m := by
      have h1 : 1 ≤ d + 1 := Nat.succ_le_succ (Nat.zero_le d)
      exact Nat.le_trans (Nat.add_le_add_left h1 n) hnd
    have hstep : StepR53 m (.app n a b) (.app (n + 1) a b) := .lift a b hn1 ha hb
    have hidx : (n + 1) + d = n + (d + 1) := by
      rw [Nat.add_assoc n 1 d, Nat.add_comm 1 d]
    have hrest := ih (n + 1) (by rw [hidx]; exact hnd)
    rw [hidx] at hrest
    exact .head hstep hrest

private theorem stepR53_lift_le {m n n' : Nat} (a b : LTerm)
    (hle : n ≤ n') (hn' : n' ≤ m) (ha : maxLabel a ≤ m) (hb : maxLabel b ≤ m) :
    ReflTransGen (StepR53 m) (.app n a b) (.app n' a b) := by
  have heq : n + (n' - n) = n' := Nat.add_sub_of_le hle
  have h := stepR53_lift_range a b ha hb (n' - n) n (by rw [heq]; exact hn')
  rw [heq] at h
  exact h

/-- **Waldmann's Simulation Lemma (Equation `(5.4)`, *Dance of the Starlings* p. 88)**:
    Every pure-`S` step `M →_S N` whose canonical labels lie in `{1, ..., m}` simulates in `R_m`
    as `toLTerm M →_(5.2) K →*_(5.3) toLTerm N`! -/
theorem waldmann_eq_5_4_simulation (m : Nat) {M N : Term} (hs : Step M N)
    (hM : maxLabel (toLTerm M) ≤ m) (hN : maxLabel (toLTerm N) ≤ m) :
    ∃ K, StepR52 m (toLTerm M) K ∧ ReflTransGen (StepR53 m) K (toLTerm N) := by
  induction hs with
  | root x y z =>
    have ⟨hc_M, hxy_M, hz⟩ := maxLabel_app_le_iff.mp hM
    have ⟨hb, hsx_M, hy⟩ := maxLabel_app_le_iff.mp hxy_M
    have ⟨ha, _, hx⟩ := maxLabel_app_le_iff.mp hsx_M
    have ⟨h1c, _, _⟩ := maxLabel_app_le_iff.mp hN
    exact ⟨toLTerm ((x ⋅ z) ⋅ (y ⋅ z)),
      StepR52.root (toLTerm x) (toLTerm y) (toLTerm z) ha hb h1c hx hy hz,
      .refl _⟩
  | @left l l' r _ ih =>
    have ⟨hk, hl, hr⟩ := maxLabel_app_le_iff.mp hM
    have ⟨_, hl', _⟩ := maxLabel_app_le_iff.mp hN
    obtain ⟨K_l, h52, h53⟩ := ih hl hl'
    exact ⟨.app (rho r) K_l (toLTerm r),
      .left hk hr h52,
      stepR53_left_star hk hr h53⟩
  | @right l r r' hr_step ih =>
    have ⟨hk, hl, hr⟩ := maxLabel_app_le_iff.mp hM
    have ⟨hk', _, hr'⟩ := maxLabel_app_le_iff.mp hN
    obtain ⟨K_r, h52, h53⟩ := ih hr hr'
    have hK_le : maxLabel K_r ≤ m := (stepR52_preserves_maxLabel h52).2
    have hmono : rho r ≤ rho r' := rho_mono_step hr_step
    have h_inner : ReflTransGen (StepR53 m) (.app (rho r) (toLTerm l) K_r) (.app (rho r) (toLTerm l) (toLTerm r')) :=
      stepR53_right_star hk hl h53
    have h_outer : ReflTransGen (StepR53 m) (.app (rho r) (toLTerm l) (toLTerm r')) (.app (rho r') (toLTerm l) (toLTerm r')) :=
      stepR53_lift_le (toLTerm l) (toLTerm r') hmono hk' hl hr'
    exact ⟨.app (rho r) (toLTerm l) K_r, .right hk hl h52, reflTransGen_trans h_inner h_outer⟩

/-! ## 3. Constructive LPO Termination (`Acc`) of `R_m` (`⋅_1 ≻ ⋅_2 ≻ ... ≻ ⋅_m`, zero `Classical.choice`) -/

def flipLabels (B : Nat) : LTerm → LTerm
  | .s => .s
  | .var k => .var k
  | .app k a b => .app (B - k) (flipLabels B a) (flipLabels B b)

/-- Rewriting + subterm descent relation on `B`-flipped `LTerm` (`d = B - k`). -/
inductive StepRB : LTerm → LTerm → Prop where
  | left {d : Nat} {a a' b : LTerm} : StepRB a a' → StepRB (.app d a b) (.app d a' b)
  | right {d : Nat} {a b b' : LTerm} : StepRB b b' → StepRB (.app d a b) (.app d a b')
  | subL (d : Nat) (a b : LTerm) : StepRB (.app d a b) a
  | subR (d : Nat) (a b : LTerm) : StepRB (.app d a b) b
  | lift {d d' : Nat} (a b : LTerm) : d' < d → StepRB (.app d a b) (.app d' a b)
  | beta {d d' d1 d2 : Nat} (x y z : LTerm) :
      d' < d → StepRB (.app d (.app d2 (.app d1 .s x) y) z) (.app d' (.app d x z) (.app d y z))

theorem stepRB_left_trans {d : Nat} {a a' : LTerm} (h : TransGen StepRB a a') (b : LTerm) :
    TransGen StepRB (.app d a b) (.app d a' b) := by
  induction h with
  | single hs => exact .single (.left hs)
  | tail _ hs ih => exact .tail ih (.left hs)

theorem stepRB_right_trans {d : Nat} (a : LTerm) {b b' : LTerm} (h : TransGen StepRB b b') :
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

theorem stepRB_acc_plus (t : LTerm) :
    Acc (fun y x => TransGen StepRB x y) t := by
  induction t with
  | s => exact acc_transGen (Acc.intro LTerm.s (fun _ hy => by cases hy))
  | var k => exact acc_transGen (Acc.intro (LTerm.var k) (fun _ hy => by cases hy))
  | app d u v ihu ihv => exact stepRB_app_all d d (Nat.le_refl d) u v ihu ihv

theorem stepR52_to_stepRB (m : Nat) {a b : LTerm} (h : StepR52 m a b) :
    StepRB (flipLabels m a) (flipLabels m b) := by
  induction h with
  | @root ka kb kc x y z _ _ h1c _ _ _ =>
    have hlt_c : kc < 1 + kc := by
      rw [Nat.add_comm 1 kc]
      exact Nat.lt_succ_self kc
    exact .beta (flipLabels m x) (flipLabels m y) (flipLabels m z) (sub_lt_sub_of_lt hlt_c h1c)
  | left _ _ _ ih => exact .left ih
  | right _ _ _ ih => exact .right ih

theorem stepR53_to_stepRB (m : Nat) {a b : LTerm} (h : StepR53 m a b) :
    StepRB (flipLabels m a) (flipLabels m b) := by
  induction h with
  | @lift n x y hn1 _ _ =>
    exact .lift (flipLabels m x) (flipLabels m y) (sub_lt_sub_of_lt (Nat.lt_succ_self n) hn1)
  | left _ _ _ ih => exact .left ih
  | right _ _ _ ih => exact .right ih

theorem stepRm_to_stepRB (m : Nat) {a b : LTerm} (h : StepRm m a b) :
    StepRB (flipLabels m a) (flipLabels m b) := by
  cases h with
  | r52 h52 => exact stepR52_to_stepRB m h52
  | r53 h53 => exact stepR53_to_stepRB m h53

private theorem acc_pullback_flipLabels (m : Nat) {u : LTerm}
    (hacc : Acc (fun y x => StepRB x y) u) :
    ∀ t, flipLabels m t = u → Acc (fun y x => StepRm m x y) t := by
  induction hacc with
  | intro u _ ih =>
    intro t heq
    subst heq
    exact Acc.intro t (fun t' hs => ih (flipLabels m t') (stepRm_to_stepRB m hs) t' rfl)

/-- **Constructive Termination of `R_m` (*Dance of the Starlings*, p. 89)**:
    For every label bound `m : Nat`, Waldmann's bounded system `R_m = (5.2) ∪ (5.3)` is
    constructively strongly normalizing (`Acc`) on all `LTerm`s. -/
theorem waldmann_Rm_strong_normalizing (m : Nat) (t : LTerm) :
    Acc (fun y x => StepRm m x y) t :=
  acc_pullback_flipLabels m (acc_of_transGen (stepRB_acc_plus (flipLabels m t))) t rfl

/-! ## 4. Waldmann's Theorem 14 (No Spiralling `S`-Terms, Open or Closed, pp. 88–89) -/

private theorem stepRm_star_r53 {m : Nat} {a b : LTerm} (h : ReflTransGen (StepR53 m) a b) :
    ReflTransGen (StepRm m) a b := by
  induction h with
  | refl _ => exact .refl _
  | head hs _ ih => exact .head (.r53 hs) ih

theorem step_to_stepRm_plus (m : Nat) {a b : Term} (hs : Step a b)
    (ha : maxLabel (toLTerm a) ≤ m) (hb : maxLabel (toLTerm b) ≤ m) :
    TransGen (StepRm m) (toLTerm a) (toLTerm b) := by
  obtain ⟨K, h52, h53⟩ := waldmann_eq_5_4_simulation m hs ha hb
  exact transGen_of_transGen_reflTransGen (.single (.r52 h52)) (stepRm_star_r53 h53)

private theorem transGen_stepRm_to_stepRB (m : Nat) {u v : LTerm} (h : TransGen (StepRm m) u v) :
    TransGen StepRB (flipLabels m u) (flipLabels m v) := by
  induction h with
  | single hs1 => exact .single (stepRm_to_stepRB m hs1)
  | tail _ hs1 ih => exact .tail ih (stepRm_to_stepRB m hs1)

theorem step_to_stepRB_plus (m : Nat) {a b : Term} (hs : Step a b)
    (ha : maxLabel (toLTerm a) ≤ m) (hb : maxLabel (toLTerm b) ≤ m) :
    TransGen StepRB (flipLabels m (toLTerm a)) (flipLabels m (toLTerm b)) :=
  transGen_stepRm_to_stepRB m (step_to_stepRm_plus m hs ha hb)

theorem stepPlus_exists_rm_bound {a b : Term} (h : StepPlus a b) :
    ∃ m0, ∀ m, m0 ≤ m →
      maxLabel (toLTerm a) ≤ m ∧ maxLabel (toLTerm b) ≤ m ∧
      TransGen StepRB (flipLabels m (toLTerm a)) (flipLabels m (toLTerm b)) := by
  induction h with
  | @single a b hs =>
    refine ⟨Nat.max (maxLabel (toLTerm a)) (maxLabel (toLTerm b)), fun m hm => ?_⟩
    have ha : maxLabel (toLTerm a) ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
    have hb : maxLabel (toLTerm b) ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
    exact ⟨ha, hb, step_to_stepRB_plus m hs ha hb⟩
  | @head a u b hs _ ih =>
    obtain ⟨m1, hm1⟩ := ih
    refine ⟨Nat.max (maxLabel (toLTerm a)) m1, fun m hm => ?_⟩
    have ha : maxLabel (toLTerm a) ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
    have h1 : m1 ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
    obtain ⟨hu, hb, hub⟩ := hm1 m h1
    exact ⟨ha, hb, transGen_trans (step_to_stepRB_plus m hs ha hu) hub⟩

theorem plugCtx_to_stepRB (m : Nat) (c : Ctx) (t : Term) :
    ReflTransGen StepRB (flipLabels m (toLTerm (plugCtx c t))) (flipLabels m (toLTerm t)) := by
  induction c with
  | hole => exact .refl _
  | left c' r ih =>
    exact .head (.subL (m - rho r) (flipLabels m (toLTerm (plugCtx c' t))) (flipLabels m (toLTerm r))) ih
  | right l c' ih =>
    exact .head (.subR (m - rho (plugCtx c' t)) (flipLabels m (toLTerm l)) (flipLabels m (toLTerm (plugCtx c' t)))) ih

/-- **Waldmann's No-Spiral Theorem (Theorem 14, 2000, *Dance of the Starlings* p. 88)**:
    For every pure-`S` term `M` (open or closed!) and every 1-hole context `C`,
    `¬ StepPlus M (plugCtx C M)`. -/
theorem waldmann_no_spiral (C : Ctx) (M : Term) : ¬ StepPlus M (plugCtx C M) := by
  intro hspiral
  obtain ⟨m0, hm0⟩ := stepPlus_exists_rm_bound hspiral
  have ⟨_, _, htr⟩ := hm0 m0 (Nat.le_refl m0)
  have hsub := plugCtx_to_stepRB m0 C M
  have hcyc := transGen_of_transGen_reflTransGen htr hsub
  exact acc_irrefl (stepRB_acc_plus (flipLabels m0 (toLTerm M))) hcyc

/-- Explicit reduction of open non-spiralling to closed non-spiralling via `closeTerm` (`x_i := S`). -/
theorem waldmann_open_from_closed
    (hclosed : ∀ (C : Ctx) (M : Term), noVars M = true → ¬ StepPlus M (plugCtx C M))
    (C : Ctx) (M : Term) : ¬ StepPlus M (plugCtx C M) := by
  intro hsp
  have hsp_closed : StepPlus (closeTerm M) (closeTerm (plugCtx C M)) :=
    subst_stepPlus (fun _ => .s) hsp
  rw [closeTerm_plugCtx] at hsp_closed
  exact hclosed (closeCtx C) (closeTerm M) (noVars_closeTerm M) hsp_closed

/-- Proper-context formulation: if `C ≠ .hole`, `M` never reduces (even in `0` or more steps) to `C[M]`. -/
theorem waldmann_no_proper_spiral {C : Ctx} (hC : C ≠ .hole) (M : Term) :
    ¬ Reduces M (plugCtx C M) := by
  intro hred
  rcases reduces_eq_or_stepPlus hred with heq | hplus
  · have hlt := plugCtx_leaves_gt hC M
    rw [← heq] at hlt
    exact Nat.lt_irrefl _ hlt
  · exact waldmann_no_spiral C M hplus

/-! ## 5. Remark 15 (p. 89): No Reducing Fixed-Point Combinator Among Pure `S`-Terms -/

/-- **Remark 15 (*Dance of the Starlings*, p. 89)**:
    No pure-`S` term `Y` can act as a reducing fixed-point combinator `Y ⋅ X →* X ⋅ (Y ⋅ X)`. -/
theorem no_reducing_fixpoint_combinator (Y X : Term) :
    ¬ Reduces (Y ⋅ X) (X ⋅ (Y ⋅ X)) := by
  have hC : (Ctx.right X .hole) ≠ .hole := fun h => by cases h
  exact waldmann_no_proper_spiral hC (Y ⋅ X)

/-! ## 6. Remark 16, Part 2 (p. 89): Unbounded `R_m` Labels & Unbounded Contracted Redex Size -/

private theorem no_infinite_stepRB_chain (g : Nat → LTerm)
    (hg : ∀ n, TransGen StepRB (g n) (g (n + 1))) : False := by
  have hacc := stepRB_acc_plus (g 0)
  have haux : ∀ {x : LTerm}, Acc (fun y x => TransGen StepRB x y) x → ∀ n, x = g n → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro n heq
      subst heq
      exact ih (g (n + 1)) (hg n) (n + 1) rfl
  exact haux hacc 0 rfl

/-- In every infinite pure-`S` reduction `f 0 → f 1 → ...`, canonical right-spine labels are unbounded. -/
theorem infinite_reduction_unbounded_rm_labels (f : Nat → Term)
    (hf : ∀ n, Step (f n) (f (n + 1))) (m : Nat) :
    ¬ (∀ n, maxLabel (toLTerm (f n)) ≤ m) := by
  intro hbound
  exact no_infinite_stepRB_chain
    (fun n => flipLabels m (toLTerm (f n)))
    (fun n => step_to_stepRB_plus m (hf n) (hbound n) (hbound (n + 1)))

/-- Step witnessing the specific contracted redex `R = S ⋅ x ⋅ y ⋅ z`. -/
inductive StepWithRedex : Term → Term → Term → Prop where
  | root (x y z : Term) : StepWithRedex (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z)) (S ⋅ x ⋅ y ⋅ z)
  | left {a a' b r : Term} : StepWithRedex a a' r → StepWithRedex (a ⋅ b) (a' ⋅ b) r
  | right {a b b' r : Term} : StepWithRedex b b' r → StepWithRedex (a ⋅ b) (a ⋅ b') r

theorem step_has_redex {a b : Term} (h : Step a b) : ∃ r, StepWithRedex a b r := by
  induction h with
  | root x y z => exact ⟨S ⋅ x ⋅ y ⋅ z, .root x y z⟩
  | left _ ih => obtain ⟨r, hr⟩ := ih; exact ⟨r, .left hr⟩
  | right _ ih => obtain ⟨r, hr⟩ := ih; exact ⟨r, .right hr⟩

theorem stepWithRedex_to_step {a b r : Term} (h : StepWithRedex a b r) : Step a b := by
  induction h with
  | root x y z => exact .root x y z
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

def allLabelsOne : Term → LTerm
  | .s => .s
  | .var k => .var k
  | .app a b => .app 1 (allLabelsOne a) (allLabelsOne b)

theorem eraseLabels_allLabelsOne (t : Term) : eraseLabels (allLabelsOne t) = t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [allLabelsOne, eraseLabels, iha, ihb]

theorem maxLabel_allLabelsOne_le (t : Term) (B : Nat) (hB : 1 ≤ B) :
    maxLabel (allLabelsOne t) ≤ B := by
  induction t with
  | s => exact Nat.zero_le B
  | var _ => exact Nat.zero_le B
  | app a b iha ihb => exact maxLabel_app_le_iff.mpr ⟨hB, iha, ihb⟩

/-- Every label `k` in `L` satisfies `1 ≤ k ≤ rho (eraseLabels rightChild)`. -/
def ValidLowerLabels : LTerm → Prop
  | .s => True
  | .var _ => True
  | .app k a b => 1 ≤ k ∧ k ≤ rho (eraseLabels b) ∧ ValidLowerLabels a ∧ ValidLowerLabels b

theorem validLowerLabels_allLabelsOne (t : Term) : ValidLowerLabels (allLabelsOne t) := by
  induction t with
  | s => trivial
  | var _ => trivial
  | app a b iha ihb =>
    refine ⟨Nat.le_refl 1, ?_, iha, ihb⟩
    rw [eraseLabels_allLabelsOne]
    exact rho_pos b

/-- Pure `(5.2)` simulation without `(5.3)` lifts preserves `ValidLowerLabels` and `maxLabel ≤ B`
    whenever the contracted redex has `leaves r ≤ B`! -/
private theorem stepWithRedex_sim_r52 (B : Nat) {a b r : Term}
    (hs : StepWithRedex a b r) (hr : leaves r ≤ B) :
    ∀ L : LTerm, eraseLabels L = a → ValidLowerLabels L → maxLabel L ≤ B →
      ∃ L' : LTerm, eraseLabels L' = b ∧ ValidLowerLabels L' ∧ maxLabel L' ≤ B ∧ StepR52 B L L' := by
  induction hs with
  | @root x y z =>
    intro L hL hval hmax
    cases L with
    | s => cases hL
    | var _ => cases hL
    | app kc lxy lz =>
      cases lxy with
      | s => injection hL with h1 _; cases h1
      | var _ => injection hL with h1 _; cases h1
      | app kb lsx ly =>
        cases lsx with
        | s => injection hL with h1 _; injection h1 with h2 _; cases h2
        | var _ => injection hL with h1 _; injection h1 with h2 _; cases h2
        | app ka ls lx =>
          cases ls with
          | var _ =>
            injection hL with h1 _
            injection h1 with h2 _
            injection h2 with h3 _
            cases h3
          | app _ _ _ =>
            injection hL with h1 _
            injection h1 with h2 _
            injection h2 with h3 _
            cases h3
          | s =>
            injection hL with hxy hz
            injection hxy with hsx hy
            injection hsx with _ hx
            have ⟨hc_pos, hc_rho, hval_xy, hval_z⟩ := hval
            have ⟨_, _, hval_sx, hval_y⟩ := hval_xy
            have ⟨_, _, _, hval_x⟩ := hval_sx
            have ⟨_, hm_xy, hm_z⟩ := maxLabel_app_le_iff.mp hmax
            have ⟨hb_le, hm_sx, hm_y⟩ := maxLabel_app_le_iff.mp hm_xy
            have ⟨ha_le, _, hm_x⟩ := maxLabel_app_le_iff.mp hm_sx
            have h1c_le_B : 1 + kc ≤ B := by
              rw [hz] at hc_rho
              have hrz : rho z ≤ leaves z := rho_le_leaves z
              have h1z : 1 + leaves z ≤ leaves (S ⋅ x ⋅ y ⋅ z) := by
                change 1 + leaves z ≤ ((1 + leaves x) + leaves y) + leaves z
                have h1xy : 1 ≤ (1 + leaves x) + leaves y :=
                  Nat.le_trans (Nat.le_add_right 1 (leaves x)) (Nat.le_add_right _ (leaves y))
                exact Nat.add_le_add_right h1xy (leaves z)
              exact Nat.le_trans (Nat.add_le_add_left (Nat.le_trans hc_rho hrz) 1) (Nat.le_trans h1z hr)
            have hc_le_B : kc ≤ B := Nat.le_trans (Nat.le_add_left kc 1) h1c_le_B
            let L' : LTerm := .app (1 + kc) (.app kc lx lz) (.app kc ly lz)
            have hstep52 : StepR52 B (.app kc (.app kb (.app ka .s lx) ly) lz) L' :=
              .root lx ly lz ha_le hb_le h1c_le_B hm_x hm_y hm_z
            refine ⟨L', ?_, ?_, (stepR52_preserves_maxLabel hstep52).2, hstep52⟩
            · change (eraseLabels lx ⋅ eraseLabels lz) ⋅ (eraseLabels ly ⋅ eraseLabels lz) =
                (x ⋅ z) ⋅ (y ⋅ z)
              rw [hx, hy, hz]
            · refine ⟨Nat.le_trans (Nat.le_refl 1) (Nat.le_add_right 1 kc), ?_,
                ⟨hc_pos, hc_rho, hval_x, hval_z⟩,
                ⟨hc_pos, hc_rho, hval_y, hval_z⟩⟩
              change 1 + kc ≤ 1 + (1 + rs (eraseLabels lz))
              exact Nat.add_le_add_left hc_rho 1
  | @left a a' b0 r hleft ih =>
    intro L hL hval hmax
    cases L with
    | s => cases hL
    | var _ => cases hL
    | app k la lb =>
      injection hL with ha hb0
      have ⟨hk1, hk_rho, hva, hvb⟩ := hval
      have ⟨hk_B, hma, hmb⟩ := maxLabel_app_le_iff.mp hmax
      obtain ⟨la', hea', hva', hma', hs52⟩ := ih hr la ha hva hma
      refine ⟨.app k la' lb, ?_, ⟨hk1, hk_rho, hva', hvb⟩,
        maxLabel_app_le_iff.mpr ⟨hk_B, hma', hmb⟩, .left hk_B hmb hs52⟩
      simp only [eraseLabels, hea', hb0]
  | @right a0 b b' r hright ih =>
    intro L hL hval hmax
    cases L with
    | s => cases hL
    | var _ => cases hL
    | app k la lb =>
      injection hL with ha0 hb
      have ⟨hk1, hk_rho, hva, hvb⟩ := hval
      have ⟨hk_B, hma, hmb⟩ := maxLabel_app_le_iff.mp hmax
      obtain ⟨lb', heb', hvb', hmb', hs52⟩ := ih hr lb hb hvb hmb
      have hk_rho' : k ≤ rho (eraseLabels lb') := by
        rw [heb']
        rw [hb] at hk_rho
        exact Nat.le_trans hk_rho (rho_mono_step (stepWithRedex_to_step hright))
      refine ⟨.app k la lb', ?_, ⟨hk1, hk_rho', hva, hvb'⟩,
        maxLabel_app_le_iff.mpr ⟨hk_B, hma, hmb'⟩, .right hk_B hma hs52⟩
      simp only [eraseLabels, ha0, heb']

private theorem no_bounded_redex_infinite_aux (B : Nat)
    (f : Nat → Term) (red : Nat → Term)
    (hstep : ∀ n, StepWithRedex (f n) (f (n + 1)) (red n))
    (hbound : ∀ n, leaves (red n) ≤ B) :
    ∀ {u : LTerm}, Acc (fun y x => StepRm B x y) u →
      ∀ (n : Nat), eraseLabels u = f n → ValidLowerLabels u → maxLabel u ≤ B → False := by
  intro u hacc
  induction hacc with
  | intro u _ ih =>
    intro n heu hval hmax
    obtain ⟨u', heu', hval', hmax', hs52⟩ :=
      stepWithRedex_sim_r52 B (hstep n) (hbound n) u heu hval hmax
    exact ih u' (.r52 hs52) (n + 1) heu' hval' hmax'

/-- **Remark 16, Part 2 (*Dance of the Starlings*, p. 89 — Unbounded Contracted Redex Size)**:
    In every infinite `S`-reduction `f 0 → f 1 → ...` contracting redexes `red 0, red 1, ...`,
    the leaf counts `leaves (red n)` of the contracted redexes cannot be bounded by any `B : Nat`! -/
theorem infinite_reduction_unbounded_redex_leaves
    (f : Nat → Term) (red : Nat → Term)
    (hstep : ∀ n, StepWithRedex (f n) (f (n + 1)) (red n)) (B : Nat) :
    ¬ (∀ n, leaves (red n) ≤ B) := by
  intro hbound
  let B' := Nat.max 1 B
  have h1B' : 1 ≤ B' := Nat.le_max_left 1 B
  have hBB' : B ≤ B' := Nat.le_max_right 1 B
  exact no_bounded_redex_infinite_aux B' f red hstep
    (fun n => Nat.le_trans (hbound n) hBB')
    (waldmann_Rm_strong_normalizing B' (allLabelsOne (f 0)))
    0 (eraseLabels_allLabelsOne (f 0))
    (validLowerLabels_allLabelsOne (f 0))
    (maxLabel_allLabelsOne_le (f 0) B' h1B')

end FormalNoSpiral

#print axioms FormalNoSpiral.waldmann_eq_5_4_simulation
#print axioms FormalNoSpiral.waldmann_Rm_strong_normalizing
#print axioms FormalNoSpiral.waldmann_no_spiral
#print axioms FormalNoSpiral.waldmann_open_from_closed
#print axioms FormalNoSpiral.waldmann_no_proper_spiral
#print axioms FormalNoSpiral.no_reducing_fixpoint_combinator
#print axioms FormalNoSpiral.infinite_reduction_unbounded_rm_labels
#print axioms FormalNoSpiral.infinite_reduction_unbounded_redex_leaves
