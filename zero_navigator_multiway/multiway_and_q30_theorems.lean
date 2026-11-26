import formal_algebra.s_structural_laws
import formal_algebra.sn_hn_algebras

/-!
# Zero-Navigator Multiway Reachability (`→_S*`) and Dana Scott's Convertibility Problem (`=_S`, Question 30)

Machine-checked in Lean 4.33.1 with **zero placeholders, zero user-declared postulates,
and strictly constructive kernel proofs** (`#print axioms` uses at most `[propext, Quot.sound]`).

## Main Formalized Results
1. **Confluence Characterization & Takahashi/Gross–Knuth Cofinality for Question 30**
   (`convS_iff_common_reduct`, `scott_q30_gk_cofinality`):
   `ConvS a b ↔ ∃ m, Reduces b (completeDevIter m a)`.
2. **Unconditional Decidability of Pointwise Multiway Reachability & `SN`-Target Convertibility**
   (`decideReduces`, `convS_sn_iff`, `decideConvOfSN`, `decideConvClosedSN`):
   - For **all** pure-`S` terms `u, v` (even non-normalizing!), pointwise multiway reachability
     `Reduces u v` (`u →_S* v`) is constructively decidable via Bergstra's `(leaves, weight)` measure.
   - `StrongNormalizing` is `ConvS`-invariant, and for any closed target `v` with `evalSN v ≠ .sn38`,
     `ConvS t v` is constructively decidable—proving any undecidable `=_S` target must lie outside `SN`.
3. **Root-Normal-Form (`RNF`) Structural Decomposition of `=_S`** (`rnf_convS_app_iff`, `rnf_not_convS_s`):
   For any two Root Normal Forms `a1 ⋅ b1` and `a2 ⋅ b2`,
   `ConvS (a1 ⋅ b1) (a2 ⋅ b2) ↔ (ConvS a1 a2 ∧ ConvS b1 b2)`.
4. **The Multiway Asymmetric Thunk-Gating Obstruction Theorem**
   (`hasCall_reduces`, `multiway_no_exclusive_second_thunk`, `bool0_calls_first_only`,
    `no_church_boolean_pair_in_pure_s`):
   While `B_comb = S ⋅ S` activates `var 0` without activating `var 1`, **no** pure-`S` term `M`
   free of `var 0, var 1` can ever activate `var 1` along any multiway path `M ⋅ var 0 ⋅ var 1 ⋅ ... →_S* T`
   without already activating `var 0` (`hasCall 1 T = true → hasCall 0 T = true`).
5. **Exact 4-Row Pure-Line (`|Redex(T)| = 1`) Stack Automaton Characterization**
   (`redexCount_StackHead`, `pure_line_four_cases`):
   Characterizes all normal-form stack transitions preserving `redexCount = 1`.
6. **Spurious Multiway Halt Shortcut Counterexamples**
   (`protected_trie_nonhalting_shortcut_7steps`, `filin_dispatcher_nonhalting_shortcut_5steps`):
   Formal 7-step and 5-step pure-`S` multiway shortcut derivations showing why unopened-generator
   halt flags and `D ⋅ Q` branch dispatchers produce false halts without an external navigator.
7. **Waldmann's Order-1 Polymorphic Merge Pair & Minimal Size-7/9 Non-Cancellative Merge Tower**
   (`waldmann_not_convS`, `waldmann_polymorphic_merge`, `minimal_merge_not_convS`,
    `minimal_merge_at_s`, `ssss_n1_s_convS_ssss_n2_s`, `tower_nf_merge_family`).
-/

namespace ZeroNavigatorMultiway

open FormalAlgebra

/-! ## 1. Basic `ConvS` & Contextual Helpers -/

def appList : Term → List Term → Term
  | t, [] => t
  | t, u :: us => appList (t ⋅ u) us

theorem reduces_left_ctx {a a' : Term} (h : Reduces a a') (b : Term) : Reduces (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.left hs) ih

theorem reduces_right_ctx (a : Term) {b b' : Term} (h : Reduces b b') : Reduces (a ⋅ b) (a ⋅ b') := by
  induction h with
  | refl _ => exact .refl _
  | next hs _ ih => exact .next (.right hs) ih

theorem reduces_app_both {a a' b b' : Term} (ha : Reduces a a') (hb : Reduces b b') :
    Reduces (a ⋅ b) (a' ⋅ b') :=
  reduces_trans (reduces_left_ctx ha b) (reduces_right_ctx a' hb)

theorem reduces_to_convS {a b : Term} (h : Reduces a b) : ConvS a b := by
  induction h with
  | refl u => exact .refl u
  | next hs _ ih => exact .trans (.step hs) ih

theorem convS_left {a a' : Term} (h : ConvS a a') (b : Term) : ConvS (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact .step (.left hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convS_right (a : Term) {b b' : Term} (h : ConvS b b') : ConvS (a ⋅ b) (a ⋅ b') := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact .step (.right hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convS_app {a a' b b' : Term} (ha : ConvS a a') (hb : ConvS b b') :
    ConvS (a ⋅ b) (a' ⋅ b') :=
  .trans (convS_left ha b) (convS_right a' hb)

/-- **Church–Rosser Equivalence for `ConvS`**:
    `a =_S b` iff `a` and `b` share a finite common reduct `k`. -/
theorem convS_iff_common_reduct {a b : Term} :
    ConvS a b ↔ ∃ k, Reduces a k ∧ Reduces b k := by
  constructor
  · intro h
    induction h with
    | refl u => exact ⟨u, .refl u, .refl u⟩
    | step hs => exact ⟨_, .next hs (.refl _), .refl _⟩
    | symm _ ih =>
      obtain ⟨k, h1, h2⟩ := ih
      exact ⟨k, h2, h1⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨k1, hak1, hbk1⟩ := ih1
      obtain ⟨k2, hbk2, hck2⟩ := ih2
      obtain ⟨d, hk1d, hk2d⟩ := church_rosser hbk1 hbk2
      exact ⟨d, reduces_trans hak1 hk1d, reduces_trans hck2 hk2d⟩
  · intro ⟨k, hak, hbk⟩
    exact .trans (reduces_to_convS hak) (.symm (reduces_to_convS hbk))

theorem isNormalForm_reduces_eq {a b : Term} (hnf : IsNormalForm a) (hr : Reduces a b) : a = b := by
  cases hr with
  | refl _ => rfl
  | next hs _ => exfalso; exact hnf _ hs

theorem distinct_nf_not_convS {a b : Term}
    (ha : IsNormalForm a) (hb : IsNormalForm b) (hne : a ≠ b) : ¬ ConvS a b := by
  intro hconv
  obtain ⟨k, hak, hbk⟩ := convS_iff_common_reduct.mp hconv
  have h1 := isNormalForm_reduces_eq ha hak
  have h2 := isNormalForm_reduces_eq hb hbk
  exact hne (h1.trans h2.symm)

/-! ## 2. Gross–Knuth / Takahashi Cofinality Characterization of Scott's Question 30 -/

def completeDevIter : Nat → Term → Term
  | 0, t => t
  | n + 1, t => completeDev (completeDevIter n t)

theorem completeDevIter_succ_right (n : Nat) (t : Term) :
    completeDevIter n (completeDev t) = completeDevIter (n + 1) t := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [completeDevIter, ih]

theorem parStep_self_completeDev (t : Term) : ParStep t (completeDev t) :=
  parStep_triangle (parStep_refl t)

theorem reduces_completeDevIter (n : Nat) (t : Term) : Reduces t (completeDevIter n t) := by
  induction n with
  | zero => exact .refl t
  | succ m ih =>
    exact reduces_trans ih (parStep_to_reduces (parStep_self_completeDev _))

theorem parStep_completeDev_mono {a b : Term} (h : ParStep a b) :
    ParStep (completeDev a) (completeDev b) :=
  parStep_triangle (parStep_triangle h)

theorem parStep_completeDevIter_mono (n : Nat) {a b : Term} (h : ParStep a b) :
    ParStep (completeDevIter n a) (completeDevIter n b) := by
  induction n with
  | zero => exact h
  | succ m ih => exact parStep_completeDev_mono ih

inductive ParStepsN : Nat → Term → Term → Prop where
  | zero (a : Term) : ParStepsN 0 a a
  | succ {n : Nat} {a b c : Term} : ParStep a b → ParStepsN n b c → ParStepsN (n + 1) a c

theorem parStepsN_tail {n : Nat} {a b c : Term}
    (h1 : ParStepsN n a b) (h2 : ParStep b c) : ParStepsN (n + 1) a c := by
  induction h1 with
  | zero _ => exact .succ h2 (.zero _)
  | succ hs _ ih => exact .succ hs (ih h2)

theorem parStepsN_to_reduces {n : Nat} {a b : Term} (h : ParStepsN n a b) : Reduces a b := by
  induction h with
  | zero u => exact .refl u
  | succ hs _ ih => exact reduces_trans (parStep_to_reduces hs) ih

theorem reduces_to_parStepsN {a b : Term} (h : Reduces a b) : ∃ n, ParStepsN n a b := by
  induction h with
  | refl u => exact ⟨0, .zero u⟩
  | next hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .succ (step_to_parStep hs) hn⟩

theorem parStepsN_cofinal {n : Nat} {a k : Term} (h : ParStepsN n a k) :
    ParStepsN n k (completeDevIter n a) := by
  induction h with
  | zero u => exact .zero u
  | @succ m u u1 k hu1 _ ih =>
    have htri : ParStep u1 (completeDev u) := parStep_triangle hu1
    have hmono : ParStep (completeDevIter m u1) (completeDevIter m (completeDev u)) :=
      parStep_completeDevIter_mono m htri
    rw [completeDevIter_succ_right m u] at hmono
    exact parStepsN_tail ih hmono

/-- **Gross–Knuth / Takahashi Cofinality Theorem for Dana Scott's Question 30**:
    Two pure-`S` terms `a` and `b` are `S`-convertible (`a =_S b`) iff `b` reduces in finitely
    many steps to some deterministic full-parallel iterate `completeDevIter m a`. -/
theorem scott_q30_gk_cofinality {a b : Term} :
    ConvS a b ↔ ∃ m : Nat, Reduces b (completeDevIter m a) := by
  constructor
  · intro hconv
    obtain ⟨k, hak, hbk⟩ := convS_iff_common_reduct.mp hconv
    obtain ⟨m, hpar⟩ := reduces_to_parStepsN hak
    have hcof := parStepsN_to_reduces (parStepsN_cofinal hpar)
    exact ⟨m, reduces_trans hbk hcof⟩
  · intro ⟨m, hbm⟩
    exact convS_iff_common_reduct.mpr ⟨completeDevIter m a, reduces_completeDevIter m a, hbm⟩

/-! ## 3. Constructive Decidability of Pointwise Multiway Reachability & `SN`-Target Convertibility -/

def oneStepList : Term → List Term
  | .s => []
  | .var _ => []
  | .app l r =>
      let rootL := match l with
        | .app (.app .s x) y => [((x ⋅ r) ⋅ (y ⋅ r))]
        | _ => []
      rootL ++ (oneStepList l).map (fun l' => l' ⋅ r) ++ (oneStepList r).map (fun r' => l ⋅ r')

private theorem mem_rootL_iff (l r u : Term) :
    (u ∈ match l with | .app (.app .s x) y => [((x ⋅ r) ⋅ (y ⋅ r))] | _ => []) ↔
      ∃ x y, l = S ⋅ x ⋅ y ∧ u = (x ⋅ r) ⋅ (y ⋅ r) := by
  cases l with
  | s => simp
  | var _ => simp
  | app l1 y =>
    cases l1 with
    | s =>
      simp only [List.mem_nil_iff, false_iff]
      intro ⟨x, y', h, _⟩
      injection h with h1 _
      cases h1
    | var _ =>
      simp only [List.mem_nil_iff, false_iff]
      intro ⟨x, y', h, _⟩
      injection h with h1 _
      cases h1
    | app l2 x =>
      cases l2 with
      | s =>
        simp only [List.mem_singleton]
        constructor
        · intro hu; exact ⟨x, y, rfl, hu⟩
        · intro ⟨x', y', hl, hu⟩
          injection hl with hl1 hy
          injection hl1 with _ hx
          subst hx; subst hy; exact hu
      | var _ =>
        simp only [List.mem_nil_iff, false_iff]
        intro ⟨x', y', hl, _⟩
        injection hl with hl1 _
        injection hl1 with hl2 _
        cases hl2
      | app _ _ =>
        simp only [List.mem_nil_iff, false_iff]
        intro ⟨x', y', hl, _⟩
        injection hl with hl1 _
        injection hl1 with hl2 _
        cases hl2

theorem mem_oneStepList_iff {t u : Term} : u ∈ oneStepList t ↔ Step t u := by
  induction t generalizing u with
  | s =>
    simp only [oneStepList, List.not_mem_nil, false_iff]
    intro h; cases h
  | var _ =>
    simp only [oneStepList, List.not_mem_nil, false_iff]
    intro h; cases h
  | app l r ihl ihr =>
    simp only [oneStepList, List.mem_append, List.mem_map]
    rw [mem_rootL_iff]
    constructor
    · rintro ((⟨x, y, rfl, rfl⟩ | ⟨l', hl', rfl⟩) | ⟨r', hr', rfl⟩)
      · exact Step.root x y r
      · exact Step.left (ihl.mp hl')
      · exact Step.right (ihr.mp hr')
    · intro hs
      cases hs with
      | root x y _ => exact Or.inl (Or.inl ⟨x, y, rfl, rfl⟩)
      | @left _ l' _ hl => exact Or.inl (Or.inr ⟨l', ihl.mpr hl, rfl⟩)
      | @right _ _ r' hr => exact Or.inr ⟨r', ihr.mpr hr, rfl⟩

theorem oneStepList_eq_nil_iff {t : Term} : oneStepList t = [] ↔ IsNormalForm t := by
  constructor
  · intro hnil u hs
    have hm := mem_oneStepList_iff.mpr hs
    rw [hnil] at hm
    cases hm
  · intro hnf
    cases h : oneStepList t with
    | nil => rfl
    | cons u _ =>
      exfalso
      exact hnf u (mem_oneStepList_iff.mp (by rw [h]; exact List.Mem.head _))

instance decideIsNormalForm (t : Term) : Decidable (IsNormalForm t) :=
  if h : oneStepList t = [] then
    isTrue (oneStepList_eq_nil_iff.mp h)
  else
    isFalse (fun hnf => h (oneStepList_eq_nil_iff.mpr hnf))

private theorem list_any_eq_true_iff {α : Type} (xs : List α) (p : α → Bool) :
    xs.any p = true ↔ ∃ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp [List.any]
  | cons a as ih =>
    simp only [List.any, Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro (ha | has)
      · exact ⟨a, Or.inl rfl, ha⟩
      · obtain ⟨x, hx, hpx⟩ := ih.mp has
        exact ⟨x, Or.inr hx, hpx⟩
    · rintro ⟨x, rfl | hx, hpx⟩
      · exact Or.inl hpx
      · exact Or.inr (ih.mpr ⟨x, hx, hpx⟩)

def reducesWFuel (recLF : Term → Term → Bool) : Nat → Term → Term → Bool
  | 0, u, v => decide (u = v)
  | wf + 1, u, v =>
      decide (u = v) ||
      if decide (leaves v < leaves u) then false
      else
        (oneStepList u).any (fun u' =>
          if decide (leaves u' = leaves u) then
            reducesWFuel recLF wf u' v
          else if decide (leaves u' ≤ leaves v) then
            recLF u' v
          else false)

def reducesFuel : Nat → Nat → Term → Term → Bool
  | 0, wf, u, v => reducesWFuel (fun _ _ => false) wf u v
  | lf + 1, wf, u, v => reducesWFuel (fun u' v' => reducesFuel lf (bergstraWeight u') u' v') wf u v

private theorem reducesWFuel_sound {recLF : Term → Term → Bool}
    (hrec : ∀ u' v', recLF u' v' = true → Reduces u' v') :
    ∀ (wf : Nat) (u v : Term), reducesWFuel recLF wf u v = true → Reduces u v
  | 0, u, v, h => by
    have heq : u = v := of_decide_eq_true h
    subst heq
    exact .refl u
  | wf + 1, u, v, h => by
    simp only [reducesWFuel, Bool.or_eq_true] at h
    rcases h with heq | hstep
    · have hu := of_decide_eq_true heq
      subst hu
      exact .refl u
    · split at hstep
      · cases hstep
      · obtain ⟨u', hu'mem, hbr⟩ := (list_any_eq_true_iff _ _).mp hstep
        have hs : Step u u' := mem_oneStepList_iff.mp hu'mem
        split at hbr
        · exact .next hs (reducesWFuel_sound hrec wf u' v hbr)
        · split at hbr
          · exact .next hs (hrec u' v hbr)
          · cases hbr

theorem reducesFuel_sound :
    ∀ (lf wf : Nat) (u v : Term), reducesFuel lf wf u v = true → Reduces u v
  | 0, wf, u, v, h => reducesWFuel_sound (fun _ _ hc => by cases hc) wf u v h
  | lf + 1, wf, u, v, h =>
    reducesWFuel_sound (fun u' v' hc => reducesFuel_sound lf (bergstraWeight u') u' v' hc) wf u v h

private theorem sub_lt_of_lt_le : ∀ {B a b : Nat}, a < b → b ≤ B → B - b < B - a
  | 0, _, _, h1, h2 => by cases Nat.eq_zero_of_le_zero h2; cases h1
  | B + 1, 0, b + 1, _, _ => by
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    exact Nat.lt_succ_of_le (Nat.sub_le B b)
  | B + 1, a + 1, b + 1, h1, h2 => by
    simp only [Nat.succ_sub_succ_eq_sub]
    exact sub_lt_of_lt_le (Nat.lt_of_succ_lt_succ h1) (Nat.le_of_succ_le_succ h2)

theorem reducesFuel_complete {u v : Term} (hr : Reduces u v) :
    ∀ (lf wf : Nat), leaves v - leaves u ≤ lf → bergstraWeight u ≤ wf →
      reducesFuel lf wf u v = true := by
  induction hr with
  | refl a =>
    intro lf wf _ _
    cases lf <;> cases wf <;> simp [reducesFuel, reducesWFuel]
  | @next a u' v hs hrest ih =>
    intro lf wf hlf hwf
    have hw_pos : 1 ≤ wf := Nat.le_trans (bergstraWeight_pos a) hwf
    cases wf with
    | zero => cases hw_pos
    | succ wf' =>
      have hle_step : leaves a ≤ leaves u' := leaves_mono_step hs
      have hle_rest : leaves u' ≤ leaves v := leaves_mono_reduces hrest
      have hle_av : leaves a ≤ leaves v := Nat.le_trans hle_step hle_rest
      have hnot_lt : ¬ leaves v < leaves a := Nat.not_lt_of_ge hle_av
      cases lf with
      | zero =>
        simp only [reducesFuel, reducesWFuel, Bool.or_eq_true]
        refine Or.inr ?_
        rw [if_neg (by intro hc; exact hnot_lt (of_decide_eq_true hc))]
        refine (list_any_eq_true_iff _ _).mpr ⟨u', mem_oneStepList_iff.mpr hs, ?_⟩
        by_cases heq : leaves u' = leaves a
        · rw [if_pos (decide_eq_true heq)]
          have hw_drop : bergstraWeight u' < bergstraWeight a :=
            equal_leaves_strict_weight_drop hs heq.symm
          have hw_le : bergstraWeight u' ≤ wf' :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw_drop hwf)
          have hlf' : leaves v - leaves u' ≤ 0 := by rw [heq]; exact hlf
          exact ih 0 wf' hlf' hw_le
        · exfalso
          have hlt_step : leaves a < leaves u' := Nat.lt_of_le_of_ne hle_step (Ne.symm heq)
          have hsub_lt : leaves v - leaves u' < leaves v - leaves a :=
            sub_lt_of_lt_le hlt_step hle_rest
          exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hsub_lt hlf)
      | succ lf' =>
        simp only [reducesFuel, reducesWFuel, Bool.or_eq_true]
        refine Or.inr ?_
        rw [if_neg (by intro hc; exact hnot_lt (of_decide_eq_true hc))]
        refine (list_any_eq_true_iff _ _).mpr ⟨u', mem_oneStepList_iff.mpr hs, ?_⟩
        by_cases heq : leaves u' = leaves a
        · rw [if_pos (decide_eq_true heq)]
          have hw_drop : bergstraWeight u' < bergstraWeight a :=
            equal_leaves_strict_weight_drop hs heq.symm
          have hw_le : bergstraWeight u' ≤ wf' :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw_drop hwf)
          have hlf' : leaves v - leaves u' ≤ lf' + 1 := by rw [heq]; exact hlf
          exact ih (lf' + 1) wf' hlf' hw_le
        · rw [if_neg (by intro hc; exact heq (of_decide_eq_true hc))]
          rw [if_pos (decide_eq_true hle_rest)]
          have hlt_step : leaves a < leaves u' := Nat.lt_of_le_of_ne hle_step (Ne.symm heq)
          have hsub_lt : leaves v - leaves u' < leaves v - leaves a :=
            sub_lt_of_lt_le hlt_step hle_rest
          have hlt_lf : leaves v - leaves u' < lf' + 1 := Nat.lt_of_lt_of_le hsub_lt hlf
          exact ih lf' (bergstraWeight u') (Nat.le_of_lt_succ hlt_lf) (Nat.le_refl _)

def reducesBool (u v : Term) : Bool :=
  reducesFuel (leaves v - leaves u) (bergstraWeight u) u v

theorem reducesBool_iff {u v : Term} : reducesBool u v = true ↔ Reduces u v :=
  ⟨reducesFuel_sound _ _ u v, fun hr => reducesFuel_complete hr _ _ (Nat.le_refl _) (Nat.le_refl _)⟩

/-- **Unconditional Decidability of Pointwise Multiway Reachability (`u →_S* v`)**:
    Constructively decides `Reduces u v` for any two pure-`S` terms `u, v` (open or closed,
    `SN` or non-`SN`!). -/
instance decideReduces (u v : Term) : Decidable (Reduces u v) :=
  if h : reducesBool u v = true then
    isTrue (reducesBool_iff.mp h)
  else
    isFalse (fun hr => h (reducesBool_iff.mpr hr))

/-- **Conservation Invariance of `StrongNormalizing` under `=_S`**:
    Because pure `S` is orthogonal and non-erasing (`WN ↔ SN`), `a =_S b` preserves `SN`. -/
theorem convS_sn_iff {a b : Term} (h : ConvS a b) :
    StrongNormalizing a ↔ StrongNormalizing b := by
  induction h with
  | refl _ => exact Iff.rfl
  | step hs => exact ⟨fun ha => Acc.inv ha hs, fun hb => conservation_step hs hb⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def nfOfSN : (u : Term) → StrongNormalizing u → { nf : Term // Reduces u nf ∧ IsNormalForm nf } :=
  fun u hsn =>
    Acc.rec
      (motive := fun x _ => { nf : Term // Reduces x nf ∧ IsNormalForm nf })
      (fun x _ ih =>
        match hL : oneStepList x with
        | [] => ⟨x, .refl x, oneStepList_eq_nil_iff.mp hL⟩
        | x' :: _ =>
          have hs : Step x x' := mem_oneStepList_iff.mp (by rw [hL]; exact List.Mem.head _)
          let sub := ih x' hs
          ⟨sub.1, .next hs sub.2.1, sub.2.2⟩)
      hsn

/-- **Constructive Decision Procedure for `SN`-Target Convertibility (`t =_S v` when `v ∈ SN`)**:
    Given `v ∈ SN` and decidability of `t ∈ SN`, constructively decides `ConvS t v`. -/
def decideConvOfSN (t v : Term) (hv_sn : StrongNormalizing v)
    (ht_dec : Decidable (StrongNormalizing t)) : Decidable (ConvS t v) :=
  match ht_dec with
  | isFalse hnot_sn =>
    isFalse (fun hconv => hnot_sn ((convS_sn_iff hconv).mpr hv_sn))
  | isTrue ht_sn =>
    let nft := nfOfSN t ht_sn
    let nfv := nfOfSN v hv_sn
    if heq : nft.1 = nfv.1 then
      isTrue (by
        have hr_v : Reduces v nft.1 := heq ▸ nfv.2.1
        exact convS_iff_common_reduct.mpr ⟨nft.1, nft.2.1, hr_v⟩)
    else
      isFalse (fun hconv => by
        have hnf_conv : ConvS nft.1 nfv.1 :=
          .trans (.symm (reduces_to_convS nft.2.1)) (.trans hconv (reduces_to_convS nfv.2.1))
        exact distinct_nf_not_convS nft.2.2 nfv.2.2 heq hnf_conv)

/-- **Closed `SN`-Target Convertibility Decidability Theorem (via Waldmann's 39-State Algebra `A_SN`)**:
    For any closed pure-`S` terms `t, v` where `v ∈ SN` (`evalSN v ≠ .sn38`), `ConvS t v` is
    constructively decidable in `CL(S)`. Consequently, any undecidable `=_S` reduction target
    for Dana Scott's Question 30 **must** be non-terminating (`evalSN v = .sn38`). -/
def decideConvClosedSN (t v : Term) (ht : noVars t = true) (hv : noVars v = true)
    (hv_sn : evalSN v ≠ .sn38) : Decidable (ConvS t v) :=
  have hv_strong : StrongNormalizing v := (waldmann_theorem_9 hv).1.mpr hv_sn
  have ht_dec : Decidable (StrongNormalizing t) :=
    if hts : evalSN t ≠ .sn38 then
      isTrue ((waldmann_theorem_9 ht).1.mpr hts)
    else
      isFalse (fun hsn => hts ((waldmann_theorem_9 ht).1.mp hsn))
  decideConvOfSN t v hv_strong ht_dec

/-! ## 4. Root-Normal-Form (`RNF`) Structural Decomposition of `=_S` (Question 30 / 31 Bridge) -/

theorem rnf_left_no_sab {a b : Term} (hrnf : IsRootNormalForm (a ⋅ b)) :
    ∀ p q, ¬ Reduces a (S ⋅ p ⋅ q) :=
  fun p q hr => hrnf ⟨p, q, b, reduces_left_ctx hr b⟩

/-- **Exact Root-Normal-Form Decomposition Theorem for `=_S`**:
    Whenever `a1 ⋅ b1` and `a2 ⋅ b2` are in Root Normal Form (`IsRootNormalForm`, decidable in
    `O(|T|)` time on closed terms by `footnote4_rnf_iff` via the 35-state algebra `A_HN`),
    `(a1 ⋅ b1) =_S (a2 ⋅ b2) ↔ (a1 =_S a2 ∧ b1 =_S b2)`. -/
theorem rnf_convS_app_iff {a1 b1 a2 b2 : Term}
    (hr1 : IsRootNormalForm (a1 ⋅ b1)) (hr2 : IsRootNormalForm (a2 ⋅ b2)) :
    ConvS (a1 ⋅ b1) (a2 ⋅ b2) ↔ (ConvS a1 a2 ∧ ConvS b1 b2) := by
  constructor
  · intro hconv
    obtain ⟨k, hk1, hk2⟩ := convS_iff_common_reduct.mp hconv
    obtain ⟨a1', b1', hkeq1, hra1, hrb1⟩ :=
      reduces_app_no_sab hk1 a1 b1 (rnf_left_no_sab hr1) rfl
    obtain ⟨a2', b2', hkeq2, hra2, hrb2⟩ :=
      reduces_app_no_sab hk2 a2 b2 (rnf_left_no_sab hr2) rfl
    have hpair : a1' ⋅ b1' = a2' ⋅ b2' := hkeq1.symm.trans hkeq2
    injection hpair with ha_eq hb_eq
    subst ha_eq; subst hb_eq
    exact ⟨convS_iff_common_reduct.mpr ⟨a1', hra1, hra2⟩,
           convS_iff_common_reduct.mpr ⟨b1', hrb1, hrb2⟩⟩
  · intro ⟨ha, hb⟩
    exact convS_app ha hb

theorem rnf_app_not_convS_s {a b : Term} (hr : IsRootNormalForm (a ⋅ b)) :
    ¬ ConvS (a ⋅ b) S := by
  intro hconv
  obtain ⟨k, hk1, hk2⟩ := convS_iff_common_reduct.mp hconv
  obtain ⟨a', b', hkeq, _, _⟩ := reduces_app_no_sab hk1 a b (rnf_left_no_sab hr) rfl
  have hs_nf : IsNormalForm S := fun _ hs => by cases hs
  have hsk : S = k := isNormalForm_reduces_eq hs_nf hk2
  have habs : S = a' ⋅ b' := hsk.trans hkeq
  cases habs

/-! ## 5. Attack Line 1 Core: The Multiway Asymmetric Thunk-Gating Obstruction Theorem -/

/-- `hasCall v t` is `true` iff variable `var v` appears in function position (`var v ⋅ w`) inside `t`. -/
def hasCall (v : Nat) : Term → Bool
  | .s => false
  | .var _ => false
  | .app l r => decide (l = .var v) || hasCall v l || hasCall v r

private theorem hasCall_app_iff (v : Nat) (a b : Term) :
    hasCall v (a ⋅ b) = true ↔ (a = .var v ∨ hasCall v a = true ∨ hasCall v b = true) := by
  simp only [hasCall, Bool.or_eq_true]
  constructor
  · rintro ((h1 | h2) | h3)
    · exact Or.inl (of_decide_eq_true h1)
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
  · rintro (h1 | h2 | h3)
    · exact Or.inl (Or.inl (decide_eq_true h1))
    · exact Or.inl (Or.inr h2)
    · exact Or.inr h3

theorem hasCall_mono_step {v : Nat} {a b : Term} (hs : Step a b) :
    hasCall v a = true → hasCall v b = true := by
  induction hs with
  | root x y z =>
    intro h
    rcases (hasCall_app_iff v (S ⋅ x ⋅ y) z).mp h with hbad | hxy | hz
    · cases hbad
    · rcases (hasCall_app_iff v (S ⋅ x) y).mp hxy with hbad2 | hsx | hy
      · cases hbad2
      · rcases (hasCall_app_iff v S x).mp hsx with hbad3 | hs0 | hx
        · cases hbad3
        · cases hs0
        · exact (hasCall_app_iff v (x ⋅ z) (y ⋅ z)).mpr
            (Or.inr (Or.inl ((hasCall_app_iff v x z).mpr (Or.inr (Or.inl hx)))))
      · exact (hasCall_app_iff v (x ⋅ z) (y ⋅ z)).mpr
          (Or.inr (Or.inr ((hasCall_app_iff v y z).mpr (Or.inr (Or.inl hy)))))
    · exact (hasCall_app_iff v (x ⋅ z) (y ⋅ z)).mpr
        (Or.inr (Or.inl ((hasCall_app_iff v x z).mpr (Or.inr (Or.inr hz)))))
  | @left l l' r hstep_l ih =>
    intro h
    rcases (hasCall_app_iff v l r).mp h with hlv | hl | hr
    · subst hlv; cases hstep_l
    · exact (hasCall_app_iff v l' r).mpr (Or.inr (Or.inl (ih hl)))
    · exact (hasCall_app_iff v l' r).mpr (Or.inr (Or.inr hr))
  | @right l r r' _ ih =>
    intro h
    rcases (hasCall_app_iff v l r).mp h with hlv | hl | hr
    · exact (hasCall_app_iff v l r').mpr (Or.inl hlv)
    · exact (hasCall_app_iff v l r').mpr (Or.inr (Or.inl hl))
    · exact (hasCall_app_iff v l r').mpr (Or.inr (Or.inr (ih hr)))

theorem hasCall_reduces {v : Nat} {a b : Term} (hr : Reduces a b) :
    hasCall v a = true → hasCall v b = true := by
  induction hr with
  | refl _ => intro h; exact h
  | next hs _ ih => intro h; exact ih (hasCall_mono_step hs h)

theorem hasCall_false_of_hasVar_false {v : Nat} {t : Term} (h : hasVar v t = false) :
    hasCall v t = false := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app l r ihl ihr =>
    simp only [hasVar, Bool.or_eq_false_iff] at h
    have hlnot : l ≠ .var v := by
      intro heq; subst heq
      simp [hasVar] at h
    simp only [hasCall, decide_eq_false hlnot, ihl h.1, ihr h.2, Bool.false_or]

/-- Inductive grammar `W0`: terms formed from `c ⋅ var 0` (with `c` free of `var 0, var 1`)
    closed under binary application, before `var 0` is ever called. -/
inductive W0 : Term → Prop where
  | base (c : Term) : hasVar 0 c = false → hasVar 1 c = false → W0 (c ⋅ .var 0)
  | app {w1 w2 : Term} : W0 w1 → W0 w2 → W0 (w1 ⋅ w2)

private theorem w0_not_s : ¬ W0 S := fun h => by cases h
private theorem w0_not_var (k : Nat) : ¬ W0 (.var k) := fun h => by cases h

private theorem w0_hasVar1_false {w : Term} (hw : W0 w) : hasVar 1 w = false := by
  induction hw with
  | base c _ hc1 => simp [hasVar, hc1]
  | app _ _ ih1 ih2 => simp [hasVar, ih1, ih2]

private theorem w0_spineLen_ge1 {w : Term} (hw : W0 w) : 1 ≤ spineLen w := by
  cases hw <;> exact Nat.le_add_right 1 _

private theorem w0_s1_inv {p : Term} (hw : W0 (S ⋅ p)) : p = .var 0 := by
  cases hw with
  | base c _ _ => rfl
  | app hw1 _ => exfalso; exact w0_not_s hw1

private theorem w0_s2_inv {p q : Term} (hw : W0 (S ⋅ p ⋅ q)) : p = .var 0 ∨ q = .var 0 := by
  cases hw with
  | base c _ _ => exact Or.inr rfl
  | app hw1 _ => exact Or.inl (w0_s1_inv hw1)

private theorem w0_step {w w' : Term} (hw : W0 w) (hs : Step w w') :
    W0 w' ∨ hasCall 0 w' = true := by
  induction hw generalizing w' with
  | base c hc0 hc1 =>
    cases hs with
    | @root x y _ =>
      simp only [S, hasVar, Bool.or_eq_false_iff] at hc0 hc1
      exact Or.inl (.app (.base x hc0.1.2 hc1.1.2) (.base y hc0.2 hc1.2))
    | @left _ c' _ hcs =>
      exact Or.inl (.base c' (hasVar_false_step hcs hc0) (hasVar_false_step hcs hc1))
    | right hrs => cases hrs
  | @app w1 w2 hw1 hw2 ih1 ih2 =>
    cases hs with
    | @root p q _ =>
      rcases w0_s2_inv hw1 with rfl | rfl
      · refine Or.inr ?_
        simp [hasCall]
      · refine Or.inr ?_
        simp [hasCall]
    | @left _ w1' _ hl =>
      rcases ih1 hl with hw1' | hcall
      · exact Or.inl (.app hw1' hw2)
      · refine Or.inr ?_
        simp [hasCall, hcall]
    | @right _ _ w2' hr =>
      rcases ih2 hr with hw2' | hcall
      · exact Or.inl (.app hw1 hw2')
      · refine Or.inr ?_
        simp [hasCall, hcall]

/-- Invariant `OuterSpine`: terms of the form `appList (w ⋅ var 1) us` where `W0 w` and every `u ∈ us`
    contains neither `var 0` nor `var 1`. -/
inductive OuterSpine : Term → Prop where
  | head {w : Term} : W0 w → OuterSpine (w ⋅ .var 1)
  | snoc {t u : Term} : OuterSpine t → hasVar 0 u = false → hasVar 1 u = false → OuterSpine (t ⋅ u)

private theorem outerSpine_hasCall1_false {t : Term} (ho : OuterSpine t) : hasCall 1 t = false := by
  induction ho with
  | @head w hw =>
    have hw_not_v1 : w ≠ .var 1 := by
      intro heq; subst heq; exact w0_not_var 1 hw
    have hc1_w : hasCall 1 w = false := hasCall_false_of_hasVar_false (w0_hasVar1_false hw)
    simp [hasCall, decide_eq_false hw_not_v1, hc1_w]
  | @snoc t0 u _ _ hu1 ih =>
    have ht_not_v1 : t0 ≠ .var 1 := by
      intro heq; subst heq
      cases ‹OuterSpine (.var 1)›
    have hc1_u : hasCall 1 u = false := hasCall_false_of_hasVar_false hu1
    simp [hasCall, decide_eq_false ht_not_v1, ih, hc1_u]

private theorem outerSpine_not_s {t : Term} (ho : OuterSpine t) : t ≠ S := by
  cases ho <;> intro h <;> cases h

private theorem outerSpine_not_s1 {t : Term} (ho : OuterSpine t) (p : Term) : t ≠ S ⋅ p := by
  cases ho with
  | @head w hw =>
    intro heq
    injection heq with hw_eq _
    subst hw_eq
    exact w0_not_s hw
  | @snoc t0 _ ht0 _ _ =>
    intro heq
    injection heq with ht0_eq _
    exact outerSpine_not_s ht0 ht0_eq

private theorem outerSpine_s2_inv {t p q : Term} (ho : OuterSpine t) (heq : t = S ⋅ p ⋅ q) :
    p = .var 0 := by
  cases ho with
  | @head w hw =>
    injection heq with hw_eq _
    subst hw_eq
    exact w0_s1_inv hw
  | @snoc t0 _ ht0 _ _ =>
    injection heq with ht0_eq _
    exfalso
    exact outerSpine_not_s1 ht0 p ht0_eq

private theorem outerSpine_step {t t' : Term} (ho : OuterSpine t) (hs : Step t t') :
    OuterSpine t' ∨ hasCall 0 t' = true := by
  induction ho generalizing t' with
  | @head w hw =>
    cases hs with
    | @root p q _ =>
      rcases w0_s2_inv hw with rfl | rfl
      · refine Or.inr ?_; simp [hasCall]
      · refine Or.inr ?_; simp [hasCall]
    | @left _ w' _ hl =>
      rcases w0_step hw hl with hw' | hcall
      · exact Or.inl (.head hw')
      · refine Or.inr ?_; simp [hasCall, hcall]
    | right hr => cases hr
  | @snoc t0 u ht0 hu0 hu1 ih =>
    cases hs with
    | @root p q _ =>
      have hp0 : p = .var 0 := outerSpine_s2_inv ht0 rfl
      subst hp0
      refine Or.inr ?_
      simp [hasCall]
    | @left _ t0' _ hl =>
      rcases ih hl with ht0' | hcall
      · exact Or.inl (.snoc ht0' hu0 hu1)
      · refine Or.inr ?_; simp [hasCall, hcall]
    | @right _ _ u' hr =>
      exact Or.inl (.snoc ht0 (hasVar_false_step hr hu0) (hasVar_false_step hr hu1))

private theorem outerSpine_reduces {t t' : Term} (hr : Reduces t t') :
    OuterSpine t → OuterSpine t' ∨ hasCall 0 t' = true := by
  induction hr with
  | refl _ => intro ho; exact Or.inl ho
  | next hs hrest ih =>
    intro ho
    rcases outerSpine_step ho hs with ho' | hcall0
    · exact ih ho'
    · exact Or.inr (hasCall_reduces hrest hcall0)

private theorem outerSpine_appList {t : Term} (ho : OuterSpine t) :
    ∀ (us : List Term), (∀ u ∈ us, hasVar 0 u = false ∧ hasVar 1 u = false) →
      OuterSpine (appList t us)
  | [], _ => ho
  | u :: us, hus =>
    have ⟨hu0, hu1⟩ := hus u (List.Mem.head _)
    outerSpine_appList (.snoc ho hu0 hu1) us (fun x hx => hus x (List.Mem.tail u hx))

/-- **Theorem (The Multiway Asymmetric Thunk-Gating Obstruction Theorem in `CL(S)`)**:
    For **every** pure-`S` combinator `m` free of `var 0` and `var 1`, **every** list of extra
    arguments `us` free of `var 0` and `var 1`, and **every** multiway reduction
    `appList (m ⋅ var 0 ⋅ var 1) us →_S* t`:
    if the second thunk `var 1` is called anywhere in `t`, then the first thunk `var 0` is
    **already** called in `t`! -/
theorem multiway_no_exclusive_second_thunk (m t : Term) (us : List Term)
    (hm0 : hasVar 0 m = false) (hm1 : hasVar 1 m = false)
    (hus : ∀ u ∈ us, hasVar 0 u = false ∧ hasVar 1 u = false)
    (hred : Reduces (appList (m ⋅ .var 0 ⋅ .var 1) us) t)
    (hcall1 : hasCall 1 t = true) :
    hasCall 0 t = true := by
  have hinit : OuterSpine (appList (m ⋅ .var 0 ⋅ .var 1) us) :=
    outerSpine_appList (.head (.base m hm0 hm1)) us hus
  rcases outerSpine_reduces hred hinit with ho_end | hcall0
  · rw [outerSpine_hasCall1_false ho_end] at hcall1
    cases hcall1
  · exact hcall0

/-- **Contrast Witness (`Bool_0 = S ⋅ S`)**:
    On the first branch, `(S ⋅ S) ⋅ var 0 ⋅ var 1` reduces in 1 step to the normal form
    `(S ⋅ var 1) ⋅ (var 0 ⋅ var 1)`, which calls `var 0` and **never** calls `var 1`! -/
theorem bool0_calls_first_only :
    Step (B_comb ⋅ .var 0 ⋅ .var 1) ((S ⋅ .var 1) ⋅ (.var 0 ⋅ .var 1)) ∧
    IsNormalForm ((S ⋅ .var 1) ⋅ (.var 0 ⋅ .var 1)) ∧
    hasCall 0 ((S ⋅ .var 1) ⋅ (.var 0 ⋅ .var 1)) = true ∧
    hasCall 1 ((S ⋅ .var 1) ⋅ (.var 0 ⋅ .var 1)) = false := by
  refine ⟨Step.root S (.var 0) (.var 1), ?_, rfl, rfl⟩
  exact oneStepList_eq_nil_iff.mp rfl

/-- **Corollary (Non-Existence of Church-Boolean Thunk Gates in Pure `S`)**:
    There exists **no** closed pure-`S` combinator `b1` (`noVars b1 = true`) and extra closed
    arguments `us` (`∀ u ∈ us, noVars u = true`) that can activate `var 1` along **any**
    multiway path without simultaneously activating `var 0`. -/
theorem no_church_boolean_pair_in_pure_s :
    ¬ ∃ (b1 t : Term) (us : List Term),
        noVars b1 = true ∧
        (∀ u ∈ us, noVars u = true) ∧
        Reduces (appList (b1 ⋅ .var 0 ⋅ .var 1) us) t ∧
        hasCall 1 t = true ∧
        hasCall 0 t = false := by
  have noVars_no_var : ∀ {x : Term} (v : Nat), noVars x = true → hasVar v x = false := by
    intro x v hx
    induction x with
    | s => rfl
    | var _ => cases hx
    | app a b iha ihb =>
      simp only [noVars, Bool.and_eq_true] at hx
      simp [hasVar, iha hx.1, ihb hx.2]
  rintro ⟨b1, t, us, hb1, hus, hred, hc1, hc0⟩
  have hc0_true := multiway_no_exclusive_second_thunk b1 t us
    (noVars_no_var 0 hb1) (noVars_no_var 1 hb1)
    (fun u hu => ⟨noVars_no_var 0 (hus u hu), noVars_no_var 1 (hus u hu)⟩)
    hred hc1
  rw [hc0] at hc0_true
  cases hc0_true

/-! ## 6. Exact 4-Row Pure-Line (`|Redex(T)| = 1`) Stack Automaton Characterization -/

def isRedexRoot : Term → Bool
  | .app (.app (.app .s _) _) _ => true
  | _ => false

def redexCount : Term → Nat
  | .s => 0
  | .var _ => 0
  | t@(.app l r) => (if isRedexRoot t then 1 else 0) + redexCount l + redexCount r

theorem redexCount_eq_zero_iff_isNormalForm (t : Term) :
    redexCount t = 0 ↔ IsNormalForm t := by
  induction t with
  | s =>
    simp only [redexCount, true_iff]
    intro _ hs; cases hs
  | var _ =>
    simp only [redexCount, true_iff]
    intro _ hs; cases hs
  | app l r ihl ihr =>
    constructor
    · intro h0 u hs
      have hroot0 : (if isRedexRoot (l ⋅ r) then 1 else 0) = 0 := by
        cases hrr : isRedexRoot (l ⋅ r)
        · rfl
        · change (if isRedexRoot (l ⋅ r) then 1 else 0) + redexCount l + redexCount r = 0 at h0
          rw [hrr] at h0; simp at h0
      have hl0 : redexCount l = 0 := by
        change (if isRedexRoot (l ⋅ r) then 1 else 0) + redexCount l + redexCount r = 0 at h0
        rw [hroot0, Nat.zero_add] at h0
        exact Nat.eq_zero_of_add_eq_zero_right h0
      have hr0 : redexCount r = 0 := by
        change (if isRedexRoot (l ⋅ r) then 1 else 0) + redexCount l + redexCount r = 0 at h0
        rw [hroot0, hl0] at h0
        simp only [Nat.zero_add] at h0
        exact h0
      cases hs with
      | root x y _ => simp [S, isRedexRoot] at hroot0
      | left hl => exact (ihl.mp hl0) _ hl
      | right hr => exact (ihr.mp hr0) _ hr
    · intro hnf
      have hnot_root : isRedexRoot (l ⋅ r) = false := by
        cases l with
        | s => rfl
        | var _ => rfl
        | app l1 y =>
          cases l1 with
          | s => rfl
          | var _ => rfl
          | app l2 x =>
            cases l2 with
            | s => exfalso; exact hnf _ (Step.root x y r)
            | var _ => rfl
            | app _ _ => rfl
      have hlnf : IsNormalForm l := fun l' hl => hnf (l' ⋅ r) (.left hl)
      have hrnf : IsNormalForm r := fun r' hr => hnf (l ⋅ r') (.right hr)
      change (if isRedexRoot (l ⋅ r) then 1 else 0) + redexCount l + redexCount r = 0
      rw [hnot_root, ihl.mpr hlnf, ihr.mpr hrnf]
      rfl

private theorem spineLen_ge3_four (a b c d : Term) : 3 ≤ spineLen (a ⋅ b ⋅ c ⋅ d) := by
  change 1 + (1 + (1 + 0)) ≤ 1 + (1 + (1 + spineLen a))
  exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.zero_le (spineLen a)) 1) 1) 1

private theorem closed_nf_spineLen_le_2 {t : Term}
    (hv : noVars t = true) (hc : redexCount t = 0) :
    (spineLen t = 0 ∧ t = S) ∨
    (spineLen t = 1 ∧ ∃ a, t = S ⋅ a ∧ noVars a = true ∧ redexCount a = 0) ∨
    (spineLen t = 2 ∧ ∃ a b, t = S ⋅ a ⋅ b ∧ noVars a = true ∧ noVars b = true ∧
      redexCount a = 0 ∧ redexCount b = 0) := by
  have hnf : IsNormalForm t := (redexCount_eq_zero_iff_isNormalForm t).mp hc
  have hv_full : noVars t = true := hv
  cases t with
  | s => exact Or.inl ⟨rfl, rfl⟩
  | var _ => cases hv
  | app l b =>
    simp only [noVars, Bool.and_eq_true] at hv
    cases l with
    | s =>
      have hb0 : redexCount b = 0 :=
        (redexCount_eq_zero_iff_isNormalForm b).mpr (fun b' hs => hnf (S ⋅ b') (.right hs))
      exact Or.inr (Or.inl ⟨rfl, b, rfl, hv.2, hb0⟩)
    | var _ => cases hv.1
    | app l1 a =>
      simp only [noVars, Bool.and_eq_true] at hv
      cases l1 with
      | s =>
        have ha0 : redexCount a = 0 :=
          (redexCount_eq_zero_iff_isNormalForm a).mpr
            (fun a' hs => hnf (S ⋅ a' ⋅ b) (.left (.right hs)))
        have hb0 : redexCount b = 0 :=
          (redexCount_eq_zero_iff_isNormalForm b).mpr
            (fun b' hs => hnf (S ⋅ a ⋅ b') (.right hs))
        exact Or.inr (Or.inr ⟨rfl, a, b, rfl, hv.1.2, hv.2, ha0, hb0⟩)
      | var _ => cases hv.1.1
      | app l2 x =>
        exfalso
        have hasHeadRedex : ∀ (u : Term), noVars u = true → 3 ≤ spineLen u → ¬ IsNormalForm u := by
          intro u hvu hsl hu_nf
          induction u with
          | s => cases hsl
          | var _ => cases hvu
          | app ul ur ihul _ =>
            have hvu_ul : noVars ul = true := ((Bool.and_eq_true _ _).mp hvu).1
            cases ul with
            | s => cases Nat.not_succ_le_zero 1 (Nat.le_of_succ_le_succ hsl)
            | var _ => cases hvu_ul
            | app ul1 uy =>
              have hvu_ul1 : noVars ul1 = true := ((Bool.and_eq_true _ _).mp hvu_ul).1
              cases ul1 with
              | s => cases Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hsl))
              | var _ => cases hvu_ul1
              | app ul2 ux =>
                cases ul2 with
                | s => exact hu_nf _ (Step.root ux uy ur)
                | var _ =>
                  have hvu_ul2 : noVars (.var _) = true := ((Bool.and_eq_true _ _).mp hvu_ul1).1
                  cases hvu_ul2
                | app p q =>
                  exact ihul hvu_ul (spineLen_ge3_four p q ux uy) (fun z hz => hu_nf (z ⋅ ur) (.left hz))
        exact hasHeadRedex (l2 ⋅ x ⋅ a ⋅ b) hv_full (spineLen_ge3_four l2 x a b) hnf

private theorem isRedexRoot_eq_false_of_spineGe3 {t : Term} (hsl : 3 ≤ spineLen t) (u : Term) :
    isRedexRoot (t ⋅ u) = false := by
  cases t with
  | s => cases hsl
  | var _ => cases hsl
  | app t1 _ =>
    cases t1 with
    | s => cases Nat.not_succ_le_zero 1 (Nat.le_of_succ_le_succ hsl)
    | var _ => cases Nat.not_succ_le_zero 1 (Nat.le_of_succ_le_succ hsl)
    | app t2 _ =>
      cases t2 with
      | s => cases Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hsl))
      | var _ => rfl
      | app _ _ => rfl

private theorem redexCount_appList_of_spineGe3 {t : Term} (hsl : 3 ≤ spineLen t) :
    ∀ (us : List Term), (∀ u ∈ us, redexCount u = 0) →
      redexCount (appList t us) = redexCount t
  | [], _ => rfl
  | u :: us, hus => by
    have hu0 : redexCount u = 0 := hus u (List.Mem.head _)
    have hroot : isRedexRoot (t ⋅ u) = false := isRedexRoot_eq_false_of_spineGe3 hsl u
    have hstep : redexCount (t ⋅ u) = redexCount t := by
      change (if isRedexRoot (t ⋅ u) then 1 else 0) + redexCount t + redexCount u = redexCount t
      rw [hroot, hu0]
      simp
    have hsl' : 3 ≤ spineLen (t ⋅ u) := Nat.le_trans hsl (Nat.le_add_left _ 1)
    exact (redexCount_appList_of_spineGe3 hsl' us (fun x hx => hus x (List.Mem.tail u hx))).trans hstep

theorem redexCount_StackHead {x y w : Term} {us : List Term}
    (hx : redexCount x = 0) (hy : redexCount y = 0) (hw : redexCount w = 0)
    (hus : ∀ u ∈ us, redexCount u = 0) :
    redexCount (appList (S ⋅ x ⋅ y ⋅ w) us) = 1 := by
  rw [redexCount_appList_of_spineGe3 (spineLen_ge3_four S x y w) us hus]
  change 1 + (0 + (0 + 0 + redexCount x) + redexCount y) + redexCount w = 1
  rw [hx, hy, hw]

theorem pure_line_four_cases {x y w : Term} {us : List Term}
    (hvx : noVars x = true) (hvy : noVars y = true) (hvw : noVars w = true)
    (hx : redexCount x = 0) (hy : redexCount y = 0) (hw : redexCount w = 0)
    (hus : ∀ u ∈ us, redexCount u = 0) :
    redexCount (appList ((x ⋅ w) ⋅ (y ⋅ w)) us) = 1 ↔
      ((spineLen x = 2 ∧ spineLen y ≤ 1) ∨
       (spineLen x = 1 ∧ spineLen y ≤ 1) ∨
       (spineLen x = 0 ∧ spineLen y ≤ 1 ∧ 1 ≤ us.length) ∨
       (spineLen x = 0 ∧ spineLen y = 2 ∧ us = [])) := by
  have _ := hvw
  have hrc_yw_le1 : ∀ {z : Term}, noVars z = true → redexCount z = 0 →
      (spineLen z ≤ 1 → redexCount (z ⋅ w) = 0) ∧ (spineLen z = 2 → redexCount (z ⋅ w) = 1) := by
    intro z hvz hcz
    rcases closed_nf_spineLen_le_2 hvz hcz with ⟨hs0, rfl⟩ | ⟨hs1, a, rfl, _, ha0⟩ | ⟨hs2, a, b, rfl, _, _, ha0, hb0⟩
    · constructor
      · intro _; change 0 + 0 + redexCount w = 0; rw [hw]
      · intro h2; rw [hs0] at h2; cases h2
    · constructor
      · intro _; change 0 + (0 + 0 + redexCount a) + redexCount w = 0; rw [ha0, hw]
      · intro h2; rw [hs1] at h2; cases h2
    · constructor
      · intro hle1; rw [hs2] at hle1; cases Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ hle1)
      · intro _; exact redexCount_StackHead (us := []) ha0 hb0 hw (fun _ h => by cases h)
  rcases closed_nf_spineLen_le_2 hvx hx with ⟨hsx0, rfl⟩ | ⟨hsx1, a, rfl, _, ha0⟩ | ⟨hsx2, a, b, rfl, _, _, ha0, hb0⟩
  · -- Case `x = S` (`spineLen x = 0`)
    rcases closed_nf_spineLen_le_2 hvy hy with ⟨hsy0, _⟩ | ⟨hsy1, _, _, _, _⟩ | ⟨hsy2, _, _, _, _, _, _, _⟩
    · have hyw0 : redexCount (y ⋅ w) = 0 := (hrc_yw_le1 hvy hy).1 (by rw [hsy0]; exact Nat.zero_le 1)
      cases us with
      | nil =>
        have htot : redexCount (appList ((S ⋅ w) ⋅ (y ⋅ w)) []) = 0 := by
          change 0 + (0 + 0 + redexCount w) + redexCount (y ⋅ w) = 0
          rw [hw, hyw0]
        rw [htot, hsx0, hsy0]; simp
      | cons u1 rest =>
        have hu1 : redexCount u1 = 0 := hus u1 (List.Mem.head _)
        have hrest : ∀ u ∈ rest, redexCount u = 0 := fun u hu => hus u (List.Mem.tail u1 hu)
        have htot : redexCount (appList ((S ⋅ w) ⋅ (y ⋅ w)) (u1 :: rest)) = 1 :=
          redexCount_StackHead (x := w) (y := y ⋅ w) (w := u1) (us := rest) hw hyw0 hu1 hrest
        rw [htot, hsx0, hsy0]; simp
    · have hyw0 : redexCount (y ⋅ w) = 0 := (hrc_yw_le1 hvy hy).1 (by rw [hsy1]; exact Nat.le_refl 1)
      cases us with
      | nil =>
        have htot : redexCount (appList ((S ⋅ w) ⋅ (y ⋅ w)) []) = 0 := by
          change 0 + (0 + 0 + redexCount w) + redexCount (y ⋅ w) = 0
          rw [hw, hyw0]
        rw [htot, hsx0, hsy1]; simp
      | cons u1 rest =>
        have hu1 : redexCount u1 = 0 := hus u1 (List.Mem.head _)
        have hrest : ∀ u ∈ rest, redexCount u = 0 := fun u hu => hus u (List.Mem.tail u1 hu)
        have htot : redexCount (appList ((S ⋅ w) ⋅ (y ⋅ w)) (u1 :: rest)) = 1 :=
          redexCount_StackHead (x := w) (y := y ⋅ w) (w := u1) (us := rest) hw hyw0 hu1 hrest
        rw [htot, hsx0, hsy1]; simp
    · have hyw1 : redexCount (y ⋅ w) = 1 := (hrc_yw_le1 hvy hy).2 hsy2
      cases us with
      | nil =>
        have htot : redexCount (appList ((S ⋅ w) ⋅ (y ⋅ w)) []) = 1 := by
          change 0 + (0 + 0 + redexCount w) + redexCount (y ⋅ w) = 1
          rw [hw, hyw1]
        rw [htot, hsx0, hsy2]; simp
      | cons u1 rest =>
        have hu1 : redexCount u1 = 0 := hus u1 (List.Mem.head _)
        have hrest : ∀ u ∈ rest, redexCount u = 0 := fun u hu => hus u (List.Mem.tail u1 hu)
        have hstep1 : redexCount (((S ⋅ w) ⋅ (y ⋅ w)) ⋅ u1) = 2 := by
          change 1 + (0 + (0 + 0 + redexCount w) + redexCount (y ⋅ w)) + redexCount u1 = 2
          rw [hw, hyw1, hu1]
        have htot : redexCount (appList ((S ⋅ w) ⋅ (y ⋅ w)) (u1 :: rest)) = 2 := by
          change redexCount (appList (((S ⋅ w) ⋅ (y ⋅ w)) ⋅ u1) rest) = 2
          rw [redexCount_appList_of_spineGe3 (spineLen_ge3_four S w (y ⋅ w) u1) rest hrest]
          exact hstep1
        rw [htot, hsx0, hsy2]; simp
  · -- Case `x = S ⋅ a` (`spineLen x = 1`)
    rw [redexCount_appList_of_spineGe3 (spineLen_ge3_four S a w (y ⋅ w)) us hus]
    have hbase : redexCount ((S ⋅ a ⋅ w) ⋅ (y ⋅ w)) = 1 + redexCount (y ⋅ w) := by
      change 1 + (0 + (0 + 0 + redexCount a) + redexCount w) + redexCount (y ⋅ w) = 1 + redexCount (y ⋅ w)
      rw [ha0, hw]
    rw [hbase, hsx1]
    rcases closed_nf_spineLen_le_2 hvy hy with ⟨hsy0, _⟩ | ⟨hsy1, _, _, _, _⟩ | ⟨hsy2, _, _, _, _, _, _, _⟩
    · rw [(hrc_yw_le1 hvy hy).1 (by rw [hsy0]; exact Nat.zero_le 1), hsy0]; simp
    · rw [(hrc_yw_le1 hvy hy).1 (by rw [hsy1]; exact Nat.le_refl 1), hsy1]; simp
    · rw [(hrc_yw_le1 hvy hy).2 hsy2, hsy2]; simp
  · -- Case `x = S ⋅ a ⋅ b` (`spineLen x = 2`)
    rw [redexCount_appList_of_spineGe3 (spineLen_ge3_four (S ⋅ a) b w (y ⋅ w)) us hus]
    have hx1 : redexCount (S ⋅ a ⋅ b ⋅ w) = 1 :=
      redexCount_StackHead (us := []) ha0 hb0 hw (fun _ h => by cases h)
    have hbase : redexCount ((S ⋅ a ⋅ b ⋅ w) ⋅ (y ⋅ w)) = 1 + redexCount (y ⋅ w) := by
      change 0 + redexCount (S ⋅ a ⋅ b ⋅ w) + redexCount (y ⋅ w) = 1 + redexCount (y ⋅ w)
      rw [hx1, Nat.zero_add]
    rw [hbase, hsx2]
    rcases closed_nf_spineLen_le_2 hvy hy with ⟨hsy0, _⟩ | ⟨hsy1, _, _, _, _⟩ | ⟨hsy2, _, _, _, _, _, _, _⟩
    · rw [(hrc_yw_le1 hvy hy).1 (by rw [hsy0]; exact Nat.zero_le 1), hsy0]; simp
    · rw [(hrc_yw_le1 hvy hy).1 (by rw [hsy1]; exact Nat.le_refl 1), hsy1]; simp
    · rw [(hrc_yw_le1 hvy hy).2 hsy2, hsy2]; simp

/-! ## 7. Spurious Multiway Halt Counterexamples on Protected-Trie & `D ⋅ Q` Tag Encodings -/

def protF (l r j : Term) : Term := S ⋅ l ⋅ (S ⋅ r ⋅ j)

def isProtectedF : Term → Bool
  | .app (.app .s _) (.app (.app .s _) _) => true
  | _ => false

/-- Exact `N`-step relation `StepsN` for counting concrete multiway shortcut lengths. -/
inductive StepsN : Nat → Term → Term → Prop where
  | zero (a : Term) : StepsN 0 a a
  | succ {n : Nat} {a b c : Term} : Step a b → StepsN n b c → StepsN (n + 1) a c

theorem stepsN_to_reduces {n : Nat} {a b : Term} (h : StepsN n a b) : Reduces a b := by
  induction h with
  | zero u => exact .refl u
  | succ hs _ ih => exact .next hs ih

theorem stepsN_left {n : Nat} {a a' : Term} (h : StepsN n a a') (b : Term) :
    StepsN n (a ⋅ b) (a' ⋅ b) := by
  induction h with
  | zero _ => exact .zero _
  | succ hs _ ih => exact .succ (.left hs) ih

theorem stepsN_right (a : Term) {n : Nat} {b b' : Term} (h : StepsN n b b') :
    StepsN n (a ⋅ b) (a ⋅ b') := by
  induction h with
  | zero _ => exact .zero _
  | succ hs _ ih => exact .succ (.right hs) ih

theorem local_open_6steps (m n : Term) :
    let n1 := B_comb ⋅ n
    let n2 := B_comb ⋅ n1
    let g := m ⋅ n2 ⋅ S
    StepsN 6 ((B_comb ⋅ m) ⋅ n2 ⋅ S) (protF g g ((n ⋅ S) ⋅ g)) := by
  intro n1 n2 g
  let q := m ⋅ n2
  have s1 : Step ((B_comb ⋅ m) ⋅ n2 ⋅ S) (S ⋅ n2 ⋅ q ⋅ S) := .left (.root S m n2)
  have s2 : Step (S ⋅ n2 ⋅ q ⋅ S) ((n2 ⋅ S) ⋅ g) := .root n2 q S
  have s3 : Step ((n2 ⋅ S) ⋅ g) ((B_comb ⋅ (n1 ⋅ S)) ⋅ g) := .left (.root S n1 S)
  have s4 : Step ((B_comb ⋅ (n1 ⋅ S)) ⋅ g) (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) := .root S (n1 ⋅ S) g
  have s5 : Step (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) (S ⋅ g ⋅ ((B_comb ⋅ (n ⋅ S)) ⋅ g)) :=
    .right (.left (.root S n S))
  have s6 : Step (S ⋅ g ⋅ ((B_comb ⋅ (n ⋅ S)) ⋅ g)) (protF g g ((n ⋅ S) ⋅ g)) :=
    .right (.root S (n ⋅ S) g)
  exact .succ s1 (.succ s2 (.succ s3 (.succ s4 (.succ s5 (.succ s6 (.zero _))))))

theorem halt_generator_7steps (k : Nat) (hk : 1 ≤ k) :
    ∃ opened, StepsN 7 (counterD 0 k) opened ∧ isProtectedF opened = true := by
  cases k with
  | zero => cases hk
  | succ k0 =>
    -- `counterD 0 (k0 + 1) = C_0 ⋅ C_{k0+1} ⋅ S →^1 C_{k0+2} ⋅ C_{k0+2} ⋅ S →^6 protF ...`
    let c1 := numeralC (k0 + 1)
    have hreset : Step (counterD 0 (k0 + 1)) ((B_comb ⋅ c1) ⋅ (B_comb ⋅ (B_comb ⋅ numeralC k0)) ⋅ S) :=
      .left (.root B_comb B_comb c1)
    have hopen := local_open_6steps c1 (numeralC k0)
    exact ⟨_, .succ hreset hopen, rfl⟩

/-- **Spurious Multiway Halt Counterexample 1 (Protected-Trie Encoding, 7 Contractions)**:
    In any bare-tree hub `protF (protF (counterD 0 (k+1)) progRing j1) queueRoot j0`
    (regardless of `progRing` and `queueRoot`, including non-halting cyclic-tag loops!),
    there exists an explicit **7-contraction** pure-`S` multiway path opening `HaltFlag` to
    `isProtectedF = true` without ever inspecting or modifying `progRing` or `queueRoot`! -/
theorem protected_trie_nonhalting_shortcut_7steps (k : Nat) (progRing queueRoot j0 j1 : Term) :
    ∃ openedFlag,
      StepsN 7
        (protF (protF (counterD 0 (k + 1)) progRing j1) queueRoot j0)
        (protF (protF openedFlag progRing j1) queueRoot j0) ∧
      isProtectedF openedFlag = true := by
  obtain ⟨opened, h7, hpf⟩ := halt_generator_7steps (k + 1) (Nat.le_add_left 1 k)
  have h_in_hp : StepsN 7 (protF (counterD 0 (k + 1)) progRing j1) (protF opened progRing j1) :=
    stepsN_left (stepsN_right S h7) (S ⋅ progRing ⋅ j1)
  have h_in_hub : StepsN 7
      (protF (protF (counterD 0 (k + 1)) progRing j1) queueRoot j0)
      (protF (protF opened progRing j1) queueRoot j0) :=
    stepsN_left (stepsN_right S h_in_hp) (S ⋅ queueRoot ⋅ j0)
  exact ⟨opened, h_in_hub, hpf⟩

def val1Tag : Term := S ⋅ (S ⋅ (S ⋅ B_comb ⋅ B_comb))
def liveCell1 (tail : Term) : Term := (B_comb ⋅ val1Tag) ⋅ tail
def tombCell1 (tail : Term) : Term := (S ⋅ tail) ⋅ (val1Tag ⋅ tail)
def pushNoOp (cont : Term) : Term := S ⋅ (S ⋅ cont) ⋅ S
def filinDispatcher (a0 a1 : Term) : Term := B_comb ⋅ (S ⋅ a0 ⋅ a1)

/-- **Spurious Multiway Halt Counterexample 2 (Filin `D ⋅ Q` Dispatcher, 5 Contractions)**:
    Starting from `filinDispatcher (pushNoOp cont) a1 ⋅ liveCell1 S` (a queue containing a live
    `1`-bit, where `a1` is any non-halting append action for bit `1` and `pushNoOp cont` is the
    `bit = 0` empty-append branch), an unguided **5-contraction** pure-`S` multiway sequence
    deletes `liveCell1 S → tombCell1 S` and executes the wrong `bit = 0` branch `pushNoOp cont`,
    reaching `cont ⋅ (S ⋅ tombCell1 S)` (empty decoded queue!) regardless of `a1`! -/
theorem filin_dispatcher_nonhalting_shortcut_5steps (cont a1 : Term) :
    let qEmpty := tombCell1 S
    let a0 := pushNoOp cont
    StepsN 5
      (filinDispatcher a0 a1 ⋅ liveCell1 S)
      (S ⋅ qEmpty ⋅ (((cont ⋅ (S ⋅ qEmpty)) ⋅ (qEmpty ⋅ (S ⋅ qEmpty))) ⋅ (a1 ⋅ qEmpty))) := by
  intro qEmpty a0
  have s1 : Step (filinDispatcher a0 a1 ⋅ liveCell1 S) (filinDispatcher a0 a1 ⋅ qEmpty) :=
    .right (.root S val1Tag S)
  have s2 : Step (filinDispatcher a0 a1 ⋅ qEmpty) (S ⋅ qEmpty ⋅ ((S ⋅ a0 ⋅ a1) ⋅ qEmpty)) :=
    .root S (S ⋅ a0 ⋅ a1) qEmpty
  have s3 : Step (S ⋅ qEmpty ⋅ ((S ⋅ a0 ⋅ a1) ⋅ qEmpty)) (S ⋅ qEmpty ⋅ ((a0 ⋅ qEmpty) ⋅ (a1 ⋅ qEmpty))) :=
    .right (.root a0 a1 qEmpty)
  have s4 : Step (S ⋅ qEmpty ⋅ ((a0 ⋅ qEmpty) ⋅ (a1 ⋅ qEmpty)))
      (S ⋅ qEmpty ⋅ (((S ⋅ cont ⋅ qEmpty) ⋅ (S ⋅ qEmpty)) ⋅ (a1 ⋅ qEmpty))) :=
    .right (.left (.root (S ⋅ cont) S qEmpty))
  have s5 : Step (S ⋅ qEmpty ⋅ (((S ⋅ cont ⋅ qEmpty) ⋅ (S ⋅ qEmpty)) ⋅ (a1 ⋅ qEmpty)))
      (S ⋅ qEmpty ⋅ (((cont ⋅ (S ⋅ qEmpty)) ⋅ (qEmpty ⋅ (S ⋅ qEmpty))) ⋅ (a1 ⋅ qEmpty))) :=
    .right (.left (.root cont qEmpty (S ⋅ qEmpty)))
  exact .succ s1 (.succ s2 (.succ s3 (.succ s4 (.succ s5 (.zero _)))))

/-! ## 8. Attack Line 2 Core: Waldmann's Polymorphic Merge Pair & Non-Cancellative Merge Tower -/

/-- Waldmann's non-convertible normal-form pair (`S(S(SS)S)(SSS)` vs `S((SS)(SSS))(S(SSS)S)`),
    from Barendregt et al. (2018), Section 5.6, p. 93. -/
def U1_waldmann : Term := S ⋅ (S ⋅ B_comb ⋅ S) ⋅ A_comb
def U2_waldmann : Term := S ⋅ (B_comb ⋅ A_comb) ⋅ (S ⋅ A_comb ⋅ S)

theorem u1_waldmann_isNF : IsNormalForm U1_waldmann :=
  oneStepList_eq_nil_iff.mp rfl

theorem u2_waldmann_isNF : IsNormalForm U2_waldmann :=
  oneStepList_eq_nil_iff.mp rfl

theorem waldmann_not_convS : ¬ ConvS U1_waldmann U2_waldmann :=
  distinct_nf_not_convS u1_waldmann_isNF u2_waldmann_isNF (by decide)

def waldmannCommonTarget (z : Term) : Term :=
  let sz := S ⋅ z
  let hz := sz ⋅ sz
  let qz := z ⋅ sz ⋅ hz
  (sz ⋅ hz) ⋅ qz

theorem u1_waldmann_5steps (z : Term) :
    StepsN 5 (U1_waldmann ⋅ z) (waldmannCommonTarget z) := by
  let sz := S ⋅ z
  let hz := sz ⋅ sz
  let s1 : Step (U1_waldmann ⋅ z) ((S ⋅ B_comb ⋅ S ⋅ z) ⋅ (A_comb ⋅ z)) :=
    .root (S ⋅ B_comb ⋅ S) A_comb z
  let s2 : Step ((S ⋅ B_comb ⋅ S ⋅ z) ⋅ (A_comb ⋅ z)) (((B_comb ⋅ z) ⋅ sz) ⋅ (A_comb ⋅ z)) :=
    .left (.root B_comb S z)
  let s3 : Step (((B_comb ⋅ z) ⋅ sz) ⋅ (A_comb ⋅ z)) ((S ⋅ sz ⋅ (z ⋅ sz)) ⋅ (A_comb ⋅ z)) :=
    .left (.root S z sz)
  let s4 : Step ((S ⋅ sz ⋅ (z ⋅ sz)) ⋅ (A_comb ⋅ z)) ((S ⋅ sz ⋅ (z ⋅ sz)) ⋅ hz) :=
    .right (.root S S z)
  let s5 : Step ((S ⋅ sz ⋅ (z ⋅ sz)) ⋅ hz) (waldmannCommonTarget z) :=
    .root sz (z ⋅ sz) hz
  exact .succ s1 (.succ s2 (.succ s3 (.succ s4 (.succ s5 (.zero _)))))

theorem u2_waldmann_6steps (z : Term) :
    StepsN 6 (U2_waldmann ⋅ z) (waldmannCommonTarget z) := by
  let sz := S ⋅ z
  let hz := sz ⋅ sz
  let s1 : Step (U2_waldmann ⋅ z) ((B_comb ⋅ A_comb ⋅ z) ⋅ (S ⋅ A_comb ⋅ S ⋅ z)) :=
    .root (B_comb ⋅ A_comb) (S ⋅ A_comb ⋅ S) z
  let s2 : Step ((B_comb ⋅ A_comb ⋅ z) ⋅ (S ⋅ A_comb ⋅ S ⋅ z)) ((sz ⋅ (A_comb ⋅ z)) ⋅ (S ⋅ A_comb ⋅ S ⋅ z)) :=
    .left (.root S A_comb z)
  let s3 : Step ((sz ⋅ (A_comb ⋅ z)) ⋅ (S ⋅ A_comb ⋅ S ⋅ z)) ((sz ⋅ hz) ⋅ (S ⋅ A_comb ⋅ S ⋅ z)) :=
    .left (.right (.root S S z))
  let s4 : Step ((sz ⋅ hz) ⋅ (S ⋅ A_comb ⋅ S ⋅ z)) ((sz ⋅ hz) ⋅ ((A_comb ⋅ z) ⋅ sz)) :=
    .right (.root A_comb S z)
  let s5 : Step ((sz ⋅ hz) ⋅ ((A_comb ⋅ z) ⋅ sz)) ((sz ⋅ hz) ⋅ (hz ⋅ sz)) :=
    .right (.left (.root S S z))
  let s6 : Step ((sz ⋅ hz) ⋅ (hz ⋅ sz)) (waldmannCommonTarget z) :=
    .right (.root z sz sz)
  exact .succ s1 (.succ s2 (.succ s3 (.succ s4 (.succ s5 (.succ s6 (.zero _))))))

/-- **Theorem (Waldmann's Order-1 Polymorphic Merge Identity in Pure `CL(S)`)**:
    Although `U1_waldmann ≠_S U2_waldmann`, applying **any** pure-`S` term `z` (open or closed,
    `SN` or non-`SN`!) makes `U1_waldmann ⋅ z` (5 steps) and `U2_waldmann ⋅ z` (6 steps)
    join at the exact same finite pure-`S` term `waldmannCommonTarget z`! -/
theorem waldmann_polymorphic_merge (z : Term) :
    ConvS (U1_waldmann ⋅ z) (U2_waldmann ⋅ z) :=
  convS_iff_common_reduct.mpr
    ⟨waldmannCommonTarget z,
     stepsN_to_reduces (u1_waldmann_5steps z),
     stepsN_to_reduces (u2_waldmann_6steps z)⟩

/-- Minimal size-7 / size-9 non-convertible normal-form merge pair (`N1_min ≠_S N2_min`, yet `N1_min ⋅ S =_S N2_min ⋅ S`). -/
def N1_min : Term := S ⋅ (S ⋅ A_comb ⋅ S) ⋅ S
def N2_min : Term := S ⋅ A_comb ⋅ (S ⋅ A_comb ⋅ S)

theorem n1_min_isNF : IsNormalForm N1_min := oneStepList_eq_nil_iff.mp rfl
theorem n2_min_isNF : IsNormalForm N2_min := oneStepList_eq_nil_iff.mp rfl

theorem minimal_merge_not_convS : ¬ ConvS N1_min N2_min :=
  distinct_nf_not_convS n1_min_isNF n2_min_isNF (by decide)

def K_min_common : Term :=
  let d := (S ⋅ B_comb) ⋅ (B_comb ⋅ B_comb)
  (S ⋅ d) ⋅ (B_comb ⋅ d)

theorem minimal_merge_at_s : ConvS (N1_min ⋅ S) (N2_min ⋅ S) := by
  have heq1 : completeDevIter 6 (N1_min ⋅ S) = K_min_common := rfl
  have heq2 : completeDevIter 6 (N2_min ⋅ S) = K_min_common := rfl
  have h1 : Reduces (N1_min ⋅ S) K_min_common := heq1 ▸ reduces_completeDevIter 6 (N1_min ⋅ S)
  have h2 : Reduces (N2_min ⋅ S) K_min_common := heq2 ▸ reduces_completeDevIter 6 (N2_min ⋅ S)
  exact convS_iff_common_reduct.mpr ⟨K_min_common, h1, h2⟩

/-- Explicit formal verification of the referee check: `SSSS ⋅ N1_min ⋅ S =_S SSSS ⋅ N2_min ⋅ S`
    (both non-normalizing terms share the finite common reduct `(K_min_common) ⋅ (B_comb ⋅ K_min_common)`!). -/
theorem ssss_n1_s_convS_ssss_n2_s :
    ConvS (S ⋅ S ⋅ S ⋅ S ⋅ N1_min ⋅ S) (S ⋅ S ⋅ S ⋅ S ⋅ N2_min ⋅ S) := by
  have open_ssss : ∀ (x : Term), Reduces (S ⋅ S ⋅ S ⋅ S ⋅ x ⋅ S) ((x ⋅ S) ⋅ (B_comb ⋅ (x ⋅ S))) := by
    intro x
    have s1 : Step (S ⋅ S ⋅ S ⋅ S ⋅ x ⋅ S) ((B_comb ⋅ B_comb) ⋅ x ⋅ S) :=
      .left (.left (.root S S S))
    have s2 : Step ((B_comb ⋅ B_comb) ⋅ x ⋅ S) ((S ⋅ x ⋅ (B_comb ⋅ x)) ⋅ S) :=
      .left (.root S B_comb x)
    have s3 : Step ((S ⋅ x ⋅ (B_comb ⋅ x)) ⋅ S) ((x ⋅ S) ⋅ (B_comb ⋅ x ⋅ S)) :=
      .root x (B_comb ⋅ x) S
    have s4 : Step ((x ⋅ S) ⋅ (B_comb ⋅ x ⋅ S)) ((x ⋅ S) ⋅ (B_comb ⋅ (x ⋅ S))) :=
      .right (.root S x S)
    exact .next s1 (.next s2 (.next s3 (.next s4 (.refl _))))
  have hc1 : ConvS (S ⋅ S ⋅ S ⋅ S ⋅ N1_min ⋅ S) ((N1_min ⋅ S) ⋅ (B_comb ⋅ (N1_min ⋅ S))) :=
    reduces_to_convS (open_ssss N1_min)
  have hc2 : ConvS (S ⋅ S ⋅ S ⋅ S ⋅ N2_min ⋅ S) ((N2_min ⋅ S) ⋅ (B_comb ⋅ (N2_min ⋅ S))) :=
    reduces_to_convS (open_ssss N2_min)
  have hmid : ConvS ((N1_min ⋅ S) ⋅ (B_comb ⋅ (N1_min ⋅ S))) ((N2_min ⋅ S) ⋅ (B_comb ⋅ (N2_min ⋅ S))) :=
    convS_app minimal_merge_at_s (convS_right B_comb minimal_merge_at_s)
  exact .trans hc1 (.trans hmid (.symm hc2))

def iterB : Nat → Term → Term
  | 0, u => u
  | n + 1, u => B_comb ⋅ iterB n u

theorem iterB_isNF {u : Term} (hu : IsNormalForm u) : ∀ (n : Nat), IsNormalForm (iterB n u)
  | 0 => hu
  | n + 1 => by
    have ihn := iterB_isNF hu n
    have h0 : redexCount (iterB n u) = 0 := (redexCount_eq_zero_iff_isNormalForm _).mpr ihn
    have h1 : redexCount (B_comb ⋅ iterB n u) = 0 := by
      change 0 + (0 + 0 + 0) + redexCount (iterB n u) = 0
      rw [h0]
    exact (redexCount_eq_zero_iff_isNormalForm _).mp h1

theorem iterB_inj {u v : Term} : ∀ (n : Nat), iterB n u = iterB n v → u = v
  | 0, h => h
  | n + 1, h => by
    injection h with _ hsub
    exact iterB_inj n hsub

theorem iterB_push_s (u : Term) : ∀ (n : Nat), Reduces (iterB n u ⋅ S) (iterB n (u ⋅ S))
  | 0 => .refl (u ⋅ S)
  | n + 1 =>
    .next (.root S (iterB n u) S) (reduces_right_ctx B_comb (iterB_push_s u n))

/-- **Infinite Non-Cancellative Normal-Form Merge Tower**:
    For every `n : Nat`, `iterB n N1_min` and `iterB n N2_min` are strictly non-convertible normal
    forms (`¬ ConvS (iterB n N1_min) (iterB n N2_min)`), yet collapse to convertible terms upon
    a single application to `S` (`ConvS (iterB n N1_min ⋅ S) (iterB n N2_min ⋅ S)`)! -/
theorem tower_nf_merge_family (n : Nat) :
    ¬ ConvS (iterB n N1_min) (iterB n N2_min) ∧
    ConvS (iterB n N1_min ⋅ S) (iterB n N2_min ⋅ S) := by
  constructor
  · exact distinct_nf_not_convS
      (iterB_isNF n1_min_isNF n)
      (iterB_isNF n2_min_isNF n)
      (fun heq => (by decide : N1_min ≠ N2_min) (iterB_inj n heq))
  · have hpush1 : ConvS (iterB n N1_min ⋅ S) (iterB n (N1_min ⋅ S)) :=
      reduces_to_convS (iterB_push_s N1_min n)
    have hpush2 : ConvS (iterB n N2_min ⋅ S) (iterB n (N2_min ⋅ S)) :=
      reduces_to_convS (iterB_push_s N2_min n)
    have iterB_conv : ∀ (k : Nat) {a b : Term}, ConvS a b → ConvS (iterB k a) (iterB k b) := by
      intro k a b hab
      induction k with
      | zero => exact hab
      | succ m ihm => exact convS_right B_comb ihm
    exact .trans hpush1 (.trans (iterB_conv n minimal_merge_at_s) (.symm hpush2))

end ZeroNavigatorMultiway

#print axioms ZeroNavigatorMultiway.convS_iff_common_reduct
#print axioms ZeroNavigatorMultiway.scott_q30_gk_cofinality
#print axioms ZeroNavigatorMultiway.decideReduces
#print axioms ZeroNavigatorMultiway.convS_sn_iff
#print axioms ZeroNavigatorMultiway.decideConvOfSN
#print axioms ZeroNavigatorMultiway.decideConvClosedSN
#print axioms ZeroNavigatorMultiway.rnf_convS_app_iff
#print axioms ZeroNavigatorMultiway.multiway_no_exclusive_second_thunk
#print axioms ZeroNavigatorMultiway.bool0_calls_first_only
#print axioms ZeroNavigatorMultiway.no_church_boolean_pair_in_pure_s
#print axioms ZeroNavigatorMultiway.pure_line_four_cases
#print axioms ZeroNavigatorMultiway.protected_trie_nonhalting_shortcut_7steps
#print axioms ZeroNavigatorMultiway.filin_dispatcher_nonhalting_shortcut_5steps
#print axioms ZeroNavigatorMultiway.waldmann_not_convS
#print axioms ZeroNavigatorMultiway.waldmann_polymorphic_merge
#print axioms ZeroNavigatorMultiway.minimal_merge_not_convS
#print axioms ZeroNavigatorMultiway.minimal_merge_at_s
#print axioms ZeroNavigatorMultiway.ssss_n1_s_convS_ssss_n2_s
#print axioms ZeroNavigatorMultiway.tower_nf_merge_family
