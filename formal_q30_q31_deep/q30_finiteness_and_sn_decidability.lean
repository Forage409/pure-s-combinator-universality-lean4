import zero_navigator_multiway.multiway_and_q30_theorems

/-!
# Deep Word-Problem & Finiteness Theorems for Dana Scott's Question 30 (`ConvS` in `CL(S)`)

Machine-checked in Lean 4.33.1 with **zero `sorry`, zero `Classical.choice`, zero `native_decide`,
and zero custom axioms** (`#print axioms` uses at most `[propext, Quot.sound]`).

## Main Theorems

1. **Exact Leaf-Growth Law & Atomic-`S` vs Compound-Argument Dichotomy**
   (`leaves_root_exact`, `step_leaves_eq_iff_stepAtomicArg`, `step_closed_leaves_eq_iff_stepAtomicS`,
    `step_compound_strict_leaves_increase`):
   - Every single-step reduction `Step a b` satisfies `leaves a ≤ leaves b`.
   - On a root contraction `S ⋅ x ⋅ y ⋅ z → (x ⋅ z) ⋅ (y ⋅ z)`,
     `leaves ((x ⋅ z) ⋅ (y ⋅ z)) = leaves (S ⋅ x ⋅ y ⋅ z) + (leaves z - 1)`.
   - On closed pure-`S` terms, `Step a b` preserves leaf count (`leaves a = leaves b`) **if and only if**
     the contracted redex has atomic third argument `z = S` (`StepAtomicS a b`); whenever `z = u ⋅ v`,
     `leaves` strictly increases by `leaves (u ⋅ v) - 1 ≥ 1`.

2. **Normal-Form Equivalence-Class Structure & Constructive Finiteness Theorem**
   (`convS_normalForm_iff_reduces`, `convS_normalForm_leaves_le`, `equivClassOfSN`,
    `equivClassOfSN_spec`, `closed_normalizing_equivClass_finite`):
   - For every normal form `v`, `[v]_{=_S} = { n | Reduces n v }`, and every `n =_S v` satisfies
     `leaves n ≤ leaves v`.
   - For every closed normalizing (`SN` / `WN`) pure-`S` term `m`, its closed `=_S`-equivalence class
     `[m]_{=_S}` is **strictly finite**, constructively enumerated without duplicates by `equivClassOfSN`.

3. **Exact Syntactic Characterization of Isolated Normal Forms (`[v]_{=_S} = {v}`) & Infinite Families**
   (`exists_step_iff_hasReductPattern`, `isolated_normalForm_iff`, `isolatedNF_family`):
   - A term `v` admits a 1-step expansion (`∃ m, Step m v`) **if and only if** `hasReductPattern v = true`
     (it contains a subterm `(x ⋅ z) ⋅ (y ⋅ z)` with identical right subterms).
   - Hence a normal form `v` is isolated under `=_S` (`∀ n, ConvS n v ↔ n = v`) **if and only if**
     `hasReductPattern v = false`.
   - Exhibits explicit infinite pairwise-distinct families of isolated closed normal forms
     (`isoTower` of spine length 1 and `isolatedSpine2NF` of spine length 2).

4. **Asymmetric Decidability of `ConvS` Across `SN × All` Closed `S`-Terms**
   (`decideConvWithSN`):
   - Total, computable decision procedure `decideConvWithSN m hm n hvm hvn : Decidable (ConvS m n)`
     deciding membership in `[m]_{=_S}` across **all** closed pure-`S` terms `n` (including
     non-terminating `n`) whenever `m ∈ SN`.

5. **Canonical RNF Spine Decomposition (Frozen Trailing-`S` Cancellation) for Unsolvable Convertibility**
   (`unsolvable_rightApp_convS_iff`):
   - For **any** two unsolvable terms `m, n` (`¬ HasHNF m`, `¬ HasHNF n`) with compound right children
     (`rightIsApp m = true`, `rightIsApp n = true`) and all `j, k : Nat`,
     `ConvS (appS m j) (appS n k) ↔ (j = k ∧ ConvS m n)`.
-/

namespace FormalQ30Q31Deep

open FormalAlgebra
open ZeroNavigatorMultiway

/-! ## Section 1: Exact Leaf-Growth Law & Atomic vs Compound Redex Dichotomy -/

/-- Exact leaf-count identity for any root `S`-contraction:
    `leaves ((x ⋅ z) ⋅ (y ⋅ z)) = leaves (S ⋅ x ⋅ y ⋅ z) + (leaves z - 1)`. -/
theorem leaves_root_exact (x y z : Term) :
    leaves ((x ⋅ z) ⋅ (y ⋅ z)) = leaves (S ⋅ x ⋅ y ⋅ z) + (leaves z - 1) := by
  have hz : 1 ≤ leaves z := leaves_pos z
  change (leaves x + leaves z) + (leaves y + leaves z) =
    (((1 + leaves x) + leaves y) + leaves z) + (leaves z - 1)
  omega

/-- On a compound third argument `z = u ⋅ v`, a root `S`-contraction strictly increases leaf count
    by `leaves (u ⋅ v) - 1 ≥ 1`. -/
theorem step_compound_strict_leaves_increase (x y u v : Term) :
    leaves ((x ⋅ (u ⋅ v)) ⋅ (y ⋅ (u ⋅ v))) =
      leaves (S ⋅ x ⋅ y ⋅ (u ⋅ v)) + (leaves (u ⋅ v) - 1) ∧
    1 ≤ leaves (u ⋅ v) - 1 ∧
    leaves (S ⋅ x ⋅ y ⋅ (u ⋅ v)) < leaves ((x ⋅ (u ⋅ v)) ⋅ (y ⋅ (u ⋅ v))) := by
  have hu : 1 ≤ leaves u := leaves_pos u
  have hv : 1 ≤ leaves v := leaves_pos v
  have huv : 2 ≤ leaves (u ⋅ v) := by change 2 ≤ leaves u + leaves v; omega
  have hex := leaves_root_exact x y (u ⋅ v)
  refine ⟨hex, by omega, by omega⟩

/-- Single-step reduction contracting a redex `S ⋅ x ⋅ y ⋅ z` with atomic `z` (`leaves z = 1`). -/
inductive StepAtomicArg : Term → Term → Prop where
  | root (x y z : Term) : leaves z = 1 → StepAtomicArg (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : StepAtomicArg a a' → StepAtomicArg (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : StepAtomicArg b b' → StepAtomicArg (a ⋅ b) (a ⋅ b')

/-- Single-step reduction contracting a redex `S ⋅ x ⋅ y ⋅ S` (third argument literally `S`). -/
inductive StepAtomicS : Term → Term → Prop where
  | root (x y : Term) : StepAtomicS (S ⋅ x ⋅ y ⋅ S) ((x ⋅ S) ⋅ (y ⋅ S))
  | left {a a' b : Term} : StepAtomicS a a' → StepAtomicS (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : StepAtomicS b b' → StepAtomicS (a ⋅ b) (a ⋅ b')

theorem stepAtomicS_to_step {a b : Term} (h : StepAtomicS a b) : Step a b := by
  induction h with
  | root x y => exact Step.root x y S
  | left _ ih => exact Step.left ih
  | right _ ih => exact Step.right ih

theorem stepAtomicArg_leaves_eq {a b : Term} (h : StepAtomicArg a b) : leaves a = leaves b := by
  induction h with
  | root x y z hz1 =>
    have hex := leaves_root_exact x y z
    omega
  | @left l l' r _ ih =>
    change leaves l + leaves r = leaves l' + leaves r
    omega
  | @right l r r' _ ih =>
    change leaves l + leaves r = leaves l + leaves r'
    omega

/-- **Exact Leaf-Preservation Characterization (Open or Closed Terms)**:
    Given `Step a b`, `leaves a = leaves b` holds iff the contracted redex has `leaves z = 1`. -/
theorem step_leaves_eq_iff_stepAtomicArg {a b : Term} (hs : Step a b) :
    leaves a = leaves b ↔ StepAtomicArg a b := by
  refine ⟨?_, stepAtomicArg_leaves_eq⟩
  induction hs with
  | root x y z =>
    intro heq
    have hex := leaves_root_exact x y z
    have hpos : 1 ≤ leaves z := leaves_pos z
    exact StepAtomicArg.root x y z (by omega)
  | @left l l' r _ ih =>
    intro heq
    have hleq : leaves l = leaves l' := by
      change leaves l + leaves r = leaves l' + leaves r at heq
      omega
    exact StepAtomicArg.left (ih hleq)
  | @right l r r' _ ih =>
    intro heq
    have hreq : leaves r = leaves r' := by
      change leaves l + leaves r = leaves l + leaves r' at heq
      omega
    exact StepAtomicArg.right (ih hreq)

private theorem closed_leaves_eq_one_eq_s {t : Term} (hv : noVars t = true) (hl : leaves t = 1) :
    t = S := by
  cases t with
  | s => rfl
  | var _ => cases hv
  | app a b =>
    have ha := leaves_pos a
    have hb := leaves_pos b
    change leaves a + leaves b = 1 at hl
    omega

private theorem stepAtomicArg_closed_iff_stepAtomicS {a b : Term} (hv : noVars a = true) :
    StepAtomicArg a b ↔ StepAtomicS a b := by
  constructor
  · intro h
    induction h with
    | root x y z hz1 =>
      have hvz : noVars z = true := ((Bool.and_eq_true _ _).mp hv).2
      have hzs : z = S := closed_leaves_eq_one_eq_s hvz hz1
      subst hzs
      exact StepAtomicS.root x y
    | left _ ih =>
      exact StepAtomicS.left (ih ((Bool.and_eq_true _ _).mp hv).1)
    | right _ ih =>
      exact StepAtomicS.right (ih ((Bool.and_eq_true _ _).mp hv).2)
  · intro h
    induction h with
    | root x y => exact StepAtomicArg.root x y S rfl
    | left _ ih => exact StepAtomicArg.left (ih ((Bool.and_eq_true _ _).mp hv).1)
    | right _ ih => exact StepAtomicArg.right (ih ((Bool.and_eq_true _ _).mp hv).2)

/-- **Closed Leaf-Preservation Dichotomy**:
    On closed pure-`S` terms (`noVars a = true`), `Step a b` preserves leaf count (`leaves a = leaves b`)
    **if and only if** it contracts a redex `S ⋅ x ⋅ y ⋅ S` (`StepAtomicS a b`); otherwise
    `leaves a + 1 ≤ leaves b`. -/
theorem step_closed_leaves_eq_iff_stepAtomicS {a b : Term}
    (hv : noVars a = true) (hs : Step a b) :
    (leaves a = leaves b ↔ StepAtomicS a b) ∧
    (¬ StepAtomicS a b → leaves a + 1 ≤ leaves b) := by
  have hiff : leaves a = leaves b ↔ StepAtomicS a b :=
    (step_leaves_eq_iff_stepAtomicArg hs).trans (stepAtomicArg_closed_iff_stepAtomicS hv)
  refine ⟨hiff, ?_⟩
  intro hnot
  have hle : leaves a ≤ leaves b := leaves_mono_step hs
  have hne : leaves a ≠ leaves b := fun heq => hnot (hiff.mp heq)
  omega

/-! ## Section 2: Normal-Form Equivalence Classes & Strict Finiteness Theorem -/

/-- **Normal-Form Equivalence Class Law**:
    For every normal form `v`, `[v]_{=_S} = { n | Reduces n v }`. -/
theorem convS_normalForm_iff_reduces {v : Term} (hnf : IsNormalForm v) (n : Term) :
    ConvS n v ↔ Reduces n v := by
  constructor
  · intro hconv
    obtain ⟨w, hnw, hvw⟩ := convS_iff_common_reduct.mp hconv
    have hveq : v = w := isNormalForm_reduces_eq hnf hvw
    subst hveq
    exact hnw
  · exact reduces_to_convS

/-- **Normal-Form Leaf Upper Bound**:
    Every term `n` convertible to a normal form `v` satisfies `leaves n ≤ leaves v`. -/
theorem convS_normalForm_leaves_le {v n : Term} (hnf : IsNormalForm v) (hconv : ConvS n v) :
    leaves n ≤ leaves v :=
  leaves_mono_reduces ((convS_normalForm_iff_reduces hnf n).mp hconv)

/-! ### Constructive Duplicate-Free Enumeration of Closed `S`-Terms by Leaf Count -/

/-- Inductive duplicate-freeness predicate (bridged directly to `List.Nodup`). -/
inductive NoDupList {α : Type} : List α → Prop where
  | nil : NoDupList []
  | cons {x : α} {xs : List α} : x ∉ xs → NoDupList xs → NoDupList (x :: xs)

theorem noDupList_to_nodup {α : Type} {xs : List α} (h : NoDupList xs) : xs.Nodup := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons x xs hnot _ ih =>
    exact List.Pairwise.cons (fun y hy heq => hnot (heq ▸ hy)) ih

private def appCartesian : List Term → List Term → List Term
  | [], _ => []
  | x :: xs, ys => ys.map (fun b => x ⋅ b) ++ appCartesian xs ys

private theorem mem_appCartesian_iff {xs ys : List Term} {t : Term} :
    t ∈ appCartesian xs ys ↔ ∃ a ∈ xs, ∃ b ∈ ys, t = a ⋅ b := by
  induction xs with
  | nil =>
    simp [appCartesian]
  | cons x xs ih =>
    simp only [appCartesian, List.mem_append, List.mem_map, List.mem_cons, ih]
    constructor
    · rintro (⟨b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
      · exact ⟨x, Or.inl rfl, b, hb, rfl⟩
      · exact ⟨a, Or.inr ha, b, hb, rfl⟩
    · rintro ⟨a, rfl | ha, b, hb, rfl⟩
      · exact Or.inl ⟨b, hb, rfl⟩
      · exact Or.inr ⟨a, ha, b, hb, rfl⟩

private theorem noDup_map_app_right (a : Term) {ys : List Term} (hy : NoDupList ys) :
    NoDupList (ys.map (fun b => a ⋅ b)) := by
  induction hy with
  | nil => exact NoDupList.nil
  | @cons y ys hnot _ ih =>
    refine NoDupList.cons ?_ ih
    rw [List.mem_map]
    rintro ⟨y', hy', heq⟩
    injection heq with _ hy_eq
    subst hy_eq
    exact hnot hy'

private theorem noDup_append_of_disjoint {α : Type} {l1 l2 : List α}
    (h1 : NoDupList l1) (h2 : NoDupList l2) (hdisj : ∀ x, x ∈ l1 → x ∈ l2 → False) :
    NoDupList (l1 ++ l2) := by
  induction h1 with
  | nil => exact h2
  | @cons a as hnot _ ih =>
    refine NoDupList.cons ?_ (ih (fun x hx1 hx2 => hdisj x (List.Mem.tail a hx1) hx2))
    intro hmem
    rcases List.mem_append.mp hmem with ha1 | ha2
    · exact hnot ha1
    · exact hdisj a (List.Mem.head _) ha2

private theorem noDup_appCartesian {xs ys : List Term} (hx : NoDupList xs) (hy : NoDupList ys) :
    NoDupList (appCartesian xs ys) := by
  induction hx with
  | nil => exact NoDupList.nil
  | @cons x xs hnot _ ih =>
    refine noDup_append_of_disjoint (noDup_map_app_right x hy) ih ?_
    intro t ht1 ht2
    rw [List.mem_map] at ht1
    obtain ⟨b1, _, rfl⟩ := ht1
    obtain ⟨a2, ha2, _, _, heq⟩ := mem_appCartesian_iff.mp ht2
    injection heq with hxa _
    subst hxa
    exact hnot ha2

private def closedTermsLoop (recFn : Nat → List Term) (total : Nat) : Nat → List Term
  | 0 => []
  | i + 1 => appCartesian (recFn (i + 1)) (recFn (total - (i + 1))) ++ closedTermsLoop recFn total i

/-- Structurally recursive enumerator of all closed `S`-terms with exact leaf count `k` (given `k ≤ fuel`). -/
def closedTermsExactAux : Nat → Nat → List Term
  | 0, _ => []
  | _ + 1, 0 => []
  | _ + 1, 1 => [S]
  | fuel + 1, k + 2 => closedTermsLoop (closedTermsExactAux fuel) (k + 2) (k + 1)

def closedTermsExact (k : Nat) : List Term :=
  closedTermsExactAux k k

private theorem closedTermsExactAux_spec :
    ∀ (fuel k : Nat), k ≤ fuel →
      NoDupList (closedTermsExactAux fuel k) ∧
      (∀ t : Term, t ∈ closedTermsExactAux fuel k ↔ (noVars t = true ∧ leaves t = k))
  | 0, k, hle => by
    have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨NoDupList.nil, fun t => ?_⟩
    simp only [closedTermsExactAux, List.not_mem_nil, false_iff]
    rintro ⟨_, hl⟩
    have hp := leaves_pos t
    omega
  | _ + 1, 0, _ => by
    refine ⟨NoDupList.nil, fun t => ?_⟩
    simp only [closedTermsExactAux, List.not_mem_nil, false_iff]
    rintro ⟨_, hl⟩
    have hp := leaves_pos t
    omega
  | _ + 1, 1, _ => by
    refine ⟨NoDupList.cons (by simp) NoDupList.nil, fun t => ?_⟩
    simp only [closedTermsExactAux, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨hv, hl⟩; exact closed_leaves_eq_one_eq_s hv hl
  | fuel + 1, k + 2, hle => by
    have hloop :
        ∀ (m : Nat), m ≤ k + 1 →
          NoDupList (closedTermsLoop (closedTermsExactAux fuel) (k + 2) m) ∧
          (∀ t : Term, t ∈ closedTermsLoop (closedTermsExactAux fuel) (k + 2) m ↔
            ∃ a b, t = a ⋅ b ∧ noVars a = true ∧ noVars b = true ∧
              1 ≤ leaves a ∧ leaves a ≤ m ∧ leaves a + leaves b = k + 2) := by
      intro m hm
      induction m with
      | zero =>
        refine ⟨NoDupList.nil, fun t => ?_⟩
        simp only [closedTermsLoop, List.not_mem_nil, false_iff]
        rintro ⟨_, _, _, _, _, h1, h0, _⟩
        omega
      | succ i ih =>
        have hi_le : i ≤ k + 1 := by omega
        obtain ⟨ih_nd, ih_mem⟩ := ih hi_le
        have hL_le : i + 1 ≤ fuel := by omega
        have hR_le : (k + 2) - (i + 1) ≤ fuel := by omega
        obtain ⟨ndL, memL⟩ := closedTermsExactAux_spec fuel (i + 1) hL_le
        obtain ⟨ndR, memR⟩ := closedTermsExactAux_spec fuel ((k + 2) - (i + 1)) hR_le
        have ndCur : NoDupList (appCartesian (closedTermsExactAux fuel (i + 1))
                                             (closedTermsExactAux fuel ((k + 2) - (i + 1)))) :=
          noDup_appCartesian ndL ndR
        have ndAll : NoDupList (closedTermsLoop (closedTermsExactAux fuel) (k + 2) (i + 1)) := by
          unfold closedTermsLoop
          refine noDup_append_of_disjoint ndCur ih_nd ?_
          intro t ht1 ht2
          obtain ⟨a1, ha1, b1, _, rfl⟩ := mem_appCartesian_iff.mp ht1
          have hla1 : leaves a1 = i + 1 := ((memL a1).mp ha1).2
          obtain ⟨a2, _, heq, _, _, _, hla2_le, _⟩ := (ih_mem (a1 ⋅ b1)).mp ht2
          injection heq with ha_eq _
          subst ha_eq
          omega
        refine ⟨ndAll, fun t => ?_⟩
        simp only [closedTermsLoop, List.mem_append, mem_appCartesian_iff, ih_mem]
        constructor
        · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨a, b, rfl, hva, hvb, h1, hle_i, hsum⟩)
          · obtain ⟨hva, hla⟩ := (memL a).mp ha
            obtain ⟨hvb, hlb⟩ := (memR b).mp hb
            exact ⟨a, b, rfl, hva, hvb, by omega, by omega, by omega⟩
          · exact ⟨a, b, rfl, hva, hvb, h1, by omega, hsum⟩
        · rintro ⟨a, b, rfl, hva, hvb, h1, hle_si, hsum⟩
          by_cases heq : leaves a = i + 1
          · exact Or.inl ⟨a, (memL a).mpr ⟨hva, heq⟩, b, (memR b).mpr ⟨hvb, by omega⟩, rfl⟩
          · exact Or.inr ⟨a, b, rfl, hva, hvb, h1, by omega, hsum⟩
    obtain ⟨nd_k, mem_k⟩ := hloop (k + 1) (Nat.le_refl _)
    simp only [closedTermsExactAux]
    refine ⟨nd_k, fun t => ?_⟩
    rw [mem_k]
    constructor
    · rintro ⟨a, b, rfl, hva, hvb, _, _, hsum⟩
      exact ⟨(Bool.and_eq_true _ _).mpr ⟨hva, hvb⟩, hsum⟩
    · rintro ⟨hv, hl⟩
      cases t with
      | s => cases hl
      | var _ => cases hv
      | app a b =>
        have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
        have ha1 := leaves_pos a
        have hb1 := leaves_pos b
        change leaves a + leaves b = k + 2 at hl
        exact ⟨a, b, rfl, hva, hvb, ha1, by omega, hl⟩

theorem closedTermsExact_noDup (k : Nat) : NoDupList (closedTermsExact k) :=
  (closedTermsExactAux_spec k k (Nat.le_refl k)).1

theorem mem_closedTermsExact_iff (k : Nat) (t : Term) :
    t ∈ closedTermsExact k ↔ (noVars t = true ∧ leaves t = k) :=
  (closedTermsExactAux_spec k k (Nat.le_refl k)).2 t

/-- Duplicate-free list of all closed pure-`S` terms with `leaves t ≤ L`. -/
def closedTermsUpTo : Nat → List Term
  | 0 => []
  | L + 1 => closedTermsUpTo L ++ closedTermsExact (L + 1)

theorem mem_closedTermsUpTo_iff (L : Nat) (t : Term) :
    t ∈ closedTermsUpTo L ↔ (noVars t = true ∧ leaves t ≤ L) := by
  induction L with
  | zero =>
    simp only [closedTermsUpTo, List.not_mem_nil, false_iff]
    rintro ⟨_, hl⟩
    have hp := leaves_pos t
    omega
  | succ L ih =>
    simp only [closedTermsUpTo, List.mem_append, ih, mem_closedTermsExact_iff]
    constructor
    · rintro (⟨hv, hle⟩ | ⟨hv, heq⟩)
      · exact ⟨hv, by omega⟩
      · exact ⟨hv, by omega⟩
    · rintro ⟨hv, hle⟩
      by_cases heq : leaves t = L + 1
      · exact Or.inr ⟨hv, heq⟩
      · exact Or.inl ⟨hv, by omega⟩

theorem closedTermsUpTo_noDup (L : Nat) : NoDupList (closedTermsUpTo L) := by
  induction L with
  | zero => exact NoDupList.nil
  | succ L ih =>
    refine noDup_append_of_disjoint ih (closedTermsExact_noDup (L + 1)) ?_
    intro t ht1 ht2
    have hle := ((mem_closedTermsUpTo_iff L t).mp ht1).2
    have heq := ((mem_closedTermsExact_iff (L + 1) t).mp ht2).2
    omega

private theorem noDup_filter_local {α : Type} (p : α → Bool) {xs : List α} (h : NoDupList xs) :
    NoDupList (xs.filter p) := by
  induction h with
  | nil => exact NoDupList.nil
  | @cons a as hnot _ ih =>
    simp only [List.filter]
    cases hp : p a
    · exact ih
    · refine NoDupList.cons ?_ ih
      rw [List.mem_filter]
      exact fun ⟨hm, _⟩ => hnot hm

/-- Computable duplicate-free enumeration of the closed `=_S`-equivalence class `[m]_{=_S}`
    for any strongly normalizing term `m`. -/
def equivClassOfSN (m : Term) (hm : StrongNormalizing m) : List Term :=
  let nf := (nfOfSN m hm).1
  (closedTermsUpTo (leaves nf)).filter (fun n => reducesBool n nf)

/-- **Exact Specification of `equivClassOfSN`**:
    `equivClassOfSN m hm` is duplicate-free (`List.Nodup`) and contains **precisely** all closed
    pure-`S` terms convertible to `m`, each bounded in size by `leaves (nfOfSN m hm).1`. -/
theorem equivClassOfSN_spec (m : Term) (hm : StrongNormalizing m) :
    (equivClassOfSN m hm).Nodup ∧
    (∀ n ∈ equivClassOfSN m hm, noVars n = true ∧ leaves n ≤ leaves (nfOfSN m hm).1) ∧
    (∀ n : Term, noVars n = true → (n ∈ equivClassOfSN m hm ↔ ConvS n m)) := by
  let nf := (nfOfSN m hm).1
  have hred_m : Reduces m nf := (nfOfSN m hm).2.1
  have hnf : IsNormalForm nf := (nfOfSN m hm).2.2
  have hnd : (equivClassOfSN m hm).Nodup :=
    noDupList_to_nodup (noDup_filter_local _ (closedTermsUpTo_noDup (leaves nf)))
  refine ⟨hnd, ?_, ?_⟩
  · intro n hn
    simp only [equivClassOfSN, List.mem_filter, mem_closedTermsUpTo_iff] at hn
    exact hn.1
  · intro n hvn
    simp only [equivClassOfSN, List.mem_filter, mem_closedTermsUpTo_iff, reducesBool_iff]
    have hconv_m_nf : ConvS m nf := reduces_to_convS hred_m
    constructor
    · rintro ⟨_, hr_n_nf⟩
      exact ConvS.trans (reduces_to_convS hr_n_nf) (ConvS.symm hconv_m_nf)
    · intro hconv_n_m
      have hconv_n_nf : ConvS n nf := ConvS.trans hconv_n_m hconv_m_nf
      have hr_n_nf : Reduces n nf := (convS_normalForm_iff_reduces hnf n).mp hconv_n_nf
      exact ⟨⟨hvn, leaves_mono_reduces hr_n_nf⟩, hr_n_nf⟩

/-- **Strict Equivalence-Class Finiteness Theorem for Normalizing Pure-`S` Terms**:
    For every closed normalizing pure-`S` term `m` (`HasNormalForm m`), `[m]_{=_S}` on closed
    pure-`S` terms is strictly finite (enumerated by a concrete duplicate-free `List Term`). -/
theorem closed_normalizing_equivClass_finite {m : Term}
    (_hvm : noVars m = true) (hwn : HasNormalForm m) :
    ∃ cls : List Term,
      cls.Nodup ∧
      (∀ n : Term, noVars n = true → (n ∈ cls ↔ ConvS n m)) := by
  have hsn : StrongNormalizing m := (sn_iff_wn m).mpr hwn
  have hspec := equivClassOfSN_spec m hsn
  exact ⟨equivClassOfSN m hsn, hspec.1, hspec.2.2⟩

/-! ## Section 3: Isolated Normal Forms (`[v]_{=_S} = {v}`) & Infinite Families -/

/-- Checks whether `l = x ⋅ z1` and `r = y ⋅ z2` share the exact same right argument `z1 = z2`. -/
def sameRightArg : Term → Term → Bool
  | .app _ z1, .app _ z2 => decide (z1 = z2)
  | _, _ => false

/-- Linear-time syntactic check for whether `t` contains any `S`-reduct pattern `(x ⋅ z) ⋅ (y ⋅ z)`. -/
def hasReductPattern : Term → Bool
  | .s => false
  | .var _ => false
  | .app l r => sameRightArg l r || hasReductPattern l || hasReductPattern r

private theorem sameRightArg_iff (l r : Term) :
    sameRightArg l r = true ↔ ∃ x y z, l = x ⋅ z ∧ r = y ⋅ z := by
  cases l with
  | s =>
    constructor
    · intro h; cases h
    · rintro ⟨_, _, _, h, _⟩; cases h
  | var _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, _, _, h, _⟩; cases h
  | app x z1 =>
    cases r with
    | s =>
      constructor
      · intro h; cases h
      · rintro ⟨_, _, _, _, h⟩; cases h
    | var _ =>
      constructor
      · intro h; cases h
      · rintro ⟨_, _, _, _, h⟩; cases h
    | app y z2 =>
      simp only [sameRightArg]
      constructor
      · intro hd
        have hz : z1 = z2 := of_decide_eq_true hd
        subst hz
        exact ⟨x, y, z1, rfl, rfl⟩
      · rintro ⟨_, _, z, hl, hr⟩
        injection hl with _ hz1
        injection hr with _ hz2
        exact decide_eq_true (hz1.trans hz2.symm)

private theorem closed_pred_of_hasReductPattern :
    ∀ {v : Term}, noVars v = true → hasReductPattern v = true →
      ∃ m : Term, noVars m = true ∧ Step m v
  | .s, _, hp => by cases hp
  | .var _, hv, _ => by cases hv
  | .app l r, hv, hp => by
    have ⟨hvl, hvr⟩ := (Bool.and_eq_true _ _).mp hv
    simp only [hasReductPattern, Bool.or_eq_true, sameRightArg_iff] at hp
    rcases hp with (⟨x, y, z, rfl, rfl⟩ | hl) | hr
    · have ⟨hvx, hvz⟩ := (Bool.and_eq_true _ _).mp hvl
      have ⟨hvy, _⟩ := (Bool.and_eq_true _ _).mp hvr
      have hvm : noVars (S ⋅ x ⋅ y ⋅ z) = true := by
        simp [S, noVars, hvx, hvy, hvz]
      exact ⟨S ⋅ x ⋅ y ⋅ z, hvm, Step.root x y z⟩
    · obtain ⟨l0, hvl0, hsl0⟩ := closed_pred_of_hasReductPattern hvl hl
      exact ⟨l0 ⋅ r, (Bool.and_eq_true _ _).mpr ⟨hvl0, hvr⟩, Step.left hsl0⟩
    · obtain ⟨r0, hvr0, hsr0⟩ := closed_pred_of_hasReductPattern hvr hr
      exact ⟨l ⋅ r0, (Bool.and_eq_true _ _).mpr ⟨hvl, hvr0⟩, Step.right hsr0⟩

/-- **Exact 1-Step Predecessor Theorem**:
    A term `v` admits a backward reduction step `∃ m, Step m v` (and with `noVars m = true` whenever
    `noVars v = true`) **if and only if** `hasReductPattern v = true`. -/
theorem exists_step_iff_hasReductPattern (v : Term) :
    ((∃ m, Step m v) ↔ hasReductPattern v = true) ∧
    (noVars v = true → ((∃ m, noVars m = true ∧ Step m v) ↔ hasReductPattern v = true)) := by
  have h1 : (∃ m, Step m v) ↔ hasReductPattern v = true := by
    induction v with
    | s =>
      constructor
      · rintro ⟨_, hs⟩; cases hs
      · intro h; cases h
    | var _ =>
      constructor
      · rintro ⟨_, hs⟩; cases hs
      · intro h; cases h
    | app l r ihl ihr =>
      simp only [hasReductPattern, Bool.or_eq_true, sameRightArg_iff, ← ihl, ← ihr]
      constructor
      · rintro ⟨m, hs⟩
        cases hs with
        | root x y z => exact Or.inl (Or.inl ⟨x, y, z, rfl, rfl⟩)
        | @left l0 _ _ hl => exact Or.inl (Or.inr ⟨l0, hl⟩)
        | @right _ r0 _ hr => exact Or.inr ⟨r0, hr⟩
      · rintro ((⟨x, y, z, rfl, rfl⟩ | ⟨l0, hl⟩) | ⟨r0, hr⟩)
        · exact ⟨S ⋅ x ⋅ y ⋅ z, Step.root x y z⟩
        · exact ⟨l0 ⋅ r, Step.left hl⟩
        · exact ⟨l ⋅ r0, Step.right hr⟩
  refine ⟨h1, fun hvv => ⟨fun ⟨m, _, hs⟩ => h1.mp ⟨m, hs⟩, closed_pred_of_hasReductPattern hvv⟩⟩

private theorem lastStep_of_step_reduces {u w v : Term} (h1 : Step u w) (h2 : Reduces w v) :
    ∃ m : Term, Step m v := by
  induction h2 generalizing u with
  | refl _ => exact ⟨u, h1⟩
  | next hs2 _ ih => exact ih hs2

/-- **Exact Characterization of Isolated Normal Forms (`[v]_{=_S} = {v}`)**:
    For every normal form `v`, `[v]_{=_S} = {v}` holds **if and only if** `hasReductPattern v = false`. -/
theorem isolated_normalForm_iff {v : Term} (hnf : IsNormalForm v) :
    (∀ n : Term, ConvS n v ↔ n = v) ↔ hasReductPattern v = false := by
  constructor
  · intro hiso
    cases hp : hasReductPattern v
    · rfl
    · exfalso
      obtain ⟨m, hsm⟩ := (exists_step_iff_hasReductPattern v).1.mpr hp
      have hmv : m = v := (hiso m).mp (ConvS.step hsm)
      subst hmv
      exact hnf m hsm
  · intro hp n
    rw [convS_normalForm_iff_reduces hnf n]
    constructor
    · intro hred
      cases hred with
      | refl _ => rfl
      | next hsb hrb =>
        exfalso
        obtain ⟨m, hsm⟩ := lastStep_of_step_reduces hsb hrb
        have htrue : hasReductPattern v = true := (exists_step_iff_hasReductPattern v).1.mp ⟨m, hsm⟩
        rw [hp] at htrue
        cases htrue
    · rintro rfl
      exact Reduces.refl n

/-- First infinite family of isolated closed normal forms: right-nested `S`-towers `S(S(...(S)))`. -/
def isoTower : Nat → Term
  | 0 => S
  | k + 1 => S ⋅ isoTower k

/-- Second infinite family of isolated closed normal forms: spine-length-2 normal forms `S ⋅ S ⋅ isoTower (k + 2)`. -/
def isolatedSpine2NF (k : Nat) : Term :=
  S ⋅ S ⋅ isoTower (k + 2)

theorem isoTower_props :
    ∀ k : Nat,
      noVars (isoTower k) = true ∧
      leaves (isoTower k) = k + 1 ∧
      IsNormalForm (isoTower k) ∧
      hasReductPattern (isoTower k) = false
  | 0 => ⟨rfl, rfl, (fun _ hs => by cases hs), rfl⟩
  | k + 1 => by
    obtain ⟨hv, hl, hnf, hp⟩ := isoTower_props k
    refine ⟨(Bool.and_eq_true _ _).mpr ⟨rfl, hv⟩, ?_, ?_, ?_⟩
    · change 1 + leaves (isoTower k) = k + 1 + 1; omega
    · intro u hu
      cases hu with
      | left h1 => cases h1
      | right h2 => exact hnf _ h2
    · change (sameRightArg S (isoTower k) || hasReductPattern S || hasReductPattern (isoTower k)) = false
      rw [hp]
      rfl

/-- **Infinite Pairwise-Distinct Family of Spine-2 Isolated Closed Normal Forms**:
    Every `isolatedSpine2NF k = S ⋅ S ⋅ isoTower (k + 2)` (`k ∈ ℕ`) is a closed normal form
    whose **entire** `=_S`-equivalence class is the singleton `{isolatedSpine2NF k}`! -/
theorem isolatedNF_family :
    (∀ k : Nat,
      noVars (isolatedSpine2NF k) = true ∧
      leaves (isolatedSpine2NF k) = k + 5 ∧
      IsNormalForm (isolatedSpine2NF k) ∧
      (∀ n : Term, ConvS n (isolatedSpine2NF k) ↔ n = isolatedSpine2NF k)) ∧
    (∀ {j k : Nat}, j ≠ k → isolatedSpine2NF j ≠ isolatedSpine2NF k) := by
  refine ⟨?_, ?_⟩
  · intro k
    obtain ⟨hv, hl, hnf_rt, hp_rt⟩ := isoTower_props (k + 2)
    have hnf : IsNormalForm (isolatedSpine2NF k) := by
      intro u hu
      cases hu with
      | left hl1 =>
        cases hl1 with
        | left hll => cases hll
        | right hlr => cases hlr
      | right hr1 => exact hnf_rt _ hr1
    have hpat : hasReductPattern (isolatedSpine2NF k) = false := by
      have hne : S ≠ isoTower (k + 1) := by
        intro heq
        have hlk := (isoTower_props (k + 1)).2.1
        rw [← heq] at hlk
        cases hlk
      have hsame : sameRightArg (S ⋅ S) (isoTower (k + 2)) = false := by
        change decide (S = isoTower (k + 1)) = false
        exact decide_eq_false hne
      have hp_ss : hasReductPattern (S ⋅ S) = false := rfl
      change (sameRightArg (S ⋅ S) (isoTower (k + 2)) ||
              hasReductPattern (S ⋅ S) ||
              hasReductPattern (isoTower (k + 2))) = false
      rw [hsame, hp_ss, hp_rt]
      rfl
    refine ⟨by simp [isolatedSpine2NF, S, noVars, hv], ?_, hnf, (isolated_normalForm_iff hnf).mpr hpat⟩
    change (1 + 1) + leaves (isoTower (k + 2)) = k + 5
    omega
  · intro j k hjk heq
    have hlj : leaves (isolatedSpine2NF j) = j + 5 := by
      have hl := (isoTower_props (j + 2)).2.1
      change (1 + 1) + leaves (isoTower (j + 2)) = j + 5; omega
    have hlk : leaves (isolatedSpine2NF k) = k + 5 := by
      have hl := (isoTower_props (k + 2)).2.1
      change (1 + 1) + leaves (isoTower (k + 2)) = k + 5; omega
    rw [heq] at hlj
    omega

/-! ## Section 4: Asymmetric Decidability of `ConvS` Across `SN × All` Closed `S`-Terms -/

/-- **Asymmetric Decidability of `ConvS` Across ALL Closed `S`-Terms (`SN × All`)**:
    Given **any** strongly normalizing closed pure-`S` term `m` (`hm : StrongNormalizing m`) and
    **any** closed pure-`S` term `n` (even non-terminating / unsolvable!), membership `n ∈ [m]_{=_S}`
    (`ConvS m n`) is constructively decidable in finite time via Conservation + Church–Rosser +
    Waldmann's 39-state `A_SN` theorem (`waldmann_theorem_9`). -/
def decideConvWithSN (m : Term) (hm : StrongNormalizing m) (n : Term)
    (_hvm : noVars m = true) (hvn : noVars n = true) : Decidable (ConvS m n) :=
  let hn_dec : Decidable (StrongNormalizing n) :=
    if hns : evalSN n ≠ .sn38 then
      isTrue ((waldmann_theorem_9 hvn).1.mpr hns)
    else
      isFalse (fun hsn => hns ((waldmann_theorem_9 hvn).1.mp hsn))
  match decideConvOfSN n m hm hn_dec with
  | isTrue hnm => isTrue (ConvS.symm hnm)
  | isFalse hnot => isFalse (fun hmn => hnot (ConvS.symm hmn))

/-! ## Section 5: Canonical RNF Spine Decomposition for Unsolvable Convertibility -/

def isAppTerm : Term → Bool
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

theorem isAppTerm_step {a b : Term} (ha : isAppTerm a = true) (hs : Step a b) :
    isAppTerm b = true := by
  cases hs <;> rfl

/-- **Right-Child Application Persistence**:
    Once the right child of a term is an application, no reduction step can ever turn it into `S` or a variable. -/
theorem rightIsApp_step {a b : Term} (ha : rightIsApp a = true) (hs : Step a b) :
    rightIsApp b = true := by
  cases hs with
  | root _ _ _ => rfl
  | @left _ _ r _ =>
    cases r with
    | app _ _ => rfl
    | s => cases ha
    | var _ => cases ha
  | @right _ r r' hr =>
    have hrapp : isAppTerm r = true := by
      cases r with
      | app _ _ => rfl
      | s => cases ha
      | var _ => cases ha
    have hr' : isAppTerm r' = true := isAppTerm_step hrapp hr
    cases r' with
    | app _ _ => rfl
    | s => cases hr'
    | var _ => cases hr'

theorem rightIsApp_reduces {a b : Term} (ha : rightIsApp a = true) (hr : Reduces a b) :
    rightIsApp b = true := by
  induction hr with
  | refl _ => exact ha
  | next hs _ ih => exact ih (rightIsApp_step ha hs)

theorem trailingS_eq_zero_of_rightIsApp {t : Term} (h : rightIsApp t = true) :
    trailingS t = 0 := by
  cases t with
  | app _ r =>
    cases r with
    | app _ _ => rfl
    | s => cases h
    | var _ => cases h
  | _ => cases h

theorem trailingS_appS (m : Term) (hm : rightIsApp m = true) :
    ∀ k : Nat, trailingS (appS m k) = k
  | 0 => trailingS_eq_zero_of_rightIsApp hm
  | k + 1 => by
    change 1 + trailingS (appS m k) = k + 1
    rw [trailingS_appS m hm k]
    omega

theorem appS_inj_left {a b : Term} : ∀ {k : Nat}, appS a k = appS b k → a = b
  | 0, h => h
  | k + 1, h => by
    dsimp [appS] at h
    injection h with h1 _
    exact appS_inj_left h1

theorem reduces_appS {a b : Term} (h : Reduces a b) : ∀ k : Nat, Reduces (appS a k) (appS b k)
  | 0 => h
  | k + 1 => reduces_left (reduces_appS h k) S

theorem convS_appS {a b : Term} (h : ConvS a b) : ∀ k : Nat, ConvS (appS a k) (appS b k)
  | 0 => h
  | k + 1 => convS_left (convS_appS h k) S

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
  | k + 3, _, _, heq => by
    dsimp [appS] at heq
    injection heq with h1 _
    injection h1 with h2 _
    cases h2

/-- **Trailing-`S` Freeze Lemma**:
    If `¬ HasHNF m`, every reduct of `appS m k` has the form `appS m' k` with `Reduces m m'`. -/
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

/-- **Canonical RNF Spine Decomposition Theorem for Unsolvable Convertibility**:
    If `m` and `n` both have `¬ HasHNF` and `rightIsApp = true`, then frozen trailing `⋅ S`
    tails peel off uniquely and bi-directionally under `=_S`:
    `ConvS (appS m j) (appS n k) ↔ (j = k ∧ ConvS m n)`. -/
theorem unsolvable_rightApp_convS_iff {m n : Term}
    (hm_no : ¬ HasHNF m) (hn_no : ¬ HasHNF n)
    (hm_r : rightIsApp m = true) (hn_r : rightIsApp n = true)
    (j k : Nat) :
    ConvS (appS m j) (appS n k) ↔ (j = k ∧ ConvS m n) := by
  constructor
  · intro hconv
    obtain ⟨w, hwj, hwk⟩ := convS_iff_common_reduct.mp hconv
    obtain ⟨m', hm', rfl⟩ := no_hnf_appS_reduces hm_no j w hwj
    obtain ⟨n', hn', heq⟩ := no_hnf_appS_reduces hn_no k (appS m' j) hwk
    have tj : trailingS (appS m' j) = j := trailingS_appS m' (rightIsApp_reduces hm_r hm') j
    have tk : trailingS (appS n' k) = k := trailingS_appS n' (rightIsApp_reduces hn_r hn') k
    have hjk : j = k := by rw [heq] at tj; exact tj.symm.trans tk
    subst hjk
    have hmn' : m' = n' := appS_inj_left heq
    subst hmn'
    exact ⟨rfl, convS_iff_common_reduct.mpr ⟨m', hm', hn'⟩⟩
  · rintro ⟨rfl, hmn⟩
    exact convS_appS hmn j

theorem aaa_no_hnf : ¬ HasHNF AAA := by
  rintro ⟨h, hred, hsp⟩
  have heq : evalHN AAA = evalHN h := evalHN_reduces hred
  have h34 : evalHN AAA = .hn34 := rfl
  rw [h34] at heq
  have hvh : noVars h = true := noVars_reduces hred rfl
  exact closed_hnf_evalHN_ne_hn34 hvh hsp heq.symm

/-- Direct specialization recovering `ConvS (appS AAA j) (appS AAA k) ↔ j = k`. -/
theorem aaa_appS_convS_iff (j k : Nat) :
    ConvS (appS AAA j) (appS AAA k) ↔ j = k := by
  rw [unsolvable_rightApp_convS_iff aaa_no_hnf aaa_no_hnf rfl rfl j k]
  exact ⟨fun h => h.1, fun h => ⟨h, ConvS.refl AAA⟩⟩

end FormalQ30Q31Deep

#print axioms FormalQ30Q31Deep.step_closed_leaves_eq_iff_stepAtomicS
#print axioms FormalQ30Q31Deep.step_compound_strict_leaves_increase
#print axioms FormalQ30Q31Deep.equivClassOfSN_spec
#print axioms FormalQ30Q31Deep.closed_normalizing_equivClass_finite
#print axioms FormalQ30Q31Deep.isolated_normalForm_iff
#print axioms FormalQ30Q31Deep.isolatedNF_family
#print axioms FormalQ30Q31Deep.decideConvWithSN
#print axioms FormalQ30Q31Deep.unsolvable_rightApp_convS_iff
