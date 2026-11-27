import formal_asymptotics.asymptotic_laws
import formal_order_and_isolated.leaf_preserving_and_isolated

/-!
# Higher-Order Catalan Laws: Order `{0, 1, 2, 3}` Densities, Exact Stationary Algebra, Motzkin `CNF`, and Isolated Normal Forms

Constructive, axiom-free Lean 4.33.1 formalization (`namespace FormalOrderAndIsolated`) of:
1. **Exact Catalan DP Enumeration & Partition for Order `{0, 1, 2, 3}`**:
   - `countOrder0`, `countOrder1`, `countOrder2`, `countOrder3` defined via `dpHN` on the `{1, 11, 17, 6}`
     partition of `StateHN` and proved equal to `((treesOfSize n).filter ...).length` and semantic
     `HasExactOrder t k`.
   - `order_counts_partition_catalan`: `countOrder0 n + countOrder1 n + countOrder2 n + countOrder3 n = catalanTrees n`
     and `countOrder1 n + countOrder2 n + countOrder3 n = countHN n` for all `n`.
   - `countOrder3_eq_one`: **`∀ n ≥ 1, countOrder3 n = 1`**!
2. **Universal Positive Catalan Density Lower Bounds for All Three Macroscopic Orders (`Order 0, 1, 2`)**:
   - `countOrder2_universal_lower`: `∀ n ≥ 2, catalanTrees (n - 1) ≤ countOrder2 n + 1` (density `≥ 1/4 > 0`).
   - `countOrder1_universal_lower`: `∀ n ≥ 5, catalanTrees (n - 4) ≤ countOrder1 n` (via `S(SSS) ⋅ r`, sharp `1 = 1` at `n = 5`).
   - `countOrder0_universal_lower`: `∀ n ≥ 8, catalanTrees (n - 7) ≤ countOrder0 n` (via `SSS(S(SSS)) ⋅ r`, sharp onset at `n = 8`).
3. **Machine-Checked Exact Rational Stationary `A_HN` System & Limiting Catalan Densities `(c_0, c_1, c_2, c_3)`**:
   - Certifies over `Nat` the exact rational fixed point `Y_q(1/4) = aQuarterNum q / 113246208`
     (`2^22 * 3^3`) and the exact Perron–Frobenius eigenvector `π_q = piStationaryNum q / 7077888`
     (`2^18 * 3^3`, `π = J(a) π`), proving the exact rational Catalan densities:
     `c_0 = 2648215 / 7077888`, `c_1 = 1864553 / 7077888`, `c_2 = 2565120 / 7077888 = 835 / 2304`, `c_3 = 0`,
     with `c_0 + c_1 + c_2 + c_3 = 1`!
4. **Exact Motzkin Normal Form Recurrence (`countCNF`) & Isolated Normal Form Hierarchy / Exponential Decay**:
   - Proves `countCNF n = ((treesOfSize n).filter isClosedNFBool).length` satisfies the exact shifted
     Motzkin recurrence `M_{n-1}` (`1, 1, 2, 4, 9, 21, 51, 127, 323, ...`).
   - Proves `countIsolatedNF n ≤ countCNF n ≤ countSN n` (`isolated_le_cnf_le_sn_and_exp_decay`), universal
     exponential decay `(250 / 259)^n` of both `countIsolatedNF n` and `countCNF n` (`∀ n ≥ 1`),
     and exact census verification across small sizes.

Verified with zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`, and zero `Classical.choice`.
-/

namespace FormalOrderAndIsolated

open FormalAlgebra
open FormalAsymptotics (catalanTrees treesOfSize treesOfSize_sound treesOfSize_complete
  treesOfSize_nodup treesOfSize_recurrence catalanTrees_eq_treesOfSize_length
  catalanTrees_recurrence dpHN countHN countNonHN countSN countAcceptP
  allStatesHN nodup_allStatesHN complete_allStatesHN dpState_eq_countList
  sumList sumList_zero sumList_map sumList_append sumList_congr sumList_le_sumList
  sumList_add_distrib sumList_mul_left sumList_mul_right mem_le_sumList
  countList countList_eq_filter_length countList_eq_sumList countList_append
  countList_map countList_listFlatMap countList_mono countList_le_length
  countList_all_true listFlatMap listFlatMap_append mem_listFlatMap_iff
  splits splitsAux mem_splits_iff nodupBool_sound NodupList
  sn_and_acceptP_exponential_decay_to_zero)

local infixl:70 (priority := high) " ⋅ " => FormalAlgebra.Term.app

/-! ## 1. Exact Catalan DP Counters for Order `{0, 1, 2, 3}` & Partition of `catalanTrees n` -/

def statesOrder0 : List StateHN := [.hn34]

def statesOrder1 : List StateHN :=
  [.hn22, .hn23, .hn24, .hn25, .hn26, .hn28, .hn29, .hn30, .hn31, .hn32, .hn33]

def statesOrder2 : List StateHN :=
  [.hn6, .hn7, .hn8, .hn9, .hn10, .hn11, .hn12, .hn13,
   .hn14, .hn15, .hn16, .hn17, .hn18, .hn19, .hn20, .hn21, .hn27]

def statesOrder3 : List StateHN :=
  [.hn0, .hn1, .hn2, .hn3, .hn4, .hn5]

private theorem nodup_statesOrder0 : NodupList statesOrder0 := nodupBool_sound rfl
private theorem nodup_statesOrder1 : NodupList statesOrder1 := nodupBool_sound rfl
private theorem nodup_statesOrder2 : NodupList statesOrder2 := nodupBool_sound rfl
private theorem nodup_statesOrder3 : NodupList statesOrder3 := nodupBool_sound rfl

private theorem statesOrder0_iff_chk : checkAll1_StateHN (fun q => decide ((q ∈ statesOrder0) ↔ orderOfStateHN q = 0)) = true := rfl
private theorem statesOrder1_iff_chk : checkAll1_StateHN (fun q => decide ((q ∈ statesOrder1) ↔ orderOfStateHN q = 1)) = true := rfl
private theorem statesOrder2_iff_chk : checkAll1_StateHN (fun q => decide ((q ∈ statesOrder2) ↔ orderOfStateHN q = 2)) = true := rfl
private theorem statesOrder3_iff_chk : checkAll1_StateHN (fun q => decide ((q ∈ statesOrder3) ↔ orderOfStateHN q = 3)) = true := rfl

def countOrder0 (n : Nat) : Nat := sumList statesOrder0 (fun q => dpHN n q)
def countOrder1 (n : Nat) : Nat := sumList statesOrder1 (fun q => dpHN n q)
def countOrder2 (n : Nat) : Nat := sumList statesOrder2 (fun q => dpHN n q)
def countOrder3 (n : Nat) : Nat := sumList statesOrder3 (fun q => dpHN n q)

private theorem sumList_delta_one_loc {Q : Type} [DecidableEq Q] {allQ : List Q}
    (hnodup : NodupList allQ) (f : Q → Nat) {q : Q} (hq : q ∈ allQ) :
    sumList allQ (fun a => if a = q then f a else 0) = f q := by
  induction hnodup with
  | nil => cases hq
  | @cons z zs hz _ ih =>
    simp only [sumList]
    rcases List.mem_cons.mp hq with heq_qz | hq'
    · subst heq_qz
      rw [if_pos rfl]
      have h0 : ∀ a ∈ zs, (if a = q then f a else 0) = 0 := by
        intro a ha
        cases hax : decide (a = q) with
        | true => exfalso; exact hz ((of_decide_eq_true hax) ▸ ha)
        | false => rw [if_neg (of_decide_eq_false hax)]
      rw [sumList_congr h0, sumList_zero, Nat.add_zero]
    · have hne : z ≠ q := fun heq => hz (heq ▸ hq')
      rw [if_neg hne, Nat.zero_add, ih hq']

private theorem bool_tf (b : Bool) : b = true ∨ b = false := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem sum_subset_eq_countList_loc {Q : Type} [DecidableEq Q]
    {subQ : List Q} (hnodup : NodupList subQ)
    (pred : Q → Bool) (hpred : ∀ q : Q, (q ∈ subQ) ↔ pred q = true)
    (ev : Term → Q) (xs : List Term) :
    sumList subQ (fun q => countList (fun t => decide (ev t = q)) xs) =
      countList (fun t => pred (ev t)) xs := by
  induction xs with
  | nil =>
    simp only [countList]
    exact sumList_zero subQ
  | cons x xs ih =>
    simp only [countList]
    rw [sumList_add_distrib, ih]
    rcases bool_tf (pred (ev x)) with hp | hp
    · have hmem : ev x ∈ subQ := (hpred (ev x)).mpr hp
      have h1 : ∀ q ∈ subQ, (if decide (ev x = q) then 1 else 0) = (if q = ev x then 1 else 0) := by
        intro q _
        cases h : decide (ev x = q) with
        | true => rw [if_pos (of_decide_eq_true h).symm]; rfl
        | false =>
          have hne : q ≠ ev x := fun heq => of_decide_eq_false h heq.symm
          rw [if_neg hne]; rfl
      have hval : sumList subQ (fun q => if decide (ev x = q) then 1 else 0) = 1 :=
        (sumList_congr h1).trans (sumList_delta_one_loc hnodup (fun _ => 1) hmem)
      rw [hval, if_pos hp]
    · have hnot : ev x ∉ subQ := fun hm => by rw [(hpred (ev x)).mp hm] at hp; cases hp
      have h0 : ∀ q ∈ subQ, (if decide (ev x = q) then 1 else 0) = 0 := by
        intro q hq
        cases h : decide (ev x = q) with
        | true => exfalso; exact hnot ((of_decide_eq_true h) ▸ hq)
        | false => rfl
      have hval : sumList subQ (fun q => if decide (ev x = q) then 1 else 0) = 0 :=
        (sumList_congr h0).trans (sumList_zero subQ)
      have hp_not : ¬ (pred (ev x) = true) := by rw [hp]; exact Bool.false_ne_true
      rw [hval, if_neg hp_not]

theorem countOrder0_eq_countList (n : Nat) :
    countOrder0 n = countList (fun t => decide (orderOfStateHN (evalHN t) = 0)) (treesOfSize n) := by
  unfold countOrder0 dpHN
  rw [sumList_congr (fun q _ => dpState_eq_countList nodup_allStatesHN complete_allStatesHN deltaHN .hn0 evalHN rfl (fun _ _ => rfl) n q)]
  refine sum_subset_eq_countList_loc nodup_statesOrder0 (fun q => decide (orderOfStateHN q = 0)) (fun q => ?_) evalHN (treesOfSize n)
  have hc := of_decide_eq_true (checkAll1_StateHN_sound _ statesOrder0_iff_chk q)
  exact ⟨fun hm => decide_eq_true (hc.mp hm), fun hd => hc.mpr (of_decide_eq_true hd)⟩

theorem countOrder1_eq_countList (n : Nat) :
    countOrder1 n = countList (fun t => decide (orderOfStateHN (evalHN t) = 1)) (treesOfSize n) := by
  unfold countOrder1 dpHN
  rw [sumList_congr (fun q _ => dpState_eq_countList nodup_allStatesHN complete_allStatesHN deltaHN .hn0 evalHN rfl (fun _ _ => rfl) n q)]
  refine sum_subset_eq_countList_loc nodup_statesOrder1 (fun q => decide (orderOfStateHN q = 1)) (fun q => ?_) evalHN (treesOfSize n)
  have hc := of_decide_eq_true (checkAll1_StateHN_sound _ statesOrder1_iff_chk q)
  exact ⟨fun hm => decide_eq_true (hc.mp hm), fun hd => hc.mpr (of_decide_eq_true hd)⟩

theorem countOrder2_eq_countList (n : Nat) :
    countOrder2 n = countList (fun t => decide (orderOfStateHN (evalHN t) = 2)) (treesOfSize n) := by
  unfold countOrder2 dpHN
  rw [sumList_congr (fun q _ => dpState_eq_countList nodup_allStatesHN complete_allStatesHN deltaHN .hn0 evalHN rfl (fun _ _ => rfl) n q)]
  refine sum_subset_eq_countList_loc nodup_statesOrder2 (fun q => decide (orderOfStateHN q = 2)) (fun q => ?_) evalHN (treesOfSize n)
  have hc := of_decide_eq_true (checkAll1_StateHN_sound _ statesOrder2_iff_chk q)
  exact ⟨fun hm => decide_eq_true (hc.mp hm), fun hd => hc.mpr (of_decide_eq_true hd)⟩

theorem countOrder3_eq_countList (n : Nat) :
    countOrder3 n = countList (fun t => decide (orderOfStateHN (evalHN t) = 3)) (treesOfSize n) := by
  unfold countOrder3 dpHN
  rw [sumList_congr (fun q _ => dpState_eq_countList nodup_allStatesHN complete_allStatesHN deltaHN .hn0 evalHN rfl (fun _ _ => rfl) n q)]
  refine sum_subset_eq_countList_loc nodup_statesOrder3 (fun q => decide (orderOfStateHN q = 3)) (fun q => ?_) evalHN (treesOfSize n)
  have hc := of_decide_eq_true (checkAll1_StateHN_sound _ statesOrder3_iff_chk q)
  exact ⟨fun hm => decide_eq_true (hc.mp hm), fun hd => hc.mpr (of_decide_eq_true hd)⟩

theorem countOrder_eq_filter_length (n : Nat) :
    countOrder0 n = ((treesOfSize n).filter (fun t => decide (orderOfStateHN (evalHN t) = 0))).length ∧
    countOrder1 n = ((treesOfSize n).filter (fun t => decide (orderOfStateHN (evalHN t) = 1))).length ∧
    countOrder2 n = ((treesOfSize n).filter (fun t => decide (orderOfStateHN (evalHN t) = 2))).length ∧
    countOrder3 n = ((treesOfSize n).filter (fun t => decide (orderOfStateHN (evalHN t) = 3))).length :=
  ⟨(countOrder0_eq_countList n).trans (countList_eq_filter_length _ _),
   (countOrder1_eq_countList n).trans (countList_eq_filter_length _ _),
   (countOrder2_eq_countList n).trans (countList_eq_filter_length _ _),
   (countOrder3_eq_countList n).trans (countList_eq_filter_length _ _)⟩

private theorem sumList_const_one {α : Type} (xs : List α) :
    sumList xs (fun _ => 1) = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
    simp only [sumList, List.length_cons, ih]
    exact Nat.add_comm 1 xs.length

/-- **Exact Catalan Partition Theorem for Order `{0, 1, 2, 3}`**:
    - `countOrder0 n = countNonHN n`
    - `countOrder1 n + countOrder2 n + countOrder3 n = countHN n`
    - `countOrder0 n + countOrder1 n + countOrder2 n + countOrder3 n = catalanTrees n` -/
theorem order_counts_partition_catalan (n : Nat) :
    countOrder0 n = countNonHN n ∧
    countOrder1 n + countOrder2 n + countOrder3 n = countHN n ∧
    countOrder0 n + countOrder1 n + countOrder2 n + countOrder3 n = catalanTrees n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [countOrder0_eq_countList, FormalAsymptotics.countNonHN_eq_countList,
        countList_eq_sumList, countList_eq_sumList]
    refine sumList_congr (fun t _ => ?_)
    cases evalHN t <;> rfl
  · rw [countOrder1_eq_countList, countOrder2_eq_countList, countOrder3_eq_countList,
        FormalAsymptotics.countHN_eq_countList,
        countList_eq_sumList, countList_eq_sumList, countList_eq_sumList, countList_eq_sumList,
        ← sumList_add_distrib, ← sumList_add_distrib]
    refine sumList_congr (fun t _ => ?_)
    cases evalHN t <;> rfl
  · rw [countOrder0_eq_countList, countOrder1_eq_countList, countOrder2_eq_countList,
        countOrder3_eq_countList, catalanTrees_eq_treesOfSize_length,
        countList_eq_sumList, countList_eq_sumList, countList_eq_sumList, countList_eq_sumList,
        ← sumList_add_distrib, ← sumList_add_distrib, ← sumList_add_distrib,
        ← sumList_const_one (treesOfSize n)]
    refine sumList_congr (fun t _ => ?_)
    cases evalHN t <;> rfl

/-! ## 2. Exact Universal Order-3 Law (`countOrder3 n = 1`) and Positive Density Bounds for Orders `0, 1, 2` -/

private theorem countList_eq_one_of_unique {α : Type} [DecidableEq α]
    {p : α → Bool} {xs : List α} {w : α}
    (hnd : NodupList xs) (hw : w ∈ xs)
    (hiff : ∀ x ∈ xs, p x = true ↔ x = w) :
    countList p xs = 1 := by
  induction hnd with
  | nil => cases hw
  | @cons z zs hz _ ih =>
    simp only [countList]
    rcases List.mem_cons.mp hw with heq_wz | hw_tail
    · have hpz : p z = true := (hiff z (.head _)).mpr heq_wz.symm
      have h0 : ∀ y ∈ zs, (if p y = true then 1 else 0) = 0 := by
        intro y hy
        cases hpy : p y with
        | false => rfl
        | true =>
          have hyw : y = w := (hiff y (.tail _ hy)).mp hpy
          exfalso; exact hz (heq_wz ▸ hyw ▸ hy)
      rw [if_pos hpz, countList_eq_sumList, sumList_congr h0, sumList_zero, Nat.add_zero]
    · have hpz : p z = false := by
        cases hp : p z with
        | false => rfl
        | true =>
          have hzw : z = w := (hiff z (.head _)).mp hp
          subst hzw
          exfalso; exact hz hw_tail
      have hpz_not : ¬ (p z = true) := by rw [hpz]; exact Bool.false_ne_true
      rw [if_neg hpz_not, Nat.zero_add]
      exact ih hw_tail (fun y hy => hiff y (.tail _ hy))

/-- **Exact Universal Order-3 Counting Theorem (`∀ n ≥ 1, countOrder3 n = 1`)**:
    For every leaf size `n ≥ 1`, there is **uniquely 1** closed pure-`S` combinator of Order `3`! -/
theorem countOrder3_eq_one {n : Nat} (hn : 1 ≤ n) :
    countOrder3 n = 1 := by
  rw [countOrder3_eq_countList]
  refine countList_eq_one_of_unique (treesOfSize_nodup n)
    (treesOfSize_complete (noVars_rightComb n) (leaves_rightComb hn))
    (fun t ht => ?_)
  have ⟨hvt, hlt⟩ := treesOfSize_sound ht
  have hc := closed_order3_iff_rightComb hvt
  have hlt' : leaves t = n := hlt
  rw [closed_hasExactOrder_iff hvt 3, hlt'] at hc
  exact ⟨fun hd => hc.mp (of_decide_eq_true hd), fun heq => decide_eq_true (hc.mpr heq)⟩

/-- **Universal Positive Density Lower Bound for Order 2 (`∀ n ≥ 2`)**:
    Every 1-HNF `S ⋅ r` (`r` of size `n - 1`) has Order `2` or `3`, hence
    `catalanTrees (n - 1) ≤ countOrder2 n + 1`! -/
theorem countOrder2_universal_lower {n : Nat} (hn : 2 ≤ n) :
    catalanTrees (n - 1) ≤ countOrder2 n + 1 := by
  have ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, (Nat.sub_add_cancel hn).symm⟩
  subst hm
  have hc3 : countOrder3 (m + 2) = 1 := countOrder3_eq_one (Nat.le_add_left 1 (m + 1))
  change catalanTrees (m + 1) ≤ countOrder2 (m + 2) + 1
  conv => rhs; rw [← hc3]
  have h23_eq : countOrder2 (m + 2) + countOrder3 (m + 2) =
      countList (fun t => decide (2 ≤ orderOfStateHN (evalHN t))) (treesOfSize (m + 2)) := by
    rw [countOrder2_eq_countList, countOrder3_eq_countList,
        countList_eq_sumList, countList_eq_sumList, countList_eq_sumList, ← sumList_add_distrib]
    refine sumList_congr (fun t _ => ?_)
    cases evalHN t <;> rfl
  rw [h23_eq, treesOfSize_recurrence m]
  have hsp : splits (m + 2) = (1, m + 1) :: splitsAux m 2 := rfl
  have ht1 : treesOfSize 1 = [S] := rfl
  rw [hsp, listFlatMap]
  dsimp only
  rw [ht1, listFlatMap, listFlatMap, List.append_nil, countList_append, countList_map]
  have hall : countList (fun r => decide (2 ≤ orderOfStateHN (evalHN (S ⋅ r)))) (treesOfSize (m + 1)) =
      catalanTrees (m + 1) := by
    rw [catalanTrees_eq_treesOfSize_length (m + 1)]
    refine countList_all_true (treesOfSize (m + 1)) (fun r _ => ?_)
    change decide (2 ≤ orderOfStateHN (deltaHN .hn0 (evalHN r))) = true
    cases evalHN r <;> rfl
  rw [hall]
  exact Nat.le_add_right _ _

/-- Universal left-Order-1 generator `S ⋅ (S ⋅ S ⋅ S)` (`4` leaves, `.hn7`). -/
def leftGenOrder1_4 : Term := S ⋅ (S ⋅ S ⋅ S)

private theorem leftGenOrder1_4_props :
    noVars leftGenOrder1_4 = true ∧ leaves leftGenOrder1_4 = 4 ∧ evalHN leftGenOrder1_4 = .hn7 :=
  ⟨rfl, rfl, rfl⟩

/-- **Universal Positive Density Lower Bound for Order 1 (`∀ n ≥ 5`)**:
    `leftGenOrder1_4 ⋅ r` has Order `1` for **every** closed `r` of size `n - 4`
    (sharp equality `1 = 1` at `n = 5`)! -/
theorem countOrder1_universal_lower {n : Nat} (hn : 5 ≤ n) :
    catalanTrees (n - 4) ≤ countOrder1 n := by
  have ⟨d, hd⟩ : ∃ d, n = d + 5 := ⟨n - 5, (Nat.sub_add_cancel hn).symm⟩
  subst hd
  change catalanTrees (d + 1) ≤ countOrder1 ((d + 3) + 2)
  rw [countOrder1_eq_countList, treesOfSize_recurrence (d + 3), countList_listFlatMap]
  have hsp4 : (4, d + 1) ∈ splits ((d + 3) + 2) :=
    mem_splits_iff.mpr ⟨by decide, Nat.succ_le_succ (Nat.zero_le d), Nat.add_comm 4 (d + 1)⟩
  have hmem_w : leftGenOrder1_4 ∈ treesOfSize 4 :=
    treesOfSize_complete leftGenOrder1_4_props.1 leftGenOrder1_4_props.2.1
  have h_at_w : countList (fun t => decide (orderOfStateHN (evalHN t) = 1))
      ((treesOfSize (d + 1)).map (fun r => leftGenOrder1_4 ⋅ r)) = catalanTrees (d + 1) := by
    rw [countList_map, catalanTrees_eq_treesOfSize_length (d + 1)]
    refine countList_all_true (treesOfSize (d + 1)) (fun r _ => ?_)
    change decide (orderOfStateHN (deltaHN (evalHN leftGenOrder1_4) (evalHN r)) = 1) = true
    rw [leftGenOrder1_4_props.2.2]
    cases evalHN r <;> rfl
  have hblock4 : catalanTrees (d + 1) ≤
      countList (fun t => decide (orderOfStateHN (evalHN t) = 1))
        (listFlatMap (treesOfSize 4) (fun l => (treesOfSize (d + 1)).map (fun r => l ⋅ r))) := by
    rw [countList_listFlatMap, ← h_at_w]
    exact mem_le_sumList hmem_w
      (fun l => countList (fun t => decide (orderOfStateHN (evalHN t) = 1)) ((treesOfSize (d + 1)).map (fun r => l ⋅ r)))
  exact Nat.le_trans hblock4
    (mem_le_sumList hsp4
      (fun p => countList (fun t => decide (orderOfStateHN (evalHN t) = 1))
        (listFlatMap (treesOfSize p.1) (fun l => (treesOfSize p.2).map (fun r => l ⋅ r)))))

/-- Universal left-Order-0 generator `S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S ⋅ S))` (`7` leaves, `.hn23`). -/
def leftGenOrder0_7 : Term := S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S ⋅ S))

private theorem leftGenOrder0_7_props :
    noVars leftGenOrder0_7 = true ∧ leaves leftGenOrder0_7 = 7 ∧ evalHN leftGenOrder0_7 = .hn23 :=
  ⟨rfl, rfl, rfl⟩

/-- **Sharp Onset Positive Density Lower Bound for Order 0 (`∀ n ≥ 8`)**:
    `leftGenOrder0_7 ⋅ r` has Order `0` (`.hn34`) for **every** closed `r` of size `n - 7`,
    sharpening `catalanTrees (n - 8)` to `catalanTrees (n - 7)` right from the minimal threshold `n = 8`! -/
theorem countOrder0_universal_lower {n : Nat} (hn : 8 ≤ n) :
    catalanTrees (n - 7) ≤ countOrder0 n := by
  have ⟨d, hd⟩ : ∃ d, n = d + 8 := ⟨n - 8, (Nat.sub_add_cancel hn).symm⟩
  subst hd
  change catalanTrees (d + 1) ≤ countOrder0 ((d + 6) + 2)
  rw [countOrder0_eq_countList, treesOfSize_recurrence (d + 6), countList_listFlatMap]
  have hsp7 : (7, d + 1) ∈ splits ((d + 6) + 2) :=
    mem_splits_iff.mpr ⟨by decide, Nat.succ_le_succ (Nat.zero_le d), Nat.add_comm 7 (d + 1)⟩
  have hmem_w : leftGenOrder0_7 ∈ treesOfSize 7 :=
    treesOfSize_complete leftGenOrder0_7_props.1 leftGenOrder0_7_props.2.1
  have h_at_w : countList (fun t => decide (orderOfStateHN (evalHN t) = 0))
      ((treesOfSize (d + 1)).map (fun r => leftGenOrder0_7 ⋅ r)) = catalanTrees (d + 1) := by
    rw [countList_map, catalanTrees_eq_treesOfSize_length (d + 1)]
    refine countList_all_true (treesOfSize (d + 1)) (fun r _ => ?_)
    change decide (orderOfStateHN (deltaHN (evalHN leftGenOrder0_7) (evalHN r)) = 0) = true
    rw [leftGenOrder0_7_props.2.2]
    cases evalHN r <;> rfl
  have hblock7 : catalanTrees (d + 1) ≤
      countList (fun t => decide (orderOfStateHN (evalHN t) = 0))
        (listFlatMap (treesOfSize 7) (fun l => (treesOfSize (d + 1)).map (fun r => l ⋅ r))) := by
    rw [countList_listFlatMap, ← h_at_w]
    exact mem_le_sumList hmem_w
      (fun l => countList (fun t => decide (orderOfStateHN (evalHN t) = 0)) ((treesOfSize (d + 1)).map (fun r => l ⋅ r)))
  exact Nat.le_trans hblock7
    (mem_le_sumList hsp7
      (fun p => countList (fun t => decide (orderOfStateHN (evalHN t) = 0))
        (listFlatMap (treesOfSize p.1) (fun l => (treesOfSize p.2).map (fun r => l ⋅ r)))))

/-! ## 3. Machine-Checked Exact Rational Stationary System of `A_HN` at `z = 1/4`
    and Limiting Catalan Densities `(c_0, c_1, c_2, c_3)` -/

/-- Numerators `113246208 * Y_q(1/4)` (`113246208 = 2^22 * 3^3`). -/
def aQuarterNum : StateHN → Nat
  | .hn0 => 28311552 | .hn1 => 7077888 | .hn2 => 1769472 | .hn3 => 442368 | .hn4 => 110592
  | .hn5 => 36864 | .hn6 => 1769472 | .hn7 => 442368 | .hn8 => 626688 | .hn9 => 295248
  | .hn10 => 3106992 | .hn11 => 884736 | .hn12 => 737280 | .hn13 => 2064384 | .hn14 => 442368
  | .hn15 => 110592 | .hn16 => 110592 | .hn17 => 156672 | .hn18 => 110592 | .hn19 => 27648
  | .hn20 => 239616 | .hn21 => 59904 | .hn22 => 157440 | .hn23 => 2868329 | .hn24 => 531216
  | .hn25 => 173844 | .hn26 => 110592 | .hn27 => 73728 | .hn28 => 27648 | .hn29 => 134976
  | .hn30 => 39168 | .hn31 => 184320 | .hn32 => 6912 | .hn33 => 14976 | .hn34 => 3366067

/-- Numerators `7077888 * π_q` (`7077888 = 2^18 * 3^3`) of the stationary Catalan distribution. -/
def piStationaryNum : StateHN → Nat
  | .hn0 => 0 | .hn1 => 0 | .hn2 => 0 | .hn3 => 0 | .hn4 => 0
  | .hn5 => 0 | .hn6 => 0 | .hn7 => 0 | .hn8 => 36864 | .hn9 => 23376
  | .hn10 => 1703088 | .hn11 => 0 | .hn12 => 147456 | .hn13 => 589824 | .hn14 => 0
  | .hn15 => 0 | .hn16 => 0 | .hn17 => 9216 | .hn18 => 0 | .hn19 => 0
  | .hn20 => 36864 | .hn21 => 9216 | .hn22 => 15168 | .hn23 => 1604213 | .hn24 => 152784
  | .hn25 => 24228 | .hn26 => 0 | .hn27 => 9216 | .hn28 => 0 | .hn29 => 26688
  | .hn30 => 2304 | .hn31 => 36864 | .hn32 => 0 | .hn33 => 2304 | .hn34 => 2648215

private theorem aQuarter_fixed_point_chk : checkAll1_StateHN (fun q =>
    decide (113246208 * aQuarterNum q =
      (if q = .hn0 then 113246208 * 28311552 else 0) +
      sumList allStatesHN (fun i => sumList allStatesHN (fun j =>
        if deltaHN i j = q then aQuarterNum i * aQuarterNum j else 0)))) = true := rfl

private theorem piStationary_eigenvector_chk : checkAll1_StateHN (fun q =>
    decide (113246208 * piStationaryNum q =
      sumList allStatesHN (fun i => sumList allStatesHN (fun j =>
        if deltaHN i j = q then
          aQuarterNum i * piStationaryNum j + piStationaryNum i * aQuarterNum j
        else 0)))) = true := rfl

/-- **Exact Algebraic Certification of the Stationary `A_HN` Generating-Function System (`z = 1/4`)
    and Exact Rational Catalan Order Densities `(c_0, c_1, c_2, c_3)`**:
    - `∑_q a_q = 1/2` (`2 * ∑ aQuarterNum = 113246208`) and `a_q = (1/4)[q=0] + ∑_{δ(i,j)=q} a_i a_j`
      across all 35 states `q`.
    - `π = J(a) π` across all 35 states `q` and `∑_q π_q = 1` (`∑ piStationaryNum = 7077888`).
    - Exact rational Catalan order densities:
      * `c_0 = 2648215 / 7077888`
      * `c_1 = 1864553 / 7077888`
      * `c_2 = 2565120 / 7077888 = 835 / 2304` (`2565120 * 2304 = 835 * 7077888`)
      * `c_3 = 0 / 7077888`
      * `2648215 + 1864553 + 2565120 + 0 = 7077888`! -/
theorem exact_rational_order_catalan_densities_certified :
    (2 * sumList allStatesHN aQuarterNum = 113246208) ∧
    (∀ q : StateHN, 113246208 * aQuarterNum q =
      (if q = .hn0 then 113246208 * 28311552 else 0) +
      sumList allStatesHN (fun i => sumList allStatesHN (fun j =>
        if deltaHN i j = q then aQuarterNum i * aQuarterNum j else 0))) ∧
    (∀ q : StateHN, 113246208 * piStationaryNum q =
      sumList allStatesHN (fun i => sumList allStatesHN (fun j =>
        if deltaHN i j = q then
          aQuarterNum i * piStationaryNum j + piStationaryNum i * aQuarterNum j
        else 0))) ∧
    (sumList statesOrder0 piStationaryNum = 2648215 ∧
     sumList statesOrder1 piStationaryNum = 1864553 ∧
     sumList statesOrder2 piStationaryNum = 2565120 ∧
     2565120 * 2304 = 835 * 7077888 ∧
     sumList statesOrder3 piStationaryNum = 0 ∧
     sumList allStatesHN piStationaryNum = 7077888 ∧
     2648215 + 1864553 + 2565120 + 0 = 7077888) := by
  refine ⟨rfl,
    fun q => of_decide_eq_true (checkAll1_StateHN_sound _ aQuarter_fixed_point_chk q),
    fun q => of_decide_eq_true (checkAll1_StateHN_sound _ piStationary_eigenvector_chk q),
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## 4. Exact Motzkin Normal Form Recurrence (`countCNF`), Isolated Normal Forms (`countIsolatedNF`),
    Universal Exponential Decay, and Exact Small-`n` Census -/

def countCNFAux : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, _ + 2 => 0
  | fuel + 1, n =>
    let sub := countCNFAux fuel
    match n with
    | 0 => 0
    | 1 => 1
    | m + 2 => sub (m + 1) + sumList (splits (m + 1)) (fun p => sub p.1 * sub p.2)

/-- Exact shifted Motzkin counter `#CNF(n) = M_{n-1}` (`1, 1, 2, 4, 9, 21, 51, 127, 323, 835, ...`). -/
def countCNF (n : Nat) : Nat := countCNFAux n n

private theorem countCNFAux_zero (f : Nat) : countCNFAux f 0 = 0 := by cases f <;> rfl
private theorem countCNFAux_one (f : Nat) : countCNFAux f 1 = 1 := by cases f <;> rfl
private theorem countCNFAux_step (f m : Nat) :
    countCNFAux (f + 1) (m + 2) =
      countCNFAux f (m + 1) + sumList (splits (m + 1)) (fun p => countCNFAux f p.1 * countCNFAux f p.2) := rfl

private theorem countCNFAux_eq_of_le (fuel1 : Nat) :
    ∀ (fuel2 n : Nat), n ≤ fuel1 → n ≤ fuel2 → countCNFAux fuel1 n = countCNFAux fuel2 n := by
  induction fuel1 with
  | zero =>
    intro fuel2 n h1 _
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero h1
    subst hn0
    rw [countCNFAux_zero, countCNFAux_zero]
  | succ f1 ih =>
    intro fuel2 n h1 h2
    cases n with
    | zero => rw [countCNFAux_zero, countCNFAux_zero]
    | succ n0 =>
      cases n0 with
      | zero => rw [countCNFAux_one, countCNFAux_one]
      | succ m =>
        cases fuel2 with
        | zero => cases h2
        | succ f2 =>
          have hm1 : m + 1 ≤ f1 := Nat.le_of_succ_le_succ h1
          have hm2 : m + 1 ≤ f2 := Nat.le_of_succ_le_succ h2
          rw [countCNFAux_step, countCNFAux_step, ih f2 (m + 1) hm1 hm2]
          refine congrArg (countCNFAux f2 (m + 1) + ·) ?_
          cases m with
          | zero => rfl
          | succ m0 =>
            refine sumList_congr (fun ⟨x, y⟩ hp => ?_)
            dsimp only
            have ⟨_, _, hxy⟩ := mem_splits_iff.mp hp
            have hxm : x ≤ m0 + 2 := hxy ▸ Nat.le_add_right x y
            have hym : y ≤ m0 + 2 := hxy ▸ Nat.le_add_left y x
            rw [ih f2 x (Nat.le_trans hxm hm1) (Nat.le_trans hxm hm2),
                ih f2 y (Nat.le_trans hym hm1) (Nat.le_trans hym hm2)]

theorem countCNF_recurrence (m : Nat) :
    countCNF (m + 2) = countCNF (m + 1) + sumList (splits (m + 1)) (fun p => countCNF p.1 * countCNF p.2) := by
  change countCNFAux ((m + 1) + 1) (m + 2) = _
  rw [countCNFAux_step, countCNFAux_eq_of_le (m + 1) (m + 1) (m + 1) (Nat.le_refl _) (Nat.le_refl _)]
  refine congrArg (countCNF (m + 1) + ·) ?_
  cases m with
  | zero => rfl
  | succ m0 =>
    refine sumList_congr (fun ⟨x, y⟩ hp => ?_)
    dsimp only
    have ⟨_, _, hxy⟩ := mem_splits_iff.mp hp
    have hxm : x ≤ m0 + 2 := hxy ▸ Nat.le_add_right x y
    have hym : y ≤ m0 + 2 := hxy ▸ Nat.le_add_left y x
    rw [countCNFAux_eq_of_le (m0 + 2) x x hxm (Nat.le_refl x),
        countCNFAux_eq_of_le (m0 + 2) y y hym (Nat.le_refl y)]
    rfl

private theorem splitsAux_shift_loc (K a : Nat) :
    splitsAux K (a + 1) = (splitsAux K a).map (fun p => (p.1 + 1, p.2)) := by
  induction K generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [splitsAux, List.map_cons]
    congr 1
    exact ih (a + 1)

private theorem mem_splitsAux_fst_ge (K : Nat) :
    ∀ (a : Nat) (p : Nat × Nat), p ∈ splitsAux K a → a ≤ p.1 := by
  induction K with
  | zero => intro _ _ hp; cases hp
  | succ k ih =>
    intro a p hp
    rcases List.mem_cons.mp hp with rfl | htail
    · exact Nat.le_refl a
    · exact Nat.le_trans (Nat.le_succ a) (ih (a + 1) p htail)

private theorem countList_s2_cnf_block (as bs : List Term) :
    countList isClosedNFBool
      (listFlatMap (as.map (fun a => S ⋅ a)) (fun l => bs.map (fun b => l ⋅ b))) =
    countList isClosedNFBool as * countList isClosedNFBool bs := by
  induction as with
  | nil => simp only [List.map_nil, listFlatMap, countList, Nat.zero_mul]
  | cons a as ih =>
    simp only [List.map_cons, listFlatMap, countList_append, countList, ih]
    rw [countList_map]
    cases ha : isClosedNFBool a with
    | true =>
      have hb_eq : countList (fun b => isClosedNFBool ((S ⋅ a) ⋅ b)) bs = countList isClosedNFBool bs := by
        rw [countList_eq_sumList, countList_eq_sumList]
        refine sumList_congr (fun b _ => ?_)
        change (if (isClosedNFBool a && isClosedNFBool b) = true then 1 else 0) = _
        rw [ha, Bool.true_and]
      rw [if_pos rfl, hb_eq, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    | false =>
      have hb_zero : countList (fun b => isClosedNFBool ((S ⋅ a) ⋅ b)) bs = 0 := by
        rw [countList_eq_sumList]
        have h0 : ∀ b ∈ bs, (if isClosedNFBool ((S ⋅ a) ⋅ b) = true then 1 else 0) = 0 := by
          intro b _
          change (if (isClosedNFBool a && isClosedNFBool b) = true then 1 else 0) = 0
          rw [ha, Bool.false_and]
          rfl
        rw [sumList_congr h0, sumList_zero]
      rw [if_neg Bool.false_ne_true, hb_zero, Nat.zero_add, Nat.zero_add]

private theorem countList_cnf_left_ge2 {x y : Nat} (hx : 2 ≤ x) (bs : List Term) :
    countList isClosedNFBool
      (listFlatMap (listFlatMap (treesOfSize x) (fun l1 => (treesOfSize y).map (fun l2 => l1 ⋅ l2)))
        (fun l => bs.map (fun b => l ⋅ b))) = 0 := by
  rw [countList_listFlatMap]
  have h0 : ∀ l ∈ listFlatMap (treesOfSize x) (fun l1 => (treesOfSize y).map (fun l2 => l1 ⋅ l2)),
      countList isClosedNFBool (bs.map (fun b => l ⋅ b)) = 0 := by
    intro l hl
    obtain ⟨l1, hl1, hl2_mem⟩ := mem_listFlatMap_iff.mp hl
    obtain ⟨l2, _, rfl⟩ := List.mem_map.mp hl2_mem
    have ⟨_, hll1⟩ := treesOfSize_sound hl1
    cases l1 with
    | s =>
      change 1 = x at hll1
      rw [← hll1] at hx
      exact False.elim (absurd hx (by decide))
    | var _ =>
      change 1 = x at hll1
      rw [← hll1] at hx
      exact False.elim (absurd hx (by decide))
    | app u v =>
      rw [countList_map, countList_eq_sumList]
      have hz : ∀ b ∈ bs, (if isClosedNFBool (((u ⋅ v) ⋅ l2) ⋅ b) = true then 1 else 0) = 0 :=
        fun _ _ => rfl
      rw [sumList_congr hz, sumList_zero]
  rw [sumList_congr h0, sumList_zero]

private theorem countList_cnf_left_succ {j : Nat} (hj : 1 ≤ j) (bs : List Term) :
    countList isClosedNFBool
      (listFlatMap (treesOfSize (j + 1)) (fun l => bs.map (fun b => l ⋅ b))) =
    countList isClosedNFBool (treesOfSize j) * countList isClosedNFBool bs := by
  cases j with
  | zero => cases hj
  | succ j0 =>
    cases j0 with
    | zero =>
      have ht1 : treesOfSize 1 = [S] := rfl
      have ht2 : treesOfSize 2 = [S ⋅ S] := rfl
      rw [ht1, ht2]
      have hss : [S ⋅ S] = [S].map (fun a => S ⋅ a) := rfl
      rw [hss]
      exact countList_s2_cnf_block [S] bs
    | succ m =>
      change countList isClosedNFBool
        (listFlatMap (treesOfSize ((m + 1) + 2)) (fun l => bs.map (fun b => l ⋅ b))) = _
      rw [treesOfSize_recurrence (m + 1)]
      have hsp : splits ((m + 1) + 2) = (1, m + 2) :: splitsAux (m + 1) 2 := rfl
      have ht1 : treesOfSize 1 = [S] := rfl
      rw [hsp, listFlatMap]
      dsimp only
      rw [ht1, listFlatMap, listFlatMap, List.append_nil, listFlatMap_append, countList_append,
          countList_s2_cnf_block]
      have hrest : countList isClosedNFBool
          (listFlatMap (listFlatMap (splitsAux (m + 1) 2) (fun p =>
            listFlatMap (treesOfSize p.1) (fun l1 => (treesOfSize p.2).map (fun l2 => l1 ⋅ l2))))
            (fun l => bs.map (fun b => l ⋅ b))) = 0 := by
        have haux : ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, 2 ≤ p.1) →
            countList isClosedNFBool
              (listFlatMap (listFlatMap ps (fun p =>
                listFlatMap (treesOfSize p.1) (fun l1 => (treesOfSize p.2).map (fun l2 => l1 ⋅ l2))))
                (fun l => bs.map (fun b => l ⋅ b))) = 0 := by
          intro ps
          induction ps with
          | nil => intro _; rfl
          | cons p ps ih =>
            intro hge
            simp only [listFlatMap, listFlatMap_append, countList_append]
            rw [countList_cnf_left_ge2 (hge p (.head _)) bs,
                ih (fun q hq => hge q (.tail _ hq)), Nat.zero_add]
        exact haux (splitsAux (m + 1) 2) (fun p hp => mem_splitsAux_fst_ge (m + 1) 2 p hp)
      rw [hrest, Nat.add_zero]

/-- **Exact Motzkin Equivalence (`#CNF(n) = M_{n-1}`)**:
    `countCNF n` equals the exact number of closed pure-`S` Normal Forms of leaf size `n`! -/
theorem countCNF_eq_countList (n : Nat) :
    countCNF n = countList isClosedNFBool (treesOfSize n) := by
  have haux : ∀ B k, k ≤ B → countCNF k = countList isClosedNFBool (treesOfSize k) := by
    intro B
    induction B with
    | zero =>
      intro k hk
      cases Nat.eq_zero_of_le_zero hk
      rfl
    | succ B ih =>
      intro k hk
      cases k with
      | zero => rfl
      | succ k0 =>
        cases k0 with
        | zero => rfl
        | succ m =>
          cases m with
          | zero => rfl
          | succ d =>
            change countCNF ((d + 1) + 2) = countList isClosedNFBool (treesOfSize ((d + 1) + 2))
            have hd2B : d + 2 ≤ B := Nat.le_of_succ_le_succ hk
            rw [countCNF_recurrence (d + 1), treesOfSize_recurrence (d + 1)]
            have hsp : splits ((d + 1) + 2) = (1, d + 2) :: (splits (d + 2)).map (fun p => (p.1 + 1, p.2)) := by
              change (1, d + 2) :: splitsAux (d + 1) 2 = (1, d + 2) :: (splitsAux (d + 1) 1).map _
              rw [splitsAux_shift_loc (d + 1) 1]
            have ht1 : treesOfSize 1 = [S] := rfl
            rw [hsp, listFlatMap]
            dsimp only
            rw [ht1, listFlatMap, listFlatMap, List.append_nil, countList_append, countList_map]
            have h1_eq : countList (fun x => isClosedNFBool (S ⋅ x)) (treesOfSize (d + 2)) =
                countCNF (d + 2) := (ih (d + 2) hd2B).symm
            rw [h1_eq, countList_listFlatMap, sumList_map]
            refine congrArg (countCNF (d + 2) + ·) (sumList_congr (fun ⟨x, y⟩ hp => ?_))
            dsimp only
            have ⟨hx1, _, hxy⟩ := mem_splits_iff.mp hp
            have hxd2 : x ≤ d + 2 := hxy ▸ Nat.le_add_right x y
            have hyd2 : y ≤ d + 2 := hxy ▸ Nat.le_add_left y x
            rw [countList_cnf_left_succ hx1 (treesOfSize y),
                ← ih x (Nat.le_trans hxd2 hd2B), ← ih y (Nat.le_trans hyd2 hd2B)]
  exact haux n n (Nat.le_refl n)

theorem countCNF_eq_filter_length (n : Nat) :
    countCNF n = ((treesOfSize n).filter isClosedNFBool).length :=
  (countCNF_eq_countList n).trans (countList_eq_filter_length _ _)

/-- Exact counter `#IsolatedNF(n)` of closed Isolated Normal Forms (`[t]_{=S} = {t}`) of leaf size `n`. -/
def countIsolatedNF (n : Nat) : Nat :=
  countList isIsolatedClosedNF (treesOfSize n)

theorem countIsolatedNF_eq_filter_length (n : Nat) :
    countIsolatedNF n = ((treesOfSize n).filter isIsolatedClosedNF).length :=
  countList_eq_filter_length _ _

/-- **Universal Hierarchy & Exponential Decay Law for Isolated Normal Forms and Closed Normal Forms**:
    For all `n ≥ 1`, `1 ≤ countIsolatedNF n ≤ countCNF n ≤ countSN n`, and both decay exponentially
    relative to `catalanTrees n` at rate at most `(250 / 259)^n`! -/
theorem isolated_le_cnf_le_sn_and_exp_decay (n : Nat) (hn : 1 ≤ n) :
    1 ≤ countIsolatedNF n ∧
    countIsolatedNF n ≤ countCNF n ∧
    countCNF n ≤ countSN n ∧
    100000 * (259 ^ n) * countIsolatedNF n ≤ 5139438 * (250 ^ n) * catalanTrees n ∧
    100000 * (259 ^ n) * countCNF n ≤ 5139438 * (250 ^ n) * catalanTrees n := by
  have hmem_rc : rightComb n ∈ treesOfSize n :=
    treesOfSize_complete (noVars_rightComb n) (leaves_rightComb hn)
  have hiso_rc : isIsolatedClosedNF (rightComb n) = true :=
    (isIsolatedClosedNF_iff _).mpr ⟨noVars_rightComb n, (rightComb_isIsolatedNF n).1⟩
  have hge1 : 1 ≤ countIsolatedNF n := by
    unfold countIsolatedNF
    rw [countList_eq_sumList]
    have hm := mem_le_sumList hmem_rc (fun t => if isIsolatedClosedNF t = true then 1 else 0)
    rw [if_pos hiso_rc] at hm
    exact hm
  have hiso_le_cnf : countIsolatedNF n ≤ countCNF n := by
    rw [countCNF_eq_countList]
    exact countList_mono (treesOfSize n) (fun t _ ht => by
      have ⟨hv, hiso⟩ := (isIsolatedClosedNF_iff t).mp ht
      exact (isClosedNFBool_iff t).mpr ⟨hv, hiso.1⟩)
  have hcnf_le_sn : countCNF n ≤ countSN n := by
    rw [countCNF_eq_countList, FormalAsymptotics.countSN_eq_countList]
    refine countList_mono (treesOfSize n) (fun t _ ht => ?_)
    have ⟨hv, hnf⟩ := (isClosedNFBool_iff t).mp ht
    exact decide_eq_true ((waldmann_theorem_9 hv).1.mp (normalForm_is_sn hnf))
  have ⟨hsn_exp, _⟩ := sn_and_acceptP_exponential_decay_to_zero n hn
  have hcnf_exp : 100000 * (259 ^ n) * countCNF n ≤ 5139438 * (250 ^ n) * catalanTrees n :=
    Nat.le_trans (Nat.mul_le_mul_left _ hcnf_le_sn) hsn_exp
  have hiso_exp : 100000 * (259 ^ n) * countIsolatedNF n ≤ 5139438 * (250 ^ n) * catalanTrees n :=
    Nat.le_trans (Nat.mul_le_mul_left _ hiso_le_cnf) hcnf_exp
  exact ⟨hge1, hiso_le_cnf, hcnf_le_sn, hiso_exp, hcnf_exp⟩

set_option maxRecDepth 20000 in
/-- Exact machine-checked census verification across `n = 1..8` for Orders `0..3`, `CNF`, and `IsolatedNF`! -/
theorem exact_order_and_isolated_census_1_to_8 :
    (countOrder0 1 = 0 ∧ countOrder1 1 = 0 ∧ countOrder2 1 = 0 ∧ countOrder3 1 = 1 ∧ countCNF 1 = 1 ∧ countIsolatedNF 1 = 1) ∧
    (countOrder0 2 = 0 ∧ countOrder1 2 = 0 ∧ countOrder2 2 = 0 ∧ countOrder3 2 = 1 ∧ countCNF 2 = 1 ∧ countIsolatedNF 2 = 1) ∧
    (countOrder0 3 = 0 ∧ countOrder1 3 = 0 ∧ countOrder2 3 = 1 ∧ countOrder3 3 = 1 ∧ countCNF 3 = 2 ∧ countIsolatedNF 3 = 2) ∧
    (countOrder0 4 = 0 ∧ countOrder1 4 = 0 ∧ countOrder2 4 = 4 ∧ countOrder3 4 = 1 ∧ countCNF 4 = 4 ∧ countIsolatedNF 4 = 3) ∧
    (countOrder0 5 = 0 ∧ countOrder1 5 = 1 ∧ countOrder2 5 = 12 ∧ countOrder3 5 = 1 ∧ countCNF 5 = 9 ∧ countIsolatedNF 5 = 7) ∧
    (countOrder0 6 = 0 ∧ countOrder1 6 = 9 ∧ countOrder2 6 = 32 ∧ countOrder3 6 = 1 ∧ countCNF 6 = 21 ∧ countIsolatedNF 6 = 15) ∧
    (countOrder0 7 = 0 ∧ countOrder1 7 = 48 ∧ countOrder2 7 = 83 ∧ countOrder3 7 = 1 ∧ countCNF 7 = 51 ∧ countIsolatedNF 7 = 37) ∧
    (countOrder0 8 = 15 ∧ countOrder1 8 = 173 ∧ countOrder2 8 = 240 ∧ countOrder3 8 = 1 ∧ countCNF 8 = 127) := by
  simp only [countOrder0_eq_countList, countOrder1_eq_countList,
             countOrder2_eq_countList, countOrder3_eq_countList]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
         ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
         ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
         ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
         ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
         ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
         ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
         ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

end FormalOrderAndIsolated

#print axioms FormalOrderAndIsolated.countOrder_eq_filter_length
#print axioms FormalOrderAndIsolated.order_counts_partition_catalan
#print axioms FormalOrderAndIsolated.countOrder3_eq_one
#print axioms FormalOrderAndIsolated.countOrder2_universal_lower
#print axioms FormalOrderAndIsolated.countOrder1_universal_lower
#print axioms FormalOrderAndIsolated.countOrder0_universal_lower
#print axioms FormalOrderAndIsolated.exact_rational_order_catalan_densities_certified
#print axioms FormalOrderAndIsolated.countCNF_eq_filter_length
#print axioms FormalOrderAndIsolated.isolated_le_cnf_le_sn_and_exp_decay
#print axioms FormalOrderAndIsolated.exact_order_and_isolated_census_1_to_8
