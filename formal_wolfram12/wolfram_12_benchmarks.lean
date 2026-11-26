import formal_algebra.sn_hn_algebras
import intrinsic_research.intrinsic_theorems

/-!
# Stephen Wolfram's 12 Benchmark Pure-S Expressions and Jump-Ahead Predictability

Machine-checked in Lean 4.33.1 (`namespace FormalWolfram12`) with zero `sorry`,
zero `admit`, zero custom axioms, zero `native_decide`, and zero `Classical.choice`
(`#print axioms` uses at most `[propext, Quot.sound]` or `[propext]`).

Covers:
1. Exact syntax/reduction bijection `FormalAlgebra.Term ↔ IntrinsicTheorems.Term` lifting the
   39-state productivity algebra `A_P` (`evalP`) alongside `A_SN` (`evalSN`) and `A_HN` (`evalHN`).
2. Exact formalization of `wolfram7_a`, `wolfram7_b`, and `wolfram_1..wolfram_12` with verified
   Mathematica `s[...]` roundtrip (`toWolframStr`) matching `wolfram_announcement.txt` lines 131
   and 147–153, plus exhaustive Catalan verification of the 7-leaf non-halting threshold.
3. Frozen normal-order HNF context calculus (`LOFrame`, `wrapLOContext`), uniqueness of active
   `stepLO` focus, and the **Exact 14-Expression Algebraic & Dynamical Dichotomy Theorem**:
   - All 14 benchmarks are closed, non-halting (`evalSN = .sn38`), and globally non-productive
     (`evalP = .p37`).
   - **7** of `wolfram_1..12` (`3, 4, 6, 7, 9, 10, 12`) are immediately `.hn34` (`0` freezes).
   - **6** (`wolfram7_a, wolfram7_b, wolfram_1, 5, 8, 11`) lie in `HN \ SN` yet freeze `1..4`
     HNF frames before permanently locking into pure-head divergence (`.hn34`) forever.
   - **Uniquely 1** (`wolfram_2`) stays perpetually inside `HN \ SN` along `→_{lo}` forever
     (closed-form quadratic trajectory `(n+1)*(n+6)/2 + 1`), while `zachosPrecursor →^1 zachos`
     uniquely realizes global Böhm productivity (`evalP = .p29 ≠ .p37`, `¬ ConvS wolfram_2 zachos`)
     because `wolfram_2` hides a depth-5 Böhm-tree `⊥` inside a frozen right sibling.
4. **Explicit "Jump-Ahead" Closed-Form Predictability Theorems** (Wolfram announcement line 179):
   - $O(|t|)$ halting (`decideHaltsLO`) and head-halting (`decideHaltsHead`) decision procedures;
   - $O(|C| + \sum |t_i|)$ compositional multi-hole context halting (`decideContextHaltsLO`,
     `decideContextHaltsHead`) without constructing `C[t_1, ..., t_k]` or simulating a step;
   - $O(1)$-arithmetic two-parameter jump-ahead (`jumpAheadCounterStep n = 2 * n^2 - n + 1`) on
     `tenLeafSeed`;
   - Exact normal-form jump-ahead on `rightTower` and left-associative `sPrefix` (`S S S ...`) in
     `((m - 1) / 2) * (m / 2)` steps.
-/

namespace FormalWolfram12

open FormalAlgebra

/-! ## 1. Syntax Bijection (`FormalAlgebra.Term ↔ IntrinsicTheorems.Term`) and `A_P` Lift -/

def toIntrinsic : Term → IntrinsicTheorems.Term
  | .s => .s
  | .var k => .var k
  | .app a b => .app (toIntrinsic a) (toIntrinsic b)

def ofIntrinsic : IntrinsicTheorems.Term → Term
  | .s => .s
  | .var k => .var k
  | .app a b => .app (ofIntrinsic a) (ofIntrinsic b)

theorem ofIntrinsic_toIntrinsic (t : Term) : ofIntrinsic (toIntrinsic t) = t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp only [toIntrinsic, ofIntrinsic, iha, ihb]

theorem toIntrinsic_ofIntrinsic (u : IntrinsicTheorems.Term) : toIntrinsic (ofIntrinsic u) = u := by
  induction u with
  | s => rfl
  | var _ => rfl
  | app _ _ iha ihb => simp only [ofIntrinsic, toIntrinsic, iha, ihb]

theorem toIntrinsic_step {a b : Term} (h : Step a b) :
    IntrinsicTheorems.Step (toIntrinsic a) (toIntrinsic b) := by
  induction h with
  | root x y z => exact IntrinsicTheorems.Step.root (toIntrinsic x) (toIntrinsic y) (toIntrinsic z)
  | left _ ih => exact IntrinsicTheorems.Step.left ih
  | right _ ih => exact IntrinsicTheorems.Step.right ih

theorem toIntrinsic_reduces {a b : Term} (h : Reduces a b) :
    IntrinsicTheorems.Reduces (toIntrinsic a) (toIntrinsic b) := by
  induction h with
  | refl _ => exact IntrinsicTheorems.Reduces.refl _
  | next hs _ ih => exact IntrinsicTheorems.Reduces.next (toIntrinsic_step hs) ih

theorem toIntrinsic_conv {a b : Term} (h : ConvS a b) :
    IntrinsicTheorems.ConvS (toIntrinsic a) (toIntrinsic b) := by
  induction h with
  | refl _ => exact IntrinsicTheorems.ConvS.refl _
  | step hs => exact IntrinsicTheorems.ConvS.step (toIntrinsic_step hs)
  | symm _ ih => exact IntrinsicTheorems.ConvS.symm ih
  | trans _ _ ih1 ih2 => exact IntrinsicTheorems.ConvS.trans ih1 ih2

def evalP (t : Term) : IntrinsicTheorems.StateP :=
  IntrinsicTheorems.evalP (toIntrinsic t)

theorem evalP_app (a b : Term) :
    evalP (a ⋅ b) = IntrinsicTheorems.delta_StateP (evalP a) (evalP b) := rfl

theorem evalP_step {a b : Term} (h : Step a b) : evalP a = evalP b :=
  IntrinsicTheorems.evalP_step_invariant (toIntrinsic_step h)

theorem evalP_reduces {a b : Term} (h : Reduces a b) : evalP a = evalP b := by
  induction h with
  | refl _ => rfl
  | next hs _ ih => exact (evalP_step hs).trans ih

theorem evalP_conv {a b : Term} (h : ConvS a b) : evalP a = evalP b :=
  IntrinsicTheorems.evalP_conv_invariant (toIntrinsic_conv h)

/-! ## 2. Wolfram's 14 Benchmark Pure-`S` Expressions & 7-Leaf Minimality Theorem -/

/-- Line 131 minimal 7-leaf non-halting pure-`S` expression: `s[s][s][s[s]][s][s]`. -/
def wolfram7_a : Term := S ⋅ S ⋅ S ⋅ (S ⋅ S) ⋅ S ⋅ S

/-- Second 7-leaf non-halting pure-`S` expression: `s[s[s]][s][s][s][s]`. -/
def wolfram7_b : Term := S ⋅ (S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S

/-- Wolfram's 12 benchmark non-halting pure-`S` expressions (lines 147–153). -/
def wolfram_1  : Term := S ⋅ (S ⋅ (S ⋅ (S ⋅ S) ⋅ S)) ⋅ S ⋅ S
def wolfram_2  : Term := S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)
def wolfram_3  : Term := S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S ⋅ S))) ⋅ S
def wolfram_4  : Term := S ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S) ⋅ S)) ⋅ S ⋅ S
def wolfram_5  : Term := S ⋅ S ⋅ S ⋅ S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ S
def wolfram_6  : Term := S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S ⋅ S) ⋅ S)) ⋅ S
def wolfram_7  : Term := S ⋅ (S ⋅ S ⋅ S ⋅ (S ⋅ S)) ⋅ (S ⋅ S ⋅ S) ⋅ S
def wolfram_8  : Term := S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅ (S ⋅ S)
def wolfram_9  : Term := S ⋅ S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ S) ⋅ S ⋅ S ⋅ S ⋅ S
def wolfram_10 : Term := S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S)) ⋅ S
def wolfram_11 : Term := S ⋅ S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S ⋅ S)))) ⋅ S
def wolfram_12 : Term := S ⋅ (S ⋅ (S ⋅ S) ⋅ S ⋅ S) ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S

/-- Zachos's 9-leaf productive precursor `S(S(SS))(S(SS))(SS)` and 10-leaf `Zachos` term. -/
def zachosPrecursor : Term := S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)
def zachos          : Term := (S ⋅ (S ⋅ S) ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S))

theorem toIntrinsic_wolfram2_eq : toIntrinsic wolfram_2 = IntrinsicTheorems.Wolfram2 := rfl
theorem toIntrinsic_zachos_eq   : toIntrinsic zachos = IntrinsicTheorems.Zachos := rfl

/-- Exact Mathematica `s[...]` serializer matching Stephen Wolfram's announcement syntax. -/
def toWolframStr : Term → String
  | .s => "s"
  | .var k => "x" ++ toString k
  | .app a b => toWolframStr a ++ "[" ++ toWolframStr b ++ "]"

/-- Character-for-character verification of all 14 expressions against `wolfram_announcement.txt`
    (line 131 and lines 147–153) and `WOLFRAM_12` in `analyze_wolfram_cases.py`. -/
theorem wolfram_14_announcement_roundtrip :
    toWolframStr wolfram7_a = "s[s][s][s[s]][s][s]" ∧
    toWolframStr wolfram7_b = "s[s[s]][s][s][s][s]" ∧
    toWolframStr wolfram_1  = "s[s[s[s[s]][s]]][s][s]" ∧
    toWolframStr wolfram_2  = "s[s][s][s[s[s]]][s[s]]" ∧
    toWolframStr wolfram_3  = "s[s][s][s[s[s[s][s]]]][s]" ∧
    toWolframStr wolfram_4  = "s[s[s[s]][s[s[s]][s]]][s][s]" ∧
    toWolframStr wolfram_5  = "s[s][s][s][s][s][s[s[s]]][s]" ∧
    toWolframStr wolfram_6  = "s[s][s][s[s[s[s][s]][s]]][s]" ∧
    toWolframStr wolfram_7  = "s[s[s][s][s[s]]][s[s][s]][s]" ∧
    toWolframStr wolfram_8  = "s[s][s][s[s[s]]][s[s]][s[s]]" ∧
    toWolframStr wolfram_9  = "s[s][s][s][s[s][s]][s][s][s][s]" ∧
    toWolframStr wolfram_10 = "s[s][s][s[s[s[s[s]][s]][s]]][s]" ∧
    toWolframStr wolfram_11 = "s[s][s][s[s][s[s[s[s][s]]]]][s]" ∧
    toWolframStr wolfram_12 = "s[s[s[s]][s][s]][s[s[s]][s]][s]" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exhaustive Catalan enumeration of closed pure-`S` binary trees by leaf count. -/
def listBind {α β : Type} : List α → (α → List β) → List β
  | [], _ => []
  | x :: xs, f => f x ++ listBind xs f

private theorem mem_listBind {α β : Type} {x : α} {y : β} {xs : List α} {f : α → List β}
    (hx : x ∈ xs) (hy : y ∈ f x) : y ∈ listBind xs f := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
    cases hx with
    | head _ => exact List.mem_append_left _ hy
    | tail _ hmem => exact List.mem_append_right _ (ih hmem)

private theorem mem_map {α β : Type} (f : α → β) {x : α} {xs : List α}
    (hx : x ∈ xs) : f x ∈ xs.map f := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
    cases hx with
    | head _ => exact List.Mem.head _
    | tail _ hmem => exact List.Mem.tail _ (ih hmem)

def splitsPos : Nat → List (Nat × Nat)
  | 0 => []
  | 1 => []
  | k + 2 => (1, k + 1) :: (splitsPos (k + 1)).map (fun p => (p.1 + 1, p.2))

private theorem mem_splitsPos : ∀ (a b : Nat), 1 ≤ a → 1 ≤ b → (a, b) ∈ splitsPos (a + b)
  | 0, _, ha, _ => by cases ha
  | _, 0, _, hb => by cases hb
  | 1, b' + 1, _, _ => by
    have heq : 1 + (b' + 1) = b' + 2 := Nat.add_comm 1 (b' + 1)
    rw [heq]
    exact List.Mem.head _
  | a' + 2, b' + 1, _, _ => by
    have ih := mem_splitsPos (a' + 1) (b' + 1) (Nat.succ_le_succ (Nat.zero_le _))
      (Nat.succ_le_succ (Nat.zero_le _))
    have hsum : (a' + 1) + (b' + 1) = (a' + b') + 2 := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hsum2 : (a' + 2) + (b' + 1) = ((a' + b') + 1) + 2 := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [hsum] at ih
    rw [hsum2]
    exact List.Mem.tail _ (mem_map (fun p : Nat × Nat => (p.1 + 1, p.2)) ih)

def closedTreesAux : Nat → Nat → List Term
  | _, 0 => []
  | _, 1 => [S]
  | 0, _ + 2 => []
  | fuel + 1, n + 2 =>
    listBind (splitsPos (n + 2)) (fun p =>
      listBind (closedTreesAux fuel p.1) (fun l =>
        (closedTreesAux fuel p.2).map (fun r => l ⋅ r)))

def closedTreesOfSize (n : Nat) : List Term :=
  closedTreesAux n n

private theorem mem_closedTreesAux :
    ∀ (fuel : Nat) {t : Term}, noVars t = true → leaves t ≤ fuel →
      t ∈ closedTreesAux fuel (leaves t)
  | 0, .s, _, _ => List.Mem.head []
  | _ + 1, .s, _, _ => List.Mem.head []
  | _, .var _, hv, _ => by cases hv
  | 0, .app a b, _, hle => by
    have h2 : 2 ≤ leaves a + leaves b := Nat.add_le_add (leaves_pos a) (leaves_pos b)
    exact False.elim (Nat.not_succ_le_zero 1 (Nat.le_trans h2 hle))
  | fuel + 1, .app a b, hv, hle => by
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    have hvb := ((Bool.and_eq_true _ _).mp hv).2
    have ha1 := leaves_pos a
    have hb1 := leaves_pos b
    have ha_fuel : leaves a ≤ fuel := by
      have h1 : leaves a + 1 ≤ leaves a + leaves b := Nat.add_le_add_left hb1 (leaves a)
      exact Nat.le_of_succ_le_succ (Nat.le_trans h1 hle)
    have hb_fuel : leaves b ≤ fuel := by
      have h1 : leaves b + 1 ≤ leaves a + leaves b := by
        rw [Nat.add_comm (leaves a) (leaves b)]
        exact Nat.add_le_add_left ha1 (leaves b)
      exact Nat.le_of_succ_le_succ (Nat.le_trans h1 hle)
    have hsum2 : ∃ m, leaves a + leaves b = m + 2 := by
      cases ha_eq : leaves a with
      | zero => rw [ha_eq] at ha1; cases ha1
      | succ a0 =>
        cases hb_eq : leaves b with
        | zero => rw [hb_eq] at hb1; cases hb1
        | succ b0 =>
          exact ⟨a0 + b0, by simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩
    obtain ⟨m, hm⟩ := hsum2
    change (a ⋅ b) ∈ closedTreesAux (fuel + 1) (leaves a + leaves b)
    have hsp : (leaves a, leaves b) ∈ splitsPos (m + 2) := hm ▸ mem_splitsPos _ _ ha1 hb1
    rw [hm]
    simp only [closedTreesAux]
    exact mem_listBind hsp (mem_listBind (mem_closedTreesAux fuel hva ha_fuel)
      (mem_map (fun r => a ⋅ r) (mem_closedTreesAux fuel hvb hb_fuel)))

theorem mem_closedTreesOfSize {t : Term} (hv : noVars t = true) :
    t ∈ closedTreesOfSize (leaves t) :=
  mem_closedTreesAux (leaves t) hv (Nat.le_refl _)

def beqTerm : Term → Term → Bool
  | .s, .s => true
  | .var a, .var b => decide (a = b)
  | .app a1 b1, .app a2 b2 => beqTerm a1 a2 && beqTerm b1 b2
  | _, _ => false

theorem beqTerm_eq {a b : Term} (h : beqTerm a b = true) : a = b := by
  induction a generalizing b with
  | s => cases b <;> first | rfl | cases h
  | var k =>
    cases b with
    | var m => exact congrArg Term.var (of_decide_eq_true h)
    | _ => cases h
  | app a1 b1 iha ihb =>
    cases b with
    | app a2 b2 =>
      have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
      rw [iha h1, ihb h2]
    | _ => cases h

private theorem list_all_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (hall : xs.all p = true) (hx : x ∈ xs) : p x = true := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
    simp only [List.all, Bool.and_eq_true] at hall
    cases hx with
    | head _ => exact hall.1
    | tail _ hmem => exact ih hall.2 hmem

set_option maxRecDepth 200000 in
private theorem size_le_6_all_sn_chk :
    (closedTreesOfSize 1).all (fun u => evalSN u != .sn38) = true ∧
    (closedTreesOfSize 2).all (fun u => evalSN u != .sn38) = true ∧
    (closedTreesOfSize 3).all (fun u => evalSN u != .sn38) = true ∧
    (closedTreesOfSize 4).all (fun u => evalSN u != .sn38) = true ∧
    (closedTreesOfSize 5).all (fun u => evalSN u != .sn38) = true ∧
    (closedTreesOfSize 6).all (fun u => evalSN u != .sn38) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 200000 in
private theorem size_7_nonsn_chk :
    (closedTreesOfSize 7).all (fun u =>
      (evalSN u != .sn38) || beqTerm u wolfram7_a || beqTerm u wolfram7_b) = true := rfl

/-- **Exact 7-Leaf Non-Halting Threshold Theorem**:
    1. Every closed pure-`S` expression with at most `6` leaves halts (`StrongNormalizing t`).
    2. Out of all `132` closed pure-`S` expressions with `7` leaves, **exclusively** `wolfram7_a`
       (`s[s][s][s[s]][s][s]`, Wolfram announcement line 131) and `wolfram7_b`
       (`s[s[s]][s][s][s][s]`) fail to halt! -/
theorem seven_leaf_nonhalting_classification {t : Term} (hv : noVars t = true) :
    (leaves t ≤ 6 → StrongNormalizing t) ∧
    (leaves t = 7 → ¬ StrongNormalizing t → t = wolfram7_a ∨ t = wolfram7_b) := by
  have hmem := mem_closedTreesOfSize hv
  constructor
  · intro hle6
    have hpos := leaves_pos t
    have hne38 : evalSN t ≠ .sn38 := by
      have ⟨c1, c2, c3, c4, c5, c6⟩ := size_le_6_all_sn_chk
      match hsz : leaves t with
      | 0 => rw [hsz] at hpos; cases hpos
      | 1 => exact of_decide_eq_true (by simpa [bne] using list_all_mem c1 (hsz ▸ hmem))
      | 2 => exact of_decide_eq_true (by simpa [bne] using list_all_mem c2 (hsz ▸ hmem))
      | 3 => exact of_decide_eq_true (by simpa [bne] using list_all_mem c3 (hsz ▸ hmem))
      | 4 => exact of_decide_eq_true (by simpa [bne] using list_all_mem c4 (hsz ▸ hmem))
      | 5 => exact of_decide_eq_true (by simpa [bne] using list_all_mem c5 (hsz ▸ hmem))
      | 6 => exact of_decide_eq_true (by simpa [bne] using list_all_mem c6 (hsz ▸ hmem))
      | n + 7 =>
        rw [hsz] at hle6
        exact False.elim (Nat.not_succ_le_zero n
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hle6)))))))
    exact (waldmann_theorem_9 hv).1.mpr hne38
  · intro hsz7 hnsn
    have h38 : evalSN t = .sn38 :=
      if h : evalSN t = .sn38 then h
      else False.elim (hnsn ((waldmann_theorem_9 hv).1.mpr h))
    have hc := list_all_mem size_7_nonsn_chk (hsz7 ▸ hmem)
    rw [h38] at hc
    change (false || beqTerm t wolfram7_a || beqTerm t wolfram7_b) = true at hc
    rw [Bool.false_or] at hc
    cases (Bool.or_eq_true _ _).mp hc with
    | inl ha => exact Or.inl (beqTerm_eq ha)
    | inr hb => exact Or.inr (beqTerm_eq hb)

/-! ## 3. Frozen Leftmost-Outermost HNF Context Calculus (`LOFrame`, `wrapLOContext`) -/

inductive LOFrame where
  | s1 : LOFrame
  | s2L (r : Term) : LOFrame
  | s2R (l : Term) : LOFrame
  deriving DecidableEq, Repr

def plugFrame : LOFrame → Term → Term
  | .s1, u => S ⋅ u
  | .s2L r, u => S ⋅ u ⋅ r
  | .s2R l, u => S ⋅ l ⋅ u

def validLOFrame : LOFrame → Bool
  | .s1 => true
  | .s2L r => noVars r
  | .s2R l => noVars l && (stepLO l).isNone

def wrapLOContext : List LOFrame → Term → Term
  | [], u => u
  | f :: fs, u => plugFrame f (wrapLOContext fs u)

def validLOContext : List LOFrame → Bool
  | [] => true
  | f :: fs => validLOFrame f && validLOContext fs

theorem wrapLOContext_append (c1 c2 : List LOFrame) (u : Term) :
    wrapLOContext (c1 ++ c2) u = wrapLOContext c1 (wrapLOContext c2 u) := by
  induction c1 with
  | nil => rfl
  | cons f fs ih => simp only [List.cons_append, wrapLOContext, ih]

theorem validLOContext_append {c1 c2 : List LOFrame}
    (h1 : validLOContext c1 = true) (h2 : validLOContext c2 = true) :
    validLOContext (c1 ++ c2) = true := by
  induction c1 with
  | nil => exact h2
  | cons f fs ih =>
    simp only [validLOContext, Bool.and_eq_true] at h1
    simp only [List.cons_append, validLOContext, Bool.and_eq_true]
    exact ⟨h1.1, ih h1.2⟩

theorem noVars_wrapLOContext {ctx : List LOFrame} {u : Term}
    (hc : validLOContext ctx = true) (hu : noVars u = true) :
    noVars (wrapLOContext ctx u) = true := by
  induction ctx with
  | nil => exact hu
  | cons f fs ih =>
    simp only [validLOContext, Bool.and_eq_true] at hc
    have hsub := ih hc.2
    cases f with
    | s1 => exact hsub
    | s2L r => exact (Bool.and_eq_true _ _).mpr ⟨hsub, hc.1⟩
    | s2R l =>
      have hl := ((Bool.and_eq_true _ _).mp hc.1).1
      exact (Bool.and_eq_true _ _).mpr ⟨hl, hsub⟩

theorem stepLO_plugFrame {f : LOFrame} (hf : validLOFrame f = true)
    {u u' : Term} (hu : stepLO u = some u') :
    stepLO (plugFrame f u) = some (plugFrame f u') := by
  cases f with
  | s1 =>
    simp only [plugFrame, stepLO, rootRedexOpt, S, hu]
  | s2L r =>
    simp only [plugFrame, stepLO, rootRedexOpt, S, hu]
  | s2R l =>
    have hnone_bool : (stepLO l).isNone = true := ((Bool.and_eq_true _ _).mp hf).2
    have hl : stepLO l = none := by
      cases hs : stepLO l with
      | none => rfl
      | some _ => rw [hs] at hnone_bool; cases hnone_bool
    simp only [plugFrame, stepLO, rootRedexOpt, S, hl, hu]

theorem stepLO_wrapLOContext {ctx : List LOFrame} (hc : validLOContext ctx = true)
    {u u' : Term} (hu : stepLO u = some u') :
    stepLO (wrapLOContext ctx u) = some (wrapLOContext ctx u') := by
  induction ctx with
  | nil => exact hu
  | cons f fs ih =>
    simp only [validLOContext, Bool.and_eq_true] at hc
    exact stepLO_plugFrame hc.1 (ih hc.2)

theorem headStepOpt_some_imp_stepLO {t t' : Term} (h : headStepOpt t = some t') :
    stepLO t = some t' := by
  induction t generalizing t' with
  | s => cases h
  | var _ => cases h
  | app a b iha _ =>
    simp only [headStepOpt] at h
    simp only [stepLO]
    cases hr : rootRedexOpt a b with
    | some r =>
      rw [hr] at h
      exact h
    | none =>
      rw [hr] at h
      cases ha : headStepOpt a with
      | some a' =>
        rw [ha] at h
        rw [iha ha]
        exact h
      | none =>
        rw [ha] at h
        cases h

theorem closed_spineLen_ge_3_has_headStep {t : Term}
    (hv : noVars t = true) (hsl : 3 ≤ spineLen t) :
    ∃ t', headStepOpt t = some t' := by
  cases hh : headStepOpt t with
  | some t' => exact ⟨t', rfl⟩
  | none =>
    have hle2 := headStepOpt_none_spineLen hv hh
    exact False.elim (Nat.not_succ_le_zero 0
      (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_trans hsl hle2))))

theorem evalHN_hn34_spineLen_ge_3 {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) :
    3 ≤ spineLen t := by
  match hsp : spineLen t with
  | 0 => exact False.elim (closed_hnf_evalHN_ne_hn34 hv (by rw [hsp]; exact Nat.zero_le 2) h34)
  | 1 => exact False.elim (closed_hnf_evalHN_ne_hn34 hv (by rw [hsp]; exact Nat.succ_le_succ (Nat.zero_le 1)) h34)
  | 2 => exact False.elim (closed_hnf_evalHN_ne_hn34 hv (by rw [hsp]; exact Nat.le_refl 2) h34)
  | n + 3 => exact Nat.le_add_left 3 n

/-- Once `stepLO` reaches a valid frozen HNF context `ctx` around a closed `.hn34` focus `foc`,
    `ctx` remains **permanently frozen** for all future steps `k : Nat`, and `stepLO` executes
    pure head reduction inside `foc` forever without ever halting. -/
theorem locked_hn34_forever {ctx : List LOFrame} {foc : Term}
    (hc : validLOContext ctx = true) (hvf : noVars foc = true) (h34 : evalHN foc = .hn34)
    (k : Nat) :
    iterateLO k (wrapLOContext ctx foc) = wrapLOContext ctx (iterateLO k foc) ∧
    noVars (iterateLO k foc) = true ∧
    evalHN (iterateLO k foc) = .hn34 ∧
    3 ≤ spineLen (iterateLO k foc) ∧
    HeadStepsN k foc (iterateLO k foc) ∧
    (stepLO (iterateLO k (wrapLOContext ctx foc))).isSome = true := by
  induction k generalizing foc with
  | zero =>
    obtain ⟨f', hhf'⟩ := evalHN_hn34_has_headStep hvf h34
    have hsl_step := stepLO_wrapLOContext hc (headStepOpt_some_imp_stepLO hhf'.1)
    refine ⟨rfl, hvf, h34, evalHN_hn34_spineLen_ge_3 hvf h34, HeadStepsN.zero foc, ?_⟩
    simp only [iterateLO, hsl_step, Option.isSome]
  | succ k ih =>
    obtain ⟨foc', hhf, hhs, hvf', h34'⟩ := evalHN_hn34_has_headStep hvf h34
    have hlo_foc := headStepOpt_some_imp_stepLO hhf
    have hlo_wrap := stepLO_wrapLOContext hc hlo_foc
    obtain ⟨heq_k, hvk, h34k, hslk, hhsk, hsomek⟩ := ih hvf' h34'
    simp only [iterateLO, hlo_wrap, hlo_foc]
    exact ⟨heq_k, hvk, h34k, hslk, HeadStepsN.succ hhs hhsk, hsomek⟩

private theorem plugFrame_spineLen_le_2 (f : LOFrame) (u : Term) :
    spineLen (plugFrame f u) ≤ 2 := by
  cases f with
  | s1 => exact Nat.succ_le_succ (Nat.zero_le 1)
  | s2L _ => exact Nat.le_refl 2
  | s2R _ => exact Nat.le_refl 2

/-- Uniqueness of the active normal-order focus `(ctx, foc)` inside a valid HNF context. -/
theorem wrapLOContext_focus_unique :
    ∀ {c1 c2 : List LOFrame} {f1 f2 : Term},
      validLOContext c1 = true → validLOContext c2 = true →
      noVars f1 = true → noVars f2 = true →
      3 ≤ spineLen f1 → 3 ≤ spineLen f2 →
      wrapLOContext c1 f1 = wrapLOContext c2 f2 →
      c1 = c2 ∧ f1 = f2
  | [], [], _, _, _, _, _, _, _, _, heq => ⟨rfl, heq⟩
  | [], g :: gs, f1, f2, _, _, _, _, hsl1, _, heq => by
    have hle2 : spineLen f1 ≤ 2 := by
      change spineLen (wrapLOContext [] f1) ≤ 2
      rw [heq]
      exact plugFrame_spineLen_le_2 g (wrapLOContext gs f2)
    exact False.elim (Nat.not_succ_le_zero 0
      (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_trans hsl1 hle2))))
  | f :: fs, [], f1, f2, _, _, _, _, _, hsl2, heq => by
    have hle2 : spineLen f2 ≤ 2 := by
      change spineLen (wrapLOContext [] f2) ≤ 2
      rw [← heq]
      exact plugFrame_spineLen_le_2 f (wrapLOContext fs f1)
    exact False.elim (Nat.not_succ_le_zero 0
      (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_trans hsl2 hle2))))
  | f :: fs, g :: gs, f1, f2, hc1, hc2, hv1, hv2, hsl1, hsl2, heq => by
    simp only [validLOContext, Bool.and_eq_true] at hc1 hc2
    cases f with
    | s1 =>
      cases g with
      | s1 =>
        injection heq with _ hsub
        obtain ⟨hcs, hfs⟩ := wrapLOContext_focus_unique hc1.2 hc2.2 hv1 hv2 hsl1 hsl2 hsub
        exact ⟨congrArg (.s1 :: ·) hcs, hfs⟩
      | s2L _ => injection heq with hbad _; cases hbad
      | s2R _ => injection heq with hbad _; cases hbad
    | s2L r1 =>
      cases g with
      | s1 => injection heq with hbad _; cases hbad
      | s2L r2 =>
        injection heq with h1 hr
        injection h1 with _ hsub
        obtain ⟨hcs, hfs⟩ := wrapLOContext_focus_unique hc1.2 hc2.2 hv1 hv2 hsl1 hsl2 hsub
        exact ⟨hr ▸ congrArg (.s2L r1 :: ·) hcs, hfs⟩
      | s2R l2 =>
        injection heq with h1 _
        injection h1 with _ hsub
        obtain ⟨u', hhu'⟩ := closed_spineLen_ge_3_has_headStep hv1 hsl1
        have hstep_sub := stepLO_wrapLOContext hc1.2 (headStepOpt_some_imp_stepLO hhu')
        have hnone_l2 : (stepLO l2).isNone = true := ((Bool.and_eq_true _ _).mp hc2.1).2
        rw [← hsub, hstep_sub] at hnone_l2
        cases hnone_l2
    | s2R l1 =>
      cases g with
      | s1 => injection heq with hbad _; cases hbad
      | s2L r2 =>
        injection heq with h1 _
        injection h1 with _ hsub
        obtain ⟨u', hhu'⟩ := closed_spineLen_ge_3_has_headStep hv2 hsl2
        have hstep_sub := stepLO_wrapLOContext hc2.2 (headStepOpt_some_imp_stepLO hhu')
        have hnone_l1 : (stepLO l1).isNone = true := ((Bool.and_eq_true _ _).mp hc1.1).2
        rw [hsub, hstep_sub] at hnone_l1
        cases hnone_l1
      | s2R l2 =>
        injection heq with h1 hsub
        injection h1 with _ hl
        obtain ⟨hcs, hfs⟩ := wrapLOContext_focus_unique hc1.2 hc2.2 hv1 hv2 hsl1 hsl2 hsub
        exact ⟨hl ▸ congrArg (.s2R l1 :: ·) hcs, hfs⟩

/-! ## 4. Closed-Form Trajectory & Böhm-Productivity Separation of `wolfram_2` vs `zachos` -/

def w2Base : Term := S ⋅ (S ⋅ B_comb) ⋅ B_comb

def w2Tower : Nat → Term
  | 0 => w2Base
  | k + 1 => B_comb ⋅ w2Tower k

theorem noVars_w2Tower (k : Nat) : noVars (w2Tower k) = true := by
  induction k with
  | zero => rfl
  | succ _ ih => exact ih

theorem stepLO_w2Tower_none (k : Nat) : stepLO (w2Tower k) = none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [w2Tower, B_comb, stepLO, rootRedexOpt, S, ih]

theorem evalHN_w2Tower_succ (k : Nat) : evalHN (w2Tower (k + 1)) = .hn13 := by
  induction k with
  | zero => rfl
  | succ _ ih =>
    change deltaHN .hn1 (evalHN (w2Tower _)) = .hn13
    rw [ih]
    rfl

theorem evalHN_w2Base_app_tower (k : Nat) :
    evalHN (w2Base ⋅ w2Tower (k + 1)) = .hn23 := by
  change deltaHN (evalHN w2Base) (evalHN (w2Tower (k + 1))) = .hn23
  rw [evalHN_w2Tower_succ k]
  rfl

theorem evalHN_w2Tower_app_tower (m k : Nat) :
    evalHN (w2Tower (m + 1) ⋅ w2Tower (k + 1)) = .hn24 := by
  change deltaHN (evalHN (w2Tower (m + 1))) (evalHN (w2Tower (k + 1))) = .hn24
  rw [evalHN_w2Tower_succ m, evalHN_w2Tower_succ k]
  rfl

private theorem w2_countdown :
    ∀ (m : Nat) (z : Term), noVars z = true → stepLO z = none →
      ∀ (ctx : List LOFrame), validLOContext ctx = true →
        ∃ ctx' : List LOFrame,
          validLOContext ctx' = true ∧
          ctx'.length = ctx.length + m ∧
          iterateLO m (wrapLOContext ctx (w2Tower m ⋅ z)) =
            wrapLOContext ctx' (w2Base ⋅ z)
  | 0, _, _, _, ctx, hctx => ⟨ctx, hctx, (Nat.add_zero _).symm, rfl⟩
  | m + 1, z, hvz, hnz, ctx, hctx => by
    have hs1 : stepLO (w2Tower (m + 1) ⋅ z) = some (plugFrame (.s2R z) (w2Tower m ⋅ z)) := rfl
    have hv_fr : validLOContext [.s2R z] = true := by
      simp only [validLOContext, validLOFrame, hvz, hnz, Option.isNone, Bool.and_true]
    have hctx1 : validLOContext (ctx ++ [.s2R z]) = true := validLOContext_append hctx hv_fr
    have hstep1 : iterateLO 1 (wrapLOContext ctx (w2Tower (m + 1) ⋅ z)) =
        wrapLOContext (ctx ++ [.s2R z]) (w2Tower m ⋅ z) := by
      rw [wrapLOContext_append]
      simp only [iterateLO, stepLO_wrapLOContext hctx hs1, wrapLOContext]
    obtain ⟨ctx', hvc', hlen', hrest⟩ := w2_countdown m z hvz hnz (ctx ++ [.s2R z]) hctx1
    refine ⟨ctx', hvc', ?_, ?_⟩
    · rw [hlen', List.length_append, List.length, List.length, Nat.add_assoc, Nat.add_comm 1 m]
    · simp only [iterateLO, stepLO_wrapLOContext hctx hs1]
      change iterateLO m (wrapLOContext ctx (wrapLOContext [.s2R z] (w2Tower m ⋅ z))) =
        wrapLOContext ctx' (w2Base ⋅ z)
      rw [← wrapLOContext_append ctx [.s2R z] (w2Tower m ⋅ z)]
      exact hrest

private def w2StepsRec : Nat → Nat
  | 0 => 4
  | n + 1 => w2StepsRec n + (n + 4)

private def w2DepthRec : Nat → Nat
  | 0 => 1
  | n + 1 => w2DepthRec n + (n + 2)

private theorem two_mul_w2DepthRec (n : Nat) :
    2 * w2DepthRec n = (n + 1) * (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [w2DepthRec, Nat.mul_add]
    rw [ih]
    simp only [Nat.mul_succ, Nat.succ_mul, Nat.zero_mul, Nat.mul_zero,
      Nat.add_succ, Nat.succ_add, Nat.add_zero,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem w2DepthRec_eq (n : Nat) :
    w2DepthRec n = (n + 1) * (n + 2) / 2 := by
  rw [← two_mul_w2DepthRec n]
  exact (Nat.mul_div_right (w2DepthRec n) (by decide : 0 < 2)).symm

private theorem two_mul_w2StepsSub1 (n : Nat) :
    2 * (w2StepsRec n - 1) = (n + 1) * (n + 6) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpos : 1 ≤ w2StepsRec n := by
      clear ih
      induction n with
      | zero => exact Nat.le_add_left 1 3
      | succ _ ihn => exact Nat.le_trans ihn (Nat.le_add_right _ _)
    have hsub : w2StepsRec n + (n + 4) - 1 = (w2StepsRec n - 1) + (n + 4) := by
      cases hw : w2StepsRec n with
      | zero => rw [hw] at hpos; cases hpos
      | succ w0 =>
        simp only [Nat.succ_sub_one, Nat.succ_add]
    simp only [w2StepsRec, hsub, Nat.mul_add]
    rw [ih]
    simp only [Nat.mul_succ, Nat.succ_mul, Nat.zero_mul, Nat.mul_zero,
      Nat.add_succ, Nat.succ_add, Nat.add_zero,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Closed-form step count `(n + 1) * (n + 6) / 2 + 1` ($4, 8, 13, 19, 26, \dots$) at which
    `wolfram_2` enters macro-cycle `n + 1` under `stepLO`. -/
def jumpAheadWolfram2Step (n : Nat) : Nat :=
  (n + 1) * (n + 6) / 2 + 1

private theorem w2StepsRec_eq (n : Nat) :
    w2StepsRec n = jumpAheadWolfram2Step n := by
  have hpos : 1 ≤ w2StepsRec n := by
    induction n with
    | zero => exact Nat.le_add_left 1 3
    | succ _ ihn => exact Nat.le_trans ihn (Nat.le_add_right _ _)
  unfold jumpAheadWolfram2Step
  rw [← two_mul_w2StepsSub1 n, Nat.mul_div_right _ (by decide : 0 < 2)]
  cases hw : w2StepsRec n with
  | zero => rw [hw] at hpos; cases hpos
  | succ w0 => rfl

/-- **Closed-Form `stepLO` Jump-Ahead Theorem for `wolfram_2`**:
    For every `n : Nat`, after `(n + 1) * (n + 6) / 2 + 1` leftmost-outermost steps,
    `wolfram_2` equals `wrapLOContext ctx (w2Base ⋅ w2Tower (n + 1))` with exact HNF frame
    depth `(n + 1) * (n + 2) / 2` and active focus in `HN \ SN` (`evalHN = .hn23 ≠ .hn34`). -/
theorem wolfram2_closed_form_jump_ahead (n : Nat) :
    ∃ ctx : List LOFrame,
      validLOContext ctx = true ∧
      ctx.length = (n + 1) * (n + 2) / 2 ∧
      iterateLO (jumpAheadWolfram2Step n) wolfram_2 =
        wrapLOContext ctx (w2Base ⋅ w2Tower (n + 1)) ∧
      evalHN (w2Base ⋅ w2Tower (n + 1)) = .hn23 := by
  rw [← w2StepsRec_eq n, ← w2DepthRec_eq n]
  refine (?_ : ∃ ctx, validLOContext ctx = true ∧ ctx.length = w2DepthRec n ∧
      iterateLO (w2StepsRec n) wolfram_2 = wrapLOContext ctx (w2Base ⋅ w2Tower (n + 1))).elim
    (fun ctx ⟨h1, h2, h3⟩ => ⟨ctx, h1, h2, h3, evalHN_w2Base_app_tower n⟩)
  induction n with
  | zero =>
    exact ⟨[.s2R (w2Tower 1)], rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨ctx, hvc, hlen, hreach⟩ := ih
    let u0 := w2Base ⋅ w2Tower (k + 1)
    let u1 := (S ⋅ B_comb ⋅ w2Tower (k + 1)) ⋅ w2Tower (k + 2)
    let u2 := w2Tower (k + 3) ⋅ (w2Tower (k + 1) ⋅ w2Tower (k + 2))
    let rFreeze := w2Tower (k + 2) ⋅ (w2Tower (k + 1) ⋅ w2Tower (k + 2))
    let u3 := plugFrame (.s2L rFreeze) (w2Tower (k + 1) ⋅ w2Tower (k + 2))
    have hs0 : stepLO u0 = some u1 := rfl
    have hs1 : stepLO u1 = some u2 := rfl
    have hs2 : stepLO u2 = some u3 := rfl
    have hv_rf : validLOContext [.s2L rFreeze] = true := by
      simp only [validLOContext, validLOFrame, rFreeze, noVars,
        noVars_w2Tower, Bool.and_self]
    have h3 : iterateLO 3 (wrapLOContext ctx u0) =
        wrapLOContext (ctx ++ [.s2L rFreeze]) (w2Tower (k + 1) ⋅ w2Tower (k + 2)) := by
      rw [wrapLOContext_append]
      simp only [iterateLO,
        stepLO_wrapLOContext hvc hs0,
        stepLO_wrapLOContext hvc hs1,
        stepLO_wrapLOContext hvc hs2,
        wrapLOContext]
      rfl
    obtain ⟨ctx', hvc', hlen', hcd⟩ :=
      w2_countdown (k + 1) (w2Tower (k + 2)) (noVars_w2Tower _) (stepLO_w2Tower_none _)
        (ctx ++ [.s2L rFreeze]) (validLOContext_append hvc hv_rf)
    refine ⟨ctx', hvc', ?_, ?_⟩
    · rw [hlen', List.length_append, hlen]
      simp only [w2DepthRec, List.length, Nat.add_succ, Nat.succ_add, Nat.add_zero, Nat.zero_add,
        Nat.add_comm]
    · have hk4 : k + 4 = 3 + (k + 1) := by
        simp only [Nat.add_succ, Nat.succ_add, Nat.add_zero, Nat.add_comm]
      simp only [w2StepsRec]
      rw [iterateLO_add (w2StepsRec k) (k + 4), hreach, hk4, iterateLO_add 3 (k + 1), h3, hcd]

private theorem w2_countdown_focus_safe :
    ∀ (m j : Nat), j ≤ m →
      ∀ (k : Nat) (ctx : List LOFrame), validLOContext ctx = true →
        ∃ c foc,
          validLOContext c = true ∧
          iterateLO j (wrapLOContext ctx (w2Tower m ⋅ w2Tower (k + 2))) = wrapLOContext c foc ∧
          noVars foc = true ∧ 3 ≤ spineLen foc ∧ evalHN foc ≠ .hn34
  | m, 0, _, k, ctx, hctx => by
    refine ⟨ctx, w2Tower m ⋅ w2Tower (k + 2), hctx, rfl,
      (Bool.and_eq_true _ _).mpr ⟨noVars_w2Tower m, noVars_w2Tower (k + 2)⟩, ?_, ?_⟩
    · cases m <;> exact Nat.le_refl 3
    · cases m with
      | zero => rw [w2Tower, evalHN_w2Base_app_tower (k + 1)]; intro h; cases h
      | succ m0 => rw [evalHN_w2Tower_app_tower m0 (k + 1)]; intro h; cases h
  | 0, j + 1, hj, _, _, _ => by cases hj
  | m + 1, j + 1, hj, k, ctx, hctx => by
    let z := w2Tower (k + 2)
    have hs1 : stepLO (w2Tower (m + 1) ⋅ z) = some (plugFrame (.s2R z) (w2Tower m ⋅ z)) := rfl
    have hv_fr : validLOContext [.s2R z] = true := by
      simp only [validLOContext, validLOFrame, z, noVars_w2Tower, stepLO_w2Tower_none,
        Option.isNone, Bool.and_true]
    have hstep1 : iterateLO (j + 1) (wrapLOContext ctx (w2Tower (m + 1) ⋅ z)) =
        iterateLO j (wrapLOContext (ctx ++ [.s2R z]) (w2Tower m ⋅ z)) := by
      have hj1 : j + 1 = 1 + j := Nat.add_comm j 1
      rw [hj1, iterateLO_add 1 j, wrapLOContext_append]
      simp only [iterateLO, stepLO_wrapLOContext hctx hs1, wrapLOContext]
    rw [hstep1]
    exact w2_countdown_focus_safe m j (Nat.le_of_succ_le_succ hj) k (ctx ++ [.s2R z])
      (validLOContext_append hctx hv_fr)

private theorem w2_all_steps_upto (n : Nat) :
    ∀ t, t ≤ w2StepsRec n →
      ∃ ctx foc,
        validLOContext ctx = true ∧
        iterateLO t wolfram_2 = wrapLOContext ctx foc ∧
        noVars foc = true ∧ 3 ≤ spineLen foc ∧ evalHN foc ≠ .hn34 := by
  induction n with
  | zero =>
    intro t ht
    match t with
    | 0 => exact ⟨[], iterateLO 0 wolfram_2, rfl, rfl, rfl, Nat.le_add_left 3 1, fun h => by cases h⟩
    | 1 => exact ⟨[], iterateLO 1 wolfram_2, rfl, rfl, rfl, Nat.le_refl 3, fun h => by cases h⟩
    | 2 => exact ⟨[], iterateLO 2 wolfram_2, rfl, rfl, rfl, Nat.le_refl 3, fun h => by cases h⟩
    | 3 => exact ⟨[], iterateLO 3 wolfram_2, rfl, rfl, rfl, Nat.le_refl 3, fun h => by cases h⟩
    | 4 =>
      exact ⟨[.s2R (w2Tower 1)], w2Base ⋅ w2Tower 1, rfl, rfl, rfl, Nat.le_refl 3, fun h => by cases h⟩
    | r + 5 =>
      exact False.elim (Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ ht)))))
  | succ k ih =>
    intro t ht
    if hle : t ≤ w2StepsRec k then
      exact ih t hle
    else
      obtain ⟨ctx, hvc, _, hreach0, _⟩ := wolfram2_closed_form_jump_ahead k
      have hreach : iterateLO (w2StepsRec k) wolfram_2 = wrapLOContext ctx (w2Base ⋅ w2Tower (k + 1)) := by
        rw [w2StepsRec_eq k]
        exact hreach0
      let d := t - w2StepsRec k
      have htd : t = w2StepsRec k + d := (Nat.add_sub_of_le (Nat.le_of_not_le hle)).symm
      have hd_le : d ≤ k + 4 := by
        have h1 : w2StepsRec k + d ≤ w2StepsRec k + (k + 4) := htd ▸ ht
        exact Nat.le_of_add_le_add_left h1
      rw [htd, iterateLO_add (w2StepsRec k) d, hreach]
      let u0 := w2Base ⋅ w2Tower (k + 1)
      let u1 := (S ⋅ B_comb ⋅ w2Tower (k + 1)) ⋅ w2Tower (k + 2)
      let u2 := w2Tower (k + 3) ⋅ (w2Tower (k + 1) ⋅ w2Tower (k + 2))
      let rFreeze := w2Tower (k + 2) ⋅ (w2Tower (k + 1) ⋅ w2Tower (k + 2))
      have hs0 : stepLO u0 = some u1 := rfl
      have hs1 : stepLO u1 = some u2 := rfl
      have hs2 : stepLO u2 = some (plugFrame (.s2L rFreeze) (w2Tower (k + 1) ⋅ w2Tower (k + 2))) := rfl
      match d with
      | 0 =>
        exact ⟨ctx, u0, hvc, rfl,
          (Bool.and_eq_true _ _).mpr ⟨rfl, noVars_w2Tower (k + 1)⟩,
          Nat.le_refl 3, by rw [evalHN_w2Base_app_tower k]; intro h; cases h⟩
      | 1 =>
        have hstep : iterateLO 1 (wrapLOContext ctx u0) = wrapLOContext ctx u1 := by
          simp only [iterateLO, stepLO_wrapLOContext hvc hs0]
        have hev : evalHN u1 = .hn23 := by
          rw [← evalHN_step (stepLO_some_step hs0)]
          exact evalHN_w2Base_app_tower k
        exact ⟨ctx, u1, hvc, hstep,
          noVars_step (stepLO_some_step hs0) ((Bool.and_eq_true _ _).mpr ⟨rfl, noVars_w2Tower (k + 1)⟩),
          Nat.le_refl 3, by rw [hev]; intro h; cases h⟩
      | 2 =>
        have hstep : iterateLO 2 (wrapLOContext ctx u0) = wrapLOContext ctx u2 := by
          simp only [iterateLO, stepLO_wrapLOContext hvc hs0, stepLO_wrapLOContext hvc hs1]
        have hev : evalHN u2 = .hn23 := by
          rw [← evalHN_step (stepLO_some_step hs1), ← evalHN_step (stepLO_some_step hs0)]
          exact evalHN_w2Base_app_tower k
        exact ⟨ctx, u2, hvc, hstep,
          noVars_step (stepLO_some_step hs1)
            (noVars_step (stepLO_some_step hs0) ((Bool.and_eq_true _ _).mpr ⟨rfl, noVars_w2Tower (k + 1)⟩)),
          Nat.le_refl 3, by rw [hev]; intro h; cases h⟩
      | j + 3 =>
        have hj_le : j ≤ k + 1 :=
          Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hd_le))
        have hv_rf : validLOContext [.s2L rFreeze] = true := by
          simp only [validLOContext, validLOFrame, rFreeze, noVars,
            noVars_w2Tower, Bool.and_self]
        have hstep3 : iterateLO (j + 3) (wrapLOContext ctx u0) =
            iterateLO j (wrapLOContext (ctx ++ [.s2L rFreeze]) (w2Tower (k + 1) ⋅ w2Tower (k + 2))) := by
          have hj3 : j + 3 = 3 + j := Nat.add_comm j 3
          rw [hj3, iterateLO_add 3 j, wrapLOContext_append]
          simp only [iterateLO,
            stepLO_wrapLOContext hvc hs0,
            stepLO_wrapLOContext hvc hs1,
            stepLO_wrapLOContext hvc hs2,
            wrapLOContext]
        rw [hstep3]
        exact w2_countdown_focus_safe (k + 1) j hj_le k (ctx ++ [.s2L rFreeze])
          (validLOContext_append hvc hv_rf)

private theorem le_w2StepsRec (t : Nat) : t ≤ w2StepsRec t := by
  induction t with
  | zero => exact Nat.zero_le 4
  | succ m ih =>
    simp only [w2StepsRec]
    exact Nat.le_trans (Nat.succ_le_succ ih) (by
      have h1 : 1 ≤ m + 4 := Nat.le_add_left 1 (m + 3)
      exact Nat.add_le_add_left h1 (w2StepsRec m))

/-- **Perpetual `HN \ SN` Theorem for `wolfram_2` Under `stepLO`**:
    At **every** time step `t : Nat`, `iterateLO t wolfram_2` decomposes uniquely into a valid
    frozen HNF context around an active closed redex container `foc` (`3 ≤ spineLen foc`) with
    `evalHN foc ≠ .hn34`. Consequently, `wolfram_2` never halts AND never locks into `.hn34`
    under `stepLO` at any step `t : Nat`! -/
theorem wolfram2_perpetual_hn_minus_sn (t : Nat) :
    (∃ ctx foc,
      validLOContext ctx = true ∧
      iterateLO t wolfram_2 = wrapLOContext ctx foc ∧
      noVars foc = true ∧ 3 ≤ spineLen foc ∧ evalHN foc ≠ .hn34) ∧
    (∀ ctx' foc',
      validLOContext ctx' = true → noVars foc' = true → 3 ≤ spineLen foc' →
      iterateLO t wolfram_2 = wrapLOContext ctx' foc' → evalHN foc' ≠ .hn34) := by
  have hex := w2_all_steps_upto t t (le_w2StepsRec t)
  refine ⟨hex, ?_⟩
  intro ctx' foc' hvc' hvf' hsl' heq'
  obtain ⟨ctx, foc, hvc, heq, hvf, hsl, hne⟩ := hex
  obtain ⟨_, hfoc_eq⟩ := wrapLOContext_focus_unique hvc hvc' hvf hvf' hsl hsl' (heq.symm.trans heq')
  exact hfoc_eq ▸ hne

/-- Closed-form `iterateHead` reducer for explicit Böhm-tree navigation. -/
def iterateHead : Nat → Term → Term
  | 0, t => t
  | k + 1, t =>
    match headStepOpt t with
    | some t' => iterateHead k t'
    | none => t

theorem iterateHead_headReduces (k : Nat) (t : Term) :
    HeadReduces t (iterateHead k t) := by
  induction k generalizing t with
  | zero => exact HeadReduces.refl t
  | succ k ih =>
    simp only [iterateHead]
    cases hh : headStepOpt t with
    | none => exact HeadReduces.refl t
    | some t' => exact HeadReduces.next (headStepOpt_some hh) (ih t')

def zachosBase : Term := S ⋅ B_comb ⋅ B_comb

def zachosTower : Nat → Term
  | 0 => zachosBase
  | k + 1 => B_comb ⋅ zachosTower k

theorem noVars_zachosTower (k : Nat) : noVars (zachosTower k) = true := by
  induction k with
  | zero => rfl
  | succ _ ih => exact ih

theorem stepLO_zachosTower_none (k : Nat) : stepLO (zachosTower k) = none := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zachosTower, B_comb, stepLO, rootRedexOpt, S, ih]

private theorem zachos_countdown :
    ∀ (m : Nat) (z : Term), noVars z = true → stepLO z = none →
      ∀ (ctx : List LOFrame), validLOContext ctx = true →
        ∃ ctx' : List LOFrame,
          validLOContext ctx' = true ∧
          ctx'.length = ctx.length + m ∧
          iterateLO m (wrapLOContext ctx (zachosTower m ⋅ z)) =
            wrapLOContext ctx' (zachosBase ⋅ z)
  | 0, _, _, _, ctx, hctx => ⟨ctx, hctx, (Nat.add_zero _).symm, rfl⟩
  | m + 1, z, hvz, hnz, ctx, hctx => by
    have hs1 : stepLO (zachosTower (m + 1) ⋅ z) = some (plugFrame (.s2R z) (zachosTower m ⋅ z)) := rfl
    have hv_fr : validLOContext [.s2R z] = true := by
      simp only [validLOContext, validLOFrame, hvz, hnz, Option.isNone, Bool.and_true]
    obtain ⟨ctx', hvc', hlen', hrest⟩ :=
      zachos_countdown m z hvz hnz (ctx ++ [.s2R z]) (validLOContext_append hctx hv_fr)
    refine ⟨ctx', hvc', ?_, ?_⟩
    · rw [hlen', List.length_append, List.length, List.length, Nat.add_assoc, Nat.add_comm 1 m]
    · simp only [iterateLO, stepLO_wrapLOContext hctx hs1]
      change iterateLO m (wrapLOContext ctx (wrapLOContext [.s2R z] (zachosTower m ⋅ z))) =
        wrapLOContext ctx' (zachosBase ⋅ z)
      rw [← wrapLOContext_append ctx [.s2R z] (zachosTower m ⋅ z)]
      exact hrest

private def zachosStepsRec : Nat → Nat
  | 0 => 0
  | n + 1 => zachosStepsRec n + (n + 2)

private def zachosDepthRec : Nat → Nat
  | 0 => 0
  | n + 1 => zachosDepthRec n + (n + 1)

private theorem two_mul_zachosStepsRec (n : Nat) :
    2 * zachosStepsRec n = n * (n + 3) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zachosStepsRec, Nat.mul_add]
    rw [ih]
    simp only [Nat.mul_succ, Nat.succ_mul, Nat.zero_mul, Nat.mul_zero,
      Nat.add_succ, Nat.succ_add, Nat.add_zero,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem two_mul_zachosDepthRec (n : Nat) :
    2 * zachosDepthRec n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zachosDepthRec, Nat.mul_add]
    rw [ih]
    simp only [Nat.mul_succ, Nat.succ_mul, Nat.zero_mul, Nat.mul_zero,
      Nat.add_succ, Nat.succ_add, Nat.add_zero,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Closed-form step count `n * (n + 3) / 2` ($0, 2, 5, 9, 14, 20, \dots$) for `zachos`. -/
def jumpAheadZachosStep (n : Nat) : Nat :=
  n * (n + 3) / 2

/-- **Closed-Form `stepLO` Jump-Ahead Theorem for `zachos`**:
    For every `n : Nat`, after `n * (n + 3) / 2` leftmost-outermost steps, `zachos` equals
    `wrapLOContext ctx (zachosBase ⋅ zachosTower n)` with exact pure-`.s2R` normal-form HNF
    depth `n * (n + 1) / 2` and `evalP = .p29 ≠ .p37`. -/
theorem zachos_closed_form_jump_ahead (n : Nat) :
    ∃ ctx : List LOFrame,
      validLOContext ctx = true ∧
      ctx.length = n * (n + 1) / 2 ∧
      iterateLO (jumpAheadZachosStep n) zachos =
        wrapLOContext ctx (zachosBase ⋅ zachosTower n) ∧
      evalP (zachosBase ⋅ zachosTower n) = .p29 := by
  have hs_eq : zachosStepsRec n = jumpAheadZachosStep n := by
    unfold jumpAheadZachosStep
    rw [← two_mul_zachosStepsRec n]
    exact (Nat.mul_div_right _ (by decide : 0 < 2)).symm
  have hd_eq : zachosDepthRec n = n * (n + 1) / 2 := by
    rw [← two_mul_zachosDepthRec n]
    exact (Nat.mul_div_right _ (by decide : 0 < 2)).symm
  rw [← hs_eq, ← hd_eq]
  have hp_tower : ∀ m, evalP (zachosBase ⋅ zachosTower m) = .p29 := by
    intro m
    cases m with
    | zero => rfl
    | succ m0 =>
      have hp_t : ∀ r, evalP (zachosTower (r + 1)) = .p32 := by
        intro r
        induction r with
        | zero => rfl
        | succ _ ihr =>
          change IntrinsicTheorems.delta_StateP .p1 (evalP (zachosTower _)) = .p32
          rw [ihr]
          rfl
      change IntrinsicTheorems.delta_StateP (evalP zachosBase) (evalP (zachosTower (m0 + 1))) = .p29
      rw [hp_t m0]
      rfl
  clear hs_eq hd_eq
  refine (?_ : ∃ ctx, validLOContext ctx = true ∧ ctx.length = zachosDepthRec n ∧
      iterateLO (zachosStepsRec n) zachos = wrapLOContext ctx (zachosBase ⋅ zachosTower n)).elim
    (fun ctx ⟨h1, h2, h3⟩ => ⟨ctx, h1, h2, h3, hp_tower n⟩)
  induction n with
  | zero => exact ⟨[], rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨ctx, hvc, hlen, hreach⟩ := ih
    have hs0 : stepLO (zachosBase ⋅ zachosTower k) =
        some (zachosTower (k + 1) ⋅ zachosTower (k + 1)) := rfl
    have h1 : iterateLO 1 (wrapLOContext ctx (zachosBase ⋅ zachosTower k)) =
        wrapLOContext ctx (zachosTower (k + 1) ⋅ zachosTower (k + 1)) := by
      simp only [iterateLO, stepLO_wrapLOContext hvc hs0]
    obtain ⟨ctx', hvc', hlen', hcd⟩ :=
      zachos_countdown (k + 1) (zachosTower (k + 1)) (noVars_zachosTower _)
        (stepLO_zachosTower_none _) ctx hvc
    refine ⟨ctx', hvc', ?_, ?_⟩
    · rw [hlen', hlen]
      rfl
    · have hk2 : k + 2 = 1 + (k + 1) := Nat.add_comm (k + 1) 1
      simp only [zachosStepsRec]
      rw [iterateLO_add (zachosStepsRec k) (k + 2), hreach, hk2, iterateLO_add 1 (k + 1), h1, hcd]

/-- **Exact Separation Between `wolfram_2` and `zachos` (`A_P` State `.p37` vs `.p29`)**:
    1. `zachosPrecursor = S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)` reduces in 1 root step
       to `zachos = (S ⋅ (S ⋅ S) ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S))`, and both have
       `evalP = .p29 ≠ .p37` (globally Böhm-productive across all subtrees).
    2. `wolfram_2 = S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)` reduces in 1 head step to
       `(S ⋅ (S ⋅ (S ⋅ S))) ⋅ (S ⋅ (S ⋅ (S ⋅ S))) ⋅ (S ⋅ S)`, is **not** `$=_{S}$`-convertible
       to `zachos` (`¬ ConvS wolfram_2 zachos`), and has `evalP wolfram_2 = .p37`: its Böhm tree
       hits `⊥` (`evalHN = .hn34`, `¬ HasHNF`) at depth `5` along path `[1, 1, 1, 1, 0]` inside
       the right sibling permanently frozen by `stepLO` at step `7`! -/
theorem zachos_vs_wolfram2_separation :
    Step zachosPrecursor zachos ∧
    evalP zachosPrecursor = .p29 ∧
    evalP zachos = .p29 ∧
    evalP wolfram_2 = .p37 ∧
    ¬ ConvS wolfram_2 zachos ∧
    ∃ (l0 c0 l1 c1 l2 c2 l3 c3 c4 r4 : Term),
      HeadReduces wolfram_2 (S ⋅ l0 ⋅ c0) ∧
      HeadReduces c0 (S ⋅ l1 ⋅ c1) ∧
      HeadReduces c1 (S ⋅ l2 ⋅ c2) ∧
      HeadReduces c2 (S ⋅ l3 ⋅ c3) ∧
      HeadReduces c3 (S ⋅ c4 ⋅ r4) ∧
      noVars c4 = true ∧ evalHN c4 = .hn34 ∧ ¬ HasHNF c4 := by
  refine ⟨Step.root (S ⋅ (S ⋅ S)) (S ⋅ (S ⋅ S)) (S ⋅ S), rfl, rfl, rfl, ?_, ?_⟩
  · intro hconv
    have heq := evalP_conv hconv
    change IntrinsicTheorems.StateP.p37 = IntrinsicTheorems.StateP.p29 at heq
    cases heq
  · let t0 := iterateHead 4 wolfram_2
    let c0 := S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)))
    let l0 := S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))
    let c1 := S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))) ⋅
      (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅ (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)))))
    let l1 := S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅ (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))))
    let c2 := S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅
      (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅ (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)))))
    let l2 := S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅ (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))))
    let c3 := S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅
      (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅ (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)))))
    let l3 := S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅ (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))))
    let c4 := S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅
      (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)))) ⋅
      (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅
        (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))))))
    let r4 := S ⋅ S ⋅
      (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅
        (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))))) ⋅
      (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅
        (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)))) ⋅
        (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)) ⋅
          (S ⋅ S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S)))))))
    have hd0 : iterateHead 4 wolfram_2 = S ⋅ l0 ⋅ c0 := rfl
    have hd1 : iterateHead 3 c0 = S ⋅ l1 ⋅ c1 := rfl
    have hd2 : iterateHead 1 c1 = S ⋅ l2 ⋅ c2 := rfl
    have hd3 : iterateHead 1 c2 = S ⋅ l3 ⋅ c3 := rfl
    have hd4 : iterateHead 3 c3 = S ⋅ c4 ⋅ r4 := rfl
    have hvc4 : noVars c4 = true := rfl
    have h34c4 : evalHN c4 = .hn34 := rfl
    exact ⟨l0, c0, l1, c1, l2, c2, l3, c3, c4, r4,
      hd0 ▸ iterateHead_headReduces 4 wolfram_2,
      hd1 ▸ iterateHead_headReduces 3 c0,
      hd2 ▸ iterateHead_headReduces 1 c1,
      hd3 ▸ iterateHead_headReduces 1 c2,
      hd4 ▸ iterateHead_headReduces 3 c3,
      hvc4, h34c4,
      fun hh => ((barendregt_open_problem_10 hvc4).1.mp hh) h34c4⟩

/-! ## 5. Exact 14-Expression Algebraic & Dynamical Dichotomy Theorem -/

/-- Explicit frozen HNF contexts and `.hn34` focuses reached by the 6 `HN \ SN` benchmarks
    (`wolfram7_a`, `wolfram7_b`, `wolfram_1`, `wolfram_5`, `wolfram_8`, `wolfram_11`). -/
def ctx_wolfram7_a : List LOFrame :=
  [.s2R (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S))]
def foc_wolfram7_a : Term :=
  S ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S))

def ctx_wolfram7_b : List LOFrame :=
  [.s2R (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S))]
def foc_wolfram7_b : Term :=
  S ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ (S ⋅ S) ⋅ S) ⋅ S))

def ctx_wolfram_1 : List LOFrame :=
  [ .s2R (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)))))
  , .s2L (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)))) ⋅
      (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S))) ⋅
        (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)))))))
  , .s2L (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)))) ⋅
      (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)) ⋅
        (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)))))))
  , .s2L (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅
      (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S))))) ⋅
      (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)))) ⋅
        (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅
          (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)))))))) ]
def foc_wolfram_1 : Term :=
  S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S)))) ⋅
    (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅
      (S ⋅ (S ⋅ S) ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ (S ⋅ S))))))

def ctx_wolfram_5 : List LOFrame :=
  [.s2R (S ⋅ (S ⋅ (S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S) ⋅ S))) ⋅
    (S ⋅ (S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S) ⋅ S))) ⋅
      (S ⋅ (S ⋅ (S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S) ⋅ S)))) ⋅
        (S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S) ⋅ S)) ⋅ (S ⋅ (S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ S) ⋅ S)))))))))]
def foc_wolfram_5 : Term :=
  S ⋅ S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ S ⋅ (S ⋅ (S ⋅ S ⋅ S ⋅ S ⋅ (S ⋅ (S ⋅ S)) ⋅ S))

def ctx_wolfram_8 : List LOFrame :=
  [.s2L (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))) ⋅ (S ⋅ S) ⋅
    (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅ (S ⋅ S) ⋅
      (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))) ⋅ (S ⋅ S))))]
def foc_wolfram_8 : Term :=
  S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅ (S ⋅ S) ⋅
    (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S) ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S)) ⋅ (S ⋅ S))) ⋅ (S ⋅ S))

def ctx_wolfram_11 : List LOFrame :=
  [.s2R (S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S ⋅ S)))) ⋅ S)]
def foc_wolfram_11 : Term :=
  S ⋅ (S ⋅ (S ⋅ S ⋅ S)) ⋅ S ⋅ (S ⋅ (S ⋅ S ⋅ (S ⋅ (S ⋅ (S ⋅ S ⋅ S)))) ⋅ S)

/-- Unified predicate for a closed non-halting pure-`S` term that freezes `d` HNF frames at
    step `t₀` and then executes pure-head divergence inside a permanent `.hn34` focus forever. -/
def LocksIntoPureHeadAt (w : Term) (t0 d : Nat) (ctx : List LOFrame) (foc : Term) : Prop :=
  noVars w = true ∧
  evalSN w = .sn38 ∧
  ¬ StrongNormalizing w ∧
  evalP w = .p37 ∧
  ctx.length = d ∧
  validLOContext ctx = true ∧
  noVars foc = true ∧
  evalHN foc = .hn34 ∧
  iterateLO t0 w = wrapLOContext ctx foc ∧
  ∀ k : Nat,
    iterateLO (t0 + k) w = wrapLOContext ctx (iterateLO k foc) ∧
    HeadStepsN k foc (iterateLO k foc)

private theorem mk_locksIntoPureHeadAt {w : Term} {t0 d : Nat} {ctx : List LOFrame} {foc : Term}
    (hvw : noVars w = true) (hsn : evalSN w = .sn38) (hp : evalP w = .p37)
    (hlen : ctx.length = d) (hvc : validLOContext ctx = true)
    (hvf : noVars foc = true) (h34 : evalHN foc = .hn34)
    (hit : iterateLO t0 w = wrapLOContext ctx foc) :
    LocksIntoPureHeadAt w t0 d ctx foc := by
  refine ⟨hvw, hsn, fun h => ((waldmann_theorem_9 hvw).1.mp h) hsn,
    hp, hlen, hvc, hvf, h34, hit, ?_⟩
  intro k
  obtain ⟨heq, _, _, _, hhsk, _⟩ := locked_hn34_forever hvc hvf h34 k
  rw [iterateLO_add t0 k, hit]
  exact ⟨heq, hhsk⟩

private theorem mk_immediate_hn34 {w : Term}
    (hvw : noVars w = true) (hsn : evalSN w = .sn38)
    (h34 : evalHN w = .hn34) (hp : evalP w = .p37) :
    evalHN w = .hn34 ∧ ¬ HasHNF w ∧ LocksIntoPureHeadAt w 0 0 [] w :=
  ⟨h34, fun hh => ((barendregt_open_problem_10 hvw).1.mp hh) h34,
    mk_locksIntoPureHeadAt hvw hsn hp rfl rfl hvw h34 rfl⟩

/-- **Exact 14-Expression Algebraic & Dynamical Dichotomy Theorem**:
    1. **7 Immediate Head-Divergent Benchmarks (`wolfram_3, 4, 6, 7, 9, 10, 12`)**:
       `evalHN = .hn34`, `¬ HasHNF`, `0` HNF freezes (`ctx = []`), pure head steps forever.
    2. **6 Freezing `HN \ SN` Benchmarks (`wolfram7_a, wolfram7_b, wolfram_1, 5, 8, 11`)**:
       `evalHN ≠ .hn34` (`HasHNF`), `evalP = .p37`, reaching an explicit valid frozen HNF
       context of depth `1 ≤ d ≤ 4` (`d = 4` on `wolfram_1`, `d = 1` on the other 5) around
       a permanent `.hn34` focus in `t₀ ≤ 21` steps (`8, 9, 18, 21, 8, 4`).
    3. **Unique Perpetual `HN \ SN` `stepLO` Benchmark (`wolfram_2`) vs `zachos`**:
       `wolfram_2` is closed, non-halting (`evalSN = .sn38`), head-normalizing (`evalHN = .hn24`),
       and **uniquely** never hits an `.hn34` focus at any `stepLO` step `t : Nat`
       (following `wolfram2_closed_form_jump_ahead`), while `zachosPrecursor →^1 zachos`
       uniquely achieves global Böhm productivity (`evalP = .p29 ≠ .p37`). -/
theorem wolfram_14_dichotomy_master :
    -- Part I: 7 immediately head-divergent benchmarks (0 HNF freezes)
    ((evalHN wolfram_3 = .hn34 ∧ ¬ HasHNF wolfram_3 ∧ LocksIntoPureHeadAt wolfram_3 0 0 [] wolfram_3) ∧
     (evalHN wolfram_4 = .hn34 ∧ ¬ HasHNF wolfram_4 ∧ LocksIntoPureHeadAt wolfram_4 0 0 [] wolfram_4) ∧
     (evalHN wolfram_6 = .hn34 ∧ ¬ HasHNF wolfram_6 ∧ LocksIntoPureHeadAt wolfram_6 0 0 [] wolfram_6) ∧
     (evalHN wolfram_7 = .hn34 ∧ ¬ HasHNF wolfram_7 ∧ LocksIntoPureHeadAt wolfram_7 0 0 [] wolfram_7) ∧
     (evalHN wolfram_9 = .hn34 ∧ ¬ HasHNF wolfram_9 ∧ LocksIntoPureHeadAt wolfram_9 0 0 [] wolfram_9) ∧
     (evalHN wolfram_10 = .hn34 ∧ ¬ HasHNF wolfram_10 ∧ LocksIntoPureHeadAt wolfram_10 0 0 [] wolfram_10) ∧
     (evalHN wolfram_12 = .hn34 ∧ ¬ HasHNF wolfram_12 ∧ LocksIntoPureHeadAt wolfram_12 0 0 [] wolfram_12)) ∧
    -- Part II: 6 freezing HN \ SN benchmarks (1..4 HNF freezes, then permanent .hn34 focus)
    ((evalHN wolfram7_a = .hn23 ∧ HasHNF wolfram7_a ∧ LocksIntoPureHeadAt wolfram7_a 8 1 ctx_wolfram7_a foc_wolfram7_a) ∧
     (evalHN wolfram7_b = .hn23 ∧ HasHNF wolfram7_b ∧ LocksIntoPureHeadAt wolfram7_b 9 1 ctx_wolfram7_b foc_wolfram7_b) ∧
     (evalHN wolfram_1 = .hn23 ∧ HasHNF wolfram_1 ∧ LocksIntoPureHeadAt wolfram_1 18 4 ctx_wolfram_1 foc_wolfram_1) ∧
     (evalHN wolfram_5 = .hn23 ∧ HasHNF wolfram_5 ∧ LocksIntoPureHeadAt wolfram_5 21 1 ctx_wolfram_5 foc_wolfram_5) ∧
     (evalHN wolfram_8 = .hn23 ∧ HasHNF wolfram_8 ∧ LocksIntoPureHeadAt wolfram_8 8 1 ctx_wolfram_8 foc_wolfram_8) ∧
     (evalHN wolfram_11 = .hn25 ∧ HasHNF wolfram_11 ∧ LocksIntoPureHeadAt wolfram_11 4 1 ctx_wolfram_11 foc_wolfram_11)) ∧
    -- Part III: Unique perpetual HN \ SN normal-order trajectory of wolfram_2 + Zachos separation
    (noVars wolfram_2 = true ∧
     evalSN wolfram_2 = .sn38 ∧
     ¬ StrongNormalizing wolfram_2 ∧
     evalHN wolfram_2 = .hn24 ∧
     HasHNF wolfram_2 ∧
     (∀ t : Nat, ∀ ctx foc,
       validLOContext ctx = true → noVars foc = true → 3 ≤ spineLen foc →
       iterateLO t wolfram_2 = wrapLOContext ctx foc → evalHN foc ≠ .hn34) ∧
     Step zachosPrecursor zachos ∧
     evalP zachos = .p29 ∧
     evalP wolfram_2 = .p37 ∧
     ¬ ConvS wolfram_2 zachos) := by
  have hhnf : ∀ {w : Term}, noVars w = true → evalHN w ≠ .hn34 → HasHNF w :=
    fun hv hne => (barendregt_open_problem_10 hv).1.mpr hne
  refine ⟨⟨mk_immediate_hn34 rfl rfl rfl rfl,
           mk_immediate_hn34 rfl rfl rfl rfl,
           mk_immediate_hn34 rfl rfl rfl rfl,
           mk_immediate_hn34 rfl rfl rfl rfl,
           mk_immediate_hn34 rfl rfl rfl rfl,
           mk_immediate_hn34 rfl rfl rfl rfl,
           mk_immediate_hn34 rfl rfl rfl rfl⟩,
          ⟨⟨rfl, hhnf rfl (fun h => by cases h), mk_locksIntoPureHeadAt rfl rfl rfl rfl rfl rfl rfl rfl⟩,
           ⟨rfl, hhnf rfl (fun h => by cases h), mk_locksIntoPureHeadAt rfl rfl rfl rfl rfl rfl rfl rfl⟩,
           ⟨rfl, hhnf rfl (fun h => by cases h), mk_locksIntoPureHeadAt rfl rfl rfl rfl rfl rfl rfl rfl⟩,
           ⟨rfl, hhnf rfl (fun h => by cases h), mk_locksIntoPureHeadAt rfl rfl rfl rfl rfl rfl rfl rfl⟩,
           ⟨rfl, hhnf rfl (fun h => by cases h), mk_locksIntoPureHeadAt rfl rfl rfl rfl rfl rfl rfl rfl⟩,
           ⟨rfl, hhnf rfl (fun h => by cases h), mk_locksIntoPureHeadAt rfl rfl rfl rfl rfl rfl rfl rfl⟩⟩,
          ⟨rfl, rfl,
           fun h => ((waldmann_theorem_9 (t := wolfram_2) rfl).1.mp h) rfl,
           rfl,
           hhnf rfl (fun h => by cases h),
           fun t => (wolfram2_perpetual_hn_minus_sn t).2,
           Step.root (S ⋅ (S ⋅ S)) (S ⋅ (S ⋅ S)) (S ⋅ S),
           rfl, rfl, zachos_vs_wolfram2_separation.2.2.2.2.1⟩⟩

/-! ## 6. Explicit "Jump-Ahead" Closed-Form Predictability Theorems (Wolfram Line 179) -/

/-! ### 6.1 $O(|t|)$ Eventual Halting & Head-Halting Jump-Ahead Decision Procedures -/

/-- Total $O(|t|)$ decision function determining whether `t` halts under `stepLO` (and under all
    reduction orders) without simulating a single rewrite step. -/
def decideHaltsLO (t : Term) : Bool :=
  evalSN t != .sn38

/-- Total $O(|t|)$ decision function determining whether `t` reaches a Head Normal Form under
    `headStepOpt` without simulating a single rewrite step. -/
def decideHaltsHead (t : Term) : Bool :=
  evalHN t != .hn34

theorem reduces_iterateLO (k : Nat) (t : Term) : Reduces t (iterateLO k t) := by
  induction k generalizing t with
  | zero => exact Reduces.refl t
  | succ k ih =>
    simp only [iterateLO]
    cases hs : stepLO t with
    | none => exact Reduces.refl t
    | some t' => exact Reduces.next (stepLO_some_step hs) (ih t')

theorem sn_imp_iterateLO_halts {t : Term} (hsn : StrongNormalizing t) :
    ∃ k : Nat, stepLO (iterateLO k t) = none := by
  induction hsn with
  | intro t _ ih =>
    cases hs : stepLO t with
    | none => exact ⟨0, hs⟩
    | some t' =>
      obtain ⟨k, hk⟩ := ih t' (stepLO_some_step hs)
      refine ⟨k + 1, ?_⟩
      simp only [iterateLO, hs, hk]

theorem iterateLO_halts_imp_sn {t : Term} (h : ∃ k : Nat, stepLO (iterateLO k t) = none) :
    StrongNormalizing t := by
  obtain ⟨k, hk⟩ := h
  exact wn_implies_sn ⟨iterateLO k t, reduces_iterateLO k t, stepLO_none_isNormalForm hk⟩

/-- **Jump-Ahead Halting Predictability Theorem (`decideHaltsLO`)**:
    For every closed pure-`S` term `t`, `decideHaltsLO t` always terminates in `leaves t - 1`
    table lookups ($O(|t|)$ time) and exactly determines whether `iterateLO` ever halts! -/
theorem decideHaltsLO_iff_halts {t : Term} (hv : noVars t = true) :
    (decideHaltsLO t = true ↔ StrongNormalizing t) ∧
    (decideHaltsLO t = true ↔ HasNormalForm t) ∧
    (decideHaltsLO t = true ↔ ∃ k : Nat, stepLO (iterateLO k t) = none) ∧
    (decideHaltsLO t = false ↔ ∀ k : Nat, (stepLO (iterateLO k t)).isSome = true) := by
  have h1 : decideHaltsLO t = true ↔ evalSN t ≠ .sn38 := by
    unfold decideHaltsLO
    simp only [bne_iff_ne]
  have ⟨hsn_iff, hwn_iff⟩ := waldmann_theorem_9 hv
  have hlo_iff : StrongNormalizing t ↔ ∃ k : Nat, stepLO (iterateLO k t) = none :=
    ⟨sn_imp_iterateLO_halts, iterateLO_halts_imp_sn⟩
  have hfull : decideHaltsLO t = true ↔ ∃ k : Nat, stepLO (iterateLO k t) = none :=
    (h1.trans hsn_iff.symm).trans hlo_iff
  refine ⟨h1.trans hsn_iff.symm, h1.trans hwn_iff.symm, hfull, ?_⟩
  constructor
  · intro hfalse k
    cases hs : stepLO (iterateLO k t) with
    | some _ => rfl
    | none =>
      have htrue : decideHaltsLO t = true := hfull.mpr ⟨k, hs⟩
      rw [htrue] at hfalse
      cases hfalse
  · intro hall
    cases hd : decideHaltsLO t with
    | false => rfl
    | true =>
      obtain ⟨k, hk⟩ := hfull.mp hd
      have hsome := hall k
      rw [hk] at hsome
      cases hsome

/-- **Jump-Ahead Head-Termination Predictability Theorem (`decideHaltsHead`)**:
    For every closed pure-`S` term `t`, `decideHaltsHead t` always terminates in `leaves t - 1`
    table lookups ($O(|t|)$ time) and exactly determines whether `iterateHead` reaches a Head
    Normal Form (with explicit upper bound `muHN t + 1` steps when `true`, and infinite head
    reduction when `false`). -/
theorem decideHaltsHead_iff_halts {t : Term} (hv : noVars t = true) :
    (decideHaltsHead t = true ↔ HasHNF t) ∧
    (decideHaltsHead t = true ↔ ∃ k : Nat, headStepOpt (iterateHead k t) = none) ∧
    (decideHaltsHead t = false ↔ ∀ k : Nat, (headStepOpt (iterateHead k t)).isSome = true) := by
  have h1 : decideHaltsHead t = true ↔ evalHN t ≠ .hn34 := by
    unfold decideHaltsHead
    simp only [bne_iff_ne]
  have ⟨hhnf_iff, hinf_iff⟩ := barendregt_open_problem_10 hv
  have hiter_eq : ∀ (n : Nat) (u : Term), iterateHead n u = headNormalizeAux n u := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro u
      simp only [iterateHead, headNormalizeAux]
      cases headStepOpt u with
      | none => rfl
      | some u' => exact ih u'
  have hhead_halts : evalHN t ≠ .hn34 ↔ ∃ k : Nat, headStepOpt (iterateHead k t) = none := by
    constructor
    · intro hne
      obtain ⟨hred, hvw, hsl⟩ := headNormalize_reduces_hnf hv hne
      refine ⟨muHN t + 1, ?_⟩
      rw [hiter_eq]
      change headStepOpt (headNormalize t) = none
      cases hh : headStepOpt (headNormalize t) with
      | none => rfl
      | some w =>
        have hs := headStepOpt_some hh
        -- Closed HNF has spineLen ≤ 2, which cannot take a HeadStep!
        have hno_hs : ∀ {a b : Term}, HeadStep a b → ¬ spineLen a ≤ 2 := by
          intro a b hstep
          induction hstep with
          | root x y z =>
            intro hbad
            exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hbad))
          | @left l l' r _ ih =>
            intro hbad
            exact ih (Nat.le_trans (Nat.le_add_left (spineLen l) 1) hbad)
        exact False.elim (hno_hs hs hsl)
    · intro ⟨k, hk⟩
      have hred := headReduces_to_reduces (iterateHead_headReduces k t)
      have hvk := noVars_reduces hred hv
      exact hhnf_iff.mp ⟨iterateHead k t, hred, headStepOpt_none_spineLen hvk hk⟩
  refine ⟨h1.trans hhnf_iff.symm, h1.trans hhead_halts, ?_⟩
  constructor
  · intro hfalse k
    cases hh : headStepOpt (iterateHead k t) with
    | some _ => rfl
    | none =>
      have htrue : decideHaltsHead t = true := (h1.trans hhead_halts).mpr ⟨k, hh⟩
      rw [htrue] at hfalse
      cases hfalse
  · intro hall
    cases hd : decideHaltsHead t with
    | false => rfl
    | true =>
      obtain ⟨k, hk⟩ := (h1.trans hhead_halts).mp hd
      have hsome := hall k
      rw [hk] at hsome
      cases hsome

/-! ### 6.2 $O(|C| + \sum |t_i|)$ Multi-Hole Context Compositional Jump-Ahead -/

/-- Multi-hole pure-`S` context `C[□_0, ..., □_{k-1}]`. -/
inductive SContext where
  | s : SContext
  | hole : Nat → SContext
  | app : SContext → SContext → SContext
  deriving DecidableEq, Repr

def SContext.size : SContext → Nat
  | .s => 1
  | .hole _ => 1
  | .app a b => SContext.size a + SContext.size b

def listGetD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, i + 1, d => listGetD xs i d

theorem listGetD_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) (d : α) :
    listGetD (xs.map f) i (f d) = f (listGetD xs i d) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem listGetD_prop {α : Type} {p : α → Bool} {xs : List α}
    (hall : xs.all p = true) (i : Nat) {d : α} (hd : p d = true) :
    p (listGetD xs i d) = true := by
  induction xs generalizing i with
  | nil => exact hd
  | cons x xs ih =>
    simp only [List.all, Bool.and_eq_true] at hall
    cases i with
    | zero => exact hall.1
    | succ i => exact ih hall.2 i

/-- Plug closed terms `args = [t_0, ..., t_{k-1}]` into `C` (defaulting unused indices to `S`). -/
def plugContext : SContext → List Term → Term
  | .s, _ => S
  | .hole i, args => listGetD args i S
  | .app a b, args => plugContext a args ⋅ plugContext b args

theorem noVars_plugContext (C : SContext) {args : List Term} (hargs : args.all noVars = true) :
    noVars (plugContext C args) = true := by
  induction C with
  | s => rfl
  | hole i => exact listGetD_prop hargs i rfl
  | app _ _ iha ihb => exact (Bool.and_eq_true _ _).mpr ⟨iha, ihb⟩

/-- Evaluate `A_SN` on a context from precomputed hole states in $O(|C|)$ table lookups. -/
def evalContextSN : SContext → List StateSN → StateSN
  | .s, _ => .sn0
  | .hole i, st => listGetD st i .sn0
  | .app a b, st => deltaSN (evalContextSN a st) (evalContextSN b st)

/-- Evaluate `A_HN` on a context from precomputed hole states in $O(|C|)$ table lookups. -/
def evalContextHN : SContext → List StateHN → StateHN
  | .s, _ => .hn0
  | .hole i, st => listGetD st i .hn0
  | .app a b, st => deltaHN (evalContextHN a st) (evalContextHN b st)

/-- Evaluate `A_P` on a context from precomputed hole states in $O(|C|)$ table lookups. -/
def evalContextP : SContext → List IntrinsicTheorems.StateP → IntrinsicTheorems.StateP
  | .s, _ => .p0
  | .hole i, st => listGetD st i .p0
  | .app a b, st => IntrinsicTheorems.delta_StateP (evalContextP a st) (evalContextP b st)

/-- **$O(|C| + \sum |t_i|)$ Context Halting Decision Function**:
    Evaluates each `t_i ∈ args` **once** ($O(\sum |t_i|)$) and traverses `C` **once** ($O(|C|)$),
    even when `C` duplicates holes exponentially, without constructing `plugContext C args`
    or simulating a single reduction step! -/
def decideContextHaltsLO (C : SContext) (args : List Term) : Bool :=
  evalContextSN C (args.map evalSN) != .sn38

def decideContextHaltsHead (C : SContext) (args : List Term) : Bool :=
  evalContextHN C (args.map evalHN) != .hn34

theorem evalContext_homomorphism (C : SContext) (args : List Term) :
    evalSN (plugContext C args) = evalContextSN C (args.map evalSN) ∧
    evalHN (plugContext C args) = evalContextHN C (args.map evalHN) ∧
    evalP (plugContext C args) = evalContextP C (args.map evalP) := by
  induction C with
  | s => exact ⟨rfl, rfl, rfl⟩
  | hole i =>
    exact ⟨(listGetD_map evalSN args i S).symm,
           (listGetD_map evalHN args i S).symm,
           (listGetD_map evalP args i S).symm⟩
  | app a b iha ihb =>
    exact ⟨by simp only [plugContext, evalSN, evalContextSN, iha.1, ihb.1],
           by simp only [plugContext, evalHN, evalContextHN, iha.2.1, ihb.2.1],
           by simp only [plugContext, evalP_app, evalContextP, iha.2.2, ihb.2.2]⟩

/-- **Compositional Context Jump-Ahead Theorem (`decideContextHaltsLO` & `decideContextHaltsHead`)**:
    Determines whether `C[t_1, ..., t_k]` halts (and whether it head-halts) in
    $O(|C| + \sum |t_i|)$ time without building `C[t_1, ..., t_k]` or running `stepLO`. -/
theorem decideContextHalts_exact (C : SContext) {args : List Term}
    (hargs : args.all noVars = true) :
    (decideContextHaltsLO C args = decideHaltsLO (plugContext C args)) ∧
    (decideContextHaltsLO C args = true ↔ StrongNormalizing (plugContext C args)) ∧
    (decideContextHaltsLO C args = true ↔ ∃ m, stepLO (iterateLO m (plugContext C args)) = none) ∧
    (decideContextHaltsHead C args = decideHaltsHead (plugContext C args)) ∧
    (decideContextHaltsHead C args = true ↔ HasHNF (plugContext C args)) := by
  have hhom := evalContext_homomorphism C args
  have hv := noVars_plugContext C hargs
  have heq_lo : decideContextHaltsLO C args = decideHaltsLO (plugContext C args) := by
    unfold decideContextHaltsLO decideHaltsLO
    rw [hhom.1]
  have heq_hd : decideContextHaltsHead C args = decideHaltsHead (plugContext C args) := by
    unfold decideContextHaltsHead decideHaltsHead
    rw [hhom.2.1]
  have hlo := decideHaltsLO_iff_halts hv
  have hhd := decideHaltsHead_iff_halts hv
  exact ⟨heq_lo, heq_lo ▸ hlo.1, heq_lo ▸ hlo.2.2.1, heq_hd, heq_hd ▸ hhd.1⟩

/-! ### 6.3 $O(1)$-Arithmetic Jump-Ahead for the 10-Leaf Quadratic Counter Seed -/

/-- Exact $O(1)$-arithmetic step formula `2 * n^2 - n + 1` for the 10-leaf two-counter seed. -/
def jumpAheadCounterStep (n : Nat) : Nat :=
  2 * n ^ 2 - n + 1

private theorem pow2_eq_mul (n : Nat) : 2 * n ^ 2 = 2 * n * n := by
  have hp : n ^ 2 = n * n := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [hp, Nat.mul_assoc 2 n n]

private theorem counterD_partial_countdown :
    ∀ (r m p : Nat), r ≤ m →
      ∀ (ctx : List Term),
        ∃ ctx' : List Term,
          ctx'.length = ctx.length + r ∧
          iterateLO (4 * r) (wrapLeftHNF ctx (counterD m (p + 1))) =
            wrapLeftHNF ctx' (counterD (m - r) (p + 1))
  | 0, m, _, _, ctx => by
    refine ⟨ctx, (Nat.add_zero _).symm, ?_⟩
    rw [Nat.mul_zero, Nat.sub_zero]
    rfl
  | r + 1, 0, _, hr, _ => by cases hr
  | r + 1, m + 1, p, hr, ctx => by
    let u0 := counterD (m + 1) (p + 1)
    let u1 := ((S ⋅ numeralC (p + 1)) ⋅ (numeralC m ⋅ numeralC (p + 1))) ⋅ S
    let u2 := (numeralC (p + 1) ⋅ S) ⋅ counterD m (p + 1)
    let u3 := (S ⋅ S ⋅ (numeralC p ⋅ S)) ⋅ counterD m (p + 1)
    let rFrozen := (numeralC p ⋅ S) ⋅ counterD m (p + 1)
    let u4 := S ⋅ counterD m (p + 1) ⋅ rFrozen
    have hs0 : stepLO u0 = some u1 := rfl
    have hs1 : stepLO u1 = some u2 := rfl
    have hs2 : stepLO u2 = some u3 := rfl
    have hs3 : stepLO u3 = some u4 := rfl
    have happ : ∀ (c : List Term) (foc rf : Term),
        wrapLeftHNF (c ++ [rf]) foc = wrapLeftHNF c (S ⋅ foc ⋅ rf) := by
      intro c foc rf
      induction c with
      | nil => rfl
      | cons x xs ih => simp only [List.cons_append, wrapLeftHNF, ih]
    have h4 : iterateLO 4 (wrapLeftHNF ctx u0) =
        wrapLeftHNF (ctx ++ [rFrozen]) (counterD m (p + 1)) := by
      rw [happ]
      simp only [iterateLO,
        stepLO_wrapLeftHNF ctx hs0,
        stepLO_wrapLeftHNF ctx hs1,
        stepLO_wrapLeftHNF ctx hs2,
        stepLO_wrapLeftHNF ctx hs3]
      rfl
    obtain ⟨ctx', hlen', hrest⟩ :=
      counterD_partial_countdown r m p (Nat.le_of_succ_le_succ hr) (ctx ++ [rFrozen])
    refine ⟨ctx', ?_, ?_⟩
    · rw [hlen', List.length_append, List.length, List.length, Nat.add_assoc, Nat.add_comm 1 r]
    · have h4r : 4 * (r + 1) = 4 + 4 * r := by
        rw [Nat.mul_add 4 r 1, Nat.mul_one, Nat.add_comm (4 * r) 4]
      rw [h4r, iterateLO_add 4 (4 * r), h4, hrest, Nat.succ_sub_succ_eq_sub]

/-- **Two-Parameter $O(1)$-Arithmetic Jump-Ahead Theorem for `tenLeafSeed`**:
    For every `n ≥ 1` and every intra-cycle offset `r ≤ n`, `tenLeafSeed` at step
    `jumpAheadCounterStep n + 4 * r` (`(2 * n^2 - n + 1) + 4 * r`) has exact active focus
    `counterD (n - r) n` wrapped inside `n * (n - 1) / 2 + r` frozen left-active 2-HNFs!
    In particular:
    - `r = 0`: `iterateLO (2 * n^2 - n + 1) tenLeafSeed = wrapLeftHNF ctx (counterD n n)`
    - `r = n`: `iterateLO (2 * n^2 + 3 * n + 1) tenLeafSeed = wrapLeftHNF ctx' (counterD 0 n)`. -/
theorem jump_ahead_tenLeafSeed_two_param (n r : Nat) (hn : 1 ≤ n) (hr : r ≤ n) :
    (∃ ctx0 : List Term,
      ctx0.length = n * (n - 1) / 2 ∧
      iterateLO (jumpAheadCounterStep n) tenLeafSeed = wrapLeftHNF ctx0 (counterD n n)) ∧
    (∃ ctx : List Term,
      ctx.length = n * (n - 1) / 2 + r ∧
      iterateLO (jumpAheadCounterStep n + 4 * r) tenLeafSeed =
        wrapLeftHNF ctx (counterD (n - r) n)) := by
  have hbase : ∃ ctx0 : List Term,
      ctx0.length = n * (n - 1) / 2 ∧
      iterateLO (jumpAheadCounterStep n) tenLeafSeed = wrapLeftHNF ctx0 (counterD n n) := by
    unfold jumpAheadCounterStep
    rw [pow2_eq_mul n]
    exact stepLO_quadratic_two_counter_pos n hn
  refine ⟨hbase, ?_⟩
  obtain ⟨ctx0, hlen0, hreach0⟩ := hbase
  cases n with
  | zero => cases hn
  | succ p =>
    obtain ⟨ctx, hlen, hcd⟩ := counterD_partial_countdown r (p + 1) p hr ctx0
    refine ⟨ctx, ?_, ?_⟩
    · rw [hlen, hlen0]
    · rw [iterateLO_add (jumpAheadCounterStep (p + 1)) (4 * r), hreach0, hcd]

/-! ### 6.4 Closed-Form Normal-Form Jump-Ahead on `rightTower` and `sPrefix` (`S S S ...`) -/

theorem stepLO_rightTower_none (m : Nat) : stepLO (rightTower m) = none := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [rightTower, stepLO, rootRedexOpt, S, ih]

theorem jump_ahead_rightTower (m k : Nat) :
    IsNormalForm (rightTower m) ∧ iterateLO k (rightTower m) = rightTower m := by
  refine ⟨stepLO_none_isNormalForm (stepLO_rightTower_none m), ?_⟩
  induction k with
  | zero => rfl
  | succ _ _ =>
    simp only [iterateLO, stepLO_rightTower_none m]

/-- Left-associative pure-`S` prefix `sPrefix m = S ⋅ S ⋅ ... ⋅ S` (`m + 1` leaves). -/
def sPrefix : Nat → Term
  | 0 => S
  | m + 1 => sPrefix m ⋅ S

/-- Exact closed-form Normal Form `sPrefixNF m` of `sPrefix m` (a right-tower of `S ⋅ S`!). -/
def sPrefixNF : Nat → Term
  | 0 => S
  | 1 => S ⋅ S
  | 2 => S ⋅ S ⋅ S
  | m + 3 => B_comb ⋅ sPrefixNF (m + 1)

theorem stepLO_sPrefixNF_none : ∀ (m : Nat), stepLO (sPrefixNF m) = none
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | m + 3 => by
    have ih := stepLO_sPrefixNF_none (m + 1)
    simp only [sPrefixNF, B_comb, stepLO, rootRedexOpt, S, ih]

private theorem sPrefix_peel :
    ∀ (d : Nat),
      iterateLO (d + 1) (sPrefix (d + 3)) = B_comb ⋅ sPrefix (d + 1) ∧
      (∀ j, j < d + 1 →
        noVars (iterateLO j (sPrefix (d + 3))) = true ∧
        3 ≤ spineLen (iterateLO j (sPrefix (d + 3))))
  | 0 => by
    refine ⟨rfl, ?_⟩
    intro j hj
    cases j with
    | zero => exact ⟨rfl, Nat.le_refl 3⟩
    | succ j0 => cases Nat.lt_of_succ_lt_succ hj
  | d + 1 => by
    obtain ⟨hpeel, hmid⟩ := sPrefix_peel d
    -- First show for `0 ≤ j ≤ d + 1`, `iterateLO j (sPrefix (d + 3) ⋅ S) = iterateLO j (sPrefix (d + 3)) ⋅ S`
    have hlift : ∀ j, j ≤ d + 1 →
        iterateLO j (sPrefix (d + 3) ⋅ S) = iterateLO j (sPrefix (d + 3)) ⋅ S := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
        have hj_lt : j < d + 1 := hj
        have ⟨hvj, hslj⟩ := hmid j hj_lt
        obtain ⟨u', hhu'⟩ := closed_spineLen_ge_3_has_headStep hvj hslj
        have hloj := headStepOpt_some_imp_stepLO hhu'
        have hr_none : rootRedexOpt (iterateLO j (sPrefix (d + 3))) S = none := by
          cases hr : rootRedexOpt (iterateLO j (sPrefix (d + 3))) S with
          | none => rfl
          | some r =>
            obtain ⟨x, y, heq, _⟩ := rootRedexOpt_some hr
            rw [heq] at hslj
            exact False.elim (Nat.not_succ_le_zero 0
              (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hslj)))
        have hstep_app : stepLO (iterateLO j (sPrefix (d + 3)) ⋅ S) = some (u' ⋅ S) := by
          simp only [stepLO, hr_none, hloj]
        rw [iterateLO_add j 1 (sPrefix (d + 3) ⋅ S),
            iterateLO_add j 1 (sPrefix (d + 3)), ih (Nat.le_of_lt hj_lt)]
        simp only [iterateLO, hstep_app, hloj]
    have hd1 := hlift (d + 1) (Nat.le_refl _)
    rw [hpeel] at hd1
    have hlast : iterateLO 1 ((B_comb ⋅ sPrefix (d + 1)) ⋅ S) = B_comb ⋅ sPrefix (d + 2) := rfl
    refine ⟨?_, ?_⟩
    · have hd2 : d + 2 = (d + 1) + 1 := rfl
      change iterateLO ((d + 1) + 1) (sPrefix (d + 3) ⋅ S) = B_comb ⋅ sPrefix (d + 2)
      rw [iterateLO_add (d + 1) 1, hd1, hlast]
    · intro j hj
      change noVars (iterateLO j (sPrefix (d + 3) ⋅ S)) = true ∧
        3 ≤ spineLen (iterateLO j (sPrefix (d + 3) ⋅ S))
      if hlt : j < d + 1 then
        rw [hlift j (Nat.le_of_lt hlt)]
        have ⟨hvj, hslj⟩ := hmid j hlt
        exact ⟨(Bool.and_eq_true _ _).mpr ⟨hvj, rfl⟩,
          Nat.le_trans hslj (Nat.le_add_left _ 1)⟩
      else
        have heq_j : j = d + 1 := Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.not_lt.mp hlt)
        rw [heq_j, hd1]
        have hv_sub : noVars (sPrefix (d + 1)) = true := by
          clear hpeel hmid hlift hd1 hlast hj hlt heq_j
          induction d with
          | zero => rfl
          | succ _ ihd => exact (Bool.and_eq_true _ _).mpr ⟨ihd, rfl⟩
        exact ⟨(Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨rfl, hv_sub⟩, rfl⟩,
          Nat.le_refl 3⟩

private def sPrefixStepsRec : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | d + 3 => (d + 1) + sPrefixStepsRec (d + 1)

/-- Exact closed-form halting time `((m - 1) / 2) * (m / 2)` ($0, 0, 0, 1, 2, 4, 6, 9, 12, 16, \dots$)
    for the left-associative pure-`S` spine `sPrefix m`. -/
def sPrefixSteps (m : Nat) : Nat :=
  ((m - 1) / 2) * (m / 2)

private theorem add_two_div_two (x : Nat) : (x + 2) / 2 = x / 2 + 1 :=
  Nat.add_div_right x (by decide : 0 < 2)

private theorem sPrefixStepsRec_eq : ∀ (m : Nat), sPrefixStepsRec m = sPrefixSteps m
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | d + 4 => by
    have ih := sPrefixStepsRec_eq (d + 2)
    simp only [sPrefixStepsRec]
    rw [ih]
    unfold sPrefixSteps
    have hsub1 : d + 4 - 1 = (d + 1) + 2 := rfl
    have hsub2 : d + 2 - 1 = d + 1 := rfl
    have hadd4 : d + 4 = (d + 2) + 2 := rfl
    rw [hsub1, hsub2, hadd4, add_two_div_two (d + 1), add_two_div_two (d + 2)]
    -- Prove `(d + 2) + ((d + 1) / 2) * ((d + 2) / 2) = ((d + 1) / 2 + 1) * ((d + 2) / 2 + 1)`
    -- Expand RHS: `q1 * q2 + q1 + q2 + 1`, so need `(d + 1) / 2 + (d + 2) / 2 + 1 = d + 2`,
    -- i.e. `(d + 1) / 2 + (d + 2) / 2 = d + 1`!
    have hhalf_sum : ∀ x : Nat, x / 2 + (x + 1) / 2 = x := by
      intro x
      induction x with
      | zero => rfl
      | succ x ihx =>
        have hx2 : (x + 1) + 1 = x + 2 := rfl
        rw [hx2, add_two_div_two x, ← Nat.add_assoc ((x + 1) / 2) (x / 2) 1,
            Nat.add_comm ((x + 1) / 2) (x / 2), ihx]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    have hsum_d : (d + 1) / 2 + (d + 2) / 2 = d + 1 := hhalf_sum (d + 1)
    have hrhs :
        (d + 1) / 2 * ((d + 2) / 2) + (d + 2) / 2 + ((d + 1) / 2 + 1) =
        ((d + 1) / 2 + (d + 2) / 2 + 1) + (d + 1) / 2 * ((d + 2) / 2) := by
      simp only [Nat.add_assoc, Nat.add_comm]
    rw [hrhs, hsum_d]

private theorem sPrefix_exact_rec :
    ∀ (m : Nat),
      iterateLO (sPrefixStepsRec m) (sPrefix m) = sPrefixNF m ∧
      (∀ j, j < sPrefixStepsRec m → (stepLO (iterateLO j (sPrefix m))).isSome = true)
  | 0 => ⟨rfl, fun _ h => by cases h⟩
  | 1 => ⟨rfl, fun _ h => by cases h⟩
  | 2 => ⟨rfl, fun _ h => by cases h⟩
  | d + 3 => by
    obtain ⟨hpeel, hmid⟩ := sPrefix_peel d
    obtain ⟨hih_nf, hih_some⟩ := sPrefix_exact_rec (d + 1)
    have hv_s2r : validLOFrame (.s2R S) = true := rfl
    have hwrap_iter : ∀ k u,
        (∀ i, i < k → (stepLO (iterateLO i u)).isSome = true) →
        iterateLO k (B_comb ⋅ u) = B_comb ⋅ iterateLO k u := by
      intro k
      induction k with
      | zero => intro _ _; rfl
      | succ k ihk =>
        intro u hall
        have h0 : (stepLO u).isSome = true := hall 0 (Nat.zero_lt_succ k)
        cases hs : stepLO u with
        | none => rw [hs] at h0; cases h0
        | some u' =>
          have hstep_b : stepLO (B_comb ⋅ u) = some (B_comb ⋅ u') :=
            stepLO_plugFrame hv_s2r hs
          simp only [iterateLO, hstep_b, hs]
          exact ihk u' (fun i hi => by
            have hsi := hall (i + 1) (Nat.succ_lt_succ hi)
            simp only [iterateLO, hs] at hsi
            exact hsi)
    refine ⟨?_, ?_⟩
    · simp only [sPrefixStepsRec]
      rw [iterateLO_add (d + 1) (sPrefixStepsRec (d + 1)), hpeel,
          hwrap_iter (sPrefixStepsRec (d + 1)) (sPrefix (d + 1)) hih_some, hih_nf]
      rfl
    · intro j hj
      simp only [sPrefixStepsRec] at hj
      if hlt : j < d + 1 then
        have ⟨hvj, hslj⟩ := hmid j hlt
        obtain ⟨u', hhu'⟩ := closed_spineLen_ge_3_has_headStep hvj hslj
        rw [headStepOpt_some_imp_stepLO hhu']
        rfl
      else
        let i := j - (d + 1)
        have hji : j = (d + 1) + i := (Nat.add_sub_of_le (Nat.not_lt.mp hlt)).symm
        have hi_lt : i < sPrefixStepsRec (d + 1) := by
          have h1 : (d + 1) + i < (d + 1) + sPrefixStepsRec (d + 1) := hji ▸ hj
          exact Nat.lt_of_add_lt_add_left h1
        rw [hji, iterateLO_add (d + 1) i, hpeel,
            hwrap_iter i (sPrefix (d + 1)) (fun r hr => hih_some r (Nat.lt_trans hr hi_lt))]
        have hsi := hih_some i hi_lt
        cases hs : stepLO (iterateLO i (sPrefix (d + 1))) with
        | none => rw [hs] at hsi; cases hsi
        | some u' =>
          have hstep_b : stepLO (B_comb ⋅ iterateLO i (sPrefix (d + 1))) = some (B_comb ⋅ u') :=
            stepLO_plugFrame hv_s2r hs
          rw [hstep_b]
          rfl

/-- **Exact Normal-Form Jump-Ahead Theorem for `sPrefix` (`S S S ...`)**:
    For every `m : Nat` and `r : Nat`:
    1. `sPrefixNF m` is in closed Normal Form (`IsNormalForm (sPrefixNF m)`).
    2. `sPrefix m` reaches `sPrefixNF m` in **exact** step count `sPrefixSteps m = ((m - 1) / 2) * (m / 2)`,
       so `iterateLO (sPrefixSteps m + r) (sPrefix m) = sPrefixNF m` for all `r : Nat`.
    3. Every strictly earlier step `j < sPrefixSteps m` is still active (`(stepLO (iterateLO j (sPrefix m))).isSome = true`). -/
theorem jump_ahead_sPrefix_exact (m r : Nat) :
    IsNormalForm (sPrefixNF m) ∧
    iterateLO (sPrefixSteps m + r) (sPrefix m) = sPrefixNF m ∧
    (∀ j, j < sPrefixSteps m → (stepLO (iterateLO j (sPrefix m))).isSome = true) := by
  rw [← sPrefixStepsRec_eq m]
  obtain ⟨hnf_eq, hsome⟩ := sPrefix_exact_rec m
  have hstay : ∀ k, iterateLO k (sPrefixNF m) = sPrefixNF m := by
    intro k
    induction k with
    | zero => rfl
    | succ _ _ => simp only [iterateLO, stepLO_sPrefixNF_none m]
  refine ⟨stepLO_none_isNormalForm (stepLO_sPrefixNF_none m), ?_, hsome⟩
  rw [iterateLO_add (sPrefixStepsRec m) r, hnf_eq, hstay r]

end FormalWolfram12

#print axioms FormalWolfram12.wolfram_14_announcement_roundtrip
#print axioms FormalWolfram12.seven_leaf_nonhalting_classification
#print axioms FormalWolfram12.wolfram2_closed_form_jump_ahead
#print axioms FormalWolfram12.wolfram2_perpetual_hn_minus_sn
#print axioms FormalWolfram12.zachos_closed_form_jump_ahead
#print axioms FormalWolfram12.zachos_vs_wolfram2_separation
#print axioms FormalWolfram12.wolfram_14_dichotomy_master
#print axioms FormalWolfram12.decideHaltsLO_iff_halts
#print axioms FormalWolfram12.decideHaltsHead_iff_halts
#print axioms FormalWolfram12.decideContextHalts_exact
#print axioms FormalWolfram12.jump_ahead_tenLeafSeed_two_param
#print axioms FormalWolfram12.jump_ahead_rightTower
#print axioms FormalWolfram12.jump_ahead_sPrefix_exact
