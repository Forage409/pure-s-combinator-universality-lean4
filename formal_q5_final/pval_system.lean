import formal_q5_final.ph_tables

/-!
# File 2 of 3 (`formal_q5_final/pval_system.lean`):
1. Exact Zachos family `zachosG` and the 20-line universal `hasBot_zachos_app` theorem;
2. Canonical Productive Values (`PVal`) and syntactic characterization of `.p0, .p1, .p14, .p32`;
3. Fuel-indexed total application `pval_apply` with built-in `out2dList` soundness;
4. Completeness of `PVal` evaluation: every closed pure-`S` term with `isAccPH (evalPH t) = true`
   reduces (`Reduces t v.toTerm`) to a canonical `PVal`!
-/

namespace FormalQ5Final

set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

open FormalAlgebra
open Q5SNStratifiedGame

/-! ## 1. Zachos Generator Family `zachosG` & Universal `hasBot_zachos_app` -/

def zachosT : Term := S ⋅ S

def zachosG : Nat → Term
  | 0 => S ⋅ zachosT ⋅ zachosT
  | k + 1 => zachosT ⋅ zachosG k

theorem noVars_zachosG : ∀ k : Nat, noVars (zachosG k) = true
  | 0 => rfl
  | k + 1 => (Bool.and_eq_true _ _).mpr ⟨rfl, noVars_zachosG k⟩

theorem evalP_zachosG_zero : evalP (zachosG 0) = .p14 := rfl
theorem evalHN_zachosG_zero : evalHN (zachosG 0) = .hn16 := rfl

theorem evalP_zachosG_succ : ∀ k : Nat, evalP (zachosG (k + 1)) = .p32
  | 0 => rfl
  | k + 1 => by
    change deltaP (evalP zachosT) (evalP (zachosG (k + 1))) = .p32
    rw [evalP_zachosG_succ k]; rfl

theorem evalHN_zachosG_succ : ∀ k : Nat, evalHN (zachosG (k + 1)) = .hn13
  | 0 => rfl
  | k + 1 => by
    change deltaHN (evalHN zachosT) (evalHN (zachosG (k + 1))) = .hn13
    rw [evalHN_zachosG_succ k]; rfl

theorem isZachosP_zachosG (k : Nat) : isZachosP (evalP (zachosG k)) = true := by
  cases k with
  | zero => rfl
  | succ k' => simp only [evalP_zachosG_succ]; rfl

theorem evalP_zachos_pair (m n : Nat) : evalP (zachosG m ⋅ zachosG n) = .p29 := by
  cases m <;> cases n <;>
    simp only [evalP, evalP_zachosG_zero, evalP_zachosG_succ] <;> rfl

theorem evalHN_zachos_pair (m n : Nat) :
    evalHN (zachosG m ⋅ zachosG n) = .hn23 ∨ evalHN (zachosG m ⋅ zachosG n) = .hn24 := by
  cases m <;> cases n <;>
    simp only [evalHN, evalHN_zachosG_zero, evalHN_zachosG_succ]
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem zachos_hn_step_chk : checkAll1_StateHN (fun hz =>
    decide ((deltaHN .hn23 hz = .hn34 ∨ deltaHN .hn23 hz = .hn23) ∧
            (deltaHN .hn24 hz = .hn34 ∨ deltaHN .hn24 hz = .hn23) ∧
            (deltaHN (deltaHN .hn16 hz) .hn23 = .hn34) ∧
            (deltaHN (deltaHN .hn16 hz) .hn34 = .hn34))) = true := rfl

private theorem zachos_chain_hasBot : ∀ (n : Nat) {z w : Term},
    noVars z = true → noVars w = true →
    evalHN ((zachosG 0 ⋅ z) ⋅ w) = .hn34 →
    HasBot ((zachosG n ⋅ z) ⋅ w)
  | 0, z, w, hvz, hvw, h34 =>
    have hv : noVars ((zachosG 0 ⋅ z) ⋅ w) = true :=
      (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨noVars_zachosG 0, hvz⟩, hvw⟩
    ⟨0, closed_evalHN_hn34_hasBot0 hv h34⟩
  | n + 1, z, w, hvz, hvw, h34 => by
    obtain ⟨d, hd⟩ := zachos_chain_hasBot n hvz hvw h34
    have hvzw : noVars (z ⋅ w) = true := (Bool.and_eq_true _ _).mpr ⟨hvz, hvw⟩
    have hvgnzw : noVars ((zachosG n ⋅ z) ⋅ w) = true :=
      (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨noVars_zachosG n, hvz⟩, hvw⟩
    have hrhs : HasBotWithin (d + 1) ((z ⋅ w) ⋅ ((zachosG n ⋅ z) ⋅ w)) :=
      hasBotWithin_app_right hvzw hvgnzw hd
    have hstep1 : Step ((zachosG (n + 1) ⋅ z) ⋅ w) ((S ⋅ z ⋅ (zachosG n ⋅ z)) ⋅ w) :=
      Step.left (Step.root S (zachosG n) z)
    have hstep2 : Step ((S ⋅ z ⋅ (zachosG n ⋅ z)) ⋅ w) ((z ⋅ w) ⋅ ((zachosG n ⋅ z) ⋅ w)) :=
      Step.root z (zachosG n ⋅ z) w
    have hred : Reduces ((zachosG (n + 1) ⋅ z) ⋅ w) ((z ⋅ w) ⋅ ((zachosG n ⋅ z) ⋅ w)) :=
      Reduces.next hstep1 (Reduces.next hstep2 (Reduces.refl _))
    exact ⟨d + 1, hasBotWithin_backward_reduces hred hrhs⟩

theorem hasBot_zachos_succ (k n : Nat) {z : Term} (hvz : noVars z = true) :
    HasBot ((zachosG (k + 1) ⋅ zachosG n) ⋅ z) := by
  let w := (zachosG k ⋅ zachosG n) ⋅ z
  have hvw : noVars w = true :=
    (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨noVars_zachosG k, noVars_zachosG n⟩, hvz⟩
  have hchk := of_decide_eq_true (checkAll1_StateHN_sound _ zachos_hn_step_chk (evalHN z))
  have hw_hn : evalHN w = .hn34 ∨ evalHN w = .hn23 := by
    change deltaHN (evalHN (zachosG k ⋅ zachosG n)) (evalHN z) = .hn34 ∨
           deltaHN (evalHN (zachosG k ⋅ zachosG n)) (evalHN z) = .hn23
    rcases evalHN_zachos_pair k n with h23 | h24
    · rw [h23]; exact hchk.1
    · rw [h24]; exact hchk.2.1
  have h0_34 : evalHN ((zachosG 0 ⋅ z) ⋅ w) = .hn34 := by
    change deltaHN (deltaHN (evalHN (zachosG 0)) (evalHN z)) (evalHN w) = .hn34
    rw [evalHN_zachosG_zero]
    rcases hw_hn with hw34 | hw23
    · rw [hw34]; exact hchk.2.2.2
    · rw [hw23]; exact hchk.2.2.1
  obtain ⟨d, hd⟩ := zachos_chain_hasBot n hvz hvw h0_34
  have hs1 : Step ((zachosG (k + 1) ⋅ zachosG n) ⋅ z) ((S ⋅ zachosG n ⋅ (zachosG k ⋅ zachosG n)) ⋅ z) :=
    Step.left (Step.root S (zachosG k) (zachosG n))
  have hs2 : Step ((S ⋅ zachosG n ⋅ (zachosG k ⋅ zachosG n)) ⋅ z) ((zachosG n ⋅ z) ⋅ w) :=
    Step.root (zachosG n) (zachosG k ⋅ zachosG n) z
  exact ⟨d, hasBotWithin_backward_reduces (Reduces.next hs1 (Reduces.next hs2 (Reduces.refl _))) hd⟩

/-- **Universal Zachos-Application Böhm-Bottom Theorem**:
    For all `m, n : Nat` and every closed pure-`S` term `z`, `(zachosG m ⋅ zachosG n) ⋅ z` has `⊥` in its Böhm tree! -/
theorem hasBot_zachos_app (m n : Nat) {z : Term} (hvz : noVars z = true) :
    HasBot ((zachosG m ⋅ zachosG n) ⋅ z) := by
  cases m with
  | succ k => exact hasBot_zachos_succ k n hvz
  | zero =>
    obtain ⟨d, hd⟩ := hasBot_zachos_succ n (n + 1) hvz
    have hs : Step ((zachosG 0 ⋅ zachosG n) ⋅ z) ((zachosG (n + 1) ⋅ zachosG (n + 1)) ⋅ z) :=
      Step.left (Step.root zachosT zachosT (zachosG n))
    exact ⟨d, hasBotWithin_backward_reduces (Reduces.next hs (Reduces.refl _)) hd⟩


/-! ## 2. Canonical Productive Values (`PVal`) & Syntactic Rigidity of `.p0, .p1, .p14, .p32` -/

inductive PVal : Type where
  | s : PVal
  | s1 : PVal → PVal
  | s2 : PVal → PVal → PVal
  | zachos : Nat → Nat → PVal

namespace PVal

def toTerm : PVal → Term
  | .s => S
  | .s1 u => S ⋅ u.toTerm
  | .s2 a b => S ⋅ a.toTerm ⋅ b.toTerm
  | .zachos m n => zachosG m ⋅ zachosG n

def size : PVal → Nat
  | .s => 1
  | .s1 u => u.size + 1
  | .s2 a b => a.size + b.size + 1
  | .zachos _ _ => 1

theorem size_pos : ∀ v : PVal, 1 ≤ v.size
  | .s => Nat.le_refl 1
  | .s1 _ => Nat.le_add_left 1 _
  | .s2 _ _ => Nat.le_add_left 1 _
  | .zachos _ _ => Nat.le_refl 1

theorem noVars_toTerm : ∀ v : PVal, noVars v.toTerm = true
  | .s => rfl
  | .s1 u => (Bool.and_eq_true _ _).mpr ⟨rfl, noVars_toTerm u⟩
  | .s2 a b => (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨rfl, noVars_toTerm a⟩, noVars_toTerm b⟩
  | .zachos m n => (Bool.and_eq_true _ _).mpr ⟨noVars_zachosG m, noVars_zachosG n⟩

theorem evalP_ne_p37 : ∀ v : PVal, evalP v.toTerm ≠ .p37
  | .s => by decide
  | .s1 u => by
    have hu : isAccP (evalP u.toTerm) = true := by simp [isAccP, evalP_ne_p37 u]
    have h1 : isAccP (deltaP .p0 (evalP u.toTerm)) = true := by rw [deltaP_hnf1_iff]; exact hu
    intro hbad; change deltaP .p0 (evalP u.toTerm) = .p37 at hbad
    rw [hbad] at h1; cases h1
  | .s2 a b => by
    have ha : isAccP (evalP a.toTerm) = true := by simp [isAccP, evalP_ne_p37 a]
    have hb : isAccP (evalP b.toTerm) = true := by simp [isAccP, evalP_ne_p37 b]
    have h2 : isAccP (deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)) = true := by
      rw [deltaP_hnf2_iff, ha, hb]; rfl
    intro hbad; change deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm) = .p37 at hbad
    rw [hbad] at h2; cases h2
  | .zachos m n => by rw [toTerm, evalP_zachos_pair]; decide

theorem isAccPH_toTerm (v : PVal) : isAccPH (evalPH v.toTerm) = true := by
  rw [isAccPH_evalPH (noVars_toTerm v)]
  exact decide_eq_true (evalP_ne_p37 v)

end PVal

private theorem pval_rigidity_chk : checkAll2_StateP (fun a b =>
    decide ((deltaP a b ≠ .p0) ∧
            (deltaP .p0 a = .p1 → a = .p0) ∧
            (deltaP (deltaP .p0 a) b ≠ .p1) ∧
            (isZachosP (deltaP .p0 a) = false) ∧
            (deltaP (deltaP .p0 a) b = .p14 → a = .p1 ∧ b = .p1) ∧
            (deltaP (deltaP .p0 a) b = .p32 → a = .p0 ∧ isZachosP b = true) ∧
            (deltaP .p29 b = .p37))) = true := rfl

theorem deltaP_p29_sink (b : StateP) : deltaP .p29 b = .p37 :=
  (of_decide_eq_true (checkAll2_StateP_sound _ pval_rigidity_chk .p0 b)).2.2.2.2.2.2

theorem pval_eq_s_of_p0 : ∀ (v : PVal), evalP v.toTerm = .p0 → v = .s
  | .s, _ => rfl
  | .s1 u, h => False.elim ((of_decide_eq_true (checkAll2_StateP_sound _ pval_rigidity_chk .p0 (evalP u.toTerm))).1 h)
  | .s2 a b, h => False.elim ((of_decide_eq_true (checkAll2_StateP_sound _ pval_rigidity_chk (evalP (S ⋅ a.toTerm)) (evalP b.toTerm))).1 h)
  | .zachos m n, h => by rw [PVal.toTerm, evalP_zachos_pair] at h; cases h

theorem pval_eq_s1s_of_p1 : ∀ (v : PVal), evalP v.toTerm = .p1 → v = .s1 .s
  | .s, h => by cases h
  | .s1 u, h => by
    have hu0 : evalP u.toTerm = .p0 :=
      (of_decide_eq_true (checkAll2_StateP_sound _ pval_rigidity_chk (evalP u.toTerm) .p0)).2.1 h
    rw [pval_eq_s_of_p0 u hu0]
  | .s2 a b, h =>
    False.elim ((of_decide_eq_true (checkAll2_StateP_sound _ pval_rigidity_chk (evalP a.toTerm) (evalP b.toTerm))).2.2.1 h)
  | .zachos m n, h => by rw [PVal.toTerm, evalP_zachos_pair] at h; cases h

/-- Computably extracts `k : Nat` such that `v.toTerm = zachosG k` whenever `isZachosP (evalP v.toTerm) = true`! -/
def pvalZachosIdx : PVal → Nat
  | .s2 .s b => pvalZachosIdx b + 1
  | _ => 0

theorem pvalZachosIdx_spec : ∀ (v : PVal), isZachosP (evalP v.toTerm) = true →
    v.toTerm = zachosG (pvalZachosIdx v)
  | .s, h => by cases h
  | .s1 u, h => by
    have hf : isZachosP (deltaP .p0 (evalP u.toTerm)) = false :=
      (of_decide_eq_true (checkAll2_StateP_sound _ pval_rigidity_chk (evalP u.toTerm) .p0)).2.2.2.1
    change isZachosP (deltaP .p0 (evalP u.toTerm)) = true at h
    rw [hf] at h; cases h
  | .zachos m n, h => by rw [PVal.toTerm, evalP_zachos_pair] at h; cases h
  | .s2 a b, h => by
    have hchk := of_decide_eq_true (checkAll2_StateP_sound _ pval_rigidity_chk (evalP a.toTerm) (evalP b.toTerm))
    change isZachosP (deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)) = true at h
    cases hd : deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm) <;> rw [hd] at h <;> try cases h
    · -- `.p14`: `a = .s1 .s` and `b = .s1 .s`
      have ⟨ha1, hb1⟩ := hchk.2.2.2.2.1 hd
      rw [pval_eq_s1s_of_p1 a ha1, pval_eq_s1s_of_p1 b hb1]
      rfl
    · -- `.p32`: `a = .s` and `isZachosP (evalP b.toTerm) = true`
      have ⟨ha0, hbz⟩ := hchk.2.2.2.2.2.1 hd
      have ha_s : a = .s := pval_eq_s_of_p0 a ha0
      subst ha_s
      have ih := pvalZachosIdx_spec b hbz
      change S ⋅ S ⋅ b.toTerm = zachosT ⋅ zachosG (pvalZachosIdx b)
      rw [ih]; rfl


/-! ## 3. Fuel-Indexed Total `PVal` Application (`pval_apply`) & Completeness -/

structure PValAppRes (f w : PVal) : Type where
  val : PVal
  red : Reduces (f.toTerm ⋅ w.toTerm) val.toTerm
  from_s : f = .s → val = .s1 w
  from_s1 : ∀ u : PVal, f = .s1 u → val = .s2 u w
  s1_imp : ∀ u : PVal, val = .s1 u → f = .s ∧ u = w
  s2_mem : ∀ c d : PVal, val = .s2 c d →
    out2dHas (evalPH f.toTerm) (evalPH w.toTerm) (evalPH c.toTerm) (evalPH d.toTerm) = true

private theorem rankP_unpack {x y z : StateP}
    (hx : x ≠ .p37) (hy : y ≠ .p37) (hz : z ≠ .p37)
    (hf : deltaP (deltaP .p0 x) y ≠ .p37)
    (hfz : deltaP (deltaP (deltaP .p0 x) y) z ≠ .p37)
    (hnz : !(isZachosP (deltaP (deltaP .p0 x) y) && isZachosP z) = true) :
    let r := tripleRankP x y z
    let n1 := deltaP x z
    let n2 := deltaP y z
    (1 ≤ r ∧ r ≤ maxSubRankP (deltaP (deltaP .p0 x) y) z ∧ maxSubRankP x z ≤ r ∧ maxSubRankP y z ≤ r) ∧
    (¬(isZachosP n1 && isZachosP n2) = true →
      (isS2StateP x = true → maxSubRankP n1 n2 + 1 ≤ r) ∧
      (∀ u, u ≠ .p37 → deltaP .p0 u = x → tripleRankP u z n2 + 1 ≤ r)) := by
  have h := rankP_ok_chk x y z
  dsimp only [rankP_ok_fn] at h
  have hcond : (beqP x .p37 || beqP y .p37 || beqP z .p37 || beqP (deltaP (deltaP .p0 x) y) .p37 ||
      beqP (deltaP (deltaP (deltaP .p0 x) y) z) .p37 || (isZachosP (deltaP (deltaP .p0 x) y) && isZachosP z)) = false := by
    cases h1 : beqP x .p37
    · cases h2 : beqP y .p37
      · cases h3 : beqP z .p37
        · cases h4 : beqP (deltaP (deltaP .p0 x) y) .p37
          · cases h5 : beqP (deltaP (deltaP (deltaP .p0 x) y) z) .p37
            · cases h6 : (isZachosP (deltaP (deltaP .p0 x) y) && isZachosP z)
              · rfl
              · rw [h6] at hnz; cases hnz
            · exact False.elim (hfz (eq_of_beqP h5))
          · exact False.elim (hf (eq_of_beqP h4))
        · exact False.elim (hz (eq_of_beqP h3))
      · exact False.elim (hy (eq_of_beqP h2))
    · exact False.elim (hx (eq_of_beqP h1))
  rw [hcond, if_false_eq_true] at h
  have ⟨hb1, hb2⟩ := (Bool.and_eq_true _ _).mp h
  have ⟨hb1a, hb1d⟩ := (Bool.and_eq_true _ _).mp hb1
  have ⟨hb1b, hb1c⟩ := (Bool.and_eq_true _ _).mp hb1a
  have ⟨hc1, hc2⟩ := (Bool.and_eq_true _ _).mp hb1b
  refine ⟨⟨Nat.le_of_ble_eq_true hc1, Nat.le_of_ble_eq_true hc2, Nat.le_of_ble_eq_true hb1c, Nat.le_of_ble_eq_true hb1d⟩, ?_⟩
  intro hnz2
  cases hzz : (isZachosP (deltaP x z) && isZachosP (deltaP y z))
  · rw [hzz, if_false_eq_true] at hb2
    have ⟨hm, hall⟩ := (Bool.and_eq_true _ _).mp hb2
    refine ⟨fun hs2 => Nat.le_of_ble_eq_true (imp_bool hs2 hm), fun u hu hdu => ?_⟩
    have hu_chk := checkAll1_StateP_sound _ hall u
    have hu_false : (beqP u .p37 || !beqP (deltaP .p0 u) x) = false := by
      cases hc_u : beqP u .p37
      · cases hc_eq : beqP (deltaP .p0 u) x
        · exact False.elim (ne_of_beqP_false hc_eq hdu)
        · rfl
      · exact False.elim (hu (eq_of_beqP hc_u))
    rw [hu_false, if_false_eq_true] at hu_chk
    exact Nat.le_of_ble_eq_true hu_chk
  · exact False.elim (hnz2 hzz)

def pvalRank : PVal → StateP → Nat
  | .s2 a b, z =>
    if isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP z then 0
    else tripleRankP (evalP a.toTerm) (evalP b.toTerm) z
  | _, _ => 0

private theorem pvalRank_le_maxSubRankP (f : PVal) {z : StateP}
    (hz : z ≠ .p37) (hfz : deltaP (evalP f.toTerm) z ≠ .p37) :
    pvalRank f z ≤ maxSubRankP (evalP f.toTerm) z := by
  cases f with
  | s => exact Nat.zero_le _
  | s1 _ => exact Nat.zero_le _
  | zachos _ _ => exact Nat.zero_le _
  | s2 a b =>
    dsimp only [pvalRank]
    cases hzz : (isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP z)
    · rw [if_false_eq_true]
      have hnz : !(isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP z) = true := by rw [hzz]; rfl
      exact (rankP_unpack (PVal.evalP_ne_p37 a) (PVal.evalP_ne_p37 b) hz (PVal.evalP_ne_p37 (.s2 a b)) hfz hnz).1.2.1
    · rw [if_true_eq_true]; exact Nat.zero_le _

def pvalApplyAux : (rk : Nat) → (sz : Nat) → (f w : PVal) →
    f.size ≤ sz →
    deltaP (evalP f.toTerm) (evalP w.toTerm) ≠ .p37 →
    pvalRank f (evalP w.toTerm) ≤ rk →
    PValAppRes f w
  | _, _, .s, w, _, _, _ =>
    { val := .s1 w
      red := Reduces.refl _
      from_s := fun _ => rfl
      from_s1 := fun _ h => by cases h
      s1_imp := fun _ h => ⟨rfl, by injection h with h'; exact h'.symm⟩
      s2_mem := fun _ _ h => by cases h }
  | _, _, .s1 u, w, _, hfw, _ =>
    { val := .s2 u w
      red := Reduces.refl _
      from_s := fun h => by cases h
      from_s1 := fun u' h => by injection h with hu; subst hu; rfl
      s1_imp := fun _ h => by cases h
      s2_mem := fun c d h => by
        injection h with hc hd
        subst hc; subst hd
        have hacc_fw : isAccPH (deltaPH (deltaPH ph0 (evalPH u.toTerm)) (evalPH w.toTerm)) = true := by
          change isAccPH (evalPH ((PVal.s1 u).toTerm ⋅ w.toTerm)) = true
          rw [isAccPH_evalPH (t := (PVal.s1 u).toTerm ⋅ w.toTerm)
            ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s1 u), PVal.noVars_toTerm w⟩)]
          exact decide_eq_true hfw
        exact out2d_s1_mem (evalPH u.toTerm) (evalPH w.toTerm) (PVal.isAccPH_toTerm u) (PVal.isAccPH_toTerm w) hacc_fw }
  | _, _, .zachos m n, w, _, hfw, _ =>
    False.elim (by
      have hp : evalP (PVal.zachos m n).toTerm = .p29 := evalP_zachos_pair m n
      rw [hp, deltaP_p29_sink] at hfw
      exact hfw rfl)
  | rk, 0, .s2 a b, _, hsz, _, _ =>
    False.elim (Nat.not_succ_le_zero _ hsz)
  | rk, sz + 1, .s2 a b, w, hsz, hfw, hrk =>
    if hzf : (isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP (evalP w.toTerm)) = true then
      let m := pvalZachosIdx (.s2 a b)
      let n := pvalZachosIdx w
      { val := .zachos m n
        red := by
          have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hzf
          have eq1 := pvalZachosIdx_spec (.s2 a b) h1
          have eq2 := pvalZachosIdx_spec w h2
          change Reduces ((PVal.s2 a b).toTerm ⋅ w.toTerm) (zachosG m ⋅ zachosG n)
          rw [eq1, eq2]; exact Reduces.refl _
        from_s := fun h => by cases h
        from_s1 := fun _ h => by cases h
        s1_imp := fun _ h => by cases h
        s2_mem := fun _ _ h => by cases h }
    else
      have hnz_f : !(isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP (evalP w.toTerm)) = true := by
        cases hc : (isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP (evalP w.toTerm))
        · rfl
        · exact False.elim (hzf hc)
      have hunp := rankP_unpack (PVal.evalP_ne_p37 a) (PVal.evalP_ne_p37 b) (PVal.evalP_ne_p37 w)
        (PVal.evalP_ne_p37 (.s2 a b)) hfw hnz_f
      have htr_pos : 1 ≤ tripleRankP (evalP a.toTerm) (evalP b.toTerm) (evalP w.toTerm) := hunp.1.1
      have htr_le : tripleRankP (evalP a.toTerm) (evalP b.toTerm) (evalP w.toTerm) ≤ rk := by
        dsimp only [pvalRank] at hrk
        cases hzz : (isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP (evalP w.toTerm))
        · rw [hzz, if_false_eq_true] at hrk; exact hrk
        · rw [hzz] at hnz_f; cases hnz_f
      match rk, Nat.le_trans htr_pos htr_le with
      | 0, hbad => False.elim (Nat.not_succ_le_zero 0 hbad)
      | rk' + 1, _ =>
        have ha_sz : a.size ≤ sz := by
          have hbpos := PVal.size_pos b
          change a.size + b.size + 1 ≤ sz + 1 at hsz
          omega
        have hb_sz : b.size ≤ sz := by
          have hapos := PVal.size_pos a
          change a.size + b.size + 1 ≤ sz + 1 at hsz
          omega
        have haw_ne : deltaP (evalP a.toTerm) (evalP w.toTerm) ≠ .p37 := by
          intro hbad
          have hs37 : deltaP (deltaP (evalP a.toTerm) (evalP w.toTerm)) (deltaP (evalP b.toTerm) (evalP w.toTerm)) = .p37 := by
            rw [hbad]; exact (deltaP_sink _).1
          rw [← deltaP_s_law] at hs37
          exact hfw hs37
        have hbw_ne : deltaP (evalP b.toTerm) (evalP w.toTerm) ≠ .p37 := by
          intro hbad
          have hs37 : deltaP (deltaP (evalP a.toTerm) (evalP w.toTerm)) (deltaP (evalP b.toTerm) (evalP w.toTerm)) = .p37 := by
            rw [hbad]; exact (deltaP_sink _).2
          rw [← deltaP_s_law] at hs37
          exact hfw hs37
        have hra_rk : pvalRank a (evalP w.toTerm) ≤ rk' + 1 :=
          Nat.le_trans (pvalRank_le_maxSubRankP a (PVal.evalP_ne_p37 w) haw_ne)
            (Nat.le_trans hunp.1.2.2.1 htr_le)
        have hrb_rk : pvalRank b (evalP w.toTerm) ≤ rk' + 1 :=
          Nat.le_trans (pvalRank_le_maxSubRankP b (PVal.evalP_ne_p37 w) hbw_ne)
            (Nat.le_trans hunp.1.2.2.2 htr_le)
        let ra := pvalApplyAux (rk' + 1) sz a w ha_sz haw_ne hra_rk
        let rb := pvalApplyAux (rk' + 1) sz b w hb_sz hbw_ne hrb_rk
        have hp_ra : evalP ra.val.toTerm = deltaP (evalP a.toTerm) (evalP w.toTerm) :=
          (evalP_reduces ra.red).symm
        have hp_rb : evalP rb.val.toTerm = deltaP (evalP b.toTerm) (evalP w.toTerm) :=
          (evalP_reduces rb.red).symm
        have hph_ra : evalPH ra.val.toTerm = deltaPH (evalPH a.toTerm) (evalPH w.toTerm) :=
          (evalPH_reduces ra.red).symm
        have hph_rb : evalPH rb.val.toTerm = deltaPH (evalPH b.toTerm) (evalPH w.toTerm) :=
          (evalPH_reduces rb.red).symm
        have hstep_root : Reduces ((PVal.s2 a b).toTerm ⋅ w.toTerm) (ra.val.toTerm ⋅ rb.val.toTerm) :=
          Reduces.next (Step.root a.toTerm b.toTerm w.toTerm)
            (reduces_trans (reduces_left ra.red _) (reduces_right _ rb.red))
        if hzn : (isZachosP (evalP ra.val.toTerm) && isZachosP (evalP rb.val.toTerm)) = true then
          let m := pvalZachosIdx ra.val
          let n := pvalZachosIdx rb.val
          { val := .zachos m n
            red := by
              have ⟨hz1, hz2⟩ := (Bool.and_eq_true _ _).mp hzn
              have eq1 := pvalZachosIdx_spec ra.val hz1
              have eq2 := pvalZachosIdx_spec rb.val hz2
              change Reduces ((PVal.s2 a b).toTerm ⋅ w.toTerm) (zachosG m ⋅ zachosG n)
              rw [← eq1, ← eq2]; exact hstep_root
            from_s := fun h => by cases h
            from_s1 := fun _ h => by cases h
            s1_imp := fun _ h => by cases h
            s2_mem := fun _ _ h => by cases h }
        else
          have hnz_n : ¬(isZachosP (deltaP (evalP a.toTerm) (evalP w.toTerm)) &&
                         isZachosP (deltaP (evalP b.toTerm) (evalP w.toTerm))) = true := by
            intro hbad; rw [← hp_ra, ← hp_rb] at hbad; exact hzn hbad
          have hprod_ne : deltaP (evalP ra.val.toTerm) (evalP rb.val.toTerm) ≠ .p37 := by
            rw [hp_ra, hp_rb, ← deltaP_s_law]; exact hfw
          have hsub_rk : pvalRank ra.val (evalP rb.val.toTerm) ≤ rk' := by
            have ha_cases : (∃ u, a = .s1 u) ∨ (a = .s) ∨ (∃ m n, a = .zachos m n) ∨ (∃ a1 a2, a = .s2 a1 a2) :=
              match a with
              | .s1 u => Or.inl ⟨u, rfl⟩
              | .s => Or.inr (Or.inl rfl)
              | .zachos m n => Or.inr (Or.inr (Or.inl ⟨m, n, rfl⟩))
              | .s2 a1 a2 => Or.inr (Or.inr (Or.inr ⟨a1, a2, rfl⟩))
            rcases ha_cases with ⟨u, ha_s1⟩ | ha_s | ⟨m, n, ha_z⟩ | ⟨a1, a2, ha_s2⟩
            · rw [ra.from_s1 u ha_s1]
              dsimp only [pvalRank]
              cases hzz2 : (isZachosP (evalP (PVal.s2 u w).toTerm) && isZachosP (evalP rb.val.toTerm))
              · rw [if_false_eq_true, hp_rb]
                have hdu : deltaP .p0 (evalP u.toTerm) = evalP a.toTerm := by rw [ha_s1]; rfl
                have hle_u := (hunp.2 hnz_n).2 (evalP u.toTerm) (PVal.evalP_ne_p37 u) hdu
                omega
              · rw [if_true_eq_true]; exact Nat.zero_le _
            · rw [ra.from_s ha_s]; exact Nat.zero_le _
            · exfalso
              have hp29 : evalP a.toTerm = .p29 := by rw [ha_z]; exact evalP_zachos_pair m n
              rw [hp29, deltaP_p29_sink] at haw_ne; exact haw_ne rfl
            · have hs2 : isS2StateP (evalP a.toTerm) = true := by
                rw [ha_s2]
                exact isS2StateP_intro (PVal.evalP_ne_p37 a1) (PVal.evalP_ne_p37 a2) (PVal.evalP_ne_p37 (.s2 a1 a2))
              have hmax_le : maxSubRankP (evalP ra.val.toTerm) (evalP rb.val.toTerm) ≤ rk' := by
                rw [hp_ra, hp_rb]
                have hle1 := (hunp.2 hnz_n).1 hs2
                omega
              exact Nat.le_trans (pvalRank_le_maxSubRankP ra.val (PVal.evalP_ne_p37 rb.val) hprod_ne) hmax_le
          let rfin := pvalApplyAux rk' ra.val.size ra.val rb.val (Nat.le_refl _) hprod_ne hsub_rk
          { val := rfin.val
            red := reduces_trans hstep_root rfin.red
            from_s := fun h => by cases h
            from_s1 := fun _ h => by cases h
            s1_imp := fun u hu => by
              obtain ⟨hra_s, _⟩ := rfin.s1_imp u hu
              exfalso
              have hph0 : evalPH ra.val.toTerm = ph0 := by rw [hra_s]; rfl
              rw [hph_ra] at hph0
              exact deltaPH_ne_ph0 (evalPH a.toTerm) (evalPH w.toTerm) hph0
            s2_mem := fun c d hcd => by
              have hacc_fw : isAccPH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH w.toTerm)) = true := by
                change isAccPH (evalPH ((PVal.s2 a b).toTerm ⋅ w.toTerm)) = true
                rw [isAccPH_evalPH (t := (PVal.s2 a b).toTerm ⋅ w.toTerm)
                  ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 a b), PVal.noVars_toTerm w⟩)]
                exact decide_eq_true hfw
              have hnz_f_ph : !(isZachosPH (deltaPH (deltaPH ph0 (evalPH a.toTerm)) (evalPH b.toTerm)) &&
                                isZachosPH (evalPH w.toTerm)) = true := by
                dsimp only [isZachosPH, deltaPH, evalPH]
                exact hnz_f
              have hnz_n_ph : !(isZachosPH (deltaPH (evalPH a.toTerm) (evalPH w.toTerm)) &&
                                isZachosPH (deltaPH (evalPH b.toTerm) (evalPH w.toTerm))) = true := by
                have hf0 : decide ((isZachosPH (deltaPH (evalPH a.toTerm) (evalPH w.toTerm)) &&
                                    isZachosPH (deltaPH (evalPH b.toTerm) (evalPH w.toTerm))) = true) = false :=
                  decide_eq_false hnz_n
                rw [hf0]; rfl
              cases hra_v : ra.val with
              | s =>
                exfalso
                have hph0 : evalPH ra.val.toTerm = ph0 := by rw [hra_v]; rfl
                rw [hph_ra] at hph0
                exact deltaPH_ne_ph0 _ _ hph0
              | zachos m n =>
                exfalso
                have hp29 : evalP ra.val.toTerm = .p29 := by rw [hra_v]; exact evalP_zachos_pair m n
                rw [hp29, deltaP_p29_sink] at hprod_ne
                exact hprod_ne rfl
              | s1 u =>
                obtain ⟨ha_s, hu_w⟩ := ra.s1_imp u hra_v
                subst ha_s; rw [hu_w] at hra_v
                have hrfin_eq : rfin.val = .s2 w rb.val := rfin.from_s1 w hra_v
                rw [hrfin_eq] at hcd
                injection hcd with hc_eq hd_eq
                subst hc_eq; subst hd_eq
                rw [hph_rb]
                exact out2d_s2_a0 (evalPH b.toTerm) (evalPH w.toTerm)
                  (PVal.isAccPH_toTerm b) (PVal.isAccPH_toTerm w)
                  (PVal.isAccPH_toTerm (.s2 .s b)) hacc_fw hnz_f_ph hnz_n_ph
              | s2 u1 u2 =>
                have hmem_aw : out2dHas (evalPH a.toTerm) (evalPH w.toTerm) (evalPH u1.toTerm) (evalPH u2.toTerm) = true :=
                  ra.s2_mem u1 u2 hra_v
                have hmem_fin : out2dHas (evalPH ra.val.toTerm) (evalPH rb.val.toTerm) (evalPH c.toTerm) (evalPH d.toTerm) = true :=
                  rfin.s2_mem c d hcd
                rw [hra_v] at hmem_fin
                change out2dHas (deltaPH (deltaPH ph0 (evalPH u1.toTerm)) (evalPH u2.toTerm)) (evalPH rb.val.toTerm)
                  (evalPH c.toTerm) (evalPH d.toTerm) = true at hmem_fin
                rw [hph_rb] at hmem_fin
                have hnz_u12 : !(isZachosPH (deltaPH (deltaPH ph0 (evalPH u1.toTerm)) (evalPH u2.toTerm)) &&
                                 isZachosPH (deltaPH (evalPH b.toTerm) (evalPH w.toTerm))) = true := by
                  have heq_u12 : deltaPH (deltaPH ph0 (evalPH u1.toTerm)) (evalPH u2.toTerm) =
                      deltaPH (evalPH a.toTerm) (evalPH w.toTerm) := by
                    rw [← hph_ra, hra_v]; rfl
                  rw [heq_u12]; exact hnz_n_ph
                exact out2d_trans (PVal.isAccPH_toTerm a) (PVal.isAccPH_toTerm b) (PVal.isAccPH_toTerm w)
                  (PVal.isAccPH_toTerm (.s2 a b)) hacc_fw hnz_f_ph hnz_n_ph hnz_u12 hmem_aw hmem_fin }

/-- Total `PVal` application on all productive pairs `(f, w : PVal)` with `evalP (f.toTerm ⋅ w.toTerm) ≠ .p37`. -/
def pvalApply (f w : PVal) (hfw : deltaP (evalP f.toTerm) (evalP w.toTerm) ≠ .p37) : PValAppRes f w :=
  pvalApplyAux (pvalRank f (evalP w.toTerm)) f.size f w (Nat.le_refl _) hfw (Nat.le_refl _)

/-- **Canonical `PVal` Evaluation Theorem**:
    Every closed pure-`S` term `t` with `evalP t ≠ .p37` reduces (`Reduces t v.toTerm`) to a canonical `PVal`! -/
def toPVal : (t : Term) → noVars t = true → evalP t ≠ .p37 → Σ' v : PVal, Reduces t v.toTerm
  | .s, _, _ => ⟨.s, Reduces.refl S⟩
  | .var _, hv, _ => False.elim (by cases hv)
  | .app a b, hv, hab =>
    have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
    have ha_ne : evalP a ≠ .p37 := fun h37 => hab (by change deltaP (evalP a) (evalP b) = .p37; rw [h37]; exact (deltaP_sink _).1)
    have hb_ne : evalP b ≠ .p37 := fun h37 => hab (by change deltaP (evalP a) (evalP b) = .p37; rw [h37]; exact (deltaP_sink _).2)
    let ⟨va, hra⟩ := toPVal a hva ha_ne
    let ⟨vb, hrb⟩ := toPVal b hvb hb_ne
    have hprod_ne : deltaP (evalP va.toTerm) (evalP vb.toTerm) ≠ .p37 := by
      rw [← evalP_reduces hra, ← evalP_reduces hrb]; exact hab
    let r := pvalApply va vb hprod_ne
    ⟨r.val, reduces_trans (reduces_trans (reduces_left hra b) (reduces_right va.toTerm hrb)) r.red⟩

end FormalQ5Final
