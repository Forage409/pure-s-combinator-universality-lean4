import formal_q10_q5_simplified.chunks.q10_chunk_0
import formal_q10_q5_simplified.chunks.q10_chunk_1
import formal_q10_q5_simplified.chunks.q10_chunk_2
import formal_q10_q5_simplified.chunks.q10_chunk_3

/-!
# Simplified Proofs of Waldmann's Theorem 9 (`A_SN`), Barendregt et al. Open Problem 10 (`A_HN`),
# Automaton-Free Head Conservation, Pointwise Minimality of `hnA`, Rank-1 Impossibility,
# and `Acc`-Based Pure-`S` Head-Escape & Böhm Sink Laws

Zero `sorry`, zero `Classical.choice`, zero `native_decide`, zero custom axioms.
-/

namespace SimplifiedQ10Q5
set_option linter.constructorNameAsVariable false
open FormalAlgebra

/-! ## 1. Deterministic `headStepOpt` and Automaton-Free Head Conservation (`HasHNF ↔ StrongHeadNormalizing`) -/

def rootRedexOpt (a b : Term) : Option Term :=
  match a with | .app (.app .s x) y => some ((x ⋅ b) ⋅ (y ⋅ b)) | _ => none

theorem rootRedexOpt_some {a b r : Term} (h : rootRedexOpt a b = some r) :
    ∃ x y, a = S ⋅ x ⋅ y ∧ r = (x ⋅ b) ⋅ (y ⋅ b) := by
  cases a with
  | s => cases h | var _ => cases h
  | app a1 y => cases a1 with
    | s => cases h | var _ => cases h
    | app a2 x => cases a2 with | s => injection h with hr; exact ⟨x, y, rfl, hr.symm⟩ | var _ => cases h | app _ _ => cases h

theorem rootRedexOpt_none {a b : Term} (h : rootRedexOpt a b = none) : ∀ x y, a ≠ S ⋅ x ⋅ y := by
  intro x y heq; subst heq; cases h

def headStepOpt : Term → Option Term
  | .s => none | .var _ => none
  | .app a b =>
    match rootRedexOpt a b with
    | some r => some r
    | none => match headStepOpt a with | some a' => some (a' ⋅ b) | none => none

theorem headStepOpt_some {t t' : Term} (h : headStepOpt t = some t') : HeadStep t t' := by
  induction t generalizing t' with
  | s => cases h | var _ => cases h
  | app a b iha _ =>
    simp only [headStepOpt] at h
    cases hr : rootRedexOpt a b with
    | some r =>
      rw [hr] at h; injection h with heq; subst heq
      obtain ⟨x, y, ha, hreq⟩ := rootRedexOpt_some hr; subst ha; subst hreq; exact HeadStep.root x y b
    | none =>
      rw [hr] at h; cases ha : headStepOpt a with
      | some a' => rw [ha] at h; injection h with heq; subst heq; exact HeadStep.left (iha ha)
      | none => rw [ha] at h; cases h

theorem headStep_spineLen_ge_3 {a b : Term} (hs : HeadStep a b) : 3 ≤ spineLen a := by
  induction hs with | root _ _ _ => exact Nat.le_refl 3 | left _ ih => exact Nat.le_trans ih (Nat.le_add_left _ 1)

theorem headStepOpt_none_closed {t : Term} (hv : noVars t = true) (h : headStepOpt t = none) :
    t = S ∨ (∃ x, t = S ⋅ x) ∨ (∃ x y, t = S ⋅ x ⋅ y) := by
  induction t with
  | s => exact Or.inl rfl | var _ => cases hv
  | app a b iha _ =>
    have ⟨hva, _⟩ := (Bool.and_eq_true _ _).mp hv; simp only [headStepOpt] at h
    cases hr : rootRedexOpt a b with
    | some _ => rw [hr] at h; cases h
    | none =>
      rw [hr] at h; cases ha : headStepOpt a with
      | some _ => rw [ha] at h; cases h
      | none =>
        rcases iha hva ha with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
        · exact Or.inr (Or.inl ⟨b, rfl⟩)
        · exact Or.inr (Or.inr ⟨x, b, rfl⟩)
        · exfalso; exact rootRedexOpt_none hr x y rfl

theorem headStepOpt_none_spineLen {t : Term} (hv : noVars t = true) (h : headStepOpt t = none) : spineLen t ≤ 2 := by
  rcases headStepOpt_none_closed hv h with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · exact Nat.zero_le 2
  · exact Nat.succ_le_succ (Nat.zero_le 1)
  · exact Nat.le_refl 2

def StrongHeadNormalizing (t : Term) : Prop := Acc (fun b a => HeadStep a b) t

private theorem weightedPar_refl_local (t : Term) : WeightedPar 0 t t := by
  induction t with | s => exact .s | var k => exact .var k | app _ _ iha ihb => exact .app iha ihb

private theorem weightedPar_of_step_local {a b : Term} (h : Step a b) : ∃ w, WeightedPar w a b := by
  induction h with
  | root x y z => exact ⟨1, .beta (weightedPar_refl_local x) (weightedPar_refl_local y) (weightedPar_refl_local z)⟩
  | left _ ih => obtain ⟨w, hw⟩ := ih; exact ⟨w + 0, .app hw (weightedPar_refl_local _)⟩
  | right _ ih => obtain ⟨w, hw⟩ := ih; exact ⟨0 + w, .app (weightedPar_refl_local _) hw⟩

private theorem weightedPar_head_project {w : Nat} {m n m1 : Term}
    (d : WeightedPar w m n) (hs : HeadStep m m1) :
    (∃ w1, w1 < w ∧ WeightedPar w1 m1 n) ∨ (∃ w1 n1, HeadStep n n1 ∧ WeightedPar w1 m1 n1) := by
  induction d generalizing m1 with
  | s => cases hs | var _ => cases hs
  | @beta wx wy wz x x' y y' z z' dx dy dz _ _ _ =>
    cases hs with
    | root _ _ _ => exact Or.inl ⟨(wx + wz) + (wy + wz), by omega, .app (.app dx dz) (.app dy dz)⟩
    | left hl => exfalso; have hge3 := headStep_spineLen_ge_3 hl; change 3 ≤ 2 at hge3; omega
  | @app wa wb a a' b b' da db iha _ =>
    cases hs with
    | @root x y _ =>
      cases da with | @app _ _ _ _ _ y' dsx dy => cases dsx with | @app _ _ _ _ _ x' ds dx =>
        cases ds; exact Or.inr ⟨_, (x' ⋅ b') ⋅ (y' ⋅ b'), HeadStep.root x' y' b', .app (.app dx db) (.app dy db)⟩
    | @left _ a1 _ ha =>
      rcases iha ha with ⟨wa1, hw, da1⟩ | ⟨wa1, a1', hstep, da1⟩
      · exact Or.inl ⟨wa1 + wb, by omega, .app da1 db⟩
      · exact Or.inr ⟨wa1 + wb, a1' ⋅ b', HeadStep.left hstep, .app da1 db⟩

private theorem shn_pullback_weightedPar :
    ∀ {n : Term}, StrongHeadNormalizing n → ∀ (k : Nat) {w : Nat} {m : Term}, WeightedPar w m n → w ≤ k → StrongHeadNormalizing m := by
  intro n hn; induction hn with | intro n _ ihn =>
    intro k; induction k with
    | zero =>
      intro w m d hk; refine Acc.intro m (fun m1 hs => ?_)
      rcases weightedPar_head_project d hs with ⟨w1, hw, _⟩ | ⟨w1, n1, hns, d1⟩
      · exact False.elim (by omega)
      · exact ihn n1 hns w1 d1 (Nat.le_refl _)
    | succ k ihk =>
      intro w m d hk; refine Acc.intro m (fun m1 hs => ?_)
      rcases weightedPar_head_project d hs with ⟨w1, hw, d1⟩ | ⟨w1, n1, hns, d1⟩
      · exact ihk d1 (by omega)
      · exact ihn n1 hns w1 d1 (Nat.le_refl _)

theorem head_conservation_step {m n : Term} (hs : Step m n) (hshn : StrongHeadNormalizing n) : StrongHeadNormalizing m := by
  obtain ⟨w, hw⟩ := weightedPar_of_step_local hs; exact shn_pullback_weightedPar hshn w hw (Nat.le_refl w)

theorem hnf_is_strongHeadNormalizing {h : Term} (hsl : spineLen h ≤ 2) : StrongHeadNormalizing h :=
  Acc.intro h (fun _ hs => False.elim (by have := headStep_spineLen_ge_3 hs; omega))

theorem hasHNF_implies_strongHeadNormalizing {t : Term} (hhnf : HasHNF t) : StrongHeadNormalizing t := by
  obtain ⟨h, hred, hsl⟩ := hhnf
  induction hred with | refl _ => exact hnf_is_strongHeadNormalizing hsl | next hs _ ih => exact head_conservation_step hs (ih hsl)

theorem shn_reduces_hnf {t : Term} (hshn : StrongHeadNormalizing t) :
    ∃ h, HeadReduces t h ∧ headStepOpt h = none := by
  induction hshn with | intro t _ ih =>
    cases hh : headStepOpt t with
    | none => exact ⟨t, HeadReduces.refl t, hh⟩
    | some t' =>
      obtain ⟨h, hr, hn⟩ := ih t' (headStepOpt_some hh)
      exact ⟨h, HeadReduces.next (headStepOpt_some hh) hr, hn⟩

theorem hasHNF_iff_strongHeadNormalizing {t : Term} (hv : noVars t = true) : HasHNF t ↔ StrongHeadNormalizing t := by
  refine ⟨hasHNF_implies_strongHeadNormalizing, fun hshn => ?_⟩
  obtain ⟨h, hred, hnone⟩ := shn_reduces_hnf hshn; have hrs := headReduces_to_reduces hred
  exact ⟨h, hrs, headStepOpt_none_spineLen (noVars_reduces hrs hv) hnone⟩

/-! ## 2. Simplified Proof of Waldmann's Theorem 9 (`A_SN`, 39 States — 3D Table Eliminated) -/

def stepLO : Term → Option Term
  | .s => none | .var _ => none
  | .app a b =>
    match rootRedexOpt a b with
    | some r => some r
    | none => match stepLO a with | some a' => some (a' ⋅ b) | none => match stepLO b with | some b' => some (a ⋅ b') | none => none

theorem stepLO_some_step {t t' : Term} (h : stepLO t = some t') : Step t t' := by
  induction t generalizing t' with
  | s => cases h | var _ => cases h
  | app a b iha ihb =>
    simp only [stepLO] at h; cases hr : rootRedexOpt a b with
    | some r => rw [hr] at h; injection h with heq; subst heq; obtain ⟨x, y, ha, hreq⟩ := rootRedexOpt_some hr; subst ha; subst hreq; exact Step.root x y b
    | none =>
      rw [hr] at h; cases ha : stepLO a with
      | some a' => rw [ha] at h; injection h with heq; subst heq; exact Step.left (iha ha)
      | none => rw [ha] at h; cases hb : stepLO b with | some b' => rw [hb] at h; injection h with heq; subst heq; exact Step.right (ihb hb) | none => rw [hb] at h; cases h

theorem stepLO_none_isNormalForm {t : Term} (h : stepLO t = none) : IsNormalForm t := by
  intro t' hs; induction hs with
  | root _ _ _ => cases h
  | @left a _ _ _ iha => simp only [stepLO] at h; cases hr : rootRedexOpt a _ with | some _ => rw [hr] at h; cases h | none => rw [hr] at h; cases ha : stepLO a with | some _ => rw [ha] at h; cases h | none => exact iha ha
  | @right a b _ _ ihb => simp only [stepLO] at h; cases hr : rootRedexOpt a b with | some _ => rw [hr] at h; cases h | none => rw [hr] at h; cases ha : stepLO a with | some _ => rw [ha] at h; cases h | none => rw [ha] at h; cases hb : stepLO b with | some _ => rw [hb] at h; cases h | none => exact ihb hb

theorem sn_iff_wn (t : Term) : StrongNormalizing t ↔ HasNormalForm t := by
  refine ⟨fun hsn => ?_, wn_implies_sn⟩
  induction hsn with | intro t _ ih => cases h : stepLO t with
    | none => exact ⟨t, Reduces.refl t, stepLO_none_isNormalForm h⟩
    | some t' => obtain ⟨nf, hr, hnf⟩ := ih t' (stepLO_some_step h); exact ⟨nf, Reduces.next (stepLO_some_step h) hr, hnf⟩

theorem ofSnIdx_snIdx (a : StateSN) : ofSnIdx (snIdx a) = a := by cases a <;> rfl
theorem snIdx_lt_39 (a : StateSN) : snIdx a < 39 := by cases a <;> decide
theorem snIdx_ofSnIdx {i : Nat} (hi : i < 39) : snIdx (ofSnIdx i) = i :=
  Nat.eq_of_beq_eq_true (checkNat1_sound 39 _ snIdx_ofSnIdx_chk hi)
theorem eq_of_beq_StateSN {a b : StateSN} (h : beq_StateSN a b = true) : a = b := by
  have h2 := congrArg ofSnIdx (Nat.eq_of_beq_eq_true h); rwa [ofSnIdx_snIdx, ofSnIdx_snIdx] at h2
theorem ne_of_beq_StateSN_false {a b : StateSN} (h : beq_StateSN a b = false) : a ≠ b := by
  intro heq; subst heq; unfold beq_StateSN at h; rw [Nat.beq_refl] at h; cases h

private theorem snIdx_deltaSN (a b : StateSN) : snIdx (deltaSN a b) = dsnIdx (snIdx a) (snIdx b) ∧ dsnIdx (snIdx a) (snIdx b) < 39 := by
  have h := checkNat2_sound 39 39 _ dsn_bridge_chk (snIdx_lt_39 a) (snIdx_lt_39 b)
  rw [ofSnIdx_snIdx, ofSnIdx_snIdx] at h
  exact ⟨Nat.eq_of_beq_eq_true (and_left h), Nat.le_of_ble_eq_true (and_right h)⟩

private theorem dsn_s_law_all {x : Nat} (hx : x < 39) : dsn_s_law_row x = true :=
  match x, hx with
  | 0, _ => dsn_s_law_r0 | 1, _ => dsn_s_law_r1 | 2, _ => dsn_s_law_r2 | 3, _ => dsn_s_law_r3 | 4, _ => dsn_s_law_r4
  | 5, _ => dsn_s_law_r5 | 6, _ => dsn_s_law_r6 | 7, _ => dsn_s_law_r7 | 8, _ => dsn_s_law_r8 | 9, _ => dsn_s_law_r9
  | 10, _ => dsn_s_law_r10 | 11, _ => dsn_s_law_r11 | 12, _ => dsn_s_law_r12 | 13, _ => dsn_s_law_r13 | 14, _ => dsn_s_law_r14
  | 15, _ => dsn_s_law_r15 | 16, _ => dsn_s_law_r16 | 17, _ => dsn_s_law_r17 | 18, _ => dsn_s_law_r18 | 19, _ => dsn_s_law_r19
  | 20, _ => dsn_s_law_r20 | 21, _ => dsn_s_law_r21 | 22, _ => dsn_s_law_r22 | 23, _ => dsn_s_law_r23 | 24, _ => dsn_s_law_r24
  | 25, _ => dsn_s_law_r25 | 26, _ => dsn_s_law_r26 | 27, _ => dsn_s_law_r27 | 28, _ => dsn_s_law_r28 | 29, _ => dsn_s_law_r29
  | 30, _ => dsn_s_law_r30 | 31, _ => dsn_s_law_r31 | 32, _ => dsn_s_law_r32 | 33, _ => dsn_s_law_r33 | 34, _ => dsn_s_law_r34
  | 35, _ => dsn_s_law_r35 | 36, _ => dsn_s_law_r36 | 37, _ => dsn_s_law_r37 | 38, _ => dsn_s_law_r38
  | _ + 39, hbad => False.elim (by omega)
private theorem sn_ranks_all {x : Nat} (hx : x < 39) : sn_ranks_row x = true :=
  match x, hx with
  | 0, _ => sn_ranks_r0 | 1, _ => sn_ranks_r1 | 2, _ => sn_ranks_r2 | 3, _ => sn_ranks_r3 | 4, _ => sn_ranks_r4
  | 5, _ => sn_ranks_r5 | 6, _ => sn_ranks_r6 | 7, _ => sn_ranks_r7 | 8, _ => sn_ranks_r8 | 9, _ => sn_ranks_r9
  | 10, _ => sn_ranks_r10 | 11, _ => sn_ranks_r11 | 12, _ => sn_ranks_r12 | 13, _ => sn_ranks_r13 | 14, _ => sn_ranks_r14
  | 15, _ => sn_ranks_r15 | 16, _ => sn_ranks_r16 | 17, _ => sn_ranks_r17 | 18, _ => sn_ranks_r18 | 19, _ => sn_ranks_r19
  | 20, _ => sn_ranks_r20 | 21, _ => sn_ranks_r21 | 22, _ => sn_ranks_r22 | 23, _ => sn_ranks_r23 | 24, _ => sn_ranks_r24
  | 25, _ => sn_ranks_r25 | 26, _ => sn_ranks_r26 | 27, _ => sn_ranks_r27 | 28, _ => sn_ranks_r28 | 29, _ => sn_ranks_r29
  | 30, _ => sn_ranks_r30 | 31, _ => sn_ranks_r31 | 32, _ => sn_ranks_r32 | 33, _ => sn_ranks_r33 | 34, _ => sn_ranks_r34
  | 35, _ => sn_ranks_r35 | 36, _ => sn_ranks_r36 | 37, _ => sn_ranks_r37 | 38, _ => sn_ranks_r38
  | _ + 39, hbad => False.elim (by omega)

theorem deltaSN_s_law (x y z : StateSN) : deltaSN (deltaSN (deltaSN .sn0 x) y) z = deltaSN (deltaSN x z) (deltaSN y z) := by
  have h := Nat.eq_of_beq_eq_true (checkNat2_sound 39 39 _ (dsn_s_law_all (snIdx_lt_39 x)) (snIdx_lt_39 y) (snIdx_lt_39 z))
  have hL : snIdx (deltaSN (deltaSN (deltaSN .sn0 x) y) z) = dsnIdx (dsnIdx (dsnIdx 0 (snIdx x)) (snIdx y)) (snIdx z) := by
    rw [(snIdx_deltaSN _ z).1, (snIdx_deltaSN _ y).1, (snIdx_deltaSN .sn0 x).1]; rfl
  have hR : snIdx (deltaSN (deltaSN x z) (deltaSN y z)) = dsnIdx (dsnIdx (snIdx x) (snIdx z)) (dsnIdx (snIdx y) (snIdx z)) := by
    rw [(snIdx_deltaSN _ _).1, (snIdx_deltaSN x z).1, (snIdx_deltaSN y z).1]
  exact eq_of_beq_StateSN (Nat.beq_eq.mpr (hL.trans (h.trans hR.symm)))

theorem deltaSN_ne_sn38_factors {x y : StateSN} (h : deltaSN x y ≠ .sn38) : x ≠ .sn38 ∧ y ≠ .sn38 := by
  have hm := checkNat2_sound 39 39 _ sn_meta_chk (snIdx_lt_39 x) (snIdx_lt_39 y)
  refine ⟨fun hx => h ?_, fun hy => h ?_⟩
  · subst hx; exact eq_of_beq_StateSN (by unfold beq_StateSN; rw [(snIdx_deltaSN .sn38 y).1]; exact and_left (and_left (and_left hm)))
  · subst hy; exact eq_of_beq_StateSN (by unfold beq_StateSN; rw [(snIdx_deltaSN x .sn38).1]; exact and_right (and_left (and_left hm)))

theorem evalSN_step {a b : Term} (h : Step a b) : evalSN a = evalSN b := by
  induction h with | root _ _ _ => exact deltaSN_s_law _ _ _ | left _ ih => simp [evalSN, ih] | right _ ih => simp [evalSN, ih]
theorem evalSN_reduces {a b : Term} (h : Reduces a b) : evalSN a = evalSN b := by
  induction h with | refl _ => rfl | next hs _ ih => exact (evalSN_step hs).trans ih

theorem closed_nf_evalSN_ne_sn38 {t : Term} (hv : noVars t = true) (hnf : IsNormalForm t) : evalSN t ≠ .sn38 := by
  induction t with
  | s => exact ne_of_beq_StateSN_false rfl | var _ => cases hv
  | app a b iha ihb =>
    have hnone : headStepOpt (a ⋅ b) = none := by
      cases hh : headStepOpt (a ⋅ b) with | none => rfl | some w => exfalso; exact hnf w (headStep_to_step (headStepOpt_some hh))
    have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
    have hnfa : IsNormalForm a := fun a' hs => hnf (a' ⋅ b) (Step.left hs)
    have hnfb : IsNormalForm b := fun b' hs => hnf (a ⋅ b') (Step.right hs)
    rcases headStepOpt_none_closed hv hnone with heq | ⟨x, heq⟩ | ⟨x, y, heq⟩
    · cases heq
    · injection heq with ha hb; subst ha; subst hb
      intro h38; change deltaSN .sn0 (evalSN b) = .sn38 at h38
      have hm := and_right (and_left (checkNat2_sound 39 39 _ sn_meta_chk (snIdx_lt_39 (evalSN b)) (by decide : 0 < 39)))
      have hb38 : Nat.beq (snIdx (evalSN b)) 38 = false := by cases hc : Nat.beq (snIdx (evalSN b)) 38 with | false => rfl | true => exact False.elim (ihb hvb hnfb (eq_of_beq_StateSN hc))
      have hs1 : dsnIdx 0 (snIdx (evalSN b)) = 38 := by have := (snIdx_deltaSN .sn0 (evalSN b)).1; rw [h38] at this; exact this.symm
      rw [hb38, Bool.false_or, hs1] at hm; cases hm
    · injection heq with ha hb; subst ha; subst hb
      have hx := (deltaSN_ne_sn38_factors (iha hva hnfa)).2
      intro h38; change deltaSN (deltaSN .sn0 (evalSN x)) (evalSN b) = .sn38 at h38
      have hm := and_right (checkNat2_sound 39 39 _ sn_meta_chk (snIdx_lt_39 (evalSN x)) (snIdx_lt_39 (evalSN b)))
      have hx38 : Nat.beq (snIdx (evalSN x)) 38 = false := by cases hc : Nat.beq (snIdx (evalSN x)) 38 with | false => rfl | true => exact False.elim (hx (eq_of_beq_StateSN hc))
      have hb38 : Nat.beq (snIdx (evalSN b)) 38 = false := by cases hc : Nat.beq (snIdx (evalSN b)) 38 with | false => rfl | true => exact False.elim (ihb hvb hnfb (eq_of_beq_StateSN hc))
      have hs2 : dsnIdx (dsnIdx 0 (snIdx (evalSN x))) (snIdx (evalSN b)) = 38 := by
        have := (snIdx_deltaSN (deltaSN .sn0 (evalSN x)) (evalSN b)).1; rw [(snIdx_deltaSN .sn0 (evalSN x)).1, h38] at this; exact this.symm
      rw [hx38, hb38, Bool.false_or, Bool.false_or, hs2] at hm; cases hm

private theorem tripleRankSN_bounds {x y z : StateSN} (hval : deltaSN (deltaSN (deltaSN .sn0 x) y) z ≠ .sn38) :
    1 ≤ tripleRankSN x y z ∧ maxSubRankSN x z ≤ tripleRankSN x y z ∧ maxSubRankSN y z ≤ tripleRankSN x y z ∧
    (isS2StateSN x = true → maxSubRankSN (deltaSN x z) (deltaSN y z) < tripleRankSN x y z) := by
  have hall := checkNat2_sound 39 39 _ (sn_ranks_all (snIdx_lt_39 x)) (snIdx_lt_39 y) (snIdx_lt_39 z)
  have h := and_right (and_left hall)
  have hne : Nat.beq (dsnIdx (dsnIdx (dsnIdx 0 (snIdx x)) (snIdx y)) (snIdx z)) 38 = false := by
    cases hc : Nat.beq (dsnIdx (dsnIdx (dsnIdx 0 (snIdx x)) (snIdx y)) (snIdx z)) 38 with
    | false => rfl
    | true =>
      exfalso; apply hval; apply eq_of_beq_StateSN; unfold beq_StateSN
      rw [(snIdx_deltaSN _ z).1, (snIdx_deltaSN _ y).1, (snIdx_deltaSN .sn0 x).1]; exact hc
  rw [hne, Bool.false_or] at h
  refine ⟨Nat.le_of_ble_eq_true (and_left (and_left (and_left h))), Nat.le_of_ble_eq_true (and_right (and_left (and_left h))), Nat.le_of_ble_eq_true (and_right (and_left h)), fun hs2 => ?_⟩
  have h4 := imp_bool hs2 (and_right h)
  unfold maxSubRankSN tripleRankSN; rw [(snIdx_deltaSN x z).1, (snIdx_deltaSN y z).1]
  exact Nat.le_of_ble_eq_true h4

private theorem tripleRankSN_s1_lt {u y z : StateSN} (hval : deltaSN (deltaSN (deltaSN .sn0 (deltaSN .sn0 u)) y) z ≠ .sn38) :
    tripleRankSN u z (deltaSN y z) < tripleRankSN (deltaSN .sn0 u) y z := by
  have h := and_right (checkNat2_sound 39 39 _ (sn_ranks_all (snIdx_lt_39 u)) (snIdx_lt_39 y) (snIdx_lt_39 z))
  have hne : Nat.beq (dsnIdx (dsnIdx (dsnIdx 0 (dsnIdx 0 (snIdx u))) (snIdx y)) (snIdx z)) 38 = false := by
    cases hc : Nat.beq (dsnIdx (dsnIdx (dsnIdx 0 (dsnIdx 0 (snIdx u))) (snIdx y)) (snIdx z)) 38 with
    | false => rfl
    | true =>
      exfalso; apply hval; apply eq_of_beq_StateSN; unfold beq_StateSN
      rw [(snIdx_deltaSN _ z).1, (snIdx_deltaSN _ y).1, (snIdx_deltaSN .sn0 _).1, (snIdx_deltaSN .sn0 u).1]; exact hc
  rw [hne, Bool.false_or] at h
  unfold tripleRankSN; rw [(snIdx_deltaSN y z).1, (snIdx_deltaSN .sn0 u).1]
  exact Nat.le_of_ble_eq_true h

inductive CNF where | s : CNF | s1 : CNF → CNF | s2 : CNF → CNF → CNF
def CNF.toTerm : CNF → Term | .s => S | .s1 x => S ⋅ x.toTerm | .s2 x y => S ⋅ x.toTerm ⋅ y.toTerm
def CNF.size : CNF → Nat | .s => 1 | .s1 x => 1 + x.size | .s2 x y => 1 + x.size + y.size
theorem CNF.size_pos (c : CNF) : 1 ≤ c.size := by cases c <;> simp [CNF.size] <;> omega
theorem CNF.noVars_toTerm : ∀ c : CNF, noVars c.toTerm = true
  | .s => rfl | .s1 x => x.noVars_toTerm | .s2 x y => (Bool.and_eq_true _ _).mpr ⟨x.noVars_toTerm, y.noVars_toTerm⟩
theorem CNF.isNormalForm_toTerm : ∀ c : CNF, IsNormalForm c.toTerm
  | .s => fun _ hs => by cases hs
  | .s1 x => fun _ hs => by cases hs with | left hl => cases hl | right hr => exact x.isNormalForm_toTerm _ hr
  | .s2 x y => fun _ hs => by cases hs with | left hl => (cases hl with | left hll => cases hll | right hlr => exact x.isNormalForm_toTerm _ hlr) | right hr => exact y.isNormalForm_toTerm _ hr
theorem CNF.evalSN_ne_sn38 (c : CNF) : evalSN c.toTerm ≠ .sn38 := closed_nf_evalSN_ne_sn38 c.noVars_toTerm c.isNormalForm_toTerm
def cnfCallRank (f z : CNF) : Nat := match f with | .s => 0 | .s1 _ => 0 | .s2 x y => tripleRankSN (evalSN x.toTerm) (evalSN y.toTerm) (evalSN z.toTerm)
private theorem cnf_callRank_le_maxSub (f z : CNF) : cnfCallRank f z ≤ maxSubRankSN (evalSN f.toTerm) (evalSN z.toTerm) := by
  cases f with | s => exact Nat.zero_le _ | s1 _ => exact Nat.zero_le _ | s2 x y =>
    have h := and_left (and_left (checkNat2_sound 39 39 _ (sn_ranks_all (snIdx_lt_39 (evalSN x.toTerm))) (snIdx_lt_39 (evalSN y.toTerm)) (snIdx_lt_39 (evalSN z.toTerm))))
    have hx : Nat.beq (snIdx (evalSN x.toTerm)) 38 = false := by cases hc : Nat.beq (snIdx (evalSN x.toTerm)) 38 with | false => rfl | true => exact False.elim (x.evalSN_ne_sn38 (eq_of_beq_StateSN hc))
    have hy : Nat.beq (snIdx (evalSN y.toTerm)) 38 = false := by cases hc : Nat.beq (snIdx (evalSN y.toTerm)) 38 with | false => rfl | true => exact False.elim (y.evalSN_ne_sn38 (eq_of_beq_StateSN hc))
    rw [hx, hy, Bool.false_or, Bool.false_or] at h
    change trSNIdx _ _ _ ≤ msSNIdx (snIdx (deltaSN (deltaSN .sn0 (evalSN x.toTerm)) (evalSN y.toTerm))) _
    rw [(snIdx_deltaSN _ _).1, (snIdx_deltaSN .sn0 _).1]
    exact Nat.le_of_ble_eq_true h

private theorem cnf_apply_aux : ∀ (rk sz : Nat) (f z : CNF),
    evalSN (f.toTerm ⋅ z.toTerm) ≠ .sn38 → cnfCallRank f z ≤ rk → f.size ≤ sz →
    ∃ res : CNF, Reduces (f.toTerm ⋅ z.toTerm) res.toTerm ∧ (f = .s → res = .s1 z) ∧ (∀ u, f = .s1 u → res = .s2 u z) := by
  intro rk; induction rk with
  | zero =>
    intro sz f z hval hrk _; cases f with
    | s => exact ⟨.s1 z, ⟨Reduces.refl _, ⟨fun _ => rfl, fun _ h => by cases h⟩⟩⟩
    | s1 u => exact ⟨.s2 u z, ⟨Reduces.refl _, ⟨fun h => (by cases h), fun u' h => by injection h with hu; subst hu; rfl⟩⟩⟩
    | s2 x y =>
      change tripleRankSN (evalSN x.toTerm) (evalSN y.toTerm) (evalSN z.toTerm) ≤ 0 at hrk
      have ⟨hpos, _, _, _⟩ := tripleRankSN_bounds hval
      exact False.elim (by omega)
  | succ rk ihrk =>
    intro sz; induction sz with
    | zero => intro f _ _ _ hsz; exact False.elim (by have := f.size_pos; omega)
    | succ sz ihsz =>
      intro f z hval hrk hsz; cases f with
      | s => exact ⟨.s1 z, ⟨Reduces.refl _, ⟨fun _ => rfl, fun _ h => by cases h⟩⟩⟩
      | s1 u => exact ⟨.s2 u z, ⟨Reduces.refl _, ⟨fun h => (by cases h), fun u' h => by injection h with hu; subst hu; rfl⟩⟩⟩
      | s2 x y =>
        change tripleRankSN (evalSN x.toTerm) (evalSN y.toTerm) (evalSN z.toTerm) ≤ rk + 1 at hrk
        have hval_rhs : evalSN ((x.toTerm ⋅ z.toTerm) ⋅ (y.toTerm ⋅ z.toTerm)) ≠ .sn38 := fun h38 => hval ((deltaSN_s_law _ _ _).trans h38)
        have ⟨hval_xz, hval_yz⟩ := deltaSN_ne_sn38_factors hval_rhs
        have ⟨_, hA, hB, hC3⟩ := tripleRankSN_bounds hval
        have hsz_x : x.size ≤ sz := by have := y.size_pos; simp only [CNF.size] at hsz; omega
        have hsz_y : y.size ≤ sz := by have := x.size_pos; simp only [CNF.size] at hsz; omega
        obtain ⟨n1, hred1, hs0_1, hs1_1⟩ := ihsz x z hval_xz (Nat.le_trans (cnf_callRank_le_maxSub x z) (Nat.le_trans hA hrk)) hsz_x
        obtain ⟨n2, hred2, _, _⟩ := ihsz y z hval_yz (Nat.le_trans (cnf_callRank_le_maxSub y z) (Nat.le_trans hB hrk)) hsz_y
        have heq1 : evalSN n1.toTerm = deltaSN (evalSN x.toTerm) (evalSN z.toTerm) := (evalSN_reduces hred1).symm
        have heq2 : evalSN n2.toTerm = deltaSN (evalSN y.toTerm) (evalSN z.toTerm) := (evalSN_reduces hred2).symm
        have hval_12 : evalSN (n1.toTerm ⋅ n2.toTerm) ≠ .sn38 := by change deltaSN _ _ ≠ .sn38; rw [heq1, heq2]; exact hval_rhs
        have hrk_12 : cnfCallRank n1 n2 ≤ rk := by
          cases x with
          | s => rw [hs0_1 rfl]; exact Nat.zero_le _
          | s1 u =>
            rw [hs1_1 u rfl]; change tripleRankSN (evalSN u.toTerm) (evalSN z.toTerm) (evalSN n2.toTerm) ≤ rk
            rw [heq2]; have hlt : tripleRankSN (evalSN u.toTerm) (evalSN z.toTerm) (deltaSN (evalSN y.toTerm) (evalSN z.toTerm)) < tripleRankSN (evalSN (CNF.s1 u).toTerm) (evalSN y.toTerm) (evalSN z.toTerm) := tripleRankSN_s1_lt hval
            omega
          | s2 a b =>
            have hs2 := checkNat2_sound 39 39 _ isS2_sn_chk (snIdx_lt_39 (evalSN a.toTerm)) (snIdx_lt_39 (evalSN b.toTerm))
            have ha : Nat.beq (snIdx (evalSN a.toTerm)) 38 = false := by cases hc : Nat.beq (snIdx (evalSN a.toTerm)) 38 with | false => rfl | true => exact False.elim (a.evalSN_ne_sn38 (eq_of_beq_StateSN hc))
            have hb : Nat.beq (snIdx (evalSN b.toTerm)) 38 = false := by cases hc : Nat.beq (snIdx (evalSN b.toTerm)) 38 with | false => rfl | true => exact False.elim (b.evalSN_ne_sn38 (eq_of_beq_StateSN hc))
            rw [ha, hb, Bool.false_or, Bool.false_or] at hs2
            have hs2' : isS2StateSN (evalSN (CNF.s2 a b).toTerm) = true := by
              unfold isS2StateSN; change isS2SNTree.lookup (snIdx (deltaSN (deltaSN .sn0 (evalSN a.toTerm)) (evalSN b.toTerm))) = true
              rw [(snIdx_deltaSN _ _).1, (snIdx_deltaSN .sn0 _).1]; exact hs2
            have hlt := hC3 hs2'; have hsub := cnf_callRank_le_maxSub n1 n2; rw [heq1, heq2] at hsub; omega
        obtain ⟨res, hred3, _, _⟩ := ihrk n1.size n1 n2 hval_12 hrk_12 (Nat.le_refl _)
        exact ⟨res, ⟨Reduces.next (Step.root _ _ _) (reduces_trans (reduces_app hred1 hred2) hred3), ⟨fun h => (by cases h), fun _ h => by cases h⟩⟩⟩

theorem closed_evalSN_ne_sn38_reduces_cnf {t : Term} (hv : noVars t = true) (hval : evalSN t ≠ .sn38) : ∃ c : CNF, Reduces t c.toTerm := by
  induction t with
  | s => exact ⟨.s, Reduces.refl S⟩ | var _ => cases hv
  | app a b iha ihb =>
    have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv; have ⟨ha, hb⟩ := deltaSN_ne_sn38_factors hval
    obtain ⟨ca, hra⟩ := iha hva ha; obtain ⟨cb, hrb⟩ := ihb hvb hb
    have hv_ab : evalSN (ca.toTerm ⋅ cb.toTerm) ≠ .sn38 := by change deltaSN _ _ ≠ .sn38; rw [← evalSN_reduces hra, ← evalSN_reduces hrb]; exact hval
    obtain ⟨res, hrab, _, _⟩ := cnf_apply_aux (cnfCallRank ca cb) ca.size ca cb hv_ab (Nat.le_refl _) (Nat.le_refl _)
    exact ⟨res, reduces_trans (reduces_app hra hrb) hrab⟩

theorem waldmann_theorem_9_simplified {t : Term} (hv : noVars t = true) :
    (StrongNormalizing t ↔ evalSN t ≠ .sn38) ∧ (HasNormalForm t ↔ evalSN t ≠ .sn38) := by
  have hwn : HasNormalForm t ↔ evalSN t ≠ .sn38 := ⟨
    fun ⟨nf, hr, hnf⟩ => evalSN_reduces hr ▸ closed_nf_evalSN_ne_sn38 (noVars_reduces hr hv) hnf,
    fun hval => let ⟨c, hr⟩ := closed_evalSN_ne_sn38_reduces_cnf hv hval; ⟨c.toTerm, hr, c.isNormalForm_toTerm⟩⟩
  exact ⟨(sn_iff_wn t).trans hwn, hwn⟩

/-! ## 3. Simplified Open Problem 10 (`A_HN`, 35 States — `hnB ≡ 0` Potential & Global Minimality) -/

theorem ofHnIdx_hnIdx (a : StateHN) : ofHnIdx (hnIdx a) = a := by cases a <;> rfl
theorem hnIdx_lt_35 (a : StateHN) : hnIdx a < 35 := by cases a <;> decide
theorem hnIdx_ofHnIdx {i : Nat} (hi : i < 35) : hnIdx (ofHnIdx i) = i :=
  Nat.eq_of_beq_eq_true (checkNat1_sound 35 _ hnIdx_ofHnIdx_chk hi)
theorem eq_of_beq_StateHN {a b : StateHN} (h : beq_StateHN a b = true) : a = b := by
  have h2 := congrArg ofHnIdx (Nat.eq_of_beq_eq_true h); rwa [ofHnIdx_hnIdx, ofHnIdx_hnIdx] at h2
theorem ne_of_beq_StateHN_false {a b : StateHN} (h : beq_StateHN a b = false) : a ≠ b := by
  intro heq; subst heq; unfold beq_StateHN at h; rw [Nat.beq_refl] at h; cases h

theorem hnIdx_deltaHN (a b : StateHN) : hnIdx (deltaHN a b) = dhnIdx (hnIdx a) (hnIdx b) ∧ dhnIdx (hnIdx a) (hnIdx b) < 35 := by
  have h := checkNat2_sound 35 35 _ dhn_bridge_chk (hnIdx_lt_35 a) (hnIdx_lt_35 b)
  rw [ofHnIdx_hnIdx, ofHnIdx_hnIdx] at h
  exact ⟨Nat.eq_of_beq_eq_true (and_left h), Nat.le_of_ble_eq_true (and_right h)⟩

private theorem dhn_s_law_all {x : Nat} (hx : x < 35) : dhn_s_law_row x = true :=
  match x, hx with
  | 0, _ => dhn_s_law_r0 | 1, _ => dhn_s_law_r1 | 2, _ => dhn_s_law_r2 | 3, _ => dhn_s_law_r3 | 4, _ => dhn_s_law_r4
  | 5, _ => dhn_s_law_r5 | 6, _ => dhn_s_law_r6 | 7, _ => dhn_s_law_r7 | 8, _ => dhn_s_law_r8 | 9, _ => dhn_s_law_r9
  | 10, _ => dhn_s_law_r10 | 11, _ => dhn_s_law_r11 | 12, _ => dhn_s_law_r12 | 13, _ => dhn_s_law_r13 | 14, _ => dhn_s_law_r14
  | 15, _ => dhn_s_law_r15 | 16, _ => dhn_s_law_r16 | 17, _ => dhn_s_law_r17 | 18, _ => dhn_s_law_r18 | 19, _ => dhn_s_law_r19
  | 20, _ => dhn_s_law_r20 | 21, _ => dhn_s_law_r21 | 22, _ => dhn_s_law_r22 | 23, _ => dhn_s_law_r23 | 24, _ => dhn_s_law_r24
  | 25, _ => dhn_s_law_r25 | 26, _ => dhn_s_law_r26 | 27, _ => dhn_s_law_r27 | 28, _ => dhn_s_law_r28 | 29, _ => dhn_s_law_r29
  | 30, _ => dhn_s_law_r30 | 31, _ => dhn_s_law_r31 | 32, _ => dhn_s_law_r32 | 33, _ => dhn_s_law_r33 | 34, _ => dhn_s_law_r34
  | _ + 35, hbad => False.elim (by omega)
private theorem hna_valid_all {x : Nat} (hx : x < 35) : hna_valid_row x = true :=
  match x, hx with
  | 0, _ => hna_valid_r0 | 1, _ => hna_valid_r1 | 2, _ => hna_valid_r2 | 3, _ => hna_valid_r3 | 4, _ => hna_valid_r4
  | 5, _ => hna_valid_r5 | 6, _ => hna_valid_r6 | 7, _ => hna_valid_r7 | 8, _ => hna_valid_r8 | 9, _ => hna_valid_r9
  | 10, _ => hna_valid_r10 | 11, _ => hna_valid_r11 | 12, _ => hna_valid_r12 | 13, _ => hna_valid_r13 | 14, _ => hna_valid_r14
  | 15, _ => hna_valid_r15 | 16, _ => hna_valid_r16 | 17, _ => hna_valid_r17 | 18, _ => hna_valid_r18 | 19, _ => hna_valid_r19
  | 20, _ => hna_valid_r20 | 21, _ => hna_valid_r21 | 22, _ => hna_valid_r22 | 23, _ => hna_valid_r23 | 24, _ => hna_valid_r24
  | 25, _ => hna_valid_r25 | 26, _ => hna_valid_r26 | 27, _ => hna_valid_r27 | 28, _ => hna_valid_r28 | 29, _ => hna_valid_r29
  | 30, _ => hna_valid_r30 | 31, _ => hna_valid_r31 | 32, _ => hna_valid_r32 | 33, _ => hna_valid_r33 | 34, _ => hna_valid_r34
  | _ + 35, hbad => False.elim (by omega)

theorem deltaHN_s_law (x y z : StateHN) : deltaHN (deltaHN (deltaHN .hn0 x) y) z = deltaHN (deltaHN x z) (deltaHN y z) := by
  have h := Nat.eq_of_beq_eq_true (checkNat2_sound 35 35 _ (dhn_s_law_all (hnIdx_lt_35 x)) (hnIdx_lt_35 y) (hnIdx_lt_35 z))
  have hL : hnIdx (deltaHN (deltaHN (deltaHN .hn0 x) y) z) = dhnIdx (dhnIdx (dhnIdx 0 (hnIdx x)) (hnIdx y)) (hnIdx z) := by
    rw [(hnIdx_deltaHN _ z).1, (hnIdx_deltaHN _ y).1, (hnIdx_deltaHN .hn0 x).1]; rfl
  have hR : hnIdx (deltaHN (deltaHN x z) (deltaHN y z)) = dhnIdx (dhnIdx (hnIdx x) (hnIdx z)) (dhnIdx (hnIdx y) (hnIdx z)) := by
    rw [(hnIdx_deltaHN _ _).1, (hnIdx_deltaHN x z).1, (hnIdx_deltaHN y z).1]
  exact eq_of_beq_StateHN (Nat.beq_eq.mpr (hL.trans (h.trans hR.symm)))

theorem deltaHN_hn34_left (y : StateHN) : deltaHN .hn34 y = .hn34 := by
  have h := and_left (and_left (and_left (checkNat2_sound 35 35 _ hn_meta_chk (by decide : 34 < 35) (hnIdx_lt_35 y))))
  exact eq_of_beq_StateHN (by unfold beq_StateHN; rw [(hnIdx_deltaHN .hn34 y).1]; exact h)
theorem deltaHN_ne_hn34_left {x y : StateHN} (h : deltaHN x y ≠ .hn34) : x ≠ .hn34 := fun hx => h (hx ▸ deltaHN_hn34_left y)
theorem deltaHN_ne_hn0 (x y : StateHN) : deltaHN x y ≠ .hn0 := by
  intro h0; have hm := and_right (and_left (and_left (checkNat2_sound 35 35 _ hn_meta_chk (hnIdx_lt_35 x) (hnIdx_lt_35 y))))
  have heq : dhnIdx (hnIdx x) (hnIdx y) = 0 := by have := (hnIdx_deltaHN x y).1; rw [h0] at this; exact this.symm
  rw [heq] at hm; cases hm

theorem evalHN_step {a b : Term} (h : Step a b) : evalHN a = evalHN b := by
  induction h with | root _ _ _ => exact deltaHN_s_law _ _ _ | left _ ih => simp [evalHN, ih] | right _ ih => simp [evalHN, ih]
theorem evalHN_reduces {a b : Term} (h : Reduces a b) : evalHN a = evalHN b := by
  induction h with | refl _ => rfl | next hs _ ih => exact (evalHN_step hs).trans ih
theorem evalHN_conv {a b : Term} (h : ConvS a b) : evalHN a = evalHN b := by
  induction h with | refl _ => rfl | step hs => exact evalHN_step hs | symm _ ih => exact ih.symm | trans _ _ i1 i2 => exact i1.trans i2

theorem closed_spineLen_le_2_shapes {t : Term} (hv : noVars t = true) (hsl : spineLen t ≤ 2) :
    t = S ∨ (∃ x, t = S ⋅ x) ∨ (∃ x y, t = S ⋅ x ⋅ y) := by
  cases t with
  | s => exact Or.inl rfl | var _ => cases hv
  | app a b =>
    have hva := ((Bool.and_eq_true _ _).mp hv).1
    cases a with
    | s => exact Or.inr (Or.inl ⟨b, rfl⟩) | var _ => cases hva
    | app a1 y =>
      have hva1 := ((Bool.and_eq_true _ _).mp hva).1
      cases a1 with
      | s => exact Or.inr (Or.inr ⟨y, b, rfl⟩) | var _ => cases hva1
      | app a2 _ => exact False.elim (by change 1 + (1 + (1 + spineLen a2)) ≤ 2 at hsl; omega)

theorem closed_hnf_evalHN_ne_hn34 {h : Term} (hv : noVars h = true) (hsl : spineLen h ≤ 2) : evalHN h ≠ .hn34 := by
  rcases closed_spineLen_le_2_shapes hv hsl with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · exact ne_of_beq_StateHN_false rfl
  · intro h34; change deltaHN .hn0 (evalHN x) = .hn34 at h34
    have hm := and_right (and_left (checkNat2_sound 35 35 _ hn_meta_chk (hnIdx_lt_35 (evalHN x)) (by decide : 0 < 35)))
    have hs1 : dhnIdx 0 (hnIdx (evalHN x)) = 34 := by have := (hnIdx_deltaHN .hn0 (evalHN x)).1; rw [h34] at this; exact this.symm
    rw [hs1] at hm; cases hm
  · intro h34; change deltaHN (deltaHN .hn0 (evalHN x)) (evalHN y) = .hn34 at h34
    have hm := and_right (checkNat2_sound 35 35 _ hn_meta_chk (hnIdx_lt_35 (evalHN x)) (hnIdx_lt_35 (evalHN y)))
    have hs2 : dhnIdx (dhnIdx 0 (hnIdx (evalHN x))) (hnIdx (evalHN y)) = 34 := by
      have := (hnIdx_deltaHN (deltaHN .hn0 (evalHN x)) (evalHN y)).1; rw [(hnIdx_deltaHN .hn0 (evalHN x)).1, h34] at this; exact this.symm
    rw [hs2] at hm; cases hm

private theorem hnA_eq_idx (a b : StateHN) : hnA a b = hnaIdx (hnIdx a) (hnIdx b) := by
  have h := checkNat2_sound 35 35 _ hna_bridge_chk (hnIdx_lt_35 a) (hnIdx_lt_35 b)
  rw [ofHnIdx_hnIdx, ofHnIdx_hnIdx] at h; exact Nat.eq_of_beq_eq_true h

def IsValidHNA (A' : StateHN → StateHN → Nat) : Prop :=
  ∀ x y z : StateHN, deltaHN (deltaHN (deltaHN .hn0 x) y) z ≠ .hn34 →
    1 ≤ A' .hn0 x ∧
    A' (deltaHN x z) (deltaHN y z) ≤ A' (deltaHN .hn0 x) y ∧
    A' x z + A' (deltaHN x z) (deltaHN y z) * A' y z ≤ A' (deltaHN (deltaHN .hn0 x) y) z

theorem hnA_isValid : IsValidHNA hnA := by
  intro x y z hval
  have h := checkNat2_sound 35 35 _ (hna_valid_all (hnIdx_lt_35 x)) (hnIdx_lt_35 y) (hnIdx_lt_35 z)
  have hne : Nat.beq (dhnIdx (dhnIdx (dhnIdx 0 (hnIdx x)) (hnIdx y)) (hnIdx z)) 34 = false := by
    cases hc : Nat.beq (dhnIdx (dhnIdx (dhnIdx 0 (hnIdx x)) (hnIdx y)) (hnIdx z)) 34 with
    | false => rfl
    | true =>
      exfalso; apply hval; apply eq_of_beq_StateHN; unfold beq_StateHN
      rw [(hnIdx_deltaHN _ z).1, (hnIdx_deltaHN _ y).1, (hnIdx_deltaHN .hn0 x).1]; exact hc
  rw [hne, Bool.false_or] at h
  simp only [hnA_eq_idx, (hnIdx_deltaHN _ _).1]; change 1 ≤ hnaIdx 0 (hnIdx x) ∧ _
  exact ⟨Nat.le_of_ble_eq_true (and_left (and_left h)), Nat.le_of_ble_eq_true (and_right (and_left h)), Nat.le_of_ble_eq_true (and_right h)⟩

def muHN : Term → Nat
  | .s => 1 | .var _ => 1
  | .app l r => muHN l + hnA (evalHN l) (evalHN r) * muHN r

private theorem zero_b_algebra_lemma (mx my mz a0 as1 as2 ax ay auv : Nat)
    (h1 : 1 ≤ a0) (h2 : auv ≤ as1) (h3 : ax + auv * ay ≤ as2) :
    ((mx + ax * mz) + auv * (my + ay * mz)) + 1 ≤ (((1 + a0 * mx) + as1 * my) + as2 * mz) := by
  have p1 : mx ≤ a0 * mx := by have hm := Nat.mul_le_mul_right mx h1; rwa [Nat.one_mul] at hm
  have p2 : auv * my ≤ as1 * my := Nat.mul_le_mul_right my h2
  have p3 : ax * mz + (auv * ay) * mz ≤ as2 * mz := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right mz h3
  rw [Nat.mul_add auv my (ay * mz), ← Nat.mul_assoc auv ay mz]; omega

theorem muHN_headStep_drop {m m' : Term} (hs : HeadStep m m') (hval : evalHN m ≠ .hn34) : muHN m' + 1 ≤ muHN m := by
  induction hs with
  | root x y z =>
    have ⟨h1, h2, h3⟩ := hnA_isValid (evalHN x) (evalHN y) (evalHN z) hval
    exact zero_b_algebra_lemma (muHN x) (muHN y) (muHN z) _ _ _ _ _ _ h1 h2 h3
  | @left l l' r hl ih =>
    have hdrop := ih (deltaHN_ne_hn34_left hval)
    have heq : evalHN l' = evalHN l := (evalHN_step (headStep_to_step hl)).symm
    change (muHN l' + hnA (evalHN l') (evalHN r) * muHN r) + 1 ≤ muHN l + hnA (evalHN l) (evalHN r) * muHN r
    rw [heq]; omega

def headNormalizeAux : Nat → Term → Term
  | 0, t => t | fuel + 1, t => match headStepOpt t with | none => t | some t' => headNormalizeAux fuel t'

private theorem headNormalizeAux_spec : ∀ (fuel : Nat) {t : Term},
    noVars t = true → evalHN t ≠ .hn34 → muHN t < fuel →
    HeadReduces t (headNormalizeAux fuel t) ∧ IsClosedHNF (headNormalizeAux fuel t) := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ hlt; exact False.elim (by omega)
  | succ fuel ih =>
    intro t hv hval hlt; simp only [headNormalizeAux]
    cases hh : headStepOpt t with
    | none => exact ⟨HeadReduces.refl t, hv, headStepOpt_none_spineLen hv hh⟩
    | some t' =>
      have hs := headStepOpt_some hh; have hv' := noVars_step (headStep_to_step hs) hv
      have hval' : evalHN t' ≠ .hn34 := (evalHN_step (headStep_to_step hs)) ▸ hval
      have hdrop := muHN_headStep_drop hs hval
      obtain ⟨hr, hhnf⟩ := ih hv' hval' (by omega); exact ⟨HeadReduces.next hs hr, hhnf⟩

def headNormalize (t : Term) : Term := headNormalizeAux (muHN t + 1) t
theorem headNormalize_reduces_hnf {t : Term} (hv : noVars t = true) (hval : evalHN t ≠ .hn34) :
    HeadReduces t (headNormalize t) ∧ IsClosedHNF (headNormalize t) :=
  headNormalizeAux_spec (muHN t + 1) hv hval (Nat.lt_succ_self _)

inductive HeadStepsN : Nat → Term → Term → Prop where
  | zero (t : Term) : HeadStepsN 0 t t
  | succ {k : Nat} {a b c : Term} : HeadStep a b → HeadStepsN k b c → HeadStepsN (k + 1) a c

theorem evalHN_hn34_infinite_head {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) : ∀ k, ∃ u, HeadStepsN k t u := by
  intro k; induction k generalizing t with
  | zero => exact ⟨t, .zero t⟩
  | succ k ih =>
    cases hh : headStepOpt t with
    | none => exfalso; exact closed_hnf_evalHN_ne_hn34 hv (headStepOpt_none_spineLen hv hh) h34
    | some t' =>
      have hs := headStepOpt_some hh
      obtain ⟨u, hrest⟩ := ih (noVars_step (headStep_to_step hs) hv) ((evalHN_step (headStep_to_step hs)).symm.trans h34)
      exact ⟨u, .succ hs hrest⟩

theorem barendregt_open_problem_10_simplified {t : Term} (hv : noVars t = true) :
    (HasHNF t ↔ evalHN t ≠ .hn34) ∧ (evalHN t = .hn34 ↔ ∀ k, ∃ u, HeadStepsN k t u) := by
  have hhnf : HasHNF t ↔ evalHN t ≠ .hn34 := ⟨
    fun ⟨h, hr, hsl⟩ => evalHN_reduces hr ▸ closed_hnf_evalHN_ne_hn34 (noVars_reduces hr hv) hsl,
    fun hval => let ⟨hr, _, hsl⟩ := headNormalize_reduces_hnf hv hval; ⟨headNormalize t, headReduces_to_reduces hr, hsl⟩⟩
  refine ⟨hhnf, evalHN_hn34_infinite_head hv, fun hinf => ?_⟩
  cases h34 : beq_StateHN (evalHN t) .hn34 with
  | true => exact eq_of_beq_StateHN h34
  | false =>
    exfalso
    obtain ⟨u, hsteps⟩ := hinf (muHN t + 1)
    have hdrop : ∀ {k a b}, HeadStepsN k a b → evalHN a ≠ .hn34 → muHN b + k ≤ muHN a := by
      intro k a b hs; induction hs with
      | zero _ => intro _; exact Nat.le_refl _
      | @succ k0 a0 b0 _ hs0 _ ih => intro hv0; have hd1 := muHN_headStep_drop hs0 hv0; have hd2 := ih ((evalHN_step (headStep_to_step hs0)) ▸ hv0); omega
    have := hdrop hsteps (ne_of_beq_StateHN_false h34); omega

/-! ### 3.1 Single-Table DAG Certificate for Global Pointwise Minimality of `hnA` & Rank-1 Impossibility -/

private theorem hna_dag_cell_step {A' : StateHN → StateHN → Nat} (hA : IsValidHNA A')
    {lvl u v code : Nat}
    (ih : ∀ a b, a < 35 → b < 35 → hnaLvlIdx a b ≤ lvl → hnaIdx a b ≤ A' (ofHnIdx a) (ofHnIdx b))
    (hlv : hnaLvlIdx u v ≤ lvl + 1)
    (hcell : hna_dag_cell_ok u v code = true) :
    hnaIdx u v ≤ A' (ofHnIdx u) (ofHnIdx v) := by
  have h := and_right hcell
  cases h0 : Nat.beq (hnaLvlIdx u v) 0 <;> rw [h0] at h
  · rw [if_false_eq_true] at h
    have hx35 : witX code < 35 := Nat.le_of_ble_eq_true (and_left (and_left (and_left (and_left h))))
    have hy35 : witY code < 35 := Nat.le_of_ble_eq_true (and_right (and_left (and_left (and_left h))))
    have hz35 : witZ code < 35 := Nat.le_of_ble_eq_true (and_right (and_left (and_left h)))
    have hnot34 := and_right (and_left h)
    have hbody := and_right h
    have hval : deltaHN (deltaHN (deltaHN .hn0 (ofHnIdx (witX code))) (ofHnIdx (witY code))) (ofHnIdx (witZ code)) ≠ .hn34 := by
      intro hbad; have heq := congrArg hnIdx hbad
      rw [(hnIdx_deltaHN _ _).1, (hnIdx_deltaHN _ _).1, (hnIdx_deltaHN .hn0 _).1, hnIdx_ofHnIdx hx35, hnIdx_ofHnIdx hy35, hnIdx_ofHnIdx hz35] at heq
      rw [show hnIdx .hn0 = 0 from rfl, show hnIdx .hn34 = 34 from rfl] at heq
      rw [heq] at hnot34; cases hnot34
    have ⟨hv1, hv2, hv3⟩ := hA (ofHnIdx (witX code)) (ofHnIdx (witY code)) (ofHnIdx (witZ code)) hval
    have hxz35 : dhnIdx (witX code) (witZ code) < 35 := by have := (hnIdx_deltaHN (ofHnIdx (witX code)) (ofHnIdx (witZ code))).2; rwa [hnIdx_ofHnIdx hx35, hnIdx_ofHnIdx hz35] at this
    have hyz35 : dhnIdx (witY code) (witZ code) < 35 := by have := (hnIdx_deltaHN (ofHnIdx (witY code)) (ofHnIdx (witZ code))).2; rwa [hnIdx_ofHnIdx hy35, hnIdx_ofHnIdx hz35] at this
    have heq_xz : ofHnIdx (dhnIdx (witX code) (witZ code)) = deltaHN (ofHnIdx (witX code)) (ofHnIdx (witZ code)) := by
      have h1 := (hnIdx_deltaHN (ofHnIdx (witX code)) (ofHnIdx (witZ code))).1; rw [hnIdx_ofHnIdx hx35, hnIdx_ofHnIdx hz35] at h1
      have h2 := congrArg ofHnIdx h1; rw [ofHnIdx_hnIdx] at h2; exact h2.symm
    have heq_yz : ofHnIdx (dhnIdx (witY code) (witZ code)) = deltaHN (ofHnIdx (witY code)) (ofHnIdx (witZ code)) := by
      have h1 := (hnIdx_deltaHN (ofHnIdx (witY code)) (ofHnIdx (witZ code))).1; rw [hnIdx_ofHnIdx hy35, hnIdx_ofHnIdx hz35] at h1
      have h2 := congrArg ofHnIdx h1; rw [ofHnIdx_hnIdx] at h2; exact h2.symm
    cases ht1 : Nat.beq (witTag code) 1 <;> rw [ht1] at hbody
    · rw [if_false_eq_true] at hbody
      cases ht2 : Nat.beq (witTag code) 2 <;> rw [ht2] at hbody
      · rw [if_false_eq_true] at hbody
        have hu_eq : u = dhnIdx (dhnIdx 0 (witX code)) (witY code) := Nat.eq_of_beq_eq_true (and_right (and_left (and_left (and_left (and_left hbody)))))
        have hv_eq : v = witZ code := Nat.eq_of_beq_eq_true (and_right (and_left (and_left (and_left hbody))))
        have hlv_x := Nat.le_of_ble_eq_true (and_right (and_left (and_left hbody)))
        have hprod_c := and_right (and_left hbody)
        have hle_val := Nat.le_of_ble_eq_true (and_right hbody)
        have heq_s2 : ofHnIdx u = deltaHN (deltaHN .hn0 (ofHnIdx (witX code))) (ofHnIdx (witY code)) := by
          have h1 := (hnIdx_deltaHN (deltaHN .hn0 (ofHnIdx (witX code))) (ofHnIdx (witY code))).1
          rw [(hnIdx_deltaHN .hn0 (ofHnIdx (witX code))).1, show hnIdx .hn0 = 0 from rfl, hnIdx_ofHnIdx hx35, hnIdx_ofHnIdx hy35, ← hu_eq] at h1
          have h2 := congrArg ofHnIdx h1; rw [ofHnIdx_hnIdx] at h2; exact h2.symm
        have hbx := ih (witX code) (witZ code) hx35 hz35 (by omega)
        have hb_prod : hnaIdx (dhnIdx (witX code) (witZ code)) (dhnIdx (witY code) (witZ code)) * hnaIdx (witY code) (witZ code) ≤ A' (deltaHN (ofHnIdx (witX code)) (ofHnIdx (witZ code))) (deltaHN (ofHnIdx (witY code)) (ofHnIdx (witZ code))) * A' (ofHnIdx (witY code)) (ofHnIdx (witZ code)) := by
          rcases (Bool.or_eq_true _ _).mp hprod_c with hp0 | hboth
          · rw [Nat.eq_of_beq_eq_true hp0]; exact Nat.zero_le _
          · have hlv_uv := Nat.le_of_ble_eq_true (and_left hboth)
            have hlv_y := Nat.le_of_ble_eq_true (and_right hboth)
            have hbuv := ih (dhnIdx (witX code) (witZ code)) (dhnIdx (witY code) (witZ code)) hxz35 hyz35 (by omega)
            rw [heq_xz, heq_yz] at hbuv
            exact Nat.mul_le_mul hbuv (ih (witY code) (witZ code) hy35 hz35 (by omega))
        refine Nat.le_trans hle_val ?_
        rw [heq_s2, hv_eq]
        exact Nat.le_trans (Nat.add_le_add hbx hb_prod) hv3
      · rw [if_true_eq_true] at hbody
        have hu_eq : u = dhnIdx 0 (witX code) := Nat.eq_of_beq_eq_true (and_left (and_left (and_left hbody)))
        have hv_eq : v = witY code := Nat.eq_of_beq_eq_true (and_right (and_left (and_left hbody)))
        have hlv_uv := Nat.le_of_ble_eq_true (and_right (and_left hbody))
        have hle_val := Nat.le_of_ble_eq_true (and_right hbody)
        have heq_s1 : ofHnIdx u = deltaHN .hn0 (ofHnIdx (witX code)) := by
          have h1 := (hnIdx_deltaHN .hn0 (ofHnIdx (witX code))).1
          rw [show hnIdx .hn0 = 0 from rfl, hnIdx_ofHnIdx hx35, ← hu_eq] at h1
          have h2 := congrArg ofHnIdx h1; rw [ofHnIdx_hnIdx] at h2; exact h2.symm
        have hbuv := ih (dhnIdx (witX code) (witZ code)) (dhnIdx (witY code) (witZ code)) hxz35 hyz35 (by omega)
        rw [heq_xz, heq_yz] at hbuv
        refine Nat.le_trans hle_val ?_
        rw [heq_s1, hv_eq]
        exact Nat.le_trans hbuv hv2
    · rw [if_true_eq_true] at hbody
      have hu_eq : u = 0 := Nat.eq_of_beq_eq_true (and_left (and_left hbody))
      have hv_eq : v = witX code := Nat.eq_of_beq_eq_true (and_right (and_left hbody))
      have hle_val := Nat.le_of_ble_eq_true (and_right hbody)
      refine Nat.le_trans hle_val ?_
      rw [hu_eq, hv_eq]; exact hv1
  · rw [if_true_eq_true] at h; rw [Nat.eq_of_beq_eq_true h]; exact Nat.zero_le _

private theorem hna_dag_level_bound {A' : StateHN → StateHN → Nat} (hA : IsValidHNA A') :
    ∀ (lvl u v : Nat), u < 35 → v < 35 → hnaLvlIdx u v ≤ lvl → hnaIdx u v ≤ A' (ofHnIdx u) (ofHnIdx v) := by
  intro lvl; induction lvl with
  | zero =>
    intro u v hu hv hlv
    have h := and_right (checkNat2_sound 35 35 _ hna_dag_cert_chk hu hv)
    have h0 : Nat.beq (hnaLvlIdx u v) 0 = true := Nat.beq_eq.mpr (Nat.eq_zero_of_le_zero hlv)
    rw [h0, if_true_eq_true] at h; rw [Nat.eq_of_beq_eq_true h]; exact Nat.zero_le _
  | succ lvl ih =>
    intro u v hu hv hlv
    exact hna_dag_cell_step hA ih hlv (checkNat2_sound 35 35 _ hna_dag_cert_chk hu hv)

/-- **Exact Pointwise Minimality of `hnA`**: Every valid multiplier matrix `A'` satisfies `hnA u v ≤ A' u v`! -/
theorem hnA_pointwise_minimal {A' : StateHN → StateHN → Nat} (hA : IsValidHNA A') : ∀ u v : StateHN, hnA u v ≤ A' u v := by
  intro u v; rw [hnA_eq_idx u v]
  have hlv := Nat.le_of_ble_eq_true (and_left (checkNat2_sound 35 35 _ hna_dag_cert_chk (hnIdx_lt_35 u) (hnIdx_lt_35 v)))
  have hfin := hna_dag_level_bound hA 13 (hnIdx u) (hnIdx v) (hnIdx_lt_35 u) (hnIdx_lt_35 v) hlv
  rwa [ofHnIdx_hnIdx, ofHnIdx_hnIdx] at hfin

theorem hnA_max_30_optimal {A' : StateHN → StateHN → Nat} (hA : IsValidHNA A') : 30 ≤ A' .hn10 .hn0 :=
  hnA_pointwise_minimal hA .hn10 .hn0

theorem no_masked_rank1_hnA (mask : StateHN → StateHN → Bool) (wL wR : StateHN → Nat) :
    ¬ IsValidHNA (fun u v => if mask u v then wL u * wR v else 0) := by
  intro hA
  let A' := fun u v => if mask u v then wL u * wR v else 0
  have hmin := hnA_pointwise_minimal (A' := A') hA
  have h5_0  : 15 ≤ A' .hn5 .hn0  := hmin .hn5 .hn0
  have h10_1 : 15 ≤ A' .hn10 .hn1 := hmin .hn10 .hn1
  have h0_0  : 1  ≤ A' .hn0 .hn0  := hmin .hn0 .hn0
  have h10_0 : 30 ≤ A' .hn10 .hn0 := hmin .hn10 .hn0
  have hs2 := (hA .hn5 .hn0 .hn0 (ne_of_beq_StateHN_false rfl)).2.2
  change A' .hn5 .hn0 + A' .hn10 .hn1 * A' .hn0 .hn0 ≤ A' .hn10 .hn0 at hs2
  dsimp only [A'] at h5_0 h10_1 h0_0 h10_0 hs2
  cases hm1 : mask .hn5 .hn0 <;> rw [hm1] at h5_0 hs2
  · rw [if_false_eq_true] at h5_0; omega
  · rw [if_true_eq_true] at h5_0 hs2
    cases hm2 : mask .hn10 .hn1 <;> rw [hm2] at h10_1 hs2
    · rw [if_false_eq_true] at h10_1; omega
    · rw [if_true_eq_true] at h10_1 hs2
      cases hm3 : mask .hn0 .hn0 <;> rw [hm3] at h0_0 hs2
      · rw [if_false_eq_true] at h0_0; omega
      · rw [if_true_eq_true] at h0_0 hs2
        cases hm4 : mask .hn10 .hn0 <;> rw [hm4] at h10_0 hs2
        · rw [if_false_eq_true] at h10_0; omega
        · rw [if_true_eq_true] at h10_0 hs2
          have hwR0_pos : 1 ≤ wR .hn0 := by cases h : wR .hn0 with | zero => rw [h, Nat.mul_zero] at h0_0; omega | succ _ => omega
          have hw5_pos : 1 ≤ wL .hn5 := by cases h : wL .hn5 with | zero => rw [h, Nat.zero_mul] at h5_0; omega | succ _ => omega
          have hw10_1_pos : 1 ≤ wR .hn1 * wL .hn0 := by
            cases h1 : wR .hn1 with
            | zero => rw [h1, Nat.mul_zero] at h10_1; omega
            | succ _ => cases h2 : wL .hn0 with | zero => rw [h2, Nat.zero_mul] at h0_0; omega | succ _ => exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
          have hprod_ge : wL .hn10 * wR .hn0 ≤ (wL .hn10 * wR .hn1) * (wL .hn0 * wR .hn0) := by
            have heq : (wL .hn10 * wR .hn1) * (wL .hn0 * wR .hn0) = (wR .hn1 * wL .hn0) * (wL .hn10 * wR .hn0) := by
              simp only [Nat.mul_left_comm, Nat.mul_comm]
            rw [heq]; have hm := Nat.mul_le_mul_right (wL .hn10 * wR .hn0) hw10_1_pos; rwa [Nat.one_mul] at hm
          have h5_pos : 1 ≤ wL .hn5 * wR .hn0 := Nat.mul_pos hw5_pos hwR0_pos
          omega

theorem no_1d_left_hnA (wL : StateHN → Nat) : ¬ IsValidHNA (fun u _ => wL u) := by
  intro hA; exact no_masked_rank1_hnA (fun _ _ => true) wL (fun _ => 1) (fun x y z hv => by simp only [if_true, Nat.mul_one]; exact hA x y z hv)

theorem no_1d_right_hnA (wR : StateHN → Nat) : ¬ IsValidHNA (fun _ v => wR v) := by
  intro hA; exact no_masked_rank1_hnA (fun _ _ => true) (fun _ => 1) wR (fun x y z hv => by simp only [if_true, Nat.one_mul]; exact hA x y z hv)

/-! ## 4. Potential-Free `pure_s_head_escape` (via `Acc` Pullback) & Exact Böhm Sink Laws -/

inductive HasBotWithin : Nat → Term → Prop where
  | bot_div {d : Nat} {t : Term} : ¬ HasHNF t → HasBotWithin d t
  | bot_s1 {d : Nat} {t a : Term} : Reduces t (S ⋅ a) → HasBotWithin d a → HasBotWithin (d + 1) t
  | bot_s2_l {d : Nat} {t a b : Term} : Reduces t (S ⋅ a ⋅ b) → HasBotWithin d a → HasBotWithin (d + 1) t
  | bot_s2_r {d : Nat} {t a b : Term} : Reduces t (S ⋅ a ⋅ b) → HasBotWithin d b → HasBotWithin (d + 1) t

def HasBot (t : Term) : Prop := ∃ d, HasBotWithin d t
def Productive (t : Term) : Prop := ¬ HasBot t

theorem hasBotWithin_mono {d1 d2 : Nat} {t : Term} (hle : d1 ≤ d2) (h : HasBotWithin d1 t) : HasBotWithin d2 t := by
  induction h generalizing d2 with
  | bot_div hno => exact .bot_div hno
  | bot_s1 hr _ ih => cases d2 with | zero => exact False.elim (by omega) | succ _ => exact .bot_s1 hr (ih (by omega))
  | bot_s2_l hr _ ih => cases d2 with | zero => exact False.elim (by omega) | succ _ => exact .bot_s2_l hr (ih (by omega))
  | bot_s2_r hr _ ih => cases d2 with | zero => exact False.elim (by omega) | succ _ => exact .bot_s2_r hr (ih (by omega))

theorem step_preserves_spineLen_le_2 {a b : Term} (hs : Step a b) (hsl : spineLen a ≤ 2) : spineLen b ≤ 2 := by
  cases hs with
  | root _ _ _ => change 3 ≤ 2 at hsl; omega
  | @left l _ _ hl =>
    cases hl with
    | root _ _ _ => change 4 ≤ 2 at hsl; omega
    | @left ll _ _ hll => cases ll with | s => cases hll | var _ => cases hll | app u _ => change 1 + (1 + (1 + spineLen u)) ≤ 2 at hsl; omega
    | right _ => exact hsl
  | right _ => exact hsl

theorem reduces_preserves_spineLen_le_2 {a b : Term} (hr : Reduces a b) (hsl : spineLen a ≤ 2) : spineLen b ≤ 2 := by
  induction hr with | refl _ => exact hsl | next hs _ ih => exact ih (step_preserves_spineLen_le_2 hs hsl)

theorem s1_reduces_inv {m u x : Term} (h : Reduces m u) (hm : m = S ⋅ x) : ∃ x', u = S ⋅ x' ∧ Reduces x x' := by
  induction h generalizing x with
  | refl _ => exact ⟨x, hm, Reduces.refl x⟩
  | @next _ _ _ hs _ ih => subst hm; cases hs with | left hl => cases hl | right hx1 => obtain ⟨x', hu, hx'⟩ := ih rfl; exact ⟨x', hu, Reduces.next hx1 hx'⟩

theorem s2_reduces_inv {m u x y : Term} (h : Reduces m u) (hm : m = S ⋅ x ⋅ y) : ∃ x' y', u = S ⋅ x' ⋅ y' ∧ Reduces x x' ∧ Reduces y y' := by
  induction h generalizing x y with
  | refl _ => exact ⟨x, y, hm, Reduces.refl x, Reduces.refl y⟩
  | @next _ _ _ hs _ ih =>
    subst hm; cases hs with
    | left hl => cases hl with | left hll => cases hll | right hx1 => obtain ⟨x', y', hu, hx', hy'⟩ := ih rfl; exact ⟨x', y', hu, Reduces.next hx1 hx', hy'⟩
    | right hy1 => obtain ⟨x', y', hu, hx', hy'⟩ := ih rfl; exact ⟨x', y', hu, hx', Reduces.next hy1 hy'⟩

theorem hasBotWithin_backward_reduces {d : Nat} {a b : Term} (hab : Reduces a b) (hb : HasBotWithin d b) : HasBotWithin d a := by
  cases hb with
  | bot_div hno => refine .bot_div (fun ⟨h, hah, hsl⟩ => hno ?_); obtain ⟨u, hbu, hhu⟩ := church_rosser hab hah; exact ⟨u, hbu, reduces_preserves_spineLen_le_2 hhu hsl⟩
  | bot_s1 hr ha => exact .bot_s1 (reduces_trans hab hr) ha
  | bot_s2_l hr ha => exact .bot_s2_l (reduces_trans hab hr) ha
  | bot_s2_r hr ha => exact .bot_s2_r (reduces_trans hab hr) ha

theorem hasBotWithin_forward_reduces {d : Nat} {a b : Term} (hab : Reduces a b) (ha : HasBotWithin d a) : HasBotWithin d b := by
  induction ha generalizing b with
  | bot_div hno => exact .bot_div (fun ⟨h, hbh, hsl⟩ => hno ⟨h, reduces_trans hab hbh, hsl⟩)
  | bot_s1 hr _ ih => obtain ⟨u, hbu, hsu⟩ := church_rosser hab hr; obtain ⟨x', rfl, hxx'⟩ := s1_reduces_inv hsu rfl; exact .bot_s1 hbu (ih hxx')
  | bot_s2_l hr _ ih => obtain ⟨u, hbu, hsu⟩ := church_rosser hab hr; obtain ⟨x', y', rfl, hxx', _⟩ := s2_reduces_inv hsu rfl; exact .bot_s2_l hbu (ih hxx')
  | bot_s2_r hr _ ih => obtain ⟨u, hbu, hsu⟩ := church_rosser hab hr; obtain ⟨x', y', rfl, _, hyy'⟩ := s2_reduces_inv hsu rfl; exact .bot_s2_r hbu (ih hyy')

theorem productive_conv_invariant {a b : Term} (hconv : ConvS a b) : Productive a ↔ Productive b := by
  have hinv : ∀ {d x y}, ConvS x y → (HasBotWithin d x ↔ HasBotWithin d y) := by
    intro d x y hc; induction hc with
    | refl _ => exact Iff.rfl
    | step hs => have hr := Reduces.next hs (Reduces.refl _); exact ⟨hasBotWithin_forward_reduces hr, hasBotWithin_backward_reduces hr⟩
    | symm _ ih => exact ih.symm | trans _ _ i1 i2 => exact i1.trans i2
  exact ⟨fun hp ⟨d, hb⟩ => hp ⟨d, (hinv hconv).mpr hb⟩, fun hp ⟨d, ha⟩ => hp ⟨d, (hinv hconv).mp ha⟩⟩

theorem closed_evalHN_hn34_hasBot0 {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) : HasBotWithin 0 t :=
  .bot_div (fun hh => ((barendregt_open_problem_10_simplified hv).1.mp hh) h34)

theorem closed_not_hasHNF_evalHN_hn34 {t : Term} (hv : noVars t = true) (hno : ¬ HasHNF t) : evalHN t = .hn34 := by
  cases h34 : beq_StateHN (evalHN t) .hn34 with
  | true => exact eq_of_beq_StateHN h34
  | false => exact False.elim (hno ((barendregt_open_problem_10_simplified hv).1.mpr (ne_of_beq_StateHN_false h34)))

def onlyVar0 : Term → Bool | .s => true | .var k => Nat.beq k 0 | .app a b => onlyVar0 a && onlyVar0 b
def isVar0Leaf : Term → Bool | .var 0 => true | _ => false
def hasXSpine : Term → Bool | .s => false | .var k => Nat.beq k 0 | .app a b => hasXSpine a || isVar0Leaf (headLeaf b)

theorem isVar0Leaf_iff (t : Term) : isVar0Leaf t = true ↔ t = .var 0 := by
  cases t with | s => simp [isVar0Leaf] | app _ _ => simp [isVar0Leaf] | var k => cases k with | zero => simp [isVar0Leaf] | succ _ => simp [isVar0Leaf]

theorem noVars_implies_onlyVar0 {t : Term} (hv : noVars t = true) : onlyVar0 t = true := by
  induction t with | s => rfl | var _ => cases hv | app _ _ iha ihb => have ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp hv; exact (Bool.and_eq_true _ _).mpr ⟨iha ha, ihb hb⟩

theorem onlyVar0_headStep {a b : Term} (hs : HeadStep a b) : onlyVar0 a = true → onlyVar0 b = true := by
  induction hs with
  | root _ _ _ => simp only [S, onlyVar0, Bool.and_eq_true]; intro ⟨⟨⟨_, hx⟩, hy⟩, hz⟩; exact ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
  | left _ ih => simp only [onlyVar0, Bool.and_eq_true]; intro ⟨ha, hb⟩; exact ⟨ih ha, hb⟩

theorem hasXSpine_of_headLeaf_var0 {t : Term} (h : headLeaf t = .var 0) : hasXSpine t = true := by
  induction t with
  | s => cases h
  | var k => change headLeaf (.var k) = .var 0 at h; injection h with hk; subst hk; rfl
  | app _ _ iha _ => exact (Bool.or_eq_true _ _).mpr (Or.inl (iha h))

theorem hasXSpine_headStep {a b : Term} (hs : HeadStep a b) : hasXSpine a = true → hasXSpine b = true := by
  induction hs with
  | root x y z =>
    intro h; simp only [S, hasXSpine, Bool.false_or, Bool.or_eq_true] at h
    rcases h with (hx | hy) | hz
    · exact hasXSpine_of_headLeaf_var0 (t := (x ⋅ z) ⋅ (y ⋅ z)) ((isVar0Leaf_iff _).mp hx)
    · have hy0 := (isVar0Leaf_iff _).mp hy
      have hyz : isVar0Leaf (headLeaf (y ⋅ z)) = true := (isVar0Leaf_iff _).mpr hy0
      exact (Bool.or_eq_true _ _).mpr (Or.inr hyz)
    · exact (Bool.or_eq_true _ _).mpr (Or.inl ((Bool.or_eq_true _ _).mpr (Or.inr hz)))
  | left _ ih => intro h; rcases (Bool.or_eq_true _ _).mp h with ha | hb; exact (Bool.or_eq_true _ _).mpr (Or.inl (ih ha)); exact (Bool.or_eq_true _ _).mpr (Or.inr hb)

theorem subst_headStep (σ : Nat → Term) {a b : Term} (hs : HeadStep a b) : HeadStep (subst σ a) (subst σ b) := by
  induction hs with | root _ _ _ => exact .root _ _ _ | left _ ih => exact .left ih

theorem subst_headReduces (σ : Nat → Term) {a b : Term} (hr : HeadReduces a b) : HeadReduces (subst σ a) (subst σ b) := by
  induction hr with | refl _ => exact .refl _ | next hs _ ih => exact .next (subst_headStep σ hs) ih

theorem shn_of_subst (σ : Nat → Term) {u : Term} (h : StrongHeadNormalizing (subst σ u)) : StrongHeadNormalizing u := by
  generalize heq : subst σ u = m at h
  induction h generalizing u with | intro _ _ ih => exact Acc.intro u (fun u' hs => ih (subst σ u') (heq ▸ subst_headStep σ hs) rfl)

theorem open_hnf_dichotomy {u : Term} (hov : onlyVar0 u = true) (hnone : headStepOpt u = none) :
    headLeaf u = .var 0 ∨ u = S ∨ (∃ a, u = S ⋅ a) ∨ (∃ a b, u = S ⋅ a ⋅ b) := by
  induction u with
  | s => exact Or.inr (Or.inl rfl)
  | var k => have hk := Nat.eq_of_beq_eq_true hov; subst hk; exact Or.inl rfl
  | app a b iha _ =>
    have ⟨hova, _⟩ := (Bool.and_eq_true _ _).mp hov; simp only [headStepOpt] at hnone
    cases hr : rootRedexOpt a b with
    | some _ => rw [hr] at hnone; cases hnone
    | none =>
      rw [hr] at hnone; cases ha : headStepOpt a with
      | some _ => rw [ha] at hnone; cases hnone
      | none =>
        rcases iha hova ha with hl0 | rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
        · exact Or.inl hl0
        · exact Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨x, b, rfl⟩))
        · exfalso; exact rootRedexOpt_none hr x y rfl

theorem pure_s_head_escape {f w : Term} (hvf : noVars f = true) (hvw : noVars w = true) (hval : evalHN (f ⋅ w) ≠ .hn34) :
    ∃ uStar, HeadReduces (f ⋅ .var 0) uStar ∧
      (headLeaf uStar = .var 0 ∨ (∃ a, uStar = S ⋅ a ∧ headLeaf a = .var 0) ∨
       (∃ a b, uStar = S ⋅ a ⋅ b ∧ (headLeaf a = .var 0 ∨ headLeaf b = .var 0))) := by
  let σ : Nat → Term := fun _ => w
  have hvfw : noVars (f ⋅ w) = true := (Bool.and_eq_true _ _).mpr ⟨hvf, hvw⟩
  have hhnf_fw : HasHNF (f ⋅ w) := (barendregt_open_problem_10_simplified hvfw).1.mpr hval
  have hsub_eq : subst σ (f ⋅ .var 0) = f ⋅ w := by change subst σ f ⋅ w = f ⋅ w; rw [subst_noVars σ f hvf]
  have hshn_open : StrongHeadNormalizing (f ⋅ .var 0) :=
    shn_of_subst σ (hsub_eq.symm ▸ hasHNF_implies_strongHeadNormalizing hhnf_fw)
  obtain ⟨uStar, hred, hnone⟩ := shn_reduces_hnf hshn_open
  have hpres : ∀ {a b}, HeadReduces a b → onlyVar0 a = true → hasXSpine a = true → onlyVar0 b = true ∧ hasXSpine b = true := by
    intro a b hr; induction hr with
    | refl _ => exact fun h1 h2 => ⟨h1, h2⟩
    | next hs _ ih => exact fun h1 h2 => ih (onlyVar0_headStep hs h1) (hasXSpine_headStep hs h2)
  have ⟨hov_s, hxs_s⟩ := hpres hred ((Bool.and_eq_true _ _).mpr ⟨noVars_implies_onlyVar0 hvf, rfl⟩) ((Bool.or_eq_true _ _).mpr (Or.inr rfl))
  refine ⟨uStar, hred, ?_⟩
  rcases open_hnf_dichotomy hov_s hnone with hl0 | heq_s | ⟨a, heq1⟩ | ⟨a, b, heq2⟩
  · exact Or.inl hl0
  · rw [heq_s] at hxs_s; cases hxs_s
  · rw [heq1] at hxs_s; simp only [S, hasXSpine, Bool.false_or] at hxs_s
    exact Or.inr (Or.inl ⟨a, heq1, (isVar0Leaf_iff _).mp hxs_s⟩)
  · rw [heq2] at hxs_s; simp only [S, hasXSpine, Bool.false_or, Bool.or_eq_true] at hxs_s
    rcases hxs_s with ha | hb
    · exact Or.inr (Or.inr ⟨a, b, heq2, Or.inl ((isVar0Leaf_iff _).mp ha)⟩)
    · exact Or.inr (Or.inr ⟨a, b, heq2, Or.inr ((isVar0Leaf_iff _).mp hb)⟩)

theorem noVars_subst_closed {w : Term} (hw : noVars w = true) : ∀ u : Term, noVars (subst (fun _ => w) u) = true
  | .s => rfl | .var _ => hw | .app a b => (Bool.and_eq_true _ _).mpr ⟨noVars_subst_closed hw a, noVars_subst_closed hw b⟩

private theorem headLeaf_var0_subst_bot {d : Nat}
    (hleft : ∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin d y → HasBotWithin d (y ⋅ z))
    {w : Term} (hvw : noVars w = true) (hbw : HasBotWithin d w) :
    ∀ u : Term, headLeaf u = .var 0 → HasBotWithin d (subst (fun _ => w) u)
  | .s, h => by cases h
  | .var _, _ => hbw
  | .app a b, hl => hleft (noVars_subst_closed hvw a) (noVars_subst_closed hvw b) (headLeaf_var0_subst_bot hleft hvw hbw a hl)

private theorem right_sink_from_left_sink {d : Nat}
    (hleft : ∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin d y → HasBotWithin d (y ⋅ z))
    {f w : Term} (hvf : noVars f = true) (hvw : noVars w = true) (hbw : HasBotWithin d w) : HasBotWithin (d + 1) (f ⋅ w) := by
  cases h34 : beq_StateHN (evalHN (f ⋅ w)) .hn34
  · obtain ⟨uStar, hred_open, hcases⟩ := pure_s_head_escape hvf hvw (ne_of_beq_StateHN_false h34)
    let σ : Nat → Term := fun _ => w
    have hred_closed : Reduces (f ⋅ w) (subst σ uStar) := by
      have hr := headReduces_to_reduces (subst_headReduces σ hred_open)
      have heq : subst σ (f ⋅ .var 0) = f ⋅ w := by change subst σ f ⋅ w = f ⋅ w; rw [subst_noVars σ f hvf]
      rwa [heq] at hr
    rcases hcases with hl0 | ⟨a, rfl, hla⟩ | ⟨a, b, rfl, hla | hlb⟩
    · exact hasBotWithin_mono (Nat.le_succ d) (hasBotWithin_backward_reduces hred_closed (headLeaf_var0_subst_bot hleft hvw hbw uStar hl0))
    · exact .bot_s1 hred_closed (headLeaf_var0_subst_bot hleft hvw hbw a hla)
    · exact .bot_s2_l hred_closed (headLeaf_var0_subst_bot hleft hvw hbw a hla)
    · exact .bot_s2_r hred_closed (headLeaf_var0_subst_bot hleft hvw hbw b hlb)
  · exact hasBotWithin_mono (Nat.zero_le _) (closed_evalHN_hn34_hasBot0 ((Bool.and_eq_true _ _).mpr ⟨hvf, hvw⟩) (eq_of_beq_StateHN h34))

private theorem both_sink_laws : ∀ d : Nat,
    (∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin d y → HasBotWithin d (y ⋅ z)) ∧
    (∀ {f w : Term}, noVars f = true → noVars w = true → HasBotWithin d w → HasBotWithin (d + 1) (f ⋅ w))
  | 0 =>
    have hl0 : ∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin 0 y → HasBotWithin 0 (y ⋅ z) := by
      intro y z hvy hvz hby; cases hby with | bot_div hno =>
        have h34y := closed_not_hasHNF_evalHN_hn34 hvy hno
        have h34yz : evalHN (y ⋅ z) = .hn34 := by change deltaHN (evalHN y) (evalHN z) = .hn34; rw [h34y]; rfl
        exact closed_evalHN_hn34_hasBot0 ((Bool.and_eq_true _ _).mpr ⟨hvy, hvz⟩) h34yz
    ⟨hl0, fun hvf hvw hbw => right_sink_from_left_sink hl0 hvf hvw hbw⟩
  | d + 1 =>
    let ⟨ihl, ihr⟩ := both_sink_laws d
    have hls : ∀ {y z : Term}, noVars y = true → noVars z = true → HasBotWithin (d + 1) y → HasBotWithin (d + 1) (y ⋅ z) := by
      intro y z hvy hvz hby; have hvyz : noVars (y ⋅ z) = true := (Bool.and_eq_true _ _).mpr ⟨hvy, hvz⟩
      cases hby with
      | bot_div hno =>
        have h34y := closed_not_hasHNF_evalHN_hn34 hvy hno
        have h34yz : evalHN (y ⋅ z) = .hn34 := by change deltaHN (evalHN y) (evalHN z) = .hn34; rw [h34y]; rfl
        exact hasBotWithin_mono (Nat.zero_le _) (closed_evalHN_hn34_hasBot0 hvyz h34yz)
      | bot_s1 hr hba => exact .bot_s2_l (reduces_left hr z) hba
      | @bot_s2_l _ _ a b hr hba =>
        have ⟨hsa, hvb⟩ := (Bool.and_eq_true _ _).mp (noVars_reduces hr hvy); have ⟨_, hva⟩ := (Bool.and_eq_true _ _).mp hsa
        have hstep : Reduces (y ⋅ z) ((a ⋅ z) ⋅ (b ⋅ z)) := reduces_trans (reduces_left hr z) (.next (.root a b z) (.refl _))
        exact hasBotWithin_mono (Nat.le_succ d) (hasBotWithin_backward_reduces hstep (ihl ((Bool.and_eq_true _ _).mpr ⟨hva, hvz⟩) ((Bool.and_eq_true _ _).mpr ⟨hvb, hvz⟩) (ihl hva hvz hba)))
      | @bot_s2_r _ _ a b hr hbb =>
        have ⟨hsa, hvb⟩ := (Bool.and_eq_true _ _).mp (noVars_reduces hr hvy); have ⟨_, hva⟩ := (Bool.and_eq_true _ _).mp hsa
        have hstep : Reduces (y ⋅ z) ((a ⋅ z) ⋅ (b ⋅ z)) := reduces_trans (reduces_left hr z) (.next (.root a b z) (.refl _))
        exact hasBotWithin_backward_reduces hstep (ihr ((Bool.and_eq_true _ _).mpr ⟨hva, hvz⟩) ((Bool.and_eq_true _ _).mpr ⟨hvb, hvz⟩) (ihl hvb hvz hbb))
    ⟨hls, fun hvf hvw hbw => right_sink_from_left_sink hls hvf hvw hbw⟩

theorem hasBotWithin_app_left {d : Nat} {y z : Term} (hvy : noVars y = true) (hvz : noVars z = true) (h : HasBotWithin d y) : HasBotWithin d (y ⋅ z) :=
  (both_sink_laws d).1 hvy hvz h

theorem hasBotWithin_app_right {d : Nat} {f w : Term} (hvf : noVars f = true) (hvw : noVars w = true) (h : HasBotWithin d w) : HasBotWithin (d + 1) (f ⋅ w) :=
  (both_sink_laws d).2 hvf hvw h

end SimplifiedQ10Q5

#print axioms SimplifiedQ10Q5.head_conservation_step
#print axioms SimplifiedQ10Q5.hasHNF_iff_strongHeadNormalizing
#print axioms SimplifiedQ10Q5.waldmann_theorem_9_simplified
#print axioms SimplifiedQ10Q5.barendregt_open_problem_10_simplified
#print axioms SimplifiedQ10Q5.hnA_pointwise_minimal
#print axioms SimplifiedQ10Q5.hnA_max_30_optimal
#print axioms SimplifiedQ10Q5.no_masked_rank1_hnA
#print axioms SimplifiedQ10Q5.no_1d_left_hnA
#print axioms SimplifiedQ10Q5.no_1d_right_hnA
#print axioms SimplifiedQ10Q5.pure_s_head_escape
#print axioms SimplifiedQ10Q5.hasBotWithin_app_left
#print axioms SimplifiedQ10Q5.hasBotWithin_app_right
