import formal_q5_final.chunks.q5_chunk_00
import formal_q5_final.chunks.q5_chunk_01
import formal_q5_final.chunks.q5_chunk_02
import formal_q5_final.chunks.q5_chunk_03
import formal_q5_final.chunks.q5_chunk_04
import formal_q5_final.chunks.q5_chunk_05
import formal_q5_final.chunks.q5_chunk_06
import formal_q5_final.chunks.q5_chunk_07
import formal_q5_final.chunks.q5_chunk_08
import formal_q5_final.chunks.q5_chunk_09
import formal_q5_final.chunks.q5_chunk_10
import formal_q5_final.chunks.q5_chunk_11
import formal_q5_final.chunks.q5_chunk_12
import formal_q5_final.chunks.q5_chunk_13
import formal_q5_final.chunks.q5_chunk_14
import formal_q5_final.chunks.q5_chunk_15

namespace FormalQ5Final
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
open FormalAlgebra Q5SNStratifiedGame

theorem phIdx_deltaPH {a b : PH} (ha : isReachPH a = true) (hb : isReachPH b = true) :
    phIdx (deltaPH a b) = dphIdx (phIdx a) (phIdx b) := by
  have hrow : dph_bridge_row a.1 = true :=
    match a.1 with
    | .p0 => dph_bridge_p0 | .p1 => dph_bridge_p1 | .p2 => dph_bridge_p2
    | .p3 => dph_bridge_p3 | .p4 => dph_bridge_p4 | .p5 => dph_bridge_p5
    | .p6 => dph_bridge_p6 | .p7 => dph_bridge_p7 | .p8 => dph_bridge_p8
    | .p9 => dph_bridge_p9 | .p10 => dph_bridge_p10 | .p11 => dph_bridge_p11
    | .p12 => dph_bridge_p12 | .p13 => dph_bridge_p13 | .p14 => dph_bridge_p14
    | .p15 => dph_bridge_p15 | .p16 => dph_bridge_p16 | .p17 => dph_bridge_p17
    | .p18 => dph_bridge_p18 | .p19 => dph_bridge_p19 | .p20 => dph_bridge_p20
    | .p21 => dph_bridge_p21 | .p22 => dph_bridge_p22 | .p23 => dph_bridge_p23
    | .p24 => dph_bridge_p24 | .p25 => dph_bridge_p25 | .p26 => dph_bridge_p26
    | .p27 => dph_bridge_p27 | .p28 => dph_bridge_p28 | .p29 => dph_bridge_p29
    | .p30 => dph_bridge_p30 | .p31 => dph_bridge_p31 | .p32 => dph_bridge_p32
    | .p33 => dph_bridge_p33 | .p34 => dph_bridge_p34 | .p35 => dph_bridge_p35
    | .p36 => dph_bridge_p36 | .p37 => dph_bridge_p37 | .p38 => dph_bridge_p38
  have h1 := allListHN_mem hrow (mem_jointHNs ha)
  exact Nat.eq_of_beq_eq_true (checkReach1_PH_sound _ h1 b hb)

theorem kindPH_s1 (q : PH) (ha : isAccPH q = true) :
    isAccPH (deltaPH ph0 q) = true ∧ kindPH (deltaPH ph0 q) = 1 := by
  have ⟨hr, _⟩ := (Bool.and_eq_true _ _).mp ha
  have hu := reach_1d_unpack hr
  have hai : isAccIdx (phIdx q) = true := by rw [← hu.2.2.1]; exact ha
  have ⟨hs1_acc, hs1_k⟩ := hu.2.2.2.2.2 hai
  have hrs1 : isReachPH (deltaPH ph0 q) = true := isReachPH_deltaPH (by rfl) hr
  have heq_idx : phIdx (deltaPH ph0 q) = dphIdx 0 (phIdx q) := phIdx_deltaPH (by rfl) hr
  have hu_s1 := reach_1d_unpack hrs1
  refine ⟨?_, ?_⟩
  · rw [hu_s1.2.2.1, heq_idx]; exact hs1_acc
  · unfold kindPH; rw [heq_idx]; exact hs1_k

theorem out2d_2d_idx_at {x y : Nat} (hx : x < 95) (hy : y < 95) :
    let s1 := dphIdx 0 x; let s2 := dphIdx s1 y
    isAccIdx s2 = true ∧ kindIdx s2 = 2 ∧
    memNat (95 * x + y) (out2dListIdx s1 y) = true ∧
    (let f0 := dphIdx (dphIdx 0 0) x; let n1 := dphIdx 0 y; let n2 := dphIdx x y
     (isAccIdx f0 && isAccIdx (dphIdx f0 y) && !(isZachosIdx f0 && isZachosIdx y) && !(isZachosIdx n1 && isZachosIdx n2)) = true →
       isAccIdx n2 = true ∧ memNat (95 * y + n2) (out2dListIdx f0 y) = true) := by
  have hthm : out2d_2d_idx_ok = true := out2d_2d_idx_thm
  unfold out2d_2d_idx_ok at hthm
  have hx_row := checkNat_sound hthm hx
  have hxy := checkNat_sound hx_row hy
  dsimp only [] at hxy
  have ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp hxy
  have ⟨h2, h3'⟩ := (Bool.and_eq_true _ _).mp h3
  have ⟨h1, h2'⟩ := (Bool.and_eq_true _ _).mp h2
  refine ⟨h1, Nat.eq_of_beq_eq_true h2', h3', fun hc0 => ?_⟩
  rw [hc0, if_true_eq_true] at h4; exact (Bool.and_eq_true _ _).mp h4

theorem kindPH_s2 (x y : PH) (hx : isAccPH x = true) (hy : isAccPH y = true) :
    isAccPH (deltaPH (deltaPH ph0 x) y) = true ∧ kindPH (deltaPH (deltaPH ph0 x) y) = 2 := by
  have ⟨hrx, _⟩ := (Bool.and_eq_true _ _).mp hx; have ⟨hry, _⟩ := (Bool.and_eq_true _ _).mp hy
  have h := out2d_2d_idx_at (phIdx_lt_95 hx) (phIdx_lt_95 hy)
  have hrs1 : isReachPH (deltaPH ph0 x) = true := isReachPH_deltaPH (by rfl) hrx
  have hrs2 : isReachPH (deltaPH (deltaPH ph0 x) y) = true := isReachPH_deltaPH hrs1 hry
  have hi1 : phIdx (deltaPH ph0 x) = dphIdx 0 (phIdx x) := phIdx_deltaPH (by rfl) hrx
  have hi2 : phIdx (deltaPH (deltaPH ph0 x) y) = dphIdx (dphIdx 0 (phIdx x)) (phIdx y) := by
    rw [phIdx_deltaPH hrs1 hry, hi1]
  rw [(reach_1d_unpack hrs2).2.2.1, hi2]; unfold kindPH; rw [hi2]
  exact ⟨h.1, h.2.1⟩

theorem rankP_ok_chk (x y z : StateP) : rankP_ok_fn x y z = true :=
  match x with
  | .p0 => checkAll2_StateP_sound _ rankP_ok_r0 y z | .p1 => checkAll2_StateP_sound _ rankP_ok_r1 y z | .p2 => checkAll2_StateP_sound _ rankP_ok_r2 y z
  | .p3 => checkAll2_StateP_sound _ rankP_ok_r3 y z | .p4 => checkAll2_StateP_sound _ rankP_ok_r4 y z | .p5 => checkAll2_StateP_sound _ rankP_ok_r5 y z
  | .p6 => checkAll2_StateP_sound _ rankP_ok_r6 y z | .p7 => checkAll2_StateP_sound _ rankP_ok_r7 y z | .p8 => checkAll2_StateP_sound _ rankP_ok_r8 y z
  | .p9 => checkAll2_StateP_sound _ rankP_ok_r9 y z | .p10 => checkAll2_StateP_sound _ rankP_ok_r10 y z | .p11 => checkAll2_StateP_sound _ rankP_ok_r11 y z
  | .p12 => checkAll2_StateP_sound _ rankP_ok_r12 y z | .p13 => checkAll2_StateP_sound _ rankP_ok_r13 y z | .p14 => checkAll2_StateP_sound _ rankP_ok_r14 y z
  | .p15 => checkAll2_StateP_sound _ rankP_ok_r15 y z | .p16 => checkAll2_StateP_sound _ rankP_ok_r16 y z | .p17 => checkAll2_StateP_sound _ rankP_ok_r17 y z
  | .p18 => checkAll2_StateP_sound _ rankP_ok_r18 y z | .p19 => checkAll2_StateP_sound _ rankP_ok_r19 y z | .p20 => checkAll2_StateP_sound _ rankP_ok_r20 y z
  | .p21 => checkAll2_StateP_sound _ rankP_ok_r21 y z | .p22 => checkAll2_StateP_sound _ rankP_ok_r22 y z | .p23 => checkAll2_StateP_sound _ rankP_ok_r23 y z
  | .p24 => checkAll2_StateP_sound _ rankP_ok_r24 y z | .p25 => checkAll2_StateP_sound _ rankP_ok_r25 y z | .p26 => checkAll2_StateP_sound _ rankP_ok_r26 y z
  | .p27 => checkAll2_StateP_sound _ rankP_ok_r27 y z | .p28 => checkAll2_StateP_sound _ rankP_ok_r28 y z | .p29 => checkAll2_StateP_sound _ rankP_ok_r29 y z
  | .p30 => checkAll2_StateP_sound _ rankP_ok_r30 y z | .p31 => checkAll2_StateP_sound _ rankP_ok_r31 y z | .p32 => checkAll2_StateP_sound _ rankP_ok_r32 y z
  | .p33 => checkAll2_StateP_sound _ rankP_ok_r33 y z | .p34 => checkAll2_StateP_sound _ rankP_ok_r34 y z | .p35 => checkAll2_StateP_sound _ rankP_ok_r35 y z
  | .p36 => checkAll2_StateP_sound _ rankP_ok_r36 y z | .p37 => checkAll2_StateP_sound _ rankP_ok_r37 y z | .p38 => checkAll2_StateP_sound _ rankP_ok_r38 y z

theorem out2d_s1_mem (u w : PH) (hu : isAccPH u = true) (hw : isAccPH w = true)
    (_hfw : isAccPH (deltaPH (deltaPH ph0 u) w) = true) : out2dHas (deltaPH ph0 u) w u w = true := by
  have ⟨hru, _⟩ := (Bool.and_eq_true _ _).mp hu
  have h := out2d_2d_idx_at (phIdx_lt_95 hu) (phIdx_lt_95 hw)
  have hi1 : phIdx (deltaPH ph0 u) = dphIdx 0 (phIdx u) := phIdx_deltaPH (by rfl) hru
  unfold out2dHas out2dList; rw [hu, hw, hi1]; exact h.2.2.1

theorem out2d_s2_a0 (b w : PH) (hb : isAccPH b = true) (hw : isAccPH w = true)
    (hf : isAccPH (deltaPH (deltaPH ph0 ph0) b) = true)
    (hfw : isAccPH (deltaPH (deltaPH (deltaPH ph0 ph0) b) w) = true)
    (hnz1 : !(isZachosPH (deltaPH (deltaPH ph0 ph0) b) && isZachosPH w) = true)
    (hnz2 : !(isZachosPH (deltaPH ph0 w) && isZachosPH (deltaPH b w)) = true) :
    out2dHas (deltaPH (deltaPH ph0 ph0) b) w w (deltaPH b w) = true := by
  have ⟨hrb, _⟩ := (Bool.and_eq_true _ _).mp hb; have ⟨hrw, _⟩ := (Bool.and_eq_true _ _).mp hw
  have h := out2d_2d_idx_at (phIdx_lt_95 hb) (phIdx_lt_95 hw)
  have hrf : isReachPH (deltaPH (deltaPH ph0 ph0) b) = true := isReachPH_deltaPH (by rfl) hrb
  have hrfw : isReachPH (deltaPH (deltaPH (deltaPH ph0 ph0) b) w) = true := isReachPH_deltaPH hrf hrw
  have hrn1 : isReachPH (deltaPH ph0 w) = true := isReachPH_deltaPH (by rfl) hrw
  have hrn2 : isReachPH (deltaPH b w) = true := isReachPH_deltaPH hrb hrw
  have hif : phIdx (deltaPH (deltaPH ph0 ph0) b) = dphIdx (dphIdx 0 0) (phIdx b) := phIdx_deltaPH (by rfl) hrb
  have hifw : phIdx (deltaPH (deltaPH (deltaPH ph0 ph0) b) w) = dphIdx (dphIdx (dphIdx 0 0) (phIdx b)) (phIdx w) := by rw [phIdx_deltaPH hrf hrw, hif]
  have hin1 : phIdx (deltaPH ph0 w) = dphIdx 0 (phIdx w) := phIdx_deltaPH (by rfl) hrw
  have hin2 : phIdx (deltaPH b w) = dphIdx (phIdx b) (phIdx w) := phIdx_deltaPH hrb hrw
  have hcond : (isAccIdx (dphIdx (dphIdx 0 0) (phIdx b)) && isAccIdx (dphIdx (dphIdx (dphIdx 0 0) (phIdx b)) (phIdx w)) &&
      !(isZachosIdx (dphIdx (dphIdx 0 0) (phIdx b)) && isZachosIdx (phIdx w)) &&
      !(isZachosIdx (dphIdx 0 (phIdx w)) && isZachosIdx (dphIdx (phIdx b) (phIdx w)))) = true := by
    rw [← hifw, ← hif, ← hin1, ← hin2, ← (reach_1d_unpack hrf).2.2.1, ← (reach_1d_unpack hrfw).2.2.1,
        ← (reach_1d_unpack hrf).2.2.2.2.1, ← (reach_1d_unpack hrw).2.2.2.2.1,
        ← (reach_1d_unpack hrn1).2.2.2.2.1, ← (reach_1d_unpack hrn2).2.2.2.2.1,
        hf, hfw]
    cases hz1 : (isZachosPH (deltaPH (deltaPH ph0 ph0) b) && isZachosPH w)
    · cases hz2 : (isZachosPH (deltaPH ph0 w) && isZachosPH (deltaPH b w))
      · rfl
      · rw [hz2] at hnz2; cases hnz2
    · rw [hz1] at hnz1; cases hnz1
  have ⟨hn2_acc, hmem⟩ := h.2.2.2 hcond
  unfold out2dHas out2dList
  rw [hw, (reach_1d_unpack hrn2).2.2.1, hin2, hif, hn2_acc]; exact hmem

theorem out2d_trans_idx_all {a : Nat} (ha : a < 95) : out2d_trans_idx_row a = true :=
  match a, ha with
  | 0, _ => out2d_trans_r0
  | 1, _ => out2d_trans_r1
  | 2, _ => out2d_trans_r2
  | 3, _ => out2d_trans_r3
  | 4, _ => out2d_trans_r4
  | 5, _ => out2d_trans_r5
  | 6, _ => out2d_trans_r6
  | 7, _ => out2d_trans_r7
  | 8, _ => out2d_trans_r8
  | 9, _ => out2d_trans_r9
  | 10, _ => out2d_trans_r10
  | 11, _ => out2d_trans_r11
  | 12, _ => out2d_trans_r12
  | 13, _ => out2d_trans_r13
  | 14, _ => out2d_trans_r14
  | 15, _ => out2d_trans_r15
  | 16, _ => out2d_trans_r16
  | 17, _ => out2d_trans_r17
  | 18, _ => out2d_trans_r18
  | 19, _ => out2d_trans_r19
  | 20, _ => out2d_trans_r20
  | 21, _ => out2d_trans_r21
  | 22, _ => out2d_trans_r22
  | 23, _ => out2d_trans_r23
  | 24, _ => out2d_trans_r24
  | 25, _ => out2d_trans_r25
  | 26, _ => out2d_trans_r26
  | 27, _ => out2d_trans_r27
  | 28, _ => out2d_trans_r28
  | 29, _ => out2d_trans_r29
  | 30, _ => out2d_trans_r30
  | 31, _ => out2d_trans_r31
  | 32, _ => out2d_trans_r32
  | 33, _ => out2d_trans_r33
  | 34, _ => out2d_trans_r34
  | 35, _ => out2d_trans_r35
  | 36, _ => out2d_trans_r36
  | 37, _ => out2d_trans_r37
  | 38, _ => out2d_trans_r38
  | 39, _ => out2d_trans_r39
  | 40, _ => out2d_trans_r40
  | 41, _ => out2d_trans_r41
  | 42, _ => out2d_trans_r42
  | 43, _ => out2d_trans_r43
  | 44, _ => out2d_trans_r44
  | 45, _ => out2d_trans_r45
  | 46, _ => out2d_trans_r46
  | 47, _ => out2d_trans_r47
  | 48, _ => out2d_trans_r48
  | 49, _ => out2d_trans_r49
  | 50, _ => out2d_trans_r50
  | 51, _ => out2d_trans_r51
  | 52, _ => out2d_trans_r52
  | 53, _ => out2d_trans_r53
  | 54, _ => out2d_trans_r54
  | 55, _ => out2d_trans_r55
  | 56, _ => out2d_trans_r56
  | 57, _ => out2d_trans_r57
  | 58, _ => out2d_trans_r58
  | 59, _ => out2d_trans_r59
  | 60, _ => out2d_trans_r60
  | 61, _ => out2d_trans_r61
  | 62, _ => out2d_trans_r62
  | 63, _ => out2d_trans_r63
  | 64, _ => out2d_trans_r64
  | 65, _ => out2d_trans_r65
  | 66, _ => out2d_trans_r66
  | 67, _ => out2d_trans_r67
  | 68, _ => out2d_trans_r68
  | 69, _ => out2d_trans_r69
  | 70, _ => out2d_trans_r70
  | 71, _ => out2d_trans_r71
  | 72, _ => out2d_trans_r72
  | 73, _ => out2d_trans_r73
  | 74, _ => out2d_trans_r74
  | 75, _ => out2d_trans_r75
  | 76, _ => out2d_trans_r76
  | 77, _ => out2d_trans_r77
  | 78, _ => out2d_trans_r78
  | 79, _ => out2d_trans_r79
  | 80, _ => out2d_trans_r80
  | 81, _ => out2d_trans_r81
  | 82, _ => out2d_trans_r82
  | 83, _ => out2d_trans_r83
  | 84, _ => out2d_trans_r84
  | 85, _ => out2d_trans_r85
  | 86, _ => out2d_trans_r86
  | 87, _ => out2d_trans_r87
  | 88, _ => out2d_trans_r88
  | 89, _ => out2d_trans_r89
  | 90, _ => out2d_trans_r90
  | 91, _ => out2d_trans_r91
  | 92, _ => out2d_trans_r92
  | 93, _ => out2d_trans_r93
  | 94, _ => out2d_trans_r94
  | n + 95, hbad => False.elim (by omega)

theorem out2d_trans {a b w u1 u2 c d : PH}
    (ha : isAccPH a = true) (hb : isAccPH b = true) (hw : isAccPH w = true)
    (hf : isAccPH (deltaPH (deltaPH ph0 a) b) = true)
    (hfw : isAccPH (deltaPH (deltaPH (deltaPH ph0 a) b) w) = true)
    (hnz1 : !(isZachosPH (deltaPH (deltaPH ph0 a) b) && isZachosPH w) = true)
    (hnz2 : !(isZachosPH (deltaPH a w) && isZachosPH (deltaPH b w)) = true)
    (hnz3 : !(isZachosPH (deltaPH (deltaPH ph0 u1) u2) && isZachosPH (deltaPH b w)) = true)
    (hmem1 : out2dHas a w u1 u2 = true)
    (hmem2 : out2dHas (deltaPH (deltaPH ph0 u1) u2) (deltaPH b w) c d = true) :
    out2dHas (deltaPH (deltaPH ph0 a) b) w c d = true := by
  have ⟨hra, _⟩ := (Bool.and_eq_true _ _).mp ha; have ⟨hrb, _⟩ := (Bool.and_eq_true _ _).mp hb; have ⟨hrw, _⟩ := (Bool.and_eq_true _ _).mp hw
  have hrow_a := out2d_trans_idx_all (phIdx_lt_95 ha)
  dsimp only [out2d_trans_idx_row] at hrow_a
  have hrb_row := checkNat_sound hrow_a (phIdx_lt_95 hb)
  have hrf : isReachPH (deltaPH (deltaPH ph0 a) b) = true := isReachPH_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb
  have hrfw : isReachPH (deltaPH (deltaPH (deltaPH ph0 a) b) w) = true := isReachPH_deltaPH hrf hrw
  have hrn1 : isReachPH (deltaPH a w) = true := isReachPH_deltaPH hra hrw
  have hrn2 : isReachPH (deltaPH b w) = true := isReachPH_deltaPH hrb hrw
  have hif : phIdx (deltaPH (deltaPH ph0 a) b) = dphIdx (dphIdx 0 (phIdx a)) (phIdx b) := by
    rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb, phIdx_deltaPH (by rfl) hra]; rfl
  have hifw : phIdx (deltaPH (deltaPH (deltaPH ph0 a) b) w) = dphIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) (phIdx w) := by rw [phIdx_deltaPH hrf hrw, hif]
  have hin1 : phIdx (deltaPH a w) = dphIdx (phIdx a) (phIdx w) := phIdx_deltaPH hra hrw
  have hin2 : phIdx (deltaPH b w) = dphIdx (phIdx b) (phIdx w) := phIdx_deltaPH hrb hrw
  have hfi : (!isAccIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b))) = false := by
    rw [← hif, ← (reach_1d_unpack hrf).2.2.1, hf]; rfl
  rw [hfi, if_false_eq_true] at hrb_row
  have hrw_row := checkNat_sound hrb_row (phIdx_lt_95 hw)
  have hg2 : (!isAccIdx (dphIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) (phIdx w)) ||
      (isZachosIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) && isZachosIdx (phIdx w)) ||
      (isZachosIdx (dphIdx (phIdx a) (phIdx w)) && isZachosIdx (dphIdx (phIdx b) (phIdx w)))) = false := by
    rw [← hifw, ← hif, ← hin1, ← hin2, ← (reach_1d_unpack hrfw).2.2.1,
        ← (reach_1d_unpack hrf).2.2.2.2.1, ← (reach_1d_unpack hrw).2.2.2.2.1,
        ← (reach_1d_unpack hrn1).2.2.2.2.1, ← (reach_1d_unpack hrn2).2.2.2.2.1, hfw]
    cases hz1 : (isZachosPH (deltaPH (deltaPH ph0 a) b) && isZachosPH w)
    · cases hz2 : (isZachosPH (deltaPH a w) && isZachosPH (deltaPH b w))
      · rfl
      · rw [hz2] at hnz2; cases hnz2
    · rw [hz1] at hnz1; cases hnz1
  rw [hg2, if_false_eq_true] at hrw_row
  unfold out2dHas out2dList at hmem1 hmem2 ⊢
  have ⟨hu12_acc, hm1⟩ := (Bool.and_eq_true _ _).mp hmem1
  have ⟨hu1_a, hu2_a⟩ := (Bool.and_eq_true _ _).mp hu12_acc
  have ⟨hru1, _⟩ := (Bool.and_eq_true _ _).mp hu1_a; have ⟨hru2, _⟩ := (Bool.and_eq_true _ _).mp hu2_a
  have hlt1 := phIdx_lt_95 hu1_a; have hlt2 := phIdx_lt_95 hu2_a
  have hd1 : (95 * phIdx u1 + phIdx u2) / 95 = phIdx u1 := by omega
  have hd2 : (95 * phIdx u1 + phIdx u2) % 95 = phIdx u2 := by omega
  have hbit := allNat_mem hrw_row hm1; rw [hd1, hd2] at hbit
  have hru12 : isReachPH (deltaPH (deltaPH ph0 u1) u2) = true := isReachPH_deltaPH (isReachPH_deltaPH (by rfl) hru1) hru2
  have hiu12 : phIdx (deltaPH (deltaPH ph0 u1) u2) = dphIdx (dphIdx 0 (phIdx u1)) (phIdx u2) := by
    rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hru1) hru2, phIdx_deltaPH (by rfl) hru1]; rfl
  have hz3_f : (isZachosIdx (dphIdx (dphIdx 0 (phIdx u1)) (phIdx u2)) && isZachosIdx (dphIdx (phIdx b) (phIdx w))) = false := by
    rw [← hiu12, ← hin2, ← (reach_1d_unpack hru12).2.2.2.2.1, ← (reach_1d_unpack hrn2).2.2.2.2.1]
    cases hz3 : (isZachosPH (deltaPH (deltaPH ph0 u1) u2) && isZachosPH (deltaPH b w))
    · rfl
    · rw [hz3] at hnz3; cases hnz3
  rw [hz3_f, if_false_eq_true] at hbit
  have ⟨hcd, hm2⟩ := (Bool.and_eq_true _ _).mp hmem2
  rw [hiu12, hin2] at hm2; rw [hif]
  exact (Bool.and_eq_true _ _).mpr ⟨hcd, subsetNat_mem hbit hm2⟩

end FormalQ5Final
