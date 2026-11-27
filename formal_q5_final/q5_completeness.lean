import formal_q5_final.pval_system

namespace FormalQ5Final
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
open FormalAlgebra Q5SNStratifiedGame

theorem checkAcc1_PH_not_hn34 (q : PH) (ha : isAccPH q = true) : isHN34PH q = false := by
  have ⟨hr, _⟩ := (Bool.and_eq_true _ _).mp ha
  have hlt := phIdx_lt_95 ha
  rw [(reach_1d_unpack hr).2.2.2.1]
  unfold isHN34Idx
  cases h : Nat.beq (phIdx q) 112
  · rfl
  · exfalso; have heq := Nat.eq_of_beq_eq_true h; omega

theorem tripleRank_eq_idx {x y z : PH} (hx : isReachPH x = true) (hy : isReachPH y = true) (hz : isReachPH z = true) :
    tripleRank x y z = tripleRankIdx (phIdx x) (phIdx y) (phIdx z) := by
  dsimp only [tripleRank, tripleRankIdx, pairRank, c3Rank]
  have hr1 : isReachPH (deltaPH x z) = true := isReachPH_deltaPH hx hz
  have hr2 : isReachPH (deltaPH y z) = true := isReachPH_deltaPH hy hz
  rw [(reach_1d_unpack hr1).2.2.2.1, (reach_1d_unpack hr2).2.2.2.1,
      phIdx_deltaPH hx hz, phIdx_deltaPH hy hz, (reach_1d_unpack hy).2.2.1]

theorem minPos_cases {a b rk : Nat} (hpos : 1 ≤ minPos a b) (hle : minPos a b ≤ rk) :
    (1 ≤ a ∧ a ≤ rk) ∨ (1 ≤ b ∧ b ≤ rk) := by
  unfold minPos at hpos hle
  cases ha : Nat.beq a 0
  · rw [ha, if_false_eq_true] at hpos hle
    have hapos : 1 ≤ a := by cases a with | zero => cases ha | succ n => omega
    cases hb : Nat.beq b 0
    · rw [hb, if_false_eq_true] at hpos hle
      have hbpos : 1 ≤ b := by cases b with | zero => cases hb | succ n => omega
      cases hab : Nat.ble a b
      · rw [hab, if_false_eq_true] at hle; exact Or.inr ⟨hbpos, hle⟩
      · rw [hab, if_true_eq_true] at hle; exact Or.inl ⟨hapos, hle⟩
    · rw [hb, if_true_eq_true] at hle; exact Or.inl ⟨hapos, hle⟩
  · rw [ha, if_true_eq_true] at hpos hle; exact Or.inr ⟨hpos, hle⟩

theorem rWeakRank_props {pr rk : Nat} (hpos : 1 ≤ rWeakRank pr) (hle : rWeakRank pr ≤ rk) :
    1 ≤ pr ∧ pr ≤ rk ∧ (rk % 2 = 0 → pr + 1 ≤ rk) := by
  unfold rWeakRank at hpos hle
  cases hp0 : Nat.beq pr 0
  · rw [hp0, if_false_eq_true] at hpos hle
    have hpr1 : 1 ≤ pr := by cases pr with | zero => cases hp0 | succ n => omega
    cases hodd : Nat.beq (pr % 2) 1
    · rw [hodd, if_false_eq_true] at hle
      exact ⟨hpr1, by omega, fun _ => hle⟩
    · rw [hodd, if_true_eq_true] at hle
      have heq1 : pr % 2 = 1 := Nat.eq_of_beq_eq_true hodd
      exact ⟨hpr1, hle, fun hev => by omega⟩
  · rw [hp0, if_true_eq_true] at hpos; cases hpos

theorem tripleRank_cases {x y z : PH} {rk : Nat}
    (hpos : 1 ≤ tripleRank x y z) (hle : tripleRank x y z ≤ rk) :
    isHN34PH (deltaPH y z) = true ∨
    isHN34PH (deltaPH x z) = true ∨
    (1 ≤ pairRank x z ∧ pairRank x z ≤ rk) ∨
    (isAccPH y = true ∧ 1 ≤ pairRank y z ∧ pairRank y z ≤ rk ∧ (rk % 2 = 0 → pairRank y z + 1 ≤ rk)) ∨
    (1 ≤ c3Rank x z (deltaPH y z) ∧ c3Rank x z (deltaPH y z) ≤ rk) := by
  unfold tripleRank at hpos hle
  cases hn2 : isHN34PH (deltaPH y z)
  · cases hn1 : isHN34PH (deltaPH x z)
    · simp only [hn2, hn1, Bool.false_or, if_false_eq_true] at hpos hle
      rcases minPos_cases hpos hle with hL | hrest
      · exact Or.inr (Or.inr (Or.inl hL))
      · rcases minPos_cases hrest.1 hrest.2 with hR | hC
        · cases hy : isAccPH y
          · rw [hy, if_false_eq_true] at hR; exact False.elim (Nat.not_succ_le_zero 0 hR.1)
          · rw [hy, if_true_eq_true] at hR
            obtain ⟨hp1, hple, hev⟩ := rWeakRank_props hR.1 hR.2
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hp1, hple, hev⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

def ob1_fn (f z : PH) : Bool :=
  (if 1 ≤ pairRank f z then decide (kindPH f = 2) && !isAccPH (deltaPH f z) else true) &&
  (if isAccPH f && isAccPH z && !isAccPH (deltaPH f z) then decide (1 ≤ pairRank f z ∧ pairRank f z ≤ 17) else true)

theorem ob1_chk (f z : PH) (hf : isAccPH f = true) (hz : isReachPH z = true) : ob1_fn f z = true := by
  have ⟨hrf, _⟩ := (Bool.and_eq_true _ _).mp hf
  have hthm : ob1_idx_ok = true := ob1_idx_thm
  unfold ob1_idx_ok at hthm
  have hf_row := checkNat_sound hthm (phIdx_lt_95 hf)
  have h := checkNat_sound hf_row (phIdx_lt_113 hz)
  have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  have hr_dfz : isReachPH (deltaPH f z) = true := isReachPH_deltaPH hrf hz
  have hidfz : phIdx (deltaPH f z) = dphIdx (phIdx f) (phIdx z) := phIdx_deltaPH hrf hz
  unfold ob1_fn
  refine (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩
  · if hpr : 1 ≤ pairRank f z then
      rw [if_pos hpr]
      have hble : Nat.ble 1 (pairRankIdx (phIdx f) (phIdx z)) = true := Nat.ble_eq.mpr hpr
      rw [hble, if_true_eq_true] at h1
      have ⟨hk, hna⟩ := (Bool.and_eq_true _ _).mp h1
      rw [(reach_1d_unpack hr_dfz).2.2.1, hidfz]
      exact (Bool.and_eq_true _ _).mpr ⟨decide_eq_true (Nat.eq_of_beq_eq_true hk), hna⟩
    else rw [if_neg hpr]
  · cases hc : (isAccPH f && isAccPH z && !isAccPH (deltaPH f z))
    · rfl
    · have hci : (isAccIdx (phIdx f) && isAccIdx (phIdx z) && !isAccIdx (dphIdx (phIdx f) (phIdx z))) = true := by
        rw [← hidfz, ← (reach_1d_unpack hrf).2.2.1, ← (reach_1d_unpack hz).2.2.1, ← (reach_1d_unpack hr_dfz).2.2.1]
        exact hc
      rw [hci, if_true_eq_true] at h2
      have ⟨hp1, hp17⟩ := (Bool.and_eq_true _ _).mp h2
      exact decide_eq_true ⟨Nat.le_of_ble_eq_true hp1, Nat.le_of_ble_eq_true hp17⟩

def ob2_fn (a b z : PH) : Bool :=
  let f := deltaPH (deltaPH ph0 a) b; let pr := pairRank f z
  if Nat.beq pr 0 || isHN34PH z || isHN34PH (deltaPH f z) then true
  else let tr := tripleRank a b z; decide (1 ≤ tr ∧ tr ≤ pr)

theorem ob2_idx_all {a : Nat} (ha : a < 95) : ob2_idx_row a = true :=
  match a, ha with
  | 0, _ => ob2_r0
  | 1, _ => ob2_r1
  | 2, _ => ob2_r2
  | 3, _ => ob2_r3
  | 4, _ => ob2_r4
  | 5, _ => ob2_r5
  | 6, _ => ob2_r6
  | 7, _ => ob2_r7
  | 8, _ => ob2_r8
  | 9, _ => ob2_r9
  | 10, _ => ob2_r10
  | 11, _ => ob2_r11
  | 12, _ => ob2_r12
  | 13, _ => ob2_r13
  | 14, _ => ob2_r14
  | 15, _ => ob2_r15
  | 16, _ => ob2_r16
  | 17, _ => ob2_r17
  | 18, _ => ob2_r18
  | 19, _ => ob2_r19
  | 20, _ => ob2_r20
  | 21, _ => ob2_r21
  | 22, _ => ob2_r22
  | 23, _ => ob2_r23
  | 24, _ => ob2_r24
  | 25, _ => ob2_r25
  | 26, _ => ob2_r26
  | 27, _ => ob2_r27
  | 28, _ => ob2_r28
  | 29, _ => ob2_r29
  | 30, _ => ob2_r30
  | 31, _ => ob2_r31
  | 32, _ => ob2_r32
  | 33, _ => ob2_r33
  | 34, _ => ob2_r34
  | 35, _ => ob2_r35
  | 36, _ => ob2_r36
  | 37, _ => ob2_r37
  | 38, _ => ob2_r38
  | 39, _ => ob2_r39
  | 40, _ => ob2_r40
  | 41, _ => ob2_r41
  | 42, _ => ob2_r42
  | 43, _ => ob2_r43
  | 44, _ => ob2_r44
  | 45, _ => ob2_r45
  | 46, _ => ob2_r46
  | 47, _ => ob2_r47
  | 48, _ => ob2_r48
  | 49, _ => ob2_r49
  | 50, _ => ob2_r50
  | 51, _ => ob2_r51
  | 52, _ => ob2_r52
  | 53, _ => ob2_r53
  | 54, _ => ob2_r54
  | 55, _ => ob2_r55
  | 56, _ => ob2_r56
  | 57, _ => ob2_r57
  | 58, _ => ob2_r58
  | 59, _ => ob2_r59
  | 60, _ => ob2_r60
  | 61, _ => ob2_r61
  | 62, _ => ob2_r62
  | 63, _ => ob2_r63
  | 64, _ => ob2_r64
  | 65, _ => ob2_r65
  | 66, _ => ob2_r66
  | 67, _ => ob2_r67
  | 68, _ => ob2_r68
  | 69, _ => ob2_r69
  | 70, _ => ob2_r70
  | 71, _ => ob2_r71
  | 72, _ => ob2_r72
  | 73, _ => ob2_r73
  | 74, _ => ob2_r74
  | 75, _ => ob2_r75
  | 76, _ => ob2_r76
  | 77, _ => ob2_r77
  | 78, _ => ob2_r78
  | 79, _ => ob2_r79
  | 80, _ => ob2_r80
  | 81, _ => ob2_r81
  | 82, _ => ob2_r82
  | 83, _ => ob2_r83
  | 84, _ => ob2_r84
  | 85, _ => ob2_r85
  | 86, _ => ob2_r86
  | 87, _ => ob2_r87
  | 88, _ => ob2_r88
  | 89, _ => ob2_r89
  | 90, _ => ob2_r90
  | 91, _ => ob2_r91
  | 92, _ => ob2_r92
  | 93, _ => ob2_r93
  | 94, _ => ob2_r94
  | n + 95, hbad => False.elim (by omega)

theorem ob3_idx_all {a : Nat} (ha : a < 95) : ob3_idx_row a = true :=
  match a, ha with
  | 0, _ => ob3_r0
  | 1, _ => ob3_r1
  | 2, _ => ob3_r2
  | 3, _ => ob3_r3
  | 4, _ => ob3_r4
  | 5, _ => ob3_r5
  | 6, _ => ob3_r6
  | 7, _ => ob3_r7
  | 8, _ => ob3_r8
  | 9, _ => ob3_r9
  | 10, _ => ob3_r10
  | 11, _ => ob3_r11
  | 12, _ => ob3_r12
  | 13, _ => ob3_r13
  | 14, _ => ob3_r14
  | 15, _ => ob3_r15
  | 16, _ => ob3_r16
  | 17, _ => ob3_r17
  | 18, _ => ob3_r18
  | 19, _ => ob3_r19
  | 20, _ => ob3_r20
  | 21, _ => ob3_r21
  | 22, _ => ob3_r22
  | 23, _ => ob3_r23
  | 24, _ => ob3_r24
  | 25, _ => ob3_r25
  | 26, _ => ob3_r26
  | 27, _ => ob3_r27
  | 28, _ => ob3_r28
  | 29, _ => ob3_r29
  | 30, _ => ob3_r30
  | 31, _ => ob3_r31
  | 32, _ => ob3_r32
  | 33, _ => ob3_r33
  | 34, _ => ob3_r34
  | 35, _ => ob3_r35
  | 36, _ => ob3_r36
  | 37, _ => ob3_r37
  | 38, _ => ob3_r38
  | 39, _ => ob3_r39
  | 40, _ => ob3_r40
  | 41, _ => ob3_r41
  | 42, _ => ob3_r42
  | 43, _ => ob3_r43
  | 44, _ => ob3_r44
  | 45, _ => ob3_r45
  | 46, _ => ob3_r46
  | 47, _ => ob3_r47
  | 48, _ => ob3_r48
  | 49, _ => ob3_r49
  | 50, _ => ob3_r50
  | 51, _ => ob3_r51
  | 52, _ => ob3_r52
  | 53, _ => ob3_r53
  | 54, _ => ob3_r54
  | 55, _ => ob3_r55
  | 56, _ => ob3_r56
  | 57, _ => ob3_r57
  | 58, _ => ob3_r58
  | 59, _ => ob3_r59
  | 60, _ => ob3_r60
  | 61, _ => ob3_r61
  | 62, _ => ob3_r62
  | 63, _ => ob3_r63
  | 64, _ => ob3_r64
  | 65, _ => ob3_r65
  | 66, _ => ob3_r66
  | 67, _ => ob3_r67
  | 68, _ => ob3_r68
  | 69, _ => ob3_r69
  | 70, _ => ob3_r70
  | 71, _ => ob3_r71
  | 72, _ => ob3_r72
  | 73, _ => ob3_r73
  | 74, _ => ob3_r74
  | 75, _ => ob3_r75
  | 76, _ => ob3_r76
  | 77, _ => ob3_r77
  | 78, _ => ob3_r78
  | 79, _ => ob3_r79
  | 80, _ => ob3_r80
  | 81, _ => ob3_r81
  | 82, _ => ob3_r82
  | 83, _ => ob3_r83
  | 84, _ => ob3_r84
  | 85, _ => ob3_r85
  | 86, _ => ob3_r86
  | 87, _ => ob3_r87
  | 88, _ => ob3_r88
  | 89, _ => ob3_r89
  | 90, _ => ob3_r90
  | 91, _ => ob3_r91
  | 92, _ => ob3_r92
  | 93, _ => ob3_r93
  | 94, _ => ob3_r94
  | n + 95, hbad => False.elim (by omega)

theorem ob4_idx_all {a : Nat} (ha : a < 95) : ob4_idx_row a = true :=
  match a, ha with
  | 0, _ => ob4_r0
  | 1, _ => ob4_r1
  | 2, _ => ob4_r2
  | 3, _ => ob4_r3
  | 4, _ => ob4_r4
  | 5, _ => ob4_r5
  | 6, _ => ob4_r6
  | 7, _ => ob4_r7
  | 8, _ => ob4_r8
  | 9, _ => ob4_r9
  | 10, _ => ob4_r10
  | 11, _ => ob4_r11
  | 12, _ => ob4_r12
  | 13, _ => ob4_r13
  | 14, _ => ob4_r14
  | 15, _ => ob4_r15
  | 16, _ => ob4_r16
  | 17, _ => ob4_r17
  | 18, _ => ob4_r18
  | 19, _ => ob4_r19
  | 20, _ => ob4_r20
  | 21, _ => ob4_r21
  | 22, _ => ob4_r22
  | 23, _ => ob4_r23
  | 24, _ => ob4_r24
  | 25, _ => ob4_r25
  | 26, _ => ob4_r26
  | 27, _ => ob4_r27
  | 28, _ => ob4_r28
  | 29, _ => ob4_r29
  | 30, _ => ob4_r30
  | 31, _ => ob4_r31
  | 32, _ => ob4_r32
  | 33, _ => ob4_r33
  | 34, _ => ob4_r34
  | 35, _ => ob4_r35
  | 36, _ => ob4_r36
  | 37, _ => ob4_r37
  | 38, _ => ob4_r38
  | 39, _ => ob4_r39
  | 40, _ => ob4_r40
  | 41, _ => ob4_r41
  | 42, _ => ob4_r42
  | 43, _ => ob4_r43
  | 44, _ => ob4_r44
  | 45, _ => ob4_r45
  | 46, _ => ob4_r46
  | 47, _ => ob4_r47
  | 48, _ => ob4_r48
  | 49, _ => ob4_r49
  | 50, _ => ob4_r50
  | 51, _ => ob4_r51
  | 52, _ => ob4_r52
  | 53, _ => ob4_r53
  | 54, _ => ob4_r54
  | 55, _ => ob4_r55
  | 56, _ => ob4_r56
  | 57, _ => ob4_r57
  | 58, _ => ob4_r58
  | 59, _ => ob4_r59
  | 60, _ => ob4_r60
  | 61, _ => ob4_r61
  | 62, _ => ob4_r62
  | 63, _ => ob4_r63
  | 64, _ => ob4_r64
  | 65, _ => ob4_r65
  | 66, _ => ob4_r66
  | 67, _ => ob4_r67
  | 68, _ => ob4_r68
  | 69, _ => ob4_r69
  | 70, _ => ob4_r70
  | 71, _ => ob4_r71
  | 72, _ => ob4_r72
  | 73, _ => ob4_r73
  | 74, _ => ob4_r74
  | 75, _ => ob4_r75
  | 76, _ => ob4_r76
  | 77, _ => ob4_r77
  | 78, _ => ob4_r78
  | 79, _ => ob4_r79
  | 80, _ => ob4_r80
  | 81, _ => ob4_r81
  | 82, _ => ob4_r82
  | 83, _ => ob4_r83
  | 84, _ => ob4_r84
  | 85, _ => ob4_r85
  | 86, _ => ob4_r86
  | 87, _ => ob4_r87
  | 88, _ => ob4_r88
  | 89, _ => ob4_r89
  | 90, _ => ob4_r90
  | 91, _ => ob4_r91
  | 92, _ => ob4_r92
  | 93, _ => ob4_r93
  | 94, _ => ob4_r94
  | n + 95, hbad => False.elim (by omega)

theorem ob2_chk (a b z : PH) (ha : isAccPH a = true) (hb : isAccPH b = true) (hz : isReachPH z = true) : ob2_fn a b z = true := by
  have ⟨hra, _⟩ := (Bool.and_eq_true _ _).mp ha; have ⟨hrb, _⟩ := (Bool.and_eq_true _ _).mp hb
  have hrow := ob2_idx_all (phIdx_lt_95 ha); dsimp only [ob2_idx_row] at hrow
  have h1 := checkNat_sound hrow (phIdx_lt_95 hb)
  have h := checkNat_sound h1 (phIdx_lt_113 hz)
  have hrf : isReachPH (deltaPH (deltaPH ph0 a) b) = true := isReachPH_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb
  have hrfz : isReachPH (deltaPH (deltaPH (deltaPH ph0 a) b) z) = true := isReachPH_deltaPH hrf hz
  have hif : phIdx (deltaPH (deltaPH ph0 a) b) = dphIdx (dphIdx 0 (phIdx a)) (phIdx b) := by
    rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb, phIdx_deltaPH (by rfl) hra]; rfl
  have hifz : phIdx (deltaPH (deltaPH (deltaPH ph0 a) b) z) = dphIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) (phIdx z) := by
    rw [phIdx_deltaPH hrf hz, hif]
  dsimp only [ob2_fn]
  cases hc : (Nat.beq (pairRank (deltaPH (deltaPH ph0 a) b) z) 0 || isHN34PH z || isHN34PH (deltaPH (deltaPH (deltaPH ph0 a) b) z))
  · rw [if_false_eq_true]
    have hci : (Nat.beq (pairRankIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) (phIdx z)) 0 || isHN34Idx (phIdx z) ||
        isHN34Idx (dphIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) (phIdx z))) = false := by
      rw [← hifz, ← hif, ← (reach_1d_unpack hz).2.2.2.1, ← (reach_1d_unpack hrfz).2.2.2.1]
      exact hc
    rw [hci, if_false_eq_true] at h
    have ⟨ht1, htle⟩ := (Bool.and_eq_true _ _).mp h
    rw [tripleRank_eq_idx hra hrb hz]; unfold pairRank; rw [hif]
    exact decide_eq_true ⟨Nat.le_of_ble_eq_true ht1, Nat.le_of_ble_eq_true htle⟩
  · rw [if_true_eq_true]

theorem c3Rank_ph0 (z n2 : PH) (hz : isReachPH z = true) (hn2 : isReachPH n2 = true) : c3Rank ph0 z n2 = 0 := by
  change c3RankIdx 0 (phIdx z) (phIdx n2) = 0
  have h1 := checkNat_sound c3_ph0_idx_thm (phIdx_lt_113 hz)
  have h2 := checkNat_sound h1 (phIdx_lt_113 hn2)
  exact Nat.eq_of_beq_eq_true h2

def ob3_fn (u z n2 : PH) : Bool :=
  let x := deltaPH ph0 u; let cr := c3Rank x z n2
  if Nat.beq cr 0 || isHN34PH z || isHN34PH n2 then true
  else
    let un2 := deltaPH u n2
    if isHN34PH un2 then true
    else if !isAccPH un2 && Nat.beq (kindPH u) 2 then decide (1 ≤ pairRank u n2 ∧ pairRank u n2 ≤ cr)
    else isHN34PH (deltaPH (deltaPH x z) n2) ||
         (let tr := tripleRank u z n2; decide (1 ≤ tr ∧ (if cr % 2 = 1 then tr + 1 ≤ cr else tr ≤ cr)))

theorem ob3_chk (u z n2 : PH) (hu : isAccPH u = true) (hz : isReachPH z = true) (hn2 : isReachPH n2 = true) : ob3_fn u z n2 = true := by
  have ⟨hru, _⟩ := (Bool.and_eq_true _ _).mp hu
  have hrow := ob3_idx_all (phIdx_lt_95 hu); dsimp only [ob3_idx_row] at hrow
  have h1 := checkNat_sound hrow (phIdx_lt_113 hz)
  dsimp only [ob3_fn]
  cases htop : (Nat.beq (c3Rank (deltaPH ph0 u) z n2) 0 || isHN34PH z || isHN34PH n2)
  · rw [if_false_eq_true]
    have ⟨htop12, hn2_f⟩ := Bool.or_eq_false_iff.mp htop
    have ⟨hcr_f, hz_f⟩ := Bool.or_eq_false_iff.mp htop12
    have hzi : isHN34Idx (phIdx z) = false := by rw [← (reach_1d_unpack hz).2.2.2.1]; exact hz_f
    rw [hzi, if_false_eq_true] at h1
    have h2 := checkNat_sound h1 (phIdx_lt_113 hn2)
    have hrx : isReachPH (deltaPH ph0 u) = true := isReachPH_deltaPH (by rfl) hru
    have hix : phIdx (deltaPH ph0 u) = dphIdx 0 (phIdx u) := phIdx_deltaPH (by rfl) hru
    have hg1 : (Nat.beq (c3RankIdx (dphIdx 0 (phIdx u)) (phIdx z) (phIdx n2)) 0 || isHN34Idx (phIdx n2)) = false := by
      rw [← hix, ← (reach_1d_unpack hn2).2.2.2.1]
      exact Bool.or_eq_false_iff.mpr ⟨hcr_f, hn2_f⟩
    rw [hg1, if_false_eq_true] at h2
    have hrun2 : isReachPH (deltaPH u n2) = true := isReachPH_deltaPH hru hn2
    have hiun2 : phIdx (deltaPH u n2) = dphIdx (phIdx u) (phIdx n2) := phIdx_deltaPH hru hn2
    cases hun2 : isHN34PH (deltaPH u n2)
    · rw [if_false_eq_true]
      have hun2i : isHN34Idx (dphIdx (phIdx u) (phIdx n2)) = false := by
        rw [← hiun2, ← (reach_1d_unpack hrun2).2.2.2.1]; exact hun2
      rw [hun2i, if_false_eq_true] at h2
      cases hbr : (!isAccPH (deltaPH u n2) && Nat.beq (kindPH u) 2)
      · rw [if_false_eq_true]
        have hbri : (!isAccIdx (dphIdx (phIdx u) (phIdx n2)) && Nat.beq (kindIdx (phIdx u)) 2) = false := by
          rw [← hiun2, ← (reach_1d_unpack hrun2).2.2.1]; exact hbr
        rw [hbri, if_false_eq_true] at h2
        have hrxz : isReachPH (deltaPH (deltaPH ph0 u) z) = true := isReachPH_deltaPH hrx hz
        have hrxzn2 : isReachPH (deltaPH (deltaPH (deltaPH ph0 u) z) n2) = true := isReachPH_deltaPH hrxz hn2
        have hixzn2 : phIdx (deltaPH (deltaPH (deltaPH ph0 u) z) n2) = dphIdx (dphIdx (dphIdx 0 (phIdx u)) (phIdx z)) (phIdx n2) := by
          rw [phIdx_deltaPH hrxz hn2, phIdx_deltaPH hrx hz, hix]
        rcases (Bool.or_eq_true _ _).mp h2 with h34_i | htr_i
        · apply (Bool.or_eq_true _ _).mpr; left
          rw [(reach_1d_unpack hrxzn2).2.2.2.1, hixzn2]; exact h34_i
        · apply (Bool.or_eq_true _ _).mpr; right
          have ⟨ht1, hcmp⟩ := (Bool.and_eq_true _ _).mp htr_i
          rw [tripleRank_eq_idx hru hz hn2]; unfold c3Rank; rw [hix]
          refine decide_eq_true ⟨Nat.le_of_ble_eq_true ht1, ?_⟩
          if hmod : c3RankIdx (dphIdx 0 (phIdx u)) (phIdx z) (phIdx n2) % 2 = 1 then
            rw [if_pos hmod]
            have hb_mod : Nat.beq (c3RankIdx (dphIdx 0 (phIdx u)) (phIdx z) (phIdx n2) % 2) 1 = true := Nat.beq_eq.mpr hmod
            rw [hb_mod, if_true_eq_true] at hcmp
            exact Nat.le_of_ble_eq_true hcmp
          else
            rw [if_neg hmod]
            cases hb_mod : Nat.beq (c3RankIdx (dphIdx 0 (phIdx u)) (phIdx z) (phIdx n2) % 2) 1
            · rw [hb_mod, if_false_eq_true] at hcmp; exact Nat.le_of_ble_eq_true hcmp
            · exact False.elim (hmod (Nat.eq_of_beq_eq_true hb_mod))
      · rw [if_true_eq_true]
        have hbri : (!isAccIdx (dphIdx (phIdx u) (phIdx n2)) && Nat.beq (kindIdx (phIdx u)) 2) = true := by
          rw [← hiun2, ← (reach_1d_unpack hrun2).2.2.1]; exact hbr
        rw [hbri, if_true_eq_true] at h2
        have ⟨hp1, hple⟩ := (Bool.and_eq_true _ _).mp h2
        unfold pairRank c3Rank; rw [hix]
        exact decide_eq_true ⟨Nat.le_of_ble_eq_true hp1, Nat.le_of_ble_eq_true hple⟩
    · rw [if_true_eq_true]
  · rw [if_true_eq_true]

def ob4_fn (x z n2 : PH) : Bool :=
  let cr := c3Rank x z n2
  if Nat.beq cr 0 || !Nat.beq (kindPH x) 2 || isHN34PH z || isHN34PH n2 then true
  else isAccPH z && isAccPH (deltaPH x z) &&
       out2dAllPairs x z (fun a b =>
         isHN34PH (deltaPH (deltaPH (deltaPH ph0 a) b) n2) ||
         (let tr := tripleRank a b n2; decide (1 ≤ tr ∧ tr + 1 ≤ cr)))

theorem ob4_chk (x z n2 : PH) (hx : isAccPH x = true) (hz : isReachPH z = true) (hn2 : isReachPH n2 = true) : ob4_fn x z n2 = true := by
  have ⟨hrx, _⟩ := (Bool.and_eq_true _ _).mp hx
  have hrow := ob4_idx_all (phIdx_lt_95 hx)
  dsimp only [ob4_idx_row] at hrow
  dsimp only [ob4_fn]
  cases htop : (Nat.beq (c3Rank x z n2) 0 || !Nat.beq (kindPH x) 2 || isHN34PH z || isHN34PH n2)
  · rw [if_false_eq_true]
    have ⟨ht123, hn2_f⟩ := Bool.or_eq_false_iff.mp htop
    have ⟨ht12, hz_f⟩ := Bool.or_eq_false_iff.mp ht123
    have ⟨hcr_f, hk2_f⟩ := Bool.or_eq_false_iff.mp ht12
    have hk2_eq : (!Nat.beq (kindIdx (phIdx x)) 2) = false := hk2_f
    rw [hk2_eq, if_false_eq_true] at hrow
    have h1 := checkNat_sound hrow (phIdx_lt_113 hz)
    have hzi : isHN34Idx (phIdx z) = false := by rw [← (reach_1d_unpack hz).2.2.2.1]; exact hz_f
    rw [hzi, if_false_eq_true] at h1
    have h2 := checkNat_sound h1 (phIdx_lt_113 hn2)
    have hg2 : (Nat.beq (c3RankIdx (phIdx x) (phIdx z) (phIdx n2)) 0 || isHN34Idx (phIdx n2)) = false := by
      rw [← (reach_1d_unpack hn2).2.2.2.1]; exact Bool.or_eq_false_iff.mpr ⟨hcr_f, hn2_f⟩
    rw [hg2, if_false_eq_true] at h2
    have ⟨hacc_pair, hall_i⟩ := (Bool.and_eq_true _ _).mp h2
    have ⟨hz_ai, hxz_ai⟩ := (Bool.and_eq_true _ _).mp hacc_pair
    have hrxz : isReachPH (deltaPH x z) = true := isReachPH_deltaPH hrx hz
    have hz_acc : isAccPH z = true := by rw [(reach_1d_unpack hz).2.2.1]; exact hz_ai
    have hxz_acc : isAccPH (deltaPH x z) = true := by rw [(reach_1d_unpack hrxz).2.2.1, phIdx_deltaPH hrx hz]; exact hxz_ai
    rw [hz_acc, hxz_acc]; simp only [Bool.true_and]
    -- Show `allNat` of the `PH` predicate follows from `allNat` of the `Nat` predicate!
    unfold out2dAllPairs out2dList
    generalize out2dListIdx (phIdx x) (phIdx z) = xs at hall_i ⊢
    induction xs with
    | nil => rfl
    | cons idx rest ih =>
      have ⟨hhead, htail⟩ := (Bool.and_eq_true _ _).mp hall_i
      refine (Bool.and_eq_true _ _).mpr ⟨?_, ih htail⟩
      have ⟨hidx_lt, hbody⟩ := (Bool.and_eq_true _ _).mp hhead
      have hlt9025 : idx < 9025 := Nat.le_of_ble_eq_true hidx_lt
      have ha113 : idx / 95 < 113 := by omega
      have hb113 : idx % 95 < 113 := by omega
      have ⟨hra, hia⟩ := ofPhIdx_spec ha113
      have ⟨hrb, hib⟩ := ofPhIdx_spec hb113
      have hrsab : isReachPH (deltaPH (deltaPH ph0 (idxToU1 idx)) (idxToU2 idx)) = true :=
        isReachPH_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb
      have hrsabn2 : isReachPH (deltaPH (deltaPH (deltaPH ph0 (idxToU1 idx)) (idxToU2 idx)) n2) = true :=
        isReachPH_deltaPH hrsab hn2
      have hisabn2 : phIdx (deltaPH (deltaPH (deltaPH ph0 (idxToU1 idx)) (idxToU2 idx)) n2) =
          dphIdx (dphIdx (dphIdx 0 (idx / 95)) (idx % 95)) (phIdx n2) := by
        rw [phIdx_deltaPH hrsab hn2]
        unfold idxToU1 idxToU2
        rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb, phIdx_deltaPH (by rfl) hra, hia, hib]; rfl
      rcases (Bool.or_eq_true _ _).mp hbody with h34_i | htr_i
      · apply (Bool.or_eq_true _ _).mpr; left
        rw [(reach_1d_unpack hrsabn2).2.2.2.1, hisabn2]; exact h34_i
      · apply (Bool.or_eq_true _ _).mpr; right
        have ⟨ht1, htle⟩ := (Bool.and_eq_true _ _).mp htr_i
        have htr_eq : tripleRank (idxToU1 idx) (idxToU2 idx) n2 = tripleRankIdx (idx / 95) (idx % 95) (phIdx n2) := by
          unfold idxToU1 idxToU2
          rw [tripleRank_eq_idx hra hrb hn2, hia, hib]
        rw [htr_eq]
        exact decide_eq_true ⟨Nat.le_of_ble_eq_true ht1, Nat.le_of_ble_eq_true htle⟩
  · rw [if_true_eq_true]

inductive Arg : Type where
  | pval : PVal → Arg
  | raw : Term → Arg

def Arg.toTerm : Arg → Term
  | .pval v => v.toTerm
  | .raw t => t

def Arg.pvalSize : Arg → Nat
  | .pval v => v.size
  | .raw _ => 0

structure ValidArg (a : Arg) : Prop where
  hv : noVars a.toTerm = true
  not_hn34 : isHN34PH (evalPH a.toTerm) = false
  acc_is_pval : isAccPH (evalPH a.toTerm) = true → ∃ v : PVal, a = .pval v

theorem ValidArg.reach {a : Arg} (ha : ValidArg a) : isReachPH (evalPH a.toTerm) = true :=
  evalPH_isReach ha.hv

private theorem acc_not_hn34_chk : checkAcc1_PH (fun q => !isHN34PH q) = true := rfl

theorem validArg_pval (v : PVal) : ValidArg (.pval v) := by
  refine ⟨PVal.noVars_toTerm v, ?_, fun _ => ⟨v, rfl⟩⟩
  change isHN34PH (evalPH v.toTerm) = false
  have h := checkAcc1_PH_sound _ acc_not_hn34_chk (evalPH v.toTerm) (PVal.isAccPH_toTerm v)
  cases hc : isHN34PH (evalPH v.toTerm) <;> rw [hc] at h <;> first | rfl | cases h

def mkValidArg (t : Term) (hv : noVars t = true) (hnot34 : isHN34PH (evalPH t) = false) :
    Σ' a : Arg, Reduces t a.toTerm ∧ evalPH a.toTerm = evalPH t ∧ ValidArg a :=
  if hp : evalP t ≠ .p37 then
    let ⟨v, hred⟩ := toPVal t hv hp
    ⟨.pval v, hred, (evalPH_reduces hred).symm, validArg_pval v⟩
  else
    ⟨.raw t, Reduces.refl t, rfl,
     ⟨hv, hnot34, fun hacc => by
       exfalso
       change isAccPH (evalPH t) = true at hacc
       rw [isAccPH_evalPH hv] at hacc
       exact hp (of_decide_eq_true hacc)⟩⟩

private theorem hasBot_from_hn34_ph {t : Term} (hv : noVars t = true) (h34 : isHN34PH (evalPH t) = true) :
    HasBot t :=
  ⟨0, closed_evalHN_hn34_hasBot0 hv (of_decide_eq_true h34)⟩

private theorem hasBot_app_left_bot {y z : Term} (hvy : noVars y = true) (hvz : noVars z = true)
    (hb : HasBot y) : HasBot (y ⋅ z) :=
  let ⟨d, hd⟩ := hb; ⟨d, hasBotWithin_app_left hvy hvz hd⟩

private theorem hasBot_app_right_bot {f w : Term} (hvf : noVars f = true) (hvw : noVars w = true)
    (hb : HasBot w) : HasBot (f ⋅ w) :=
  let ⟨d, hd⟩ := hb; ⟨d + 1, hasBotWithin_app_right hvf hvw hd⟩

private theorem hasBot_back {a b : Term} (hr : Reduces a b) (hb : HasBot b) : HasBot a :=
  let ⟨d, hd⟩ := hb; ⟨d, hasBotWithin_backward_reduces hr hd⟩

def RankSolvedUpTo (rk : Nat) : Prop :=
  (∀ (f : PVal) (z : Arg), ValidArg z →
    1 ≤ pairRank (evalPH f.toTerm) (evalPH z.toTerm) →
    pairRank (evalPH f.toTerm) (evalPH z.toTerm) ≤ rk →
    HasBot (f.toTerm ⋅ z.toTerm)) ∧
  (∀ (x : PVal) (y z : Arg), ValidArg y → ValidArg z →
    1 ≤ tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) →
    tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) ≤ rk →
    HasBot ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm))

theorem rankSolved_zero : RankSolvedUpTo 0 :=
  ⟨fun _ _ _ h1 h0 => False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans h1 h0)),
   fun _ _ _ _ _ h1 h0 => False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans h1 h0))⟩

private theorem solve_c3_step {rk x_sz : Nat} (ih_rk : RankSolvedUpTo rk)
    (same_pair : ∀ (u : PVal) (w : Arg), ValidArg w →
      1 ≤ pairRank (evalPH u.toTerm) (evalPH w.toTerm) →
      pairRank (evalPH u.toTerm) (evalPH w.toTerm) ≤ rk + 1 →
      u.size < x_sz → HasBot (u.toTerm ⋅ w.toTerm))
    (same_s1_even : (rk + 1) % 2 = 0 → ∀ (u : PVal) (z w : Arg), ValidArg z → ValidArg w →
      1 ≤ tripleRank (evalPH u.toTerm) (evalPH z.toTerm) (evalPH w.toTerm) →
      tripleRank (evalPH u.toTerm) (evalPH z.toTerm) (evalPH w.toTerm) ≤ rk + 1 →
      u.size < x_sz → HasBot ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ w.toTerm))
    (x : PVal) (hx_sz : x.size = x_sz) (y z : Arg) (hy : ValidArg y) (hz : ValidArg z)
    (hcpos : 1 ≤ c3Rank (evalPH x.toTerm) (evalPH z.toTerm) (deltaPH (evalPH y.toTerm) (evalPH z.toTerm)))
    (hcle : c3Rank (evalPH x.toTerm) (evalPH z.toTerm) (deltaPH (evalPH y.toTerm) (evalPH z.toTerm)) ≤ rk + 1) :
    HasBot ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) := by
  let n2 := deltaPH (evalPH y.toTerm) (evalPH z.toTerm)
  have hr_n2 : isReachPH n2 = true := isReachPH_deltaPH hy.reach hz.reach
  have hvyz : noVars (y.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨hy.hv, hz.hv⟩
  have hvxz : noVars (x.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm x, hz.hv⟩
  have hroot1 : Reduces ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) ((x.toTerm ⋅ z.toTerm) ⋅ (y.toTerm ⋅ z.toTerm)) :=
    Reduces.next (Step.root x.toTerm y.toTerm z.toTerm) (Reduces.refl _)
  cases hn2_34 : isHN34PH n2
  · let ⟨yn2, hred_yn2, hph_yn2, hval_yn2⟩ := mkValidArg (y.toTerm ⋅ z.toTerm) hvyz hn2_34
    cases hx : x with
    | s =>
      exfalso
      have hz0 : c3Rank ph0 (evalPH z.toTerm) n2 = 0 := c3Rank_ph0 _ _ hz.reach hr_n2
      rw [hx] at hcpos; change 1 ≤ c3Rank ph0 (evalPH z.toTerm) n2 at hcpos
      rw [hz0] at hcpos; exact Nat.not_succ_le_zero 0 hcpos
    | zachos m n =>
      have hb_l : HasBot (zachosG m ⋅ zachosG n ⋅ z.toTerm) := hasBot_zachos_app m n hz.hv
      rw [hx] at hroot1 hvxz
      exact hasBot_back hroot1 (hasBot_app_left_bot hvxz hvyz hb_l)
    | s1 u =>
      have hu_lt : u.size < x_sz := by rw [← hx_sz, hx]; change u.size < u.size + 1; omega
      have hob3 := ob3_chk (evalPH u.toTerm) (evalPH z.toTerm) n2 (PVal.isAccPH_toTerm u) hz.reach hr_n2
      dsimp only [ob3_fn] at hob3
      have hcr0 : Nat.beq (c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2) 0 = false := by
        rw [hx] at hcpos; change 1 ≤ c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2 at hcpos
        cases hc : c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2
        · rw [hc] at hcpos; cases hcpos
        · rfl
      have hcond3 : (Nat.beq (c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2) 0 ||
          isHN34PH (evalPH z.toTerm) || isHN34PH n2) = false := by
        rw [hcr0, hz.not_hn34, hn2_34]; rfl
      rw [hcond3, if_false_eq_true] at hob3
      have hred_mid : Reduces ((S ⋅ (PVal.s1 u).toTerm ⋅ y.toTerm) ⋅ z.toTerm)
          ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm) :=
        Reduces.next (Step.root (S ⋅ u.toTerm) y.toTerm z.toTerm) (reduces_right _ hred_yn2)
      cases hun2_34 : isHN34PH (deltaPH (evalPH u.toTerm) n2)
      · rw [hun2_34, if_false_eq_true] at hob3
        cases hbranch : (!isAccPH (deltaPH (evalPH u.toTerm) n2) && Nat.beq (kindPH (evalPH u.toTerm)) 2)
        · rw [hbranch, if_false_eq_true] at hob3
          rcases (Bool.or_eq_true _ _).mp hob3 with htop34 | htr_ok
          · have hv_mid : noVars ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm) = true :=
              (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨rfl, PVal.noVars_toTerm u⟩, hz.hv⟩, hval_yn2.hv⟩
            have h34_mid : isHN34PH (evalPH ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm)) = true := by
              change isHN34PH (deltaPH (deltaPH (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm)) (evalPH yn2.toTerm)) = true
              rw [hph_yn2]; exact htop34
            exact hasBot_back hred_mid (hasBot_from_hn34_ph hv_mid h34_mid)
          · have ⟨htr1, htr_cmp⟩ := of_decide_eq_true htr_ok
            have hph_n2 : n2 = evalPH yn2.toTerm := hph_yn2.symm
            rw [hx] at hcle
            change c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2 ≤ rk + 1 at hcle
            rw [hph_n2] at htr1 htr_cmp hcle
            if hlt_rk : c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) (evalPH yn2.toTerm) ≤ rk then
              have htr_le_rk : tripleRank (evalPH u.toTerm) (evalPH z.toTerm) (evalPH yn2.toTerm) ≤ rk := by
                split at htr_cmp <;> omega
              exact hasBot_back hred_mid (ih_rk.2 u z yn2 hz hval_yn2 htr1 htr_le_rk)
            else
              have hcr_eq : c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) (evalPH yn2.toTerm) = rk + 1 := by omega
              rw [hcr_eq] at htr_cmp
              if hodd : (rk + 1) % 2 = 1 then
                rw [if_pos hodd] at htr_cmp
                exact hasBot_back hred_mid (ih_rk.2 u z yn2 hz hval_yn2 htr1 (by omega))
              else
                rw [if_neg hodd] at htr_cmp
                have heven : (rk + 1) % 2 = 0 := by omega
                exact hasBot_back hred_mid (same_s1_even heven u z yn2 hz hval_yn2 htr1 htr_cmp hu_lt)
        · rw [hbranch, if_true_eq_true] at hob3
          have ⟨hpr1, hpr_le⟩ := of_decide_eq_true hob3
          have hph_n2 : n2 = evalPH yn2.toTerm := hph_yn2.symm
          rw [hx] at hcle
          change c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2 ≤ rk + 1 at hcle
          rw [hph_n2] at hpr1 hpr_le hcle
          have hbot_u : HasBot (u.toTerm ⋅ yn2.toTerm) :=
            same_pair u yn2 hval_yn2 hpr1 (Nat.le_trans hpr_le hcle) hu_lt
          have hstep2 : Reduces ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm)
              ((u.toTerm ⋅ yn2.toTerm) ⋅ (z.toTerm ⋅ yn2.toTerm)) :=
            Reduces.next (Step.root u.toTerm z.toTerm yn2.toTerm) (Reduces.refl _)
          exact hasBot_back (reduces_trans hred_mid hstep2)
            (hasBot_app_left_bot ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm u, hval_yn2.hv⟩)
              ((Bool.and_eq_true _ _).mpr ⟨hz.hv, hval_yn2.hv⟩) hbot_u)
      · have hv_un2 : noVars (u.toTerm ⋅ yn2.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm u, hval_yn2.hv⟩
        have h34_un2 : isHN34PH (evalPH (u.toTerm ⋅ yn2.toTerm)) = true := by
          change isHN34PH (deltaPH (evalPH u.toTerm) (evalPH yn2.toTerm)) = true
          rw [hph_yn2]; exact hun2_34
        have hstep2 : Reduces ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm)
            ((u.toTerm ⋅ yn2.toTerm) ⋅ (z.toTerm ⋅ yn2.toTerm)) :=
          Reduces.next (Step.root u.toTerm z.toTerm yn2.toTerm) (Reduces.refl _)
        exact hasBot_back (reduces_trans hred_mid hstep2)
          (hasBot_app_left_bot hv_un2 ((Bool.and_eq_true _ _).mpr ⟨hz.hv, hval_yn2.hv⟩)
            (hasBot_from_hn34_ph hv_un2 h34_un2))
    | s2 x1 x2 =>
      have hk2 : kindPH (evalPH (PVal.s2 x1 x2).toTerm) = 2 :=
        (kindPH_s2 _ _ (PVal.isAccPH_toTerm x1) (PVal.isAccPH_toTerm x2)).2
      have hob4 := ob4_chk (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2 (PVal.isAccPH_toTerm (.s2 x1 x2)) hz.reach hr_n2
      dsimp only [ob4_fn] at hob4
      rw [hx] at hcpos hcle
      have hcr0 : Nat.beq (c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2) 0 = false := by
        change 1 ≤ c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2 at hcpos
        cases hc : c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2
        · rw [hc] at hcpos; cases hcpos
        · rfl
      have hk2_f : (!Nat.beq (kindPH (evalPH (PVal.s2 x1 x2).toTerm)) 2) = false := by rw [hk2]; rfl
      have hcond4 : (Nat.beq (c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2) 0 ||
          !Nat.beq (kindPH (evalPH (PVal.s2 x1 x2).toTerm)) 2 || isHN34PH (evalPH z.toTerm) || isHN34PH n2) = false := by
        rw [hcr0, hk2_f, hz.not_hn34, hn2_34]; rfl
      rw [hcond4, if_false_eq_true] at hob4
      have ⟨hpair_acc, hall_bits⟩ := (Bool.and_eq_true _ _).mp hob4
      have ⟨hz_acc, hxz_acc⟩ := (Bool.and_eq_true _ _).mp hpair_acc
      obtain ⟨vz, hvz_eq⟩ := hz.acc_is_pval hz_acc
      subst hvz_eq
      have hfw_ne : deltaP (evalP (PVal.s2 x1 x2).toTerm) (evalP vz.toTerm) ≠ .p37 := by
        change isAccPH (evalPH ((PVal.s2 x1 x2).toTerm ⋅ vz.toTerm)) = true at hxz_acc
        rw [isAccPH_evalPH (t := (PVal.s2 x1 x2).toTerm ⋅ vz.toTerm)
          ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 x1 x2), PVal.noVars_toTerm vz⟩)] at hxz_acc
        exact of_decide_eq_true hxz_acc
      let rap := pvalApply (.s2 x1 x2) vz hfw_ne
      have hred_all : Reduces ((S ⋅ (PVal.s2 x1 x2).toTerm ⋅ y.toTerm) ⋅ (Arg.pval vz).toTerm) (rap.val.toTerm ⋅ yn2.toTerm) :=
        Reduces.next (Step.root (PVal.s2 x1 x2).toTerm y.toTerm vz.toTerm)
          (reduces_trans (reduces_left rap.red _) (reduces_right _ hred_yn2))
      cases hrv : rap.val with
      | s =>
        exfalso
        have hph0 : evalPH rap.val.toTerm = ph0 := by rw [hrv]; rfl
        rw [← evalPH_reduces rap.red] at hph0
        exact deltaPH_ne_ph0 (evalPH (PVal.s2 x1 x2).toTerm) (evalPH vz.toTerm) hph0
      | s1 w0 =>
        obtain ⟨hbad, _⟩ := rap.s1_imp w0 hrv
        cases hbad
      | zachos m n =>
        rw [hrv] at hred_all
        exact hasBot_back hred_all (hasBot_zachos_app m n hval_yn2.hv)
      | s2 a b =>
        have hmem : out2dHas (evalPH (PVal.s2 x1 x2).toTerm) (evalPH (Arg.pval vz).toTerm) (evalPH a.toTerm) (evalPH b.toTerm) = true :=
          rap.s2_mem a b hrv
        have hbit := out2dAllPairs_sound hall_bits hmem
        rw [hrv] at hred_all
        rcases (Bool.or_eq_true _ _).mp hbit with h34_ab | htr_ab
        · have hv_ab : noVars ((S ⋅ a.toTerm ⋅ b.toTerm) ⋅ yn2.toTerm) = true :=
            (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 a b), hval_yn2.hv⟩
          have h34_term : isHN34PH (evalPH ((S ⋅ a.toTerm ⋅ b.toTerm) ⋅ yn2.toTerm)) = true := by
            change isHN34PH (deltaPH (deltaPH (deltaPH ph0 (evalPH a.toTerm)) (evalPH b.toTerm)) (evalPH yn2.toTerm)) = true
            rw [hph_yn2]; exact h34_ab
          exact hasBot_back hred_all (hasBot_from_hn34_ph hv_ab h34_term)
        · have ⟨htr1, htr_lt⟩ := of_decide_eq_true htr_ab
          have hph_n2 : n2 = evalPH yn2.toTerm := hph_yn2.symm
          change c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH (Arg.pval vz).toTerm) n2 ≤ rk + 1 at hcle
          rw [hph_n2] at htr1 htr_lt hcle
          have htr_le : tripleRank (evalPH a.toTerm) (evalPH (Arg.pval b).toTerm) (evalPH yn2.toTerm) ≤ rk := by
            change tripleRank (evalPH a.toTerm) (evalPH b.toTerm) (evalPH yn2.toTerm) ≤ rk; omega
          exact hasBot_back hred_all (ih_rk.2 a (.pval b) yn2 (validArg_pval b) hval_yn2 htr1 htr_le)
  · have h34_yz : isHN34PH (evalPH (y.toTerm ⋅ z.toTerm)) = true := hn2_34
    exact hasBot_back hroot1 (hasBot_app_right_bot hvxz hvyz (hasBot_from_hn34_ph hvyz h34_yz))

theorem rankSolved_step {rk : Nat} (ih_rk : RankSolvedUpTo rk) : RankSolvedUpTo (rk + 1) := by
  if hodd : (rk + 1) % 2 = 1 then
    have hM : ∀ (M : Nat),
        (∀ (f : PVal) (z : Arg), 2 * f.size ≤ M → ValidArg z →
          1 ≤ pairRank (evalPH f.toTerm) (evalPH z.toTerm) →
          pairRank (evalPH f.toTerm) (evalPH z.toTerm) ≤ rk + 1 →
          HasBot (f.toTerm ⋅ z.toTerm)) ∧
        (∀ (x : PVal) (y z : Arg), 2 * (x.size + y.pvalSize) + 1 ≤ M → ValidArg y → ValidArg z →
          1 ≤ tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) →
          tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) ≤ rk + 1 →
          HasBot ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm)) := by
      intro M
      induction M with
      | zero =>
        refine ⟨fun f _ hle => False.elim (by have := PVal.size_pos f; omega),
                fun _ _ _ hle => False.elim (by omega)⟩
      | succ M' ihM =>
        refine ⟨?_, ?_⟩
        · intro f z hsz hz hpos hle
          cases hf : f with
          | s =>
            have hob1 := (Bool.and_eq_true _ _).mp (ob1_chk ph0 (evalPH z.toTerm) (PVal.isAccPH_toTerm .s) hz.reach)
            rw [hf] at hpos; change 1 ≤ pairRank ph0 (evalPH z.toTerm) at hpos
            have hk := hob1.1; rw [if_pos hpos] at hk
            have hk2 : kindPH ph0 = 2 := of_decide_eq_true (and_left hk)
            cases hk2
          | s1 u =>
            have hk1 := (kindPH_s1 (evalPH u.toTerm) (PVal.isAccPH_toTerm u)).2
            have hob1 := (Bool.and_eq_true _ _).mp (ob1_chk (evalPH (PVal.s1 u).toTerm) (evalPH z.toTerm) (PVal.isAccPH_toTerm (.s1 u)) hz.reach)
            rw [hf] at hpos
            have hk := hob1.1; rw [if_pos hpos] at hk
            have hk2 : kindPH (deltaPH ph0 (evalPH u.toTerm)) = 2 := of_decide_eq_true (and_left hk)
            rw [hk1] at hk2; cases hk2
          | zachos m n =>
            exact hasBot_zachos_app m n hz.hv
          | s2 a b =>
            rw [hf] at hpos hle hsz
            cases h34 : isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))
            · have hob2 := ob2_chk (evalPH a.toTerm) (evalPH b.toTerm) (evalPH z.toTerm) (PVal.isAccPH_toTerm a) (PVal.isAccPH_toTerm b) hz.reach
              dsimp only [ob2_fn] at hob2
              have hpr0 : Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 = false := by
                cases hp : pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)
                · rw [hp] at hpos; cases hpos
                · rfl
              have hc2 : (Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 ||
                  isHN34PH (evalPH z.toTerm) || isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))) = false := by
                rw [hpr0, hz.not_hn34, h34]; rfl
              change (if (Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 ||
                  isHN34PH (evalPH z.toTerm) || isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))) = true then true else _) = true at hob2
              rw [hc2, if_false_eq_true] at hob2
              have ⟨htr1, htr_le⟩ := of_decide_eq_true hob2
              have hsub_M : 2 * (a.size + (Arg.pval b).pvalSize) + 1 ≤ M' := by
                change 2 * (a.size + b.size + 1) ≤ M' + 1 at hsz
                change 2 * (a.size + b.size) + 1 ≤ M'; omega
              exact ihM.2 a (.pval b) z hsub_M (validArg_pval b) hz htr1 (Nat.le_trans htr_le hle)
            · exact hasBot_from_hn34_ph ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 a b), hz.hv⟩) h34
        · intro x y z hsz hy hz hpos hle
          have hvxz : noVars (x.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm x, hz.hv⟩
          have hvyz : noVars (y.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨hy.hv, hz.hv⟩
          have hroot : Reduces ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) ((x.toTerm ⋅ z.toTerm) ⋅ (y.toTerm ⋅ z.toTerm)) :=
            Reduces.next (Step.root x.toTerm y.toTerm z.toTerm) (Reduces.refl _)
          rcases tripleRank_cases hpos hle with hn2 | hn1 | hL | hR | hC
          · exact hasBot_back hroot (hasBot_app_right_bot hvxz hvyz (hasBot_from_hn34_ph hvyz hn2))
          · exact hasBot_back hroot (hasBot_app_left_bot hvxz hvyz (hasBot_from_hn34_ph hvxz hn1))
          · have hsub_M : 2 * x.size ≤ M' := by omega
            exact hasBot_back hroot (hasBot_app_left_bot hvxz hvyz (ihM.1 x z hsub_M hz hL.1 hL.2))
          · obtain ⟨vy, hvy_eq⟩ := hy.acc_is_pval hR.1
            subst hvy_eq
            have hx_pos := PVal.size_pos x
            have hsub_M : 2 * vy.size ≤ M' := by
              change 2 * (x.size + vy.size) + 1 ≤ M' + 1 at hsz; omega
            exact hasBot_back hroot (hasBot_app_right_bot hvxz hvyz (ihM.1 vy z hsub_M hz hR.2.1 hR.2.2.1))
          · exact solve_c3_step ih_rk
              (fun u w hw hp1 hple hult => ihM.1 u w (by omega) hw hp1 hple)
              (fun hev => False.elim (by omega))
              x rfl y z hy hz hC.1 hC.2
    exact ⟨fun f z => (hM (2 * f.size)).1 f z (Nat.le_refl _),
           fun x y z => (hM (2 * (x.size + y.pvalSize) + 1)).2 x y z (Nat.le_refl _)⟩
  else
    have heven : (rk + 1) % 2 = 0 := by omega
    have hM : ∀ (M : Nat),
        (∀ (f : PVal) (z : Arg), 2 * f.size ≤ M → ValidArg z →
          1 ≤ pairRank (evalPH f.toTerm) (evalPH z.toTerm) →
          pairRank (evalPH f.toTerm) (evalPH z.toTerm) ≤ rk + 1 →
          HasBot (f.toTerm ⋅ z.toTerm)) ∧
        (∀ (x : PVal) (y z : Arg), 2 * x.size + 1 ≤ M → ValidArg y → ValidArg z →
          1 ≤ tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) →
          tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) ≤ rk + 1 →
          HasBot ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm)) := by
      intro M
      induction M with
      | zero =>
        refine ⟨fun f _ hle => False.elim (by have := PVal.size_pos f; omega),
                fun _ _ _ hle => False.elim (by omega)⟩
      | succ M' ihM =>
        refine ⟨?_, ?_⟩
        · intro f z hsz hz hpos hle
          cases hf : f with
          | s =>
            have hob1 := (Bool.and_eq_true _ _).mp (ob1_chk ph0 (evalPH z.toTerm) (PVal.isAccPH_toTerm .s) hz.reach)
            rw [hf] at hpos; change 1 ≤ pairRank ph0 (evalPH z.toTerm) at hpos
            have hk := hob1.1; rw [if_pos hpos] at hk
            have hk2 : kindPH ph0 = 2 := of_decide_eq_true (and_left hk)
            cases hk2
          | s1 u =>
            have hk1 := (kindPH_s1 (evalPH u.toTerm) (PVal.isAccPH_toTerm u)).2
            have hob1 := (Bool.and_eq_true _ _).mp (ob1_chk (evalPH (PVal.s1 u).toTerm) (evalPH z.toTerm) (PVal.isAccPH_toTerm (.s1 u)) hz.reach)
            rw [hf] at hpos
            have hk := hob1.1; rw [if_pos hpos] at hk
            have hk2 : kindPH (deltaPH ph0 (evalPH u.toTerm)) = 2 := of_decide_eq_true (and_left hk)
            rw [hk1] at hk2; cases hk2
          | zachos m n =>
            exact hasBot_zachos_app m n hz.hv
          | s2 a b =>
            rw [hf] at hpos hle hsz
            cases h34 : isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))
            · have hob2 := ob2_chk (evalPH a.toTerm) (evalPH b.toTerm) (evalPH z.toTerm) (PVal.isAccPH_toTerm a) (PVal.isAccPH_toTerm b) hz.reach
              dsimp only [ob2_fn] at hob2
              have hpr0 : Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 = false := by
                cases hp : pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)
                · rw [hp] at hpos; cases hpos
                · rfl
              have hc2 : (Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 ||
                  isHN34PH (evalPH z.toTerm) || isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))) = false := by
                rw [hpr0, hz.not_hn34, h34]; rfl
              change (if (Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 ||
                  isHN34PH (evalPH z.toTerm) || isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))) = true then true else _) = true at hob2
              rw [hc2, if_false_eq_true] at hob2
              have ⟨htr1, htr_le⟩ := of_decide_eq_true hob2
              have hb_pos := PVal.size_pos b
              have hsub_M : 2 * a.size + 1 ≤ M' := by
                change 2 * (a.size + b.size + 1) ≤ M' + 1 at hsz; omega
              exact ihM.2 a (.pval b) z hsub_M (validArg_pval b) hz htr1 (Nat.le_trans htr_le hle)
            · exact hasBot_from_hn34_ph ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 a b), hz.hv⟩) h34
        · intro x y z hsz hy hz hpos hle
          have hvxz : noVars (x.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm x, hz.hv⟩
          have hvyz : noVars (y.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨hy.hv, hz.hv⟩
          have hroot : Reduces ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) ((x.toTerm ⋅ z.toTerm) ⋅ (y.toTerm ⋅ z.toTerm)) :=
            Reduces.next (Step.root x.toTerm y.toTerm z.toTerm) (Reduces.refl _)
          rcases tripleRank_cases hpos hle with hn2 | hn1 | hL | hR | hC
          · exact hasBot_back hroot (hasBot_app_right_bot hvxz hvyz (hasBot_from_hn34_ph hvyz hn2))
          · exact hasBot_back hroot (hasBot_app_left_bot hvxz hvyz (hasBot_from_hn34_ph hvxz hn1))
          · have hsub_M : 2 * x.size ≤ M' := by omega
            exact hasBot_back hroot (hasBot_app_left_bot hvxz hvyz (ihM.1 x z hsub_M hz hL.1 hL.2))
          · obtain ⟨vy, hvy_eq⟩ := hy.acc_is_pval hR.1
            subst hvy_eq
            have hR_step : (rk + 1) % 2 = 0 → pairRank (evalPH vy.toTerm) (evalPH z.toTerm) + 1 ≤ rk + 1 := hR.2.2.2
            have hR1 : 1 ≤ pairRank (evalPH vy.toTerm) (evalPH z.toTerm) := hR.2.1
            have hpr_rk : pairRank (evalPH vy.toTerm) (evalPH z.toTerm) ≤ rk := by
              have := hR_step heven; omega
            exact hasBot_back hroot (hasBot_app_right_bot hvxz hvyz (ih_rk.1 vy z hz hR1 hpr_rk))
          · exact solve_c3_step ih_rk
              (fun u w hw hp1 hple hult => ihM.1 u w (by omega) hw hp1 hple)
              (fun _ u z' w' hz' hw' ht1 htle hult => ihM.2 u z' w' (by omega) hz' hw' ht1 htle)
              x rfl y z hy hz hC.1 hC.2
    exact ⟨fun f z => (hM (2 * f.size)).1 f z (Nat.le_refl _),
           fun x y z => (hM (2 * x.size + 1)).2 x y z (Nat.le_refl _)⟩

theorem rankSolved_all : ∀ k : Nat, RankSolvedUpTo k
  | 0 => rankSolved_zero
  | k + 1 => rankSolved_step (rankSolved_all k)

theorem pval_root_pair_hasBot (f z : PVal) (h37 : evalP (f.toTerm ⋅ z.toTerm) = .p37) :
    HasBot (f.toTerm ⋅ z.toTerm) := by
  have hnot_acc : (!isAccPH (deltaPH (evalPH f.toTerm) (evalPH z.toTerm))) = true := by
    change (!isAccPH (evalPH (f.toTerm ⋅ z.toTerm))) = true
    rw [isAccPH_evalPH (t := f.toTerm ⋅ z.toTerm)
      ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm f, PVal.noVars_toTerm z⟩), h37]
    rfl
  have hob1 := (Bool.and_eq_true _ _).mp (ob1_chk (evalPH f.toTerm) (evalPH z.toTerm) (PVal.isAccPH_toTerm f) (evalPH_isReach (PVal.noVars_toTerm z)))
  have hr := hob1.2
  have hc : (isAccPH (evalPH f.toTerm) && isAccPH (evalPH z.toTerm) &&
      !isAccPH (deltaPH (evalPH f.toTerm) (evalPH z.toTerm))) = true := by
    rw [PVal.isAccPH_toTerm f, PVal.isAccPH_toTerm z, hnot_acc]; rfl
  rw [hc, if_true_eq_true] at hr
  have ⟨h1, h17⟩ := of_decide_eq_true hr
  exact (rankSolved_all 17).1 f (.pval z) (validArg_pval z) h1 h17

theorem evalP_eq_p37_implies_hasBot : ∀ {t : Term}, noVars t = true → evalP t = .p37 → HasBot t
  | .s, _, h37 => by cases h37
  | .var _, hv, _ => by cases hv
  | .app a b, hv, h37 => by
    have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
    if ha37 : evalP a = .p37 then
      exact hasBot_app_left_bot hva hvb (evalP_eq_p37_implies_hasBot hva ha37)
    else if hb37 : evalP b = .p37 then
      exact hasBot_app_right_bot hva hvb (evalP_eq_p37_implies_hasBot hvb hb37)
    else
      let ⟨va, hra⟩ := toPVal a hva ha37
      let ⟨vb, hrb⟩ := toPVal b hvb hb37
      have hprod37 : evalP (va.toTerm ⋅ vb.toTerm) = .p37 := by
        change deltaP (evalP va.toTerm) (evalP vb.toTerm) = .p37
        rw [← evalP_reduces hra, ← evalP_reduces hrb]; exact h37
      have hred : Reduces (a ⋅ b) (va.toTerm ⋅ vb.toTerm) :=
        reduces_trans (reduces_left hra b) (reduces_right va.toTerm hrb)
      exact hasBot_back hred (pval_root_pair_hasBot va vb hprod37)

/-- **Barendregt, Endrullis, Klop & Waldmann's Open Question 5 (Constructive Resolution)**:
    A closed pure-`S` combinator `t` is Böhm-tree productive (`Productive t`) if and only if
    the 39-state finite `S`-algebra `A_P` accepts `t` (`evalP t ≠ .p37`). -/
theorem barendregt_open_question_5 {t : Term} (hv : noVars t = true) :
    Productive t ↔ evalP t ≠ .p37 := by
  constructor
  · intro hprod h37
    exact hprod (evalP_eq_p37_implies_hasBot hv h37)
  · exact evalP_ne_p37_implies_productive hv

theorem productive_or_hasBot_closed {t : Term} (hv : noVars t = true) :
    Productive t ∨ HasBot t :=
  if h37 : evalP t = .p37 then
    Or.inr (evalP_eq_p37_implies_hasBot hv h37)
  else
    Or.inl (evalP_ne_p37_implies_productive hv h37)

end FormalQ5Final

#print axioms FormalQ5Final.barendregt_open_question_5
#print axioms FormalQ5Final.productive_or_hasBot_closed
