import formal_q10_q5_simplified.q10_thm9_defs

namespace SimplifiedQ10Q5

theorem dsn_bridge_chk : checkNat2 39 39 (fun i j => Nat.beq (snIdx (deltaSN (ofSnIdx i) (ofSnIdx j))) (dsnIdx i j) && Nat.ble (dsnIdx i j + 1) 39) = true := rfl
theorem dhn_bridge_chk : checkNat2 35 35 (fun i j => Nat.beq (hnIdx (deltaHN (ofHnIdx i) (ofHnIdx j))) (dhnIdx i j) && Nat.ble (dhnIdx i j + 1) 35) = true := rfl
theorem dsn_s_law_r0 : dsn_s_law_row 0 = true := rfl
theorem dsn_s_law_r2 : dsn_s_law_row 2 = true := rfl
theorem dsn_s_law_r4 : dsn_s_law_row 4 = true := rfl
theorem dsn_s_law_r6 : dsn_s_law_row 6 = true := rfl
theorem dsn_s_law_r8 : dsn_s_law_row 8 = true := rfl
theorem dsn_s_law_r10 : dsn_s_law_row 10 = true := rfl
theorem dsn_s_law_r12 : dsn_s_law_row 12 = true := rfl
theorem dsn_s_law_r14 : dsn_s_law_row 14 = true := rfl
theorem dsn_s_law_r16 : dsn_s_law_row 16 = true := rfl
theorem dsn_s_law_r18 : dsn_s_law_row 18 = true := rfl
theorem dsn_s_law_r20 : dsn_s_law_row 20 = true := rfl
theorem dsn_s_law_r22 : dsn_s_law_row 22 = true := rfl
theorem dsn_s_law_r24 : dsn_s_law_row 24 = true := rfl
theorem dsn_s_law_r26 : dsn_s_law_row 26 = true := rfl
theorem dsn_s_law_r28 : dsn_s_law_row 28 = true := rfl
theorem dsn_s_law_r30 : dsn_s_law_row 30 = true := rfl
theorem dsn_s_law_r32 : dsn_s_law_row 32 = true := rfl
theorem dsn_s_law_r34 : dsn_s_law_row 34 = true := rfl
theorem dsn_s_law_r36 : dsn_s_law_row 36 = true := rfl
theorem dsn_s_law_r38 : dsn_s_law_row 38 = true := rfl
theorem dhn_s_law_r1 : dhn_s_law_row 1 = true := rfl
theorem dhn_s_law_r3 : dhn_s_law_row 3 = true := rfl
theorem dhn_s_law_r5 : dhn_s_law_row 5 = true := rfl
theorem dhn_s_law_r7 : dhn_s_law_row 7 = true := rfl
theorem dhn_s_law_r9 : dhn_s_law_row 9 = true := rfl
theorem dhn_s_law_r11 : dhn_s_law_row 11 = true := rfl
theorem dhn_s_law_r13 : dhn_s_law_row 13 = true := rfl
theorem dhn_s_law_r15 : dhn_s_law_row 15 = true := rfl
theorem dhn_s_law_r17 : dhn_s_law_row 17 = true := rfl
theorem dhn_s_law_r19 : dhn_s_law_row 19 = true := rfl
theorem dhn_s_law_r21 : dhn_s_law_row 21 = true := rfl
theorem dhn_s_law_r23 : dhn_s_law_row 23 = true := rfl
theorem dhn_s_law_r25 : dhn_s_law_row 25 = true := rfl
theorem dhn_s_law_r27 : dhn_s_law_row 27 = true := rfl
theorem dhn_s_law_r29 : dhn_s_law_row 29 = true := rfl
theorem dhn_s_law_r31 : dhn_s_law_row 31 = true := rfl
theorem dhn_s_law_r33 : dhn_s_law_row 33 = true := rfl

end SimplifiedQ10Q5
