import formal_q10_q5_simplified.q10_thm9_defs

namespace SimplifiedQ10Q5

theorem isS2_sn_chk : checkNat2 39 39 (fun x y => Nat.beq x 38 || Nat.beq y 38 || isS2SNTree.lookup (dsnIdx (dsnIdx 0 x) y)) = true := rfl
theorem hna_bridge_chk : checkNat2 35 35 (fun i j => Nat.beq (hnA (ofHnIdx i) (ofHnIdx j)) (hnaIdx i j)) = true := rfl
theorem dsn_s_law_r1 : dsn_s_law_row 1 = true := rfl
theorem dsn_s_law_r3 : dsn_s_law_row 3 = true := rfl
theorem dsn_s_law_r5 : dsn_s_law_row 5 = true := rfl
theorem dsn_s_law_r7 : dsn_s_law_row 7 = true := rfl
theorem dsn_s_law_r9 : dsn_s_law_row 9 = true := rfl
theorem dsn_s_law_r11 : dsn_s_law_row 11 = true := rfl
theorem dsn_s_law_r13 : dsn_s_law_row 13 = true := rfl
theorem dsn_s_law_r15 : dsn_s_law_row 15 = true := rfl
theorem dsn_s_law_r17 : dsn_s_law_row 17 = true := rfl
theorem dsn_s_law_r19 : dsn_s_law_row 19 = true := rfl
theorem dsn_s_law_r21 : dsn_s_law_row 21 = true := rfl
theorem dsn_s_law_r23 : dsn_s_law_row 23 = true := rfl
theorem dsn_s_law_r25 : dsn_s_law_row 25 = true := rfl
theorem dsn_s_law_r27 : dsn_s_law_row 27 = true := rfl
theorem dsn_s_law_r29 : dsn_s_law_row 29 = true := rfl
theorem dsn_s_law_r31 : dsn_s_law_row 31 = true := rfl
theorem dsn_s_law_r33 : dsn_s_law_row 33 = true := rfl
theorem dsn_s_law_r35 : dsn_s_law_row 35 = true := rfl
theorem dsn_s_law_r37 : dsn_s_law_row 37 = true := rfl
theorem dhn_s_law_r0 : dhn_s_law_row 0 = true := rfl
theorem dhn_s_law_r2 : dhn_s_law_row 2 = true := rfl
theorem dhn_s_law_r4 : dhn_s_law_row 4 = true := rfl
theorem dhn_s_law_r6 : dhn_s_law_row 6 = true := rfl
theorem dhn_s_law_r8 : dhn_s_law_row 8 = true := rfl
theorem dhn_s_law_r10 : dhn_s_law_row 10 = true := rfl
theorem dhn_s_law_r12 : dhn_s_law_row 12 = true := rfl
theorem dhn_s_law_r14 : dhn_s_law_row 14 = true := rfl
theorem dhn_s_law_r16 : dhn_s_law_row 16 = true := rfl
theorem dhn_s_law_r18 : dhn_s_law_row 18 = true := rfl
theorem dhn_s_law_r20 : dhn_s_law_row 20 = true := rfl
theorem dhn_s_law_r22 : dhn_s_law_row 22 = true := rfl
theorem dhn_s_law_r24 : dhn_s_law_row 24 = true := rfl
theorem dhn_s_law_r26 : dhn_s_law_row 26 = true := rfl
theorem dhn_s_law_r28 : dhn_s_law_row 28 = true := rfl
theorem dhn_s_law_r30 : dhn_s_law_row 30 = true := rfl
theorem dhn_s_law_r32 : dhn_s_law_row 32 = true := rfl
theorem dhn_s_law_r34 : dhn_s_law_row 34 = true := rfl

end SimplifiedQ10Q5
