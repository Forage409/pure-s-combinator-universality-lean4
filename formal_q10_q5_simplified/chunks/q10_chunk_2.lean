import formal_q10_q5_simplified.q10_thm9_defs

namespace SimplifiedQ10Q5

theorem sn_meta_chk : checkNat2 39 39 (fun x y => Nat.beq (dsnIdx 38 y) 38 && Nat.beq (dsnIdx x 38) 38 && (Nat.beq x 38 || !Nat.beq (dsnIdx 0 x) 38) && (Nat.beq x 38 || Nat.beq y 38 || !Nat.beq (dsnIdx (dsnIdx 0 x) y) 38)) = true := rfl
theorem hn_meta_chk : checkNat2 35 35 (fun x y => Nat.beq (dhnIdx 34 y) 34 && !Nat.beq (dhnIdx x y) 0 && !Nat.beq (dhnIdx 0 x) 34 && !Nat.beq (dhnIdx (dhnIdx 0 x) y) 34) = true := rfl
theorem sn_ranks_r0 : sn_ranks_row 0 = true := rfl
theorem sn_ranks_r2 : sn_ranks_row 2 = true := rfl
theorem sn_ranks_r4 : sn_ranks_row 4 = true := rfl
theorem sn_ranks_r6 : sn_ranks_row 6 = true := rfl
theorem sn_ranks_r8 : sn_ranks_row 8 = true := rfl
theorem sn_ranks_r10 : sn_ranks_row 10 = true := rfl
theorem sn_ranks_r12 : sn_ranks_row 12 = true := rfl
theorem sn_ranks_r14 : sn_ranks_row 14 = true := rfl
theorem sn_ranks_r16 : sn_ranks_row 16 = true := rfl
theorem sn_ranks_r18 : sn_ranks_row 18 = true := rfl
theorem sn_ranks_r20 : sn_ranks_row 20 = true := rfl
theorem sn_ranks_r22 : sn_ranks_row 22 = true := rfl
theorem sn_ranks_r24 : sn_ranks_row 24 = true := rfl
theorem sn_ranks_r26 : sn_ranks_row 26 = true := rfl
theorem sn_ranks_r28 : sn_ranks_row 28 = true := rfl
theorem sn_ranks_r30 : sn_ranks_row 30 = true := rfl
theorem sn_ranks_r32 : sn_ranks_row 32 = true := rfl
theorem sn_ranks_r34 : sn_ranks_row 34 = true := rfl
theorem sn_ranks_r36 : sn_ranks_row 36 = true := rfl
theorem sn_ranks_r38 : sn_ranks_row 38 = true := rfl
theorem hna_valid_r1 : hna_valid_row 1 = true := rfl
theorem hna_valid_r3 : hna_valid_row 3 = true := rfl
theorem hna_valid_r5 : hna_valid_row 5 = true := rfl
theorem hna_valid_r7 : hna_valid_row 7 = true := rfl
theorem hna_valid_r9 : hna_valid_row 9 = true := rfl
theorem hna_valid_r11 : hna_valid_row 11 = true := rfl
theorem hna_valid_r13 : hna_valid_row 13 = true := rfl
theorem hna_valid_r15 : hna_valid_row 15 = true := rfl
theorem hna_valid_r17 : hna_valid_row 17 = true := rfl
theorem hna_valid_r19 : hna_valid_row 19 = true := rfl
theorem hna_valid_r21 : hna_valid_row 21 = true := rfl
theorem hna_valid_r23 : hna_valid_row 23 = true := rfl
theorem hna_valid_r25 : hna_valid_row 25 = true := rfl
theorem hna_valid_r27 : hna_valid_row 27 = true := rfl
theorem hna_valid_r29 : hna_valid_row 29 = true := rfl
theorem hna_valid_r31 : hna_valid_row 31 = true := rfl
theorem hna_valid_r33 : hna_valid_row 33 = true := rfl

end SimplifiedQ10Q5
