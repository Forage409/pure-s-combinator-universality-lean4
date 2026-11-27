import formal_q10_q5_simplified.q10_thm9_defs

namespace SimplifiedQ10Q5

theorem snIdx_ofSnIdx_chk : checkNat1 39 (fun i => Nat.beq (snIdx (ofSnIdx i)) i) = true := rfl
theorem hnIdx_ofHnIdx_chk : checkNat1 35 (fun i => Nat.beq (hnIdx (ofHnIdx i)) i) = true := rfl
theorem hna_dag_cert_chk : hna_dag_cert_ok = true := rfl
theorem sn_ranks_r1 : sn_ranks_row 1 = true := rfl
theorem sn_ranks_r3 : sn_ranks_row 3 = true := rfl
theorem sn_ranks_r5 : sn_ranks_row 5 = true := rfl
theorem sn_ranks_r7 : sn_ranks_row 7 = true := rfl
theorem sn_ranks_r9 : sn_ranks_row 9 = true := rfl
theorem sn_ranks_r11 : sn_ranks_row 11 = true := rfl
theorem sn_ranks_r13 : sn_ranks_row 13 = true := rfl
theorem sn_ranks_r15 : sn_ranks_row 15 = true := rfl
theorem sn_ranks_r17 : sn_ranks_row 17 = true := rfl
theorem sn_ranks_r19 : sn_ranks_row 19 = true := rfl
theorem sn_ranks_r21 : sn_ranks_row 21 = true := rfl
theorem sn_ranks_r23 : sn_ranks_row 23 = true := rfl
theorem sn_ranks_r25 : sn_ranks_row 25 = true := rfl
theorem sn_ranks_r27 : sn_ranks_row 27 = true := rfl
theorem sn_ranks_r29 : sn_ranks_row 29 = true := rfl
theorem sn_ranks_r31 : sn_ranks_row 31 = true := rfl
theorem sn_ranks_r33 : sn_ranks_row 33 = true := rfl
theorem sn_ranks_r35 : sn_ranks_row 35 = true := rfl
theorem sn_ranks_r37 : sn_ranks_row 37 = true := rfl
theorem hna_valid_r0 : hna_valid_row 0 = true := rfl
theorem hna_valid_r2 : hna_valid_row 2 = true := rfl
theorem hna_valid_r4 : hna_valid_row 4 = true := rfl
theorem hna_valid_r6 : hna_valid_row 6 = true := rfl
theorem hna_valid_r8 : hna_valid_row 8 = true := rfl
theorem hna_valid_r10 : hna_valid_row 10 = true := rfl
theorem hna_valid_r12 : hna_valid_row 12 = true := rfl
theorem hna_valid_r14 : hna_valid_row 14 = true := rfl
theorem hna_valid_r16 : hna_valid_row 16 = true := rfl
theorem hna_valid_r18 : hna_valid_row 18 = true := rfl
theorem hna_valid_r20 : hna_valid_row 20 = true := rfl
theorem hna_valid_r22 : hna_valid_row 22 = true := rfl
theorem hna_valid_r24 : hna_valid_row 24 = true := rfl
theorem hna_valid_r26 : hna_valid_row 26 = true := rfl
theorem hna_valid_r28 : hna_valid_row 28 = true := rfl
theorem hna_valid_r30 : hna_valid_row 30 = true := rfl
theorem hna_valid_r32 : hna_valid_row 32 = true := rfl
theorem hna_valid_r34 : hna_valid_row 34 = true := rfl

end SimplifiedQ10Q5
