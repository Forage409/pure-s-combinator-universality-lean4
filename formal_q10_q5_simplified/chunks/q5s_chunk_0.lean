import formal_q10_q5_simplified.q5_defs

namespace SimplifiedQ10Q5
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem pIdx_ofPIdx_chk : checkNat1 39 (fun i => Nat.beq (pIdx (ofPIdx i)) i) = true := rfl
theorem c3_ph0_idx_thm : checkNat2 113 113 (fun z n2 => Nat.beq (c3RankIdx 0 z n2) 0) = true := rfl
theorem rankP_idx_r2 : rankP_idx_row 2 = true := rfl
theorem rankP_idx_r6 : rankP_idx_row 6 = true := rfl
theorem rankP_idx_r10 : rankP_idx_row 10 = true := rfl
theorem rankP_idx_r14 : rankP_idx_row 14 = true := rfl
theorem rankP_idx_r18 : rankP_idx_row 18 = true := rfl
theorem rankP_idx_r22 : rankP_idx_row 22 = true := rfl
theorem rankP_idx_r26 : rankP_idx_row 26 = true := rfl
theorem rankP_idx_r30 : rankP_idx_row 30 = true := rfl
theorem rankP_idx_r34 : rankP_idx_row 34 = true := rfl
theorem rankP_idx_r38 : rankP_idx_row 38 = true := rfl
theorem nerode_sep_r3 : nerode_sep_row 3 = true := rfl
theorem nerode_sep_r7 : nerode_sep_row 7 = true := rfl
theorem nerode_sep_r11 : nerode_sep_row 11 = true := rfl
theorem nerode_sep_r15 : nerode_sep_row 15 = true := rfl
theorem nerode_sep_r19 : nerode_sep_row 19 = true := rfl
theorem nerode_sep_r23 : nerode_sep_row 23 = true := rfl
theorem nerode_sep_r27 : nerode_sep_row 27 = true := rfl
theorem nerode_sep_r31 : nerode_sep_row 31 = true := rfl
theorem nerode_sep_r35 : nerode_sep_row 35 = true := rfl
theorem nerode_sep_r39 : nerode_sep_row 39 = true := rfl
theorem nerode_sep_r43 : nerode_sep_row 43 = true := rfl
theorem nerode_sep_r47 : nerode_sep_row 47 = true := rfl
theorem nerode_sep_r51 : nerode_sep_row 51 = true := rfl
theorem nerode_sep_r55 : nerode_sep_row 55 = true := rfl
theorem nerode_sep_r59 : nerode_sep_row 59 = true := rfl
theorem nerode_sep_r63 : nerode_sep_row 63 = true := rfl
theorem nerode_sep_r67 : nerode_sep_row 67 = true := rfl
theorem nerode_sep_r71 : nerode_sep_row 71 = true := rfl
theorem nerode_sep_r75 : nerode_sep_row 75 = true := rfl
theorem nerode_sep_r79 : nerode_sep_row 79 = true := rfl
theorem nerode_sep_r83 : nerode_sep_row 83 = true := rfl
theorem nerode_sep_r87 : nerode_sep_row 87 = true := rfl
theorem nerode_sep_r91 : nerode_sep_row 91 = true := rfl
theorem nerode_sep_r95 : nerode_sep_row 95 = true := rfl
theorem nerode_sep_r99 : nerode_sep_row 99 = true := rfl
theorem nerode_sep_r103 : nerode_sep_row 103 = true := rfl
theorem nerode_sep_r107 : nerode_sep_row 107 = true := rfl
theorem nerode_sep_r111 : nerode_sep_row 111 = true := rfl
theorem ob2_r1 : ob2_idx_row 1 = true := rfl
theorem ob2_r3 : ob2_idx_row 3 = true := rfl
theorem ob2_r5 : ob2_idx_row 5 = true := rfl
theorem ob2_r7 : ob2_idx_row 7 = true := rfl
theorem ob2_r9 : ob2_idx_row 9 = true := rfl
theorem ob2_r11 : ob2_idx_row 11 = true := rfl
theorem ob2_r13 : ob2_idx_row 13 = true := rfl
theorem ob2_r15 : ob2_idx_row 15 = true := rfl
theorem ob2_r17 : ob2_idx_row 17 = true := rfl
theorem ob2_r19 : ob2_idx_row 19 = true := rfl
theorem ob2_r21 : ob2_idx_row 21 = true := rfl
theorem ob2_r23 : ob2_idx_row 23 = true := rfl
theorem ob2_r25 : ob2_idx_row 25 = true := rfl
theorem ob2_r27 : ob2_idx_row 27 = true := rfl
theorem ob2_r29 : ob2_idx_row 29 = true := rfl
theorem ob2_r31 : ob2_idx_row 31 = true := rfl
theorem ob2_r33 : ob2_idx_row 33 = true := rfl
theorem ob2_r35 : ob2_idx_row 35 = true := rfl
theorem ob2_r37 : ob2_idx_row 37 = true := rfl
theorem ob2_r39 : ob2_idx_row 39 = true := rfl
theorem ob2_r41 : ob2_idx_row 41 = true := rfl
theorem ob2_r43 : ob2_idx_row 43 = true := rfl
theorem ob2_r45 : ob2_idx_row 45 = true := rfl
theorem ob2_r47 : ob2_idx_row 47 = true := rfl
theorem ob2_r49 : ob2_idx_row 49 = true := rfl
theorem ob2_r51 : ob2_idx_row 51 = true := rfl
theorem ob2_r53 : ob2_idx_row 53 = true := rfl
theorem ob2_r55 : ob2_idx_row 55 = true := rfl
theorem ob2_r57 : ob2_idx_row 57 = true := rfl
theorem ob2_r59 : ob2_idx_row 59 = true := rfl
theorem ob2_r61 : ob2_idx_row 61 = true := rfl
theorem ob2_r63 : ob2_idx_row 63 = true := rfl
theorem ob2_r65 : ob2_idx_row 65 = true := rfl
theorem ob2_r67 : ob2_idx_row 67 = true := rfl
theorem ob2_r69 : ob2_idx_row 69 = true := rfl
theorem ob2_r71 : ob2_idx_row 71 = true := rfl
theorem ob2_r73 : ob2_idx_row 73 = true := rfl
theorem ob2_r75 : ob2_idx_row 75 = true := rfl
theorem ob2_r77 : ob2_idx_row 77 = true := rfl
theorem ob2_r79 : ob2_idx_row 79 = true := rfl
theorem ob2_r81 : ob2_idx_row 81 = true := rfl
theorem ob2_r83 : ob2_idx_row 83 = true := rfl
theorem ob2_r85 : ob2_idx_row 85 = true := rfl
theorem ob2_r87 : ob2_idx_row 87 = true := rfl
theorem ob2_r89 : ob2_idx_row 89 = true := rfl
theorem ob2_r91 : ob2_idx_row 91 = true := rfl
theorem ob2_r93 : ob2_idx_row 93 = true := rfl

end SimplifiedQ10Q5
