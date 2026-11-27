import formal_q10_q5_simplified.q5_defs

namespace SimplifiedQ10Q5
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem zachos_hn_chk : checkNat1 35 (fun hz => (Nat.beq (dhnIdx 23 hz) 34 || Nat.beq (dhnIdx 23 hz) 23) && (Nat.beq (dhnIdx 24 hz) 34 || Nat.beq (dhnIdx 24 hz) 23) && Nat.beq (dhnIdx (dhnIdx 16 hz) 23) 34 && Nat.beq (dhnIdx (dhnIdx 16 hz) 34) 34) = true := rfl
theorem dp_s_law_r0 : dp_s_law_row 0 = true := rfl
theorem dp_s_law_r4 : dp_s_law_row 4 = true := rfl
theorem dp_s_law_r8 : dp_s_law_row 8 = true := rfl
theorem dp_s_law_r12 : dp_s_law_row 12 = true := rfl
theorem dp_s_law_r16 : dp_s_law_row 16 = true := rfl
theorem dp_s_law_r20 : dp_s_law_row 20 = true := rfl
theorem dp_s_law_r24 : dp_s_law_row 24 = true := rfl
theorem dp_s_law_r28 : dp_s_law_row 28 = true := rfl
theorem dp_s_law_r32 : dp_s_law_row 32 = true := rfl
theorem dp_s_law_r36 : dp_s_law_row 36 = true := rfl
theorem dph_bridge_r1 : dph_bridge_row 1 = true := rfl
theorem dph_bridge_r5 : dph_bridge_row 5 = true := rfl
theorem dph_bridge_r9 : dph_bridge_row 9 = true := rfl
theorem dph_bridge_r13 : dph_bridge_row 13 = true := rfl
theorem dph_bridge_r17 : dph_bridge_row 17 = true := rfl
theorem dph_bridge_r21 : dph_bridge_row 21 = true := rfl
theorem dph_bridge_r25 : dph_bridge_row 25 = true := rfl
theorem dph_bridge_r29 : dph_bridge_row 29 = true := rfl
theorem dph_bridge_r33 : dph_bridge_row 33 = true := rfl
theorem dph_bridge_r37 : dph_bridge_row 37 = true := rfl
theorem dph_bridge_r41 : dph_bridge_row 41 = true := rfl
theorem dph_bridge_r45 : dph_bridge_row 45 = true := rfl
theorem dph_bridge_r49 : dph_bridge_row 49 = true := rfl
theorem dph_bridge_r53 : dph_bridge_row 53 = true := rfl
theorem dph_bridge_r57 : dph_bridge_row 57 = true := rfl
theorem dph_bridge_r61 : dph_bridge_row 61 = true := rfl
theorem dph_bridge_r65 : dph_bridge_row 65 = true := rfl
theorem dph_bridge_r69 : dph_bridge_row 69 = true := rfl
theorem dph_bridge_r73 : dph_bridge_row 73 = true := rfl
theorem dph_bridge_r77 : dph_bridge_row 77 = true := rfl
theorem dph_bridge_r81 : dph_bridge_row 81 = true := rfl
theorem dph_bridge_r85 : dph_bridge_row 85 = true := rfl
theorem dph_bridge_r89 : dph_bridge_row 89 = true := rfl
theorem dph_bridge_r93 : dph_bridge_row 93 = true := rfl
theorem dph_bridge_r97 : dph_bridge_row 97 = true := rfl
theorem dph_bridge_r101 : dph_bridge_row 101 = true := rfl
theorem dph_bridge_r105 : dph_bridge_row 105 = true := rfl
theorem dph_bridge_r109 : dph_bridge_row 109 = true := rfl
theorem out2d_trans_r0 : out2d_trans_idx_row 0 = true := rfl
theorem out2d_trans_r2 : out2d_trans_idx_row 2 = true := rfl
theorem out2d_trans_r4 : out2d_trans_idx_row 4 = true := rfl
theorem out2d_trans_r6 : out2d_trans_idx_row 6 = true := rfl
theorem out2d_trans_r8 : out2d_trans_idx_row 8 = true := rfl
theorem out2d_trans_r10 : out2d_trans_idx_row 10 = true := rfl
theorem out2d_trans_r12 : out2d_trans_idx_row 12 = true := rfl
theorem out2d_trans_r14 : out2d_trans_idx_row 14 = true := rfl
theorem out2d_trans_r16 : out2d_trans_idx_row 16 = true := rfl
theorem out2d_trans_r18 : out2d_trans_idx_row 18 = true := rfl
theorem out2d_trans_r20 : out2d_trans_idx_row 20 = true := rfl
theorem out2d_trans_r22 : out2d_trans_idx_row 22 = true := rfl
theorem out2d_trans_r24 : out2d_trans_idx_row 24 = true := rfl
theorem out2d_trans_r26 : out2d_trans_idx_row 26 = true := rfl
theorem out2d_trans_r28 : out2d_trans_idx_row 28 = true := rfl
theorem out2d_trans_r30 : out2d_trans_idx_row 30 = true := rfl
theorem out2d_trans_r32 : out2d_trans_idx_row 32 = true := rfl
theorem out2d_trans_r34 : out2d_trans_idx_row 34 = true := rfl
theorem out2d_trans_r36 : out2d_trans_idx_row 36 = true := rfl
theorem out2d_trans_r38 : out2d_trans_idx_row 38 = true := rfl
theorem out2d_trans_r40 : out2d_trans_idx_row 40 = true := rfl
theorem out2d_trans_r42 : out2d_trans_idx_row 42 = true := rfl
theorem out2d_trans_r44 : out2d_trans_idx_row 44 = true := rfl
theorem out2d_trans_r46 : out2d_trans_idx_row 46 = true := rfl
theorem out2d_trans_r48 : out2d_trans_idx_row 48 = true := rfl
theorem out2d_trans_r50 : out2d_trans_idx_row 50 = true := rfl
theorem out2d_trans_r52 : out2d_trans_idx_row 52 = true := rfl
theorem out2d_trans_r54 : out2d_trans_idx_row 54 = true := rfl
theorem out2d_trans_r56 : out2d_trans_idx_row 56 = true := rfl
theorem out2d_trans_r58 : out2d_trans_idx_row 58 = true := rfl
theorem out2d_trans_r60 : out2d_trans_idx_row 60 = true := rfl
theorem out2d_trans_r62 : out2d_trans_idx_row 62 = true := rfl
theorem out2d_trans_r64 : out2d_trans_idx_row 64 = true := rfl
theorem out2d_trans_r66 : out2d_trans_idx_row 66 = true := rfl
theorem out2d_trans_r68 : out2d_trans_idx_row 68 = true := rfl
theorem out2d_trans_r70 : out2d_trans_idx_row 70 = true := rfl
theorem out2d_trans_r72 : out2d_trans_idx_row 72 = true := rfl
theorem out2d_trans_r74 : out2d_trans_idx_row 74 = true := rfl
theorem out2d_trans_r76 : out2d_trans_idx_row 76 = true := rfl
theorem out2d_trans_r78 : out2d_trans_idx_row 78 = true := rfl
theorem out2d_trans_r80 : out2d_trans_idx_row 80 = true := rfl
theorem out2d_trans_r82 : out2d_trans_idx_row 82 = true := rfl
theorem out2d_trans_r84 : out2d_trans_idx_row 84 = true := rfl
theorem out2d_trans_r86 : out2d_trans_idx_row 86 = true := rfl
theorem out2d_trans_r88 : out2d_trans_idx_row 88 = true := rfl
theorem out2d_trans_r90 : out2d_trans_idx_row 90 = true := rfl
theorem out2d_trans_r92 : out2d_trans_idx_row 92 = true := rfl
theorem out2d_trans_r94 : out2d_trans_idx_row 94 = true := rfl

end SimplifiedQ10Q5
