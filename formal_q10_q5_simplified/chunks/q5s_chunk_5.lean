import formal_q10_q5_simplified.q5_defs

namespace SimplifiedQ10Q5
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem phIdx_sound_chk : checkNat2 39 35 (fun p h => let i := phIdx (ofPIdx p, ofHnIdx h); Nat.beq i 127 || (Nat.ble (i + 1) 113 && beqPH (ofPhIdx i) (ofPIdx p, ofHnIdx h))) = true := rfl
theorem dp_s_law_r1 : dp_s_law_row 1 = true := rfl
theorem dp_s_law_r5 : dp_s_law_row 5 = true := rfl
theorem dp_s_law_r9 : dp_s_law_row 9 = true := rfl
theorem dp_s_law_r13 : dp_s_law_row 13 = true := rfl
theorem dp_s_law_r17 : dp_s_law_row 17 = true := rfl
theorem dp_s_law_r21 : dp_s_law_row 21 = true := rfl
theorem dp_s_law_r25 : dp_s_law_row 25 = true := rfl
theorem dp_s_law_r29 : dp_s_law_row 29 = true := rfl
theorem dp_s_law_r33 : dp_s_law_row 33 = true := rfl
theorem dp_s_law_r37 : dp_s_law_row 37 = true := rfl
theorem dph_bridge_r2 : dph_bridge_row 2 = true := rfl
theorem dph_bridge_r6 : dph_bridge_row 6 = true := rfl
theorem dph_bridge_r10 : dph_bridge_row 10 = true := rfl
theorem dph_bridge_r14 : dph_bridge_row 14 = true := rfl
theorem dph_bridge_r18 : dph_bridge_row 18 = true := rfl
theorem dph_bridge_r22 : dph_bridge_row 22 = true := rfl
theorem dph_bridge_r26 : dph_bridge_row 26 = true := rfl
theorem dph_bridge_r30 : dph_bridge_row 30 = true := rfl
theorem dph_bridge_r34 : dph_bridge_row 34 = true := rfl
theorem dph_bridge_r38 : dph_bridge_row 38 = true := rfl
theorem dph_bridge_r42 : dph_bridge_row 42 = true := rfl
theorem dph_bridge_r46 : dph_bridge_row 46 = true := rfl
theorem dph_bridge_r50 : dph_bridge_row 50 = true := rfl
theorem dph_bridge_r54 : dph_bridge_row 54 = true := rfl
theorem dph_bridge_r58 : dph_bridge_row 58 = true := rfl
theorem dph_bridge_r62 : dph_bridge_row 62 = true := rfl
theorem dph_bridge_r66 : dph_bridge_row 66 = true := rfl
theorem dph_bridge_r70 : dph_bridge_row 70 = true := rfl
theorem dph_bridge_r74 : dph_bridge_row 74 = true := rfl
theorem dph_bridge_r78 : dph_bridge_row 78 = true := rfl
theorem dph_bridge_r82 : dph_bridge_row 82 = true := rfl
theorem dph_bridge_r86 : dph_bridge_row 86 = true := rfl
theorem dph_bridge_r90 : dph_bridge_row 90 = true := rfl
theorem dph_bridge_r94 : dph_bridge_row 94 = true := rfl
theorem dph_bridge_r98 : dph_bridge_row 98 = true := rfl
theorem dph_bridge_r102 : dph_bridge_row 102 = true := rfl
theorem dph_bridge_r106 : dph_bridge_row 106 = true := rfl
theorem dph_bridge_r110 : dph_bridge_row 110 = true := rfl
theorem ob3_r0 : ob3_idx_row 0 = true := rfl
theorem ob3_r2 : ob3_idx_row 2 = true := rfl
theorem ob3_r4 : ob3_idx_row 4 = true := rfl
theorem ob3_r6 : ob3_idx_row 6 = true := rfl
theorem ob3_r8 : ob3_idx_row 8 = true := rfl
theorem ob3_r10 : ob3_idx_row 10 = true := rfl
theorem ob3_r12 : ob3_idx_row 12 = true := rfl
theorem ob3_r14 : ob3_idx_row 14 = true := rfl
theorem ob3_r16 : ob3_idx_row 16 = true := rfl
theorem ob3_r18 : ob3_idx_row 18 = true := rfl
theorem ob3_r20 : ob3_idx_row 20 = true := rfl
theorem ob3_r22 : ob3_idx_row 22 = true := rfl
theorem ob3_r24 : ob3_idx_row 24 = true := rfl
theorem ob3_r26 : ob3_idx_row 26 = true := rfl
theorem ob3_r28 : ob3_idx_row 28 = true := rfl
theorem ob3_r30 : ob3_idx_row 30 = true := rfl
theorem ob3_r32 : ob3_idx_row 32 = true := rfl
theorem ob3_r34 : ob3_idx_row 34 = true := rfl
theorem ob3_r36 : ob3_idx_row 36 = true := rfl
theorem ob3_r38 : ob3_idx_row 38 = true := rfl
theorem ob3_r40 : ob3_idx_row 40 = true := rfl
theorem ob3_r42 : ob3_idx_row 42 = true := rfl
theorem ob3_r44 : ob3_idx_row 44 = true := rfl
theorem ob3_r46 : ob3_idx_row 46 = true := rfl
theorem ob3_r48 : ob3_idx_row 48 = true := rfl
theorem ob3_r50 : ob3_idx_row 50 = true := rfl
theorem ob3_r52 : ob3_idx_row 52 = true := rfl
theorem ob3_r54 : ob3_idx_row 54 = true := rfl
theorem ob3_r56 : ob3_idx_row 56 = true := rfl
theorem ob3_r58 : ob3_idx_row 58 = true := rfl
theorem ob3_r60 : ob3_idx_row 60 = true := rfl
theorem ob3_r62 : ob3_idx_row 62 = true := rfl
theorem ob3_r64 : ob3_idx_row 64 = true := rfl
theorem ob3_r66 : ob3_idx_row 66 = true := rfl
theorem ob3_r68 : ob3_idx_row 68 = true := rfl
theorem ob3_r70 : ob3_idx_row 70 = true := rfl
theorem ob3_r72 : ob3_idx_row 72 = true := rfl
theorem ob3_r74 : ob3_idx_row 74 = true := rfl
theorem ob3_r76 : ob3_idx_row 76 = true := rfl
theorem ob3_r78 : ob3_idx_row 78 = true := rfl
theorem ob3_r80 : ob3_idx_row 80 = true := rfl
theorem ob3_r82 : ob3_idx_row 82 = true := rfl
theorem ob3_r84 : ob3_idx_row 84 = true := rfl
theorem ob3_r86 : ob3_idx_row 86 = true := rfl
theorem ob3_r88 : ob3_idx_row 88 = true := rfl
theorem ob3_r90 : ob3_idx_row 90 = true := rfl
theorem ob3_r92 : ob3_idx_row 92 = true := rfl
theorem ob3_r94 : ob3_idx_row 94 = true := rfl

end SimplifiedQ10Q5
