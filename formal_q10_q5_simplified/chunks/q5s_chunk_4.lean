import formal_q10_q5_simplified.q5_defs

namespace SimplifiedQ10Q5
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem reach_1d_chk : checkNat1 113 (fun i => let q := ofPhIdx i; Nat.beq (phIdx q) i && boolBeq (!beqP q.1 .p37) (isAccIdx i) && boolBeq (isHN34PH q) (isHN34Idx i) && boolBeq (isZachosPH q) (isZachosIdx i) && (!isAccIdx i || (isAccIdx (dphIdx 0 i) && Nat.beq (kindIdx (dphIdx 0 i)) 1))) = true := rfl
theorem rankP_idx_r0 : rankP_idx_row 0 = true := rfl
theorem rankP_idx_r4 : rankP_idx_row 4 = true := rfl
theorem rankP_idx_r8 : rankP_idx_row 8 = true := rfl
theorem rankP_idx_r12 : rankP_idx_row 12 = true := rfl
theorem rankP_idx_r16 : rankP_idx_row 16 = true := rfl
theorem rankP_idx_r20 : rankP_idx_row 20 = true := rfl
theorem rankP_idx_r24 : rankP_idx_row 24 = true := rfl
theorem rankP_idx_r28 : rankP_idx_row 28 = true := rfl
theorem rankP_idx_r32 : rankP_idx_row 32 = true := rfl
theorem rankP_idx_r36 : rankP_idx_row 36 = true := rfl
theorem nerode_sep_r1 : nerode_sep_row 1 = true := rfl
theorem nerode_sep_r5 : nerode_sep_row 5 = true := rfl
theorem nerode_sep_r9 : nerode_sep_row 9 = true := rfl
theorem nerode_sep_r13 : nerode_sep_row 13 = true := rfl
theorem nerode_sep_r17 : nerode_sep_row 17 = true := rfl
theorem nerode_sep_r21 : nerode_sep_row 21 = true := rfl
theorem nerode_sep_r25 : nerode_sep_row 25 = true := rfl
theorem nerode_sep_r29 : nerode_sep_row 29 = true := rfl
theorem nerode_sep_r33 : nerode_sep_row 33 = true := rfl
theorem nerode_sep_r37 : nerode_sep_row 37 = true := rfl
theorem nerode_sep_r41 : nerode_sep_row 41 = true := rfl
theorem nerode_sep_r45 : nerode_sep_row 45 = true := rfl
theorem nerode_sep_r49 : nerode_sep_row 49 = true := rfl
theorem nerode_sep_r53 : nerode_sep_row 53 = true := rfl
theorem nerode_sep_r57 : nerode_sep_row 57 = true := rfl
theorem nerode_sep_r61 : nerode_sep_row 61 = true := rfl
theorem nerode_sep_r65 : nerode_sep_row 65 = true := rfl
theorem nerode_sep_r69 : nerode_sep_row 69 = true := rfl
theorem nerode_sep_r73 : nerode_sep_row 73 = true := rfl
theorem nerode_sep_r77 : nerode_sep_row 77 = true := rfl
theorem nerode_sep_r81 : nerode_sep_row 81 = true := rfl
theorem nerode_sep_r85 : nerode_sep_row 85 = true := rfl
theorem nerode_sep_r89 : nerode_sep_row 89 = true := rfl
theorem nerode_sep_r93 : nerode_sep_row 93 = true := rfl
theorem nerode_sep_r97 : nerode_sep_row 97 = true := rfl
theorem nerode_sep_r101 : nerode_sep_row 101 = true := rfl
theorem nerode_sep_r105 : nerode_sep_row 105 = true := rfl
theorem nerode_sep_r109 : nerode_sep_row 109 = true := rfl
theorem ob2_r0 : ob2_idx_row 0 = true := rfl
theorem ob2_r2 : ob2_idx_row 2 = true := rfl
theorem ob2_r4 : ob2_idx_row 4 = true := rfl
theorem ob2_r6 : ob2_idx_row 6 = true := rfl
theorem ob2_r8 : ob2_idx_row 8 = true := rfl
theorem ob2_r10 : ob2_idx_row 10 = true := rfl
theorem ob2_r12 : ob2_idx_row 12 = true := rfl
theorem ob2_r14 : ob2_idx_row 14 = true := rfl
theorem ob2_r16 : ob2_idx_row 16 = true := rfl
theorem ob2_r18 : ob2_idx_row 18 = true := rfl
theorem ob2_r20 : ob2_idx_row 20 = true := rfl
theorem ob2_r22 : ob2_idx_row 22 = true := rfl
theorem ob2_r24 : ob2_idx_row 24 = true := rfl
theorem ob2_r26 : ob2_idx_row 26 = true := rfl
theorem ob2_r28 : ob2_idx_row 28 = true := rfl
theorem ob2_r30 : ob2_idx_row 30 = true := rfl
theorem ob2_r32 : ob2_idx_row 32 = true := rfl
theorem ob2_r34 : ob2_idx_row 34 = true := rfl
theorem ob2_r36 : ob2_idx_row 36 = true := rfl
theorem ob2_r38 : ob2_idx_row 38 = true := rfl
theorem ob2_r40 : ob2_idx_row 40 = true := rfl
theorem ob2_r42 : ob2_idx_row 42 = true := rfl
theorem ob2_r44 : ob2_idx_row 44 = true := rfl
theorem ob2_r46 : ob2_idx_row 46 = true := rfl
theorem ob2_r48 : ob2_idx_row 48 = true := rfl
theorem ob2_r50 : ob2_idx_row 50 = true := rfl
theorem ob2_r52 : ob2_idx_row 52 = true := rfl
theorem ob2_r54 : ob2_idx_row 54 = true := rfl
theorem ob2_r56 : ob2_idx_row 56 = true := rfl
theorem ob2_r58 : ob2_idx_row 58 = true := rfl
theorem ob2_r60 : ob2_idx_row 60 = true := rfl
theorem ob2_r62 : ob2_idx_row 62 = true := rfl
theorem ob2_r64 : ob2_idx_row 64 = true := rfl
theorem ob2_r66 : ob2_idx_row 66 = true := rfl
theorem ob2_r68 : ob2_idx_row 68 = true := rfl
theorem ob2_r70 : ob2_idx_row 70 = true := rfl
theorem ob2_r72 : ob2_idx_row 72 = true := rfl
theorem ob2_r74 : ob2_idx_row 74 = true := rfl
theorem ob2_r76 : ob2_idx_row 76 = true := rfl
theorem ob2_r78 : ob2_idx_row 78 = true := rfl
theorem ob2_r80 : ob2_idx_row 80 = true := rfl
theorem ob2_r82 : ob2_idx_row 82 = true := rfl
theorem ob2_r84 : ob2_idx_row 84 = true := rfl
theorem ob2_r86 : ob2_idx_row 86 = true := rfl
theorem ob2_r88 : ob2_idx_row 88 = true := rfl
theorem ob2_r90 : ob2_idx_row 90 = true := rfl
theorem ob2_r92 : ob2_idx_row 92 = true := rfl
theorem ob2_r94 : ob2_idx_row 94 = true := rfl

end SimplifiedQ10Q5
