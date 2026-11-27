import formal_q10_q5_simplified.q5_defs

namespace SimplifiedQ10Q5
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem dp_meta_chk : checkNat2 39 39 (fun x y => Nat.beq (dpIdx 37 y) 37 && Nat.beq (dpIdx x 37) 37 && boolBeq (!Nat.beq (dpIdx 0 x) 37) (!Nat.beq x 37) && boolBeq (!Nat.beq (dpIdx (dpIdx 0 x) y) 37) (!Nat.beq x 37 && !Nat.beq y 37) && !Nat.beq (dpIdx x y) 0 && Nat.beq (dpIdx 29 y) 37 && (!Nat.beq (dpIdx 0 x) 1 || Nat.beq x 0) && !Nat.beq (dpIdx (dpIdx 0 x) y) 1 && !isZachosPIdx (dpIdx 0 x) && (!Nat.beq (dpIdx (dpIdx 0 x) y) 14 || (Nat.beq x 1 && Nat.beq y 1)) && (!Nat.beq (dpIdx (dpIdx 0 x) y) 32 || (Nat.beq x 0 && isZachosPIdx y)) && (Nat.beq x 37 || Nat.beq y 37 || Nat.beq (dpIdx (dpIdx 0 x) y) 37 || isS2PTree.lookup (dpIdx (dpIdx 0 x) y))) = true := rfl
theorem sepCtxOps_lt_chk : checkNat1 17 (fun k => allNat (fun x => Nat.ble (x + 1) 113) ((sepCtxOps k).map Prod.snd)) = true := rfl
theorem rankP_idx_r3 : rankP_idx_row 3 = true := rfl
theorem rankP_idx_r7 : rankP_idx_row 7 = true := rfl
theorem rankP_idx_r11 : rankP_idx_row 11 = true := rfl
theorem rankP_idx_r15 : rankP_idx_row 15 = true := rfl
theorem rankP_idx_r19 : rankP_idx_row 19 = true := rfl
theorem rankP_idx_r23 : rankP_idx_row 23 = true := rfl
theorem rankP_idx_r27 : rankP_idx_row 27 = true := rfl
theorem rankP_idx_r31 : rankP_idx_row 31 = true := rfl
theorem rankP_idx_r35 : rankP_idx_row 35 = true := rfl
theorem nerode_sep_r0 : nerode_sep_row 0 = true := rfl
theorem nerode_sep_r4 : nerode_sep_row 4 = true := rfl
theorem nerode_sep_r8 : nerode_sep_row 8 = true := rfl
theorem nerode_sep_r12 : nerode_sep_row 12 = true := rfl
theorem nerode_sep_r16 : nerode_sep_row 16 = true := rfl
theorem nerode_sep_r20 : nerode_sep_row 20 = true := rfl
theorem nerode_sep_r24 : nerode_sep_row 24 = true := rfl
theorem nerode_sep_r28 : nerode_sep_row 28 = true := rfl
theorem nerode_sep_r32 : nerode_sep_row 32 = true := rfl
theorem nerode_sep_r36 : nerode_sep_row 36 = true := rfl
theorem nerode_sep_r40 : nerode_sep_row 40 = true := rfl
theorem nerode_sep_r44 : nerode_sep_row 44 = true := rfl
theorem nerode_sep_r48 : nerode_sep_row 48 = true := rfl
theorem nerode_sep_r52 : nerode_sep_row 52 = true := rfl
theorem nerode_sep_r56 : nerode_sep_row 56 = true := rfl
theorem nerode_sep_r60 : nerode_sep_row 60 = true := rfl
theorem nerode_sep_r64 : nerode_sep_row 64 = true := rfl
theorem nerode_sep_r68 : nerode_sep_row 68 = true := rfl
theorem nerode_sep_r72 : nerode_sep_row 72 = true := rfl
theorem nerode_sep_r76 : nerode_sep_row 76 = true := rfl
theorem nerode_sep_r80 : nerode_sep_row 80 = true := rfl
theorem nerode_sep_r84 : nerode_sep_row 84 = true := rfl
theorem nerode_sep_r88 : nerode_sep_row 88 = true := rfl
theorem nerode_sep_r92 : nerode_sep_row 92 = true := rfl
theorem nerode_sep_r96 : nerode_sep_row 96 = true := rfl
theorem nerode_sep_r100 : nerode_sep_row 100 = true := rfl
theorem nerode_sep_r104 : nerode_sep_row 104 = true := rfl
theorem nerode_sep_r108 : nerode_sep_row 108 = true := rfl
theorem nerode_sep_r112 : nerode_sep_row 112 = true := rfl
theorem ob4_r1 : ob4_idx_row 1 = true := rfl
theorem ob4_r3 : ob4_idx_row 3 = true := rfl
theorem ob4_r5 : ob4_idx_row 5 = true := rfl
theorem ob4_r7 : ob4_idx_row 7 = true := rfl
theorem ob4_r9 : ob4_idx_row 9 = true := rfl
theorem ob4_r11 : ob4_idx_row 11 = true := rfl
theorem ob4_r13 : ob4_idx_row 13 = true := rfl
theorem ob4_r15 : ob4_idx_row 15 = true := rfl
theorem ob4_r17 : ob4_idx_row 17 = true := rfl
theorem ob4_r19 : ob4_idx_row 19 = true := rfl
theorem ob4_r21 : ob4_idx_row 21 = true := rfl
theorem ob4_r23 : ob4_idx_row 23 = true := rfl
theorem ob4_r25 : ob4_idx_row 25 = true := rfl
theorem ob4_r27 : ob4_idx_row 27 = true := rfl
theorem ob4_r29 : ob4_idx_row 29 = true := rfl
theorem ob4_r31 : ob4_idx_row 31 = true := rfl
theorem ob4_r33 : ob4_idx_row 33 = true := rfl
theorem ob4_r35 : ob4_idx_row 35 = true := rfl
theorem ob4_r37 : ob4_idx_row 37 = true := rfl
theorem ob4_r39 : ob4_idx_row 39 = true := rfl
theorem ob4_r41 : ob4_idx_row 41 = true := rfl
theorem ob4_r43 : ob4_idx_row 43 = true := rfl
theorem ob4_r45 : ob4_idx_row 45 = true := rfl
theorem ob4_r47 : ob4_idx_row 47 = true := rfl
theorem ob4_r49 : ob4_idx_row 49 = true := rfl
theorem ob4_r51 : ob4_idx_row 51 = true := rfl
theorem ob4_r53 : ob4_idx_row 53 = true := rfl
theorem ob4_r55 : ob4_idx_row 55 = true := rfl
theorem ob4_r57 : ob4_idx_row 57 = true := rfl
theorem ob4_r59 : ob4_idx_row 59 = true := rfl
theorem ob4_r61 : ob4_idx_row 61 = true := rfl
theorem ob4_r63 : ob4_idx_row 63 = true := rfl
theorem ob4_r65 : ob4_idx_row 65 = true := rfl
theorem ob4_r67 : ob4_idx_row 67 = true := rfl
theorem ob4_r69 : ob4_idx_row 69 = true := rfl
theorem ob4_r71 : ob4_idx_row 71 = true := rfl
theorem ob4_r73 : ob4_idx_row 73 = true := rfl
theorem ob4_r75 : ob4_idx_row 75 = true := rfl
theorem ob4_r77 : ob4_idx_row 77 = true := rfl
theorem ob4_r79 : ob4_idx_row 79 = true := rfl
theorem ob4_r81 : ob4_idx_row 81 = true := rfl
theorem ob4_r83 : ob4_idx_row 83 = true := rfl
theorem ob4_r85 : ob4_idx_row 85 = true := rfl
theorem ob4_r87 : ob4_idx_row 87 = true := rfl
theorem ob4_r89 : ob4_idx_row 89 = true := rfl
theorem ob4_r91 : ob4_idx_row 91 = true := rfl
theorem ob4_r93 : ob4_idx_row 93 = true := rfl

end SimplifiedQ10Q5
