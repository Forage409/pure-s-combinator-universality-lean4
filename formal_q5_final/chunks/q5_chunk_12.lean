import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem rankP_ok_r4 : checkAll2_StateP (rankP_ok_fn .p4) = true := rfl
theorem rankP_ok_r12 : checkAll2_StateP (rankP_ok_fn .p12) = true := rfl
theorem rankP_ok_r20 : checkAll2_StateP (rankP_ok_fn .p20) = true := rfl
theorem rankP_ok_r28 : checkAll2_StateP (rankP_ok_fn .p28) = true := rfl
theorem rankP_ok_r36 : checkAll2_StateP (rankP_ok_fn .p36) = true := rfl
theorem ob4_r2 : ob4_idx_row 2 = true := rfl
theorem ob4_r6 : ob4_idx_row 6 = true := rfl
theorem ob4_r10 : ob4_idx_row 10 = true := rfl
theorem ob4_r14 : ob4_idx_row 14 = true := rfl
theorem ob4_r18 : ob4_idx_row 18 = true := rfl
theorem ob4_r22 : ob4_idx_row 22 = true := rfl
theorem ob4_r26 : ob4_idx_row 26 = true := rfl
theorem ob4_r30 : ob4_idx_row 30 = true := rfl
theorem ob4_r34 : ob4_idx_row 34 = true := rfl
theorem ob4_r38 : ob4_idx_row 38 = true := rfl
theorem ob4_r42 : ob4_idx_row 42 = true := rfl
theorem ob4_r46 : ob4_idx_row 46 = true := rfl
theorem ob4_r50 : ob4_idx_row 50 = true := rfl
theorem ob4_r54 : ob4_idx_row 54 = true := rfl
theorem ob4_r58 : ob4_idx_row 58 = true := rfl
theorem ob4_r62 : ob4_idx_row 62 = true := rfl
theorem ob4_r66 : ob4_idx_row 66 = true := rfl
theorem ob4_r70 : ob4_idx_row 70 = true := rfl
theorem ob4_r74 : ob4_idx_row 74 = true := rfl
theorem ob4_r78 : ob4_idx_row 78 = true := rfl
theorem ob4_r82 : ob4_idx_row 82 = true := rfl
theorem ob4_r86 : ob4_idx_row 86 = true := rfl
theorem ob4_r90 : ob4_idx_row 90 = true := rfl
theorem ob4_r94 : ob4_idx_row 94 = true := rfl

end FormalQ5Final
