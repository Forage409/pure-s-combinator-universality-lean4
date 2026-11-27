import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem rankP_ok_r3 : checkAll2_StateP (rankP_ok_fn .p3) = true := rfl
theorem rankP_ok_r11 : checkAll2_StateP (rankP_ok_fn .p11) = true := rfl
theorem rankP_ok_r19 : checkAll2_StateP (rankP_ok_fn .p19) = true := rfl
theorem rankP_ok_r27 : checkAll2_StateP (rankP_ok_fn .p27) = true := rfl
theorem rankP_ok_r35 : checkAll2_StateP (rankP_ok_fn .p35) = true := rfl
theorem ob2_r2 : ob2_idx_row 2 = true := rfl
theorem ob2_r6 : ob2_idx_row 6 = true := rfl
theorem ob2_r10 : ob2_idx_row 10 = true := rfl
theorem ob2_r14 : ob2_idx_row 14 = true := rfl
theorem ob2_r18 : ob2_idx_row 18 = true := rfl
theorem ob2_r22 : ob2_idx_row 22 = true := rfl
theorem ob2_r26 : ob2_idx_row 26 = true := rfl
theorem ob2_r30 : ob2_idx_row 30 = true := rfl
theorem ob2_r34 : ob2_idx_row 34 = true := rfl
theorem ob2_r38 : ob2_idx_row 38 = true := rfl
theorem ob2_r42 : ob2_idx_row 42 = true := rfl
theorem ob2_r46 : ob2_idx_row 46 = true := rfl
theorem ob2_r50 : ob2_idx_row 50 = true := rfl
theorem ob2_r54 : ob2_idx_row 54 = true := rfl
theorem ob2_r58 : ob2_idx_row 58 = true := rfl
theorem ob2_r62 : ob2_idx_row 62 = true := rfl
theorem ob2_r66 : ob2_idx_row 66 = true := rfl
theorem ob2_r70 : ob2_idx_row 70 = true := rfl
theorem ob2_r74 : ob2_idx_row 74 = true := rfl
theorem ob2_r78 : ob2_idx_row 78 = true := rfl
theorem ob2_r82 : ob2_idx_row 82 = true := rfl
theorem ob2_r86 : ob2_idx_row 86 = true := rfl
theorem ob2_r90 : ob2_idx_row 90 = true := rfl
theorem ob2_r94 : ob2_idx_row 94 = true := rfl

end FormalQ5Final
