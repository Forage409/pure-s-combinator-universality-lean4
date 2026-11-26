import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem rankP_ok_r2 : checkAll2_StateP (rankP_ok_fn .p2) = true := rfl
theorem rankP_ok_r10 : checkAll2_StateP (rankP_ok_fn .p10) = true := rfl
theorem rankP_ok_r18 : checkAll2_StateP (rankP_ok_fn .p18) = true := rfl
theorem rankP_ok_r26 : checkAll2_StateP (rankP_ok_fn .p26) = true := rfl
theorem rankP_ok_r34 : checkAll2_StateP (rankP_ok_fn .p34) = true := rfl
theorem ob4_r1 : ob4_idx_row 1 = true := rfl
theorem ob4_r5 : ob4_idx_row 5 = true := rfl
theorem ob4_r9 : ob4_idx_row 9 = true := rfl
theorem ob4_r13 : ob4_idx_row 13 = true := rfl
theorem ob4_r17 : ob4_idx_row 17 = true := rfl
theorem ob4_r21 : ob4_idx_row 21 = true := rfl
theorem ob4_r25 : ob4_idx_row 25 = true := rfl
theorem ob4_r29 : ob4_idx_row 29 = true := rfl
theorem ob4_r33 : ob4_idx_row 33 = true := rfl
theorem ob4_r37 : ob4_idx_row 37 = true := rfl
theorem ob4_r41 : ob4_idx_row 41 = true := rfl
theorem ob4_r45 : ob4_idx_row 45 = true := rfl
theorem ob4_r49 : ob4_idx_row 49 = true := rfl
theorem ob4_r53 : ob4_idx_row 53 = true := rfl
theorem ob4_r57 : ob4_idx_row 57 = true := rfl
theorem ob4_r61 : ob4_idx_row 61 = true := rfl
theorem ob4_r65 : ob4_idx_row 65 = true := rfl
theorem ob4_r69 : ob4_idx_row 69 = true := rfl
theorem ob4_r73 : ob4_idx_row 73 = true := rfl
theorem ob4_r77 : ob4_idx_row 77 = true := rfl
theorem ob4_r81 : ob4_idx_row 81 = true := rfl
theorem ob4_r85 : ob4_idx_row 85 = true := rfl
theorem ob4_r89 : ob4_idx_row 89 = true := rfl
theorem ob4_r93 : ob4_idx_row 93 = true := rfl

end FormalQ5Final
