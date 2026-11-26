import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem rankP_ok_r1 : checkAll2_StateP (rankP_ok_fn .p1) = true := rfl
theorem rankP_ok_r9 : checkAll2_StateP (rankP_ok_fn .p9) = true := rfl
theorem rankP_ok_r17 : checkAll2_StateP (rankP_ok_fn .p17) = true := rfl
theorem rankP_ok_r25 : checkAll2_StateP (rankP_ok_fn .p25) = true := rfl
theorem rankP_ok_r33 : checkAll2_StateP (rankP_ok_fn .p33) = true := rfl
theorem ob2_r1 : ob2_idx_row 1 = true := rfl
theorem ob2_r5 : ob2_idx_row 5 = true := rfl
theorem ob2_r9 : ob2_idx_row 9 = true := rfl
theorem ob2_r13 : ob2_idx_row 13 = true := rfl
theorem ob2_r17 : ob2_idx_row 17 = true := rfl
theorem ob2_r21 : ob2_idx_row 21 = true := rfl
theorem ob2_r25 : ob2_idx_row 25 = true := rfl
theorem ob2_r29 : ob2_idx_row 29 = true := rfl
theorem ob2_r33 : ob2_idx_row 33 = true := rfl
theorem ob2_r37 : ob2_idx_row 37 = true := rfl
theorem ob2_r41 : ob2_idx_row 41 = true := rfl
theorem ob2_r45 : ob2_idx_row 45 = true := rfl
theorem ob2_r49 : ob2_idx_row 49 = true := rfl
theorem ob2_r53 : ob2_idx_row 53 = true := rfl
theorem ob2_r57 : ob2_idx_row 57 = true := rfl
theorem ob2_r61 : ob2_idx_row 61 = true := rfl
theorem ob2_r65 : ob2_idx_row 65 = true := rfl
theorem ob2_r69 : ob2_idx_row 69 = true := rfl
theorem ob2_r73 : ob2_idx_row 73 = true := rfl
theorem ob2_r77 : ob2_idx_row 77 = true := rfl
theorem ob2_r81 : ob2_idx_row 81 = true := rfl
theorem ob2_r85 : ob2_idx_row 85 = true := rfl
theorem ob2_r89 : ob2_idx_row 89 = true := rfl
theorem ob2_r93 : ob2_idx_row 93 = true := rfl

end FormalQ5Final
