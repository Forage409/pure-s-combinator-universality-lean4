import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem rankP_ok_r5 : checkAll2_StateP (rankP_ok_fn .p5) = true := rfl
theorem rankP_ok_r13 : checkAll2_StateP (rankP_ok_fn .p13) = true := rfl
theorem rankP_ok_r21 : checkAll2_StateP (rankP_ok_fn .p21) = true := rfl
theorem rankP_ok_r29 : checkAll2_StateP (rankP_ok_fn .p29) = true := rfl
theorem rankP_ok_r37 : checkAll2_StateP (rankP_ok_fn .p37) = true := rfl
theorem ob2_r3 : ob2_idx_row 3 = true := rfl
theorem ob2_r7 : ob2_idx_row 7 = true := rfl
theorem ob2_r11 : ob2_idx_row 11 = true := rfl
theorem ob2_r15 : ob2_idx_row 15 = true := rfl
theorem ob2_r19 : ob2_idx_row 19 = true := rfl
theorem ob2_r23 : ob2_idx_row 23 = true := rfl
theorem ob2_r27 : ob2_idx_row 27 = true := rfl
theorem ob2_r31 : ob2_idx_row 31 = true := rfl
theorem ob2_r35 : ob2_idx_row 35 = true := rfl
theorem ob2_r39 : ob2_idx_row 39 = true := rfl
theorem ob2_r43 : ob2_idx_row 43 = true := rfl
theorem ob2_r47 : ob2_idx_row 47 = true := rfl
theorem ob2_r51 : ob2_idx_row 51 = true := rfl
theorem ob2_r55 : ob2_idx_row 55 = true := rfl
theorem ob2_r59 : ob2_idx_row 59 = true := rfl
theorem ob2_r63 : ob2_idx_row 63 = true := rfl
theorem ob2_r67 : ob2_idx_row 67 = true := rfl
theorem ob2_r71 : ob2_idx_row 71 = true := rfl
theorem ob2_r75 : ob2_idx_row 75 = true := rfl
theorem ob2_r79 : ob2_idx_row 79 = true := rfl
theorem ob2_r83 : ob2_idx_row 83 = true := rfl
theorem ob2_r87 : ob2_idx_row 87 = true := rfl
theorem ob2_r91 : ob2_idx_row 91 = true := rfl

end FormalQ5Final
