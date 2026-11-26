import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem out2d_2d_idx_thm : out2d_2d_idx_ok = true := rfl
theorem rankP_ok_r6 : checkAll2_StateP (rankP_ok_fn .p6) = true := rfl
theorem rankP_ok_r14 : checkAll2_StateP (rankP_ok_fn .p14) = true := rfl
theorem rankP_ok_r22 : checkAll2_StateP (rankP_ok_fn .p22) = true := rfl
theorem rankP_ok_r30 : checkAll2_StateP (rankP_ok_fn .p30) = true := rfl
theorem rankP_ok_r38 : checkAll2_StateP (rankP_ok_fn .p38) = true := rfl
theorem ob4_r3 : ob4_idx_row 3 = true := rfl
theorem ob4_r7 : ob4_idx_row 7 = true := rfl
theorem ob4_r11 : ob4_idx_row 11 = true := rfl
theorem ob4_r15 : ob4_idx_row 15 = true := rfl
theorem ob4_r19 : ob4_idx_row 19 = true := rfl
theorem ob4_r23 : ob4_idx_row 23 = true := rfl
theorem ob4_r27 : ob4_idx_row 27 = true := rfl
theorem ob4_r31 : ob4_idx_row 31 = true := rfl
theorem ob4_r35 : ob4_idx_row 35 = true := rfl
theorem ob4_r39 : ob4_idx_row 39 = true := rfl
theorem ob4_r43 : ob4_idx_row 43 = true := rfl
theorem ob4_r47 : ob4_idx_row 47 = true := rfl
theorem ob4_r51 : ob4_idx_row 51 = true := rfl
theorem ob4_r55 : ob4_idx_row 55 = true := rfl
theorem ob4_r59 : ob4_idx_row 59 = true := rfl
theorem ob4_r63 : ob4_idx_row 63 = true := rfl
theorem ob4_r67 : ob4_idx_row 67 = true := rfl
theorem ob4_r71 : ob4_idx_row 71 = true := rfl
theorem ob4_r75 : ob4_idx_row 75 = true := rfl
theorem ob4_r79 : ob4_idx_row 79 = true := rfl
theorem ob4_r83 : ob4_idx_row 83 = true := rfl
theorem ob4_r87 : ob4_idx_row 87 = true := rfl
theorem ob4_r91 : ob4_idx_row 91 = true := rfl

end FormalQ5Final
