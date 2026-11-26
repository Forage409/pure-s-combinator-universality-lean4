import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem rankP_ok_r0 : checkAll2_StateP (rankP_ok_fn .p0) = true := rfl
theorem rankP_ok_r8 : checkAll2_StateP (rankP_ok_fn .p8) = true := rfl
theorem rankP_ok_r16 : checkAll2_StateP (rankP_ok_fn .p16) = true := rfl
theorem rankP_ok_r24 : checkAll2_StateP (rankP_ok_fn .p24) = true := rfl
theorem rankP_ok_r32 : checkAll2_StateP (rankP_ok_fn .p32) = true := rfl
theorem ob4_r0 : ob4_idx_row 0 = true := rfl
theorem ob4_r4 : ob4_idx_row 4 = true := rfl
theorem ob4_r8 : ob4_idx_row 8 = true := rfl
theorem ob4_r12 : ob4_idx_row 12 = true := rfl
theorem ob4_r16 : ob4_idx_row 16 = true := rfl
theorem ob4_r20 : ob4_idx_row 20 = true := rfl
theorem ob4_r24 : ob4_idx_row 24 = true := rfl
theorem ob4_r28 : ob4_idx_row 28 = true := rfl
theorem ob4_r32 : ob4_idx_row 32 = true := rfl
theorem ob4_r36 : ob4_idx_row 36 = true := rfl
theorem ob4_r40 : ob4_idx_row 40 = true := rfl
theorem ob4_r44 : ob4_idx_row 44 = true := rfl
theorem ob4_r48 : ob4_idx_row 48 = true := rfl
theorem ob4_r52 : ob4_idx_row 52 = true := rfl
theorem ob4_r56 : ob4_idx_row 56 = true := rfl
theorem ob4_r60 : ob4_idx_row 60 = true := rfl
theorem ob4_r64 : ob4_idx_row 64 = true := rfl
theorem ob4_r68 : ob4_idx_row 68 = true := rfl
theorem ob4_r72 : ob4_idx_row 72 = true := rfl
theorem ob4_r76 : ob4_idx_row 76 = true := rfl
theorem ob4_r80 : ob4_idx_row 80 = true := rfl
theorem ob4_r84 : ob4_idx_row 84 = true := rfl
theorem ob4_r88 : ob4_idx_row 88 = true := rfl
theorem ob4_r92 : ob4_idx_row 92 = true := rfl

end FormalQ5Final
