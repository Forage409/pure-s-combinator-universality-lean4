import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem c3_ph0_idx_thm : checkNat (fun z => checkNat (fun n2 => Nat.beq (c3RankIdx 0 z n2) 0) 113) 113 = true := rfl
theorem rankP_ok_r7 : checkAll2_StateP (rankP_ok_fn .p7) = true := rfl
theorem rankP_ok_r15 : checkAll2_StateP (rankP_ok_fn .p15) = true := rfl
theorem rankP_ok_r23 : checkAll2_StateP (rankP_ok_fn .p23) = true := rfl
theorem rankP_ok_r31 : checkAll2_StateP (rankP_ok_fn .p31) = true := rfl
theorem ob2_r0 : ob2_idx_row 0 = true := rfl
theorem ob2_r4 : ob2_idx_row 4 = true := rfl
theorem ob2_r8 : ob2_idx_row 8 = true := rfl
theorem ob2_r12 : ob2_idx_row 12 = true := rfl
theorem ob2_r16 : ob2_idx_row 16 = true := rfl
theorem ob2_r20 : ob2_idx_row 20 = true := rfl
theorem ob2_r24 : ob2_idx_row 24 = true := rfl
theorem ob2_r28 : ob2_idx_row 28 = true := rfl
theorem ob2_r32 : ob2_idx_row 32 = true := rfl
theorem ob2_r36 : ob2_idx_row 36 = true := rfl
theorem ob2_r40 : ob2_idx_row 40 = true := rfl
theorem ob2_r44 : ob2_idx_row 44 = true := rfl
theorem ob2_r48 : ob2_idx_row 48 = true := rfl
theorem ob2_r52 : ob2_idx_row 52 = true := rfl
theorem ob2_r56 : ob2_idx_row 56 = true := rfl
theorem ob2_r60 : ob2_idx_row 60 = true := rfl
theorem ob2_r64 : ob2_idx_row 64 = true := rfl
theorem ob2_r68 : ob2_idx_row 68 = true := rfl
theorem ob2_r72 : ob2_idx_row 72 = true := rfl
theorem ob2_r76 : ob2_idx_row 76 = true := rfl
theorem ob2_r80 : ob2_idx_row 80 = true := rfl
theorem ob2_r84 : ob2_idx_row 84 = true := rfl
theorem ob2_r88 : ob2_idx_row 88 = true := rfl
theorem ob2_r92 : ob2_idx_row 92 = true := rfl

end FormalQ5Final
