import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem dph_bridge_p0 : dph_bridge_row .p0 = true := rfl
theorem dph_bridge_p8 : dph_bridge_row .p8 = true := rfl
theorem dph_bridge_p16 : dph_bridge_row .p16 = true := rfl
theorem dph_bridge_p24 : dph_bridge_row .p24 = true := rfl
theorem dph_bridge_p32 : dph_bridge_row .p32 = true := rfl
theorem ob3_r0 : ob3_idx_row 0 = true := rfl
theorem ob3_r4 : ob3_idx_row 4 = true := rfl
theorem ob3_r8 : ob3_idx_row 8 = true := rfl
theorem ob3_r12 : ob3_idx_row 12 = true := rfl
theorem ob3_r16 : ob3_idx_row 16 = true := rfl
theorem ob3_r20 : ob3_idx_row 20 = true := rfl
theorem ob3_r24 : ob3_idx_row 24 = true := rfl
theorem ob3_r28 : ob3_idx_row 28 = true := rfl
theorem ob3_r32 : ob3_idx_row 32 = true := rfl
theorem ob3_r36 : ob3_idx_row 36 = true := rfl
theorem ob3_r40 : ob3_idx_row 40 = true := rfl
theorem ob3_r44 : ob3_idx_row 44 = true := rfl
theorem ob3_r48 : ob3_idx_row 48 = true := rfl
theorem ob3_r52 : ob3_idx_row 52 = true := rfl
theorem ob3_r56 : ob3_idx_row 56 = true := rfl
theorem ob3_r60 : ob3_idx_row 60 = true := rfl
theorem ob3_r64 : ob3_idx_row 64 = true := rfl
theorem ob3_r68 : ob3_idx_row 68 = true := rfl
theorem ob3_r72 : ob3_idx_row 72 = true := rfl
theorem ob3_r76 : ob3_idx_row 76 = true := rfl
theorem ob3_r80 : ob3_idx_row 80 = true := rfl
theorem ob3_r84 : ob3_idx_row 84 = true := rfl
theorem ob3_r88 : ob3_idx_row 88 = true := rfl
theorem ob3_r92 : ob3_idx_row 92 = true := rfl

end FormalQ5Final
