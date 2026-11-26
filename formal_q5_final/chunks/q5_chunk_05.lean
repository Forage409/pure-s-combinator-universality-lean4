import formal_q5_final.ph_defs

namespace FormalQ5Final
open FormalAlgebra Q5SNStratifiedGame
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem dph_bridge_p1 : dph_bridge_row .p1 = true := rfl
theorem dph_bridge_p9 : dph_bridge_row .p9 = true := rfl
theorem dph_bridge_p17 : dph_bridge_row .p17 = true := rfl
theorem dph_bridge_p25 : dph_bridge_row .p25 = true := rfl
theorem dph_bridge_p33 : dph_bridge_row .p33 = true := rfl
theorem out2d_trans_r1 : out2d_trans_idx_row 1 = true := rfl
theorem out2d_trans_r5 : out2d_trans_idx_row 5 = true := rfl
theorem out2d_trans_r9 : out2d_trans_idx_row 9 = true := rfl
theorem out2d_trans_r13 : out2d_trans_idx_row 13 = true := rfl
theorem out2d_trans_r17 : out2d_trans_idx_row 17 = true := rfl
theorem out2d_trans_r21 : out2d_trans_idx_row 21 = true := rfl
theorem out2d_trans_r25 : out2d_trans_idx_row 25 = true := rfl
theorem out2d_trans_r29 : out2d_trans_idx_row 29 = true := rfl
theorem out2d_trans_r33 : out2d_trans_idx_row 33 = true := rfl
theorem out2d_trans_r37 : out2d_trans_idx_row 37 = true := rfl
theorem out2d_trans_r41 : out2d_trans_idx_row 41 = true := rfl
theorem out2d_trans_r45 : out2d_trans_idx_row 45 = true := rfl
theorem out2d_trans_r49 : out2d_trans_idx_row 49 = true := rfl
theorem out2d_trans_r53 : out2d_trans_idx_row 53 = true := rfl
theorem out2d_trans_r57 : out2d_trans_idx_row 57 = true := rfl
theorem out2d_trans_r61 : out2d_trans_idx_row 61 = true := rfl
theorem out2d_trans_r65 : out2d_trans_idx_row 65 = true := rfl
theorem out2d_trans_r69 : out2d_trans_idx_row 69 = true := rfl
theorem out2d_trans_r73 : out2d_trans_idx_row 73 = true := rfl
theorem out2d_trans_r77 : out2d_trans_idx_row 77 = true := rfl
theorem out2d_trans_r81 : out2d_trans_idx_row 81 = true := rfl
theorem out2d_trans_r85 : out2d_trans_idx_row 85 = true := rfl
theorem out2d_trans_r89 : out2d_trans_idx_row 89 = true := rfl
theorem out2d_trans_r93 : out2d_trans_idx_row 93 = true := rfl

end FormalQ5Final
