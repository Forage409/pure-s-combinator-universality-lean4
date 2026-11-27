import formal_q10_q5_simplified.q5_defs

namespace SimplifiedQ10Q5
open FormalAlgebra
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem dp_bridge_chk : checkNat2 39 39 (fun i j => Nat.beq (pIdx (deltaP (ofPIdx i) (ofPIdx j))) (dpIdx i j) && Nat.ble (dpIdx i j + 1) 39) = true := rfl
theorem dp_s_law_r11 : dp_s_law_row 11 = true := rfl
theorem dp_s_law_r27 : dp_s_law_row 27 = true := rfl
theorem dph_bridge_r4 : dph_bridge_row 4 = true := rfl
theorem dph_bridge_r20 : dph_bridge_row 20 = true := rfl
theorem dph_bridge_r36 : dph_bridge_row 36 = true := rfl
theorem dph_bridge_r52 : dph_bridge_row 52 = true := rfl
theorem dph_bridge_r68 : dph_bridge_row 68 = true := rfl
theorem dph_bridge_r84 : dph_bridge_row 84 = true := rfl
theorem dph_bridge_r100 : dph_bridge_row 100 = true := rfl
theorem ob3_r1 : ob3_idx_row 1 = true := rfl
theorem ob3_r9 : ob3_idx_row 9 = true := rfl
theorem ob3_r17 : ob3_idx_row 17 = true := rfl
theorem ob3_r25 : ob3_idx_row 25 = true := rfl
theorem ob3_r33 : ob3_idx_row 33 = true := rfl
theorem ob3_r41 : ob3_idx_row 41 = true := rfl
theorem ob3_r49 : ob3_idx_row 49 = true := rfl
theorem ob3_r57 : ob3_idx_row 57 = true := rfl
theorem ob3_r65 : ob3_idx_row 65 = true := rfl
theorem ob3_r73 : ob3_idx_row 73 = true := rfl
theorem ob3_r81 : ob3_idx_row 81 = true := rfl
theorem ob3_r89 : ob3_idx_row 89 = true := rfl

end SimplifiedQ10Q5
