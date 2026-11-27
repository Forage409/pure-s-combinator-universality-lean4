import formal_q10_q5_simplified.q5_defs

namespace SimplifiedQ10Q5
open FormalAlgebra
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem witTerm_chk : checkNat1 113 (fun i => noVars (witTerm i) && Nat.beq (phIdx (evalPH (witTerm i))) i) = true := rfl
theorem dp_s_law_r15 : dp_s_law_row 15 = true := rfl
theorem dp_s_law_r31 : dp_s_law_row 31 = true := rfl
theorem dph_bridge_r8 : dph_bridge_row 8 = true := rfl
theorem dph_bridge_r24 : dph_bridge_row 24 = true := rfl
theorem dph_bridge_r40 : dph_bridge_row 40 = true := rfl
theorem dph_bridge_r56 : dph_bridge_row 56 = true := rfl
theorem dph_bridge_r72 : dph_bridge_row 72 = true := rfl
theorem dph_bridge_r88 : dph_bridge_row 88 = true := rfl
theorem dph_bridge_r104 : dph_bridge_row 104 = true := rfl
theorem ob3_r3 : ob3_idx_row 3 = true := rfl
theorem ob3_r11 : ob3_idx_row 11 = true := rfl
theorem ob3_r19 : ob3_idx_row 19 = true := rfl
theorem ob3_r27 : ob3_idx_row 27 = true := rfl
theorem ob3_r35 : ob3_idx_row 35 = true := rfl
theorem ob3_r43 : ob3_idx_row 43 = true := rfl
theorem ob3_r51 : ob3_idx_row 51 = true := rfl
theorem ob3_r59 : ob3_idx_row 59 = true := rfl
theorem ob3_r67 : ob3_idx_row 67 = true := rfl
theorem ob3_r75 : ob3_idx_row 75 = true := rfl
theorem ob3_r83 : ob3_idx_row 83 = true := rfl
theorem ob3_r91 : ob3_idx_row 91 = true := rfl

end SimplifiedQ10Q5
