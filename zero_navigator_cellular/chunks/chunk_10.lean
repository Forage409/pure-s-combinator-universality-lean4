import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_10 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h10) y) z) (deltaHN (deltaHN .h10 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_26 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h26) y) z) (deltaHN (deltaHN .h26 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_7 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h7 y z) = true := rfl

theorem preorders_HN_row_23 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h23 y z) = true := rfl

theorem s_row_SN_2 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s2) y) z) (deltaSN (deltaSN .s2 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_18 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s18) y) z) (deltaSN (deltaSN .s18 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_34 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s34) y) z) (deltaSN (deltaSN .s34 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_11 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s11 y z) = true := rfl

theorem preorders_SN_row_27 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s27 y z) = true := rfl

theorem s_row_P_2 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p2) y) z) (deltaP (deltaP .p2 z) (deltaP y z))) = true := rfl

theorem s_row_P_18 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p18) y) z) (deltaP (deltaP .p18 z) (deltaP y z))) = true := rfl

theorem s_row_P_34 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p34) y) z) (deltaP (deltaP .p34 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_11 : checkAll2_StateP (fun y z => allPreordersStep_P .p11 y z) = true := rfl

theorem preorders_P_row_27 : checkAll2_StateP (fun y z => allPreordersStep_P .p27 y z) = true := rfl

end ZeroNavigatorCellular
