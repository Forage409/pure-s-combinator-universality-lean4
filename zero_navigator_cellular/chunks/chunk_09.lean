import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_9 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h9) y) z) (deltaHN (deltaHN .h9 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_25 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h25) y) z) (deltaHN (deltaHN .h25 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_6 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h6 y z) = true := rfl

theorem preorders_HN_row_22 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h22 y z) = true := rfl

theorem s_row_SN_1 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s1) y) z) (deltaSN (deltaSN .s1 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_17 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s17) y) z) (deltaSN (deltaSN .s17 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_33 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s33) y) z) (deltaSN (deltaSN .s33 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_10 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s10 y z) = true := rfl

theorem preorders_SN_row_26 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s26 y z) = true := rfl

theorem s_row_P_1 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p1) y) z) (deltaP (deltaP .p1 z) (deltaP y z))) = true := rfl

theorem s_row_P_17 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p17) y) z) (deltaP (deltaP .p17 z) (deltaP y z))) = true := rfl

theorem s_row_P_33 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p33) y) z) (deltaP (deltaP .p33 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_10 : checkAll2_StateP (fun y z => allPreordersStep_P .p10 y z) = true := rfl

theorem preorders_P_row_26 : checkAll2_StateP (fun y z => allPreordersStep_P .p26 y z) = true := rfl

end ZeroNavigatorCellular
