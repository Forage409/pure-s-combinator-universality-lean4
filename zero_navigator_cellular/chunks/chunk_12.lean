import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_12 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h12) y) z) (deltaHN (deltaHN .h12 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_28 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h28) y) z) (deltaHN (deltaHN .h28 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_9 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h9 y z) = true := rfl

theorem preorders_HN_row_25 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h25 y z) = true := rfl

theorem s_row_SN_4 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s4) y) z) (deltaSN (deltaSN .s4 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_20 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s20) y) z) (deltaSN (deltaSN .s20 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_36 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s36) y) z) (deltaSN (deltaSN .s36 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_13 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s13 y z) = true := rfl

theorem preorders_SN_row_29 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s29 y z) = true := rfl

theorem s_row_P_4 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p4) y) z) (deltaP (deltaP .p4 z) (deltaP y z))) = true := rfl

theorem s_row_P_20 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p20) y) z) (deltaP (deltaP .p20 z) (deltaP y z))) = true := rfl

theorem s_row_P_36 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p36) y) z) (deltaP (deltaP .p36 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_13 : checkAll2_StateP (fun y z => allPreordersStep_P .p13 y z) = true := rfl

theorem preorders_P_row_29 : checkAll2_StateP (fun y z => allPreordersStep_P .p29 y z) = true := rfl

end ZeroNavigatorCellular
