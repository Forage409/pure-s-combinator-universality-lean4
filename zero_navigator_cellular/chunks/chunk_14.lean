import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_14 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h14) y) z) (deltaHN (deltaHN .h14 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_30 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h30) y) z) (deltaHN (deltaHN .h30 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_11 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h11 y z) = true := rfl

theorem preorders_HN_row_27 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h27 y z) = true := rfl

theorem s_row_SN_6 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s6) y) z) (deltaSN (deltaSN .s6 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_22 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s22) y) z) (deltaSN (deltaSN .s22 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_38 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s38) y) z) (deltaSN (deltaSN .s38 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_15 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s15 y z) = true := rfl

theorem preorders_SN_row_31 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s31 y z) = true := rfl

theorem s_row_P_6 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p6) y) z) (deltaP (deltaP .p6 z) (deltaP y z))) = true := rfl

theorem s_row_P_22 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p22) y) z) (deltaP (deltaP .p22 z) (deltaP y z))) = true := rfl

theorem s_row_P_38 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p38) y) z) (deltaP (deltaP .p38 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_15 : checkAll2_StateP (fun y z => allPreordersStep_P .p15 y z) = true := rfl

theorem preorders_P_row_31 : checkAll2_StateP (fun y z => allPreordersStep_P .p31 y z) = true := rfl

end ZeroNavigatorCellular
