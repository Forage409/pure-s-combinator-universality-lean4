import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_2 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h2) y) z) (deltaHN (deltaHN .h2 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_18 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h18) y) z) (deltaHN (deltaHN .h18 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_34 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h34) y) z) (deltaHN (deltaHN .h34 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_15 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h15 y z) = true := rfl

theorem preorders_HN_row_31 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h31 y z) = true := rfl

theorem s_row_SN_10 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s10) y) z) (deltaSN (deltaSN .s10 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_26 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s26) y) z) (deltaSN (deltaSN .s26 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_3 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s3 y z) = true := rfl

theorem preorders_SN_row_19 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s19 y z) = true := rfl

theorem preorders_SN_row_35 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s35 y z) = true := rfl

theorem s_row_P_10 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p10) y) z) (deltaP (deltaP .p10 z) (deltaP y z))) = true := rfl

theorem s_row_P_26 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p26) y) z) (deltaP (deltaP .p26 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_3 : checkAll2_StateP (fun y z => allPreordersStep_P .p3 y z) = true := rfl

theorem preorders_P_row_19 : checkAll2_StateP (fun y z => allPreordersStep_P .p19 y z) = true := rfl

theorem preorders_P_row_35 : checkAll2_StateP (fun y z => allPreordersStep_P .p35 y z) = true := rfl

end ZeroNavigatorCellular
