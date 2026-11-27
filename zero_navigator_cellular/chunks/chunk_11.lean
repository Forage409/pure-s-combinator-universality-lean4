import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_11 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h11) y) z) (deltaHN (deltaHN .h11 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_27 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h27) y) z) (deltaHN (deltaHN .h27 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_8 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h8 y z) = true := rfl

theorem preorders_HN_row_24 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h24 y z) = true := rfl

theorem s_row_SN_3 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s3) y) z) (deltaSN (deltaSN .s3 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_19 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s19) y) z) (deltaSN (deltaSN .s19 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_35 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s35) y) z) (deltaSN (deltaSN .s35 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_12 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s12 y z) = true := rfl

theorem preorders_SN_row_28 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s28 y z) = true := rfl

theorem s_row_P_3 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p3) y) z) (deltaP (deltaP .p3 z) (deltaP y z))) = true := rfl

theorem s_row_P_19 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p19) y) z) (deltaP (deltaP .p19 z) (deltaP y z))) = true := rfl

theorem s_row_P_35 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p35) y) z) (deltaP (deltaP .p35 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_12 : checkAll2_StateP (fun y z => allPreordersStep_P .p12 y z) = true := rfl

theorem preorders_P_row_28 : checkAll2_StateP (fun y z => allPreordersStep_P .p28 y z) = true := rfl

end ZeroNavigatorCellular
