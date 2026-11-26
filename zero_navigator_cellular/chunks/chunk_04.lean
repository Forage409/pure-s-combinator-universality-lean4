import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_4 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h4) y) z) (deltaHN (deltaHN .h4 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_20 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h20) y) z) (deltaHN (deltaHN .h20 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_1 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h1 y z) = true := rfl

theorem preorders_HN_row_17 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h17 y z) = true := rfl

theorem preorders_HN_row_33 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h33 y z) = true := rfl

theorem s_row_SN_12 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s12) y) z) (deltaSN (deltaSN .s12 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_28 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s28) y) z) (deltaSN (deltaSN .s28 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_5 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s5 y z) = true := rfl

theorem preorders_SN_row_21 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s21 y z) = true := rfl

theorem preorders_SN_row_37 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s37 y z) = true := rfl

theorem s_row_P_12 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p12) y) z) (deltaP (deltaP .p12 z) (deltaP y z))) = true := rfl

theorem s_row_P_28 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p28) y) z) (deltaP (deltaP .p28 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_5 : checkAll2_StateP (fun y z => allPreordersStep_P .p5 y z) = true := rfl

theorem preorders_P_row_21 : checkAll2_StateP (fun y z => allPreordersStep_P .p21 y z) = true := rfl

theorem preorders_P_row_37 : checkAll2_StateP (fun y z => allPreordersStep_P .p37 y z) = true := rfl

end ZeroNavigatorCellular
