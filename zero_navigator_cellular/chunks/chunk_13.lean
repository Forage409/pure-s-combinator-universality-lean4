import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_13 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h13) y) z) (deltaHN (deltaHN .h13 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_29 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h29) y) z) (deltaHN (deltaHN .h29 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_10 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h10 y z) = true := rfl

theorem preorders_HN_row_26 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h26 y z) = true := rfl

theorem s_row_SN_5 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s5) y) z) (deltaSN (deltaSN .s5 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_21 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s21) y) z) (deltaSN (deltaSN .s21 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_37 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s37) y) z) (deltaSN (deltaSN .s37 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_14 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s14 y z) = true := rfl

theorem preorders_SN_row_30 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s30 y z) = true := rfl

theorem s_row_P_5 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p5) y) z) (deltaP (deltaP .p5 z) (deltaP y z))) = true := rfl

theorem s_row_P_21 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p21) y) z) (deltaP (deltaP .p21 z) (deltaP y z))) = true := rfl

theorem s_row_P_37 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p37) y) z) (deltaP (deltaP .p37 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_14 : checkAll2_StateP (fun y z => allPreordersStep_P .p14 y z) = true := rfl

theorem preorders_P_row_30 : checkAll2_StateP (fun y z => allPreordersStep_P .p30 y z) = true := rfl

end ZeroNavigatorCellular
