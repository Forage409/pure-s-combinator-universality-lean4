import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_5 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h5) y) z) (deltaHN (deltaHN .h5 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_21 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h21) y) z) (deltaHN (deltaHN .h21 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_2 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h2 y z) = true := rfl

theorem preorders_HN_row_18 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h18 y z) = true := rfl

theorem preorders_HN_row_34 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h34 y z) = true := rfl

theorem s_row_SN_13 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s13) y) z) (deltaSN (deltaSN .s13 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_29 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s29) y) z) (deltaSN (deltaSN .s29 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_6 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s6 y z) = true := rfl

theorem preorders_SN_row_22 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s22 y z) = true := rfl

theorem preorders_SN_row_38 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s38 y z) = true := rfl

theorem s_row_P_13 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p13) y) z) (deltaP (deltaP .p13 z) (deltaP y z))) = true := rfl

theorem s_row_P_29 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p29) y) z) (deltaP (deltaP .p29 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_6 : checkAll2_StateP (fun y z => allPreordersStep_P .p6 y z) = true := rfl

theorem preorders_P_row_22 : checkAll2_StateP (fun y z => allPreordersStep_P .p22 y z) = true := rfl

theorem preorders_P_row_38 : checkAll2_StateP (fun y z => allPreordersStep_P .p38 y z) = true := rfl

end ZeroNavigatorCellular
