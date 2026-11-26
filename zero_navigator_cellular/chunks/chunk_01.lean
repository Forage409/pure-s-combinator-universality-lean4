import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_1 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h1) y) z) (deltaHN (deltaHN .h1 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_17 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h17) y) z) (deltaHN (deltaHN .h17 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_33 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h33) y) z) (deltaHN (deltaHN .h33 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_14 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h14 y z) = true := rfl

theorem preorders_HN_row_30 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h30 y z) = true := rfl

theorem s_row_SN_9 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s9) y) z) (deltaSN (deltaSN .s9 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_25 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s25) y) z) (deltaSN (deltaSN .s25 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_2 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s2 y z) = true := rfl

theorem preorders_SN_row_18 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s18 y z) = true := rfl

theorem preorders_SN_row_34 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s34 y z) = true := rfl

theorem s_row_P_9 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p9) y) z) (deltaP (deltaP .p9 z) (deltaP y z))) = true := rfl

theorem s_row_P_25 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p25) y) z) (deltaP (deltaP .p25 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_2 : checkAll2_StateP (fun y z => allPreordersStep_P .p2 y z) = true := rfl

theorem preorders_P_row_18 : checkAll2_StateP (fun y z => allPreordersStep_P .p18 y z) = true := rfl

theorem preorders_P_row_34 : checkAll2_StateP (fun y z => allPreordersStep_P .p34 y z) = true := rfl

end ZeroNavigatorCellular
