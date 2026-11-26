import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_6 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h6) y) z) (deltaHN (deltaHN .h6 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_22 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h22) y) z) (deltaHN (deltaHN .h22 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_3 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h3 y z) = true := rfl

theorem preorders_HN_row_19 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h19 y z) = true := rfl

theorem preorders_HN_refl : checkAll1_StateHN (fun x => ((le_HN_0 x x && (le_HN_1 x x && le_HN_2 x x)) && (le_HN_3 x x && (le_HN_4 x x && le_HN_5 x x)))) = true := rfl

theorem s_row_SN_14 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s14) y) z) (deltaSN (deltaSN .s14 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_30 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s30) y) z) (deltaSN (deltaSN .s30 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_7 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s7 y z) = true := rfl

theorem preorders_SN_row_23 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s23 y z) = true := rfl

theorem preorders_SN_refl : checkAll1_StateSN (fun x => ((le_SN_0 x x && le_SN_1 x x) && (le_SN_2 x x && (le_SN_3 x x && le_SN_4 x x)))) = true := rfl

theorem s_row_P_14 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p14) y) z) (deltaP (deltaP .p14 z) (deltaP y z))) = true := rfl

theorem s_row_P_30 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p30) y) z) (deltaP (deltaP .p30 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_7 : checkAll2_StateP (fun y z => allPreordersStep_P .p7 y z) = true := rfl

theorem preorders_P_row_23 : checkAll2_StateP (fun y z => allPreordersStep_P .p23 y z) = true := rfl

theorem preorders_P_refl : checkAll1_StateP (fun x => ((le_P_0 x x && le_P_1 x x) && (le_P_2 x x && (le_P_3 x x && le_P_4 x x)))) = true := rfl

end ZeroNavigatorCellular
