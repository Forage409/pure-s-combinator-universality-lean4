import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_3 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h3) y) z) (deltaHN (deltaHN .h3 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_19 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h19) y) z) (deltaHN (deltaHN .h19 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_0 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h0 y z) = true := rfl

theorem preorders_HN_row_16 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h16 y z) = true := rfl

theorem preorders_HN_row_32 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h32 y z) = true := rfl

theorem s_row_SN_11 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s11) y) z) (deltaSN (deltaSN .s11 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_27 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s27) y) z) (deltaSN (deltaSN .s27 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_4 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s4 y z) = true := rfl

theorem preorders_SN_row_20 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s20 y z) = true := rfl

theorem preorders_SN_row_36 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s36 y z) = true := rfl

theorem s_row_P_11 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p11) y) z) (deltaP (deltaP .p11 z) (deltaP y z))) = true := rfl

theorem s_row_P_27 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p27) y) z) (deltaP (deltaP .p27 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_4 : checkAll2_StateP (fun y z => allPreordersStep_P .p4 y z) = true := rfl

theorem preorders_P_row_20 : checkAll2_StateP (fun y z => allPreordersStep_P .p20 y z) = true := rfl

theorem preorders_P_row_36 : checkAll2_StateP (fun y z => allPreordersStep_P .p36 y z) = true := rfl

end ZeroNavigatorCellular
