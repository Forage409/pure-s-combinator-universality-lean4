import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_0 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h0) y) z) (deltaHN (deltaHN .h0 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_16 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h16) y) z) (deltaHN (deltaHN .h16 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_32 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h32) y) z) (deltaHN (deltaHN .h32 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_13 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h13 y z) = true := rfl

theorem preorders_HN_row_29 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h29 y z) = true := rfl

theorem s_row_SN_8 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s8) y) z) (deltaSN (deltaSN .s8 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_24 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s24) y) z) (deltaSN (deltaSN .s24 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_1 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s1 y z) = true := rfl

theorem preorders_SN_row_17 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s17 y z) = true := rfl

theorem preorders_SN_row_33 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s33 y z) = true := rfl

theorem s_row_P_8 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p8) y) z) (deltaP (deltaP .p8 z) (deltaP y z))) = true := rfl

theorem s_row_P_24 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p24) y) z) (deltaP (deltaP .p24 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_1 : checkAll2_StateP (fun y z => allPreordersStep_P .p1 y z) = true := rfl

theorem preorders_P_row_17 : checkAll2_StateP (fun y z => allPreordersStep_P .p17 y z) = true := rfl

theorem preorders_P_row_33 : checkAll2_StateP (fun y z => allPreordersStep_P .p33 y z) = true := rfl

end ZeroNavigatorCellular
