import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_15 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h15) y) z) (deltaHN (deltaHN .h15 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_31 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h31) y) z) (deltaHN (deltaHN .h31 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_12 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h12 y z) = true := rfl

theorem preorders_HN_row_28 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h28 y z) = true := rfl

theorem s_row_SN_7 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s7) y) z) (deltaSN (deltaSN .s7 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_23 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s23) y) z) (deltaSN (deltaSN .s23 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_0 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s0 y z) = true := rfl

theorem preorders_SN_row_16 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s16 y z) = true := rfl

theorem preorders_SN_row_32 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s32 y z) = true := rfl

theorem s_row_P_7 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p7) y) z) (deltaP (deltaP .p7 z) (deltaP y z))) = true := rfl

theorem s_row_P_23 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p23) y) z) (deltaP (deltaP .p23 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_0 : checkAll2_StateP (fun y z => allPreordersStep_P .p0 y z) = true := rfl

theorem preorders_P_row_16 : checkAll2_StateP (fun y z => allPreordersStep_P .p16 y z) = true := rfl

theorem preorders_P_row_32 : checkAll2_StateP (fun y z => allPreordersStep_P .p32 y z) = true := rfl

end ZeroNavigatorCellular
