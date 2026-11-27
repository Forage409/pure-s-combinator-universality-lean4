import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_8 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h8) y) z) (deltaHN (deltaHN .h8 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_24 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h24) y) z) (deltaHN (deltaHN .h24 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_5 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h5 y z) = true := rfl

theorem preorders_HN_row_21 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h21 y z) = true := rfl

theorem s_row_SN_0 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s0) y) z) (deltaSN (deltaSN .s0 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_16 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s16) y) z) (deltaSN (deltaSN .s16 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_32 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s32) y) z) (deltaSN (deltaSN .s32 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_9 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s9 y z) = true := rfl

theorem preorders_SN_row_25 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s25 y z) = true := rfl

theorem s_row_P_0 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p0) y) z) (deltaP (deltaP .p0 z) (deltaP y z))) = true := rfl

theorem s_row_P_16 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p16) y) z) (deltaP (deltaP .p16 z) (deltaP y z))) = true := rfl

theorem s_row_P_32 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p32) y) z) (deltaP (deltaP .p32 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_9 : checkAll2_StateP (fun y z => allPreordersStep_P .p9 y z) = true := rfl

theorem preorders_P_row_25 : checkAll2_StateP (fun y z => allPreordersStep_P .p25 y z) = true := rfl

end ZeroNavigatorCellular
