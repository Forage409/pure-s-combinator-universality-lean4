import zero_navigator_cellular.cellular_defs

namespace ZeroNavigatorCellular

theorem s_row_HN_7 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h7) y) z) (deltaHN (deltaHN .h7 z) (deltaHN y z))) = true := rfl

theorem s_row_HN_23 : checkAll2_StateHN (fun y z => beq_StateHN (deltaHN (deltaHN (deltaHN .h0 .h23) y) z) (deltaHN (deltaHN .h23 z) (deltaHN y z))) = true := rfl

theorem preorders_HN_row_4 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h4 y z) = true := rfl

theorem preorders_HN_row_20 : checkAll2_StateHN (fun y z => allPreordersStep_HN .h20 y z) = true := rfl

theorem sep_HN_all_bool : checkAll2_StateHN (fun x y => beq_StateHN x y || sep_HN x y) = true := rfl

theorem s_row_SN_15 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s15) y) z) (deltaSN (deltaSN .s15 z) (deltaSN y z))) = true := rfl

theorem s_row_SN_31 : checkAll2_StateSN (fun y z => beq_StateSN (deltaSN (deltaSN (deltaSN .s0 .s31) y) z) (deltaSN (deltaSN .s31 z) (deltaSN y z))) = true := rfl

theorem preorders_SN_row_8 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s8 y z) = true := rfl

theorem preorders_SN_row_24 : checkAll2_StateSN (fun y z => allPreordersStep_SN .s24 y z) = true := rfl

theorem sep_SN_all_bool : checkAll2_StateSN (fun x y => beq_StateSN x y || sep_SN x y) = true := rfl

theorem s_row_P_15 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p15) y) z) (deltaP (deltaP .p15 z) (deltaP y z))) = true := rfl

theorem s_row_P_31 : checkAll2_StateP (fun y z => beq_StateP (deltaP (deltaP (deltaP .p0 .p31) y) z) (deltaP (deltaP .p31 z) (deltaP y z))) = true := rfl

theorem preorders_P_row_8 : checkAll2_StateP (fun y z => allPreordersStep_P .p8 y z) = true := rfl

theorem preorders_P_row_24 : checkAll2_StateP (fun y z => allPreordersStep_P .p24 y z) = true := rfl

theorem sep_P_all_bool : checkAll2_StateP (fun x y => beq_StateP x y || sep_P x y) = true := rfl

end ZeroNavigatorCellular
