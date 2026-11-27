import formal_lambda_conjectures.lambda_base
import formal_lambda_conjectures.lambda_standardization_conservation
import formal_lambda_conjectures.conjecture_40_order
import formal_lambda_conjectures.conjectures_42_43_and_repair
import formal_lambda_conjectures.question_34_hereditary_and_shattering

/-!
# Unified Verification Entrypoint: Conjectures 40, 42, and 43 of Barendregt et al. (2017)

Imports all four self-contained constructive Lean 4.33.1 modules in
`formal_lambda_conjectures/` and verifies every landmark theorem under `#print axioms`
(at most `[propext]`, zero `Classical.choice`, zero `Quot.sound`, zero `sorry`,
zero `native_decide`, zero custom axioms).
-/

-- Module 1: Untyped `λ`-Calculus, `λI` Variable Conservation, Parallel `β`, & Church–Rosser
#print axioms FormalLambdaConjectures.subst_subst
#print axioms FormalLambdaConjectures.isLambdaI_and_occurs_betaStep
#print axioms FormalLambdaConjectures.parBeta_diamond
#print axioms FormalLambdaConjectures.church_rosser_beta
#print axioms FormalLambdaConjectures.church_rosser_betaConv
#print axioms FormalLambdaConjectures.betaNF_unique

-- Module 2: Weak-Head Standardization & Church's Conservation Theorem on `λI` (`WN_β ↔ SN_β`)
#print axioms FormalLambdaConjectures.wh_standardization_lam
#print axioms FormalLambdaConjectures.wh_standardization_apps_bvar
#print axioms FormalLambdaConjectures.wh_standardization_apps_fvar
#print axioms FormalLambdaConjectures.sn_head_expansion
#print axioms FormalLambdaConjectures.lambdaI_wn_implies_sn
#print axioms FormalLambdaConjectures.lambdaI_wn_iff_sn
#print axioms FormalLambdaConjectures.hasBetaNF_app_fvar

-- Module 3: Resolution of Conjecture 40 (TRUE for Full `CL({S,K,I})` & Pure `CL(S)`)
#print axioms FormalLambdaConjectures.step_to_betaReduces
#print axioms FormalLambdaConjectures.cl_reduces_partial_iff_lam_reduces_abs
#print axioms FormalLambdaConjectures.pureS_reduces_partial_iff_lam_reduces_abs
#print axioms FormalLambdaConjectures.neverConsumesDummyVars_iff_no_partial
#print axioms FormalLambdaConjectures.conjecture_40_full_cl
#print axioms FormalLambdaConjectures.conjecture_40_infinite_order
#print axioms FormalLambdaConjectures.conjecture_40_pure_s
#print axioms FormalLambdaConjectures.pureS_order_le_three
#print axioms FormalLambdaConjectures.toLam_order_le_three

-- Module 4: Refutation of Conjectures 42 & 43 (`14`, `15`, `16`, `18` Leaves) & Repaired Theorem
#print axioms FormalLambdaConjectures.w9_hasNormalForm
#print axioms FormalLambdaConjectures.w9_toLam_no_betaNF
#print axioms FormalLambdaConjectures.n10_is_cl_nf
#print axioms FormalLambdaConjectures.n10_toLam_no_betaNF
#print axioms FormalLambdaConjectures.w_waldmann_is_cl_nf
#print axioms FormalLambdaConjectures.w_waldmann_toLam_no_betaNF
#print axioms FormalLambdaConjectures.conjecture_42_and_43_refuted_14_leaves
#print axioms FormalLambdaConjectures.conjecture_42_and_43_refuted_15_leaves_nf
#print axioms FormalLambdaConjectures.conjecture_42_and_43_refuted_16_leaves_nf
#print axioms FormalLambdaConjectures.conjecture_42_and_43_refuted_waldmann_w
#print axioms FormalLambdaConjectures.conjecture_42_false
#print axioms FormalLambdaConjectures.conjecture_43_false
#print axioms FormalLambdaConjectures.conjecture_42_reverse_valid
#print axioms FormalLambdaConjectures.repaired_conjecture_42


-- Module 5: Question 34 Single-Constant Reduction, Absorbing `λI` Sink, & Congruence Incomparability
#print axioms FormalLambdaConjectures.deepCLNorm_iff_deepNorm1
#print axioms FormalLambdaConjectures.question_34_iff_single_constant_saturation
#print axioms FormalLambdaConjectures.checkDeepNorm1_sound
#print axioms FormalLambdaConjectures.question_34_unique_absorbing_sink
#print axioms FormalLambdaConjectures.question_34_q6_four_way_nf_shattering
#print axioms FormalLambdaConjectures.question_34_incomparable_with_cl_sn
