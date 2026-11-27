import s_challenge_master_headline

/-!
# Adversarial Referee Deep Kernel & Axiom Audit (`axiom_deep_audit.lean`)
Audits every declaration in `SChallengeMaster` and every pillar theorem across all
imported Wave 1 + Wave 2 subsystems in `s_challenge_master_headline.lean` for:
1. Strict constructive axiom purity (`[propext, Quot.sound]`, `[propext]`, or `[]` — zero `Classical.choice`, zero custom axioms);
2. Cross-subsystem `#guard` parity (11-state `haltAutomaton == pfHaltAutomaton`, 10-leaf seed, 11-leaf `Rule 110`, pocket transducer CTS execution).
-/

-- 1. Complete `#print axioms` on EVERY declaration in `SChallengeMaster`
#print axioms SChallengeMaster.toAlgebraTerm
#print axioms SChallengeMaster.ofAlgebraTerm
#print axioms SChallengeMaster.ofAlgebra_toAlgebra
#print axioms SChallengeMaster.toAlgebra_ofAlgebra
#print axioms SChallengeMaster.toAlgebra_isPureS_eq_noVars
#print axioms SChallengeMaster.step_iff_algebraStep
#print axioms SChallengeMaster.toTopTerm
#print axioms SChallengeMaster.ofTopTerm
#print axioms SChallengeMaster.ofTop_toTop
#print axioms SChallengeMaster.step_iff_topStep
#print axioms SChallengeMaster.toIntrinsicTerm
#print axioms SChallengeMaster.ofIntrinsicTerm
#print axioms SChallengeMaster.ofIntrinsic_toIntrinsic
#print axioms SChallengeMaster.step_iff_intrinsicStep
#print axioms SChallengeMaster.toFixedOrderTerm
#print axioms SChallengeMaster.ofFixedOrderTerm
#print axioms SChallengeMaster.ofFixedOrder_toFixedOrder
#print axioms SChallengeMaster.step_iff_fixedOrderStep
#print axioms SChallengeMaster.toCellularTerm
#print axioms SChallengeMaster.ofCellularTerm
#print axioms SChallengeMaster.ofCellular_toCellular
#print axioms SChallengeMaster.step_iff_cellularStep
#print axioms SChallengeMaster.toBookTerm
#print axioms SChallengeMaster.ofBookTerm
#print axioms SChallengeMaster.ofBook_toBook
#print axioms SChallengeMaster.step_iff_bookStep
#print axioms SChallengeMaster.toNoSpiralTerm
#print axioms SChallengeMaster.ofNoSpiralTerm
#print axioms SChallengeMaster.ofNoSpiral_toNoSpiral
#print axioms SChallengeMaster.step_iff_noSpiralStep
#print axioms SChallengeMaster.toLambdaCLTerm
#print axioms SChallengeMaster.ofLambdaCLTerm
#print axioms SChallengeMaster.ofLambdaCL_toLambdaCL
#print axioms SChallengeMaster.step_iff_lambdaCLStep
#print axioms SChallengeMaster.tapeLen_eq_uConfigLength
#print axioms SChallengeMaster.compiled_tm_initial_leaves_poly
#print axioms SChallengeMaster.grand_pure_s_tm_universality_and_readback
#print axioms SChallengeMaster.grand_program_free_cts_universality
#print axioms SChallengeMaster.grand_controller_separation_and_spurious_halts
#print axioms SChallengeMaster.grand_zero_navigator_barriers_and_open_problems
#print axioms SChallengeMaster.grand_open_question_5_and_bohm_game
#print axioms SChallengeMaster.grand_wolfram_benchmarks_and_minimality_census
#print axioms SChallengeMaster.grand_macroscopic_phase_transitions
#print axioms SChallengeMaster.grand_pocket_transducer_and_lo_jump_ahead
#print axioms SChallengeMaster.grand_conjecture17_and_leaf_preserving_suite
#print axioms SChallengeMaster.grand_simplified_algebras_bohm_and_orders
#print axioms SChallengeMaster.grand_lambda_conjectures_and_equational_suite

-- 2. Pillar theorems across all imported formal subsystems (Wave 1 + Wave 2)
#print axioms source_halts_iff_u_stops
#print axioms u_halt_output_readback
#print axioms encodeSourceInstance_poly_bound
#print axioms constructive_fixed_u_to_s_halting
#print axioms haltAutomaton_accepts_eq_rootHalt
#print axioms mem_allControls
#print axioms invoke_unit_initial_state
#print axioms all_input_linear_microtick_bound
#print axioms exists_microtick_le_node_bound
#print axioms fullSelectorTrace_iff_invokeTrace
#print axioms decodeBareSTermOutput_correct
#print axioms pure_s_normality_and_contraction_contract
#print axioms exact_trajectory_agreement
#print axioms halted_s_term_reads_back_u_config
#print axioms polynomial_initial_size_bound
#print axioms polynomial_trajectory_size_bound
#print axioms FormalProgramFree.pfSelect
#print axioms FormalProgramFree.pfSelect_step_sound
#print axioms FormalProgramFree.pfSelect_halt_iff
#print axioms FormalProgramFree.seed_reduces_to_encodeProgramFreeCTS
#print axioms FormalProgramFree.encodeProgramFreeCTS_isClosedPureS
#print axioms FormalProgramFree.encodeProgramFreeCTS_leaves_poly
#print axioms FormalProgramFree.encodeProgramFreeCTS_trajectory_leaves_poly
#print axioms FormalProgramFree.program_free_cts_halting_iff_automaton
#print axioms FormalProgramFree.decodeProgramFreeCTS_of_halted_trace
#print axioms FormalWolframFrontier.PocketTreeTransducer.annotate_steps_exact
#print axioms FormalWolframFrontier.PocketTreeTransducer.locateRedex_steps_le_depth
#print axioms FormalWolframFrontier.PocketTreeTransducer.transducer_steps_linear_bound
#print axioms FormalWolframFrontier.pocketPFSelect_eq_pfSelect
#print axioms FormalWolframFrontier.pocket_transducer_cts_universality
#print axioms FormalWolframFrontier.zachos_all_step_closed_form
#print axioms FormalWolframFrontier.wolfram2_vs_w2Twin_shift_14
#print axioms FormalWolframFrontier.tenLeafSeed_all_step_exact_leaves
#print axioms FormalWolframFrontier.aaa_lo_and_multiway_master
#print axioms FormalWolframFrontier.goe_s2_iff
#print axioms FormalWolframFrontier.decideGardenOfEdenNF_iff
#print axioms FormalAlgebra.TrivialRuleSeparation.fixed_universal_trivial_rule_separation
#print axioms FormalAlgebra.waldmann_theorem_9
#print axioms FormalAlgebra.barendregt_open_problem_10
#print axioms FormalAlgebra.barendregt_question_7_solution
#print axioms FormalTopTermination.waldmann_theorem_29_top_termination
#print axioms FormalTopTermination.every_closed_sterm_has_rnf
#print axioms IntrinsicTheorems.aaa_not_conv_aaas
#print axioms ZeroNavigatorFixedOrder.no_six_consecutive_case3_li
#print axioms ZeroNavigatorFixedOrder.pure_line_all_six_coincide
#print axioms ZeroNavigatorFixedOrder.zachos_unified_quadratic_trace
#print axioms ZeroNavigatorMultiway.scott_q30_gk_cofinality
#print axioms ZeroNavigatorMultiway.decideReduces
#print axioms ZeroNavigatorMultiway.decideConvClosedSN
#print axioms ZeroNavigatorMultiway.no_church_boolean_pair_in_pure_s
#print axioms ZeroNavigatorMultiway.protected_trie_nonhalting_shortcut_7steps
#print axioms ZeroNavigatorMultiway.filin_dispatcher_nonhalting_shortcut_5steps
#print axioms ZeroNavigatorCellular.no_rule110_SN
#print axioms ZeroNavigatorCellular.dnand_rule110_correct
#print axioms Q5SNStratifiedGame.productive_conv_invariant
#print axioms Q5SNStratifiedGame.hasBotWithin_app_left
#print axioms Q5SNStratifiedGame.hasBotWithin_app_right
#print axioms Q5SNStratifiedGame.unique_nonSN_productive_root_redex_state
#print axioms Q5SNStratifiedGame.bohm_game_asymmetry_size8
#print axioms FormalQ5Final.barendregt_open_question_5
#print axioms FormalQ5Final.productive_or_hasBot_closed
#print axioms SimplifiedQ31Q7.question_31_infinite_family
#print axioms SimplifiedQ31Q7.question_7_atomic_leaf_splits
#print axioms SimplifiedQ10Q5.hasHNF_iff_strongHeadNormalizing
#print axioms SimplifiedQ10Q5.hnA_pointwise_minimal
#print axioms SimplifiedQ10Q5.no_masked_rank1_hnA
#print axioms SimplifiedQ10Q5.barendregt_open_question_5_simplified
#print axioms SimplifiedQ10Q5.ph_113_nerode_minimal
#print axioms FormalQ30Q31Deep.productive_oneSided_bohm_iff_convS
#print axioms FormalQ30Q31Deep.decideConvProd
#print axioms FormalQ30Q31Deep.semiProductive_clockedBohm_unfaithful
#print axioms FormalQ30Q31Deep.closed_normalizing_equivClass_finite
#print axioms FormalOrderAndIsolated.leftSubtreeSum_leafPresStep
#print axioms FormalOrderAndIsolated.leafPres_sn
#print axioms FormalOrderAndIsolated.leftComb_leafPres_quarter_square
#print axioms FormalOrderAndIsolated.visser_van_oostrom_exact_order_exhaustion
#print axioms FormalOrderAndIsolated.minimal_automaton_lower_bound_12
#print axioms FormalOrderAndIsolated.countOrder3_eq_one
#print axioms FormalOrderAndIsolated.exact_rational_order_catalan_densities_certified
#print axioms FormalNoSpiral.bergstra_no_cycle
#print axioms FormalNoSpiral.waldmann_no_spiral
#print axioms FormalNoSpiral.klop_theorem_18_flat_sk_sn
#print axioms FormalNoSpiral.conjecture17_no_open_spiral_unless_self_right_tail
#print axioms FormalNoSpiral.step_minMaxRS_le
#print axioms FormalNoSpiral.conjecture17_one_var_linear_subst_arbitrary_M
#print axioms FormalNoSpiral.conjecture17_iff_no_dpChain_spiral
#print axioms Conjecture17Obstructions.no_open_spiral_bounded_rs
#print axioms Conjecture17Obstructions.no_two_step_open_spiral
#print axioms Conjecture17Obstructions.waldmann_open_parametric_near_miss
#print axioms FormalLambdaConjectures.church_rosser_beta
#print axioms FormalLambdaConjectures.lambdaI_wn_iff_sn
#print axioms FormalLambdaConjectures.conjecture_40_full_cl
#print axioms FormalLambdaConjectures.conjecture_40_pure_s
#print axioms FormalLambdaConjectures.conjecture_42_and_43_refuted_14_leaves
#print axioms FormalLambdaConjectures.conjecture_42_and_43_refuted_15_leaves_nf
#print axioms FormalLambdaConjectures.repaired_conjecture_42
#print axioms FormalLambdaConjectures.question_34_iff_single_constant_saturation
#print axioms FormalLambdaConjectures.question_34_unique_absorbing_sink
#print axioms FormalLambdaConjectures.question_34_incomparable_with_cl_sn
#print axioms FormalQ32.sFree_rigidity
#print axioms FormalQ32.theoremA_waldmann_8_11_separation
#print axioms FormalQ32.convBeta_A_B_open
#print axioms FormalQ32.question_32_negative_resolution
#print axioms FormalQ32.no_finite_equational_axiomatization_of_lambda_beta
#print axioms FormalWolfram12.wolfram_14_dichotomy_master
#print axioms FormalWolfram12.decideContextHalts_exact
#print axioms FormalWolfram12.jump_ahead_sPrefix_exact
#print axioms FormalMinimality.theorem_A_universal_sn_le_6
#print axioms FormalMinimality.theorem_B_exact_size_7_classification
#print axioms FormalMinimality.theorem_C_exact_size_8_classification
#print axioms FormalMinimality.theorem_D_minimal_productive_non_sn_size_9
#print axioms FormalAsymptotics.universal_count_hierarchy
#print axioms FormalAsymptotics.hn_universal_two_sided_density_bounds
#print axioms FormalAsymptotics.sn_and_acceptP_exponential_decay_to_zero

-- 3. Kernel `#guard` & `#eval` Cross-Subsystem Parity Checks
#eval ("walkerBound_on_S", walkerBound .s, "node_formula_on_S", 3500 * (2 * leaves .s - 1))
#guard execTicks 1 initControl (rootCursor .s) == .done .normal

-- Exact 11-state automaton parity: haltAutomaton == pfHaltAutomaton
#guard (List.finRange 11).all fun l =>
  (List.finRange 11).all fun r =>
    haltAutomaton.appState l r == FormalProgramFree.pfHaltAutomaton.appState l r
#guard (List.finRange 11).all fun q =>
  haltAutomaton.accept q == FormalProgramFree.pfHaltAutomaton.accept q

-- Exact 10-leaf seed parity: tenLeafSeed == S(S(SS))(S(SS))(SS)S
#guard tenLeafSeed == (((S ⋅ (S ⋅ B)) ⋅ (S ⋅ B)) ⋅ B) ⋅ S
#guard leaves tenLeafSeed == 10

-- Exact 11-leaf Rule 110 AST parity: S(S(yx)(S(yz)(S(zy)S)))
#guard SChallengeMaster.toCellularTerm
    (S ⋅ (S ⋅ (.var 1 ⋅ .var 0) ⋅ (S ⋅ (.var 1 ⋅ .var 2) ⋅ (S ⋅ (.var 2 ⋅ .var 1) ⋅ S)))) ==
  ZeroNavigatorCellular.rule110Term (.var 0) (.var 1) (.var 2)
#guard leaves (SChallengeMaster.ofCellularTerm
    (ZeroNavigatorCellular.rule110Term .s .s .s)) == 11
