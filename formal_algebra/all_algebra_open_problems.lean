import formal_algebra.s_structural_laws
import formal_algebra.sn_hn_algebras
import formal_algebra.question7_flipflop
import formal_algebra.trivial_rule_separation

/-!
# Unified Verification Entrypoint: Pure S Algebraic & Controller-Separation Formalization

Imports all four self-contained Lean 4.33.1 modules in `formal_algebra/` and verifies
every landmark theorem in a single unified environment under `#print axioms`
(at most `[propext, Quot.sound]`, zero `Classical.choice`, zero custom axioms).
-/

-- Module 1: `formal_algebra/s_structural_laws.lean`
#print axioms FormalAlgebra.bergstra_no_cycle
#print axioms FormalAlgebra.church_rosser
#print axioms FormalAlgebra.conservation_step
#print axioms FormalAlgebra.wn_implies_sn
#print axioms FormalAlgebra.visser_van_oostrom_no_sab
#print axioms FormalAlgebra.visser_van_oostrom_order_le_3
#print axioms FormalAlgebra.waldmann_no_spiral
#print axioms FormalAlgebra.waldmann_no_proper_spiral

-- Module 2: `formal_algebra/sn_hn_algebras.lean`
#print axioms FormalAlgebra.sn_iff_wn
#print axioms FormalAlgebra.deltaSN_s_law
#print axioms FormalAlgebra.waldmann_theorem_9
#print axioms FormalAlgebra.deltaHN_s_law
#print axioms FormalAlgebra.barendregt_open_problem_10
#print axioms FormalAlgebra.g_spine_dag_property
#print axioms FormalAlgebra.footnote4_rnf_iff
#print axioms FormalAlgebra.five_composite_args_hn34
#print axioms FormalAlgebra.five_composite_args_rnf
#print axioms FormalAlgebra.joint_algebra_exact_112_partition
#print axioms FormalAlgebra.evalSN_ne_sn38_implies_evalHN_ne_hn34
#print axioms FormalAlgebra.third_arg_head_exclusion
#print axioms FormalAlgebra.stepLO_quadratic_two_counter
#print axioms FormalAlgebra.stepLO_quadratic_two_counter_pos

-- Module 3: `formal_algebra/question7_flipflop.lean`
#print axioms FormalAlgebra.hnf2_sn
#print axioms FormalAlgebra.r_gadget_s_not_sn
#print axioms FormalAlgebra.r_gadget_ss_sn
#print axioms FormalAlgebra.barendregt_question_7_solution
#print axioms FormalAlgebra.one_step_rescue_classification
#print axioms FormalAlgebra.both_rescue_plugs_realized

-- Module 4: `formal_algebra/trivial_rule_separation.lean`
#print axioms FormalAlgebra.TrivialRuleSeparation.leafStep_adds_one_leaf
#print axioms FormalAlgebra.TrivialRuleSeparation.trivialRootResetStep_is_leafStep
#print axioms FormalAlgebra.TrivialRuleSeparation.trivialRootResetStep_det
#print axioms FormalAlgebra.TrivialRuleSeparation.trivial_rule_root_reset_universal
#print axioms FormalAlgebra.TrivialRuleSeparation.fixed_universal_trivial_rule_separation
