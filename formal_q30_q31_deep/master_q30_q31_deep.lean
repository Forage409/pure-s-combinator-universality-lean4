import formal_q30_q31_deep.q30_finiteness_and_sn_decidability
import formal_q30_q31_deep.q31_productive_bohm_faithfulness

/-!
# Master Verification Entrypoint for `formal_q30_q31_deep`
# Deep Theorems on Dana Scott's Question 30 & Barendregt et al. Question 31

Imports both modules and verifies kernel axiom purity across all headline theorems:
- Zero `sorry` / `sorryAx`
- Zero `Classical.choice`
- Zero `native_decide` / `Lean.ofReduceBool`
- Zero custom `axiom` declarations
-/

-- Target A: Productive Böhm Faithfulness, Clocked-Böhm Dichotomy, and `Prod × All` Decidability
#print axioms FormalQ30Q31Deep.productive_oneSided_bohm_iff_convS
#print axioms FormalQ30Q31Deep.productive_bohm_faithful
#print axioms FormalQ30Q31Deep.decideConvProd
#print axioms FormalQ30Q31Deep.joinOfConvProd
#print axioms FormalQ30Q31Deep.sn_strict_subset_productive
#print axioms FormalQ30Q31Deep.unsolvable_clockedBohm_unfaithful
#print axioms FormalQ30Q31Deep.semiProductive_clockedBohm_unfaithful
#print axioms FormalQ30Q31Deep.zachos_convS_clock_mismatch
#print axioms FormalQ30Q31Deep.productive_nonSN_distinct_same_clockedBohm

-- Target B: Leaf-Growth Dichotomy, Equivalence-Class Finiteness, Isolated NFs, `SN × All` Decidability, and RNF Spine Peeling
#print axioms FormalQ30Q31Deep.step_closed_leaves_eq_iff_stepAtomicS
#print axioms FormalQ30Q31Deep.step_compound_strict_leaves_increase
#print axioms FormalQ30Q31Deep.equivClassOfSN_spec
#print axioms FormalQ30Q31Deep.closed_normalizing_equivClass_finite
#print axioms FormalQ30Q31Deep.exists_step_iff_hasReductPattern
#print axioms FormalQ30Q31Deep.isolated_normalForm_iff
#print axioms FormalQ30Q31Deep.isolatedNF_family
#print axioms FormalQ30Q31Deep.decideConvWithSN
#print axioms FormalQ30Q31Deep.unsolvable_rightApp_convS_iff
