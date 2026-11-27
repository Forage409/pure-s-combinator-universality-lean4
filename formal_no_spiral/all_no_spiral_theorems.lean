import formal_no_spiral.bergstra_and_klop
import formal_no_spiral.waldmann_no_spiral
import formal_no_spiral.conjecture17_open_spirals
import formal_no_spiral.conjecture17_top_termination_corollaries

/-!
# Unified Verification Entrypoint: Constructive No-Spiral & Conjecture 17 Formalization (`formal_no_spiral`)

Imports all four modules of `formal_no_spiral/` and audits every headline theorem with
`#print axioms` in Lean 4.33.1 (verifying zero `sorry`, zero `Classical.choice`, zero `native_decide`,
and zero custom axioms — at most `[propext]`).
-/

-- Target 1: Bergstra's Theorem 13, Constructive Remark 16a, and Klop's Theorem 18
#print axioms FormalNoSpiral.bergstra_no_cycle
#print axioms FormalNoSpiral.bergstra_no_cycle_via_right_spine
#print axioms FormalNoSpiral.infinite_reduction_unbounded_leaves
#print axioms FormalNoSpiral.klop_sp_strong_normalizing
#print axioms FormalNoSpiral.klop_theorem_18_flat_sk_sn

-- Target 2: Waldmann's Theorem 14 (`R_m` LPO `Acc`), Remark 15, and Remark 16b
#print axioms FormalNoSpiral.waldmann_eq_5_4_simulation
#print axioms FormalNoSpiral.waldmann_Rm_strong_normalizing
#print axioms FormalNoSpiral.waldmann_no_spiral
#print axioms FormalNoSpiral.waldmann_open_from_closed
#print axioms FormalNoSpiral.waldmann_no_proper_spiral
#print axioms FormalNoSpiral.no_reducing_fixpoint_combinator
#print axioms FormalNoSpiral.infinite_reduction_unbounded_rm_labels
#print axioms FormalNoSpiral.infinite_reduction_unbounded_redex_leaves

-- Target 3 (Parts I & II): Weighted Right-Spine LPO & Constructive DP Self-Right-Tail Theorem
#print axioms FormalNoSpiral.conjecture17_weighted_waldmann
#print axioms FormalNoSpiral.conjecture17_ground_right_spine_subst
#print axioms FormalNoSpiral.conjecture17_nonincreasing_rs_subst
#print axioms FormalNoSpiral.open_spiral_subterm_or_self_right_tail
#print axioms FormalNoSpiral.conjecture17_no_open_spiral_unless_self_right_tail
#print axioms FormalNoSpiral.conjecture17_distinct_rightLeaf_subst
#print axioms FormalNoSpiral.conjecture17_single_var

-- Target 3 (Part III): Unconditional Empty-Context & Head/Left-Spine Non-Spiralling Theorems
#print axioms FormalNoSpiral.conjecture17_empty_context
#print axioms FormalNoSpiral.conjecture17_var_head_leftCtx
#print axioms FormalNoSpiral.conjecture17_hnf_leftCtx
