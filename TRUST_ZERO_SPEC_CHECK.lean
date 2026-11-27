import formal_algebra.all_algebra_open_problems
import formal_top_termination.top_termination
import intrinsic_research.intrinsic_theorems
import formal_q5_final.q5_completeness
import SIMPLIFIED_Q31_Q7_BOOK_PROOFS
import formal_wolfram_frontier.wolfram_frontier_master
import formal_lambda_conjectures.all_lambda_conjectures
import formal_q32_equational.all_q32_theorems
import formal_q30_q31_deep.master_q30_q31_deep
import formal_q10_q5_simplified.q5_simplified
import formal_order_and_isolated.all_order_and_isolated_theorems
import formal_no_spiral.all_no_spiral_theorems
import formal_conjecture17_obstructions.conjecture17_obstructions
import formal_conjecture17_deep.minmaxrs_deep_obstructions
import s_challenge_master_headline

/-!
# 60-Second Human-Auditable Specification Check (`TRUST_ZERO_SPEC_CHECK.lean`)

To verify a large mechanized development without reading 202 proof files, an auditor only needs to check two things:
1. **Specification Fidelity:** Do `Term`, `Step`, `StrongNormalizing`, `HasNormalForm`, `HasHNF`, `IsRootNormalForm`, `Productive`, and `Lam` / `BetaStep` match the standard textbook definitions of pure-`S` combinatory logic (`S x y z → (x z)(y z)`) and untyped `λ`-calculus?
2. **Kernel & Axiom Purity:** Does Lean 4's kernel accept the headline theorems with zero `sorry`, zero custom `axiom`s, zero `native_decide`, and zero `Classical.choice`?

Run from the repository root with Lean 4.33.1 (`LEAN_PATH=.`):
```bash
lean TRUST_ZERO_SPEC_CHECK.lean
```
-/

namespace TrustZeroAudit

/-! ## Part 1: Definitional Sanity Checks (`rfl`) on Pure-`S` Syntax & Rewriting -/

example :
    (FormalAlgebra.S = FormalAlgebra.Term.s) ∧
    (∀ x y z : FormalAlgebra.Term,
      FormalAlgebra.Step (FormalAlgebra.S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))) ∧
    (∀ t : FormalAlgebra.Term,
      FormalAlgebra.StrongNormalizing t ↔ Acc (fun b a => FormalAlgebra.Step a b) t) ∧
    (∀ t : FormalAlgebra.Term,
      FormalAlgebra.HasNormalForm t ↔
        ∃ nf, FormalAlgebra.Reduces t nf ∧ (∀ t', ¬ FormalAlgebra.Step nf t')) ∧
    (∀ t : FormalAlgebra.Term,
      FormalAlgebra.HasHNF t ↔
        ∃ h, FormalAlgebra.Reduces t h ∧ FormalAlgebra.spineLen h ≤ 2) ∧
    (∀ t : FormalAlgebra.Term,
      FormalAlgebra.IsRootNormalForm t ↔
        ¬ ∃ x y z, FormalAlgebra.Reduces t (FormalAlgebra.S ⋅ x ⋅ y ⋅ z)) :=
  ⟨rfl, FormalAlgebra.Step.root, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

-- Verify `Q5SNStratifiedGame.Productive` is definitionally `¬ ∃ d, HasBotWithin d t`:
example (t : FormalAlgebra.Term) :
    Q5SNStratifiedGame.Productive t = (¬ ∃ d : Nat, Q5SNStratifiedGame.HasBotWithin d t) := rfl

-- Verify syntax/reduction bijections across all AST namespaces in `s_challenge_master_headline.lean`:
#check @SChallengeMaster.ofAlgebra_toAlgebra
#check @SChallengeMaster.step_iff_algebraStep
#check @SChallengeMaster.step_iff_bookStep
#check @SChallengeMaster.step_iff_noSpiralStep
#check @SChallengeMaster.step_iff_lambdaCLStep

/-! ## Part 2: Exact Type Signatures Across Wolfram Challenge & All 11 Items of Barendregt et al. (2017) -/

-- 1. Waldmann's 39-state Strong Normalization Theorem (`SN ↔ WN ↔ evalSN ≠ .sn38`):
#check @FormalAlgebra.waldmann_theorem_9

-- 2. Question 10 & Footnote 4 (35-state `A_HN`, Automaton-Free Head Conservation & Pure Multiplier `hnA`):
#check @FormalAlgebra.barendregt_open_problem_10
#check @SimplifiedQ10Q5.hasHNF_iff_strongHeadNormalizing
#check @SimplifiedQ10Q5.hnA_pointwise_minimal
#check @SimplifiedQ10Q5.no_masked_rank1_hnA

-- 3. Global Top-Termination, Leaf-Preserving `ΔL = -2` Conservation, & Conjecture 17 Obstructions:
#check @FormalTopTermination.waldmann_theorem_29_top_termination
#check @FormalOrderAndIsolated.leftSubtreeSum_leafPresStep
#check @FormalNoSpiral.conjecture17_no_open_spiral_unless_self_right_tail
#check @FormalNoSpiral.conjecture17_one_var_linear_subst_arbitrary_M
#check @FormalNoSpiral.conjecture17_iff_no_dpChain_spiral

-- 4. Question 5 (39-state `A_P`, Rank-10 Stratification & 113-State `PH` Myhill–Nerode Minimality):
#check @FormalQ5Final.barendregt_open_question_5
#check @SimplifiedQ10Q5.barendregt_open_question_5_simplified
#check @SimplifiedQ10Q5.ph_113_nerode_minimal

-- 5. Questions 7, 30, & 31 (Automaton-Free Book Proofs + Productive Böhm Faithfulness Dichotomy):
#check @SimplifiedQ31Q7.question_7_atomic_leaf_splits
#check @SimplifiedQ31Q7.question_31_infinite_family
#check @FormalQ30Q31Deep.productive_oneSided_bohm_iff_convS
#check @FormalQ30Q31Deep.decideConvProd
#check @FormalQ30Q31Deep.semiProductive_clockedBohm_unfaithful

-- 6. Functional Order `{0,1,2,3}` Minimal Algebras (`35, 12, 3`) & Certified Catalan Order Densities:
#check @FormalOrderAndIsolated.visser_van_oostrom_exact_order_exhaustion
#check @FormalOrderAndIsolated.exact_rational_order_catalan_densities_certified

-- 7. `λI`-Calculus Translation: Conjecture 40 (True), Conjectures 42 & 43 (Refuted + Repaired), Questions 32 & 34:
#check @FormalLambdaConjectures.lambdaI_wn_iff_sn
#check @FormalLambdaConjectures.conjecture_40_full_cl
#check @FormalLambdaConjectures.conjecture_42_and_43_refuted_14_leaves
#check @FormalLambdaConjectures.repaired_conjecture_42
#check @FormalLambdaConjectures.question_34_iff_single_constant_saturation
#check @FormalLambdaConjectures.question_34_unique_absorbing_sink
#check @FormalLambdaConjectures.question_34_incomparable_with_cl_sn
#check @FormalQ32.no_finite_equational_axiomatization_of_lambda_beta

-- 8. Unified Grand Master Theorems (including `(25, 23, 136)` Pocket Tree Transducer & All-Step Jump-Ahead):
#check @SChallengeMaster.grand_pure_s_tm_universality_and_readback
#check @SChallengeMaster.grand_program_free_cts_universality
#check @SChallengeMaster.grand_pocket_transducer_and_lo_jump_ahead
#check @SChallengeMaster.grand_conjecture17_and_leaf_preserving_suite
#check @SChallengeMaster.grand_simplified_algebras_bohm_and_orders
#check @SChallengeMaster.grand_lambda_conjectures_and_equational_suite
#check @SChallengeMaster.grand_controller_separation_and_spurious_halts
#check @SChallengeMaster.grand_zero_navigator_barriers_and_open_problems
#check @SChallengeMaster.grand_wolfram_benchmarks_and_minimality_census
#check @SChallengeMaster.grand_macroscopic_phase_transitions

/-! ## Part 3: Kernel Axiom Footprint Verification (Zero `Classical.choice`, Zero Custom Axioms) -/

#print axioms SChallengeMaster.grand_pure_s_tm_universality_and_readback
#print axioms SChallengeMaster.grand_program_free_cts_universality
#print axioms SChallengeMaster.grand_pocket_transducer_and_lo_jump_ahead
#print axioms SChallengeMaster.grand_conjecture17_and_leaf_preserving_suite
#print axioms SChallengeMaster.grand_simplified_algebras_bohm_and_orders
#print axioms SChallengeMaster.grand_lambda_conjectures_and_equational_suite
#print axioms SChallengeMaster.grand_controller_separation_and_spurious_halts
#print axioms SChallengeMaster.grand_zero_navigator_barriers_and_open_problems
#print axioms SChallengeMaster.grand_wolfram_benchmarks_and_minimality_census
#print axioms SChallengeMaster.grand_macroscopic_phase_transitions

end TrustZeroAudit
