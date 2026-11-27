import formal_q32_equational.lam_beta_cr
import formal_q32_equational.lambda_i_rigidity
import formal_q32_equational.q32_backward_cones
import formal_q32_equational.question_32_negative_resolution

/-!
# Unified Verification Entrypoint: Negative Resolution of Open Question 32 (`formal_q32_equational`)

Imports all four modules of `formal_q32_equational/` and audits every headline theorem with
`#print axioms` in Lean 4.33.1 (verifying zero `sorry`, zero `Classical.choice`, zero `native_decide`,
and zero custom axioms — at most `[propext]`).
-/

-- Target 1: Constructive `λβ` Church–Rosser & Translation Lifting (`lam_beta_cr.lean`)
#print axioms FormalQ32.church_rosser_beta
#print axioms FormalQ32.convBeta_to_nf
#print axioms FormalQ32.convS_to_convBeta
#print axioms FormalQ32.convBeta_subst_term

-- Target 2: `λI` Quantitative Invariants, `S`-Free Rigidity, and Theorem A (`lambda_i_rigidity.lean`)
#print axioms FormalQ32.leaves_le_of_betaReduces
#print axioms FormalQ32.countVar_le_of_betaReduces
#print axioms FormalQ32.exists_sNF_of_betaNF
#print axioms FormalQ32.convS_iff_eq_of_isolated
#print axioms FormalQ32.sFree_rigidity
#print axioms FormalQ32.theoremA_rigidity_var
#print axioms FormalQ32.theoremA_rigidity_S
#print axioms FormalQ32.theoremA_rigidity_SS
#print axioms FormalQ32.theoremA_rigidity_SSS
#print axioms FormalQ32.theoremA_open_8_11_separation
#print axioms FormalQ32.theoremA_waldmann_8_11_separation

-- Target 3: Infinite `(A_open, B_open)` Family & Backward-Cone Global `λβ`-Rigidity (`q32_backward_cones.lean`)
#print axioms FormalQ32.convBeta_A_B_open
#print axioms FormalQ32.convBeta_M_N_closed
#print axioms FormalQ32.rigidity_sTower_SS
#print axioms FormalQ32.rigidity_arm_SS
#print axioms FormalQ32.rigidity_s_arm_SS
#print axioms FormalQ32.rigidity_A_var

-- Target 4: Negative Resolution of Open Question 32 (`question_32_negative_resolution.lean`)
#print axioms FormalQ32.eqTheoryDerives_sound
#print axioms FormalQ32.eqTheoryDerives_subterm_rigid
#print axioms FormalQ32.no_finite_closed_beta_sound_basis
#print axioms FormalQ32.question_32_negative_resolution
#print axioms FormalQ32.no_finite_equational_axiomatization_of_lambda_beta
