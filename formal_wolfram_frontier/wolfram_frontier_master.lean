import formal_wolfram_frontier.pocket_pf_transducer
import formal_wolfram_frontier.lo_jump_ahead_and_goe

/-!
# Wolfram Frontier Master Entrypoint

Combines both parts of the Wolfram $S$ Combinator Challenge Ruliology & Pocket Transducer Frontier:
1. **`formal_wolfram_frontier.pocket_pf_transducer`**:
   - Generic two-pass contextual finite-state tree transducer `PocketTreeTransducer R Q P`
     with exact Pass-1 step count `2 * leaves t - 1`, unconditional linear total bound
     `≤ 2 * leaves t - 1 + treeDepth t`, and strict bound `+ 2 ≤ 2 * leaves t - 1 + treeDepth t`
     on every `.step` contraction.
   - Explicit minimal `(Fin 25, Fin 23, Fin 136)` instance `pocketPFTransducer` (`25` static
     structural roles, `23` bottom-up states per node, `136` role-free 1-binary-edge top-down
     pointer states, zero universal Turing/tag transition table), 100% extensionally equal to
     `FormalProgramFree.pfSelect` on all closed pure-`S` trees (`pocketPFSelect_eq_pfSelect`),
     with end-to-end Cyclic Tag System universality from the 10-leaf seed `S(S(SS))(S(SS))(SS)S`
     (`pocket_transducer_cts_universality`).
2. **`formal_wolfram_frontier.lo_jump_ahead_and_goe`**:
   - Explicit all-step closed-form `→_{lo}` jump-ahead state and cubic leaf-count theorems on
     `zachos` (`zachos_all_step_closed_form`, `zachos_triangular_staircase_law`),
     `wolfram_2` & its `=_S`-inconvertible `+14` twin `w2Twin` (`wolfram2_all_step_closed_form`,
     `wolfram2_vs_w2Twin_shift_14`), and `tenLeafSeed = R_PF ⋅ S` (`tenLeafSeed_all_step_exact_leaves`),
     plus the 3-rule multiway grammar `GA` and universal `S(SS)` subterm exclusion on `AAA`
     (`aaa_lo_and_multiway_master`).
   - Complete characterization (`goe_s2_iff`), infinite tower law (`goe_s2_of_leaves_le`),
     constructive decidability (`decideGardenOfEdenNF_iff`), and exact Catalan census (`1..7`)
     of Garden-of-Eden closed Normal Forms (`exact_garden_of_eden_census_1_to_7`), together with
     sharp multiway (`↠_S`) vs. `→_{lo}` normal-form subterm appearance separations for both
     halting (`sn_subterm_appearance_separation`) and infinite non-halting
     (`infinite_lo_subterm_appearance_separation`) pure-`S` evolutions.
-/

-- Part I: Pocket Transducer Compression & Linear Complexity
#print axioms FormalWolframFrontier.PocketTreeTransducer.annotate_steps_exact
#print axioms FormalWolframFrontier.PocketTreeTransducer.locateRedex_steps_le_depth
#print axioms FormalWolframFrontier.PocketTreeTransducer.transducer_steps_linear_bound
#print axioms FormalWolframFrontier.PocketTreeTransducer.transducer_steps_strict_on_step
#print axioms FormalWolframFrontier.annotate_state_eq_specBU
#print axioms FormalWolframFrontier.pocketPF_acceptHalt_eq_pfRootHalt
#print axioms FormalWolframFrontier.pocketPF_locate_eq_pfSelectAddress
#print axioms FormalWolframFrontier.pocketPFSelect_eq_pfSelect
#print axioms FormalWolframFrontier.pocketPFTrace_iff_pfTrace
#print axioms FormalWolframFrontier.pocket_transducer_cts_universality

-- Part II: Jump-Ahead Closed Forms, Garden-of-Eden NFs & Multiway/LO Subterm Separation
#print axioms FormalWolframFrontier.zachos_all_step_closed_form
#print axioms FormalWolframFrontier.zachos_triangular_staircase_law
#print axioms FormalWolframFrontier.wolfram2_all_step_closed_form
#print axioms FormalWolframFrontier.wolfram2_vs_w2Twin_shift_14
#print axioms FormalWolframFrontier.tenLeafSeed_all_step_exact_leaves
#print axioms FormalWolframFrontier.aaa_lo_and_multiway_master
#print axioms FormalWolframFrontier.goe_s2_iff
#print axioms FormalWolframFrontier.goe_s2_of_leaves_le
#print axioms FormalWolframFrontier.decideGardenOfEdenNF_iff
#print axioms FormalWolframFrontier.exact_garden_of_eden_census_1_to_7
#print axioms FormalWolframFrontier.sn_subterm_appearance_separation
#print axioms FormalWolframFrontier.infinite_lo_subterm_appearance_separation
