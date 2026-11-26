import formal_refinement.refine_0_0
import formal_refinement.refine_0_1
import formal_refinement.refine_0_2
import formal_refinement.refine_0_3
import formal_refinement.refine_0_4
import formal_refinement.refine_0_5
import formal_refinement.refine_0_6
import formal_refinement.refine_0_7
import formal_refinement.refine_0_8
import formal_refinement.refine_0_9
import formal_refinement.refine_0_10
import formal_refinement.refine_1_0
import formal_refinement.refine_1_1
import formal_refinement.refine_1_2
import formal_refinement.refine_1_3
import formal_refinement.refine_1_4
import formal_refinement.refine_1_5
import formal_refinement.refine_1_6
import formal_refinement.refine_1_7
import formal_refinement.refine_1_8
import formal_refinement.refine_1_9
import formal_refinement.refine_1_10
import formal_refinement.refine_2_0
import formal_refinement.refine_2_1
import formal_refinement.refine_2_2
import formal_refinement.refine_2_3
import formal_refinement.refine_2_4
import formal_refinement.refine_2_5
import formal_refinement.refine_2_6
import formal_refinement.refine_2_7
import formal_refinement.refine_2_8
import formal_refinement.refine_2_10
import formal_refinement.refine_halt

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem u_defined_step_refines (u : UConfig) (hdefined : uNext u ≠ none) :
    ∃ u' out, uNext u = some u' ∧ iteratePlain fixedBinaryProgram 10 (encodeUConfig u) = some out ∧
      PlainEq out (encodeUConfig u') := by
  cases u with
  | mk left symbol right state =>
    have hq : state.val = 0 ∨ state.val = 1 ∨ state.val = 2 := by omega
    have hs : symbol.val = 0 ∨ symbol.val = 1 ∨ symbol.val = 2 ∨ symbol.val = 3 ∨ symbol.val = 4 ∨ symbol.val = 5 ∨ symbol.val = 6 ∨ symbol.val = 7 ∨ symbol.val = 8 ∨ symbol.val = 9 ∨ symbol.val = 10 := by omega
    rcases hq with hq | hq | hq
    · rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (0 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_0_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (1 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_1_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (2 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_2_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (3 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_3_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (4 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_4_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (5 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_5_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (6 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_6_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (7 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_7_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (8 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_8_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (9 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_9_refines left right
      · have hq' : state = (0 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (10 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_0_10_refines left right
    · rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (0 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_0_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (1 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_1_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (2 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_2_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (3 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_3_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (4 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_4_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (5 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_5_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (6 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_6_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (7 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_7_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (8 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_8_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (9 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_9_refines left right
      · have hq' : state = (1 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (10 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_1_10_refines left right
    · rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (0 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_0_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (1 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_1_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (2 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_2_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (3 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_3_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (4 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_4_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (5 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_5_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (6 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_6_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (7 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_7_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (8 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_8_refines left right
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (9 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact False.elim (hdefined (source_2_9_stops left right).1)
      · have hq' : state = (2 : Fin 3) := by apply Fin.ext; exact hq.trans (by decide)
        have hs' : symbol = (10 : Fin 11) := by apply Fin.ext; exact hs.trans (by decide)
        subst state
        subst symbol
        exact source_2_10_refines left right

#print axioms u_defined_step_refines

theorem u_next_none_iff_rule_none (u : UConfig) :
    uNext u = none ↔ fixedUProgram u.state u.symbol = none := by
  cases u with
  | mk left symbol right state =>
    cases hrule : fixedUProgram state symbol with
    | none => simp [uNext,hrule]
    | some inst =>
      cases inst with
      | mk written next direction =>
        cases direction <;> cases right <;> cases left <;> simp [uNext,hrule]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem u_undefined_exact_pair : ∀ (q : Fin 3) (symbol : Fin 11),
    (fixedUProgram q symbol).isNone = decide (q.val = 2 ∧ symbol.val = 9) := by decide

theorem u_stopped_refines (u : UConfig) (hstop : uNext u = none) :
    ∃ mid, iteratePlain fixedBinaryProgram 6 (encodeUConfig u) = some mid ∧ plainNext fixedBinaryProgram mid = none := by
  cases u with
  | mk left symbol right state =>
    have hnone : fixedUProgram state symbol = none := (u_next_none_iff_rule_none _).mp hstop
    have htest := u_undefined_exact_pair state symbol
    rw [hnone] at htest
    have hpair : state.val = 2 ∧ symbol.val = 9 := by
      apply of_decide_eq_true
      exact htest.symm
    have hq : state = (2 : Fin 3) := by apply Fin.ext; exact hpair.1.trans (by decide)
    have hs : symbol = (9 : Fin 11) := by apply Fin.ext; exact hpair.2.trans (by decide)
    subst state
    subst symbol
    exact (source_2_9_stops left right).2

#print axioms u_next_none_iff_rule_none
#print axioms u_undefined_exact_pair
#print axioms u_stopped_refines

theorem plain_eq_trans {a b c : PlainConfig} (h1 : PlainEq a b) (h2 : PlainEq b c) : PlainEq a c := by
  obtain ⟨hl1,hb1,hq1,hr1⟩ := h1
  obtain ⟨hl2,hb2,hq2,hr2⟩ := h2
  exact ⟨hl1.trans hl2,hb1.trans hb2,hq1.trans hq2,fun i => (hr1 i).trans (hr2 i)⟩

theorem iterate_plain_is_run (program : BinaryProgram) (n : Nat) (a b : PlainConfig)
    (h : iteratePlain program n a = some b) : PlainRun program n a b := by
  induction n generalizing a with
  | zero => simp [iteratePlain] at h; subst b; exact PlainRun.zero _
  | succ n ih =>
    cases hs : plainNext program a with
    | none => simp [iteratePlain,hs] at h
    | some next =>
      have hr : iteratePlain program n next = some b := by simpa [iteratePlain,hs] using h
      exact PlainRun.next hs (ih next hr)

theorem plain_run_trans (program : BinaryProgram) {n m : Nat} {a b c : PlainConfig}
    (h : PlainRun program n a b) (k : PlainRun program m b c) : PlainRun program (n+m) a c := by
  induction h with
  | zero _ => simpa using k
  | @next n a b c hab rest ih =>
    have result := PlainRun.next hab (ih k)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

#print axioms plain_eq_trans
#print axioms iterate_plain_is_run
#print axioms plain_run_trans

inductive URun : Nat → UConfig → UConfig → Prop where
  | zero (state : UConfig) : URun 0 state state
  | next {n : Nat} {a b c : UConfig} : uNext a = some b → URun n b c → URun (n+1) a c

theorem u_run_refines_binary {n : Nat} {a b : UConfig} (run : URun n a b) :
    ∀ binary, PlainEq (encodeUConfig a) binary → ∃ final,
      PlainRun fixedBinaryProgram (10*n) binary final ∧ PlainEq (encodeUConfig b) final := by
  induction run with
  | zero state =>
    intro binary heq
    exact ⟨binary,PlainRun.zero _,heq⟩
  | @next n a b c hstep rest ih =>
    intro binary heq
    have hdefined : uNext a ≠ none := by rw [hstep]; simp
    obtain ⟨u',canonical,hsource,hiter,hcanonical⟩ := u_defined_step_refines a hdefined
    have heqU : u' = b := Option.some.inj (hsource.symm.trans hstep)
    subst u'
    have hplain := iterate_plain_is_run fixedBinaryProgram 10 (encodeUConfig a) canonical hiter
    obtain ⟨intermediate,hfirst,hbetween⟩ := plain_run_equiv_forward fixedBinaryProgram hplain binary heq
    have hnextEq : PlainEq (encodeUConfig b) intermediate := plain_eq_trans (plain_eq_symm hcanonical) hbetween
    obtain ⟨final,hrest,hfinal⟩ := ih intermediate hnextEq
    have hcombined := plain_run_trans fixedBinaryProgram hfirst hrest
    refine ⟨final,?_,hfinal⟩
    simpa [Nat.mul_add,Nat.add_comm] using hcombined

#print axioms u_run_refines_binary

def UEventuallyStops (initial : UConfig) : Prop := ∃ n final, URun n initial final ∧ uNext final = none

def URunsForever (initial : UConfig) : Prop := ∀ n, ∃ final, URun n initial final

theorem u_halt_implies_binary_halt (initial : UConfig) :
    UEventuallyStops initial → PlainEventuallyStops fixedBinaryProgram (encodeUConfig initial) := by
  intro hstop
  obtain ⟨n,final,urun,hfinal⟩ := hstop
  obtain ⟨binary,hrun,heq⟩ := u_run_refines_binary urun (encodeUConfig initial) (plain_eq_refl _)
  obtain ⟨canonical,hiter,hcanonicalStop⟩ := u_stopped_refines final hfinal
  have hcanonicalRun := iterate_plain_is_run fixedBinaryProgram 6 (encodeUConfig final) canonical hiter
  obtain ⟨out,hrest,houtEq⟩ := plain_run_equiv_forward fixedBinaryProgram hcanonicalRun binary heq
  have hnext := plain_next_respects_equiv fixedBinaryProgram canonical out houtEq
  cases hstopOut : plainNext fixedBinaryProgram out with
  | none => exact ⟨10*n+6,out,plain_run_trans fixedBinaryProgram hrun hrest,hstopOut⟩
  | some x => simp [hcanonicalStop,hstopOut,OptionPlainEq] at hnext

#print axioms u_halt_implies_binary_halt

theorem u_run_snoc {n : Nat} {a b c : UConfig} (run : URun n a b) (step : uNext b = some c) : URun (n+1) a c := by
  induction run with
  | zero state => exact URun.next step (URun.zero _)
  | @next n a b c first rest ih => exact URun.next first (ih step)

theorem u_no_halt_runs_forever (initial : UConfig) (hnot : ¬ UEventuallyStops initial) : URunsForever initial := by
  intro n
  induction n with
  | zero => exact ⟨initial,URun.zero _⟩
  | succ n ih =>
    obtain ⟨current,run⟩ := ih
    cases hs : uNext current with
    | none => exfalso; exact hnot ⟨n,current,run,hs⟩
    | some next => exact ⟨next,u_run_snoc run hs⟩

theorem plain_run_split (program : BinaryProgram) (n m : Nat) {a b : PlainConfig}
    (run : PlainRun program (n+m) a b) : ∃ middle, PlainRun program n a middle ∧ PlainRun program m middle b := by
  induction n generalizing a b with
  | zero => refine ⟨a,PlainRun.zero _,?_⟩; simpa using run
  | succ n ih =>
    have heq : (n+1)+m = (n+m)+1 := by omega
    rw [heq] at run
    cases run with
    | @next _ _ mid _ hstep rest =>
      obtain ⟨middle,hpre,hsuf⟩ := ih rest
      exact ⟨middle,PlainRun.next hstep hpre,hsuf⟩

theorem u_forever_implies_binary_forever (initial : UConfig) (hforever : URunsForever initial) :
    PlainRunsForever fixedBinaryProgram (encodeUConfig initial) := by
  intro m
  obtain ⟨final,urun⟩ := hforever (m+1)
  obtain ⟨out,hrun,_⟩ := u_run_refines_binary urun (encodeUConfig initial) (plain_eq_refl _)
  have hn : m ≤ 10*(m+1) := by omega
  have heq : 10*(m+1) = m + (10*(m+1)-m) := by omega
  rw [heq] at hrun
  obtain ⟨middle,hprefix,_⟩ := plain_run_split fixedBinaryProgram m (10*(m+1)-m) hrun
  exact ⟨middle,hprefix⟩

theorem plain_run_unique (program : BinaryProgram) {n : Nat} {a b : PlainConfig}
    (run : PlainRun program n a b) : ∀ c, PlainRun program n a c → b = c := by
  induction run with
  | zero state => intro c hc; cases hc; rfl
  | @next k a b c hfirst rest ih =>
    intro out hout
    cases hout with
    | @next _ _ mid _ hother tail =>
      rw [hfirst] at hother
      have eq : b = mid := Option.some.inj hother
      subst mid
      exact ih out tail

theorem u_halt_iff_binary_halt (initial : UConfig) :
    UEventuallyStops initial ↔ PlainEventuallyStops fixedBinaryProgram (encodeUConfig initial) := by
  constructor
  · exact u_halt_implies_binary_halt initial
  · intro hbinary
    classical
    by_cases hu : UEventuallyStops initial
    · exact hu
    · have hforever := u_forever_implies_binary_forever initial (u_no_halt_runs_forever initial hu)
      obtain ⟨n,final,hrun,hstop⟩ := hbinary
      obtain ⟨future,runFuture⟩ := hforever (n+1)
      obtain ⟨middle,hprefix,hsuffix⟩ := plain_run_split fixedBinaryProgram n 1 runFuture
      have hsame : final = middle := plain_run_unique fixedBinaryProgram hrun middle hprefix
      subst middle
      cases hsuffix with
      | next hstep rest => rw [hstop] at hstep; cases hstep

#print axioms u_run_snoc
#print axioms u_no_halt_runs_forever
#print axioms u_forever_implies_binary_forever
#print axioms u_halt_iff_binary_halt
