import formal_utm.neary_u311_sim
import formal_controller.constructive_endpoint
import formal_controller.halt_tree_automaton
import formal_controller.finite_tree_walker
import formal_controller.s_output_and_bounds

/-!
# Composed Bare-Term Output Decoder, `InvokeTrace`, and Exact Node Micro-Tick Bound

Closes all formal interface composition items between `formal_utm` and `formal_controller`
with **zero `Classical.choice`**:
1. `exists_microtick_le_node_bound`: for **every** `t : Term` (including the 1-leaf atom `.s`),
   `execTicks` from `(initControl, rootCursor t)` finishes with `.done (invoke t)` in at most
   `3500 * (2 * leaves t - 1)` positive micro-ticks.
2. `InvokeTrace` & `fullSelectorTrace_iff_invokeTrace`: exact step-by-step equivalence between
   `FullSelectorTrace fixedBinaryProgram` and direct iteration of the finite-state walker `invoke`.
3. `decodeBareSTermOutput : Term → Option (List Bool)` & `decodeBareSTermOutput_correct`:
   a single composed linear-time structural reader mapping any halted pure-`S` term `reached`
   directly to `some (canonicalOutput M w hsrc)`.
-/

theorem exists_microtick_le_node_bound (t : Term) :
    ∃ k, 1 ≤ k ∧ k ≤ 3500 * (2 * leaves t - 1) ∧
      execTicks k initControl (rootCursor t) = .done (invoke t) := by
  cases ht : t with
  | s =>
      exact ⟨1, by omega, by simp [leaves], rfl⟩
  | var n =>
      exact ⟨1, by omega, by simp [leaves], rfl⟩
  | app l r =>
      have hl := leaves_pos l
      have hr := leaves_pos r
      have hge2 : 2 ≤ leaves (l ⋅ r) := by simp [leaves]; omega
      obtain ⟨res, ⟨k, hk1, hkB, hex⟩, _⟩ := all_input_validTermination (l ⋅ r)
      have hinv : invoke (l ⋅ r) = res := by
        have hB : execTicks (walkerBound (l ⋅ r)) initControl (rootCursor (l ⋅ r)) = .done res := by
          have heq : walkerBound (l ⋅ r) = k + (walkerBound (l ⋅ r) - k) := by omega
          rw [heq]
          exact execTicks_add_done (walkerBound (l ⋅ r) - k) hex
        simp [invoke, runTicks, hB]
      subst res
      have hbound : walkerBound (l ⋅ r) ≤ 3500 * (2 * leaves (l ⋅ r) - 1) := by
        unfold walkerBound walkerConst
        have hlin : leaves (l ⋅ r) + 1 ≤ 2 * leaves (l ⋅ r) - 1 := by omega
        exact Nat.mul_le_mul_left 3500 hlin
      exact ⟨k, hk1, Nat.le_trans hkB hbound, hex⟩

/-- Explicit `InvokeTrace` directly iterating the finite-state occurrence-tree walker `invoke`. -/
inductive InvokeTrace : Nat → Term → Term → Prop where
  | zero (a : Term) : InvokeTrace 0 a a
  | next {n : Nat} {a b c : Term} :
      invoke a = .contracted b → InvokeTrace n b c → InvokeTrace (n + 1) a c

theorem invokeTrace_trans {n m : Nat} {a b c : Term}
    (h1 : InvokeTrace n a b) (h2 : InvokeTrace m b c) : InvokeTrace (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | next hs _ ih =>
      have r := InvokeTrace.next hs (ih h2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

private theorem step_preserves_pureS {x y : Term} (hs : Step x y) (hp : isPureS x = true) :
    isPureS y = true := by
  induction hs with
  | root a b c =>
      simp only [S, isPureS, Bool.and_eq_true, true_and] at hp ⊢
      exact ⟨⟨hp.1.1, hp.2⟩, ⟨hp.1.2, hp.2⟩⟩
  | left _ ih =>
      simp only [isPureS, Bool.and_eq_true] at hp ⊢
      exact ⟨ih hp.1, hp.2⟩
  | right _ ih =>
      simp only [isPureS, Bool.and_eq_true] at hp ⊢
      exact ⟨hp.1, ih hp.2⟩

theorem invokeTrace_reduces {k : Nat} {a b : Term}
    (h : InvokeTrace k a b) (hp : isPureS a = true) : Reduces a b := by
  induction h with
  | zero x => exact Reduces.refl x
  | @next _ x y _ hinv _ ih =>
      have hstep : Step x y := by
        have hc := pure_s_normality_and_contraction_contract x hp
        rw [hinv] at hc
        exact hc.2 y rfl
      exact Reduces.next hstep (ih (step_preserves_pureS hstep hp))

theorem fullSelectorTrace_iff_invokeTrace (u0 : UConfig) (k : Nat) (reached : Term) :
    FullSelectorTrace fixedBinaryProgram k (sEncodeU u0) reached ↔
      InvokeTrace k (sEncodeU u0) reached := by
  constructor
  · intro hfull
    have haux : ∀ (m : Nat) (mid : Term), m ≤ k →
        FullSelectorTrace fixedBinaryProgram m (sEncodeU u0) mid →
        ∀ (rem : Nat) (fin : Term), m + rem = k →
        FullSelectorTrace fixedBinaryProgram rem mid fin →
        InvokeTrace rem mid fin := by
      intro m mid _ hpre rem
      induction rem generalizing m mid with
      | zero =>
          intro fin _ hrem
          cases hrem
          exact InvokeTrace.zero mid
      | succ r ih =>
          intro fin hsum hrem
          cases hrem with
          | @next _ _ nxt _ path hsel hdir htail =>
              have hcon : contractAt mid path = some nxt :=
                (contractAt_iff_directedStep mid nxt path).mpr hdir
              have hinv : invoke mid = .contracted nxt :=
                (exact_trajectory_agreement u0 hpre).1 path nxt hsel hcon
              have hstep1 : FullSelectorTrace fixedBinaryProgram 1 mid nxt :=
                FullSelectorTrace.next hsel hdir (FullSelectorTrace.zero nxt)
              have hpre' : FullSelectorTrace fixedBinaryProgram (m + 1) (sEncodeU u0) nxt :=
                full_selector_trace_trans hpre hstep1
              exact InvokeTrace.next hinv (ih (m + 1) nxt (by omega) hpre' fin (by omega) htail)
    exact haux 0 (sEncodeU u0) (Nat.zero_le k) (FullSelectorTrace.zero _) k reached (Nat.zero_add k) hfull
  · intro hinv
    have haux : ∀ (m : Nat) (mid : Term), m ≤ k →
        FullSelectorTrace fixedBinaryProgram m (sEncodeU u0) mid →
        ∀ (rem : Nat) (fin : Term), m + rem = k →
        InvokeTrace rem mid fin →
        FullSelectorTrace fixedBinaryProgram rem mid fin := by
      intro m mid _ hpre rem
      induction rem generalizing m mid with
      | zero =>
          intro fin _ hrem
          cases hrem
          exact FullSelectorTrace.zero mid
      | succ r ih =>
          intro fin hsum hrem
          cases hrem with
          | @next _ _ nxt _ hstep htail =>
              obtain ⟨path, nxt', hsel, hcon, hinvEq⟩ := (exact_trajectory_agreement u0 hpre).2
              rw [hstep] at hinvEq
              injection hinvEq with heq
              subst heq
              have hdir : DirectedStep path mid nxt :=
                (contractAt_iff_directedStep mid nxt path).mp hcon
              have hstep1 : FullSelectorTrace fixedBinaryProgram 1 mid nxt :=
                FullSelectorTrace.next hsel hdir (FullSelectorTrace.zero nxt)
              have hpre' : FullSelectorTrace fixedBinaryProgram (m + 1) (sEncodeU u0) nxt :=
                full_selector_trace_trans hpre hstep1
              exact FullSelectorTrace.next hsel hdir (ih (m + 1) nxt (by omega) hpre' fin (by omega) htail)
    exact haux 0 (sEncodeU u0) (Nat.zero_le k) (FullSelectorTrace.zero _) k reached (Nat.zero_add k) hinv

/-- Reconstruct the halted `UConfig` from `(bitHead, syms)` read off a bare pure-`S` term. -/
def uConfigFromSReadback (bitHead : Nat) (syms : List (Fin 11)) : UConfig :=
  let uHead := bitHead / 4
  ⟨((List.range uHead).map (symbolAt syms)).reverse,
   symbolAt syms uHead,
   syms.drop (uHead + 1),
   stateU3⟩

/-- **Single Composed Bare-`S`-Term Output Decoder (`Term → Option (List Bool)`)**:
    Reads the canonical halted source Turing machine output directly from a bare pure-`S` term
    with zero Turing-machine simulation. -/
def decodeBareSTermOutput (root : Term) : Option (List Bool) := do
  let (bitHead, syms) ← readHaltedUConfigFromS root
  decodeHaltedUConfig (uConfigFromSReadback bitHead syms)

private theorem uSymAt_eq_symbolAt : ∀ (xs : List (Fin 11)) (i : Nat), uSymAt xs i = symbolAt xs i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, i + 1 => uSymAt_eq_symbolAt rest i

private theorem symbolAt_drop : ∀ (xs : List (Fin 11)) (k i : Nat),
    symbolAt (xs.drop k) i = symbolAt xs (k + i)
  | [], _, _ => by simp [symbolAt]
  | x :: xs, 0, i => by simp
  | _ :: xs, k + 1, i => by
      have h : k + 1 + i = (k + i) + 1 := by omega
      rw [h]
      exact symbolAt_drop xs k i

private theorem symbolAt_append_left : ∀ (xs ys : List (Fin 11)) (i : Nat),
    i < xs.length → symbolAt (xs ++ ys) i = symbolAt xs i
  | [], _, _, h => by cases h
  | s :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h => symbolAt_append_left xs ys i (Nat.lt_of_succ_lt_succ h)

private theorem symbolAt_append_right : ∀ (xs ys : List (Fin 11)) (i : Nat),
    symbolAt (xs ++ ys) (xs.length + i) = symbolAt ys i
  | [], ys, i => by simp
  | _ :: xs, ys, i => by
      have h : (xs.length + 1) + i = (xs.length + i) + 1 := by omega
      simp only [List.cons_append, List.length_cons, h, symbolAt]
      exact symbolAt_append_right xs ys i

private theorem map_range_symbolAt : ∀ (xs : List (Fin 11)),
    (List.range xs.length).map (symbolAt xs) = xs
  | [] => rfl
  | x :: xs => by
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      exact map_range_symbolAt xs

theorem uConfigEq_from_sReadback {uFinal : UConfig} {syms : List (Fin 11)}
    (hstop : uNext uFinal = none)
    (heqSyms : USymbolsEqModBlanks syms (uConfigTape uFinal)) :
    UConfigEq uFinal (uConfigFromSReadback (4 * uConfigHead uFinal) syms) := by
  cases uFinal with
  | mk leftRev sym right st =>
      have hnone : fixedUProgram st sym = none := (u_next_none_iff_rule_none _).mp hstop
      have htest := u_undefined_exact_pair st sym
      rw [hnone] at htest
      have hpair : st.val = 2 ∧ sym.val = 9 := of_decide_eq_true htest.symm
      have hst : st = stateU3 := by apply Fin.ext; exact hpair.1
      subst hst
      have hdiv : (4 * leftRev.length) / 4 = leftRev.length := by omega
      unfold uConfigFromSReadback uConfigHead
      dsimp only []
      rw [hdiv]
      have hmapEq : (List.range leftRev.length).map (symbolAt syms) = leftRev.reverse := by
        have hlenRev : leftRev.length = leftRev.reverse.length := (List.length_reverse).symm
        rw [hlenRev]
        have hcongr : (List.range leftRev.reverse.length).map (symbolAt syms) =
            (List.range leftRev.reverse.length).map (symbolAt leftRev.reverse) := by
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          rw [heqSyms i]
          exact symbolAt_append_left leftRev.reverse (sym :: right) i hi
        rw [hcongr, map_range_symbolAt]
      have hsymEq : sym = symbolAt syms leftRev.length := by
        rw [heqSyms leftRev.length]
        unfold uConfigTape
        dsimp only []
        have hlenRev : leftRev.length = leftRev.reverse.length + 0 := by simp
        rw [hlenRev, symbolAt_append_right leftRev.reverse (sym :: right) 0]
        rfl
      refine ⟨by rw [hmapEq, List.reverse_reverse], hsymEq, rfl, ?_⟩
      intro j
      rw [uSymAt_eq_symbolAt, uSymAt_eq_symbolAt, symbolAt_drop, heqSyms (leftRev.length + 1 + j)]
      unfold uConfigTape
      dsimp only []
      have hidx : leftRev.length + 1 + j = leftRev.reverse.length + (j + 1) := by simp; omega
      rw [hidx, symbolAt_append_right leftRev.reverse (sym :: right) (j + 1)]
      rfl

theorem decodeBareSTermOutput_correct (M : SourceTM) (w : List Bool)
    (hsrc : SourceEventuallyStopsTM M w) {k : Nat} {reached : Term}
    (htrace : InvokeTrace k (sEncodeU (encodeSourceInstance M w)) reached)
    (hhalt : haltAutomaton.evalAccepts reached = true) :
    decodeBareSTermOutput reached = some (canonicalOutput M w hsrc) := by
  have hfull := (fullSelectorTrace_iff_invokeTrace (encodeSourceInstance M w) k reached).mpr htrace
  have hrootHalt : rootHalt reached = true := by
    rw [← haltAutomaton_accepts_eq_rootHalt]; exact hhalt
  obtain ⟨t, srcFinal, hsrcRun, hsrcStop⟩ := id hsrc
  obtain ⟨normFinal, hnormRun, hfinSt, _, hmFin, hnormStop⟩ :=
    source_halt_to_norm_exit M w hsrcRun hsrcStop
  obtain ⟨uSteps1, u1, _, huRun1, hinv1⟩ :=
    normRun_to_postIndex (normalizeSafeTM M) (encodeMarkedWord w) hnormRun
  obtain ⟨uSteps2, uFinal, _, huRun2, huStop, rightBits, hrbits, heqFinal⟩ :=
    postIndex_halt (normalizeSafeTM M) hinv1 hnormStop
  have huRunTot := uRun_trans huRun1 huRun2
  obtain ⟨syms, hreadS, heqSyms⟩ :=
    halted_s_term_reads_back_u_config huRunTot huStop hfull hrootHalt
  have hactFinal : (normalizeSafeTM M).rule normFinal.state (bitAt normFinal.tape 0) =
      ⟨true, .left, ⟨numNormStates M - 1, by have := numNormStates_ge_3 M; omega⟩⟩ := by
    rw [hmFin.1]
    exact normSafeRule_halt M normFinal.state hfinSt true
  have hwTrue : ((normalizeSafeTM M).rule normFinal.state (bitAt normFinal.tape 0)).write = true := by
    rw [hactFinal]
  let act := (normalizeSafeTM M).rule normFinal.state (bitAt normFinal.tape 0)
  have hbGe2 : 5 + 5 * act.next.val ≥ 2 := by omega
  have heqTrue : UConfigEq
      (uAt (tableFull (normalizeSafeTM M))
        (symDELTA :: (List.replicate (5 * ((normalizeSafeTM M).numStates - act.next.val) - 3) symLA ++
          List.replicate (5 + 5 * act.next.val) symLB ++
          symLA :: encodeRightBit true ++ encodeRightTape rightBits))
        stateU3)
      (uConfigFromSReadback (4 * uConfigHead uFinal) syms) := by
    have heq1 : UConfigEq
        (uAt (tableFull (normalizeSafeTM M))
          (symDELTA :: (List.replicate (5 * ((normalizeSafeTM M).numStates - act.next.val) - 3) symLA ++
            List.replicate (5 + 5 * act.next.val) symLB ++
            symLA :: encodeRightBit true ++ encodeRightTape rightBits))
          stateU3) uFinal := by
      rw [← hwTrue]; exact heqFinal
    exact uConfigEq_trans heq1 (uConfigEq_from_sReadback huStop heqSyms)
  have hdec := decodeHaltedUConfig_of_marked_halt (tableFull (normalizeSafeTM M))
    (5 * ((normalizeSafeTM M).numStates - act.next.val) - 3) (5 + 5 * act.next.val) hbGe2
    srcFinal.tape normFinal.tape rightBits hmFin hrbits
    (uConfigFromSReadback (4 * uConfigHead uFinal) syms) heqTrue
  unfold decodeBareSTermOutput
  rw [hreadS]
  dsimp only [Bind.bind, Option.bind]
  rw [hdec]
  exact congrArg some (canonicalOutput_eq_of_run hsrc hsrcRun hsrcStop).symm

#print axioms exists_microtick_le_node_bound
#print axioms invokeTrace_reduces
#print axioms fullSelectorTrace_iff_invokeTrace
#print axioms decodeBareSTermOutput_correct
