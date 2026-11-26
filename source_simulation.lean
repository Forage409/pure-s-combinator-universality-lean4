import canonical_tape
import controller_plan

/- A source transition relation on finite canonical record tapes. This file
   connects the checked native-S movement lemmas to a source step. It does
   not yet show that an independently defined whole-root selector always
   realizes these transitions. -/

def AllOff (cells : List (List UniversalCell)) : Prop :=
  ∀ cell ∈ cells, (decodedCell cell).status = .off

def ActiveAt (cell : List UniversalCell) (q : Fin 132) (bit : Bool) : Prop :=
  decodedCell cell = ⟨bit,.active,q.val⟩

abbrev BinaryProgram := Fin 132 → Bool → Option SourceInstruction

inductive SourceTransition (program : BinaryProgram) :
    List (List UniversalCell) → List (List UniversalCell) → Prop where
  | stay (before : List (List UniversalCell)) (source : List UniversalCell)
      (after : List (List UniversalCell)) (q : Fin 132) (bit : Bool) (inst : SourceInstruction) :
      AllOff before → ActiveAt source q bit → AllOff after →
      program q bit = some inst → inst.direction = .stay →
      SourceTransition program (before ++ source :: after)
        (before ++ (source ++ [activeCellRecord inst.write inst.next]) :: after)
  | leftBoundary (source : List UniversalCell) (after : List (List UniversalCell))
      (q : Fin 132) (bit : Bool) (inst : SourceInstruction) :
      ActiveAt source q bit → AllOff after → program q bit = some inst → inst.direction = .left →
      SourceTransition program (source :: after) ((source ++ [activeCellRecord inst.write inst.next]) :: after)
  | rightExisting (before : List (List UniversalCell)) (source destination : List UniversalCell)
      (after : List (List UniversalCell)) (q : Fin 132) (bit : Bool) (inst : SourceInstruction) :
      AllOff before → ActiveAt source q bit → (decodedCell destination).status = .off → AllOff after →
      program q bit = some inst → inst.direction = .right →
      SourceTransition program (before ++ source :: destination :: after)
        (before ++ (source ++ [pendingRightCell inst.write inst.next,offCellRecord inst.write]) ::
          (destination ++ [activeCellRecord (decodedCell destination).bit inst.next]) :: after)
  | rightExtend (before : List (List UniversalCell)) (source : List UniversalCell)
      (q : Fin 132) (bit : Bool) (inst : SourceInstruction) :
      AllOff before → ActiveAt source q bit → program q bit = some inst → inst.direction = .right →
      SourceTransition program (before ++ [source])
        (before ++ [source ++ [pendingRightCell inst.write inst.next,offCellRecord inst.write],
          [activeCellRecord false inst.next]])
  | leftExisting (before : List (List UniversalCell)) (destination source : List UniversalCell)
      (after : List (List UniversalCell)) (q : Fin 132) (bit : Bool) (inst : SourceInstruction) :
      AllOff before → (decodedCell destination).status = .off → ActiveAt source q bit → AllOff after →
      program q bit = some inst → inst.direction = .left →
      SourceTransition program (before ++ destination :: source :: after)
        (before ++ (destination ++ [activeCellRecord (decodedCell destination).bit inst.next]) ::
          (source ++ [pendingLeftCell inst.write inst.next,offCellRecord inst.write]) :: after)

theorem source_transition_has_native_s_path (program : BinaryProgram) {start finish : List (List UniversalCell)}
    (h : SourceTransition program start finish) (d : Nat) (flag hubJunk : Term) :
    ∃ k, 6 ≤ k ∧ k ≤ 511 ∧ ExactSteps k (canonicalRoot start d flag hubJunk) (canonicalRoot finish d flag hubJunk) := by
  cases h with
  | stay before source after q bit inst hbefore hsource hafter hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_stay_step_native before source after d flag hubJunk inst.write inst.next hbefore hs hafter
    exact ⟨k,lo,by omega,hsteps⟩
  | leftBoundary source after q bit inst hsource hafter hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    have hoff : AllOff ([] : List (List UniversalCell)) := by intro cell h; simp at h
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_stay_step_native [] source after d flag hubJunk inst.write inst.next hoff hs hafter
    exact ⟨k,lo,by omega,hsteps⟩
  | rightExisting before source destination after q bit inst hbefore hsource hdest hafter hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_right_step_native before source destination after d flag hubJunk inst.write inst.next hbefore hs hdest hafter
    exact ⟨k,by omega,by omega,hsteps⟩
  | rightExtend before source q bit inst hbefore hsource hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_right_extension_native before source d flag hubJunk inst.write inst.next hbefore hs
    exact ⟨k,by omega,hi,hsteps⟩
  | leftExisting before destination source after q bit inst hbefore hdest hsource hafter hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_left_step_native before destination source after d flag hubJunk inst.write inst.next hbefore hs hdest hafter
    exact ⟨k,by omega,by omega,hsteps⟩

#print axioms source_transition_has_native_s_path

inductive SourceRun (program : BinaryProgram) : Nat → List (List UniversalCell) → List (List UniversalCell) → Prop where
  | zero (state : List (List UniversalCell)) : SourceRun program 0 state state
  | next {n : Nat} {a b c : List (List UniversalCell)} :
      SourceTransition program a b → SourceRun program n b c → SourceRun program (n+1) a c

theorem finite_source_run_has_native_s_path (program : BinaryProgram) {n : Nat}
    {start finish : List (List UniversalCell)} (run : SourceRun program n start finish)
    (d : Nat) (flag hubJunk : Term) :
    ∃ k, 6*n ≤ k ∧ k ≤ 511*n ∧
      ExactSteps k (canonicalRoot start d flag hubJunk) (canonicalRoot finish d flag hubJunk) := by
  induction run with
  | zero state => exact ⟨0,by simp,by simp,ExactSteps.zero _⟩
  | @next n a b c hstep rest ih =>
    obtain ⟨k1,lo1,hi1,first⟩ := source_transition_has_native_s_path program hstep d flag hubJunk
    obtain ⟨k2,lo2,hi2,remaining⟩ := ih
    refine ⟨k1+k2,?_,?_,exact_steps_trans first remaining⟩ <;> omega

#print axioms finite_source_run_has_native_s_path

theorem newest_cells_append (cells : List UniversalCell) (entry : UniversalCell) (start : Option Cell) :
    newestCells (cells ++ [entry]) start = some entry.val := by
  induction cells generalizing start with
  | nil => rfl
  | cons cell rest ih => simp [newestCells,ih]

theorem decoded_cell_append (cells : List UniversalCell) (entry : UniversalCell) :
    decodedCell (cells ++ [entry]) = entry.val := by
  unfold decodedCell
  rw [newest_cells_append]
  rfl

def WellFormed (cells : List (List UniversalCell)) : Prop :=
  ∃ before source after q bit,
    cells = before ++ source :: after ∧ AllOff before ∧ ActiveAt source q bit ∧ AllOff after

theorem appended_active_is_active (cells : List UniversalCell) (bit : Bool) (q : Fin 132) :
    ActiveAt (cells ++ [activeCellRecord bit q]) q bit := by
  unfold ActiveAt
  rw [decoded_cell_append]
  rfl

theorem appended_off_is_off (cells : List UniversalCell) (bit : Bool) :
    (decodedCell (cells ++ [offCellRecord bit])).status = .off := by
  rw [decoded_cell_append]
  rfl

theorem alloff_append (xs ys : List (List UniversalCell)) :
    AllOff xs → AllOff ys → AllOff (xs ++ ys) := by
  intro hx hy cell hmem
  simp only [List.mem_append] at hmem
  rcases hmem with h | h
  · exact hx cell h
  · exact hy cell h

theorem alloff_single (cell : List UniversalCell) (h : (decodedCell cell).status = .off) : AllOff [cell] := by
  intro x hx
  simp at hx
  subst x
  exact h

#print axioms newest_cells_append
#print axioms decoded_cell_append
#print axioms appended_active_is_active
#print axioms appended_off_is_off

theorem source_transition_preserves_well_formed (program : BinaryProgram) {start finish : List (List UniversalCell)}
    (h : SourceTransition program start finish) : WellFormed finish := by
  cases h with
  | stay before source after q bit inst hbefore hsource hafter hrule hdir =>
    exact ⟨before,source ++ [activeCellRecord inst.write inst.next],after,inst.next,inst.write,
      rfl,hbefore,appended_active_is_active source inst.write inst.next,hafter⟩
  | leftBoundary source after q bit inst hsource hafter hrule hdir =>
    refine ⟨[],source ++ [activeCellRecord inst.write inst.next],after,inst.next,inst.write,?_,?_,?_,hafter⟩
    · rfl
    · intro cell hc; simp at hc
    · exact appended_active_is_active source inst.write inst.next
  | rightExisting before source destination after q bit inst hbefore hsource hdest hafter hrule hdir =>
    let newSource := source ++ [pendingRightCell inst.write inst.next,offCellRecord inst.write]
    let newDestination := destination ++ [activeCellRecord (decodedCell destination).bit inst.next]
    have hoff : (decodedCell newSource).status = .off := by
      simpa [newSource,List.append_assoc] using
        appended_off_is_off (source ++ [pendingRightCell inst.write inst.next]) inst.write
    have hprefix : AllOff (before ++ [newSource]) := alloff_append before [newSource] hbefore (alloff_single newSource hoff)
    refine ⟨before ++ [newSource],newDestination,after,inst.next,(decodedCell destination).bit,?_,hprefix,?_,hafter⟩
    · simp [newSource,newDestination,List.append_assoc]
    · exact appended_active_is_active destination (decodedCell destination).bit inst.next
  | rightExtend before source q bit inst hbefore hsource hrule hdir =>
    let newSource := source ++ [pendingRightCell inst.write inst.next,offCellRecord inst.write]
    let newDestination := [activeCellRecord false inst.next]
    have hoff : (decodedCell newSource).status = .off := by
      simpa [newSource,List.append_assoc] using
        appended_off_is_off (source ++ [pendingRightCell inst.write inst.next]) inst.write
    have hprefix : AllOff (before ++ [newSource]) := alloff_append before [newSource] hbefore (alloff_single newSource hoff)
    refine ⟨before ++ [newSource],newDestination,[],inst.next,false,?_,hprefix,?_,?_⟩
    · simp [newSource,newDestination,List.append_assoc]
    · simpa [newDestination] using appended_active_is_active [] false inst.next
    · intro cell hc; simp at hc
  | leftExisting before destination source after q bit inst hbefore hdest hsource hafter hrule hdir =>
    let newSource := source ++ [pendingLeftCell inst.write inst.next,offCellRecord inst.write]
    let newDestination := destination ++ [activeCellRecord (decodedCell destination).bit inst.next]
    have hoff : (decodedCell newSource).status = .off := by
      simpa [newSource,List.append_assoc] using
        appended_off_is_off (source ++ [pendingLeftCell inst.write inst.next]) inst.write
    have htail : AllOff (newSource :: after) := by
      have hh := alloff_append [newSource] after (alloff_single newSource hoff) hafter
      simpa using hh
    refine ⟨before,newDestination,newSource :: after,inst.next,(decodedCell destination).bit,?_,hbefore,?_,htail⟩
    · rfl
    · exact appended_active_is_active destination (decodedCell destination).bit inst.next

#print axioms source_transition_preserves_well_formed

theorem defined_source_step_exists (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit : Bool) (inst : SourceInstruction)
    (hbefore : AllOff before) (hsource : ActiveAt source q bit) (hafter : AllOff after)
    (hrule : program q bit = some inst) :
    ∃ finish, SourceTransition program (before ++ source :: after) finish := by
  cases hd : inst.direction with
  | stay =>
    exact ⟨_,SourceTransition.stay before source after q bit inst hbefore hsource hafter hrule hd⟩
  | right =>
    cases after with
    | nil =>
      exact ⟨_,SourceTransition.rightExtend before source q bit inst hbefore hsource hrule hd⟩
    | cons destination rest =>
      have hdest : (decodedCell destination).status = .off := hafter destination (by simp)
      have hrest : AllOff rest := by
        intro cell hc
        exact hafter cell (by simp [hc])
      exact ⟨_,SourceTransition.rightExisting before source destination rest q bit inst hbefore hsource hdest hrest hrule hd⟩
  | left =>
    rcases List.eq_nil_or_concat before with hnil | ⟨prior,destination,hprefix⟩
    · subst before
      exact ⟨_,SourceTransition.leftBoundary source after q bit inst hsource hafter hrule hd⟩
    · rw [List.concat_eq_append] at hprefix
      subst before
      have hdest : (decodedCell destination).status = .off := hbefore destination (by simp)
      have hoff : AllOff prior := by
        intro cell hc
        exact hbefore cell (by simp [hc])
      refine ⟨prior ++ (destination ++ [activeCellRecord (decodedCell destination).bit inst.next]) ::
        (source ++ [pendingLeftCell inst.write inst.next,offCellRecord inst.write]) :: after, ?_⟩
      simpa [List.append_assoc] using
        SourceTransition.leftExisting prior destination source after q bit inst hoff hdest hsource hafter hrule hd

#print axioms defined_source_step_exists

theorem alloff_decoded_not_active (cells : List (List UniversalCell)) (h : AllOff cells) :
    ∀ c ∈ cells.map decodedCell, activeCell c = false := by
  intro c hc
  obtain ⟨records,hr,rfl⟩ := List.mem_map.mp hc
  simp [activeCell,h records hr]

theorem alloff_decoded_not_moving (cells : List (List UniversalCell)) (h : AllOff cells) :
    ∀ c ∈ cells.map decodedCell, movingCell c = false := by
  intro c hc
  obtain ⟨records,hr,rfl⟩ := List.mem_map.mp hc
  simp [movingCell,isMoving,h records hr]

theorem well_formed_boundary_priority
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit : Bool) (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after) :
    priorityScan ((before ++ source :: after).map decodedCell) = .active before.length := by
  have hbefore := alloff_decoded_not_active before hb
  have hmoveBefore := alloff_decoded_not_moving before hb
  have hmoveAfter := alloff_decoded_not_moving after ha
  have hsourceActive : activeCell (decodedCell source) = true := by
    rw [hs]
    rfl
  have hsourceMoving : movingCell (decodedCell source) = false := by
    rw [hs]
    rfl
  have hnone : ∀ c ∈ before.map decodedCell ++ decodedCell source :: after.map decodedCell, movingCell c = false := by
    intro c hc
    simp only [List.mem_append,List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact hmoveBefore c hc
    · subst c; exact hsourceMoving
    · exact hmoveAfter c hc
  have hp := active_selected_when_no_pending (before.map decodedCell) (after.map decodedCell)
    (decodedCell source) hnone hbefore hsourceActive
  simpa using hp

#print axioms well_formed_boundary_priority

theorem canonical_boundary_priority
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit : Bool) (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after) (d : Nat) :
    priorityConcrete (canonicalTape (before ++ source :: after) d) = .active before.length := by
  let cells := before ++ source :: after
  have hp := phase_at_good d
  have hm : layoutMatches (storageTapeLayout cells) (canonicalTape cells d) :=
    finite_layout_decodes (storageTapeLayout cells) (phaseAt d).1 (phaseAt d).2 hp.1 hp.2
  rw [concrete_priority_matches_decoded cells (canonicalTape cells d) hm]
  exact well_formed_boundary_priority before source after q bit hb hs ha

#print axioms canonical_boundary_priority

theorem source_transition_has_safe_s_path (program : BinaryProgram) {start finish : List (List UniversalCell)}
    (h : SourceTransition program start finish) (d : Nat) (flag hubJunk : Term)
    (hflag : parseFrame flag = none) :
    ∃ k, 6 ≤ k ∧ k ≤ 511 ∧ SafeExactSteps k (canonicalRoot start d flag hubJunk) (canonicalRoot finish d flag hubJunk) := by
  cases h with
  | stay before source after q bit inst hbefore hsource hafter hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_stay_step_safe before source after d flag hubJunk inst.write inst.next hflag hbefore hs hafter
    exact ⟨k,lo,by omega,hsteps⟩
  | leftBoundary source after q bit inst hsource hafter hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    have hoff : AllOff ([] : List (List UniversalCell)) := by intro cell h; simp at h
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_stay_step_safe [] source after d flag hubJunk inst.write inst.next hflag hoff hs hafter
    exact ⟨k,lo,by omega,hsteps⟩
  | rightExisting before source destination after q bit inst hbefore hsource hdest hafter hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_right_step_safe before source destination after d flag hubJunk inst.write inst.next hflag hbefore hs hdest hafter
    exact ⟨k,by omega,by omega,hsteps⟩
  | rightExtend before source q bit inst hbefore hsource hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_right_extension_safe before source d flag hubJunk inst.write inst.next hflag hbefore hs
    exact ⟨k,by omega,hi,hsteps⟩
  | leftExisting before destination source after q bit inst hbefore hdest hsource hafter hrule hdir =>
    have hs : (decodedCell source).status = .active := by rw [hsource]
    obtain ⟨k,lo,hi,hsteps⟩ := canonical_left_step_safe before destination source after d flag hubJunk inst.write inst.next hflag hbefore hs hdest hafter
    exact ⟨k,by omega,by omega,hsteps⟩


#print axioms source_transition_has_safe_s_path

theorem finite_source_run_has_safe_s_path (program : BinaryProgram) {n : Nat}
    {start finish : List (List UniversalCell)} (run : SourceRun program n start finish)
    (d : Nat) (flag hubJunk : Term) (hflag : parseFrame flag = none) :
    ∃ k, 6*n ≤ k ∧ k ≤ 511*n ∧
      SafeExactSteps k (canonicalRoot start d flag hubJunk) (canonicalRoot finish d flag hubJunk) := by
  induction run with
  | zero state => exact ⟨0,by simp,by simp,SafeExactSteps.zero _⟩
  | @next n a b c hstep rest ih =>
    obtain ⟨k1,lo1,hi1,first⟩ := source_transition_has_safe_s_path program hstep d flag hubJunk hflag
    obtain ⟨k2,lo2,hi2,remaining⟩ := ih
    refine ⟨k1+k2,?_,?_,safe_exact_trans first remaining⟩ <;> omega

#print axioms finite_source_run_has_safe_s_path

theorem canonical_boundary_priority_path
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit : Bool) (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after) (d : Nat) :
    priorityConcretePath (canonicalTape (before ++ source :: after) d) =
      .active (physicalPath (List.replicate before.length true)) := by
  let cells := before ++ source :: after
  have hp := phase_at_good d
  have hm : layoutMatches (storageTapeLayout cells) (canonicalTape cells d) :=
    finite_layout_decodes (storageTapeLayout cells) (phaseAt d).1 (phaseAt d).2 hp.1 hp.2
  have hslot : layoutMatches (slotTapeLayout (cells.map CellSlot.stable)) (canonicalTape cells d) := by
    rw [stable_slots_tape_eq]
    exact hm
  have hdec : (cells.map CellSlot.stable).map slotDecoded = cells.map decodedCell := by
    simp [List.map_map,Function.comp_def,slotDecoded,slotRecords]
  rw [concrete_priority_path_matches_decoded (cells.map CellSlot.stable) (canonicalTape cells d) hslot,hdec]
  rw [well_formed_boundary_priority before source after q bit hb hs ha]
  rfl

#print axioms canonical_boundary_priority_path

theorem stopped_boundary_exposes_halt (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit : Bool) (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after)
    (hstop : program q bit = none) (d flagDepth : Nat) (hubJunk : Term) :
    let cells := before ++ source :: after
    let tape := canonicalTape cells d
    let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2
    ∃ k, 6 ≤ k ∧ k ≤ 7 ∧
      activePlan (physicalPath (List.replicate before.length true)) false (program q bit) = .halt ∧
      SeedHaltTrace tape hubJunk (.active (physicalPath (List.replicate before.length true))) k (depthBase flagDepth) flagOpen ∧
      SafeExactSteps k (canonicalRoot cells d (depthBase flagDepth) hubJunk) (seedHubRoot flagOpen tape hubJunk) ∧
      rootHalt (seedHubRoot flagOpen tape hubJunk) = true := by
  let cells := before ++ source :: after
  let tape := canonicalTape cells d
  let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2
  have hp : priorityConcretePath tape = .active (physicalPath (List.replicate before.length true)) :=
    canonical_boundary_priority_path before source after q bit hb hs ha d
  obtain ⟨k,hk,htrace,hobserved⟩ := halt_field_opens_in_seed flagDepth tape hubJunk _ hp
  have hsafe := seed_halt_trace_is_safe tape hubJunk _ htrace
  refine ⟨k,?_,?_,?_,htrace,hsafe,?_⟩
  · cases hk <;> omega
  · cases hk <;> omega
  · rw [hstop]; rfl
  · rw [root_halt_seed]
    exact hobserved

#print axioms stopped_boundary_exposes_halt

theorem finite_run_then_halt_event (program : BinaryProgram) {n : Nat} {start : List (List UniversalCell)}
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (run : SourceRun program n start (before ++ source :: after))
    (q : Fin 132) (bit : Bool) (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after)
    (hstop : program q bit = none) (d flagDepth : Nat) (hubJunk : Term) :
    let tape := canonicalTape (before ++ source :: after) d
    let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2
    ∃ k, 6*n+6 ≤ k ∧ k ≤ 511*n+7 ∧
      SafeExactSteps k (canonicalRoot start d (depthBase flagDepth) hubJunk) (seedHubRoot flagOpen tape hubJunk) ∧
      rootHalt (seedHubRoot flagOpen tape hubJunk) = true := by
  let tape := canonicalTape (before ++ source :: after) d
  let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2
  obtain ⟨k1,lo1,hi1,hfirst⟩ := finite_source_run_has_safe_s_path program run d (depthBase flagDepth) hubJunk (depth_base_closed flagDepth)
  obtain ⟨k2,lo2,hi2,_,_,hlast,hobserved⟩ :=
    stopped_boundary_exposes_halt program before source after q bit hb hs ha hstop d flagDepth hubJunk
  refine ⟨k1+k2,?_,?_,safe_exact_trans hfirst hlast,hobserved⟩ <;> omega

#print axioms finite_run_then_halt_event
