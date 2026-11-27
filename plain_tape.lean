import full_root_selector

/- Conventional finite zipper tape, independent of the S representation. -/

structure PlainConfig where
  left : List Bool
  bit : Bool
  right : List Bool
  state : Fin 132
  deriving DecidableEq, Repr

def plainNext (program : BinaryProgram) (c : PlainConfig) : Option PlainConfig :=
  match program c.state c.bit with
  | none => none
  | some inst =>
    match inst.direction with
    | .stay => some ⟨c.left,inst.write,c.right,inst.next⟩
    | .right => match c.right with
      | [] => some ⟨c.left ++ [inst.write],false,[],inst.next⟩
      | bit :: rest => some ⟨c.left ++ [inst.write],bit,rest,inst.next⟩
    | .left => match c.left.reverse with
      | [] => some ⟨[],inst.write,c.right,inst.next⟩
      | bit :: rest => some ⟨rest.reverse,bit,inst.write :: c.right,inst.next⟩

def cellBits (cells : List (List UniversalCell)) : List Bool := cells.map (fun c => (decodedCell c).bit)

def PlainRep (cells : List (List UniversalCell)) (c : PlainConfig) : Prop :=
  ∃ before source after,
    cells = before ++ source :: after ∧ AllOff before ∧ ActiveAt source c.state c.bit ∧ AllOff after ∧
      cellBits before = c.left ∧ cellBits after = c.right

def offRecords (bit : Bool) : List UniversalCell := if bit then [offCellRecord true] else []

theorem off_records_decode (bit : Bool) : decodedCell (offRecords bit) = ⟨bit,.off,0⟩ := by
  cases bit <;> rfl

theorem off_records_alloff (bits : List Bool) : AllOff (bits.map offRecords) := by
  intro cell hc
  obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp hc
  rw [off_records_decode]

theorem off_records_bits (bits : List Bool) : cellBits (bits.map offRecords) = bits := by
  unfold cellBits
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [off_records_decode,ih]

def initialRecords (c : PlainConfig) : List (List UniversalCell) :=
  c.left.map offRecords ++ [ [activeCellRecord c.bit c.state] ] ++ c.right.map offRecords

theorem initial_records_represent (c : PlainConfig) : PlainRep (initialRecords c) c := by
  refine ⟨c.left.map offRecords,[activeCellRecord c.bit c.state],c.right.map offRecords,?_,?_,?_,?_,?_,?_⟩
  · simp [initialRecords,List.append_assoc]
  · exact off_records_alloff c.left
  · simpa using appended_active_is_active [] c.bit c.state
  · exact off_records_alloff c.right
  · exact off_records_bits c.left
  · exact off_records_bits c.right

#print axioms off_records_decode
#print axioms initial_records_represent

theorem plain_stay_lift (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit written : Bool) (next : Fin 132)
    (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after)
    (hrule : program q bit = some ⟨written,next,.stay⟩) :
    let c : PlainConfig := ⟨cellBits before,bit,cellBits after,q⟩
    let c' : PlainConfig := ⟨cellBits before,written,cellBits after,next⟩
    let cells := before ++ source :: after
    let cells' := before ++ (source ++ [activeCellRecord written next]) :: after
    plainNext program c = some c' ∧ SourceTransition program cells cells' ∧ PlainRep cells' c' := by
  constructor
  · simp [plainNext,hrule]
  constructor
  · exact SourceTransition.stay before source after q bit ⟨written,next,.stay⟩ hb hs ha hrule rfl
  · exact ⟨before,source ++ [activeCellRecord written next],after,rfl,hb,
      appended_active_is_active source written next,ha,rfl,rfl⟩

#print axioms plain_stay_lift

theorem plain_right_existing_lift (program : BinaryProgram)
    (before : List (List UniversalCell)) (source destination : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit written : Bool) (next : Fin 132)
    (hb : AllOff before) (hs : ActiveAt source q bit) (hd : (decodedCell destination).status = .off) (ha : AllOff after)
    (hrule : program q bit = some ⟨written,next,.right⟩) :
    let c : PlainConfig := ⟨cellBits before,bit,(decodedCell destination).bit :: cellBits after,q⟩
    let c' : PlainConfig := ⟨cellBits before ++ [written],(decodedCell destination).bit,cellBits after,next⟩
    let newSource := source ++ [pendingRightCell written next,offCellRecord written]
    let newDestination := destination ++ [activeCellRecord (decodedCell destination).bit next]
    let cells := before ++ source :: destination :: after
    let cells' := before ++ newSource :: newDestination :: after
    plainNext program c = some c' ∧ SourceTransition program cells cells' ∧ PlainRep cells' c' := by
  let newSource := source ++ [pendingRightCell written next,offCellRecord written]
  let newDestination := destination ++ [activeCellRecord (decodedCell destination).bit next]
  have hoff : (decodedCell newSource).status = .off := by
    simpa [newSource,List.append_assoc] using appended_off_is_off (source ++ [pendingRightCell written next]) written
  have hprefix : AllOff (before ++ [newSource]) := alloff_append before [newSource] hb (alloff_single newSource hoff)
  have hnewcell : decodedCell newSource = (offCellRecord written).val := by
    simpa [newSource,List.append_assoc] using decoded_cell_append (source ++ [pendingRightCell written next]) (offCellRecord written)
  have hbits : cellBits (before ++ [newSource]) = cellBits before ++ [written] := by
    simp [cellBits,List.map_append,hnewcell,offCellRecord]
  constructor
  · simp [plainNext,hrule]
  constructor
  · exact SourceTransition.rightExisting before source destination after q bit ⟨written,next,.right⟩ hb hs hd ha hrule rfl
  · refine ⟨before ++ [newSource],newDestination,after,?_,hprefix,?_,ha,hbits,rfl⟩
    · simp [newSource,newDestination,List.append_assoc]
    · exact appended_active_is_active destination (decodedCell destination).bit next

#print axioms plain_right_existing_lift

theorem plain_right_extension_lift (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (q : Fin 132) (bit written : Bool) (next : Fin 132)
    (hb : AllOff before) (hs : ActiveAt source q bit)
    (hrule : program q bit = some ⟨written,next,.right⟩) :
    let c : PlainConfig := ⟨cellBits before,bit,[],q⟩
    let c' : PlainConfig := ⟨cellBits before ++ [written],false,[],next⟩
    let newSource := source ++ [pendingRightCell written next,offCellRecord written]
    let cells := before ++ [source]
    let cells' := before ++ [newSource,[activeCellRecord false next]]
    plainNext program c = some c' ∧ SourceTransition program cells cells' ∧ PlainRep cells' c' := by
  let newSource := source ++ [pendingRightCell written next,offCellRecord written]
  have hoff : (decodedCell newSource).status = .off := by
    simpa [newSource,List.append_assoc] using appended_off_is_off (source ++ [pendingRightCell written next]) written
  have hnewcell : decodedCell newSource = (offCellRecord written).val := by
    simpa [newSource,List.append_assoc] using decoded_cell_append (source ++ [pendingRightCell written next]) (offCellRecord written)
  have hprefix : AllOff (before ++ [newSource]) := alloff_append before [newSource] hb (alloff_single newSource hoff)
  have hbits : cellBits (before ++ [newSource]) = cellBits before ++ [written] := by
    simp [cellBits,List.map_append,hnewcell,offCellRecord]
  constructor
  · simp [plainNext,hrule]
  constructor
  · exact SourceTransition.rightExtend before source q bit ⟨written,next,.right⟩ hb hs hrule rfl
  · refine ⟨before ++ [newSource],[activeCellRecord false next],[],?_,hprefix,?_,?_,hbits,rfl⟩
    · simp [newSource,List.append_assoc]
    · simpa using appended_active_is_active [] false next
    · intro c hc; simp at hc

#print axioms plain_right_extension_lift

theorem plain_left_boundary_lift (program : BinaryProgram)
    (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit written : Bool) (next : Fin 132)
    (hs : ActiveAt source q bit) (ha : AllOff after)
    (hrule : program q bit = some ⟨written,next,.left⟩) :
    let c : PlainConfig := ⟨[],bit,cellBits after,q⟩
    let c' : PlainConfig := ⟨[],written,cellBits after,next⟩
    let cells := source :: after
    let cells' := (source ++ [activeCellRecord written next]) :: after
    plainNext program c = some c' ∧ SourceTransition program cells cells' ∧ PlainRep cells' c' := by
  constructor
  · simp [plainNext,hrule]
  constructor
  · exact SourceTransition.leftBoundary source after q bit ⟨written,next,.left⟩ hs ha hrule rfl
  · refine ⟨[],source ++ [activeCellRecord written next],after,?_,?_,?_,ha,rfl,rfl⟩
    · rfl
    · intro x hx; simp at hx
    · exact appended_active_is_active source written next

#print axioms plain_left_boundary_lift

theorem plain_left_existing_lift (program : BinaryProgram)
    (before : List (List UniversalCell)) (destination source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit written : Bool) (next : Fin 132)
    (hb : AllOff before) (hd : (decodedCell destination).status = .off) (hs : ActiveAt source q bit) (ha : AllOff after)
    (hrule : program q bit = some ⟨written,next,.left⟩) :
    let c : PlainConfig := ⟨cellBits before ++ [(decodedCell destination).bit],bit,cellBits after,q⟩
    let c' : PlainConfig := ⟨cellBits before,(decodedCell destination).bit,written :: cellBits after,next⟩
    let newSource := source ++ [pendingLeftCell written next,offCellRecord written]
    let newDestination := destination ++ [activeCellRecord (decodedCell destination).bit next]
    let cells := before ++ destination :: source :: after
    let cells' := before ++ newDestination :: newSource :: after
    plainNext program c = some c' ∧ SourceTransition program cells cells' ∧ PlainRep cells' c' := by
  let newSource := source ++ [pendingLeftCell written next,offCellRecord written]
  let newDestination := destination ++ [activeCellRecord (decodedCell destination).bit next]
  have hoff : (decodedCell newSource).status = .off := by
    simpa [newSource,List.append_assoc] using appended_off_is_off (source ++ [pendingLeftCell written next]) written
  have hnewcell : decodedCell newSource = (offCellRecord written).val := by
    simpa [newSource,List.append_assoc] using decoded_cell_append (source ++ [pendingLeftCell written next]) (offCellRecord written)
  have htail : AllOff (newSource :: after) := by
    have h := alloff_append [newSource] after (alloff_single newSource hoff) ha
    simpa using h
  have hbits : cellBits (newSource :: after) = written :: cellBits after := by
    simp [cellBits,hnewcell,offCellRecord]
  constructor
  · simp [plainNext,hrule]
  constructor
  · exact SourceTransition.leftExisting before destination source after q bit ⟨written,next,.left⟩ hb hd hs ha hrule rfl
  · refine ⟨before,newDestination,newSource :: after,rfl,hb,?_,htail,rfl,hbits⟩
    exact appended_active_is_active destination (decodedCell destination).bit next

#print axioms plain_left_existing_lift

theorem defined_plain_step_lifts (program : BinaryProgram) (c c' : PlainConfig)
    (records : List (List UniversalCell)) (hrep : PlainRep records c)
    (hstep : plainNext program c = some c') :
    ∃ records', SourceTransition program records records' ∧ PlainRep records' c' := by
  cases c with
  | mk left bit right q =>
    obtain ⟨before,source,after,hrecords,hbefore,hsource,hafter,hleft,hright⟩ := hrep
    subst records
    change ActiveAt source q bit at hsource
    change cellBits before = left at hleft
    change cellBits after = right at hright
    subst left
    subst right
    cases hrule : program q bit with
    | none => simp [plainNext,hrule] at hstep
    | some inst =>
      cases inst with
      | mk written next direction =>
        cases direction with
        | stay =>
          obtain ⟨hnative,htransition,hrep'⟩ := plain_stay_lift program before source after q bit written next
            hbefore hsource hafter hrule
          have heq : c' = ⟨cellBits before,written,cellBits after,next⟩ := Option.some.inj (hstep.symm.trans hnative)
          subst c'
          exact ⟨_,htransition,hrep'⟩
        | right =>
          cases after with
          | nil =>
            obtain ⟨hnative,htransition,hrep'⟩ := plain_right_extension_lift program before source q bit written next
              hbefore hsource hrule
            have heq : c' = ⟨cellBits before ++ [written],false,[],next⟩ := Option.some.inj (hstep.symm.trans hnative)
            subst c'
            exact ⟨_,htransition,hrep'⟩
          | cons destination rest =>
            have hd : (decodedCell destination).status = .off := hafter destination (by simp)
            have ht : AllOff rest := by intro cell hc; exact hafter cell (by simp [hc])
            obtain ⟨hnative,htransition,hrep'⟩ := plain_right_existing_lift program before source destination rest q bit written next
              hbefore hsource hd ht hrule
            have hstep' : plainNext program ⟨cellBits before,bit,(decodedCell destination).bit :: cellBits rest,q⟩ = some c' := by
              simpa [cellBits] using hstep
            have heq : c' = ⟨cellBits before ++ [written],(decodedCell destination).bit,cellBits rest,next⟩ :=
              Option.some.inj (hstep'.symm.trans hnative)
            subst c'
            exact ⟨_,htransition,hrep'⟩
        | left =>
          rcases List.eq_nil_or_concat before with hnil | ⟨prior,destination,hprior⟩
          · subst before
            obtain ⟨hnative,htransition,hrep'⟩ := plain_left_boundary_lift program source after q bit written next
              hsource hafter hrule
            have heq : c' = ⟨[],written,cellBits after,next⟩ := Option.some.inj (hstep.symm.trans hnative)
            subst c'
            exact ⟨_,htransition,hrep'⟩
          · rw [List.concat_eq_append] at hprior
            subst before
            have hd : (decodedCell destination).status = .off := hbefore destination (by simp)
            have hb : AllOff prior := by intro cell hc; exact hbefore cell (by simp [hc])
            obtain ⟨hnative,htransition,hrep'⟩ := plain_left_existing_lift program prior destination source after q bit written next
              hb hd hsource hafter hrule
            have hstep' : plainNext program ⟨cellBits prior ++ [(decodedCell destination).bit],bit,cellBits after,q⟩ = some c' := by
              simpa [cellBits,List.map_append] using hstep
            have heq : c' = ⟨cellBits prior,(decodedCell destination).bit,written :: cellBits after,next⟩ :=
              Option.some.inj (hstep'.symm.trans hnative)
            subst c'
            refine ⟨_,?_,hrep'⟩
            simpa [List.append_assoc] using htransition

#print axioms defined_plain_step_lifts

theorem plain_next_none_iff_rule_none (program : BinaryProgram) (c : PlainConfig) :
    plainNext program c = none ↔ program c.state c.bit = none := by
  cases c with
  | mk left bit right q =>
    cases hrule : program q bit with
    | none => simp [plainNext,hrule]
    | some inst =>
      cases inst with
      | mk written next direction =>
        cases direction <;> cases right <;> cases hleft : List.reverse left <;>
          simp [plainNext,hrule,hleft]

theorem stopped_plain_config_lifts (program : BinaryProgram) (c : PlainConfig)
    (records : List (List UniversalCell)) (hrep : PlainRep records c)
    (hstop : plainNext program c = none) : SourceStopped program records := by
  obtain ⟨before,source,after,hrecords,hbefore,hsource,hafter,hleft,hright⟩ := hrep
  exact ⟨before,source,after,c.state,c.bit,hrecords,hbefore,hsource,hafter,
    (plain_next_none_iff_rule_none program c).mp hstop⟩

#print axioms plain_next_none_iff_rule_none
#print axioms stopped_plain_config_lifts

inductive PlainRun (program : BinaryProgram) : Nat → PlainConfig → PlainConfig → Prop where
  | zero (state : PlainConfig) : PlainRun program 0 state state
  | next {n : Nat} {a b c : PlainConfig} : plainNext program a = some b → PlainRun program n b c →
      PlainRun program (n+1) a c

theorem plain_run_lifts (program : BinaryProgram) {n : Nat} {a b : PlainConfig}
    (run : PlainRun program n a b) :
    ∀ records, PlainRep records a → ∃ finalRecords, SourceRun program n records finalRecords ∧ PlainRep finalRecords b := by
  induction run with
  | zero state => intro records hrep; exact ⟨records,SourceRun.zero _,hrep⟩
  | @next n a b c hfirst rest ih =>
    intro records hrep
    obtain ⟨nextRecords,htransition,hrep'⟩ := defined_plain_step_lifts program a b records hrep hfirst
    obtain ⟨finalRecords,hrun,hfinal⟩ := ih nextRecords hrep'
    exact ⟨finalRecords,SourceRun.next htransition hrun,hfinal⟩

#print axioms plain_run_lifts

def PlainEventuallyStops (program : BinaryProgram) (initial : PlainConfig) : Prop :=
  ∃ n final, PlainRun program n initial final ∧ plainNext program final = none

def PlainRunsForever (program : BinaryProgram) (initial : PlainConfig) : Prop :=
  ∀ n, ∃ final, PlainRun program n initial final

theorem plain_run_snoc (program : BinaryProgram) {n : Nat} {a b c : PlainConfig}
    (run : PlainRun program n a b) (step : plainNext program b = some c) : PlainRun program (n+1) a c := by
  induction run with
  | zero state => exact PlainRun.next step (PlainRun.zero _)
  | @next n a b c first rest ih => exact PlainRun.next first (ih step)

theorem plain_no_halt_runs_forever (program : BinaryProgram) (initial : PlainConfig)
    (hnot : ¬ PlainEventuallyStops program initial) : PlainRunsForever program initial := by
  intro n
  induction n with
  | zero => exact ⟨initial,PlainRun.zero _⟩
  | succ n ih =>
    obtain ⟨current,run⟩ := ih
    cases hstep : plainNext program current with
    | none => exfalso; exact hnot ⟨n,current,run,hstep⟩
    | some next => exact ⟨next,plain_run_snoc program run hstep⟩

theorem plain_forever_lifts (program : BinaryProgram) (c : PlainConfig)
    (records : List (List UniversalCell)) (hrep : PlainRep records c)
    (hforever : PlainRunsForever program c) : SourceRunsForever program records := by
  intro n
  obtain ⟨final,run⟩ := hforever n
  obtain ⟨out,hrun,_⟩ := plain_run_lifts program run records hrep
  exact ⟨out,hrun⟩

theorem plain_rep_well_formed (records : List (List UniversalCell)) (c : PlainConfig)
    (hrep : PlainRep records c) : WellFormed records := by
  obtain ⟨before,source,after,heq,hbefore,hsource,hafter,_,_⟩ := hrep
  exact ⟨before,source,after,c.state,c.bit,heq,hbefore,hsource,hafter⟩

theorem plain_halting_iff_selected_halt (program : BinaryProgram) (initial : PlainConfig)
    (d flagDepth : Nat) (hubJunk : Term) :
    PlainEventuallyStops program initial ↔
      ∃ k reached, FullSelectorTrace program k
        (canonicalRoot (initialRecords initial) d (depthBase flagDepth) hubJunk) reached ∧ rootHalt reached = true := by
  have hrep := initial_records_represent initial
  constructor
  · intro hstop
    obtain ⟨n,final,run,hfinal⟩ := hstop
    obtain ⟨finalRecords,hrun,hrepFinal⟩ := plain_run_lifts program run (initialRecords initial) hrep
    have hstopped := stopped_plain_config_lifts program final finalRecords hrepFinal hfinal
    have hsourceStop : SourceEventuallyStops program (initialRecords initial) := ⟨n,finalRecords,hrun,hstopped⟩
    exact (source_halting_iff_selected_halt_event program (initialRecords initial)
      (plain_rep_well_formed _ initial hrep) d flagDepth hubJunk).mp hsourceStop
  · intro hevent
    obtain ⟨k,reached,htrace,hhalt⟩ := hevent
    classical
    by_cases hstop : PlainEventuallyStops program initial
    · exact hstop
    · have hforever := plain_no_halt_runs_forever program initial hstop
      have hsourceForever := plain_forever_lifts program initial (initialRecords initial) hrep hforever
      have hfalse := forever_source_never_triggers_halt program (initialRecords initial) hsourceForever
        d flagDepth hubJunk k reached htrace
      rw [hfalse] at hhalt
      cases hhalt

#print axioms plain_run_snoc
#print axioms plain_no_halt_runs_forever
#print axioms plain_forever_lifts
#print axioms plain_halting_iff_selected_halt
