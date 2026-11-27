import stable_version_append

/- If a version subtree changes while its decoded value remains unchanged,
   the global pending-first and active-cell scans see exactly the same tape. -/

def tapeAroundVersion : List (Term × Term) → Term → Term → Term → Term
  | [], version, tail, junk => frameTerm version tail junk
  | (priorVersion, priorJunk) :: rest, version, tail, junk =>
      frameTerm priorVersion (tapeAroundVersion rest version tail junk) priorJunk

theorem seek_ignores_equivalent_version (earlier : List (Term × Term)) (pred : Cell → Bool)
    (a b tail junk : Term) (h : cellFromVersion a = cellFromVersion b) :
    seekConcreteCell pred (tapeAroundVersion earlier a tail junk) =
      seekConcreteCell pred (tapeAroundVersion earlier b tail junk) := by
  induction earlier with
  | nil => simp [tapeAroundVersion,seek_concrete_frame,h]
  | cons x xs ih =>
    rcases x with ⟨version,j⟩
    simp [tapeAroundVersion,seek_concrete_frame,ih]

theorem priority_ignores_equivalent_version (earlier : List (Term × Term))
    (a b tail junk : Term) (h : cellFromVersion a = cellFromVersion b) :
    priorityConcretePath (tapeAroundVersion earlier a tail junk) =
      priorityConcretePath (tapeAroundVersion earlier b tail junk) := by
  unfold priorityConcretePath
  rw [seek_ignores_equivalent_version earlier movingCell a b tail junk h,
      seek_ignores_equivalent_version earlier activeCell a b tail junk h]

#print axioms seek_ignores_equivalent_version
#print axioms priority_ignores_equivalent_version

def priorTapeFrames : List (Term × Term) → List ProtectedFrame
  | [] => []
  | (version,junk) :: rest => priorTapeFrames rest ++ [.right version junk]

def tapeFrames (earlier : List (Term × Term)) (tail junk : Term) : List ProtectedFrame :=
  [.left tail junk] ++ priorTapeFrames earlier

theorem tape_around_is_protected_context (earlier : List (Term × Term)) (version tail junk : Term) :
    tapeAroundVersion earlier version tail junk = wrapProtected (tapeFrames earlier tail junk) version := by
  induction earlier with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨prior,j⟩
    simp only [tapeAroundVersion]
    rw [ih]
    simp [tapeFrames,priorTapeFrames,wrapProtected,List.foldl_append]

#print axioms tape_around_is_protected_context

def GlobalStableStep (earlier : List (Term × Term)) (tail junk initial : Term)
    (desired : List Bool) (a b : Term) : Prop :=
  priorityConcretePath (tapeAroundVersion earlier a tail junk) =
    priorityConcretePath (tapeAroundVersion earlier initial tail junk) ∧
  cellFromVersion a = cellFromVersion initial ∧
  ∃ path focus relpath,
    chooseSVersionTree 11 desired a = some (physicalPath path) ∧
    termAt a (physicalPath path) = some focus ∧ nextOpeningAddress focus = some relpath ∧
    DirectedStep (contextPath (tapeFrames earlier tail junk) ++ (physicalPath path ++ relpath))
      (tapeAroundVersion earlier a tail junk) (tapeAroundVersion earlier b tail junk)

inductive GlobalStableTrace (earlier : List (Term × Term)) (tail junk initial : Term)
    (desired : List Bool) : Nat → Term → Term → Prop where
  | zero (a : Term) : GlobalStableTrace earlier tail junk initial desired 0 a a
  | next {n : Nat} {a b c : Term} : GlobalStableStep earlier tail junk initial desired a b →
      GlobalStableTrace earlier tail junk initial desired n b c →
      GlobalStableTrace earlier tail junk initial desired (n+1) a c

theorem stable_native_trace_preserves_global_scan (earlier : List (Term × Term))
    (tail junk initial : Term) (desired : List Bool) (old : Option (List Bool))
    (hinit : scanVersionTree 11 none initial = old) {n : Nat} {a b : Term}
    (trace : StableAdaptiveTrace 11 desired old n a b) :
    GlobalStableTrace earlier tail junk initial desired n a b := by
  induction trace with
  | zero x => exact GlobalStableTrace.zero x
  | @next n a b c hstep rest ih =>
    obtain ⟨⟨path,hchoose,focus,relpath,hat,hlocal,hdir⟩,hvalue⟩ := hstep
    have hcell : cellFromVersion a = cellFromVersion initial := by
      unfold cellFromVersion
      rw [hvalue,hinit]
    have hpriority := priority_ignores_equivalent_version earlier a initial tail junk hcell
    have hlift := directed_protected_context (tapeFrames earlier tail junk) hdir
    have hglobal : GlobalStableStep earlier tail junk initial desired a b := by
      refine ⟨hpriority,hcell,path,focus,relpath,hchoose,hat,hlocal,?_⟩
      simpa [← tape_around_is_protected_context] using hlift
    exact GlobalStableTrace.next hglobal ih

#print axioms stable_native_trace_preserves_global_scan

theorem global_stable_version_append (records : List UniversalCell) (entry : UniversalCell) (d : Nat)
    (earlier : List (Term × Term)) (tail junk : Term) :
    let entries := records.map encodedEntry
    let newEntry := encodedEntry entry
    let initial := layoutTerm (versionLayout entries) (phaseAt d).1 (phaseAt d).2
    let final := layoutTerm (versionLayout (entries ++ [newEntry])) (phaseAt d).1 (phaseAt d).2
    ∃ k, GlobalStableTrace earlier tail junk initial newEntry.val k initial final ∧
      6 ≤ k ∧ k ≤ 168 ∧ cellFromVersion final = entry.val := by
  let entries := records.map encodedEntry
  let newEntry := encodedEntry entry
  let initial := layoutTerm (versionLayout entries) (phaseAt d).1 (phaseAt d).2
  let final := layoutTerm (versionLayout (entries ++ [newEntry])) (phaseAt d).1 (phaseAt d).2
  obtain ⟨k,htrace,hlower,hupper,hfinal⟩ := fully_stable_fuel_free_version_append entries newEntry d
  have hp := phase_at_good d
  have hm : layoutMatches (versionLayout entries) initial :=
    finite_layout_decodes (versionLayout entries) (phaseAt d).1 (phaseAt d).2 hp.1 hp.2
  have hinit : scanVersionTree 11 none initial = newestRecords entries none :=
    scan_tree_committed_records entries initial none hm
  have hglobal := stable_native_trace_preserves_global_scan earlier tail junk initial newEntry.val
    (newestRecords entries none) hinit htrace
  refine ⟨k,hglobal,hlower,?_,?_⟩
  · omega
  · unfold cellFromVersion
    rw [hfinal]
    simp [newEntry,encoded_entry_roundtrip]

#print axioms global_stable_version_append

theorem directed_step_is_native {p : List Bool} {a b : Term} (h : DirectedStep p a b) : Step a b := by
  induction h with
  | root x y z => exact Step.root x y z
  | left _ ih => exact Step.left ih
  | right _ ih => exact Step.right ih

theorem global_stable_trace_is_exact (earlier : List (Term × Term)) (tail junk initial : Term)
    (desired : List Bool) {n : Nat} {a b : Term}
    (trace : GlobalStableTrace earlier tail junk initial desired n a b) :
    ExactSteps n (tapeAroundVersion earlier a tail junk) (tapeAroundVersion earlier b tail junk) := by
  induction trace with
  | zero x => exact ExactSteps.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨_,_,path,focus,rel,hchoose,hat,hlocal,hdir⟩ := hstep
    exact ExactSteps.next (directed_step_is_native hdir) ih

#print axioms directed_step_is_native
#print axioms global_stable_trace_is_exact

def concreteVersion (records : List UniversalCell) (d : Nat) : Term :=
  layoutTerm (versionLayout (records.map encodedEntry)) (phaseAt d).1 (phaseAt d).2

def adjacentTape (source destination tail sourceJunk destinationJunk : Term) : Term :=
  frameTerm source (frameTerm destination tail destinationJunk) sourceJunk

theorem three_adjacent_commits_native (source destination : List UniversalCell)
    (pending active off : UniversalCell) (sourceDepth destinationDepth : Nat)
    (tail sourceJunk destinationJunk : Term) :
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let d0 := concreteVersion destination destinationDepth
    let d1 := concreteVersion (destination ++ [active]) destinationDepth
    ∃ k1 k2 k3,
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (6 ≤ k2 ∧ k2 ≤ 168) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧
      ExactSteps k1 (adjacentTape s0 d0 tail sourceJunk destinationJunk)
        (adjacentTape s1 d0 tail sourceJunk destinationJunk) ∧
      ExactSteps k2 (adjacentTape s1 d0 tail sourceJunk destinationJunk)
        (adjacentTape s1 d1 tail sourceJunk destinationJunk) ∧
      ExactSteps k3 (adjacentTape s1 d1 tail sourceJunk destinationJunk)
        (adjacentTape s2 d1 tail sourceJunk destinationJunk) ∧
      cellFromVersion s1 = pending.val ∧ cellFromVersion d1 = active.val ∧ cellFromVersion s2 = off.val := by
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let d0 := concreteVersion destination destinationDepth
  let d1 := concreteVersion (destination ++ [active]) destinationDepth
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth [] (frameTerm d0 tail destinationJunk) sourceJunk
  obtain ⟨k2,t2,lo2,hi2,read2⟩ :=
    global_stable_version_append destination active destinationDepth [(s1,sourceJunk)] tail destinationJunk
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth [] (frameTerm d1 tail destinationJunk) sourceJunk
  have e1 : ExactSteps k1 (adjacentTape s0 d0 tail sourceJunk destinationJunk)
      (adjacentTape s1 d0 tail sourceJunk destinationJunk) := by
    simpa [adjacentTape,tapeAroundVersion,concreteVersion,s0,s1,d0,List.map_append] using
      global_stable_trace_is_exact [] (frameTerm d0 tail destinationJunk) sourceJunk s0 (encodedEntry pending).val t1
  have e2 : ExactSteps k2 (adjacentTape s1 d0 tail sourceJunk destinationJunk)
      (adjacentTape s1 d1 tail sourceJunk destinationJunk) := by
    simpa [adjacentTape,tapeAroundVersion,concreteVersion,s1,d0,d1,List.map_append] using
      global_stable_trace_is_exact [(s1,sourceJunk)] tail destinationJunk d0 (encodedEntry active).val t2
  have e3 : ExactSteps k3 (adjacentTape s1 d1 tail sourceJunk destinationJunk)
      (adjacentTape s2 d1 tail sourceJunk destinationJunk) := by
    simpa [adjacentTape,tapeAroundVersion,concreteVersion,s1,s2,d1,List.map_append,List.append_assoc] using
      global_stable_trace_is_exact [] (frameTerm d1 tail destinationJunk) sourceJunk s1 (encodedEntry off).val t3
  refine ⟨k1,k2,k3,⟨lo1,hi1⟩,⟨lo2,hi2⟩,⟨lo3,hi3⟩,e1,e2,e3,?_,?_,?_⟩
  · simpa [s1,concreteVersion,List.map_append] using read1
  · simpa [d1,concreteVersion,List.map_append] using read2
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3

#print axioms three_adjacent_commits_native

theorem concrete_version_decodes (records : List UniversalCell) (d : Nat) :
    cellFromVersion (concreteVersion records d) = decodedCell records := by
  unfold concreteVersion cellFromVersion decodedCell
  have hp := phase_at_good d
  have hm := finite_layout_decodes (versionLayout (records.map encodedEntry))
    (phaseAt d).1 (phaseAt d).2 hp.1 hp.2
  rw [scan_tree_universal_cells records _ hm]

#print axioms concrete_version_decodes

theorem adjacent_priority_initial (src dst tail js jd : Term)
    (hs : (cellFromVersion src).status = .active) (hd : (cellFromVersion dst).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (adjacentTape src dst tail js jd) = .active [] := by
  simp [priorityConcretePath,adjacentTape,seek_concrete_frame,movingCell,activeCell,isMoving,hs,hd,htail]

theorem adjacent_priority_pending (src dst tail js jd : Term)
    (hs : isMoving (cellFromVersion src).status = true) :
    priorityConcretePath (adjacentTape src dst tail js jd) = .pending [] := by
  simp [priorityConcretePath,adjacentTape,seek_concrete_frame,movingCell,hs]

theorem adjacent_priority_complete (src dst tail js jd : Term)
    (hs : (cellFromVersion src).status = .off) (hd : (cellFromVersion dst).status = .active)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (adjacentTape src dst tail js jd) = .active [true,false,true] := by
  simp [priorityConcretePath,adjacentTape,seek_concrete_frame,movingCell,activeCell,isMoving,hs,hd,htail]

#print axioms adjacent_priority_initial
#print axioms adjacent_priority_pending
#print axioms adjacent_priority_complete

def pendingRightCell (bit : Bool) (q : Fin 132) : UniversalCell := ⟨⟨bit,.movingRight,q.val⟩,q.isLt⟩
def activeCellRecord (bit : Bool) (q : Fin 132) : UniversalCell := ⟨⟨bit,.active,q.val⟩,q.isLt⟩
def offCellRecord (bit : Bool) : UniversalCell := ⟨⟨bit,.off,0⟩,Nat.zero_lt_succ 131⟩

theorem right_move_global_three_phase (source destination : List UniversalCell)
    (sourceDepth destinationDepth : Nat) (tail sourceJunk destinationJunk : Term)
    (written : Bool) (nextState : Fin 132)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let d0 := concreteVersion destination destinationDepth
    let d1 := concreteVersion (destination ++ [active]) destinationDepth
    ∃ k1 k2 k3,
      GlobalStableTrace [] (frameTerm d0 tail destinationJunk) sourceJunk s0 (encodedEntry pending).val k1 s0 s1 ∧
      GlobalStableTrace [(s1,sourceJunk)] tail destinationJunk d0 (encodedEntry active).val k2 d0 d1 ∧
      GlobalStableTrace [] (frameTerm d1 tail destinationJunk) sourceJunk s1 (encodedEntry off).val k3 s1 s2 ∧
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (6 ≤ k2 ∧ k2 ≤ 168) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧
      priorityConcretePath (adjacentTape s0 d0 tail sourceJunk destinationJunk) = .active [] ∧
      priorityConcretePath (adjacentTape s1 d0 tail sourceJunk destinationJunk) = .pending [] ∧
      priorityConcretePath (adjacentTape s1 d1 tail sourceJunk destinationJunk) = .pending [] ∧
      priorityConcretePath (adjacentTape s2 d1 tail sourceJunk destinationJunk) = .active [true,false,true] ∧
      cellFromVersion s2 = off.val ∧ cellFromVersion d1 = active.val := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
  let off := offCellRecord written
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let d0 := concreteVersion destination destinationDepth
  let d1 := concreteVersion (destination ++ [active]) destinationDepth
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth [] (frameTerm d0 tail destinationJunk) sourceJunk
  obtain ⟨k2,t2,lo2,hi2,read2⟩ :=
    global_stable_version_append destination active destinationDepth [(s1,sourceJunk)] tail destinationJunk
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth [] (frameTerm d1 tail destinationJunk) sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by
    simpa [s0,concrete_version_decodes] using hsource
  have hd0 : (cellFromVersion d0).status = .off := by
    simpa [d0,concrete_version_decodes] using hdestination
  have hs1 : isMoving (cellFromVersion s1).status = true := by
    rw [show cellFromVersion s1 = pending.val from by simpa [s1,concreteVersion,List.map_append] using read1]
    rfl
  have hd1 : (cellFromVersion d1).status = .active := by
    rw [show cellFromVersion d1 = active.val from by simpa [d1,concreteVersion,List.map_append] using read2]
    rfl
  have hs2 : (cellFromVersion s2).status = .off := by
    rw [show cellFromVersion s2 = off.val from by simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3]
    rfl
  refine ⟨k1,k2,k3,?_,?_,?_,⟨lo1,hi1⟩,⟨lo2,hi2⟩,⟨lo3,hi3⟩,?_,?_,?_,?_,?_,?_⟩
  · simpa [s0,s1,d0,concreteVersion,List.map_append] using t1
  · simpa [s1,d0,d1,concreteVersion,List.map_append] using t2
  · simpa [s1,s2,d1,concreteVersion,List.map_append,List.append_assoc] using t3
  · exact adjacent_priority_initial s0 d0 tail sourceJunk destinationJunk hs0 hd0 htail
  · exact adjacent_priority_pending s1 d0 tail sourceJunk destinationJunk hs1
  · exact adjacent_priority_pending s1 d1 tail sourceJunk destinationJunk hs1
  · exact adjacent_priority_complete s2 d1 tail sourceJunk destinationJunk hs2 hd1 htail
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3
  · simpa [d1,concreteVersion,List.map_append] using read2

#print axioms right_move_global_three_phase

theorem left_adjacent_priority_initial (dst src tail jd js : Term)
    (hd : (cellFromVersion dst).status = .off) (hs : (cellFromVersion src).status = .active)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (adjacentTape dst src tail jd js) = .active [true,false,true] := by
  simp [priorityConcretePath,adjacentTape,seek_concrete_frame,movingCell,activeCell,isMoving,hs,hd,htail]

theorem left_adjacent_priority_pending (dst src tail jd js : Term)
    (hd : isMoving (cellFromVersion dst).status = false)
    (hs : isMoving (cellFromVersion src).status = true) :
    priorityConcretePath (adjacentTape dst src tail jd js) = .pending [true,false,true] := by
  simp [priorityConcretePath,adjacentTape,seek_concrete_frame,movingCell,hs,hd]

theorem left_adjacent_priority_complete (dst src tail jd js : Term)
    (hd : (cellFromVersion dst).status = .active) (hs : (cellFromVersion src).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (adjacentTape dst src tail jd js) = .active [] := by
  simp [priorityConcretePath,adjacentTape,seek_concrete_frame,movingCell,activeCell,isMoving,hs,hd,htail]

#print axioms left_adjacent_priority_initial
#print axioms left_adjacent_priority_pending
#print axioms left_adjacent_priority_complete

def pendingLeftCell (bit : Bool) (q : Fin 132) : UniversalCell := ⟨⟨bit,.movingLeft,q.val⟩,q.isLt⟩

theorem left_move_global_three_phase (source destination : List UniversalCell)
    (sourceDepth destinationDepth : Nat) (tail sourceJunk destinationJunk : Term)
    (written : Bool) (nextState : Fin 132)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    let pending := pendingLeftCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let d0 := concreteVersion destination destinationDepth
    let d1 := concreteVersion (destination ++ [active]) destinationDepth
    ∃ k1 k2 k3,
      GlobalStableTrace [(d0,destinationJunk)] tail sourceJunk s0 (encodedEntry pending).val k1 s0 s1 ∧
      GlobalStableTrace [] (frameTerm s1 tail sourceJunk) destinationJunk d0 (encodedEntry active).val k2 d0 d1 ∧
      GlobalStableTrace [(d1,destinationJunk)] tail sourceJunk s1 (encodedEntry off).val k3 s1 s2 ∧
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (6 ≤ k2 ∧ k2 ≤ 168) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧
      priorityConcretePath (adjacentTape d0 s0 tail destinationJunk sourceJunk) = .active [true,false,true] ∧
      priorityConcretePath (adjacentTape d0 s1 tail destinationJunk sourceJunk) = .pending [true,false,true] ∧
      priorityConcretePath (adjacentTape d1 s1 tail destinationJunk sourceJunk) = .pending [true,false,true] ∧
      priorityConcretePath (adjacentTape d1 s2 tail destinationJunk sourceJunk) = .active [] ∧
      cellFromVersion s2 = off.val ∧ cellFromVersion d1 = active.val := by
  let pending := pendingLeftCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
  let off := offCellRecord written
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let d0 := concreteVersion destination destinationDepth
  let d1 := concreteVersion (destination ++ [active]) destinationDepth
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth [(d0,destinationJunk)] tail sourceJunk
  obtain ⟨k2,t2,lo2,hi2,read2⟩ :=
    global_stable_version_append destination active destinationDepth [] (frameTerm s1 tail sourceJunk) destinationJunk
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth [(d1,destinationJunk)] tail sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by
    simpa [s0,concrete_version_decodes] using hsource
  have hd0 : (cellFromVersion d0).status = .off := by
    simpa [d0,concrete_version_decodes] using hdestination
  have hs1 : isMoving (cellFromVersion s1).status = true := by
    rw [show cellFromVersion s1 = pending.val from by simpa [s1,concreteVersion,List.map_append] using read1]
    rfl
  have hd0m : isMoving (cellFromVersion d0).status = false := by simp [hd0,isMoving]
  have hd1 : (cellFromVersion d1).status = .active := by
    rw [show cellFromVersion d1 = active.val from by simpa [d1,concreteVersion,List.map_append] using read2]
    rfl
  have hd1m : isMoving (cellFromVersion d1).status = false := by simp [hd1,isMoving]
  have hs2 : (cellFromVersion s2).status = .off := by
    rw [show cellFromVersion s2 = off.val from by simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3]
    rfl
  refine ⟨k1,k2,k3,?_,?_,?_,⟨lo1,hi1⟩,⟨lo2,hi2⟩,⟨lo3,hi3⟩,?_,?_,?_,?_,?_,?_⟩
  · simpa [s0,s1,d0,concreteVersion,List.map_append] using t1
  · simpa [s1,d0,d1,concreteVersion,List.map_append] using t2
  · simpa [s1,s2,d1,concreteVersion,List.map_append,List.append_assoc] using t3
  · exact left_adjacent_priority_initial d0 s0 tail destinationJunk sourceJunk hd0 hs0 htail
  · exact left_adjacent_priority_pending d0 s1 tail destinationJunk sourceJunk hd0m hs1
  · exact left_adjacent_priority_pending d1 s1 tail destinationJunk sourceJunk hd1m hs1
  · exact left_adjacent_priority_complete d1 s2 tail destinationJunk sourceJunk hd1 hs2 htail
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3
  · simpa [d1,concreteVersion,List.map_append] using read2

#print axioms left_move_global_three_phase

def prependTape : List (Term × Term) → Term → Term
  | [], tail => tail
  | (version,junk) :: rest, tail => frameTerm version (prependTape rest tail) junk

def prefixPath (earlier : List (Term × Term)) : List Bool :=
  physicalPath (List.replicate earlier.length true)

def appendPathChoice (prefixPath : List Bool) : PathChoice → PathChoice
  | .pending p => .pending (prefixPath ++ p)
  | .active p => .active (prefixPath ++ p)
  | .none => .none

theorem seek_skips_nonmatching_prefix (earlier : List (Term × Term)) (pred : Cell → Bool)
    (tail : Term) (h : ∀ x ∈ earlier, pred (cellFromVersion x.1) = false) :
    seekConcreteCell pred (prependTape earlier tail) =
      (seekConcreteCell pred tail).map (fun p => prefixPath earlier ++ p) := by
  induction earlier with
  | nil => simp [prependTape,prefixPath,physicalPath]
  | cons pair rest ih =>
    rcases pair with ⟨version,junk⟩
    have hfirst : pred (cellFromVersion version) = false := h (version,junk) (by simp)
    have hrest : ∀ x ∈ rest, pred (cellFromVersion x.1) = false := by
      intro x hx
      exact h x (by simp [hx])
    simp [prependTape,seek_concrete_frame,hfirst,ih hrest,prefixPath,List.replicate_succ,
      physicalPath,Option.map_map,Function.comp_def]

theorem priority_skips_off_prefix (earlier : List (Term × Term)) (tail : Term)
    (h : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off) :
    priorityConcretePath (prependTape earlier tail) = appendPathChoice (prefixPath earlier) (priorityConcretePath tail) := by
  have hm : ∀ x ∈ earlier, movingCell (cellFromVersion x.1) = false := by
    intro x hx
    simp [movingCell,isMoving,h x hx]
  have ha : ∀ x ∈ earlier, activeCell (cellFromVersion x.1) = false := by
    intro x hx
    simp [activeCell,h x hx]
  unfold priorityConcretePath
  rw [seek_skips_nonmatching_prefix earlier movingCell tail hm,seek_skips_nonmatching_prefix earlier activeCell tail ha]
  cases hmove : seekConcreteCell movingCell tail <;> cases hactive : seekConcreteCell activeCell tail <;>
    simp [appendPathChoice]

theorem prepend_tape_around (earlier other : List (Term × Term)) (version tail junk : Term) :
    tapeAroundVersion (earlier ++ other) version tail junk =
      prependTape earlier (tapeAroundVersion other version tail junk) := by
  induction earlier with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨version0,j⟩
    simp [tapeAroundVersion,prependTape,ih]

#print axioms seek_skips_nonmatching_prefix
#print axioms priority_skips_off_prefix
#print axioms prepend_tape_around

theorem prefixed_adjacent_priority_initial (earlier : List (Term × Term)) (src dst tail js jd : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hs : (cellFromVersion src).status = .active) (hd : (cellFromVersion dst).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (prependTape earlier (adjacentTape src dst tail js jd)) = .active (prefixPath earlier) := by
  rw [priority_skips_off_prefix earlier _ hprefix,adjacent_priority_initial src dst tail js jd hs hd htail]
  simp [appendPathChoice]

theorem prefixed_adjacent_priority_pending (earlier : List (Term × Term)) (src dst tail js jd : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hs : isMoving (cellFromVersion src).status = true) :
    priorityConcretePath (prependTape earlier (adjacentTape src dst tail js jd)) = .pending (prefixPath earlier) := by
  rw [priority_skips_off_prefix earlier _ hprefix,adjacent_priority_pending src dst tail js jd hs]
  simp [appendPathChoice]

theorem prefixed_adjacent_priority_complete (earlier : List (Term × Term)) (src dst tail js jd : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hs : (cellFromVersion src).status = .off) (hd : (cellFromVersion dst).status = .active)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (prependTape earlier (adjacentTape src dst tail js jd)) =
      .active (prefixPath earlier ++ [true,false,true]) := by
  rw [priority_skips_off_prefix earlier _ hprefix,adjacent_priority_complete src dst tail js jd hs hd htail]
  rfl

#print axioms prefixed_adjacent_priority_initial
#print axioms prefixed_adjacent_priority_pending
#print axioms prefixed_adjacent_priority_complete

theorem right_move_with_off_prefix (source destination : List UniversalCell)
    (sourceDepth destinationDepth : Nat) (tail sourceJunk destinationJunk : Term)
    (earlier : List (Term × Term))
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (written : Bool) (nextState : Fin 132)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let d0 := concreteVersion destination destinationDepth
    let d1 := concreteVersion (destination ++ [active]) destinationDepth
    ∃ k1 k2 k3,
      GlobalStableTrace earlier (frameTerm d0 tail destinationJunk) sourceJunk s0 (encodedEntry pending).val k1 s0 s1 ∧
      GlobalStableTrace (earlier ++ [(s1,sourceJunk)]) tail destinationJunk d0 (encodedEntry active).val k2 d0 d1 ∧
      GlobalStableTrace earlier (frameTerm d1 tail destinationJunk) sourceJunk s1 (encodedEntry off).val k3 s1 s2 ∧
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (6 ≤ k2 ∧ k2 ≤ 168) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s0 d0 tail sourceJunk destinationJunk)) = .active (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s1 d0 tail sourceJunk destinationJunk)) = .pending (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s1 d1 tail sourceJunk destinationJunk)) = .pending (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s2 d1 tail sourceJunk destinationJunk)) = .active (prefixPath earlier ++ [true,false,true]) ∧
      cellFromVersion s2 = off.val ∧ cellFromVersion d1 = active.val := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
  let off := offCellRecord written
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let d0 := concreteVersion destination destinationDepth
  let d1 := concreteVersion (destination ++ [active]) destinationDepth
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth earlier (frameTerm d0 tail destinationJunk) sourceJunk
  obtain ⟨k2,t2,lo2,hi2,read2⟩ :=
    global_stable_version_append destination active destinationDepth (earlier ++ [(s1,sourceJunk)]) tail destinationJunk
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth earlier (frameTerm d1 tail destinationJunk) sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by
    simpa [s0,concrete_version_decodes] using hsource
  have hd0 : (cellFromVersion d0).status = .off := by
    simpa [d0,concrete_version_decodes] using hdestination
  have hs1 : isMoving (cellFromVersion s1).status = true := by
    rw [show cellFromVersion s1 = pending.val from by simpa [s1,concreteVersion,List.map_append] using read1]
    rfl
  have hd1 : (cellFromVersion d1).status = .active := by
    rw [show cellFromVersion d1 = active.val from by simpa [d1,concreteVersion,List.map_append] using read2]
    rfl
  have hs2 : (cellFromVersion s2).status = .off := by
    rw [show cellFromVersion s2 = off.val from by simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3]
    rfl
  refine ⟨k1,k2,k3,?_,?_,?_,⟨lo1,hi1⟩,⟨lo2,hi2⟩,⟨lo3,hi3⟩,?_,?_,?_,?_,?_,?_⟩
  · simpa [s0,s1,d0,concreteVersion,List.map_append] using t1
  · simpa [s1,d0,d1,concreteVersion,List.map_append] using t2
  · simpa [s1,s2,d1,concreteVersion,List.map_append,List.append_assoc] using t3
  · exact prefixed_adjacent_priority_initial earlier s0 d0 tail sourceJunk destinationJunk hprefix hs0 hd0 htail
  · exact prefixed_adjacent_priority_pending earlier s1 d0 tail sourceJunk destinationJunk hprefix hs1
  · exact prefixed_adjacent_priority_pending earlier s1 d1 tail sourceJunk destinationJunk hprefix hs1
  · exact prefixed_adjacent_priority_complete earlier s2 d1 tail sourceJunk destinationJunk hprefix hs2 hd1 htail
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3
  · simpa [d1,concreteVersion,List.map_append] using read2


#print axioms right_move_with_off_prefix

theorem prefixed_left_priority_initial (earlier : List (Term × Term)) (dst src tail jd js : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hd : (cellFromVersion dst).status = .off) (hs : (cellFromVersion src).status = .active)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (prependTape earlier (adjacentTape dst src tail jd js)) =
      .active (prefixPath earlier ++ [true,false,true]) := by
  rw [priority_skips_off_prefix earlier _ hprefix,left_adjacent_priority_initial dst src tail jd js hd hs htail]
  rfl

theorem prefixed_left_priority_pending (earlier : List (Term × Term)) (dst src tail jd js : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hd : isMoving (cellFromVersion dst).status = false) (hs : isMoving (cellFromVersion src).status = true) :
    priorityConcretePath (prependTape earlier (adjacentTape dst src tail jd js)) =
      .pending (prefixPath earlier ++ [true,false,true]) := by
  rw [priority_skips_off_prefix earlier _ hprefix,left_adjacent_priority_pending dst src tail jd js hd hs]
  rfl

theorem prefixed_left_priority_complete (earlier : List (Term × Term)) (dst src tail jd js : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hd : (cellFromVersion dst).status = .active) (hs : (cellFromVersion src).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (prependTape earlier (adjacentTape dst src tail jd js)) = .active (prefixPath earlier) := by
  rw [priority_skips_off_prefix earlier _ hprefix,left_adjacent_priority_complete dst src tail jd js hd hs htail]
  simp [appendPathChoice]

#print axioms prefixed_left_priority_initial
#print axioms prefixed_left_priority_pending
#print axioms prefixed_left_priority_complete

theorem left_move_with_off_prefix (source destination : List UniversalCell)
    (sourceDepth destinationDepth : Nat) (tail sourceJunk destinationJunk : Term)
    (earlier : List (Term × Term))
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (written : Bool) (nextState : Fin 132)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    let pending := pendingLeftCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let d0 := concreteVersion destination destinationDepth
    let d1 := concreteVersion (destination ++ [active]) destinationDepth
    ∃ k1 k2 k3,
      GlobalStableTrace (earlier ++ [(d0,destinationJunk)]) tail sourceJunk s0 (encodedEntry pending).val k1 s0 s1 ∧
      GlobalStableTrace earlier (frameTerm s1 tail sourceJunk) destinationJunk d0 (encodedEntry active).val k2 d0 d1 ∧
      GlobalStableTrace (earlier ++ [(d1,destinationJunk)]) tail sourceJunk s1 (encodedEntry off).val k3 s1 s2 ∧
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (6 ≤ k2 ∧ k2 ≤ 168) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧
      priorityConcretePath (prependTape earlier (adjacentTape d0 s0 tail destinationJunk sourceJunk)) = .active (prefixPath earlier ++ [true,false,true]) ∧
      priorityConcretePath (prependTape earlier (adjacentTape d0 s1 tail destinationJunk sourceJunk)) = .pending (prefixPath earlier ++ [true,false,true]) ∧
      priorityConcretePath (prependTape earlier (adjacentTape d1 s1 tail destinationJunk sourceJunk)) = .pending (prefixPath earlier ++ [true,false,true]) ∧
      priorityConcretePath (prependTape earlier (adjacentTape d1 s2 tail destinationJunk sourceJunk)) = .active (prefixPath earlier) ∧
      cellFromVersion s2 = off.val ∧ cellFromVersion d1 = active.val := by
  let pending := pendingLeftCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
  let off := offCellRecord written
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let d0 := concreteVersion destination destinationDepth
  let d1 := concreteVersion (destination ++ [active]) destinationDepth
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth (earlier ++ [(d0,destinationJunk)]) tail sourceJunk
  obtain ⟨k2,t2,lo2,hi2,read2⟩ :=
    global_stable_version_append destination active destinationDepth earlier (frameTerm s1 tail sourceJunk) destinationJunk
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth (earlier ++ [(d1,destinationJunk)]) tail sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by
    simpa [s0,concrete_version_decodes] using hsource
  have hd0 : (cellFromVersion d0).status = .off := by
    simpa [d0,concrete_version_decodes] using hdestination
  have hs1 : isMoving (cellFromVersion s1).status = true := by
    rw [show cellFromVersion s1 = pending.val from by simpa [s1,concreteVersion,List.map_append] using read1]
    rfl
  have hd0m : isMoving (cellFromVersion d0).status = false := by simp [hd0,isMoving]
  have hd1 : (cellFromVersion d1).status = .active := by
    rw [show cellFromVersion d1 = active.val from by simpa [d1,concreteVersion,List.map_append] using read2]
    rfl
  have hd1m : isMoving (cellFromVersion d1).status = false := by simp [hd1,isMoving]
  have hs2 : (cellFromVersion s2).status = .off := by
    rw [show cellFromVersion s2 = off.val from by simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3]
    rfl
  refine ⟨k1,k2,k3,?_,?_,?_,⟨lo1,hi1⟩,⟨lo2,hi2⟩,⟨lo3,hi3⟩,?_,?_,?_,?_,?_,?_⟩
  · simpa [s0,s1,d0,concreteVersion,List.map_append] using t1
  · simpa [s1,d0,d1,concreteVersion,List.map_append] using t2
  · simpa [s1,s2,d1,concreteVersion,List.map_append,List.append_assoc] using t3
  · exact prefixed_left_priority_initial earlier d0 s0 tail destinationJunk sourceJunk hprefix hd0 hs0 htail
  · exact prefixed_left_priority_pending earlier d0 s1 tail destinationJunk sourceJunk hprefix hd0m hs1
  · exact prefixed_left_priority_pending earlier d1 s1 tail destinationJunk sourceJunk hprefix hd1m hs1
  · exact prefixed_left_priority_complete earlier d1 s2 tail destinationJunk sourceJunk hprefix hd1 hs2 htail
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3
  · simpa [d1,concreteVersion,List.map_append] using read2


#print axioms left_move_with_off_prefix

theorem single_active_priority (version tail junk : Term)
    (hactive : (cellFromVersion version).status = .active)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (frameTerm version tail junk) = .active [] := by
  simp [priorityConcretePath,seek_concrete_frame,movingCell,activeCell,isMoving,hactive,htail]

theorem prefixed_single_active_priority (earlier : List (Term × Term)) (version tail junk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hactive : (cellFromVersion version).status = .active)
    (htail : seekConcreteCell movingCell tail = none) :
    priorityConcretePath (prependTape earlier (frameTerm version tail junk)) = .active (prefixPath earlier) := by
  rw [priority_skips_off_prefix earlier _ hprefix,single_active_priority version tail junk hactive htail]
  simp [appendPathChoice]

theorem stay_global_one_phase (source : List UniversalCell) (sourceDepth : Nat)
    (earlier : List (Term × Term)) (tail sourceJunk : Term)
    (written : Bool) (nextState : Fin 132)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hsource : (decodedCell source).status = .active)
    (htail : seekConcreteCell movingCell tail = none) :
    let active := activeCellRecord written nextState
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [active]) sourceDepth
    ∃ k, GlobalStableTrace earlier tail sourceJunk s0 (encodedEntry active).val k s0 s1 ∧
      6 ≤ k ∧ k ≤ 168 ∧
      priorityConcretePath (prependTape earlier (frameTerm s0 tail sourceJunk)) = .active (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (frameTerm s1 tail sourceJunk)) = .active (prefixPath earlier) ∧
      cellFromVersion s1 = active.val := by
  let active := activeCellRecord written nextState
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [active]) sourceDepth
  obtain ⟨k,trace,hlower,hupper,hread⟩ :=
    global_stable_version_append source active sourceDepth earlier tail sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by
    simpa [s0,concrete_version_decodes] using hsource
  have hs1 : (cellFromVersion s1).status = .active := by
    rw [show cellFromVersion s1 = active.val from by simpa [s1,concreteVersion,List.map_append] using hread]
    rfl
  refine ⟨k,?_,hlower,hupper,?_,?_,?_⟩
  · simpa [s0,s1,concreteVersion,List.map_append] using trace
  · exact prefixed_single_active_priority earlier s0 tail sourceJunk hprefix hs0 htail
  · exact prefixed_single_active_priority earlier s1 tail sourceJunk hprefix hs1 htail
  · simpa [s1,concreteVersion,List.map_append] using hread

#print axioms single_active_priority
#print axioms stay_global_one_phase

def tailFrames (earlier : List (Term × Term)) (version junk : Term) : List ProtectedFrame :=
  [.right version junk] ++ priorTapeFrames earlier

theorem tail_context_representation (earlier : List (Term × Term)) (version tail junk : Term) :
    prependTape earlier (frameTerm version tail junk) = wrapProtected (tailFrames earlier version junk) tail := by
  induction earlier with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨prior,j⟩
    simp only [prependTape]
    rw [ih]
    simp [tailFrames,priorTapeFrames,wrapProtected,List.foldl_append]

theorem single_pending_priority (version tail junk : Term)
    (hpending : isMoving (cellFromVersion version).status = true) :
    priorityConcretePath (frameTerm version tail junk) = .pending [] := by
  simp [priorityConcretePath,seek_concrete_frame,movingCell,hpending]

theorem prefixed_single_pending_priority (earlier : List (Term × Term)) (version tail junk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hpending : isMoving (cellFromVersion version).status = true) :
    priorityConcretePath (prependTape earlier (frameTerm version tail junk)) = .pending (prefixPath earlier) := by
  rw [priority_skips_off_prefix earlier _ hprefix,single_pending_priority version tail junk hpending]
  simp [appendPathChoice]

#print axioms tail_context_representation
#print axioms prefixed_single_pending_priority

inductive PendingTailTrace (earlier : List (Term × Term)) (version junk : Term) : Nat → Term → Term → Prop where
  | zero (a : Term) : PendingTailTrace earlier version junk 0 a a
  | next {n : Nat} {a b c : Term} :
      priorityConcretePath (prependTape earlier (frameTerm version a junk)) = .pending (prefixPath earlier) →
      FocusedStep (tailFrames earlier version junk) a b →
      PendingTailTrace earlier version junk n b c → PendingTailTrace earlier version junk (n+1) a c

theorem focused_tail_keeps_pending (earlier : List (Term × Term)) (version junk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hpending : isMoving (cellFromVersion version).status = true)
    {n : Nat} {a b : Term} (h : FocusedSteps (tailFrames earlier version junk) n a b) :
    PendingTailTrace earlier version junk n a b := by
  induction h with
  | zero x => exact PendingTailTrace.zero x
  | @next n a b c hab rest ih =>
    exact PendingTailTrace.next (prefixed_single_pending_priority earlier version a junk hprefix hpending) hab ih

theorem pending_tail_positive_open (earlier : List (Term × Term)) (version junk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hpending : isMoving (cellFromVersion version).status = true) (m n : Nat) :
    PendingTailTrace earlier version junk 6 (generator (m+1) (n+2))
      (frameTerm (generator m (n+2)) (generator m (n+2))
        ((numeral n ⋅ S) ⋅ generator m (n+2))) :=
  focused_tail_keeps_pending earlier version junk hprefix hpending
    (positive_opening_selected_in_context (tailFrames earlier version junk) m n)

theorem pending_tail_zero_open (earlier : List (Term × Term)) (version junk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hpending : isMoving (cellFromVersion version).status = true) (n : Nat) :
    PendingTailTrace earlier version junk 7 (generator 0 (n+2))
      (frameTerm (generator (n+2) (n+3)) (generator (n+2) (n+3))
        ((numeral (n+1) ⋅ S) ⋅ generator (n+2) (n+3))) :=
  focused_tail_keeps_pending earlier version junk hprefix hpending
    (zero_opening_selected_in_context (tailFrames earlier version junk) n)

#print axioms focused_tail_keeps_pending
#print axioms pending_tail_positive_open
#print axioms pending_tail_zero_open

theorem unopened_version_decodes_blank (m n : Nat) : cellFromVersion (generator m n) = defaultCell := by
  unfold cellFromVersion
  rw [scan_version_tree_closed 11 none (generator m n) (parse_generator_closed m n)]
  rfl

theorem unopened_tail_has_no_pending (m n : Nat) : seekConcreteCell movingCell (generator m n) = none :=
  seek_concrete_closed movingCell (generator m n) (parse_generator_closed m n)

#print axioms unopened_version_decodes_blank
#print axioms unopened_tail_has_no_pending

theorem closed_opening_trace_is_chosen {n : Nat} {a b : Term} (h : ClosedOpeningTrace n a b) :
    ChosenSteps n a b := by
  induction h with
  | finish hs _ => exact ChosenSteps.next hs (ChosenSteps.zero _)
  | more hs _ _ ih => exact ChosenSteps.next hs ih

theorem pending_tail_opens_at_depth (earlier : List (Term × Term)) (version junk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hpending : isMoving (cellFromVersion version).status = true) (d : Nat) :
    ∃ k, (k=6 ∨ k=7) ∧ PendingTailTrace earlier version junk k (depthBase d)
      (layoutTerm (.opened .unopened .unopened) (phaseAt d).1 (phaseAt d).2) := by
  obtain ⟨k,hk,htrace⟩ := good_phase_opening_trace (phaseAt d) (phase_at_good d)
  have hchosen := closed_opening_trace_is_chosen htrace
  have hfocused := chosen_steps_in_protected_context (tailFrames earlier version junk) hchosen
  exact ⟨k,hk,focused_tail_keeps_pending earlier version junk hprefix hpending hfocused⟩

theorem depth_child_is_blank (d : Nat) : cellFromVersion (depthBase d) = defaultCell := by
  exact unopened_version_decodes_blank (phaseAt d).1 (phaseAt d).2

theorem depth_child_has_no_pending (d : Nat) : seekConcreteCell movingCell (depthBase d) = none := by
  exact unopened_tail_has_no_pending (phaseAt d).1 (phaseAt d).2

theorem opened_empty_cell_shape (d : Nat) :
    layoutTerm (.opened .unopened .unopened) (phaseAt d).1 (phaseAt d).2 =
      frameTerm (depthBase (d+1)) (depthBase (d+1)) (depthJunk d) := by
  simpa [depthBase,depthJunk,phaseBase,phaseAt,layoutTerm] using
    layout_opened_phase .unopened .unopened (phaseAt d) (phase_at_good d)

#print axioms pending_tail_opens_at_depth
#print axioms depth_child_is_blank
#print axioms depth_child_has_no_pending
#print axioms opened_empty_cell_shape

theorem empty_concrete_version (d : Nat) : concreteVersion [] d = depthBase d := by rfl

theorem right_move_extends_tape (source : List UniversalCell) (sourceDepth tailDepth : Nat)
    (earlier : List (Term × Term)) (sourceJunk : Term) (written : Bool) (nextState : Fin 132)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hsource : (decodedCell source).status = .active) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord false nextState
    let off := offCellRecord written
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let blank := depthBase (tailDepth+1)
    let d1 := concreteVersion [active] (tailDepth+1)
    let cell0 := frameTerm blank blank (depthJunk tailDepth)
    let cell1 := frameTerm d1 blank (depthJunk tailDepth)
    ∃ k1 k2 k3 k4,
      GlobalStableTrace earlier (depthBase tailDepth) sourceJunk s0 (encodedEntry pending).val k1 s0 s1 ∧
      PendingTailTrace earlier s1 sourceJunk k2 (depthBase tailDepth) cell0 ∧
      GlobalStableTrace (earlier ++ [(s1,sourceJunk)]) blank (depthJunk tailDepth) blank (encodedEntry active).val k3 blank d1 ∧
      GlobalStableTrace earlier cell1 sourceJunk s1 (encodedEntry off).val k4 s1 s2 ∧
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (k2=6 ∨ k2=7) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧ (6 ≤ k4 ∧ k4 ≤ 168) ∧
      priorityConcretePath (prependTape earlier (frameTerm s0 (depthBase tailDepth) sourceJunk)) = .active (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s2 d1 blank sourceJunk (depthJunk tailDepth))) =
        .active (prefixPath earlier ++ [true,false,true]) ∧
      cellFromVersion s2 = off.val ∧ cellFromVersion d1 = active.val := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord false nextState
  let off := offCellRecord written
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let blank := depthBase (tailDepth+1)
  let d1 := concreteVersion [active] (tailDepth+1)
  let cell0 := frameTerm blank blank (depthJunk tailDepth)
  let cell1 := frameTerm d1 blank (depthJunk tailDepth)
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth earlier (depthBase tailDepth) sourceJunk
  have hs1 : isMoving (cellFromVersion s1).status = true := by
    rw [show cellFromVersion s1 = pending.val from by simpa [s1,concreteVersion,List.map_append] using read1]
    rfl
  obtain ⟨k2,hk2,t2⟩ := pending_tail_opens_at_depth earlier s1 sourceJunk hprefix hs1 tailDepth
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append [] active (tailDepth+1) (earlier ++ [(s1,sourceJunk)]) blank (depthJunk tailDepth)
  obtain ⟨k4,t4,lo4,hi4,read4⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth earlier cell1 sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by simpa [s0,concrete_version_decodes] using hsource
  have hs2 : (cellFromVersion s2).status = .off := by
    rw [show cellFromVersion s2 = off.val from by simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read4]
    rfl
  have hd1 : (cellFromVersion d1).status = .active := by
    rw [show cellFromVersion d1 = active.val from by simpa [d1,concreteVersion,List.map_append] using read3]
    rfl
  refine ⟨k1,k2,k3,k4,?_,?_,?_,?_,⟨lo1,hi1⟩,hk2,⟨lo3,hi3⟩,⟨lo4,hi4⟩,?_,?_,?_,?_⟩
  · simpa [s0,s1,concreteVersion,List.map_append] using t1
  · simpa [cell0,blank,opened_empty_cell_shape] using t2
  · simpa [blank,d1,s1,concreteVersion,depthBase,phaseBase,versionLayout,layoutTerm,List.map_append] using t3
  · simpa [s1,s2,cell1,d1,blank,concreteVersion,List.map_append,List.append_assoc] using t4
  · exact prefixed_single_active_priority earlier s0 (depthBase tailDepth) sourceJunk hprefix hs0
      (depth_child_has_no_pending tailDepth)
  · exact prefixed_adjacent_priority_complete earlier s2 d1 blank sourceJunk (depthJunk tailDepth)
      hprefix hs2 hd1 (depth_child_has_no_pending (tailDepth+1))
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read4
  · simpa [d1,concreteVersion,List.map_append] using read3

#print axioms right_move_extends_tape

theorem halt_field_closed_observation (flag tape junk : Term) (hclosed : parseFrame flag = none) :
    haltObserved (frameTerm flag tape junk) = false := by
  simp [haltObserved,parse_frame,flagValue,hclosed]

theorem halt_field_open_observation (flag tape junk : Term)
    (hopen : layoutMatches (.opened .unopened .unopened) flag) :
    haltObserved (frameTerm flag tape junk) = true := by
  have hv := matched_layout_flag (.opened .unopened .unopened) flag hopen
  simp [haltObserved,parse_frame,hv,layoutIsOpen]

inductive HaltOpeningTrace (tape junk : Term) (choice : PathChoice) : Nat → Term → Term → Prop where
  | zero (a : Term) : HaltOpeningTrace tape junk choice 0 a a
  | next {n : Nat} {a b c : Term} :
      haltObserved (frameTerm a tape junk) = false → priorityConcretePath tape = choice →
      FocusedStep [.left tape junk] a b → HaltOpeningTrace tape junk choice n b c →
      HaltOpeningTrace tape junk choice (n+1) a c

theorem lift_halt_opening {n : Nat} {a b : Term} (trace : ClosedOpeningTrace n a b)
    (tape junk : Term) (choice : PathChoice) (hpriority : priorityConcretePath tape = choice)
    (hclosed : parseFrame a = none) : HaltOpeningTrace tape junk choice n a b := by
  induction trace with
  | @finish a b hstep hopen =>
    exact HaltOpeningTrace.next (halt_field_closed_observation a tape junk hclosed) hpriority
      (selected_step_in_protected_context [.left tape junk] hstep) (HaltOpeningTrace.zero b)
  | @more n a b c hstep hnext rest ih =>
    exact HaltOpeningTrace.next (halt_field_closed_observation a tape junk hclosed) hpriority
      (selected_step_in_protected_context [.left tape junk] hstep) (ih hnext)

theorem halt_field_can_open (flagDepth : Nat) (tape junk : Term) (choice : PathChoice)
    (hpriority : priorityConcretePath tape = choice) :
    ∃ k, (k=6 ∨ k=7) ∧
      HaltOpeningTrace tape junk choice k (depthBase flagDepth)
        (layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2) ∧
      haltObserved (frameTerm
        (layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2) tape junk) = true := by
  obtain ⟨k,hk,htrace⟩ := good_phase_opening_trace (phaseAt flagDepth) (phase_at_good flagDepth)
  have hclosed := depth_base_closed flagDepth
  have hdone := finite_layout_decodes (.opened .unopened .unopened)
    (phaseAt flagDepth).1 (phaseAt flagDepth).2 (phase_at_good flagDepth).1 (phase_at_good flagDepth).2
  exact ⟨k,hk,lift_halt_opening htrace tape junk choice hpriority hclosed,
    halt_field_open_observation _ tape junk hdone⟩

#print axioms halt_field_closed_observation
#print axioms lift_halt_opening
#print axioms halt_field_can_open

def seedHubRoot (flag tape hubJunk : Term) : Term :=
  (numeral 1 ⋅ S) ⋅ frameTerm flag tape hubJunk

theorem tape_step_under_seed_hub {p : List Bool} {a b : Term}
    (h : DirectedStep p a b) (flag hubJunk : Term) :
    DirectedStep ([true,true,false,true] ++ p) (seedHubRoot flag a hubJunk) (seedHubRoot flag b hubJunk) := by
  exact DirectedStep.right (DirectedStep.right (DirectedStep.left (DirectedStep.right h)))

theorem closed_flag_stays_closed_under_seed_hub (flag tape hubJunk : Term)
    (hflag : parseFrame flag = none) :
    haltObserved (frameTerm flag tape hubJunk) = false :=
  halt_field_closed_observation flag tape hubJunk hflag

def HubStableStep (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term)
    (desired : List Bool) (a b : Term) : Prop :=
  priorityConcretePath (tapeAroundVersion earlier a tail junk) =
    priorityConcretePath (tapeAroundVersion earlier initial tail junk) ∧
  cellFromVersion a = cellFromVersion initial ∧
  ∃ path focus relpath,
    chooseSVersionTree 11 desired a = some (physicalPath path) ∧
    termAt a (physicalPath path) = some focus ∧ nextOpeningAddress focus = some relpath ∧
    DirectedStep ([true,true,false,true] ++ contextPath (tapeFrames earlier tail junk) ++
      (physicalPath path ++ relpath))
      (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk)

inductive HubStableTrace (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term)
    (desired : List Bool) : Nat → Term → Term → Prop where
  | zero (a : Term) : HubStableTrace earlier tail junk initial flag hubJunk desired 0 a a
  | next {n : Nat} {a b c : Term} : HubStableStep earlier tail junk initial flag hubJunk desired a b →
      HubStableTrace earlier tail junk initial flag hubJunk desired n b c →
      HubStableTrace earlier tail junk initial flag hubJunk desired (n+1) a c

theorem global_trace_lifts_to_seed_hub (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term)
    (desired : List Bool) {n : Nat} {a b : Term}
    (trace : GlobalStableTrace earlier tail junk initial desired n a b) :
    HubStableTrace earlier tail junk initial flag hubJunk desired n a b := by
  induction trace with
  | zero x => exact HubStableTrace.zero x
  | @next n a b c hstep rest ih =>
    obtain ⟨hp,hcell,path,focus,rel,hchoose,hat,hlocal,hdir⟩ := hstep
    have hlift := tape_step_under_seed_hub hdir flag hubJunk
    have hglobal : HubStableStep earlier tail junk initial flag hubJunk desired a b := by
      refine ⟨hp,hcell,path,focus,rel,hchoose,hat,hlocal,?_⟩
      simpa [List.append_assoc] using hlift
    exact HubStableTrace.next hglobal ih

#print axioms tape_step_under_seed_hub
#print axioms global_trace_lifts_to_seed_hub

theorem right_move_in_seed_hub (source destination : List UniversalCell)
    (sourceDepth destinationDepth : Nat) (tail sourceJunk destinationJunk : Term)
    (earlier : List (Term × Term)) (flag hubJunk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (written : Bool) (nextState : Fin 132)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let d0 := concreteVersion destination destinationDepth
    let d1 := concreteVersion (destination ++ [active]) destinationDepth
    ∃ k1 k2 k3,
      HubStableTrace earlier (frameTerm d0 tail destinationJunk) sourceJunk s0 flag hubJunk (encodedEntry pending).val k1 s0 s1 ∧
      HubStableTrace (earlier ++ [(s1,sourceJunk)]) tail destinationJunk d0 flag hubJunk (encodedEntry active).val k2 d0 d1 ∧
      HubStableTrace earlier (frameTerm d1 tail destinationJunk) sourceJunk s1 flag hubJunk (encodedEntry off).val k3 s1 s2 ∧
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (6 ≤ k2 ∧ k2 ≤ 168) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s0 d0 tail sourceJunk destinationJunk)) = .active (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s1 d0 tail sourceJunk destinationJunk)) = .pending (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s1 d1 tail sourceJunk destinationJunk)) = .pending (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s2 d1 tail sourceJunk destinationJunk)) = .active (prefixPath earlier ++ [true,false,true]) ∧
      cellFromVersion s2 = off.val ∧ cellFromVersion d1 = active.val := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
  let off := offCellRecord written
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let d0 := concreteVersion destination destinationDepth
  let d1 := concreteVersion (destination ++ [active]) destinationDepth
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth earlier (frameTerm d0 tail destinationJunk) sourceJunk
  obtain ⟨k2,t2,lo2,hi2,read2⟩ :=
    global_stable_version_append destination active destinationDepth (earlier ++ [(s1,sourceJunk)]) tail destinationJunk
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth earlier (frameTerm d1 tail destinationJunk) sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by
    simpa [s0,concrete_version_decodes] using hsource
  have hd0 : (cellFromVersion d0).status = .off := by
    simpa [d0,concrete_version_decodes] using hdestination
  have hs1 : isMoving (cellFromVersion s1).status = true := by
    rw [show cellFromVersion s1 = pending.val from by simpa [s1,concreteVersion,List.map_append] using read1]
    rfl
  have hd1 : (cellFromVersion d1).status = .active := by
    rw [show cellFromVersion d1 = active.val from by simpa [d1,concreteVersion,List.map_append] using read2]
    rfl
  have hs2 : (cellFromVersion s2).status = .off := by
    rw [show cellFromVersion s2 = off.val from by simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3]
    rfl
  refine ⟨k1,k2,k3,?_,?_,?_,⟨lo1,hi1⟩,⟨lo2,hi2⟩,⟨lo3,hi3⟩,?_,?_,?_,?_,?_,?_⟩
  · simpa [s0,s1,d0,concreteVersion,List.map_append] using global_trace_lifts_to_seed_hub earlier (frameTerm d0 tail destinationJunk) sourceJunk s0 flag hubJunk (encodedEntry pending).val t1
  · simpa [s1,d0,d1,concreteVersion,List.map_append] using global_trace_lifts_to_seed_hub (earlier ++ [(s1,sourceJunk)]) tail destinationJunk d0 flag hubJunk (encodedEntry active).val t2
  · simpa [s1,s2,d1,concreteVersion,List.map_append,List.append_assoc] using global_trace_lifts_to_seed_hub earlier (frameTerm d1 tail destinationJunk) sourceJunk s1 flag hubJunk (encodedEntry off).val t3
  · exact prefixed_adjacent_priority_initial earlier s0 d0 tail sourceJunk destinationJunk hprefix hs0 hd0 htail
  · exact prefixed_adjacent_priority_pending earlier s1 d0 tail sourceJunk destinationJunk hprefix hs1
  · exact prefixed_adjacent_priority_pending earlier s1 d1 tail sourceJunk destinationJunk hprefix hs1
  · exact prefixed_adjacent_priority_complete earlier s2 d1 tail sourceJunk destinationJunk hprefix hs2 hd1 htail
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3
  · simpa [d1,concreteVersion,List.map_append] using read2



#print axioms right_move_in_seed_hub

theorem left_move_in_seed_hub (source destination : List UniversalCell)
    (sourceDepth destinationDepth : Nat) (tail sourceJunk destinationJunk : Term)
    (earlier : List (Term × Term)) (flag hubJunk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (written : Bool) (nextState : Fin 132)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (htail : seekConcreteCell movingCell tail = none) :
    let pending := pendingLeftCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let d0 := concreteVersion destination destinationDepth
    let d1 := concreteVersion (destination ++ [active]) destinationDepth
    ∃ k1 k2 k3,
      HubStableTrace (earlier ++ [(d0,destinationJunk)]) tail sourceJunk s0 flag hubJunk (encodedEntry pending).val k1 s0 s1 ∧
      HubStableTrace earlier (frameTerm s1 tail sourceJunk) destinationJunk d0 flag hubJunk (encodedEntry active).val k2 d0 d1 ∧
      HubStableTrace (earlier ++ [(d1,destinationJunk)]) tail sourceJunk s1 flag hubJunk (encodedEntry off).val k3 s1 s2 ∧
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (6 ≤ k2 ∧ k2 ≤ 168) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧
      priorityConcretePath (prependTape earlier (adjacentTape d0 s0 tail destinationJunk sourceJunk)) = .active (prefixPath earlier ++ [true,false,true]) ∧
      priorityConcretePath (prependTape earlier (adjacentTape d0 s1 tail destinationJunk sourceJunk)) = .pending (prefixPath earlier ++ [true,false,true]) ∧
      priorityConcretePath (prependTape earlier (adjacentTape d1 s1 tail destinationJunk sourceJunk)) = .pending (prefixPath earlier ++ [true,false,true]) ∧
      priorityConcretePath (prependTape earlier (adjacentTape d1 s2 tail destinationJunk sourceJunk)) = .active (prefixPath earlier) ∧
      cellFromVersion s2 = off.val ∧ cellFromVersion d1 = active.val := by
  let pending := pendingLeftCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
  let off := offCellRecord written
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let d0 := concreteVersion destination destinationDepth
  let d1 := concreteVersion (destination ++ [active]) destinationDepth
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth (earlier ++ [(d0,destinationJunk)]) tail sourceJunk
  obtain ⟨k2,t2,lo2,hi2,read2⟩ :=
    global_stable_version_append destination active destinationDepth earlier (frameTerm s1 tail sourceJunk) destinationJunk
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth (earlier ++ [(d1,destinationJunk)]) tail sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by
    simpa [s0,concrete_version_decodes] using hsource
  have hd0 : (cellFromVersion d0).status = .off := by
    simpa [d0,concrete_version_decodes] using hdestination
  have hs1 : isMoving (cellFromVersion s1).status = true := by
    rw [show cellFromVersion s1 = pending.val from by simpa [s1,concreteVersion,List.map_append] using read1]
    rfl
  have hd0m : isMoving (cellFromVersion d0).status = false := by simp [hd0,isMoving]
  have hd1 : (cellFromVersion d1).status = .active := by
    rw [show cellFromVersion d1 = active.val from by simpa [d1,concreteVersion,List.map_append] using read2]
    rfl
  have hd1m : isMoving (cellFromVersion d1).status = false := by simp [hd1,isMoving]
  have hs2 : (cellFromVersion s2).status = .off := by
    rw [show cellFromVersion s2 = off.val from by simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3]
    rfl
  refine ⟨k1,k2,k3,?_,?_,?_,⟨lo1,hi1⟩,⟨lo2,hi2⟩,⟨lo3,hi3⟩,?_,?_,?_,?_,?_,?_⟩
  · simpa [s0,s1,d0,concreteVersion,List.map_append] using global_trace_lifts_to_seed_hub (earlier ++ [(d0,destinationJunk)]) tail sourceJunk s0 flag hubJunk (encodedEntry pending).val t1
  · simpa [s1,d0,d1,concreteVersion,List.map_append] using global_trace_lifts_to_seed_hub earlier (frameTerm s1 tail sourceJunk) destinationJunk d0 flag hubJunk (encodedEntry active).val t2
  · simpa [s1,s2,d1,concreteVersion,List.map_append,List.append_assoc] using global_trace_lifts_to_seed_hub (earlier ++ [(d1,destinationJunk)]) tail sourceJunk s1 flag hubJunk (encodedEntry off).val t3
  · exact prefixed_left_priority_initial earlier d0 s0 tail destinationJunk sourceJunk hprefix hd0 hs0 htail
  · exact prefixed_left_priority_pending earlier d0 s1 tail destinationJunk sourceJunk hprefix hd0m hs1
  · exact prefixed_left_priority_pending earlier d1 s1 tail destinationJunk sourceJunk hprefix hd1m hs1
  · exact prefixed_left_priority_complete earlier d1 s2 tail destinationJunk sourceJunk hprefix hd1 hs2 htail
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read3
  · simpa [d1,concreteVersion,List.map_append] using read2



#print axioms left_move_in_seed_hub

theorem stay_in_seed_hub (source : List UniversalCell) (sourceDepth : Nat)
    (earlier : List (Term × Term)) (tail sourceJunk flag hubJunk : Term)
    (written : Bool) (nextState : Fin 132)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hsource : (decodedCell source).status = .active)
    (htail : seekConcreteCell movingCell tail = none) :
    let active := activeCellRecord written nextState
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [active]) sourceDepth
    ∃ k, HubStableTrace earlier tail sourceJunk s0 flag hubJunk (encodedEntry active).val k s0 s1 ∧
      6 ≤ k ∧ k ≤ 168 ∧
      priorityConcretePath (prependTape earlier (frameTerm s0 tail sourceJunk)) = .active (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (frameTerm s1 tail sourceJunk)) = .active (prefixPath earlier) ∧
      cellFromVersion s1 = active.val := by
  let active := activeCellRecord written nextState
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [active]) sourceDepth
  obtain ⟨k,trace,hlower,hupper,hread⟩ :=
    global_stable_version_append source active sourceDepth earlier tail sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by
    simpa [s0,concrete_version_decodes] using hsource
  have hs1 : (cellFromVersion s1).status = .active := by
    rw [show cellFromVersion s1 = active.val from by simpa [s1,concreteVersion,List.map_append] using hread]
    rfl
  refine ⟨k,?_,hlower,hupper,?_,?_,?_⟩
  · simpa [s0,s1,concreteVersion,List.map_append] using global_trace_lifts_to_seed_hub earlier tail sourceJunk s0 flag hubJunk (encodedEntry active).val trace
  · exact prefixed_single_active_priority earlier s0 tail sourceJunk hprefix hs0 htail
  · exact prefixed_single_active_priority earlier s1 tail sourceJunk hprefix hs1 htail
  · simpa [s1,concreteVersion,List.map_append] using hread


#print axioms stay_in_seed_hub

def HubPendingTailStep (earlier : List (Term × Term)) (version junk flag hubJunk : Term) (a b : Term) : Prop :=
  priorityConcretePath (prependTape earlier (frameTerm version a junk)) = .pending (prefixPath earlier) ∧
  ∃ relpath, nextOpeningAddress a = some relpath ∧
    DirectedStep ([true,true,false,true] ++ contextPath (tailFrames earlier version junk) ++ relpath)
      (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk)
      (seedHubRoot flag (prependTape earlier (frameTerm version b junk)) hubJunk)

inductive HubPendingTailTrace (earlier : List (Term × Term)) (version junk flag hubJunk : Term) :
    Nat → Term → Term → Prop where
  | zero (a : Term) : HubPendingTailTrace earlier version junk flag hubJunk 0 a a
  | next {n : Nat} {a b c : Term} : HubPendingTailStep earlier version junk flag hubJunk a b →
      HubPendingTailTrace earlier version junk flag hubJunk n b c →
      HubPendingTailTrace earlier version junk flag hubJunk (n+1) a c

theorem pending_tail_trace_lifts_to_seed_hub (earlier : List (Term × Term))
    (version junk flag hubJunk : Term) {n : Nat} {a b : Term}
    (trace : PendingTailTrace earlier version junk n a b) :
    HubPendingTailTrace earlier version junk flag hubJunk n a b := by
  induction trace with
  | zero x => exact HubPendingTailTrace.zero x
  | @next n a b c hp hstep rest ih =>
    obtain ⟨rel,hlocal,hdir⟩ := hstep
    have hroot := tape_step_under_seed_hub hdir flag hubJunk
    have hglobal : HubPendingTailStep earlier version junk flag hubJunk a b := by
      refine ⟨hp,rel,hlocal,?_⟩
      simpa [← tail_context_representation,List.append_assoc] using hroot
    exact HubPendingTailTrace.next hglobal ih

#print axioms pending_tail_trace_lifts_to_seed_hub

theorem right_extension_in_seed_hub (source : List UniversalCell) (sourceDepth tailDepth : Nat)
    (earlier : List (Term × Term)) (sourceJunk flag hubJunk : Term) (written : Bool) (nextState : Fin 132)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hsource : (decodedCell source).status = .active) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord false nextState
    let off := offCellRecord written
    let s0 := concreteVersion source sourceDepth
    let s1 := concreteVersion (source ++ [pending]) sourceDepth
    let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
    let blank := depthBase (tailDepth+1)
    let d1 := concreteVersion [active] (tailDepth+1)
    let cell0 := frameTerm blank blank (depthJunk tailDepth)
    let cell1 := frameTerm d1 blank (depthJunk tailDepth)
    ∃ k1 k2 k3 k4,
      HubStableTrace earlier (depthBase tailDepth) sourceJunk s0 flag hubJunk (encodedEntry pending).val k1 s0 s1 ∧
      HubPendingTailTrace earlier s1 sourceJunk flag hubJunk k2 (depthBase tailDepth) cell0 ∧
      HubStableTrace (earlier ++ [(s1,sourceJunk)]) blank (depthJunk tailDepth) blank flag hubJunk (encodedEntry active).val k3 blank d1 ∧
      HubStableTrace earlier cell1 sourceJunk s1 flag hubJunk (encodedEntry off).val k4 s1 s2 ∧
      (6 ≤ k1 ∧ k1 ≤ 168) ∧ (k2=6 ∨ k2=7) ∧ (6 ≤ k3 ∧ k3 ≤ 168) ∧ (6 ≤ k4 ∧ k4 ≤ 168) ∧
      priorityConcretePath (prependTape earlier (frameTerm s0 (depthBase tailDepth) sourceJunk)) = .active (prefixPath earlier) ∧
      priorityConcretePath (prependTape earlier (adjacentTape s2 d1 blank sourceJunk (depthJunk tailDepth))) =
        .active (prefixPath earlier ++ [true,false,true]) ∧
      cellFromVersion s2 = off.val ∧ cellFromVersion d1 = active.val := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord false nextState
  let off := offCellRecord written
  let s0 := concreteVersion source sourceDepth
  let s1 := concreteVersion (source ++ [pending]) sourceDepth
  let s2 := concreteVersion (source ++ [pending,off]) sourceDepth
  let blank := depthBase (tailDepth+1)
  let d1 := concreteVersion [active] (tailDepth+1)
  let cell0 := frameTerm blank blank (depthJunk tailDepth)
  let cell1 := frameTerm d1 blank (depthJunk tailDepth)
  obtain ⟨k1,t1,lo1,hi1,read1⟩ :=
    global_stable_version_append source pending sourceDepth earlier (depthBase tailDepth) sourceJunk
  have hs1 : isMoving (cellFromVersion s1).status = true := by
    rw [show cellFromVersion s1 = pending.val from by simpa [s1,concreteVersion,List.map_append] using read1]
    rfl
  obtain ⟨k2,hk2,t2⟩ := pending_tail_opens_at_depth earlier s1 sourceJunk hprefix hs1 tailDepth
  obtain ⟨k3,t3,lo3,hi3,read3⟩ :=
    global_stable_version_append [] active (tailDepth+1) (earlier ++ [(s1,sourceJunk)]) blank (depthJunk tailDepth)
  obtain ⟨k4,t4,lo4,hi4,read4⟩ :=
    global_stable_version_append (source ++ [pending]) off sourceDepth earlier cell1 sourceJunk
  have hs0 : (cellFromVersion s0).status = .active := by simpa [s0,concrete_version_decodes] using hsource
  have hs2 : (cellFromVersion s2).status = .off := by
    rw [show cellFromVersion s2 = off.val from by simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read4]
    rfl
  have hd1 : (cellFromVersion d1).status = .active := by
    rw [show cellFromVersion d1 = active.val from by simpa [d1,concreteVersion,List.map_append] using read3]
    rfl
  refine ⟨k1,k2,k3,k4,?_,?_,?_,?_,⟨lo1,hi1⟩,hk2,⟨lo3,hi3⟩,⟨lo4,hi4⟩,?_,?_,?_,?_⟩
  · simpa [s0,s1,concreteVersion,List.map_append] using global_trace_lifts_to_seed_hub earlier (depthBase tailDepth) sourceJunk s0 flag hubJunk (encodedEntry pending).val t1
  · simpa [cell0,blank,opened_empty_cell_shape] using pending_tail_trace_lifts_to_seed_hub earlier s1 sourceJunk flag hubJunk t2
  · simpa [blank,d1,s1,concreteVersion,depthBase,phaseBase,versionLayout,layoutTerm,List.map_append] using global_trace_lifts_to_seed_hub (earlier ++ [(s1,sourceJunk)]) blank (depthJunk tailDepth) blank flag hubJunk (encodedEntry active).val t3
  · simpa [s1,s2,cell1,d1,blank,concreteVersion,List.map_append,List.append_assoc] using global_trace_lifts_to_seed_hub earlier cell1 sourceJunk s1 flag hubJunk (encodedEntry off).val t4
  · exact prefixed_single_active_priority earlier s0 (depthBase tailDepth) sourceJunk hprefix hs0
      (depth_child_has_no_pending tailDepth)
  · exact prefixed_adjacent_priority_complete earlier s2 d1 blank sourceJunk (depthJunk tailDepth)
      hprefix hs2 hd1 (depth_child_has_no_pending (tailDepth+1))
  · simpa [s2,concreteVersion,List.map_append,List.append_assoc] using read4
  · simpa [d1,concreteVersion,List.map_append] using read3


#print axioms right_extension_in_seed_hub

def SeedHaltStep (tape junk : Term) (choice : PathChoice) (a b : Term) : Prop :=
  haltObserved (frameTerm a tape junk) = false ∧ priorityConcretePath tape = choice ∧
  ∃ relpath, nextOpeningAddress a = some relpath ∧
    DirectedStep ([true] ++ contextPath [.left tape junk] ++ relpath)
      (seedHubRoot a tape junk) (seedHubRoot b tape junk)

inductive SeedHaltTrace (tape junk : Term) (choice : PathChoice) : Nat → Term → Term → Prop where
  | zero (a : Term) : SeedHaltTrace tape junk choice 0 a a
  | next {n : Nat} {a b c : Term} : SeedHaltStep tape junk choice a b →
      SeedHaltTrace tape junk choice n b c → SeedHaltTrace tape junk choice (n+1) a c

theorem halt_trace_lifts_to_seed (tape junk : Term) (choice : PathChoice) {n : Nat} {a b : Term}
    (trace : HaltOpeningTrace tape junk choice n a b) : SeedHaltTrace tape junk choice n a b := by
  induction trace with
  | zero x => exact SeedHaltTrace.zero x
  | @next n a b c hflag hp hfocus rest ih =>
    obtain ⟨rel,hlocal,hdir⟩ := hfocus
    have hroot := DirectedStep.right (a := numeral 1 ⋅ S) hdir
    have hstep : SeedHaltStep tape junk choice a b := by
      refine ⟨hflag,hp,rel,hlocal,?_⟩
      simpa [seedHubRoot,wrapProtected,contextPath,framePath,List.append_assoc] using hroot
    exact SeedHaltTrace.next hstep ih

theorem halt_field_opens_in_seed (flagDepth : Nat) (tape junk : Term) (choice : PathChoice)
    (hpriority : priorityConcretePath tape = choice) :
    ∃ k, (k=6 ∨ k=7) ∧
      SeedHaltTrace tape junk choice k (depthBase flagDepth)
        (layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2) ∧
      haltObserved (frameTerm
        (layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2) tape junk) = true := by
  obtain ⟨k,hk,htrace,hobserved⟩ := halt_field_can_open flagDepth tape junk choice hpriority
  exact ⟨k,hk,halt_trace_lifts_to_seed tape junk choice htrace,hobserved⟩

#print axioms halt_trace_lifts_to_seed
#print axioms halt_field_opens_in_seed

def noWork (tape : Term) : Prop :=
  seekConcreteCell movingCell tape = none ∧ seekConcreteCell activeCell tape = none

def cleanBoundary (earlier : List (Term × Term)) (version tail : Term) : Prop :=
  (∀ x ∈ earlier, (cellFromVersion x.1).status = .off) ∧
  (cellFromVersion version).status = .active ∧ noWork tail

theorem off_cell_preserves_no_work (version tail junk : Term)
    (hoff : (cellFromVersion version).status = .off) (htail : noWork tail) :
    noWork (frameTerm version tail junk) := by
  obtain ⟨hm,ha⟩ := htail
  simp [noWork,seek_concrete_frame,movingCell,activeCell,isMoving,hoff,hm,ha]

theorem off_prefix_append (earlier : List (Term × Term)) (version junk : Term)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hoff : (cellFromVersion version).status = .off) :
    ∀ x ∈ earlier ++ [(version,junk)], (cellFromVersion x.1).status = .off := by
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with h | h
  · exact hprefix x h
  · subst x; exact hoff

theorem clean_boundary_right_update (earlier : List (Term × Term))
    (oldSource newSource newDestination tail sourceJunk : Term)
    (hbefore : cleanBoundary earlier oldSource tail)
    (hoff : (cellFromVersion newSource).status = .off)
    (hactive : (cellFromVersion newDestination).status = .active) :
    cleanBoundary (earlier ++ [(newSource,sourceJunk)]) newDestination tail := by
  exact ⟨off_prefix_append earlier newSource sourceJunk hbefore.1 hoff,hactive,hbefore.2.2⟩

theorem clean_boundary_left_update (earlier : List (Term × Term))
    (oldSource newSource newDestination tail sourceJunk : Term)
    (hbefore : cleanBoundary earlier oldSource tail)
    (hoff : (cellFromVersion newSource).status = .off)
    (hactive : (cellFromVersion newDestination).status = .active) :
    cleanBoundary earlier newDestination (frameTerm newSource tail sourceJunk) := by
  exact ⟨hbefore.1,hactive,off_cell_preserves_no_work newSource tail sourceJunk hoff hbefore.2.2⟩

#print axioms off_cell_preserves_no_work
#print axioms off_prefix_append
#print axioms clean_boundary_right_update
#print axioms clean_boundary_left_update

theorem clean_boundary_stay_update (earlier : List (Term × Term)) (oldSource newSource tail : Term)
    (hbefore : cleanBoundary earlier oldSource tail)
    (hactive : (cellFromVersion newSource).status = .active) : cleanBoundary earlier newSource tail := by
  exact ⟨hbefore.1,hactive,hbefore.2.2⟩

theorem unopened_tail_no_work (m n : Nat) : noWork (generator m n) := by
  exact ⟨seek_concrete_closed movingCell (generator m n) (parse_generator_closed m n),
    seek_concrete_closed activeCell (generator m n) (parse_generator_closed m n)⟩

#print axioms clean_boundary_stay_update
#print axioms unopened_tail_no_work

theorem hub_stable_trace_is_exact (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term)
    (desired : List Bool) {n : Nat} {a b : Term}
    (trace : HubStableTrace earlier tail junk initial flag hubJunk desired n a b) :
    ExactSteps n (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk) := by
  induction trace with
  | zero x => exact ExactSteps.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨_,_,path,focus,rel,hchoose,hat,hlocal,hdir⟩ := hstep
    exact ExactSteps.next (directed_step_is_native hdir) ih

#print axioms hub_stable_trace_is_exact

inductive HubNoHaltTrace (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term)
    (desired : List Bool) : Nat → Term → Term → Prop where
  | zero (a : Term) : HubNoHaltTrace earlier tail junk initial flag hubJunk desired 0 a a
  | next {n : Nat} {a b c : Term} : HubStableStep earlier tail junk initial flag hubJunk desired a b →
      haltObserved (frameTerm flag (tapeAroundVersion earlier a tail junk) hubJunk) = false →
      HubNoHaltTrace earlier tail junk initial flag hubJunk desired n b c →
      HubNoHaltTrace earlier tail junk initial flag hubJunk desired (n+1) a c

theorem hub_trace_keeps_halt_closed (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term)
    (desired : List Bool) (hflag : parseFrame flag = none) {n : Nat} {a b : Term}
    (trace : HubStableTrace earlier tail junk initial flag hubJunk desired n a b) :
    HubNoHaltTrace earlier tail junk initial flag hubJunk desired n a b := by
  induction trace with
  | zero x => exact HubNoHaltTrace.zero x
  | @next n a b c hstep rest ih =>
    exact HubNoHaltTrace.next hstep
      (halt_field_closed_observation flag (tapeAroundVersion earlier a tail junk) hubJunk hflag) ih

#print axioms hub_trace_keeps_halt_closed

theorem adjacent_contexts_stitch (earlier : List (Term × Term)) (source destination tail sourceJunk destinationJunk : Term) :
    tapeAroundVersion earlier source (frameTerm destination tail destinationJunk) sourceJunk =
      tapeAroundVersion (earlier ++ [(source,sourceJunk)]) destination tail destinationJunk := by
  calc
    tapeAroundVersion earlier source (frameTerm destination tail destinationJunk) sourceJunk =
        prependTape earlier (frameTerm source (frameTerm destination tail destinationJunk) sourceJunk) := by
      simpa [tapeAroundVersion] using
        (prepend_tape_around earlier [] source (frameTerm destination tail destinationJunk) sourceJunk)
    _ = tapeAroundVersion (earlier ++ [(source,sourceJunk)]) destination tail destinationJunk := by
      rw [prepend_tape_around]
      rfl

#print axioms adjacent_contexts_stitch

theorem tape_around_adjacent (earlier : List (Term × Term)) (source destination tail sourceJunk destinationJunk : Term) :
    tapeAroundVersion earlier source (frameTerm destination tail destinationJunk) sourceJunk =
      prependTape earlier (adjacentTape source destination tail sourceJunk destinationJunk) := by
  simpa [tapeAroundVersion,adjacentTape] using
    (prepend_tape_around earlier [] source (frameTerm destination tail destinationJunk) sourceJunk)

#print axioms tape_around_adjacent

theorem hub_pending_tail_trace_is_exact (earlier : List (Term × Term)) (version junk flag hubJunk : Term)
    {n : Nat} {a b : Term} (trace : HubPendingTailTrace earlier version junk flag hubJunk n a b) :
    ExactSteps n (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk)
      (seedHubRoot flag (prependTape earlier (frameTerm version b junk)) hubJunk) := by
  induction trace with
  | zero x => exact ExactSteps.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨_,rel,hlocal,hdir⟩ := hstep
    exact ExactSteps.next (directed_step_is_native hdir) ih

#print axioms hub_pending_tail_trace_is_exact

theorem tape_around_single (earlier : List (Term × Term)) (version tail junk : Term) :
    tapeAroundVersion earlier version tail junk = prependTape earlier (frameTerm version tail junk) := by
  simpa [tapeAroundVersion] using (prepend_tape_around earlier [] version tail junk)

#print axioms tape_around_single

def rootHalt : Term → Bool
  | .app _ hub => haltObserved hub
  | _ => false

theorem root_halt_seed (flag tape hubJunk : Term) :
    rootHalt (seedHubRoot flag tape hubJunk) = haltObserved (frameTerm flag tape hubJunk) := by rfl

inductive SafeExactSteps : Nat → Term → Term → Prop where
  | zero (a : Term) : SafeExactSteps 0 a a
  | next {n : Nat} {a b c : Term} : rootHalt a = false → Step a b → SafeExactSteps n b c → SafeExactSteps (n+1) a c

theorem safe_exact_trans {n m : Nat} {a b c : Term}
    (h : SafeExactSteps n a b) (k : SafeExactSteps m b c) : SafeExactSteps (n+m) a c := by
  induction h with
  | zero _ => simpa using k
  | @next n a b c hhalt hab rest ih =>
    have result := SafeExactSteps.next hhalt hab (ih k)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem hub_stable_trace_is_safe (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term)
    (desired : List Bool) (hflag : parseFrame flag = none) {n : Nat} {a b : Term}
    (trace : HubStableTrace earlier tail junk initial flag hubJunk desired n a b) :
    SafeExactSteps n (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk) := by
  induction trace with
  | zero x => exact SafeExactSteps.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨_,_,path,focus,rel,hchoose,hat,hlocal,hdir⟩ := hstep
    have hhalt : rootHalt (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk) = false := by
      rw [root_halt_seed]
      exact halt_field_closed_observation flag _ hubJunk hflag
    exact SafeExactSteps.next hhalt (directed_step_is_native hdir) ih

theorem hub_pending_tail_trace_is_safe (earlier : List (Term × Term)) (version junk flag hubJunk : Term)
    (hflag : parseFrame flag = none) {n : Nat} {a b : Term}
    (trace : HubPendingTailTrace earlier version junk flag hubJunk n a b) :
    SafeExactSteps n (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk)
      (seedHubRoot flag (prependTape earlier (frameTerm version b junk)) hubJunk) := by
  induction trace with
  | zero x => exact SafeExactSteps.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨_,rel,hlocal,hdir⟩ := hstep
    have hhalt : rootHalt (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk) = false := by
      rw [root_halt_seed]
      exact halt_field_closed_observation flag _ hubJunk hflag
    exact SafeExactSteps.next hhalt (directed_step_is_native hdir) ih

#print axioms root_halt_seed
#print axioms safe_exact_trans
#print axioms hub_stable_trace_is_safe
#print axioms hub_pending_tail_trace_is_safe

theorem seed_halt_trace_is_safe (tape junk : Term) (choice : PathChoice) {n : Nat} {a b : Term}
    (trace : SeedHaltTrace tape junk choice n a b) :
    SafeExactSteps n (seedHubRoot a tape junk) (seedHubRoot b tape junk) := by
  induction trace with
  | zero x => exact SafeExactSteps.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨hflag,_,rel,hlocal,hdir⟩ := hstep
    have hroot : rootHalt (seedHubRoot a tape junk) = false := by
      rw [root_halt_seed]
      exact hflag
    exact SafeExactSteps.next hroot (directed_step_is_native hdir) ih

#print axioms seed_halt_trace_is_safe
