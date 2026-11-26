import stable_global_scan

/- Canonical list-of-cells decomposition into the S tape context. -/

def canonicalTape (cells : List (List UniversalCell)) (depth : Nat) : Term :=
  layoutTerm (storageTapeLayout cells) (phaseAt depth).1 (phaseAt depth).2

def canonicalPrefix : List (List UniversalCell) → Nat → List (Term × Term)
  | [], _ => []
  | cell :: rest, depth => (concreteVersion cell (depth+1),depthJunk depth) :: canonicalPrefix rest (depth+1)

theorem canonical_tape_nil (d : Nat) : canonicalTape [] d = depthBase d := by rfl

theorem canonical_tape_cons (cell : List UniversalCell) (rest : List (List UniversalCell)) (d : Nat) :
    canonicalTape (cell :: rest) d =
      frameTerm (concreteVersion cell (d+1)) (canonicalTape rest (d+1)) (depthJunk d) := by
  unfold canonicalTape storageTapeLayout
  rw [layout_opened_phase _ _ _ (phase_at_good d)]
  simp [concreteVersion,depthJunk,phaseAt]
  cases rest <;> rfl

theorem canonical_tape_append (before after : List (List UniversalCell)) :
    ∀ d, canonicalTape (before ++ after) d =
      prependTape (canonicalPrefix before d) (canonicalTape after (d+before.length)) := by
  induction before with
  | nil => intro d; simp [canonicalPrefix,prependTape]
  | cons cell rest ih =>
    intro d
    simp only [List.cons_append,canonical_tape_cons,canonicalPrefix,prependTape]
    rw [ih]
    simp [Nat.add_assoc,Nat.add_comm]

#print axioms canonical_tape_nil
#print axioms canonical_tape_cons
#print axioms canonical_tape_append

theorem canonical_prefix_off (before : List (List UniversalCell)) :
    ∀ d, (∀ cell ∈ before, (decodedCell cell).status = .off) →
      ∀ x ∈ canonicalPrefix before d, (cellFromVersion x.1).status = .off := by
  induction before with
  | nil => intro d h x hx; simp [canonicalPrefix] at hx
  | cons cell rest ih =>
    intro d h x hx
    simp only [canonicalPrefix,List.mem_cons] at hx
    rcases hx with heq | htail
    · subst x
      rw [concrete_version_decodes]
      exact h cell (by simp)
    · have hrest : ∀ cell ∈ rest, (decodedCell cell).status = .off := by
        intro c hc
        exact h c (by simp [hc])
      exact ih (d+1) hrest x htail

theorem stable_slots_tape_eq (cells : List (List UniversalCell)) :
    slotTapeLayout (cells.map CellSlot.stable) = storageTapeLayout cells := by
  induction cells with
  | nil => rfl
  | cons a rest ih => simp [slotTapeLayout,storageTapeLayout,slotVersionLayout,ih]

theorem canonical_tape_off_no_work (cells : List (List UniversalCell)) (d : Nat)
    (hoff : ∀ cell ∈ cells, (decodedCell cell).status = .off) : noWork (canonicalTape cells d) := by
  have hp := phase_at_good d
  have hm : layoutMatches (storageTapeLayout cells) (canonicalTape cells d) :=
    finite_layout_decodes (storageTapeLayout cells) (phaseAt d).1 (phaseAt d).2 hp.1 hp.2
  have hmove : ∀ c ∈ cells.map decodedCell, movingCell c = false := by
    intro c hc
    obtain ⟨records,hr,rfl⟩ := List.mem_map.mp hc
    simp [movingCell,isMoving,hoff records hr]
  have hactive : ∀ c ∈ cells.map decodedCell, activeCell c = false := by
    intro c hc
    obtain ⟨records,hr,rfl⟩ := List.mem_map.mp hc
    simp [activeCell,hoff records hr]
  have hlayout := stable_slots_tape_eq cells
  have hslot : layoutMatches (slotTapeLayout (cells.map CellSlot.stable)) (canonicalTape cells d) := by
    rw [hlayout]
    exact hm
  have hsm := seek_concrete_slots (cells.map CellSlot.stable) movingCell (canonicalTape cells d) hslot
  have hsa := seek_concrete_slots (cells.map CellSlot.stable) activeCell (canonicalTape cells d) hslot
  have hdec : (cells.map CellSlot.stable).map slotDecoded = cells.map decodedCell := by
    simp [List.map_map,Function.comp_def,slotDecoded,slotRecords]
  unfold noWork
  rw [hsm,hsa,hdec,scan_none_when_absent movingCell _ hmove,scan_none_when_absent activeCell _ hactive]
  simp

#print axioms canonical_prefix_off
#print axioms canonical_tape_off_no_work

theorem canonical_adjacent_decompose (before : List (List UniversalCell)) (source destination : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) :
    canonicalTape (before ++ source :: destination :: after) d =
      prependTape (canonicalPrefix before d)
        (adjacentTape (concreteVersion source (d+before.length+1))
          (concreteVersion destination (d+before.length+2))
          (canonicalTape after (d+before.length+2))
          (depthJunk (d+before.length)) (depthJunk (d+before.length+1))) := by
  rw [canonical_tape_append]
  rw [canonical_tape_cons,canonical_tape_cons]
  simp [adjacentTape,Nat.add_assoc]

#print axioms canonical_adjacent_decompose

def canonicalRoot (cells : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term) : Term :=
  seedHubRoot flag (canonicalTape cells d) hubJunk

theorem canonical_right_step_native
    (before : List (List UniversalCell)) (source destination : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term) (written : Bool) (q : Fin 132)
    (hbefore : ∀ cell ∈ before, (decodedCell cell).status = .off)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (hafter : ∀ cell ∈ after, (decodedCell cell).status = .off) :
    let pending := pendingRightCell written q
    let active := activeCellRecord (decodedCell destination).bit q
    let off := offCellRecord written
    ∃ k, 18 ≤ k ∧ k ≤ 504 ∧
      ExactSteps k (canonicalRoot (before ++ source :: destination :: after) d flag hubJunk)
        (canonicalRoot (before ++ (source ++ [pending,off]) :: (destination ++ [active]) :: after) d flag hubJunk) := by
  let pending := pendingRightCell written q
  let active := activeCellRecord (decodedCell destination).bit q
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let sd := d+before.length+1
  let dd := d+before.length+2
  let sj := depthJunk (d+before.length)
  let dj := depthJunk (d+before.length+1)
  let tail := canonicalTape after (d+before.length+2)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending,off]) sd
  let d0 := concreteVersion destination dd
  let d1 := concreteVersion (destination ++ [active]) dd
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  obtain ⟨k1,k2,k3,t1,t2,t3,hb1,hb2,hb3,_,_,_,_,_,_⟩ :=
    right_move_in_seed_hub source destination sd dd tail sj dj earlier flag hubJunk hprefix written q
      hsource hdestination htail
  have e1 := hub_stable_trace_is_exact earlier (frameTerm d0 tail dj) sj s0 flag hubJunk (encodedEntry pending).val t1
  have e2 := hub_stable_trace_is_exact (earlier ++ [(s1,sj)]) tail dj d0 flag hubJunk (encodedEntry active).val t2
  have e3 := hub_stable_trace_is_exact earlier (frameTerm d1 tail dj) sj s1 flag hubJunk (encodedEntry off).val t3
  rw [← adjacent_contexts_stitch earlier s1 d0 tail sj dj, ← adjacent_contexts_stitch earlier s1 d1 tail sj dj] at e2
  have combined := exact_steps_trans e1 (exact_steps_trans e2 e3)
  have hstart : tapeAroundVersion earlier s0 (frameTerm d0 tail dj) sj =
      canonicalTape (before ++ source :: destination :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before source destination after d).symm
  have hend : tapeAroundVersion earlier s2 (frameTerm d1 tail dj) sj =
      canonicalTape (before ++ (source ++ [pending,off]) :: (destination ++ [active]) :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before (source ++ [pending,off]) (destination ++ [active]) after d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+k3),?_,?_,?_⟩
  · omega
  · omega
  · exact combined

#print axioms canonical_right_step_native

theorem canonical_left_step_native
    (before : List (List UniversalCell)) (destination source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term) (written : Bool) (q : Fin 132)
    (hbefore : ∀ cell ∈ before, (decodedCell cell).status = .off)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (hafter : ∀ cell ∈ after, (decodedCell cell).status = .off) :
    let pending := pendingLeftCell written q
    let active := activeCellRecord (decodedCell destination).bit q
    let off := offCellRecord written
    ∃ k, 18 ≤ k ∧ k ≤ 504 ∧
      ExactSteps k (canonicalRoot (before ++ destination :: source :: after) d flag hubJunk)
        (canonicalRoot (before ++ (destination ++ [active]) :: (source ++ [pending,off]) :: after) d flag hubJunk) := by
  let pending := pendingLeftCell written q
  let active := activeCellRecord (decodedCell destination).bit q
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let dd := d+before.length+1
  let sd := d+before.length+2
  let dj := depthJunk (d+before.length)
  let sj := depthJunk (d+before.length+1)
  let tail := canonicalTape after (d+before.length+2)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending,off]) sd
  let d0 := concreteVersion destination dd
  let d1 := concreteVersion (destination ++ [active]) dd
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  obtain ⟨k1,k2,k3,t1,t2,t3,hb1,hb2,hb3,_,_,_,_,_,_⟩ :=
    left_move_in_seed_hub source destination sd dd tail sj dj earlier flag hubJunk hprefix written q
      hsource hdestination htail
  have e1 := hub_stable_trace_is_exact (earlier ++ [(d0,dj)]) tail sj s0 flag hubJunk (encodedEntry pending).val t1
  have e2 := hub_stable_trace_is_exact earlier (frameTerm s1 tail sj) dj d0 flag hubJunk (encodedEntry active).val t2
  have e3 := hub_stable_trace_is_exact (earlier ++ [(d1,dj)]) tail sj s1 flag hubJunk (encodedEntry off).val t3
  rw [← adjacent_contexts_stitch earlier d0 s0 tail dj sj, ← adjacent_contexts_stitch earlier d0 s1 tail dj sj] at e1
  rw [← adjacent_contexts_stitch earlier d1 s1 tail dj sj, ← adjacent_contexts_stitch earlier d1 s2 tail dj sj] at e3
  have combined := exact_steps_trans e1 (exact_steps_trans e2 e3)
  have hstart : tapeAroundVersion earlier d0 (frameTerm s0 tail sj) dj =
      canonicalTape (before ++ destination :: source :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before destination source after d).symm
  have hend : tapeAroundVersion earlier d1 (frameTerm s2 tail sj) dj =
      canonicalTape (before ++ (destination ++ [active]) :: (source ++ [pending,off]) :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before (destination ++ [active]) (source ++ [pending,off]) after d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+k3),?_,?_,?_⟩
  · omega
  · omega
  · exact combined

#print axioms canonical_left_step_native

theorem canonical_single_decompose (before : List (List UniversalCell)) (source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) :
    canonicalTape (before ++ source :: after) d =
      tapeAroundVersion (canonicalPrefix before d) (concreteVersion source (d+before.length+1))
        (canonicalTape after (d+before.length+1)) (depthJunk (d+before.length)) := by
  rw [canonical_tape_append,canonical_tape_cons]
  simpa [tapeAroundVersion] using
    (prepend_tape_around (canonicalPrefix before d) []
      (concreteVersion source (d+before.length+1)) (canonicalTape after (d+before.length+1))
      (depthJunk (d+before.length))).symm

theorem canonical_stay_step_native
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term) (written : Bool) (q : Fin 132)
    (hbefore : ∀ cell ∈ before, (decodedCell cell).status = .off)
    (hsource : (decodedCell source).status = .active)
    (hafter : ∀ cell ∈ after, (decodedCell cell).status = .off) :
    let active := activeCellRecord written q
    ∃ k, 6 ≤ k ∧ k ≤ 168 ∧
      ExactSteps k (canonicalRoot (before ++ source :: after) d flag hubJunk)
        (canonicalRoot (before ++ (source ++ [active]) :: after) d flag hubJunk) := by
  let active := activeCellRecord written q
  let earlier := canonicalPrefix before d
  let sd := d+before.length+1
  let sj := depthJunk (d+before.length)
  let tail := canonicalTape after (d+before.length+1)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [active]) sd
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  obtain ⟨k,trace,hlower,hupper,_,_,_⟩ :=
    stay_in_seed_hub source sd earlier tail sj flag hubJunk written q hprefix hsource htail
  have combined := hub_stable_trace_is_exact earlier tail sj s0 flag hubJunk (encodedEntry active).val trace
  have hstart : tapeAroundVersion earlier s0 tail sj = canonicalTape (before ++ source :: after) d := by
    exact (canonical_single_decompose before source after d).symm
  have hend : tapeAroundVersion earlier s1 tail sj = canonicalTape (before ++ (source ++ [active]) :: after) d := by
    exact (canonical_single_decompose before (source ++ [active]) after d).symm
  rw [hstart,hend] at combined
  exact ⟨k,hlower,hupper,combined⟩

#print axioms canonical_single_decompose
#print axioms canonical_stay_step_native

theorem canonical_right_extension_native
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (d : Nat) (flag hubJunk : Term) (written : Bool) (q : Fin 132)
    (hbefore : ∀ cell ∈ before, (decodedCell cell).status = .off)
    (hsource : (decodedCell source).status = .active) :
    let pending := pendingRightCell written q
    let active := activeCellRecord false q
    let off := offCellRecord written
    ∃ k, 24 ≤ k ∧ k ≤ 511 ∧
      ExactSteps k (canonicalRoot (before ++ [source]) d flag hubJunk)
        (canonicalRoot (before ++ [source ++ [pending,off],[active]]) d flag hubJunk) := by
  let pending := pendingRightCell written q
  let active := activeCellRecord false q
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let sd := d+before.length+1
  let td := d+before.length+1
  let sj := depthJunk (d+before.length)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending,off]) sd
  let blank := depthBase (td+1)
  let d1 := concreteVersion [active] (td+1)
  let cell0 := frameTerm blank blank (depthJunk td)
  let cell1 := frameTerm d1 blank (depthJunk td)
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  obtain ⟨k1,k2,k3,k4,t1,t2,t3,t4,hb1,hb2,hb3,hb4,_,_,_,_⟩ :=
    right_extension_in_seed_hub source sd td earlier sj flag hubJunk written q hprefix hsource
  have e1 := hub_stable_trace_is_exact earlier (depthBase td) sj s0 flag hubJunk (encodedEntry pending).val t1
  have e2 := hub_pending_tail_trace_is_exact earlier s1 sj flag hubJunk t2
  have e3 := hub_stable_trace_is_exact (earlier ++ [(s1,sj)]) blank (depthJunk td) blank flag hubJunk (encodedEntry active).val t3
  have e4 := hub_stable_trace_is_exact earlier cell1 sj s1 flag hubJunk (encodedEntry off).val t4
  rw [← tape_around_single earlier s1 (depthBase td) sj, ← tape_around_single earlier s1 cell0 sj] at e2
  have hcell0 : cell0 = frameTerm blank blank (depthJunk td) := rfl
  rw [hcell0, adjacent_contexts_stitch earlier s1 blank blank sj (depthJunk td)] at e2
  have hcell1 : cell1 = frameTerm d1 blank (depthJunk td) := rfl
  rw [hcell1, adjacent_contexts_stitch earlier s1 d1 blank sj (depthJunk td)] at e4
  have combined := exact_steps_trans e1 (exact_steps_trans e2 (exact_steps_trans e3 e4))
  have hstart : tapeAroundVersion earlier s0 (depthBase td) sj = canonicalTape (before ++ [source]) d := by
    simpa [td,canonical_tape_nil] using (canonical_single_decompose before source [] d).symm
  have hend : tapeAroundVersion earlier s2 (frameTerm d1 blank (depthJunk td)) sj =
      canonicalTape (before ++ [source ++ [pending,off],[active]]) d := by
    rw [tape_around_adjacent]
    simpa [td,blank,d1,canonical_tape_nil] using
      (canonical_adjacent_decompose before (source ++ [pending,off]) [active] [] d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+(k3+k4)),?_,?_,?_⟩
  · cases hb2 <;> omega
  · cases hb2 <;> omega
  · exact combined

#print axioms canonical_right_extension_native

theorem canonical_right_step_safe
    (before : List (List UniversalCell)) (source destination : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term) (written : Bool) (q : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : ∀ cell ∈ before, (decodedCell cell).status = .off)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (hafter : ∀ cell ∈ after, (decodedCell cell).status = .off) :
    let pending := pendingRightCell written q
    let active := activeCellRecord (decodedCell destination).bit q
    let off := offCellRecord written
    ∃ k, 18 ≤ k ∧ k ≤ 504 ∧
      SafeExactSteps k (canonicalRoot (before ++ source :: destination :: after) d flag hubJunk)
        (canonicalRoot (before ++ (source ++ [pending,off]) :: (destination ++ [active]) :: after) d flag hubJunk) := by
  let pending := pendingRightCell written q
  let active := activeCellRecord (decodedCell destination).bit q
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let sd := d+before.length+1
  let dd := d+before.length+2
  let sj := depthJunk (d+before.length)
  let dj := depthJunk (d+before.length+1)
  let tail := canonicalTape after (d+before.length+2)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending,off]) sd
  let d0 := concreteVersion destination dd
  let d1 := concreteVersion (destination ++ [active]) dd
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  obtain ⟨k1,k2,k3,t1,t2,t3,hb1,hb2,hb3,_,_,_,_,_,_⟩ :=
    right_move_in_seed_hub source destination sd dd tail sj dj earlier flag hubJunk hprefix written q
      hsource hdestination htail
  have e1 := hub_stable_trace_is_safe earlier (frameTerm d0 tail dj) sj s0 flag hubJunk (encodedEntry pending).val hflag t1
  have e2 := hub_stable_trace_is_safe (earlier ++ [(s1,sj)]) tail dj d0 flag hubJunk (encodedEntry active).val hflag t2
  have e3 := hub_stable_trace_is_safe earlier (frameTerm d1 tail dj) sj s1 flag hubJunk (encodedEntry off).val hflag t3
  rw [← adjacent_contexts_stitch earlier s1 d0 tail sj dj, ← adjacent_contexts_stitch earlier s1 d1 tail sj dj] at e2
  have combined := safe_exact_trans e1 (safe_exact_trans e2 e3)
  have hstart : tapeAroundVersion earlier s0 (frameTerm d0 tail dj) sj =
      canonicalTape (before ++ source :: destination :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before source destination after d).symm
  have hend : tapeAroundVersion earlier s2 (frameTerm d1 tail dj) sj =
      canonicalTape (before ++ (source ++ [pending,off]) :: (destination ++ [active]) :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before (source ++ [pending,off]) (destination ++ [active]) after d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+k3),?_,?_,?_⟩
  · omega
  · omega
  · exact combined


#print axioms canonical_right_step_safe

theorem canonical_left_step_safe
    (before : List (List UniversalCell)) (destination source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term) (written : Bool) (q : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : ∀ cell ∈ before, (decodedCell cell).status = .off)
    (hsource : (decodedCell source).status = .active)
    (hdestination : (decodedCell destination).status = .off)
    (hafter : ∀ cell ∈ after, (decodedCell cell).status = .off) :
    let pending := pendingLeftCell written q
    let active := activeCellRecord (decodedCell destination).bit q
    let off := offCellRecord written
    ∃ k, 18 ≤ k ∧ k ≤ 504 ∧
      SafeExactSteps k (canonicalRoot (before ++ destination :: source :: after) d flag hubJunk)
        (canonicalRoot (before ++ (destination ++ [active]) :: (source ++ [pending,off]) :: after) d flag hubJunk) := by
  let pending := pendingLeftCell written q
  let active := activeCellRecord (decodedCell destination).bit q
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let dd := d+before.length+1
  let sd := d+before.length+2
  let dj := depthJunk (d+before.length)
  let sj := depthJunk (d+before.length+1)
  let tail := canonicalTape after (d+before.length+2)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending,off]) sd
  let d0 := concreteVersion destination dd
  let d1 := concreteVersion (destination ++ [active]) dd
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  obtain ⟨k1,k2,k3,t1,t2,t3,hb1,hb2,hb3,_,_,_,_,_,_⟩ :=
    left_move_in_seed_hub source destination sd dd tail sj dj earlier flag hubJunk hprefix written q
      hsource hdestination htail
  have e1 := hub_stable_trace_is_safe (earlier ++ [(d0,dj)]) tail sj s0 flag hubJunk (encodedEntry pending).val hflag t1
  have e2 := hub_stable_trace_is_safe earlier (frameTerm s1 tail sj) dj d0 flag hubJunk (encodedEntry active).val hflag t2
  have e3 := hub_stable_trace_is_safe (earlier ++ [(d1,dj)]) tail sj s1 flag hubJunk (encodedEntry off).val hflag t3
  rw [← adjacent_contexts_stitch earlier d0 s0 tail dj sj, ← adjacent_contexts_stitch earlier d0 s1 tail dj sj] at e1
  rw [← adjacent_contexts_stitch earlier d1 s1 tail dj sj, ← adjacent_contexts_stitch earlier d1 s2 tail dj sj] at e3
  have combined := safe_exact_trans e1 (safe_exact_trans e2 e3)
  have hstart : tapeAroundVersion earlier d0 (frameTerm s0 tail sj) dj =
      canonicalTape (before ++ destination :: source :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before destination source after d).symm
  have hend : tapeAroundVersion earlier d1 (frameTerm s2 tail sj) dj =
      canonicalTape (before ++ (destination ++ [active]) :: (source ++ [pending,off]) :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before (destination ++ [active]) (source ++ [pending,off]) after d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+k3),?_,?_,?_⟩
  · omega
  · omega
  · exact combined


#print axioms canonical_left_step_safe

theorem canonical_stay_step_safe
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term) (written : Bool) (q : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : ∀ cell ∈ before, (decodedCell cell).status = .off)
    (hsource : (decodedCell source).status = .active)
    (hafter : ∀ cell ∈ after, (decodedCell cell).status = .off) :
    let active := activeCellRecord written q
    ∃ k, 6 ≤ k ∧ k ≤ 168 ∧
      SafeExactSteps k (canonicalRoot (before ++ source :: after) d flag hubJunk)
        (canonicalRoot (before ++ (source ++ [active]) :: after) d flag hubJunk) := by
  let active := activeCellRecord written q
  let earlier := canonicalPrefix before d
  let sd := d+before.length+1
  let sj := depthJunk (d+before.length)
  let tail := canonicalTape after (d+before.length+1)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [active]) sd
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  obtain ⟨k,trace,hlower,hupper,_,_,_⟩ :=
    stay_in_seed_hub source sd earlier tail sj flag hubJunk written q hprefix hsource htail
  have combined := hub_stable_trace_is_safe earlier tail sj s0 flag hubJunk (encodedEntry active).val hflag trace
  have hstart : tapeAroundVersion earlier s0 tail sj = canonicalTape (before ++ source :: after) d := by
    exact (canonical_single_decompose before source after d).symm
  have hend : tapeAroundVersion earlier s1 tail sj = canonicalTape (before ++ (source ++ [active]) :: after) d := by
    exact (canonical_single_decompose before (source ++ [active]) after d).symm
  rw [hstart,hend] at combined
  exact ⟨k,hlower,hupper,combined⟩

#print axioms canonical_single_decompose

#print axioms canonical_stay_step_safe

theorem canonical_right_extension_safe
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (d : Nat) (flag hubJunk : Term) (written : Bool) (q : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : ∀ cell ∈ before, (decodedCell cell).status = .off)
    (hsource : (decodedCell source).status = .active) :
    let pending := pendingRightCell written q
    let active := activeCellRecord false q
    let off := offCellRecord written
    ∃ k, 24 ≤ k ∧ k ≤ 511 ∧
      SafeExactSteps k (canonicalRoot (before ++ [source]) d flag hubJunk)
        (canonicalRoot (before ++ [source ++ [pending,off],[active]]) d flag hubJunk) := by
  let pending := pendingRightCell written q
  let active := activeCellRecord false q
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let sd := d+before.length+1
  let td := d+before.length+1
  let sj := depthJunk (d+before.length)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending,off]) sd
  let blank := depthBase (td+1)
  let d1 := concreteVersion [active] (td+1)
  let cell0 := frameTerm blank blank (depthJunk td)
  let cell1 := frameTerm d1 blank (depthJunk td)
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  obtain ⟨k1,k2,k3,k4,t1,t2,t3,t4,hb1,hb2,hb3,hb4,_,_,_,_⟩ :=
    right_extension_in_seed_hub source sd td earlier sj flag hubJunk written q hprefix hsource
  have e1 := hub_stable_trace_is_safe earlier (depthBase td) sj s0 flag hubJunk (encodedEntry pending).val hflag t1
  have e2 := hub_pending_tail_trace_is_safe earlier s1 sj flag hubJunk hflag t2
  have e3 := hub_stable_trace_is_safe (earlier ++ [(s1,sj)]) blank (depthJunk td) blank flag hubJunk (encodedEntry active).val hflag t3
  have e4 := hub_stable_trace_is_safe earlier cell1 sj s1 flag hubJunk (encodedEntry off).val hflag t4
  rw [← tape_around_single earlier s1 (depthBase td) sj, ← tape_around_single earlier s1 cell0 sj] at e2
  have hcell0 : cell0 = frameTerm blank blank (depthJunk td) := rfl
  rw [hcell0, adjacent_contexts_stitch earlier s1 blank blank sj (depthJunk td)] at e2
  have hcell1 : cell1 = frameTerm d1 blank (depthJunk td) := rfl
  rw [hcell1, adjacent_contexts_stitch earlier s1 d1 blank sj (depthJunk td)] at e4
  have combined := safe_exact_trans e1 (safe_exact_trans e2 (safe_exact_trans e3 e4))
  have hstart : tapeAroundVersion earlier s0 (depthBase td) sj = canonicalTape (before ++ [source]) d := by
    simpa [td,canonical_tape_nil] using (canonical_single_decompose before source [] d).symm
  have hend : tapeAroundVersion earlier s2 (frameTerm d1 blank (depthJunk td)) sj =
      canonicalTape (before ++ [source ++ [pending,off],[active]]) d := by
    rw [tape_around_adjacent]
    simpa [td,blank,d1,canonical_tape_nil] using
      (canonical_adjacent_decompose before (source ++ [pending,off]) [active] [] d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+(k3+k4)),?_,?_,?_⟩
  · cases hb2 <;> omega
  · cases hb2 <;> omega
  · exact combined


#print axioms canonical_right_extension_safe
