import u_to_s_endpoint

/- Constructive elimination of `Classical.choice` from `fixed_u_to_s_halting`
   and all supporting S-side halting equivalences.

   Two sources of `Classical.choice` existed in the upstream chain:
   1. `by_cases` on halting in `full_root_selector.lean`, `plain_tape.lean`,
      and `u_step_refinement.lean`;
   2. `↓reduceIte` inside `pending_right_done_plan` / `pending_left_done_plan`
      in `controller_plan.lean`.

   Here we replace both constructively: `pending_*_done_plan` reduces by
   `Nat.beq_refl`, and reverse halting runs `uRunFor (k + 1)` / `plainRunFor (k + 1)`
   so a non-halting prefix of length `k + 1` lifts via the `6 * n ≤ m` native
   lower bound to a closed-flag checkpoint past `k`, contradicting
   `halt_cannot_precede_closed_checkpoint` with zero `Classical.choice`. -/

theorem nat_beq_self (q : Nat) : (q == q) = true :=
  decide_eq_true rfl

theorem constructive_pending_right_done_plan (src dst : List Bool) (b old : Bool) (q : Nat) :
    pendingPlan src dst ⟨b, .movingRight, q⟩ (some ⟨old, .active, q⟩) = .append src ⟨b, .off, 0⟩ := by
  dsimp [pendingPlan, isMoving]
  rw [nat_beq_self q]
  rfl

theorem constructive_pending_left_done_plan (src dst : List Bool) (b old : Bool) (q : Nat) :
    pendingPlan src dst ⟨b, .movingLeft, q⟩ (some ⟨old, .active, q⟩) = .append src ⟨b, .off, 0⟩ := by
  dsimp [pendingPlan, isMoving]
  rw [nat_beq_self q]
  rfl

theorem constructive_canonical_right_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (source destination : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term)
    (q : Fin 132) (bit written : Bool) (nextState : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : AllOff before) (hsource : ActiveAt source q bit)
    (hdestination : (decodedCell destination).status = .off) (hafter : AllOff after)
    (hrule : program q bit = some ⟨written, nextState, .right⟩) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    ∃ k, 18 ≤ k ∧ k ≤ 504 ∧
      FullSelectorTrace program k (canonicalRoot (before ++ source :: destination :: after) d flag hubJunk)
        (canonicalRoot (before ++ (source ++ [pending, off]) :: (destination ++ [active]) :: after) d flag hubJunk) := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let sd := d + before.length + 1
  let dd := d + before.length + 2
  let sj := depthJunk (d + before.length)
  let dj := depthJunk (d + before.length + 1)
  let tail := canonicalTape after (d + before.length + 2)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending, off]) sd
  let d0 := concreteVersion destination dd
  let d1 := concreteVersion (destination ++ [active]) dd
  let srcPath := prefixPath earlier
  let dstPath := srcPath ++ nextCellPath
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  have hsourceStatus : (decodedCell source).status = .active := by rw [hsource]
  obtain ⟨k1, k2, k3, t1, t2, t3, hb1, hb2, hb3, hp0, hp1, hp2, _, _, _⟩ :=
    right_move_in_seed_hub source destination sd dd tail sj dj earlier flag hubJunk hprefix written nextState
      hsourceStatus hdestination htail
  have hv : flagValue flag = false := by simp [flagValue, hflag]
  have hs0 : cellFromVersion s0 = ⟨bit, .active, q.val⟩ := by simpa [s0, concrete_version_decodes, ActiveAt] using hsource
  have hs1 : cellFromVersion s1 = pending.val := by simp [s1, concrete_version_decodes, decoded_cell_append]
  have hd0 : cellFromVersion d0 = decodedCell destination := concrete_version_decodes destination dd
  have hd1 : cellFromVersion d1 = active.val := by simp [d1, concrete_version_decodes, decoded_cell_append]
  have hpriority1 : priorityConcretePath (tapeAroundVersion earlier s0 (frameTerm d0 tail dj) sj) = .active srcPath := by
    rw [tape_around_adjacent]
    exact hp0
  have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
  have hplan1 : activePlan srcPath srcPath.isEmpty
      (program ⟨(cellFromVersion s0).state, hstate⟩ (cellFromVersion s0).bit) = .append srcPath pending.val := by
    have hq : (⟨(cellFromVersion s0).state, hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
    have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
    rw [hq, hbit, hrule]
    rfl
  have f1 := active_global_trace_is_full_selector program earlier (frameTerm d0 tail dj) sj s0 flag hubJunk pending.val
    hv hpriority1 hstate hplan1 (by simpa [encodedEntry, pending] using t1)
  have hpriority2 : priorityConcretePath (tapeAroundVersion (earlier ++ [(s1, sj)]) d0 tail dj) = .pending srcPath := by
    rw [← adjacent_contexts_stitch earlier s1 d0 tail sj dj, tape_around_adjacent]
    exact hp1
  have hsource2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
      readCellAt (tapeAroundVersion (earlier ++ [(s1, sj)]) v tail dj) srcPath = some pending.val := by
    intro v _
    rw [source_before_focused_cell_read, hs1]
  have hdest2 : pendingDestinationPath pending.val srcPath = some (prefixPath (earlier ++ [(s1, sj)])) := by
    rw [prefix_path_append_cell]
    rfl
  have htarget2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion (earlier ++ [(s1, sj)]) v tail dj) (prefixPath (earlier ++ [(s1, sj)])) = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion d0 := by
    intro v heq
    exact ⟨frameTerm v tail dj, v, tail, dj, term_at_tape_around_cell _ _ _ _, parse_frame _ _ _, heq⟩
  have hplan2 : pendingPlan srcPath (prefixPath (earlier ++ [(s1, sj)])) pending.val (some (cellFromVersion d0)) =
      .append (prefixPath (earlier ++ [(s1, sj)])) active.val := by
    simpa [pending, active, pendingRightCell, activeCellRecord, hd0] using
      pending_right_off_general srcPath (prefixPath (earlier ++ [(s1, sj)])) written nextState.val (decodedCell destination) hdestination
  have f2 := pending_global_trace_general program (earlier ++ [(s1, sj)]) tail dj d0 flag hubJunk
    active.val pending.val (cellFromVersion d0) srcPath (prefixPath (earlier ++ [(s1, sj)]))
    hv hpriority2 hsource2 hdest2 htarget2 hplan2 (by simpa [encodedEntry, active] using t2)
  have hpriority3 : priorityConcretePath (tapeAroundVersion earlier s1 (frameTerm d1 tail dj) sj) = .pending srcPath := by
    rw [tape_around_adjacent]
    exact hp2
  have hsource3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      readCellAt (tapeAroundVersion earlier v (frameTerm d1 tail dj) sj) srcPath = some pending.val := by
    intro v heq
    rw [read_cell_at_tape_around, heq, hs1]
  have hdest3 : pendingDestinationPath pending.val srcPath = some dstPath := rfl
  have htarget3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v (frameTerm d1 tail dj) sj) dstPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = active.val := by
    intro v _
    exact ⟨frameTerm d1 tail dj, d1, tail, dj, target_after_focused_cell_term _ _ _ _ _ _, parse_frame _ _ _, hd1⟩
  have hplan3 : pendingPlan srcPath dstPath pending.val (some active.val) = .append srcPath off.val :=
    constructive_pending_right_done_plan srcPath dstPath written (decodedCell destination).bit nextState.val
  have f3 := pending_global_trace_general program earlier (frameTerm d1 tail dj) sj s1 flag hubJunk
    off.val pending.val active.val srcPath dstPath hv hpriority3 hsource3 hdest3 htarget3 hplan3
    (by simpa [encodedEntry, off] using t3)
  rw [← adjacent_contexts_stitch earlier s1 d0 tail sj dj, ← adjacent_contexts_stitch earlier s1 d1 tail sj dj] at f2
  have combined := full_selector_trace_trans f1 (full_selector_trace_trans f2 f3)
  have hstart : tapeAroundVersion earlier s0 (frameTerm d0 tail dj) sj = canonicalTape (before ++ source :: destination :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before source destination after d).symm
  have hend : tapeAroundVersion earlier s2 (frameTerm d1 tail dj) sj =
      canonicalTape (before ++ (source ++ [pending, off]) :: (destination ++ [active]) :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before (source ++ [pending, off]) (destination ++ [active]) after d).symm
  rw [hstart, hend] at combined
  refine ⟨k1 + (k2 + k3), ?_, ?_, combined⟩ <;> omega

theorem constructive_canonical_left_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (destination source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term)
    (q : Fin 132) (bit written : Bool) (nextState : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : AllOff before) (hdestination : (decodedCell destination).status = .off)
    (hsource : ActiveAt source q bit) (hafter : AllOff after)
    (hrule : program q bit = some ⟨written, nextState, .left⟩) :
    let pending := pendingLeftCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    ∃ k, 18 ≤ k ∧ k ≤ 504 ∧
      FullSelectorTrace program k (canonicalRoot (before ++ destination :: source :: after) d flag hubJunk)
        (canonicalRoot (before ++ (destination ++ [active]) :: (source ++ [pending, off]) :: after) d flag hubJunk) := by
  let pending := pendingLeftCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let dd := d + before.length + 1
  let sd := d + before.length + 2
  let dj := depthJunk (d + before.length)
  let sj := depthJunk (d + before.length + 1)
  let tail := canonicalTape after (d + before.length + 2)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending, off]) sd
  let d0 := concreteVersion destination dd
  let d1 := concreteVersion (destination ++ [active]) dd
  let dstPath := prefixPath earlier
  let srcPath := dstPath ++ nextCellPath
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  have hsourceStatus : (decodedCell source).status = .active := by rw [hsource]
  obtain ⟨k1, k2, k3, t1, t2, t3, hb1, hb2, hb3, hp0, hp1, hp2, _, _, _⟩ :=
    left_move_in_seed_hub source destination sd dd tail sj dj earlier flag hubJunk hprefix written nextState
      hsourceStatus hdestination htail
  have hv : flagValue flag = false := by simp [flagValue, hflag]
  have hs0 : cellFromVersion s0 = ⟨bit, .active, q.val⟩ := by simpa [s0, concrete_version_decodes, ActiveAt] using hsource
  have hs1 : cellFromVersion s1 = pending.val := by simp [s1, concrete_version_decodes, decoded_cell_append]
  have hd0 : cellFromVersion d0 = decodedCell destination := concrete_version_decodes destination dd
  have hd1 : cellFromVersion d1 = active.val := by simp [d1, concrete_version_decodes, decoded_cell_append]
  have hsrc1 : prefixPath (earlier ++ [(d0, dj)]) = srcPath := by
    simpa [srcPath, dstPath] using prefix_path_append_cell earlier d0 dj
  have hpriority1 : priorityConcretePath (tapeAroundVersion (earlier ++ [(d0, dj)]) s0 tail sj) =
      .active (prefixPath (earlier ++ [(d0, dj)])) := by
    rw [← adjacent_contexts_stitch earlier d0 s0 tail dj sj, tape_around_adjacent, hsrc1]
    exact hp0
  have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
  have hplan1 : activePlan (prefixPath (earlier ++ [(d0, dj)])) (prefixPath (earlier ++ [(d0, dj)])).isEmpty
      (program ⟨(cellFromVersion s0).state, hstate⟩ (cellFromVersion s0).bit) =
        .append (prefixPath (earlier ++ [(d0, dj)])) pending.val := by
    have hq : (⟨(cellFromVersion s0).state, hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
    have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
    have hempty : (prefixPath (earlier ++ [(d0, dj)])).isEmpty = false := by
      rw [hsrc1]
      simp [srcPath, nextCellPath]
    rw [hq, hbit, hrule, hempty]
    rfl
  have f1 := active_global_trace_is_full_selector program (earlier ++ [(d0, dj)]) tail sj s0 flag hubJunk pending.val
    hv hpriority1 hstate hplan1 (by simpa [encodedEntry, pending] using t1)
  have hpriority2 : priorityConcretePath (tapeAroundVersion earlier d0 (frameTerm s1 tail sj) dj) = .pending srcPath := by
    rw [tape_around_adjacent]
    exact hp1
  have hsource2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
      readCellAt (tapeAroundVersion earlier v (frameTerm s1 tail sj) dj) srcPath = some pending.val := by
    intro v _
    rw [show srcPath = prefixPath earlier ++ nextCellPath from rfl, source_after_focused_cell_read, hs1]
  have hdest2 : pendingDestinationPath pending.val srcPath = some (prefixPath earlier) := by
    simpa [srcPath, dstPath, pending, pendingLeftCell] using pending_left_destination (prefixPath earlier) written nextState.val
  have htarget2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v (frameTerm s1 tail sj) dj) (prefixPath earlier) = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion d0 := by
    intro v heq
    exact ⟨frameTerm v (frameTerm s1 tail sj) dj, v, frameTerm s1 tail sj, dj,
      term_at_tape_around_cell _ _ _ _, parse_frame _ _ _, heq⟩
  have hplan2 : pendingPlan srcPath (prefixPath earlier) pending.val (some (cellFromVersion d0)) =
      .append (prefixPath earlier) active.val := by
    simpa [pending, active, pendingLeftCell, activeCellRecord, hd0] using
      pending_left_off_general srcPath (prefixPath earlier) written nextState.val (decodedCell destination) hdestination
  have f2 := pending_global_trace_general program earlier (frameTerm s1 tail sj) dj d0 flag hubJunk
    active.val pending.val (cellFromVersion d0) srcPath (prefixPath earlier)
    hv hpriority2 hsource2 hdest2 htarget2 hplan2 (by simpa [encodedEntry, active] using t2)
  have hsrc3 : prefixPath (earlier ++ [(d1, dj)]) = srcPath := by
    simpa [srcPath, dstPath] using prefix_path_append_cell earlier d1 dj
  have hpriority3 : priorityConcretePath (tapeAroundVersion (earlier ++ [(d1, dj)]) s1 tail sj) = .pending srcPath := by
    rw [← adjacent_contexts_stitch earlier d1 s1 tail dj sj, tape_around_adjacent]
    exact hp2
  have hsource3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      readCellAt (tapeAroundVersion (earlier ++ [(d1, dj)]) v tail sj) srcPath = some pending.val := by
    intro v heq
    rw [← hsrc3, read_cell_at_tape_around, heq, hs1]
  have hdest3 : pendingDestinationPath pending.val srcPath = some dstPath := by
    simpa [srcPath, dstPath, pending, pendingLeftCell] using pending_left_destination (prefixPath earlier) written nextState.val
  have htarget3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion (earlier ++ [(d1, dj)]) v tail sj) dstPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = active.val := by
    intro v _
    refine ⟨frameTerm d1 (frameTerm v tail sj) dj, d1, frameTerm v tail sj, dj, ?_, parse_frame _ _ _, hd1⟩
    rw [prepend_tape_around]
    simpa [tapeAroundVersion, dstPath] using term_at_prepend_tape earlier (frameTerm d1 (frameTerm v tail sj) dj)
  have hplan3 : pendingPlan srcPath dstPath pending.val (some active.val) =
      .append (prefixPath (earlier ++ [(d1, dj)])) off.val := by
    rw [hsrc3]
    exact constructive_pending_left_done_plan srcPath dstPath written (decodedCell destination).bit nextState.val
  have f3 := pending_global_trace_general program (earlier ++ [(d1, dj)]) tail sj s1 flag hubJunk
    off.val pending.val active.val srcPath dstPath hv hpriority3 hsource3 hdest3 htarget3 hplan3
    (by simpa [encodedEntry, off] using t3)
  rw [← adjacent_contexts_stitch earlier d0 s0 tail dj sj, ← adjacent_contexts_stitch earlier d0 s1 tail dj sj] at f1
  rw [← adjacent_contexts_stitch earlier d1 s1 tail dj sj, ← adjacent_contexts_stitch earlier d1 s2 tail dj sj] at f3
  have combined := full_selector_trace_trans f1 (full_selector_trace_trans f2 f3)
  have hstart : tapeAroundVersion earlier d0 (frameTerm s0 tail sj) dj = canonicalTape (before ++ destination :: source :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before destination source after d).symm
  have hend : tapeAroundVersion earlier d1 (frameTerm s2 tail sj) dj =
      canonicalTape (before ++ (destination ++ [active]) :: (source ++ [pending, off]) :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before (destination ++ [active]) (source ++ [pending, off]) after d).symm
  rw [hstart, hend] at combined
  refine ⟨k1 + (k2 + k3), ?_, ?_, combined⟩ <;> omega

theorem constructive_canonical_right_extension_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (d : Nat) (flag hubJunk : Term) (q : Fin 132) (bit written : Bool) (nextState : Fin 132)
    (hflag : parseFrame flag = none) (hbefore : AllOff before) (hsource : ActiveAt source q bit)
    (hrule : program q bit = some ⟨written, nextState, .right⟩) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord false nextState
    let off := offCellRecord written
    ∃ k, 24 ≤ k ∧ k ≤ 511 ∧
      FullSelectorTrace program k (canonicalRoot (before ++ [source]) d flag hubJunk)
        (canonicalRoot (before ++ [source ++ [pending, off], [active]]) d flag hubJunk) := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord false nextState
  let off := offCellRecord written
  let earlier := canonicalPrefix before d
  let sd := d + before.length + 1
  let td := d + before.length + 1
  let sj := depthJunk (d + before.length)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [pending]) sd
  let s2 := concreteVersion (source ++ [pending, off]) sd
  let blank := depthBase (td + 1)
  let d1 := concreteVersion [active] (td + 1)
  let cell0 := frameTerm blank blank (depthJunk td)
  let cell1 := frameTerm d1 blank (depthJunk td)
  let srcPath := prefixPath earlier
  let dstPath := srcPath ++ nextCellPath
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have hsourceStatus : (decodedCell source).status = .active := by rw [hsource]
  obtain ⟨k1, k2, k3, k4, t1, t2, t3, t4, hb1, hb2, hb3, hb4, hp0, _, _, readActive⟩ :=
    right_extension_in_seed_hub source sd td earlier sj flag hubJunk written nextState hprefix hsourceStatus
  have hv : flagValue flag = false := by simp [flagValue, hflag]
  have hs0 : cellFromVersion s0 = ⟨bit, .active, q.val⟩ := by simpa [s0, concrete_version_decodes, ActiveAt] using hsource
  have hs1 : cellFromVersion s1 = pending.val := by simp [s1, concrete_version_decodes, decoded_cell_append]
  have hblank : cellFromVersion blank = defaultCell := depth_child_is_blank (td + 1)
  have hd1 : cellFromVersion d1 = active.val := by simpa [d1, concreteVersion, List.map_append] using readActive
  have hpriority1 : priorityConcretePath (tapeAroundVersion earlier s0 (depthBase td) sj) = .active srcPath := by
    rw [tape_around_single]
    exact hp0
  have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
  have hplan1 : activePlan srcPath srcPath.isEmpty
      (program ⟨(cellFromVersion s0).state, hstate⟩ (cellFromVersion s0).bit) = .append srcPath pending.val := by
    have hq : (⟨(cellFromVersion s0).state, hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
    have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
    rw [hq, hbit, hrule]
    rfl
  have f1 := active_global_trace_is_full_selector program earlier (depthBase td) sj s0 flag hubJunk pending.val
    hv hpriority1 hstate hplan1 (by simpa [encodedEntry, pending] using t1)
  have f2 := pending_tail_trace_is_full_selector program earlier s1 sj flag hubJunk written nextState.val
    hv (by simpa [pending, pendingRightCell] using hs1) t2
  have hmoving : isMoving (cellFromVersion s1).status = true := by rw [hs1]; rfl
  have hpending := prefixed_single_pending_priority earlier s1 cell0 sj hprefix hmoving
  have hpriority3 : priorityConcretePath (tapeAroundVersion (earlier ++ [(s1, sj)]) blank blank (depthJunk td)) = .pending srcPath := by
    rw [← adjacent_contexts_stitch earlier s1 blank blank sj (depthJunk td), tape_around_adjacent]
    exact hpending
  have hsource3 : ∀ v, cellFromVersion v = cellFromVersion blank →
      readCellAt (tapeAroundVersion (earlier ++ [(s1, sj)]) v blank (depthJunk td)) srcPath = some pending.val := by
    intro v _
    rw [source_before_focused_cell_read, hs1]
  have hdest3 : pendingDestinationPath pending.val srcPath = some (prefixPath (earlier ++ [(s1, sj)])) := by
    rw [prefix_path_append_cell]
    rfl
  have htarget3 : ∀ v, cellFromVersion v = cellFromVersion blank →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion (earlier ++ [(s1, sj)]) v blank (depthJunk td))
          (prefixPath (earlier ++ [(s1, sj)])) = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion blank := by
    intro v heq
    exact ⟨frameTerm v blank (depthJunk td), v, blank, depthJunk td, term_at_tape_around_cell _ _ _ _, parse_frame _ _ _, heq⟩
  have hplan3 : pendingPlan srcPath (prefixPath (earlier ++ [(s1, sj)])) pending.val (some (cellFromVersion blank)) =
      .append (prefixPath (earlier ++ [(s1, sj)])) active.val := by
    rw [hblank]
    exact pending_right_off_plan srcPath (prefixPath (earlier ++ [(s1, sj)])) written false nextState.val
  have f3 := pending_global_trace_general program (earlier ++ [(s1, sj)]) blank (depthJunk td) blank flag hubJunk
    active.val pending.val (cellFromVersion blank) srcPath (prefixPath (earlier ++ [(s1, sj)]))
    hv hpriority3 hsource3 hdest3 htarget3 hplan3 (by simpa [encodedEntry, active] using t3)
  have hpriority4 : priorityConcretePath (tapeAroundVersion earlier s1 cell1 sj) = .pending srcPath := by
    rw [tape_around_single]
    exact prefixed_single_pending_priority earlier s1 cell1 sj hprefix hmoving
  have hsource4 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      readCellAt (tapeAroundVersion earlier v cell1 sj) srcPath = some pending.val := by
    intro v heq
    rw [read_cell_at_tape_around, heq, hs1]
  have hdest4 : pendingDestinationPath pending.val srcPath = some dstPath := rfl
  have htarget4 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v cell1 sj) dstPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = active.val := by
    intro v _
    exact ⟨cell1, d1, blank, depthJunk td, target_after_focused_cell_term _ _ _ _ _ _, parse_frame _ _ _, hd1⟩
  have hplan4 : pendingPlan srcPath dstPath pending.val (some active.val) = .append srcPath off.val :=
    constructive_pending_right_done_plan srcPath dstPath written false nextState.val
  have f4 := pending_global_trace_general program earlier cell1 sj s1 flag hubJunk
    off.val pending.val active.val srcPath dstPath hv hpriority4 hsource4 hdest4 htarget4 hplan4
    (by simpa [encodedEntry, off] using t4)
  rw [← tape_around_single earlier s1 (depthBase td) sj, ← tape_around_single earlier s1 cell0 sj] at f2
  rw [show cell0 = frameTerm blank blank (depthJunk td) from rfl,
      adjacent_contexts_stitch earlier s1 blank blank sj (depthJunk td)] at f2
  rw [show cell1 = frameTerm d1 blank (depthJunk td) from rfl,
      adjacent_contexts_stitch earlier s1 d1 blank sj (depthJunk td)] at f4
  have combined := full_selector_trace_trans f1 (full_selector_trace_trans f2 (full_selector_trace_trans f3 f4))
  have hstart : tapeAroundVersion earlier s0 (depthBase td) sj = canonicalTape (before ++ [source]) d := by
    simpa [td, canonical_tape_nil] using (canonical_single_decompose before source [] d).symm
  have hend : tapeAroundVersion earlier s2 (frameTerm d1 blank (depthJunk td)) sj =
      canonicalTape (before ++ [source ++ [pending, off], [active]]) d := by
    rw [tape_around_adjacent]
    simpa [td, blank, d1, canonical_tape_nil] using
      (canonical_adjacent_decompose before (source ++ [pending, off]) [active] [] d).symm
  rw [hstart, hend] at combined
  refine ⟨k1 + (k2 + (k3 + k4)), ?_, ?_, combined⟩
  · cases hb2 <;> omega
  · cases hb2 <;> omega

theorem constructive_source_transition_full_selector (program : BinaryProgram)
    {start finish : List (List UniversalCell)}
    (h : SourceTransition program start finish) (d : Nat) (flag hubJunk : Term)
    (hflag : parseFrame flag = none) :
    ∃ k, 6 ≤ k ∧ k ≤ 511 ∧
      FullSelectorTrace program k (canonicalRoot start d flag hubJunk) (canonicalRoot finish d flag hubJunk) := by
  cases h with
  | stay before source after q bit inst hbefore hsource hafter hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | left => cases hdir
          | right => cases hdir
          | stay =>
              obtain ⟨k, lo, hi, trace⟩ := canonical_stay_full_selector program before source after d flag hubJunk
                q bit written nextState hflag hbefore hsource hafter hrule
              exact ⟨k, lo, by omega, trace⟩
  | leftBoundary source after q bit inst hsource hafter hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | stay => cases hdir
          | right => cases hdir
          | left =>
              have hoff : AllOff ([] : List (List UniversalCell)) := by intro cell hc; simp at hc
              obtain ⟨k, lo, hi, trace⟩ := canonical_left_boundary_full_selector program [] source after d flag hubJunk
                q bit written nextState hflag rfl hoff hsource hafter hrule
              exact ⟨k, lo, by omega, trace⟩
  | rightExisting before source destination after q bit inst hbefore hsource hdest hafter hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | stay => cases hdir
          | left => cases hdir
          | right =>
              obtain ⟨k, lo, hi, trace⟩ := constructive_canonical_right_full_selector program before source destination
                after d flag hubJunk q bit written nextState hflag hbefore hsource hdest hafter hrule
              exact ⟨k, by omega, by omega, trace⟩
  | rightExtend before source q bit inst hbefore hsource hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | stay => cases hdir
          | left => cases hdir
          | right =>
              obtain ⟨k, lo, hi, trace⟩ := constructive_canonical_right_extension_full_selector program before source
                d flag hubJunk q bit written nextState hflag hbefore hsource hrule
              exact ⟨k, by omega, hi, trace⟩
  | leftExisting before destination source after q bit inst hbefore hdest hsource hafter hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | stay => cases hdir
          | right => cases hdir
          | left =>
              obtain ⟨k, lo, hi, trace⟩ := constructive_canonical_left_full_selector program before destination source
                after d flag hubJunk q bit written nextState hflag hbefore hdest hsource hafter hrule
              exact ⟨k, by omega, by omega, trace⟩

theorem constructive_finite_source_run_full_selector (program : BinaryProgram) {n : Nat}
    {start finish : List (List UniversalCell)} (run : SourceRun program n start finish)
    (d : Nat) (flag hubJunk : Term) (hflag : parseFrame flag = none) :
    ∃ k, 6 * n ≤ k ∧ k ≤ 511 * n ∧
      FullSelectorTrace program k (canonicalRoot start d flag hubJunk) (canonicalRoot finish d flag hubJunk) := by
  induction run with
  | zero _ => exact ⟨0, by simp, by simp, FullSelectorTrace.zero _⟩
  | @next n a b c hstep _ ih =>
      obtain ⟨k1, lo1, hi1, first⟩ := constructive_source_transition_full_selector program hstep d flag hubJunk hflag
      obtain ⟨k2, lo2, hi2, remaining⟩ := ih
      refine ⟨k1 + k2, ?_, ?_, full_selector_trace_trans first remaining⟩ <;> omega

theorem constructive_finite_run_then_halt_full_selector (program : BinaryProgram)
    {n : Nat} {start : List (List UniversalCell)}
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (run : SourceRun program n start (before ++ source :: after))
    (q : Fin 132) (bit : Bool) (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after)
    (hstop : program q bit = none) (d flagDepth : Nat) (hubJunk : Term) :
    let tape := canonicalTape (before ++ source :: after) d
    let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2
    ∃ k, 6 * n + 6 ≤ k ∧ k ≤ 511 * n + 7 ∧
      FullSelectorTrace program k (canonicalRoot start d (depthBase flagDepth) hubJunk) (seedHubRoot flagOpen tape hubJunk) ∧
      rootHalt (seedHubRoot flagOpen tape hubJunk) = true := by
  obtain ⟨k1, lo1, hi1, hfirst⟩ :=
    constructive_finite_source_run_full_selector program run d (depthBase flagDepth) hubJunk (depth_base_closed flagDepth)
  obtain ⟨k2, lo2, hi2, hlast, hobserved⟩ :=
    stopped_boundary_full_selector program before source after q bit hb hs ha hstop d flagDepth hubJunk
  refine ⟨k1 + k2, ?_, ?_, full_selector_trace_trans hfirst hlast, hobserved⟩ <;> omega

/-- Run `uNext` for up to `fuel` steps, returning `inl ⟨steps, final⟩` as soon as
    `uNext final = none`, or `inr future` after `fuel` defined transitions. -/
def uRunFor : Nat → UConfig → Sum (Nat × UConfig) UConfig
  | 0, u => .inr u
  | fuel + 1, u =>
      match uNext u with
      | none => .inl (0, u)
      | some u' =>
          match uRunFor fuel u' with
          | .inl (n, final) => .inl (n + 1, final)
          | .inr future => .inr future

theorem uRunFor_spec (fuel : Nat) (u : UConfig) :
    match uRunFor fuel u with
    | .inl (n, final) => n ≤ fuel ∧ URun n u final ∧ uNext final = none
    | .inr future => URun fuel u future := by
  induction fuel generalizing u with
  | zero =>
      simp [uRunFor]
      exact URun.zero u
  | succ fuel ih =>
      cases hs : uNext u with
      | none =>
          simp [uRunFor, hs]
          exact URun.zero u
      | some u' =>
          have ih' := ih u'
          cases hr : uRunFor fuel u' with
          | inl pair =>
              rcases pair with ⟨n, final⟩
              rw [hr] at ih'
              rcases ih' with ⟨hle, hrun, hstop⟩
              simp [uRunFor, hs, hr]
              exact ⟨hle, URun.next hs hrun, hstop⟩
          | inr future =>
              rw [hr] at ih'
              simp [uRunFor, hs, hr]
              exact URun.next hs ih'

theorem u_bounded_stop_or_run (steps : Nat) (start : UConfig) :
    UEventuallyStops start ∨ ∃ future, URun steps start future := by
  have hspec := uRunFor_spec steps start
  cases hr : uRunFor steps start with
  | inl pair =>
      rcases pair with ⟨n, final⟩
      rw [hr] at hspec
      exact Or.inl ⟨n, final, hspec.2.1, hspec.2.2⟩
  | inr future =>
      rw [hr] at hspec
      exact Or.inr ⟨future, hspec⟩

/-- Computable bounded runner for `plainNext`. -/
def plainRunFor (program : BinaryProgram) : Nat → PlainConfig → Sum (Nat × PlainConfig) PlainConfig
  | 0, c => .inr c
  | fuel + 1, c =>
      match plainNext program c with
      | none => .inl (0, c)
      | some c' =>
          match plainRunFor program fuel c' with
          | .inl (n, final) => .inl (n + 1, final)
          | .inr future => .inr future

theorem plainRunFor_spec (program : BinaryProgram) (fuel : Nat) (c : PlainConfig) :
    match plainRunFor program fuel c with
    | .inl (n, final) => n ≤ fuel ∧ PlainRun program n c final ∧ plainNext program final = none
    | .inr future => PlainRun program fuel c future := by
  induction fuel generalizing c with
  | zero =>
      simp [plainRunFor]
      exact PlainRun.zero c
  | succ fuel ih =>
      cases hs : plainNext program c with
      | none =>
          simp [plainRunFor, hs]
          exact PlainRun.zero c
      | some c' =>
          have ih' := ih c'
          cases hr : plainRunFor program fuel c' with
          | inl pair =>
              rcases pair with ⟨n, final⟩
              rw [hr] at ih'
              rcases ih' with ⟨hle, hrun, hstop⟩
              simp [plainRunFor, hs, hr]
              exact ⟨hle, PlainRun.next hs hrun, hstop⟩
          | inr future =>
              rw [hr] at ih'
              simp [plainRunFor, hs, hr]
              exact PlainRun.next hs ih'

theorem plain_bounded_stop_or_run (program : BinaryProgram) (steps : Nat) (start : PlainConfig) :
    PlainEventuallyStops program start ∨ ∃ future, PlainRun program steps start future := by
  have hspec := plainRunFor_spec program steps start
  cases hr : plainRunFor program steps start with
  | inl pair =>
      rcases pair with ⟨n, final⟩
      rw [hr] at hspec
      exact Or.inl ⟨n, final, hspec.2.1, hspec.2.2⟩
  | inr future =>
      rw [hr] at hspec
      exact Or.inr ⟨future, hspec⟩

theorem source_bounded_stop_or_run (program : BinaryProgram) (steps : Nat)
    (start : List (List UniversalCell)) (hvalid : WellFormed start) :
    SourceEventuallyStops program start ∨ ∃ future, SourceRun program steps start future := by
  induction steps with
  | zero => exact Or.inr ⟨start, SourceRun.zero _⟩
  | succ n ih =>
      cases ih with
      | inl hstop => exact Or.inl hstop
      | inr hrun =>
          obtain ⟨mid, run⟩ := hrun
          have hv : WellFormed mid := source_run_preserves_well_formed program run hvalid
          obtain ⟨before, source, after, q, bit, hmid, hbefore, hsource, hafter⟩ := hv
          cases hrule : program q bit with
          | none =>
              exact Or.inl ⟨n, mid, run, before, source, after, q, bit, hmid, hbefore, hsource, hafter, hrule⟩
          | some inst =>
              obtain ⟨next, hstep⟩ := defined_source_step_exists program before source after q bit inst
                hbefore hsource hafter hrule
              rw [← hmid] at hstep
              exact Or.inr ⟨next, source_run_snoc program run hstep⟩

theorem canonical_root_closed_halt (cells : List (List UniversalCell)) (d flagDepth : Nat) (hubJunk : Term) :
    rootHalt (canonicalRoot cells d (depthBase flagDepth) hubJunk) = false := by
  unfold canonicalRoot
  rw [root_halt_seed]
  exact halt_field_closed_observation (depthBase flagDepth) _ hubJunk (depth_base_closed flagDepth)

theorem constructive_source_halting_iff_selected_halt_event
    (program : BinaryProgram) (start : List (List UniversalCell))
    (hvalid : WellFormed start) (d flagDepth : Nat) (hubJunk : Term) :
    SourceEventuallyStops program start ↔
      ∃ k reached,
        FullSelectorTrace program k (canonicalRoot start d (depthBase flagDepth) hubJunk) reached ∧
        rootHalt reached = true := by
  constructor
  · intro hstop
    obtain ⟨n, finish, run, before, source, after, q, bit, hfinish, hbefore, hsource, hafter, hrule⟩ := hstop
    subst finish
    obtain ⟨k, _, _, htrace, hhalt⟩ :=
      constructive_finite_run_then_halt_full_selector program before source after run q bit
        hbefore hsource hafter hrule d flagDepth hubJunk
    exact ⟨k, _, htrace, hhalt⟩
  · intro ⟨k, reached, htrace, hhalt⟩
    rcases source_bounded_stop_or_run program (k + 1) start hvalid with hstop | ⟨future, hrun⟩
    · exact hstop
    · obtain ⟨m, hlower, _, hcheckpoint⟩ :=
        constructive_finite_source_run_full_selector program hrun d (depthBase flagDepth) hubJunk
          (depth_base_closed flagDepth)
      have hle : k ≤ m := by omega
      have hclosed := canonical_root_closed_halt future d flagDepth hubJunk
      exact False.elim (halt_cannot_precede_closed_checkpoint program k m _ reached _ htrace hhalt hcheckpoint hle hclosed)

theorem constructive_plain_halting_iff_selected_halt
    (program : BinaryProgram) (initial : PlainConfig)
    (d flagDepth : Nat) (hubJunk : Term) :
    PlainEventuallyStops program initial ↔
      ∃ k reached,
        FullSelectorTrace program k
          (canonicalRoot (initialRecords initial) d (depthBase flagDepth) hubJunk) reached ∧
        rootHalt reached = true := by
  have hrep := initial_records_represent initial
  constructor
  · intro ⟨n, final, run, hfinal⟩
    obtain ⟨finalRecords, hrun, hrepFinal⟩ := plain_run_lifts program run (initialRecords initial) hrep
    have hstopped := stopped_plain_config_lifts program final finalRecords hrepFinal hfinal
    exact (constructive_source_halting_iff_selected_halt_event program (initialRecords initial)
      (plain_rep_well_formed _ initial hrep) d flagDepth hubJunk).mp ⟨n, finalRecords, hrun, hstopped⟩
  · intro ⟨k, reached, htrace, hhalt⟩
    rcases plain_bounded_stop_or_run program (k + 1) initial with hstop | ⟨future, hplainRun⟩
    · exact hstop
    · obtain ⟨futureRecords, hsourceRun, _⟩ := plain_run_lifts program hplainRun (initialRecords initial) hrep
      obtain ⟨m, hlower, _, hcheckpoint⟩ :=
        constructive_finite_source_run_full_selector program hsourceRun d (depthBase flagDepth) hubJunk
          (depth_base_closed flagDepth)
      have hle : k ≤ m := by omega
      have hclosed := canonical_root_closed_halt futureRecords d flagDepth hubJunk
      exact False.elim (halt_cannot_precede_closed_checkpoint program k m _ reached _ htrace hhalt hcheckpoint hle hclosed)

theorem constructive_u_halt_iff_binary_halt (initial : UConfig) :
    UEventuallyStops initial ↔ PlainEventuallyStops fixedBinaryProgram (encodeUConfig initial) := by
  constructor
  · exact u_halt_implies_binary_halt initial
  · intro ⟨n, final, hrun, hstop⟩
    rcases u_bounded_stop_or_run (n + 1) initial with hu | ⟨uFuture, urun⟩
    · exact hu
    · obtain ⟨binFuture, hbinRun, _⟩ := u_run_refines_binary urun (encodeUConfig initial) (plain_eq_refl _)
      have heq : 10 * (n + 1) = n + (1 + (9 * n + 9)) := by omega
      rw [heq] at hbinRun
      obtain ⟨middle, hprefix, hsuffix⟩ := plain_run_split fixedBinaryProgram n (1 + (9 * n + 9)) hbinRun
      have hsame : final = middle := plain_run_unique fixedBinaryProgram hrun middle hprefix
      subst middle
      have h1 : 1 + (9 * n + 9) = (9 * n + 9) + 1 := by omega
      rw [h1] at hsuffix
      cases hsuffix with
      | next hstep _ =>
          rw [hstop] at hstep
          cases hstep

theorem constructive_fixed_u_halt_iff_selected_s_event
    (initial : UConfig) (d flagDepth : Nat) (hubJunk : Term) :
    UEventuallyStops initial ↔
      ∃ k reached,
        FullSelectorTrace fixedBinaryProgram k
          (canonicalRoot (initialRecords (encodeUConfig initial)) d (depthBase flagDepth) hubJunk) reached ∧
        rootHalt reached = true := by
  constructor
  · intro hu
    exact (constructive_plain_halting_iff_selected_halt fixedBinaryProgram (encodeUConfig initial)
      d flagDepth hubJunk).mp (u_halt_implies_binary_halt initial hu)
  · intro ⟨k, reached, htrace, hhalt⟩
    rcases u_bounded_stop_or_run (k + 1) initial with hu | ⟨uFuture, urun⟩
    · exact hu
    · obtain ⟨binFuture, hplainRun, _⟩ :=
        u_run_refines_binary urun (encodeUConfig initial) (plain_eq_refl _)
      obtain ⟨sourceFuture, hsourceRun, _⟩ :=
        plain_run_lifts fixedBinaryProgram hplainRun
          (initialRecords (encodeUConfig initial)) (initial_records_represent _)
      obtain ⟨m, hlower, _, hcheckpoint⟩ :=
        constructive_finite_source_run_full_selector fixedBinaryProgram hsourceRun d (depthBase flagDepth) hubJunk
          (depth_base_closed flagDepth)
      have hle : k ≤ m := by omega
      have hclosed := canonical_root_closed_halt sourceFuture d flagDepth hubJunk
      exact False.elim (halt_cannot_precede_closed_checkpoint fixedBinaryProgram k m _ reached _
        htrace hhalt hcheckpoint hle hclosed)

theorem constructive_fixed_u_to_s_halting (initial : UConfig) :
    UEventuallyStops initial ↔
      ∃ k reached, FullSelectorTrace fixedBinaryProgram k (sEncodeU initial) reached ∧ rootHalt reached = true :=
  constructive_fixed_u_halt_iff_selected_s_event initial 1 1 (depthJunk 0)

#print axioms uRunFor_spec
#print axioms constructive_finite_source_run_full_selector
#print axioms constructive_finite_run_then_halt_full_selector
#print axioms constructive_source_halting_iff_selected_halt_event
#print axioms constructive_plain_halting_iff_selected_halt
#print axioms constructive_u_halt_iff_binary_halt
#print axioms constructive_fixed_u_halt_iff_selected_s_event
#print axioms constructive_fixed_u_to_s_halting
