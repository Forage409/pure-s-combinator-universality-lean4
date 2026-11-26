import source_simulation

/- A single stateless selector on the whole pure-S root. All addresses are
   physical occurrence-tree paths. Its all-input correctness theorem is an
   outstanding obligation; malformed inputs may return none. -/

def rootHubPath : List Bool := [true]
def hubFlagPath : List Bool := [true,false,true]
def rootTapePath : List Bool := [true,true,false,true]
def cellVersionPath : List Bool := [false,true]
def nextCellPath : List Bool := [true,false,true]

def selectOpeningAt (root : Term) (path : List Bool) : Option (List Bool) := do
  let focus ← termAt root path
  let rel ← nextOpeningAddress focus
  some (path ++ rel)

def selectVersionAt (root : Term) (path : List Bool) (record : Cell) : Option (List Bool) := do
  let version ← termAt root path
  let slot ← chooseSVersionTree 11 (encodeCellBits record (stateBits8 record.state)) version
  selectOpeningAt root (path ++ slot)

def readCellAt (tape : Term) (path : List Bool) : Option Cell := do
  let cell ← termAt tape path
  let (version,_,_) ← parseFrame cell
  some (cellFromVersion version)

def chooseCellWrite (root : Term) (cellPath : List Bool) (record : Cell) : Option (List Bool) :=
  selectVersionAt root (rootTapePath ++ cellPath ++ cellVersionPath) record

def chooseActive (program : BinaryProgram) (root : Term) (tape : Term) (cellPath : List Bool) : Option (List Bool) := do
  let cell ← readCellAt tape cellPath
  if h : cell.state < 132 then
    let q : Fin 132 := ⟨cell.state,h⟩
    match activePlan cellPath (cellPath.isEmpty) (program q cell.bit) with
    | .halt => selectOpeningAt root hubFlagPath
    | .append path record => chooseCellWrite root path record
    | _ => none
  else none

def parentCellPath (path : List Bool) : List Bool := path.take (path.length - 3)

def pendingDestinationPath (pending : Cell) (sourcePath : List Bool) : Option (List Bool) :=
  match pending.status with
  | .movingRight => some (sourcePath ++ nextCellPath)
  | .movingLeft => if sourcePath.isEmpty then none else some (parentCellPath sourcePath)
  | _ => none

def choosePending (root : Term) (tape : Term) (sourcePath : List Bool) : Option (List Bool) := do
  let pending ← readCellAt tape sourcePath
  let targetPath ← pendingDestinationPath pending sourcePath
  let targetTerm ← termAt tape targetPath
  let target := match parseFrame targetTerm with
    | none => none
    | some (version,_,_) => some (cellFromVersion version)
  match pendingPlan sourcePath targetPath pending target with
  | .openDestination path => selectOpeningAt root (rootTapePath ++ path)
  | .append path record => chooseCellWrite root path record
  | _ => none

def closedLeftFrontier : Term → List Bool
  | .app (.app .s left) (.app (.app .s _) _) => [false,true] ++ closedLeftFrontier left
  | _ => []

def fullRootSelector (program : BinaryProgram) (root : Term) : Option (List Bool) := do
  let hub ← termAt root rootHubPath
  let (flag,tape,_) ← parseFrame hub
  if flagValue flag then
    let path := hubFlagPath ++ closedLeftFrontier flag
    selectOpeningAt root path
  else
    match priorityConcretePath tape with
    | .pending path => choosePending root tape path
    | .active path => chooseActive program root tape path
    | .none => none

#print axioms fullRootSelector

theorem full_selector_active_branch (program : BinaryProgram) (flag tape junk : Term) (path : List Bool)
    (hflag : flagValue flag = false) (hpriority : priorityConcretePath tape = .active path) :
    fullRootSelector program (seedHubRoot flag tape junk) = chooseActive program (seedHubRoot flag tape junk) tape path := by
  simp [fullRootSelector,termAt,rootHubPath,seedHubRoot,parse_frame,hflag,hpriority]

theorem full_selector_pending_branch (program : BinaryProgram) (flag tape junk : Term) (path : List Bool)
    (hflag : flagValue flag = false) (hpriority : priorityConcretePath tape = .pending path) :
    fullRootSelector program (seedHubRoot flag tape junk) = choosePending (seedHubRoot flag tape junk) tape path := by
  simp [fullRootSelector,termAt,rootHubPath,seedHubRoot,parse_frame,hflag,hpriority]

theorem full_selector_halt_branch (program : BinaryProgram) (flag tape junk : Term)
    (hflag : flagValue flag = true) :
    fullRootSelector program (seedHubRoot flag tape junk) =
      selectOpeningAt (seedHubRoot flag tape junk) (hubFlagPath ++ closedLeftFrontier flag) := by
  simp [fullRootSelector,termAt,rootHubPath,seedHubRoot,parse_frame,hflag]

#print axioms full_selector_active_branch
#print axioms full_selector_pending_branch
#print axioms full_selector_halt_branch

theorem context_path_append (a b : List ProtectedFrame) :
    contextPath (a ++ b) = contextPath b ++ contextPath a := by
  induction a with
  | nil => simp [contextPath]
  | cons f rest ih => simp [contextPath,ih,List.append_assoc]

theorem prior_tape_frame_path (earlier : List (Term × Term)) :
    contextPath (priorTapeFrames earlier) = prefixPath earlier := by
  induction earlier with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨version,junk⟩
    simp [priorTapeFrames,context_path_append,contextPath,framePath,ih,prefixPath,
      List.replicate_succ,physicalPath]

theorem tape_frame_path (earlier : List (Term × Term)) (tail junk : Term) :
    contextPath (tapeFrames earlier tail junk) = prefixPath earlier ++ cellVersionPath := by
  simp [tapeFrames,contextPath,framePath,prior_tape_frame_path,cellVersionPath]

#print axioms context_path_append
#print axioms prior_tape_frame_path
#print axioms tape_frame_path

theorem term_at_append (term : Term) (path suffix : List Bool) :
    termAt term (path ++ suffix) = (termAt term path).bind (fun focus => termAt focus suffix) := by
  induction path generalizing term with
  | nil =>
    rw [term_at_nil]
    rfl
  | cons side rest ih =>
    cases term with
    | s => simp [termAt]
    | var x => simp [termAt]
    | app l r => cases side <;> simp [termAt,ih]

theorem term_at_tape_around_version (earlier : List (Term × Term)) (version tail junk : Term) :
    termAt (tapeAroundVersion earlier version tail junk) (prefixPath earlier ++ cellVersionPath) = some version := by
  induction earlier with
  | nil => simp [tapeAroundVersion,prefixPath,physicalPath,cellVersionPath,termAt,frameTerm,term_at_nil]
  | cons pair rest ih =>
    rcases pair with ⟨prior,j⟩
    simpa [tapeAroundVersion,prefixPath,List.replicate_succ,physicalPath,termAt,frameTerm] using ih

theorem term_at_seed_tape (flag tape junk : Term) (path : List Bool) :
    termAt (seedHubRoot flag tape junk) (rootTapePath ++ path) = termAt tape path := by
  simp [seedHubRoot,rootTapePath,termAt,frameTerm]

#print axioms term_at_append
#print axioms term_at_tape_around_version
#print axioms term_at_seed_tape

theorem term_at_tape_around_cell (earlier : List (Term × Term)) (version tail junk : Term) :
    termAt (tapeAroundVersion earlier version tail junk) (prefixPath earlier) = some (frameTerm version tail junk) := by
  induction earlier with
  | nil => simpa [tapeAroundVersion,prefixPath,physicalPath] using term_at_nil (frameTerm version tail junk)
  | cons pair rest ih =>
    rcases pair with ⟨prior,j⟩
    simpa [tapeAroundVersion,prefixPath,List.replicate_succ,physicalPath,termAt,frameTerm] using ih

theorem read_cell_at_tape_around (earlier : List (Term × Term)) (version tail junk : Term) :
    readCellAt (tapeAroundVersion earlier version tail junk) (prefixPath earlier) = some (cellFromVersion version) := by
  simp [readCellAt,term_at_tape_around_cell,parse_frame]

#print axioms term_at_tape_around_cell
#print axioms read_cell_at_tape_around

theorem active_global_step_is_full_selector (program : BinaryProgram)
    (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term) (record : Cell)
    (a b : Term)
    (hflag : flagValue flag = false)
    (hpriority : priorityConcretePath (tapeAroundVersion earlier initial tail junk) = .active (prefixPath earlier))
    (hstate : (cellFromVersion initial).state < 132)
    (hplan : activePlan (prefixPath earlier) (prefixPath earlier).isEmpty
        (program ⟨(cellFromVersion initial).state,hstate⟩ (cellFromVersion initial).bit) =
      .append (prefixPath earlier) record)
    (hstep : HubStableStep earlier tail junk initial flag hubJunk
      (encodeCellBits record (stateBits8 record.state)) a b) :
    ∃ path, fullRootSelector program (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk) = some path ∧
      DirectedStep path (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
        (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk) := by
  obtain ⟨hp,hcell,slot,focus,rel,hchoose,hat,hlocal,hdir⟩ := hstep
  have hp' : priorityConcretePath (tapeAroundVersion earlier a tail junk) = .active (prefixPath earlier) := hp.trans hpriority
  let root := seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk
  let versionPath := rootTapePath ++ prefixPath earlier ++ cellVersionPath
  have hver : termAt root versionPath = some a := by
    simp [root,versionPath,List.append_assoc,term_at_seed_tape,term_at_tape_around_version]
  have hfocus : termAt root (versionPath ++ physicalPath slot) = some focus := by
    rw [term_at_append,hver]
    exact hat
  have hver' : termAt (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (rootTapePath ++ (prefixPath earlier ++ cellVersionPath)) = some a := by
    simpa [root,versionPath,List.append_assoc] using hver
  have hfocus' : termAt (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (rootTapePath ++ (prefixPath earlier ++ (cellVersionPath ++ physicalPath slot))) = some focus := by
    simpa [root,versionPath,List.append_assoc] using hfocus
  have hselected : fullRootSelector program root = some (versionPath ++ physicalPath slot ++ rel) := by
    rw [full_selector_active_branch program flag (tapeAroundVersion earlier a tail junk) hubJunk (prefixPath earlier) hflag hp']
    simp [chooseActive,read_cell_at_tape_around,hcell,hstate,hplan,chooseCellWrite,
      selectVersionAt,selectOpeningAt,versionPath,hver',hchoose,hfocus',hlocal,List.append_assoc]
  refine ⟨versionPath ++ physicalPath slot ++ rel,hselected,?_⟩
  simpa [root,versionPath,rootTapePath,tape_frame_path,List.append_assoc] using hdir

#print axioms active_global_step_is_full_selector

inductive FullSelectorTrace (program : BinaryProgram) : Nat → Term → Term → Prop where
  | zero (a : Term) : FullSelectorTrace program 0 a a
  | next {n : Nat} {a b c : Term} {path : List Bool} :
      fullRootSelector program a = some path → DirectedStep path a b →
      FullSelectorTrace program n b c → FullSelectorTrace program (n+1) a c

theorem active_global_trace_is_full_selector (program : BinaryProgram)
    (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term) (record : Cell)
    (hflag : flagValue flag = false)
    (hpriority : priorityConcretePath (tapeAroundVersion earlier initial tail junk) = .active (prefixPath earlier))
    (hstate : (cellFromVersion initial).state < 132)
    (hplan : activePlan (prefixPath earlier) (prefixPath earlier).isEmpty
        (program ⟨(cellFromVersion initial).state,hstate⟩ (cellFromVersion initial).bit) =
      .append (prefixPath earlier) record)
    {n : Nat} {a b : Term}
    (trace : HubStableTrace earlier tail junk initial flag hubJunk
      (encodeCellBits record (stateBits8 record.state)) n a b) :
    FullSelectorTrace program n (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk) := by
  induction trace with
  | zero x => exact FullSelectorTrace.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨path,hselect,hdir⟩ :=
      active_global_step_is_full_selector program earlier tail junk initial flag hubJunk record a b
        hflag hpriority hstate hplan hstep
    exact FullSelectorTrace.next hselect hdir ih

#print axioms active_global_trace_is_full_selector

theorem pending_global_step_is_full_selector (program : BinaryProgram)
    (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term) (record pending : Cell)
    (sourcePath : List Bool) (a b : Term)
    (hflag : flagValue flag = false)
    (hpriority : priorityConcretePath (tapeAroundVersion earlier initial tail junk) = .pending sourcePath)
    (hsource : ∀ v, cellFromVersion v = cellFromVersion initial →
      readCellAt (tapeAroundVersion earlier v tail junk) sourcePath = some pending)
    (hdestination : pendingDestinationPath pending sourcePath = some (prefixPath earlier))
    (hplan : pendingPlan sourcePath (prefixPath earlier) pending (some (cellFromVersion initial)) =
      .append (prefixPath earlier) record)
    (hstep : HubStableStep earlier tail junk initial flag hubJunk
      (encodeCellBits record (stateBits8 record.state)) a b) :
    ∃ path, fullRootSelector program (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk) = some path ∧
      DirectedStep path (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
        (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk) := by
  obtain ⟨hp,hcell,slot,focus,rel,hchoose,hat,hlocal,hdir⟩ := hstep
  have hp' : priorityConcretePath (tapeAroundVersion earlier a tail junk) = .pending sourcePath := hp.trans hpriority
  let root := seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk
  let versionPath := rootTapePath ++ prefixPath earlier ++ cellVersionPath
  have hver : termAt root versionPath = some a := by
    simp [root,versionPath,List.append_assoc,term_at_seed_tape,term_at_tape_around_version]
  have hfocus : termAt root (versionPath ++ physicalPath slot) = some focus := by
    rw [term_at_append,hver]
    exact hat
  have hver' : termAt (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (rootTapePath ++ (prefixPath earlier ++ cellVersionPath)) = some a := by
    simpa [root,versionPath,List.append_assoc] using hver
  have hfocus' : termAt (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (rootTapePath ++ (prefixPath earlier ++ (cellVersionPath ++ physicalPath slot))) = some focus := by
    simpa [root,versionPath,List.append_assoc] using hfocus
  have hselected : fullRootSelector program root = some (versionPath ++ physicalPath slot ++ rel) := by
    rw [full_selector_pending_branch program flag (tapeAroundVersion earlier a tail junk) hubJunk sourcePath hflag hp']
    simp [choosePending,hsource a hcell,hdestination,term_at_tape_around_cell,parse_frame,hcell,hplan,
      chooseCellWrite,selectVersionAt,selectOpeningAt,versionPath,hver',hchoose,hfocus',hlocal,List.append_assoc]
  refine ⟨versionPath ++ physicalPath slot ++ rel,hselected,?_⟩
  simpa [root,versionPath,rootTapePath,tape_frame_path,List.append_assoc] using hdir

#print axioms pending_global_step_is_full_selector

theorem pending_global_trace_is_full_selector (program : BinaryProgram)
    (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term) (record pending : Cell)
    (sourcePath : List Bool)
    (hflag : flagValue flag = false)
    (hpriority : priorityConcretePath (tapeAroundVersion earlier initial tail junk) = .pending sourcePath)
    (hsource : ∀ v, cellFromVersion v = cellFromVersion initial →
      readCellAt (tapeAroundVersion earlier v tail junk) sourcePath = some pending)
    (hdestination : pendingDestinationPath pending sourcePath = some (prefixPath earlier))
    (hplan : pendingPlan sourcePath (prefixPath earlier) pending (some (cellFromVersion initial)) =
      .append (prefixPath earlier) record)
    {n : Nat} {a b : Term}
    (trace : HubStableTrace earlier tail junk initial flag hubJunk
      (encodeCellBits record (stateBits8 record.state)) n a b) :
    FullSelectorTrace program n (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk) := by
  induction trace with
  | zero x => exact FullSelectorTrace.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨path,hselect,hdir⟩ :=
      pending_global_step_is_full_selector program earlier tail junk initial flag hubJunk record pending sourcePath a b
        hflag hpriority hsource hdestination hplan hstep
    exact FullSelectorTrace.next hselect hdir ih

#print axioms pending_global_trace_is_full_selector

theorem term_at_prepend_tape (earlier : List (Term × Term)) (tail : Term) :
    termAt (prependTape earlier tail) (prefixPath earlier) = some tail := by
  induction earlier with
  | nil => simpa [prependTape,prefixPath,physicalPath] using term_at_nil tail
  | cons pair rest ih =>
    rcases pair with ⟨version,junk⟩
    simpa [prependTape,prefixPath,List.replicate_succ,physicalPath,termAt,frameTerm] using ih

theorem source_before_focused_cell_read (prior : List (Term × Term))
    (sourceVersion sourceJunk focus tail focusJunk : Term) :
    readCellAt (tapeAroundVersion (prior ++ [(sourceVersion,sourceJunk)]) focus tail focusJunk)
      (prefixPath prior) = some (cellFromVersion sourceVersion) := by
  rw [prepend_tape_around]
  simp [tapeAroundVersion,readCellAt,term_at_prepend_tape,parse_frame]

theorem source_after_focused_cell_read (prior : List (Term × Term))
    (focus sourceVersion tail focusJunk sourceJunk : Term) :
    readCellAt (tapeAroundVersion prior focus (frameTerm sourceVersion tail sourceJunk) focusJunk)
      (prefixPath prior ++ nextCellPath) = some (cellFromVersion sourceVersion) := by
  unfold readCellAt
  rw [term_at_append,term_at_tape_around_cell]
  simp [nextCellPath,termAt,frameTerm,parseFrame,S]

#print axioms term_at_prepend_tape
#print axioms source_before_focused_cell_read
#print axioms source_after_focused_cell_read

theorem physical_path_append (a b : List Bool) :
    physicalPath (a ++ b) = physicalPath a ++ physicalPath b := by
  induction a with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [physicalPath,ih]

theorem true_path_block_commutes (n : Nat) :
    nextCellPath ++ physicalPath (List.replicate n true) = physicalPath (List.replicate n true) ++ nextCellPath := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,physicalPath]
    simp [nextCellPath] at ih ⊢
    exact ih

theorem replicated_true_path_succ (n : Nat) :
    physicalPath (List.replicate (n+1) true) = physicalPath (List.replicate n true) ++ nextCellPath := by
  rw [List.replicate_succ]
  change nextCellPath ++ physicalPath (List.replicate n true) = _
  exact true_path_block_commutes n

theorem prefix_path_append_cell (prior : List (Term × Term)) (version junk : Term) :
    prefixPath (prior ++ [(version,junk)]) = prefixPath prior ++ nextCellPath := by
  simp [prefixPath,List.length_append,replicated_true_path_succ]

#print axioms physical_path_append
#print axioms prefix_path_append_cell

theorem parent_of_next_cell (path : List Bool) :
    parentCellPath (path ++ nextCellPath) = path := by
  simp [parentCellPath,nextCellPath,List.length_append]

#print axioms parent_of_next_cell

theorem pending_right_destination (path : List Bool) (bit : Bool) (q : Nat) :
    pendingDestinationPath ⟨bit,.movingRight,q⟩ path = some (path ++ nextCellPath) := by rfl

theorem pending_left_destination (path : List Bool) (bit : Bool) (q : Nat) :
    pendingDestinationPath ⟨bit,.movingLeft,q⟩ (path ++ nextCellPath) = some path := by
  simp [pendingDestinationPath,nextCellPath,parentCellPath,List.length_append]

#print axioms pending_right_destination
#print axioms pending_left_destination

theorem term_at_seed_flag (flag tape junk : Term) :
    termAt (seedHubRoot flag tape junk) hubFlagPath = some flag := by
  simp [seedHubRoot,hubFlagPath,termAt,frameTerm,term_at_nil]

theorem halt_seed_step_is_full_selector (program : BinaryProgram) (tape junk : Term) (sourcePath : List Bool)
    (q : Fin 132) (bit : Bool)
    (hpriority : priorityConcretePath tape = .active sourcePath)
    (hread : readCellAt tape sourcePath = some ⟨bit,.active,q.val⟩)
    (hstop : program q bit = none) {a b : Term}
    (hstep : SeedHaltStep tape junk (.active sourcePath) a b) :
    ∃ path, fullRootSelector program (seedHubRoot a tape junk) = some path ∧
      DirectedStep path (seedHubRoot a tape junk) (seedHubRoot b tape junk) := by
  obtain ⟨hflag,_,rel,hlocal,hdir⟩ := hstep
  have hv : flagValue a = false := by simpa [haltObserved,parse_frame] using hflag
  have hsel : fullRootSelector program (seedHubRoot a tape junk) = some (hubFlagPath ++ rel) := by
    rw [full_selector_active_branch program a tape junk sourcePath hv hpriority]
    simp [chooseActive,hread,hstop,activePlan,selectOpeningAt,term_at_seed_flag,hlocal]
  refine ⟨hubFlagPath ++ rel,hsel,?_⟩
  simpa [hubFlagPath,contextPath,framePath,List.append_assoc] using hdir

theorem halt_seed_trace_is_full_selector (program : BinaryProgram) (tape junk : Term) (sourcePath : List Bool)
    (q : Fin 132) (bit : Bool)
    (hpriority : priorityConcretePath tape = .active sourcePath)
    (hread : readCellAt tape sourcePath = some ⟨bit,.active,q.val⟩)
    (hstop : program q bit = none) {n : Nat} {a b : Term}
    (trace : SeedHaltTrace tape junk (.active sourcePath) n a b) :
    FullSelectorTrace program n (seedHubRoot a tape junk) (seedHubRoot b tape junk) := by
  induction trace with
  | zero x => exact FullSelectorTrace.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨path,hselect,hdir⟩ := halt_seed_step_is_full_selector program tape junk sourcePath q bit
      hpriority hread hstop hstep
    exact FullSelectorTrace.next hselect hdir ih

#print axioms term_at_seed_flag
#print axioms halt_seed_step_is_full_selector
#print axioms halt_seed_trace_is_full_selector

theorem canonical_prefix_length (before : List (List UniversalCell)) : ∀ d,
    (canonicalPrefix before d).length = before.length := by
  induction before with
  | nil => intro d; rfl
  | cons cell rest ih => intro d; simp [canonicalPrefix,ih]

theorem canonical_boundary_reads_active
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit : Bool) (hs : ActiveAt source q bit) (d : Nat) :
    readCellAt (canonicalTape (before ++ source :: after) d) (physicalPath (List.replicate before.length true)) =
      some ⟨bit,.active,q.val⟩ := by
  rw [canonical_single_decompose]
  have hpath : prefixPath (canonicalPrefix before d) = physicalPath (List.replicate before.length true) := by
    simp [prefixPath,canonical_prefix_length]
  rw [← hpath]
  rw [read_cell_at_tape_around,concrete_version_decodes]
  rw [hs]

#print axioms canonical_boundary_reads_active

theorem stopped_boundary_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit : Bool) (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after)
    (hstop : program q bit = none) (d flagDepth : Nat) (hubJunk : Term) :
    let cells := before ++ source :: after
    let tape := canonicalTape cells d
    let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2
    ∃ k, 6 ≤ k ∧ k ≤ 7 ∧
      FullSelectorTrace program k (canonicalRoot cells d (depthBase flagDepth) hubJunk) (seedHubRoot flagOpen tape hubJunk) ∧
      rootHalt (seedHubRoot flagOpen tape hubJunk) = true := by
  let tape := canonicalTape (before ++ source :: after) d
  let sourcePath := physicalPath (List.replicate before.length true)
  obtain ⟨k,hlower,hupper,_,htrace,_,hobserved⟩ :=
    stopped_boundary_exposes_halt program before source after q bit hb hs ha hstop d flagDepth hubJunk
  have hpriority : priorityConcretePath tape = .active sourcePath :=
    canonical_boundary_priority_path before source after q bit hb hs ha d
  have hread : readCellAt tape sourcePath = some ⟨bit,.active,q.val⟩ :=
    canonical_boundary_reads_active before source after q bit hs d
  exact ⟨k,hlower,hupper,
    halt_seed_trace_is_full_selector program tape hubJunk sourcePath q bit hpriority hread hstop htrace,hobserved⟩

#print axioms stopped_boundary_full_selector

theorem pending_global_step_general (program : BinaryProgram)
    (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term) (record pending targetCell : Cell)
    (sourcePath targetPath : List Bool) (a b : Term)
    (hflag : flagValue flag = false)
    (hpriority : priorityConcretePath (tapeAroundVersion earlier initial tail junk) = .pending sourcePath)
    (hsource : ∀ v, cellFromVersion v = cellFromVersion initial →
      readCellAt (tapeAroundVersion earlier v tail junk) sourcePath = some pending)
    (hdestination : pendingDestinationPath pending sourcePath = some targetPath)
    (htarget : ∀ v, cellFromVersion v = cellFromVersion initial →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v tail junk) targetPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion,targetTail,targetJunk) ∧ cellFromVersion targetVersion = targetCell)
    (hplan : pendingPlan sourcePath targetPath pending (some targetCell) = .append (prefixPath earlier) record)
    (hstep : HubStableStep earlier tail junk initial flag hubJunk
      (encodeCellBits record (stateBits8 record.state)) a b) :
    ∃ path, fullRootSelector program (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk) = some path ∧
      DirectedStep path (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
        (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk) := by
  obtain ⟨hp,hcell,slot,focus,rel,hchoose,hat,hlocal,hdir⟩ := hstep
  have hp' : priorityConcretePath (tapeAroundVersion earlier a tail junk) = .pending sourcePath := hp.trans hpriority
  obtain ⟨targetTerm,targetVersion,targetTail,targetJunk,htargetAt,htargetParse,htargetValue⟩ := htarget a hcell
  let root := seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk
  let versionPath := rootTapePath ++ prefixPath earlier ++ cellVersionPath
  have hver : termAt root versionPath = some a := by
    simp [root,versionPath,List.append_assoc,term_at_seed_tape,term_at_tape_around_version]
  have hfocus : termAt root (versionPath ++ physicalPath slot) = some focus := by
    rw [term_at_append,hver]
    exact hat
  have hver' : termAt (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (rootTapePath ++ (prefixPath earlier ++ cellVersionPath)) = some a := by
    simpa [root,versionPath,List.append_assoc] using hver
  have hfocus' : termAt (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (rootTapePath ++ (prefixPath earlier ++ (cellVersionPath ++ physicalPath slot))) = some focus := by
    simpa [root,versionPath,List.append_assoc] using hfocus
  have hselected : fullRootSelector program root = some (versionPath ++ physicalPath slot ++ rel) := by
    rw [full_selector_pending_branch program flag (tapeAroundVersion earlier a tail junk) hubJunk sourcePath hflag hp']
    simp [choosePending,hsource a hcell,hdestination,htargetAt,htargetParse,htargetValue,hplan,
      chooseCellWrite,selectVersionAt,selectOpeningAt,versionPath,hver',hchoose,hfocus',hlocal,List.append_assoc]
  refine ⟨versionPath ++ physicalPath slot ++ rel,hselected,?_⟩
  simpa [root,versionPath,rootTapePath,tape_frame_path,List.append_assoc] using hdir

theorem pending_global_trace_general (program : BinaryProgram)
    (earlier : List (Term × Term)) (tail junk initial flag hubJunk : Term) (record pending targetCell : Cell)
    (sourcePath targetPath : List Bool)
    (hflag : flagValue flag = false)
    (hpriority : priorityConcretePath (tapeAroundVersion earlier initial tail junk) = .pending sourcePath)
    (hsource : ∀ v, cellFromVersion v = cellFromVersion initial →
      readCellAt (tapeAroundVersion earlier v tail junk) sourcePath = some pending)
    (hdestination : pendingDestinationPath pending sourcePath = some targetPath)
    (htarget : ∀ v, cellFromVersion v = cellFromVersion initial →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v tail junk) targetPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion,targetTail,targetJunk) ∧ cellFromVersion targetVersion = targetCell)
    (hplan : pendingPlan sourcePath targetPath pending (some targetCell) = .append (prefixPath earlier) record)
    {n : Nat} {a b : Term}
    (trace : HubStableTrace earlier tail junk initial flag hubJunk
      (encodeCellBits record (stateBits8 record.state)) n a b) :
    FullSelectorTrace program n (seedHubRoot flag (tapeAroundVersion earlier a tail junk) hubJunk)
      (seedHubRoot flag (tapeAroundVersion earlier b tail junk) hubJunk) := by
  induction trace with
  | zero x => exact FullSelectorTrace.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨path,hselect,hdir⟩ :=
      pending_global_step_general program earlier tail junk initial flag hubJunk record pending targetCell
        sourcePath targetPath a b hflag hpriority hsource hdestination htarget hplan hstep
    exact FullSelectorTrace.next hselect hdir ih

#print axioms pending_global_step_general
#print axioms pending_global_trace_general

theorem target_after_focused_cell_term (prior : List (Term × Term))
    (focus targetVersion tail focusJunk targetJunk : Term) :
    termAt (tapeAroundVersion prior focus (frameTerm targetVersion tail targetJunk) focusJunk)
      (prefixPath prior ++ nextCellPath) = some (frameTerm targetVersion tail targetJunk) := by
  rw [term_at_append,term_at_tape_around_cell]
  simp [nextCellPath,termAt,frameTerm]

theorem full_selector_trace_trans {program : BinaryProgram} {n m : Nat} {a b c : Term}
    (h : FullSelectorTrace program n a b) (k : FullSelectorTrace program m b c) :
    FullSelectorTrace program (n+m) a c := by
  induction h with
  | zero _ => simpa using k
  | @next n a b c path hselect hdir rest ih =>
    have result := FullSelectorTrace.next hselect hdir (ih k)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

#print axioms target_after_focused_cell_term
#print axioms full_selector_trace_trans

/- First complete whole-root selector refinement: a stay instruction. -/
theorem canonical_stay_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term)
    (q : Fin 132) (bit written : Bool) (nextState : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : AllOff before) (hsource : ActiveAt source q bit) (hafter : AllOff after)
    (hrule : program q bit = some ⟨written,nextState,.stay⟩) :
    let active := activeCellRecord written nextState
    ∃ k, 6 ≤ k ∧ k ≤ 168 ∧
      FullSelectorTrace program k (canonicalRoot (before ++ source :: after) d flag hubJunk)
        (canonicalRoot (before ++ (source ++ [active]) :: after) d flag hubJunk) := by
  let active := activeCellRecord written nextState
  let earlier := canonicalPrefix before d
  let sd := d+before.length+1
  let sj := depthJunk (d+before.length)
  let tail := canonicalTape after (d+before.length+1)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [active]) sd
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  have hs : (decodedCell source).status = .active := by rw [hsource]
  obtain ⟨k,trace,hlower,hupper,hpriority,_,_⟩ :=
    stay_in_seed_hub source sd earlier tail sj flag hubJunk written nextState hprefix hs htail
  have hp : priorityConcretePath (tapeAroundVersion earlier s0 tail sj) = .active (prefixPath earlier) := by
    rw [tape_around_single]
    exact hpriority
  have hcell : cellFromVersion s0 = ⟨bit,.active,q.val⟩ := by
    simpa [s0,concrete_version_decodes,ActiveAt] using hsource
  have hstate : (cellFromVersion s0).state < 132 := by rw [hcell]; exact q.isLt
  have hplan : activePlan (prefixPath earlier) (prefixPath earlier).isEmpty
      (program ⟨(cellFromVersion s0).state,hstate⟩ (cellFromVersion s0).bit) =
        .append (prefixPath earlier) active.val := by
    have hq : (⟨(cellFromVersion s0).state,hstate⟩ : Fin 132) = q := by
      apply Fin.ext
      simp [hcell]
    have hbit : (cellFromVersion s0).bit = bit := by rw [hcell]
    rw [hq,hbit,hrule]
    rfl
  have hv : flagValue flag = false := by simp [flagValue,hflag]
  have hfull := active_global_trace_is_full_selector program earlier tail sj s0 flag hubJunk active.val
    hv hp hstate hplan (by simpa [encodedEntry,active] using trace)
  have hstart : tapeAroundVersion earlier s0 tail sj = canonicalTape (before ++ source :: after) d :=
    (canonical_single_decompose before source after d).symm
  have hend : tapeAroundVersion earlier s1 tail sj = canonicalTape (before ++ (source ++ [active]) :: after) d :=
    (canonical_single_decompose before (source ++ [active]) after d).symm
  rw [hstart,hend] at hfull
  exact ⟨k,hlower,hupper,hfull⟩

#print axioms canonical_stay_full_selector

theorem canonical_left_boundary_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term)
    (q : Fin 132) (bit written : Bool) (nextState : Fin 132)
    (hflag : parseFrame flag = none) (hboundary : before = [])
    (hbefore : AllOff before) (hsource : ActiveAt source q bit) (hafter : AllOff after)
    (hrule : program q bit = some ⟨written,nextState,.left⟩) :
    let active := activeCellRecord written nextState
    ∃ k, 6 ≤ k ∧ k ≤ 168 ∧
      FullSelectorTrace program k (canonicalRoot (before ++ source :: after) d flag hubJunk)
        (canonicalRoot (before ++ (source ++ [active]) :: after) d flag hubJunk) := by
  let active := activeCellRecord written nextState
  let earlier := canonicalPrefix before d
  let sd := d+before.length+1
  let sj := depthJunk (d+before.length)
  let tail := canonicalTape after (d+before.length+1)
  let s0 := concreteVersion source sd
  let s1 := concreteVersion (source ++ [active]) sd
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  have hs : (decodedCell source).status = .active := by rw [hsource]
  obtain ⟨k,trace,hlower,hupper,hpriority,_,_⟩ :=
    stay_in_seed_hub source sd earlier tail sj flag hubJunk written nextState hprefix hs htail
  have hp : priorityConcretePath (tapeAroundVersion earlier s0 tail sj) = .active (prefixPath earlier) := by
    rw [tape_around_single]
    exact hpriority
  have hcell : cellFromVersion s0 = ⟨bit,.active,q.val⟩ := by
    simpa [s0,concrete_version_decodes,ActiveAt] using hsource
  have hstate : (cellFromVersion s0).state < 132 := by rw [hcell]; exact q.isLt
  have hplan : activePlan (prefixPath earlier) (prefixPath earlier).isEmpty
      (program ⟨(cellFromVersion s0).state,hstate⟩ (cellFromVersion s0).bit) =
        .append (prefixPath earlier) active.val := by
    have hq : (⟨(cellFromVersion s0).state,hstate⟩ : Fin 132) = q := by
      apply Fin.ext
      simp [hcell]
    have hbit : (cellFromVersion s0).bit = bit := by rw [hcell]
    have hempty : (prefixPath earlier).isEmpty = true := by
      simp [earlier,hboundary,canonicalPrefix,prefixPath,physicalPath]
    rw [hq,hbit,hrule,hempty]
    rfl
  have hv : flagValue flag = false := by simp [flagValue,hflag]
  have hfull := active_global_trace_is_full_selector program earlier tail sj s0 flag hubJunk active.val
    hv hp hstate hplan (by simpa [encodedEntry,active] using trace)
  have hstart : tapeAroundVersion earlier s0 tail sj = canonicalTape (before ++ source :: after) d :=
    (canonical_single_decompose before source after d).symm
  have hend : tapeAroundVersion earlier s1 tail sj = canonicalTape (before ++ (source ++ [active]) :: after) d :=
    (canonical_single_decompose before (source ++ [active]) after d).symm
  rw [hstart,hend] at hfull
  exact ⟨k,hlower,hupper,hfull⟩


#print axioms canonical_left_boundary_full_selector

theorem canonical_right_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (source destination : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term)
    (q : Fin 132) (bit written : Bool) (nextState : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : AllOff before) (hsource : ActiveAt source q bit)
    (hdestination : (decodedCell destination).status = .off) (hafter : AllOff after)
    (hrule : program q bit = some ⟨written,nextState,.right⟩) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    ∃ k, 18 ≤ k ∧ k ≤ 504 ∧
      FullSelectorTrace program k (canonicalRoot (before ++ source :: destination :: after) d flag hubJunk)
        (canonicalRoot (before ++ (source ++ [pending,off]) :: (destination ++ [active]) :: after) d flag hubJunk) := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
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
  let srcPath := prefixPath earlier
  let dstPath := srcPath ++ nextCellPath
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  have hsourceStatus : (decodedCell source).status = .active := by rw [hsource]
  obtain ⟨k1,k2,k3,t1,t2,t3,hb1,hb2,hb3,hp0,hp1,hp2,hp3,readOff,readActive⟩ :=
    right_move_in_seed_hub source destination sd dd tail sj dj earlier flag hubJunk hprefix written nextState
      hsourceStatus hdestination htail
  have hv : flagValue flag = false := by simp [flagValue,hflag]
  have hs0 : cellFromVersion s0 = ⟨bit,.active,q.val⟩ := by simpa [s0,concrete_version_decodes,ActiveAt] using hsource
  have hs1 : cellFromVersion s1 = pending.val := by simp [s1,concrete_version_decodes,decoded_cell_append]
  have hd0 : cellFromVersion d0 = decodedCell destination := by exact concrete_version_decodes destination dd
  have hd1 : cellFromVersion d1 = active.val := by simp [d1,concrete_version_decodes,decoded_cell_append]
  have hpriority1 : priorityConcretePath (tapeAroundVersion earlier s0 (frameTerm d0 tail dj) sj) = .active srcPath := by
    rw [tape_around_adjacent]
    exact hp0
  have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
  have hplan1 : activePlan srcPath srcPath.isEmpty
      (program ⟨(cellFromVersion s0).state,hstate⟩ (cellFromVersion s0).bit) = .append srcPath pending.val := by
    have hq : (⟨(cellFromVersion s0).state,hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
    have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
    rw [hq,hbit,hrule]
    rfl
  have f1 := active_global_trace_is_full_selector program earlier (frameTerm d0 tail dj) sj s0 flag hubJunk pending.val
    hv hpriority1 hstate hplan1 (by simpa [encodedEntry,pending] using t1)
  have hpriority2 : priorityConcretePath (tapeAroundVersion (earlier ++ [(s1,sj)]) d0 tail dj) = .pending srcPath := by
    rw [← adjacent_contexts_stitch earlier s1 d0 tail sj dj,tape_around_adjacent]
    exact hp1
  have hsource2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
      readCellAt (tapeAroundVersion (earlier ++ [(s1,sj)]) v tail dj) srcPath = some pending.val := by
    intro v heq
    rw [source_before_focused_cell_read,hs1]
  have hdest2 : pendingDestinationPath pending.val srcPath = some (prefixPath (earlier ++ [(s1,sj)])) := by
    rw [prefix_path_append_cell]
    rfl
  have htarget2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion (earlier ++ [(s1,sj)]) v tail dj) (prefixPath (earlier ++ [(s1,sj)])) = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion,targetTail,targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion d0 := by
    intro v heq
    exact ⟨frameTerm v tail dj,v,tail,dj,term_at_tape_around_cell _ _ _ _,parse_frame _ _ _,heq⟩
  have hplan2 : pendingPlan srcPath (prefixPath (earlier ++ [(s1,sj)])) pending.val (some (cellFromVersion d0)) =
      .append (prefixPath (earlier ++ [(s1,sj)])) active.val := by
    simpa [pending,active,pendingRightCell,activeCellRecord,hd0] using
      pending_right_off_general srcPath (prefixPath (earlier ++ [(s1,sj)])) written nextState.val (decodedCell destination) hdestination
  have f2 := pending_global_trace_general program (earlier ++ [(s1,sj)]) tail dj d0 flag hubJunk
    active.val pending.val (cellFromVersion d0) srcPath (prefixPath (earlier ++ [(s1,sj)]))
    hv hpriority2 hsource2 hdest2 htarget2 hplan2 (by simpa [encodedEntry,active] using t2)
  have hpriority3 : priorityConcretePath (tapeAroundVersion earlier s1 (frameTerm d1 tail dj) sj) = .pending srcPath := by
    rw [tape_around_adjacent]
    exact hp2
  have hsource3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      readCellAt (tapeAroundVersion earlier v (frameTerm d1 tail dj) sj) srcPath = some pending.val := by
    intro v heq
    rw [read_cell_at_tape_around,heq,hs1]
  have hdest3 : pendingDestinationPath pending.val srcPath = some dstPath := by rfl
  have htarget3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v (frameTerm d1 tail dj) sj) dstPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion,targetTail,targetJunk) ∧ cellFromVersion targetVersion = active.val := by
    intro v heq
    exact ⟨frameTerm d1 tail dj,d1,tail,dj,target_after_focused_cell_term _ _ _ _ _ _,parse_frame _ _ _,hd1⟩
  have hplan3 : pendingPlan srcPath dstPath pending.val (some active.val) = .append srcPath off.val := by
    exact pending_right_done_plan srcPath dstPath written (decodedCell destination).bit nextState.val
  have f3 := pending_global_trace_general program earlier (frameTerm d1 tail dj) sj s1 flag hubJunk
    off.val pending.val active.val srcPath dstPath hv hpriority3 hsource3 hdest3 htarget3 hplan3
    (by simpa [encodedEntry,off] using t3)
  rw [← adjacent_contexts_stitch earlier s1 d0 tail sj dj, ← adjacent_contexts_stitch earlier s1 d1 tail sj dj] at f2
  have combined := full_selector_trace_trans f1 (full_selector_trace_trans f2 f3)
  have hstart : tapeAroundVersion earlier s0 (frameTerm d0 tail dj) sj = canonicalTape (before ++ source :: destination :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before source destination after d).symm
  have hend : tapeAroundVersion earlier s2 (frameTerm d1 tail dj) sj =
      canonicalTape (before ++ (source ++ [pending,off]) :: (destination ++ [active]) :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before (source ++ [pending,off]) (destination ++ [active]) after d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+k3),?_,?_,combined⟩ <;> omega

#print axioms canonical_right_full_selector

theorem canonical_left_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (destination source : List UniversalCell)
    (after : List (List UniversalCell)) (d : Nat) (flag hubJunk : Term)
    (q : Fin 132) (bit written : Bool) (nextState : Fin 132)
    (hflag : parseFrame flag = none)
    (hbefore : AllOff before) (hdestination : (decodedCell destination).status = .off)
    (hsource : ActiveAt source q bit) (hafter : AllOff after)
    (hrule : program q bit = some ⟨written,nextState,.left⟩) :
    let pending := pendingLeftCell written nextState
    let active := activeCellRecord (decodedCell destination).bit nextState
    let off := offCellRecord written
    ∃ k, 18 ≤ k ∧ k ≤ 504 ∧
      FullSelectorTrace program k (canonicalRoot (before ++ destination :: source :: after) d flag hubJunk)
        (canonicalRoot (before ++ (destination ++ [active]) :: (source ++ [pending,off]) :: after) d flag hubJunk) := by
  let pending := pendingLeftCell written nextState
  let active := activeCellRecord (decodedCell destination).bit nextState
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
  let dstPath := prefixPath earlier
  let srcPath := dstPath ++ nextCellPath
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have htail : seekConcreteCell movingCell tail = none := (canonical_tape_off_no_work after _ hafter).1
  have hsourceStatus : (decodedCell source).status = .active := by rw [hsource]
  obtain ⟨k1,k2,k3,t1,t2,t3,hb1,hb2,hb3,hp0,hp1,hp2,hp3,readOff,readActive⟩ :=
    left_move_in_seed_hub source destination sd dd tail sj dj earlier flag hubJunk hprefix written nextState
      hsourceStatus hdestination htail
  have hv : flagValue flag = false := by simp [flagValue,hflag]
  have hs0 : cellFromVersion s0 = ⟨bit,.active,q.val⟩ := by simpa [s0,concrete_version_decodes,ActiveAt] using hsource
  have hs1 : cellFromVersion s1 = pending.val := by simp [s1,concrete_version_decodes,decoded_cell_append]
  have hd0 : cellFromVersion d0 = decodedCell destination := by exact concrete_version_decodes destination dd
  have hd1 : cellFromVersion d1 = active.val := by simp [d1,concrete_version_decodes,decoded_cell_append]
  have hsrc1 : prefixPath (earlier ++ [(d0,dj)]) = srcPath := by
    simpa [srcPath,dstPath] using prefix_path_append_cell earlier d0 dj
  have hpriority1 : priorityConcretePath (tapeAroundVersion (earlier ++ [(d0,dj)]) s0 tail sj) =
      .active (prefixPath (earlier ++ [(d0,dj)])) := by
    rw [← adjacent_contexts_stitch earlier d0 s0 tail dj sj,tape_around_adjacent,hsrc1]
    exact hp0
  have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
  have hplan1 : activePlan (prefixPath (earlier ++ [(d0,dj)])) (prefixPath (earlier ++ [(d0,dj)])).isEmpty
      (program ⟨(cellFromVersion s0).state,hstate⟩ (cellFromVersion s0).bit) =
        .append (prefixPath (earlier ++ [(d0,dj)])) pending.val := by
    have hq : (⟨(cellFromVersion s0).state,hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
    have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
    have hempty : (prefixPath (earlier ++ [(d0,dj)])).isEmpty = false := by
      rw [hsrc1]
      simp [srcPath,nextCellPath]
    rw [hq,hbit,hrule,hempty]
    rfl
  have f1 := active_global_trace_is_full_selector program (earlier ++ [(d0,dj)]) tail sj s0 flag hubJunk pending.val
    hv hpriority1 hstate hplan1 (by simpa [encodedEntry,pending] using t1)
  have hpriority2 : priorityConcretePath (tapeAroundVersion earlier d0 (frameTerm s1 tail sj) dj) = .pending srcPath := by
    rw [tape_around_adjacent]
    exact hp1
  have hsource2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
      readCellAt (tapeAroundVersion earlier v (frameTerm s1 tail sj) dj) srcPath = some pending.val := by
    intro v heq
    rw [show srcPath = prefixPath earlier ++ nextCellPath from rfl,source_after_focused_cell_read,hs1]
  have hdest2 : pendingDestinationPath pending.val srcPath = some (prefixPath earlier) := by
    simpa [srcPath,dstPath,pending,pendingLeftCell] using pending_left_destination (prefixPath earlier) written nextState.val
  have htarget2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v (frameTerm s1 tail sj) dj) (prefixPath earlier) = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion,targetTail,targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion d0 := by
    intro v heq
    exact ⟨frameTerm v (frameTerm s1 tail sj) dj,v,frameTerm s1 tail sj,dj,
      term_at_tape_around_cell _ _ _ _,parse_frame _ _ _,heq⟩
  have hplan2 : pendingPlan srcPath (prefixPath earlier) pending.val (some (cellFromVersion d0)) =
      .append (prefixPath earlier) active.val := by
    simpa [pending,active,pendingLeftCell,activeCellRecord,hd0] using
      pending_left_off_general srcPath (prefixPath earlier) written nextState.val (decodedCell destination) hdestination
  have f2 := pending_global_trace_general program earlier (frameTerm s1 tail sj) dj d0 flag hubJunk
    active.val pending.val (cellFromVersion d0) srcPath (prefixPath earlier)
    hv hpriority2 hsource2 hdest2 htarget2 hplan2 (by simpa [encodedEntry,active] using t2)
  have hsrc3 : prefixPath (earlier ++ [(d1,dj)]) = srcPath := by
    simpa [srcPath,dstPath] using prefix_path_append_cell earlier d1 dj
  have hpriority3 : priorityConcretePath (tapeAroundVersion (earlier ++ [(d1,dj)]) s1 tail sj) = .pending srcPath := by
    rw [← adjacent_contexts_stitch earlier d1 s1 tail dj sj,tape_around_adjacent]
    exact hp2
  have hsource3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      readCellAt (tapeAroundVersion (earlier ++ [(d1,dj)]) v tail sj) srcPath = some pending.val := by
    intro v heq
    rw [← hsrc3,read_cell_at_tape_around,heq,hs1]
  have hdest3 : pendingDestinationPath pending.val srcPath = some dstPath := by
    simpa [srcPath,dstPath,pending,pendingLeftCell] using pending_left_destination (prefixPath earlier) written nextState.val
  have htarget3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion (earlier ++ [(d1,dj)]) v tail sj) dstPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion,targetTail,targetJunk) ∧ cellFromVersion targetVersion = active.val := by
    intro v heq
    refine ⟨frameTerm d1 (frameTerm v tail sj) dj,d1,frameTerm v tail sj,dj,?_,parse_frame _ _ _,hd1⟩
    rw [prepend_tape_around]
    simpa [tapeAroundVersion,dstPath] using term_at_prepend_tape earlier (frameTerm d1 (frameTerm v tail sj) dj)
  have hplan3 : pendingPlan srcPath dstPath pending.val (some active.val) =
      .append (prefixPath (earlier ++ [(d1,dj)])) off.val := by
    rw [hsrc3]
    exact pending_left_done_plan srcPath dstPath written (decodedCell destination).bit nextState.val
  have f3 := pending_global_trace_general program (earlier ++ [(d1,dj)]) tail sj s1 flag hubJunk
    off.val pending.val active.val srcPath dstPath hv hpriority3 hsource3 hdest3 htarget3 hplan3
    (by simpa [encodedEntry,off] using t3)
  rw [← adjacent_contexts_stitch earlier d0 s0 tail dj sj, ← adjacent_contexts_stitch earlier d0 s1 tail dj sj] at f1
  rw [← adjacent_contexts_stitch earlier d1 s1 tail dj sj, ← adjacent_contexts_stitch earlier d1 s2 tail dj sj] at f3
  have combined := full_selector_trace_trans f1 (full_selector_trace_trans f2 f3)
  have hstart : tapeAroundVersion earlier d0 (frameTerm s0 tail sj) dj = canonicalTape (before ++ destination :: source :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before destination source after d).symm
  have hend : tapeAroundVersion earlier d1 (frameTerm s2 tail sj) dj =
      canonicalTape (before ++ (destination ++ [active]) :: (source ++ [pending,off]) :: after) d := by
    rw [tape_around_adjacent]
    exact (canonical_adjacent_decompose before (destination ++ [active]) (source ++ [pending,off]) after d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+k3),?_,?_,combined⟩ <;> omega

#print axioms canonical_left_full_selector

theorem tail_frame_path (earlier : List (Term × Term)) (version junk : Term) :
    contextPath (tailFrames earlier version junk) = prefixPath earlier ++ nextCellPath := by
  simp [tailFrames,contextPath,framePath,prior_tape_frame_path,nextCellPath]

theorem target_after_prepend_cell (earlier : List (Term × Term)) (version target junk : Term) :
    termAt (prependTape earlier (frameTerm version target junk)) (prefixPath earlier ++ nextCellPath) = some target := by
  rw [term_at_append,term_at_prepend_tape]
  simp [nextCellPath,termAt,frameTerm,term_at_nil]

theorem source_at_prepend_cell (earlier : List (Term × Term)) (version target junk : Term) :
    readCellAt (prependTape earlier (frameTerm version target junk)) (prefixPath earlier) = some (cellFromVersion version) := by
  simp [readCellAt,term_at_prepend_tape,parse_frame]

theorem opening_choice_implies_closed (term : Term) (path : List Bool)
    (h : nextOpeningAddress term = some path) : parseFrame term = none := by
  cases hp : parseFrame term with
  | none => rfl
  | some data => simp [nextOpeningAddress,hp] at h

#print axioms tail_frame_path
#print axioms target_after_prepend_cell
#print axioms source_at_prepend_cell
#print axioms opening_choice_implies_closed

theorem pending_tail_step_is_full_selector (program : BinaryProgram)
    (earlier : List (Term × Term)) (version junk flag hubJunk : Term) (bit : Bool) (q : Nat) (a b : Term)
    (hflag : flagValue flag = false) (hpending : cellFromVersion version = ⟨bit,.movingRight,q⟩)
    (hstep : HubPendingTailStep earlier version junk flag hubJunk a b) :
    ∃ path, fullRootSelector program (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk) = some path ∧
      DirectedStep path (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk)
        (seedHubRoot flag (prependTape earlier (frameTerm version b junk)) hubJunk) := by
  obtain ⟨hpriority,rel,hlocal,hdir⟩ := hstep
  have hclosed : parseFrame a = none := opening_choice_implies_closed a rel hlocal
  have hsource : readCellAt (prependTape earlier (frameTerm version a junk)) (prefixPath earlier) =
      some ⟨bit,.movingRight,q⟩ := by rw [source_at_prepend_cell,hpending]
  have htarget : termAt (prependTape earlier (frameTerm version a junk)) (prefixPath earlier ++ nextCellPath) = some a :=
    target_after_prepend_cell earlier version a junk
  have hrootTarget : termAt (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk)
      (rootTapePath ++ (prefixPath earlier ++ nextCellPath)) = some a := by
    rw [term_at_seed_tape]
    exact htarget
  have hselected : fullRootSelector program (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk) =
      some ((rootTapePath ++ (prefixPath earlier ++ nextCellPath)) ++ rel) := by
    rw [full_selector_pending_branch program flag (prependTape earlier (frameTerm version a junk)) hubJunk
      (prefixPath earlier) hflag hpriority]
    simp [choosePending,hsource,pendingDestinationPath,htarget,hclosed,pendingPlan,isMoving,
      selectOpeningAt,hrootTarget,hlocal,List.append_assoc]
  refine ⟨(rootTapePath ++ (prefixPath earlier ++ nextCellPath)) ++ rel,hselected,?_⟩
  simpa [rootTapePath,tail_frame_path,List.append_assoc] using hdir

theorem pending_tail_trace_is_full_selector (program : BinaryProgram)
    (earlier : List (Term × Term)) (version junk flag hubJunk : Term) (bit : Bool) (q : Nat)
    (hflag : flagValue flag = false) (hpending : cellFromVersion version = ⟨bit,.movingRight,q⟩)
    {n : Nat} {a b : Term} (trace : HubPendingTailTrace earlier version junk flag hubJunk n a b) :
    FullSelectorTrace program n (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) hubJunk)
      (seedHubRoot flag (prependTape earlier (frameTerm version b junk)) hubJunk) := by
  induction trace with
  | zero x => exact FullSelectorTrace.zero _
  | @next n a b c hstep rest ih =>
    obtain ⟨path,hselect,hdir⟩ := pending_tail_step_is_full_selector program earlier version junk flag hubJunk bit q a b
      hflag hpending hstep
    exact FullSelectorTrace.next hselect hdir ih

#print axioms pending_tail_step_is_full_selector
#print axioms pending_tail_trace_is_full_selector

theorem canonical_right_extension_full_selector (program : BinaryProgram)
    (before : List (List UniversalCell)) (source : List UniversalCell)
    (d : Nat) (flag hubJunk : Term) (q : Fin 132) (bit written : Bool) (nextState : Fin 132)
    (hflag : parseFrame flag = none) (hbefore : AllOff before) (hsource : ActiveAt source q bit)
    (hrule : program q bit = some ⟨written,nextState,.right⟩) :
    let pending := pendingRightCell written nextState
    let active := activeCellRecord false nextState
    let off := offCellRecord written
    ∃ k, 24 ≤ k ∧ k ≤ 511 ∧
      FullSelectorTrace program k (canonicalRoot (before ++ [source]) d flag hubJunk)
        (canonicalRoot (before ++ [source ++ [pending,off],[active]]) d flag hubJunk) := by
  let pending := pendingRightCell written nextState
  let active := activeCellRecord false nextState
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
  let srcPath := prefixPath earlier
  let dstPath := srcPath ++ nextCellPath
  have hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off := canonical_prefix_off before d hbefore
  have hsourceStatus : (decodedCell source).status = .active := by rw [hsource]
  obtain ⟨k1,k2,k3,k4,t1,t2,t3,t4,hb1,hb2,hb3,hb4,hp0,hp4,readOff,readActive⟩ :=
    right_extension_in_seed_hub source sd td earlier sj flag hubJunk written nextState hprefix hsourceStatus
  have hv : flagValue flag = false := by simp [flagValue,hflag]
  have hs0 : cellFromVersion s0 = ⟨bit,.active,q.val⟩ := by simpa [s0,concrete_version_decodes,ActiveAt] using hsource
  have hs1 : cellFromVersion s1 = pending.val := by simp [s1,concrete_version_decodes,decoded_cell_append]
  have hblank : cellFromVersion blank = defaultCell := depth_child_is_blank (td+1)
  have hd1 : cellFromVersion d1 = active.val := by simpa [d1,concreteVersion,List.map_append] using readActive
  have hpriority1 : priorityConcretePath (tapeAroundVersion earlier s0 (depthBase td) sj) = .active srcPath := by
    rw [tape_around_single]
    exact hp0
  have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
  have hplan1 : activePlan srcPath srcPath.isEmpty
      (program ⟨(cellFromVersion s0).state,hstate⟩ (cellFromVersion s0).bit) = .append srcPath pending.val := by
    have hq : (⟨(cellFromVersion s0).state,hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
    have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
    rw [hq,hbit,hrule]
    rfl
  have f1 := active_global_trace_is_full_selector program earlier (depthBase td) sj s0 flag hubJunk pending.val
    hv hpriority1 hstate hplan1 (by simpa [encodedEntry,pending] using t1)
  have f2 := pending_tail_trace_is_full_selector program earlier s1 sj flag hubJunk written nextState.val
    hv (by simpa [pending,pendingRightCell] using hs1) t2
  have hmoving : isMoving (cellFromVersion s1).status = true := by rw [hs1]; rfl
  have hpending := prefixed_single_pending_priority earlier s1 cell0 sj hprefix hmoving
  have hpriority3 : priorityConcretePath (tapeAroundVersion (earlier ++ [(s1,sj)]) blank blank (depthJunk td)) = .pending srcPath := by
    rw [← adjacent_contexts_stitch earlier s1 blank blank sj (depthJunk td),tape_around_adjacent]
    exact hpending
  have hsource3 : ∀ v, cellFromVersion v = cellFromVersion blank →
      readCellAt (tapeAroundVersion (earlier ++ [(s1,sj)]) v blank (depthJunk td)) srcPath = some pending.val := by
    intro v heq
    rw [source_before_focused_cell_read,hs1]
  have hdest3 : pendingDestinationPath pending.val srcPath = some (prefixPath (earlier ++ [(s1,sj)])) := by
    rw [prefix_path_append_cell]
    rfl
  have htarget3 : ∀ v, cellFromVersion v = cellFromVersion blank →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion (earlier ++ [(s1,sj)]) v blank (depthJunk td))
          (prefixPath (earlier ++ [(s1,sj)])) = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion,targetTail,targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion blank := by
    intro v heq
    exact ⟨frameTerm v blank (depthJunk td),v,blank,depthJunk td,term_at_tape_around_cell _ _ _ _,parse_frame _ _ _,heq⟩
  have hplan3 : pendingPlan srcPath (prefixPath (earlier ++ [(s1,sj)])) pending.val (some (cellFromVersion blank)) =
      .append (prefixPath (earlier ++ [(s1,sj)])) active.val := by
    rw [hblank]
    exact pending_right_off_plan srcPath (prefixPath (earlier ++ [(s1,sj)])) written false nextState.val
  have f3 := pending_global_trace_general program (earlier ++ [(s1,sj)]) blank (depthJunk td) blank flag hubJunk
    active.val pending.val (cellFromVersion blank) srcPath (prefixPath (earlier ++ [(s1,sj)]))
    hv hpriority3 hsource3 hdest3 htarget3 hplan3 (by simpa [encodedEntry,active] using t3)
  have hpriority4 : priorityConcretePath (tapeAroundVersion earlier s1 cell1 sj) = .pending srcPath := by
    rw [tape_around_single]
    exact prefixed_single_pending_priority earlier s1 cell1 sj hprefix hmoving
  have hsource4 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      readCellAt (tapeAroundVersion earlier v cell1 sj) srcPath = some pending.val := by
    intro v heq
    rw [read_cell_at_tape_around,heq,hs1]
  have hdest4 : pendingDestinationPath pending.val srcPath = some dstPath := by rfl
  have htarget4 : ∀ v, cellFromVersion v = cellFromVersion s1 →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v cell1 sj) dstPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion,targetTail,targetJunk) ∧ cellFromVersion targetVersion = active.val := by
    intro v heq
    exact ⟨cell1,d1,blank,depthJunk td,target_after_focused_cell_term _ _ _ _ _ _,parse_frame _ _ _,hd1⟩
  have hplan4 : pendingPlan srcPath dstPath pending.val (some active.val) = .append srcPath off.val := by
    exact pending_right_done_plan srcPath dstPath written false nextState.val
  have f4 := pending_global_trace_general program earlier cell1 sj s1 flag hubJunk
    off.val pending.val active.val srcPath dstPath hv hpriority4 hsource4 hdest4 htarget4 hplan4
    (by simpa [encodedEntry,off] using t4)
  rw [← tape_around_single earlier s1 (depthBase td) sj, ← tape_around_single earlier s1 cell0 sj] at f2
  rw [show cell0 = frameTerm blank blank (depthJunk td) from rfl,
      adjacent_contexts_stitch earlier s1 blank blank sj (depthJunk td)] at f2
  rw [show cell1 = frameTerm d1 blank (depthJunk td) from rfl,
      adjacent_contexts_stitch earlier s1 d1 blank sj (depthJunk td)] at f4
  have combined := full_selector_trace_trans f1 (full_selector_trace_trans f2 (full_selector_trace_trans f3 f4))
  have hstart : tapeAroundVersion earlier s0 (depthBase td) sj = canonicalTape (before ++ [source]) d := by
    simpa [td,canonical_tape_nil] using (canonical_single_decompose before source [] d).symm
  have hend : tapeAroundVersion earlier s2 (frameTerm d1 blank (depthJunk td)) sj =
      canonicalTape (before ++ [source ++ [pending,off],[active]]) d := by
    rw [tape_around_adjacent]
    simpa [td,blank,d1,canonical_tape_nil] using
      (canonical_adjacent_decompose before (source ++ [pending,off]) [active] [] d).symm
  rw [hstart,hend] at combined
  refine ⟨k1+(k2+(k3+k4)),?_,?_,combined⟩
  · cases hb2 <;> omega
  · cases hb2 <;> omega

#print axioms canonical_right_extension_full_selector

theorem source_transition_full_selector (program : BinaryProgram) {start finish : List (List UniversalCell)}
    (h : SourceTransition program start finish) (d : Nat) (flag hubJunk : Term)
    (hflag : parseFrame flag = none) :
    ∃ k, 6 ≤ k ∧ k ≤ 511 ∧ FullSelectorTrace program k (canonicalRoot start d flag hubJunk) (canonicalRoot finish d flag hubJunk) := by
  cases h with
  | stay before source after q bit inst hbefore hsource hafter hrule hdir =>
    cases inst with
    | mk written nextState direction =>
      cases direction with
      | left => cases hdir
      | right => cases hdir
      | stay =>
        obtain ⟨k,lo,hi,trace⟩ := canonical_stay_full_selector program before source after d flag hubJunk q bit written nextState
          hflag hbefore hsource hafter hrule
        exact ⟨k,lo,by omega,trace⟩
  | leftBoundary source after q bit inst hsource hafter hrule hdir =>
    cases inst with
    | mk written nextState direction =>
      cases direction with
      | stay => cases hdir
      | right => cases hdir
      | left =>
        have hoff : AllOff ([] : List (List UniversalCell)) := by intro cell hc; simp at hc
        obtain ⟨k,lo,hi,trace⟩ := canonical_left_boundary_full_selector program [] source after d flag hubJunk q bit written nextState
          hflag rfl hoff hsource hafter hrule
        exact ⟨k,lo,by omega,trace⟩
  | rightExisting before source destination after q bit inst hbefore hsource hdest hafter hrule hdir =>
    cases inst with
    | mk written nextState direction =>
      cases direction with
      | stay => cases hdir
      | left => cases hdir
      | right =>
        obtain ⟨k,lo,hi,trace⟩ := canonical_right_full_selector program before source destination after d flag hubJunk q bit written nextState
          hflag hbefore hsource hdest hafter hrule
        exact ⟨k,by omega,by omega,trace⟩
  | rightExtend before source q bit inst hbefore hsource hrule hdir =>
    cases inst with
    | mk written nextState direction =>
      cases direction with
      | stay => cases hdir
      | left => cases hdir
      | right =>
        obtain ⟨k,lo,hi,trace⟩ := canonical_right_extension_full_selector program before source d flag hubJunk q bit written nextState
          hflag hbefore hsource hrule
        exact ⟨k,by omega,hi,trace⟩
  | leftExisting before destination source after q bit inst hbefore hdest hsource hafter hrule hdir =>
    cases inst with
    | mk written nextState direction =>
      cases direction with
      | stay => cases hdir
      | right => cases hdir
      | left =>
        obtain ⟨k,lo,hi,trace⟩ := canonical_left_full_selector program before destination source after d flag hubJunk q bit written nextState
          hflag hbefore hdest hsource hafter hrule
        exact ⟨k,by omega,by omega,trace⟩

#print axioms source_transition_full_selector

theorem finite_source_run_full_selector (program : BinaryProgram) {n : Nat}
    {start finish : List (List UniversalCell)} (run : SourceRun program n start finish)
    (d : Nat) (flag hubJunk : Term) (hflag : parseFrame flag = none) :
    ∃ k, 6*n ≤ k ∧ k ≤ 511*n ∧
      FullSelectorTrace program k (canonicalRoot start d flag hubJunk) (canonicalRoot finish d flag hubJunk) := by
  induction run with
  | zero state => exact ⟨0,by simp,by simp,FullSelectorTrace.zero _⟩
  | @next n a b c hstep rest ih =>
    obtain ⟨k1,lo1,hi1,first⟩ := source_transition_full_selector program hstep d flag hubJunk hflag
    obtain ⟨k2,lo2,hi2,remaining⟩ := ih
    refine ⟨k1+k2,?_,?_,full_selector_trace_trans first remaining⟩ <;> omega

#print axioms finite_source_run_full_selector

theorem finite_run_then_halt_full_selector (program : BinaryProgram) {n : Nat} {start : List (List UniversalCell)}
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (run : SourceRun program n start (before ++ source :: after))
    (q : Fin 132) (bit : Bool) (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after)
    (hstop : program q bit = none) (d flagDepth : Nat) (hubJunk : Term) :
    let tape := canonicalTape (before ++ source :: after) d
    let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2
    ∃ k, 6*n+6 ≤ k ∧ k ≤ 511*n+7 ∧
      FullSelectorTrace program k (canonicalRoot start d (depthBase flagDepth) hubJunk) (seedHubRoot flagOpen tape hubJunk) ∧
      rootHalt (seedHubRoot flagOpen tape hubJunk) = true := by
  let tape := canonicalTape (before ++ source :: after) d
  let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt flagDepth).1 (phaseAt flagDepth).2
  obtain ⟨k1,lo1,hi1,hfirst⟩ := finite_source_run_full_selector program run d (depthBase flagDepth) hubJunk (depth_base_closed flagDepth)
  obtain ⟨k2,lo2,hi2,hlast,hobserved⟩ :=
    stopped_boundary_full_selector program before source after q bit hb hs ha hstop d flagDepth hubJunk
  refine ⟨k1+k2,?_,?_,full_selector_trace_trans hfirst hlast,hobserved⟩ <;> omega

#print axioms finite_run_then_halt_full_selector

theorem directed_step_decompose (pref : List Bool) :
    ∀ (rel : List Bool) (a b : Term), DirectedStep (pref ++ rel) a b →
      ∃ x y, termAt a pref = some x ∧ termAt b pref = some y ∧
        DirectedStep rel x y ∧ replaceTermAt a pref y = some b := by
  induction pref with
  | nil =>
    intro rel a b h
    exact ⟨a,b,term_at_nil a,term_at_nil b,h,replace_at_nil a b⟩
  | cons side pref ih =>
    intro rel a b h
    cases side with
    | false =>
      cases h with
      | left hchild =>
        obtain ⟨x,y,hx,hy,hxy,hreplace⟩ := ih rel _ _ hchild
        refine ⟨x,y,?_,?_,hxy,?_⟩
        · simpa [termAt] using hx
        · simpa [termAt] using hy
        · simp [replaceTermAt,hreplace]
    | true =>
      cases h with
      | right hchild =>
        obtain ⟨x,y,hx,hy,hxy,hreplace⟩ := ih rel _ _ hchild
        refine ⟨x,y,?_,?_,hxy,?_⟩
        · simpa [termAt] using hx
        · simpa [termAt] using hy
        · simp [replaceTermAt,hreplace]

#print axioms directed_step_decompose

theorem full_selector_halt_persists_one_step (program : BinaryProgram) (flag tape hubJunk : Term)
    (hflag : flagValue flag = true) (path : List Bool) (out : Term)
    (hselect : fullRootSelector program (seedHubRoot flag tape hubJunk) = some path)
    (hstep : DirectedStep path (seedHubRoot flag tape hubJunk) out) :
    ∃ newFlag, out = seedHubRoot newFlag tape hubJunk ∧ flagValue newFlag = true := by
  cases hp : parseFrame flag with
  | none => simp [flagValue,hp] at hflag
  | some data =>
    rcases data with ⟨left,right,junk⟩
    have hflagEq := parse_frame_sound flag left right junk hp
    subst flag
    rw [full_selector_halt_branch program (frameTerm left right junk) tape hubJunk (by simp [flagValue,parse_frame])] at hselect
    let frontier := closedLeftFrontier left
    have hfront : closedLeftFrontier (frameTerm left right junk) = [false,true] ++ frontier := by rfl
    rw [hfront] at hselect
    unfold selectOpeningAt at hselect
    cases hat : termAt (seedHubRoot (frameTerm left right junk) tape hubJunk)
        (hubFlagPath ++ ([false,true] ++ frontier)) with
    | none =>
      simp only [List.cons_append,List.nil_append] at hat
      simp [hat] at hselect
    | some focus =>
      simp only [List.cons_append,List.nil_append] at hat
      cases hrel : nextOpeningAddress focus with
      | none => simp [hat,hrel] at hselect
      | some rel =>
        simp [hat,hrel] at hselect
        subst path
        have hstep' : DirectedStep ([true,false,true,false,true] ++ (frontier ++ rel))
            (seedHubRoot (frameTerm left right junk) tape hubJunk) out := by
          simpa [hubFlagPath,List.append_assoc] using hstep
        obtain ⟨x,y,_,_,_,hreplace⟩ := directed_step_decompose [true,false,true,false,true] (frontier ++ rel) _ _ hstep'
        have hshape : replaceTermAt (seedHubRoot (frameTerm left right junk) tape hubJunk)
            [true,false,true,false,true] y = some (seedHubRoot (frameTerm y right junk) tape hubJunk) := by
          simp [seedHubRoot,frameTerm,replaceTermAt,replace_at_nil]
        rw [hshape] at hreplace
        have hout : out = seedHubRoot (frameTerm y right junk) tape hubJunk := (Option.some.inj hreplace).symm
        refine ⟨frameTerm y right junk,hout,?_⟩
        simp [flagValue,parse_frame]

#print axioms full_selector_halt_persists_one_step

theorem full_selector_halt_persists_trace (program : BinaryProgram) {n : Nat} {initial final : Term}
    (trace : FullSelectorTrace program n initial final) :
    ∀ flag tape hubJunk, initial = seedHubRoot flag tape hubJunk → flagValue flag = true →
      ∃ finalFlag, final = seedHubRoot finalFlag tape hubJunk ∧ flagValue finalFlag = true := by
  induction trace with
  | zero a =>
    intro flag tape hubJunk hinit hflag
    subst a
    exact ⟨flag,rfl,hflag⟩
  | @next n a b c path hselect hstep rest ih =>
    intro flag tape hubJunk hinit hflag
    subst a
    obtain ⟨nextFlag,hb,hnext⟩ := full_selector_halt_persists_one_step program flag tape hubJunk hflag path b hselect hstep
    exact ih nextFlag tape hubJunk hb hnext

#print axioms full_selector_halt_persists_trace

theorem full_selector_step_unique (program : BinaryProgram) (a b c : Term) (p q : List Bool)
    (hs1 : fullRootSelector program a = some p) (hs2 : fullRootSelector program a = some q)
    (hd1 : DirectedStep p a b) (hd2 : DirectedStep q a c) : b = c := by
  rw [hs1] at hs2
  have hp : p = q := Option.some.inj hs2
  subst q
  exact directed_step_unique hd1 c hd2

theorem full_selector_trace_unique (program : BinaryProgram) {n : Nat} {a b : Term}
    (h : FullSelectorTrace program n a b) :
    ∀ c, FullSelectorTrace program n a c → b = c := by
  induction h with
  | zero a =>
    intro c hc
    cases hc
    rfl
  | @next n a b c path hs hd rest ih =>
    intro out hout
    cases hout with
    | @next _ _ mid _ path' hs' hd' tail =>
      have heq : b = mid := full_selector_step_unique program a b mid path path' hs hs' hd hd'
      subst mid
      exact ih out tail

#print axioms full_selector_step_unique
#print axioms full_selector_trace_unique

theorem full_selector_trace_split (program : BinaryProgram) (n m : Nat) {a b : Term}
    (trace : FullSelectorTrace program (n+m) a b) :
    ∃ middle, FullSelectorTrace program n a middle ∧ FullSelectorTrace program m middle b := by
  induction n generalizing a b with
  | zero =>
    refine ⟨a,FullSelectorTrace.zero _,?_⟩
    simpa using trace
  | succ n ih =>
    have heq : (n+1)+m = (n+m)+1 := by omega
    rw [heq] at trace
    cases trace with
    | @next _ _ mid _ path hselect hstep rest =>
      obtain ⟨middle,hpre,hsuf⟩ := ih rest
      exact ⟨middle,FullSelectorTrace.next hselect hstep hpre,hsuf⟩

#print axioms full_selector_trace_split

def wrappedHubRoot (header flag tape hubJunk : Term) : Term := header ⋅ frameTerm flag tape hubJunk

theorem wrapped_selector_halt_branch (program : BinaryProgram) (header flag tape junk : Term)
    (hflag : flagValue flag = true) :
    fullRootSelector program (wrappedHubRoot header flag tape junk) =
      selectOpeningAt (wrappedHubRoot header flag tape junk) (hubFlagPath ++ closedLeftFrontier flag) := by
  simp [fullRootSelector,termAt,rootHubPath,wrappedHubRoot,parse_frame,hflag]

#print axioms wrapped_selector_halt_branch

theorem wrapped_selector_halt_persists_one_step (program : BinaryProgram) (header flag tape hubJunk : Term)
    (hflag : flagValue flag = true) (path : List Bool) (out : Term)
    (hselect : fullRootSelector program (wrappedHubRoot header flag tape hubJunk) = some path)
    (hstep : DirectedStep path (wrappedHubRoot header flag tape hubJunk) out) :
    ∃ newFlag, out = wrappedHubRoot header newFlag tape hubJunk ∧ flagValue newFlag = true := by
  cases hp : parseFrame flag with
  | none => simp [flagValue,hp] at hflag
  | some data =>
    rcases data with ⟨left,right,junk⟩
    have hflagEq := parse_frame_sound flag left right junk hp
    subst flag
    rw [wrapped_selector_halt_branch program header (frameTerm left right junk) tape hubJunk (by simp [flagValue,parse_frame])] at hselect
    let frontier := closedLeftFrontier left
    have hfront : closedLeftFrontier (frameTerm left right junk) = [false,true] ++ frontier := by rfl
    rw [hfront] at hselect
    unfold selectOpeningAt at hselect
    cases hat : termAt (wrappedHubRoot header (frameTerm left right junk) tape hubJunk)
        (hubFlagPath ++ ([false,true] ++ frontier)) with
    | none =>
      simp only [List.cons_append,List.nil_append] at hat
      simp [hat] at hselect
    | some focus =>
      simp only [List.cons_append,List.nil_append] at hat
      cases hrel : nextOpeningAddress focus with
      | none => simp [hat,hrel] at hselect
      | some rel =>
        simp [hat,hrel] at hselect
        subst path
        have hstep' : DirectedStep ([true,false,true,false,true] ++ (frontier ++ rel))
            (wrappedHubRoot header (frameTerm left right junk) tape hubJunk) out := by
          simpa [hubFlagPath,List.append_assoc] using hstep
        obtain ⟨x,y,_,_,_,hreplace⟩ := directed_step_decompose [true,false,true,false,true] (frontier ++ rel) _ _ hstep'
        have hshape : replaceTermAt (wrappedHubRoot header (frameTerm left right junk) tape hubJunk)
            [true,false,true,false,true] y = some (wrappedHubRoot header (frameTerm y right junk) tape hubJunk) := by
          simp [wrappedHubRoot,frameTerm,replaceTermAt,replace_at_nil]
        rw [hshape] at hreplace
        have hout : out = wrappedHubRoot header (frameTerm y right junk) tape hubJunk := (Option.some.inj hreplace).symm
        refine ⟨frameTerm y right junk,hout,?_⟩
        simp [flagValue,parse_frame]


#print axioms wrapped_selector_halt_persists_one_step

theorem root_halt_decompose (term : Term) (h : rootHalt term = true) :
    ∃ header flag tape junk, term = wrappedHubRoot header flag tape junk ∧ flagValue flag = true := by
  cases term with
  | s => simp [rootHalt] at h
  | var i => simp [rootHalt] at h
  | app header hub =>
    cases hp : parseFrame hub with
    | none => simp [rootHalt,haltObserved,hp] at h
    | some data =>
      rcases data with ⟨flag,tape,junk⟩
      have hhub := parse_frame_sound hub flag tape junk hp
      have hflag : flagValue flag = true := by simpa [rootHalt,haltObserved,hp] using h
      exact ⟨header,flag,tape,junk,by simp [wrappedHubRoot,← hhub],hflag⟩

theorem full_selector_root_halt_persists_step (program : BinaryProgram) (a b : Term) (path : List Bool)
    (hhalt : rootHalt a = true) (hselect : fullRootSelector program a = some path) (hstep : DirectedStep path a b) :
    rootHalt b = true := by
  obtain ⟨header,flag,tape,junk,ha,hflag⟩ := root_halt_decompose a hhalt
  subst a
  obtain ⟨nextFlag,hb,hnext⟩ := wrapped_selector_halt_persists_one_step program header flag tape junk hflag path b hselect hstep
  rw [hb]
  simp [rootHalt,wrappedHubRoot,haltObserved,parse_frame,hnext]

theorem full_selector_root_halt_persists_trace (program : BinaryProgram) {n : Nat} {a b : Term}
    (trace : FullSelectorTrace program n a b) (hhalt : rootHalt a = true) : rootHalt b = true := by
  induction trace with
  | zero _ => exact hhalt
  | @next n a b c path hselect hstep rest ih =>
    exact ih (full_selector_root_halt_persists_step program a b path hhalt hselect hstep)

#print axioms root_halt_decompose
#print axioms full_selector_root_halt_persists_step
#print axioms full_selector_root_halt_persists_trace

theorem halt_cannot_precede_closed_checkpoint (program : BinaryProgram) (m n : Nat)
    (start reached checkpoint : Term) (hreach : FullSelectorTrace program m start reached)
    (hhalt : rootHalt reached = true) (hcheckpoint : FullSelectorTrace program n start checkpoint)
    (hle : m ≤ n) (hclosed : rootHalt checkpoint = false) : False := by
  have heq : n = m + (n-m) := by omega
  rw [heq] at hcheckpoint
  obtain ⟨middle,hbefore,hafter⟩ := full_selector_trace_split program m (n-m) hcheckpoint
  have hsame : reached = middle := full_selector_trace_unique program hreach middle hbefore
  subst middle
  have hfinal := full_selector_root_halt_persists_trace program hafter hhalt
  rw [hclosed] at hfinal
  cases hfinal

#print axioms halt_cannot_precede_closed_checkpoint

def SourceRunsForever (program : BinaryProgram) (start : List (List UniversalCell)) : Prop :=
  ∀ n, ∃ finish, SourceRun program n start finish

theorem forever_source_never_triggers_halt (program : BinaryProgram) (start : List (List UniversalCell))
    (hforever : SourceRunsForever program start) (d flagDepth : Nat) (hubJunk : Term)
    (m : Nat) (reached : Term)
    (htrace : FullSelectorTrace program m (canonicalRoot start d (depthBase flagDepth) hubJunk) reached) :
    rootHalt reached = false := by
  by_cases hhalt : rootHalt reached = true
  · obtain ⟨finish,run⟩ := hforever (m+1)
    obtain ⟨k,hlower,hupper,hcheckpoint⟩ := finite_source_run_full_selector program run d (depthBase flagDepth) hubJunk
      (depth_base_closed flagDepth)
    have hle : m ≤ k := by omega
    have hclosed : rootHalt (canonicalRoot finish d (depthBase flagDepth) hubJunk) = false := by
      unfold canonicalRoot
      rw [root_halt_seed]
      exact halt_field_closed_observation (depthBase flagDepth) _ hubJunk (depth_base_closed flagDepth)
    exact False.elim (halt_cannot_precede_closed_checkpoint program m k _ reached _ htrace hhalt hcheckpoint hle hclosed)
  · cases hh : rootHalt reached <;> simp_all

#print axioms forever_source_never_triggers_halt

def SourceStopped (program : BinaryProgram) (cells : List (List UniversalCell)) : Prop :=
  ∃ before source after q bit,
    cells = before ++ source :: after ∧ AllOff before ∧ ActiveAt source q bit ∧ AllOff after ∧ program q bit = none

def SourceEventuallyStops (program : BinaryProgram) (start : List (List UniversalCell)) : Prop :=
  ∃ n finish, SourceRun program n start finish ∧ SourceStopped program finish

theorem source_run_snoc (program : BinaryProgram) {n : Nat} {a b c : List (List UniversalCell)}
    (run : SourceRun program n a b) (step : SourceTransition program b c) : SourceRun program (n+1) a c := by
  induction run with
  | zero state => exact SourceRun.next step (SourceRun.zero _)
  | @next n a b c first rest ih =>
    exact SourceRun.next first (ih step)

theorem source_run_preserves_well_formed (program : BinaryProgram) {n : Nat}
    {start finish : List (List UniversalCell)} (run : SourceRun program n start finish)
    (hvalid : WellFormed start) : WellFormed finish := by
  induction run with
  | zero state => exact hvalid
  | @next n a b c first rest ih =>
    exact ih (source_transition_preserves_well_formed program first)

theorem no_source_halt_implies_forever (program : BinaryProgram) (start : List (List UniversalCell))
    (hvalid : WellFormed start) (hnot : ¬ SourceEventuallyStops program start) : SourceRunsForever program start := by
  intro n
  induction n with
  | zero => exact ⟨start,SourceRun.zero _⟩
  | succ n ih =>
    obtain ⟨finish,run⟩ := ih
    have hv : WellFormed finish := source_run_preserves_well_formed program run hvalid
    obtain ⟨before,source,after,q,bit,hfinish,hbefore,hsource,hafter⟩ := hv
    cases hrule : program q bit with
    | none =>
      exfalso
      apply hnot
      refine ⟨n,finish,run,before,source,after,q,bit,hfinish,hbefore,hsource,hafter,hrule⟩
    | some inst =>
      obtain ⟨next,hstep⟩ := defined_source_step_exists program before source after q bit inst hbefore hsource hafter hrule
      rw [← hfinish] at hstep
      exact ⟨next,source_run_snoc program run hstep⟩

#print axioms source_run_snoc
#print axioms source_run_preserves_well_formed
#print axioms no_source_halt_implies_forever

theorem source_halting_iff_selected_halt_event (program : BinaryProgram) (start : List (List UniversalCell))
    (hvalid : WellFormed start) (d flagDepth : Nat) (hubJunk : Term) :
    SourceEventuallyStops program start ↔
      ∃ k reached, FullSelectorTrace program k (canonicalRoot start d (depthBase flagDepth) hubJunk) reached ∧ rootHalt reached = true := by
  constructor
  · intro hstop
    obtain ⟨n,finish,run,before,source,after,q,bit,hfinish,hbefore,hsource,hafter,hrule⟩ := hstop
    subst finish
    obtain ⟨k,_,_,htrace,hhalt⟩ :=
      finite_run_then_halt_full_selector program before source after run q bit hbefore hsource hafter hrule d flagDepth hubJunk
    exact ⟨k,_,htrace,hhalt⟩
  · intro hevent
    obtain ⟨k,reached,htrace,hhalt⟩ := hevent
    classical
    by_cases hstop : SourceEventuallyStops program start
    · exact hstop
    · have hforever := no_source_halt_implies_forever program start hvalid hstop
      have hfalse := forever_source_never_triggers_halt program start hforever d flagDepth hubJunk k reached htrace
      rw [hfalse] at hhalt
      cases hhalt

#print axioms source_halting_iff_selected_halt_event
