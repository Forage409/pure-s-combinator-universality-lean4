import Std

/- Abstract committed-record transaction for a non-clamped head movement.
   Connection to actual protected S-tree decoding is a separate obligation. -/

inductive Status where
  | off | active | movingLeft | movingRight
  deriving DecidableEq, Repr

structure Cell where
  bit : Bool
  status : Status
  state : Nat
  deriving DecidableEq, Repr

abbrev Tape := Nat → Cell

def put (t : Tape) (i : Nat) (v : Cell) (j : Nat) : Cell :=
  if j = i then v else t j

def pendingCell (bit : Bool) (q : Nat) (s : Status) : Cell := ⟨bit,s,q⟩
def newActive (t : Tape) (j q : Nat) : Cell := ⟨(t j).bit,.active,q⟩
def oldOff (bit : Bool) : Cell := ⟨bit,.off,0⟩

def phase1 (t : Tape) (i : Nat) (bit : Bool) (q : Nat) (dir : Status) : Tape :=
  put t i (pendingCell bit q dir)

def phase2 (t : Tape) (i j : Nat) (bit : Bool) (q : Nat) (dir : Status) : Tape :=
  put (phase1 t i bit q dir) j (newActive t j q)

def phase3 (t : Tape) (i j : Nat) (bit : Bool) (q : Nat) (dir : Status) : Tape :=
  put (phase2 t i j bit q dir) i (oldOff bit)

theorem phase1_pending (t : Tape) (i : Nat) (bit : Bool) (q : Nat) (dir : Status) :
    phase1 t i bit q dir i = pendingCell bit q dir := by
  simp [phase1, put]

theorem phase1_target_unchanged (t : Tape) (i j : Nat) (bit : Bool) (q : Nat)
    (dir : Status) (h : j ≠ i) : phase1 t i bit q dir j = t j := by
  simp [phase1, put, h]

theorem phase2_pending_and_active (t : Tape) (i j : Nat) (bit : Bool)
    (q : Nat) (dir : Status) (h : i ≠ j) :
    phase2 t i j bit q dir i = pendingCell bit q dir ∧
    phase2 t i j bit q dir j = newActive t j q := by
  simp [phase2, phase1, put, h]

theorem phase3_commits_move (t : Tape) (i j : Nat) (bit : Bool)
    (q : Nat) (dir : Status) (h : i ≠ j) :
    phase3 t i j bit q dir i = oldOff bit ∧
    phase3 t i j bit q dir j = newActive t j q ∧
    (∀ k, k ≠ i → k ≠ j → phase3 t i j bit q dir k = t k) := by
  constructor
  · simp [phase3, put]
  constructor
  · simp [phase3, phase2, put, Ne.symm h]
  · intro k hi hj
    simp [phase3, phase2, phase1, put, hi, hj]

theorem phase3_unique_active (t : Tape) (i j : Nat) (bit : Bool)
    (q : Nat) (dir : Status) (h : i ≠ j)
    (hoff : ∀ k, k ≠ i → (t k).status = .off) :
    (phase3 t i j bit q dir j).status = .active ∧
    (∀ k, k ≠ j → (phase3 t i j bit q dir k).status = .off) := by
  obtain ⟨_, hj, others⟩ := phase3_commits_move t i j bit q dir h
  constructor
  · rw [hj]
    rfl
  · intro k hkj
    by_cases hki : k = i
    · subst k
      simp [phase3, put, oldOff]
    · rw [others k hki hkj]
      exact hoff k hki

#print axioms phase1_pending
#print axioms phase1_target_unchanged
#print axioms phase2_pending_and_active
#print axioms phase3_commits_move
#print axioms phase3_unique_active

theorem phase2_other_cells_unchanged (t : Tape) (i j k : Nat) (bit : Bool)
    (q : Nat) (dir : Status) (hi : k ≠ i) (hj : k ≠ j) :
    phase2 t i j bit q dir k = t k := by
  simp [phase2, phase1, put, hi, hj]

theorem pending_record_preserves_recovery_data (t : Tape) (i j : Nat)
    (bit : Bool) (q : Nat) (dir : Status) (h : i ≠ j) :
    (phase2 t i j bit q dir i).bit = bit ∧
    (phase2 t i j bit q dir i).state = q ∧
    (phase2 t i j bit q dir i).status = dir := by
  have hp := (phase2_pending_and_active t i j bit q dir h).1
  rw [hp]
  exact ⟨rfl,rfl,rfl⟩

#print axioms phase2_other_cells_unchanged
#print axioms pending_record_preserves_recovery_data

abbrev RecordTape := Nat → List (Option Cell)

def chooseRecord (old entry : Option Cell) : Option Cell :=
  match entry with
  | none => old
  | some x => some x

def recordValue (xs : List (Option Cell)) : Cell :=
  (xs.foldl chooseRecord none).getD ⟨false,.off,0⟩

def decodeRecords (t : RecordTape) : Tape := fun i => recordValue (t i)

def appendRecord (t : RecordTape) (i : Nat) (entry : Option Cell) : RecordTape :=
  fun j => if j = i then t j ++ [entry] else t j

theorem decode_uncommitted_append (t : RecordTape) (i : Nat) :
    decodeRecords (appendRecord t i none) = decodeRecords t := by
  funext j
  by_cases h : j = i
  · simp [decodeRecords, appendRecord, h, recordValue, List.foldl_append, chooseRecord]
  · simp [decodeRecords, appendRecord, h]

theorem decode_committed_append (t : RecordTape) (i : Nat) (v : Cell) :
    decodeRecords (appendRecord t i (some v)) = put (decodeRecords t) i v := by
  funext j
  by_cases h : j = i
  · simp [decodeRecords, appendRecord, h, recordValue, List.foldl_append, chooseRecord, put]
  · simp [decodeRecords, appendRecord, h, put]

def recordPhase1 (t : RecordTape) (i : Nat) (bit : Bool) (q : Nat) (dir : Status) : RecordTape :=
  appendRecord t i (some (pendingCell bit q dir))

def recordPhase2 (t : RecordTape) (i j : Nat) (bit : Bool) (q : Nat) (dir : Status) : RecordTape :=
  appendRecord (recordPhase1 t i bit q dir) j (some (newActive (decodeRecords t) j q))

def recordPhase3 (t : RecordTape) (i j : Nat) (bit : Bool) (q : Nat) (dir : Status) : RecordTape :=
  appendRecord (recordPhase2 t i j bit q dir) i (some (oldOff bit))

theorem decoded_record_phase3 (t : RecordTape) (i j : Nat) (bit : Bool)
    (q : Nat) (dir : Status) :
    decodeRecords (recordPhase3 t i j bit q dir) = phase3 (decodeRecords t) i j bit q dir := by
  unfold recordPhase3 recordPhase2 recordPhase1 phase3 phase2 phase1
  rw [decode_committed_append, decode_committed_append, decode_committed_append]

#print axioms decode_uncommitted_append
#print axioms decode_committed_append
#print axioms decoded_record_phase3

theorem decoded_record_move_has_unique_head (t : RecordTape) (i j : Nat)
    (bit : Bool) (q : Nat) (dir : Status) (h : i ≠ j)
    (hoff : ∀ k, k ≠ i → (decodeRecords t k).status = .off) :
    (decodeRecords (recordPhase3 t i j bit q dir) j).status = .active ∧
    (∀ k, k ≠ j → (decodeRecords (recordPhase3 t i j bit q dir) k).status = .off) := by
  rw [decoded_record_phase3]
  exact phase3_unique_active (decodeRecords t) i j bit q dir h hoff

theorem interrupted_record_move_is_invisible (t : RecordTape) (i j target : Nat)
    (bit : Bool) (q : Nat) (dir : Status) :
    decodeRecords (appendRecord (recordPhase2 t i j bit q dir) target none) =
      decodeRecords (recordPhase2 t i j bit q dir) :=
  decode_uncommitted_append (recordPhase2 t i j bit q dir) target

#print axioms decoded_record_move_has_unique_head
#print axioms interrupted_record_move_is_invisible

theorem decoded_record_phase1 (t : RecordTape) (i : Nat) (bit : Bool)
    (q : Nat) (dir : Status) :
    decodeRecords (recordPhase1 t i bit q dir) = phase1 (decodeRecords t) i bit q dir := by
  unfold recordPhase1 phase1
  exact decode_committed_append t i (pendingCell bit q dir)

theorem decoded_record_phase2 (t : RecordTape) (i j : Nat) (bit : Bool)
    (q : Nat) (dir : Status) :
    decodeRecords (recordPhase2 t i j bit q dir) = phase2 (decodeRecords t) i j bit q dir := by
  unfold recordPhase2 phase2
  rw [decode_committed_append, decoded_record_phase1]

theorem record_phase2_recovery (t : RecordTape) (i j : Nat) (bit : Bool)
    (q : Nat) (dir : Status) (h : i ≠ j) :
    (decodeRecords (recordPhase2 t i j bit q dir) i).bit = bit ∧
    (decodeRecords (recordPhase2 t i j bit q dir) i).state = q ∧
    (decodeRecords (recordPhase2 t i j bit q dir) i).status = dir := by
  rw [decoded_record_phase2]
  exact pending_record_preserves_recovery_data (decodeRecords t) i j bit q dir h

#print axioms decoded_record_phase1
#print axioms decoded_record_phase2
#print axioms record_phase2_recovery

inductive MoveDecision where
  | markPending | activateTarget | clearOld | boundary
  deriving DecidableEq, Repr

def isMoving : Status → Bool
  | .movingLeft | .movingRight => true
  | _ => false

def decideMove (t : Tape) (i j : Nat) : MoveDecision :=
  if isMoving (t i).status then
    if (t j).status == .active then .clearOld else .activateTarget
  else if (t i).status == .active then .markPending else .boundary

theorem decide_before_move (t : Tape) (i j : Nat) (h : (t i).status = .active) :
    decideMove t i j = .markPending := by
  simp [decideMove, h, isMoving]

theorem decide_after_pending (t : Tape) (i j : Nat) (bit : Bool) (q : Nat)
    (dir : Status) (hij : i ≠ j) (hmove : isMoving dir = true)
    (hoff : (t j).status = .off) :
    decideMove (phase1 t i bit q dir) i j = .activateTarget := by
  have hp := phase1_pending t i bit q dir
  have ht := phase1_target_unchanged t i j bit q dir (Ne.symm hij)
  simp [decideMove, hp, ht, pendingCell, hmove, hoff]

theorem decide_after_target (t : Tape) (i j : Nat) (bit : Bool) (q : Nat)
    (dir : Status) (hij : i ≠ j) (hmove : isMoving dir = true) :
    decideMove (phase2 t i j bit q dir) i j = .clearOld := by
  obtain ⟨hp,ht⟩ := phase2_pending_and_active t i j bit q dir hij
  simp [decideMove, hp, ht, pendingCell, newActive, hmove]

theorem decide_after_commit (t : Tape) (i j : Nat) (bit : Bool) (q : Nat)
    (dir : Status) (hij : i ≠ j) :
    decideMove (phase3 t i j bit q dir) i j = .boundary := by
  have hp := (phase3_commits_move t i j bit q dir hij).1
  simp [decideMove, hp, oldOff, isMoving]

#print axioms decide_before_move
#print axioms decide_after_pending
#print axioms decide_after_target
#print axioms decide_after_commit

theorem record_pending_decision (t : RecordTape) (i j : Nat) (bit : Bool) (q : Nat)
    (dir : Status) (hij : i ≠ j) (hmove : isMoving dir = true)
    (hoff : (decodeRecords t j).status = .off) :
    decideMove (decodeRecords (recordPhase1 t i bit q dir)) i j = .activateTarget := by
  rw [decoded_record_phase1]
  exact decide_after_pending (decodeRecords t) i j bit q dir hij hmove hoff

theorem record_target_decision (t : RecordTape) (i j : Nat) (bit : Bool) (q : Nat)
    (dir : Status) (hij : i ≠ j) (hmove : isMoving dir = true) :
    decideMove (decodeRecords (recordPhase2 t i j bit q dir)) i j = .clearOld := by
  rw [decoded_record_phase2]
  exact decide_after_target (decodeRecords t) i j bit q dir hij hmove

theorem interrupted_record_keeps_decision (t : RecordTape) (slot i j : Nat) :
    decideMove (decodeRecords (appendRecord t slot none)) i j = decideMove (decodeRecords t) i j := by
  rw [decode_uncommitted_append]

#print axioms record_pending_decision
#print axioms record_target_decision
#print axioms interrupted_record_keeps_decision
