import stable_global_scan

/- Finite control decisions at a source boundary or during a pending move.
   The general scanner and S-record operations are verified separately. -/

inductive SourceDirection where
  | left | stay | right
  deriving DecidableEq, Repr

structure SourceInstruction where
  write : Bool
  next : Fin 132
  direction : SourceDirection

inductive ControllerPlan where
  | halt
  | openDestination : List Bool → ControllerPlan
  | append : List Bool → Cell → ControllerPlan
  | invalid
  deriving DecidableEq, Repr

def activePlan (sourcePath : List Bool) (atLeftBoundary : Bool)
    (instruction : Option SourceInstruction) : ControllerPlan :=
  match instruction with
  | none => .halt
  | some inst =>
    match inst.direction with
    | .stay => .append sourcePath ⟨inst.write,.active,inst.next.val⟩
    | .left =>
      if atLeftBoundary then .append sourcePath ⟨inst.write,.active,inst.next.val⟩
      else .append sourcePath ⟨inst.write,.movingLeft,inst.next.val⟩
    | .right => .append sourcePath ⟨inst.write,.movingRight,inst.next.val⟩

def pendingPlan (sourcePath destinationPath : List Bool) (pending : Cell)
    (destination : Option Cell) : ControllerPlan :=
  if !isMoving pending.status then .invalid else
  match destination with
  | none => if pending.status == .movingRight then .openDestination destinationPath else .invalid
  | some cell =>
    if cell.status == .off then .append destinationPath ⟨cell.bit,.active,pending.state⟩
    else if cell.status == .active && cell.state == pending.state then
      .append sourcePath ⟨pending.bit,.off,0⟩
    else .invalid

theorem active_right_plan (path : List Bool) (b : Bool) (q : Fin 132) (boundary : Bool) :
    activePlan path boundary (some ⟨b,q,.right⟩) = .append path ⟨b,.movingRight,q.val⟩ := by rfl

theorem active_left_plan (path : List Bool) (b : Bool) (q : Fin 132) :
    activePlan path false (some ⟨b,q,.left⟩) = .append path ⟨b,.movingLeft,q.val⟩ := by rfl

theorem active_boundary_left_plan (path : List Bool) (b : Bool) (q : Fin 132) :
    activePlan path true (some ⟨b,q,.left⟩) = .append path ⟨b,.active,q.val⟩ := by rfl

theorem active_stay_plan (path : List Bool) (b : Bool) (q : Fin 132) (boundary : Bool) :
    activePlan path boundary (some ⟨b,q,.stay⟩) = .append path ⟨b,.active,q.val⟩ := by rfl

theorem missing_rule_plan (path : List Bool) (boundary : Bool) : activePlan path boundary none = .halt := by rfl

theorem pending_right_empty_plan (src dst : List Bool) (b : Bool) (q : Nat) :
    pendingPlan src dst ⟨b,.movingRight,q⟩ none = .openDestination dst := by rfl

theorem pending_right_off_plan (src dst : List Bool) (b old : Bool) (q : Nat) :
    pendingPlan src dst ⟨b,.movingRight,q⟩ (some ⟨old,.off,0⟩) = .append dst ⟨old,.active,q⟩ := by rfl

theorem pending_left_off_plan (src dst : List Bool) (b old : Bool) (q : Nat) :
    pendingPlan src dst ⟨b,.movingLeft,q⟩ (some ⟨old,.off,0⟩) = .append dst ⟨old,.active,q⟩ := by rfl

theorem pending_right_done_plan (src dst : List Bool) (b old : Bool) (q : Nat) :
    pendingPlan src dst ⟨b,.movingRight,q⟩ (some ⟨old,.active,q⟩) = .append src ⟨b,.off,0⟩ := by
  simp only [pendingPlan,isMoving,beq_self_eq_true, Bool.not_true, Bool.false_eq_true, Bool.true_and, ↓reduceIte]
  rfl

theorem pending_left_done_plan (src dst : List Bool) (b old : Bool) (q : Nat) :
    pendingPlan src dst ⟨b,.movingLeft,q⟩ (some ⟨old,.active,q⟩) = .append src ⟨b,.off,0⟩ := by
  simp only [pendingPlan,isMoving,beq_self_eq_true, Bool.not_true, Bool.false_eq_true, Bool.true_and, ↓reduceIte]
  rfl

#print axioms active_right_plan
#print axioms active_left_plan
#print axioms active_boundary_left_plan
#print axioms active_stay_plan
#print axioms missing_rule_plan
#print axioms pending_right_empty_plan
#print axioms pending_right_off_plan
#print axioms pending_left_off_plan
#print axioms pending_right_done_plan
#print axioms pending_left_done_plan

theorem pending_right_off_any_state (src dst : List Bool) (b old : Bool) (q oldState : Nat) :
    pendingPlan src dst ⟨b,.movingRight,q⟩ (some ⟨old,.off,oldState⟩) = .append dst ⟨old,.active,q⟩ := by rfl

theorem pending_left_off_any_state (src dst : List Bool) (b old : Bool) (q oldState : Nat) :
    pendingPlan src dst ⟨b,.movingLeft,q⟩ (some ⟨old,.off,oldState⟩) = .append dst ⟨old,.active,q⟩ := by rfl

#print axioms pending_right_off_any_state
#print axioms pending_left_off_any_state

theorem pending_right_off_general (src dst : List Bool) (b : Bool) (q : Nat) (c : Cell)
    (h : c.status = .off) :
    pendingPlan src dst ⟨b,.movingRight,q⟩ (some c) = .append dst ⟨c.bit,.active,q⟩ := by
  cases c with
  | mk bit status state => cases status <;> simp_all [pendingPlan,isMoving]

theorem pending_left_off_general (src dst : List Bool) (b : Bool) (q : Nat) (c : Cell)
    (h : c.status = .off) :
    pendingPlan src dst ⟨b,.movingLeft,q⟩ (some c) = .append dst ⟨c.bit,.active,q⟩ := by
  cases c with
  | mk bit status state => cases status <;> simp_all [pendingPlan,isMoving]

#print axioms pending_right_off_general
#print axioms pending_left_off_general

theorem right_three_phase_plans (sourcePath destinationPath : List Bool) (written : Bool)
    (q : Fin 132) (destination : Cell) (hoff : destination.status = .off) :
    activePlan sourcePath false (some ⟨written,q,.right⟩) =
      .append sourcePath (pendingRightCell written q).val ∧
    pendingPlan sourcePath destinationPath (pendingRightCell written q).val (some destination) =
      .append destinationPath (activeCellRecord destination.bit q).val ∧
    pendingPlan sourcePath destinationPath (pendingRightCell written q).val
      (some (activeCellRecord destination.bit q).val) = .append sourcePath (offCellRecord written).val := by
  constructor
  · rfl
  constructor
  · exact pending_right_off_general sourcePath destinationPath written q.val destination hoff
  · exact pending_right_done_plan sourcePath destinationPath written destination.bit q.val

theorem left_three_phase_plans (sourcePath destinationPath : List Bool) (written : Bool)
    (q : Fin 132) (destination : Cell) (hoff : destination.status = .off) :
    activePlan sourcePath false (some ⟨written,q,.left⟩) =
      .append sourcePath (pendingLeftCell written q).val ∧
    pendingPlan sourcePath destinationPath (pendingLeftCell written q).val (some destination) =
      .append destinationPath (activeCellRecord destination.bit q).val ∧
    pendingPlan sourcePath destinationPath (pendingLeftCell written q).val
      (some (activeCellRecord destination.bit q).val) = .append sourcePath (offCellRecord written).val := by
  constructor
  · rfl
  constructor
  · exact pending_left_off_general sourcePath destinationPath written q.val destination hoff
  · exact pending_left_done_plan sourcePath destinationPath written destination.bit q.val

#print axioms right_three_phase_plans
#print axioms left_three_phase_plans

theorem right_plans_match_prefixed_tape (earlier : List (Term × Term))
    (destination : List UniversalCell) (written : Bool) (q : Fin 132)
    (hdestination : (decodedCell destination).status = .off) :
    let src := prefixPath earlier
    let dst := prefixPath earlier ++ [true,false,true]
    activePlan src false (some ⟨written,q,.right⟩) =
      .append src (pendingRightCell written q).val ∧
    pendingPlan src dst (pendingRightCell written q).val (some (decodedCell destination)) =
      .append dst (activeCellRecord (decodedCell destination).bit q).val ∧
    pendingPlan src dst (pendingRightCell written q).val
      (some (activeCellRecord (decodedCell destination).bit q).val) = .append src (offCellRecord written).val := by
  exact right_three_phase_plans _ _ written q (decodedCell destination) hdestination

theorem left_plans_match_prefixed_tape (earlier : List (Term × Term))
    (destination : List UniversalCell) (written : Bool) (q : Fin 132)
    (hdestination : (decodedCell destination).status = .off) :
    let dst := prefixPath earlier
    let src := prefixPath earlier ++ [true,false,true]
    activePlan src false (some ⟨written,q,.left⟩) =
      .append src (pendingLeftCell written q).val ∧
    pendingPlan src dst (pendingLeftCell written q).val (some (decodedCell destination)) =
      .append dst (activeCellRecord (decodedCell destination).bit q).val ∧
    pendingPlan src dst (pendingLeftCell written q).val
      (some (activeCellRecord (decodedCell destination).bit q).val) = .append src (offCellRecord written).val := by
  exact left_three_phase_plans _ _ written q (decodedCell destination) hdestination

#print axioms right_plans_match_prefixed_tape
#print axioms left_plans_match_prefixed_tape
