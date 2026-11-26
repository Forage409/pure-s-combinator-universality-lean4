import move_transaction
import finite_selector_scan

/- Global pending-first source-head search on a finite decoded cell list.
   The connection to root walking in the concrete S occurrence tree is
   a separate lemma. -/

inductive WorkChoice where
  | pending : Nat → WorkChoice
  | active : Nat → WorkChoice
  | none : WorkChoice
  deriving DecidableEq, Repr

def activeCell (c : Cell) : Bool := c.status == .active
def movingCell (c : Cell) : Bool := isMoving c.status

def priorityScan (cells : List Cell) : WorkChoice :=
  match scanIndex movingCell cells with
  | some i => .pending i
  | none => match scanIndex activeCell cells with
    | some i => .active i
    | none => .none

theorem pending_has_priority (before after : List Cell) (target : Cell)
    (hbefore : ∀ c ∈ before, movingCell c = false) (htarget : movingCell target = true) :
    priorityScan (before ++ target :: after) = .pending before.length := by
  unfold priorityScan
  rw [scan_finds_first movingCell before after target hbefore htarget]

theorem active_selected_when_no_pending (before after : List Cell) (target : Cell)
    (hnopending : ∀ c ∈ before ++ target :: after, movingCell c = false)
    (hbefore : ∀ c ∈ before, activeCell c = false) (htarget : activeCell target = true) :
    priorityScan (before ++ target :: after) = .active before.length := by
  unfold priorityScan
  rw [scan_none_when_absent movingCell (before ++ target :: after) hnopending]
  rw [scan_finds_first activeCell before after target hbefore htarget]

theorem no_work_without_active_or_pending (cells : List Cell)
    (hmove : ∀ c ∈ cells, movingCell c = false)
    (hactive : ∀ c ∈ cells, activeCell c = false) : priorityScan cells = .none := by
  unfold priorityScan
  rw [scan_none_when_absent movingCell cells hmove,scan_none_when_absent activeCell cells hactive]

#print axioms pending_has_priority
#print axioms active_selected_when_no_pending
#print axioms no_work_without_active_or_pending
