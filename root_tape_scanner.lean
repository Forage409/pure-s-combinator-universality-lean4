import phase_layout
import s_record_bridge
import priority_scan

/- Structural (fuel-free) scan of a concrete S version chain. -/

def scanVersionTree (width : Nat) (current : Option (List Bool)) : Term → Option (List Bool)
  | .app (.app .s next) (.app (.app .s fields) _) =>
      let updated := match readFields width fields with | none => current | some bits => some bits
      scanVersionTree width updated next
  | _ => current

theorem scan_version_tree_closed (width : Nat) (current : Option (List Bool)) (term : Term)
    (h : parseFrame term = none) : scanVersionTree width current term = current := by
  unfold parseFrame at h
  unfold scanVersionTree
  split <;> simp_all

theorem scan_version_tree_frame (width : Nat) (current : Option (List Bool)) (next fields junk : Term) :
    scanVersionTree width current (frameTerm next fields junk) =
      scanVersionTree width (match readFields width fields with | none => current | some bits => some bits) next := by
  rfl

theorem scan_tree_committed_records {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) :
    ∀ term current, layoutMatches (versionLayout records) term →
      scanVersionTree width current term = newestRecords records current := by
  induction records with
  | nil =>
    intro term current h
    have hclosed : parseFrame term = none := h
    simpa [newestRecords] using scan_version_tree_closed width current term hclosed
  | cons entry rest ih =>
    intro term current h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hread : readFields width tr = some entry.val := by
      rw [matched_fields_read width (fieldsLayout entry.val) tr hr]
      simpa [entry.property] using read_layout_fields_complete entry.val
    simpa [scan_version_tree_frame,hread,newestRecords] using ih tl (some entry.val) hl

theorem scan_tree_partial_records {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (pref : List Bool)
    (hpref : pref.length ≤ width) :
    ∀ term current, layoutMatches (partialVersionLayout pref records) term →
      scanVersionTree width current term = newestRecords records current := by
  induction records with
  | nil =>
    intro term current h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hw : pref.length+(width-pref.length)=width := by omega
    have hread : readFields width tr = none := by
      rw [matched_fields_read width (partialFieldsLayout pref) tr hr, ← hw]
      exact read_layout_fields_incomplete pref (width-pref.length)
    have hclosed : parseFrame tl = none := hl
    simpa [scan_version_tree_frame,hread,newestRecords] using scan_version_tree_closed width current tl hclosed
  | cons entry rest ih =>
    intro term current h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hread : readFields width tr = some entry.val := by
      rw [matched_fields_read width (fieldsLayout entry.val) tr hr]
      simpa [entry.property] using read_layout_fields_complete entry.val
    simpa [scan_version_tree_frame,hread,newestRecords] using ih tl (some entry.val) hl

#print axioms scan_version_tree_closed
#print axioms scan_tree_committed_records
#print axioms scan_tree_partial_records

theorem scan_tree_universal_cells (cells : List UniversalCell) (term : Term)
    (h : layoutMatches (versionLayout (cells.map encodedEntry)) term) :
    (scanVersionTree 11 none term).bind decodeCellBits = newestCells cells none := by
  rw [scan_tree_committed_records (cells.map encodedEntry) term none h]
  exact newest_records_decode cells none

theorem scan_tree_universal_cells_partial (cells : List UniversalCell) (pref : List Bool)
    (hpref : pref.length ≤ 11) (term : Term)
    (h : layoutMatches (partialVersionLayout pref (cells.map encodedEntry)) term) :
    (scanVersionTree 11 none term).bind decodeCellBits = newestCells cells none := by
  rw [scan_tree_partial_records (cells.map encodedEntry) pref hpref term none h]
  exact newest_records_decode cells none

#print axioms scan_tree_universal_cells
#print axioms scan_tree_universal_cells_partial

def defaultCell : Cell := ⟨false,.off,0⟩

def cellFromVersion (version : Term) : Cell :=
  ((scanVersionTree 11 none version).bind decodeCellBits).getD defaultCell

def decodedCell (records : List UniversalCell) : Cell := (newestCells records none).getD defaultCell

def storageTapeLayout : List (List UniversalCell) → Layout
  | [] => .unopened
  | records :: rest => .opened (versionLayout (records.map encodedEntry)) (storageTapeLayout rest)

def findConcreteCell (pred : Cell → Bool) : Term → Option Nat
  | .app (.app .s version) (.app (.app .s rest) _) =>
      if pred (cellFromVersion version) then some 0 else (findConcreteCell pred rest).map Nat.succ
  | _ => none

theorem find_concrete_closed (pred : Cell → Bool) (term : Term) (h : parseFrame term = none) :
    findConcreteCell pred term = none := by
  unfold parseFrame at h
  unfold findConcreteCell
  split <;> simp_all

theorem find_concrete_frame (pred : Cell → Bool) (version rest junk : Term) :
    findConcreteCell pred (frameTerm version rest junk) =
      if pred (cellFromVersion version) then some 0 else (findConcreteCell pred rest).map Nat.succ := by
  rfl

theorem scan_concrete_tape (records : List (List UniversalCell)) (pred : Cell → Bool) :
    ∀ term, layoutMatches (storageTapeLayout records) term →
      findConcreteCell pred term = scanIndex pred (records.map decodedCell) := by
  induction records with
  | nil =>
    intro term h
    have hclosed : parseFrame term = none := h
    simpa [storageTapeLayout,scanIndex] using find_concrete_closed pred term hclosed
  | cons entry rest ih =>
    intro term h
    obtain ⟨version,tail,j,hparse,hversion,htail⟩ := h
    have hterm := parse_frame_sound term version tail j hparse
    subst term
    have hcell : cellFromVersion version = decodedCell entry := by
      unfold cellFromVersion decodedCell
      rw [scan_tree_universal_cells entry version hversion]
    simpa [find_concrete_frame,hcell,scanIndex] using
      congrArg (fun x => if pred (decodedCell entry) then some 0 else x.map Nat.succ) (ih tail htail)

#print axioms find_concrete_closed
#print axioms scan_concrete_tape

def priorityConcrete (tape : Term) : WorkChoice :=
  match findConcreteCell movingCell tape with
  | some i => .pending i
  | none => match findConcreteCell activeCell tape with
    | some i => .active i
    | none => .none

theorem concrete_priority_matches_decoded (records : List (List UniversalCell))
    (term : Term) (h : layoutMatches (storageTapeLayout records) term) :
    priorityConcrete term = priorityScan (records.map decodedCell) := by
  unfold priorityConcrete priorityScan
  rw [scan_concrete_tape records movingCell term h,scan_concrete_tape records activeCell term h]
  rfl

#print axioms concrete_priority_matches_decoded

inductive CellSlot where
  | stable : List UniversalCell → CellSlot
  | writing : List UniversalCell → {pref : List Bool // pref.length ≤ 11} → CellSlot

def slotRecords : CellSlot → List UniversalCell
  | .stable records => records
  | .writing records _ => records

def slotVersionLayout : CellSlot → Layout
  | .stable records => versionLayout (records.map encodedEntry)
  | .writing records pref => partialVersionLayout pref.val (records.map encodedEntry)

def slotDecoded (slot : CellSlot) : Cell := decodedCell (slotRecords slot)

def slotTapeLayout : List CellSlot → Layout
  | [] => .unopened
  | slot :: rest => .opened (slotVersionLayout slot) (slotTapeLayout rest)

theorem concrete_slot_decodes (slot : CellSlot) (term : Term)
    (h : layoutMatches (slotVersionLayout slot) term) : cellFromVersion term = slotDecoded slot := by
  cases slot with
  | stable records =>
    unfold cellFromVersion slotDecoded slotRecords decodedCell
    rw [scan_tree_universal_cells records term h]
  | writing records pref =>
    unfold cellFromVersion slotDecoded slotRecords decodedCell
    rw [scan_tree_universal_cells_partial records pref.val pref.property term h]

theorem scan_concrete_slots (slots : List CellSlot) (pred : Cell → Bool) :
    ∀ term, layoutMatches (slotTapeLayout slots) term →
      findConcreteCell pred term = scanIndex pred (slots.map slotDecoded) := by
  induction slots with
  | nil =>
    intro term h
    have hclosed : parseFrame term = none := h
    simpa [slotTapeLayout,scanIndex] using find_concrete_closed pred term hclosed
  | cons slot rest ih =>
    intro term h
    obtain ⟨version,tail,j,hparse,hversion,htail⟩ := h
    have hterm := parse_frame_sound term version tail j hparse
    subst term
    have hcell := concrete_slot_decodes slot version hversion
    simpa [find_concrete_frame,hcell,scanIndex] using
      congrArg (fun x => if pred (slotDecoded slot) then some 0 else x.map Nat.succ) (ih tail htail)

theorem concrete_priority_ignores_unfinished_record (slots : List CellSlot) (term : Term)
    (h : layoutMatches (slotTapeLayout slots) term) :
    priorityConcrete term = priorityScan (slots.map slotDecoded) := by
  unfold priorityConcrete priorityScan
  rw [scan_concrete_slots slots movingCell term h,scan_concrete_slots slots activeCell term h]
  rfl

#print axioms concrete_slot_decodes
#print axioms scan_concrete_slots
#print axioms concrete_priority_ignores_unfinished_record

theorem concrete_finds_pending (slots : List CellSlot) (term : Term)
    (h : layoutMatches (slotTapeLayout slots) term)
    (before after : List Cell) (target : Cell)
    (hdecoded : slots.map slotDecoded = before ++ target :: after)
    (hbefore : ∀ c ∈ before, movingCell c = false) (htarget : movingCell target = true) :
    priorityConcrete term = .pending before.length := by
  rw [concrete_priority_ignores_unfinished_record slots term h,hdecoded]
  exact pending_has_priority before after target hbefore htarget

theorem concrete_finds_active (slots : List CellSlot) (term : Term)
    (h : layoutMatches (slotTapeLayout slots) term)
    (before after : List Cell) (target : Cell)
    (hdecoded : slots.map slotDecoded = before ++ target :: after)
    (hnopending : ∀ c ∈ before ++ target :: after, movingCell c = false)
    (hbefore : ∀ c ∈ before, activeCell c = false) (htarget : activeCell target = true) :
    priorityConcrete term = .active before.length := by
  rw [concrete_priority_ignores_unfinished_record slots term h,hdecoded]
  exact active_selected_when_no_pending before after target hnopending hbefore htarget

#print axioms concrete_finds_pending
#print axioms concrete_finds_active

def seekConcreteCell (pred : Cell → Bool) : Term → Option (List Bool)
  | .app (.app .s version) (.app (.app .s rest) _) =>
      if pred (cellFromVersion version) then some []
      else (seekConcreteCell pred rest).map (fun p => [true,false,true] ++ p)
  | _ => none

theorem seek_concrete_closed (pred : Cell → Bool) (term : Term) (h : parseFrame term = none) :
    seekConcreteCell pred term = none := by
  unfold parseFrame at h
  unfold seekConcreteCell
  split <;> simp_all

theorem seek_concrete_frame (pred : Cell → Bool) (version rest junk : Term) :
    seekConcreteCell pred (frameTerm version rest junk) =
      if pred (cellFromVersion version) then some []
      else (seekConcreteCell pred rest).map (fun p => [true,false,true] ++ p) := by
  rfl

theorem seek_concrete_slots (slots : List CellSlot) (pred : Cell → Bool) :
    ∀ term, layoutMatches (slotTapeLayout slots) term →
      seekConcreteCell pred term =
        (scanIndex pred (slots.map slotDecoded)).map (fun i => physicalPath (List.replicate i true)) := by
  induction slots with
  | nil =>
    intro term h
    have hclosed : parseFrame term = none := h
    simpa [slotTapeLayout,scanIndex] using seek_concrete_closed pred term hclosed
  | cons slot rest ih =>
    intro term h
    obtain ⟨version,tail,j,hparse,hversion,htail⟩ := h
    have hterm := parse_frame_sound term version tail j hparse
    subst term
    have hcell := concrete_slot_decodes slot version hversion
    have htail' := ih tail htail
    cases hv : pred (slotDecoded slot) <;>
      simp [seek_concrete_frame,hcell,scanIndex,hv,htail',physicalPath,
        Option.map_map,Function.comp_def,List.replicate_succ]

#print axioms seek_concrete_closed
#print axioms seek_concrete_slots

inductive PathChoice where
  | pending : List Bool → PathChoice
  | active : List Bool → PathChoice
  | none : PathChoice
  deriving DecidableEq, Repr

def priorityConcretePath (term : Term) : PathChoice :=
  match seekConcreteCell movingCell term with
  | some path => .pending path
  | none => match seekConcreteCell activeCell term with
    | some path => .active path
    | none => .none

def workChoicePath : WorkChoice → PathChoice
  | .pending i => .pending (physicalPath (List.replicate i true))
  | .active i => .active (physicalPath (List.replicate i true))
  | .none => .none

theorem concrete_priority_path_matches_decoded (slots : List CellSlot) (term : Term)
    (h : layoutMatches (slotTapeLayout slots) term) :
    priorityConcretePath term = workChoicePath (priorityScan (slots.map slotDecoded)) := by
  unfold priorityConcretePath priorityScan
  rw [seek_concrete_slots slots movingCell term h,seek_concrete_slots slots activeCell term h]
  cases hm : scanIndex movingCell (List.map slotDecoded slots) <;>
    cases ha : scanIndex activeCell (List.map slotDecoded slots) <;>
    simp [workChoicePath]

#print axioms concrete_priority_path_matches_decoded

theorem scan_tree_uncommitted_fields {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (fields : Layout)
    (hfields : readLayoutFields width fields = none) :
    ∀ term current, layoutMatches (versionWithFields records fields) term →
      scanVersionTree width current term = newestRecords records current := by
  induction records with
  | nil =>
    intro term current h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hread : readFields width tr = none := by
      rw [matched_fields_read width fields tr hr]
      exact hfields
    have hclosed : parseFrame tl = none := hl
    simpa [scan_version_tree_frame,hread,newestRecords] using scan_version_tree_closed width current tl hclosed
  | cons entry rest ih =>
    intro term current h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hread : readFields width tr = some entry.val := by
      rw [matched_fields_read width (fieldsLayout entry.val) tr hr]
      simpa [entry.property] using read_layout_fields_complete entry.val
    simpa [scan_version_tree_frame,hread,newestRecords] using ih tl (some entry.val) hl

#print axioms scan_tree_uncommitted_fields

theorem fuel_free_append_and_fuel_free_read {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (d : Nat) :
    ∃ k, TreeAdaptiveNativeTrace width entry.val k
        (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2)
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) ∧
      6 ≤ k ∧ k ≤ 7*(2*width+2) ∧
      scanVersionTree width none
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) = some entry.val := by
  obtain ⟨k,htrace,hlower,hupper,_⟩ := fuel_free_native_version_append records entry d
  have hp := phase_at_good d
  have hm := finite_layout_decodes (versionLayout (records ++ [entry]))
    (phaseAt d).1 (phaseAt d).2 hp.1 hp.2
  refine ⟨k,htrace,hlower,hupper,?_⟩
  rw [scan_tree_committed_records (records ++ [entry]) _ none hm]
  exact newest_records_append records entry none

#print axioms fuel_free_append_and_fuel_free_read
