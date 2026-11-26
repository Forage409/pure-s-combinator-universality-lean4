import protected_opening
import move_transaction

/- Bridges the concrete S-tree version decoder to abstract transaction cells.
   Binary state bits are represented as a list; a separate encoding routine
   must supply a list that decodes to the desired finite state number. -/

def stateNumber (bits : List Bool) : Nat :=
  bits.foldl (fun n b => 2*n + if b then 1 else 0) 0

def statusBits : Status → Bool × Bool
  | .off => (false,false)
  | .active => (false,true)
  | .movingLeft => (true,false)
  | .movingRight => (true,true)

def bitsStatus (a b : Bool) : Status :=
  if a then (if b then .movingRight else .movingLeft)
  else (if b then .active else .off)

def encodeCellBits (c : Cell) (stateBits : List Bool) : List Bool :=
  let code := statusBits c.status
  c.bit :: code.1 :: code.2 :: stateBits

def decodeCellBits : List Bool → Option Cell
  | b :: x :: y :: stateBits => some ⟨b,bitsStatus x y,stateNumber stateBits⟩
  | _ => none

def readSCell (width : Nat) (term : Term) : Option Cell :=
  (readVersion width term).bind decodeCellBits

theorem status_roundtrip (s : Status) : bitsStatus (statusBits s).1 (statusBits s).2 = s := by
  cases s <;> rfl

theorem cell_bit_roundtrip (c : Cell) (stateBits : List Bool)
    (hs : stateNumber stateBits = c.state) :
    decodeCellBits (encodeCellBits c stateBits) = some c := by
  cases c with
  | mk bit status state =>
    cases status <;> simp [encodeCellBits, statusBits, decodeCellBits, bitsStatus, hs]

theorem committed_s_cell_read (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (depth : Nat) (next : Term)
    (c : Cell) (stateBits : List Bool) (hs : stateNumber stateBits = c.state) :
    readSCell (encodeCellBits c stateBits).length
      (indexedVersion base junk depth next (encodeCellBits c stateBits)) = some c := by
  unfold readSCell
  rw [committed_version_readable base junk hbase]
  simp [cell_bit_roundtrip c stateBits hs]

theorem incomplete_s_cell_invisible (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (depth remaining : Nat)
    (next : Term) (pref : List Bool) :
    readSCell (pref.length + remaining) (indexedPartialVersion base junk depth next pref) = none := by
  unfold readSCell
  rw [incomplete_version_invisible base junk hbase]
  rfl

#print axioms status_roundtrip
#print axioms cell_bit_roundtrip
#print axioms committed_s_cell_read
#print axioms incomplete_s_cell_invisible

def stateBits8 (n : Nat) : List Bool :=
  (List.range 8).map (fun i => decide ((n / 2^(7-i)) % 2 = 1))

theorem stateBits8_width (n : Nat) : (stateBits8 n).length = 8 := by
  simp [stateBits8]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem fixed_universal_states_roundtrip :
    ∀ q : Fin 132, stateNumber (stateBits8 q.val) = q.val := by
  decide

#print axioms stateBits8_width
#print axioms fixed_universal_states_roundtrip

theorem fixed_cell_width (bit : Bool) (s : Status) (q : Fin 132) :
    (encodeCellBits ⟨bit,s,q.val⟩ (stateBits8 q.val)).length = 11 := by
  cases s <;> simp [encodeCellBits, statusBits, stateBits8_width]

theorem fixed_universal_cell_read (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (depth : Nat) (next : Term)
    (bit : Bool) (s : Status) (q : Fin 132) :
    readSCell 11 (indexedVersion base junk depth next
      (encodeCellBits ⟨bit,s,q.val⟩ (stateBits8 q.val))) = some ⟨bit,s,q.val⟩ := by
  have hread := committed_s_cell_read base junk hbase depth next
    ⟨bit,s,q.val⟩ (stateBits8 q.val) (fixed_universal_states_roundtrip q)
  simpa [fixed_cell_width] using hread

#print axioms fixed_cell_width
#print axioms fixed_universal_cell_read

abbrev UniversalCell := {c : Cell // c.state < 132}

def encodedEntry (c : UniversalCell) : {bits : List Bool // bits.length = 11} :=
  ⟨encodeCellBits c.val (stateBits8 c.val.state), by
    simp [encodeCellBits, stateBits8_width]⟩

theorem encoded_entry_roundtrip (c : UniversalCell) :
    decodeCellBits (encodedEntry c).val = some c.val := by
  exact cell_bit_roundtrip c.val (stateBits8 c.val.state)
    (fixed_universal_states_roundtrip ⟨c.val.state,c.property⟩)

def newestCells : List UniversalCell → Option Cell → Option Cell
  | [], current => current
  | entry :: rest, _ => newestCells rest (some entry.val)

theorem newest_records_decode (cells : List UniversalCell) (start : Option (List Bool)) :
    (newestRecords (cells.map encodedEntry) start).bind decodeCellBits =
      newestCells cells (start.bind decodeCellBits) := by
  induction cells generalizing start with
  | nil => rfl
  | cons entry rest ih =>
    simp [newestRecords, newestCells, ih, encoded_entry_roundtrip]

theorem scan_s_chain_decodes_newest (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (depth : Nat)
    (cells : List UniversalCell) :
    let entries := cells.map encodedEntry
    (scanVersions (entries.length+1) 11 (versionChain base junk 11 depth entries) none).bind decodeCellBits =
      newestCells cells none := by
  dsimp only
  rw [scan_committed_version_chain base junk hbase]
  exact newest_records_decode cells none

#print axioms encoded_entry_roundtrip
#print axioms newest_records_decode
#print axioms scan_s_chain_decodes_newest

theorem scan_s_chain_ignores_incomplete_write (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (depth : Nat)
    (cells : List UniversalCell) (pref : List Bool) (hpref : pref.length ≤ 11) :
    let entries := cells.map encodedEntry
    (scanVersions (entries.length+2) 11 (versionChainPartial base junk 11 pref depth entries) none).bind decodeCellBits =
      newestCells cells none := by
  dsimp only
  rw [scan_chain_ignores_partial_tail base junk hbase 11 pref hpref]
  exact newest_records_decode cells none

#print axioms scan_s_chain_ignores_incomplete_write
