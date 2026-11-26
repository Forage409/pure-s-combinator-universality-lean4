import plain_tape
import fixed_binary_table

/- Specialize the checked selected-halting theorem to the fixed 132-state
   executable binary table. The universal-machine correspondence is separate. -/

def fixedBinaryProgram (q : Fin 132) (bit : Bool) : Option SourceInstruction := do
  let row ← fixedBinaryTable.find? (fun r => r.q == q.val && r.read == bit)
  if h : row.next < 132 then
    let direction := if row.move = -1 then SourceDirection.left
      else if row.move = 1 then SourceDirection.right else SourceDirection.stay
    some ⟨row.write,⟨row.next,h⟩,direction⟩
  else none

theorem fixed_binary_halt_iff_selected_event (initial : PlainConfig) (d flagDepth : Nat) (hubJunk : Term) :
    PlainEventuallyStops fixedBinaryProgram initial ↔
      ∃ k reached, FullSelectorTrace fixedBinaryProgram k
        (canonicalRoot (initialRecords initial) d (depthBase flagDepth) hubJunk) reached ∧ rootHalt reached = true :=
  plain_halting_iff_selected_halt fixedBinaryProgram initial d flagDepth hubJunk

#print axioms fixedBinaryProgram
#print axioms fixed_binary_halt_iff_selected_event
