import fixed_u_program
import formal_symbolic.sym_halt

set_option maxRecDepth 20000

theorem source_2_9_stops (left right : List (Fin 11)) :
    uNext ⟨left,9,right,2⟩ = none ∧
      ∃ mid, iteratePlain fixedBinaryProgram 6 (encodeUConfig ⟨left,9,right,2⟩) = some mid ∧
        plainNext fixedBinaryProgram mid = none := by
  have hs0 : symbolBitAt (9 : Fin 11) 0 = true := by decide
  have hs1 : symbolBitAt (9 : Fin 11) 1 = false := by decide
  have hs2 : symbolBitAt (9 : Fin 11) 2 = false := by decide
  have hs3 : symbolBitAt (9 : Fin 11) 3 = true := by decide
  have hstart : binaryStartState (2 : Fin 3) = (55 : Fin 132) := by decide
  refine ⟨rfl,⟨flattenSymbols left.reverse,true,false :: false :: true :: flattenSymbols right,(41 : Fin 132)⟩,?_,?_⟩
  · simpa [encodeUConfig,hs0,hs1,hs2,hs3,hstart] using u_2_9_rewind (flattenSymbols left.reverse) (flattenSymbols right)
  · simp [plainNext]

#print axioms source_2_9_stops
