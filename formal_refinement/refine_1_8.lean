import fixed_u_program
import formal_symbolic.sym_1_8
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

theorem source_1_8_refines (left right : List (Fin 11)) :
    ∃ u' out, uNext ⟨left,8,right,1⟩ = some u' ∧
      iteratePlain fixedBinaryProgram 10 (encodeUConfig ⟨left,8,right,1⟩) = some out ∧ PlainEq out (encodeUConfig u') := by
  have hs0 : symbolBitAt (8 : Fin 11) 0 = true := by decide
  have hs1 : symbolBitAt (8 : Fin 11) 1 = false := by decide
  have hs2 : symbolBitAt (8 : Fin 11) 2 = false := by decide
  have hs3 : symbolBitAt (8 : Fin 11) 3 = false := by decide
  have hstart : binaryStartState (1 : Fin 3) = (54 : Fin 132) := by decide
  have hnext : binaryStartState (1 : Fin 3) = (54 : Fin 132) := by decide
  have hblock : symbolBlock (8 : Fin 11) = [true,false,false,false] := by decide
  cases right with
  | nil =>
    let out : PlainConfig := ⟨flattenSymbols left.reverse ++ [true,false,false,false],false,[],(54 : Fin 132)⟩
    refine ⟨⟨(8 : Fin 11)::left,0,[],1⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,out,hs0,hs1,hs2,hs3,hstart,hnext] using u_1_8_right (flattenSymbols left.reverse) []
    · simpa [out,hblock,hnext] using encode_u_right_empty_equiv left (8 : Fin 11) (1 : Fin 3)
  | cons b rest =>
    let out : PlainConfig := ⟨flattenSymbols left.reverse ++ [true,false,false,false],symbolBitAt b 0,
      [symbolBitAt b 1,symbolBitAt b 2,symbolBitAt b 3] ++ flattenSymbols rest,(54 : Fin 132)⟩
    refine ⟨⟨(8 : Fin 11)::left,b,rest,1⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,symbolBlock,out,hs0,hs1,hs2,hs3,hstart,hnext] using
        u_1_8_right (flattenSymbols left.reverse) (symbolBlock b ++ flattenSymbols rest)
    · simpa [out,hblock,hnext] using encode_u_right_nonempty_equiv left rest (8 : Fin 11) b (1 : Fin 3)

#print axioms source_1_8_refines
