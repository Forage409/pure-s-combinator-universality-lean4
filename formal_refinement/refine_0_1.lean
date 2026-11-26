import fixed_u_program
import formal_symbolic.sym_0_1
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

theorem source_0_1_refines (left right : List (Fin 11)) :
    ∃ u' out, uNext ⟨left,1,right,0⟩ = some u' ∧
      iteratePlain fixedBinaryProgram 10 (encodeUConfig ⟨left,1,right,0⟩) = some out ∧ PlainEq out (encodeUConfig u') := by
  have hs0 : symbolBitAt (1 : Fin 11) 0 = false := by decide
  have hs1 : symbolBitAt (1 : Fin 11) 1 = false := by decide
  have hs2 : symbolBitAt (1 : Fin 11) 2 = false := by decide
  have hs3 : symbolBitAt (1 : Fin 11) 3 = true := by decide
  have hstart : binaryStartState (0 : Fin 3) = (0 : Fin 132) := by decide
  have hnext : binaryStartState (1 : Fin 3) = (54 : Fin 132) := by decide
  have hblock : symbolBlock (6 : Fin 11) = [false,true,true,false] := by decide
  cases right with
  | nil =>
    let out : PlainConfig := ⟨flattenSymbols left.reverse ++ [false,true,true,false],false,[],(54 : Fin 132)⟩
    refine ⟨⟨(6 : Fin 11)::left,0,[],1⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,out,hs0,hs1,hs2,hs3,hstart,hnext] using u_0_1_right (flattenSymbols left.reverse) []
    · simpa [out,hblock,hnext] using encode_u_right_empty_equiv left (6 : Fin 11) (1 : Fin 3)
  | cons b rest =>
    let out : PlainConfig := ⟨flattenSymbols left.reverse ++ [false,true,true,false],symbolBitAt b 0,
      [symbolBitAt b 1,symbolBitAt b 2,symbolBitAt b 3] ++ flattenSymbols rest,(54 : Fin 132)⟩
    refine ⟨⟨(6 : Fin 11)::left,b,rest,1⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,symbolBlock,out,hs0,hs1,hs2,hs3,hstart,hnext] using
        u_0_1_right (flattenSymbols left.reverse) (symbolBlock b ++ flattenSymbols rest)
    · simpa [out,hblock,hnext] using encode_u_right_nonempty_equiv left rest (6 : Fin 11) b (1 : Fin 3)

#print axioms source_0_1_refines
