import fixed_u_program
import formal_symbolic.sym_1_10
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

theorem source_1_10_refines (left right : List (Fin 11)) :
    ∃ u' out, uNext ⟨left,10,right,1⟩ = some u' ∧
      iteratePlain fixedBinaryProgram 10 (encodeUConfig ⟨left,10,right,1⟩) = some out ∧ PlainEq out (encodeUConfig u') := by
  have hs0 : symbolBitAt (10 : Fin 11) 0 = true := by decide
  have hs1 : symbolBitAt (10 : Fin 11) 1 = false := by decide
  have hs2 : symbolBitAt (10 : Fin 11) 2 = true := by decide
  have hs3 : symbolBitAt (10 : Fin 11) 3 = false := by decide
  have hstart : binaryStartState (1 : Fin 3) = (54 : Fin 132) := by decide
  have hnext : binaryStartState (2 : Fin 3) = (55 : Fin 132) := by decide
  have hblock : symbolBlock (7 : Fin 11) = [false,true,true,true] := by decide
  cases right with
  | nil =>
    let out : PlainConfig := ⟨flattenSymbols left.reverse ++ [false,true,true,true],false,[],(55 : Fin 132)⟩
    refine ⟨⟨(7 : Fin 11)::left,0,[],2⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,out,hs0,hs1,hs2,hs3,hstart,hnext] using u_1_10_right (flattenSymbols left.reverse) []
    · simpa [out,hblock,hnext] using encode_u_right_empty_equiv left (7 : Fin 11) (2 : Fin 3)
  | cons b rest =>
    let out : PlainConfig := ⟨flattenSymbols left.reverse ++ [false,true,true,true],symbolBitAt b 0,
      [symbolBitAt b 1,symbolBitAt b 2,symbolBitAt b 3] ++ flattenSymbols rest,(55 : Fin 132)⟩
    refine ⟨⟨(7 : Fin 11)::left,b,rest,2⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,symbolBlock,out,hs0,hs1,hs2,hs3,hstart,hnext] using
        u_1_10_right (flattenSymbols left.reverse) (symbolBlock b ++ flattenSymbols rest)
    · simpa [out,hblock,hnext] using encode_u_right_nonempty_equiv left rest (7 : Fin 11) b (2 : Fin 3)

#print axioms source_1_10_refines
