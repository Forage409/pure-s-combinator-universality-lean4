import fixed_u_program
import formal_symbolic.sym_2_7
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

theorem source_2_7_refines (left right : List (Fin 11)) :
    ∃ u' out, uNext ⟨left,7,right,2⟩ = some u' ∧
      iteratePlain fixedBinaryProgram 10 (encodeUConfig ⟨left,7,right,2⟩) = some out ∧ PlainEq out (encodeUConfig u') := by
  have hs0 : symbolBitAt (7 : Fin 11) 0 = false := by decide
  have hs1 : symbolBitAt (7 : Fin 11) 1 = true := by decide
  have hs2 : symbolBitAt (7 : Fin 11) 2 = true := by decide
  have hs3 : symbolBitAt (7 : Fin 11) 3 = true := by decide
  have hstart : binaryStartState (2 : Fin 3) = (55 : Fin 132) := by decide
  have hnext : binaryStartState (2 : Fin 3) = (55 : Fin 132) := by decide
  have hblock : symbolBlock (0 : Fin 11) = [false,false,false,false] := by decide
  cases left with
  | nil =>
    let out : PlainConfig := ⟨[],false,false :: false :: false :: flattenSymbols right,(55 : Fin 132)⟩
    refine ⟨⟨[],0,right,2⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,out,hs0,hs1,hs2,hs3,hstart,hnext] using u_2_7_boundary (flattenSymbols right)
    · have hw0 : symbolBitAt (0 : Fin 11) 0 = false := by decide
      have hw1 : symbolBitAt (0 : Fin 11) 1 = false := by decide
      have hw2 : symbolBitAt (0 : Fin 11) 2 = false := by decide
      have hw3 : symbolBitAt (0 : Fin 11) 3 = false := by decide
      simpa [out,hnext,hw0,hw1,hw2,hw3] using encode_u_left_boundary_equiv right (0 : Fin 11) (2 : Fin 3)
  | cons previous rest =>
    let out : PlainConfig := ⟨flattenSymbols rest.reverse,symbolBitAt previous 0,
      [symbolBitAt previous 1,symbolBitAt previous 2,symbolBitAt previous 3,false,false,false,false] ++ flattenSymbols right,
      (55 : Fin 132)⟩
    refine ⟨⟨rest,previous,(0 : Fin 11)::right,2⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,symbolBlock,out,List.reverse_cons,List.flatMap_append,hs0,hs1,hs2,hs3,hstart,hnext] using
        u_2_7_left (flattenSymbols rest.reverse) (flattenSymbols right)
          (symbolBitAt previous 0) (symbolBitAt previous 1) (symbolBitAt previous 2) (symbolBitAt previous 3)
    · simpa [out,hblock,hnext,List.append_assoc] using
        encode_u_left_nonempty_equiv rest right previous (0 : Fin 11) (2 : Fin 3)

#print axioms source_2_7_refines
