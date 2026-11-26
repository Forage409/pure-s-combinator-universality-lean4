import fixed_u_program
import formal_symbolic.sym_1_6
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

theorem source_1_6_refines (left right : List (Fin 11)) :
    ∃ u' out, uNext ⟨left,6,right,1⟩ = some u' ∧
      iteratePlain fixedBinaryProgram 10 (encodeUConfig ⟨left,6,right,1⟩) = some out ∧ PlainEq out (encodeUConfig u') := by
  have hs0 : symbolBitAt (6 : Fin 11) 0 = false := by decide
  have hs1 : symbolBitAt (6 : Fin 11) 1 = true := by decide
  have hs2 : symbolBitAt (6 : Fin 11) 2 = true := by decide
  have hs3 : symbolBitAt (6 : Fin 11) 3 = false := by decide
  have hstart : binaryStartState (1 : Fin 3) = (54 : Fin 132) := by decide
  have hnext : binaryStartState (1 : Fin 3) = (54 : Fin 132) := by decide
  have hblock : symbolBlock (4 : Fin 11) = [false,true,false,false] := by decide
  cases left with
  | nil =>
    let out : PlainConfig := ⟨[],false,true :: false :: false :: flattenSymbols right,(54 : Fin 132)⟩
    refine ⟨⟨[],4,right,1⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,out,hs0,hs1,hs2,hs3,hstart,hnext] using u_1_6_boundary (flattenSymbols right)
    · have hw0 : symbolBitAt (4 : Fin 11) 0 = false := by decide
      have hw1 : symbolBitAt (4 : Fin 11) 1 = true := by decide
      have hw2 : symbolBitAt (4 : Fin 11) 2 = false := by decide
      have hw3 : symbolBitAt (4 : Fin 11) 3 = false := by decide
      simpa [out,hnext,hw0,hw1,hw2,hw3] using encode_u_left_boundary_equiv right (4 : Fin 11) (1 : Fin 3)
  | cons previous rest =>
    let out : PlainConfig := ⟨flattenSymbols rest.reverse,symbolBitAt previous 0,
      [symbolBitAt previous 1,symbolBitAt previous 2,symbolBitAt previous 3,false,true,false,false] ++ flattenSymbols right,
      (54 : Fin 132)⟩
    refine ⟨⟨rest,previous,(4 : Fin 11)::right,1⟩,out,?_,?_,?_⟩
    · rfl
    · simpa [encodeUConfig,flattenSymbols,symbolBlock,out,List.reverse_cons,List.flatMap_append,hs0,hs1,hs2,hs3,hstart,hnext] using
        u_1_6_left (flattenSymbols rest.reverse) (flattenSymbols right)
          (symbolBitAt previous 0) (symbolBitAt previous 1) (symbolBitAt previous 2) (symbolBitAt previous 3)
    · simpa [out,hblock,hnext,List.append_assoc] using
        encode_u_left_nonempty_equiv rest right previous (4 : Fin 11) (1 : Fin 3)

#print axioms source_1_6_refines
