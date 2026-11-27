import binary_symbolic_base
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem u_2_10_left (left right : List Bool) (a b c d : Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨left ++ [a,b,c,d],true,false :: true :: false :: right,(55 : Fin 132)⟩ =
      some ⟨left,a,[b,c,d,false,false,false,true] ++ right,(55 : Fin 132)⟩ := by
  cases b <;> cases c <;> cases d <;> simp [iteratePlain,plainNext,List.reverse_append,List.append_assoc]

theorem u_2_10_boundary (right : List Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨[],true,false :: true :: false :: right,(55 : Fin 132)⟩ =
      some ⟨[],false,false :: false :: true :: right,(55 : Fin 132)⟩ := by
  simp [iteratePlain,plainNext]
#print axioms u_2_10_left
#print axioms u_2_10_boundary
