import binary_symbolic_base
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem u_0_2_left (left right : List Bool) (a b c d : Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨left ++ [a,b,c,d],false,false :: true :: false :: right,(0 : Fin 132)⟩ =
      some ⟨left,a,[b,c,d,false,true,false,false] ++ right,(0 : Fin 132)⟩ := by
  cases b <;> cases c <;> cases d <;> simp [iteratePlain,plainNext,List.reverse_append,List.append_assoc]

theorem u_0_2_boundary (right : List Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨[],false,false :: true :: false :: right,(0 : Fin 132)⟩ =
      some ⟨[],false,true :: false :: false :: right,(0 : Fin 132)⟩ := by
  simp [iteratePlain,plainNext]
#print axioms u_0_2_left
#print axioms u_0_2_boundary
