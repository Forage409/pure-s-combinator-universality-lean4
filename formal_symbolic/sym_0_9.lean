import binary_symbolic_base
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem u_0_9_left (left right : List Bool) (a b c d : Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨left ++ [a,b,c,d],true,false :: false :: true :: right,(0 : Fin 132)⟩ =
      some ⟨left,a,[b,c,d,true,false,false,false] ++ right,(0 : Fin 132)⟩ := by
  cases b <;> cases c <;> cases d <;> simp [iteratePlain,plainNext,List.reverse_append,List.append_assoc]

theorem u_0_9_boundary (right : List Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨[],true,false :: false :: true :: right,(0 : Fin 132)⟩ =
      some ⟨[],true,false :: false :: false :: right,(0 : Fin 132)⟩ := by
  simp [iteratePlain,plainNext]
#print axioms u_0_9_left
#print axioms u_0_9_boundary
