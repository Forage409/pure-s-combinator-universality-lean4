import binary_symbolic_base
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem u_0_1_right (left right : List Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨left,false,false :: false :: true :: right,(0 : Fin 132)⟩ =
      match right with
      | [] => some ⟨left ++ [false,true,true,false],false,[],(54 : Fin 132)⟩
      | b :: rest => some ⟨left ++ [false,true,true,false],b,rest,(54 : Fin 132)⟩ := by
  cases right <;> simp [iteratePlain,plainNext]
#print axioms u_0_1_right
