import binary_symbolic_base
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem u_2_8_right (left right : List Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨left,true,false :: false :: false :: right,(55 : Fin 132)⟩ =
      match right with
      | [] => some ⟨left ++ [true,false,false,true],false,[],(55 : Fin 132)⟩
      | b :: rest => some ⟨left ++ [true,false,false,true],b,rest,(55 : Fin 132)⟩ := by
  cases right <;> simp [iteratePlain,plainNext]
#print axioms u_2_8_right
