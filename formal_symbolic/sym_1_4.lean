import binary_symbolic_base
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem u_1_4_right (left right : List Bool) :
    iteratePlain fixedBinaryProgram 10 ⟨left,false,true :: false :: false :: right,(54 : Fin 132)⟩ =
      match right with
      | [] => some ⟨left ++ [false,false,true,false],false,[],(54 : Fin 132)⟩
      | b :: rest => some ⟨left ++ [false,false,true,false],b,rest,(54 : Fin 132)⟩ := by
  cases right <;> simp [iteratePlain,plainNext]
#print axioms u_1_4_right
