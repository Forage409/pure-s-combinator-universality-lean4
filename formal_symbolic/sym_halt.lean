import binary_symbolic_base
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

theorem u_2_9_halt (left right : List Bool) :
    iteratePlain fixedBinaryProgram 7 ⟨left,true,false :: false :: true :: right,(55 : Fin 132)⟩ = none := by
  simp [iteratePlain,plainNext]

#print axioms u_2_9_halt

theorem u_2_9_rewind (left right : List Bool) :
    iteratePlain fixedBinaryProgram 6 ⟨left,true,false :: false :: true :: right,(55 : Fin 132)⟩ =
      some ⟨left,true,false :: false :: true :: right,(41 : Fin 132)⟩ := by
  simp [iteratePlain,plainNext]

#print axioms u_2_9_rewind
