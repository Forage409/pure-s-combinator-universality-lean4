import u_machine_base

structure UInstruction where
  write : Fin 11
  next : Fin 3
  direction : SourceDirection

def fixedUProgram (q : Fin 3) (symbol : Fin 11) : Option UInstruction :=
  match q.val,symbol.val with
  | 0,0 => some ⟨6,0,.right⟩
  | 0,1 => some ⟨6,1,.right⟩
  | 0,2 => some ⟨4,0,.left⟩
  | 0,3 => some ⟨5,0,.left⟩
  | 0,4 => some ⟨6,0,.right⟩
  | 0,5 => some ⟨7,0,.right⟩
  | 0,6 => some ⟨4,0,.left⟩
  | 0,7 => some ⟨5,0,.left⟩
  | 0,8 => some ⟨9,0,.right⟩
  | 0,9 => some ⟨8,0,.left⟩
  | 0,10 => some ⟨0,2,.left⟩
  | 1,0 => some ⟨10,1,.left⟩
  | 1,1 => some ⟨1,0,.left⟩
  | 1,2 => some ⟨6,0,.right⟩
  | 1,3 => some ⟨7,2,.right⟩
  | 1,4 => some ⟨2,1,.right⟩
  | 1,5 => some ⟨3,1,.right⟩
  | 1,6 => some ⟨4,1,.left⟩
  | 1,7 => some ⟨5,1,.left⟩
  | 1,8 => some ⟨8,1,.right⟩
  | 1,9 => some ⟨8,1,.left⟩
  | 1,10 => some ⟨7,2,.right⟩
  | 2,0 => some ⟨0,2,.left⟩
  | 2,1 => some ⟨2,0,.right⟩
  | 2,2 => some ⟨2,0,.right⟩
  | 2,3 => some ⟨0,0,.left⟩
  | 2,4 => some ⟨6,2,.right⟩
  | 2,5 => some ⟨7,2,.right⟩
  | 2,6 => some ⟨10,1,.left⟩
  | 2,7 => some ⟨0,2,.left⟩
  | 2,8 => some ⟨9,2,.right⟩
  | 2,10 => some ⟨1,2,.left⟩
  | _,_ => none

def uNext (u : UConfig) : Option UConfig :=
  match fixedUProgram u.state u.symbol with
  | none => none
  | some inst =>
    match inst.direction with
    | .stay => some ⟨u.leftRev,inst.write,u.right,inst.next⟩
    | .right => match u.right with
      | [] => some ⟨inst.write :: u.leftRev,0,[],inst.next⟩
      | bit :: rest => some ⟨inst.write :: u.leftRev,bit,rest,inst.next⟩
    | .left => match u.leftRev with
      | [] => some ⟨[],inst.write,u.right,inst.next⟩
      | bit :: rest => some ⟨rest,bit,inst.write :: u.right,inst.next⟩

#print axioms fixedUProgram
#print axioms uNext
