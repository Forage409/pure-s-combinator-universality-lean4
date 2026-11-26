import binary_symbolic_base
import plain_equivalence

structure UConfig where
  leftRev : List (Fin 11)
  symbol : Fin 11
  right : List (Fin 11)
  state : Fin 3
  deriving DecidableEq, Repr

def symbolBitAt (symbol : Fin 11) (i : Nat) : Bool := decide ((symbol.val / 2^(3-i)) % 2 = 1)

def symbolBlock (symbol : Fin 11) : List Bool :=
  [symbolBitAt symbol 0,symbolBitAt symbol 1,symbolBitAt symbol 2,symbolBitAt symbol 3]

def flattenSymbols (symbols : List (Fin 11)) : List Bool := symbols.flatMap symbolBlock

def binaryStartState (q : Fin 3) : Fin 132 :=
  if q.val = 0 then 0 else if q.val = 1 then 54 else 55

def encodeUConfig (u : UConfig) : PlainConfig :=
  ⟨flattenSymbols u.leftRev.reverse, symbolBitAt u.symbol 0,
    [symbolBitAt u.symbol 1,symbolBitAt u.symbol 2,symbolBitAt u.symbol 3] ++ flattenSymbols u.right,
    binaryStartState u.state⟩

#print axioms encodeUConfig

theorem encode_u_right_empty_equiv (left : List (Fin 11)) (written : Fin 11) (q : Fin 3) :
    PlainEq ⟨flattenSymbols left.reverse ++ symbolBlock written,false,[],binaryStartState q⟩
      (encodeUConfig ⟨written :: left,0,[],q⟩) := by
  have hp : RightEq [] [false,false,false] := by simpa using right_eq_pad [] 3
  simpa [PlainEq,encodeUConfig,flattenSymbols,binaryStartState,List.reverse_cons,List.flatMap_append,symbolBitAt] using hp

theorem encode_u_right_nonempty_equiv (left rest : List (Fin 11)) (written nextSymbol : Fin 11) (q : Fin 3) :
    PlainEq ⟨flattenSymbols left.reverse ++ symbolBlock written,symbolBitAt nextSymbol 0,
        [symbolBitAt nextSymbol 1,symbolBitAt nextSymbol 2,symbolBitAt nextSymbol 3] ++ flattenSymbols rest,binaryStartState q⟩
      (encodeUConfig ⟨written :: left,nextSymbol,rest,q⟩) := by
  simp [PlainEq,encodeUConfig,flattenSymbols,List.reverse_cons,List.flatMap_append,RightEq]

theorem encode_u_left_nonempty_equiv (left right : List (Fin 11)) (previous written : Fin 11) (q : Fin 3) :
    PlainEq ⟨flattenSymbols left.reverse,symbolBitAt previous 0,
        [symbolBitAt previous 1,symbolBitAt previous 2,symbolBitAt previous 3] ++ symbolBlock written ++ flattenSymbols right,
        binaryStartState q⟩
      (encodeUConfig ⟨left,previous,written :: right,q⟩) := by
  simp [PlainEq,encodeUConfig,flattenSymbols,RightEq]

theorem encode_u_left_boundary_equiv (right : List (Fin 11)) (written : Fin 11) (q : Fin 3) :
    PlainEq ⟨[],symbolBitAt written 0,
        [symbolBitAt written 1,symbolBitAt written 2,symbolBitAt written 3] ++ flattenSymbols right,
        binaryStartState q⟩
      (encodeUConfig ⟨[],written,right,q⟩) := by
  simp [PlainEq,encodeUConfig,flattenSymbols,RightEq]

#print axioms encode_u_right_empty_equiv
#print axioms encode_u_right_nonempty_equiv
#print axioms encode_u_left_nonempty_equiv
#print axioms encode_u_left_boundary_equiv
