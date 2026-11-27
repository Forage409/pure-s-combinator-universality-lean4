import plain_tape

/- Infinite blank suffix equivalence for finite zipper representations. -/

def bitAt : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: rest, n+1 => bitAt rest n

def RightEq (a b : List Bool) : Prop := ∀ i, bitAt a i = bitAt b i

theorem right_eq_head (a b : List Bool) (h : RightEq a b) :
    bitAt a 0 = bitAt b 0 := h 0

theorem right_eq_tails (a b : List Bool) (h : RightEq a b) :
    RightEq (a.drop 1) (b.drop 1) := by
  intro i
  have hi := h (i+1)
  cases a <;> cases b <;> simpa [bitAt] using hi

theorem right_eq_cons (a b : List Bool) (x : Bool) (h : RightEq a b) : RightEq (x::a) (x::b) := by
  intro i
  cases i with
  | zero => rfl
  | succ i => exact h i

def PlainEq (a b : PlainConfig) : Prop :=
  a.left = b.left ∧ a.bit = b.bit ∧ a.state = b.state ∧ RightEq a.right b.right

def OptionPlainEq : Option PlainConfig → Option PlainConfig → Prop
  | none, none => True
  | some a, some b => PlainEq a b
  | _, _ => False

theorem right_head_eq (a b : List Bool) (h : RightEq a b) : a.headD false = b.headD false := by
  cases a <;> cases b <;> exact h 0

#print axioms right_eq_head
#print axioms right_eq_tails
#print axioms right_eq_cons
#print axioms right_head_eq

def plainMoveRight (left right : List Bool) (write : Bool) (q : Fin 132) : PlainConfig :=
  ⟨left ++ [write],right.headD false,right.drop 1,q⟩

def plainMoveLeft (left right : List Bool) (write : Bool) (q : Fin 132) : PlainConfig :=
  match left.reverse with
  | [] => ⟨[],write,right,q⟩
  | bit :: rest => ⟨rest.reverse,bit,write :: right,q⟩

theorem right_move_equiv (left a b : List Bool) (write : Bool) (q : Fin 132) (h : RightEq a b) :
    PlainEq (plainMoveRight left a write q) (plainMoveRight left b write q) := by
  exact ⟨rfl,right_head_eq a b h,rfl,right_eq_tails a b h⟩

theorem left_move_equiv (left a b : List Bool) (write : Bool) (q : Fin 132) (h : RightEq a b) :
    PlainEq (plainMoveLeft left a write q) (plainMoveLeft left b write q) := by
  unfold plainMoveLeft
  cases left.reverse with
  | nil => exact ⟨rfl,rfl,rfl,h⟩
  | cons bit rest => exact ⟨rfl,rfl,rfl,right_eq_cons a b write h⟩

theorem plain_next_respects_equiv (program : BinaryProgram) (a b : PlainConfig)
    (h : PlainEq a b) : OptionPlainEq (plainNext program a) (plainNext program b) := by
  cases a with
  | mk left bit ra q =>
    cases b with
    | mk left' bit' rb q' =>
      obtain ⟨hl,hb,hq,hr⟩ := h
      change left = left' at hl
      change bit = bit' at hb
      change q = q' at hq
      change RightEq ra rb at hr
      subst left'
      subst bit'
      subst q'
      cases hrule : program q bit with
      | none => simp [plainNext,hrule,OptionPlainEq]
      | some inst =>
        cases inst with
        | mk write next direction =>
          cases direction with
          | stay =>
            simpa [plainNext,hrule,OptionPlainEq,PlainEq] using hr
          | right =>
            have hm := right_move_equiv left ra rb write next hr
            cases ra <;> cases rb <;>
              simpa [plainNext,hrule,OptionPlainEq,plainMoveRight] using hm
          | left =>
            have hm := left_move_equiv left ra rb write next hr
            cases hx : left.reverse <;>
              simpa [plainNext,hrule,OptionPlainEq,plainMoveLeft,hx] using hm

#print axioms right_move_equiv
#print axioms left_move_equiv
#print axioms plain_next_respects_equiv

theorem bit_at_false_padding (count index : Nat) : bitAt (List.replicate count false) index = false := by
  induction count generalizing index with
  | zero => cases index <;> rfl
  | succ count ih =>
    cases index with
    | zero => rfl
    | succ i => simpa [List.replicate_succ,bitAt] using ih i

theorem right_eq_pad (xs : List Bool) (count : Nat) : RightEq xs (xs ++ List.replicate count false) := by
  induction xs with
  | nil =>
    intro i
    simpa [bitAt] using (bit_at_false_padding count i).symm
  | cons b bs ih =>
    simpa using right_eq_cons bs (bs ++ List.replicate count false) b ih

#print axioms bit_at_false_padding
#print axioms right_eq_pad

theorem plain_eq_refl (c : PlainConfig) : PlainEq c c := by
  exact ⟨rfl,rfl,rfl,fun _ => rfl⟩

theorem plain_eq_symm {a b : PlainConfig} (h : PlainEq a b) : PlainEq b a := by
  obtain ⟨hl,hb,hq,hr⟩ := h
  exact ⟨hl.symm,hb.symm,hq.symm,fun i => (hr i).symm⟩

theorem plain_run_equiv_forward (program : BinaryProgram) {n : Nat} {a b : PlainConfig}
    (run : PlainRun program n a b) :
    ∀ a', PlainEq a a' → ∃ b', PlainRun program n a' b' ∧ PlainEq b b' := by
  induction run with
  | zero state =>
    intro a' heq
    exact ⟨a',PlainRun.zero _,heq⟩
  | @next n a b c hstep rest ih =>
    intro a' heq
    have hnext := plain_next_respects_equiv program a a' heq
    cases hstep' : plainNext program a' with
    | none => simp [hstep,hstep',OptionPlainEq] at hnext
    | some b' =>
      have hbb : PlainEq b b' := by simpa [hstep,hstep',OptionPlainEq] using hnext
      obtain ⟨c',hrun,hcc⟩ := ih b' hbb
      exact ⟨c',PlainRun.next hstep' hrun,hcc⟩

theorem plain_halt_equiv (program : BinaryProgram) (a b : PlainConfig) (h : PlainEq a b) :
    PlainEventuallyStops program a ↔ PlainEventuallyStops program b := by
  constructor
  · intro ha
    obtain ⟨n,final,run,hstop⟩ := ha
    obtain ⟨final',run',heq⟩ := plain_run_equiv_forward program run b h
    have hnext := plain_next_respects_equiv program final final' heq
    cases hstop' : plainNext program final' with
    | none => exact ⟨n,final',run',hstop'⟩
    | some x => simp [hstop,hstop',OptionPlainEq] at hnext
  · intro hb
    obtain ⟨n,final,run,hstop⟩ := hb
    obtain ⟨final',run',heq⟩ := plain_run_equiv_forward program run a (plain_eq_symm h)
    have hnext := plain_next_respects_equiv program final final' heq
    cases hstop' : plainNext program final' with
    | none => exact ⟨n,final',run',hstop'⟩
    | some x => simp [hstop,hstop',OptionPlainEq] at hnext

#print axioms plain_run_equiv_forward
#print axioms plain_halt_equiv
