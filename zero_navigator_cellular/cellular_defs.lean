/-!
# Shared Definitions for `ZeroNavigatorCellular`
-/

namespace ZeroNavigatorCellular

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true a b).mp h).1

theorem and_right {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true a b).mp h).2

theorem or_eq_true_elim {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

inductive Code6 where
  | mk (b0 b1 b2 b3 b4 b5 : Bool) : Code6
  deriving Repr

def beqCode6 : Code6 → Code6 → Bool
  | .mk a0 a1 a2 a3 a4 a5, .mk b0 b1 b2 b3 b4 b5 =>
    ((a0 == b0) && (a1 == b1)) && ((a2 == b2) && (a3 == b3)) && ((a4 == b4) && (a5 == b5))

theorem beqBool_eq {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem beqCode6_eq {u v : Code6} (h : beqCode6 u v = true) : u = v := by
  cases u with
  | mk a0 a1 a2 a3 a4 a5 =>
    cases v with
    | mk b0 b1 b2 b3 b4 b5 =>
      have h0123 := and_left h
      have h45 := and_right h
      have h01 := and_left h0123
      have h23 := and_right h0123
      rw [beqBool_eq (and_left h01), beqBool_eq (and_right h01),
          beqBool_eq (and_left h23), beqBool_eq (and_right h23),
          beqBool_eq (and_left h45), beqBool_eq (and_right h45)]

inductive Term where
  | s : Term
  | var : Nat → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

infixl:70 " ⋅ " => Term.app

def S : Term := Term.s

inductive Step : Term → Term → Prop where
  | root (x y z : Term) : Step (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : Step a a' → Step (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Step b b' → Step (a ⋅ b) (a ⋅ b')

inductive Reduces : Term → Term → Prop where
  | refl (a : Term) : Reduces a a
  | next {a b c : Term} : Step a b → Reduces b c → Reduces a c

inductive ConvS : Term → Term → Prop where
  | refl (a : Term) : ConvS a a
  | step {a b : Term} : Step a b → ConvS a b
  | symm {a b : Term} : ConvS a b → ConvS b a
  | trans {a b c : Term} : ConvS a b → ConvS b c → ConvS a c

inductive Poly (Q : Type) : Nat → Type where
  | const : Q → Poly Q k
  | var   : Fin k → Poly Q k
  | app   : Poly Q k → Poly Q k → Poly Q k

def evalPoly {Q : Type} {k : Nat} (op : Q → Q → Q) : Poly Q k → (Fin k → Q) → Q
  | .const c, _ => c
  | .var i, env => env i
  | .app p1 p2, env => op (evalPoly op p1 env) (evalPoly op p2 env)

def substPoly {Q : Type} {k m : Nat} (f : Fin k → Poly Q m) : Poly Q k → Poly Q m
  | .const c => .const c
  | .var i => f i
  | .app p1 p2 => .app (substPoly f p1) (substPoly f p2)

theorem evalPoly_subst {Q : Type} {k m : Nat} (op : Q → Q → Q)
    (f : Fin k → Poly Q m) (P : Poly Q k) (env : Fin m → Q) :
    evalPoly op (substPoly f P) env = evalPoly op P (fun i => evalPoly op (f i) env) := by
  induction P with
  | const _ => rfl
  | var _ => rfl
  | app _ _ ih1 ih2 => simp only [substPoly, evalPoly, ih1, ih2]

structure IsCompatPreorder {Q : Type} (op : Q → Q → Q) (le : Q → Q → Bool) : Prop where
  refl  : ∀ x, le x x = true
  left  : ∀ x y z, le x y = true → le (op x z) (op y z) = true
  right : ∀ x y z, le x y = true → le (op z x) (op z y) = true
  trans : ∀ x y z, le x y = true → le y z = true → le x z = true

inductive StateHN where
  | h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34
  deriving Repr

def toCode_StateHN : StateHN → Code6
  | .h0 => .mk false false false false false false
  | .h1 => .mk true false false false false false
  | .h2 => .mk false true false false false false
  | .h3 => .mk true true false false false false
  | .h4 => .mk false false true false false false
  | .h5 => .mk true false true false false false
  | .h6 => .mk false true true false false false
  | .h7 => .mk true true true false false false
  | .h8 => .mk false false false true false false
  | .h9 => .mk true false false true false false
  | .h10 => .mk false true false true false false
  | .h11 => .mk true true false true false false
  | .h12 => .mk false false true true false false
  | .h13 => .mk true false true true false false
  | .h14 => .mk false true true true false false
  | .h15 => .mk true true true true false false
  | .h16 => .mk false false false false true false
  | .h17 => .mk true false false false true false
  | .h18 => .mk false true false false true false
  | .h19 => .mk true true false false true false
  | .h20 => .mk false false true false true false
  | .h21 => .mk true false true false true false
  | .h22 => .mk false true true false true false
  | .h23 => .mk true true true false true false
  | .h24 => .mk false false false true true false
  | .h25 => .mk true false false true true false
  | .h26 => .mk false true false true true false
  | .h27 => .mk true true false true true false
  | .h28 => .mk false false true true true false
  | .h29 => .mk true false true true true false
  | .h30 => .mk false true true true true false
  | .h31 => .mk true true true true true false
  | .h32 => .mk false false false false false true
  | .h33 => .mk true false false false false true
  | .h34 => .mk false true false false false true

def ofCode_StateHN : Code6 → StateHN
  | .mk false false false false false false => .h0
  | .mk true false false false false false => .h1
  | .mk false true false false false false => .h2
  | .mk true true false false false false => .h3
  | .mk false false true false false false => .h4
  | .mk true false true false false false => .h5
  | .mk false true true false false false => .h6
  | .mk true true true false false false => .h7
  | .mk false false false true false false => .h8
  | .mk true false false true false false => .h9
  | .mk false true false true false false => .h10
  | .mk true true false true false false => .h11
  | .mk false false true true false false => .h12
  | .mk true false true true false false => .h13
  | .mk false true true true false false => .h14
  | .mk true true true true false false => .h15
  | .mk false false false false true false => .h16
  | .mk true false false false true false => .h17
  | .mk false true false false true false => .h18
  | .mk true true false false true false => .h19
  | .mk false false true false true false => .h20
  | .mk true false true false true false => .h21
  | .mk false true true false true false => .h22
  | .mk true true true false true false => .h23
  | .mk false false false true true false => .h24
  | .mk true false false true true false => .h25
  | .mk false true false true true false => .h26
  | .mk true true false true true false => .h27
  | .mk false false true true true false => .h28
  | .mk true false true true true false => .h29
  | .mk false true true true true false => .h30
  | .mk true true true true true false => .h31
  | .mk false false false false false true => .h32
  | .mk true false false false false true => .h33
  | .mk false true false false false true => .h34
  | _ => .h0

theorem ofCode_toCode_StateHN (x : StateHN) : ofCode_StateHN (toCode_StateHN x) = x := by
  cases x <;> rfl

def beq_StateHN (x y : StateHN) : Bool := beqCode6 (toCode_StateHN x) (toCode_StateHN y)

theorem beq_StateHN_eq {x y : StateHN} (h : beq_StateHN x y = true) : x = y := by
  have hc := beqCode6_eq h
  have h1 := congrArg ofCode_StateHN hc
  rw [ofCode_toCode_StateHN, ofCode_toCode_StateHN] at h1
  exact h1

def checkAll1_StateHN (p : StateHN → Bool) : Bool :=
  (((((p .h0 && p .h1) && (p .h2 && p .h3)) && ((p .h4 && p .h5) && (p .h6 && p .h7))) && (((p .h8 && p .h9) && (p .h10 && p .h11)) && ((p .h12 && p .h13) && (p .h14 && (p .h15 && p .h16))))) && ((((p .h17 && p .h18) && (p .h19 && p .h20)) && ((p .h21 && p .h22) && (p .h23 && (p .h24 && p .h25)))) && (((p .h26 && p .h27) && (p .h28 && p .h29)) && ((p .h30 && p .h31) && (p .h32 && (p .h33 && p .h34))))))

theorem checkAll1_StateHN_sound (p : StateHN → Bool)
    (h : checkAll1_StateHN p = true) (x : StateHN) : p x = true :=
  match x with
  | .h0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .h1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .h2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .h3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .h4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .h5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .h6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .h7 => (and_right (and_right (and_right (and_left (and_left h)))))
  | .h8 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .h9 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .h10 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .h11 => (and_right (and_right (and_left (and_right (and_left h)))))
  | .h12 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .h13 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .h14 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .h15 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .h16 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .h17 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .h18 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .h19 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .h20 => (and_right (and_right (and_left (and_left (and_right h)))))
  | .h21 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .h22 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .h23 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .h24 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .h25 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .h26 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .h27 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .h28 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .h29 => (and_right (and_right (and_left (and_right (and_right h)))))
  | .h30 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .h31 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .h32 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .h33 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .h34 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateHN (p : StateHN → StateHN → Bool) : Bool :=
  checkAll1_StateHN (fun x => checkAll1_StateHN (fun y => p x y))

theorem checkAll2_StateHN_sound (p : StateHN → StateHN → Bool)
    (h : checkAll2_StateHN p = true) (x y : StateHN) : p x y = true :=
  checkAll1_StateHN_sound _ (checkAll1_StateHN_sound _ h x) y

def deltaHN : StateHN → StateHN → StateHN
  | .h0, y => match y with | .h0 => .h1 | .h1 => .h2 | .h2 => .h3 | .h3 => .h4 | .h4 => .h5 | .h5 => .h5 | .h6 => .h7 | .h7 => .h8 | .h8 => .h9 | .h11 => .h12 | .h12 => .h8 | .h13 => .h12 | .h14 => .h15 | .h15 => .h8 | .h16 => .h8 | .h17 => .h9 | .h18 => .h19 | .h19 => .h9 | .h20 => .h21 | .h21 => .h9 | .h26 => .h27 | .h28 => .h9 | .h29 => .h9 | .h30 => .h9 | .h31 => .h27 | .h32 => .h9 | _ => .h10
  | .h1, y => match y with | .h0 => .h6 | .h1 => .h11 | _ => .h13
  | .h2, y => match y with | .h0 => .h14 | .h1 => .h16 | .h2 => .h8 | .h3 => .h9 | .h6 => .h17 | .h7 => .h9 | .h11 => .h17 | .h12 => .h9 | .h13 => .h17 | _ => .h10
  | .h3, y => match y with | .h0 => .h18 | _ => .h20
  | .h4, y => match y with | .h0 => .h8 | _ => .h10
  | .h5, _ => .h10
  | .h6, y => match y with | .h0 => .h11 | .h1 => .h8 | .h2 => .h20 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | .h6 => .h22 | .h11 => .h22 | .h13 => .h22 | .h14 => .h24 | .h18 => .h25 | .h26 => .h25 | .h31 => .h25 | _ => .h23
  | .h7, y => match y with | .h0 => .h26 | .h1 => .h28 | .h2 => .h29 | .h3 => .h22 | .h6 => .h30 | .h7 => .h22 | .h11 => .h30 | .h12 => .h22 | .h13 => .h30 | _ => .h24
  | .h8, y => match y with | .h0 => .h24 | _ => .h23
  | .h9, y => match y with | .h0 => .h25 | _ => .h23
  | .h10, _ => .h23
  | .h11, y => match y with | .h0 => .h13 | .h1 => .h17 | .h2 => .h20 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | .h6 => .h30 | .h11 => .h29 | .h13 => .h29 | .h14 => .h24 | .h18 => .h25 | .h26 => .h25 | .h31 => .h25 | _ => .h23
  | .h12, y => match y with | .h0 => .h31 | .h1 => .h29 | .h2 => .h29 | .h3 => .h22 | .h6 => .h29 | .h7 => .h22 | .h11 => .h29 | .h12 => .h22 | .h13 => .h29 | _ => .h24
  | .h13, y => match y with | .h0 => .h13 | .h1 => .h10 | .h2 => .h20 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | .h6 => .h24 | .h11 => .h24 | .h13 => .h24 | .h14 => .h24 | .h18 => .h25 | .h26 => .h25 | .h31 => .h25 | _ => .h23
  | .h14, y => match y with | .h0 => .h8 | .h1 => .h20 | .h2 => .h10 | .h3 => .h10 | .h4 => .h10 | .h5 => .h10 | _ => .h23
  | .h15, _ => .h24
  | .h16, y => match y with | .h0 => .h22 | .h1 => .h29 | _ => .h24
  | .h17, y => match y with | .h0 => .h22 | _ => .h23
  | .h18, y => match y with | .h0 => .h20 | .h1 => .h24 | _ => .h23
  | .h19, y => match y with | .h0 => .h32 | _ => .h25
  | .h20, y => match y with | .h1 => .h24 | _ => .h23
  | .h21, y => match y with | .h0 => .h33 | _ => .h23
  | .h22, y => match y with | .h0 => .h25 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | _ => .h34
  | .h23, _ => .h34
  | .h24, y => match y with | .h0 => .h23 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | _ => .h34
  | .h25, y => match y with | .h0 => .h23 | _ => .h34
  | .h26, y => match y with | .h0 => .h17 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | _ => .h34
  | .h27, _ => .h25
  | .h28, y => match y with | .h0 => .h30 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | _ => .h34
  | .h29, y => match y with | .h0 => .h24 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | _ => .h34
  | .h30, y => match y with | .h0 => .h29 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | _ => .h34
  | .h31, y => match y with | .h0 => .h10 | .h1 => .h23 | .h2 => .h23 | .h3 => .h23 | .h4 => .h23 | .h5 => .h23 | _ => .h34
  | .h32, y => match y with | .h0 => .h24 | .h1 => .h23 | _ => .h34
  | .h33, y => match y with | .h1 => .h23 | _ => .h34
  | .h34, _ => .h34

def le_HN_0 : StateHN → StateHN → Bool
  | .h0, _ => true
  | .h1, y => match y with | .h0 => false | _ => true
  | .h2, y => match y with | .h0 => false | .h1 => false | .h6 => false | _ => true
  | .h3, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h6 => false | .h7 => false | _ => true
  | .h4, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h6 => false | .h7 => false | _ => true
  | .h5, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h6 => false | .h7 => false | _ => true
  | .h6, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h7 => false | _ => true
  | .h7, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h14 => false | .h18 => false | _ => true
  | .h8, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h9, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h10, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h11, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h14 => false | .h15 => false | .h18 => false | _ => true
  | .h12, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h13, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h14, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | _ => true
  | .h15, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h14 => false | .h18 => false | _ => true
  | .h16, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h18 => false | _ => true
  | .h17, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h18, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h14 => false | _ => true
  | .h19, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h26 => false | _ => true
  | .h20, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h21, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h22, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h23, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h24, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h25, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h26, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | _ => true
  | .h27, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h28, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | _ => true
  | .h29, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h30, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h31, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h32, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h33, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true
  | .h34, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h26 => false | .h28 => false | _ => true

def le_HN_0_step (x y z : StateHN) : Bool :=
  (!le_HN_0 x y) || ((le_HN_0 (deltaHN x z) (deltaHN y z) && le_HN_0 (deltaHN z x) (deltaHN z y)) && ((!le_HN_0 y z) || le_HN_0 x z))

def le_HN_1 : StateHN → StateHN → Bool
  | .h0, y => match y with | .h0 => true | _ => false
  | .h1, y => match y with | .h1 => true | .h2 => true | .h3 => true | .h4 => true | .h5 => true | _ => false
  | .h2, y => match y with | .h2 => true | .h3 => true | .h4 => true | .h5 => true | _ => false
  | .h3, y => match y with | .h3 => true | .h4 => true | .h5 => true | _ => false
  | .h4, y => match y with | .h4 => true | .h5 => true | _ => false
  | .h5, y => match y with | .h5 => true | _ => false
  | .h6, y => match y with | .h6 => true | .h8 => true | .h9 => true | .h10 => true | .h14 => true | .h18 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h7, y => match y with | .h7 => true | .h8 => true | .h9 => true | .h10 => true | .h15 => true | .h18 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h8, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h9, y => match y with | .h9 => true | .h10 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h10, y => match y with | .h9 => true | .h10 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h11, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h12 => false | .h14 => false | .h15 => false | .h18 => false | .h26 => false | .h28 => false | _ => true
  | .h12, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h13 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h26 => false | .h28 => false | .h31 => false | _ => true
  | .h13, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h12 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h26 => false | .h28 => false | _ => true
  | .h14, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h14 => true | .h18 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h15, y => match y with | .h9 => true | .h10 => true | .h15 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h16, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h16 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h17, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h17 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h18, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h18 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h19, y => match y with | .h9 => true | .h10 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h20, y => match y with | .h9 => true | .h10 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h21, y => match y with | .h9 => true | .h10 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h22, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h23, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h24, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h25, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h26, y => match y with | .h9 => true | .h10 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h27, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h28, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h28 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h29, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h30, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h17 => true | .h19 => true | .h20 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h31, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h12 => false | .h13 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h26 => false | .h28 => false | _ => true
  | .h32, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h33, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h34, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h32 => true | .h33 => true | .h34 => true | _ => false

def le_HN_1_step (x y z : StateHN) : Bool :=
  (!le_HN_1 x y) || ((le_HN_1 (deltaHN x z) (deltaHN y z) && le_HN_1 (deltaHN z x) (deltaHN z y)) && ((!le_HN_1 y z) || le_HN_1 x z))

def le_HN_2 : StateHN → StateHN → Bool
  | .h0, y => match y with | .h0 => true | .h2 => true | .h4 => true | .h5 => true | .h9 => true | .h10 => true | .h15 => true | .h16 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h33 => true | .h34 => true | _ => false
  | .h1, y => match y with | .h1 => true | .h3 => true | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h14 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h2, y => match y with | .h2 => true | .h4 => true | .h5 => true | .h9 => true | .h10 => true | .h15 => true | .h16 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h33 => true | .h34 => true | _ => false
  | .h3, y => match y with | .h3 => true | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h4, y => match y with | .h4 => true | .h5 => true | .h9 => true | .h10 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h5, y => match y with | .h5 => true | .h10 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h6, y => match y with | .h6 => true | .h8 => true | .h9 => true | .h10 => true | .h13 => true | .h18 => true | .h20 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h7, y => match y with | .h7 => true | .h9 => true | .h10 => true | .h12 => true | .h17 => true | .h19 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h8, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h9, y => match y with | .h9 => true | .h10 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h10, y => match y with | .h10 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h11, y => match y with | .h10 => true | .h11 => true | .h13 => true | .h20 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h12, y => match y with | .h10 => true | .h12 => true | .h17 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h13, y => match y with | .h10 => true | .h13 => true | .h20 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h14, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h14 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h15, y => match y with | .h9 => true | .h10 => true | .h15 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h16, y => match y with | .h9 => true | .h10 => true | .h16 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h33 => true | .h34 => true | _ => false
  | .h17, y => match y with | .h10 => true | .h17 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h18, y => match y with | .h10 => true | .h18 => true | .h20 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h19, y => match y with | .h10 => true | .h19 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h20, y => match y with | .h10 => true | .h20 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h21, y => match y with | .h10 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h22, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h23, y => match y with | .h23 => true | .h34 => true | _ => false
  | .h24, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h25, y => match y with | .h23 => true | .h25 => true | .h34 => true | _ => false
  | .h26, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h29 => true | .h31 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h27, y => match y with | .h9 => true | .h10 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h33 => true | .h34 => true | _ => false
  | .h28, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h28 => true | .h29 => true | .h33 => true | .h34 => true | _ => false
  | .h29, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h33 => true | .h34 => true | _ => false
  | .h30, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h30 => true | .h33 => true | .h34 => true | _ => false
  | .h31, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h31 => true | .h33 => true | .h34 => true | _ => false
  | .h32, y => match y with | .h23 => true | .h25 => true | .h32 => true | .h33 => true | .h34 => true | _ => false
  | .h33, y => match y with | .h23 => true | .h33 => true | .h34 => true | _ => false
  | .h34, y => match y with | .h34 => true | _ => false

def le_HN_2_step (x y z : StateHN) : Bool :=
  (!le_HN_2 x y) || ((le_HN_2 (deltaHN x z) (deltaHN y z) && le_HN_2 (deltaHN z x) (deltaHN z y)) && ((!le_HN_2 y z) || le_HN_2 x z))

def le_HN_3 : StateHN → StateHN → Bool
  | .h0, y => match y with | .h0 => true | _ => false
  | .h1, y => match y with | .h1 => true | _ => false
  | .h2, y => match y with | .h2 => true | _ => false
  | .h3, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h6 => false | .h11 => false | .h12 => false | .h13 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h20 => false | .h21 => false | .h31 => false | .h32 => false | .h33 => false | _ => true
  | .h4, y => match y with | .h4 => true | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h5, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h6, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h11 => false | .h12 => false | .h13 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h20 => false | .h21 => false | .h31 => false | .h32 => false | .h33 => false | _ => true
  | .h7, y => match y with | .h4 => true | .h5 => true | .h7 => true | .h8 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h8, y => match y with | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h9, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h10, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h11, y => match y with | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h11 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h12, y => match y with | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h12 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h31 => true | .h34 => true | _ => false
  | .h13, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h20 => false | .h21 => false | .h32 => false | .h33 => false | _ => true
  | .h14, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h6 => false | .h11 => false | .h12 => false | .h13 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h20 => false | .h21 => false | .h31 => false | .h32 => false | .h33 => false | _ => true
  | .h15, y => match y with | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h15 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h16, y => match y with | .h16 => true | _ => false
  | .h17, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h18, y => match y with | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h17 => true | .h18 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h19, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h19 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h20, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h20 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h21, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h21 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h22, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h23, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h24, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h25, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h26, y => match y with | .h5 => true | .h8 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h27, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h28, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h28 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h29, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h30, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false
  | .h31, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h31 => true | .h34 => true | _ => false
  | .h32, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h32 => true | .h34 => true | _ => false
  | .h33, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h33 => true | .h34 => true | _ => false
  | .h34, y => match y with | .h5 => true | .h9 => true | .h10 => true | .h17 => true | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h29 => true | .h30 => true | .h34 => true | _ => false

def le_HN_3_step (x y z : StateHN) : Bool :=
  (!le_HN_3 x y) || ((le_HN_3 (deltaHN x z) (deltaHN y z) && le_HN_3 (deltaHN z x) (deltaHN z y)) && ((!le_HN_3 y z) || le_HN_3 x z))

def le_HN_4 : StateHN → StateHN → Bool
  | .h0, y => match y with | .h0 => true | _ => false
  | .h1, y => match y with | .h1 => true | _ => false
  | .h2, y => match y with | .h2 => true | .h6 => true | _ => false
  | .h3, y => match y with | .h3 => true | .h6 => true | .h7 => true | _ => false
  | .h4, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h5 => false | .h6 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h5, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h6, y => match y with | .h6 => true | _ => false
  | .h7, y => match y with | .h7 => true | _ => false
  | .h8, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h9, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h10, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h11, y => match y with | .h11 => true | _ => false
  | .h12, y => match y with | .h12 => true | _ => false
  | .h13, y => match y with | .h13 => true | _ => false
  | .h14, y => match y with | .h11 => true | .h14 => true | _ => false
  | .h15, y => match y with | .h12 => true | .h15 => true | _ => false
  | .h16, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h17, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h18, y => match y with | .h11 => true | .h18 => true | .h26 => true | _ => false
  | .h19, y => match y with | .h12 => true | .h19 => true | .h27 => true | _ => false
  | .h20, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h21, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h22, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h23, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h24, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h25, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h26, y => match y with | .h26 => true | _ => false
  | .h27, y => match y with | .h27 => true | _ => false
  | .h28, y => match y with | .h28 => true | _ => false
  | .h29, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h30, y => match y with | .h30 => true | _ => false
  | .h31, y => match y with | .h31 => true | _ => false
  | .h32, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | _ => true
  | .h33, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true
  | .h34, y => match y with | .h0 => false | .h1 => false | .h2 => false | .h3 => false | .h4 => false | .h5 => false | .h6 => false | .h7 => false | .h11 => false | .h14 => false | .h15 => false | .h16 => false | .h18 => false | .h19 => false | .h32 => false | _ => true

def le_HN_4_step (x y z : StateHN) : Bool :=
  (!le_HN_4 x y) || ((le_HN_4 (deltaHN x z) (deltaHN y z) && le_HN_4 (deltaHN z x) (deltaHN z y)) && ((!le_HN_4 y z) || le_HN_4 x z))

def le_HN_5 : StateHN → StateHN → Bool
  | .h0, y => match y with | .h0 => true | _ => false
  | .h1, y => match y with | .h1 => true | _ => false
  | .h2, y => match y with | .h2 => true | _ => false
  | .h3, y => match y with | .h3 => true | _ => false
  | .h4, y => match y with | .h4 => true | _ => false
  | .h5, y => match y with | .h5 => true | _ => false
  | .h6, y => match y with | .h6 => true | .h14 => true | _ => false
  | .h7, y => match y with | .h7 => true | .h15 => true | _ => false
  | .h8, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h20 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h9, y => match y with | .h9 => true | .h10 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h10, y => match y with | .h9 => true | .h10 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h11, y => match y with | .h8 => true | .h9 => true | .h10 => true | .h11 => true | .h20 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h12, y => match y with | .h9 => true | .h10 => true | .h12 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h13, y => match y with | .h13 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h14, y => match y with | .h14 => true | _ => false
  | .h15, y => match y with | .h15 => true | _ => false
  | .h16, y => match y with | .h16 => true | _ => false
  | .h17, y => match y with | .h9 => true | .h10 => true | .h17 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h18, y => match y with | .h18 => true | _ => false
  | .h19, y => match y with | .h19 => true | _ => false
  | .h20, y => match y with | .h9 => true | .h10 => true | .h20 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h21, y => match y with | .h9 => true | .h10 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h22, y => match y with | .h22 => true | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h23, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h24, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h25, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h26, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h26 => true | .h33 => true | .h34 => true | _ => false
  | .h27, y => match y with | .h9 => true | .h10 => true | .h21 => true | .h23 => true | .h24 => true | .h25 => true | .h27 => true | .h33 => true | .h34 => true | _ => false
  | .h28, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h28 => true | .h33 => true | .h34 => true | _ => false
  | .h29, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h29 => true | .h33 => true | .h34 => true | _ => false
  | .h30, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h30 => true | .h33 => true | .h34 => true | _ => false
  | .h31, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h31 => true | .h33 => true | .h34 => true | _ => false
  | .h32, y => match y with | .h32 => true | _ => false
  | .h33, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false
  | .h34, y => match y with | .h23 => true | .h24 => true | .h25 => true | .h33 => true | .h34 => true | _ => false

def le_HN_5_step (x y z : StateHN) : Bool :=
  (!le_HN_5 x y) || ((le_HN_5 (deltaHN x z) (deltaHN y z) && le_HN_5 (deltaHN z x) (deltaHN z y)) && ((!le_HN_5 y z) || le_HN_5 x z))

def allPreordersStep_HN (x y z : StateHN) : Bool :=
  ((le_HN_0_step x y z && (le_HN_1_step x y z && le_HN_2_step x y z)) && (le_HN_3_step x y z && (le_HN_4_step x y z && le_HN_5_step x y z)))

def sep_HN (x y : StateHN) : Bool :=
  (le_HN_0 x y != le_HN_0 y x) || (le_HN_1 x y != le_HN_1 y x) || (le_HN_2 x y != le_HN_2 y x) || (le_HN_3 x y != le_HN_3 y x) || (le_HN_4 x y != le_HN_4 y x) || (le_HN_5 x y != le_HN_5 y x)

inductive StateSN where
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11 | s12 | s13 | s14 | s15 | s16 | s17 | s18 | s19 | s20 | s21 | s22 | s23 | s24 | s25 | s26 | s27 | s28 | s29 | s30 | s31 | s32 | s33 | s34 | s35 | s36 | s37 | s38
  deriving Repr

def toCode_StateSN : StateSN → Code6
  | .s0 => .mk false false false false false false
  | .s1 => .mk true false false false false false
  | .s2 => .mk false true false false false false
  | .s3 => .mk true true false false false false
  | .s4 => .mk false false true false false false
  | .s5 => .mk true false true false false false
  | .s6 => .mk false true true false false false
  | .s7 => .mk true true true false false false
  | .s8 => .mk false false false true false false
  | .s9 => .mk true false false true false false
  | .s10 => .mk false true false true false false
  | .s11 => .mk true true false true false false
  | .s12 => .mk false false true true false false
  | .s13 => .mk true false true true false false
  | .s14 => .mk false true true true false false
  | .s15 => .mk true true true true false false
  | .s16 => .mk false false false false true false
  | .s17 => .mk true false false false true false
  | .s18 => .mk false true false false true false
  | .s19 => .mk true true false false true false
  | .s20 => .mk false false true false true false
  | .s21 => .mk true false true false true false
  | .s22 => .mk false true true false true false
  | .s23 => .mk true true true false true false
  | .s24 => .mk false false false true true false
  | .s25 => .mk true false false true true false
  | .s26 => .mk false true false true true false
  | .s27 => .mk true true false true true false
  | .s28 => .mk false false true true true false
  | .s29 => .mk true false true true true false
  | .s30 => .mk false true true true true false
  | .s31 => .mk true true true true true false
  | .s32 => .mk false false false false false true
  | .s33 => .mk true false false false false true
  | .s34 => .mk false true false false false true
  | .s35 => .mk true true false false false true
  | .s36 => .mk false false true false false true
  | .s37 => .mk true false true false false true
  | .s38 => .mk false true true false false true

def ofCode_StateSN : Code6 → StateSN
  | .mk false false false false false false => .s0
  | .mk true false false false false false => .s1
  | .mk false true false false false false => .s2
  | .mk true true false false false false => .s3
  | .mk false false true false false false => .s4
  | .mk true false true false false false => .s5
  | .mk false true true false false false => .s6
  | .mk true true true false false false => .s7
  | .mk false false false true false false => .s8
  | .mk true false false true false false => .s9
  | .mk false true false true false false => .s10
  | .mk true true false true false false => .s11
  | .mk false false true true false false => .s12
  | .mk true false true true false false => .s13
  | .mk false true true true false false => .s14
  | .mk true true true true false false => .s15
  | .mk false false false false true false => .s16
  | .mk true false false false true false => .s17
  | .mk false true false false true false => .s18
  | .mk true true false false true false => .s19
  | .mk false false true false true false => .s20
  | .mk true false true false true false => .s21
  | .mk false true true false true false => .s22
  | .mk true true true false true false => .s23
  | .mk false false false true true false => .s24
  | .mk true false false true true false => .s25
  | .mk false true false true true false => .s26
  | .mk true true false true true false => .s27
  | .mk false false true true true false => .s28
  | .mk true false true true true false => .s29
  | .mk false true true true true false => .s30
  | .mk true true true true true false => .s31
  | .mk false false false false false true => .s32
  | .mk true false false false false true => .s33
  | .mk false true false false false true => .s34
  | .mk true true false false false true => .s35
  | .mk false false true false false true => .s36
  | .mk true false true false false true => .s37
  | .mk false true true false false true => .s38
  | _ => .s0

theorem ofCode_toCode_StateSN (x : StateSN) : ofCode_StateSN (toCode_StateSN x) = x := by
  cases x <;> rfl

def beq_StateSN (x y : StateSN) : Bool := beqCode6 (toCode_StateSN x) (toCode_StateSN y)

theorem beq_StateSN_eq {x y : StateSN} (h : beq_StateSN x y = true) : x = y := by
  have hc := beqCode6_eq h
  have h1 := congrArg ofCode_StateSN hc
  rw [ofCode_toCode_StateSN, ofCode_toCode_StateSN] at h1
  exact h1

def checkAll1_StateSN (p : StateSN → Bool) : Bool :=
  (((((p .s0 && p .s1) && (p .s2 && p .s3)) && ((p .s4 && p .s5) && (p .s6 && (p .s7 && p .s8)))) && (((p .s9 && p .s10) && (p .s11 && (p .s12 && p .s13))) && ((p .s14 && p .s15) && (p .s16 && (p .s17 && p .s18))))) && ((((p .s19 && p .s20) && (p .s21 && (p .s22 && p .s23))) && ((p .s24 && p .s25) && (p .s26 && (p .s27 && p .s28)))) && (((p .s29 && p .s30) && (p .s31 && (p .s32 && p .s33))) && ((p .s34 && p .s35) && (p .s36 && (p .s37 && p .s38))))))

theorem checkAll1_StateSN_sound (p : StateSN → Bool)
    (h : checkAll1_StateSN p = true) (x : StateSN) : p x = true :=
  match x with
  | .s0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .s1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .s2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .s3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .s4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .s5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .s6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .s7 => (and_left (and_right (and_right (and_right (and_left (and_left h))))))
  | .s8 => (and_right (and_right (and_right (and_right (and_left (and_left h))))))
  | .s9 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .s10 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .s11 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .s12 => (and_left (and_right (and_right (and_left (and_right (and_left h))))))
  | .s13 => (and_right (and_right (and_right (and_left (and_right (and_left h))))))
  | .s14 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .s15 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .s16 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .s17 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .s18 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .s19 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .s20 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .s21 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .s22 => (and_left (and_right (and_right (and_left (and_left (and_right h))))))
  | .s23 => (and_right (and_right (and_right (and_left (and_left (and_right h))))))
  | .s24 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .s25 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .s26 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .s27 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .s28 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .s29 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .s30 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .s31 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .s32 => (and_left (and_right (and_right (and_left (and_right (and_right h))))))
  | .s33 => (and_right (and_right (and_right (and_left (and_right (and_right h))))))
  | .s34 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .s35 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .s36 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .s37 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .s38 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateSN (p : StateSN → StateSN → Bool) : Bool :=
  checkAll1_StateSN (fun x => checkAll1_StateSN (fun y => p x y))

theorem checkAll2_StateSN_sound (p : StateSN → StateSN → Bool)
    (h : checkAll2_StateSN p = true) (x y : StateSN) : p x y = true :=
  checkAll1_StateSN_sound _ (checkAll1_StateSN_sound _ h x) y

def deltaSN : StateSN → StateSN → StateSN
  | .s0, y => match y with | .s0 => .s1 | .s1 => .s2 | .s2 => .s3 | .s3 => .s4 | .s4 => .s5 | .s7 => .s8 | .s8 => .s5 | .s9 => .s10 | .s10 => .s5 | .s11 => .s12 | .s12 => .s5 | .s13 => .s4 | .s14 => .s5 | .s15 => .s10 | .s16 => .s5 | .s17 => .s5 | .s18 => .s5 | .s19 => .s20 | .s32 => .s21 | .s36 => .s21 | .s38 => .s38 | _ => .s6
  | .s1, y => match y with | .s0 => .s7 | .s1 => .s9 | .s2 => .s11 | .s3 => .s13 | .s4 => .s14 | .s5 => .s5 | .s6 => .s6 | .s8 => .s16 | .s10 => .s17 | .s11 => .s11 | .s12 => .s18 | .s13 => .s13 | .s14 => .s14 | .s16 => .s16 | .s17 => .s17 | .s18 => .s18 | .s19 => .s19 | .s20 => .s21 | .s21 => .s21 | .s22 => .s23 | .s23 => .s23 | .s24 => .s24 | .s25 => .s25 | .s26 => .s26 | .s27 => .s27 | .s28 => .s28 | .s29 => .s29 | .s30 => .s30 | .s31 => .s31 | .s32 => .s32 | .s33 => .s33 | .s34 => .s34 | .s35 => .s35 | .s36 => .s36 | .s37 => .s37 | .s38 => .s38 | _ => .s15
  | .s2, y => match y with | .s0 => .s19 | .s1 => .s22 | .s2 => .s24 | .s7 => .s26 | .s9 => .s26 | .s15 => .s26 | .s29 => .s29 | .s30 => .s30 | .s31 => .s31 | .s32 => .s31 | .s33 => .s31 | .s34 => .s29 | .s35 => .s29 | .s36 => .s31 | .s37 => .s31 | .s38 => .s38 | _ => .s25
  | .s3, y => match y with | .s0 => .s27 | .s1 => .s28 | .s2 => .s29 | .s3 => .s29 | .s7 => .s29 | .s9 => .s29 | .s11 => .s29 | .s13 => .s29 | .s15 => .s29 | .s19 => .s29 | .s32 => .s29 | .s36 => .s29 | .s38 => .s38 | _ => .s30
  | .s4, y => match y with | .s0 => .s31 | .s1 => .s31 | .s2 => .s29 | .s3 => .s29 | .s7 => .s29 | .s9 => .s29 | .s11 => .s29 | .s13 => .s29 | .s15 => .s29 | .s19 => .s29 | .s32 => .s29 | .s36 => .s29 | .s38 => .s38 | _ => .s30
  | .s5, y => match y with | .s0 => .s29 | .s38 => .s38 | _ => .s30
  | .s6, y => match y with | .s38 => .s38 | _ => .s30
  | .s7, y => match y with | .s0 => .s9 | .s1 => .s24 | .s2 => .s29 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s8, y => match y with | .s0 => .s32 | .s1 => .s33 | .s7 => .s34 | .s9 => .s34 | .s15 => .s34 | .s30 => .s30 | .s38 => .s38 | _ => .s29
  | .s9, y => match y with | .s0 => .s15 | .s1 => .s26 | .s2 => .s29 | .s3 => .s29 | .s7 => .s34 | .s9 => .s35 | .s11 => .s29 | .s13 => .s29 | .s15 => .s35 | .s38 => .s38 | _ => .s30
  | .s10, y => match y with | .s0 => .s36 | .s1 => .s37 | .s7 => .s35 | .s9 => .s35 | .s15 => .s35 | .s30 => .s30 | .s38 => .s38 | _ => .s29
  | .s11, y => match y with | .s0 => .s19 | .s1 => .s25 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s12, y => match y with | .s0 => .s37 | .s1 => .s31 | .s2 => .s29 | .s3 => .s29 | .s7 => .s29 | .s9 => .s29 | .s11 => .s29 | .s13 => .s29 | .s15 => .s29 | .s19 => .s29 | .s32 => .s29 | .s36 => .s29 | .s38 => .s38 | _ => .s30
  | .s13, y => match y with | .s0 => .s27 | .s1 => .s25 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s14, y => match y with | .s0 => .s31 | .s1 => .s31 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s15, y => match y with | .s0 => .s15 | .s1 => .s25 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s16, y => match y with | .s0 => .s32 | .s1 => .s31 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s17, y => match y with | .s0 => .s36 | .s1 => .s31 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s18, y => match y with | .s0 => .s37 | .s1 => .s31 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s19, y => match y with | .s0 => .s24 | .s1 => .s29 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38 | _ => .s30
  | .s20, y => match y with | .s0 => .s29 | .s1 => .s29 | .s2 => .s29 | .s3 => .s29 | .s7 => .s29 | .s9 => .s29 | .s11 => .s29 | .s13 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s21, y => match y with | .s0 => .s29 | .s1 => .s29 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s38 => .s38 | _ => .s30
  | .s22, y => match y with | .s0 => .s29 | .s1 => .s35 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38 | _ => .s30
  | .s23, y => match y with | .s0 => .s29 | .s1 => .s29 | .s7 => .s29 | .s9 => .s29 | .s15 => .s29 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38 | _ => .s30
  | .s24, y => match y with | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38 | _ => .s30
  | .s25, y => match y with | .s19 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38 | _ => .s30
  | .s26, y => match y with | .s0 => .s29 | .s19 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38 | _ => .s30
  | .s27, y => match y with | .s0 => .s29 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38 | _ => .s30
  | .s28, y => match y with | .s1 => .s29 | .s19 => .s38 | .s22 => .s38 | .s23 => .s38 | .s24 => .s38 | .s25 => .s38 | .s26 => .s38 | .s27 => .s38 | .s28 => .s38 | .s29 => .s38 | .s30 => .s38 | .s31 => .s38 | .s32 => .s38 | .s33 => .s38 | .s34 => .s38 | .s35 => .s38 | .s36 => .s38 | .s37 => .s38 | .s38 => .s38 | _ => .s30
  | .s29, y => match y with | .s0 => .s30 | _ => .s38
  | .s30, _ => .s38
  | .s31, y => match y with | .s0 => .s30 | .s1 => .s30 | _ => .s38
  | .s32, y => match y with | .s0 => .s26 | .s1 => .s30 | _ => .s38
  | .s33, y => match y with | .s0 => .s34 | .s1 => .s30 | _ => .s38
  | .s34, y => match y with | .s0 => .s35 | _ => .s38
  | .s35, y => match y with | .s0 => .s29 | _ => .s38
  | .s36, y => match y with | .s0 => .s25 | .s1 => .s30 | _ => .s38
  | .s37, y => match y with | .s0 => .s29 | .s1 => .s30 | _ => .s38
  | .s38, _ => .s38

def le_SN_0 : StateSN → StateSN → Bool
  | .s0, y => match y with | .s1 => false | _ => true
  | .s1, y => match y with | .s0 => false | _ => true
  | .s2, y => match y with | .s0 => false | .s1 => false | .s7 => false | .s9 => false | .s15 => false | _ => true
  | .s3, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s15 => false | .s16 => false | .s17 => false | _ => true
  | .s4, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s12 => false | .s13 => false | .s15 => false | .s16 => false | .s17 => false | .s18 => false | .s19 => false | .s32 => false | .s36 => false | _ => true
  | .s5, y => match y with | .s5 => true | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s6, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s7, y => match y with | .s0 => false | .s1 => false | .s2 => false | _ => true
  | .s8, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s9 => false | .s11 => false | .s13 => false | .s15 => false | .s19 => false | .s32 => false | .s36 => false | _ => true
  | .s9, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s7 => false | _ => true
  | .s10, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s11 => false | .s13 => false | .s15 => false | .s16 => false | .s19 => false | .s32 => false | .s36 => false | _ => true
  | .s11, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s15 => false | _ => true
  | .s12, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s13 => false | .s15 => false | .s16 => false | .s17 => false | .s19 => false | .s32 => false | .s36 => false | _ => true
  | .s13, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s15 => false | .s16 => false | .s17 => false | _ => true
  | .s14, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s4 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s12 => false | .s13 => false | .s15 => false | .s16 => false | .s17 => false | .s18 => false | .s19 => false | .s32 => false | .s36 => false | _ => true
  | .s15, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | _ => true
  | .s16, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s13 => false | .s15 => false | .s19 => false | .s32 => false | .s36 => false | _ => true
  | .s17, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s13 => false | .s15 => false | .s16 => false | .s19 => false | .s32 => false | .s36 => false | _ => true
  | .s18, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s12 => false | .s13 => false | .s15 => false | .s16 => false | .s17 => false | .s19 => false | .s32 => false | .s36 => false | _ => true
  | .s19, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s13 => false | .s15 => false | .s16 => false | .s17 => false | _ => true
  | .s20, y => match y with | .s5 => true | .s6 => true | .s20 => true | .s21 => true | .s25 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s21, y => match y with | .s5 => true | .s6 => true | .s21 => true | .s25 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s22, y => match y with | .s5 => true | .s6 => true | .s20 => true | .s21 => true | .s22 => true | .s23 => true | .s24 => true | .s25 => true | .s26 => true | .s27 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s33 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s23, y => match y with | .s5 => true | .s6 => true | .s20 => true | .s21 => true | .s23 => true | .s24 => true | .s25 => true | .s26 => true | .s27 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s33 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s24, y => match y with | .s5 => true | .s6 => true | .s20 => true | .s21 => true | .s24 => true | .s25 => true | .s26 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s33 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s25, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s26, y => match y with | .s5 => true | .s6 => true | .s20 => true | .s21 => true | .s25 => true | .s26 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s33 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s27, y => match y with | .s5 => true | .s6 => true | .s20 => true | .s21 => true | .s24 => true | .s25 => true | .s26 => true | .s27 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s33 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s28, y => match y with | .s5 => true | .s6 => true | .s25 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s29, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s30, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s31, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s32, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s13 => false | .s15 => false | .s16 => false | .s17 => false | .s19 => false | _ => true
  | .s33, y => match y with | .s5 => true | .s6 => true | .s20 => true | .s21 => true | .s25 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s33 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s34, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s35, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s36, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | .s10 => false | .s11 => false | .s12 => false | .s13 => false | .s15 => false | .s16 => false | .s17 => false | .s18 => false | .s19 => false | .s32 => false | _ => true
  | .s37, y => match y with | .s5 => true | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s37 => true | .s38 => true | _ => false
  | .s38, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s38 => true | _ => false

def le_SN_0_step (x y z : StateSN) : Bool :=
  (!le_SN_0 x y) || ((le_SN_0 (deltaSN x z) (deltaSN y z) && le_SN_0 (deltaSN z x) (deltaSN z y)) && ((!le_SN_0 y z) || le_SN_0 x z))

def le_SN_1 : StateSN → StateSN → Bool
  | .s0, y => match y with | .s0 => true | .s2 => true | .s4 => true | .s6 => true | .s20 => true | .s22 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s35 => true | .s38 => true | _ => false
  | .s1, y => match y with | .s1 => true | .s3 => true | .s5 => true | .s6 => true | .s19 => true | .s24 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s2, y => match y with | .s2 => true | .s4 => true | .s6 => true | .s20 => true | .s22 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s35 => true | .s38 => true | _ => false
  | .s3, y => match y with | .s3 => true | .s5 => true | .s6 => true | .s24 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s4, y => match y with | .s4 => true | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s5, y => match y with | .s5 => true | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s6, y => match y with | .s6 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s7, y => match y with | .s6 => true | .s7 => true | .s11 => true | .s14 => true | .s21 => true | .s23 => true | .s24 => true | .s25 => true | .s27 => true | .s29 => true | .s30 => true | .s31 => true | .s35 => true | .s38 => true | _ => false
  | .s8, y => match y with | .s5 => true | .s6 => true | .s8 => true | .s12 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s9, y => match y with | .s5 => true | .s6 => true | .s9 => true | .s13 => true | .s19 => true | .s24 => true | .s25 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s10, y => match y with | .s4 => true | .s5 => true | .s6 => true | .s10 => true | .s12 => true | .s20 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s11, y => match y with | .s6 => true | .s11 => true | .s14 => true | .s21 => true | .s23 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s35 => true | .s38 => true | _ => false
  | .s12, y => match y with | .s5 => true | .s6 => true | .s12 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s13, y => match y with | .s5 => true | .s6 => true | .s13 => true | .s24 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s14, y => match y with | .s6 => true | .s14 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s15, y => match y with | .s5 => true | .s6 => true | .s11 => true | .s13 => true | .s14 => true | .s15 => true | .s19 => true | .s21 => true | .s23 => true | .s24 => true | .s25 => true | .s27 => true | .s28 => true | .s29 => true | .s30 => true | .s31 => true | .s35 => true | .s38 => true | _ => false
  | .s16, y => match y with | .s5 => true | .s6 => true | .s16 => true | .s18 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s17, y => match y with | .s5 => true | .s6 => true | .s14 => true | .s17 => true | .s18 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s18, y => match y with | .s5 => true | .s6 => true | .s18 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s19, y => match y with | .s19 => true | .s24 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s20, y => match y with | .s6 => true | .s20 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s21, y => match y with | .s6 => true | .s21 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s22, y => match y with | .s22 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s35 => true | .s38 => true | _ => false
  | .s23, y => match y with | .s23 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s35 => true | .s38 => true | _ => false
  | .s24, y => match y with | .s24 => true | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s25, y => match y with | .s25 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s26, y => match y with | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s27, y => match y with | .s27 => true | .s29 => true | .s30 => true | .s38 => true | _ => false
  | .s28, y => match y with | .s28 => true | .s29 => true | .s30 => true | .s38 => true | _ => false
  | .s29, y => match y with | .s29 => true | .s30 => true | .s38 => true | _ => false
  | .s30, y => match y with | .s30 => true | .s38 => true | _ => false
  | .s31, y => match y with | .s29 => true | .s30 => true | .s31 => true | .s38 => true | _ => false
  | .s32, y => match y with | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s37 => true | .s38 => true | _ => false
  | .s33, y => match y with | .s29 => true | .s30 => true | .s31 => true | .s33 => true | .s38 => true | _ => false
  | .s34, y => match y with | .s29 => true | .s30 => true | .s34 => true | .s35 => true | .s38 => true | _ => false
  | .s35, y => match y with | .s29 => true | .s30 => true | .s35 => true | .s38 => true | _ => false
  | .s36, y => match y with | .s29 => true | .s30 => true | .s31 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s37, y => match y with | .s29 => true | .s30 => true | .s31 => true | .s37 => true | .s38 => true | _ => false
  | .s38, y => match y with | .s38 => true | _ => false

def le_SN_1_step (x y z : StateSN) : Bool :=
  (!le_SN_1 x y) || ((le_SN_1 (deltaSN x z) (deltaSN y z) && le_SN_1 (deltaSN z x) (deltaSN z y)) && ((!le_SN_1 y z) || le_SN_1 x z))

def le_SN_2 : StateSN → StateSN → Bool
  | .s0, _ => true
  | .s1, y => match y with | .s0 => false | _ => true
  | .s2, y => match y with | .s0 => false | .s1 => false | .s7 => false | _ => true
  | .s3, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s4, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s5, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s6, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s7, y => match y with | .s0 => false | .s1 => false | _ => true
  | .s8, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s7 => false | .s9 => false | _ => true
  | .s9, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | _ => true
  | .s10, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s11, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s12, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s13, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s14, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s15, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s16, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s17, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s18, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s19, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s20, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s21, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s22, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s23, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s24, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s25, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s26, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s27, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s28, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s29, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s30, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s31, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s32, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s33, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s34, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s35, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s36, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s37, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true
  | .s38, y => match y with | .s0 => false | .s1 => false | .s2 => false | .s3 => false | .s7 => false | .s8 => false | .s9 => false | _ => true

def le_SN_2_step (x y z : StateSN) : Bool :=
  (!le_SN_2 x y) || ((le_SN_2 (deltaSN x z) (deltaSN y z) && le_SN_2 (deltaSN z x) (deltaSN z y)) && ((!le_SN_2 y z) || le_SN_2 x z))

def le_SN_3 : StateSN → StateSN → Bool
  | .s0, y => match y with | .s0 => true | _ => false
  | .s1, y => match y with | .s1 => true | _ => false
  | .s2, y => match y with | .s2 => true | _ => false
  | .s3, y => match y with | .s3 => true | .s8 => true | _ => false
  | .s4, y => match y with | .s4 => true | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s5, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s6, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s7, y => match y with | .s7 => true | _ => false
  | .s8, y => match y with | .s8 => true | _ => false
  | .s9, y => match y with | .s9 => true | _ => false
  | .s10, y => match y with | .s10 => true | _ => false
  | .s11, y => match y with | .s10 => true | .s11 => true | .s17 => true | _ => false
  | .s12, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s12 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s13, y => match y with | .s10 => true | .s13 => true | .s16 => true | .s17 => true | _ => false
  | .s14, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s14 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s15, y => match y with | .s15 => true | _ => false
  | .s16, y => match y with | .s10 => true | .s16 => true | .s17 => true | _ => false
  | .s17, y => match y with | .s17 => true | _ => false
  | .s18, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s18 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s19, y => match y with | .s10 => true | .s16 => true | .s17 => true | .s19 => true | .s36 => true | _ => false
  | .s20, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s20 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s21, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s22, y => match y with | .s22 => true | _ => false
  | .s23, y => match y with | .s23 => true | _ => false
  | .s24, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s24 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s25, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s26, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s27, y => match y with | .s10 => true | .s16 => true | .s17 => true | .s27 => true | .s32 => true | .s36 => true | _ => false
  | .s28, y => match y with | .s28 => true | .s33 => true | _ => false
  | .s29, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s30, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s31, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s32, y => match y with | .s10 => true | .s16 => true | .s17 => true | .s32 => true | .s36 => true | _ => false
  | .s33, y => match y with | .s33 => true | _ => false
  | .s34, y => match y with | .s34 => true | _ => false
  | .s35, y => match y with | .s35 => true | _ => false
  | .s36, y => match y with | .s10 => true | .s16 => true | .s17 => true | .s36 => true | _ => false
  | .s37, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s38, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s16 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s32 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false

def le_SN_3_step (x y z : StateSN) : Bool :=
  (!le_SN_3 x y) || ((le_SN_3 (deltaSN x z) (deltaSN y z) && le_SN_3 (deltaSN z x) (deltaSN z y)) && ((!le_SN_3 y z) || le_SN_3 x z))

def le_SN_4 : StateSN → StateSN → Bool
  | .s0, y => match y with | .s0 => true | _ => false
  | .s1, y => match y with | .s1 => true | _ => false
  | .s2, y => match y with | .s2 => true | _ => false
  | .s3, y => match y with | .s3 => true | _ => false
  | .s4, y => match y with | .s4 => true | _ => false
  | .s5, y => match y with | .s5 => true | .s10 => true | .s15 => true | .s17 => true | _ => false
  | .s6, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s15 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s7, y => match y with | .s7 => true | _ => false
  | .s8, y => match y with | .s8 => true | _ => false
  | .s9, y => match y with | .s9 => true | _ => false
  | .s10, y => match y with | .s10 => true | .s15 => true | _ => false
  | .s11, y => match y with | .s11 => true | _ => false
  | .s12, y => match y with | .s12 => true | _ => false
  | .s13, y => match y with | .s13 => true | _ => false
  | .s14, y => match y with | .s14 => true | _ => false
  | .s15, y => match y with | .s15 => true | _ => false
  | .s16, y => match y with | .s16 => true | _ => false
  | .s17, y => match y with | .s15 => true | .s17 => true | _ => false
  | .s18, y => match y with | .s18 => true | _ => false
  | .s19, y => match y with | .s19 => true | _ => false
  | .s20, y => match y with | .s20 => true | _ => false
  | .s21, y => match y with | .s10 => true | .s15 => true | .s17 => true | .s21 => true | _ => false
  | .s22, y => match y with | .s22 => true | _ => false
  | .s23, y => match y with | .s23 => true | _ => false
  | .s24, y => match y with | .s24 => true | _ => false
  | .s25, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s15 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s26, y => match y with | .s26 => true | _ => false
  | .s27, y => match y with | .s27 => true | _ => false
  | .s28, y => match y with | .s28 => true | _ => false
  | .s29, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s15 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s30, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s15 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s31, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s15 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s32, y => match y with | .s32 => true | _ => false
  | .s33, y => match y with | .s33 => true | _ => false
  | .s34, y => match y with | .s34 => true | _ => false
  | .s35, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s15 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s36, y => match y with | .s15 => true | .s36 => true | _ => false
  | .s37, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s15 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false
  | .s38, y => match y with | .s5 => true | .s6 => true | .s10 => true | .s15 => true | .s17 => true | .s21 => true | .s25 => true | .s26 => true | .s29 => true | .s30 => true | .s31 => true | .s34 => true | .s35 => true | .s36 => true | .s37 => true | .s38 => true | _ => false

def le_SN_4_step (x y z : StateSN) : Bool :=
  (!le_SN_4 x y) || ((le_SN_4 (deltaSN x z) (deltaSN y z) && le_SN_4 (deltaSN z x) (deltaSN z y)) && ((!le_SN_4 y z) || le_SN_4 x z))

def allPreordersStep_SN (x y z : StateSN) : Bool :=
  ((le_SN_0_step x y z && le_SN_1_step x y z) && (le_SN_2_step x y z && (le_SN_3_step x y z && le_SN_4_step x y z)))

def sep_SN (x y : StateSN) : Bool :=
  (le_SN_0 x y != le_SN_0 y x) || (le_SN_1 x y != le_SN_1 y x) || (le_SN_2 x y != le_SN_2 y x) || (le_SN_3 x y != le_SN_3 y x) || (le_SN_4 x y != le_SN_4 y x)

inductive StateP where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p25 | p26 | p27 | p28 | p29 | p30 | p31 | p32 | p33 | p34 | p35 | p36 | p37 | p38
  deriving Repr

def toCode_StateP : StateP → Code6
  | .p0 => .mk false false false false false false
  | .p1 => .mk true false false false false false
  | .p2 => .mk false true false false false false
  | .p3 => .mk true true false false false false
  | .p4 => .mk false false true false false false
  | .p5 => .mk true false true false false false
  | .p6 => .mk false true true false false false
  | .p7 => .mk true true true false false false
  | .p8 => .mk false false false true false false
  | .p9 => .mk true false false true false false
  | .p10 => .mk false true false true false false
  | .p11 => .mk true true false true false false
  | .p12 => .mk false false true true false false
  | .p13 => .mk true false true true false false
  | .p14 => .mk false true true true false false
  | .p15 => .mk true true true true false false
  | .p16 => .mk false false false false true false
  | .p17 => .mk true false false false true false
  | .p18 => .mk false true false false true false
  | .p19 => .mk true true false false true false
  | .p20 => .mk false false true false true false
  | .p21 => .mk true false true false true false
  | .p22 => .mk false true true false true false
  | .p23 => .mk true true true false true false
  | .p24 => .mk false false false true true false
  | .p25 => .mk true false false true true false
  | .p26 => .mk false true false true true false
  | .p27 => .mk true true false true true false
  | .p28 => .mk false false true true true false
  | .p29 => .mk true false true true true false
  | .p30 => .mk false true true true true false
  | .p31 => .mk true true true true true false
  | .p32 => .mk false false false false false true
  | .p33 => .mk true false false false false true
  | .p34 => .mk false true false false false true
  | .p35 => .mk true true false false false true
  | .p36 => .mk false false true false false true
  | .p37 => .mk true false true false false true
  | .p38 => .mk false true true false false true

def ofCode_StateP : Code6 → StateP
  | .mk false false false false false false => .p0
  | .mk true false false false false false => .p1
  | .mk false true false false false false => .p2
  | .mk true true false false false false => .p3
  | .mk false false true false false false => .p4
  | .mk true false true false false false => .p5
  | .mk false true true false false false => .p6
  | .mk true true true false false false => .p7
  | .mk false false false true false false => .p8
  | .mk true false false true false false => .p9
  | .mk false true false true false false => .p10
  | .mk true true false true false false => .p11
  | .mk false false true true false false => .p12
  | .mk true false true true false false => .p13
  | .mk false true true true false false => .p14
  | .mk true true true true false false => .p15
  | .mk false false false false true false => .p16
  | .mk true false false false true false => .p17
  | .mk false true false false true false => .p18
  | .mk true true false false true false => .p19
  | .mk false false true false true false => .p20
  | .mk true false true false true false => .p21
  | .mk false true true false true false => .p22
  | .mk true true true false true false => .p23
  | .mk false false false true true false => .p24
  | .mk true false false true true false => .p25
  | .mk false true false true true false => .p26
  | .mk true true false true true false => .p27
  | .mk false false true true true false => .p28
  | .mk true false true true true false => .p29
  | .mk false true true true true false => .p30
  | .mk true true true true true false => .p31
  | .mk false false false false false true => .p32
  | .mk true false false false false true => .p33
  | .mk false true false false false true => .p34
  | .mk true true false false false true => .p35
  | .mk false false true false false true => .p36
  | .mk true false true false false true => .p37
  | .mk false true true false false true => .p38
  | _ => .p0

theorem ofCode_toCode_StateP (x : StateP) : ofCode_StateP (toCode_StateP x) = x := by
  cases x <;> rfl

def beq_StateP (x y : StateP) : Bool := beqCode6 (toCode_StateP x) (toCode_StateP y)

theorem beq_StateP_eq {x y : StateP} (h : beq_StateP x y = true) : x = y := by
  have hc := beqCode6_eq h
  have h1 := congrArg ofCode_StateP hc
  rw [ofCode_toCode_StateP, ofCode_toCode_StateP] at h1
  exact h1

def checkAll1_StateP (p : StateP → Bool) : Bool :=
  (((((p .p0 && p .p1) && (p .p2 && p .p3)) && ((p .p4 && p .p5) && (p .p6 && (p .p7 && p .p8)))) && (((p .p9 && p .p10) && (p .p11 && (p .p12 && p .p13))) && ((p .p14 && p .p15) && (p .p16 && (p .p17 && p .p18))))) && ((((p .p19 && p .p20) && (p .p21 && (p .p22 && p .p23))) && ((p .p24 && p .p25) && (p .p26 && (p .p27 && p .p28)))) && (((p .p29 && p .p30) && (p .p31 && (p .p32 && p .p33))) && ((p .p34 && p .p35) && (p .p36 && (p .p37 && p .p38))))))

theorem checkAll1_StateP_sound (p : StateP → Bool)
    (h : checkAll1_StateP p = true) (x : StateP) : p x = true :=
  match x with
  | .p0 => (and_left (and_left (and_left (and_left (and_left h)))))
  | .p1 => (and_right (and_left (and_left (and_left (and_left h)))))
  | .p2 => (and_left (and_right (and_left (and_left (and_left h)))))
  | .p3 => (and_right (and_right (and_left (and_left (and_left h)))))
  | .p4 => (and_left (and_left (and_right (and_left (and_left h)))))
  | .p5 => (and_right (and_left (and_right (and_left (and_left h)))))
  | .p6 => (and_left (and_right (and_right (and_left (and_left h)))))
  | .p7 => (and_left (and_right (and_right (and_right (and_left (and_left h))))))
  | .p8 => (and_right (and_right (and_right (and_right (and_left (and_left h))))))
  | .p9 => (and_left (and_left (and_left (and_right (and_left h)))))
  | .p10 => (and_right (and_left (and_left (and_right (and_left h)))))
  | .p11 => (and_left (and_right (and_left (and_right (and_left h)))))
  | .p12 => (and_left (and_right (and_right (and_left (and_right (and_left h))))))
  | .p13 => (and_right (and_right (and_right (and_left (and_right (and_left h))))))
  | .p14 => (and_left (and_left (and_right (and_right (and_left h)))))
  | .p15 => (and_right (and_left (and_right (and_right (and_left h)))))
  | .p16 => (and_left (and_right (and_right (and_right (and_left h)))))
  | .p17 => (and_left (and_right (and_right (and_right (and_right (and_left h))))))
  | .p18 => (and_right (and_right (and_right (and_right (and_right (and_left h))))))
  | .p19 => (and_left (and_left (and_left (and_left (and_right h)))))
  | .p20 => (and_right (and_left (and_left (and_left (and_right h)))))
  | .p21 => (and_left (and_right (and_left (and_left (and_right h)))))
  | .p22 => (and_left (and_right (and_right (and_left (and_left (and_right h))))))
  | .p23 => (and_right (and_right (and_right (and_left (and_left (and_right h))))))
  | .p24 => (and_left (and_left (and_right (and_left (and_right h)))))
  | .p25 => (and_right (and_left (and_right (and_left (and_right h)))))
  | .p26 => (and_left (and_right (and_right (and_left (and_right h)))))
  | .p27 => (and_left (and_right (and_right (and_right (and_left (and_right h))))))
  | .p28 => (and_right (and_right (and_right (and_right (and_left (and_right h))))))
  | .p29 => (and_left (and_left (and_left (and_right (and_right h)))))
  | .p30 => (and_right (and_left (and_left (and_right (and_right h)))))
  | .p31 => (and_left (and_right (and_left (and_right (and_right h)))))
  | .p32 => (and_left (and_right (and_right (and_left (and_right (and_right h))))))
  | .p33 => (and_right (and_right (and_right (and_left (and_right (and_right h))))))
  | .p34 => (and_left (and_left (and_right (and_right (and_right h)))))
  | .p35 => (and_right (and_left (and_right (and_right (and_right h)))))
  | .p36 => (and_left (and_right (and_right (and_right (and_right h)))))
  | .p37 => (and_left (and_right (and_right (and_right (and_right (and_right h))))))
  | .p38 => (and_right (and_right (and_right (and_right (and_right (and_right h))))))

def checkAll2_StateP (p : StateP → StateP → Bool) : Bool :=
  checkAll1_StateP (fun x => checkAll1_StateP (fun y => p x y))

theorem checkAll2_StateP_sound (p : StateP → StateP → Bool)
    (h : checkAll2_StateP p = true) (x y : StateP) : p x y = true :=
  checkAll1_StateP_sound _ (checkAll1_StateP_sound _ h x) y

def deltaP : StateP → StateP → StateP
  | .p0, y => match y with | .p0 => .p1 | .p1 => .p2 | .p2 => .p4 | .p3 => .p5 | .p4 => .p8 | .p5 => .p9 | .p6 => .p10 | .p7 => .p11 | .p8 => .p9 | .p10 => .p9 | .p12 => .p19 | .p13 => .p10 | .p17 => .p20 | .p19 => .p9 | .p21 => .p8 | .p22 => .p9 | .p28 => .p20 | .p30 => .p9 | .p31 => .p9 | .p37 => .p37 | .p38 => .p9 | _ => .p18
  | .p1, y => match y with | .p0 => .p3 | .p1 => .p6 | .p2 => .p12 | .p4 => .p21 | .p5 => .p22 | .p7 => .p7 | .p8 => .p30 | .p9 => .p9 | .p10 => .p31 | .p11 => .p20 | .p12 => .p12 | .p14 => .p32 | .p15 => .p15 | .p16 => .p16 | .p17 => .p17 | .p18 => .p18 | .p19 => .p38 | .p20 => .p20 | .p21 => .p21 | .p22 => .p22 | .p23 => .p23 | .p24 => .p24 | .p25 => .p25 | .p26 => .p26 | .p27 => .p27 | .p28 => .p28 | .p29 => .p29 | .p30 => .p30 | .p31 => .p31 | .p32 => .p32 | .p33 => .p33 | .p34 => .p34 | .p35 => .p35 | .p36 => .p36 | .p37 => .p37 | .p38 => .p38 | _ => .p13
  | .p2, y => match y with | .p0 => .p7 | .p1 => .p14 | .p2 => .p15 | .p3 => .p23 | .p6 => .p23 | .p13 => .p23 | .p17 => .p27 | .p24 => .p24 | .p26 => .p27 | .p27 => .p27 | .p28 => .p27 | .p29 => .p29 | .p34 => .p24 | .p35 => .p27 | .p36 => .p24 | .p37 => .p37 | _ => .p33
  | .p3, y => match y with | .p0 => .p6 | .p1 => .p15 | .p2 => .p24 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p4, y => match y with | .p0 => .p16 | .p1 => .p25 | .p2 => .p27 | .p3 => .p24 | .p4 => .p24 | .p6 => .p24 | .p7 => .p24 | .p12 => .p24 | .p13 => .p24 | .p17 => .p24 | .p21 => .p24 | .p28 => .p24 | .p37 => .p37 | _ => .p29
  | .p5, y => match y with | .p0 => .p17 | .p1 => .p26 | .p3 => .p34 | .p6 => .p34 | .p13 => .p34 | .p29 => .p29 | .p37 => .p37 | _ => .p24
  | .p6, y => match y with | .p0 => .p13 | .p1 => .p23 | .p2 => .p24 | .p3 => .p34 | .p4 => .p24 | .p6 => .p36 | .p12 => .p24 | .p13 => .p36 | .p21 => .p24 | .p37 => .p37 | _ => .p29
  | .p7, y => match y with | .p0 => .p15 | .p1 => .p24 | .p17 => .p37 | .p24 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p8, y => match y with | .p0 => .p27 | .p1 => .p27 | .p2 => .p24 | .p3 => .p24 | .p4 => .p24 | .p6 => .p24 | .p7 => .p24 | .p12 => .p24 | .p13 => .p24 | .p17 => .p24 | .p21 => .p24 | .p28 => .p24 | .p37 => .p37 | _ => .p29
  | .p9, y => match y with | .p0 => .p24 | .p37 => .p37 | _ => .p29
  | .p10, y => match y with | .p0 => .p28 | .p1 => .p35 | .p3 => .p36 | .p6 => .p36 | .p13 => .p36 | .p29 => .p29 | .p37 => .p37 | _ => .p24
  | .p11, y => match y with | .p0 => .p24 | .p1 => .p24 | .p2 => .p24 | .p3 => .p24 | .p4 => .p24 | .p6 => .p24 | .p12 => .p24 | .p13 => .p24 | .p21 => .p24 | .p37 => .p37 | _ => .p29
  | .p12, y => match y with | .p0 => .p7 | .p1 => .p33 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p13, y => match y with | .p0 => .p13 | .p1 => .p33 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p14, y => match y with | .p0 => .p24 | .p1 => .p36 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p15 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p15, y => match y with | .p14 => .p37 | .p15 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p32 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p16, y => match y with | .p0 => .p24 | .p17 => .p37 | .p24 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p17, y => match y with | .p0 => .p23 | .p1 => .p29 | _ => .p37
  | .p18, y => match y with | .p37 => .p37 | _ => .p29
  | .p19, y => match y with | .p0 => .p35 | .p1 => .p27 | .p2 => .p24 | .p3 => .p24 | .p4 => .p24 | .p6 => .p24 | .p7 => .p24 | .p12 => .p24 | .p13 => .p24 | .p17 => .p24 | .p21 => .p24 | .p28 => .p24 | .p37 => .p37 | _ => .p29
  | .p20, y => match y with | .p0 => .p24 | .p1 => .p24 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p21, y => match y with | .p0 => .p16 | .p1 => .p33 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p22, y => match y with | .p0 => .p17 | .p1 => .p27 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p23, y => match y with | .p0 => .p24 | .p7 => .p37 | .p14 => .p37 | .p15 => .p37 | .p16 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p32 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p24, y => match y with | .p0 => .p29 | _ => .p37
  | .p25, y => match y with | .p1 => .p24 | .p7 => .p37 | .p14 => .p37 | .p15 => .p37 | .p16 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p32 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p26, y => match y with | .p0 => .p34 | .p1 => .p29 | _ => .p37
  | .p27, y => match y with | .p0 => .p29 | .p1 => .p29 | _ => .p37
  | .p28, y => match y with | .p0 => .p33 | .p1 => .p29 | _ => .p37
  | .p29, _ => .p37
  | .p30, y => match y with | .p0 => .p27 | .p1 => .p27 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p31, y => match y with | .p0 => .p28 | .p1 => .p27 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29
  | .p32, y => match y with | .p0 => .p24 | .p1 => .p24 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p15 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p33, y => match y with | .p7 => .p37 | .p14 => .p37 | .p15 => .p37 | .p16 => .p37 | .p17 => .p37 | .p23 => .p37 | .p24 => .p37 | .p25 => .p37 | .p26 => .p37 | .p27 => .p37 | .p28 => .p37 | .p29 => .p37 | .p32 => .p37 | .p33 => .p37 | .p34 => .p37 | .p35 => .p37 | .p36 => .p37 | .p37 => .p37 | _ => .p29
  | .p34, y => match y with | .p0 => .p36 | _ => .p37
  | .p35, y => match y with | .p0 => .p24 | .p1 => .p29 | _ => .p37
  | .p36, y => match y with | .p0 => .p24 | _ => .p37
  | .p37, _ => .p37
  | .p38, y => match y with | .p0 => .p35 | .p1 => .p27 | .p3 => .p24 | .p6 => .p24 | .p13 => .p24 | .p37 => .p37 | _ => .p29

def le_P_0 : StateP → StateP → Bool
  | .p0, y => match y with | .p1 => false | _ => true
  | .p1, y => match y with | .p0 => false | _ => true
  | .p2, y => match y with | .p0 => false | .p1 => false | .p3 => false | .p6 => false | .p13 => false | _ => true
  | .p3, y => match y with | .p0 => false | .p1 => false | .p2 => false | _ => true
  | .p4, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p5 => false | .p6 => false | .p10 => false | .p12 => false | .p13 => false | .p22 => false | .p31 => false | _ => true
  | .p5, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p6 => false | .p12 => false | .p13 => false | .p21 => false | _ => true
  | .p6, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | _ => true
  | .p7, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p8 => false | .p10 => false | .p12 => false | .p13 => false | .p19 => false | .p21 => false | .p22 => false | .p30 => false | .p31 => false | .p38 => false | _ => true
  | .p8, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p7 => false | .p10 => false | .p12 => false | .p13 => false | .p17 => false | .p19 => false | .p21 => false | .p22 => false | .p31 => false | .p38 => false | _ => true
  | .p9, y => match y with | .p9 => true | .p11 => true | .p15 => true | .p16 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p25 => true | .p26 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p10, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p12 => false | .p13 => false | .p21 => false | .p22 => false | _ => true
  | .p11, y => match y with | .p11 => true | .p18 => true | .p20 => true | .p24 => true | .p25 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p12, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p10 => false | .p13 => false | _ => true
  | .p13, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p10 => false | _ => true
  | .p14, y => match y with | .p9 => true | .p11 => true | .p14 => true | .p15 => true | .p16 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p25 => true | .p26 => true | .p27 => true | .p29 => true | .p32 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p15, y => match y with | .p11 => true | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p25 => true | .p26 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p16, y => match y with | .p11 => true | .p15 => true | .p16 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p25 => true | .p26 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p17, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p7 => false | .p8 => false | .p10 => false | .p12 => false | .p13 => false | .p19 => false | .p21 => false | .p22 => false | .p30 => false | .p31 => false | .p38 => false | _ => true
  | .p18, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p19, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p7 => false | .p10 => false | .p12 => false | .p13 => false | .p17 => false | .p21 => false | .p22 => false | .p31 => false | _ => true
  | .p20, y => match y with | .p18 => true | .p20 => true | .p24 => true | .p25 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p21, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p10 => false | .p12 => false | .p13 => false | .p22 => false | .p31 => false | _ => true
  | .p22, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p10 => false | .p12 => false | .p13 => false | .p21 => false | _ => true
  | .p23, y => match y with | .p11 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p25 => true | .p26 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p24, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p25, y => match y with | .p18 => true | .p24 => true | .p25 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p26, y => match y with | .p11 => true | .p18 => true | .p20 => true | .p24 => true | .p25 => true | .p26 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p27, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p28, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p7 => false | .p8 => false | .p10 => false | .p12 => false | .p13 => false | .p17 => false | .p19 => false | .p21 => false | .p22 => false | .p30 => false | .p31 => false | .p38 => false | _ => true
  | .p29, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p30, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p7 => false | .p8 => false | .p10 => false | .p12 => false | .p13 => false | .p17 => false | .p19 => false | .p21 => false | .p22 => false | .p31 => false | .p38 => false | _ => true
  | .p31, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p10 => false | .p12 => false | .p13 => false | .p21 => false | .p22 => false | _ => true
  | .p32, y => match y with | .p9 => true | .p11 => true | .p15 => true | .p16 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p25 => true | .p26 => true | .p27 => true | .p29 => true | .p32 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p33, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p34, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p35, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p36, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p37, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p38, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | .p7 => false | .p10 => false | .p12 => false | .p13 => false | .p17 => false | .p19 => false | .p21 => false | .p22 => false | .p31 => false | _ => true

def le_P_0_step (x y z : StateP) : Bool :=
  (!le_P_0 x y) || ((le_P_0 (deltaP x z) (deltaP y z) && le_P_0 (deltaP z x) (deltaP z y)) && ((!le_P_0 y z) || le_P_0 x z))

def le_P_1 : StateP → StateP → Bool
  | .p0, y => match y with | .p0 => true | .p2 => true | .p8 => true | .p11 => true | .p14 => true | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p36 => true | .p37 => true | _ => false
  | .p1, y => match y with | .p1 => true | .p4 => true | .p7 => true | .p9 => true | .p15 => true | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p2, y => match y with | .p2 => true | .p8 => true | .p11 => true | .p14 => true | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p36 => true | .p37 => true | _ => false
  | .p3, y => match y with | .p3 => true | .p12 => true | .p15 => true | .p16 => true | .p18 => true | .p20 => true | .p24 => true | .p27 => true | .p29 => true | .p30 => true | .p32 => true | .p33 => true | .p36 => true | .p37 => true | _ => false
  | .p4, y => match y with | .p4 => true | .p9 => true | .p15 => true | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p5, y => match y with | .p5 => true | .p9 => true | .p18 => true | .p19 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p6, y => match y with | .p6 => true | .p7 => true | .p9 => true | .p15 => true | .p18 => true | .p21 => true | .p24 => true | .p25 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p7, y => match y with | .p7 => true | .p15 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p8, y => match y with | .p8 => true | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p9, y => match y with | .p9 => true | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p10, y => match y with | .p8 => true | .p9 => true | .p10 => true | .p11 => true | .p18 => true | .p19 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p11, y => match y with | .p11 => true | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p12, y => match y with | .p12 => true | .p18 => true | .p20 => true | .p24 => true | .p27 => true | .p29 => true | .p30 => true | .p32 => true | .p33 => true | .p36 => true | .p37 => true | _ => false
  | .p13, y => match y with | .p7 => true | .p9 => true | .p12 => true | .p13 => true | .p15 => true | .p16 => true | .p18 => true | .p20 => true | .p21 => true | .p24 => true | .p25 => true | .p27 => true | .p29 => true | .p30 => true | .p32 => true | .p33 => true | .p36 => true | .p37 => true | _ => false
  | .p14, y => match y with | .p14 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p36 => true | .p37 => true | _ => false
  | .p15, y => match y with | .p15 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p16, y => match y with | .p16 => true | .p24 => true | .p27 => true | .p29 => true | .p37 => true | _ => false
  | .p17, y => match y with | .p17 => true | .p24 => true | .p27 => true | .p29 => true | .p35 => true | .p37 => true | _ => false
  | .p18, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p19, y => match y with | .p9 => true | .p18 => true | .p19 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p20, y => match y with | .p18 => true | .p20 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p21, y => match y with | .p9 => true | .p15 => true | .p18 => true | .p21 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p22, y => match y with | .p9 => true | .p18 => true | .p22 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | .p38 => true | _ => false
  | .p23, y => match y with | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p24, y => match y with | .p24 => true | .p29 => true | .p37 => true | _ => false
  | .p25, y => match y with | .p24 => true | .p25 => true | .p29 => true | .p37 => true | _ => false
  | .p26, y => match y with | .p24 => true | .p26 => true | .p27 => true | .p29 => true | .p37 => true | _ => false
  | .p27, y => match y with | .p24 => true | .p27 => true | .p29 => true | .p37 => true | _ => false
  | .p28, y => match y with | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p35 => true | .p37 => true | _ => false
  | .p29, y => match y with | .p29 => true | .p37 => true | _ => false
  | .p30, y => match y with | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p30 => true | .p33 => true | .p37 => true | _ => false
  | .p31, y => match y with | .p9 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p30 => true | .p31 => true | .p33 => true | .p37 => true | .p38 => true | _ => false
  | .p32, y => match y with | .p24 => true | .p27 => true | .p29 => true | .p32 => true | .p33 => true | .p36 => true | .p37 => true | _ => false
  | .p33, y => match y with | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | _ => false
  | .p34, y => match y with | .p24 => true | .p29 => true | .p34 => true | .p36 => true | .p37 => true | _ => false
  | .p35, y => match y with | .p24 => true | .p27 => true | .p29 => true | .p35 => true | .p37 => true | _ => false
  | .p36, y => match y with | .p24 => true | .p29 => true | .p36 => true | .p37 => true | _ => false
  | .p37, y => match y with | .p37 => true | _ => false
  | .p38, y => match y with | .p9 => true | .p18 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p37 => true | .p38 => true | _ => false

def le_P_1_step (x y z : StateP) : Bool :=
  (!le_P_1 x y) || ((le_P_1 (deltaP x z) (deltaP y z) && le_P_1 (deltaP z x) (deltaP z y)) && ((!le_P_1 y z) || le_P_1 x z))

def le_P_2 : StateP → StateP → Bool
  | .p0, _ => true
  | .p1, y => match y with | .p0 => false | _ => true
  | .p2, y => match y with | .p0 => false | .p1 => false | .p3 => false | _ => true
  | .p3, y => match y with | .p0 => false | .p1 => false | _ => true
  | .p4, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p5 => false | .p6 => false | _ => true
  | .p5, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p6 => false | _ => true
  | .p6, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | _ => true
  | .p7, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p8, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p9, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p10, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p11, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p12, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p13, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p14, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p15, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p16, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p17, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p18, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p19, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p20, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p21, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p22, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p23, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p24, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p25, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p26, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p27, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p28, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p29, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p30, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p31, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p32, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p33, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p34, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p35, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p36, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p37, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true
  | .p38, y => match y with | .p0 => false | .p1 => false | .p2 => false | .p3 => false | .p4 => false | .p5 => false | .p6 => false | _ => true

def le_P_2_step (x y z : StateP) : Bool :=
  (!le_P_2 x y) || ((le_P_2 (deltaP x z) (deltaP y z) && le_P_2 (deltaP z x) (deltaP z y)) && ((!le_P_2 y z) || le_P_2 x z))

def le_P_3 : StateP → StateP → Bool
  | .p0, y => match y with | .p0 => true | _ => false
  | .p1, y => match y with | .p1 => true | _ => false
  | .p2, y => match y with | .p2 => true | _ => false
  | .p3, y => match y with | .p3 => true | _ => false
  | .p4, y => match y with | .p4 => true | .p5 => true | _ => false
  | .p5, y => match y with | .p5 => true | _ => false
  | .p6, y => match y with | .p6 => true | _ => false
  | .p7, y => match y with | .p7 => true | .p28 => true | _ => false
  | .p8, y => match y with | .p7 => true | .p8 => true | .p9 => true | .p11 => true | .p15 => true | .p17 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p9, y => match y with | .p9 => true | .p11 => true | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p10, y => match y with | .p10 => true | _ => false
  | .p11, y => match y with | .p11 => true | .p20 => true | _ => false
  | .p12, y => match y with | .p10 => true | .p12 => true | .p31 => true | _ => false
  | .p13, y => match y with | .p13 => true | _ => false
  | .p14, y => match y with | .p14 => true | _ => false
  | .p15, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p16, y => match y with | .p16 => true | .p17 => true | .p28 => true | _ => false
  | .p17, y => match y with | .p17 => true | .p28 => true | _ => false
  | .p18, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p19, y => match y with | .p7 => true | .p9 => true | .p11 => true | .p15 => true | .p17 => true | .p18 => true | .p19 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p20, y => match y with | .p20 => true | _ => false
  | .p21, y => match y with | .p10 => true | .p21 => true | .p22 => true | .p31 => true | _ => false
  | .p22, y => match y with | .p10 => true | .p22 => true | .p31 => true | _ => false
  | .p23, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p24, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p25, y => match y with | .p25 => true | .p26 => true | _ => false
  | .p26, y => match y with | .p26 => true | _ => false
  | .p27, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p28, y => match y with | .p28 => true | _ => false
  | .p29, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p30, y => match y with | .p7 => true | .p9 => true | .p11 => true | .p15 => true | .p17 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p30 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p31, y => match y with | .p31 => true | _ => false
  | .p32, y => match y with | .p32 => true | _ => false
  | .p33, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p34, y => match y with | .p34 => true | _ => false
  | .p35, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p36, y => match y with | .p36 => true | _ => false
  | .p37, y => match y with | .p15 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p38, y => match y with | .p7 => true | .p9 => true | .p11 => true | .p15 => true | .p17 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | .p38 => true | _ => false

def le_P_3_step (x y z : StateP) : Bool :=
  (!le_P_3 x y) || ((le_P_3 (deltaP x z) (deltaP y z) && le_P_3 (deltaP z x) (deltaP z y)) && ((!le_P_3 y z) || le_P_3 x z))

def le_P_4 : StateP → StateP → Bool
  | .p0, y => match y with | .p0 => true | _ => false
  | .p1, y => match y with | .p1 => true | _ => false
  | .p2, y => match y with | .p2 => true | _ => false
  | .p3, y => match y with | .p3 => true | _ => false
  | .p4, y => match y with | .p4 => true | _ => false
  | .p5, y => match y with | .p5 => true | _ => false
  | .p6, y => match y with | .p6 => true | _ => false
  | .p7, y => match y with | .p7 => true | _ => false
  | .p8, y => match y with | .p8 => true | _ => false
  | .p9, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p31 => true | _ => false
  | .p10, y => match y with | .p10 => true | .p13 => true | _ => false
  | .p11, y => match y with | .p11 => true | _ => false
  | .p12, y => match y with | .p12 => true | _ => false
  | .p13, y => match y with | .p13 => true | _ => false
  | .p14, y => match y with | .p14 => true | _ => false
  | .p15, y => match y with | .p15 => true | _ => false
  | .p16, y => match y with | .p16 => true | _ => false
  | .p17, y => match y with | .p17 => true | _ => false
  | .p18, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p31 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p19, y => match y with | .p19 => true | _ => false
  | .p20, y => match y with | .p10 => true | .p13 => true | .p20 => true | .p31 => true | _ => false
  | .p21, y => match y with | .p21 => true | _ => false
  | .p22, y => match y with | .p22 => true | _ => false
  | .p23, y => match y with | .p23 => true | _ => false
  | .p24, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p31 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p25, y => match y with | .p25 => true | _ => false
  | .p26, y => match y with | .p26 => true | _ => false
  | .p27, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p31 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p28, y => match y with | .p13 => true | .p28 => true | _ => false
  | .p29, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p31 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p30, y => match y with | .p30 => true | _ => false
  | .p31, y => match y with | .p13 => true | .p31 => true | _ => false
  | .p32, y => match y with | .p32 => true | _ => false
  | .p33, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p31 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p34, y => match y with | .p34 => true | _ => false
  | .p35, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p31 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p36, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p31 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p37, y => match y with | .p9 => true | .p10 => true | .p13 => true | .p18 => true | .p20 => true | .p23 => true | .p24 => true | .p27 => true | .p28 => true | .p29 => true | .p31 => true | .p33 => true | .p34 => true | .p35 => true | .p36 => true | .p37 => true | _ => false
  | .p38, y => match y with | .p38 => true | _ => false

def le_P_4_step (x y z : StateP) : Bool :=
  (!le_P_4 x y) || ((le_P_4 (deltaP x z) (deltaP y z) && le_P_4 (deltaP z x) (deltaP z y)) && ((!le_P_4 y z) || le_P_4 x z))

def allPreordersStep_P (x y z : StateP) : Bool :=
  ((le_P_0_step x y z && le_P_1_step x y z) && (le_P_2_step x y z && (le_P_3_step x y z && le_P_4_step x y z)))

def sep_P (x y : StateP) : Bool :=
  (le_P_0 x y != le_P_0 y x) || (le_P_1 x y != le_P_1 y x) || (le_P_2 x y != le_P_2 y x) || (le_P_3 x y != le_P_3 y x) || (le_P_4 x y != le_P_4 y x)

end ZeroNavigatorCellular
