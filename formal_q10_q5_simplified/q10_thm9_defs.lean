import formal_algebra.s_structural_laws

namespace SimplifiedQ10Q5
set_option linter.constructorNameAsVariable false
open FormalAlgebra

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := ((Bool.and_eq_true a b).mp h).1
theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := ((Bool.and_eq_true a b).mp h).2
theorem imp_bool {a b : Bool} (ha : a = true) (h : (!a || b) = true) : b = true := by rw [ha] at h; exact h
theorem if_false_eq_true {α : Type} {t e : α} : (if false = true then t else e) = e := rfl
theorem if_true_eq_true  {α : Type} {t e : α} : (if true = true then t else e) = t := rfl

inductive PTree64 (α : Type) where
  | lf (v : α) : PTree64 α
  | nd (l r : PTree64 α) : PTree64 α

def PTree64.get {α : Type} : PTree64 α → Bool → Bool → Bool → Bool → Bool → Bool → α
  | .lf v, _, _, _, _, _, _ => v
  | .nd l _, false, b4, b3, b2, b1, b0 => PTree64.get l b4 b3 b2 b1 b0 false
  | .nd _ r, true,  b4, b3, b2, b1, b0 => PTree64.get r b4 b3 b2 b1 b0 false

def PTree64.lookup {α : Type} (t : PTree64 α) (n : Nat) : α :=
  let b5 := Nat.ble 32 n; let n := if b5 then n - 32 else n
  let b4 := Nat.ble 16 n; let n := if b4 then n - 16 else n
  let b3 := Nat.ble 8 n;  let n := if b3 then n - 8 else n
  let b2 := Nat.ble 4 n;  let n := if b2 then n - 4 else n
  let b1 := Nat.ble 2 n;  let n := if b1 then n - 2 else n
  t.get b5 b4 b3 b2 b1 (Nat.ble 1 n)

def checkNat (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => f k && checkNat f k

theorem checkNat_sound {f : Nat → Bool} : ∀ {n i : Nat}, checkNat f n = true → i < n → f i = true
  | 0, _, _, hi => False.elim (Nat.not_lt_zero _ hi)
  | k + 1, i, h, hi => by
    have ⟨hfk, hrest⟩ := (Bool.and_eq_true _ _).mp h
    if heq : i = k then subst heq; exact hfk
    else exact checkNat_sound hrest (by omega)

def checkNat1 (n : Nat) (f : Nat → Bool) : Bool := checkNat f n
theorem checkNat1_sound (n : Nat) (f : Nat → Bool) (h : checkNat1 n f = true) {i : Nat} (hi : i < n) : f i = true :=
  checkNat_sound h hi

def checkNat2 (n1 n2 : Nat) (f : Nat → Nat → Bool) : Bool :=
  checkNat1 n1 (fun i => checkNat1 n2 (fun j => f i j))
theorem checkNat2_sound (n1 n2 : Nat) (f : Nat → Nat → Bool) (h : checkNat2 n1 n2 f = true)
    {i j : Nat} (hi : i < n1) (hj : j < n2) : f i j = true :=
  checkNat1_sound n2 (fun j => f i j) (checkNat1_sound n1 _ h hi) hj

inductive StateSN where
  | sn0 | sn1 | sn2 | sn3 | sn4 | sn5 | sn6 | sn7 | sn8 | sn9 | sn10 | sn11 | sn12 | sn13 | sn14 | sn15 | sn16 | sn17 | sn18 | sn19 | sn20 | sn21 | sn22 | sn23 | sn24 | sn25 | sn26 | sn27 | sn28 | sn29 | sn30 | sn31 | sn32 | sn33 | sn34 | sn35 | sn36 | sn37 | sn38
def snIdx : StateSN → Nat | .sn0 => 0 | .sn1 => 1 | .sn2 => 2 | .sn3 => 3 | .sn4 => 4 | .sn5 => 5 | .sn6 => 6 | .sn7 => 7 | .sn8 => 8 | .sn9 => 9 | .sn10 => 10 | .sn11 => 11 | .sn12 => 12 | .sn13 => 13 | .sn14 => 14 | .sn15 => 15 | .sn16 => 16 | .sn17 => 17 | .sn18 => 18 | .sn19 => 19 | .sn20 => 20 | .sn21 => 21 | .sn22 => 22 | .sn23 => 23 | .sn24 => 24 | .sn25 => 25 | .sn26 => 26 | .sn27 => 27 | .sn28 => 28 | .sn29 => 29 | .sn30 => 30 | .sn31 => 31 | .sn32 => 32 | .sn33 => 33 | .sn34 => 34 | .sn35 => 35 | .sn36 => 36 | .sn37 => 37 | .sn38 => 38
def ofSnIdxTree : PTree64 StateSN := (.nd (.nd (.nd (.nd (.nd (.nd (.lf .sn0) (.lf .sn1)) (.nd (.lf .sn2) (.lf .sn3))) (.nd (.nd (.lf .sn4) (.lf .sn5)) (.nd (.lf .sn6) (.lf .sn7)))) (.nd (.nd (.nd (.lf .sn8) (.lf .sn9)) (.nd (.lf .sn10) (.lf .sn11))) (.nd (.nd (.lf .sn12) (.lf .sn13)) (.nd (.lf .sn14) (.lf .sn15))))) (.nd (.nd (.nd (.nd (.lf .sn16) (.lf .sn17)) (.nd (.lf .sn18) (.lf .sn19))) (.nd (.nd (.lf .sn20) (.lf .sn21)) (.nd (.lf .sn22) (.lf .sn23)))) (.nd (.nd (.nd (.lf .sn24) (.lf .sn25)) (.nd (.lf .sn26) (.lf .sn27))) (.nd (.nd (.lf .sn28) (.lf .sn29)) (.nd (.lf .sn30) (.lf .sn31)))))) (.nd (.nd (.nd (.nd (.nd (.lf .sn32) (.lf .sn33)) (.nd (.lf .sn34) (.lf .sn35))) (.nd (.nd (.lf .sn36) (.lf .sn37)) (.lf .sn38))) (.lf .sn38)) (.lf .sn38)))
def ofSnIdx (n : Nat) : StateSN := ofSnIdxTree.lookup n
def beq_StateSN (a b : StateSN) : Bool := Nat.beq (snIdx a) (snIdx b)
def deltaSN : StateSN → StateSN → StateSN
  | .sn0, y => match y with | .sn0 => .sn1 | .sn1 => .sn2 | .sn2 => .sn3 | .sn3 => .sn4 | .sn4 => .sn5 | .sn7 => .sn8 | .sn8 => .sn5 | .sn9 => .sn10 | .sn10 => .sn5 | .sn11 => .sn12 | .sn12 => .sn5 | .sn13 => .sn4 | .sn14 => .sn5 | .sn15 => .sn10 | .sn16 => .sn5 | .sn17 => .sn5 | .sn18 => .sn5 | .sn19 => .sn20 | .sn32 => .sn21 | .sn36 => .sn21 | .sn38 => .sn38 | _ => .sn6
  | .sn1, y => match y with | .sn0 => .sn7 | .sn1 => .sn9 | .sn2 => .sn11 | .sn3 => .sn13 | .sn4 => .sn14 | .sn5 => .sn5 | .sn6 => .sn6 | .sn8 => .sn16 | .sn10 => .sn17 | .sn11 => .sn11 | .sn12 => .sn18 | .sn13 => .sn13 | .sn14 => .sn14 | .sn16 => .sn16 | .sn17 => .sn17 | .sn18 => .sn18 | .sn19 => .sn19 | .sn20 => .sn21 | .sn21 => .sn21 | .sn22 => .sn23 | .sn23 => .sn23 | .sn24 => .sn24 | .sn25 => .sn25 | .sn26 => .sn26 | .sn27 => .sn27 | .sn28 => .sn28 | .sn29 => .sn29 | .sn30 => .sn30 | .sn31 => .sn31 | .sn32 => .sn32 | .sn33 => .sn33 | .sn34 => .sn34 | .sn35 => .sn35 | .sn36 => .sn36 | .sn37 => .sn37 | .sn38 => .sn38 | _ => .sn15
  | .sn2, y => match y with | .sn0 => .sn19 | .sn1 => .sn22 | .sn2 => .sn24 | .sn7 => .sn26 | .sn9 => .sn26 | .sn15 => .sn26 | .sn29 => .sn29 | .sn30 => .sn30 | .sn31 => .sn31 | .sn32 => .sn31 | .sn33 => .sn31 | .sn34 => .sn29 | .sn35 => .sn29 | .sn36 => .sn31 | .sn37 => .sn31 | .sn38 => .sn38 | _ => .sn25
  | .sn3, y => match y with | .sn0 => .sn27 | .sn1 => .sn28 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn29 | .sn19 => .sn29 | .sn32 => .sn29 | .sn36 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn4, y => match y with | .sn0 => .sn31 | .sn1 => .sn31 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn29 | .sn19 => .sn29 | .sn32 => .sn29 | .sn36 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn5, y => match y with | .sn0 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn6, y => match y with | .sn38 => .sn38 | _ => .sn30
  | .sn7, y => match y with | .sn0 => .sn9 | .sn1 => .sn24 | .sn2 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn8, y => match y with | .sn0 => .sn32 | .sn1 => .sn33 | .sn7 => .sn34 | .sn9 => .sn34 | .sn15 => .sn34 | .sn30 => .sn30 | .sn38 => .sn38 | _ => .sn29
  | .sn9, y => match y with | .sn0 => .sn15 | .sn1 => .sn26 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn34 | .sn9 => .sn35 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn35 | .sn38 => .sn38 | _ => .sn30
  | .sn10, y => match y with | .sn0 => .sn36 | .sn1 => .sn37 | .sn7 => .sn35 | .sn9 => .sn35 | .sn15 => .sn35 | .sn30 => .sn30 | .sn38 => .sn38 | _ => .sn29
  | .sn11, y => match y with | .sn0 => .sn19 | .sn1 => .sn25 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn12, y => match y with | .sn0 => .sn37 | .sn1 => .sn31 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn29 | .sn19 => .sn29 | .sn32 => .sn29 | .sn36 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn13, y => match y with | .sn0 => .sn27 | .sn1 => .sn25 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn14, y => match y with | .sn0 => .sn31 | .sn1 => .sn31 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn15, y => match y with | .sn0 => .sn15 | .sn1 => .sn25 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn16, y => match y with | .sn0 => .sn32 | .sn1 => .sn31 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn17, y => match y with | .sn0 => .sn36 | .sn1 => .sn31 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn18, y => match y with | .sn0 => .sn37 | .sn1 => .sn31 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn19, y => match y with | .sn0 => .sn24 | .sn1 => .sn29 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn20, y => match y with | .sn0 => .sn29 | .sn1 => .sn29 | .sn2 => .sn29 | .sn3 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn11 => .sn29 | .sn13 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn21, y => match y with | .sn0 => .sn29 | .sn1 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn38 => .sn38 | _ => .sn30
  | .sn22, y => match y with | .sn0 => .sn29 | .sn1 => .sn35 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn23, y => match y with | .sn0 => .sn29 | .sn1 => .sn29 | .sn7 => .sn29 | .sn9 => .sn29 | .sn15 => .sn29 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn24, y => match y with | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn25, y => match y with | .sn19 => .sn38 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn27 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn26, y => match y with | .sn0 => .sn29 | .sn19 => .sn38 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn27 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn27, y => match y with | .sn0 => .sn29 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn28, y => match y with | .sn1 => .sn29 | .sn19 => .sn38 | .sn22 => .sn38 | .sn23 => .sn38 | .sn24 => .sn38 | .sn25 => .sn38 | .sn26 => .sn38 | .sn27 => .sn38 | .sn28 => .sn38 | .sn29 => .sn38 | .sn30 => .sn38 | .sn31 => .sn38 | .sn32 => .sn38 | .sn33 => .sn38 | .sn34 => .sn38 | .sn35 => .sn38 | .sn36 => .sn38 | .sn37 => .sn38 | .sn38 => .sn38 | _ => .sn30
  | .sn29, y => match y with | .sn0 => .sn30 | _ => .sn38
  | .sn30, _ => .sn38
  | .sn31, y => match y with | .sn0 => .sn30 | .sn1 => .sn30 | _ => .sn38
  | .sn32, y => match y with | .sn0 => .sn26 | .sn1 => .sn30 | _ => .sn38
  | .sn33, y => match y with | .sn0 => .sn34 | .sn1 => .sn30 | _ => .sn38
  | .sn34, y => match y with | .sn0 => .sn35 | _ => .sn38
  | .sn35, y => match y with | .sn0 => .sn29 | _ => .sn38
  | .sn36, y => match y with | .sn0 => .sn25 | .sn1 => .sn30 | _ => .sn38
  | .sn37, y => match y with | .sn0 => .sn29 | .sn1 => .sn30 | _ => .sn38
  | .sn38, _ => .sn38
def dsnRow_0 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 1) (.lf 2)) (.nd (.lf 3) (.lf 4))) (.nd (.nd (.lf 5) (.lf 6)) (.nd (.lf 6) (.lf 8)))) (.nd (.nd (.nd (.lf 5) (.lf 10)) (.nd (.lf 5) (.lf 12))) (.nd (.nd (.lf 5) (.lf 4)) (.nd (.lf 5) (.lf 10))))) (.nd (.nd (.nd (.lf 5) (.nd (.lf 5) (.lf 20))) (.lf 6)) (.lf 6))) (.nd (.nd (.nd (.nd (.nd (.lf 21) (.lf 6)) (.lf 6)) (.nd (.nd (.lf 21) (.lf 6)) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_1 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 7) (.lf 9)) (.nd (.lf 11) (.lf 13))) (.nd (.nd (.lf 14) (.lf 5)) (.nd (.lf 6) (.lf 15)))) (.nd (.nd (.nd (.lf 16) (.lf 15)) (.nd (.lf 17) (.lf 11))) (.nd (.nd (.lf 18) (.lf 13)) (.nd (.lf 14) (.lf 15))))) (.nd (.nd (.nd (.nd (.lf 16) (.lf 17)) (.nd (.lf 18) (.lf 19))) (.nd (.lf 21) (.lf 23))) (.nd (.nd (.nd (.lf 24) (.lf 25)) (.nd (.lf 26) (.lf 27))) (.nd (.nd (.lf 28) (.lf 29)) (.nd (.lf 30) (.lf 31)))))) (.nd (.nd (.nd (.nd (.nd (.lf 32) (.lf 33)) (.nd (.lf 34) (.lf 35))) (.nd (.nd (.lf 36) (.lf 37)) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_2 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 19) (.lf 22)) (.nd (.lf 24) (.lf 25))) (.nd (.lf 25) (.nd (.lf 25) (.lf 26)))) (.nd (.nd (.nd (.lf 25) (.lf 26)) (.lf 25)) (.nd (.lf 25) (.nd (.lf 25) (.lf 26))))) (.nd (.lf 25) (.nd (.lf 25) (.nd (.nd (.lf 25) (.lf 29)) (.nd (.lf 30) (.lf 31)))))) (.nd (.nd (.nd (.nd (.lf 31) (.lf 29)) (.nd (.lf 31) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_3 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 27) (.lf 28)) (.lf 29)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 29))) (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 29))))) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 29))) (.lf 30)) (.lf 30))) (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.lf 30)) (.nd (.nd (.lf 29) (.lf 30)) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_4 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 31) (.lf 29)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 29))) (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 29))))) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 29))) (.lf 30)) (.lf 30))) (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.lf 30)) (.nd (.nd (.lf 29) (.lf 30)) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_5 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.lf 30)) (.lf 30)) (.lf 30)) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_6 : PTree64 Nat := (.nd (.lf 30) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_7 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 24)) (.nd (.lf 29) (.lf 30))) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_8 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 32) (.lf 33)) (.lf 29)) (.nd (.lf 29) (.nd (.lf 29) (.lf 34)))) (.nd (.nd (.nd (.lf 29) (.lf 34)) (.lf 29)) (.nd (.lf 29) (.nd (.lf 29) (.lf 34))))) (.nd (.lf 29) (.nd (.lf 29) (.nd (.lf 29) (.nd (.lf 30) (.lf 29)))))) (.nd (.nd (.nd (.lf 29) (.nd (.lf 29) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_9 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 15) (.lf 26)) (.lf 29)) (.nd (.lf 30) (.nd (.lf 30) (.lf 34)))) (.nd (.nd (.nd (.lf 30) (.lf 35)) (.nd (.lf 30) (.lf 29))) (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 35))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_10 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 36) (.lf 37)) (.lf 29)) (.nd (.lf 29) (.nd (.lf 29) (.lf 35)))) (.nd (.nd (.nd (.lf 29) (.lf 35)) (.lf 29)) (.nd (.lf 29) (.nd (.lf 29) (.lf 35))))) (.nd (.lf 29) (.nd (.lf 29) (.nd (.lf 29) (.nd (.lf 30) (.lf 29)))))) (.nd (.nd (.nd (.lf 29) (.nd (.lf 29) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_11 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 19) (.lf 25)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_12 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 37) (.lf 31)) (.lf 29)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 29))) (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 29))))) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 29))) (.lf 30)) (.lf 30))) (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.lf 30)) (.nd (.nd (.lf 29) (.lf 30)) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_13 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 27) (.lf 25)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_14 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 31) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_15 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 15) (.lf 25)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_16 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 32) (.lf 31)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_17 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 36) (.lf 31)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_18 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 37) (.lf 31)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_19 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 24) (.lf 29)) (.lf 30)) (.lf 30)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.nd (.nd (.lf 30) (.lf 38)) (.lf 38))))) (.lf 38))
def dsnRow_20 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 29) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 29))) (.nd (.nd (.lf 30) (.lf 29)) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_21 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.lf 38)) (.lf 38)))
def dsnRow_22 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 35)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.nd (.nd (.lf 38) (.nd (.lf 38) (.lf 30))) (.lf 38)))) (.lf 38))
def dsnRow_23 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29)))) (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.lf 29))))) (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.nd (.nd (.lf 38) (.nd (.lf 38) (.lf 30))) (.lf 38)))) (.lf 38))
def dsnRow_24 : PTree64 Nat := (.nd (.nd (.lf 30) (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.nd (.nd (.lf 38) (.nd (.lf 38) (.lf 30))) (.lf 38)))) (.lf 38))
def dsnRow_25 : PTree64 Nat := (.nd (.nd (.lf 30) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.nd (.lf 30) (.lf 38))) (.lf 38))) (.lf 38))
def dsnRow_26 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.lf 30)) (.lf 30)) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.nd (.lf 30) (.lf 38))) (.lf 38))) (.lf 38))
def dsnRow_27 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.lf 30)) (.lf 30)) (.lf 30)) (.nd (.lf 30) (.nd (.lf 30) (.nd (.nd (.lf 30) (.lf 38)) (.lf 38))))) (.lf 38))
def dsnRow_28 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 30) (.lf 29)) (.lf 30)) (.lf 30)) (.lf 30)) (.nd (.nd (.nd (.lf 30) (.nd (.lf 30) (.lf 38))) (.nd (.lf 30) (.lf 38))) (.lf 38))) (.lf 38))
def dsnRow_29 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 30) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38))
def dsnRow_30 : PTree64 Nat := (.lf 38)
def dsnRow_31 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 30) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38))
def dsnRow_32 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 26) (.lf 30)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38))
def dsnRow_33 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 34) (.lf 30)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38))
def dsnRow_34 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 35) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38))
def dsnRow_35 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38))
def dsnRow_36 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 25) (.lf 30)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38))
def dsnRow_37 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 30)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38)) (.lf 38))
def dsnRow_38 : PTree64 Nat := (.lf 38)
def dsnTree : PTree64 (PTree64 Nat) := (.nd (.nd (.nd (.nd (.nd (.nd (.lf dsnRow_0) (.lf dsnRow_1)) (.nd (.lf dsnRow_2) (.lf dsnRow_3))) (.nd (.nd (.lf dsnRow_4) (.lf dsnRow_5)) (.nd (.lf dsnRow_6) (.lf dsnRow_7)))) (.nd (.nd (.nd (.lf dsnRow_8) (.lf dsnRow_9)) (.nd (.lf dsnRow_10) (.lf dsnRow_11))) (.nd (.nd (.lf dsnRow_12) (.lf dsnRow_13)) (.nd (.lf dsnRow_14) (.lf dsnRow_15))))) (.nd (.nd (.nd (.nd (.lf dsnRow_16) (.lf dsnRow_17)) (.nd (.lf dsnRow_18) (.lf dsnRow_19))) (.nd (.nd (.lf dsnRow_20) (.lf dsnRow_21)) (.nd (.lf dsnRow_22) (.lf dsnRow_23)))) (.nd (.nd (.nd (.lf dsnRow_24) (.lf dsnRow_25)) (.nd (.lf dsnRow_26) (.lf dsnRow_27))) (.nd (.nd (.lf dsnRow_28) (.lf dsnRow_29)) (.nd (.lf dsnRow_30) (.lf dsnRow_31)))))) (.nd (.nd (.nd (.nd (.nd (.lf dsnRow_32) (.lf dsnRow_33)) (.nd (.lf dsnRow_34) (.lf dsnRow_35))) (.nd (.nd (.lf dsnRow_36) (.lf dsnRow_37)) (.lf dsnRow_38))) (.lf (.lf 38))) (.lf (.lf 38))))
def dsnIdx (i j : Nat) : Nat := (dsnTree.lookup i).lookup j
def isS2SNTree : PTree64 Bool := (.nd (.nd (.nd (.nd (.lf false) (.nd (.nd (.lf false) (.lf true)) (.lf true))) (.nd (.nd (.nd (.lf false) (.lf true)) (.nd (.lf false) (.lf true))) (.nd (.nd (.lf false) (.lf true)) (.lf true)))) (.nd (.nd (.lf true) (.nd (.nd (.lf false) (.lf true)) (.lf true))) (.lf true))) (.nd (.nd (.nd (.lf true) (.nd (.lf true) (.lf false))) (.lf false)) (.lf false)))
def isS2StateSN (q : StateSN) : Bool := isS2SNTree.lookup (snIdx q)
def msSNRow_0 : PTree64 Nat := (.lf 0)
def msSNRow_1 : PTree64 Nat := (.lf 0)
def msSNRow_2 : PTree64 Nat := (.lf 0)
def msSNRow_3 : PTree64 Nat := (.lf 0)
def msSNRow_4 : PTree64 Nat := (.lf 0)
def msSNRow_5 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_6 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_7 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_8 : PTree64 Nat := (.lf 0)
def msSNRow_9 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_10 : PTree64 Nat := (.lf 0)
def msSNRow_11 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_12 : PTree64 Nat := (.lf 0)
def msSNRow_13 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_14 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_15 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_16 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_17 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_18 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_19 : PTree64 Nat := (.nd (.nd (.lf 2) (.nd (.nd (.nd (.lf 2) (.nd (.lf 2) (.lf 3))) (.nd (.lf 2) (.lf 3))) (.nd (.nd (.nd (.lf 3) (.lf 4)) (.nd (.lf 3) (.lf 4))) (.nd (.nd (.lf 4) (.lf 0)) (.lf 0))))) (.lf 0))
def msSNRow_20 : PTree64 Nat := (.lf 0)
def msSNRow_21 : PTree64 Nat := (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)))
def msSNRow_22 : PTree64 Nat := (.nd (.nd (.lf 2) (.nd (.nd (.nd (.lf 2) (.nd (.lf 2) (.lf 4))) (.nd (.lf 2) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5))) (.lf 0)))) (.lf 0))
def msSNRow_23 : PTree64 Nat := (.nd (.nd (.lf 2) (.nd (.nd (.nd (.lf 2) (.nd (.lf 2) (.lf 4))) (.nd (.lf 2) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5))) (.lf 0)))) (.lf 0))
def msSNRow_24 : PTree64 Nat := (.nd (.nd (.lf 2) (.nd (.nd (.nd (.lf 2) (.nd (.lf 2) (.lf 5))) (.nd (.lf 2) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5))) (.lf 0)))) (.lf 0))
def msSNRow_25 : PTree64 Nat := (.nd (.nd (.lf 3) (.nd (.nd (.nd (.lf 3) (.nd (.lf 3) (.lf 0))) (.nd (.lf 3) (.lf 0))) (.lf 0))) (.lf 0))
def msSNRow_26 : PTree64 Nat := (.nd (.nd (.lf 2) (.nd (.nd (.nd (.lf 2) (.nd (.lf 2) (.lf 0))) (.nd (.lf 2) (.lf 0))) (.lf 0))) (.lf 0))
def msSNRow_27 : PTree64 Nat := (.nd (.nd (.lf 3) (.nd (.lf 3) (.nd (.nd (.nd (.lf 3) (.lf 4)) (.nd (.lf 3) (.lf 4))) (.nd (.nd (.lf 4) (.lf 0)) (.lf 0))))) (.lf 0))
def msSNRow_28 : PTree64 Nat := (.nd (.nd (.lf 3) (.nd (.nd (.nd (.lf 3) (.nd (.lf 3) (.lf 0))) (.nd (.lf 3) (.lf 0))) (.lf 0))) (.lf 0))
def msSNRow_29 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 6) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def msSNRow_30 : PTree64 Nat := (.lf 0)
def msSNRow_31 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 4) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def msSNRow_32 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 3)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def msSNRow_33 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 3)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def msSNRow_34 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def msSNRow_35 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def msSNRow_36 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 4)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def msSNRow_37 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 3) (.lf 4)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def msSNRow_38 : PTree64 Nat := (.lf 0)
def msSNTree : PTree64 (PTree64 Nat) := (.nd (.nd (.nd (.nd (.nd (.nd (.lf msSNRow_0) (.lf msSNRow_1)) (.nd (.lf msSNRow_2) (.lf msSNRow_3))) (.nd (.nd (.lf msSNRow_4) (.lf msSNRow_5)) (.nd (.lf msSNRow_6) (.lf msSNRow_7)))) (.nd (.nd (.nd (.lf msSNRow_8) (.lf msSNRow_9)) (.nd (.lf msSNRow_10) (.lf msSNRow_11))) (.nd (.nd (.lf msSNRow_12) (.lf msSNRow_13)) (.nd (.lf msSNRow_14) (.lf msSNRow_15))))) (.nd (.nd (.nd (.nd (.lf msSNRow_16) (.lf msSNRow_17)) (.nd (.lf msSNRow_18) (.lf msSNRow_19))) (.nd (.nd (.lf msSNRow_20) (.lf msSNRow_21)) (.nd (.lf msSNRow_22) (.lf msSNRow_23)))) (.nd (.nd (.nd (.lf msSNRow_24) (.lf msSNRow_25)) (.nd (.lf msSNRow_26) (.lf msSNRow_27))) (.nd (.nd (.lf msSNRow_28) (.lf msSNRow_29)) (.nd (.lf msSNRow_30) (.lf msSNRow_31)))))) (.nd (.nd (.nd (.nd (.nd (.lf msSNRow_32) (.lf msSNRow_33)) (.nd (.lf msSNRow_34) (.lf msSNRow_35))) (.nd (.nd (.lf msSNRow_36) (.lf msSNRow_37)) (.lf msSNRow_38))) (.lf (.lf 0))) (.lf (.lf 0))))
def msSNIdx (i j : Nat) : Nat := (msSNTree.lookup i).lookup j
def maxSubRankSN (a b : StateSN) : Nat := msSNIdx (snIdx a) (snIdx b)
def sn1OvrRow_0 : PTree64 Nat := (.lf 0)
def sn1OvrRow_1 : PTree64 Nat := (.lf 0)
def sn1OvrRow_2 : PTree64 Nat := (.lf 0)
def sn1OvrRow_3 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 1) (.lf 0)) (.lf 0))) (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0)))) (.lf 0)) (.lf 0))
def sn1OvrRow_4 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0))))) (.lf 0)) (.lf 0))
def sn1OvrRow_5 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.nd (.lf 1) (.lf 0)))) (.lf 0)) (.lf 0)) (.lf 0))
def sn1OvrRow_6 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0)))) (.lf 0)) (.lf 0)) (.lf 0))
def sn1OvrRow_7 : PTree64 Nat := (.lf 0)
def sn1OvrRow_8 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.lf 0)) (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))) (.lf 0))
def sn1OvrRow_9 : PTree64 Nat := (.lf 0)
def sn1OvrRow_10 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.lf 0)) (.nd (.nd (.nd (.nd (.lf 0) (.lf 1)) (.lf 0)) (.lf 0)) (.lf 0))) (.lf 0))
def sn1OvrRow_11 : PTree64 Nat := (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 1))) (.nd (.nd (.lf 1) (.lf 0)) (.lf 0)))) (.lf 0)) (.lf 0))
def sn1OvrRow_12 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.lf 0)) (.nd (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def sn1OvrRow_13 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 1) (.lf 0)) (.lf 0))) (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0)))) (.lf 0)) (.lf 0))
def sn1OvrRow_14 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0))))) (.lf 0)) (.lf 0))
def sn1OvrRow_15 : PTree64 Nat := (.lf 0)
def sn1OvrRow_16 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.lf 0)) (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))) (.lf 0))
def sn1OvrRow_17 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.lf 0)) (.nd (.nd (.nd (.nd (.lf 0) (.lf 1)) (.lf 0)) (.lf 0)) (.lf 0))) (.lf 0))
def sn1OvrRow_18 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.lf 0)) (.nd (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def sn1OvrRow_19 : PTree64 Nat := (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.nd (.nd (.lf 1) (.lf 0)) (.lf 0))) (.lf 0))) (.lf 0))
def sn1OvrRow_20 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0)))) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.lf 0))) (.lf 0))
def sn1OvrRow_21 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0)))) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0))) (.lf 0))) (.lf 0))
def sn1OvrRow_22 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0)))) (.lf 0)) (.lf 0)) (.lf 0))
def sn1OvrRow_23 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0)))) (.lf 0)) (.lf 0)) (.lf 0))
def sn1OvrRow_24 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0)))) (.lf 0)) (.lf 0)) (.lf 0))
def sn1OvrRow_25 : PTree64 Nat := (.lf 0)
def sn1OvrRow_26 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 0) (.nd (.lf 0) (.nd (.lf 1) (.lf 0)))) (.lf 0)) (.lf 0)) (.lf 0))
def sn1OvrRow_27 : PTree64 Nat := (.lf 0)
def sn1OvrRow_28 : PTree64 Nat := (.lf 0)
def sn1OvrRow_29 : PTree64 Nat := (.lf 0)
def sn1OvrRow_30 : PTree64 Nat := (.lf 0)
def sn1OvrRow_31 : PTree64 Nat := (.lf 0)
def sn1OvrRow_32 : PTree64 Nat := (.lf 0)
def sn1OvrRow_33 : PTree64 Nat := (.lf 0)
def sn1OvrRow_34 : PTree64 Nat := (.lf 0)
def sn1OvrRow_35 : PTree64 Nat := (.lf 0)
def sn1OvrRow_36 : PTree64 Nat := (.lf 0)
def sn1OvrRow_37 : PTree64 Nat := (.lf 0)
def sn1OvrRow_38 : PTree64 Nat := (.lf 0)
def sn1OvrTree : PTree64 (PTree64 Nat) := (.nd (.nd (.nd (.nd (.nd (.nd (.lf sn1OvrRow_0) (.lf sn1OvrRow_1)) (.nd (.lf sn1OvrRow_2) (.lf sn1OvrRow_3))) (.nd (.nd (.lf sn1OvrRow_4) (.lf sn1OvrRow_5)) (.nd (.lf sn1OvrRow_6) (.lf sn1OvrRow_7)))) (.nd (.nd (.nd (.lf sn1OvrRow_8) (.lf sn1OvrRow_9)) (.nd (.lf sn1OvrRow_10) (.lf sn1OvrRow_11))) (.nd (.nd (.lf sn1OvrRow_12) (.lf sn1OvrRow_13)) (.nd (.lf sn1OvrRow_14) (.lf sn1OvrRow_15))))) (.nd (.nd (.nd (.nd (.lf sn1OvrRow_16) (.lf sn1OvrRow_17)) (.nd (.lf sn1OvrRow_18) (.lf sn1OvrRow_19))) (.nd (.nd (.lf sn1OvrRow_20) (.lf sn1OvrRow_21)) (.nd (.lf sn1OvrRow_22) (.lf sn1OvrRow_23)))) (.nd (.nd (.nd (.lf sn1OvrRow_24) (.lf sn1OvrRow_25)) (.nd (.lf sn1OvrRow_26) (.lf sn1OvrRow_27))) (.nd (.nd (.lf sn1OvrRow_28) (.lf sn1OvrRow_29)) (.nd (.lf sn1OvrRow_30) (.lf sn1OvrRow_31)))))) (.nd (.nd (.nd (.nd (.nd (.lf sn1OvrRow_32) (.lf sn1OvrRow_33)) (.nd (.lf sn1OvrRow_34) (.lf sn1OvrRow_35))) (.nd (.nd (.lf sn1OvrRow_36) (.lf sn1OvrRow_37)) (.lf sn1OvrRow_38))) (.lf (.lf 0))) (.lf (.lf 0))))
def sn1OvrIdx (i j : Nat) : Nat := (sn1OvrTree.lookup i).lookup j
def trSNIdx (x y z : Nat) : Nat :=
  if Nat.beq x 9 && Nat.beq y 0 && Nat.beq z 1 then 3
  else if Nat.beq x 1 && Nat.beq (sn1OvrIdx y z) 1 then 2
  else msSNIdx (dsnIdx (dsnIdx 0 x) y) z
def tripleRankSN (x y z : StateSN) : Nat := trSNIdx (snIdx x) (snIdx y) (snIdx z)
def evalSN : Term → StateSN | .s => .sn0 | .var _ => .sn0 | .app a b => deltaSN (evalSN a) (evalSN b)

def dsn_s_law_row (x : Nat) : Bool :=
  checkNat2 39 39 (fun y z => Nat.beq (dsnIdx (dsnIdx (dsnIdx 0 x) y) z) (dsnIdx (dsnIdx x z) (dsnIdx y z)))
def sn_ranks_row (x : Nat) : Bool :=
  checkNat2 39 39 (fun y z =>
    (Nat.beq x 38 || Nat.beq y 38 || Nat.ble (trSNIdx x y z) (msSNIdx (dsnIdx (dsnIdx 0 x) y) z)) &&
    (Nat.beq (dsnIdx (dsnIdx (dsnIdx 0 x) y) z) 38 ||
      (Nat.ble 1 (trSNIdx x y z) && Nat.ble (msSNIdx x z) (trSNIdx x y z) && Nat.ble (msSNIdx y z) (trSNIdx x y z) &&
       (!isS2SNTree.lookup x || Nat.ble (msSNIdx (dsnIdx x z) (dsnIdx y z) + 1) (trSNIdx x y z)))) &&
    (Nat.beq (dsnIdx (dsnIdx (dsnIdx 0 (dsnIdx 0 x)) y) z) 38 || Nat.ble (trSNIdx x z (dsnIdx y z) + 1) (trSNIdx (dsnIdx 0 x) y z)))

inductive StateHN where
  | hn0 | hn1 | hn2 | hn3 | hn4 | hn5 | hn6 | hn7 | hn8 | hn9 | hn10 | hn11 | hn12 | hn13 | hn14 | hn15 | hn16 | hn17 | hn18 | hn19 | hn20 | hn21 | hn22 | hn23 | hn24 | hn25 | hn26 | hn27 | hn28 | hn29 | hn30 | hn31 | hn32 | hn33 | hn34
def hnIdx : StateHN → Nat | .hn0 => 0 | .hn1 => 1 | .hn2 => 2 | .hn3 => 3 | .hn4 => 4 | .hn5 => 5 | .hn6 => 6 | .hn7 => 7 | .hn8 => 8 | .hn9 => 9 | .hn10 => 10 | .hn11 => 11 | .hn12 => 12 | .hn13 => 13 | .hn14 => 14 | .hn15 => 15 | .hn16 => 16 | .hn17 => 17 | .hn18 => 18 | .hn19 => 19 | .hn20 => 20 | .hn21 => 21 | .hn22 => 22 | .hn23 => 23 | .hn24 => 24 | .hn25 => 25 | .hn26 => 26 | .hn27 => 27 | .hn28 => 28 | .hn29 => 29 | .hn30 => 30 | .hn31 => 31 | .hn32 => 32 | .hn33 => 33 | .hn34 => 34
def ofHnIdxTree : PTree64 StateHN := (.nd (.nd (.nd (.nd (.nd (.nd (.lf .hn0) (.lf .hn1)) (.nd (.lf .hn2) (.lf .hn3))) (.nd (.nd (.lf .hn4) (.lf .hn5)) (.nd (.lf .hn6) (.lf .hn7)))) (.nd (.nd (.nd (.lf .hn8) (.lf .hn9)) (.nd (.lf .hn10) (.lf .hn11))) (.nd (.nd (.lf .hn12) (.lf .hn13)) (.nd (.lf .hn14) (.lf .hn15))))) (.nd (.nd (.nd (.nd (.lf .hn16) (.lf .hn17)) (.nd (.lf .hn18) (.lf .hn19))) (.nd (.nd (.lf .hn20) (.lf .hn21)) (.nd (.lf .hn22) (.lf .hn23)))) (.nd (.nd (.nd (.lf .hn24) (.lf .hn25)) (.nd (.lf .hn26) (.lf .hn27))) (.nd (.nd (.lf .hn28) (.lf .hn29)) (.nd (.lf .hn30) (.lf .hn31)))))) (.nd (.nd (.nd (.nd (.nd (.lf .hn32) (.lf .hn33)) (.lf .hn34)) (.lf .hn34)) (.lf .hn34)) (.lf .hn34)))
def ofHnIdx (n : Nat) : StateHN := ofHnIdxTree.lookup n
def beq_StateHN (a b : StateHN) : Bool := Nat.beq (hnIdx a) (hnIdx b)
def deltaHN : StateHN → StateHN → StateHN
  | .hn0, y => match y with | .hn0 => .hn1 | .hn1 => .hn2 | .hn2 => .hn3 | .hn3 => .hn4 | .hn4 => .hn5 | .hn5 => .hn5 | .hn6 => .hn7 | .hn7 => .hn8 | .hn8 => .hn9 | .hn11 => .hn12 | .hn12 => .hn8 | .hn13 => .hn12 | .hn14 => .hn15 | .hn15 => .hn8 | .hn16 => .hn8 | .hn17 => .hn9 | .hn18 => .hn19 | .hn19 => .hn9 | .hn20 => .hn21 | .hn21 => .hn9 | .hn26 => .hn27 | .hn28 => .hn9 | .hn29 => .hn9 | .hn30 => .hn9 | .hn31 => .hn27 | .hn32 => .hn9 | _ => .hn10
  | .hn1, y => match y with | .hn0 => .hn6 | .hn1 => .hn11 | _ => .hn13
  | .hn2, y => match y with | .hn0 => .hn14 | .hn1 => .hn16 | .hn2 => .hn8 | .hn3 => .hn9 | .hn6 => .hn17 | .hn7 => .hn9 | .hn11 => .hn17 | .hn12 => .hn9 | .hn13 => .hn17 | _ => .hn10
  | .hn3, y => match y with | .hn0 => .hn18 | _ => .hn20
  | .hn4, y => match y with | .hn0 => .hn8 | _ => .hn10
  | .hn5, _ => .hn10
  | .hn6, y => match y with | .hn0 => .hn11 | .hn1 => .hn8 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn22 | .hn11 => .hn22 | .hn13 => .hn22 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn7, y => match y with | .hn0 => .hn26 | .hn1 => .hn28 | .hn2 => .hn29 | .hn3 => .hn22 | .hn6 => .hn30 | .hn7 => .hn22 | .hn11 => .hn30 | .hn12 => .hn22 | .hn13 => .hn30 | _ => .hn24
  | .hn8, y => match y with | .hn0 => .hn24 | _ => .hn23
  | .hn9, y => match y with | .hn0 => .hn25 | _ => .hn23
  | .hn10, _ => .hn23
  | .hn11, y => match y with | .hn0 => .hn13 | .hn1 => .hn17 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn30 | .hn11 => .hn29 | .hn13 => .hn29 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn12, y => match y with | .hn0 => .hn31 | .hn1 => .hn29 | .hn2 => .hn29 | .hn3 => .hn22 | .hn6 => .hn29 | .hn7 => .hn22 | .hn11 => .hn29 | .hn12 => .hn22 | .hn13 => .hn29 | _ => .hn24
  | .hn13, y => match y with | .hn0 => .hn13 | .hn1 => .hn10 | .hn2 => .hn20 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | .hn6 => .hn24 | .hn11 => .hn24 | .hn13 => .hn24 | .hn14 => .hn24 | .hn18 => .hn25 | .hn26 => .hn25 | .hn31 => .hn25 | _ => .hn23
  | .hn14, y => match y with | .hn0 => .hn8 | .hn1 => .hn20 | .hn2 => .hn10 | .hn3 => .hn10 | .hn4 => .hn10 | .hn5 => .hn10 | _ => .hn23
  | .hn15, _ => .hn24
  | .hn16, y => match y with | .hn0 => .hn22 | .hn1 => .hn29 | _ => .hn24
  | .hn17, y => match y with | .hn0 => .hn22 | _ => .hn23
  | .hn18, y => match y with | .hn0 => .hn20 | .hn1 => .hn24 | _ => .hn23
  | .hn19, y => match y with | .hn0 => .hn32 | _ => .hn25
  | .hn20, y => match y with | .hn1 => .hn24 | _ => .hn23
  | .hn21, y => match y with | .hn0 => .hn33 | _ => .hn23
  | .hn22, y => match y with | .hn0 => .hn25 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn23, _ => .hn34
  | .hn24, y => match y with | .hn0 => .hn23 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn25, y => match y with | .hn0 => .hn23 | _ => .hn34
  | .hn26, y => match y with | .hn0 => .hn17 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn27, _ => .hn25
  | .hn28, y => match y with | .hn0 => .hn30 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn29, y => match y with | .hn0 => .hn24 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn30, y => match y with | .hn0 => .hn29 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn31, y => match y with | .hn0 => .hn10 | .hn1 => .hn23 | .hn2 => .hn23 | .hn3 => .hn23 | .hn4 => .hn23 | .hn5 => .hn23 | _ => .hn34
  | .hn32, y => match y with | .hn0 => .hn24 | .hn1 => .hn23 | _ => .hn34
  | .hn33, y => match y with | .hn1 => .hn23 | _ => .hn34
  | .hn34, _ => .hn34
def dhnRow_0 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 1) (.lf 2)) (.nd (.lf 3) (.lf 4))) (.nd (.lf 5) (.nd (.lf 7) (.lf 8)))) (.nd (.nd (.nd (.lf 9) (.lf 10)) (.nd (.lf 10) (.lf 12))) (.nd (.nd (.lf 8) (.lf 12)) (.nd (.lf 15) (.lf 8))))) (.nd (.nd (.nd (.nd (.lf 8) (.lf 9)) (.nd (.lf 19) (.lf 9))) (.nd (.nd (.lf 21) (.lf 9)) (.lf 10))) (.nd (.nd (.lf 10) (.nd (.lf 27) (.lf 10))) (.nd (.lf 9) (.nd (.lf 9) (.lf 27)))))) (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 10)) (.lf 10)) (.lf 34)) (.lf 34)) (.lf 34)))
def dhnRow_1 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 6) (.lf 11)) (.lf 13)) (.lf 13)) (.lf 13)) (.lf 13)) (.lf 13))
def dhnRow_2 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 14) (.lf 16)) (.nd (.lf 8) (.lf 9))) (.nd (.lf 10) (.nd (.lf 17) (.lf 9)))) (.nd (.nd (.lf 10) (.nd (.lf 10) (.lf 17))) (.nd (.nd (.lf 9) (.lf 17)) (.lf 10)))) (.lf 10)) (.lf 10))
def dhnRow_3 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 18) (.lf 20)) (.lf 20)) (.lf 20)) (.lf 20)) (.lf 20)) (.lf 20))
def dhnRow_4 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 10)) (.lf 10)) (.lf 10)) (.lf 10)) (.lf 10)) (.lf 10))
def dhnRow_5 : PTree64 Nat := (.lf 10)
def dhnRow_6 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 11) (.lf 8)) (.nd (.lf 20) (.lf 10))) (.nd (.lf 10) (.nd (.lf 22) (.lf 23)))) (.nd (.nd (.lf 23) (.nd (.lf 23) (.lf 22))) (.nd (.nd (.lf 23) (.lf 22)) (.nd (.lf 24) (.lf 23))))) (.nd (.nd (.nd (.lf 23) (.nd (.lf 25) (.lf 23))) (.lf 23)) (.nd (.nd (.lf 23) (.nd (.lf 25) (.lf 23))) (.nd (.lf 23) (.nd (.lf 23) (.lf 25)))))) (.lf 23))
def dhnRow_7 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 26) (.lf 28)) (.nd (.lf 29) (.lf 22))) (.nd (.lf 24) (.nd (.lf 30) (.lf 22)))) (.nd (.nd (.lf 24) (.nd (.lf 24) (.lf 30))) (.nd (.nd (.lf 22) (.lf 30)) (.lf 24)))) (.lf 24)) (.lf 24))
def dhnRow_8 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 24) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23))
def dhnRow_9 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 25) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23))
def dhnRow_10 : PTree64 Nat := (.lf 23)
def dhnRow_11 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 13) (.lf 17)) (.nd (.lf 20) (.lf 10))) (.nd (.lf 10) (.nd (.lf 30) (.lf 23)))) (.nd (.nd (.lf 23) (.nd (.lf 23) (.lf 29))) (.nd (.nd (.lf 23) (.lf 29)) (.nd (.lf 24) (.lf 23))))) (.nd (.nd (.nd (.lf 23) (.nd (.lf 25) (.lf 23))) (.lf 23)) (.nd (.nd (.lf 23) (.nd (.lf 25) (.lf 23))) (.nd (.lf 23) (.nd (.lf 23) (.lf 25)))))) (.lf 23))
def dhnRow_12 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 31) (.lf 29)) (.nd (.lf 29) (.lf 22))) (.nd (.lf 24) (.nd (.lf 29) (.lf 22)))) (.nd (.nd (.lf 24) (.nd (.lf 24) (.lf 29))) (.nd (.nd (.lf 22) (.lf 29)) (.lf 24)))) (.lf 24)) (.lf 24))
def dhnRow_13 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 13) (.lf 10)) (.nd (.lf 20) (.lf 10))) (.nd (.lf 10) (.nd (.lf 24) (.lf 23)))) (.nd (.nd (.lf 23) (.nd (.lf 23) (.lf 24))) (.nd (.nd (.lf 23) (.lf 24)) (.nd (.lf 24) (.lf 23))))) (.nd (.nd (.nd (.lf 23) (.nd (.lf 25) (.lf 23))) (.lf 23)) (.nd (.nd (.lf 23) (.nd (.lf 25) (.lf 23))) (.nd (.lf 23) (.nd (.lf 23) (.lf 25)))))) (.lf 23))
def dhnRow_14 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 20)) (.lf 10)) (.nd (.lf 10) (.lf 23))) (.lf 23)) (.lf 23)) (.lf 23))
def dhnRow_15 : PTree64 Nat := (.lf 24)
def dhnRow_16 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 22) (.lf 29)) (.lf 24)) (.lf 24)) (.lf 24)) (.lf 24)) (.lf 24))
def dhnRow_17 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 22) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23))
def dhnRow_18 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 20) (.lf 24)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23))
def dhnRow_19 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 32) (.lf 25)) (.lf 25)) (.lf 25)) (.lf 25)) (.lf 25)) (.lf 25))
def dhnRow_20 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 23) (.lf 24)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23))
def dhnRow_21 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 33) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23)) (.lf 23))
def dhnRow_22 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 25) (.lf 23)) (.lf 23)) (.nd (.lf 23) (.lf 34))) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_23 : PTree64 Nat := (.lf 34)
def dhnRow_24 : PTree64 Nat := (.nd (.nd (.nd (.nd (.lf 23) (.nd (.lf 23) (.lf 34))) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_25 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 23) (.lf 34)) (.lf 34)) (.lf 34)) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_26 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 17) (.lf 23)) (.lf 23)) (.nd (.lf 23) (.lf 34))) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_27 : PTree64 Nat := (.lf 25)
def dhnRow_28 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 30) (.lf 23)) (.lf 23)) (.nd (.lf 23) (.lf 34))) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_29 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 24) (.lf 23)) (.lf 23)) (.nd (.lf 23) (.lf 34))) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_30 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 29) (.lf 23)) (.lf 23)) (.nd (.lf 23) (.lf 34))) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_31 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 10) (.lf 23)) (.lf 23)) (.nd (.lf 23) (.lf 34))) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_32 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 24) (.lf 23)) (.lf 34)) (.lf 34)) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_33 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 34) (.lf 23)) (.lf 34)) (.lf 34)) (.lf 34)) (.lf 34)) (.lf 34))
def dhnRow_34 : PTree64 Nat := (.lf 34)
def dhnTree : PTree64 (PTree64 Nat) := (.nd (.nd (.nd (.nd (.nd (.nd (.lf dhnRow_0) (.lf dhnRow_1)) (.nd (.lf dhnRow_2) (.lf dhnRow_3))) (.nd (.nd (.lf dhnRow_4) (.lf dhnRow_5)) (.nd (.lf dhnRow_6) (.lf dhnRow_7)))) (.nd (.nd (.nd (.lf dhnRow_8) (.lf dhnRow_9)) (.nd (.lf dhnRow_10) (.lf dhnRow_11))) (.nd (.nd (.lf dhnRow_12) (.lf dhnRow_13)) (.nd (.lf dhnRow_14) (.lf dhnRow_15))))) (.nd (.nd (.nd (.nd (.lf dhnRow_16) (.lf dhnRow_17)) (.nd (.lf dhnRow_18) (.lf dhnRow_19))) (.nd (.nd (.lf dhnRow_20) (.lf dhnRow_21)) (.nd (.lf dhnRow_22) (.lf dhnRow_23)))) (.nd (.nd (.nd (.lf dhnRow_24) (.lf dhnRow_25)) (.nd (.lf dhnRow_26) (.lf dhnRow_27))) (.nd (.nd (.lf dhnRow_28) (.lf dhnRow_29)) (.nd (.lf dhnRow_30) (.lf dhnRow_31)))))) (.nd (.nd (.nd (.nd (.nd (.lf dhnRow_32) (.lf dhnRow_33)) (.lf dhnRow_34)) (.lf (.lf 34))) (.lf (.lf 34))) (.lf (.lf 34))))
def dhnIdx (i j : Nat) : Nat := (dhnTree.lookup i).lookup j
def evalHN : Term → StateHN | .s => .hn0 | .var _ => .hn0 | .app a b => deltaHN (evalHN a) (evalHN b)
def hnA : StateHN → StateHN → Nat
  | .hn0, y => match y with | .hn9 => 0 | .hn10 => 0 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn1, y => match y with | .hn0 => 2 | .hn1 => 2 | .hn2 => 1 | .hn6 => 1 | .hn7 => 1 | .hn11 => 1 | _ => 0
  | .hn2, y => match y with | .hn0 => 2 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn3, y => match y with | .hn0 => 4 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 2 | .hn11 => 1 | .hn13 => 1 | .hn18 => 1 | _ => 0
  | .hn4, y => match y with | .hn0 => 6 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | .hn28 => 1 | _ => 0
  | .hn5, y => match y with | .hn0 => 15 | .hn1 => 7 | .hn3 => 2 | .hn6 => 4 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn6, y => match y with | .hn0 => 3 | .hn1 => 2 | .hn2 => 2 | .hn6 => 2 | .hn9 => 0 | .hn10 => 0 | .hn11 => 2 | .hn13 => 2 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn7, y => match y with | .hn0 => 5 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 1 | .hn12 => 1 | .hn13 => 1 | .hn14 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn8, y => match y with | .hn0 => 12 | .hn1 => 6 | .hn2 => 2 | .hn3 => 2 | .hn6 => 5 | .hn7 => 1 | .hn11 => 3 | .hn13 => 2 | .hn18 => 2 | _ => 0
  | .hn9, y => match y with | .hn0 => 16 | .hn1 => 6 | .hn2 => 2 | .hn3 => 1 | .hn6 => 4 | .hn7 => 1 | .hn11 => 3 | .hn13 => 2 | .hn18 => 1 | _ => 0
  | .hn10, y => match y with | .hn0 => 30 | .hn1 => 15 | .hn2 => 3 | .hn3 => 2 | .hn6 => 7 | .hn7 => 3 | .hn11 => 4 | .hn13 => 2 | .hn18 => 1 | .hn28 => 1 | _ => 0
  | .hn11, y => match y with | .hn0 => 3 | .hn1 => 5 | .hn2 => 2 | .hn6 => 2 | .hn7 => 3 | .hn9 => 0 | .hn10 => 0 | .hn11 => 3 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn12, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn2 => 1 | .hn3 => 1 | .hn4 => 1 | .hn6 => 2 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn13, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn6 => 4 | .hn9 => 0 | .hn10 => 0 | .hn11 => 2 | .hn13 => 2 | .hn22 => 0 | .hn23 => 0 | .hn24 => 0 | .hn25 => 0 | .hn27 => 0 | .hn33 => 0 | .hn34 => 0 | _ => 1
  | .hn14, y => match y with | .hn0 => 4 | .hn1 => 4 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | .hn6 => 2 | .hn7 => 2 | .hn11 => 2 | .hn12 => 1 | .hn13 => 1 | .hn14 => 1 | .hn15 => 1 | .hn16 => 1 | .hn18 => 1 | .hn20 => 1 | _ => 0
  | .hn15, y => match y with | .hn0 => 6 | .hn1 => 5 | .hn2 => 1 | .hn3 => 2 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn16, y => match y with | .hn0 => 6 | .hn1 => 8 | .hn2 => 3 | .hn6 => 3 | .hn7 => 3 | .hn11 => 3 | _ => 0
  | .hn17, y => match y with | .hn0 => 10 | .hn1 => 7 | .hn2 => 3 | .hn6 => 3 | .hn7 => 1 | .hn11 => 4 | .hn13 => 1 | _ => 0
  | .hn18, y => match y with | .hn0 => 6 | .hn1 => 6 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn19, y => match y with | .hn0 => 9 | .hn1 => 3 | .hn2 => 1 | .hn3 => 1 | .hn6 => 3 | .hn7 => 1 | .hn11 => 2 | .hn13 => 2 | .hn28 => 1 | _ => 0
  | .hn20, y => match y with | .hn0 => 8 | .hn1 => 9 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn6 => 3 | .hn7 => 3 | .hn11 => 3 | .hn12 => 1 | .hn13 => 2 | .hn14 => 1 | .hn16 => 1 | .hn18 => 1 | .hn19 => 1 | .hn26 => 1 | .hn28 => 1 | .hn30 => 1 | _ => 0
  | .hn21, y => match y with | .hn0 => 7 | _ => 0
  | .hn22, y => match y with | .hn0 => 9 | .hn1 => 7 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn23, _ => 0
  | .hn24, y => match y with | .hn0 => 18 | .hn1 => 12 | .hn2 => 7 | .hn3 => 4 | .hn4 => 2 | .hn5 => 1 | _ => 0
  | .hn25, y => match y with | .hn0 => 27 | _ => 0
  | .hn26, y => match y with | .hn0 => 8 | .hn1 => 4 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn27, y => match y with | .hn0 => 15 | .hn1 => 7 | .hn3 => 1 | .hn6 => 4 | .hn11 => 2 | .hn13 => 2 | _ => 0
  | .hn28, y => match y with | .hn0 => 7 | .hn1 => 8 | .hn2 => 4 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn29, y => match y with | .hn0 => 12 | .hn1 => 13 | .hn2 => 4 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn30, y => match y with | .hn0 => 12 | .hn1 => 2 | .hn2 => 2 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn31, y => match y with | .hn0 => 8 | .hn1 => 8 | .hn2 => 3 | .hn3 => 1 | .hn4 => 1 | .hn5 => 1 | _ => 0
  | .hn32, y => match y with | .hn0 => 15 | .hn1 => 13 | _ => 0
  | .hn33, y => match y with | .hn1 => 16 | _ => 0
  | .hn34, _ => 0
def hnaRow_0 : PTree64 Nat := (.nd (.nd (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 0) (.lf 1))) (.lf 1))) (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 1)))) (.nd (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaRow_1 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 2) (.nd (.lf 1) (.lf 0))) (.nd (.lf 0) (.lf 1))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 1))) (.lf 0))) (.lf 0)) (.lf 0))
def hnaRow_2 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 3)) (.lf 1)) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 2) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 1) (.lf 2)) (.nd (.lf 1) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 1)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 1) (.lf 0)))))) (.lf 0))
def hnaRow_3 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 4) (.lf 3)) (.lf 1)) (.nd (.lf 0) (.nd (.lf 2) (.lf 0)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 1))) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaRow_4 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 6) (.lf 3)) (.lf 1)) (.nd (.lf 0) (.nd (.lf 2) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 0) (.lf 2)) (.lf 0)))) (.nd (.lf 0) (.nd (.lf 0) (.nd (.nd (.lf 1) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaRow_5 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 15) (.lf 7)) (.nd (.lf 0) (.lf 2))) (.nd (.lf 0) (.nd (.lf 4) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 0) (.lf 2)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaRow_6 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 3) (.lf 2)) (.nd (.lf 2) (.lf 1))) (.nd (.lf 1) (.nd (.lf 2) (.lf 1)))) (.nd (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 1) (.lf 2)) (.lf 1)))) (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 1)))) (.nd (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaRow_7 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 5) (.lf 3)) (.lf 1)) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 3) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 1))) (.nd (.lf 1) (.nd (.lf 1) (.lf 0))))) (.nd (.nd (.nd (.lf 0) (.lf 1)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 1) (.lf 0)))))) (.lf 0))
def hnaRow_8 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 12) (.lf 6)) (.lf 2)) (.nd (.lf 0) (.nd (.lf 5) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 3))) (.nd (.nd (.lf 0) (.lf 2)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 2) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaRow_9 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 16) (.lf 6)) (.nd (.lf 2) (.lf 1))) (.nd (.lf 0) (.nd (.lf 4) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 3))) (.nd (.nd (.lf 0) (.lf 2)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaRow_10 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 30) (.lf 15)) (.nd (.lf 3) (.lf 2))) (.nd (.lf 0) (.nd (.lf 7) (.lf 3)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 4))) (.nd (.nd (.lf 0) (.lf 2)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.nd (.lf 0) (.nd (.nd (.lf 1) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaRow_11 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 3) (.lf 5)) (.nd (.lf 2) (.lf 1))) (.nd (.lf 1) (.nd (.lf 2) (.lf 3)))) (.nd (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 0) (.lf 3))) (.lf 1))) (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 1)))) (.nd (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaRow_12 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 4) (.lf 1)) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 2) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 1) (.lf 2)) (.nd (.lf 1) (.lf 0))))) (.nd (.nd (.nd (.lf 0) (.lf 1)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 1) (.lf 0)))))) (.lf 0))
def hnaRow_13 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 4) (.lf 1)) (.nd (.lf 1) (.nd (.lf 4) (.lf 1)))) (.nd (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 1) (.lf 2)) (.lf 1)))) (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 1)))) (.nd (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaRow_14 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 4) (.nd (.lf 2) (.lf 1))) (.nd (.lf 1) (.lf 2))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.lf 1))) (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 1) (.lf 0)) (.lf 0))) (.lf 0))) (.lf 0))
def hnaRow_15 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 6) (.lf 5)) (.nd (.lf 1) (.lf 2))) (.nd (.lf 0) (.nd (.lf 3) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 0) (.lf 2)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaRow_16 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 6) (.lf 8)) (.nd (.lf 3) (.lf 0))) (.nd (.lf 0) (.lf 3))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 3))) (.lf 0))) (.lf 0)) (.lf 0))
def hnaRow_17 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 10) (.lf 7)) (.nd (.lf 3) (.lf 0))) (.nd (.lf 0) (.nd (.lf 3) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 4))) (.nd (.nd (.lf 0) (.lf 1)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaRow_18 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 6) (.nd (.lf 3) (.lf 1))) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 3) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 1) (.lf 2)) (.nd (.lf 1) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 1)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 1) (.lf 0)))))) (.lf 0))
def hnaRow_19 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 3)) (.lf 1)) (.nd (.lf 0) (.nd (.lf 3) (.lf 1)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 0) (.lf 2)) (.lf 0)))) (.nd (.lf 0) (.nd (.lf 0) (.nd (.nd (.lf 1) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaRow_20 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 9)) (.nd (.lf 3) (.lf 1))) (.nd (.nd (.lf 1) (.lf 0)) (.lf 3))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 3))) (.nd (.nd (.lf 1) (.lf 2)) (.nd (.lf 1) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 1)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 1) (.lf 0)))))) (.lf 0))
def hnaRow_21 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 7) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_22 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 7)) (.nd (.lf 2) (.lf 1))) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_23 : PTree64 Nat := (.lf 0)
def hnaRow_24 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 18) (.lf 12)) (.nd (.lf 7) (.lf 4))) (.nd (.nd (.lf 2) (.lf 1)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_25 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 27) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_26 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 4)) (.nd (.lf 3) (.lf 1))) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_27 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 15) (.lf 7)) (.nd (.lf 0) (.lf 1))) (.nd (.lf 0) (.nd (.lf 4) (.lf 0)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 2))) (.nd (.nd (.lf 0) (.lf 2)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaRow_28 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 7) (.lf 8)) (.nd (.lf 4) (.lf 1))) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_29 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 12) (.lf 13)) (.nd (.lf 4) (.lf 1))) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_30 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 12) (.lf 2)) (.nd (.lf 2) (.lf 1))) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_31 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 8) (.nd (.lf 3) (.lf 1))) (.nd (.lf 1) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_32 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 15) (.lf 13)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_33 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 0) (.lf 16)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaRow_34 : PTree64 Nat := (.lf 0)
def hnaTree : PTree64 (PTree64 Nat) := (.nd (.nd (.nd (.nd (.nd (.nd (.lf hnaRow_0) (.lf hnaRow_1)) (.nd (.lf hnaRow_2) (.lf hnaRow_3))) (.nd (.nd (.lf hnaRow_4) (.lf hnaRow_5)) (.nd (.lf hnaRow_6) (.lf hnaRow_7)))) (.nd (.nd (.nd (.lf hnaRow_8) (.lf hnaRow_9)) (.nd (.lf hnaRow_10) (.lf hnaRow_11))) (.nd (.nd (.lf hnaRow_12) (.lf hnaRow_13)) (.nd (.lf hnaRow_14) (.lf hnaRow_15))))) (.nd (.nd (.nd (.nd (.lf hnaRow_16) (.lf hnaRow_17)) (.nd (.lf hnaRow_18) (.lf hnaRow_19))) (.nd (.nd (.lf hnaRow_20) (.lf hnaRow_21)) (.nd (.lf hnaRow_22) (.lf hnaRow_23)))) (.nd (.nd (.nd (.lf hnaRow_24) (.lf hnaRow_25)) (.nd (.lf hnaRow_26) (.lf hnaRow_27))) (.nd (.nd (.lf hnaRow_28) (.lf hnaRow_29)) (.nd (.lf hnaRow_30) (.lf hnaRow_31)))))) (.nd (.nd (.nd (.nd (.nd (.lf hnaRow_32) (.lf hnaRow_33)) (.lf hnaRow_34)) (.lf (.lf 0))) (.lf (.lf 0))) (.lf (.lf 0))))
def hnaIdx (i j : Nat) : Nat := (hnaTree.lookup i).lookup j
def hnaLvlRow_0 : PTree64 Nat := (.nd (.nd (.nd (.lf 1) (.nd (.nd (.nd (.lf 1) (.lf 0)) (.nd (.lf 0) (.lf 1))) (.lf 1))) (.nd (.nd (.lf 1) (.nd (.lf 1) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 1) (.lf 0))) (.lf 1)))) (.nd (.nd (.nd (.nd (.nd (.lf 1) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaLvlRow_1 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 7) (.lf 6)) (.nd (.lf 4) (.lf 0))) (.nd (.lf 0) (.nd (.lf 5) (.lf 4)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 4))) (.lf 0))) (.lf 0)) (.lf 0))
def hnaLvlRow_2 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 5) (.lf 7)) (.lf 3)) (.nd (.nd (.lf 3) (.lf 0)) (.nd (.lf 5) (.lf 3)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5))) (.nd (.nd (.lf 3) (.lf 5)) (.nd (.lf 3) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 3) (.lf 0)) (.lf 3)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 3) (.lf 0))) (.nd (.nd (.lf 3) (.lf 0)) (.nd (.lf 3) (.lf 0)))))) (.lf 0))
def hnaLvlRow_3 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 6)) (.lf 4)) (.nd (.lf 0) (.nd (.lf 6) (.lf 0)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 4))) (.nd (.nd (.lf 0) (.lf 4)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 4) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaLvlRow_4 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 7)) (.lf 5)) (.nd (.lf 0) (.nd (.lf 7) (.lf 5)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 7))) (.nd (.nd (.lf 0) (.lf 7)) (.lf 0)))) (.nd (.lf 0) (.nd (.lf 0) (.nd (.nd (.lf 5) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaLvlRow_5 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 12) (.lf 10)) (.nd (.lf 0) (.lf 6))) (.nd (.lf 0) (.nd (.lf 8) (.lf 7)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 6))) (.nd (.nd (.lf 0) (.lf 6)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaLvlRow_6 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 7) (.lf 4)) (.nd (.lf 5) (.lf 2))) (.nd (.lf 2) (.nd (.lf 4) (.lf 2)))) (.nd (.nd (.nd (.lf 2) (.lf 0)) (.nd (.lf 0) (.lf 4))) (.nd (.nd (.lf 2) (.lf 4)) (.lf 2)))) (.nd (.nd (.lf 2) (.nd (.lf 2) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 2) (.lf 0))) (.lf 2)))) (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaLvlRow_7 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 7)) (.lf 3)) (.nd (.nd (.lf 3) (.lf 0)) (.nd (.lf 7) (.lf 3)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 3))) (.nd (.lf 3) (.nd (.lf 3) (.lf 0))))) (.nd (.nd (.nd (.lf 0) (.lf 3)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 3) (.lf 0))) (.nd (.nd (.lf 3) (.lf 0)) (.nd (.lf 3) (.lf 0)))))) (.lf 0))
def hnaLvlRow_8 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 7)) (.lf 5)) (.nd (.lf 0) (.nd (.lf 8) (.lf 5)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 6))) (.nd (.nd (.lf 0) (.lf 5)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 5) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaLvlRow_9 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 10) (.lf 9)) (.lf 5)) (.nd (.lf 0) (.nd (.lf 8) (.lf 5)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 6))) (.nd (.nd (.lf 0) (.lf 6)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 5) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaLvlRow_10 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 13) (.lf 11)) (.nd (.lf 6) (.lf 7))) (.nd (.lf 0) (.nd (.lf 9) (.lf 6)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 7))) (.nd (.nd (.lf 0) (.lf 5)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 5) (.lf 0))) (.lf 0)) (.nd (.lf 0) (.nd (.nd (.lf 6) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaLvlRow_11 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 7)) (.nd (.lf 5) (.lf 2))) (.nd (.lf 2) (.lf 6))) (.nd (.nd (.nd (.lf 2) (.lf 0)) (.nd (.lf 0) (.lf 6))) (.lf 2))) (.nd (.nd (.lf 2) (.nd (.lf 2) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 2) (.lf 0))) (.lf 2)))) (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaLvlRow_12 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 8)) (.lf 3)) (.nd (.nd (.lf 3) (.lf 0)) (.nd (.lf 5) (.lf 3)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5))) (.nd (.nd (.lf 3) (.lf 5)) (.nd (.lf 3) (.lf 0))))) (.nd (.nd (.nd (.lf 0) (.lf 3)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 3) (.lf 0))) (.nd (.nd (.lf 3) (.lf 0)) (.nd (.lf 3) (.lf 0)))))) (.lf 0))
def hnaLvlRow_13 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 2)) (.nd (.lf 2) (.nd (.lf 8) (.lf 2)))) (.nd (.nd (.nd (.lf 2) (.lf 0)) (.nd (.lf 0) (.lf 4))) (.nd (.nd (.lf 2) (.lf 4)) (.lf 2)))) (.nd (.nd (.lf 2) (.nd (.lf 2) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 2) (.lf 0))) (.lf 2)))) (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaLvlRow_14 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 7)) (.nd (.lf 5) (.lf 3))) (.nd (.lf 3) (.nd (.lf 6) (.lf 5)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5))) (.lf 3))) (.nd (.nd (.nd (.nd (.lf 3) (.lf 0)) (.nd (.lf 3) (.lf 0))) (.nd (.nd (.lf 3) (.lf 0)) (.lf 0))) (.lf 0))) (.lf 0))
def hnaLvlRow_15 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 9)) (.nd (.lf 5) (.lf 6))) (.nd (.lf 0) (.nd (.lf 7) (.lf 5)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 6))) (.nd (.nd (.lf 0) (.lf 6)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaLvlRow_16 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 7)) (.nd (.lf 5) (.lf 0))) (.nd (.lf 0) (.nd (.lf 6) (.lf 5)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5))) (.lf 0))) (.lf 0)) (.lf 0))
def hnaLvlRow_17 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 8)) (.nd (.lf 6) (.lf 0))) (.nd (.lf 0) (.nd (.lf 7) (.lf 5)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 7))) (.nd (.nd (.lf 0) (.lf 3)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaLvlRow_18 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 8) (.nd (.lf 6) (.lf 4))) (.nd (.nd (.lf 4) (.lf 0)) (.nd (.lf 6) (.lf 4)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 6))) (.nd (.nd (.lf 4) (.lf 6)) (.nd (.lf 4) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 4) (.lf 0)) (.lf 4)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 4) (.lf 0))) (.nd (.nd (.lf 4) (.lf 0)) (.nd (.lf 4) (.lf 0)))))) (.lf 0))
def hnaLvlRow_19 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 7)) (.lf 5)) (.nd (.lf 0) (.nd (.lf 7) (.lf 5)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 7))) (.nd (.nd (.lf 0) (.lf 7)) (.lf 0)))) (.nd (.lf 0) (.nd (.lf 0) (.nd (.nd (.lf 5) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaLvlRow_20 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 8) (.nd (.lf 6) (.lf 4))) (.nd (.nd (.lf 4) (.lf 0)) (.nd (.lf 6) (.lf 7)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 6))) (.nd (.nd (.lf 4) (.lf 6)) (.nd (.lf 4) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 4) (.lf 0)) (.lf 4)) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 4) (.lf 0))) (.nd (.nd (.lf 4) (.lf 0)) (.nd (.lf 4) (.lf 0)))))) (.lf 0))
def hnaLvlRow_21 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_22 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 9) (.nd (.lf 6) (.lf 3))) (.nd (.lf 3) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_23 : PTree64 Nat := (.lf 0)
def hnaLvlRow_24 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 8)) (.nd (.lf 8) (.lf 7))) (.nd (.nd (.lf 4) (.lf 3)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_25 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 10) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_26 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 6)) (.nd (.lf 6) (.lf 3))) (.nd (.lf 3) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_27 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 12) (.lf 10)) (.nd (.lf 0) (.lf 6))) (.nd (.lf 0) (.nd (.lf 8) (.lf 0)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 6))) (.nd (.nd (.lf 0) (.lf 6)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaLvlRow_28 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 7)) (.nd (.lf 7) (.lf 3))) (.nd (.lf 3) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_29 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 8)) (.nd (.lf 7) (.lf 3))) (.nd (.lf 3) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_30 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 8) (.lf 5)) (.nd (.lf 6) (.lf 3))) (.nd (.lf 3) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_31 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 8)) (.nd (.lf 6) (.lf 3))) (.nd (.lf 3) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_32 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.lf 9) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_33 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 0) (.lf 9)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaLvlRow_34 : PTree64 Nat := (.lf 0)
def hnaLvlTree : PTree64 (PTree64 Nat) := (.nd (.nd (.nd (.nd (.nd (.nd (.lf hnaLvlRow_0) (.lf hnaLvlRow_1)) (.nd (.lf hnaLvlRow_2) (.lf hnaLvlRow_3))) (.nd (.nd (.lf hnaLvlRow_4) (.lf hnaLvlRow_5)) (.nd (.lf hnaLvlRow_6) (.lf hnaLvlRow_7)))) (.nd (.nd (.nd (.lf hnaLvlRow_8) (.lf hnaLvlRow_9)) (.nd (.lf hnaLvlRow_10) (.lf hnaLvlRow_11))) (.nd (.nd (.lf hnaLvlRow_12) (.lf hnaLvlRow_13)) (.nd (.lf hnaLvlRow_14) (.lf hnaLvlRow_15))))) (.nd (.nd (.nd (.nd (.lf hnaLvlRow_16) (.lf hnaLvlRow_17)) (.nd (.lf hnaLvlRow_18) (.lf hnaLvlRow_19))) (.nd (.nd (.lf hnaLvlRow_20) (.lf hnaLvlRow_21)) (.nd (.lf hnaLvlRow_22) (.lf hnaLvlRow_23)))) (.nd (.nd (.nd (.lf hnaLvlRow_24) (.lf hnaLvlRow_25)) (.nd (.lf hnaLvlRow_26) (.lf hnaLvlRow_27))) (.nd (.nd (.lf hnaLvlRow_28) (.lf hnaLvlRow_29)) (.nd (.lf hnaLvlRow_30) (.lf hnaLvlRow_31)))))) (.nd (.nd (.nd (.nd (.nd (.lf hnaLvlRow_32) (.lf hnaLvlRow_33)) (.lf hnaLvlRow_34)) (.lf (.lf 0))) (.lf (.lf 0))) (.lf (.lf 0))))
def hnaLvlIdx (i j : Nat) : Nat := (hnaLvlTree.lookup i).lookup j
def hnaWitRow_0 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 1) (.lf 9)) (.nd (.lf 17) (.lf 25))) (.nd (.nd (.lf 33) (.lf 41)) (.nd (.lf 49) (.lf 57)))) (.nd (.nd (.nd (.lf 65) (.lf 0)) (.nd (.lf 0) (.lf 89))) (.nd (.nd (.lf 97) (.lf 105)) (.nd (.lf 113) (.lf 121))))) (.nd (.nd (.nd (.nd (.lf 129) (.lf 137)) (.nd (.lf 145) (.lf 153))) (.nd (.nd (.lf 32929) (.lf 169)) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 209) (.lf 0))) (.nd (.nd (.lf 225) (.lf 233)) (.nd (.lf 241) (.lf 249)))))) (.nd (.nd (.nd (.nd (.nd (.lf 257) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaWitRow_1 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 2) (.lf 33282)) (.nd (.lf 33794) (.lf 0))) (.nd (.lf 0) (.nd (.lf 3074) (.lf 36354)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 202242))) (.lf 0))) (.lf 0)) (.lf 0))
def hnaWitRow_2 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 10) (.lf 33290)) (.nd (.lf 1034) (.lf 1546))) (.nd (.nd (.lf 2058) (.lf 0)) (.nd (.lf 3082) (.lf 3594)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5642))) (.nd (.nd (.lf 6154) (.lf 6666)) (.nd (.lf 7178) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 40970) (.lf 0)) (.nd (.lf 9226) (.lf 9738))) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 13322) (.lf 0))) (.nd (.nd (.lf 14346) (.lf 0)) (.nd (.lf 15370) (.lf 0)))))) (.lf 0))
def hnaWitRow_3 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 18) (.lf 33298)) (.nd (.lf 1042) (.lf 1554))) (.nd (.lf 0) (.nd (.lf 3090) (.lf 0)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5650))) (.nd (.nd (.lf 0) (.lf 6674)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 9234) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaWitRow_4 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 26) (.lf 538)) (.nd (.lf 1050) (.lf 1562))) (.nd (.lf 0) (.nd (.lf 3098) (.lf 3610)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5658))) (.nd (.nd (.lf 0) (.lf 6682)) (.lf 0)))) (.nd (.lf 0) (.nd (.lf 0) (.nd (.nd (.lf 14362) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaWitRow_5 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 42) (.lf 554)) (.nd (.lf 0) (.lf 1570))) (.nd (.lf 0) (.nd (.lf 3114) (.lf 36386)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5666))) (.nd (.nd (.lf 0) (.lf 6690)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaWitRow_6 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 3) (.lf 32771)) (.nd (.lf 65539) (.lf 98307))) (.nd (.nd (.lf 131075) (.lf 163843)) (.nd (.lf 196611) (.lf 229379)))) (.nd (.nd (.nd (.lf 262147) (.lf 0)) (.nd (.lf 0) (.lf 360451))) (.nd (.nd (.lf 393219) (.lf 425987)) (.nd (.lf 458755) (.lf 491523))))) (.nd (.nd (.nd (.nd (.lf 524291) (.lf 557059)) (.nd (.lf 589827) (.lf 622595))) (.nd (.nd (.lf 655363) (.lf 688131)) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 851971) (.lf 0))) (.nd (.nd (.lf 917507) (.lf 950275)) (.nd (.lf 983043) (.lf 1015811)))))) (.nd (.nd (.nd (.nd (.nd (.lf 1048579) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaWitRow_7 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 50) (.lf 33330)) (.nd (.lf 1074) (.lf 1586))) (.nd (.nd (.lf 2098) (.lf 0)) (.nd (.lf 3122) (.lf 3634)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5682))) (.nd (.nd (.lf 6194) (.lf 6706)) (.nd (.lf 7218) (.lf 0))))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 9266) (.lf 9778))) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 13362) (.lf 0))) (.nd (.nd (.lf 14386) (.lf 0)) (.nd (.lf 15410) (.lf 0)))))) (.lf 0))
def hnaWitRow_8 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 122) (.lf 32795)) (.nd (.lf 66571) (.lf 98331))) (.nd (.lf 0) (.nd (.lf 196635) (.lf 230411)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 361483))) (.nd (.nd (.lf 0) (.lf 426011)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 589851) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaWitRow_9 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 170) (.lf 38923)) (.nd (.lf 67083) (.lf 99851))) (.nd (.lf 0) (.nd (.lf 200203) (.lf 230923)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 366603))) (.nd (.nd (.lf 0) (.lf 432139)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 591371) (.lf 0))) (.lf 0)) (.lf 0))) (.lf 0))
def hnaWitRow_10 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 43) (.lf 33323)) (.nd (.lf 66083) (.lf 98347))) (.nd (.lf 0) (.nd (.lf 196651) (.lf 229923)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 361003))) (.nd (.nd (.lf 0) (.lf 429595)) (.lf 0)))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 590363) (.lf 0))) (.lf 0)) (.nd (.lf 0) (.nd (.nd (.lf 917539) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaWitRow_11 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 515) (.lf 33283)) (.nd (.lf 66051) (.lf 98819))) (.nd (.nd (.lf 131587) (.lf 164355)) (.nd (.lf 197123) (.lf 229891)))) (.nd (.nd (.nd (.lf 262659) (.lf 0)) (.nd (.lf 0) (.lf 360963))) (.nd (.nd (.lf 393731) (.lf 426499)) (.nd (.lf 459267) (.lf 492035))))) (.nd (.nd (.nd (.nd (.lf 524803) (.lf 557571)) (.nd (.lf 590339) (.lf 623107))) (.nd (.nd (.lf 655875) (.lf 688643)) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 852483) (.lf 0))) (.nd (.nd (.lf 918019) (.lf 950787)) (.nd (.lf 983555) (.lf 1016323)))))) (.nd (.nd (.nd (.nd (.nd (.lf 1049091) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaWitRow_12 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 90) (.lf 33370)) (.nd (.lf 1114) (.lf 1626))) (.nd (.nd (.lf 2138) (.lf 0)) (.nd (.lf 3162) (.lf 3674)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5722))) (.nd (.nd (.lf 6234) (.lf 6746)) (.nd (.lf 7258) (.lf 0))))) (.nd (.nd (.nd (.lf 0) (.nd (.lf 9306) (.lf 9818))) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 13402) (.lf 0))) (.nd (.nd (.lf 14426) (.lf 0)) (.nd (.lf 15450) (.lf 0)))))) (.lf 0))
def hnaWitRow_13 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 3075) (.lf 33795)) (.nd (.lf 66563) (.lf 99331))) (.nd (.nd (.lf 132099) (.lf 164867)) (.nd (.lf 200195) (.lf 230403)))) (.nd (.nd (.nd (.lf 263171) (.lf 0)) (.nd (.lf 0) (.lf 364035))) (.nd (.nd (.lf 394243) (.lf 429571)) (.nd (.lf 459779) (.lf 492547))))) (.nd (.nd (.nd (.nd (.lf 525315) (.lf 558083)) (.nd (.lf 590851) (.lf 623619))) (.nd (.nd (.lf 656387) (.lf 689155)) (.lf 0))) (.nd (.nd (.lf 0) (.nd (.lf 852995) (.lf 0))) (.nd (.nd (.lf 918531) (.lf 951299)) (.nd (.lf 984067) (.lf 1016835)))))) (.nd (.nd (.nd (.nd (.nd (.lf 1049603) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)))
def hnaWitRow_14 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 11) (.lf 32779)) (.nd (.lf 65547) (.lf 98315))) (.nd (.nd (.lf 131083) (.lf 163851)) (.nd (.lf 196619) (.lf 229387)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 360459))) (.nd (.nd (.lf 393227) (.lf 425995)) (.nd (.lf 458763) (.lf 491531))))) (.nd (.nd (.nd (.nd (.lf 524299) (.lf 0)) (.nd (.lf 589835) (.lf 0))) (.nd (.nd (.lf 655371) (.lf 0)) (.lf 0))) (.lf 0))) (.lf 0))
def hnaWitRow_15 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 114) (.lf 626)) (.nd (.lf 33906) (.lf 1650))) (.nd (.lf 0) (.nd (.lf 3186) (.lf 36466)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5746))) (.nd (.nd (.lf 0) (.lf 6770)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaWitRow_16 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 523) (.lf 33291)) (.nd (.lf 66059) (.lf 0))) (.nd (.lf 0) (.nd (.lf 197131) (.lf 229899)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 360971))) (.lf 0))) (.lf 0)) (.lf 0))
def hnaWitRow_17 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 6667) (.lf 38411)) (.nd (.lf 68619) (.lf 0))) (.nd (.lf 0) (.nd (.lf 202251) (.lf 232459)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 366091))) (.nd (.nd (.lf 0) (.lf 431627)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaWitRow_18 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 19) (.lf 32787)) (.nd (.lf 65555) (.lf 98323))) (.nd (.nd (.lf 131091) (.lf 0)) (.nd (.lf 196627) (.lf 229395)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 360467))) (.nd (.nd (.lf 393235) (.lf 426003)) (.nd (.lf 458771) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 524307) (.lf 0)) (.nd (.lf 589843) (.lf 622611))) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 851987) (.lf 0))) (.nd (.nd (.lf 917523) (.lf 0)) (.nd (.lf 983059) (.lf 0)))))) (.lf 0))
def hnaWitRow_19 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 146) (.lf 658)) (.nd (.lf 1170) (.lf 1682))) (.nd (.lf 0) (.nd (.lf 3218) (.lf 3730)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5778))) (.nd (.nd (.lf 0) (.lf 6802)) (.lf 0)))) (.nd (.lf 0) (.nd (.lf 0) (.nd (.nd (.lf 14482) (.lf 0)) (.lf 0))))) (.lf 0))
def hnaWitRow_20 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 3091) (.lf 33299)) (.nd (.lf 66067) (.lf 98835))) (.nd (.nd (.lf 131603) (.lf 0)) (.nd (.lf 197139) (.lf 229907)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 360979))) (.nd (.nd (.lf 393747) (.lf 426515)) (.nd (.lf 459283) (.lf 0))))) (.nd (.nd (.nd (.nd (.lf 524819) (.lf 0)) (.nd (.lf 590355) (.lf 623123))) (.lf 0)) (.nd (.nd (.lf 0) (.nd (.lf 852499) (.lf 0))) (.nd (.nd (.lf 918035) (.lf 0)) (.nd (.lf 983571) (.lf 0)))))) (.lf 0))
def hnaWitRow_21 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 32930) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_22 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 3691) (.lf 36459)) (.nd (.lf 67123) (.lf 99891))) (.nd (.nd (.lf 132659) (.lf 165427)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_23 : PTree64 Nat := (.lf 0)
def hnaWitRow_24 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 123) (.lf 32899)) (.nd (.lf 65667) (.lf 98427))) (.nd (.nd (.lf 131131) (.lf 165939)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_25 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 259) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_26 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 51) (.lf 32819)) (.nd (.lf 65587) (.lf 98355))) (.nd (.nd (.lf 131123) (.lf 163891)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_27 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 250) (.lf 762)) (.nd (.lf 0) (.lf 1786))) (.nd (.lf 0) (.nd (.lf 3282) (.lf 0)))) (.nd (.nd (.lf 0) (.nd (.lf 0) (.lf 5882))) (.nd (.nd (.lf 0) (.lf 6906)) (.lf 0)))) (.lf 0)) (.lf 0))
def hnaWitRow_28 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 563) (.lf 33331)) (.nd (.lf 66099) (.lf 98867))) (.nd (.nd (.lf 131635) (.lf 164403)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_29 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 619) (.lf 33371)) (.nd (.lf 66139) (.lf 99379))) (.nd (.nd (.lf 132147) (.lf 164915)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_30 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 3123) (.lf 35891)) (.nd (.lf 68659) (.lf 101427))) (.nd (.nd (.lf 134195) (.lf 166963)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_31 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 107) (.lf 32859)) (.nd (.lf 65627) (.lf 98395))) (.nd (.nd (.lf 131163) (.lf 163931)) (.lf 0))) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_32 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 147) (.lf 32915)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_33 : PTree64 Nat := (.nd (.nd (.nd (.nd (.nd (.nd (.lf 0) (.lf 32931)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0)) (.lf 0))
def hnaWitRow_34 : PTree64 Nat := (.lf 0)
def hnaWitTree : PTree64 (PTree64 Nat) := (.nd (.nd (.nd (.nd (.nd (.nd (.lf hnaWitRow_0) (.lf hnaWitRow_1)) (.nd (.lf hnaWitRow_2) (.lf hnaWitRow_3))) (.nd (.nd (.lf hnaWitRow_4) (.lf hnaWitRow_5)) (.nd (.lf hnaWitRow_6) (.lf hnaWitRow_7)))) (.nd (.nd (.nd (.lf hnaWitRow_8) (.lf hnaWitRow_9)) (.nd (.lf hnaWitRow_10) (.lf hnaWitRow_11))) (.nd (.nd (.lf hnaWitRow_12) (.lf hnaWitRow_13)) (.nd (.lf hnaWitRow_14) (.lf hnaWitRow_15))))) (.nd (.nd (.nd (.nd (.lf hnaWitRow_16) (.lf hnaWitRow_17)) (.nd (.lf hnaWitRow_18) (.lf hnaWitRow_19))) (.nd (.nd (.lf hnaWitRow_20) (.lf hnaWitRow_21)) (.nd (.lf hnaWitRow_22) (.lf hnaWitRow_23)))) (.nd (.nd (.nd (.lf hnaWitRow_24) (.lf hnaWitRow_25)) (.nd (.lf hnaWitRow_26) (.lf hnaWitRow_27))) (.nd (.nd (.lf hnaWitRow_28) (.lf hnaWitRow_29)) (.nd (.lf hnaWitRow_30) (.lf hnaWitRow_31)))))) (.nd (.nd (.nd (.nd (.nd (.lf hnaWitRow_32) (.lf hnaWitRow_33)) (.lf hnaWitRow_34)) (.lf (.lf 0))) (.lf (.lf 0))) (.lf (.lf 0))))
def hnaWitIdx (i j : Nat) : Nat := (hnaWitTree.lookup i).lookup j

def dhn_s_law_row (x : Nat) : Bool :=
  checkNat2 35 35 (fun y z => Nat.beq (dhnIdx (dhnIdx (dhnIdx 0 x) y) z) (dhnIdx (dhnIdx x z) (dhnIdx y z)))
def hna_valid_row (x : Nat) : Bool :=
  checkNat2 35 35 (fun y z =>
    Nat.beq (dhnIdx (dhnIdx (dhnIdx 0 x) y) z) 34 ||
    (Nat.ble 1 (hnaIdx 0 x) && Nat.ble (hnaIdx (dhnIdx x z) (dhnIdx y z)) (hnaIdx (dhnIdx 0 x) y) &&
     Nat.ble (hnaIdx x z + hnaIdx (dhnIdx x z) (dhnIdx y z) * hnaIdx y z) (hnaIdx (dhnIdx (dhnIdx 0 x) y) z)))

def witTag (c : Nat) : Nat := c % 8
def witX   (c : Nat) : Nat := (c / 8) % 64
def witY   (c : Nat) : Nat := (c / 512) % 64
def witZ   (c : Nat) : Nat := c / 32768

def hna_dag_cell_ok (u v code : Nat) : Bool :=
  Nat.ble (hnaLvlIdx u v) 13 &&
  (if Nat.beq (hnaLvlIdx u v) 0 then Nat.beq (hnaIdx u v) 0
   else
     Nat.ble (witX code + 1) 35 && Nat.ble (witY code + 1) 35 && Nat.ble (witZ code + 1) 35 &&
     !Nat.beq (dhnIdx (dhnIdx (dhnIdx 0 (witX code)) (witY code)) (witZ code)) 34 &&
     (if Nat.beq (witTag code) 1 then Nat.beq u 0 && Nat.beq v (witX code) && Nat.ble (hnaIdx u v) 1
      else if Nat.beq (witTag code) 2 then
        Nat.beq u (dhnIdx 0 (witX code)) && Nat.beq v (witY code) &&
        Nat.ble (hnaLvlIdx (dhnIdx (witX code) (witZ code)) (dhnIdx (witY code) (witZ code)) + 1) (hnaLvlIdx u v) &&
        Nat.ble (hnaIdx u v) (hnaIdx (dhnIdx (witX code) (witZ code)) (dhnIdx (witY code) (witZ code)))
      else
        Nat.beq (witTag code) 3 && Nat.beq u (dhnIdx (dhnIdx 0 (witX code)) (witY code)) && Nat.beq v (witZ code) &&
        Nat.ble (hnaLvlIdx (witX code) (witZ code) + 1) (hnaLvlIdx u v) &&
        (Nat.beq (hnaIdx (dhnIdx (witX code) (witZ code)) (dhnIdx (witY code) (witZ code)) * hnaIdx (witY code) (witZ code)) 0 ||
          (Nat.ble (hnaLvlIdx (dhnIdx (witX code) (witZ code)) (dhnIdx (witY code) (witZ code)) + 1) (hnaLvlIdx u v) &&
           Nat.ble (hnaLvlIdx (witY code) (witZ code) + 1) (hnaLvlIdx u v))) &&
        Nat.ble (hnaIdx u v) (hnaIdx (witX code) (witZ code) + hnaIdx (dhnIdx (witX code) (witZ code)) (dhnIdx (witY code) (witZ code)) * hnaIdx (witY code) (witZ code))))

def hna_dag_cert_ok : Bool := checkNat2 35 35 (fun u v => hna_dag_cell_ok u v (hnaWitIdx u v))

end SimplifiedQ10Q5
