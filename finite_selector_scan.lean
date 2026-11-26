import Std

/- Generic finite-control left-to-right scan facts. This abstracts the
   protected-tape cursor; its connection to S-tree navigation is separate. -/

def scanIndex {A : Type} (p : A → Bool) : List A → Option Nat
  | [] => none
  | a :: rest => if p a then some 0 else (scanIndex p rest).map Nat.succ

theorem scan_none_when_absent {A : Type} (p : A → Bool) (xs : List A)
    (h : ∀ x ∈ xs, p x = false) : scanIndex p xs = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = false := h x (by simp)
    have hxs : ∀ y ∈ xs, p y = false := by
      intro y hy
      exact h y (by simp [hy])
    simp [scanIndex, hx, ih hxs]

theorem scan_finds_first {A : Type} (p : A → Bool) (before after : List A) (target : A)
    (hbefore : ∀ x ∈ before, p x = false) (htarget : p target = true) :
    scanIndex p (before ++ target :: after) = some before.length := by
  induction before with
  | nil => simp [scanIndex, htarget]
  | cons x xs ih =>
    have hx : p x = false := hbefore x (by simp)
    have hxs : ∀ y ∈ xs, p y = false := by
      intro y hy
      exact hbefore y (by simp [hy])
    simp [scanIndex, hx, ih hxs]

#print axioms scan_none_when_absent
#print axioms scan_finds_first
