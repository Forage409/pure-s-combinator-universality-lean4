import formal_controller.s_output_and_bounds

/-!
# Genuine Finite-State Root-Restarted Tree-Walking Controller

Replaces list-path manipulation in `fullRootSelector fixedBinaryProgram` with a genuine
finite-state root-restarted occurrence-tree-walking controller:
- Functional zipper `Cursor` (`focus`, `crumbs : List Crumb`), `rootCursor`, `rebuild`;
- 6-symbol local observation `Obs = NodeKind × Incoming`;
- Primitive walker action `Action C = moveLeft C | moveRight C | moveUp C | contractFocus | reportNormal`;
- Explicit finite `Control` type with `DecidableEq Control`, `allControls : List Control`,
  and `∀ c : Control, c ∈ allControls`;
- Unit inter-invocation state `(initControl, rootCursor t)`;
- Unconditional all-input linear microtick bound `≤ walkerConst * (leaves t + 1)` on every `t : Term`;
- Exact single-contraction / normality contract on every pure-S closed `t : Term`;
- Exact trajectory agreement with `fullRootSelector fixedBinaryProgram` + `contractAt` on every
  reachable canonical term from `sEncodeU initial`.
-/

/-! ## Section 1: Occurrence-Tree Zipper, Local Observation, Actions, and `contractAt` -/

inductive Crumb where
  | left (rightSib : Term)
  | right (leftSib : Term)
  deriving DecidableEq, Repr

structure Cursor where
  focus : Term
  crumbs : List Crumb
  deriving DecidableEq, Repr

def rootCursor (t : Term) : Cursor := ⟨t, []⟩

def rebuildWith : List Crumb → Term → Term
  | [], t => t
  | .left r :: cs, t => rebuildWith cs (t ⋅ r)
  | .right l :: cs, t => rebuildWith cs (l ⋅ t)

def rebuild (cur : Cursor) : Term :=
  rebuildWith cur.crumbs cur.focus

def crumbsPath : List Crumb → List Bool
  | [] => []
  | .left _ :: cs => crumbsPath cs ++ [false]
  | .right _ :: cs => crumbsPath cs ++ [true]

def crumbLeaves : List Crumb → Nat
  | [] => 0
  | .left r :: cs => leaves r + crumbLeaves cs
  | .right l :: cs => leaves l + crumbLeaves cs

theorem leaves_pos (t : Term) : 1 ≤ leaves t := by
  cases t with
  | s => exact Nat.le_refl 1
  | var _ => exact Nat.le_refl 1
  | app l r =>
      have hl := leaves_pos l
      have hr := leaves_pos r
      simp only [leaves]
      omega

theorem leaves_rebuildWith (cs : List Crumb) (t : Term) :
    leaves (rebuildWith cs t) = leaves t + crumbLeaves cs := by
  induction cs generalizing t with
  | nil => simp [rebuildWith, crumbLeaves]
  | cons c rest ih =>
      cases c with
      | left r =>
          simp only [rebuildWith, crumbLeaves, ih, leaves]
          omega
      | right l =>
          simp only [rebuildWith, crumbLeaves, ih, leaves]
          omega

theorem leaves_rebuild (cur : Cursor) :
    leaves (rebuild cur) = leaves cur.focus + crumbLeaves cur.crumbs :=
  leaves_rebuildWith cur.crumbs cur.focus

theorem crumbs_length_le_crumbLeaves (cs : List Crumb) :
    cs.length ≤ crumbLeaves cs := by
  induction cs with
  | nil => exact Nat.le_refl 0
  | cons c rest ih =>
      cases c with
      | left r =>
          have hr := leaves_pos r
          simp only [List.length_cons, crumbLeaves]
          omega
      | right l =>
          have hl := leaves_pos l
          simp only [List.length_cons, crumbLeaves]
          omega

theorem crumbs_length_lt_leaves_rebuild (cur : Cursor) :
    cur.crumbs.length < leaves (rebuild cur) := by
  have h1 := leaves_rebuild cur
  have h2 := crumbs_length_le_crumbLeaves cur.crumbs
  have h3 := leaves_pos cur.focus
  omega

/-- Pure-S closedness predicate (excludes `.var _`). -/
def isPureS : Term → Bool
  | .s => true
  | .var _ => false
  | .app l r => isPureS l && isPureS r

theorem isPureS_rebuildWith (cs : List Crumb) (t : Term) :
    isPureS (rebuildWith cs t) = true → isPureS t = true := by
  induction cs generalizing t with
  | nil => intro h; exact h
  | cons c rest ih =>
      intro h
      cases c with
      | left r =>
          have hsub := ih (t ⋅ r) h
          simp only [isPureS, Bool.and_eq_true] at hsub
          exact hsub.1
      | right l =>
          have hsub := ih (l ⋅ t) h
          simp only [isPureS, Bool.and_eq_true] at hsub
          exact hsub.2

theorem isPureS_focus_of_rebuild {cur : Cursor} (h : isPureS (rebuild cur) = true) :
    isPureS cur.focus = true :=
  isPureS_rebuildWith cur.crumbs cur.focus h

/-- 2-symbol node kind (`isS` vs `isApp`; `.var _` is treated as non-application leaf). -/
inductive NodeKind where
  | isS
  | isApp
  deriving DecidableEq, Repr

/-- 3-symbol incoming-edge direction (`root | fromLeft | fromRight`). -/
inductive Incoming where
  | root
  | fromLeft
  | fromRight
  deriving DecidableEq, Repr

/-- 6-symbol local observation alphabet. -/
abbrev Obs := NodeKind × Incoming

def nodeKindOf : Term → NodeKind
  | .app _ _ => .isApp
  | .s => .isS
  | .var _ => .isS

def incomingOf : List Crumb → Incoming
  | [] => .root
  | .left _ :: _ => .fromLeft
  | .right _ :: _ => .fromRight

def observe (cur : Cursor) : Obs :=
  (nodeKindOf cur.focus, incomingOf cur.crumbs)

theorem pureS_isS_eq_s {t : Term} (hp : isPureS t = true) (hk : nodeKindOf t = .isS) :
    t = .s := by
  cases t with
  | s => rfl
  | var _ => simp [isPureS] at hp
  | app _ _ => simp [nodeKindOf] at hk

/-- Primitive tree-walker actions (no `stay` constructor). -/
inductive Action (C : Type) where
  | moveLeft : C → Action C
  | moveRight : C → Action C
  | moveUp : C → Action C
  | contractFocus : Action C
  | reportNormal : Action C
  deriving DecidableEq, Repr

/-- Single-invocation result of the root-restarted controller. -/
inductive InvokeResult where
  | normal
  | contracted (out : Term)
  deriving DecidableEq, Repr

/-- Contract an S-redex `S ⋅ x ⋅ y ⋅ z ↦ (x ⋅ z) ⋅ (y ⋅ z)` at the root of a subterm. -/
def contractRoot : Term → Option Term
  | .app (.app (.app .s x) y) z => some ((x ⋅ z) ⋅ (y ⋅ z))
  | _ => none

/-- Contract an S-redex at an explicit occurrence-tree path. -/
def contractAt : Term → List Bool → Option Term
  | t, [] => contractRoot t
  | t, side :: p =>
      match t, side with
      | .app l r, false => (contractAt l p).map (· ⋅ r)
      | .app l r, true => (contractAt r p).map (l ⋅ ·)
      | _, _ => none

theorem contractRoot_iff_directedStep (t t' : Term) :
    contractRoot t = some t' ↔ DirectedStep [] t t' := by
  constructor
  · intro h
    match t with
    | .app (.app (.app .s x) y) z =>
        simp only [contractRoot, Option.some.injEq] at h
        subst t'
        exact DirectedStep.root x y z
    | .s => simp [contractRoot] at h
    | .var _ => simp [contractRoot] at h
    | .app .s _ => simp [contractRoot] at h
    | .app (.var _) _ => simp [contractRoot] at h
    | .app (.app .s _) _ => simp [contractRoot] at h
    | .app (.app (.var _) _) _ => simp [contractRoot] at h
    | .app (.app (.app (.var _) _) _) _ => simp [contractRoot] at h
    | .app (.app (.app (.app _ _) _) _) _ => simp [contractRoot] at h
  · intro h
    cases h with
    | root x y z => rfl

theorem contractAt_iff_directedStep (t t' : Term) (p : List Bool) :
    contractAt t p = some t' ↔ DirectedStep p t t' := by
  induction p generalizing t t' with
  | nil => simpa [contractAt] using contractRoot_iff_directedStep t t'
  | cons side rest ih =>
      constructor
      · intro h
        cases t with
        | s => simp [contractAt] at h
        | var _ => simp [contractAt] at h
        | app l r =>
            cases side with
            | false =>
                cases hx : contractAt l rest with
                | none => simp [contractAt, hx] at h
                | some l' =>
                    simp only [contractAt, hx, Option.map, Option.some.injEq] at h
                    subst t'
                    exact DirectedStep.left ((ih l l').mp hx)
            | true =>
                cases hx : contractAt r rest with
                | none => simp [contractAt, hx] at h
                | some r' =>
                    simp only [contractAt, hx, Option.map, Option.some.injEq] at h
                    subst t'
                    exact DirectedStep.right ((ih r r').mp hx)
      · intro h
        cases h with
        | @left _ a a' b ha =>
            simp only [contractAt]
            rw [(ih a a').mpr ha]
            rfl
        | @right _ a b b' hb =>
            simp only [contractAt]
            rw [(ih b b').mpr hb]
            rfl

theorem directedStep_rebuildWith (cs : List Crumb) {p : List Bool} {a b : Term}
    (h : DirectedStep p a b) :
    DirectedStep (crumbsPath cs ++ p) (rebuildWith cs a) (rebuildWith cs b) := by
  induction cs generalizing p a b with
  | nil => simpa [crumbsPath, rebuildWith] using h
  | cons c rest ih =>
      cases c with
      | left r =>
          have hstep := DirectedStep.left (b := r) h
          simpa [crumbsPath, rebuildWith, List.append_assoc] using ih hstep
      | right l =>
          have hstep := DirectedStep.right (a := l) h
          simpa [crumbsPath, rebuildWith, List.append_assoc] using ih hstep

theorem directedStep_rebuild_root (cur : Cursor) {next : Term}
    (h : contractRoot cur.focus = some next) :
    DirectedStep (crumbsPath cur.crumbs) (rebuild cur) (rebuild { cur with focus := next }) := by
  have hr := (contractRoot_iff_directedStep cur.focus next).mp h
  simpa [rebuild, List.append_nil] using directedStep_rebuildWith cur.crumbs hr

theorem termAt_rebuildWith (cs : List Crumb) (t : Term) :
    termAt (rebuildWith cs t) (crumbsPath cs) = some t := by
  induction cs generalizing t with
  | nil => exact term_at_nil t
  | cons c rest ih =>
      cases c with
      | left r =>
          simp only [rebuildWith, crumbsPath]
          rw [term_at_append, ih (t ⋅ r)]
          exact term_at_nil t
      | right l =>
          simp only [rebuildWith, crumbsPath]
          rw [term_at_append, ih (l ⋅ t)]
          exact term_at_nil t


/-! ## Section 2: Finite Registers, Explicit Finite `Control` State Type, and `allControls` -/

abbrev Bits11 := { bs : List Bool // bs.length = 11 }
abbrev BitsLe11 := { bs : List Bool // bs.length ≤ 11 }

/-- Finite 11-bit decoded cell representation (`bit`, `status`, 8-bit `state : Fin 256`). -/
structure Cell8 where
  bit : Bool
  status : Status
  state : Fin 256
  deriving DecidableEq, Repr

def cell8ToCell (c : Cell8) : Cell :=
  ⟨c.bit, c.status, c.state.val⟩

def defaultCell8 : Cell8 :=
  ⟨false, .off, ⟨0, by decide⟩⟩

theorem foldl_stateNumber_bound (bs : List Bool) :
    ∀ acc : Nat, bs.foldl (fun n b => 2 * n + if b then 1 else 0) acc < (acc + 1) * 2 ^ bs.length := by
  induction bs with
  | nil =>
      intro acc
      simp
  | cons b rest ih =>
      intro acc
      have hsub := ih (2 * acc + if b then 1 else 0)
      have hpow : 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by
        rw [Nat.pow_succ, Nat.mul_comm]
      cases b with
      | false =>
          simp only [List.foldl_cons, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsub ⊢
          simp only [List.length_cons, hpow]
          have hmul : (2 * acc + 1) * 2 ^ rest.length ≤ (acc + 1) * (2 * 2 ^ rest.length) := by
            have h1 : 2 * acc + 1 ≤ 2 * (acc + 1) := by omega
            calc
              (2 * acc + 1) * 2 ^ rest.length ≤ (2 * (acc + 1)) * 2 ^ rest.length :=
                Nat.mul_le_mul_right _ h1
              _ = (acc + 1) * (2 * 2 ^ rest.length) := by
                simp [Nat.mul_assoc, Nat.mul_comm]
          omega
      | true =>
          simp only [List.foldl_cons, ↓reduceIte] at hsub ⊢
          simp only [List.length_cons, hpow]
          have hmul : (2 * acc + 1 + 1) * 2 ^ rest.length = (acc + 1) * (2 * 2 ^ rest.length) := by
            have h1 : 2 * acc + 1 + 1 = 2 * (acc + 1) := by omega
            rw [h1]
            simp [Nat.mul_assoc, Nat.mul_comm]
          omega

theorem stateNumber_lt_256 (bs : List Bool) (h : bs.length = 8) :
    stateNumber bs < 256 := by
  have hb := foldl_stateNumber_bound bs 0
  rw [h] at hb
  simpa [stateNumber] using hb

def decodeBits11 (bits : Bits11) : Cell8 :=
  match bits.val, bits.property with
  | b :: x :: y :: rest, h =>
      have hrest : rest.length = 8 := by simp at h; exact h
      ⟨b, bitsStatus x y, ⟨stateNumber rest, stateNumber_lt_256 rest hrest⟩⟩

theorem decodeBits11_agrees (bits : Bits11) :
    decodeCellBits bits.val = some (cell8ToCell (decodeBits11 bits)) := by
  rcases bits with ⟨bs, h⟩
  match bs, h with
  | b :: x :: y :: rest, h =>
      rfl

def encodeRecord11 (c : Cell) : Bits11 :=
  ⟨encodeCellBits c (stateBits8 c.state), by simp [encodeCellBits, stateBits8_width]⟩

def pushBit11 (acc : BitsLe11) (b : Bool) (h : acc.val.length < 11) : BitsLe11 :=
  ⟨acc.val ++ [b], by simp; omega⟩

/-- Symbolic finite enumerators with constructive completeness proofs. -/
def allBools : List Bool := [false, true]

theorem mem_allBools (b : Bool) : b ∈ allBools := by
  cases b <;> simp [allBools]

def allFins : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.succ_pos n⟩ :: (allFins n).map Fin.succ

theorem mem_allFins : ∀ {n : Nat} (i : Fin n), i ∈ allFins n
  | 0, ⟨_, h⟩ => False.elim (Nat.not_lt_zero _ h)
  | n + 1, ⟨0, _⟩ => by simp [allFins]
  | n + 1, ⟨k + 1, h⟩ => by
      have hk : k < n := Nat.lt_of_succ_lt_succ h
      have ih := mem_allFins ⟨k, hk⟩
      simp only [allFins, List.mem_cons, List.mem_map]
      exact Or.inr ⟨⟨k, hk⟩, ih, rfl⟩

def allBitsExact : (n : Nat) → List { bs : List Bool // bs.length = n }
  | 0 => [⟨[], rfl⟩]
  | n + 1 =>
      (allBitsExact n).flatMap fun ⟨bs, h⟩ =>
        [⟨false :: bs, by simp [h]⟩, ⟨true :: bs, by simp [h]⟩]

theorem mem_allBitsExact : ∀ {n : Nat} (x : { bs : List Bool // bs.length = n }), x ∈ allBitsExact n
  | 0, ⟨[], _⟩ => by simp [allBitsExact]
  | n + 1, ⟨b :: bs, h⟩ => by
      have h' : bs.length = n := by simp at h; exact h
      have ih := mem_allBitsExact ⟨bs, h'⟩
      simp only [allBitsExact, List.mem_flatMap]
      refine ⟨⟨bs, h'⟩, ih, ?_⟩
      cases b <;> simp

def allBitsLe : (n : Nat) → List { bs : List Bool // bs.length ≤ n }
  | 0 => [⟨[], Nat.le_refl 0⟩]
  | n + 1 =>
      ⟨[], Nat.zero_le _⟩ ::
      (allBitsLe n).flatMap fun ⟨bs, h⟩ =>
        [⟨false :: bs, by simp; omega⟩, ⟨true :: bs, by simp; omega⟩]

theorem mem_allBitsLe : ∀ {n : Nat} (x : { bs : List Bool // bs.length ≤ n }), x ∈ allBitsLe n
  | 0, ⟨[], _⟩ => by simp [allBitsLe]
  | n + 1, ⟨[], _⟩ => by simp [allBitsLe]
  | n + 1, ⟨b :: bs, h⟩ => by
      have h' : bs.length ≤ n := by simp at h; omega
      have ih := mem_allBitsLe ⟨bs, h'⟩
      simp only [allBitsLe, List.mem_cons, List.mem_flatMap]
      right
      refine ⟨⟨bs, h'⟩, ih, ?_⟩
      cases b <;> simp

def allOptions {α : Type} (xs : List α) : List (Option α) :=
  none :: xs.map some

theorem mem_allOptions {α : Type} {xs : List α} (hm : ∀ x : α, x ∈ xs) :
    ∀ o : Option α, o ∈ allOptions xs
  | none => by simp [allOptions]
  | some x => by simp [allOptions, hm x]

def allStatuses : List Status := [.off, .active, .movingLeft, .movingRight]

theorem mem_allStatuses (s : Status) : s ∈ allStatuses := by
  cases s <;> simp [allStatuses]

def allCell8s : List Cell8 :=
  allBools.flatMap fun b =>
    allStatuses.flatMap fun st =>
      (allFins 256).map fun q => ⟨b, st, q⟩

theorem mem_allCell8s (c : Cell8) : c ∈ allCell8s := by
  rcases c with ⟨b, st, q⟩
  simp only [allCell8s, List.mem_flatMap, List.mem_map]
  exact ⟨b, mem_allBools b, st, mem_allStatuses st, q, mem_allFins q, rfl⟩

/-- Subroutine caller tags (strictly acyclic hierarchy). -/
inductive CellCaller where
  | seekPending
  | seekActive
  | readDestRight (pending : Cell8)
  | readDestLeft (pending : Cell8)
  deriving DecidableEq, Repr

inductive HubCheckCont where
  | rewindTapeChk
  | rewindHaltChk
  | activeBoundaryChk (cell : Cell8)
  | pendingLeftChk (pending : Cell8)
  deriving DecidableEq, Repr

inductive UpCont where
  | flagToHub
  | rfBitValBack (caller : CellCaller) (acc : BitsLe11)
  | rfClimb (caller : CellCaller) (res : Option Bits11) (rem : Fin 12)
  | rcBottomToPrev (caller : CellCaller)
  | rcSearchTestParent (caller : CellCaller)
  | rcAfterRf (caller : CellCaller) (found : Option Cell8)
  | rcHaveTestParent (caller : CellCaller) (cell : Cell8)
  | rewindToTape
  | rewindToHubHalt
  | activeBoundaryTest (cell : Cell8)
  | pendingRightBackToSrc (bit : Bool)
  | pendingLeftToParent (pending : Cell8)
  | chkCommClimb (desired : Bits11) (committed : Bool) (rem : Fin 12)
  | appendFldFlagBack (bs : BitsLe11)
  deriving DecidableEq, Repr

inductive StrictFrameCont where
  | hubInit
  | flagInit
  | frontierWalk
  | upCheck (ret : UpCont)
  | rfBitFrame (caller : CellCaller) (acc : BitsLe11)
  | rfBitVal (caller : CellCaller) (acc : BitsLe11)
  | rcDown (caller : CellCaller)
  | seekCell (passIsActive : Bool)
  | pendingRightDest (pending : Cell8)
  | appendVer (desired : Bits11)
  | chkComm (desired : Bits11) (idx : Fin 12)
  | appendFldNode (remBits : BitsLe11)
  | appendFldFlag (bs : BitsLe11)
  deriving DecidableEq, Repr

/-- Local 16-microtick strict-frame lookahead states. -/
inductive SfState where
  | sf0 (ret : StrictFrameCont)
  | sf1 (ret : StrictFrameCont)
  | sf2 (ret : StrictFrameCont)
  | sfAbortA (ret : StrictFrameCont)
  | sf3 (ret : StrictFrameCont)
  | sf4 (ret : StrictFrameCont)
  | sf5 (ret : StrictFrameCont)
  | sf6 (ret : StrictFrameCont)
  | sfAbortB (ret : StrictFrameCont)
  | sf7 (ret : StrictFrameCont)
  | sf8 (ret : StrictFrameCont)
  | sfAtB (ret : StrictFrameCont)
  | sfJ0 (ret : StrictFrameCont)
  | sfJ1 (ret : StrictFrameCont)
  | sfJ2 (ret : StrictFrameCont)
  | sfJUp2 (ret : StrictFrameCont) (ok : Bool)
  | sfJUp1 (ret : StrictFrameCont) (ok : Bool)
  | sfUpFromJ (ret : StrictFrameCont) (ok : Bool)
  | sfDone (ret : StrictFrameCont) (res : Bool)
  deriving DecidableEq, Repr

inductive DownLCont where
  | toFlagInit
  | toFrontier
  | toRcStart (caller : CellCaller)
  | toRcDown (caller : CellCaller)
  | toRcInspect (caller : CellCaller)
  | toRfBitVal (caller : CellCaller) (acc : BitsLe11)
  | toHaltFlagOpen
  | toAppendVerEntry (desired : Bits11)
  | toAppendVerNext (desired : Bits11)
  | toAppendFldFlag (bs : BitsLe11)
  deriving DecidableEq, Repr

inductive DownRCont where
  | toTapeInit
  | toTapePass2
  | toNextCell (passIsActive : Bool)
  | toRfEntry (caller : CellCaller)
  | toRfNext (caller : CellCaller) (acc : BitsLe11)
  | toRcDone (caller : CellCaller) (cell : Cell8)
  | toActiveBoundaryBack (desired : Bits11)
  | toPendingRightDest (pending : Cell8)
  | toPendingLeftBackToSrc (desired : Bits11)
  | toChkComm (desired : Bits11)
  | toChkCommNext (desired : Bits11) (idx : Fin 12)
  | toAppendFld (remBits : BitsLe11)
  deriving DecidableEq, Repr

/-- Bounded 5-edge opening check (`nextOpeningAddress` + contraction). -/
inductive OpenState where
  | pf0
  | pf1
  | pf2
  | pfAbortA
  | pf3
  | pf4
  | pf5
  | pf6
  | pfAbortB
  | pf7
  | pf8 (ok : Bool)
  | pf9 (ok : Bool)
  | pfDone (isOpenFrame : Bool)
  | leftArity (d : Fin 5)
  | back2_1
  | back2_0
  | rightArity (d : Fin 5)
  deriving DecidableEq, Repr

/-- Root-ascend fallback, Euler-tour leftmost-redex search, and 3-edge redex climb. -/
inductive EulerState where
  | abortToRoot
  | eulerSpine (d : Fin 4)
  | eulerFromLeft
  | eulerFromRight
  | climbToRedex2
  | climbToRedex1
  | contractRedex
  deriving DecidableEq, Repr

/-- Explicit finite control state type of the root-restarted tree-walking controller. -/
inductive Control where
  | init
  | sf (s : SfState)
  | up1 (ret : UpCont)
  | upDone (ret : UpCont) (fromRight : Bool)
  | downL1 (next : DownLCont)
  | downLDone (next : DownLCont)
  | downR1 (next : DownRCont)
  | downR2 (next : DownRCont)
  | downRDone (next : DownRCont)
  | hubChk1 (ret : HubCheckCont)
  | hubChkDone (ret : HubCheckCont) (isHub : Bool)
  | openSub (s : OpenState)
  | euler (s : EulerState)
  deriving DecidableEq, Repr

def initControl : Control := .init

/-! ### Explicit Finite State List `allControls` & Completeness Proof -/

def allCellCallers : List CellCaller :=
  [.seekPending, .seekActive] ++
  allCell8s.map .readDestRight ++
  allCell8s.map .readDestLeft

theorem mem_allCellCallers (x : CellCaller) : x ∈ allCellCallers := by
  cases x with
  | seekPending => simp [allCellCallers]
  | seekActive => simp [allCellCallers]
  | readDestRight p => simp [allCellCallers, mem_allCell8s p]
  | readDestLeft p => simp [allCellCallers, mem_allCell8s p]

def allHubCheckConts : List HubCheckCont :=
  [.rewindTapeChk, .rewindHaltChk] ++
  allCell8s.map .activeBoundaryChk ++
  allCell8s.map .pendingLeftChk

theorem mem_allHubCheckConts (x : HubCheckCont) : x ∈ allHubCheckConts := by
  cases x with
  | rewindTapeChk => simp [allHubCheckConts]
  | rewindHaltChk => simp [allHubCheckConts]
  | activeBoundaryChk c => simp [allHubCheckConts, mem_allCell8s c]
  | pendingLeftChk p => simp [allHubCheckConts, mem_allCell8s p]

def allUpConts : List UpCont :=
  [.flagToHub, .rewindToTape, .rewindToHubHalt] ++
  (allCellCallers.flatMap fun c => (allBitsLe 11).map (.rfBitValBack c)) ++
  (allCellCallers.flatMap fun c =>
    (allOptions (allBitsExact 11)).flatMap fun r => (allFins 12).map (.rfClimb c r)) ++
  allCellCallers.map .rcBottomToPrev ++
  allCellCallers.map .rcSearchTestParent ++
  (allCellCallers.flatMap fun c => (allOptions allCell8s).map (.rcAfterRf c)) ++
  (allCellCallers.flatMap fun c => allCell8s.map (.rcHaveTestParent c)) ++
  allCell8s.map .activeBoundaryTest ++
  allBools.map .pendingRightBackToSrc ++
  allCell8s.map .pendingLeftToParent ++
  ((allBitsExact 11).flatMap fun d =>
    allBools.flatMap fun cm => (allFins 12).map (.chkCommClimb d cm)) ++
  (allBitsLe 11).map .appendFldFlagBack

theorem mem_allUpConts (x : UpCont) : x ∈ allUpConts := by
  have hOptB := mem_allOptions (mem_allBitsExact (n := 11))
  have hOptC := mem_allOptions mem_allCell8s
  cases x with
  | flagToHub => simp [allUpConts]
  | rewindToTape => simp [allUpConts]
  | rewindToHubHalt => simp [allUpConts]
  | rfBitValBack c acc =>
      simp only [allUpConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; left; left; left; left; left; left; left; right
      exact ⟨c, mem_allCellCallers c, acc, mem_allBitsLe acc, rfl⟩
  | rfClimb c r rem =>
      simp only [allUpConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; left; left; left; left; left; left; right
      exact ⟨c, mem_allCellCallers c, r, hOptB r, rem, mem_allFins rem, rfl⟩
  | rcBottomToPrev c =>
      simp [allUpConts, mem_allCellCallers c]
  | rcSearchTestParent c =>
      simp [allUpConts, mem_allCellCallers c]
  | rcAfterRf c f =>
      simp only [allUpConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; left; left; left; right
      exact ⟨c, mem_allCellCallers c, f, hOptC f, rfl⟩
  | rcHaveTestParent c cell =>
      simp only [allUpConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; left; left; right
      exact ⟨c, mem_allCellCallers c, cell, mem_allCell8s cell, rfl⟩
  | activeBoundaryTest cell =>
      simp [allUpConts, mem_allCell8s cell]
  | pendingRightBackToSrc b =>
      simp [allUpConts, mem_allBools b]
  | pendingLeftToParent p =>
      simp [allUpConts, mem_allCell8s p]
  | chkCommClimb d cm rem =>
      simp only [allUpConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; right
      exact ⟨d, mem_allBitsExact d, cm, mem_allBools cm, rem, mem_allFins rem, rfl⟩
  | appendFldFlagBack bs =>
      simp [allUpConts, mem_allBitsLe bs]

def allStrictFrameConts : List StrictFrameCont :=
  [.hubInit, .flagInit, .frontierWalk] ++
  allUpConts.map .upCheck ++
  (allCellCallers.flatMap fun c => (allBitsLe 11).map (.rfBitFrame c)) ++
  (allCellCallers.flatMap fun c => (allBitsLe 11).map (.rfBitVal c)) ++
  allCellCallers.map .rcDown ++
  allBools.map .seekCell ++
  allCell8s.map .pendingRightDest ++
  (allBitsExact 11).map .appendVer ++
  ((allBitsExact 11).flatMap fun d => (allFins 12).map (.chkComm d)) ++
  (allBitsLe 11).map .appendFldNode ++
  (allBitsLe 11).map .appendFldFlag

theorem mem_allStrictFrameConts (x : StrictFrameCont) : x ∈ allStrictFrameConts := by
  cases x with
  | hubInit => simp [allStrictFrameConts]
  | flagInit => simp [allStrictFrameConts]
  | frontierWalk => simp [allStrictFrameConts]
  | upCheck u => simp [allStrictFrameConts, mem_allUpConts u]
  | rfBitFrame c acc =>
      simp only [allStrictFrameConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; left; left; left; left; left; right
      exact ⟨c, mem_allCellCallers c, acc, mem_allBitsLe acc, rfl⟩
  | rfBitVal c acc =>
      simp only [allStrictFrameConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; left; left; left; left; right
      exact ⟨c, mem_allCellCallers c, acc, mem_allBitsLe acc, rfl⟩
  | rcDown c => simp [allStrictFrameConts, mem_allCellCallers c]
  | seekCell b => simp [allStrictFrameConts, mem_allBools b]
  | pendingRightDest p => simp [allStrictFrameConts, mem_allCell8s p]
  | appendVer d => simp [allStrictFrameConts, mem_allBitsExact d]
  | chkComm d idx =>
      simp only [allStrictFrameConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; right
      exact ⟨d, mem_allBitsExact d, idx, mem_allFins idx, rfl⟩
  | appendFldNode rem => simp [allStrictFrameConts, mem_allBitsLe rem]
  | appendFldFlag bs => simp [allStrictFrameConts, mem_allBitsLe bs]

def allSfStates : List SfState :=
  allStrictFrameConts.flatMap fun r =>
    [.sf0 r, .sf1 r, .sf2 r, .sfAbortA r, .sf3 r, .sf4 r, .sf5 r, .sf6 r,
     .sfAbortB r, .sf7 r, .sf8 r, .sfAtB r, .sfJ0 r, .sfJ1 r, .sfJ2 r,
     .sfJUp2 r false, .sfJUp2 r true, .sfJUp1 r false, .sfJUp1 r true,
     .sfUpFromJ r false, .sfUpFromJ r true, .sfDone r false, .sfDone r true]

theorem mem_allSfStates (s : SfState) : s ∈ allSfStates := by
  cases s with
  | sf0 r | sf1 r | sf2 r | sfAbortA r | sf3 r | sf4 r | sf5 r | sf6 r
  | sfAbortB r | sf7 r | sf8 r | sfAtB r | sfJ0 r | sfJ1 r | sfJ2 r =>
      simp only [allSfStates, List.mem_flatMap]
      exact ⟨r, mem_allStrictFrameConts r, by simp⟩
  | sfJUp2 r b | sfJUp1 r b | sfUpFromJ r b | sfDone r b =>
      simp only [allSfStates, List.mem_flatMap]
      refine ⟨r, mem_allStrictFrameConts r, ?_⟩
      cases b <;> simp

def allDownLConts : List DownLCont :=
  [.toFlagInit, .toFrontier, .toHaltFlagOpen] ++
  allCellCallers.map .toRcStart ++
  allCellCallers.map .toRcDown ++
  allCellCallers.map .toRcInspect ++
  (allCellCallers.flatMap fun c => (allBitsLe 11).map (.toRfBitVal c)) ++
  (allBitsExact 11).map .toAppendVerEntry ++
  (allBitsExact 11).map .toAppendVerNext ++
  (allBitsLe 11).map .toAppendFldFlag

theorem mem_allDownLConts (x : DownLCont) : x ∈ allDownLConts := by
  cases x with
  | toFlagInit => simp [allDownLConts]
  | toFrontier => simp [allDownLConts]
  | toHaltFlagOpen => simp [allDownLConts]
  | toRcStart c => simp [allDownLConts, mem_allCellCallers c]
  | toRcDown c => simp [allDownLConts, mem_allCellCallers c]
  | toRcInspect c => simp [allDownLConts, mem_allCellCallers c]
  | toRfBitVal c acc =>
      simp only [allDownLConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; right
      exact ⟨c, mem_allCellCallers c, acc, mem_allBitsLe acc, rfl⟩
  | toAppendVerEntry d => simp [allDownLConts, mem_allBitsExact d]
  | toAppendVerNext d => simp [allDownLConts, mem_allBitsExact d]
  | toAppendFldFlag bs => simp [allDownLConts, mem_allBitsLe bs]

def allDownRConts : List DownRCont :=
  [.toTapeInit, .toTapePass2] ++
  allBools.map .toNextCell ++
  allCellCallers.map .toRfEntry ++
  (allCellCallers.flatMap fun c => (allBitsLe 11).map (.toRfNext c)) ++
  (allCellCallers.flatMap fun c => allCell8s.map (.toRcDone c)) ++
  (allBitsExact 11).map .toActiveBoundaryBack ++
  allCell8s.map .toPendingRightDest ++
  (allBitsExact 11).map .toPendingLeftBackToSrc ++
  (allBitsExact 11).map .toChkComm ++
  ((allBitsExact 11).flatMap fun d => (allFins 12).map (.toChkCommNext d)) ++
  (allBitsLe 11).map .toAppendFld

theorem mem_allDownRConts (x : DownRCont) : x ∈ allDownRConts := by
  cases x with
  | toTapeInit => simp [allDownRConts]
  | toTapePass2 => simp [allDownRConts]
  | toNextCell b => simp [allDownRConts, mem_allBools b]
  | toRfEntry c => simp [allDownRConts, mem_allCellCallers c]
  | toRfNext c acc =>
      simp only [allDownRConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; left; left; left; left; right
      exact ⟨c, mem_allCellCallers c, acc, mem_allBitsLe acc, rfl⟩
  | toRcDone c cell =>
      simp only [allDownRConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left; left; left; left; left; right
      exact ⟨c, mem_allCellCallers c, cell, mem_allCell8s cell, rfl⟩
  | toActiveBoundaryBack d => simp [allDownRConts, mem_allBitsExact d]
  | toPendingRightDest p => simp [allDownRConts, mem_allCell8s p]
  | toPendingLeftBackToSrc d => simp [allDownRConts, mem_allBitsExact d]
  | toChkComm d => simp [allDownRConts, mem_allBitsExact d]
  | toChkCommNext d idx =>
      simp only [allDownRConts, List.mem_append, List.mem_flatMap, List.mem_map]
      left; right
      exact ⟨d, mem_allBitsExact d, idx, mem_allFins idx, rfl⟩
  | toAppendFld rem => simp [allDownRConts, mem_allBitsLe rem]

def allOpenStates : List OpenState :=
  [.pf0, .pf1, .pf2, .pfAbortA, .pf3, .pf4, .pf5, .pf6, .pfAbortB, .pf7,
   .pf8 false, .pf8 true, .pf9 false, .pf9 true, .pfDone false, .pfDone true,
   .back2_1, .back2_0] ++
  (allFins 5).map .leftArity ++
  (allFins 5).map .rightArity

theorem mem_allOpenStates (s : OpenState) : s ∈ allOpenStates := by
  cases s with
  | pf0 | pf1 | pf2 | pfAbortA | pf3 | pf4 | pf5 | pf6 | pfAbortB | pf7
  | back2_1 | back2_0 => simp [allOpenStates]
  | pf8 b | pf9 b | pfDone b => cases b <;> simp [allOpenStates]
  | leftArity d => simp [allOpenStates, mem_allFins d]
  | rightArity d => simp [allOpenStates, mem_allFins d]

def allEulerStates : List EulerState :=
  [.abortToRoot, .eulerFromLeft, .eulerFromRight, .climbToRedex2, .climbToRedex1, .contractRedex] ++
  (allFins 4).map .eulerSpine

theorem mem_allEulerStates (s : EulerState) : s ∈ allEulerStates := by
  cases s with
  | abortToRoot | eulerFromLeft | eulerFromRight | climbToRedex2 | climbToRedex1 | contractRedex =>
      simp [allEulerStates]
  | eulerSpine d => simp [allEulerStates, mem_allFins d]

/-- Complete explicit finite list of all `Control` states. -/
def allControls : List Control :=
  [.init] ++
  allSfStates.map .sf ++
  allUpConts.map .up1 ++
  (allUpConts.flatMap fun u => [Control.upDone u false, Control.upDone u true]) ++
  allDownLConts.map .downL1 ++
  allDownLConts.map .downLDone ++
  allDownRConts.map .downR1 ++
  allDownRConts.map .downR2 ++
  allDownRConts.map .downRDone ++
  allHubCheckConts.map .hubChk1 ++
  (allHubCheckConts.flatMap fun h => [Control.hubChkDone h false, Control.hubChkDone h true]) ++
  allOpenStates.map .openSub ++
  allEulerStates.map .euler

/-- Every `c : Control` belongs to the explicit finite list `allControls`. -/
theorem mem_allControls (c : Control) : c ∈ allControls := by
  cases c with
  | init => simp [allControls]
  | sf s => simp [allControls, mem_allSfStates s]
  | up1 u => simp [allControls, mem_allUpConts u]
  | upDone u b =>
      simp only [allControls, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; left; left; left; left; right
      refine ⟨u, mem_allUpConts u, ?_⟩
      cases b <;> simp
  | downL1 d => simp [allControls, mem_allDownLConts d]
  | downLDone d => simp [allControls, mem_allDownLConts d]
  | downR1 d => simp [allControls, mem_allDownRConts d]
  | downR2 d => simp [allControls, mem_allDownRConts d]
  | downRDone d => simp [allControls, mem_allDownRConts d]
  | hubChk1 h => simp [allControls, mem_allHubCheckConts h]
  | hubChkDone h b =>
      simp only [allControls, List.mem_append, List.mem_flatMap]
      left; left; right
      refine ⟨h, mem_allHubCheckConts h, ?_⟩
      cases b <;> simp
  | openSub s => simp [allControls, mem_allOpenStates s]
  | euler s => simp [allControls, mem_allEulerStates s]


/-! ### Primitive Transition Function `step : Control → Obs → Action Control` -/

def nextEulerDepth (d : Fin 4) : Fin 4 :=
  if h : d.val + 1 < 4 then ⟨d.val + 1, h⟩ else ⟨3, by decide⟩

def stepEuler : EulerState → Obs → Action Control
  | .abortToRoot, (nk, .root) =>
      match nk with
      | .isApp => .moveLeft (.euler (.eulerSpine ⟨1, by decide⟩))
      | .isS => .reportNormal
  | .abortToRoot, (_, _) => .moveUp (.euler .abortToRoot)
  | .eulerSpine d, (.isApp, _) =>
      .moveLeft (.euler (.eulerSpine (nextEulerDepth d)))
  | .eulerSpine d, (.isS, inc) =>
      if d.val == 3 then .moveUp (.euler .climbToRedex2)
      else match inc with
        | .root => .reportNormal
        | .fromLeft => .moveUp (.euler .eulerFromLeft)
        | .fromRight => .moveUp (.euler .eulerFromRight)
  | .eulerFromLeft, _ => .moveRight (.euler (.eulerSpine ⟨0, by decide⟩))
  | .eulerFromRight, (_, inc) =>
      match inc with
      | .root => .reportNormal
      | .fromLeft => .moveUp (.euler .eulerFromLeft)
      | .fromRight => .moveUp (.euler .eulerFromRight)
  | .climbToRedex2, _ => .moveUp (.euler .climbToRedex1)
  | .climbToRedex1, _ => .moveUp (.euler .contractRedex)
  | .contractRedex, _ => .contractFocus

def startAbort (obs : Obs) : Action Control :=
  stepEuler .abortToRoot obs

def stepOpen : OpenState → Obs → Action Control
  | .pf0, (.isApp, _) => .moveLeft (.openSub .pf1)
  | .pf0, (.isS, inc) =>
      -- `plainFrameObs` is false on a leaf, and `arityFuel 5` on a leaf is 0 -> abort!
      startAbort (.isS, inc)
  | .pf1, (.isApp, _) => .moveLeft (.openSub .pf2)
  | .pf1, (.isS, _) => .moveUp (.openSub (.pfDone false))
  | .pf2, (.isS, _) => .moveUp (.openSub .pf3)
  | .pf2, (.isApp, _) => .moveUp (.openSub .pfAbortA)
  | .pfAbortA, _ => .moveUp (.openSub (.pfDone false))
  | .pf3, _ => .moveUp (.openSub .pf4)
  | .pf4, _ => .moveRight (.openSub .pf5)
  | .pf5, (.isApp, _) => .moveLeft (.openSub .pf6)
  | .pf5, (.isS, _) => .moveUp (.openSub (.pfDone false))
  | .pf6, (.isApp, _) => .moveLeft (.openSub .pf7)
  | .pf6, (.isS, _) => .moveUp (.openSub .pfAbortB)
  | .pfAbortB, _ => .moveUp (.openSub (.pfDone false))
  | .pf7, (nk, _) => .moveUp (.openSub (.pf8 (nk == .isS)))
  | .pf8 ok, _ => .moveUp (.openSub (.pf9 ok))
  | .pf9 ok, _ => .moveUp (.openSub (.pfDone ok))
  | .pfDone true, obs => startAbort obs
  | .pfDone false, (.isApp, _) => .moveLeft (.openSub (.leftArity ⟨1, by decide⟩))
  | .pfDone false, (.isS, inc) => startAbort (.isS, inc)
  | .leftArity d, (.isApp, inc) =>
      if h : d.val + 1 < 5 then .moveLeft (.openSub (.leftArity ⟨d.val + 1, h⟩))
      else startAbort (.isApp, inc)
  | .leftArity d, (.isS, inc) =>
      if d.val == 4 || d.val == 3 then .moveUp (.euler .climbToRedex2)
      else if d.val == 2 then .moveUp (.openSub .back2_1)
      else startAbort (.isS, inc)
  | .back2_1, _ => .moveUp (.openSub .back2_0)
  | .back2_0, _ => .moveRight (.openSub (.rightArity ⟨0, by decide⟩))
  | .rightArity d, (.isApp, inc) =>
      if h : d.val + 1 < 5 then .moveLeft (.openSub (.rightArity ⟨d.val + 1, h⟩))
      else startAbort (.isApp, inc)
  | .rightArity d, (.isS, inc) =>
      if d.val == 4 || d.val == 3 then .moveUp (.euler .climbToRedex2)
      else startAbort (.isS, inc)

def startOpen (obs : Obs) : Action Control :=
  stepOpen .pf0 obs

def startDownL (next : DownLCont) : Action Control :=
  .moveLeft (.downL1 next)

def startDownR (next : DownRCont) : Action Control :=
  .moveRight (.downR1 next)

def startUp (ret : UpCont) : Action Control :=
  .moveUp (.up1 ret)

def startHubChk (ret : HubCheckCont) : Action Control :=
  .moveUp (.hubChk1 ret)

def onCellRead (caller : CellCaller) (cell : Cell8) (obs : Obs) : Action Control :=
  match caller with
  | .seekPending =>
      match cell.status with
      | .movingRight => startDownR (.toPendingRightDest cell)
      | .movingLeft => startUp (.pendingLeftToParent cell)
      | _ => startDownR (.toNextCell false)
  | .seekActive =>
      if cell.status == .active then
        if h : cell.state.val < 132 then
          match fixedBinaryProgram ⟨cell.state.val, h⟩ cell.bit with
          | none => startUp .rewindToHubHalt
          | some inst =>
              match inst.direction with
              | .stay =>
                  startDownL (.toAppendVerEntry (encodeRecord11 ⟨inst.write, .active, inst.next.val⟩))
              | .right =>
                  startDownL (.toAppendVerEntry (encodeRecord11 ⟨inst.write, .movingRight, inst.next.val⟩))
              | .left =>
                  startUp (.activeBoundaryTest cell)
        else startAbort obs
      else startDownR (.toNextCell true)
  | .readDestRight pending =>
      if cell.status == .off then
        startDownL (.toAppendVerEntry (encodeRecord11 ⟨cell.bit, .active, pending.state.val⟩))
      else if cell.status == .active && cell.state == pending.state then
        startUp (.pendingRightBackToSrc pending.bit)
      else startAbort obs
  | .readDestLeft pending =>
      if cell.status == .off then
        startDownL (.toAppendVerEntry (encodeRecord11 ⟨cell.bit, .active, pending.state.val⟩))
      else if cell.status == .active && cell.state == pending.state then
        startDownR (.toPendingLeftBackToSrc (encodeRecord11 ⟨pending.bit, .off, 0⟩))
      else startAbort obs

def onHubChkDone (ret : HubCheckCont) (isHub : Bool) (obs : Obs) : Action Control :=
  match ret with
  | .rewindTapeChk =>
      if isHub then startDownR .toTapePass2
      else startUp .rewindToTape
  | .rewindHaltChk =>
      if isHub then startDownL .toHaltFlagOpen
      else startUp .rewindToHubHalt
  | .activeBoundaryChk cell =>
      if h : cell.state.val < 132 then
        match fixedBinaryProgram ⟨cell.state.val, h⟩ cell.bit with
        | some inst =>
            let st : Status := if isHub then .active else .movingLeft
            startDownR (.toActiveBoundaryBack (encodeRecord11 ⟨inst.write, st, inst.next.val⟩))
        | none => startAbort obs
      else startAbort obs
  | .pendingLeftChk pending =>
      if isHub then startAbort obs
      else startDownL (.toRcStart (.readDestLeft pending))

def onUpDone (ret : UpCont) (fromRight : Bool) (_obs : Obs) : Action Control :=
  match ret with
  | .flagToHub => startDownR .toTapeInit
  | .rfBitValBack caller acc => startDownR (.toRfNext caller acc)
  | .rfClimb caller res rem =>
      if h : rem.val = 0 then
        startUp (.rcAfterRf caller (res.map decodeBits11))
      else
        startUp (.rfClimb caller res ⟨rem.val - 1, by omega⟩)
  | .rcBottomToPrev caller => startUp (.rcSearchTestParent caller)
  | .rcSearchTestParent caller =>
      if fromRight then startDownR (.toRcDone caller defaultCell8)
      else startDownL (.toRcInspect caller)
  | .rcAfterRf caller found =>
      match found with
      | none => startUp (.rcSearchTestParent caller)
      | some cell => startUp (.rcHaveTestParent caller cell)
  | .rcHaveTestParent caller cell =>
      if fromRight then startDownR (.toRcDone caller cell)
      else startUp (.rcHaveTestParent caller cell)
  | .rewindToTape => startHubChk .rewindTapeChk
  | .rewindToHubHalt => startHubChk .rewindHaltChk
  | .activeBoundaryTest cell => startHubChk (.activeBoundaryChk cell)
  | .pendingRightBackToSrc bit =>
      startDownL (.toAppendVerEntry (encodeRecord11 ⟨bit, .off, 0⟩))
  | .pendingLeftToParent pending => startHubChk (.pendingLeftChk pending)
  | .chkCommClimb desired committed rem =>
      if h : rem.val = 0 then
        if committed then startDownL (.toAppendVerNext desired)
        else startDownR (.toAppendFld ⟨desired.val, Nat.le_of_eq desired.property⟩)
      else
        startUp (.chkCommClimb desired committed ⟨rem.val - 1, by omega⟩)
  | .appendFldFlagBack bs => startDownR (.toAppendFld bs)

def onSfDone (ret : StrictFrameCont) (res : Bool) (obs : Obs) : Action Control :=
  match ret with
  | .hubInit =>
      if res then startDownL .toFlagInit else startAbort obs
  | .flagInit =>
      if res then startDownL .toFrontier else startUp .flagToHub
  | .frontierWalk =>
      if res then startDownL .toFrontier else startOpen obs
  | .upCheck u =>
      if res then onUpDone u false obs else .moveUp (.upDone u true)
  | .rfBitFrame caller acc =>
      if hlen : acc.val.length = 11 then
        let out : Option Bits11 := if res then some ⟨acc.val, hlen⟩ else none
        startUp (.rfClimb caller out ⟨11, by decide⟩)
      else
        have hlt : acc.val.length < 11 := Nat.lt_of_le_of_ne acc.property hlen
        if res then startDownL (.toRfBitVal caller acc)
        else startUp (.rfClimb caller none ⟨acc.val.length, by omega⟩)
  | .rfBitVal caller acc =>
      if hlt : acc.val.length < 11 then
        startUp (.rfBitValBack caller (pushBit11 acc res hlt))
      else startAbort obs
  | .rcDown caller =>
      if res then startDownL (.toRcDown caller) else startUp (.rcBottomToPrev caller)
  | .seekCell passIsActive =>
      if res then
        startDownL (.toRcStart (if passIsActive then .seekActive else .seekPending))
      else
        if passIsActive then startAbort obs else startUp .rewindToTape
  | .pendingRightDest pending =>
      if res then startDownL (.toRcStart (.readDestRight pending))
      else startOpen obs
  | .appendVer desired =>
      if res then startDownR (.toChkComm desired)
      else startOpen obs
  | .chkComm desired idx =>
      if !res then startUp (.chkCommClimb desired false idx)
      else if hnext : idx.val + 1 < 12 then
        startDownR (.toChkCommNext desired ⟨idx.val + 1, hnext⟩)
      else
        startUp (.chkCommClimb desired true idx)
  | .appendFldNode remBits =>
      match remBits.val, remBits.property with
      | [], _ =>
          if res then startAbort obs else startOpen obs
      | b :: bs, hle =>
          have hbs : bs.length ≤ 11 := by simp at hle; omega
          if !res then startOpen obs
          else if b then startDownL (.toAppendFldFlag ⟨bs, hbs⟩)
          else startDownR (.toAppendFld ⟨bs, hbs⟩)
  | .appendFldFlag bs =>
      if res then startUp (.appendFldFlagBack bs)
      else startOpen obs

def stepSf : SfState → Obs → Action Control
  | .sf0 ret, (.isApp, _) => .moveLeft (.sf (.sf1 ret))
  | .sf0 ret, (.isS, inc) => onSfDone ret false (.isS, inc)
  | .sf1 ret, (.isApp, _) => .moveLeft (.sf (.sf2 ret))
  | .sf1 ret, (.isS, _) => .moveUp (.sf (.sfDone ret false))
  | .sf2 ret, (.isS, _) => .moveUp (.sf (.sf3 ret))
  | .sf2 ret, (.isApp, _) => .moveUp (.sf (.sfAbortA ret))
  | .sfAbortA ret, _ => .moveUp (.sf (.sfDone ret false))
  | .sf3 ret, _ => .moveUp (.sf (.sf4 ret))
  | .sf4 ret, _ => .moveRight (.sf (.sf5 ret))
  | .sf5 ret, (.isApp, _) => .moveLeft (.sf (.sf6 ret))
  | .sf5 ret, (.isS, _) => .moveUp (.sf (.sfDone ret false))
  | .sf6 ret, (.isApp, _) => .moveLeft (.sf (.sf7 ret))
  | .sf6 ret, (.isS, _) => .moveUp (.sf (.sfAbortB ret))
  | .sfAbortB ret, _ => .moveUp (.sf (.sfDone ret false))
  | .sf7 ret, (.isS, _) => .moveUp (.sf (.sf8 ret))
  | .sf7 ret, (.isApp, _) => .moveUp (.sf (.sfJUp1 ret false))
  | .sf8 ret, _ => .moveUp (.sf (.sfAtB ret))
  | .sfAtB ret, _ => .moveRight (.sf (.sfJ0 ret))
  | .sfJ0 ret, (.isS, _) => .moveUp (.sf (.sfUpFromJ ret true))
  | .sfJ0 ret, (.isApp, _) => .moveLeft (.sf (.sfJ1 ret))
  | .sfJ1 ret, (.isS, _) => .moveUp (.sf (.sfJUp1 ret true))
  | .sfJ1 ret, (.isApp, _) => .moveLeft (.sf (.sfJ2 ret))
  | .sfJ2 ret, (nk, _) => .moveUp (.sf (.sfJUp2 ret (nk == .isApp)))
  | .sfJUp2 ret ok, _ => .moveUp (.sf (.sfJUp1 ret ok))
  | .sfJUp1 ret ok, _ => .moveUp (.sf (.sfUpFromJ ret ok))
  | .sfUpFromJ ret ok, _ => .moveUp (.sf (.sfDone ret ok))
  | .sfDone ret res, obs => onSfDone ret res obs

def startSf (ret : StrictFrameCont) (obs : Obs) : Action Control :=
  stepSf (.sf0 ret) obs

def onDownLDone (next : DownLCont) (obs : Obs) : Action Control :=
  match next with
  | .toFlagInit => startSf .flagInit obs
  | .toFrontier => startSf .frontierWalk obs
  | .toRcStart caller => startSf (.rcDown caller) obs
  | .toRcDown caller => startSf (.rcDown caller) obs
  | .toRcInspect caller => startDownR (.toRfEntry caller)
  | .toRfBitVal caller acc => startSf (.rfBitVal caller acc) obs
  | .toHaltFlagOpen => startOpen obs
  | .toAppendVerEntry desired => startSf (.appendVer desired) obs
  | .toAppendVerNext desired => startSf (.appendVer desired) obs
  | .toAppendFldFlag bs => startSf (.appendFldFlag bs) obs

def onDownRDone (next : DownRCont) (obs : Obs) : Action Control :=
  match next with
  | .toTapeInit => startSf (.seekCell false) obs
  | .toTapePass2 => startSf (.seekCell true) obs
  | .toNextCell passIsActive => startSf (.seekCell passIsActive) obs
  | .toRfEntry caller => startSf (.rfBitFrame caller ⟨[], Nat.zero_le 11⟩) obs
  | .toRfNext caller acc => startSf (.rfBitFrame caller acc) obs
  | .toRcDone caller cell => onCellRead caller cell obs
  | .toActiveBoundaryBack desired => startDownL (.toAppendVerEntry desired)
  | .toPendingRightDest pending => startSf (.pendingRightDest pending) obs
  | .toPendingLeftBackToSrc desired => startDownL (.toAppendVerEntry desired)
  | .toChkComm desired => startSf (.chkComm desired ⟨0, by decide⟩) obs
  | .toChkCommNext desired idx => startSf (.chkComm desired idx) obs
  | .toAppendFld remBits => startSf (.appendFldNode remBits) obs

/-- The primitive finite-state tree-walking controller transition table. -/
def step : Control → Obs → Action Control
  | .init, (.isApp, _) => .moveRight (.sf (.sf0 .hubInit))
  | .init, (.isS, _) => .reportNormal
  | .sf s, obs => stepSf s obs
  | .up1 ret, _ => .moveUp (.sf (.sf0 (.upCheck ret)))
  | .upDone ret fromRight, obs => onUpDone ret fromRight obs
  | .downL1 next, _ => .moveRight (.downLDone next)
  | .downLDone next, obs => onDownLDone next obs
  | .downR1 next, _ => .moveLeft (.downR2 next)
  | .downR2 next, _ => .moveRight (.downRDone next)
  | .downRDone next, obs => onDownRDone next obs
  | .hubChk1 ret, (_, .root) => .moveRight (.hubChkDone ret true)
  | .hubChk1 ret, (_, .fromLeft) => .moveRight (.hubChkDone ret false)
  | .hubChk1 _, (_, .fromRight) => .moveUp (.euler .abortToRoot)
  | .hubChkDone ret isHub, obs => onHubChkDone ret isHub obs
  | .openSub s, obs => stepOpen s obs
  | .euler s, obs => stepEuler s obs


/-! ## Section 3: Execution Semantics, Unit Inter-Invocation State, & CPS Composition -/

inductive WalkState where
  | running (c : Control) (cur : Cursor)
  | done (res : InvokeResult)
  | stuck
  deriving DecidableEq, Repr

def applyAction (cur : Cursor) : Action Control → WalkState
  | .moveLeft c' =>
      match cur.focus with
      | .app l r => .running c' ⟨l, .left r :: cur.crumbs⟩
      | _ => .stuck
  | .moveRight c' =>
      match cur.focus with
      | .app l r => .running c' ⟨r, .right l :: cur.crumbs⟩
      | _ => .stuck
  | .moveUp c' =>
      match cur.crumbs with
      | .left r :: cs => .running c' ⟨cur.focus ⋅ r, cs⟩
      | .right l :: cs => .running c' ⟨l ⋅ cur.focus, cs⟩
      | [] => .stuck
  | .contractFocus =>
      match contractRoot cur.focus with
      | some next => .done (.contracted (rebuild { cur with focus := next }))
      | none => .done .normal
  | .reportNormal => .done .normal

def microstep (c : Control) (cur : Cursor) : WalkState :=
  applyAction cur (step c (observe cur))

def execTicks : Nat → Control → Cursor → WalkState
  | 0, c, cur => .running c cur
  | n + 1, c, cur =>
      match microstep c cur with
      | .running c' cur' => execTicks n c' cur'
      | .done res => .done res
      | .stuck => .stuck

def runTicks (fuel : Nat) (c : Control) (cur : Cursor) : Option InvokeResult :=
  match execTicks fuel c cur with
  | .done res => some res
  | _ => none

/-- Explicit linear microtick constant for all-input termination. -/
def walkerConst : Nat := 3500

def walkerBound (t : Term) : Nat :=
  walkerConst * (leaves t + 1)

/-- Root-restarted controller invocation: always begins from `(initControl, rootCursor t)`. -/
def invoke (t : Term) : InvokeResult :=
  (runTicks (walkerBound t) initControl (rootCursor t)).getD .normal

/-- **(a) Unit Inter-Invocation State**: `invoke` depends solely on `execTicks` from
    `(initControl, rootCursor t)` with zero persistent memory across contractions. -/
theorem invoke_unit_initial_state (t : Term) :
    invoke t = (runTicks (walkerBound t) initControl (rootCursor t)).getD .normal := rfl

theorem execTicks_add_running {k1 : Nat} (k2 : Nat) {c0 c1 : Control} {cur0 cur1 : Cursor}
    (h1 : execTicks k1 c0 cur0 = .running c1 cur1) :
    execTicks (k1 + k2) c0 cur0 = execTicks k2 c1 cur1 := by
  induction k1 generalizing c0 cur0 with
  | zero =>
      simp only [execTicks, WalkState.running.injEq] at h1
      rcases h1 with ⟨rfl, rfl⟩
      simp
  | succ n ih =>
      simp only [execTicks] at h1
      cases hm : microstep c0 cur0 with
      | running cm curm =>
          rw [hm] at h1
          have hadd : n + 1 + k2 = (n + k2) + 1 := by omega
          rw [hadd]
          simp only [execTicks, hm]
          exact ih h1
      | done _ => rw [hm] at h1; cases h1
      | stuck => rw [hm] at h1; cases h1

theorem execTicks_add_done {k1 : Nat} (k2 : Nat) {c0 : Control} {cur0 : Cursor} {res : InvokeResult}
    (h1 : execTicks k1 c0 cur0 = .done res) :
    execTicks (k1 + k2) c0 cur0 = .done res := by
  induction k1 generalizing c0 cur0 with
  | zero => simp [execTicks] at h1
  | succ n ih =>
      simp only [execTicks] at h1
      have hadd : n + 1 + k2 = (n + k2) + 1 := by omega
      rw [hadd]
      cases hm : microstep c0 cur0 with
      | running cm curm =>
          rw [hm] at h1
          simp only [execTicks, hm]
          exact ih h1
      | done r =>
          rw [hm] at h1
          simp only [execTicks, hm, h1]
      | stuck => rw [hm] at h1; cases h1

theorem execTicks_done_unique {k1 k2 : Nat} {c : Control} {cur : Cursor} {r1 r2 : InvokeResult}
    (h1 : execTicks k1 c cur = .done r1) (h2 : execTicks k2 c cur = .done r2) :
    r1 = r2 := by
  have ha := execTicks_add_done k2 h1
  have hb := execTicks_add_done k1 h2
  have hcomm : k1 + k2 = k2 + k1 := Nat.add_comm k1 k2
  rw [hcomm, hb] at ha
  injection ha with h
  exact h.symm

theorem applyAction_preserves_rebuild (cur : Cursor) (act : Action Control)
    {c' : Control} {cur' : Cursor}
    (h : applyAction cur act = .running c' cur') :
    rebuild cur = rebuild cur' := by
  cases act with
  | moveLeft _ =>
      cases hf : cur.focus with
      | app l r =>
          simp only [applyAction, hf, WalkState.running.injEq] at h
          rcases h with ⟨_, rfl⟩
          simp [rebuild, rebuildWith, hf]
      | s => simp [applyAction, hf] at h
      | var _ => simp [applyAction, hf] at h
  | moveRight _ =>
      cases hf : cur.focus with
      | app l r =>
          simp only [applyAction, hf, WalkState.running.injEq] at h
          rcases h with ⟨_, rfl⟩
          simp [rebuild, rebuildWith, hf]
      | s => simp [applyAction, hf] at h
      | var _ => simp [applyAction, hf] at h
  | moveUp _ =>
      cases hcs : cur.crumbs with
      | nil => simp [applyAction, hcs] at h
      | cons cr rest =>
          cases cr with
          | left r =>
              simp only [applyAction, hcs, WalkState.running.injEq] at h
              rcases h with ⟨_, rfl⟩
              simp [rebuild, rebuildWith, hcs]
          | right l =>
              simp only [applyAction, hcs, WalkState.running.injEq] at h
              rcases h with ⟨_, rfl⟩
              simp [rebuild, rebuildWith, hcs]
  | contractFocus =>
      cases hc : contractRoot cur.focus <;> simp [applyAction, hc] at h
  | reportNormal => simp [applyAction] at h

theorem microstep_preserves_rebuild {c1 c2 : Control} {cur1 cur2 : Cursor}
    (h : microstep c1 cur1 = .running c2 cur2) :
    rebuild cur1 = rebuild cur2 :=
  applyAction_preserves_rebuild cur1 _ h

theorem execTicks_preserves_rebuild {k : Nat} {c1 c2 : Control} {cur1 cur2 : Cursor}
    (h : execTicks k c1 cur1 = .running c2 cur2) :
    rebuild cur1 = rebuild cur2 := by
  induction k generalizing c1 cur1 with
  | zero =>
      simp only [execTicks, WalkState.running.injEq] at h
      rcases h with ⟨_, rfl⟩
      rfl
  | succ n ih =>
      simp only [execTicks] at h
      cases hm : microstep c1 cur1 with
      | running cm curm =>
          rw [hm] at h
          exact (microstep_preserves_rebuild hm).trans (ih h)
      | done _ => rw [hm] at h; cases h
      | stuck => rw [hm] at h; cases h

/-- Termination within `B` positive microticks without getting `.stuck`. -/
def TerminatesWithin (B : Nat) (c : Control) (cur : Cursor) (res : InvokeResult) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ B ∧ execTicks k c cur = .done res

theorem terminatesWithin_mono {B1 B2 : Nat} {c : Control} {cur : Cursor} {res : InvokeResult}
    (hle : B1 ≤ B2) (h : TerminatesWithin B1 c cur res) :
    TerminatesWithin B2 c cur res := by
  obtain ⟨k, hlo, hhi, hex⟩ := h
  exact ⟨k, hlo, Nat.le_trans hhi hle, hex⟩

/-- Soundness predicate for pure-S single-contraction and normality. -/
def ValidResult (root : Term) (res : InvokeResult) : Prop :=
  isPureS root = true →
    match res with
    | .normal => ¬ ∃ t', Step root t'
    | .contracted t' => Step root t'

def ValidTermination (B : Nat) (c : Control) (cur : Cursor) : Prop :=
  ∃ res, TerminatesWithin B c cur res ∧ ValidResult (rebuild cur) res

theorem validTermination_mono {B1 B2 : Nat} {c : Control} {cur : Cursor}
    (hle : B1 ≤ B2) (h : ValidTermination B1 c cur) :
    ValidTermination B2 c cur := by
  obtain ⟨res, ht, hv⟩ := h
  exact ⟨res, terminatesWithin_mono hle ht, hv⟩

/-- Compositional subroutine relation supporting both 0-tick dispatch aliases and `k ≥ 1` moves. -/
def StepsTo (B : Nat) (c1 : Control) (cur1 : Cursor) (c2 : Control) (cur2 : Cursor) : Prop :=
  rebuild cur1 = rebuild cur2 ∧
  ∀ {B_rest : Nat} {res : InvokeResult},
    TerminatesWithin B_rest c2 cur2 res → TerminatesWithin (B + B_rest) c1 cur1 res

theorem StepsTo.refl (c : Control) (cur : Cursor) : StepsTo 0 c cur c cur := by
  refine ⟨rfl, ?_⟩
  intro B_rest res h
  simpa using h

theorem StepsTo.trans {B1 B2 : Nat} {c1 c2 c3 : Control} {cur1 cur2 cur3 : Cursor}
    (h1 : StepsTo B1 c1 cur1 c2 cur2) (h2 : StepsTo B2 c2 cur2 c3 cur3) :
    StepsTo (B1 + B2) c1 cur1 c3 cur3 := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro B_rest res ht
  have ht2 := h1.2 (h2.2 ht)
  obtain ⟨k, hlo, hhi, hex⟩ := ht2
  exact ⟨k, hlo, by omega, hex⟩

theorem StepsTo.mono {B1 B2 : Nat} {c1 c2 : Control} {cur1 cur2 : Cursor}
    (hle : B1 ≤ B2) (h : StepsTo B1 c1 cur1 c2 cur2) :
    StepsTo B2 c1 cur1 c2 cur2 := by
  refine ⟨h.1, ?_⟩
  intro B_rest res ht
  exact terminatesWithin_mono (by omega) (h.2 ht)

theorem StepsTo.of_alias {c1 c2 : Control} {cur : Cursor}
    (h : microstep c1 cur = microstep c2 cur) :
    StepsTo 0 c1 cur c2 cur := by
  refine ⟨rfl, ?_⟩
  intro B_rest res ⟨k, hlo, hhi, hex⟩
  cases k with
  | zero => exact False.elim (by omega)
  | succ m =>
      refine ⟨m + 1, by omega, by omega, ?_⟩
      simp only [execTicks] at hex ⊢
      rw [h]
      exact hex

theorem StepsTo.of_step {c1 c2 : Control} {cur1 cur2 : Cursor}
    (hm : microstep c1 cur1 = .running c2 cur2) :
    StepsTo 1 c1 cur1 c2 cur2 := by
  refine ⟨microstep_preserves_rebuild hm, ?_⟩
  intro B_rest res ⟨k, hlo, hhi, hex⟩
  refine ⟨1 + k, by omega, by omega, ?_⟩
  have h1 : execTicks 1 c1 cur1 = .running c2 cur2 := by
    simp [execTicks, hm]
  rw [execTicks_add_running k h1]
  exact hex

theorem StepsTo.of_exec {k B : Nat} {c1 c2 : Control} {cur1 cur2 : Cursor}
    (hlo : 1 ≤ k) (hhi : k ≤ B)
    (hex : execTicks k c1 cur1 = .running c2 cur2) :
    StepsTo B c1 cur1 c2 cur2 := by
  refine ⟨execTicks_preserves_rebuild hex, ?_⟩
  intro B_rest res ⟨k2, hk2_lo, hk2_hi, hex2⟩
  refine ⟨k + k2, by omega, by omega, ?_⟩
  rw [execTicks_add_running k2 hex]
  exact hex2

theorem StepsTo.toValidTermination {B1 B2 : Nat} {c1 c2 : Control} {cur1 cur2 : Cursor}
    (h1 : StepsTo B1 c1 cur1 c2 cur2) (h2 : ValidTermination B2 c2 cur2) :
    ValidTermination (B1 + B2) c1 cur1 := by
  obtain ⟨res, ht, hv⟩ := h2
  rw [← h1.1] at hv
  exact ⟨res, h1.2 ht, hv⟩

theorem rebuild_left (l r : Term) (cs : List Crumb) :
    rebuild ⟨l, .left r :: cs⟩ = rebuild ⟨l ⋅ r, cs⟩ := rfl

theorem rebuild_right (l r : Term) (cs : List Crumb) :
    rebuild ⟨r, .right l :: cs⟩ = rebuild ⟨l ⋅ r, cs⟩ := rfl


/-! ## Section 4: Redex-Climb Gadget, `.abortToRoot`, & Euler-Tour Leftmost-Redex Search -/

/-- Climbing 2 `.left` crumbs from `(u ⋅ x)` where `nodeKindOf u = .isS` and contracting
    terminates in 3 microticks and contracts a genuine S-redex on pure-S terms. -/
theorem climbToRedex2_valid (u x y z : Term) (cs : List Crumb)
    (hu : nodeKindOf u = .isS) :
    ValidTermination 3 (.euler .climbToRedex2) ⟨u ⋅ x, .left y :: .left z :: cs⟩ := by
  cases huTerm : u with
  | app _ _ => rw [huTerm] at hu; simp [nodeKindOf] at hu
  | s =>
      let out := rebuild ⟨(x ⋅ z) ⋅ (y ⋅ z), cs⟩
      have hex : execTicks 3 (.euler .climbToRedex2) ⟨.s ⋅ x, .left y :: .left z :: cs⟩ =
          .done (.contracted out) := by
        simp [execTicks, microstep, step, stepEuler, applyAction, contractRoot, out]
      refine ⟨.contracted out, ⟨3, by omega, by omega, hex⟩, ?_⟩
      intro _
      have hdir : DirectedStep (crumbsPath cs)
          (rebuild ⟨.s ⋅ x ⋅ y ⋅ z, cs⟩) (rebuild ⟨(x ⋅ z) ⋅ (y ⋅ z), cs⟩) :=
        directedStep_rebuild_root ⟨.s ⋅ x ⋅ y ⋅ z, cs⟩ rfl
      exact directed_step_is_native hdir
  | var n =>
      have hex : execTicks 3 (.euler .climbToRedex2) ⟨.var n ⋅ x, .left y :: .left z :: cs⟩ =
          .done .normal := by
        simp [execTicks, microstep, step, stepEuler, applyAction, contractRoot]
      refine ⟨.normal, ⟨3, by omega, by omega, hex⟩, ?_⟩
      intro hpure
      have hfocusPure := isPureS_focus_of_rebuild (cur := ⟨.var n ⋅ x, .left y :: .left z :: cs⟩) hpure
      simp [isPureS] at hfocusPure

theorem abortToRoot_steps (cur : Cursor) :
    StepsTo cur.crumbs.length (.euler .abortToRoot) cur
      (.euler (.eulerSpine ⟨0, by decide⟩)) (rootCursor (rebuild cur)) := by
  rcases cur with ⟨f, cs⟩
  induction cs generalizing f with
  | nil =>
      apply StepsTo.of_alias
      cases f <;> rfl
  | cons c rest ih =>
      cases c with
      | left r =>
          have h1 : StepsTo 1 (.euler .abortToRoot) ⟨f, .left r :: rest⟩
              (.euler .abortToRoot) ⟨f ⋅ r, rest⟩ :=
            StepsTo.of_step rfl
          have h2 := ih (f ⋅ r)
          have heq : 1 + rest.length = (Crumb.left r :: rest).length := by simp; omega
          rw [← heq]
          exact StepsTo.trans h1 h2
      | right l =>
          have h1 : StepsTo 1 (.euler .abortToRoot) ⟨f, .right l :: rest⟩
              (.euler .abortToRoot) ⟨l ⋅ f, rest⟩ :=
            StepsTo.of_step rfl
          have h2 := ih (l ⋅ f)
          have heq : 1 + rest.length = (Crumb.right l :: rest).length := by simp; omega
          rw [← heq]
          exact StepsTo.trans h1 h2

def leftStreak : List Crumb → Nat
  | .left _ :: cs => min 3 (1 + leftStreak cs)
  | _ => 0

theorem leftStreak_le_3 (cs : List Crumb) : leftStreak cs ≤ 3 := by
  cases cs with
  | nil => exact Nat.zero_le 3
  | cons c rest =>
      cases c <;> simp [leftStreak] <;> omega

theorem leftStreak_eq_3_decomp {cs : List Crumb} (h : leftStreak cs = 3) :
    ∃ x y z cs', cs = .left x :: .left y :: .left z :: cs' := by
  match cs with
  | [] => simp [leftStreak] at h
  | .right _ :: _ => simp [leftStreak] at h
  | .left x :: [] => simp [leftStreak] at h
  | .left x :: .right _ :: _ => simp [leftStreak] at h
  | .left x :: .left y :: [] => simp [leftStreak] at h
  | .left x :: .left y :: .right _ :: _ => simp [leftStreak] at h
  | .left x :: .left y :: .left z :: cs' => exact ⟨x, y, z, cs', rfl⟩

theorem nextEulerDepth_eq_leftStreak (d : Fin 4) (r : Term) (cs : List Crumb)
    (hd : d.val = leftStreak cs) :
    (nextEulerDepth d).val = leftStreak (.left r :: cs) := by
  unfold nextEulerDepth leftStreak
  rw [← hd]
  if h : d.val + 1 < 4 then
    simp [h]
    omega
  else
    simp [h]
    omega

def leftArity : Term → Nat
  | .app l _ => 1 + leftArity l
  | _ => 0

theorem no_step_of_subterms {l r : Term}
    (hl : ¬ ∃ l', Step l l') (hr : ¬ ∃ r', Step r r')
    (har : leftArity (l ⋅ r) < 3) :
    ¬ ∃ u', Step (l ⋅ r) u' := by
  intro ⟨u', hs⟩
  cases hs with
  | root x y z =>
      simp [leftArity, S] at har
  | left hsl => exact hl ⟨_, hsl⟩
  | right hsr => exact hr ⟨_, hsr⟩

/-- Post-state of finishing a normal subtree `u` during the Euler tour. -/
def eulerExitAfter (u : Term) (cs : List Crumb) : WalkState :=
  match cs with
  | [] => .done .normal
  | .left r :: cs' => .running (.euler .eulerFromLeft) ⟨u ⋅ r, cs'⟩
  | .right l :: cs' => .running (.euler .eulerFromRight) ⟨l ⋅ u, cs'⟩

theorem eulerFromRight_exec1 (u : Term) (cs : List Crumb) :
    execTicks 1 (.euler .eulerFromRight) ⟨u, cs⟩ = eulerExitAfter u cs := by
  cases cs with
  | nil => rfl
  | cons c _ =>
      cases c <;> rfl

/-- Core structural specification of the 8-state Euler-tour leftmost-redex search:
    on any subtree `u` with `d.val = leftStreak cs`, either:
    1. `ValidTermination (4 * leaves u) (.euler (.eulerSpine d)) ⟨u, cs⟩` (contracts a genuine redex on pure-S); or
    2. `leftArity u + d.val < 3 ∧ (¬ ∃ u', Step u u')` and in `≤ 4 * leaves u` positive ticks
       it reaches `eulerExitAfter u cs`. -/
theorem eulerSpine_spec (u : Term) :
    ∀ (cs : List Crumb) (d : Fin 4),
      d.val = leftStreak cs →
      ValidTermination (4 * leaves u) (.euler (.eulerSpine d)) ⟨u, cs⟩ ∨
      (leftArity u + d.val < 3 ∧ (¬ ∃ u', Step u u') ∧
        ∃ k, 1 ≤ k ∧ k + 3 ≤ 4 * leaves u ∧
          execTicks k (.euler (.eulerSpine d)) ⟨u, cs⟩ = eulerExitAfter u cs) := by
  induction u with
  | s =>
      intro cs d hd
      if h3 : d.val == 3 then
        left
        have hd3 : d.val = 3 := of_decide_eq_true h3
        obtain ⟨x, y, z, cs', hcs⟩ := leftStreak_eq_3_decomp (hd.symm.trans hd3)
        subst cs
        have hs1 : StepsTo 1 (.euler (.eulerSpine d)) ⟨.s, .left x :: .left y :: .left z :: cs'⟩
            (.euler .climbToRedex2) ⟨.s ⋅ x, .left y :: .left z :: cs'⟩ := by
          apply StepsTo.of_step
          simp [microstep, step, stepEuler, observe, nodeKindOf, incomingOf, h3, applyAction]
        exact validTermination_mono (by simp [leaves])
          (StepsTo.toValidTermination hs1 (climbToRedex2_valid .s x y z cs' rfl))
      else
        right
        have hlt3 : d.val < 3 := by
          have := d.isLt
          have hne : d.val ≠ 3 := of_decide_eq_false (Bool.eq_false_iff.mpr h3)
          omega
        refine ⟨by simp [leftArity]; omega, ?_, 1, by omega, by simp [leaves], ?_⟩
        · intro ⟨_, hs⟩; cases hs
        · cases cs with
          | nil => simp [execTicks, microstep, step, stepEuler, observe, nodeKindOf, incomingOf, h3, applyAction, eulerExitAfter]
          | cons c rest =>
              cases c <;>
                simp [execTicks, microstep, step, stepEuler, observe, nodeKindOf, incomingOf, h3, applyAction, eulerExitAfter]
  | var n =>
      intro cs d hd
      if h3 : d.val == 3 then
        left
        have hd3 : d.val = 3 := of_decide_eq_true h3
        obtain ⟨x, y, z, cs', hcs⟩ := leftStreak_eq_3_decomp (hd.symm.trans hd3)
        subst cs
        have hs1 : StepsTo 1 (.euler (.eulerSpine d)) ⟨.var n, .left x :: .left y :: .left z :: cs'⟩
            (.euler .climbToRedex2) ⟨.var n ⋅ x, .left y :: .left z :: cs'⟩ := by
          apply StepsTo.of_step
          simp [microstep, step, stepEuler, observe, nodeKindOf, incomingOf, h3, applyAction]
        exact validTermination_mono (by simp [leaves])
          (StepsTo.toValidTermination hs1 (climbToRedex2_valid (.var n) x y z cs' rfl))
      else
        right
        have hlt3 : d.val < 3 := by
          have := d.isLt
          have hne : d.val ≠ 3 := of_decide_eq_false (Bool.eq_false_iff.mpr h3)
          omega
        refine ⟨by simp [leftArity]; omega, ?_, 1, by omega, by simp [leaves], ?_⟩
        · intro ⟨_, hs⟩; cases hs
        · cases cs with
          | nil => simp [execTicks, microstep, step, stepEuler, observe, nodeKindOf, incomingOf, h3, applyAction, eulerExitAfter]
          | cons c rest =>
              cases c <;>
                simp [execTicks, microstep, step, stepEuler, observe, nodeKindOf, incomingOf, h3, applyAction, eulerExitAfter]
  | app l r ihl ihr =>
      intro cs d hd
      let dL := nextEulerDepth d
      have hdL : dL.val = leftStreak (.left r :: cs) := nextEulerDepth_eq_leftStreak d r cs hd
      have hmoveL : microstep (.euler (.eulerSpine d)) ⟨l ⋅ r, cs⟩ =
          .running (.euler (.eulerSpine dL)) ⟨l, .left r :: cs⟩ := rfl
      cases ihl (.left r :: cs) dL hdL with
      | inl hvtL =>
          left
          have hsL : StepsTo 1 (.euler (.eulerSpine d)) ⟨l ⋅ r, cs⟩
              (.euler (.eulerSpine dL)) ⟨l, .left r :: cs⟩ :=
            StepsTo.of_step hmoveL
          have hvt1 := StepsTo.toValidTermination hsL hvtL
          have hle : 1 + 4 * leaves l ≤ 4 * leaves (l ⋅ r) := by
            have hrp := leaves_pos r
            simp only [leaves]
            omega
          exact validTermination_mono hle hvt1
      | inr hnormL =>
          rcases hnormL with ⟨harL, hnoStepL, kL, hkL_lo, hkL_hi, hexL⟩
          simp only [eulerExitAfter] at hexL
          have h1L : execTicks (1 + kL) (.euler (.eulerSpine d)) ⟨l ⋅ r, cs⟩ =
              .running (.euler .eulerFromLeft) ⟨l ⋅ r, cs⟩ := by
            have hfirst : execTicks 1 (.euler (.eulerSpine d)) ⟨l ⋅ r, cs⟩ =
                .running (.euler (.eulerSpine dL)) ⟨l, .left r :: cs⟩ := hmoveL
            rw [execTicks_add_running kL hfirst]
            exact hexL
          have hmoveR : microstep (.euler .eulerFromLeft) ⟨l ⋅ r, cs⟩ =
              .running (.euler (.eulerSpine ⟨0, by decide⟩)) ⟨r, .right l :: cs⟩ := rfl
          have h1LR : execTicks ((1 + kL) + 1) (.euler (.eulerSpine d)) ⟨l ⋅ r, cs⟩ =
              .running (.euler (.eulerSpine ⟨0, by decide⟩)) ⟨r, .right l :: cs⟩ := by
            rw [execTicks_add_running 1 h1L]
            exact hmoveR
          cases ihr (.right l :: cs) ⟨0, by decide⟩ rfl with
          | inl hvtR =>
              left
              obtain ⟨res, ⟨kR, hkR_lo, hkR_hi, hexR⟩, hvR⟩ := hvtR
              have htot : execTicks (((1 + kL) + 1) + kR) (.euler (.eulerSpine d)) ⟨l ⋅ r, cs⟩ = .done res := by
                rw [execTicks_add_running kR h1LR]
                exact hexR
              have hle : ((1 + kL) + 1) + kR ≤ 4 * leaves (l ⋅ r) := by
                simp only [leaves]
                omega
              exact ⟨res, ⟨((1 + kL) + 1) + kR, by omega, hle, htot⟩, hvR⟩
          | inr hnormR =>
              right
              rcases hnormR with ⟨_, hnoStepR, kR, hkR_lo, hkR_hi, hexR⟩
              simp only [eulerExitAfter] at hexR
              have h1LRdone : execTicks (((1 + kL) + 1) + kR) (.euler (.eulerSpine d)) ⟨l ⋅ r, cs⟩ =
                  .running (.euler .eulerFromRight) ⟨l ⋅ r, cs⟩ := by
                rw [execTicks_add_running kR h1LR]
                exact hexR
              have hfinal : execTicks ((((1 + kL) + 1) + kR) + 1) (.euler (.eulerSpine d)) ⟨l ⋅ r, cs⟩ =
                  eulerExitAfter (l ⋅ r) cs := by
                rw [execTicks_add_running 1 h1LRdone]
                exact eulerFromRight_exec1 (l ⋅ r) cs
              have harCombined : leftArity (l ⋅ r) + d.val < 3 := by
                have hdLval : dL.val = min 3 (1 + d.val) := by
                  rw [hdL, leftStreak, ← hd]
                simp only [leftArity]
                omega
              have hnoStepLR : ¬ ∃ u', Step (l ⋅ r) u' :=
                no_step_of_subterms hnoStepL hnoStepR (by omega)
              refine ⟨harCombined, hnoStepLR, (((1 + kL) + 1) + kR) + 1, by omega, ?_, hfinal⟩
              simp only [leaves]
              omega

theorem eulerRoot_valid (root : Term) :
    ValidTermination (4 * leaves root) (.euler (.eulerSpine ⟨0, by decide⟩)) (rootCursor root) := by
  cases eulerSpine_spec root [] ⟨0, by decide⟩ rfl with
  | inl hvt => exact hvt
  | inr hnorm =>
      rcases hnorm with ⟨_, hnoStep, k, hk_lo, hk_hi, hex⟩
      simp only [eulerExitAfter] at hex
      exact ⟨.normal, ⟨k, hk_lo, by omega, hex⟩, fun _ => hnoStep⟩

theorem abortToRoot_valid (cur : Cursor) :
    ValidTermination (5 * leaves (rebuild cur)) (.euler .abortToRoot) cur := by
  have hs := abortToRoot_steps cur
  have hvt := StepsTo.toValidTermination hs (eulerRoot_valid (rebuild cur))
  have hlt := crumbs_length_lt_leaves_rebuild cur
  exact validTermination_mono (by omega) hvt


/-! ## Section 5: Local Frame Lookaheads, Logical Navigation, & `OpenAndContract` -/

def s2Obs : Term → Bool
  | .app (.app hd _) _ => nodeKindOf hd == .isS
  | _ => false

def plainFrameObs : Term → Bool
  | .app (.app s1 _) (.app (.app s2 _) _) => (nodeKindOf s1 == .isS) && (nodeKindOf s2 == .isS)
  | _ => false

def strictFrameObs : Term → Bool
  | .app (.app s1 _) (.app (.app s2 _) j) =>
      (nodeKindOf s1 == .isS) && (nodeKindOf s2 == .isS) && !s2Obs j
  | _ => false

theorem strictFrameObs_decomp {t : Term} (h : strictFrameObs t = true) :
    ∃ s1 l s2 r j,
      t = (s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j) ∧
      nodeKindOf s1 = .isS ∧
      nodeKindOf s2 = .isS ∧
      s2Obs j = false := by
  match t with
  | .app (.app s1 l) (.app (.app s2 r) j) =>
      simp only [strictFrameObs, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact ⟨s1, l, s2, r, j, rfl, of_decide_eq_true h.1.1, of_decide_eq_true h.1.2, h.2⟩
  | .s => simp [strictFrameObs] at h
  | .var _ => simp [strictFrameObs] at h
  | .app .s _ => simp [strictFrameObs] at h
  | .app (.var _) _ => simp [strictFrameObs] at h
  | .app (.app _ _) .s => simp [strictFrameObs] at h
  | .app (.app _ _) (.var _) => simp [strictFrameObs] at h
  | .app (.app _ _) (.app .s _) => simp [strictFrameObs] at h
  | .app (.app _ _) (.app (.var _) _) => simp [strictFrameObs] at h

/-- **Unconditional Parent-Recovery Disambiguation Lemma**: on EVERY `Term` (even non-pure-S),
    the right wrapper `(s2 ⋅ r) ⋅ j` of any `strictFrameObs`-verified frame is NEVER a strict frame. -/
theorem right_wrapper_not_strictFrameObs (s2 r j : Term) (hj : s2Obs j = false) :
    strictFrameObs ((s2 ⋅ r) ⋅ j) = false := by
  match j with
  | .app (.app a u) v =>
      simp only [s2Obs] at hj
      simp [strictFrameObs, hj]
  | .s => rfl
  | .var _ => rfl
  | .app .s _ => rfl
  | .app (.var _) _ => rfl

theorem obs_eq_on_pureS {t : Term} (hp : isPureS t = true) :
    plainFrameObs t = flagValue t ∧ strictFrameObs t = isStrictFrameBool t := by
  have hs2 : ∀ x : Term, isPureS x = true → s2Obs x = isS2Term x := by
    intro x hpx
    match x with
    | .app (.app a _) _ =>
        simp only [isPureS, Bool.and_eq_true] at hpx
        cases a with
        | s => rfl
        | var _ => simp [isPureS] at hpx
        | app _ _ => rfl
    | .s => rfl
    | .var _ => rfl
    | .app .s _ => rfl
    | .app (.var _) _ => rfl
  match t with
  | .app (.app s1 l) (.app (.app s2 r) j) =>
      simp only [isPureS, Bool.and_eq_true] at hp
      have hj := hs2 j hp.2.2
      cases s1 with
      | var _ => simp [isPureS] at hp
      | app _ _ =>
          simp [plainFrameObs, strictFrameObs, flagValue, isStrictFrameBool, parseFrame, nodeKindOf]
      | s =>
          cases s2 with
          | var _ => simp [isPureS] at hp
          | app _ _ =>
              simp [plainFrameObs, strictFrameObs, flagValue, isStrictFrameBool, parseFrame, nodeKindOf]
          | s =>
              simp [plainFrameObs, strictFrameObs, flagValue, isStrictFrameBool, parseFrame, nodeKindOf, hj]
  | .s => exact ⟨rfl, rfl⟩
  | .var _ => exact ⟨rfl, rfl⟩
  | .app .s _ => exact ⟨rfl, rfl⟩
  | .app (.var _) _ => exact ⟨rfl, rfl⟩
  | .app (.app _ _) .s => simp [plainFrameObs, strictFrameObs, flagValue, isStrictFrameBool, parseFrame]
  | .app (.app _ _) (.var _) => simp [plainFrameObs, strictFrameObs, flagValue, isStrictFrameBool, parseFrame]
  | .app (.app _ _) (.app .s _) => simp [plainFrameObs, strictFrameObs, flagValue, isStrictFrameBool, parseFrame]
  | .app (.app _ _) (.app (.var _) _) => simp [plainFrameObs, strictFrameObs, flagValue, isStrictFrameBool, parseFrame]

theorem strictFrameObs_app_left_app (u v l b : Term) :
    strictFrameObs (((u ⋅ v) ⋅ l) ⋅ b) = false := by
  match b with
  | .app (.app _ _) _ => rfl
  | .s => rfl
  | .var _ => rfl
  | .app .s _ => rfl
  | .app (.var _) _ => rfl

theorem plainFrameObs_app_left_app (u v l b : Term) :
    plainFrameObs (((u ⋅ v) ⋅ l) ⋅ b) = false := by
  match b with
  | .app (.app _ _) _ => rfl
  | .s => rfl
  | .var _ => rfl
  | .app .s _ => rfl
  | .app (.var _) _ => rfl

/-- `CheckStrictFrame` evaluates `strictFrameObs cur.focus` and restores `cur` unchanged in `≤ 16` ticks. -/
theorem checkStrictFrame_steps (ret : StrictFrameCont) (cur : Cursor) :
    StepsTo 16 (.sf (.sf0 ret)) cur (.sf (.sfDone ret (strictFrameObs cur.focus))) cur := by
  rcases cur with ⟨t, cs⟩
  cases t with
  | s => exact StepsTo.mono (by omega) (StepsTo.of_alias rfl)
  | var _ => exact StepsTo.mono (by omega) (StepsTo.of_alias rfl)
  | app a b =>
      cases a with
      | s => exact StepsTo.of_exec (k := 2) (by omega) (by omega) rfl
      | var _ => exact StepsTo.of_exec (k := 2) (by omega) (by omega) rfl
      | app a1 l =>
          cases a1 with
          | app u v =>
              dsimp only []
              rw [strictFrameObs_app_left_app u v l b]
              exact StepsTo.of_exec (k := 4) (by omega) (by omega) rfl
          | s | var _ =>
              cases b with
              | s | var _ => exact StepsTo.of_exec (k := 6) (by omega) (by omega) rfl
              | app b1 j =>
                  cases b1 with
                  | s | var _ => exact StepsTo.of_exec (k := 8) (by omega) (by omega) rfl
                  | app b11 r =>
                      cases b11 with
                      | app _ _ => exact StepsTo.of_exec (k := 10) (by omega) (by omega) rfl
                      | s | var _ =>
                          cases j with
                          | s | var _ => exact StepsTo.of_exec (k := 12) (by omega) (by omega) rfl
                          | app j1 j2 =>
                              cases j1 with
                              | s | var _ => exact StepsTo.of_exec (k := 14) (by omega) (by omega) rfl
                              | app j11 j12 =>
                                  cases j11 <;> exact StepsTo.of_exec (k := 16) (by omega) (by omega) rfl

/-- `CheckPlainFrame` evaluates `plainFrameObs cur.focus` and restores `cur` unchanged in `≤ 10` ticks. -/
theorem checkPlainFrame_steps (cur : Cursor) :
    StepsTo 10 (.openSub .pf0) cur (.openSub (.pfDone (plainFrameObs cur.focus))) cur := by
  rcases cur with ⟨t, cs⟩
  cases t with
  | s => exact StepsTo.mono (by omega) (StepsTo.of_alias rfl)
  | var _ => exact StepsTo.mono (by omega) (StepsTo.of_alias rfl)
  | app a b =>
      cases a with
      | s | var _ => exact StepsTo.of_exec (k := 2) (by omega) (by omega) rfl
      | app a1 l =>
          cases a1 with
          | app u v =>
              dsimp only []
              rw [plainFrameObs_app_left_app u v l b]
              exact StepsTo.of_exec (k := 4) (by omega) (by omega) rfl
          | s | var _ =>
              cases b with
              | s | var _ => exact StepsTo.of_exec (k := 6) (by omega) (by omega) rfl
              | app b1 j =>
                  cases b1 with
                  | s | var _ => exact StepsTo.of_exec (k := 8) (by omega) (by omega) rfl
                  | app b11 r =>
                      cases b11 <;> exact StepsTo.of_exec (k := 10) (by omega) (by omega) rfl

/-- Logical Down-Left (`[false, true]`), Down-Right (`[true, false, true]`), Up, and Hub-Check lemmas. -/
def downLCrumbs (s1 r s2 j : Term) (cs : List Crumb) : List Crumb :=
  .right s1 :: .left ((s2 ⋅ r) ⋅ j) :: cs

def downRCrumbs (s1 l s2 j : Term) (cs : List Crumb) : List Crumb :=
  .right s2 :: .left j :: .right (s1 ⋅ l) :: cs

theorem downLCrumbs_path (s1 r s2 j : Term) (cs : List Crumb) :
    crumbsPath (downLCrumbs s1 r s2 j cs) = crumbsPath cs ++ [false, true] := by
  simp [downLCrumbs, crumbsPath, List.append_assoc]

theorem downRCrumbs_path (s1 l s2 j : Term) (cs : List Crumb) :
    crumbsPath (downRCrumbs s1 l s2 j cs) = crumbsPath cs ++ [true, false, true] := by
  simp [downRCrumbs, crumbsPath, List.append_assoc]

theorem downL_steps (next : DownLCont) (s1 l s2 r j : Term) (cs : List Crumb)
    (cStart : Control)
    (hstart : microstep cStart ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩ =
      .running (.downL1 next) ⟨s1 ⋅ l, .left ((s2 ⋅ r) ⋅ j) :: cs⟩) :
    StepsTo 2 cStart ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩
      (.downLDone next) ⟨l, downLCrumbs s1 r s2 j cs⟩ := by
  have s1_step := StepsTo.of_step hstart
  have s2_step : StepsTo 1 (.downL1 next) ⟨s1 ⋅ l, .left ((s2 ⋅ r) ⋅ j) :: cs⟩
      (.downLDone next) ⟨l, downLCrumbs s1 r s2 j cs⟩ :=
    StepsTo.of_step rfl
  exact StepsTo.trans s1_step s2_step

theorem downR_steps (next : DownRCont) (s1 l s2 r j : Term) (cs : List Crumb)
    (cStart : Control)
    (hstart : microstep cStart ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩ =
      .running (.downR1 next) ⟨(s2 ⋅ r) ⋅ j, .right (s1 ⋅ l) :: cs⟩) :
    StepsTo 3 cStart ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩
      (.downRDone next) ⟨r, downRCrumbs s1 l s2 j cs⟩ := by
  have s1_step := StepsTo.of_step hstart
  have s2_step : StepsTo 1 (.downR1 next) ⟨(s2 ⋅ r) ⋅ j, .right (s1 ⋅ l) :: cs⟩
      (.downR2 next) ⟨s2 ⋅ r, .left j :: .right (s1 ⋅ l) :: cs⟩ :=
    StepsTo.of_step rfl
  have s3_step : StepsTo 1 (.downR2 next) ⟨s2 ⋅ r, .left j :: .right (s1 ⋅ l) :: cs⟩
      (.downRDone next) ⟨r, downRCrumbs s1 l s2 j cs⟩ :=
    StepsTo.of_step rfl
  exact StepsTo.trans (StepsTo.trans s1_step s2_step) s3_step

theorem up_from_left_steps (ret : UpCont) (s1 l s2 r j : Term) (cs : List Crumb)
    (hsf : strictFrameObs ((s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j)) = true)
    (cStart : Control)
    (hstart : microstep cStart ⟨l, downLCrumbs s1 r s2 j cs⟩ =
      .running (.up1 ret) ⟨s1 ⋅ l, .left ((s2 ⋅ r) ⋅ j) :: cs⟩) :
    StepsTo 19 cStart ⟨l, downLCrumbs s1 r s2 j cs⟩
      (.upDone ret false) ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩ := by
  have st1 := StepsTo.of_step hstart
  have st2 : StepsTo 1 (.up1 ret) ⟨s1 ⋅ l, .left ((s2 ⋅ r) ⋅ j) :: cs⟩
      (.sf (.sf0 (.upCheck ret))) ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩ :=
    StepsTo.of_step rfl
  have st3 := checkStrictFrame_steps (.upCheck ret) ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩
  rw [hsf] at st3
  have st4 : StepsTo 0 (.sf (.sfDone (.upCheck ret) true)) ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩
      (.upDone ret false) ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩ :=
    StepsTo.of_alias rfl
  exact StepsTo.mono (by omega) (StepsTo.trans (StepsTo.trans (StepsTo.trans st1 st2) st3) st4)

theorem up_from_right_steps (ret : UpCont) (s1 l s2 r j : Term) (cs : List Crumb)
    (hj : s2Obs j = false)
    (cStart : Control)
    (hstart : microstep cStart ⟨r, downRCrumbs s1 l s2 j cs⟩ =
      .running (.up1 ret) ⟨s2 ⋅ r, .left j :: .right (s1 ⋅ l) :: cs⟩) :
    StepsTo 19 cStart ⟨r, downRCrumbs s1 l s2 j cs⟩
      (.upDone ret true) ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩ := by
  have st1 := StepsTo.of_step hstart
  have st2 : StepsTo 1 (.up1 ret) ⟨s2 ⋅ r, .left j :: .right (s1 ⋅ l) :: cs⟩
      (.sf (.sf0 (.upCheck ret))) ⟨(s2 ⋅ r) ⋅ j, .right (s1 ⋅ l) :: cs⟩ :=
    StepsTo.of_step rfl
  have st3 := checkStrictFrame_steps (.upCheck ret) ⟨(s2 ⋅ r) ⋅ j, .right (s1 ⋅ l) :: cs⟩
  rw [right_wrapper_not_strictFrameObs s2 r j hj] at st3
  have st4 : StepsTo 1 (.sf (.sfDone (.upCheck ret) false)) ⟨(s2 ⋅ r) ⋅ j, .right (s1 ⋅ l) :: cs⟩
      (.upDone ret true) ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩ :=
    StepsTo.of_step rfl
  exact StepsTo.mono (by omega) (StepsTo.trans (StepsTo.trans (StepsTo.trans st1 st2) st3) st4)

theorem hubChk_at_hub_steps (ret : HubCheckCont) (rootLeft hub : Term)
    (cStart : Control)
    (hstart : microstep cStart ⟨hub, [.right rootLeft]⟩ =
      .running (.hubChk1 ret) ⟨rootLeft ⋅ hub, []⟩) :
    StepsTo 2 cStart ⟨hub, [.right rootLeft]⟩
      (.hubChkDone ret true) ⟨hub, [.right rootLeft]⟩ := by
  have st1 := StepsTo.of_step hstart
  have st2 : StepsTo 1 (.hubChk1 ret) ⟨rootLeft ⋅ hub, []⟩
      (.hubChkDone ret true) ⟨hub, [.right rootLeft]⟩ :=
    StepsTo.of_step rfl
  exact StepsTo.trans st1 st2

theorem hubChk_below_hub_steps (ret : HubCheckCont) (sNode focus other : Term) (cs : List Crumb)
    (cStart : Control)
    (hstart : microstep cStart ⟨focus, .right sNode :: .left other :: cs⟩ =
      .running (.hubChk1 ret) ⟨sNode ⋅ focus, .left other :: cs⟩) :
    StepsTo 2 cStart ⟨focus, .right sNode :: .left other :: cs⟩
      (.hubChkDone ret false) ⟨focus, .right sNode :: .left other :: cs⟩ := by
  have st1 := StepsTo.of_step hstart
  have st2 : StepsTo 1 (.hubChk1 ret) ⟨sNode ⋅ focus, .left other :: cs⟩
      (.hubChkDone ret false) ⟨focus, .right sNode :: .left other :: cs⟩ :=
    StepsTo.of_step rfl
  exact StepsTo.trans st1 st2

theorem rightArity_valid (r : Term) (csR : List Crumb) :
    ValidTermination (5 * leaves (rebuild ⟨r, csR⟩) + 9)
      (.openSub (.rightArity ⟨0, by decide⟩)) ⟨r, csR⟩ := by
  have hAbortAlias : ∀ (c : Control) (cur' : Cursor),
      rebuild cur' = rebuild ⟨r, csR⟩ →
      microstep c cur' = microstep (.euler .abortToRoot) cur' →
      ValidTermination (5 * leaves (rebuild ⟨r, csR⟩)) c cur' := by
    intro c cur' hreb hal
    have hvt := StepsTo.toValidTermination (StepsTo.of_alias hal) (abortToRoot_valid cur')
    rw [hreb] at hvt
    exact validTermination_mono (by omega) hvt
  cases r with
  | s =>
      have hvt := hAbortAlias (.openSub (.rightArity ⟨0, by decide⟩)) ⟨.s, csR⟩ rfl rfl
      exact validTermination_mono (by omega) hvt
  | var n =>
      have hvt := hAbortAlias (.openSub (.rightArity ⟨0, by decide⟩)) ⟨.var n, csR⟩ rfl rfl
      exact validTermination_mono (by omega) hvt
  | app r1 c1 =>
      have sR1 : StepsTo 1 (.openSub (.rightArity ⟨0, by decide⟩)) ⟨r1 ⋅ c1, csR⟩
          (.openSub (.rightArity ⟨1, by decide⟩)) ⟨r1, .left c1 :: csR⟩ :=
        StepsTo.of_step rfl
      cases r1 with
      | s =>
          have hvt := hAbortAlias (.openSub (.rightArity ⟨1, by decide⟩)) ⟨.s, .left c1 :: csR⟩ rfl rfl
          exact validTermination_mono (by omega) (StepsTo.toValidTermination sR1 hvt)
      | var n =>
          have hvt := hAbortAlias (.openSub (.rightArity ⟨1, by decide⟩)) ⟨.var n, .left c1 :: csR⟩ rfl rfl
          exact validTermination_mono (by omega) (StepsTo.toValidTermination sR1 hvt)
      | app r2 c2 =>
          have sR2 : StepsTo 1 (.openSub (.rightArity ⟨1, by decide⟩)) ⟨r2 ⋅ c2, .left c1 :: csR⟩
              (.openSub (.rightArity ⟨2, by decide⟩)) ⟨r2, .left c2 :: .left c1 :: csR⟩ :=
            StepsTo.of_step rfl
          cases r2 with
          | s =>
              have hvt := hAbortAlias (.openSub (.rightArity ⟨2, by decide⟩)) ⟨.s, .left c2 :: .left c1 :: csR⟩ rfl rfl
              exact validTermination_mono (by omega) (StepsTo.toValidTermination (StepsTo.trans sR1 sR2) hvt)
          | var n =>
              have hvt := hAbortAlias (.openSub (.rightArity ⟨2, by decide⟩)) ⟨.var n, .left c2 :: .left c1 :: csR⟩ rfl rfl
              exact validTermination_mono (by omega) (StepsTo.toValidTermination (StepsTo.trans sR1 sR2) hvt)
          | app r3 c3 =>
              have sR3 : StepsTo 1 (.openSub (.rightArity ⟨2, by decide⟩))
                  ⟨r3 ⋅ c3, .left c2 :: .left c1 :: csR⟩
                  (.openSub (.rightArity ⟨3, by decide⟩))
                  ⟨r3, .left c3 :: .left c2 :: .left c1 :: csR⟩ :=
                StepsTo.of_step rfl
              cases r3 with
              | s =>
                  have sC : StepsTo 1 (.openSub (.rightArity ⟨3, by decide⟩))
                      ⟨.s, .left c3 :: .left c2 :: .left c1 :: csR⟩
                      (.euler .climbToRedex2) ⟨.s ⋅ c3, .left c2 :: .left c1 :: csR⟩ :=
                    StepsTo.of_step rfl
                  have hvt := climbToRedex2_valid .s c3 c2 c1 csR rfl
                  exact validTermination_mono (by omega)
                    (StepsTo.toValidTermination (StepsTo.trans (StepsTo.trans sR1 sR2) (StepsTo.trans sR3 sC)) hvt)
              | var n =>
                  have sC : StepsTo 1 (.openSub (.rightArity ⟨3, by decide⟩))
                      ⟨.var n, .left c3 :: .left c2 :: .left c1 :: csR⟩
                      (.euler .climbToRedex2) ⟨.var n ⋅ c3, .left c2 :: .left c1 :: csR⟩ :=
                    StepsTo.of_step rfl
                  have hvt := climbToRedex2_valid (.var n) c3 c2 c1 csR rfl
                  exact validTermination_mono (by omega)
                    (StepsTo.toValidTermination (StepsTo.trans (StepsTo.trans sR1 sR2) (StepsTo.trans sR3 sC)) hvt)
              | app r4 c4 =>
                  have sR4 : StepsTo 1 (.openSub (.rightArity ⟨3, by decide⟩))
                      ⟨r4 ⋅ c4, .left c3 :: .left c2 :: .left c1 :: csR⟩
                      (.openSub (.rightArity ⟨4, by decide⟩))
                      ⟨r4, .left c4 :: .left c3 :: .left c2 :: .left c1 :: csR⟩ :=
                    StepsTo.of_step rfl
                  cases r4 with
                  | s =>
                      have sC : StepsTo 1 (.openSub (.rightArity ⟨4, by decide⟩))
                          ⟨.s, .left c4 :: .left c3 :: .left c2 :: .left c1 :: csR⟩
                          (.euler .climbToRedex2) ⟨.s ⋅ c4, .left c3 :: .left c2 :: .left c1 :: csR⟩ :=
                        StepsTo.of_step rfl
                      have hvt := climbToRedex2_valid .s c4 c3 c2 (.left c1 :: csR) rfl
                      exact validTermination_mono (by omega)
                        (StepsTo.toValidTermination
                          (StepsTo.trans (StepsTo.trans sR1 sR2) (StepsTo.trans (StepsTo.trans sR3 sR4) sC)) hvt)
                  | var n =>
                      have sC : StepsTo 1 (.openSub (.rightArity ⟨4, by decide⟩))
                          ⟨.var n, .left c4 :: .left c3 :: .left c2 :: .left c1 :: csR⟩
                          (.euler .climbToRedex2) ⟨.var n ⋅ c4, .left c3 :: .left c2 :: .left c1 :: csR⟩ :=
                        StepsTo.of_step rfl
                      have hvt := climbToRedex2_valid (.var n) c4 c3 c2 (.left c1 :: csR) rfl
                      exact validTermination_mono (by omega)
                        (StepsTo.toValidTermination
                          (StepsTo.trans (StepsTo.trans sR1 sR2) (StepsTo.trans (StepsTo.trans sR3 sR4) sC)) hvt)
                  | app r5 c5 =>
                      have hvt := hAbortAlias (.openSub (.rightArity ⟨4, by decide⟩))
                        ⟨r5 ⋅ c5, .left c4 :: .left c3 :: .left c2 :: .left c1 :: csR⟩ rfl rfl
                      exact validTermination_mono (by omega)
                        (StepsTo.toValidTermination (StepsTo.trans (StepsTo.trans sR1 sR2) (StepsTo.trans sR3 sR4)) hvt)

/-- All-input termination & pure-S soundness of `OpenAndContract` (`≤ 5 * leaves root + 27` ticks). -/
theorem openAndContract_valid (cur : Cursor) :
    ValidTermination (5 * leaves (rebuild cur) + 27) (.openSub .pf0) cur := by
  have hpf := checkPlainFrame_steps cur
  cases hp : plainFrameObs cur.focus with
  | true =>
      rw [hp] at hpf
      have hab : StepsTo 0 (.openSub (.pfDone true)) cur (.euler .abortToRoot) cur :=
        StepsTo.of_alias rfl
      have hvt := StepsTo.toValidTermination (StepsTo.trans hpf hab) (abortToRoot_valid cur)
      exact validTermination_mono (by omega) hvt
  | false =>
      rw [hp] at hpf
      rcases cur with ⟨f, cs⟩
      have hAbortAlias : ∀ (c : Control) (cur' : Cursor),
          rebuild cur' = rebuild ⟨f, cs⟩ →
          microstep c cur' = microstep (.euler .abortToRoot) cur' →
          ValidTermination (5 * leaves (rebuild ⟨f, cs⟩)) c cur' := by
        intro c cur' hreb hal
        have hvt := StepsTo.toValidTermination (StepsTo.of_alias hal) (abortToRoot_valid cur')
        rw [hreb] at hvt
        exact validTermination_mono (by omega) hvt
      cases f with
      | s =>
          have hvt := hAbortAlias (.openSub (.pfDone false)) ⟨.s, cs⟩ rfl rfl
          exact validTermination_mono (by omega) (StepsTo.toValidTermination hpf hvt)
      | var n =>
          have hvt := hAbortAlias (.openSub (.pfDone false)) ⟨.var n, cs⟩ rfl rfl
          exact validTermination_mono (by omega) (StepsTo.toValidTermination hpf hvt)
      | app a1 b1 =>
          have sL1 : StepsTo 1 (.openSub (.pfDone false)) ⟨a1 ⋅ b1, cs⟩
              (.openSub (.leftArity ⟨1, by decide⟩)) ⟨a1, .left b1 :: cs⟩ :=
            StepsTo.of_step rfl
          cases a1 with
          | s =>
              have hvt := hAbortAlias (.openSub (.leftArity ⟨1, by decide⟩)) ⟨.s, .left b1 :: cs⟩ rfl rfl
              exact validTermination_mono (by omega) (StepsTo.toValidTermination (StepsTo.trans hpf sL1) hvt)
          | var n =>
              have hvt := hAbortAlias (.openSub (.leftArity ⟨1, by decide⟩)) ⟨.var n, .left b1 :: cs⟩ rfl rfl
              exact validTermination_mono (by omega) (StepsTo.toValidTermination (StepsTo.trans hpf sL1) hvt)
          | app a2 b2 =>
              have sL2 : StepsTo 1 (.openSub (.leftArity ⟨1, by decide⟩)) ⟨a2 ⋅ b2, .left b1 :: cs⟩
                  (.openSub (.leftArity ⟨2, by decide⟩)) ⟨a2, .left b2 :: .left b1 :: cs⟩ :=
                StepsTo.of_step rfl
              cases a2 with
              | s =>
                  have sToR : StepsTo 3 (.openSub (.leftArity ⟨2, by decide⟩))
                      ⟨.s, .left b2 :: .left b1 :: cs⟩
                      (.openSub (.rightArity ⟨0, by decide⟩)) ⟨b1, .right (.s ⋅ b2) :: cs⟩ :=
                    StepsTo.of_exec (k := 3) (by omega) (by omega) rfl
                  have sPre := StepsTo.trans (StepsTo.trans hpf sL1) (StepsTo.trans sL2 sToR)
                  have hvt := rightArity_valid b1 (.right (.s ⋅ b2) :: cs)
                  have hrebEq : rebuild ⟨b1, .right (.s ⋅ b2) :: cs⟩ = rebuild ⟨(.s ⋅ b2) ⋅ b1, cs⟩ := rfl
                  rw [hrebEq] at hvt
                  exact validTermination_mono (by omega) (StepsTo.toValidTermination sPre hvt)
              | var n =>
                  have sToR : StepsTo 3 (.openSub (.leftArity ⟨2, by decide⟩))
                      ⟨.var n, .left b2 :: .left b1 :: cs⟩
                      (.openSub (.rightArity ⟨0, by decide⟩)) ⟨b1, .right (.var n ⋅ b2) :: cs⟩ :=
                    StepsTo.of_exec (k := 3) (by omega) (by omega) rfl
                  have sPre := StepsTo.trans (StepsTo.trans hpf sL1) (StepsTo.trans sL2 sToR)
                  have hvt := rightArity_valid b1 (.right (.var n ⋅ b2) :: cs)
                  have hrebEq : rebuild ⟨b1, .right (.var n ⋅ b2) :: cs⟩ = rebuild ⟨(.var n ⋅ b2) ⋅ b1, cs⟩ := rfl
                  rw [hrebEq] at hvt
                  exact validTermination_mono (by omega) (StepsTo.toValidTermination sPre hvt)
              | app a3 b3 =>
                  have sL3 : StepsTo 1 (.openSub (.leftArity ⟨2, by decide⟩)) ⟨a3 ⋅ b3, .left b2 :: .left b1 :: cs⟩
                      (.openSub (.leftArity ⟨3, by decide⟩)) ⟨a3, .left b3 :: .left b2 :: .left b1 :: cs⟩ :=
                    StepsTo.of_step rfl
                  cases a3 with
                  | s =>
                      have sC : StepsTo 1 (.openSub (.leftArity ⟨3, by decide⟩))
                          ⟨.s, .left b3 :: .left b2 :: .left b1 :: cs⟩
                          (.euler .climbToRedex2) ⟨.s ⋅ b3, .left b2 :: .left b1 :: cs⟩ :=
                        StepsTo.of_step rfl
                      have hvt := climbToRedex2_valid .s b3 b2 b1 cs rfl
                      exact validTermination_mono (by omega)
                        (StepsTo.toValidTermination (StepsTo.trans (StepsTo.trans hpf sL1) (StepsTo.trans sL2 (StepsTo.trans sL3 sC))) hvt)
                  | var n =>
                      have sC : StepsTo 1 (.openSub (.leftArity ⟨3, by decide⟩))
                          ⟨.var n, .left b3 :: .left b2 :: .left b1 :: cs⟩
                          (.euler .climbToRedex2) ⟨.var n ⋅ b3, .left b2 :: .left b1 :: cs⟩ :=
                        StepsTo.of_step rfl
                      have hvt := climbToRedex2_valid (.var n) b3 b2 b1 cs rfl
                      exact validTermination_mono (by omega)
                        (StepsTo.toValidTermination (StepsTo.trans (StepsTo.trans hpf sL1) (StepsTo.trans sL2 (StepsTo.trans sL3 sC))) hvt)
                  | app a4 b4 =>
                      have sL4 : StepsTo 1 (.openSub (.leftArity ⟨3, by decide⟩))
                          ⟨a4 ⋅ b4, .left b3 :: .left b2 :: .left b1 :: cs⟩
                          (.openSub (.leftArity ⟨4, by decide⟩))
                          ⟨a4, .left b4 :: .left b3 :: .left b2 :: .left b1 :: cs⟩ :=
                        StepsTo.of_step rfl
                      cases a4 with
                      | s =>
                          have sC : StepsTo 1 (.openSub (.leftArity ⟨4, by decide⟩))
                              ⟨.s, .left b4 :: .left b3 :: .left b2 :: .left b1 :: cs⟩
                              (.euler .climbToRedex2) ⟨.s ⋅ b4, .left b3 :: .left b2 :: .left b1 :: cs⟩ :=
                            StepsTo.of_step rfl
                          have hvt := climbToRedex2_valid .s b4 b3 b2 (.left b1 :: cs) rfl
                          exact validTermination_mono (by omega)
                            (StepsTo.toValidTermination
                              (StepsTo.trans (StepsTo.trans hpf sL1) (StepsTo.trans sL2 (StepsTo.trans (StepsTo.trans sL3 sL4) sC))) hvt)
                      | var n =>
                          have sC : StepsTo 1 (.openSub (.leftArity ⟨4, by decide⟩))
                              ⟨.var n, .left b4 :: .left b3 :: .left b2 :: .left b1 :: cs⟩
                              (.euler .climbToRedex2) ⟨.var n ⋅ b4, .left b3 :: .left b2 :: .left b1 :: cs⟩ :=
                            StepsTo.of_step rfl
                          have hvt := climbToRedex2_valid (.var n) b4 b3 b2 (.left b1 :: cs) rfl
                          exact validTermination_mono (by omega)
                            (StepsTo.toValidTermination
                              (StepsTo.trans (StepsTo.trans hpf sL1) (StepsTo.trans sL2 (StepsTo.trans (StepsTo.trans sL3 sL4) sC))) hvt)
                      | app a5 b5 =>
                          have hvt := hAbortAlias (.openSub (.leftArity ⟨4, by decide⟩))
                            ⟨a5 ⋅ b5, .left b4 :: .left b3 :: .left b2 :: .left b1 :: cs⟩ rfl rfl
                          exact validTermination_mono (by omega)
                            (StepsTo.toValidTermination
                              (StepsTo.trans (StepsTo.trans hpf sL1) (StepsTo.trans sL2 (StepsTo.trans sL3 sL4))) hvt)



/-! ## Section 6: All-Input Linear Microtick Bound & Pure-S Single-Contraction/Normality Contract -/

structure FrameCtx where
  s1 : Term
  other : Term
  s2 : Term
  j : Term

def ValidFrameCtx (f : FrameCtx) : Prop :=
  nodeKindOf f.s1 = .isS ∧ nodeKindOf f.s2 = .isS ∧ s2Obs f.j = false

theorem validFrameCtx_strictL (f : FrameCtx) (u : Term) (hf : ValidFrameCtx f) :
    strictFrameObs ((f.s1 ⋅ u) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j)) = true := by
  rcases hf with ⟨h1, h2, hj⟩
  simp [strictFrameObs, h1, h2, hj]

theorem validFrameCtx_strictR (f : FrameCtx) (u : Term) (hf : ValidFrameCtx f) :
    strictFrameObs ((f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j)) = true := by
  rcases hf with ⟨h1, h2, hj⟩
  simp [strictFrameObs, h1, h2, hj]

def pushLChain : List FrameCtx → List Crumb → List Crumb
  | [], cs => cs
  | f :: fs, cs => downLCrumbs f.s1 f.other f.s2 f.j (pushLChain fs cs)

def wrapLChain : List FrameCtx → Term → Term
  | [], u => u
  | f :: fs, u => wrapLChain fs ((f.s1 ⋅ u) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j))

def pushRChain : List FrameCtx → List Crumb → List Crumb
  | [], cs => cs
  | f :: fs, cs => downRCrumbs f.s1 f.other f.s2 f.j (pushRChain fs cs)

def wrapRChain : List FrameCtx → Term → Term
  | [], u => u
  | f :: fs, u => wrapRChain fs ((f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j))

theorem rebuild_pushLChain (lchain : List FrameCtx) (cs : List Crumb) (u : Term) :
    rebuild ⟨u, pushLChain lchain cs⟩ = rebuild ⟨wrapLChain lchain u, cs⟩ := by
  induction lchain generalizing u with
  | nil => rfl
  | cons f fs ih =>
      simpa [pushLChain, downLCrumbs, wrapLChain, rebuild, rebuildWith] using
        ih ((f.s1 ⋅ u) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j))

theorem rebuild_pushRChain (rchain : List FrameCtx) (cs : List Crumb) (u : Term) :
    rebuild ⟨u, pushRChain rchain cs⟩ = rebuild ⟨wrapRChain rchain u, cs⟩ := by
  induction rchain generalizing u with
  | nil => rfl
  | cons f fs ih =>
      simpa [pushRChain, downRCrumbs, wrapRChain, rebuild, rebuildWith] using
        ih ((f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j))

theorem leaves_wrapLChain_ge (lchain : List FrameCtx) (u : Term) :
    leaves u + 3 * lchain.length ≤ leaves (wrapLChain lchain u) := by
  induction lchain generalizing u with
  | nil => simp [wrapLChain]
  | cons f fs ih =>
      have hsub := ih ((f.s1 ⋅ u) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j))
      have hs1 := leaves_pos f.s1
      have hs2 := leaves_pos f.s2
      have ho := leaves_pos f.other
      have hj := leaves_pos f.j
      simp only [wrapLChain, List.length_cons]
      simp only [leaves] at hsub
      omega

theorem leaves_wrapRChain_ge (rchain : List FrameCtx) (u : Term) :
    leaves u + 3 * rchain.length ≤ leaves (wrapRChain rchain u) := by
  induction rchain generalizing u with
  | nil => simp [wrapRChain]
  | cons f fs ih =>
      have hsub := ih ((f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j))
      have hs1 := leaves_pos f.s1
      have hs2 := leaves_pos f.s2
      have ho := leaves_pos f.other
      have hj := leaves_pos f.j
      simp only [wrapRChain, List.length_cons]
      simp only [leaves] at hsub
      omega

/-! ### Subroutine `ReadFields11` (`≤ 860` ticks on EVERY tree) -/

def obsReadFields : Nat → Term → Option (List Bool)
  | 0, t => if strictFrameObs t then some [] else none
  | n + 1, t =>
      if strictFrameObs t then
        match t with
        | .app (.app _ flag) (.app (.app _ rest) _) =>
            (obsReadFields n rest).map (strictFrameObs flag :: ·)
        | _ => none
      else none

def startRClimbProp (uCont : UpCont) (rchain : List FrameCtx) (u : Term) (csBase : List Crumb)
    (cStart : Control) : Prop :=
  match rchain with
  | [] => False
  | f :: fs =>
      microstep cStart ⟨u, pushRChain (f :: fs) csBase⟩ =
        .running (.up1 uCont)
          ⟨f.s2 ⋅ u, .left f.j :: .right (f.s1 ⋅ f.other) :: pushRChain fs csBase⟩

def startLClimbProp (uCont : UpCont) (ps1 pl ps2 pj : Term) (csP : List Crumb)
    (lchain : List FrameCtx) (x : Term) (cStart : Control) : Prop :=
  match lchain with
  | [] =>
      microstep cStart ⟨x, downRCrumbs ps1 pl ps2 pj csP⟩ =
        .running (.up1 uCont)
          ⟨ps2 ⋅ x, .left pj :: .right (ps1 ⋅ pl) :: csP⟩
  | f :: fs =>
      microstep cStart ⟨x, pushLChain (f :: fs) (downRCrumbs ps1 pl ps2 pj csP)⟩ =
        .running (.up1 uCont)
          ⟨f.s1 ⋅ x, .left ((f.s2 ⋅ f.other) ⋅ f.j) :: pushLChain fs (downRCrumbs ps1 pl ps2 pj csP)⟩

theorem rfClimb_steps (caller : CellCaller) (res : Option Bits11) :
    ∀ (rchain : List FrameCtx) (rem : Fin 12) (u : Term) (csV : List Crumb) (cStart : Control),
      (∀ f ∈ rchain, ValidFrameCtx f) →
      rchain.length = rem.val + 1 →
      startRClimbProp (.rfClimb caller res rem) rchain u csV cStart →
      StepsTo (19 * (rem.val + 1)) cStart ⟨u, pushRChain rchain csV⟩
        (.upDone (.rfClimb caller res ⟨0, by decide⟩) true) ⟨wrapRChain rchain u, csV⟩ := by
  intro rchain
  induction rchain with
  | nil =>
      intro rem _ _ _ _ _ hstart
      exact False.elim hstart
  | cons f fs ih =>
      intro rem u csV cStart hall hlen hstart
      dsimp only [startRClimbProp] at hstart
      have hf : ValidFrameCtx f := hall f (by simp)
      have hfs : ∀ x ∈ fs, ValidFrameCtx x := fun x hx => hall x (by simp [hx])
      have hup1 := up_from_right_steps (.rfClimb caller res rem) f.s1 f.other f.s2 u f.j
        (pushRChain fs csV) hf.2.2 cStart hstart
      if hrem0 : rem.val = 0 then
        have hfsNil : fs = [] := by
          cases fs with
          | nil => rfl
          | cons _ _ => simp only [List.length_cons] at hlen; omega
        subst fs
        have hremEq : rem = ⟨0, by decide⟩ := by apply Fin.ext; exact hrem0
        subst hremEq
        simpa [pushRChain, wrapRChain] using hup1
      else
        let rem' : Fin 12 := ⟨rem.val - 1, by omega⟩
        have hlen' : fs.length = rem'.val + 1 := by
          simp only [List.length_cons] at hlen
          dsimp only [rem']
          omega
        cases fs with
        | nil => cases hlen'
        | cons f2 fs2 =>
            have hmNext : startRClimbProp (.rfClimb caller res rem') (f2 :: fs2)
                ((f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j)) csV
                (.upDone (.rfClimb caller res rem) true) := by
              dsimp only [startRClimbProp, microstep, step, onUpDone]
              rw [dif_neg hrem0]
              rfl
            have hrest := ih rem' ((f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j)) csV
              (.upDone (.rfClimb caller res rem) true) hfs hlen' hmNext
            have htot := StepsTo.trans hup1 hrest
            have hbound : 19 + 19 * (rem'.val + 1) ≤ 19 * (rem.val + 1) := by
              dsimp only [rem']
              omega
            simpa [pushRChain, wrapRChain] using StepsTo.mono hbound htot

theorem rfBitFrame_loop_steps (caller : CellCaller) :
    ∀ (k : Nat) (acc : BitsLe11) (rchain : List FrameCtx) (curFields : Term) (csV : List Crumb),
      acc.val.length + k = 11 →
      rchain.length = acc.val.length + 1 →
      (∀ f ∈ rchain, ValidFrameCtx f) →
      ∃ out : Option Bits11,
        out.map Subtype.val = (obsReadFields k curFields).map (acc.val ++ ·) ∧
        StepsTo (56 * k + 244) (.sf (.sf0 (.rfBitFrame caller acc)))
          ⟨curFields, pushRChain rchain csV⟩
          (.upDone (.rfClimb caller out ⟨0, by decide⟩) true)
          ⟨wrapRChain rchain curFields, csV⟩ := by
  intro k
  induction k with
  | zero =>
      intro acc rchain curFields csV hlen hrlen hall
      have hacc11 : acc.val.length = 11 := by omega
      have hrlen12 : rchain.length = 12 := by omega
      let out : Option Bits11 := if strictFrameObs curFields then some ⟨acc.val, hacc11⟩ else none
      have hsf := checkStrictFrame_steps (.rfBitFrame caller acc) ⟨curFields, pushRChain rchain csV⟩
      cases rchain with
      | nil => cases hrlen12
      | cons f fs =>
          have hm : microstep (.sf (.sfDone (.rfBitFrame caller acc) (strictFrameObs curFields)))
              ⟨curFields, pushRChain (f :: fs) csV⟩ =
              .running (.up1 (.rfClimb caller out ⟨11, by decide⟩))
                ⟨f.s2 ⋅ curFields, .left f.j :: .right (f.s1 ⋅ f.other) :: pushRChain fs csV⟩ := by
            dsimp only [microstep, step, stepSf, onSfDone]
            rw [dif_pos hacc11]
            rfl
          have hclimb := rfClimb_steps caller out (f :: fs) ⟨11, by decide⟩ curFields csV
            (.sf (.sfDone (.rfBitFrame caller acc) (strictFrameObs curFields))) hall hrlen12 hm
          refine ⟨out, ?_, StepsTo.mono (by omega) (StepsTo.trans hsf hclimb)⟩
          cases hobs : strictFrameObs curFields <;> simp [out, obsReadFields, hobs]
  | succ m ih =>
      intro acc rchain curFields csV hlen hrlen hall
      have hne11 : acc.val.length ≠ 11 := by omega
      have hlt11 : acc.val.length < 11 := by omega
      have hsf := checkStrictFrame_steps (.rfBitFrame caller acc) ⟨curFields, pushRChain rchain csV⟩
      cases hobs : strictFrameObs curFields with
      | false =>
          rw [hobs] at hsf
          cases rchain with
          | nil => cases hrlen
          | cons f fs =>
              let rem : Fin 12 := ⟨acc.val.length, by omega⟩
              have hm : microstep (.sf (.sfDone (.rfBitFrame caller acc) false))
                  ⟨curFields, pushRChain (f :: fs) csV⟩ =
                  .running (.up1 (.rfClimb caller none rem))
                    ⟨f.s2 ⋅ curFields, .left f.j :: .right (f.s1 ⋅ f.other) :: pushRChain fs csV⟩ := by
                dsimp only [microstep, step, stepSf, onSfDone]
                rw [dif_neg hne11]
                rfl
              have hclimb := rfClimb_steps caller none (f :: fs) rem curFields csV
                (.sf (.sfDone (.rfBitFrame caller acc) false)) hall (by dsimp only [rem]; exact hrlen) hm
              refine ⟨none, by simp [obsReadFields, hobs], ?_⟩
              have hbound : 16 + 19 * (rem.val + 1) ≤ 56 * (m + 1) + 244 := by
                dsimp only [rem]
                omega
              exact StepsTo.mono hbound (StepsTo.trans hsf hclimb)
      | true =>
          rw [hobs] at hsf
          obtain ⟨bs1, bitFlag, bs2, rest, bj, hcfEq, hbs1, hbs2, hbj⟩ := strictFrameObs_decomp hobs
          subst curFields
          let fBit : FrameCtx := ⟨bs1, bitFlag, bs2, bj⟩
          have hfBit : ValidFrameCtx fBit := ⟨hbs1, hbs2, hbj⟩
          let csCur := pushRChain rchain csV
          have hmDownL : microstep (.sf (.sfDone (.rfBitFrame caller acc) true))
              ⟨(bs1 ⋅ bitFlag) ⋅ ((bs2 ⋅ rest) ⋅ bj), csCur⟩ =
              .running (.downL1 (.toRfBitVal caller acc)) ⟨bs1 ⋅ bitFlag, .left ((bs2 ⋅ rest) ⋅ bj) :: csCur⟩ := by
            dsimp only [microstep, step, stepSf, onSfDone]
            rw [dif_neg hne11]
            rfl
          have sDownL := downL_steps (.toRfBitVal caller acc) bs1 bitFlag bs2 rest bj csCur _ hmDownL
          have sAlias1 : StepsTo 0 (.downLDone (.toRfBitVal caller acc))
              ⟨bitFlag, downLCrumbs bs1 rest bs2 bj csCur⟩
              (.sf (.sf0 (.rfBitVal caller acc))) ⟨bitFlag, downLCrumbs bs1 rest bs2 bj csCur⟩ :=
            StepsTo.of_alias rfl
          have sBitSf := checkStrictFrame_steps (.rfBitVal caller acc) ⟨bitFlag, downLCrumbs bs1 rest bs2 bj csCur⟩
          let b := strictFrameObs bitFlag
          let acc' := pushBit11 acc b hlt11
          have hmUpL : microstep (.sf (.sfDone (.rfBitVal caller acc) b))
              ⟨bitFlag, downLCrumbs bs1 rest bs2 bj csCur⟩ =
              .running (.up1 (.rfBitValBack caller acc')) ⟨bs1 ⋅ bitFlag, .left ((bs2 ⋅ rest) ⋅ bj) :: csCur⟩ := by
            dsimp only [microstep, step, stepSf, onSfDone]
            rw [dif_pos hlt11]
            rfl
          have sUpL := up_from_left_steps (.rfBitValBack caller acc') bs1 bitFlag bs2 rest bj csCur hobs _ hmUpL
          have sDownR := downR_steps (.toRfNext caller acc') bs1 bitFlag bs2 rest bj csCur
            (.upDone (.rfBitValBack caller acc') false) rfl
          have sAlias2 : StepsTo 0 (.downRDone (.toRfNext caller acc'))
              ⟨rest, pushRChain (fBit :: rchain) csV⟩
              (.sf (.sf0 (.rfBitFrame caller acc'))) ⟨rest, pushRChain (fBit :: rchain) csV⟩ :=
            StepsTo.of_alias rfl
          have hlen' : acc'.val.length + m = 11 := by
            dsimp only [acc', pushBit11]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          have hrlen' : (fBit :: rchain).length = acc'.val.length + 1 := by
            dsimp only [acc', pushBit11]
            simp only [List.length_cons, List.length_append, List.length_nil]
            omega
          have hall' : ∀ x ∈ fBit :: rchain, ValidFrameCtx x := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact hfBit
            · exact hall x hx'
          obtain ⟨out, houtEq, sRec⟩ := ih acc' (fBit :: rchain) rest csV hlen' hrlen' hall'
          have sAll := StepsTo.trans hsf
            (StepsTo.trans sDownL
              (StepsTo.trans sAlias1
                (StepsTo.trans sBitSf
                  (StepsTo.trans sUpL
                    (StepsTo.trans sDownR
                      (StepsTo.trans sAlias2 sRec))))))
          refine ⟨out, ?_, ?_⟩
          · rw [houtEq]
            dsimp only [acc', pushBit11, b]
            simp [obsReadFields, hobs, Option.map_map, Function.comp_def, List.append_assoc]
          · simpa [wrapRChain, fBit] using StepsTo.mono (by omega) sAll

theorem rfEntry_steps (caller : CellCaller) (vs1 vnext vs2 fields vj : Term) (csV : List Crumb)
    (hv : ValidFrameCtx ⟨vs1, vnext, vs2, vj⟩) :
    ∃ out : Option Bits11,
      out.map Subtype.val = obsReadFields 11 fields ∧
      StepsTo 860 (.downRDone (.toRfEntry caller))
        ⟨fields, downRCrumbs vs1 vnext vs2 vj csV⟩
        (.upDone (.rfClimb caller out ⟨0, by decide⟩) true)
        ⟨(vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj), csV⟩ := by
  have sAlias : StepsTo 0 (.downRDone (.toRfEntry caller))
      ⟨fields, pushRChain [⟨vs1, vnext, vs2, vj⟩] csV⟩
      (.sf (.sf0 (.rfBitFrame caller ⟨[], Nat.zero_le 11⟩)))
      ⟨fields, pushRChain [⟨vs1, vnext, vs2, vj⟩] csV⟩ :=
    StepsTo.of_alias rfl
  have hall : ∀ f ∈ ([⟨vs1, vnext, vs2, vj⟩] : List FrameCtx), ValidFrameCtx f := by
    intro f hf
    simp at hf
    subst hf
    exact hv
  obtain ⟨out, houtEq, sLoop⟩ :=
    rfBitFrame_loop_steps caller 11 ⟨[], Nat.zero_le 11⟩ [⟨vs1, vnext, vs2, vj⟩] fields csV
      rfl rfl hall
  refine ⟨out, ?_, ?_⟩
  · simpa using houtEq
  · simpa [pushRChain, wrapRChain] using StepsTo.mono (by omega) (StepsTo.trans sAlias sLoop)


/-! ### Subroutine `ReadCell` (`≤ 980 * leaves v0` ticks on EVERY tree) -/

def obsReadVersion11 (v : Term) : Option Cell8 :=
  if strictFrameObs v then
    match v with
    | .app (.app _ _) (.app (.app _ fields) _) =>
        match obsReadFields 11 fields with
        | some bs =>
            if hlen : bs.length = 11 then some (decodeBits11 ⟨bs, hlen⟩) else none
        | none => none
    | _ => none
  else none

def obsScanBottomUpAux : Nat → Term → Option Cell8
  | 0, _ => none
  | fuel + 1, t =>
      if strictFrameObs t then
        match t with
        | .app (.app _ next) _ =>
            match obsScanBottomUpAux fuel next with
            | some c => some c
            | none => obsReadVersion11 t
        | _ => none
      else none

def obsScanBottomUp (t : Term) : Option Cell8 :=
  obsScanBottomUpAux (leaves t) t

theorem obsScanBottomUpAux_unopened (fuel : Nat) {t : Term} (h : strictFrameObs t = false) :
    obsScanBottomUpAux fuel t = none := by
  cases fuel with
  | zero => rfl
  | succ _ => simp [obsScanBottomUpAux, h]

theorem obsScanBottomUp_unopened {t : Term} (h : strictFrameObs t = false) :
    obsScanBottomUp t = none :=
  obsScanBottomUpAux_unopened (leaves t) h

theorem obsScanBottomUpAux_fuel :
    ∀ (fuel1 fuel2 : Nat) (t : Term),
      leaves t ≤ fuel1 → leaves t ≤ fuel2 →
      obsScanBottomUpAux fuel1 t = obsScanBottomUpAux fuel2 t := by
  intro fuel1
  induction fuel1 with
  | zero =>
      intro _ t h1 _
      have hp := leaves_pos t
      exact False.elim (by omega)
  | succ m1 ih =>
      intro fuel2 t h1 h2
      cases fuel2 with
      | zero =>
          have hp := leaves_pos t
          exact False.elim (by omega)
      | succ m2 =>
          cases hobs : strictFrameObs t with
          | false => simp [obsScanBottomUpAux, hobs]
          | true =>
              obtain ⟨vs1, next, vs2, fields, vj, rfl, _, _, _⟩ := strictFrameObs_decomp hobs
              have hn : leaves next + 4 ≤ leaves ((vs1 ⋅ next) ⋅ ((vs2 ⋅ fields) ⋅ vj)) := by
                have := leaves_pos vs1
                have := leaves_pos vs2
                have := leaves_pos fields
                have := leaves_pos vj
                simp only [leaves]
                omega
              simp only [obsScanBottomUpAux, hobs, ↓reduceIte]
              rw [ih m2 next (by omega) (by omega)]

theorem obsScanBottomUp_frame (vs1 next vs2 fields vj : Term)
    (hsf : strictFrameObs ((vs1 ⋅ next) ⋅ ((vs2 ⋅ fields) ⋅ vj)) = true) :
    obsScanBottomUp ((vs1 ⋅ next) ⋅ ((vs2 ⋅ fields) ⋅ vj)) =
      match obsScanBottomUp next with
      | some c => some c
      | none => obsReadVersion11 ((vs1 ⋅ next) ⋅ ((vs2 ⋅ fields) ⋅ vj)) := by
  let t := (vs1 ⋅ next) ⋅ ((vs2 ⋅ fields) ⋅ vj)
  let m := leaves t - 1
  have h1 := leaves_pos vs1
  have h2 := leaves_pos vs2
  have h3 := leaves_pos fields
  have h4 := leaves_pos vj
  have h5 := leaves_pos next
  have ht : leaves t = m + 1 := by
    dsimp only [m, t]; simp only [leaves]; omega
  have hnextLe : leaves next ≤ m := by
    dsimp only [m, t]; simp only [leaves]; omega
  have hstep : obsScanBottomUpAux (leaves t) t =
      match obsScanBottomUpAux m next with
      | some c => some c
      | none => obsReadVersion11 t := by
    rw [ht]
    dsimp only [obsScanBottomUpAux, t]
    simp only [hsf, ↓reduceIte]
  unfold obsScanBottomUp
  change obsScanBottomUpAux (leaves t) t =
    match obsScanBottomUpAux (leaves next) next with
    | some c => some c
    | none => obsReadVersion11 t
  rw [hstep, obsScanBottomUpAux_fuel m (leaves next) next hnextLe (Nat.le_refl _)]

theorem obsScanBottomUp_wrapLChain_some (lchain : List FrameCtx) (u : Term) (cell : Cell8)
    (hall : ∀ f ∈ lchain, ValidFrameCtx f)
    (hu : obsScanBottomUp u = some cell) :
    obsScanBottomUp (wrapLChain lchain u) = some cell := by
  induction lchain generalizing u with
  | nil => exact hu
  | cons f fs ih =>
      have hf := hall f (by simp)
      have hfs : ∀ x ∈ fs, ValidFrameCtx x := fun x hx => hall x (by simp [hx])
      have hsf := validFrameCtx_strictL f u hf
      have hu' : obsScanBottomUp ((f.s1 ⋅ u) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j)) = some cell := by
        rw [obsScanBottomUp_frame f.s1 u f.s2 f.other f.j hsf, hu]
      exact ih ((f.s1 ⋅ u) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j)) hfs hu'

/-- `rcHaveTestParent` climbs `lchain` back to `C` and returns `cell`. -/
theorem rcHave_climb_steps (caller : CellCaller) (cell : Cell8)
    (ps1 pl ps2 pj : Term) (csP : List Crumb) (hpj : s2Obs pj = false) :
    ∀ (lchain : List FrameCtx) (x : Term) (cStart : Control),
      (∀ f ∈ lchain, ValidFrameCtx f) →
      startLClimbProp (.rcHaveTestParent caller cell) ps1 pl ps2 pj csP lchain x cStart →
      StepsTo (19 * lchain.length + 22) cStart
        ⟨x, pushLChain lchain (downRCrumbs ps1 pl ps2 pj csP)⟩
        (.downRDone (.toRcDone caller cell))
        ⟨wrapLChain lchain x, downRCrumbs ps1 pl ps2 pj csP⟩ := by
  intro lchain
  induction lchain with
  | nil =>
      intro x cStart _ hstart
      dsimp only [startLClimbProp] at hstart
      have sUp := up_from_right_steps (.rcHaveTestParent caller cell) ps1 pl ps2 x pj csP hpj cStart hstart
      have sDown := downR_steps (.toRcDone caller cell) ps1 pl ps2 x pj csP
        (.upDone (.rcHaveTestParent caller cell) true) rfl
      simpa [pushLChain, wrapLChain] using StepsTo.mono (by omega) (StepsTo.trans sUp sDown)
  | cons f fs ih =>
      intro x cStart hall hstart
      dsimp only [startLClimbProp] at hstart
      have hf := hall f (by simp)
      have hfs : ∀ y ∈ fs, ValidFrameCtx y := fun y hy => hall y (by simp [hy])
      have hsfP := validFrameCtx_strictL f x hf
      have sUp := up_from_left_steps (.rcHaveTestParent caller cell) f.s1 x f.s2 f.other f.j
        (pushLChain fs (downRCrumbs ps1 pl ps2 pj csP)) hsfP cStart hstart
      have hmNext : startLClimbProp (.rcHaveTestParent caller cell) ps1 pl ps2 pj csP fs
          ((f.s1 ⋅ x) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j))
          (.upDone (.rcHaveTestParent caller cell) false) := by
        cases fs <;> rfl
      have sRest := ih ((f.s1 ⋅ x) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j))
        (.upDone (.rcHaveTestParent caller cell) false) hfs hmNext
      simp only [List.length_cons, wrapLChain]
      exact StepsTo.mono (by omega) (StepsTo.trans sUp sRest)

/-- `rcSearchTestParent` climbs `lchain` from `X`, computing `(obsScanBottomUp v0).getD defaultCell8`
    and returning to `⟨C, csC⟩`. -/
theorem rcSearch_climb_steps (caller : CellCaller)
    (ps1 pl ps2 pj : Term) (csP : List Crumb) (hpj : s2Obs pj = false) :
    ∀ (lchain : List FrameCtx) (x : Term) (cStart : Control),
      (∀ f ∈ lchain, ValidFrameCtx f) →
      (∀ f rest, lchain = f :: rest →
        ∃ vs1 vnext vs2 fields vj,
          x = (vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj) ∧
          ValidFrameCtx ⟨vs1, vnext, vs2, vj⟩ ∧
          obsScanBottomUp vnext = none) →
      startLClimbProp (.rcSearchTestParent caller) ps1 pl ps2 pj csP lchain x cStart →
      ∃ resCell : Cell8,
        (∀ lchainV fC, lchain = lchainV ++ [fC] →
          resCell = (obsScanBottomUp (wrapLChain lchainV x)).getD defaultCell8) ∧
        (lchain = [] → resCell = defaultCell8) ∧
        StepsTo (903 * lchain.length + 22) cStart
          ⟨x, pushLChain lchain (downRCrumbs ps1 pl ps2 pj csP)⟩
          (.downRDone (.toRcDone caller resCell))
          ⟨wrapLChain lchain x, downRCrumbs ps1 pl ps2 pj csP⟩ := by
  intro lchain
  induction lchain with
  | nil =>
      intro x cStart _ _ hstart
      dsimp only [startLClimbProp] at hstart
      have sUp := up_from_right_steps (.rcSearchTestParent caller) ps1 pl ps2 x pj csP hpj cStart hstart
      have sDown := downR_steps (.toRcDone caller defaultCell8) ps1 pl ps2 x pj csP
        (.upDone (.rcSearchTestParent caller) true) rfl
      refine ⟨defaultCell8, ?_, fun _ => rfl, ?_⟩
      · intro lchainV fC heq
        cases lchainV <;> simp at heq
      · simpa [pushLChain, wrapLChain] using StepsTo.mono (by omega) (StepsTo.trans sUp sDown)
  | cons f fs ih =>
      intro x cStart hall hxDecomp hstart
      dsimp only [startLClimbProp] at hstart
      obtain ⟨vs1, vnext, vs2, fields, vj, rfl, hvCtx, hvnextNone⟩ := hxDecomp f fs rfl
      have hf := hall f (by simp)
      have hfs : ∀ y ∈ fs, ValidFrameCtx y := fun y hy => hall y (by simp [hy])
      have hsfParent := validFrameCtx_strictL f ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) hf
      let csC := downRCrumbs ps1 pl ps2 pj csP
      let csParent := pushLChain fs csC
      have sUp1 := up_from_left_steps (.rcSearchTestParent caller) f.s1
        ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) f.s2 f.other f.j csParent hsfParent cStart hstart
      have sDownL := downL_steps (.toRcInspect caller) f.s1
        ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) f.s2 f.other f.j csParent
        (.upDone (.rcSearchTestParent caller) false) rfl
      have sDownR := downR_steps (.toRfEntry caller) vs1 vnext vs2 fields vj
        (downLCrumbs f.s1 f.other f.s2 f.j csParent) (.downLDone (.toRcInspect caller)) rfl
      obtain ⟨out, houtEq, sRf⟩ := rfEntry_steps caller vs1 vnext vs2 fields vj
        (downLCrumbs f.s1 f.other f.s2 f.j csParent) hvCtx
      have sUp2 := up_from_left_steps (.rcAfterRf caller (out.map decodeBits11))
        f.s1 ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) f.s2 f.other f.j csParent hsfParent
        (.upDone (.rfClimb caller out ⟨0, by decide⟩) true) rfl
      have sStepAll := StepsTo.trans sUp1
        (StepsTo.trans sDownL (StepsTo.trans sDownR (StepsTo.trans sRf sUp2)))
      have hsfCur : strictFrameObs ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) = true :=
        validFrameCtx_strictR ⟨vs1, vnext, vs2, vj⟩ fields hvCtx
      have houtVer : out.map decodeBits11 = obsReadVersion11 ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) := by
        unfold obsReadVersion11
        simp only [hsfCur, ↓reduceIte]
        cases hout : out with
        | none =>
            simp only [hout, Option.map] at houtEq ⊢
            rw [← houtEq]
        | some bits =>
            simp only [hout, Option.map] at houtEq ⊢
            rw [← houtEq]
            dsimp only []
            rw [dif_pos bits.property]
      have hscanCur : obsScanBottomUp ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) = out.map decodeBits11 := by
        rw [obsScanBottomUp_frame vs1 vnext vs2 fields vj hsfCur, hvnextNone, houtVer]
      let pTerm := (f.s1 ⋅ ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj))) ⋅ ((f.s2 ⋅ f.other) ⋅ f.j)
      cases houtOpt : out.map decodeBits11 with
      | some cell =>
          have hmHave : startLClimbProp (.rcHaveTestParent caller cell) ps1 pl ps2 pj csP fs pTerm
              (.upDone (.rcAfterRf caller (some cell)) false) := by
            cases fs <;> rfl
          rw [houtOpt] at sStepAll
          have sHave := rcHave_climb_steps caller cell ps1 pl ps2 pj csP hpj fs pTerm
            (.upDone (.rcAfterRf caller (some cell)) false) hfs hmHave
          refine ⟨cell, ?_, ?_, ?_⟩
          · intro lchainV fC heq
            cases lchainV with
            | nil =>
                simp at heq
                rcases heq with ⟨rfl, _⟩
                simp only [wrapLChain]
                rw [hscanCur, houtOpt]
                rfl
            | cons fv lvRest =>
                simp only [List.cons_append, List.cons.injEq] at heq
                rcases heq with ⟨rfl, hfsEq⟩
                have hlvValid : ∀ y ∈ f :: lvRest, ValidFrameCtx y := by
                  intro y hy
                  apply hall y
                  rw [List.mem_cons] at hy ⊢
                  rcases hy with rfl | hy'
                  · exact Or.inl rfl
                  · right; rw [hfsEq]; exact List.mem_append_left _ hy'
                have hallSome := obsScanBottomUp_wrapLChain_some (f :: lvRest)
                  ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) cell hlvValid (hscanCur.trans houtOpt)
                rw [hallSome]
                rfl
          · intro h; cases h
          · simp only [List.length_cons, wrapLChain]
            exact StepsTo.mono (by omega) (StepsTo.trans sStepAll sHave)
      | none =>
          have hmSearch : startLClimbProp (.rcSearchTestParent caller) ps1 pl ps2 pj csP fs pTerm
              (.upDone (.rcAfterRf caller none) false) := by
            cases fs <;> rfl
          rw [houtOpt] at sStepAll
          have hpDecomp : ∀ f2 rest2, fs = f2 :: rest2 →
              ∃ ws1 wnext ws2 wfields wj,
                pTerm = (ws1 ⋅ wnext) ⋅ ((ws2 ⋅ wfields) ⋅ wj) ∧
                ValidFrameCtx ⟨ws1, wnext, ws2, wj⟩ ∧
                obsScanBottomUp wnext = none := by
            intro _ _ _
            exact ⟨f.s1, (vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj), f.s2, f.other, f.j, rfl, hf,
              hscanCur.trans houtOpt⟩
          obtain ⟨resCell, hresNonEmpty, hresEmpty, sRest⟩ :=
            ih pTerm (.upDone (.rcAfterRf caller none) false) hfs hpDecomp hmSearch
          refine ⟨resCell, ?_, ?_, ?_⟩
          · intro lchainV fC heq
            cases lchainV with
            | nil =>
                simp at heq
                rcases heq with ⟨rfl, hfsNil⟩
                rw [hresEmpty hfsNil]
                simp only [wrapLChain]
                rw [hscanCur, houtOpt]
                rfl
            | cons fv lvRest =>
                simp only [List.cons_append, List.cons.injEq] at heq
                rcases heq with ⟨rfl, hfsEq⟩
                exact hresNonEmpty lvRest fC hfsEq
          · intro h; cases h
          · simp only [List.length_cons, wrapLChain]
            exact StepsTo.mono (by omega) (StepsTo.trans sStepAll sRest)

/-- Descending `v0`'s `L`-spine in `.rcDown caller` and climbing back via `rcSearch_climb_steps`
    computes `(obsScanBottomUp v0).getD defaultCell8` and restores `⟨C, csC⟩` in `≤ 980 * leaves v0` ticks. -/
theorem rcDown_fuel_steps (caller : CellCaller)
    (ps1 pl ps2 pj : Term) (csP : List Crumb) (hpj : s2Obs pj = false)
    (fC : FrameCtx) (hfC : ValidFrameCtx fC) :
    ∀ (fuel : Nat) (u : Term) (lchainV : List FrameCtx),
      leaves u ≤ fuel →
      (∀ f ∈ lchainV, ValidFrameCtx f) →
      StepsTo (921 * lchainV.length + 980 * leaves u)
        (.sf (.sf0 (.rcDown caller)))
        ⟨u, pushLChain (lchainV ++ [fC]) (downRCrumbs ps1 pl ps2 pj csP)⟩
        (.downRDone (.toRcDone caller ((obsScanBottomUp (wrapLChain lchainV u)).getD defaultCell8)))
        ⟨wrapLChain (lchainV ++ [fC]) u, downRCrumbs ps1 pl ps2 pj csP⟩ := by
  intro fuel
  induction fuel with
  | zero =>
      intro u _ hle _
      have hp := leaves_pos u
      exact False.elim (by omega)
  | succ m ih =>
      intro u lchainV hle hallV
      let csC := downRCrumbs ps1 pl ps2 pj csP
      have sSf := checkStrictFrame_steps (.rcDown caller) ⟨u, pushLChain (lchainV ++ [fC]) csC⟩
      cases hobs : strictFrameObs u with
      | false =>
          rw [hobs] at sSf
          have hleavesGe1 := leaves_pos u
          cases lchainV with
          | nil =>
              simp only [List.nil_append] at sSf ⊢
              have sUpBot := up_from_left_steps (.rcBottomToPrev caller) fC.s1 u fC.s2 fC.other fC.j csC
                (validFrameCtx_strictL fC u hfC) (.sf (.sfDone (.rcDown caller) false)) rfl
              obtain ⟨resCell, _, hresNil, sSearch⟩ :=
                rcSearch_climb_steps caller ps1 pl ps2 pj csP hpj []
                  ((fC.s1 ⋅ u) ⋅ ((fC.s2 ⋅ fC.other) ⋅ fC.j))
                  (.upDone (.rcBottomToPrev caller) false)
                  (by intro _ h; simp at h) (by intro _ _ h; cases h) rfl
              rw [hresNil rfl] at sSearch
              have hlen0 : ([] : List FrameCtx).length = 0 := rfl
              rw [hlen0] at sSearch ⊢
              simpa [wrapLChain, obsScanBottomUp_unopened hobs] using
                StepsTo.mono (by omega) (StepsTo.trans sSf (StepsTo.trans sUpBot sSearch))
          | cons fv lvRest =>
              simp only [List.cons_append] at sSf ⊢
              have hfv := hallV fv (by simp)
              have sUpBot := up_from_left_steps (.rcBottomToPrev caller) fv.s1 u fv.s2 fv.other fv.j
                (pushLChain (lvRest ++ [fC]) csC) (validFrameCtx_strictL fv u hfv)
                (.sf (.sfDone (.rcDown caller) false)) rfl
              let xPrev := (fv.s1 ⋅ u) ⋅ ((fv.s2 ⋅ fv.other) ⋅ fv.j)
              have hallRest : ∀ y ∈ lvRest ++ [fC], ValidFrameCtx y := by
                intro y hy
                rcases List.mem_append.mp hy with hy1 | hy2
                · exact hallV y (by simp [hy1])
                · simp at hy2; subst hy2; exact hfC
              have hmSearch : startLClimbProp (.rcSearchTestParent caller) ps1 pl ps2 pj csP
                  (lvRest ++ [fC]) xPrev (.upDone (.rcBottomToPrev caller) false) := by
                cases lvRest <;> rfl
              obtain ⟨resCell, hresNonEmpty, _, sSearch⟩ :=
                rcSearch_climb_steps caller ps1 pl ps2 pj csP hpj (lvRest ++ [fC]) xPrev
                  (.upDone (.rcBottomToPrev caller) false) hallRest
                  (fun _ _ _ => ⟨fv.s1, u, fv.s2, fv.other, fv.j, rfl, hfv, obsScanBottomUp_unopened hobs⟩)
                  hmSearch
              have hresEq := hresNonEmpty lvRest fC rfl
              rw [hresEq] at sSearch
              simp only [List.length_cons, wrapLChain]
              have hlenBound : 16 + (19 + (903 * (lvRest ++ [fC]).length + 22)) ≤
                  921 * (lvRest.length + 1) + 980 * leaves u := by
                simp only [List.length_append, List.length_cons, List.length_nil]
                omega
              exact StepsTo.mono hlenBound (StepsTo.trans sSf (StepsTo.trans sUpBot sSearch))
      | true =>
          rw [hobs] at sSf
          obtain ⟨vs1, vnext, vs2, fields, vj, rfl, hvs1, hvs2, hvj⟩ := strictFrameObs_decomp hobs
          let fvNew : FrameCtx := ⟨vs1, fields, vs2, vj⟩
          have hfvNew : ValidFrameCtx fvNew := ⟨hvs1, hvs2, hvj⟩
          have sDownL := downL_steps (.toRcDown caller) vs1 vnext vs2 fields vj
            (pushLChain (lchainV ++ [fC]) csC) (.sf (.sfDone (.rcDown caller) true)) rfl
          have sAlias : StepsTo 0 (.downLDone (.toRcDown caller))
              ⟨vnext, pushLChain ((fvNew :: lchainV) ++ [fC]) csC⟩
              (.sf (.sf0 (.rcDown caller)))
              ⟨vnext, pushLChain ((fvNew :: lchainV) ++ [fC]) csC⟩ :=
            StepsTo.of_alias rfl
          have hvnextLeaves : leaves vnext + 4 ≤ leaves ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) := by
            have := leaves_pos vs1
            have := leaves_pos vs2
            have := leaves_pos fields
            have := leaves_pos vj
            simp only [leaves]
            omega
          have hallNew : ∀ y ∈ fvNew :: lchainV, ValidFrameCtx y := by
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hfvNew
            · exact hallV y hy'
          have sRec := ih vnext (fvNew :: lchainV) (by omega) hallNew
          have sTot := StepsTo.trans sSf (StepsTo.trans sDownL (StepsTo.trans sAlias sRec))
          simp only [List.cons_append, List.length_cons, wrapLChain] at sTot ⊢
          exact StepsTo.mono (by omega) sTot

theorem readCell_steps (caller : CellCaller)
    (ps1 pl ps2 pj : Term) (csP : List Crumb) (hpj : s2Obs pj = false)
    (cs1 v0 cs2 restCell cj : Term) (hC : ValidFrameCtx ⟨cs1, restCell, cs2, cj⟩) :
    StepsTo (980 * leaves v0)
      (.downLDone (.toRcStart caller))
      ⟨v0, downLCrumbs cs1 restCell cs2 cj (downRCrumbs ps1 pl ps2 pj csP)⟩
      (.downRDone (.toRcDone caller ((obsScanBottomUp v0).getD defaultCell8)))
      ⟨(cs1 ⋅ v0) ⋅ ((cs2 ⋅ restCell) ⋅ cj), downRCrumbs ps1 pl ps2 pj csP⟩ := by
  have sAlias : StepsTo 0
      (.downLDone (.toRcStart caller))
      ⟨v0, pushLChain ([] ++ [⟨cs1, restCell, cs2, cj⟩]) (downRCrumbs ps1 pl ps2 pj csP)⟩
      (.sf (.sf0 (.rcDown caller)))
      ⟨v0, pushLChain ([] ++ [⟨cs1, restCell, cs2, cj⟩]) (downRCrumbs ps1 pl ps2 pj csP)⟩ :=
    StepsTo.of_alias rfl
  have sLoop := rcDown_fuel_steps caller ps1 pl ps2 pj csP hpj
    ⟨cs1, restCell, cs2, cj⟩ hC (leaves v0) v0 [] (Nat.le_refl _) (by intro _ h; simp at h)
  have hlen0 : ([] : List FrameCtx).length = 0 := rfl
  rw [hlen0] at sLoop
  simpa [pushLChain, wrapLChain] using StepsTo.mono (by omega) (StepsTo.trans sAlias sLoop)


/-! ### Subroutines `CheckCommitted11`, `AppendFld`, `AppendVer`, `FrontierWalk`, & `Rewind` -/

def obsHasFrames : Nat → Term → Bool
  | 0, _ => true
  | n + 1, t =>
      if strictFrameObs t then
        match t with
        | .app _ (.app (.app _ rest) _) => obsHasFrames n rest
        | _ => false
      else false

theorem chkCommClimb_steps (desired : Bits11) (committed : Bool) :
    ∀ (rchain : List FrameCtx) (rem : Fin 12) (u : Term) (csV : List Crumb) (cStart : Control),
      (∀ f ∈ rchain, ValidFrameCtx f) →
      rchain.length = rem.val + 1 →
      startRClimbProp (.chkCommClimb desired committed rem) rchain u csV cStart →
      StepsTo (19 * (rem.val + 1)) cStart ⟨u, pushRChain rchain csV⟩
        (.upDone (.chkCommClimb desired committed ⟨0, by decide⟩) true)
        ⟨wrapRChain rchain u, csV⟩ := by
  intro rchain
  induction rchain with
  | nil =>
      intro rem _ _ _ _ _ hstart
      exact False.elim hstart
  | cons f fs ih =>
      intro rem u csV cStart hall hlen hstart
      dsimp only [startRClimbProp] at hstart
      have hf : ValidFrameCtx f := hall f (by simp)
      have hfs : ∀ x ∈ fs, ValidFrameCtx x := fun x hx => hall x (by simp [hx])
      have hup1 := up_from_right_steps (.chkCommClimb desired committed rem) f.s1 f.other f.s2 u f.j
        (pushRChain fs csV) hf.2.2 cStart hstart
      if hrem0 : rem.val = 0 then
        have hfsNil : fs = [] := by
          cases fs with
          | nil => rfl
          | cons _ _ => simp only [List.length_cons] at hlen; omega
        subst fs
        have hremEq : rem = ⟨0, by decide⟩ := by apply Fin.ext; exact hrem0
        subst hremEq
        simpa [pushRChain, wrapRChain] using hup1
      else
        let rem' : Fin 12 := ⟨rem.val - 1, by omega⟩
        have hlen' : fs.length = rem'.val + 1 := by
          simp only [List.length_cons] at hlen
          dsimp only [rem']
          omega
        cases fs with
        | nil => cases hlen'
        | cons f2 fs2 =>
            have hmNext : startRClimbProp (.chkCommClimb desired committed rem') (f2 :: fs2)
                ((f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j)) csV
                (.upDone (.chkCommClimb desired committed rem) true) := by
              dsimp only [startRClimbProp, microstep, step, onUpDone]
              rw [dif_neg hrem0]
              rfl
            have hrest := ih rem' ((f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j)) csV
              (.upDone (.chkCommClimb desired committed rem) true) hfs hlen' hmNext
            have htot := StepsTo.trans hup1 hrest
            have hbound : 19 + 19 * (rem'.val + 1) ≤ 19 * (rem.val + 1) := by
              dsimp only [rem']
              omega
            simpa [pushRChain, wrapRChain] using StepsTo.mono hbound htot

theorem chkComm_loop_steps (desired : Bits11) :
    ∀ (k : Nat) (idx : Fin 12) (rchain : List FrameCtx) (curFields : Term) (csV : List Crumb),
      idx.val + k = 11 →
      rchain.length = idx.val + 1 →
      (∀ f ∈ rchain, ValidFrameCtx f) →
      StepsTo (19 * k + 244) (.sf (.sf0 (.chkComm desired idx)))
        ⟨curFields, pushRChain rchain csV⟩
        (.upDone (.chkCommClimb desired (obsHasFrames (k + 1) curFields) ⟨0, by decide⟩) true)
        ⟨wrapRChain rchain curFields, csV⟩ := by
  intro k
  induction k with
  | zero =>
      intro idx rchain curFields csV hsum hrlen hall
      have hidx11 : idx = ⟨11, by decide⟩ := by apply Fin.ext; dsimp only []; omega
      subst hidx11
      have hsf := checkStrictFrame_steps (.chkComm desired ⟨11, by decide⟩) ⟨curFields, pushRChain rchain csV⟩
      cases rchain with
      | nil => cases hrlen
      | cons f fs =>
          cases hobs : strictFrameObs curFields with
          | false =>
              rw [hobs] at hsf
              have hfalse : obsHasFrames 1 curFields = false := by simp [obsHasFrames, hobs]
              rw [hfalse]
              have hclimb := chkCommClimb_steps desired false (f :: fs) ⟨11, by decide⟩ curFields csV
                (.sf (.sfDone (.chkComm desired ⟨11, by decide⟩) false)) hall hrlen rfl
              exact StepsTo.mono (by omega) (StepsTo.trans hsf hclimb)
          | true =>
              rw [hobs] at hsf
              obtain ⟨s1', l', s2', r', j', hcf, _, _, _⟩ := strictFrameObs_decomp hobs
              have htrue : obsHasFrames 1 curFields = true := by
                conv => lhs; unfold obsHasFrames
                rw [hobs]
                simp [hcf, obsHasFrames]
              rw [htrue]
              have hclimb := chkCommClimb_steps desired true (f :: fs) ⟨11, by decide⟩ curFields csV
                (.sf (.sfDone (.chkComm desired ⟨11, by decide⟩) true)) hall hrlen rfl
              exact StepsTo.mono (by omega) (StepsTo.trans hsf hclimb)
  | succ m ih =>
      intro idx rchain curFields csV hsum hrlen hall
      have hnextLt : idx.val + 1 < 12 := by omega
      have hsf := checkStrictFrame_steps (.chkComm desired idx) ⟨curFields, pushRChain rchain csV⟩
      cases hobs : strictFrameObs curFields with
      | false =>
          rw [hobs] at hsf
          cases rchain with
          | nil => cases hrlen
          | cons f fs =>
              have hfalse : obsHasFrames (m + 2) curFields = false := by simp [obsHasFrames, hobs]
              rw [hfalse]
              have hclimb := chkCommClimb_steps desired false (f :: fs) idx curFields csV
                (.sf (.sfDone (.chkComm desired idx) false)) hall hrlen rfl
              exact StepsTo.mono (by omega) (StepsTo.trans hsf hclimb)
      | true =>
          rw [hobs] at hsf
          obtain ⟨bs1, bflag, bs2, rest, bj, rfl, hbs1, hbs2, hbj⟩ := strictFrameObs_decomp hobs
          let fBit : FrameCtx := ⟨bs1, bflag, bs2, bj⟩
          have hfBit : ValidFrameCtx fBit := ⟨hbs1, hbs2, hbj⟩
          let idx' : Fin 12 := ⟨idx.val + 1, hnextLt⟩
          have hmDownR : microstep (.sf (.sfDone (.chkComm desired idx) true))
              ⟨(bs1 ⋅ bflag) ⋅ ((bs2 ⋅ rest) ⋅ bj), pushRChain rchain csV⟩ =
              .running (.downR1 (.toChkCommNext desired idx'))
                ⟨(bs2 ⋅ rest) ⋅ bj, .right (bs1 ⋅ bflag) :: pushRChain rchain csV⟩ := by
            dsimp only [microstep, step, stepSf, onSfDone]
            rw [dif_pos hnextLt]
            rfl
          have sDownR := downR_steps (.toChkCommNext desired idx') bs1 bflag bs2 rest bj
            (pushRChain rchain csV) _ hmDownR
          have sAlias : StepsTo 0 (.downRDone (.toChkCommNext desired idx'))
              ⟨rest, pushRChain (fBit :: rchain) csV⟩
              (.sf (.sf0 (.chkComm desired idx'))) ⟨rest, pushRChain (fBit :: rchain) csV⟩ :=
            StepsTo.of_alias rfl
          have hall' : ∀ x ∈ fBit :: rchain, ValidFrameCtx x := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact hfBit
            · exact hall x hx'
          have sRec := ih idx' (fBit :: rchain) rest csV (by dsimp [idx']; omega)
            (by simp only [List.length_cons, idx']; omega) hall'
          have hobsEq : obsHasFrames (m + 2) ((bs1 ⋅ bflag) ⋅ ((bs2 ⋅ rest) ⋅ bj)) = obsHasFrames (m + 1) rest := by
            conv => lhs; unfold obsHasFrames
            simp [hobs]
          rw [hobsEq]
          simpa [wrapRChain, fBit] using
            StepsTo.mono (by omega) (StepsTo.trans hsf (StepsTo.trans sDownR (StepsTo.trans sAlias sRec)))

theorem chkCommEntry_steps (desired : Bits11) (vs1 vnext vs2 fields vj : Term) (csV : List Crumb)
    (hv : ValidFrameCtx ⟨vs1, vnext, vs2, vj⟩) :
    StepsTo 453 (.downRDone (.toChkComm desired))
      ⟨fields, downRCrumbs vs1 vnext vs2 vj csV⟩
      (.upDone (.chkCommClimb desired (obsHasFrames 12 fields) ⟨0, by decide⟩) true)
      ⟨(vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj), csV⟩ := by
  have sAlias : StepsTo 0 (.downRDone (.toChkComm desired))
      ⟨fields, pushRChain [⟨vs1, vnext, vs2, vj⟩] csV⟩
      (.sf (.sf0 (.chkComm desired ⟨0, by decide⟩)))
      ⟨fields, pushRChain [⟨vs1, vnext, vs2, vj⟩] csV⟩ :=
    StepsTo.of_alias rfl
  have hall : ∀ f ∈ ([⟨vs1, vnext, vs2, vj⟩] : List FrameCtx), ValidFrameCtx f := by
    intro f hf; simp at hf; subst hf; exact hv
  have sLoop := chkComm_loop_steps desired 11 ⟨0, by decide⟩ [⟨vs1, vnext, vs2, vj⟩] fields csV
    rfl rfl hall
  simpa [pushRChain, wrapRChain] using StepsTo.mono (by omega) (StepsTo.trans sAlias sLoop)

theorem appendFld_valid :
    ∀ (bits : List Bool) (hle : bits.length ≤ 11) (cur : Cursor),
      ValidTermination (56 * bits.length + 5 * leaves (rebuild cur) + 43)
        (.sf (.sf0 (.appendFldNode ⟨bits, hle⟩))) cur := by
  intro bits
  induction bits with
  | nil =>
      intro hle cur
      have sSf := checkStrictFrame_steps (.appendFldNode ⟨[], hle⟩) cur
      cases hobs : strictFrameObs cur.focus with
      | true =>
          rw [hobs] at sSf
          have sAb : StepsTo 0 (.sf (.sfDone (.appendFldNode ⟨[], hle⟩) true)) cur (.euler .abortToRoot) cur :=
            StepsTo.of_alias rfl
          have hvt := StepsTo.toValidTermination (StepsTo.trans sSf sAb) (abortToRoot_valid cur)
          exact validTermination_mono (by simp; omega) hvt
      | false =>
          rw [hobs] at sSf
          have sOp : StepsTo 0 (.sf (.sfDone (.appendFldNode ⟨[], hle⟩) false)) cur (.openSub .pf0) cur :=
            StepsTo.of_alias rfl
          have hvt := StepsTo.toValidTermination (StepsTo.trans sSf sOp) (openAndContract_valid cur)
          exact validTermination_mono (by simp; omega) hvt
  | cons b bs ih =>
      intro hle cur
      have hbs : bs.length ≤ 11 := by simp at hle; omega
      have sSf := checkStrictFrame_steps (.appendFldNode ⟨b :: bs, hle⟩) cur
      cases hobs : strictFrameObs cur.focus with
      | false =>
          rw [hobs] at sSf
          have sOp : StepsTo 0 (.sf (.sfDone (.appendFldNode ⟨b :: bs, hle⟩) false)) cur (.openSub .pf0) cur :=
            StepsTo.of_alias rfl
          have hvt := StepsTo.toValidTermination (StepsTo.trans sSf sOp) (openAndContract_valid cur)
          exact validTermination_mono (by simp; omega) hvt
      | true =>
          rw [hobs] at sSf
          rcases cur with ⟨f, cs⟩
          obtain ⟨fs1, flag, fs2, rest, fj, rfl, hfs1, hfs2, hfj⟩ := strictFrameObs_decomp hobs
          cases b with
          | false =>
              have sDownR := downR_steps (.toAppendFld ⟨bs, hbs⟩) fs1 flag fs2 rest fj cs
                (.sf (.sfDone (.appendFldNode ⟨false :: bs, hle⟩) true)) rfl
              have sAlias : StepsTo 0 (.downRDone (.toAppendFld ⟨bs, hbs⟩))
                  ⟨rest, downRCrumbs fs1 flag fs2 fj cs⟩
                  (.sf (.sf0 (.appendFldNode ⟨bs, hbs⟩)))
                  ⟨rest, downRCrumbs fs1 flag fs2 fj cs⟩ :=
                StepsTo.of_alias rfl
              have hvt := ih hbs ⟨rest, downRCrumbs fs1 flag fs2 fj cs⟩
              have hreb : rebuild ⟨rest, downRCrumbs fs1 flag fs2 fj cs⟩ =
                  rebuild ⟨(fs1 ⋅ flag) ⋅ ((fs2 ⋅ rest) ⋅ fj), cs⟩ := rfl
              rw [hreb] at hvt
              have htot := StepsTo.toValidTermination (StepsTo.trans sSf (StepsTo.trans sDownR sAlias)) hvt
              exact validTermination_mono (by simp; omega) htot
          | true =>
              have sDownL := downL_steps (.toAppendFldFlag ⟨bs, hbs⟩) fs1 flag fs2 rest fj cs
                (.sf (.sfDone (.appendFldNode ⟨true :: bs, hle⟩) true)) rfl
              have sAlias1 : StepsTo 0 (.downLDone (.toAppendFldFlag ⟨bs, hbs⟩))
                  ⟨flag, downLCrumbs fs1 rest fs2 fj cs⟩
                  (.sf (.sf0 (.appendFldFlag ⟨bs, hbs⟩)))
                  ⟨flag, downLCrumbs fs1 rest fs2 fj cs⟩ :=
                StepsTo.of_alias rfl
              have sFlagSf := checkStrictFrame_steps (.appendFldFlag ⟨bs, hbs⟩)
                ⟨flag, downLCrumbs fs1 rest fs2 fj cs⟩
              cases hflag : strictFrameObs flag with
              | false =>
                  rw [hflag] at sFlagSf
                  have sOp : StepsTo 0 (.sf (.sfDone (.appendFldFlag ⟨bs, hbs⟩) false))
                      ⟨flag, downLCrumbs fs1 rest fs2 fj cs⟩
                      (.openSub .pf0) ⟨flag, downLCrumbs fs1 rest fs2 fj cs⟩ :=
                    StepsTo.of_alias rfl
                  have hvt := openAndContract_valid ⟨flag, downLCrumbs fs1 rest fs2 fj cs⟩
                  have hreb : rebuild ⟨flag, downLCrumbs fs1 rest fs2 fj cs⟩ =
                      rebuild ⟨(fs1 ⋅ flag) ⋅ ((fs2 ⋅ rest) ⋅ fj), cs⟩ := rfl
                  rw [hreb] at hvt
                  have htot := StepsTo.toValidTermination
                    (StepsTo.trans sSf (StepsTo.trans sDownL (StepsTo.trans sAlias1 (StepsTo.trans sFlagSf sOp)))) hvt
                  exact validTermination_mono (by simp; omega) htot
              | true =>
                  rw [hflag] at sFlagSf
                  have sUpL := up_from_left_steps (.appendFldFlagBack ⟨bs, hbs⟩) fs1 flag fs2 rest fj cs hobs
                    (.sf (.sfDone (.appendFldFlag ⟨bs, hbs⟩) true)) rfl
                  have sDownR := downR_steps (.toAppendFld ⟨bs, hbs⟩) fs1 flag fs2 rest fj cs
                    (.upDone (.appendFldFlagBack ⟨bs, hbs⟩) false) rfl
                  have sAlias2 : StepsTo 0 (.downRDone (.toAppendFld ⟨bs, hbs⟩))
                      ⟨rest, downRCrumbs fs1 flag fs2 fj cs⟩
                      (.sf (.sf0 (.appendFldNode ⟨bs, hbs⟩)))
                      ⟨rest, downRCrumbs fs1 flag fs2 fj cs⟩ :=
                    StepsTo.of_alias rfl
                  have hvt := ih hbs ⟨rest, downRCrumbs fs1 flag fs2 fj cs⟩
                  have hreb : rebuild ⟨rest, downRCrumbs fs1 flag fs2 fj cs⟩ =
                      rebuild ⟨(fs1 ⋅ flag) ⋅ ((fs2 ⋅ rest) ⋅ fj), cs⟩ := rfl
                  rw [hreb] at hvt
                  have htot := StepsTo.toValidTermination
                    (StepsTo.trans sSf
                      (StepsTo.trans sDownL
                        (StepsTo.trans sAlias1
                          (StepsTo.trans sFlagSf
                            (StepsTo.trans sUpL (StepsTo.trans sDownR sAlias2)))))) hvt
                  exact validTermination_mono (by simp; omega) htot

theorem appendVer_fuel_valid (desired : Bits11) :
    ∀ (fuel : Nat) (cur : Cursor),
      leaves cur.focus ≤ fuel →
      ValidTermination (480 * leaves cur.focus + 5 * leaves (rebuild cur) + 680)
        (.sf (.sf0 (.appendVer desired))) cur := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur hle
      have hp := leaves_pos cur.focus
      exact False.elim (by omega)
  | succ m ih =>
      intro cur hle
      rcases cur with ⟨v, cs⟩
      dsimp only [] at hle ⊢
      have sSf := checkStrictFrame_steps (.appendVer desired) ⟨v, cs⟩
      dsimp only [] at sSf
      cases hobs : strictFrameObs v with
      | false =>
          rw [hobs] at sSf
          have sOp : StepsTo 0 (.sf (.sfDone (.appendVer desired) false)) ⟨v, cs⟩ (.openSub .pf0) ⟨v, cs⟩ :=
            StepsTo.of_alias rfl
          have hvt := StepsTo.toValidTermination (StepsTo.trans sSf sOp) (openAndContract_valid ⟨v, cs⟩)
          exact validTermination_mono (by omega) hvt
      | true =>
          rw [hobs] at sSf
          obtain ⟨vs1, vnext, vs2, fields, vj, rfl, hvs1, hvs2, hvj⟩ := strictFrameObs_decomp hobs
          have hvLeaves : leaves vnext + 4 ≤ leaves ((vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj)) := by
            have := leaves_pos vs1
            have := leaves_pos vs2
            have := leaves_pos fields
            have := leaves_pos vj
            simp only [leaves]
            omega
          have sDownR1 := downR_steps (.toChkComm desired) vs1 vnext vs2 fields vj cs
            (.sf (.sfDone (.appendVer desired) true)) rfl
          have sChk := chkCommEntry_steps desired vs1 vnext vs2 fields vj cs ⟨hvs1, hvs2, hvj⟩
          cases hcomm : obsHasFrames 12 fields with
          | true =>
              rw [hcomm] at sChk
              have sDownL := downL_steps (.toAppendVerNext desired) vs1 vnext vs2 fields vj cs
                (.upDone (.chkCommClimb desired true ⟨0, by decide⟩) true) rfl
              have sAlias : StepsTo 0 (.downLDone (.toAppendVerNext desired))
                  ⟨vnext, downLCrumbs vs1 fields vs2 vj cs⟩
                  (.sf (.sf0 (.appendVer desired)))
                  ⟨vnext, downLCrumbs vs1 fields vs2 vj cs⟩ :=
                StepsTo.of_alias rfl
              have hvt := ih ⟨vnext, downLCrumbs vs1 fields vs2 vj cs⟩ (by dsimp only []; omega)
              dsimp only [] at hvt
              have hreb : rebuild ⟨vnext, downLCrumbs vs1 fields vs2 vj cs⟩ =
                  rebuild ⟨(vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj), cs⟩ := rfl
              rw [hreb] at hvt
              have htot := StepsTo.toValidTermination
                (StepsTo.trans sSf (StepsTo.trans sDownR1 (StepsTo.trans sChk (StepsTo.trans sDownL sAlias)))) hvt
              exact validTermination_mono (by omega) htot
          | false =>
              rw [hcomm] at sChk
              let remAll : BitsLe11 := ⟨desired.val, Nat.le_of_eq desired.property⟩
              have sDownR2 := downR_steps (.toAppendFld remAll) vs1 vnext vs2 fields vj cs
                (.upDone (.chkCommClimb desired false ⟨0, by decide⟩) true) rfl
              have sAlias : StepsTo 0 (.downRDone (.toAppendFld remAll))
                  ⟨fields, downRCrumbs vs1 vnext vs2 vj cs⟩
                  (.sf (.sf0 (.appendFldNode remAll)))
                  ⟨fields, downRCrumbs vs1 vnext vs2 vj cs⟩ :=
                StepsTo.of_alias rfl
              have hvt := appendFld_valid desired.val (Nat.le_of_eq desired.property)
                ⟨fields, downRCrumbs vs1 vnext vs2 vj cs⟩
              have hreb : rebuild ⟨fields, downRCrumbs vs1 vnext vs2 vj cs⟩ =
                  rebuild ⟨(vs1 ⋅ vnext) ⋅ ((vs2 ⋅ fields) ⋅ vj), cs⟩ := rfl
              rw [hreb] at hvt
              have hdlen : desired.val.length = 11 := desired.property
              have htot := StepsTo.toValidTermination
                (StepsTo.trans sSf (StepsTo.trans sDownR1 (StepsTo.trans sChk (StepsTo.trans sDownR2 sAlias)))) hvt
              exact validTermination_mono (by omega) htot

theorem appendEntry_valid (desired : Bits11) (cur : Cursor) :
    ValidTermination (485 * leaves (rebuild cur) + 680)
      (.downLDone (.toAppendVerEntry desired)) cur := by
  have sAlias : StepsTo 0 (.downLDone (.toAppendVerEntry desired)) cur
      (.sf (.sf0 (.appendVer desired))) cur :=
    StepsTo.of_alias rfl
  have hvt := appendVer_fuel_valid desired (leaves cur.focus) cur (Nat.le_refl _)
  have hfocusLe : leaves cur.focus ≤ leaves (rebuild cur) := by
    rw [leaves_rebuild]
    omega
  exact validTermination_mono (by omega) (StepsTo.toValidTermination sAlias hvt)

theorem frontierWalk_fuel_valid :
    ∀ (fuel : Nat) (cur : Cursor),
      leaves cur.focus ≤ fuel →
      ValidTermination (18 * leaves cur.focus + 5 * leaves (rebuild cur) + 43)
        (.sf (.sf0 .frontierWalk)) cur := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur hle
      have hp := leaves_pos cur.focus
      exact False.elim (by omega)
  | succ m ih =>
      intro cur hle
      rcases cur with ⟨u, cs⟩
      dsimp only [] at hle ⊢
      have sSf := checkStrictFrame_steps .frontierWalk ⟨u, cs⟩
      dsimp only [] at sSf
      cases hobs : strictFrameObs u with
      | false =>
          rw [hobs] at sSf
          have sOp : StepsTo 0 (.sf (.sfDone .frontierWalk false)) ⟨u, cs⟩ (.openSub .pf0) ⟨u, cs⟩ :=
            StepsTo.of_alias rfl
          have hvt := StepsTo.toValidTermination (StepsTo.trans sSf sOp) (openAndContract_valid ⟨u, cs⟩)
          exact validTermination_mono (by omega) hvt
      | true =>
          rw [hobs] at sSf
          obtain ⟨s1, l, s2, r, j, rfl, _, _, _⟩ := strictFrameObs_decomp hobs
          have huLeaves : leaves l + 4 ≤ leaves ((s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j)) := by
            have := leaves_pos s1
            have := leaves_pos s2
            have := leaves_pos r
            have := leaves_pos j
            simp only [leaves]
            omega
          have sDownL := downL_steps .toFrontier s1 l s2 r j cs (.sf (.sfDone .frontierWalk true)) rfl
          have sAlias : StepsTo 0 (.downLDone .toFrontier) ⟨l, downLCrumbs s1 r s2 j cs⟩
              (.sf (.sf0 .frontierWalk)) ⟨l, downLCrumbs s1 r s2 j cs⟩ :=
            StepsTo.of_alias rfl
          have hvt := ih ⟨l, downLCrumbs s1 r s2 j cs⟩ (by dsimp only []; omega)
          dsimp only [] at hvt
          have hreb : rebuild ⟨l, downLCrumbs s1 r s2 j cs⟩ =
              rebuild ⟨(s1 ⋅ l) ⋅ ((s2 ⋅ r) ⋅ j), cs⟩ := rfl
          rw [hreb] at hvt
          have htot := StepsTo.toValidTermination (StepsTo.trans sSf (StepsTo.trans sDownL sAlias)) hvt
          exact validTermination_mono (by omega) htot

theorem rewindToTape_steps (rootLeft : Term) (hubCtx : FrameCtx) (hhub : ValidFrameCtx hubCtx) :
    ∀ (rframes : List FrameCtx) (u : Term) (cStart : Control),
      (∀ f ∈ rframes, ValidFrameCtx f) →
      startRClimbProp .rewindToTape (rframes ++ [hubCtx]) u [.right rootLeft] cStart →
      StepsTo (21 * (rframes.length + 1)) cStart
        ⟨u, pushRChain (rframes ++ [hubCtx]) [.right rootLeft]⟩
        (.hubChkDone .rewindTapeChk true)
        ⟨wrapRChain (rframes ++ [hubCtx]) u, [.right rootLeft]⟩ := by
  intro rframes
  induction rframes with
  | nil =>
      intro u cStart _ hstart
      dsimp only [startRClimbProp] at hstart
      simp only [List.nil_append] at hstart ⊢
      have sUp := up_from_right_steps .rewindToTape hubCtx.s1 hubCtx.other hubCtx.s2 u hubCtx.j
        [.right rootLeft] hhub.2.2 cStart hstart
      have sChk := hubChk_at_hub_steps .rewindTapeChk rootLeft
        ((hubCtx.s1 ⋅ hubCtx.other) ⋅ ((hubCtx.s2 ⋅ u) ⋅ hubCtx.j))
        (.upDone .rewindToTape true) rfl
      simpa [pushRChain, wrapRChain] using StepsTo.mono (by omega) (StepsTo.trans sUp sChk)
  | cons f fs ih =>
      intro u cStart hall hstart
      dsimp only [startRClimbProp] at hstart
      simp only [List.cons_append] at hstart ⊢
      have hf := hall f (by simp)
      have hfs : ∀ x ∈ fs, ValidFrameCtx x := fun x hx => hall x (by simp [hx])
      have sUp := up_from_right_steps .rewindToTape f.s1 f.other f.s2 u f.j
        (pushRChain (fs ++ [hubCtx]) [.right rootLeft]) hf.2.2 cStart hstart
      let uPrev := (f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j)
      have sChk : StepsTo 2 (.upDone .rewindToTape true)
          ⟨uPrev, pushRChain (fs ++ [hubCtx]) [.right rootLeft]⟩
          (.hubChkDone .rewindTapeChk false)
          ⟨uPrev, pushRChain (fs ++ [hubCtx]) [.right rootLeft]⟩ := by
        cases fs with
        | nil =>
            exact hubChk_below_hub_steps .rewindTapeChk hubCtx.s2 uPrev hubCtx.j
              [.right (hubCtx.s1 ⋅ hubCtx.other), .right rootLeft] (.upDone .rewindToTape true) rfl
        | cons f2 fs2 =>
            exact hubChk_below_hub_steps .rewindTapeChk f2.s2 uPrev f2.j
              (.right (f2.s1 ⋅ f2.other) :: pushRChain (fs2 ++ [hubCtx]) [.right rootLeft])
              (.upDone .rewindToTape true) rfl
      have hmNext : startRClimbProp .rewindToTape (fs ++ [hubCtx]) uPrev [.right rootLeft]
          (.hubChkDone .rewindTapeChk false) := by
        dsimp only [startRClimbProp]
        cases fs <;> rfl
      have sRest := ih uPrev (.hubChkDone .rewindTapeChk false) hfs hmNext
      simp only [List.length_cons, wrapRChain]
      exact StepsTo.mono (by omega) (StepsTo.trans sUp (StepsTo.trans sChk sRest))

theorem rewindToHubHalt_steps (rootLeft : Term) (hubCtx : FrameCtx) (hhub : ValidFrameCtx hubCtx) :
    ∀ (rframes : List FrameCtx) (u : Term) (cStart : Control),
      (∀ f ∈ rframes, ValidFrameCtx f) →
      startRClimbProp .rewindToHubHalt (rframes ++ [hubCtx]) u [.right rootLeft] cStart →
      StepsTo (21 * (rframes.length + 1)) cStart
        ⟨u, pushRChain (rframes ++ [hubCtx]) [.right rootLeft]⟩
        (.hubChkDone .rewindHaltChk true)
        ⟨wrapRChain (rframes ++ [hubCtx]) u, [.right rootLeft]⟩ := by
  intro rframes
  induction rframes with
  | nil =>
      intro u cStart _ hstart
      dsimp only [startRClimbProp] at hstart
      simp only [List.nil_append] at hstart ⊢
      have sUp := up_from_right_steps .rewindToHubHalt hubCtx.s1 hubCtx.other hubCtx.s2 u hubCtx.j
        [.right rootLeft] hhub.2.2 cStart hstart
      have sChk := hubChk_at_hub_steps .rewindHaltChk rootLeft
        ((hubCtx.s1 ⋅ hubCtx.other) ⋅ ((hubCtx.s2 ⋅ u) ⋅ hubCtx.j))
        (.upDone .rewindToHubHalt true) rfl
      simpa [pushRChain, wrapRChain] using StepsTo.mono (by omega) (StepsTo.trans sUp sChk)
  | cons f fs ih =>
      intro u cStart hall hstart
      dsimp only [startRClimbProp] at hstart
      simp only [List.cons_append] at hstart ⊢
      have hf := hall f (by simp)
      have hfs : ∀ x ∈ fs, ValidFrameCtx x := fun x hx => hall x (by simp [hx])
      have sUp := up_from_right_steps .rewindToHubHalt f.s1 f.other f.s2 u f.j
        (pushRChain (fs ++ [hubCtx]) [.right rootLeft]) hf.2.2 cStart hstart
      let uPrev := (f.s1 ⋅ f.other) ⋅ ((f.s2 ⋅ u) ⋅ f.j)
      have sChk : StepsTo 2 (.upDone .rewindToHubHalt true)
          ⟨uPrev, pushRChain (fs ++ [hubCtx]) [.right rootLeft]⟩
          (.hubChkDone .rewindHaltChk false)
          ⟨uPrev, pushRChain (fs ++ [hubCtx]) [.right rootLeft]⟩ := by
        cases fs with
        | nil =>
            exact hubChk_below_hub_steps .rewindHaltChk hubCtx.s2 uPrev hubCtx.j
              [.right (hubCtx.s1 ⋅ hubCtx.other), .right rootLeft] (.upDone .rewindToHubHalt true) rfl
        | cons f2 fs2 =>
            exact hubChk_below_hub_steps .rewindHaltChk f2.s2 uPrev f2.j
              (.right (f2.s1 ⋅ f2.other) :: pushRChain (fs2 ++ [hubCtx]) [.right rootLeft])
              (.upDone .rewindToHubHalt true) rfl
      have hmNext : startRClimbProp .rewindToHubHalt (fs ++ [hubCtx]) uPrev [.right rootLeft]
          (.hubChkDone .rewindHaltChk false) := by
        dsimp only [startRClimbProp]
        cases fs <;> rfl
      have sRest := ih uPrev (.hubChkDone .rewindHaltChk false) hfs hmNext
      simp only [List.length_cons, wrapRChain]
      exact StepsTo.mono (by omega) (StepsTo.trans sUp (StepsTo.trans sChk sRest))


/-! ### Two-Pass Tape Scan (`SeekActive` & `SeekPending`) and All-Input Linear Theorem -/

abbrev hubTapeCursor (rootLeft : Term) (hubCtx : FrameCtx) (rframes : List FrameCtx) (curTape : Term) : Cursor :=
  ⟨curTape, pushRChain (rframes ++ [hubCtx]) [.right rootLeft]⟩

theorem wrapRChain_hub_split (hubCtx : FrameCtx) :
    ∀ (xs : List FrameCtx) (t : Term),
      wrapRChain (xs ++ [hubCtx]) t =
        (hubCtx.s1 ⋅ hubCtx.other) ⋅ ((hubCtx.s2 ⋅ wrapRChain xs t) ⋅ hubCtx.j) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons _ rest ih => intro t; exact ih _

theorem rframes_bound_of_hub (rootLeft : Term) (hubCtx : FrameCtx) (rframes : List FrameCtx) (curTape : Term) :
    rframes.length + 1 ≤ leaves (rebuild (hubTapeCursor rootLeft hubCtx rframes curTape)) ∧
    leaves (wrapRChain rframes curTape) ≤ leaves (rebuild (hubTapeCursor rootLeft hubCtx rframes curTape)) := by
  have h1 : rebuild (hubTapeCursor rootLeft hubCtx rframes curTape) =
      rebuild ⟨wrapRChain (rframes ++ [hubCtx]) curTape, [.right rootLeft]⟩ :=
    rebuild_pushRChain (rframes ++ [hubCtx]) [.right rootLeft] curTape
  have h2 := leaves_wrapRChain_ge (rframes ++ [hubCtx]) curTape
  have h3 : leaves (rebuild ⟨wrapRChain (rframes ++ [hubCtx]) curTape, [.right rootLeft]⟩) =
      leaves (wrapRChain (rframes ++ [hubCtx]) curTape) + leaves rootLeft := by
    simp [rebuild, rebuildWith, leaves]
    omega
  have h4 := leaves_pos curTape
  have h5 : leaves (wrapRChain rframes curTape) ≤ leaves (wrapRChain (rframes ++ [hubCtx]) curTape) := by
    rw [wrapRChain_hub_split hubCtx rframes curTape]
    simp only [leaves]
    omega
  simp only [List.length_append, List.length_cons, List.length_nil] at h2
  rw [h1, h3]
  constructor <;> omega

theorem seekActive_fuel_valid (rootLeft : Term) (hubCtx : FrameCtx) (hhub : ValidFrameCtx hubCtx) :
    ∀ (fuel : Nat) (curTape : Term) (rframes : List FrameCtx),
      leaves curTape ≤ fuel →
      (∀ f ∈ rframes, ValidFrameCtx f) →
      ValidTermination
        (1000 * leaves curTape + 510 * leaves (rebuild (hubTapeCursor rootLeft hubCtx rframes curTape)) + 750)
        (.sf (.sf0 (.seekCell true)))
        (hubTapeCursor rootLeft hubCtx rframes curTape) := by
  intro fuel
  induction fuel with
  | zero =>
      intro curTape _ hle _
      have hp := leaves_pos curTape
      exact False.elim (by omega)
  | succ m ih =>
      intro curTape rframes hle hall
      have hrfBound := (rframes_bound_of_hub rootLeft hubCtx rframes curTape).1
      have sSf := checkStrictFrame_steps (.seekCell true) (hubTapeCursor rootLeft hubCtx rframes curTape)
      cases hobs : strictFrameObs curTape with
      | false =>
          rw [hobs] at sSf
          have sAb : StepsTo 0 (.sf (.sfDone (.seekCell true) false))
              (hubTapeCursor rootLeft hubCtx rframes curTape)
              (.euler .abortToRoot)
              (hubTapeCursor rootLeft hubCtx rframes curTape) :=
            StepsTo.of_alias rfl
          have hvt := StepsTo.toValidTermination (StepsTo.trans sSf sAb)
            (abortToRoot_valid (hubTapeCursor rootLeft hubCtx rframes curTape))
          exact validTermination_mono (by omega) hvt
      | true =>
          rw [hobs] at sSf
          obtain ⟨cs1, v0, cs2, nextTape, cj, rfl, hcs1, hcs2, hcj⟩ := strictFrameObs_decomp hobs
          let cellTerm := (cs1 ⋅ v0) ⋅ ((cs2 ⋅ nextTape) ⋅ cj)
          let csCur := pushRChain (rframes ++ [hubCtx]) [.right rootLeft]
          have hcLeaves : leaves v0 + leaves nextTape + 3 ≤ leaves ((cs1 ⋅ v0) ⋅ ((cs2 ⋅ nextTape) ⋅ cj)) := by
            have := leaves_pos cs1
            have := leaves_pos cs2
            have := leaves_pos cj
            simp only [leaves]
            omega
          have hParent : ∃ pf pfs, rframes ++ [hubCtx] = pf :: pfs ∧ ValidFrameCtx pf := by
            cases rframes with
            | nil => exact ⟨hubCtx, [], rfl, hhub⟩
            | cons f0 fs0 => exact ⟨f0, fs0 ++ [hubCtx], rfl, hall f0 (by simp)⟩
          obtain ⟨pf, pfs, hpfEq, hpfValid⟩ := hParent
          have hcsCurEq : csCur = downRCrumbs pf.s1 pf.other pf.s2 pf.j (pushRChain pfs [.right rootLeft]) := by
            dsimp only [csCur]
            rw [hpfEq]
            rfl
          have sDownL := downL_steps (.toRcStart .seekActive) cs1 v0 cs2 nextTape cj csCur
            (.sf (.sfDone (.seekCell true) true)) rfl
          have sRead := readCell_steps .seekActive pf.s1 pf.other pf.s2 pf.j
            (pushRChain pfs [.right rootLeft]) hpfValid.2.2
            cs1 v0 cs2 nextTape cj ⟨hcs1, hcs2, hcj⟩
          rw [← hcsCurEq] at sRead
          let cell := (obsScanBottomUp v0).getD defaultCell8
          have sPre := StepsTo.trans sSf (StepsTo.trans sDownL sRead)
          if hact : cell.status == .active then
            if hst : cell.state.val < 132 then
              cases hprog : fixedBinaryProgram ⟨cell.state.val, hst⟩ cell.bit with
              | none =>
                  have hmRew : startRClimbProp .rewindToHubHalt (rframes ++ [hubCtx]) cellTerm [.right rootLeft]
                      (.downRDone (.toRcDone .seekActive cell)) := by
                    cases rframes <;> (
                      dsimp only [startRClimbProp, List.nil_append, List.cons_append, microstep, step, onDownRDone, onCellRead]
                      rw [if_pos hact, dif_pos hst, hprog]
                      rfl)
                  have sRew := rewindToHubHalt_steps rootLeft hubCtx hhub rframes cellTerm
                    (.downRDone (.toRcDone .seekActive cell)) hall hmRew
                  let tapeRebuilt := wrapRChain rframes cellTerm
                  rw [wrapRChain_hub_split hubCtx rframes cellTerm] at sRew
                  have sDownFlag := downL_steps .toHaltFlagOpen hubCtx.s1 hubCtx.other hubCtx.s2 tapeRebuilt hubCtx.j
                    [.right rootLeft] (.hubChkDone .rewindHaltChk true) rfl
                  have sOpAlias : StepsTo 0 (.downLDone .toHaltFlagOpen)
                      ⟨hubCtx.other, downLCrumbs hubCtx.s1 tapeRebuilt hubCtx.s2 hubCtx.j [.right rootLeft]⟩
                      (.openSub .pf0)
                      ⟨hubCtx.other, downLCrumbs hubCtx.s1 tapeRebuilt hubCtx.s2 hubCtx.j [.right rootLeft]⟩ :=
                    StepsTo.of_alias rfl
                  have sTot := StepsTo.trans sPre (StepsTo.trans sRew (StepsTo.trans sDownFlag sOpAlias))
                  have hvt := openAndContract_valid
                    ⟨hubCtx.other, downLCrumbs hubCtx.s1 tapeRebuilt hubCtx.s2 hubCtx.j [.right rootLeft]⟩
                  rw [← sTot.1] at hvt
                  exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
              | some inst =>
                  cases hdir : inst.direction with
                  | stay =>
                      let des := encodeRecord11 ⟨inst.write, .active, inst.next.val⟩
                      have hmApp : microstep (.downRDone (.toRcDone .seekActive cell)) ⟨cellTerm, csCur⟩ =
                          .running (.downL1 (.toAppendVerEntry des)) ⟨cs1 ⋅ v0, .left ((cs2 ⋅ nextTape) ⋅ cj) :: csCur⟩ := by
                        dsimp only [microstep, step, onDownRDone, onCellRead]
                        rw [if_pos hact, dif_pos hst, hprog]
                        dsimp only []
                        rw [hdir]
                        rfl
                      have sDownApp := downL_steps (.toAppendVerEntry des) cs1 v0 cs2 nextTape cj csCur _ hmApp
                      have sTot := StepsTo.trans sPre sDownApp
                      have hvt := appendEntry_valid des ⟨v0, downLCrumbs cs1 nextTape cs2 cj csCur⟩
                      rw [← sTot.1] at hvt
                      exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
                  | right =>
                      let des := encodeRecord11 ⟨inst.write, .movingRight, inst.next.val⟩
                      have hmApp : microstep (.downRDone (.toRcDone .seekActive cell)) ⟨cellTerm, csCur⟩ =
                          .running (.downL1 (.toAppendVerEntry des)) ⟨cs1 ⋅ v0, .left ((cs2 ⋅ nextTape) ⋅ cj) :: csCur⟩ := by
                        dsimp only [microstep, step, onDownRDone, onCellRead]
                        rw [if_pos hact, dif_pos hst, hprog]
                        dsimp only []
                        rw [hdir]
                        rfl
                      have sDownApp := downL_steps (.toAppendVerEntry des) cs1 v0 cs2 nextTape cj csCur _ hmApp
                      have sTot := StepsTo.trans sPre sDownApp
                      have hvt := appendEntry_valid des ⟨v0, downLCrumbs cs1 nextTape cs2 cj csCur⟩
                      rw [← sTot.1] at hvt
                      exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
                  | left =>
                      have hmUp : microstep (.downRDone (.toRcDone .seekActive cell))
                          ⟨cellTerm, downRCrumbs pf.s1 pf.other pf.s2 pf.j (pushRChain pfs [.right rootLeft])⟩ =
                          .running (.up1 (.activeBoundaryTest cell))
                            ⟨pf.s2 ⋅ cellTerm, .left pf.j :: .right (pf.s1 ⋅ pf.other) :: pushRChain pfs [.right rootLeft]⟩ := by
                        dsimp only [microstep, step, onDownRDone, onCellRead]
                        rw [if_pos hact, dif_pos hst, hprog]
                        dsimp only []
                        rw [hdir]
                        rfl
                      have sUpP := up_from_right_steps (.activeBoundaryTest cell) pf.s1 pf.other pf.s2 cellTerm pf.j
                        (pushRChain pfs [.right rootLeft]) hpfValid.2.2 _ hmUp
                      rw [← hcsCurEq] at sUpP
                      let pTerm := (pf.s1 ⋅ pf.other) ⋅ ((pf.s2 ⋅ cellTerm) ⋅ pf.j)
                      have sBoundary : ∃ isH : Bool,
                          StepsTo 2 (.upDone (.activeBoundaryTest cell) true)
                            ⟨pTerm, pushRChain pfs [.right rootLeft]⟩
                            (.hubChkDone (.activeBoundaryChk cell) isH)
                            ⟨pTerm, pushRChain pfs [.right rootLeft]⟩ := by
                        cases pfs with
                        | nil =>
                            exact ⟨true, hubChk_at_hub_steps (.activeBoundaryChk cell) rootLeft pTerm _ rfl⟩
                        | cons pf2 pfs2 =>
                            exact ⟨false, hubChk_below_hub_steps (.activeBoundaryChk cell) pf2.s2 pTerm pf2.j
                              (.right (pf2.s1 ⋅ pf2.other) :: pushRChain pfs2 [.right rootLeft]) _ rfl⟩
                      obtain ⟨isH, sChkH⟩ := sBoundary
                      let st : Status := if isH then .active else .movingLeft
                      let des := encodeRecord11 ⟨inst.write, st, inst.next.val⟩
                      have hmBack : microstep (.hubChkDone (.activeBoundaryChk cell) isH)
                          ⟨pTerm, pushRChain pfs [.right rootLeft]⟩ =
                          .running (.downR1 (.toActiveBoundaryBack des))
                            ⟨(pf.s2 ⋅ cellTerm) ⋅ pf.j, .right (pf.s1 ⋅ pf.other) :: pushRChain pfs [.right rootLeft]⟩ := by
                        dsimp only [microstep, step, onHubChkDone]
                        rw [dif_pos hst, hprog]
                        rfl
                      have sBack := downR_steps (.toActiveBoundaryBack des) pf.s1 pf.other pf.s2 cellTerm pf.j
                        (pushRChain pfs [.right rootLeft]) _ hmBack
                      rw [← hcsCurEq] at sBack
                      have sDownApp := downL_steps (.toAppendVerEntry des) cs1 v0 cs2 nextTape cj csCur
                        (.downRDone (.toActiveBoundaryBack des)) rfl
                      have sTot := StepsTo.trans sPre (StepsTo.trans sUpP (StepsTo.trans sChkH (StepsTo.trans sBack sDownApp)))
                      have hvt := appendEntry_valid des ⟨v0, downLCrumbs cs1 nextTape cs2 cj csCur⟩
                      rw [← sTot.1] at hvt
                      exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
            else
              have sAb : StepsTo 0 (.downRDone (.toRcDone .seekActive cell)) ⟨cellTerm, csCur⟩
                  (.euler .abortToRoot) ⟨cellTerm, csCur⟩ := by
                apply StepsTo.of_alias
                dsimp only [microstep, step, onDownRDone, onCellRead]
                rw [if_pos hact, dif_neg hst]
                rfl
              have sTot := StepsTo.trans sPre sAb
              have hvt := abortToRoot_valid ⟨cellTerm, csCur⟩
              rw [← sTot.1] at hvt
              exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
          else
            let fCur : FrameCtx := ⟨cs1, v0, cs2, cj⟩
            have hfCur : ValidFrameCtx fCur := ⟨hcs1, hcs2, hcj⟩
            have hmNext : microstep (.downRDone (.toRcDone .seekActive cell)) ⟨cellTerm, csCur⟩ =
                .running (.downR1 (.toNextCell true)) ⟨(cs2 ⋅ nextTape) ⋅ cj, .right (cs1 ⋅ v0) :: csCur⟩ := by
              simp [microstep, step, onDownRDone, onCellRead, hact, startDownR, applyAction, cellTerm]
            have sDownNext := downR_steps (.toNextCell true) cs1 v0 cs2 nextTape cj csCur _ hmNext
            have sAlias : StepsTo 0 (.downRDone (.toNextCell true))
                (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape)
                (.sf (.sf0 (.seekCell true)))
                (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape) :=
              StepsTo.of_alias rfl
            have hall' : ∀ x ∈ fCur :: rframes, ValidFrameCtx x := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact hfCur
              · exact hall x hx'
            have hvt := ih nextTape (fCur :: rframes) (by omega) hall'
            have sTot := StepsTo.trans sPre (StepsTo.trans sDownNext sAlias)
            rw [← sTot.1] at hvt
            exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)

theorem seekPending_fuel_valid (rootLeft : Term) (hubCtx : FrameCtx) (hhub : ValidFrameCtx hubCtx) :
    ∀ (fuel : Nat) (curTape : Term) (rframes : List FrameCtx),
      leaves curTape ≤ fuel →
      (∀ f ∈ rframes, ValidFrameCtx f) →
      ValidTermination
        (1000 * leaves curTape + 1535 * leaves (rebuild (hubTapeCursor rootLeft hubCtx rframes curTape)) + 800)
        (.sf (.sf0 (.seekCell false)))
        (hubTapeCursor rootLeft hubCtx rframes curTape) := by
  intro fuel
  induction fuel with
  | zero =>
      intro curTape _ hle _
      have hp := leaves_pos curTape
      exact False.elim (by omega)
  | succ m ih =>
      intro curTape rframes hle hall
      obtain ⟨hrfLen, hrfWrap⟩ := rframes_bound_of_hub rootLeft hubCtx rframes curTape
      have sSf := checkStrictFrame_steps (.seekCell false) (hubTapeCursor rootLeft hubCtx rframes curTape)
      cases hobs : strictFrameObs curTape with
      | false =>
          rw [hobs] at sSf
          have hmRew : startRClimbProp .rewindToTape (rframes ++ [hubCtx]) curTape [.right rootLeft]
              (.sf (.sfDone (.seekCell false) false)) := by
            dsimp only [startRClimbProp]
            cases rframes <;> rfl
          have sRew := rewindToTape_steps rootLeft hubCtx hhub rframes curTape
            (.sf (.sfDone (.seekCell false) false)) hall hmRew
          let tapeFull := wrapRChain rframes curTape
          rw [wrapRChain_hub_split hubCtx rframes curTape] at sRew
          have sDownTape := downR_steps .toTapePass2 hubCtx.s1 hubCtx.other hubCtx.s2 tapeFull hubCtx.j
            [.right rootLeft] (.hubChkDone .rewindTapeChk true) rfl
          have sAlias : StepsTo 0 (.downRDone .toTapePass2)
              (hubTapeCursor rootLeft hubCtx [] tapeFull)
              (.sf (.sf0 (.seekCell true)))
              (hubTapeCursor rootLeft hubCtx [] tapeFull) :=
            StepsTo.of_alias rfl
          have sTot := StepsTo.trans sSf (StepsTo.trans sRew (StepsTo.trans sDownTape sAlias))
          have hvt := seekActive_fuel_valid rootLeft hubCtx hhub (leaves tapeFull) tapeFull []
            (Nat.le_refl _) (by intro _ h; simp at h)
          rw [← sTot.1] at hvt
          dsimp only [tapeFull] at hvt
          exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
      | true =>
          rw [hobs] at sSf
          obtain ⟨cs1, v0, cs2, nextTape, cj, rfl, hcs1, hcs2, hcj⟩ := strictFrameObs_decomp hobs
          let cellTerm := (cs1 ⋅ v0) ⋅ ((cs2 ⋅ nextTape) ⋅ cj)
          let csCur := pushRChain (rframes ++ [hubCtx]) [.right rootLeft]
          have hcLeaves : leaves v0 + leaves nextTape + 3 ≤ leaves ((cs1 ⋅ v0) ⋅ ((cs2 ⋅ nextTape) ⋅ cj)) := by
            have := leaves_pos cs1
            have := leaves_pos cs2
            have := leaves_pos cj
            simp only [leaves]
            omega
          have hParent : ∃ pf pfs, rframes ++ [hubCtx] = pf :: pfs ∧ ValidFrameCtx pf := by
            cases rframes with
            | nil => exact ⟨hubCtx, [], rfl, hhub⟩
            | cons f0 fs0 => exact ⟨f0, fs0 ++ [hubCtx], rfl, hall f0 (by simp)⟩
          obtain ⟨pf, pfs, hpfEq, hpfValid⟩ := hParent
          have hcsCurEq : csCur = downRCrumbs pf.s1 pf.other pf.s2 pf.j (pushRChain pfs [.right rootLeft]) := by
            dsimp only [csCur]
            rw [hpfEq]
            rfl
          have sDownL := downL_steps (.toRcStart .seekPending) cs1 v0 cs2 nextTape cj csCur
            (.sf (.sfDone (.seekCell false) true)) rfl
          have sRead := readCell_steps .seekPending pf.s1 pf.other pf.s2 pf.j
            (pushRChain pfs [.right rootLeft]) hpfValid.2.2
            cs1 v0 cs2 nextTape cj ⟨hcs1, hcs2, hcj⟩
          rw [← hcsCurEq] at sRead
          let cell := (obsScanBottomUp v0).getD defaultCell8
          have sPre := StepsTo.trans sSf (StepsTo.trans sDownL sRead)
          cases hstatus : cell.status with
          | off =>
              let fCur : FrameCtx := ⟨cs1, v0, cs2, cj⟩
              have hfCur : ValidFrameCtx fCur := ⟨hcs1, hcs2, hcj⟩
              have hmNext : microstep (.downRDone (.toRcDone .seekPending cell)) ⟨cellTerm, csCur⟩ =
                  .running (.downR1 (.toNextCell false)) ⟨(cs2 ⋅ nextTape) ⋅ cj, .right (cs1 ⋅ v0) :: csCur⟩ := by
                simp [microstep, step, onDownRDone, onCellRead, hstatus, startDownR, applyAction, cellTerm]
              have sDownNext := downR_steps (.toNextCell false) cs1 v0 cs2 nextTape cj csCur _ hmNext
              have sAlias : StepsTo 0 (.downRDone (.toNextCell false))
                  (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape)
                  (.sf (.sf0 (.seekCell false)))
                  (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape) :=
                StepsTo.of_alias rfl
              have hall' : ∀ x ∈ fCur :: rframes, ValidFrameCtx x := by
                intro x hx
                rcases List.mem_cons.mp hx with rfl | hx'
                · exact hfCur
                · exact hall x hx'
              have hvt := ih nextTape (fCur :: rframes) (by omega) hall'
              have sTot := StepsTo.trans sPre (StepsTo.trans sDownNext sAlias)
              rw [← sTot.1] at hvt
              exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
          | active =>
              let fCur : FrameCtx := ⟨cs1, v0, cs2, cj⟩
              have hfCur : ValidFrameCtx fCur := ⟨hcs1, hcs2, hcj⟩
              have hmNext : microstep (.downRDone (.toRcDone .seekPending cell)) ⟨cellTerm, csCur⟩ =
                  .running (.downR1 (.toNextCell false)) ⟨(cs2 ⋅ nextTape) ⋅ cj, .right (cs1 ⋅ v0) :: csCur⟩ := by
                simp [microstep, step, onDownRDone, onCellRead, hstatus, startDownR, applyAction, cellTerm]
              have sDownNext := downR_steps (.toNextCell false) cs1 v0 cs2 nextTape cj csCur _ hmNext
              have sAlias : StepsTo 0 (.downRDone (.toNextCell false))
                  (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape)
                  (.sf (.sf0 (.seekCell false)))
                  (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape) :=
                StepsTo.of_alias rfl
              have hall' : ∀ x ∈ fCur :: rframes, ValidFrameCtx x := by
                intro x hx
                rcases List.mem_cons.mp hx with rfl | hx'
                · exact hfCur
                · exact hall x hx'
              have hvt := ih nextTape (fCur :: rframes) (by omega) hall'
              have sTot := StepsTo.trans sPre (StepsTo.trans sDownNext sAlias)
              rw [← sTot.1] at hvt
              exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
          | movingRight =>
              have hmDest : microstep (.downRDone (.toRcDone .seekPending cell)) ⟨cellTerm, csCur⟩ =
                  .running (.downR1 (.toPendingRightDest cell)) ⟨(cs2 ⋅ nextTape) ⋅ cj, .right (cs1 ⋅ v0) :: csCur⟩ := by
                simp [microstep, step, onDownRDone, onCellRead, hstatus, startDownR, applyAction, cellTerm]
              have sDownDest := downR_steps (.toPendingRightDest cell) cs1 v0 cs2 nextTape cj csCur _ hmDest
              let csDest := downRCrumbs cs1 v0 cs2 cj csCur
              have sAliasD : StepsTo 0 (.downRDone (.toPendingRightDest cell)) ⟨nextTape, csDest⟩
                  (.sf (.sf0 (.pendingRightDest cell))) ⟨nextTape, csDest⟩ :=
                StepsTo.of_alias rfl
              have sSfD := checkStrictFrame_steps (.pendingRightDest cell) ⟨nextTape, csDest⟩
              cases hobsD : strictFrameObs nextTape with
              | false =>
                  rw [hobsD] at sSfD
                  have sOp : StepsTo 0 (.sf (.sfDone (.pendingRightDest cell) false)) ⟨nextTape, csDest⟩
                      (.openSub .pf0) ⟨nextTape, csDest⟩ :=
                    StepsTo.of_alias rfl
                  have sTot := StepsTo.trans sPre (StepsTo.trans sDownDest (StepsTo.trans sAliasD (StepsTo.trans sSfD sOp)))
                  have hvt := openAndContract_valid ⟨nextTape, csDest⟩
                  rw [← sTot.1] at hvt
                  exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
              | true =>
                  rw [hobsD] at sSfD
                  obtain ⟨ds1, dv0, ds2, drest, dj, rfl, hds1, hds2, hdj⟩ := strictFrameObs_decomp hobsD
                  let dTerm := (ds1 ⋅ dv0) ⋅ ((ds2 ⋅ drest) ⋅ dj)
                  have hdLeaves : leaves dv0 + 3 ≤ leaves ((ds1 ⋅ dv0) ⋅ ((ds2 ⋅ drest) ⋅ dj)) := by
                    have := leaves_pos ds1
                    have := leaves_pos ds2
                    have := leaves_pos drest
                    have := leaves_pos dj
                    simp only [leaves]
                    omega
                  have sDownD := downL_steps (.toRcStart (.readDestRight cell)) ds1 dv0 ds2 drest dj csDest
                    (.sf (.sfDone (.pendingRightDest cell) true)) rfl
                  have sReadD := readCell_steps (.readDestRight cell) cs1 v0 cs2 cj csCur hcj
                    ds1 dv0 ds2 drest dj ⟨hds1, hds2, hdj⟩
                  let dCell := (obsScanBottomUp dv0).getD defaultCell8
                  have sPreD := StepsTo.trans sPre
                    (StepsTo.trans sDownDest (StepsTo.trans sAliasD (StepsTo.trans sSfD (StepsTo.trans sDownD sReadD))))
                  if hoff : dCell.status == .off then
                    let des := encodeRecord11 ⟨dCell.bit, .active, cell.state.val⟩
                    have hmApp : microstep (.downRDone (.toRcDone (.readDestRight cell) dCell)) ⟨dTerm, csDest⟩ =
                        .running (.downL1 (.toAppendVerEntry des)) ⟨ds1 ⋅ dv0, .left ((ds2 ⋅ drest) ⋅ dj) :: csDest⟩ := by
                      simp [microstep, step, onDownRDone, onCellRead, hoff, startDownL, applyAction, des, dTerm]
                    have sApp := downL_steps (.toAppendVerEntry des) ds1 dv0 ds2 drest dj csDest _ hmApp
                    have sTot := StepsTo.trans sPreD sApp
                    have hvt := appendEntry_valid des ⟨dv0, downLCrumbs ds1 drest ds2 dj csDest⟩
                    rw [← sTot.1] at hvt
                    exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
                  else if hdone : dCell.status == .active && dCell.state == cell.state then
                    have hmBack : microstep (.downRDone (.toRcDone (.readDestRight cell) dCell)) ⟨dTerm, csDest⟩ =
                        .running (.up1 (.pendingRightBackToSrc cell.bit))
                          ⟨cs2 ⋅ dTerm, .left cj :: .right (cs1 ⋅ v0) :: csCur⟩ := by
                      simp [microstep, step, onDownRDone, onCellRead, hoff, hdone, startUp, applyAction, csDest, downRCrumbs, dTerm]
                    have sBack := up_from_right_steps (.pendingRightBackToSrc cell.bit) cs1 v0 cs2 dTerm cj csCur hcj _ hmBack
                    let des := encodeRecord11 ⟨cell.bit, .off, 0⟩
                    have sApp := downL_steps (.toAppendVerEntry des) cs1 v0 cs2 dTerm cj csCur
                      (.upDone (.pendingRightBackToSrc cell.bit) true) rfl
                    have sTot := StepsTo.trans sPreD (StepsTo.trans sBack sApp)
                    have hvt := appendEntry_valid des ⟨v0, downLCrumbs cs1 dTerm cs2 cj csCur⟩
                    rw [← sTot.1] at hvt
                    exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
                  else
                    have sAb : StepsTo 0 (.downRDone (.toRcDone (.readDestRight cell) dCell)) ⟨dTerm, csDest⟩
                        (.euler .abortToRoot) ⟨dTerm, csDest⟩ := by
                      apply StepsTo.of_alias
                      simp [microstep, step, onDownRDone, onCellRead, hoff, hdone, startAbort, dTerm]
                    have sTot := StepsTo.trans sPreD sAb
                    have hvt := abortToRoot_valid ⟨dTerm, csDest⟩
                    rw [← sTot.1] at hvt
                    exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
          | movingLeft =>
              have hmUp : microstep (.downRDone (.toRcDone .seekPending cell))
                  ⟨cellTerm, downRCrumbs pf.s1 pf.other pf.s2 pf.j (pushRChain pfs [.right rootLeft])⟩ =
                  .running (.up1 (.pendingLeftToParent cell))
                    ⟨pf.s2 ⋅ cellTerm, .left pf.j :: .right (pf.s1 ⋅ pf.other) :: pushRChain pfs [.right rootLeft]⟩ := by
                simp [microstep, step, onDownRDone, onCellRead, hstatus, startUp, applyAction, downRCrumbs, cellTerm]
              have sUpP := up_from_right_steps (.pendingLeftToParent cell) pf.s1 pf.other pf.s2 cellTerm pf.j
                (pushRChain pfs [.right rootLeft]) hpfValid.2.2 _ hmUp
              rw [← hcsCurEq] at sUpP
              let pTerm := (pf.s1 ⋅ pf.other) ⋅ ((pf.s2 ⋅ cellTerm) ⋅ pf.j)
              cases pfs with
              | nil =>
                  have sChk := hubChk_at_hub_steps (.pendingLeftChk cell) rootLeft pTerm
                    (.upDone (.pendingLeftToParent cell) true) rfl
                  have sAb : StepsTo 0 (.hubChkDone (.pendingLeftChk cell) true) ⟨pTerm, [.right rootLeft]⟩
                      (.euler .abortToRoot) ⟨pTerm, [.right rootLeft]⟩ :=
                    StepsTo.of_alias rfl
                  have sTot := StepsTo.trans sPre (StepsTo.trans sUpP (StepsTo.trans sChk sAb))
                  have hvt := abortToRoot_valid ⟨pTerm, [.right rootLeft]⟩
                  rw [← sTot.1] at hvt
                  exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
              | cons pf2 pfs2 =>
                  have hpfsMem : pf2 ∈ rframes ++ [hubCtx] := by
                    rw [hpfEq]; simp
                  have hpf2Valid : ValidFrameCtx pf2 := by
                    rcases List.mem_append.mp hpfsMem with hr | hh
                    · exact hall pf2 hr
                    · simp at hh; subst hh; exact hhub
                  have sChk := hubChk_below_hub_steps (.pendingLeftChk cell) pf2.s2 pTerm pf2.j
                    (.right (pf2.s1 ⋅ pf2.other) :: pushRChain pfs2 [.right rootLeft])
                    (.upDone (.pendingLeftToParent cell) true) rfl
                  let csPrev := downRCrumbs pf2.s1 pf2.other pf2.s2 pf2.j (pushRChain pfs2 [.right rootLeft])
                  have sDownPrev := downL_steps (.toRcStart (.readDestLeft cell))
                    pf.s1 pf.other pf.s2 cellTerm pf.j csPrev
                    (.hubChkDone (.pendingLeftChk cell) false) rfl
                  have sReadPrev := readCell_steps (.readDestLeft cell) pf2.s1 pf2.other pf2.s2 pf2.j
                    (pushRChain pfs2 [.right rootLeft]) hpf2Valid.2.2
                    pf.s1 pf.other pf.s2 cellTerm pf.j hpfValid
                  let prevCell := (obsScanBottomUp pf.other).getD defaultCell8
                  have sPreL := StepsTo.trans sPre (StepsTo.trans sUpP (StepsTo.trans sChk (StepsTo.trans sDownPrev sReadPrev)))
                  have hpfOtherLeaves :
                      leaves pf.other ≤ leaves (rebuild (hubTapeCursor rootLeft hubCtx rframes ((cs1 ⋅ v0) ⋅ ((cs2 ⋅ nextTape) ⋅ cj)))) := by
                    have hrebP : rebuild ⟨pTerm, csPrev⟩ =
                        rebuild (hubTapeCursor rootLeft hubCtx rframes ((cs1 ⋅ v0) ⋅ ((cs2 ⋅ nextTape) ⋅ cj))) := sPreL.1.symm
                    have hlP := leaves_rebuild ⟨pTerm, csPrev⟩
                    rw [hrebP] at hlP
                    dsimp only [pTerm] at hlP
                    simp only [leaves] at hlP
                    omega
                  if hoff : prevCell.status == .off then
                    let des := encodeRecord11 ⟨prevCell.bit, .active, cell.state.val⟩
                    have hmApp : microstep (.downRDone (.toRcDone (.readDestLeft cell) prevCell)) ⟨pTerm, csPrev⟩ =
                        .running (.downL1 (.toAppendVerEntry des)) ⟨pf.s1 ⋅ pf.other, .left ((pf.s2 ⋅ cellTerm) ⋅ pf.j) :: csPrev⟩ := by
                      simp [microstep, step, onDownRDone, onCellRead, hoff, startDownL, applyAction, des, pTerm]
                    have sApp := downL_steps (.toAppendVerEntry des) pf.s1 pf.other pf.s2 cellTerm pf.j csPrev _ hmApp
                    have sTot := StepsTo.trans sPreL sApp
                    have hvt := appendEntry_valid des ⟨pf.other, downLCrumbs pf.s1 cellTerm pf.s2 pf.j csPrev⟩
                    rw [← sTot.1] at hvt
                    exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
                  else if hdone : prevCell.status == .active && prevCell.state == cell.state then
                    let des := encodeRecord11 ⟨cell.bit, .off, 0⟩
                    have hmBack : microstep (.downRDone (.toRcDone (.readDestLeft cell) prevCell)) ⟨pTerm, csPrev⟩ =
                        .running (.downR1 (.toPendingLeftBackToSrc des))
                          ⟨(pf.s2 ⋅ cellTerm) ⋅ pf.j, .right (pf.s1 ⋅ pf.other) :: csPrev⟩ := by
                      simp [microstep, step, onDownRDone, onCellRead, hoff, hdone, startDownR, applyAction, des, pTerm]
                    have sBack := downR_steps (.toPendingLeftBackToSrc des) pf.s1 pf.other pf.s2 cellTerm pf.j csPrev _ hmBack
                    have sApp := downL_steps (.toAppendVerEntry des) cs1 v0 cs2 nextTape cj
                      (downRCrumbs pf.s1 pf.other pf.s2 pf.j csPrev)
                      (.downRDone (.toPendingLeftBackToSrc des)) rfl
                    have sTot := StepsTo.trans sPreL (StepsTo.trans sBack sApp)
                    have hvt := appendEntry_valid des
                      ⟨v0, downLCrumbs cs1 nextTape cs2 cj (downRCrumbs pf.s1 pf.other pf.s2 pf.j csPrev)⟩
                    rw [← sTot.1] at hvt
                    exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)
                  else
                    have sAb : StepsTo 0 (.downRDone (.toRcDone (.readDestLeft cell) prevCell)) ⟨pTerm, csPrev⟩
                        (.euler .abortToRoot) ⟨pTerm, csPrev⟩ := by
                      apply StepsTo.of_alias
                      simp [microstep, step, onDownRDone, onCellRead, hoff, hdone, startAbort, pTerm]
                    have sTot := StepsTo.trans sPreL sAb
                    have hvt := abortToRoot_valid ⟨pTerm, csPrev⟩
                    rw [← sTot.1] at hvt
                    exact validTermination_mono (by omega) (StepsTo.toValidTermination sTot hvt)

/-- Master All-Input Valid Termination Theorem: on EVERY `t : Term` (pure-S or not, canonical or not),
    `(initControl, rootCursor t)` terminates cleanly within `walkerBound t = 3500 * (leaves t + 1)`
    microticks and satisfies `ValidResult t`. -/
theorem all_input_validTermination (t : Term) :
    ValidTermination (walkerBound t) initControl (rootCursor t) := by
  unfold walkerBound walkerConst
  cases t with
  | s =>
      refine ⟨.normal, ⟨1, by omega, by omega, rfl⟩, ?_⟩
      intro _; intro ⟨_, hs⟩; cases hs
  | var n =>
      refine ⟨.normal, ⟨1, by omega, by omega, rfl⟩, ?_⟩
      intro _; intro ⟨_, hs⟩; cases hs
  | app rootLeft hub =>
      have sInit : StepsTo 1 initControl (rootCursor (rootLeft ⋅ hub))
          (.sf (.sf0 .hubInit)) ⟨hub, [.right rootLeft]⟩ :=
        StepsTo.of_step rfl
      have sHubSf := checkStrictFrame_steps .hubInit ⟨hub, [.right rootLeft]⟩
      cases hhub : strictFrameObs hub with
      | false =>
          rw [hhub] at sHubSf
          have sAb : StepsTo 0 (.sf (.sfDone .hubInit false)) ⟨hub, [.right rootLeft]⟩
              (.euler .abortToRoot) ⟨hub, [.right rootLeft]⟩ :=
            StepsTo.of_alias rfl
          have sTot := StepsTo.trans sInit (StepsTo.trans sHubSf sAb)
          have hvt := abortToRoot_valid ⟨hub, [.right rootLeft]⟩
          rw [← sTot.1] at hvt
          exact validTermination_mono (by simp [rootCursor, rebuild, rebuildWith]; omega)
            (StepsTo.toValidTermination sTot hvt)
      | true =>
          rw [hhub] at sHubSf
          obtain ⟨hs1, flag, hs2, tape, hj, rfl, hhs1, hhs2, hhj⟩ := strictFrameObs_decomp hhub
          have hsubLeaves :
              leaves flag ≤ leaves (rootLeft ⋅ ((hs1 ⋅ flag) ⋅ ((hs2 ⋅ tape) ⋅ hj))) ∧
              leaves tape ≤ leaves (rootLeft ⋅ ((hs1 ⋅ flag) ⋅ ((hs2 ⋅ tape) ⋅ hj))) := by
            simp only [leaves]
            constructor <;> omega
          have sDownFlag := downL_steps .toFlagInit hs1 flag hs2 tape hj [.right rootLeft]
            (.sf (.sfDone .hubInit true)) rfl
          let csFlag := downLCrumbs hs1 tape hs2 hj [.right rootLeft]
          have sAliasF : StepsTo 0 (.downLDone .toFlagInit) ⟨flag, csFlag⟩
              (.sf (.sf0 .flagInit)) ⟨flag, csFlag⟩ :=
            StepsTo.of_alias rfl
          have sFlagSf := checkStrictFrame_steps .flagInit ⟨flag, csFlag⟩
          cases hflag : strictFrameObs flag with
          | true =>
              rw [hflag] at sFlagSf
              obtain ⟨fs1, fl, fs2, fr, fj, rfl, _, _, _⟩ := strictFrameObs_decomp hflag
              have hflLeaves :
                  leaves fl ≤ leaves (rootLeft ⋅ ((hs1 ⋅ ((fs1 ⋅ fl) ⋅ ((fs2 ⋅ fr) ⋅ fj))) ⋅ ((hs2 ⋅ tape) ⋅ hj))) := by
                simp only [leaves]
                omega
              have sDownFl := downL_steps .toFrontier fs1 fl fs2 fr fj csFlag
                (.sf (.sfDone .flagInit true)) rfl
              let csFl := downLCrumbs fs1 fr fs2 fj csFlag
              have sAliasFr : StepsTo 0 (.downLDone .toFrontier) ⟨fl, csFl⟩
                  (.sf (.sf0 .frontierWalk)) ⟨fl, csFl⟩ :=
                StepsTo.of_alias rfl
              have sTot := StepsTo.trans sInit
                (StepsTo.trans sHubSf
                  (StepsTo.trans sDownFlag
                    (StepsTo.trans sAliasF
                      (StepsTo.trans sFlagSf (StepsTo.trans sDownFl sAliasFr)))))
              have hvt := frontierWalk_fuel_valid (leaves fl) ⟨fl, csFl⟩ (Nat.le_refl _)
              dsimp only [] at hvt
              rw [← sTot.1] at hvt
              exact validTermination_mono (by simp only [rootCursor, rebuild, rebuildWith]; omega)
                (StepsTo.toValidTermination sTot hvt)
          | false =>
              rw [hflag] at sFlagSf
              have sUpHub := up_from_left_steps .flagToHub hs1 flag hs2 tape hj [.right rootLeft] hhub
                (.sf (.sfDone .flagInit false)) rfl
              have sDownTape := downR_steps .toTapeInit hs1 flag hs2 tape hj [.right rootLeft]
                (.upDone .flagToHub false) rfl
              let hubCtx : FrameCtx := ⟨hs1, flag, hs2, hj⟩
              have hhubCtx : ValidFrameCtx hubCtx := ⟨hhs1, hhs2, hhj⟩
              have sAliasT : StepsTo 0 (.downRDone .toTapeInit)
                  (hubTapeCursor rootLeft hubCtx [] tape)
                  (.sf (.sf0 (.seekCell false)))
                  (hubTapeCursor rootLeft hubCtx [] tape) :=
                StepsTo.of_alias rfl
              have sTot := StepsTo.trans sInit
                (StepsTo.trans sHubSf
                  (StepsTo.trans sDownFlag
                    (StepsTo.trans sAliasF
                      (StepsTo.trans sFlagSf (StepsTo.trans sUpHub (StepsTo.trans sDownTape sAliasT))))))
              have hvt := seekPending_fuel_valid rootLeft hubCtx hhubCtx (leaves tape) tape []
                (Nat.le_refl _) (by intro _ h; simp at h)
              rw [← sTot.1] at hvt
              exact validTermination_mono (by simp only [rootCursor, rebuild, rebuildWith]; omega)
                (StepsTo.toValidTermination sTot hvt)

/-- **(b) All-Input Linear Microtick Bound**: on EVERY `t : Term`, running from
    `(initControl, rootCursor t)` finishes within `walkerConst * (leaves t + 1)` microticks,
    and stabilizes to `some (invoke t)` for all `fuel ≥ walkerConst * (leaves t + 1)`. -/
theorem all_input_linear_microtick_bound (t : Term) :
    runTicks (walkerConst * (leaves t + 1)) initControl (rootCursor t) = some (invoke t) ∧
    ∀ fuel, walkerConst * (leaves t + 1) ≤ fuel →
      runTicks fuel initControl (rootCursor t) = some (invoke t) := by
  obtain ⟨res, ⟨k, hk_lo, hk_hi, hex⟩, _⟩ := all_input_validTermination t
  have hB : execTicks (walkerBound t) initControl (rootCursor t) = .done res := by
    have heq : walkerBound t = k + (walkerBound t - k) := by omega
    rw [heq]
    exact execTicks_add_done (walkerBound t - k) hex
  have hrunB : runTicks (walkerBound t) initControl (rootCursor t) = some res := by
    simp [runTicks, hB]
  have hinv : invoke t = res := by
    simp [invoke, hrunB]
  subst res
  refine ⟨hrunB, ?_⟩
  intro fuel hfuel
  have heq : fuel = walkerBound t + (fuel - walkerBound t) := by
    unfold walkerBound
    omega
  rw [heq]
  have hF := execTicks_add_done (fuel - walkerBound t) hB
  simp [runTicks, hF]

/-- **(c) Exact Single-Contraction and Normality Contract**: on every pure-S closed `t : Term`,
    `invoke t = .normal ↔ ¬ ∃ t', Step t t'`, and `invoke t = .contracted t' → Step t t'`. -/
theorem pure_s_normality_and_contraction_contract (t : Term) (hpure : isPureS t = true) :
    (invoke t = .normal ↔ ¬ ∃ t', Step t t') ∧
    (∀ t', invoke t = .contracted t' → Step t t') := by
  obtain ⟨res, ⟨k, _, hk_hi, hex⟩, hv⟩ := all_input_validTermination t
  have hB : execTicks (walkerBound t) initControl (rootCursor t) = .done res := by
    have heq : walkerBound t = k + (walkerBound t - k) := by omega
    rw [heq]
    exact execTicks_add_done (walkerBound t - k) hex
  have hinv : invoke t = res := by
    simp [invoke, runTicks, hB]
  have hvPure := hv (by simpa [rootCursor, rebuild, rebuildWith] using hpure)
  rw [hinv]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hnorm
    subst hnorm
    exact hvPure
  · intro hnoStep
    cases res with
    | normal => rfl
    | contracted t' => exact False.elim (hnoStep ⟨t', hvPure⟩)
  · intro t' hcon
    subst hcon
    exact hvPure


/-! ## Section 7: Canonical Hub Agreement & Exact Trajectory Agreement with `fullRootSelector` -/

/-- Bound-free reachability between walker configurations (tick bounds are already established in Section 6). -/
def LeadsTo (c1 : Control) (cur1 : Cursor) (c2 : Control) (cur2 : Cursor) : Prop :=
  ∃ B, StepsTo B c1 cur1 c2 cur2

def FinishesWith (c : Control) (cur : Cursor) (res : InvokeResult) : Prop :=
  ∃ k, 1 ≤ k ∧ execTicks k c cur = .done res

theorem LeadsTo.of_stepsTo {B : Nat} {c1 c2 : Control} {cur1 cur2 : Cursor}
    (h : StepsTo B c1 cur1 c2 cur2) : LeadsTo c1 cur1 c2 cur2 :=
  ⟨B, h⟩

theorem LeadsTo.trans {c1 c2 c3 : Control} {cur1 cur2 cur3 : Cursor}
    (h1 : LeadsTo c1 cur1 c2 cur2) (h2 : LeadsTo c2 cur2 c3 cur3) :
    LeadsTo c1 cur1 c3 cur3 := by
  obtain ⟨B1, s1⟩ := h1
  obtain ⟨B2, s2⟩ := h2
  exact ⟨B1 + B2, StepsTo.trans s1 s2⟩

theorem LeadsTo.toFinishesWith {c1 c2 : Control} {cur1 cur2 : Cursor} {res : InvokeResult}
    (h1 : LeadsTo c1 cur1 c2 cur2) (h2 : FinishesWith c2 cur2 res) :
    FinishesWith c1 cur1 res := by
  obtain ⟨B, s1⟩ := h1
  obtain ⟨k, hlo, hex⟩ := h2
  obtain ⟨k', hk'_lo, _, hex'⟩ := s1.2 ⟨k, hlo, Nat.le_refl k, hex⟩
  exact ⟨k', hk'_lo, hex'⟩

theorem finishesWith_eq_invoke {root : Term} {res : InvokeResult}
    (h : FinishesWith initControl (rootCursor root) res) :
    invoke root = res := by
  obtain ⟨k, _, hex⟩ := h
  have hB := (all_input_linear_microtick_bound root).1
  unfold runTicks at hB
  cases hexB : execTicks (walkerConst * (leaves root + 1)) initControl (rootCursor root) with
  | running _ _ => simp [hexB] at hB
  | stuck => simp [hexB] at hB
  | done rB =>
      simp only [hexB, Option.some.injEq] at hB
      rw [← hB]
      exact execTicks_done_unique hexB hex

/-! ### Pure-S Closedness Preservation -/

theorem numeral_isPureS (n : Nat) : isPureS (numeral n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, isPureS, B, S, ih]

theorem generator_isPureS (m n : Nat) : isPureS (generator m n) = true := by
  simp [generator, isPureS, S, numeral_isPureS]

theorem phaseJunk_isPureS (p : Nat × Nat) : isPureS (phaseJunk p) = true := by
  rcases p with ⟨m, n⟩
  cases m <;> simp [phaseJunk, isPureS, S, numeral_isPureS, generator_isPureS]

theorem layoutTerm_isPureS (s : Layout) : ∀ m n : Nat, isPureS (layoutTerm s m n) = true := by
  induction s with
  | unopened => intro m n; exact generator_isPureS m n
  | opened l r ihl ihr =>
      intro m n
      cases n with
      | zero => cases m <;> simp [layoutTerm, generator_isPureS]
      | succ n =>
          cases n with
          | zero => cases m <;> simp [layoutTerm, generator_isPureS]
          | succ n =>
              cases m with
              | zero =>
                  simp [layoutTerm, frameTerm, isPureS, S, numeral_isPureS, generator_isPureS, ihl, ihr]
              | succ m =>
                  simp [layoutTerm, frameTerm, isPureS, S, numeral_isPureS, generator_isPureS, ihl, ihr]

theorem sEncodeU_isPureS (u : UConfig) : isPureS (sEncodeU u) = true := by
  change isPureS (canonicalRoot (initialRecords (encodeUConfig u)) 1 (depthBase 1) (depthJunk 0)) = true
  unfold canonicalRoot seedHubRoot canonicalTape depthBase phaseBase depthJunk
  simp [frameTerm, isPureS, S, numeral_isPureS, generator_isPureS, layoutTerm_isPureS, phaseJunk_isPureS]

theorem directedStep_preserves_isPureS {p : List Bool} {a b : Term}
    (h : DirectedStep p a b) (ha : isPureS a = true) : isPureS b = true := by
  induction h with
  | root x y z =>
      simp only [S, isPureS, Bool.and_eq_true] at ha ⊢
      exact ⟨⟨ha.1.1.2, ha.2⟩, ⟨ha.1.2, ha.2⟩⟩
  | left _ ih =>
      simp only [isPureS, Bool.and_eq_true] at ha ⊢
      exact ⟨ih ha.1, ha.2⟩
  | right _ ih =>
      simp only [isPureS, Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1, ih ha.2⟩

theorem fullSelectorTrace_preserves_isPureS {program : BinaryProgram} {k : Nat} {a b : Term}
    (ht : FullSelectorTrace program k a b) (ha : isPureS a = true) : isPureS b = true := by
  induction ht with
  | zero _ => exact ha
  | next _ hd _ ih => exact ih (directedStep_preserves_isPureS hd ha)

/-! ### Observation-to-Semantic Agreement on `isPureS` + `logicalTreeStrict` -/

theorem strictFrameObs_eq_flagValue_of_strict {t : Term}
    (hp : isPureS t = true) (hs : logicalTreeStrict t = true) :
    strictFrameObs t = flagValue t :=
  (obs_eq_on_pureS hp).2.trans (logicalTreeStrict_eq_flag hs)

theorem parseFrame_none_of_flagValue_false {t : Term} (hf : flagValue t = false) :
    parseFrame t = none := by
  unfold flagValue at hf
  cases h : parseFrame t with
  | none => rfl
  | some _ => simp [h] at hf

theorem strictFrame_pureS_decomp {t : Term}
    (hp : isPureS t = true) (hs : logicalTreeStrict t = true) (hf : flagValue t = true) :
    ∃ l r j,
      t = frameTerm l r j ∧
      strictFrameObs (frameTerm l r j) = true ∧
      isPureS l = true ∧ isPureS r = true ∧ isPureS j = true ∧
      logicalTreeStrict l = true ∧ logicalTreeStrict r = true ∧
      s2Obs j = false ∧
      ValidFrameCtx ⟨.s, l, .s, j⟩ ∧ ValidFrameCtx ⟨.s, r, .s, j⟩ := by
  unfold flagValue at hf
  cases hpf : parseFrame t with
  | none => simp [hpf] at hf
  | some triple =>
      rcases triple with ⟨l, r, j⟩
      have ht := parse_frame_sound t l r j hpf
      subst t
      have hobs : strictFrameObs (frameTerm l r j) = true := by
        rw [strictFrameObs_eq_flagValue_of_strict hp hs]
        rfl
      simp only [frameTerm, S, isPureS, Bool.and_eq_true] at hp
      rcases hp with ⟨⟨_, hpL⟩, ⟨_, hpR⟩, hpJ⟩
      rw [logicalTreeStrict_frame] at hs
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
      rcases hs with ⟨⟨hjNs2, hsL⟩, hsR⟩
      have hjObs : s2Obs j = false := by
        match j with
        | .app (.app a _) _ =>
            simp only [isPureS, Bool.and_eq_true] at hpJ
            cases a with
            | s => cases hjNs2
            | var _ => simp [isPureS] at hpJ
            | app _ _ => rfl
        | .s => rfl
        | .var _ => rfl
        | .app .s _ => rfl
        | .app (.var _) _ => rfl
      exact ⟨l, r, j, rfl, hobs, hpL, hpR, hpJ, hsL, hsR, hjObs, ⟨rfl, rfl, hjObs⟩, ⟨rfl, rfl, hjObs⟩⟩

theorem obsReadFields_eq_readFields :
    ∀ (n : Nat) (t : Term), isPureS t = true → logicalTreeStrict t = true →
      obsReadFields n t = readFields n t := by
  intro n
  induction n with
  | zero =>
      intro t hp hs
      simp [obsReadFields, readFields, strictFrameObs_eq_flagValue_of_strict hp hs]
  | succ m ih =>
      intro t hp hs
      cases hf : flagValue t with
      | false =>
          have hobs : strictFrameObs t = false :=
            (strictFrameObs_eq_flagValue_of_strict hp hs).trans hf
          have hpf : parseFrame t = none := parseFrame_none_of_flagValue_false hf
          simp [obsReadFields, readFields, hobs, hpf]
      | true =>
          obtain ⟨flag, rest, j, rfl, hobs, hpF, hpR, _, hsF, hsR, _, _, _⟩ :=
            strictFrame_pureS_decomp hp hs hf
          have hflagEq := strictFrameObs_eq_flagValue_of_strict hpF hsF
          have hrestEq := ih rest hpR hsR
          have hL : obsReadFields (m + 1) (frameTerm flag rest j) =
              (obsReadFields m rest).map (strictFrameObs flag :: ·) := by
            conv => lhs; unfold obsReadFields
            simp only [hobs, ↓reduceIte]
            rfl
          have hR : readFields (m + 1) (frameTerm flag rest j) =
              (readFields m rest).map (flagValue flag :: ·) := by
            conv => lhs; unfold readFields; rw [parse_frame]
          rw [hL, hR, hflagEq, hrestEq]

theorem obsHasFrames_eq_isSome :
    ∀ (n : Nat) (t : Term), isPureS t = true → logicalTreeStrict t = true →
      obsHasFrames (n + 1) t = (readFields n t).isSome := by
  intro n
  induction n with
  | zero =>
      intro t hp hs
      cases hf : flagValue t with
      | false =>
          have hobs : strictFrameObs t = false :=
            (strictFrameObs_eq_flagValue_of_strict hp hs).trans hf
          simp [obsHasFrames, readFields, hobs, hf]
      | true =>
          obtain ⟨flag, rest, j, rfl, hobs, _, _, _, _, _, _, _, _⟩ :=
            strictFrame_pureS_decomp hp hs hf
          have hL : obsHasFrames 1 (frameTerm flag rest j) = true := by
            unfold obsHasFrames
            simp only [hobs, ↓reduceIte]
            rfl
          have hR : (readFields 0 (frameTerm flag rest j)).isSome = true := by
            simp [readFields, hf]
          exact hL.trans hR.symm
  | succ m ih =>
      intro t hp hs
      cases hf : flagValue t with
      | false =>
          have hobs : strictFrameObs t = false :=
            (strictFrameObs_eq_flagValue_of_strict hp hs).trans hf
          have hpf : parseFrame t = none := parseFrame_none_of_flagValue_false hf
          simp [obsHasFrames, readFields, hobs, hpf]
      | true =>
          obtain ⟨flag, rest, j, rfl, hobs, _, hpR, _, _, hsR, _, _, _⟩ :=
            strictFrame_pureS_decomp hp hs hf
          have hrest := ih rest hpR hsR
          have hL : obsHasFrames (m + 2) (frameTerm flag rest j) = obsHasFrames (m + 1) rest := by
            conv => lhs; unfold obsHasFrames
            simp only [hobs, ↓reduceIte]
            rfl
          have hR : (readFields (m + 1) (frameTerm flag rest j)).isSome = (readFields m rest).isSome := by
            conv => lhs; arg 1; unfold readFields; rw [parse_frame]; dsimp only []
            cases readFields m rest <;> rfl
          rw [hL, hR, hrest]

theorem readFields_length :
    ∀ (n : Nat) (t : Term) (bs : List Bool), readFields n t = some bs → bs.length = n := by
  intro n
  induction n with
  | zero =>
      intro t bs h
      cases hf : flagValue t <;> simp [readFields, hf] at h
      subst bs; rfl
  | succ m ih =>
      intro t bs h
      cases hpf : parseFrame t with
      | none => simp [readFields, hpf] at h
      | some triple =>
          rcases triple with ⟨flag, rest, j⟩
          cases hr : readFields m rest with
          | none => simp [readFields, hpf, hr] at h
          | some tail =>
              simp only [readFields, hpf, hr, Option.map, Option.some.injEq] at h
              subst bs
              simp [ih rest tail hr]

theorem scanVersionTree_acc_fuel (width : Nat) :
    ∀ (fuel : Nat) (v : Term) (cur : Option (List Bool)),
      leaves v ≤ fuel →
      scanVersionTree width cur v =
        match scanVersionTree width none v with
        | some bs => some bs
        | none => cur := by
  intro fuel
  induction fuel with
  | zero =>
      intro v _ hle
      have hp := leaves_pos v
      exact False.elim (by omega)
  | succ m ih =>
      intro v cur hle
      cases hpf : parseFrame v with
      | none =>
          rw [scan_version_tree_closed width cur v hpf, scan_version_tree_closed width none v hpf]
      | some triple =>
          rcases triple with ⟨next, fields, j⟩
          have hv := parse_frame_sound v next fields j hpf
          subst v
          have hnLe : leaves next ≤ m := by
            rw [frame_leaves] at hle
            have := leaves_pos fields
            have := leaves_pos j
            omega
          rw [scan_version_tree_frame, scan_version_tree_frame]
          cases hr : readFields width fields with
          | none =>
              dsimp only []
              exact ih next cur hnLe
          | some bits =>
              dsimp only []
              rw [ih next (some bits) hnLe]
              cases hs : scanVersionTree width none next <;> rfl

theorem scanVersionTree_length_fuel (width : Nat) :
    ∀ (fuel : Nat) (v : Term) (cur : Option (List Bool)) (bs : List Bool),
      leaves v ≤ fuel →
      (∀ x, cur = some x → x.length = width) →
      scanVersionTree width cur v = some bs →
      bs.length = width := by
  intro fuel
  induction fuel with
  | zero =>
      intro v _ _ hle _ _
      have hp := leaves_pos v
      exact False.elim (by omega)
  | succ m ih =>
      intro v cur bs hle hcur hscan
      cases hpf : parseFrame v with
      | none =>
          rw [scan_version_tree_closed width cur v hpf] at hscan
          exact hcur bs hscan
      | some triple =>
          rcases triple with ⟨next, fields, j⟩
          have hv := parse_frame_sound v next fields j hpf
          subst v
          have hnLe : leaves next ≤ m := by
            rw [frame_leaves] at hle
            have := leaves_pos fields
            have := leaves_pos j
            omega
          rw [scan_version_tree_frame] at hscan
          cases hr : readFields width fields with
          | none =>
              rw [hr] at hscan
              exact ih next cur bs hnLe hcur hscan
          | some fbits =>
              rw [hr] at hscan
              have hfb : fbits.length = width := readFields_length width fields fbits hr
              exact ih next (some fbits) bs hnLe
                (by intro x hx; injection hx with hx'; rw [← hx']; exact hfb) hscan

theorem obsScanBottomUp_map_fuel :
    ∀ (fuel : Nat) (v : Term),
      leaves v ≤ fuel →
      isPureS v = true →
      logicalTreeStrict v = true →
      (obsScanBottomUp v).map cell8ToCell = (scanVersionTree 11 none v).bind decodeCellBits := by
  intro fuel
  induction fuel with
  | zero =>
      intro v hle _ _
      have hp := leaves_pos v
      exact False.elim (by omega)
  | succ m ih =>
      intro v hle hp hs
      cases hf : flagValue v with
      | false =>
          have hobs : strictFrameObs v = false :=
            (strictFrameObs_eq_flagValue_of_strict hp hs).trans hf
          have hpf : parseFrame v = none := parseFrame_none_of_flagValue_false hf
          rw [obsScanBottomUp_unopened hobs, scan_version_tree_closed 11 none v hpf]
          rfl
      | true =>
          obtain ⟨next, fields, j, rfl, hobs, hpN, hpF, _, hsN, hsF, _, _, _⟩ :=
            strictFrame_pureS_decomp hp hs hf
          have hnLe : leaves next ≤ m := by
            rw [frame_leaves] at hle
            have := leaves_pos fields
            have := leaves_pos j
            omega
          have hih := ih next hnLe hpN hsN
          have hobs' : strictFrameObs ((.s ⋅ next) ⋅ ((.s ⋅ fields) ⋅ j)) = true := hobs
          change (obsScanBottomUp ((.s ⋅ next) ⋅ ((.s ⋅ fields) ⋅ j))).map cell8ToCell =
            (scanVersionTree 11 none (frameTerm next fields j)).bind decodeCellBits
          rw [obsScanBottomUp_frame .s next .s fields j hobs']
          rw [scanVersionTree_acc_fuel 11 (leaves (frameTerm next fields j)) (frameTerm next fields j) none (Nat.le_refl _)]
          rw [scan_version_tree_frame]
          rw [scanVersionTree_acc_fuel 11 (leaves next) next _ (Nat.le_refl _)]
          cases hsn : scanVersionTree 11 none next with
          | some nbs =>
              have hlen : nbs.length = 11 :=
                scanVersionTree_length_fuel 11 (leaves next) next none nbs (Nat.le_refl _)
                  (fun _ h => nomatch h) hsn
              have hdec := decodeBits11_agrees ⟨nbs, hlen⟩
              rw [hsn] at hih
              dsimp only [Bind.bind, Option.bind] at hih
              rw [hdec] at hih
              cases hob : obsScanBottomUp next with
              | none => rw [hob] at hih; cases hih
              | some c =>
                  rw [hob] at hih
                  dsimp only [Option.map, Bind.bind, Option.bind] at hih ⊢
                  dsimp only [] at hdec
                  rw [hdec]
                  exact hih
          | none =>
              rw [hsn] at hih
              cases hob : obsScanBottomUp next with
              | some c => rw [hob] at hih; cases hih
              | none =>
                  dsimp only []
                  unfold obsReadVersion11
                  simp only [hobs', ↓reduceIte, obsReadFields_eq_readFields 11 fields hpF hsF]
                  cases hrf : readFields 11 fields with
                  | none => rfl
                  | some fbs =>
                      have hflen : fbs.length = 11 := readFields_length 11 fields fbs hrf
                      simp [hflen, decodeBits11_agrees ⟨fbs, hflen⟩]

theorem obsScanBottomUp_agrees {v : Term}
    (hp : isPureS v = true) (hs : logicalTreeStrict v = true) :
    cell8ToCell ((obsScanBottomUp v).getD defaultCell8) = cellFromVersion v := by
  have hmap := obsScanBottomUp_map_fuel (leaves v) v (Nat.le_refl _) hp hs
  unfold cellFromVersion
  rw [← hmap]
  cases obsScanBottomUp v <;> rfl

/-! ### Path Agreement of `OpenAndContract`, `FrontierWalk`, and `AppendVer` -/

theorem climbToRedex2_agrees (x y z : Term) (cs : List Crumb) {out : Term}
    (hdir : DirectedStep (crumbsPath cs) (rebuild ⟨.s ⋅ x ⋅ y ⋅ z, cs⟩) out) :
    FinishesWith (.euler .climbToRedex2) ⟨.s ⋅ x, .left y :: .left z :: cs⟩ (.contracted out) := by
  have hstep : DirectedStep (crumbsPath cs)
      (rebuild ⟨.s ⋅ x ⋅ y ⋅ z, cs⟩) (rebuild ⟨(x ⋅ z) ⋅ (y ⋅ z), cs⟩) :=
    directedStep_rebuild_root ⟨.s ⋅ x ⋅ y ⋅ z, cs⟩ rfl
  have heq : rebuild ⟨(x ⋅ z) ⋅ (y ⋅ z), cs⟩ = out :=
    directed_step_unique hstep out hdir
  refine ⟨3, by omega, ?_⟩
  rw [← heq]
  simp [execTicks, microstep, step, stepEuler, applyAction, contractRoot]

theorem rightArity_agrees (b2 r : Term) (cs : List Crumb) {rel : List Bool} {out : Term}
    (hpR : isPureS r = true)
    (hopen : (match arityFuel 5 r with
              | 4 => some [true, false]
              | 3 => some [true]
              | _ => none) = some rel)
    (hdir : DirectedStep (crumbsPath cs ++ rel) (rebuild ⟨(.s ⋅ b2) ⋅ r, cs⟩) out) :
    FinishesWith (.openSub (.rightArity ⟨0, by decide⟩)) ⟨r, .right (.s ⋅ b2) :: cs⟩ (.contracted out) := by
  let csR := Crumb.right (.s ⋅ b2) :: cs
  cases r with
  | s => simp [arityFuel] at hopen
  | var _ => simp [isPureS] at hpR
  | app r1 c1 =>
      simp only [isPureS, Bool.and_eq_true] at hpR
      rcases hpR with ⟨hpR1, _⟩
      have sR1 : StepsTo 1 (.openSub (.rightArity ⟨0, by decide⟩)) ⟨r1 ⋅ c1, csR⟩
          (.openSub (.rightArity ⟨1, by decide⟩)) ⟨r1, .left c1 :: csR⟩ :=
        StepsTo.of_step rfl
      cases r1 with
      | s => simp [arityFuel] at hopen
      | var _ => simp [isPureS] at hpR1
      | app r2 c2 =>
          simp only [isPureS, Bool.and_eq_true] at hpR1
          rcases hpR1 with ⟨hpR2, _⟩
          have sR2 : StepsTo 1 (.openSub (.rightArity ⟨1, by decide⟩)) ⟨r2 ⋅ c2, .left c1 :: csR⟩
              (.openSub (.rightArity ⟨2, by decide⟩)) ⟨r2, .left c2 :: .left c1 :: csR⟩ :=
            StepsTo.of_step rfl
          cases r2 with
          | s => simp [arityFuel] at hopen
          | var _ => simp [isPureS] at hpR2
          | app r3 c3 =>
              simp only [isPureS, Bool.and_eq_true] at hpR2
              rcases hpR2 with ⟨hpR3, _⟩
              have sR3 : StepsTo 1 (.openSub (.rightArity ⟨2, by decide⟩))
                  ⟨r3 ⋅ c3, .left c2 :: .left c1 :: csR⟩
                  (.openSub (.rightArity ⟨3, by decide⟩))
                  ⟨r3, .left c3 :: .left c2 :: .left c1 :: csR⟩ :=
                StepsTo.of_step rfl
              cases r3 with
              | s =>
                  simp only [arityFuel, Option.some.injEq] at hopen
                  subst rel
                  have sC : StepsTo 1 (.openSub (.rightArity ⟨3, by decide⟩))
                      ⟨.s, .left c3 :: .left c2 :: .left c1 :: csR⟩
                      (.euler .climbToRedex2) ⟨.s ⋅ c3, .left c2 :: .left c1 :: csR⟩ :=
                    StepsTo.of_step rfl
                  have hpath : crumbsPath csR = crumbsPath cs ++ [true] := by simp [csR, crumbsPath]
                  have hfin := climbToRedex2_agrees c3 c2 c1 csR (by rw [hpath]; exact hdir)
                  exact (LeadsTo.of_stepsTo (StepsTo.trans (StepsTo.trans sR1 sR2) (StepsTo.trans sR3 sC))).toFinishesWith hfin
              | var _ => simp [isPureS] at hpR3
              | app r4 c4 =>
                  simp only [isPureS, Bool.and_eq_true] at hpR3
                  rcases hpR3 with ⟨hpR4, _⟩
                  have sR4 : StepsTo 1 (.openSub (.rightArity ⟨3, by decide⟩))
                      ⟨r4 ⋅ c4, .left c3 :: .left c2 :: .left c1 :: csR⟩
                      (.openSub (.rightArity ⟨4, by decide⟩))
                      ⟨r4, .left c4 :: .left c3 :: .left c2 :: .left c1 :: csR⟩ :=
                    StepsTo.of_step rfl
                  cases r4 with
                  | s =>
                      simp only [arityFuel, Option.some.injEq] at hopen
                      subst rel
                      have sC : StepsTo 1 (.openSub (.rightArity ⟨4, by decide⟩))
                          ⟨.s, .left c4 :: .left c3 :: .left c2 :: .left c1 :: csR⟩
                          (.euler .climbToRedex2) ⟨.s ⋅ c4, .left c3 :: .left c2 :: .left c1 :: csR⟩ :=
                        StepsTo.of_step rfl
                      have hpath : crumbsPath (.left c1 :: csR) = crumbsPath cs ++ [true, false] := by
                        simp [csR, crumbsPath, List.append_assoc]
                      have hfin := climbToRedex2_agrees c4 c3 c2 (.left c1 :: csR) (by rw [hpath]; exact hdir)
                      exact (LeadsTo.of_stepsTo
                        (StepsTo.trans (StepsTo.trans sR1 sR2) (StepsTo.trans (StepsTo.trans sR3 sR4) sC))).toFinishesWith hfin
                  | var _ => simp [isPureS] at hpR4
                  | app _ _ => simp [arityFuel] at hopen

theorem openAndContract_agrees (cur : Cursor) {rel : List Bool} {out : Term}
    (hpRoot : isPureS (rebuild cur) = true)
    (hopen : nextOpeningAddress cur.focus = some rel)
    (hdir : DirectedStep (crumbsPath cur.crumbs ++ rel) (rebuild cur) out) :
    FinishesWith (.openSub .pf0) cur (.contracted out) := by
  have hpF : isPureS cur.focus = true := isPureS_focus_of_rebuild hpRoot
  have hpfNone : (parseFrame cur.focus).isSome = false := by
    unfold nextOpeningAddress at hopen
    cases hp : (parseFrame cur.focus).isSome with
    | false => rfl
    | true => simp [hp] at hopen
  have hpfObs : plainFrameObs cur.focus = false := by
    rw [(obs_eq_on_pureS hpF).1]
    exact hpfNone
  have sPf := checkPlainFrame_steps cur
  rw [hpfObs] at sPf
  rcases cur with ⟨f, cs⟩
  dsimp only [] at hpF hpfNone hopen hdir sPf ⊢
  unfold nextOpeningAddress at hopen
  rw [hpfNone] at hopen
  simp only [Bool.false_eq_true, ↓reduceIte] at hopen
  cases f with
  | s => simp [arityFuel] at hopen
  | var _ => simp [isPureS] at hpF
  | app a1 b1 =>
      have hpA1B1 : isPureS a1 = true ∧ isPureS b1 = true := by
        simpa [isPureS, Bool.and_eq_true] using hpF
      rcases hpA1B1 with ⟨hpA1, hpB1⟩
      have sL1 : StepsTo 1 (.openSub (.pfDone false)) ⟨a1 ⋅ b1, cs⟩
          (.openSub (.leftArity ⟨1, by decide⟩)) ⟨a1, .left b1 :: cs⟩ :=
        StepsTo.of_step rfl
      cases a1 with
      | s => simp [arityFuel] at hopen
      | var _ => simp [isPureS] at hpA1
      | app a2 b2 =>
          simp only [isPureS, Bool.and_eq_true] at hpA1
          rcases hpA1 with ⟨hpA2, _⟩
          have sL2 : StepsTo 1 (.openSub (.leftArity ⟨1, by decide⟩)) ⟨a2 ⋅ b2, .left b1 :: cs⟩
              (.openSub (.leftArity ⟨2, by decide⟩)) ⟨a2, .left b2 :: .left b1 :: cs⟩ :=
            StepsTo.of_step rfl
          cases a2 with
          | s =>
              have sToR : StepsTo 3 (.openSub (.leftArity ⟨2, by decide⟩))
                  ⟨.s, .left b2 :: .left b1 :: cs⟩
                  (.openSub (.rightArity ⟨0, by decide⟩)) ⟨b1, .right (.s ⋅ b2) :: cs⟩ :=
                StepsTo.of_exec (k := 3) (by omega) (by omega) rfl
              simp only [arityFuel] at hopen
              have hfin := rightArity_agrees b2 b1 cs hpB1 hopen hdir
              exact (LeadsTo.of_stepsTo (StepsTo.trans (StepsTo.trans sPf sL1) (StepsTo.trans sL2 sToR))).toFinishesWith hfin
          | var _ => simp [isPureS] at hpA2
          | app a3 b3 =>
              simp only [isPureS, Bool.and_eq_true] at hpA2
              rcases hpA2 with ⟨hpA3, _⟩
              have sL3 : StepsTo 1 (.openSub (.leftArity ⟨2, by decide⟩)) ⟨a3 ⋅ b3, .left b2 :: .left b1 :: cs⟩
                  (.openSub (.leftArity ⟨3, by decide⟩)) ⟨a3, .left b3 :: .left b2 :: .left b1 :: cs⟩ :=
                StepsTo.of_step rfl
              cases a3 with
              | s =>
                  simp only [arityFuel, Option.some.injEq] at hopen
                  subst rel
                  simp only [List.append_nil] at hdir
                  have sC : StepsTo 1 (.openSub (.leftArity ⟨3, by decide⟩))
                      ⟨.s, .left b3 :: .left b2 :: .left b1 :: cs⟩
                      (.euler .climbToRedex2) ⟨.s ⋅ b3, .left b2 :: .left b1 :: cs⟩ :=
                    StepsTo.of_step rfl
                  have hfin := climbToRedex2_agrees b3 b2 b1 cs hdir
                  exact (LeadsTo.of_stepsTo
                    (StepsTo.trans (StepsTo.trans sPf sL1) (StepsTo.trans sL2 (StepsTo.trans sL3 sC)))).toFinishesWith hfin
              | var _ => simp [isPureS] at hpA3
              | app a4 b4 =>
                  simp only [isPureS, Bool.and_eq_true] at hpA3
                  rcases hpA3 with ⟨hpA4, _⟩
                  have sL4 : StepsTo 1 (.openSub (.leftArity ⟨3, by decide⟩))
                      ⟨a4 ⋅ b4, .left b3 :: .left b2 :: .left b1 :: cs⟩
                      (.openSub (.leftArity ⟨4, by decide⟩))
                      ⟨a4, .left b4 :: .left b3 :: .left b2 :: .left b1 :: cs⟩ :=
                    StepsTo.of_step rfl
                  cases a4 with
                  | s =>
                      simp only [arityFuel, Option.some.injEq] at hopen
                      subst rel
                      have sC : StepsTo 1 (.openSub (.leftArity ⟨4, by decide⟩))
                          ⟨.s, .left b4 :: .left b3 :: .left b2 :: .left b1 :: cs⟩
                          (.euler .climbToRedex2) ⟨.s ⋅ b4, .left b3 :: .left b2 :: .left b1 :: cs⟩ :=
                        StepsTo.of_step rfl
                      have hpath : crumbsPath (.left b1 :: cs) = crumbsPath cs ++ [false] := by
                        simp [crumbsPath]
                      have hfin := climbToRedex2_agrees b4 b3 b2 (.left b1 :: cs) (by rw [hpath]; exact hdir)
                      exact (LeadsTo.of_stepsTo
                        (StepsTo.trans (StepsTo.trans sPf sL1)
                          (StepsTo.trans sL2 (StepsTo.trans (StepsTo.trans sL3 sL4) sC)))).toFinishesWith hfin
                  | var _ => simp [isPureS] at hpA4
                  | app _ _ => simp [arityFuel] at hopen

theorem selectOpeningAt_rebuild (cur : Cursor) {path : List Bool}
    (hsel : selectOpeningAt (rebuild cur) (crumbsPath cur.crumbs) = some path) :
    ∃ rel, nextOpeningAddress cur.focus = some rel ∧ path = crumbsPath cur.crumbs ++ rel := by
  unfold selectOpeningAt rebuild at hsel
  rw [termAt_rebuildWith cur.crumbs cur.focus] at hsel
  dsimp only [Bind.bind, Option.bind] at hsel
  cases hn : nextOpeningAddress cur.focus with
  | none => simp [hn] at hsel
  | some rel =>
      simp only [hn, Option.some.injEq] at hsel
      exact ⟨rel, rfl, hsel.symm⟩

theorem openSub_of_selectOpeningAt (cur : Cursor) {path : List Bool} {out : Term}
    (hp : isPureS (rebuild cur) = true)
    (hsel : selectOpeningAt (rebuild cur) (crumbsPath cur.crumbs) = some path)
    (hdir : DirectedStep path (rebuild cur) out) :
    FinishesWith (.openSub .pf0) cur (.contracted out) := by
  obtain ⟨rel, hopen, rfl⟩ := selectOpeningAt_rebuild cur hsel
  exact openAndContract_agrees cur hp hopen hdir

theorem closedLeftFrontier_closed {t : Term} (h : parseFrame t = none) :
    closedLeftFrontier t = [] := by
  match t with
  | .app (.app .s _) (.app (.app .s _) _) => simp [parseFrame] at h
  | .s => rfl
  | .var _ => rfl
  | .app .s _ => rfl
  | .app (.var _) _ => rfl
  | .app (.app (.var _) _) _ => rfl
  | .app (.app (.app _ _) _) _ => rfl
  | .app (.app .s _) .s => rfl
  | .app (.app .s _) (.var _) => rfl
  | .app (.app .s _) (.app .s _) => rfl
  | .app (.app .s _) (.app (.var _) _) => rfl
  | .app (.app .s _) (.app (.app (.var _) _) _) => rfl
  | .app (.app .s _) (.app (.app (.app _ _) _) _) => rfl

theorem frontierWalk_agrees :
    ∀ (fuel : Nat) (cur : Cursor) {path : List Bool} {out : Term},
      leaves cur.focus ≤ fuel →
      isPureS (rebuild cur) = true →
      logicalTreeStrict cur.focus = true →
      selectOpeningAt (rebuild cur) (crumbsPath cur.crumbs ++ closedLeftFrontier cur.focus) = some path →
      DirectedStep path (rebuild cur) out →
      FinishesWith (.sf (.sf0 .frontierWalk)) cur (.contracted out) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur _ _ hle _ _ _ _
      have hp := leaves_pos cur.focus
      exact False.elim (by omega)
  | succ m ih =>
      intro cur path out hle hpRoot hsFocus hsel hdir
      rcases cur with ⟨u, cs⟩
      dsimp only [] at hle hsFocus hsel ⊢
      have hpU : isPureS u = true := isPureS_focus_of_rebuild hpRoot
      have sSf := checkStrictFrame_steps .frontierWalk ⟨u, cs⟩
      dsimp only [] at sSf
      cases hf : flagValue u with
      | false =>
          have hobs : strictFrameObs u = false := (strictFrameObs_eq_flagValue_of_strict hpU hsFocus).trans hf
          rw [hobs] at sSf
          have hcf : closedLeftFrontier u = [] := closedLeftFrontier_closed (parseFrame_none_of_flagValue_false hf)
          rw [hcf, List.append_nil] at hsel
          have sOp : StepsTo 0 (.sf (.sfDone .frontierWalk false)) ⟨u, cs⟩ (.openSub .pf0) ⟨u, cs⟩ :=
            StepsTo.of_alias rfl
          exact (LeadsTo.of_stepsTo (StepsTo.trans sSf sOp)).toFinishesWith
            (openSub_of_selectOpeningAt ⟨u, cs⟩ hpRoot hsel hdir)
      | true =>
          obtain ⟨l, r, j, rfl, hobs, _, _, _, hsL, _, _, _, _⟩ :=
            strictFrame_pureS_decomp hpU hsFocus hf
          rw [hobs] at sSf
          have hlLe : leaves l ≤ m := by
            rw [frame_leaves] at hle
            have := leaves_pos r
            have := leaves_pos j
            omega
          have sDownL := downL_steps .toFrontier .s l .s r j cs (.sf (.sfDone .frontierWalk true)) rfl
          have sAlias : StepsTo 0 (.downLDone .toFrontier) ⟨l, downLCrumbs .s r .s j cs⟩
              (.sf (.sf0 .frontierWalk)) ⟨l, downLCrumbs .s r .s j cs⟩ :=
            StepsTo.of_alias rfl
          have hsel' : selectOpeningAt (rebuild ⟨l, downLCrumbs .s r .s j cs⟩)
              (crumbsPath (downLCrumbs .s r .s j cs) ++ closedLeftFrontier l) = some path := by
            have hreb : rebuild ⟨l, downLCrumbs .s r .s j cs⟩ = rebuild ⟨frameTerm l r j, cs⟩ := rfl
            rw [hreb, downLCrumbs_path, List.append_assoc]
            exact hsel
          have hfin := ih ⟨l, downLCrumbs .s r .s j cs⟩ hlLe hpRoot hsL hsel' hdir
          exact (LeadsTo.of_stepsTo (StepsTo.trans sSf (StepsTo.trans sDownL sAlias))).toFinishesWith hfin

theorem appendFld_agrees :
    ∀ (bits : List Bool) (hle : bits.length ≤ 11) (cur : Cursor) {slot path : List Bool} {out : Term},
      isPureS (rebuild cur) = true →
      logicalTreeStrict cur.focus = true →
      chooseSFields bits cur.focus = some slot →
      selectOpeningAt (rebuild cur) (crumbsPath cur.crumbs ++ slot) = some path →
      DirectedStep path (rebuild cur) out →
      FinishesWith (.sf (.sf0 (.appendFldNode ⟨bits, hle⟩))) cur (.contracted out) := by
  intro bits
  induction bits with
  | nil =>
      intro hle cur slot path out hpRoot hsFocus hchoose hsel hdir
      rcases cur with ⟨f, cs⟩
      dsimp only [] at hsFocus hchoose hsel ⊢
      have hpF : isPureS f = true := isPureS_focus_of_rebuild hpRoot
      have sSf := checkStrictFrame_steps (.appendFldNode ⟨[], hle⟩) ⟨f, cs⟩
      dsimp only [] at sSf
      cases hf : flagValue f with
      | true => simp [chooseSFields, hf] at hchoose
      | false =>
          simp only [chooseSFields, hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hchoose
          subst slot
          rw [List.append_nil] at hsel
          have hobs : strictFrameObs f = false := (strictFrameObs_eq_flagValue_of_strict hpF hsFocus).trans hf
          rw [hobs] at sSf
          have sOp : StepsTo 0 (.sf (.sfDone (.appendFldNode ⟨[], hle⟩) false)) ⟨f, cs⟩ (.openSub .pf0) ⟨f, cs⟩ :=
            StepsTo.of_alias rfl
          exact (LeadsTo.of_stepsTo (StepsTo.trans sSf sOp)).toFinishesWith
            (openSub_of_selectOpeningAt ⟨f, cs⟩ hpRoot hsel hdir)
  | cons b bs ih =>
      intro hle cur slot path out hpRoot hsFocus hchoose hsel hdir
      have hbs : bs.length ≤ 11 := by simp at hle; omega
      rcases cur with ⟨f, cs⟩
      dsimp only [] at hsFocus hchoose hsel ⊢
      have hpF : isPureS f = true := isPureS_focus_of_rebuild hpRoot
      have sSf := checkStrictFrame_steps (.appendFldNode ⟨b :: bs, hle⟩) ⟨f, cs⟩
      dsimp only [] at sSf
      cases hf : flagValue f with
      | false =>
          have hpf : parseFrame f = none := parseFrame_none_of_flagValue_false hf
          simp only [chooseSFields, hpf, Option.some.injEq] at hchoose
          subst slot
          rw [List.append_nil] at hsel
          have hobs : strictFrameObs f = false := (strictFrameObs_eq_flagValue_of_strict hpF hsFocus).trans hf
          rw [hobs] at sSf
          have sOp : StepsTo 0 (.sf (.sfDone (.appendFldNode ⟨b :: bs, hle⟩) false)) ⟨f, cs⟩ (.openSub .pf0) ⟨f, cs⟩ :=
            StepsTo.of_alias rfl
          exact (LeadsTo.of_stepsTo (StepsTo.trans sSf sOp)).toFinishesWith
            (openSub_of_selectOpeningAt ⟨f, cs⟩ hpRoot hsel hdir)
      | true =>
          obtain ⟨flag, rest, fj, rfl, hobs, hpFlag, _, _, hsFlag, hsRest, _, _, _⟩ :=
            strictFrame_pureS_decomp hpF hsFocus hf
          rw [hobs] at sSf
          cases b with
          | false =>
              simp only [chooseSFields, parse_frame, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hchoose
              cases hcs : chooseSFields bs rest with
              | none => simp [hcs] at hchoose
              | some slot' =>
                  simp only [hcs, Option.map, Option.some.injEq] at hchoose
                  subst slot
                  have sDownR := downR_steps (.toAppendFld ⟨bs, hbs⟩) .s flag .s rest fj cs
                    (.sf (.sfDone (.appendFldNode ⟨false :: bs, hle⟩) true)) rfl
                  have sAlias : StepsTo 0 (.downRDone (.toAppendFld ⟨bs, hbs⟩))
                      ⟨rest, downRCrumbs .s flag .s fj cs⟩
                      (.sf (.sf0 (.appendFldNode ⟨bs, hbs⟩)))
                      ⟨rest, downRCrumbs .s flag .s fj cs⟩ :=
                    StepsTo.of_alias rfl
                  have hsel' : selectOpeningAt (rebuild ⟨rest, downRCrumbs .s flag .s fj cs⟩)
                      (crumbsPath (downRCrumbs .s flag .s fj cs) ++ slot') = some path := by
                    have hreb : rebuild ⟨rest, downRCrumbs .s flag .s fj cs⟩ =
                        rebuild ⟨frameTerm flag rest fj, cs⟩ := rfl
                    rw [hreb, downRCrumbs_path, List.append_assoc]
                    exact hsel
                  have hfin := ih hbs ⟨rest, downRCrumbs .s flag .s fj cs⟩ hpRoot hsRest hcs hsel' hdir
                  exact (LeadsTo.of_stepsTo (StepsTo.trans sSf (StepsTo.trans sDownR sAlias))).toFinishesWith hfin
          | true =>
              have sDownL := downL_steps (.toAppendFldFlag ⟨bs, hbs⟩) .s flag .s rest fj cs
                (.sf (.sfDone (.appendFldNode ⟨true :: bs, hle⟩) true)) rfl
              have sAlias1 : StepsTo 0 (.downLDone (.toAppendFldFlag ⟨bs, hbs⟩))
                  ⟨flag, downLCrumbs .s rest .s fj cs⟩
                  (.sf (.sf0 (.appendFldFlag ⟨bs, hbs⟩)))
                  ⟨flag, downLCrumbs .s rest .s fj cs⟩ :=
                StepsTo.of_alias rfl
              have sFlagSf := checkStrictFrame_steps (.appendFldFlag ⟨bs, hbs⟩)
                ⟨flag, downLCrumbs .s rest .s fj cs⟩
              dsimp only [] at sFlagSf
              rw [strictFrameObs_eq_flagValue_of_strict hpFlag hsFlag] at sFlagSf
              cases hfv : flagValue flag with
              | false =>
                  rw [hfv] at sFlagSf
                  simp only [chooseSFields, parse_frame, hfv, Bool.not_false, Bool.and_self, ↓reduceIte,
                    Option.some.injEq] at hchoose
                  subst slot
                  have sOp : StepsTo 0 (.sf (.sfDone (.appendFldFlag ⟨bs, hbs⟩) false))
                      ⟨flag, downLCrumbs .s rest .s fj cs⟩
                      (.openSub .pf0) ⟨flag, downLCrumbs .s rest .s fj cs⟩ :=
                    StepsTo.of_alias rfl
                  have hsel' : selectOpeningAt (rebuild ⟨flag, downLCrumbs .s rest .s fj cs⟩)
                      (crumbsPath (downLCrumbs .s rest .s fj cs)) = some path := by
                    have hreb : rebuild ⟨flag, downLCrumbs .s rest .s fj cs⟩ =
                        rebuild ⟨frameTerm flag rest fj, cs⟩ := rfl
                    rw [hreb, downLCrumbs_path]
                    exact hsel
                  have hfin := openSub_of_selectOpeningAt ⟨flag, downLCrumbs .s rest .s fj cs⟩ hpRoot hsel' hdir
                  exact (LeadsTo.of_stepsTo
                    (StepsTo.trans sSf (StepsTo.trans sDownL (StepsTo.trans sAlias1 (StepsTo.trans sFlagSf sOp))))).toFinishesWith hfin
              | true =>
                  rw [hfv] at sFlagSf
                  simp only [chooseSFields, parse_frame, hfv, Bool.not_true, Bool.and_false, Bool.false_eq_true,
                    ↓reduceIte] at hchoose
                  cases hcs : chooseSFields bs rest with
                  | none => simp [hcs] at hchoose
                  | some slot' =>
                      simp only [hcs, Option.map, Option.some.injEq] at hchoose
                      subst slot
                      have sUpL := up_from_left_steps (.appendFldFlagBack ⟨bs, hbs⟩) .s flag .s rest fj cs hobs
                        (.sf (.sfDone (.appendFldFlag ⟨bs, hbs⟩) true)) rfl
                      have sDownR := downR_steps (.toAppendFld ⟨bs, hbs⟩) .s flag .s rest fj cs
                        (.upDone (.appendFldFlagBack ⟨bs, hbs⟩) false) rfl
                      have sAlias2 : StepsTo 0 (.downRDone (.toAppendFld ⟨bs, hbs⟩))
                          ⟨rest, downRCrumbs .s flag .s fj cs⟩
                          (.sf (.sf0 (.appendFldNode ⟨bs, hbs⟩)))
                          ⟨rest, downRCrumbs .s flag .s fj cs⟩ :=
                        StepsTo.of_alias rfl
                      have hsel' : selectOpeningAt (rebuild ⟨rest, downRCrumbs .s flag .s fj cs⟩)
                          (crumbsPath (downRCrumbs .s flag .s fj cs) ++ slot') = some path := by
                        have hreb : rebuild ⟨rest, downRCrumbs .s flag .s fj cs⟩ =
                            rebuild ⟨frameTerm flag rest fj, cs⟩ := rfl
                        rw [hreb, downRCrumbs_path, List.append_assoc]
                        exact hsel
                      have hfin := ih hbs ⟨rest, downRCrumbs .s flag .s fj cs⟩ hpRoot hsRest hcs hsel' hdir
                      exact (LeadsTo.of_stepsTo
                        (StepsTo.trans sSf
                          (StepsTo.trans sDownL
                            (StepsTo.trans sAlias1
                              (StepsTo.trans sFlagSf (StepsTo.trans sUpL (StepsTo.trans sDownR sAlias2))))))).toFinishesWith hfin

theorem appendVer_agrees (desired : Bits11) :
    ∀ (fuel : Nat) (cur : Cursor) {slot path : List Bool} {out : Term},
      leaves cur.focus ≤ fuel →
      isPureS (rebuild cur) = true →
      logicalTreeStrict cur.focus = true →
      chooseSVersionTree 11 desired.val cur.focus = some slot →
      selectOpeningAt (rebuild cur) (crumbsPath cur.crumbs ++ slot) = some path →
      DirectedStep path (rebuild cur) out →
      FinishesWith (.sf (.sf0 (.appendVer desired))) cur (.contracted out) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur _ _ _ hle _ _ _ _ _
      have hp := leaves_pos cur.focus
      exact False.elim (by omega)
  | succ m ih =>
      intro cur slot path out hle hpRoot hsFocus hchoose hsel hdir
      rcases cur with ⟨v, cs⟩
      dsimp only [] at hle hsFocus hchoose hsel ⊢
      have hpV : isPureS v = true := isPureS_focus_of_rebuild hpRoot
      have sSf := checkStrictFrame_steps (.appendVer desired) ⟨v, cs⟩
      dsimp only [] at sSf
      cases hf : flagValue v with
      | false =>
          have hpf : parseFrame v = none := parseFrame_none_of_flagValue_false hf
          rw [choose_tree_closed 11 desired.val v hpf] at hchoose
          injection hchoose with hslot
          subst hslot
          rw [List.append_nil] at hsel
          have hobs : strictFrameObs v = false := (strictFrameObs_eq_flagValue_of_strict hpV hsFocus).trans hf
          rw [hobs] at sSf
          have sOp : StepsTo 0 (.sf (.sfDone (.appendVer desired) false)) ⟨v, cs⟩ (.openSub .pf0) ⟨v, cs⟩ :=
            StepsTo.of_alias rfl
          exact (LeadsTo.of_stepsTo (StepsTo.trans sSf sOp)).toFinishesWith
            (openSub_of_selectOpeningAt ⟨v, cs⟩ hpRoot hsel hdir)
      | true =>
          obtain ⟨vnext, fields, vj, rfl, hobs, _, hpFields, _, hsVnext, hsFields, _, hvCtxL, _⟩ :=
            strictFrame_pureS_decomp hpV hsFocus hf
          rw [hobs] at sSf
          have hvLe : leaves vnext ≤ m := by
            rw [frame_leaves] at hle
            have := leaves_pos fields
            have := leaves_pos vj
            omega
          have sDownR1 := downR_steps (.toChkComm desired) .s vnext .s fields vj cs
            (.sf (.sfDone (.appendVer desired) true)) rfl
          have sChk := chkCommEntry_steps desired .s vnext .s fields vj cs hvCtxL
          rw [obsHasFrames_eq_isSome 11 fields hpFields hsFields] at sChk
          rw [choose_tree_frame 11 desired.val vnext fields vj] at hchoose
          cases hrf : readFields 11 fields with
          | some fbs =>
              rw [hrf] at sChk hchoose
              dsimp only [Option.isSome] at sChk
              cases hcs : chooseSVersionTree 11 desired.val vnext with
              | none => simp [hcs] at hchoose
              | some slot' =>
                  simp only [hcs, Option.map, Option.some.injEq] at hchoose
                  subst slot
                  have sDownL := downL_steps (.toAppendVerNext desired) .s vnext .s fields vj cs
                    (.upDone (.chkCommClimb desired true ⟨0, by decide⟩) true) rfl
                  have sAlias : StepsTo 0 (.downLDone (.toAppendVerNext desired))
                      ⟨vnext, downLCrumbs .s fields .s vj cs⟩
                      (.sf (.sf0 (.appendVer desired)))
                      ⟨vnext, downLCrumbs .s fields .s vj cs⟩ :=
                    StepsTo.of_alias rfl
                  have hsel' : selectOpeningAt (rebuild ⟨vnext, downLCrumbs .s fields .s vj cs⟩)
                      (crumbsPath (downLCrumbs .s fields .s vj cs) ++ slot') = some path := by
                    have hreb : rebuild ⟨vnext, downLCrumbs .s fields .s vj cs⟩ =
                        rebuild ⟨frameTerm vnext fields vj, cs⟩ := rfl
                    rw [hreb, downLCrumbs_path, List.append_assoc]
                    exact hsel
                  have hfin := ih ⟨vnext, downLCrumbs .s fields .s vj cs⟩ hvLe hpRoot hsVnext hcs hsel' hdir
                  exact (LeadsTo.of_stepsTo
                    (StepsTo.trans sSf (StepsTo.trans sDownR1 (StepsTo.trans sChk (StepsTo.trans sDownL sAlias))))).toFinishesWith hfin
          | none =>
              rw [hrf] at sChk hchoose
              dsimp only [Option.isSome] at sChk
              cases hcs : chooseSFields desired.val fields with
              | none => simp [hcs] at hchoose
              | some slot' =>
                  simp only [hcs, Option.map, Option.some.injEq] at hchoose
                  subst slot
                  let remAll : BitsLe11 := ⟨desired.val, Nat.le_of_eq desired.property⟩
                  have sDownR2 := downR_steps (.toAppendFld remAll) .s vnext .s fields vj cs
                    (.upDone (.chkCommClimb desired false ⟨0, by decide⟩) true) rfl
                  have sAlias : StepsTo 0 (.downRDone (.toAppendFld remAll))
                      ⟨fields, downRCrumbs .s vnext .s vj cs⟩
                      (.sf (.sf0 (.appendFldNode remAll)))
                      ⟨fields, downRCrumbs .s vnext .s vj cs⟩ :=
                    StepsTo.of_alias rfl
                  have hsel' : selectOpeningAt (rebuild ⟨fields, downRCrumbs .s vnext .s vj cs⟩)
                      (crumbsPath (downRCrumbs .s vnext .s vj cs) ++ slot') = some path := by
                    have hreb : rebuild ⟨fields, downRCrumbs .s vnext .s vj cs⟩ =
                        rebuild ⟨frameTerm vnext fields vj, cs⟩ := rfl
                    rw [hreb, downRCrumbs_path, List.append_assoc]
                    exact hsel
                  have hfin := appendFld_agrees desired.val (Nat.le_of_eq desired.property)
                    ⟨fields, downRCrumbs .s vnext .s vj cs⟩ hpRoot hsFields hcs hsel' hdir
                  exact (LeadsTo.of_stepsTo
                    (StepsTo.trans sSf (StepsTo.trans sDownR1 (StepsTo.trans sChk (StepsTo.trans sDownR2 sAlias))))).toFinishesWith hfin

theorem appendEntry_agrees (record : Cell) (cur : Cursor) {path : List Bool} {out : Term}
    (hpRoot : isPureS (rebuild cur) = true)
    (hsFocus : logicalTreeStrict cur.focus = true)
    (hselVer : selectVersionAt (rebuild cur) (crumbsPath cur.crumbs) record = some path)
    (hdir : DirectedStep path (rebuild cur) out) :
    FinishesWith (.downLDone (.toAppendVerEntry (encodeRecord11 record))) cur (.contracted out) := by
  unfold selectVersionAt at hselVer
  have hat : termAt (rebuild cur) (crumbsPath cur.crumbs) = some cur.focus :=
    termAt_rebuildWith cur.crumbs cur.focus
  rw [hat] at hselVer
  dsimp only [Bind.bind, Option.bind] at hselVer
  cases hcs : chooseSVersionTree 11 (encodeCellBits record (stateBits8 record.state)) cur.focus with
  | none => simp [hcs] at hselVer
  | some slot =>
      rw [hcs] at hselVer
      dsimp only [] at hselVer
      have sAlias : StepsTo 0 (.downLDone (.toAppendVerEntry (encodeRecord11 record))) cur
          (.sf (.sf0 (.appendVer (encodeRecord11 record)))) cur :=
        StepsTo.of_alias rfl
      have hfin := appendVer_agrees (encodeRecord11 record) (leaves cur.focus) cur (Nat.le_refl _)
        hpRoot hsFocus hcs hselVer hdir
      exact (LeadsTo.of_stepsTo sAlias).toFinishesWith hfin

/-! ### Path Agreement of Two-Pass Tape Scan (`SeekActive` & `SeekPending`) and Canonical Hub -/

def CanonicalFrameCtx (f : FrameCtx) : Prop :=
  f.s1 = .s ∧ f.s2 = .s ∧ s2Obs f.j = false ∧ isPureS f.other = true ∧ logicalTreeStrict f.other = true

theorem canonicalFrameCtx_valid {f : FrameCtx} (hf : CanonicalFrameCtx f) : ValidFrameCtx f := by
  rcases hf with ⟨h1, h2, hj, _, _⟩
  unfold ValidFrameCtx
  rw [h1, h2]
  exact ⟨rfl, rfl, hj⟩

theorem fin256_beq_eq_val_beq (a b : Fin 256) : (a == b) = (a.val == b.val) := by
  if h : a.val = b.val then
    have h1 : (a == b) = true := decide_eq_true (Fin.ext h)
    have h2 : (a.val == b.val) = true := decide_eq_true h
    exact h1.trans h2.symm
  else
    have hab : a ≠ b := fun heq => h (congrArg Fin.val heq)
    have h1 : (a == b) = false := decide_eq_false hab
    have h2 : (a.val == b.val) = false := decide_eq_false h
    exact h1.trans h2.symm

def rframesRelPath : List FrameCtx → List Bool
  | [] => []
  | _ :: fs => rframesRelPath fs ++ [true, false, true]

theorem pushRChain_crumbsPath (rframes : List FrameCtx) (base : List Crumb) :
    crumbsPath (pushRChain rframes base) = crumbsPath base ++ rframesRelPath rframes := by
  induction rframes with
  | nil => simp [pushRChain, rframesRelPath]
  | cons f fs ih =>
      simp [pushRChain, downRCrumbs_path, rframesRelPath, ih, List.append_assoc]

theorem hubTapeCursor_crumbsPath (rootLeft : Term) (hubCtx : FrameCtx) (rframes : List FrameCtx) (u : Term) :
    crumbsPath (hubTapeCursor rootLeft hubCtx rframes u).crumbs = rootTapePath ++ rframesRelPath rframes := by
  dsimp only [hubTapeCursor]
  have hsplit : pushRChain (rframes ++ [hubCtx]) [.right rootLeft] =
      pushRChain rframes (pushRChain [hubCtx] [.right rootLeft]) := by
    induction rframes with
    | nil => rfl
    | cons _ _ ih => simp [pushRChain, ih]
  rw [hsplit, pushRChain_crumbsPath]
  simp [pushRChain, downRCrumbs_path, crumbsPath, rootTapePath]

theorem termAt_wrapRChain :
    ∀ (rframes : List FrameCtx) (u : Term),
      (∀ f ∈ rframes, CanonicalFrameCtx f) →
      termAt (wrapRChain rframes u) (rframesRelPath rframes) = some u := by
  intro rframes
  induction rframes with
  | nil => intro u _; exact term_at_nil u
  | cons f fs ih =>
      intro u hall
      obtain ⟨hs1, hs2, _, _, _⟩ := hall f (by simp)
      have hfs : ∀ x ∈ fs, CanonicalFrameCtx x := fun x hx => hall x (by simp [hx])
      simp only [wrapRChain, rframesRelPath, hs1, hs2]
      rw [term_at_append, ih ((.s ⋅ f.other) ⋅ ((.s ⋅ u) ⋅ f.j)) hfs]
      simp [termAt]

theorem wrapRChain_strict :
    ∀ (rframes : List FrameCtx) (u : Term),
      (∀ f ∈ rframes, CanonicalFrameCtx f) →
      isPureS (wrapRChain rframes u) = true →
      logicalTreeStrict u = true →
      logicalTreeStrict (wrapRChain rframes u) = true := by
  intro rframes
  induction rframes with
  | nil => intro _ _ _ hu; exact hu
  | cons f fs ih =>
      intro u hall hpWrap hu
      obtain ⟨hs1, hs2, hjObs, _, hsOther⟩ := hall f (by simp)
      have hfs : ∀ x ∈ fs, CanonicalFrameCtx x := fun x hx => hall x (by simp [hx])
      simp only [wrapRChain, hs1, hs2] at hpWrap ⊢
      have hpCur : isPureS ((.s ⋅ f.other) ⋅ ((.s ⋅ u) ⋅ f.j)) = true := by
        have hEq : rebuild ⟨(.s ⋅ f.other) ⋅ ((.s ⋅ u) ⋅ f.j), pushRChain fs []⟩ =
            wrapRChain fs ((.s ⋅ f.other) ⋅ ((.s ⋅ u) ⋅ f.j)) :=
          rebuild_pushRChain fs [] _
        exact isPureS_focus_of_rebuild (cur := ⟨_, pushRChain fs []⟩) (by rw [hEq]; exact hpWrap)
      simp only [isPureS, Bool.and_eq_true] at hpCur
      have hpJ : isPureS f.j = true := hpCur.2.2
      have hjNs2 : isS2Term f.j = false := by
        match hg : f.j with
        | .app (.app a _) _ =>
            rw [hg] at hpJ hjObs
            simp only [isPureS, Bool.and_eq_true] at hpJ
            cases a with
            | s => simp [s2Obs, nodeKindOf] at hjObs
            | var _ => simp [isPureS] at hpJ
            | app _ _ => rfl
        | .s => rfl
        | .var _ => rfl
        | .app .s _ => rfl
        | .app (.var _) _ => rfl
      have hframeStrict : logicalTreeStrict ((.s ⋅ f.other) ⋅ ((.s ⋅ u) ⋅ f.j)) = true := by
        change logicalTreeStrict (frameTerm f.other u f.j) = true
        rw [logicalTreeStrict_frame]
        simp [hjNs2, hsOther, hu]
      exact ih ((.s ⋅ f.other) ⋅ ((.s ⋅ u) ⋅ f.j)) hfs hpWrap hframeStrict

theorem seekConcreteCell_wrapRChain (pred : Cell → Bool) :
    ∀ (rframes : List FrameCtx) (u : Term),
      (∀ f ∈ rframes, CanonicalFrameCtx f ∧ pred (cellFromVersion f.other) = false) →
      seekConcreteCell pred (wrapRChain rframes u) =
        (seekConcreteCell pred u).map (fun p => rframesRelPath rframes ++ p) := by
  intro rframes
  induction rframes with
  | nil =>
      intro u _
      dsimp only [wrapRChain, rframesRelPath]
      cases seekConcreteCell pred u <;> simp
  | cons f fs ih =>
      intro u hall
      obtain ⟨⟨hs1, hs2, _, _, _⟩, hpredFalse⟩ := hall f (by simp)
      have hfs : ∀ x ∈ fs, CanonicalFrameCtx x ∧ pred (cellFromVersion x.other) = false :=
        fun x hx => hall x (by simp [hx])
      simp only [wrapRChain, hs1, hs2]
      rw [ih ((.s ⋅ f.other) ⋅ ((.s ⋅ u) ⋅ f.j)) hfs]
      change ((if pred (cellFromVersion f.other) then some []
               else (seekConcreteCell pred u).map (fun p => [true, false, true] ++ p))).map
              (fun p => rframesRelPath fs ++ p) = _
      rw [hpredFalse]
      simp only [Bool.false_eq_true, ↓reduceIte, rframesRelPath]
      cases seekConcreteCell pred u <;> simp [List.append_assoc]

theorem parentCellPath_snoc (p : List Bool) :
    parentCellPath (p ++ [true, false, true]) = p := by
  simp [parentCellPath]

theorem seekActive_agrees (flag : Term) (hj0 : s2Obs (depthJunk 0) = false) :
    let rootLeft := numeral 1 ⋅ S
    let hubCtx : FrameCtx := ⟨.s, flag, .s, depthJunk 0⟩
    ∀ (fuel : Nat) (curTape : Term) (rframes : List FrameCtx) {relPath path : List Bool} {out : Term},
      leaves curTape ≤ fuel →
      (∀ f ∈ rframes, CanonicalFrameCtx f) →
      isPureS (rebuild (hubTapeCursor rootLeft hubCtx rframes curTape)) = true →
      logicalTreeStrict curTape = true →
      seekConcreteCell activeCell curTape = some relPath →
      chooseActive fixedBinaryProgram
        (rebuild (hubTapeCursor rootLeft hubCtx rframes curTape))
        (wrapRChain rframes curTape)
        (rframesRelPath rframes ++ relPath) = some path →
      DirectedStep path (rebuild (hubTapeCursor rootLeft hubCtx rframes curTape)) out →
      FinishesWith (.sf (.sf0 (.seekCell true)))
        (hubTapeCursor rootLeft hubCtx rframes curTape) (.contracted out) := by
  intro rootLeft hubCtx fuel
  have hhub : ValidFrameCtx hubCtx := ⟨rfl, rfl, hj0⟩
  induction fuel with
  | zero =>
      intro curTape _ _ _ _ hle _ _ _ _ _ _
      have hp := leaves_pos curTape
      exact False.elim (by omega)
  | succ m ih =>
      intro curTape rframes relPath path out hle hall hpRoot hsTape hseek hchoose hdir
      have hallValid : ∀ f ∈ rframes, ValidFrameCtx f := fun f hf => canonicalFrameCtx_valid (hall f hf)
      have hpTape : isPureS curTape = true :=
        isPureS_focus_of_rebuild (cur := hubTapeCursor rootLeft hubCtx rframes curTape) hpRoot
      cases hfv : flagValue curTape with
      | false =>
          rw [seek_concrete_closed activeCell curTape (parseFrame_none_of_flagValue_false hfv)] at hseek
          cases hseek
      | true =>
          obtain ⟨v0, nextTape, cj, rfl, hobs, hpV0, _, _, hsV0, hsNext, hcjObs, hfCurValid, _⟩ :=
            strictFrame_pureS_decomp hpTape hsTape hfv
          have sSf := checkStrictFrame_steps (.seekCell true)
            (hubTapeCursor rootLeft hubCtx rframes (frameTerm v0 nextTape cj))
          dsimp only [hubTapeCursor] at sSf
          rw [hobs] at sSf
          let csCur := pushRChain (rframes ++ [hubCtx]) [.right rootLeft]
          have hParent : ∃ pf pfs, rframes ++ [hubCtx] = pf :: pfs ∧ ValidFrameCtx pf := by
            cases rframes with
            | nil => exact ⟨hubCtx, [], rfl, hhub⟩
            | cons f0 fs0 => exact ⟨f0, fs0 ++ [hubCtx], rfl, hallValid f0 (by simp)⟩
          obtain ⟨pf, pfs, hpfEq, hpfValid⟩ := hParent
          have hcsCurEq : csCur = downRCrumbs pf.s1 pf.other pf.s2 pf.j (pushRChain pfs [.right rootLeft]) := by
            dsimp only [csCur]; rw [hpfEq]; rfl
          have sDownL := downL_steps (.toRcStart .seekActive) .s v0 .s nextTape cj csCur
            (.sf (.sfDone (.seekCell true) true)) rfl
          have sRead := readCell_steps .seekActive pf.s1 pf.other pf.s2 pf.j
            (pushRChain pfs [.right rootLeft]) hpfValid.2.2
            .s v0 .s nextTape cj ⟨rfl, rfl, hcjObs⟩
          rw [← hcsCurEq] at sRead
          let cell := (obsScanBottomUp v0).getD defaultCell8
          have hcellEq : cell8ToCell cell = cellFromVersion v0 := obsScanBottomUp_agrees hpV0 hsV0
          have hstatusEq : cell.status = (cellFromVersion v0).status := congrArg Cell.status hcellEq
          have hbitEq : cell.bit = (cellFromVersion v0).bit := congrArg Cell.bit hcellEq
          have hstateEq : cell.state.val = (cellFromVersion v0).state := congrArg Cell.state hcellEq
          have sPre := StepsTo.trans sSf (StepsTo.trans sDownL sRead)
          rw [seek_concrete_frame] at hseek
          if hact : cell.status == .active then
            have hactCell : activeCell (cellFromVersion v0) = true := by
              unfold activeCell; rw [← hstatusEq]; exact hact
            simp only [hactCell, ↓reduceIte, Option.some.injEq] at hseek
            subst relPath
            rw [List.append_nil] at hchoose
            let tape := wrapRChain rframes (frameTerm v0 nextTape cj)
            have hreadCell : readCellAt tape (rframesRelPath rframes) = some (cellFromVersion v0) := by
              unfold readCellAt
              rw [termAt_wrapRChain rframes (frameTerm v0 nextTape cj) hall]
              simp [parse_frame]
            unfold chooseActive at hchoose
            rw [hreadCell] at hchoose
            dsimp only [Bind.bind, Option.bind] at hchoose
            if hst : cell.state.val < 132 then
              have hstV : (cellFromVersion v0).state < 132 := hstateEq ▸ hst
              rw [dif_pos hstV] at hchoose
              have hqEq : (⟨(cellFromVersion v0).state, hstV⟩ : Fin 132) = ⟨cell.state.val, hst⟩ := by
                apply Fin.ext; exact hstateEq.symm
              rw [hqEq, ← hbitEq] at hchoose
              cases hprog : fixedBinaryProgram ⟨cell.state.val, hst⟩ cell.bit with
              | none =>
                  rw [hprog] at hchoose
                  dsimp only [activePlan] at hchoose
                  have hmRew : startRClimbProp .rewindToHubHalt (rframes ++ [hubCtx]) (frameTerm v0 nextTape cj)
                      [.right rootLeft] (.downRDone (.toRcDone .seekActive cell)) := by
                    cases rframes <;> (
                      dsimp only [startRClimbProp, List.nil_append, List.cons_append, microstep, step, onDownRDone, onCellRead]
                      rw [if_pos hact, dif_pos hst, hprog]
                      rfl)
                  have sRew := rewindToHubHalt_steps rootLeft hubCtx hhub rframes (frameTerm v0 nextTape cj)
                    (.downRDone (.toRcDone .seekActive cell)) hallValid hmRew
                  rw [wrapRChain_hub_split hubCtx rframes (frameTerm v0 nextTape cj)] at sRew
                  have sDownFlag := downL_steps .toHaltFlagOpen .s flag .s tape (depthJunk 0)
                    [.right rootLeft] (.hubChkDone .rewindHaltChk true) rfl
                  let curFlag : Cursor := ⟨flag, downLCrumbs .s tape .s (depthJunk 0) [.right rootLeft]⟩
                  have sOpAlias : StepsTo 0 (.downLDone .toHaltFlagOpen) curFlag (.openSub .pf0) curFlag :=
                    StepsTo.of_alias rfl
                  have sTot := StepsTo.trans sPre (StepsTo.trans sRew (StepsTo.trans sDownFlag sOpAlias))
                  have hpathFlag : crumbsPath curFlag.crumbs = hubFlagPath := by
                    simp [curFlag, downLCrumbs_path, crumbsPath, hubFlagPath]
                  have hfin := openSub_of_selectOpeningAt curFlag (sTot.1 ▸ hpRoot)
                    (by rw [hpathFlag, ← sTot.1]; exact hchoose) (sTot.1 ▸ hdir)
                  exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
              | some inst =>
                  rw [hprog] at hchoose
                  dsimp only [activePlan] at hchoose
                  cases hdirInst : inst.direction with
                  | stay =>
                      rw [hdirInst] at hchoose
                      dsimp only [chooseCellWrite] at hchoose
                      let recCell : Cell := ⟨inst.write, .active, inst.next.val⟩
                      let des := encodeRecord11 recCell
                      have hmApp : microstep (.downRDone (.toRcDone .seekActive cell)) ⟨frameTerm v0 nextTape cj, csCur⟩ =
                          .running (.downL1 (.toAppendVerEntry des)) ⟨.s ⋅ v0, .left ((.s ⋅ nextTape) ⋅ cj) :: csCur⟩ := by
                        dsimp only [microstep, step, onDownRDone, onCellRead]
                        rw [if_pos hact, dif_pos hst, hprog]
                        dsimp only []
                        rw [hdirInst]
                        rfl
                      have sDownApp := downL_steps (.toAppendVerEntry des) .s v0 .s nextTape cj csCur _ hmApp
                      have sTot := StepsTo.trans sPre sDownApp
                      let curV0 : Cursor := ⟨v0, downLCrumbs .s nextTape .s cj csCur⟩
                      have hpathV0 : crumbsPath curV0.crumbs =
                          rootTapePath ++ rframesRelPath rframes ++ cellVersionPath := by
                        dsimp only [curV0]
                        rw [downLCrumbs_path]
                        have hc := hubTapeCursor_crumbsPath rootLeft hubCtx rframes (frameTerm v0 nextTape cj)
                        dsimp only [hubTapeCursor] at hc
                        rw [hc]
                        simp [cellVersionPath, List.append_assoc]
                      have hfin := appendEntry_agrees recCell curV0 (sTot.1 ▸ hpRoot) hsV0
                        (by rw [hpathV0, ← sTot.1]; exact hchoose) (sTot.1 ▸ hdir)
                      exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
                  | right =>
                      rw [hdirInst] at hchoose
                      dsimp only [chooseCellWrite] at hchoose
                      let recCell : Cell := ⟨inst.write, .movingRight, inst.next.val⟩
                      let des := encodeRecord11 recCell
                      have hmApp : microstep (.downRDone (.toRcDone .seekActive cell)) ⟨frameTerm v0 nextTape cj, csCur⟩ =
                          .running (.downL1 (.toAppendVerEntry des)) ⟨.s ⋅ v0, .left ((.s ⋅ nextTape) ⋅ cj) :: csCur⟩ := by
                        dsimp only [microstep, step, onDownRDone, onCellRead]
                        rw [if_pos hact, dif_pos hst, hprog]
                        dsimp only []
                        rw [hdirInst]
                        rfl
                      have sDownApp := downL_steps (.toAppendVerEntry des) .s v0 .s nextTape cj csCur _ hmApp
                      have sTot := StepsTo.trans sPre sDownApp
                      let curV0 : Cursor := ⟨v0, downLCrumbs .s nextTape .s cj csCur⟩
                      have hpathV0 : crumbsPath curV0.crumbs =
                          rootTapePath ++ rframesRelPath rframes ++ cellVersionPath := by
                        dsimp only [curV0]
                        rw [downLCrumbs_path]
                        have hc := hubTapeCursor_crumbsPath rootLeft hubCtx rframes (frameTerm v0 nextTape cj)
                        dsimp only [hubTapeCursor] at hc
                        rw [hc]
                        simp [cellVersionPath, List.append_assoc]
                      have hfin := appendEntry_agrees recCell curV0 (sTot.1 ▸ hpRoot) hsV0
                        (by rw [hpathV0, ← sTot.1]; exact hchoose) (sTot.1 ▸ hdir)
                      exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
                  | left =>
                      rw [hdirInst] at hchoose
                      have hmUp : microstep (.downRDone (.toRcDone .seekActive cell))
                          ⟨frameTerm v0 nextTape cj, downRCrumbs pf.s1 pf.other pf.s2 pf.j (pushRChain pfs [.right rootLeft])⟩ =
                          .running (.up1 (.activeBoundaryTest cell))
                            ⟨pf.s2 ⋅ frameTerm v0 nextTape cj, .left pf.j :: .right (pf.s1 ⋅ pf.other) :: pushRChain pfs [.right rootLeft]⟩ := by
                        dsimp only [microstep, step, onDownRDone, onCellRead]
                        rw [if_pos hact, dif_pos hst, hprog]
                        dsimp only []
                        rw [hdirInst]
                        rfl
                      have sUpP := up_from_right_steps (.activeBoundaryTest cell) pf.s1 pf.other pf.s2
                        (frameTerm v0 nextTape cj) pf.j (pushRChain pfs [.right rootLeft]) hpfValid.2.2 _ hmUp
                      rw [← hcsCurEq] at sUpP
                      let pTerm := (pf.s1 ⋅ pf.other) ⋅ ((pf.s2 ⋅ frameTerm v0 nextTape cj) ⋅ pf.j)
                      let isH := (rframesRelPath rframes).isEmpty
                      have sChkH : StepsTo 2 (.upDone (.activeBoundaryTest cell) true)
                          ⟨pTerm, pushRChain pfs [.right rootLeft]⟩
                          (.hubChkDone (.activeBoundaryChk cell) isH)
                          ⟨pTerm, pushRChain pfs [.right rootLeft]⟩ := by
                        cases rframes with
                        | nil =>
                            simp only [List.nil_append, List.cons.injEq] at hpfEq
                            rcases hpfEq with ⟨rfl, rfl⟩
                            exact hubChk_at_hub_steps (.activeBoundaryChk cell) rootLeft pTerm _ rfl
                        | cons f0 fs0 =>
                            simp only [List.cons_append, List.cons.injEq] at hpfEq
                            rcases hpfEq with ⟨rfl, rfl⟩
                            have hisH : isH = false := by
                              dsimp only [isH, rframesRelPath]
                              cases rframesRelPath fs0 <;> rfl
                            rw [hisH]
                            cases fs0 with
                            | nil =>
                                exact hubChk_below_hub_steps (.activeBoundaryChk cell) hubCtx.s2 pTerm hubCtx.j
                                  [.right (hubCtx.s1 ⋅ hubCtx.other), .right rootLeft] _ rfl
                            | cons f2 fs2 =>
                                exact hubChk_below_hub_steps (.activeBoundaryChk cell) f2.s2 pTerm f2.j
                                  (.right (f2.s1 ⋅ f2.other) :: pushRChain (fs2 ++ [hubCtx]) [.right rootLeft]) _ rfl
                      let st : Status := if isH then .active else .movingLeft
                      let recCell : Cell := ⟨inst.write, st, inst.next.val⟩
                      let des := encodeRecord11 recCell
                      have hmBack : microstep (.hubChkDone (.activeBoundaryChk cell) isH)
                          ⟨pTerm, pushRChain pfs [.right rootLeft]⟩ =
                          .running (.downR1 (.toActiveBoundaryBack des))
                            ⟨(pf.s2 ⋅ frameTerm v0 nextTape cj) ⋅ pf.j, .right (pf.s1 ⋅ pf.other) :: pushRChain pfs [.right rootLeft]⟩ := by
                        dsimp only [microstep, step, onHubChkDone]
                        rw [dif_pos hst, hprog]
                        rfl
                      have sBack := downR_steps (.toActiveBoundaryBack des) pf.s1 pf.other pf.s2
                        (frameTerm v0 nextTape cj) pf.j (pushRChain pfs [.right rootLeft]) _ hmBack
                      rw [← hcsCurEq] at sBack
                      have sDownApp := downL_steps (.toAppendVerEntry des) .s v0 .s nextTape cj csCur
                        (.downRDone (.toActiveBoundaryBack des)) rfl
                      have sTot := StepsTo.trans sPre (StepsTo.trans sUpP (StepsTo.trans sChkH (StepsTo.trans sBack sDownApp)))
                      let curV0 : Cursor := ⟨v0, downLCrumbs .s nextTape .s cj csCur⟩
                      have hchooseVer : selectVersionAt (rebuild (hubTapeCursor rootLeft hubCtx rframes (frameTerm v0 nextTape cj)))
                          (rootTapePath ++ rframesRelPath rframes ++ cellVersionPath) recCell = some path := by
                        cases hisH : isH with
                        | true =>
                            change (match if isH then ControllerPlan.append (rframesRelPath rframes) ⟨inst.write, .active, inst.next.val⟩
                                          else ControllerPlan.append (rframesRelPath rframes) ⟨inst.write, .movingLeft, inst.next.val⟩ with
                                    | .halt => _ | .append p r => chooseCellWrite _ p r | _ => none) = some path at hchoose
                            rw [hisH] at hchoose
                            simpa [recCell, st, hisH, chooseCellWrite] using hchoose
                        | false =>
                            change (match if isH then ControllerPlan.append (rframesRelPath rframes) ⟨inst.write, .active, inst.next.val⟩
                                          else ControllerPlan.append (rframesRelPath rframes) ⟨inst.write, .movingLeft, inst.next.val⟩ with
                                    | .halt => _ | .append p r => chooseCellWrite _ p r | _ => none) = some path at hchoose
                            rw [hisH] at hchoose
                            simpa [recCell, st, hisH, chooseCellWrite] using hchoose
                      have hpathV0 : crumbsPath curV0.crumbs =
                          rootTapePath ++ rframesRelPath rframes ++ cellVersionPath := by
                        dsimp only [curV0]
                        rw [downLCrumbs_path]
                        have hc := hubTapeCursor_crumbsPath rootLeft hubCtx rframes (frameTerm v0 nextTape cj)
                        dsimp only [hubTapeCursor] at hc
                        rw [hc]
                        simp [cellVersionPath, List.append_assoc]
                      have hfin := appendEntry_agrees recCell curV0 (sTot.1 ▸ hpRoot) hsV0
                        (by rw [hpathV0, ← sTot.1]; exact hchooseVer) (sTot.1 ▸ hdir)
                      exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
            else
              have hstNot : ¬ (cellFromVersion v0).state < 132 := hstateEq ▸ hst
              rw [dif_neg hstNot] at hchoose
              cases hchoose
          else
            have hactFalse : activeCell (cellFromVersion v0) = false := by
              unfold activeCell; rw [← hstatusEq]; exact Bool.eq_false_iff.mpr hact
            simp only [hactFalse, Bool.false_eq_true, ↓reduceIte] at hseek
            cases hsNextSeek : seekConcreteCell activeCell nextTape with
            | none => simp [hsNextSeek] at hseek
            | some relNext =>
                simp only [hsNextSeek, Option.map, Option.some.injEq] at hseek
                subst relPath
                let fCur : FrameCtx := ⟨.s, v0, .s, cj⟩
                have hfCurCan : CanonicalFrameCtx fCur := ⟨rfl, rfl, hcjObs, hpV0, hsV0⟩
                have hmNext : microstep (.downRDone (.toRcDone .seekActive cell)) ⟨frameTerm v0 nextTape cj, csCur⟩ =
                    .running (.downR1 (.toNextCell true)) ⟨(.s ⋅ nextTape) ⋅ cj, .right (.s ⋅ v0) :: csCur⟩ := by
                  simp [microstep, step, onDownRDone, onCellRead, hact, startDownR, applyAction, frameTerm, S]
                have sDownNext := downR_steps (.toNextCell true) .s v0 .s nextTape cj csCur _ hmNext
                have sAlias : StepsTo 0 (.downRDone (.toNextCell true))
                    (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape)
                    (.sf (.sf0 (.seekCell true)))
                    (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape) :=
                  StepsTo.of_alias rfl
                have sTot := StepsTo.trans sPre (StepsTo.trans sDownNext sAlias)
                have hall' : ∀ x ∈ fCur :: rframes, CanonicalFrameCtx x := by
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx'
                  · exact hfCurCan
                  · exact hall x hx'
                have hnLe : leaves nextTape ≤ m := by
                  rw [frame_leaves] at hle
                  have := leaves_pos v0
                  have := leaves_pos cj
                  omega
                have hpathAssoc : rframesRelPath (fCur :: rframes) ++ relNext =
                    rframesRelPath rframes ++ ([true, false, true] ++ relNext) := by
                  simp [rframesRelPath, List.append_assoc]
                have hfin := ih nextTape (fCur :: rframes) hnLe hall' (sTot.1 ▸ hpRoot) hsNext hsNextSeek
                  (by rw [hpathAssoc, ← sTot.1]; exact hchoose) (sTot.1 ▸ hdir)
                exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin

theorem seekPending_agrees (flag : Term) (hflagFalse : flagValue flag = false)
    (hj0 : s2Obs (depthJunk 0) = false) :
    let rootLeft := numeral 1 ⋅ S
    let hubCtx : FrameCtx := ⟨.s, flag, .s, depthJunk 0⟩
    ∀ (fuel : Nat) (curTape : Term) (rframes : List FrameCtx) {path : List Bool} {out : Term},
      leaves curTape ≤ fuel →
      (∀ f ∈ rframes, CanonicalFrameCtx f ∧ movingCell (cellFromVersion f.other) = false) →
      isPureS (seedHubRoot flag (wrapRChain rframes curTape) (depthJunk 0)) = true →
      logicalTreeStrict curTape = true →
      fullRootSelector fixedBinaryProgram
        (seedHubRoot flag (wrapRChain rframes curTape) (depthJunk 0)) = some path →
      DirectedStep path (seedHubRoot flag (wrapRChain rframes curTape) (depthJunk 0)) out →
      FinishesWith (.sf (.sf0 (.seekCell false)))
        (hubTapeCursor rootLeft hubCtx rframes curTape) (.contracted out) := by
  intro rootLeft hubCtx fuel
  have hhub : ValidFrameCtx hubCtx := ⟨rfl, rfl, hj0⟩
  have hrebHub : ∀ (rf : List FrameCtx) (u : Term),
      rebuild (hubTapeCursor rootLeft hubCtx rf u) =
        seedHubRoot flag (wrapRChain rf u) (depthJunk 0) := by
    intro rf u
    rw [rebuild_pushRChain (rf ++ [hubCtx]) [.right rootLeft] u, wrapRChain_hub_split hubCtx rf u]
    rfl
  induction fuel with
  | zero =>
      intro curTape _ _ _ hle _ _ _ _ _
      have hp := leaves_pos curTape
      exact False.elim (by omega)
  | succ m ih =>
      intro curTape rframes path out hle hall hpSeed hsTape hsel hdir
      have hallCan : ∀ f ∈ rframes, CanonicalFrameCtx f := fun f hf => (hall f hf).1
      have hallValid : ∀ f ∈ rframes, ValidFrameCtx f := fun f hf => canonicalFrameCtx_valid (hallCan f hf)
      have hpRoot : isPureS (rebuild (hubTapeCursor rootLeft hubCtx rframes curTape)) = true := by
        rw [hrebHub]; exact hpSeed
      have hpTape : isPureS curTape = true := isPureS_focus_of_rebuild hpRoot
      have sSf := checkStrictFrame_steps (.seekCell false) (hubTapeCursor rootLeft hubCtx rframes curTape)
      dsimp only [hubTapeCursor] at sSf
      cases hfv : flagValue curTape with
      | false =>
          have hobs : strictFrameObs curTape = false := (strictFrameObs_eq_flagValue_of_strict hpTape hsTape).trans hfv
          rw [hobs] at sSf
          have hmNone : seekConcreteCell movingCell (wrapRChain rframes curTape) = none := by
            rw [seekConcreteCell_wrapRChain movingCell rframes curTape hall,
              seek_concrete_closed movingCell curTape (parseFrame_none_of_flagValue_false hfv)]
            rfl
          let tapeFull := wrapRChain rframes curTape
          have hpTapeFull : isPureS tapeFull = true := by
            have hpSeed' := hpSeed
            simp only [seedHubRoot, frameTerm, S, isPureS, Bool.and_eq_true] at hpSeed'
            exact hpSeed'.2.2.1.2
          have hsTapeFull : logicalTreeStrict tapeFull = true :=
            wrapRChain_strict rframes curTape hallCan hpTapeFull hsTape
          have hselAct : ∃ actPath,
              seekConcreteCell activeCell tapeFull = some actPath ∧
              chooseActive fixedBinaryProgram (seedHubRoot flag tapeFull (depthJunk 0)) tapeFull actPath = some path := by
            cases hseekAct : seekConcreteCell activeCell tapeFull with
            | none =>
                have hprio : priorityConcretePath (wrapRChain rframes curTape) = .none := by
                  unfold priorityConcretePath
                  dsimp only [tapeFull] at hseekAct
                  rw [hmNone, hseekAct]
                simp [fullRootSelector, termAt, rootHubPath, seedHubRoot, parse_frame, hflagFalse, hprio] at hsel
            | some actPath =>
                have hprio : priorityConcretePath tapeFull = .active actPath := by
                  unfold priorityConcretePath
                  dsimp only [tapeFull]
                  rw [hmNone]
                  exact by rw [hseekAct]
                rw [full_selector_active_branch fixedBinaryProgram flag tapeFull (depthJunk 0) actPath hflagFalse hprio] at hsel
                exact ⟨actPath, rfl, hsel⟩
          obtain ⟨actPath, hseekAct, hchooseAct⟩ := hselAct
          have hmRew : startRClimbProp .rewindToTape (rframes ++ [hubCtx]) curTape [.right rootLeft]
              (.sf (.sfDone (.seekCell false) false)) := by
            dsimp only [startRClimbProp]
            cases rframes <;> rfl
          have sRew := rewindToTape_steps rootLeft hubCtx hhub rframes curTape
            (.sf (.sfDone (.seekCell false) false)) hallValid hmRew
          rw [wrapRChain_hub_split hubCtx rframes curTape] at sRew
          have sDownTape := downR_steps .toTapePass2 .s flag .s tapeFull (depthJunk 0)
            [.right rootLeft] (.hubChkDone .rewindTapeChk true) rfl
          have sAlias : StepsTo 0 (.downRDone .toTapePass2)
              (hubTapeCursor rootLeft hubCtx [] tapeFull)
              (.sf (.sf0 (.seekCell true)))
              (hubTapeCursor rootLeft hubCtx [] tapeFull) :=
            StepsTo.of_alias rfl
          have sTot := StepsTo.trans sSf (StepsTo.trans sRew (StepsTo.trans sDownTape sAlias))
          have hrebEmpty : rebuild (hubTapeCursor rootLeft hubCtx [] tapeFull) =
              seedHubRoot flag tapeFull (depthJunk 0) := hrebHub [] tapeFull
          have hfin := seekActive_agrees flag hj0 (leaves tapeFull) tapeFull [] (Nat.le_refl _)
            (fun _ h => nomatch h) (by rw [hrebEmpty]; exact hpSeed) hsTapeFull hseekAct
            (by rw [hrebEmpty]; simpa [wrapRChain, rframesRelPath] using hchooseAct)
            (by rw [hrebEmpty]; exact hdir)
          exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
      | true =>
          obtain ⟨v0, nextTape, cj, rfl, hobs, hpV0, _, _, hsV0, hsNext, hcjObs, _, _⟩ :=
            strictFrame_pureS_decomp hpTape hsTape hfv
          rw [hobs] at sSf
          let cellTerm := frameTerm v0 nextTape cj
          let csCur := pushRChain (rframes ++ [hubCtx]) [.right rootLeft]
          have hParent : ∃ pf pfs, rframes ++ [hubCtx] = pf :: pfs ∧ ValidFrameCtx pf := by
            cases rframes with
            | nil => exact ⟨hubCtx, [], rfl, hhub⟩
            | cons f0 fs0 => exact ⟨f0, fs0 ++ [hubCtx], rfl, hallValid f0 (by simp)⟩
          obtain ⟨pf, pfs, hpfEq, hpfValid⟩ := hParent
          have hcsCurEq : csCur = downRCrumbs pf.s1 pf.other pf.s2 pf.j (pushRChain pfs [.right rootLeft]) := by
            dsimp only [csCur]; rw [hpfEq]; rfl
          have sDownL := downL_steps (.toRcStart .seekPending) .s v0 .s nextTape cj csCur
            (.sf (.sfDone (.seekCell false) true)) rfl
          have sRead := readCell_steps .seekPending pf.s1 pf.other pf.s2 pf.j
            (pushRChain pfs [.right rootLeft]) hpfValid.2.2
            .s v0 .s nextTape cj ⟨rfl, rfl, hcjObs⟩
          rw [← hcsCurEq] at sRead
          let cell := (obsScanBottomUp v0).getD defaultCell8
          have hcellEq : cell8ToCell cell = cellFromVersion v0 := obsScanBottomUp_agrees hpV0 hsV0
          have hstatusEq : cell.status = (cellFromVersion v0).status := congrArg Cell.status hcellEq
          have hbitEq : cell.bit = (cellFromVersion v0).bit := congrArg Cell.bit hcellEq
          have hstateEq : cell.state.val = (cellFromVersion v0).state := congrArg Cell.state hcellEq
          have sPre := StepsTo.trans sSf (StepsTo.trans sDownL sRead)
          have hnLe : leaves nextTape ≤ m := by
            rw [frame_leaves] at hle
            have := leaves_pos v0
            have := leaves_pos cj
            omega
          cases hstatus : cell.status with
          | off =>
              let fCur : FrameCtx := ⟨.s, v0, .s, cj⟩
              have hfMoveFalse : movingCell (cellFromVersion v0) = false := by
                unfold movingCell isMoving
                rw [← hstatusEq, hstatus]
              have hall' : ∀ x ∈ fCur :: rframes, CanonicalFrameCtx x ∧ movingCell (cellFromVersion x.other) = false := by
                intro x hx
                rcases List.mem_cons.mp hx with rfl | hx'
                · exact ⟨⟨rfl, rfl, hcjObs, hpV0, hsV0⟩, hfMoveFalse⟩
                · exact hall x hx'
              have hmNext : microstep (.downRDone (.toRcDone .seekPending cell)) ⟨cellTerm, csCur⟩ =
                  .running (.downR1 (.toNextCell false)) ⟨(.s ⋅ nextTape) ⋅ cj, .right (.s ⋅ v0) :: csCur⟩ := by
                simp [microstep, step, onDownRDone, onCellRead, hstatus, startDownR, applyAction, cellTerm, frameTerm, S]
              have sDownNext := downR_steps (.toNextCell false) .s v0 .s nextTape cj csCur _ hmNext
              have sAlias : StepsTo 0 (.downRDone (.toNextCell false))
                  (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape)
                  (.sf (.sf0 (.seekCell false)))
                  (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape) :=
                StepsTo.of_alias rfl
              have sTot := StepsTo.trans sPre (StepsTo.trans sDownNext sAlias)
              have hfin := ih nextTape (fCur :: rframes) hnLe hall' hpSeed hsNext hsel hdir
              exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
          | active =>
              let fCur : FrameCtx := ⟨.s, v0, .s, cj⟩
              have hfMoveFalse : movingCell (cellFromVersion v0) = false := by
                unfold movingCell isMoving
                rw [← hstatusEq, hstatus]
              have hall' : ∀ x ∈ fCur :: rframes, CanonicalFrameCtx x ∧ movingCell (cellFromVersion x.other) = false := by
                intro x hx
                rcases List.mem_cons.mp hx with rfl | hx'
                · exact ⟨⟨rfl, rfl, hcjObs, hpV0, hsV0⟩, hfMoveFalse⟩
                · exact hall x hx'
              have hmNext : microstep (.downRDone (.toRcDone .seekPending cell)) ⟨cellTerm, csCur⟩ =
                  .running (.downR1 (.toNextCell false)) ⟨(.s ⋅ nextTape) ⋅ cj, .right (.s ⋅ v0) :: csCur⟩ := by
                simp [microstep, step, onDownRDone, onCellRead, hstatus, startDownR, applyAction, cellTerm, frameTerm, S]
              have sDownNext := downR_steps (.toNextCell false) .s v0 .s nextTape cj csCur _ hmNext
              have sAlias : StepsTo 0 (.downRDone (.toNextCell false))
                  (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape)
                  (.sf (.sf0 (.seekCell false)))
                  (hubTapeCursor rootLeft hubCtx (fCur :: rframes) nextTape) :=
                StepsTo.of_alias rfl
              have sTot := StepsTo.trans sPre (StepsTo.trans sDownNext sAlias)
              have hfin := ih nextTape (fCur :: rframes) hnLe hall' hpSeed hsNext hsel hdir
              exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
          | movingRight =>
              let tape := wrapRChain rframes cellTerm
              let srcPath := rframesRelPath rframes
              have hmoveTrue : movingCell (cellFromVersion v0) = true := by
                unfold movingCell isMoving; rw [← hstatusEq, hstatus]
              have hprio : priorityConcretePath tape = .pending srcPath := by
                unfold priorityConcretePath
                rw [seekConcreteCell_wrapRChain movingCell rframes cellTerm hall]
                simp [cellTerm, seek_concrete_frame, hmoveTrue, srcPath]
              rw [full_selector_pending_branch fixedBinaryProgram flag tape (depthJunk 0) srcPath hflagFalse hprio] at hsel
              have hreadSrc : readCellAt tape srcPath = some (cellFromVersion v0) := by
                unfold readCellAt
                rw [termAt_wrapRChain rframes cellTerm hallCan]
                simp [cellTerm, parse_frame]
              have hpendStatus : (cellFromVersion v0).status = .movingRight := hstatusEq.symm.trans hstatus
              have hdestPath : pendingDestinationPath (cellFromVersion v0) srcPath = some (srcPath ++ nextCellPath) := by
                simp [pendingDestinationPath, hpendStatus]
              have htermDest : termAt tape (srcPath ++ nextCellPath) = some nextTape := by
                rw [term_at_append, termAt_wrapRChain rframes cellTerm hallCan]
                simp [cellTerm, nextCellPath, termAt, frameTerm]
              unfold choosePending at hsel
              rw [hreadSrc] at hsel
              dsimp only [Bind.bind, Option.bind] at hsel
              rw [hdestPath] at hsel
              dsimp only [] at hsel
              rw [htermDest] at hsel
              dsimp only [] at hsel
              have hmDest : microstep (.downRDone (.toRcDone .seekPending cell)) ⟨cellTerm, csCur⟩ =
                  .running (.downR1 (.toPendingRightDest cell)) ⟨(.s ⋅ nextTape) ⋅ cj, .right (.s ⋅ v0) :: csCur⟩ := by
                simp [microstep, step, onDownRDone, onCellRead, hstatus, startDownR, applyAction, cellTerm, frameTerm, S]
              have sDownDest := downR_steps (.toPendingRightDest cell) .s v0 .s nextTape cj csCur _ hmDest
              let csDest := downRCrumbs .s v0 .s cj csCur
              have sAliasD : StepsTo 0 (.downRDone (.toPendingRightDest cell)) ⟨nextTape, csDest⟩
                  (.sf (.sf0 (.pendingRightDest cell))) ⟨nextTape, csDest⟩ :=
                StepsTo.of_alias rfl
              have sSfD := checkStrictFrame_steps (.pendingRightDest cell) ⟨nextTape, csDest⟩
              dsimp only [] at sSfD
              have hpNext : isPureS nextTape = true := by
                have hpT := hpTape
                simp only [frameTerm, S, isPureS, Bool.and_eq_true] at hpT
                exact hpT.2.1.2
              cases hfvD : flagValue nextTape with
              | false =>
                  have hobsD : strictFrameObs nextTape = false :=
                    (strictFrameObs_eq_flagValue_of_strict hpNext hsNext).trans hfvD
                  rw [hobsD] at sSfD
                  have hpfD : parseFrame nextTape = none := parseFrame_none_of_flagValue_false hfvD
                  rw [hpfD] at hsel
                  simp only [pendingPlan, isMoving, hpendStatus] at hsel
                  have sOp : StepsTo 0 (.sf (.sfDone (.pendingRightDest cell) false)) ⟨nextTape, csDest⟩
                      (.openSub .pf0) ⟨nextTape, csDest⟩ :=
                    StepsTo.of_alias rfl
                  have sTot := StepsTo.trans sPre (StepsTo.trans sDownDest (StepsTo.trans sAliasD (StepsTo.trans sSfD sOp)))
                  have hpathDest : crumbsPath csDest = rootTapePath ++ (srcPath ++ nextCellPath) := by
                    dsimp only [csDest]
                    rw [downRCrumbs_path]
                    have hc := hubTapeCursor_crumbsPath rootLeft hubCtx rframes cellTerm
                    dsimp only [hubTapeCursor] at hc
                    rw [hc]
                    simp [srcPath, nextCellPath, List.append_assoc]
                  have hrebDest : rebuild ⟨nextTape, csDest⟩ = seedHubRoot flag tape (depthJunk 0) :=
                    sTot.1.symm.trans (hrebHub rframes cellTerm)
                  have hfin := openSub_of_selectOpeningAt ⟨nextTape, csDest⟩ (by rw [hrebDest]; exact hpSeed)
                    (by rw [hrebDest, hpathDest]; exact hsel) (by rw [hrebDest]; exact hdir)
                  exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
              | true =>
                  obtain ⟨dv0, drest, dj, rfl, hobsD, hpDv0, _, _, hsDv0, _, hdjObs, _, _⟩ :=
                    strictFrame_pureS_decomp hpNext hsNext hfvD
                  rw [hobsD] at sSfD
                  rw [parse_frame] at hsel
                  dsimp only [] at hsel
                  let dTerm := frameTerm dv0 drest dj
                  have sDownD := downL_steps (.toRcStart (.readDestRight cell)) .s dv0 .s drest dj csDest
                    (.sf (.sfDone (.pendingRightDest cell) true)) rfl
                  have sReadD := readCell_steps (.readDestRight cell) .s v0 .s cj csCur hcjObs
                    .s dv0 .s drest dj ⟨rfl, rfl, hdjObs⟩
                  let dCell := (obsScanBottomUp dv0).getD defaultCell8
                  have hdCellEq : cell8ToCell dCell = cellFromVersion dv0 := obsScanBottomUp_agrees hpDv0 hsDv0
                  have hdStatusEq : dCell.status = (cellFromVersion dv0).status := congrArg Cell.status hdCellEq
                  have hdBitEq : dCell.bit = (cellFromVersion dv0).bit := congrArg Cell.bit hdCellEq
                  have hdStateEq : dCell.state.val = (cellFromVersion dv0).state := congrArg Cell.state hdCellEq
                  have sPreD := StepsTo.trans sPre
                    (StepsTo.trans sDownDest (StepsTo.trans sAliasD (StepsTo.trans sSfD (StepsTo.trans sDownD sReadD))))
                  have hbeqState : (dCell.state == cell.state) = ((cellFromVersion dv0).state == (cellFromVersion v0).state) := by
                    rw [fin256_beq_eq_val_beq, hdStateEq, hstateEq]
                  if hoff : dCell.status == .off then
                    have hoffV : ((cellFromVersion dv0).status == .off) = true := hdStatusEq ▸ hoff
                    let recCell : Cell := ⟨dCell.bit, .active, cell.state.val⟩
                    let des := encodeRecord11 recCell
                    have hmApp : microstep (.downRDone (.toRcDone (.readDestRight cell) dCell)) ⟨dTerm, csDest⟩ =
                        .running (.downL1 (.toAppendVerEntry des)) ⟨.s ⋅ dv0, .left ((.s ⋅ drest) ⋅ dj) :: csDest⟩ := by
                      simp [microstep, step, onDownRDone, onCellRead, hoff, startDownL, applyAction, des, recCell, dTerm, frameTerm, S]
                    have sApp := downL_steps (.toAppendVerEntry des) .s dv0 .s drest dj csDest _ hmApp
                    have sTot := StepsTo.trans sPreD sApp
                    let curDv0 : Cursor := ⟨dv0, downLCrumbs .s drest .s dj csDest⟩
                    have hrebDv0 : rebuild curDv0 = seedHubRoot flag tape (depthJunk 0) :=
                      sTot.1.symm.trans (hrebHub rframes cellTerm)
                    have hpathDv0 : crumbsPath curDv0.crumbs =
                        rootTapePath ++ (srcPath ++ nextCellPath) ++ cellVersionPath := by
                      dsimp only [curDv0, csDest]
                      rw [downLCrumbs_path, downRCrumbs_path]
                      have hc := hubTapeCursor_crumbsPath rootLeft hubCtx rframes cellTerm
                      dsimp only [hubTapeCursor] at hc
                      rw [hc]
                      simp [srcPath, nextCellPath, cellVersionPath, List.append_assoc]
                    have hchooseVer : selectVersionAt (seedHubRoot flag tape (depthJunk 0))
                        (rootTapePath ++ (srcPath ++ nextCellPath) ++ cellVersionPath) recCell = some path := by
                      simp only [pendingPlan, isMoving, hpendStatus, Bool.not_true, Bool.false_eq_true,
                        hoffV, ↓reduceIte, chooseCellWrite] at hsel
                      simpa [recCell, hdBitEq, hstateEq] using hsel
                    have hfin := appendEntry_agrees recCell curDv0 (by rw [hrebDv0]; exact hpSeed) hsDv0
                      (by rw [hrebDv0, hpathDv0]; exact hchooseVer) (by rw [hrebDv0]; exact hdir)
                    exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
                  else if hdone : dCell.status == .active && dCell.state == cell.state then
                    have hoffV : ((cellFromVersion dv0).status == .off) = false :=
                      hdStatusEq ▸ Bool.eq_false_iff.mpr hoff
                    have hdoneV : ((cellFromVersion dv0).status == .active &&
                        (cellFromVersion dv0).state == (cellFromVersion v0).state) = true := by
                      rw [← hdStatusEq, ← hbeqState]; exact hdone
                    have hmBack : microstep (.downRDone (.toRcDone (.readDestRight cell) dCell)) ⟨dTerm, csDest⟩ =
                        .running (.up1 (.pendingRightBackToSrc cell.bit))
                          ⟨.s ⋅ dTerm, .left cj :: .right (.s ⋅ v0) :: csCur⟩ := by
                      simp [microstep, step, onDownRDone, onCellRead, hoff, hdone, startUp,
                        applyAction, csDest, downRCrumbs, dTerm, frameTerm, S]
                    have sBack := up_from_right_steps (.pendingRightBackToSrc cell.bit) .s v0 .s dTerm cj csCur hcjObs _ hmBack
                    let recCell : Cell := ⟨cell.bit, .off, 0⟩
                    let des := encodeRecord11 recCell
                    have sApp := downL_steps (.toAppendVerEntry des) .s v0 .s dTerm cj csCur
                      (.upDone (.pendingRightBackToSrc cell.bit) true) rfl
                    have sTot := StepsTo.trans sPreD (StepsTo.trans sBack sApp)
                    let curV0 : Cursor := ⟨v0, downLCrumbs .s dTerm .s cj csCur⟩
                    have hrebV0 : rebuild curV0 = seedHubRoot flag tape (depthJunk 0) :=
                      sTot.1.symm.trans (hrebHub rframes cellTerm)
                    have hpathV0 : crumbsPath curV0.crumbs = rootTapePath ++ srcPath ++ cellVersionPath := by
                      dsimp only [curV0]
                      rw [downLCrumbs_path]
                      have hc := hubTapeCursor_crumbsPath rootLeft hubCtx rframes cellTerm
                      dsimp only [hubTapeCursor] at hc
                      rw [hc]
                      simp [srcPath, cellVersionPath, List.append_assoc]
                    have hchooseVer : selectVersionAt (seedHubRoot flag tape (depthJunk 0))
                        (rootTapePath ++ srcPath ++ cellVersionPath) recCell = some path := by
                      simp only [pendingPlan, isMoving, hpendStatus, Bool.not_true, Bool.false_eq_true,
                        hoffV, hdoneV, ↓reduceIte, chooseCellWrite] at hsel
                      simpa [recCell, hbitEq] using hsel
                    have hfin := appendEntry_agrees recCell curV0 (by rw [hrebV0]; exact hpSeed) hsV0
                      (by rw [hrebV0, hpathV0]; exact hchooseVer) (by rw [hrebV0]; exact hdir)
                    exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
                  else
                    have hoffV : ((cellFromVersion dv0).status == .off) = false :=
                      hdStatusEq ▸ Bool.eq_false_iff.mpr hoff
                    have hdoneV : ((cellFromVersion dv0).status == .active &&
                        (cellFromVersion dv0).state == (cellFromVersion v0).state) = false := by
                      rw [← hdStatusEq, ← hbeqState]; exact Bool.eq_false_iff.mpr hdone
                    simp [pendingPlan, isMoving, hpendStatus, hoffV, hdoneV] at hsel
          | movingLeft =>
              let tape := wrapRChain rframes cellTerm
              let srcPath := rframesRelPath rframes
              have hmoveTrue : movingCell (cellFromVersion v0) = true := by
                unfold movingCell isMoving; rw [← hstatusEq, hstatus]
              have hprio : priorityConcretePath tape = .pending srcPath := by
                unfold priorityConcretePath
                rw [seekConcreteCell_wrapRChain movingCell rframes cellTerm hall]
                simp [cellTerm, seek_concrete_frame, hmoveTrue, srcPath]
              rw [full_selector_pending_branch fixedBinaryProgram flag tape (depthJunk 0) srcPath hflagFalse hprio] at hsel
              have hreadSrc : readCellAt tape srcPath = some (cellFromVersion v0) := by
                unfold readCellAt
                rw [termAt_wrapRChain rframes cellTerm hallCan]
                simp [cellTerm, parse_frame]
              have hpendStatus : (cellFromVersion v0).status = .movingLeft := hstatusEq.symm.trans hstatus
              unfold choosePending at hsel
              rw [hreadSrc] at hsel
              dsimp only [Bind.bind, Option.bind] at hsel
              cases rframes with
              | nil =>
                  simp [pendingDestinationPath, hpendStatus, srcPath, rframesRelPath] at hsel
              | cons f0 rRest =>
                  simp only [List.cons_append, List.cons.injEq] at hpfEq
                  rcases hpfEq with ⟨hpfF0, rfl⟩
                  subst f0
                  have hpfCan : CanonicalFrameCtx pf := hallCan pf (by simp)
                  obtain ⟨hpfS1, hpfS2, hpfJ, hpPfOther, hsPfOther⟩ := hpfCan
                  have hsrcNonEmpty : srcPath.isEmpty = false := by
                    dsimp only [srcPath, rframesRelPath]
                    cases rframesRelPath rRest <;> rfl
                  have hdestPath : pendingDestinationPath (cellFromVersion v0) srcPath = some (rframesRelPath rRest) := by
                    unfold pendingDestinationPath
                    rw [hpendStatus, hsrcNonEmpty]
                    simp [srcPath, rframesRelPath, parentCellPath_snoc]
                  rw [hdestPath] at hsel
                  dsimp only [] at hsel
                  have hrRestCan : ∀ x ∈ rRest, CanonicalFrameCtx x := fun x hx => hallCan x (by simp [hx])
                  let pTerm := (pf.s1 ⋅ pf.other) ⋅ ((pf.s2 ⋅ cellTerm) ⋅ pf.j)
                  have hpTermFrame : pTerm = frameTerm pf.other cellTerm pf.j := by
                    dsimp only [pTerm, frameTerm, S]
                    rw [hpfS1, hpfS2]
                  have htermDest : termAt tape (rframesRelPath rRest) = some pTerm :=
                    termAt_wrapRChain rRest pTerm hrRestCan
                  rw [htermDest, hpTermFrame] at hsel
                  dsimp only [Bind.bind, Option.bind] at hsel
                  rw [parse_frame] at hsel
                  dsimp only [] at hsel
                  have hmUp : microstep (.downRDone (.toRcDone .seekPending cell))
                      ⟨cellTerm, downRCrumbs pf.s1 pf.other pf.s2 pf.j (pushRChain (rRest ++ [hubCtx]) [.right rootLeft])⟩ =
                      .running (.up1 (.pendingLeftToParent cell))
                        ⟨pf.s2 ⋅ cellTerm, .left pf.j :: .right (pf.s1 ⋅ pf.other) :: pushRChain (rRest ++ [hubCtx]) [.right rootLeft]⟩ := by
                    simp [microstep, step, onDownRDone, onCellRead, hstatus, startUp, applyAction, downRCrumbs, cellTerm, frameTerm, S]
                  have sUpP := up_from_right_steps (.pendingLeftToParent cell) pf.s1 pf.other pf.s2 cellTerm pf.j
                    (pushRChain (rRest ++ [hubCtx]) [.right rootLeft]) hpfValid.2.2 _ hmUp
                  rw [← hcsCurEq] at sUpP
                  have hpfsDecomp : ∃ pf2 pfs2, rRest ++ [hubCtx] = pf2 :: pfs2 ∧ ValidFrameCtx pf2 := by
                    cases rRest with
                    | nil => exact ⟨hubCtx, [], rfl, hhub⟩
                    | cons f2 fs2 => exact ⟨f2, fs2 ++ [hubCtx], rfl, hallValid f2 (by simp)⟩
                  obtain ⟨pf2, pfs2, hpfsEq, hpf2Valid⟩ := hpfsDecomp
                  rw [hpfsEq] at sUpP
                  have sChk := hubChk_below_hub_steps (.pendingLeftChk cell) pf2.s2 pTerm pf2.j
                    (.right (pf2.s1 ⋅ pf2.other) :: pushRChain pfs2 [.right rootLeft])
                    (.upDone (.pendingLeftToParent cell) true) rfl
                  let csPrev := downRCrumbs pf2.s1 pf2.other pf2.s2 pf2.j (pushRChain pfs2 [.right rootLeft])
                  have hcsPrevEq : csPrev = pushRChain (rRest ++ [hubCtx]) [.right rootLeft] := by
                    dsimp only [csPrev]; rw [hpfsEq]; rfl
                  have sDownPrev := downL_steps (.toRcStart (.readDestLeft cell))
                    pf.s1 pf.other pf.s2 cellTerm pf.j csPrev
                    (.hubChkDone (.pendingLeftChk cell) false) rfl
                  have sReadPrev := readCell_steps (.readDestLeft cell) pf2.s1 pf2.other pf2.s2 pf2.j
                    (pushRChain pfs2 [.right rootLeft]) hpf2Valid.2.2
                    pf.s1 pf.other pf.s2 cellTerm pf.j hpfValid
                  let prevCell := (obsScanBottomUp pf.other).getD defaultCell8
                  have hpCellEq : cell8ToCell prevCell = cellFromVersion pf.other :=
                    obsScanBottomUp_agrees hpPfOther hsPfOther
                  have hpStatusEq : prevCell.status = (cellFromVersion pf.other).status := congrArg Cell.status hpCellEq
                  have hpBitEq : prevCell.bit = (cellFromVersion pf.other).bit := congrArg Cell.bit hpCellEq
                  have hpStateEq : prevCell.state.val = (cellFromVersion pf.other).state := congrArg Cell.state hpCellEq
                  have hbeqPrev : (prevCell.state == cell.state) =
                      ((cellFromVersion pf.other).state == (cellFromVersion v0).state) := by
                    rw [fin256_beq_eq_val_beq, hpStateEq, hstateEq]
                  have sPreL := StepsTo.trans sPre (StepsTo.trans sUpP (StepsTo.trans sChk (StepsTo.trans sDownPrev sReadPrev)))
                  if hoff : prevCell.status == .off then
                    have hoffV : ((cellFromVersion pf.other).status == .off) = true := hpStatusEq ▸ hoff
                    let recCell : Cell := ⟨prevCell.bit, .active, cell.state.val⟩
                    let des := encodeRecord11 recCell
                    have hmApp : microstep (.downRDone (.toRcDone (.readDestLeft cell) prevCell)) ⟨pTerm, csPrev⟩ =
                        .running (.downL1 (.toAppendVerEntry des)) ⟨pf.s1 ⋅ pf.other, .left ((pf.s2 ⋅ cellTerm) ⋅ pf.j) :: csPrev⟩ := by
                      simp [microstep, step, onDownRDone, onCellRead, hoff, startDownL, applyAction, des, recCell, pTerm]
                    have sApp := downL_steps (.toAppendVerEntry des) pf.s1 pf.other pf.s2 cellTerm pf.j csPrev _ hmApp
                    have sTot := StepsTo.trans sPreL sApp
                    let curPrevV : Cursor := ⟨pf.other, downLCrumbs pf.s1 cellTerm pf.s2 pf.j csPrev⟩
                    have hrebPrev : rebuild curPrevV = seedHubRoot flag tape (depthJunk 0) :=
                      sTot.1.symm.trans (hrebHub (pf :: rRest) cellTerm)
                    have hpathPrev : crumbsPath curPrevV.crumbs =
                        rootTapePath ++ rframesRelPath rRest ++ cellVersionPath := by
                      dsimp only [curPrevV]
                      rw [downLCrumbs_path, hcsPrevEq]
                      have hc := hubTapeCursor_crumbsPath rootLeft hubCtx rRest pTerm
                      dsimp only [hubTapeCursor] at hc
                      rw [hc]
                      simp [cellVersionPath, List.append_assoc]
                    have hchooseVer : selectVersionAt (seedHubRoot flag tape (depthJunk 0))
                        (rootTapePath ++ rframesRelPath rRest ++ cellVersionPath) recCell = some path := by
                      simp only [pendingPlan, isMoving, hpendStatus, Bool.not_true, Bool.false_eq_true,
                        hoffV, ↓reduceIte, chooseCellWrite] at hsel
                      simpa [recCell, hpBitEq, hstateEq] using hsel
                    have hfin := appendEntry_agrees recCell curPrevV (by rw [hrebPrev]; exact hpSeed) hsPfOther
                      (by rw [hrebPrev, hpathPrev]; exact hchooseVer) (by rw [hrebPrev]; exact hdir)
                    exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
                  else if hdone : prevCell.status == .active && prevCell.state == cell.state then
                    have hoffV : ((cellFromVersion pf.other).status == .off) = false :=
                      hpStatusEq ▸ Bool.eq_false_iff.mpr hoff
                    have hdoneV : ((cellFromVersion pf.other).status == .active &&
                        (cellFromVersion pf.other).state == (cellFromVersion v0).state) = true := by
                      rw [← hpStatusEq, ← hbeqPrev]; exact hdone
                    let recCell : Cell := ⟨cell.bit, .off, 0⟩
                    let des := encodeRecord11 recCell
                    have hmBack : microstep (.downRDone (.toRcDone (.readDestLeft cell) prevCell)) ⟨pTerm, csPrev⟩ =
                        .running (.downR1 (.toPendingLeftBackToSrc des))
                          ⟨(pf.s2 ⋅ cellTerm) ⋅ pf.j, .right (pf.s1 ⋅ pf.other) :: csPrev⟩ := by
                      simp [microstep, step, onDownRDone, onCellRead, hoff, hdone, startDownR, applyAction, des, recCell, pTerm]
                    have sBack := downR_steps (.toPendingLeftBackToSrc des) pf.s1 pf.other pf.s2 cellTerm pf.j csPrev _ hmBack
                    have sApp := downL_steps (.toAppendVerEntry des) .s v0 .s nextTape cj
                      (downRCrumbs pf.s1 pf.other pf.s2 pf.j csPrev)
                      (.downRDone (.toPendingLeftBackToSrc des)) rfl
                    have sTot := StepsTo.trans sPreL (StepsTo.trans sBack sApp)
                    let curSrcV : Cursor := ⟨v0, downLCrumbs .s nextTape .s cj (downRCrumbs pf.s1 pf.other pf.s2 pf.j csPrev)⟩
                    have hrebSrc : rebuild curSrcV = seedHubRoot flag tape (depthJunk 0) :=
                      sTot.1.symm.trans (hrebHub (pf :: rRest) cellTerm)
                    have hpathSrc : crumbsPath curSrcV.crumbs =
                        rootTapePath ++ srcPath ++ cellVersionPath := by
                      dsimp only [curSrcV]
                      rw [downLCrumbs_path, downRCrumbs_path, hcsPrevEq]
                      have hc := hubTapeCursor_crumbsPath rootLeft hubCtx rRest pTerm
                      dsimp only [hubTapeCursor] at hc
                      rw [hc]
                      simp [srcPath, rframesRelPath, cellVersionPath, List.append_assoc]
                    have hchooseVer : selectVersionAt (seedHubRoot flag tape (depthJunk 0))
                        (rootTapePath ++ srcPath ++ cellVersionPath) recCell = some path := by
                      simp only [pendingPlan, isMoving, hpendStatus, Bool.not_true, Bool.false_eq_true,
                        hoffV, hdoneV, ↓reduceIte, chooseCellWrite] at hsel
                      simpa [recCell, hbitEq] using hsel
                    have hfin := appendEntry_agrees recCell curSrcV (by rw [hrebSrc]; exact hpSeed) hsV0
                      (by rw [hrebSrc, hpathSrc]; exact hchooseVer) (by rw [hrebSrc]; exact hdir)
                    exact (LeadsTo.of_stepsTo sTot).toFinishesWith hfin
                  else
                    have hoffV : ((cellFromVersion pf.other).status == .off) = false :=
                      hpStatusEq ▸ Bool.eq_false_iff.mpr hoff
                    have hdoneV : ((cellFromVersion pf.other).status == .active &&
                        (cellFromVersion pf.other).state == (cellFromVersion v0).state) = false := by
                      rw [← hpStatusEq, ← hbeqPrev]; exact Bool.eq_false_iff.mpr hdone
                    simp [pendingPlan, isMoving, hpendStatus, hoffV, hdoneV] at hsel

/-- Canonical Hub Agreement: on any pure-S `seedHubRoot flag tape (depthJunk 0)` whose hub satisfies
    `logicalTreeStrict`, whenever `fullRootSelector fixedBinaryProgram` selects `path` and `contractAt`
    produces `out`, `invoke` returns `.contracted out`. -/
theorem invoke_agrees_on_canonical_hub (flag tape : Term) {path : List Bool} {out : Term}
    (hpRoot : isPureS (seedHubRoot flag tape (depthJunk 0)) = true)
    (hsHub : logicalTreeStrict (frameTerm flag tape (depthJunk 0)) = true)
    (hsel : fullRootSelector fixedBinaryProgram (seedHubRoot flag tape (depthJunk 0)) = some path)
    (hcon : contractAt (seedHubRoot flag tape (depthJunk 0)) path = some out) :
    invoke (seedHubRoot flag tape (depthJunk 0)) = .contracted out := by
  have hdir : DirectedStep path (seedHubRoot flag tape (depthJunk 0)) out :=
    (contractAt_iff_directedStep _ _ path).mp hcon
  let rootLeft := numeral 1 ⋅ S
  let hub := frameTerm flag tape (depthJunk 0)
  have hpHub : isPureS hub = true := by
    have h := hpRoot
    simp only [seedHubRoot, isPureS, Bool.and_eq_true] at h
    exact h.2
  have hhubObs : strictFrameObs (frameTerm flag tape (depthJunk 0)) = true := by
    rw [strictFrameObs_eq_flagValue_of_strict hpHub hsHub]
    rfl
  have hpFlag : isPureS flag = true := by
    have h := hpHub
    simp only [hub, frameTerm, S, isPureS, Bool.and_eq_true] at h
    exact h.1.2
  have hpJ0 : isPureS (depthJunk 0) = true := by
    have h := hpHub
    simp only [hub, frameTerm, S, isPureS, Bool.and_eq_true] at h
    exact h.2.2
  have hsHub' := hsHub
  rw [logicalTreeStrict_frame] at hsHub'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsHub'
  rcases hsHub' with ⟨⟨hj0Ns2, hsFlag⟩, hsTape⟩
  have hj0Obs : s2Obs (depthJunk 0) = false := by
    match hg : depthJunk 0 with
    | .app (.app a _) _ =>
        rw [hg] at hpJ0 hj0Ns2
        simp only [isPureS, Bool.and_eq_true] at hpJ0
        cases a with
        | s => cases hj0Ns2
        | var _ => simp [isPureS] at hpJ0
        | app _ _ => rfl
    | .s => rfl
    | .var _ => rfl
    | .app .s _ => rfl
    | .app (.var _) _ => rfl
  have sInit : StepsTo 1 initControl (rootCursor (seedHubRoot flag tape (depthJunk 0)))
      (.sf (.sf0 .hubInit)) ⟨hub, [.right rootLeft]⟩ :=
    StepsTo.of_step rfl
  have sHubSf := checkStrictFrame_steps .hubInit ⟨hub, [.right rootLeft]⟩
  dsimp only [hub] at sHubSf
  rw [hhubObs] at sHubSf
  have sDownFlag := downL_steps .toFlagInit .s flag .s tape (depthJunk 0) [.right rootLeft]
    (.sf (.sfDone .hubInit true)) rfl
  let csFlag := downLCrumbs .s tape .s (depthJunk 0) [.right rootLeft]
  have sAliasF : StepsTo 0 (.downLDone .toFlagInit) ⟨flag, csFlag⟩
      (.sf (.sf0 .flagInit)) ⟨flag, csFlag⟩ :=
    StepsTo.of_alias rfl
  have sFlagSf := checkStrictFrame_steps .flagInit ⟨flag, csFlag⟩
  dsimp only [] at sFlagSf
  cases hfv : flagValue flag with
  | true =>
      obtain ⟨fl, fr, fj, rfl, hflagObs, _, _, _, hsFl, _, _, _, _⟩ :=
        strictFrame_pureS_decomp hpFlag hsFlag hfv
      rw [hflagObs] at sFlagSf
      rw [full_selector_halt_branch fixedBinaryProgram (frameTerm fl fr fj) tape (depthJunk 0) hfv] at hsel
      have sDownFl := downL_steps .toFrontier .s fl .s fr fj csFlag
        (.sf (.sfDone .flagInit true)) rfl
      let csFl := downLCrumbs .s fr .s fj csFlag
      have sAliasFr : StepsTo 0 (.downLDone .toFrontier) ⟨fl, csFl⟩
          (.sf (.sf0 .frontierWalk)) ⟨fl, csFl⟩ :=
        StepsTo.of_alias rfl
      have sTot := StepsTo.trans sInit
        (StepsTo.trans sHubSf
          (StepsTo.trans sDownFlag
            (StepsTo.trans sAliasF (StepsTo.trans sFlagSf (StepsTo.trans sDownFl sAliasFr)))))
      have hrebFl : rebuild ⟨fl, csFl⟩ = seedHubRoot (frameTerm fl fr fj) tape (depthJunk 0) := sTot.1.symm
      have hpathFl : crumbsPath csFl ++ closedLeftFrontier fl =
          hubFlagPath ++ closedLeftFrontier (frameTerm fl fr fj) := by
        simp [csFl, csFlag, downLCrumbs_path, crumbsPath, hubFlagPath, closedLeftFrontier, frameTerm, S]
      have hfin := frontierWalk_agrees (leaves fl) ⟨fl, csFl⟩ (Nat.le_refl _)
        (by rw [hrebFl]; exact hpRoot) hsFl (by rw [hrebFl, hpathFl]; exact hsel) (by rw [hrebFl]; exact hdir)
      exact finishesWith_eq_invoke ((LeadsTo.of_stepsTo sTot).toFinishesWith hfin)
  | false =>
      have hflagObs : strictFrameObs flag = false :=
        (strictFrameObs_eq_flagValue_of_strict hpFlag hsFlag).trans hfv
      rw [hflagObs] at sFlagSf
      have sUpHub := up_from_left_steps .flagToHub .s flag .s tape (depthJunk 0) [.right rootLeft] hhubObs
        (.sf (.sfDone .flagInit false)) rfl
      have sDownTape := downR_steps .toTapeInit .s flag .s tape (depthJunk 0) [.right rootLeft]
        (.upDone .flagToHub false) rfl
      let hubCtx : FrameCtx := ⟨.s, flag, .s, depthJunk 0⟩
      have sAliasT : StepsTo 0 (.downRDone .toTapeInit)
          (hubTapeCursor rootLeft hubCtx [] tape)
          (.sf (.sf0 (.seekCell false)))
          (hubTapeCursor rootLeft hubCtx [] tape) :=
        StepsTo.of_alias rfl
      have sTot := StepsTo.trans sInit
        (StepsTo.trans sHubSf
          (StepsTo.trans sDownFlag
            (StepsTo.trans sAliasF (StepsTo.trans sFlagSf (StepsTo.trans sUpHub (StepsTo.trans sDownTape sAliasT))))))
      have hfin := seekPending_agrees flag hfv hj0Obs (leaves tape) tape [] (Nat.le_refl _)
        (fun _ h => nomatch h) hpRoot hsTape hsel hdir
      exact finishesWith_eq_invoke ((LeadsTo.of_stepsTo sTot).toFinishesWith hfin)

theorem niceSelectorTrace_step_props {program : BinaryProgram} {M k : Nat}
    {start checkpoint reached : Term}
    (hnice : NiceSelectorTrace program M start checkpoint)
    (hfull : FullSelectorTrace program k start reached)
    (hk : k < M) :
    (∃ flag tape,
      reached = seedHubRoot flag tape (depthJunk 0) ∧
      logicalTreeStrict (frameTerm flag tape (depthJunk 0)) = true) ∧
    (∃ path next,
      fullRootSelector program reached = some path ∧
      DirectedStep path reached next) := by
  induction k generalizing M start with
  | zero =>
      cases hfull
      cases hnice with
      | zero _ => exact False.elim (by omega)
      | @next _ _ b _ path hhub _ hsel hdir _ =>
          exact ⟨hhub, ⟨path, b, hsel, hdir⟩⟩
  | succ k ih =>
      cases hfull with
      | @next _ _ mid1 _ path1 hs1 hd1 tailFull =>
          cases hnice with
          | zero _ => exact False.elim (by omega)
          | @next _ _ b _ path2 _ _ hs2 hd2 restNice =>
              have heq : b = mid1 := full_selector_step_unique program start b mid1 path2 path1 hs2 hs1 hd2 hd1
              subst mid1
              exact ih restNice tailFull (by omega)

/-- **(d) Exact Trajectory Agreement**: at EVERY reachable canonical trajectory term `reached`
    from `sEncodeU initial` (`FullSelectorTrace fixedBinaryProgram k (sEncodeU initial) reached`),
    1. For any `path, t'` with `fullRootSelector fixedBinaryProgram reached = some path` and
       `contractAt reached path = some t'`, `invoke reached = .contracted t'`;
    2. Moreover, `fullRootSelector fixedBinaryProgram reached` always selects a valid redex `path`
       whose contraction `t'` matches `invoke reached = .contracted t'`. -/
theorem exact_trajectory_agreement (initial : UConfig) {k : Nat} {reached : Term}
    (htrace : FullSelectorTrace fixedBinaryProgram k (sEncodeU initial) reached) :
    (∀ path t',
      fullRootSelector fixedBinaryProgram reached = some path →
      contractAt reached path = some t' →
      invoke reached = .contracted t') ∧
    (∃ path t',
      fullRootSelector fixedBinaryProgram reached = some path ∧
      contractAt reached path = some t' ∧
      invoke reached = .contracted t') := by
  have hpReached : isPureS reached = true :=
    fullSelectorTrace_preserves_isPureS htrace (sEncodeU_isPureS initial)
  have hrep0 := initial_records_represent (encodeUConfig initial)
  have hspec := plainRunFor_spec fixedBinaryProgram (k + 1) (encodeUConfig initial)
  have hStepProps :
      (∃ flag tape,
        reached = seedHubRoot flag tape (depthJunk 0) ∧
        logicalTreeStrict (frameTerm flag tape (depthJunk 0)) = true) ∧
      (∃ path next,
        fullRootSelector fixedBinaryProgram reached = some path ∧
        DirectedStep path reached next) := by
    cases hr : plainRunFor fixedBinaryProgram (k + 1) (encodeUConfig initial) with
    | inr future =>
        rw [hr] at hspec
        obtain ⟨_, hsourceRun, _⟩ :=
          plain_run_lifts fixedBinaryProgram hspec (initialRecords (encodeUConfig initial)) hrep0
        obtain ⟨M, hloM, _, hnice⟩ := source_run_nice_selector fixedBinaryProgram hsourceRun
        exact niceSelectorTrace_step_props hnice htrace (by omega)
    | inl pair =>
        rcases pair with ⟨_, stoppedCfg⟩
        rw [hr] at hspec
        rcases hspec with ⟨_, hplainRun, hstopPlain⟩
        obtain ⟨finalCells, hsourceRun, hrepFinal⟩ :=
          plain_run_lifts fixedBinaryProgram hplainRun (initialRecords (encodeUConfig initial)) hrep0
        obtain ⟨before, source, after, hcellsEq, hb, hs, ha, _, _⟩ := hrepFinal
        subst finalCells
        have hruleNone : fixedBinaryProgram stoppedCfg.state stoppedCfg.bit = none :=
          (plain_next_none_iff_rule_none fixedBinaryProgram stoppedCfg).mp hstopPlain
        obtain ⟨k1, _, _, hnice1⟩ := source_run_nice_selector fixedBinaryProgram hsourceRun
        let tape := canonicalTape (before ++ source :: after) 1
        let srcPath := physicalPath (List.replicate before.length true)
        have htapeStrict : logicalTreeStrict tape = true :=
          layoutTerm_logicalTreeStrict _ _ (phase_at_good 1)
        have hpriority : priorityConcretePath tape = .active srcPath :=
          canonical_boundary_priority_path before source after stoppedCfg.state stoppedCfg.bit hb hs ha 1
        have hread : readCellAt tape srcPath = some ⟨stoppedCfg.bit, .active, stoppedCfg.state.val⟩ :=
          canonical_boundary_reads_active before source after stoppedCfg.state stoppedCfg.bit hs 1
        obtain ⟨k2, hk2, hnice2⟩ :=
          seed_halt_nice_trace fixedBinaryProgram tape htapeStrict srcPath stoppedCfg.state stoppedCfg.bit
            hpriority hread hruleNone
        obtain ⟨k3, lo3, _, hnice3⟩ := post_halt_run_nice fixedBinaryProgram tape htapeStrict (k + 1)
        have htotalNice := niceSelectorTrace_trans hnice1 (niceSelectorTrace_trans hnice2 hnice3)
        have hkM : k < k1 + (k2 + k3) := by cases hk2 <;> omega
        exact niceSelectorTrace_step_props htotalNice htrace hkM
  obtain ⟨⟨flag, tape, rfl, hsHub⟩, ⟨path0, next0, hsel0, hdir0⟩⟩ := hStepProps
  have hcond : ∀ path t',
      fullRootSelector fixedBinaryProgram (seedHubRoot flag tape (depthJunk 0)) = some path →
      contractAt (seedHubRoot flag tape (depthJunk 0)) path = some t' →
      invoke (seedHubRoot flag tape (depthJunk 0)) = .contracted t' :=
    fun _ _ hs hc => invoke_agrees_on_canonical_hub flag tape hpReached hsHub hs hc
  have hcon0 : contractAt (seedHubRoot flag tape (depthJunk 0)) path0 = some next0 :=
    (contractAt_iff_directedStep _ _ path0).mpr hdir0
  exact ⟨hcond, ⟨path0, next0, hsel0, hcon0, hcond path0 next0 hsel0 hcon0⟩⟩

#print axioms mem_allControls
#print axioms invoke_unit_initial_state
#print axioms all_input_linear_microtick_bound
#print axioms pure_s_normality_and_contraction_contract
#print axioms invoke_agrees_on_canonical_hub
#print axioms exact_trajectory_agreement


