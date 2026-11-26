import u_step_refinement

/-!
# Partial Deterministic Binary One-Sided Source Turing Machine

Defines `SourceTM` with clamped-left one-sided binary tape semantics, halting
precisely when `stepRule` returns `none`, together with constructive bounded
execution, canonical output trimming, and constructive halting search via `Acc`.
-/

structure SourceAct (numStates : Nat) where
  write : Bool
  dir : SourceDirection
  next : Fin numStates
  deriving DecidableEq, Repr

structure SourceTM where
  numStates : Nat
  hpos : numStates ≥ 1
  stepRule : Fin numStates → Bool → Option (SourceAct numStates)

structure SourceConfig (numStates : Nat) where
  state : Fin numStates
  head : Nat
  tape : List Bool
  deriving DecidableEq, Repr

def writeTapeList : List Bool → Nat → Bool → List Bool
  | [], 0, b => [b]
  | [], n + 1, b => false :: writeTapeList [] n b
  | _ :: xs, 0, b => b :: xs
  | x :: xs, n + 1, b => x :: writeTapeList xs n b

theorem bitAt_nil (i : Nat) : bitAt [] i = false := by
  cases i <;> rfl

theorem bitAt_writeTapeList (xs : List Bool) (pos : Nat) (val : Bool) (i : Nat) :
    bitAt (writeTapeList xs pos val) i = if i = pos then val else bitAt xs i := by
  induction pos generalizing xs i with
  | zero =>
    cases xs with
    | nil =>
      cases i with
      | zero => rfl
      | succ j =>
        rw [if_neg (Nat.succ_ne_zero j)]
        exact bitAt_nil j
    | cons x rest =>
      cases i with
      | zero => rfl
      | succ j =>
        rw [if_neg (Nat.succ_ne_zero j)]
        rfl
  | succ p ih =>
    cases xs with
    | nil =>
      cases i with
      | zero =>
        rw [if_neg (Nat.succ_ne_zero p).symm]
        rfl
      | succ j =>
        change bitAt (writeTapeList [] p val) j = if j + 1 = p + 1 then val else bitAt [] j
        rw [ih [] j]
        by_cases hjp : j = p
        · subst hjp; rw [if_pos rfl, if_pos rfl]
        · have hsucc : j + 1 ≠ p + 1 := fun h => hjp (Nat.succ.inj h)
          rw [if_neg hjp, if_neg hsucc]
    | cons x rest =>
      cases i with
      | zero =>
        rw [if_neg (Nat.succ_ne_zero p).symm]
        rfl
      | succ j =>
        change bitAt (writeTapeList rest p val) j = if j + 1 = p + 1 then val else bitAt rest j
        rw [ih rest j]
        by_cases hjp : j = p
        · subst hjp; rw [if_pos rfl, if_pos rfl]
        · have hsucc : j + 1 ≠ p + 1 := fun h => hjp (Nat.succ.inj h)
          rw [if_neg hjp, if_neg hsucc]

def sourceMoveHead (d : SourceDirection) (h : Nat) : Nat :=
  match d with
  | .left => h - 1
  | .stay => h
  | .right => h + 1

def initSourceConfig (M : SourceTM) (w : List Bool) : SourceConfig M.numStates :=
  ⟨⟨0, M.hpos⟩, 0, w⟩

def sourceStep (M : SourceTM) (c : SourceConfig M.numStates) : Option (SourceConfig M.numStates) :=
  match M.stepRule c.state (bitAt c.tape c.head) with
  | none => none
  | some act =>
    some ⟨act.next, sourceMoveHead act.dir c.head, writeTapeList c.tape c.head act.write⟩

theorem sourceStep_none_iff (M : SourceTM) (c : SourceConfig M.numStates) :
    sourceStep M c = none ↔ M.stepRule c.state (bitAt c.tape c.head) = none := by
  unfold sourceStep
  cases M.stepRule c.state (bitAt c.tape c.head) <;> simp

inductive SourceTMRun (M : SourceTM) : Nat → SourceConfig M.numStates → SourceConfig M.numStates → Prop where
  | zero (c : SourceConfig M.numStates) : SourceTMRun M 0 c c
  | next {n : Nat} {a b c : SourceConfig M.numStates} :
      sourceStep M a = some b → SourceTMRun M n b c → SourceTMRun M (n + 1) a c

theorem sourceTMRun_trans {M : SourceTM} {n m : Nat} {a b c : SourceConfig M.numStates}
    (h1 : SourceTMRun M n a b) (h2 : SourceTMRun M m b c) : SourceTMRun M (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | @next k x y z hstep rest ih =>
    have r := SourceTMRun.next hstep (ih h2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem sourceTMRun_snoc {M : SourceTM} {n : Nat} {a b c : SourceConfig M.numStates}
    (h1 : SourceTMRun M n a b) (hstep : sourceStep M b = some c) : SourceTMRun M (n + 1) a c :=
  sourceTMRun_trans h1 (SourceTMRun.next hstep (SourceTMRun.zero c))

theorem sourceTMRun_deterministic {M : SourceTM} {n : Nat} {a b c : SourceConfig M.numStates}
    (h1 : SourceTMRun M n a b) (h2 : SourceTMRun M n a c) : b = c := by
  induction h1 generalizing c with
  | zero _ =>
    cases h2
    rfl
  | @next k x y z hs1 rest1 ih =>
    cases h2 with
    | @next _ _ y2 _ hs2 rest2 =>
      rw [hs1] at hs2
      injection hs2 with hy
      subst hy
      exact ih rest2

theorem sourceTMRun_halt_unique {M : SourceTM} {n1 n2 : Nat} {a b1 b2 : SourceConfig M.numStates}
    (r1 : SourceTMRun M n1 a b1) (s1 : sourceStep M b1 = none)
    (r2 : SourceTMRun M n2 a b2) (s2 : sourceStep M b2 = none) :
    n1 = n2 ∧ b1 = b2 := by
  induction r1 generalizing n2 b2 with
  | zero c =>
    cases r2 with
    | zero _ => exact ⟨rfl, rfl⟩
    | next hs2 _ => rw [s1] at hs2; cases hs2
  | @next k x y z hs1 rest1 ih =>
    cases r2 with
    | zero _ => rw [s2] at hs1; cases hs1
    | @next k2 _ y2 _ hs2 rest2 =>
      rw [hs1] at hs2
      injection hs2 with hy
      subst hy
      obtain ⟨hn, hb⟩ := ih s1 rest2 s2
      exact ⟨congrArg (· + 1) hn, hb⟩

def SourceEventuallyStopsTM (M : SourceTM) (w : List Bool) : Prop :=
  ∃ n final, SourceTMRun M n (initSourceConfig M w) final ∧ sourceStep M final = none

inductive BoundedSourceOutcome (M : SourceTM) (start : SourceConfig M.numStates) (bound : Nat) : Type where
  | halted (steps : Nat) (hle : steps ≤ bound) (final : SourceConfig M.numStates)
      (run : SourceTMRun M steps start final) (stop : sourceStep M final = none)
  | running (curr : SourceConfig M.numStates) (run : SourceTMRun M (bound + 1) start curr)

def evalSourceBounded (M : SourceTM) (start : SourceConfig M.numStates) :
    (bound : Nat) → BoundedSourceOutcome M start bound
  | 0 =>
    match hs : sourceStep M start with
    | none => .halted 0 (Nat.le_refl 0) start (.zero start) hs
    | some nxt => .running nxt (.next hs (.zero nxt))
  | bound + 1 =>
    match evalSourceBounded M start bound with
    | .halted k hle fin run hstop => .halted k (Nat.le_succ_of_le hle) fin run hstop
    | .running curr run =>
      match hs : sourceStep M curr with
      | none => .halted (bound + 1) (Nat.le_refl _) curr run hs
      | some nxt => .running nxt (sourceTMRun_snoc run hs)

/-! ## Canonical Tape Trimming -/

def trimRightFalse : List Bool → List Bool
  | [] => []
  | b :: xs =>
    match trimRightFalse xs with
    | [] => if b then [true] else []
    | ys => b :: ys

def IsTrimmed : List Bool → Prop
  | [] => True
  | b :: xs => IsTrimmed xs ∧ (xs = [] → b = true)

theorem isTrimmed_trimRightFalse (xs : List Bool) : IsTrimmed (trimRightFalse xs) := by
  induction xs with
  | nil => trivial
  | cons b rest ih =>
    unfold trimRightFalse
    cases ht : trimRightFalse rest with
    | nil =>
      cases b <;> simp [IsTrimmed]
    | cons y ys =>
      rw [ht] at ih
      exact ⟨ih, fun h => by cases h⟩

theorem bitAt_trimRightFalse (xs : List Bool) (i : Nat) :
    bitAt (trimRightFalse xs) i = bitAt xs i := by
  induction xs generalizing i with
  | nil => rfl
  | cons b rest ih =>
    unfold trimRightFalse
    cases ht : trimRightFalse rest with
    | nil =>
      cases b with
      | false =>
        cases i with
        | zero => rfl
        | succ j =>
          have h := ih j
          rw [ht, bitAt_nil] at h
          simpa [bitAt, bitAt_nil] using h
      | true =>
        cases i with
        | zero => rfl
        | succ j =>
          have h := ih j
          rw [ht, bitAt_nil] at h
          simpa [bitAt, bitAt_nil] using h
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ j =>
        have h := ih j
        rw [ht] at h
        simpa [bitAt] using h

theorem exists_true_of_isTrimmed_cons {b : Bool} {xs : List Bool}
    (h : IsTrimmed (b :: xs)) : ∃ i, bitAt (b :: xs) i = true := by
  induction xs generalizing b with
  | nil =>
    have hb : b = true := h.2 rfl
    exact ⟨0, by simp [bitAt, hb]⟩
  | cons y ys ih =>
    obtain ⟨i, hi⟩ := ih h.1
    exact ⟨i + 1, by simpa [bitAt] using hi⟩

theorem eq_of_isTrimmed_bitAt_eq {xs ys : List Bool}
    (hx : IsTrimmed xs) (hy : IsTrimmed ys) (heq : ∀ i, bitAt xs i = bitAt ys i) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b bs =>
      obtain ⟨i, hi⟩ := exists_true_of_isTrimmed_cons hy
      have h0 := heq i
      rw [bitAt_nil, hi] at h0
      cases h0
  | cons a as ih =>
    cases ys with
    | nil =>
      obtain ⟨i, hi⟩ := exists_true_of_isTrimmed_cons hx
      have h0 := heq i
      rw [hi, bitAt_nil] at h0
      cases h0
    | cons b bs =>
      have hab : a = b := by simpa [bitAt] using heq 0
      subst hab
      have htail : as = bs := ih hx.1 hy.1 (fun i => by simpa [bitAt] using heq (i + 1))
      rw [htail]

theorem trimRightFalse_eq_of_bitAt_eq {xs ys : List Bool}
    (heq : ∀ i, bitAt xs i = bitAt ys i) :
    trimRightFalse xs = trimRightFalse ys := by
  apply eq_of_isTrimmed_bitAt_eq (isTrimmed_trimRightFalse xs) (isTrimmed_trimRightFalse ys)
  intro i
  rw [bitAt_trimRightFalse, bitAt_trimRightFalse, heq]

def sourceConfigOutput {k : Nat} (c : SourceConfig k) : List Bool :=
  trimRightFalse c.tape

/-! ## Constructive Halting Search (`Acc`-based, Purely Constructive) -/

def sourceHaltsWithinBool (M : SourceTM) (w : List Bool) (bound : Nat) : Bool :=
  match evalSourceBounded M (initSourceConfig M w) bound with
  | .halted _ _ _ _ _ => true
  | .running _ _ => false

def SourceSearchRel (M : SourceTM) (w : List Bool) (m k : Nat) : Prop :=
  m = k + 1 ∧ sourceHaltsWithinBool M w k = false

theorem sourceHaltsWithinBool_true_of_halt {M : SourceTM} {w : List Bool}
    {n : Nat} {final : SourceConfig M.numStates}
    (hrun : SourceTMRun M n (initSourceConfig M w) final)
    (hstop : sourceStep M final = none) :
    sourceHaltsWithinBool M w n = true := by
  unfold sourceHaltsWithinBool
  cases hev : evalSourceBounded M (initSourceConfig M w) n with
  | halted _ _ _ _ _ => rfl
  | running curr runMore =>
    -- Split `runMore` of length `n + 1` into `n` steps + `1` step
    have hcontra : False := by
      clear hev
      have hsplit : ∀ {k : Nat} {s f1 f2 : SourceConfig M.numStates},
          SourceTMRun M k s f1 → sourceStep M f1 = none → SourceTMRun M (k + 1) s f2 → False := by
        intro k
        induction k with
        | zero =>
          intro s f1 f2 r0 hs0 r1
          cases r0
          cases r1 with
          | next hs _ => rw [hs0] at hs; cases hs
        | succ k ih =>
          intro s f1 f2 rk hsk rk1
          cases rk with
          | next hsA restA =>
            cases rk1 with
            | next hsB restB =>
              rw [hsA] at hsB
              injection hsB with heq
              subst heq
              exact ih restA hsk restB
      exact hsplit hrun hstop runMore
    exact False.elim hcontra

private theorem acc_of_halts_at (M : SourceTM) (w : List Bool) (target : Nat)
    (ht : sourceHaltsWithinBool M w target = true) :
    ∀ d k, k + d = target → Acc (SourceSearchRel M w) k := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have hkt : k = target := by omega
    subst hkt
    refine Acc.intro k (fun m hm => ?_)
    have hfalse : sourceHaltsWithinBool M w k = false := hm.2
    rw [ht] at hfalse
    cases hfalse
  | succ d ih =>
    intro k hk
    refine Acc.intro k (fun m hm => ?_)
    have hm1 : m = k + 1 := hm.1
    subst hm1
    exact ih (k + 1) (by omega)

theorem acc_zero_of_eventually_stops (M : SourceTM) (w : List Bool)
    (h : SourceEventuallyStopsTM M w) : Acc (SourceSearchRel M w) 0 := by
  obtain ⟨n, final, hrun, hstop⟩ := h
  have ht := sourceHaltsWithinBool_true_of_halt hrun hstop
  exact acc_of_halts_at M w n ht n 0 (Nat.zero_add n)

def findHaltingBoundAux (M : SourceTM) (w : List Bool)
    (k : Nat) (hacc : Acc (SourceSearchRel M w) k) :
    { b : Nat // sourceHaltsWithinBool M w b = true } :=
  @WellFounded.fixF Nat (SourceSearchRel M w)
    (fun _ => { b : Nat // sourceHaltsWithinBool M w b = true })
    (fun x ih =>
      match hb : sourceHaltsWithinBool M w x with
      | true => ⟨x, hb⟩
      | false => ih (x + 1) ⟨rfl, hb⟩)
    k hacc

def findHaltingOutcome (M : SourceTM) (w : List Bool) (h : SourceEventuallyStopsTM M w) :
    { c : SourceConfig M.numStates // ∃ n, SourceTMRun M n (initSourceConfig M w) c ∧ sourceStep M c = none } :=
  let ⟨b, hb⟩ := findHaltingBoundAux M w 0 (acc_zero_of_eventually_stops M w h)
  match hev : evalSourceBounded M (initSourceConfig M w) b with
  | .halted steps _ final run stop => ⟨final, ⟨steps, run, stop⟩⟩
  | .running _ _ =>
    False.elim (by
      unfold sourceHaltsWithinBool at hb
      rw [hev] at hb
      cases hb)

def canonicalOutput (M : SourceTM) (w : List Bool) (h : SourceEventuallyStopsTM M w) : List Bool :=
  sourceConfigOutput (findHaltingOutcome M w h).val

theorem canonicalOutput_eq_of_run {M : SourceTM} {w : List Bool}
    (h : SourceEventuallyStopsTM M w) {n : Nat} {final : SourceConfig M.numStates}
    (hrun : SourceTMRun M n (initSourceConfig M w) final)
    (hstop : sourceStep M final = none) :
    canonicalOutput M w h = sourceConfigOutput final := by
  unfold canonicalOutput
  obtain ⟨m, hrunM, hstopM⟩ := (findHaltingOutcome M w h).property
  have ⟨_, heq⟩ := sourceTMRun_halt_unique hrunM hstopM hrun hstop
  rw [heq]

#print axioms bitAt_writeTapeList
#print axioms evalSourceBounded
#print axioms trimRightFalse_eq_of_bitAt_eq
#print axioms canonicalOutput
#print axioms canonicalOutput_eq_of_run
