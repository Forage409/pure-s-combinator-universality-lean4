import formal_utm.source_tm

/-!
# Boundary-Safe Marked-Tape Normalizer (`normalizeSafe`)

Formalizes `normalize_neary_safe.py` exactly:
- Compiles any partial deterministic binary one-sided `SourceTM` and input `w`
  into a total L/R binary `NormalizedTM` and marked initial word.
- Even cells hold markers (`true` sentinel at `0`, `false` at `2*i > 0`);
  odd cells `2*i + 1` hold source data bits `bitAt srcTape i`.
- State `0` moves right from cell `0` to cell `1` in state `1`.
- Defined source rules execute in 2 normalized steps via dedicated auxiliary
  states ordered lexicographically by `(q, b)`, never attempting a left move
  from cell `0`.
- Undefined source rules transition to the unique final state `numStates - 1`,
  which walks left without modifying any tape bits until exiting left from `0`.
-/

inductive NormDir where
  | left | right
  deriving DecidableEq, Repr

structure NormAct (numStates : Nat) where
  write : Bool
  dir : NormDir
  next : Fin numStates
  deriving DecidableEq, Repr

structure NormalizedTM where
  numStates : Nat
  hge2 : numStates ≥ 2
  rule : Fin numStates → Bool → NormAct numStates
  hfinal : ∀ b : Bool,
    rule ⟨numStates - 1, by omega⟩ b = ⟨b, .left, ⟨numStates - 1, by omega⟩⟩

structure NormConfig (numStates : Nat) where
  state : Fin numStates
  head : Nat
  tape : List Bool
  deriving DecidableEq, Repr

def initNormConfig (N : NormalizedTM) (word : List Bool) : NormConfig N.numStates :=
  ⟨⟨0, by have := N.hge2; omega⟩, 0, word⟩

/-- Safe one-sided normalized step: returns `none` precisely when the machine
    attempts to move `.left` from cell `0` (triggering Neary's Lemma 3.4.3 halt). -/
def normStepSafe (N : NormalizedTM) (c : NormConfig N.numStates) : Option (NormConfig N.numStates) :=
  match (N.rule c.state (bitAt c.tape c.head)).dir with
  | .left =>
    if c.head = 0 then none
    else some ⟨(N.rule c.state (bitAt c.tape c.head)).next, c.head - 1,
               writeTapeList c.tape c.head (N.rule c.state (bitAt c.tape c.head)).write⟩
  | .right =>
    some ⟨(N.rule c.state (bitAt c.tape c.head)).next, c.head + 1,
          writeTapeList c.tape c.head (N.rule c.state (bitAt c.tape c.head)).write⟩

theorem normStepSafe_none_iff (N : NormalizedTM) (c : NormConfig N.numStates) :
    normStepSafe N c = none ↔ c.head = 0 ∧ (N.rule c.state (bitAt c.tape c.head)).dir = .left := by
  unfold normStepSafe
  cases hd : (N.rule c.state (bitAt c.tape c.head)).dir with
  | left =>
    by_cases hh : c.head = 0
    · rw [if_pos hh]; simp [hh]
    · rw [if_neg hh]; simp [hh]
  | right =>
    simp

inductive NormRun (N : NormalizedTM) : Nat → NormConfig N.numStates → NormConfig N.numStates → Prop where
  | zero (c : NormConfig N.numStates) : NormRun N 0 c c
  | next {n : Nat} {a b c : NormConfig N.numStates} :
      normStepSafe N a = some b → NormRun N n b c → NormRun N (n + 1) a c

theorem normRun_trans {N : NormalizedTM} {n m : Nat} {a b c : NormConfig N.numStates}
    (h1 : NormRun N n a b) (h2 : NormRun N m b c) : NormRun N (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | @next k x y z hs rest ih =>
    have r := NormRun.next hs (ih h2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem normRun_snoc {N : NormalizedTM} {n : Nat} {a b c : NormConfig N.numStates}
    (h1 : NormRun N n a b) (hs : normStepSafe N b = some c) : NormRun N (n + 1) a c :=
  normRun_trans h1 (NormRun.next hs (NormRun.zero c))

theorem normRun_deterministic {N : NormalizedTM} {n : Nat} {a b c : NormConfig N.numStates}
    (h1 : NormRun N n a b) (h2 : NormRun N n a c) : b = c := by
  induction h1 generalizing c with
  | zero _ => cases h2; rfl
  | @next k x y z hs1 rest1 ih =>
    cases h2 with
    | @next _ _ y2 _ hs2 rest2 =>
      rw [hs1] at hs2
      injection hs2 with hy
      subst hy
      exact ih rest2

theorem normRun_halt_unique {N : NormalizedTM} {n1 n2 : Nat} {a b1 b2 : NormConfig N.numStates}
    (r1 : NormRun N n1 a b1) (s1 : normStepSafe N b1 = none)
    (r2 : NormRun N n2 a b2) (s2 : normStepSafe N b2 = none) :
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

theorem normRun_no_extend_after_stop {N : NormalizedTM} {n m : Nat}
    {a b c : NormConfig N.numStates}
    (r1 : NormRun N n a b) (s1 : normStepSafe N b = none)
    (r2 : NormRun N m a c) : m ≤ n := by
  induction r1 generalizing m c with
  | zero _ =>
    cases r2 with
    | zero _ => exact Nat.le_refl 0
    | next hs2 _ => rw [s1] at hs2; cases hs2
  | @next k x y z hs1 rest1 ih =>
    cases r2 with
    | zero _ => exact Nat.zero_le _
    | @next m' _ y2 _ hs2 rest2 =>
      rw [hs1] at hs2
      injection hs2 with hy
      subst hy
      exact Nat.succ_le_succ (ih s1 rest2)

def NormEventuallyExits (N : NormalizedTM) (word : List Bool) : Prop :=
  ∃ m final, NormRun N m (initNormConfig N word) final ∧ normStepSafe N final = none

/-! ## Marked Word Construction & Invariant -/

def interleaveMarkers : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | b :: bs => b :: false :: interleaveMarkers bs

def encodeMarkedWord (w : List Bool) : List Bool :=
  match w with
  | [] => [true, false]
  | _ => true :: interleaveMarkers w

theorem interleaveMarkers_length : ∀ (w : List Bool), (interleaveMarkers w).length ≤ 2 * w.length
  | [] => by simp [interleaveMarkers]
  | [b] => by simp [interleaveMarkers]
  | b :: b2 :: bs => by
    have ih := interleaveMarkers_length (b2 :: bs)
    simp only [interleaveMarkers, List.length_cons] at ih ⊢
    omega

theorem encodeMarkedWord_length (w : List Bool) :
    (encodeMarkedWord w).length ≤ 2 * w.length + 2 := by
  cases w with
  | nil => simp [encodeMarkedWord]
  | cons b bs =>
    have h := interleaveMarkers_length (b :: bs)
    simp only [List.length_cons] at h
    simp only [encodeMarkedWord, List.length_cons]
    omega

def MarkedTapeMatches (srcTape normTape : List Bool) : Prop :=
  bitAt normTape 0 = true ∧
  (∀ i : Nat, i > 0 → bitAt normTape (2 * i) = false) ∧
  (∀ i : Nat, bitAt normTape (2 * i + 1) = bitAt srcTape i)

private theorem bitAt_interleave_even : ∀ (b : Bool) (bs : List Bool) (i : Nat),
    bitAt (interleaveMarkers (b :: bs)) (2 * i) = bitAt (b :: bs) i
  | b, [], 0 => rfl
  | b, [], i + 1 => by
    have h1 : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
    rw [h1]
    simp [interleaveMarkers, bitAt]
  | b, b2 :: rest, 0 => rfl
  | b, b2 :: rest, i + 1 => by
    have h1 : 2 * (i + 1) = 2 * i + 2 := by omega
    rw [h1]
    change bitAt (interleaveMarkers (b2 :: rest)) (2 * i) = bitAt (b2 :: rest) i
    exact bitAt_interleave_even b2 rest i

private theorem bitAt_interleave_odd : ∀ (b : Bool) (bs : List Bool) (i : Nat),
    bitAt (interleaveMarkers (b :: bs)) (2 * i + 1) = false
  | b, [], 0 => rfl
  | b, [], i + 1 => by
    have h1 : 2 * (i + 1) + 1 = (2 * i + 2) + 1 := by omega
    rw [h1]
    simp [interleaveMarkers, bitAt]
  | b, b2 :: rest, 0 => rfl
  | b, b2 :: rest, i + 1 => by
    have h1 : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
    rw [h1]
    change bitAt (interleaveMarkers (b2 :: rest)) (2 * i + 1) = false
    exact bitAt_interleave_odd b2 rest i

theorem encodeMarkedWord_matches (w : List Bool) :
    MarkedTapeMatches w (encodeMarkedWord w) := by
  cases w with
  | nil =>
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact False.elim (by omega)
      | succ k =>
        have h2 : 2 * (k + 1) = (2 * k) + 2 := by omega
        rw [h2]
        simp [encodeMarkedWord, bitAt]
    · intro i
      cases i with
      | zero => rfl
      | succ k =>
        have h2 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
        rw [h2]
        simp [encodeMarkedWord, bitAt]
  | cons b bs =>
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact False.elim (by omega)
      | succ k =>
        have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
        rw [h2]
        change bitAt (interleaveMarkers (b :: bs)) (2 * k + 1) = false
        exact bitAt_interleave_odd b bs k
    · intro i
      change bitAt (interleaveMarkers (b :: bs)) (2 * i) = bitAt (b :: bs) i
      exact bitAt_interleave_even b bs i

theorem markedTape_write_same (srcTape normTape : List Bool) (pos : Nat)
    (hm : MarkedTapeMatches srcTape normTape) :
    MarkedTapeMatches srcTape (writeTapeList normTape pos (bitAt normTape pos)) := by
  have heq : ∀ k, bitAt (writeTapeList normTape pos (bitAt normTape pos)) k = bitAt normTape k := by
    intro k
    rw [bitAt_writeTapeList]
    by_cases hk : k = pos
    · subst hk; rw [if_pos rfl]
    · rw [if_neg hk]
  exact ⟨by rw [heq]; exact hm.1,
         fun i hi => by rw [heq]; exact hm.2.1 i hi,
         fun i => by rw [heq]; exact hm.2.2 i⟩

theorem markedTape_write_data (srcTape normTape : List Bool) (h : Nat) (val : Bool)
    (hm : MarkedTapeMatches srcTape normTape) :
    MarkedTapeMatches (writeTapeList srcTape h val) (writeTapeList normTape (2 * h + 1) val) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bitAt_writeTapeList, if_neg (by omega)]
    exact hm.1
  · intro i hi
    rw [bitAt_writeTapeList, if_neg (by omega)]
    exact hm.2.1 i hi
  · intro i
    rw [bitAt_writeTapeList, bitAt_writeTapeList]
    by_cases hih : i = h
    · subst hih
      rw [if_pos rfl, if_pos rfl]
    · have hne : 2 * i + 1 ≠ 2 * h + 1 := by omega
      rw [if_neg hne, if_neg hih]
      exact hm.2.2 i

/-! ## Auxiliary State Table & `normalizeSafe` -/

def definedActsAt (M : SourceTM) (q : Fin M.numStates) : List (SourceAct M.numStates) :=
  (match M.stepRule q false with | some a => [a] | none => []) ++
  (match M.stepRule q true  with | some a => [a] | none => [])

def definedActsUpTo (M : SourceTM) : Nat → List (SourceAct M.numStates)
  | 0 => []
  | q + 1 =>
    definedActsUpTo M q ++
      if h : q < M.numStates then definedActsAt M ⟨q, h⟩ else []

def definedActs (M : SourceTM) : List (SourceAct M.numStates) :=
  definedActsUpTo M M.numStates

def auxOffset (M : SourceTM) (q : Fin M.numStates) (b : Bool) : Nat :=
  (definedActsUpTo M q.val).length +
    match b, M.stepRule q false with
    | true, some _ => 1
    | _, _ => 0

def numNormStates (M : SourceTM) : Nat :=
  M.numStates + 2 + (definedActs M).length

theorem definedActsAt_length_le (M : SourceTM) (q : Fin M.numStates) :
    (definedActsAt M q).length ≤ 2 := by
  unfold definedActsAt
  cases M.stepRule q false <;> cases M.stepRule q true <;> simp

theorem definedActsUpTo_length_le (M : SourceTM) :
    ∀ n : Nat, (definedActsUpTo M n).length ≤ 2 * n
  | 0 => by simp [definedActsUpTo]
  | n + 1 => by
    have ih := definedActsUpTo_length_le M n
    unfold definedActsUpTo
    by_cases hn : n < M.numStates
    · rw [dif_pos hn, List.length_append]
      have h2 := definedActsAt_length_le M ⟨n, hn⟩
      omega
    · rw [dif_neg hn, List.length_append]
      simp only [List.length_nil]
      omega

theorem numNormStates_ge_3 (M : SourceTM) : numNormStates M ≥ 3 := by
  have hp := M.hpos
  unfold numNormStates
  omega

theorem numNormStates_le (M : SourceTM) : numNormStates M ≤ 3 * M.numStates + 2 := by
  have h := definedActsUpTo_length_le M M.numStates
  unfold numNormStates definedActs
  omega

private theorem definedActsUpTo_prefix_get (M : SourceTM) {k n : Nat} (hkn : k ≤ n)
    {i : Nat} (hi : i < (definedActsUpTo M k).length) :
    (definedActsUpTo M n)[i]? = (definedActsUpTo M k)[i]? ∧
    i < (definedActsUpTo M n).length := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨rfl, hi⟩
  | succ m ih =>
    by_cases hkm : k ≤ m
    · obtain ⟨heq, hlen⟩ := ih hkm
      have hstep1 : (definedActsUpTo M (m + 1))[i]? = (definedActsUpTo M m)[i]? := by
        change (definedActsUpTo M m ++
          if h : m < M.numStates then definedActsAt M ⟨m, h⟩ else [])[i]? =
          (definedActsUpTo M m)[i]?
        exact List.getElem?_append_left hlen
      have hstep2 : i < (definedActsUpTo M (m + 1)).length := by
        change i < (definedActsUpTo M m ++
          if h : m < M.numStates then definedActsAt M ⟨m, h⟩ else []).length
        rw [List.length_append]
        omega
      exact ⟨hstep1.trans heq, hstep2⟩
    · have hkeq : k = m + 1 := by omega
      subst hkeq
      exact ⟨rfl, hi⟩

private theorem definedActsUpTo_mono_length (M : SourceTM) {k n : Nat} (hkn : k ≤ n) :
    (definedActsUpTo M k).length ≤ (definedActsUpTo M n).length := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; exact Nat.le_refl _
  | succ m ih =>
    by_cases hkm : k ≤ m
    · have hm1 := ih hkm
      change (definedActsUpTo M k).length ≤
        (definedActsUpTo M m ++ if h : m < M.numStates then definedActsAt M ⟨m, h⟩ else []).length
      rw [List.length_append]
      omega
    · have hkeq : k = m + 1 := by omega
      subst hkeq; exact Nat.le_refl _

theorem auxOffset_le_length (M : SourceTM) (q : Fin M.numStates) (b : Bool) :
    auxOffset M q b ≤ (definedActs M).length := by
  have hstep : auxOffset M q b ≤ (definedActsUpTo M (q.val + 1)).length := by
    let xs := definedActsUpTo M q.val
    change auxOffset M q b ≤
      (xs ++ if h : q.val < M.numStates then definedActsAt M ⟨q.val, h⟩ else []).length
    rw [dif_pos q.isLt, List.length_append]
    unfold auxOffset definedActsAt
    cases b <;> cases M.stepRule q false <;> cases M.stepRule q true <;> simp [xs]
  exact Nat.le_trans hstep (definedActsUpTo_mono_length M (Nat.succ_le_of_lt q.isLt))

theorem auxOffset_spec (M : SourceTM) (q : Fin M.numStates) (b : Bool)
    (act : SourceAct M.numStates) (hr : M.stepRule q b = some act) :
    auxOffset M q b < (definedActs M).length ∧
    (definedActs M)[auxOffset M q b]? = some act := by
  have hstep : auxOffset M q b < (definedActsUpTo M (q.val + 1)).length ∧
      (definedActsUpTo M (q.val + 1))[auxOffset M q b]? = some act := by
    let xs := definedActsUpTo M q.val
    change auxOffset M q b < (xs ++ if h : q.val < M.numStates then definedActsAt M ⟨q.val, h⟩ else []).length ∧
           (xs ++ if h : q.val < M.numStates then definedActsAt M ⟨q.val, h⟩ else [])[auxOffset M q b]? = some act
    rw [dif_pos q.isLt]
    unfold auxOffset definedActsAt
    cases b with
    | false =>
      rw [hr]
      cases M.stepRule q true with
      | none =>
        dsimp only []
        refine ⟨by simp [xs, List.length_append], ?_⟩
        have hidx : xs.length + 0 = xs.length := Nat.add_zero _
        rw [hidx, List.getElem?_append_right (Nat.le_refl xs.length), Nat.sub_self]
        rfl
      | some a1 =>
        dsimp only []
        refine ⟨by simp [xs, List.length_append], ?_⟩
        have hidx : xs.length + 0 = xs.length := Nat.add_zero _
        rw [hidx, List.getElem?_append_right (Nat.le_refl xs.length), Nat.sub_self]
        rfl
    | true =>
      rw [hr]
      cases h0 : M.stepRule q false with
      | none =>
        dsimp only []
        refine ⟨by simp [xs, List.length_append], ?_⟩
        have hidx : xs.length + 0 = xs.length := Nat.add_zero _
        rw [hidx, List.getElem?_append_right (Nat.le_refl xs.length), Nat.sub_self]
        rfl
      | some a0 =>
        dsimp only []
        refine ⟨by simp [xs, List.length_append], ?_⟩
        rw [List.getElem?_append_right (by omega : xs.length ≤ xs.length + 1)]
        have hsub : xs.length + 1 - xs.length = 1 := by omega
        rw [hsub]
        rfl
  obtain ⟨heq, hlen⟩ := definedActsUpTo_prefix_get M (Nat.succ_le_of_lt q.isLt) hstep.1
  unfold definedActs
  exact ⟨hlen, heq.trans hstep.2⟩

def mkAuxNormAct (M : SourceTM) (act : SourceAct M.numStates) (bit : Bool) :
    NormAct (numNormStates M) :=
  let secondDir : NormDir :=
    match act.dir with
    | .left => if bit then .right else .left
    | .right => .right
    | .stay => .left
  have hnxt : act.next.val + 1 < numNormStates M := by
    have hlt := act.next.isLt
    unfold numNormStates
    omega
  ⟨bit, secondDir, ⟨act.next.val + 1, hnxt⟩⟩

def normSafeRule (M : SourceTM) (s : Fin (numNormStates M)) (bit : Bool) :
    NormAct (numNormStates M) :=
  have h3 := numNormStates_ge_3 M
  if hs0 : s.val = 0 then
    ⟨bit, .right, ⟨1, by omega⟩⟩
  else if hsSrc : s.val < M.numStates + 1 then
    let q : Fin M.numStates := ⟨s.val - 1, by omega⟩
    match M.stepRule q bit with
    | none => ⟨bit, .left, ⟨numNormStates M - 1, by omega⟩⟩
    | some act =>
      have haux := auxOffset_le_length M q bit
      let aIdx := M.numStates + 1 + auxOffset M q bit
      have haLt : aIdx < numNormStates M := by
        unfold numNormStates
        omega
      let firstDir : NormDir :=
        match act.dir with
        | .left => .left
        | .stay => .right
        | .right => .right
      ⟨act.write, firstDir, ⟨aIdx, haLt⟩⟩
  else if hsAux : s.val < M.numStates + 1 + (definedActs M).length then
    have hidx : s.val - (M.numStates + 1) < (definedActs M).length := by omega
    mkAuxNormAct M ((definedActs M)[s.val - (M.numStates + 1)]'hidx) bit
  else
    ⟨bit, .left, ⟨numNormStates M - 1, by omega⟩⟩

def normalizeSafeTM (M : SourceTM) : NormalizedTM where
  numStates := numNormStates M
  hge2 := by have h := numNormStates_ge_3 M; omega
  rule := normSafeRule M
  hfinal := by
    intro b
    have h3 := numNormStates_ge_3 M
    unfold normSafeRule
    have hne0 : numNormStates M - 1 ≠ 0 := by omega
    have hnot1 : ¬ (numNormStates M - 1 < M.numStates + 1) := by
      unfold numNormStates; omega
    have hnot2 : ¬ (numNormStates M - 1 < M.numStates + 1 + (definedActs M).length) := by
      unfold numNormStates; omega
    rw [dif_neg hne0, dif_neg hnot1, dif_neg hnot2]

@[simp] theorem normalizeSafeTM_numStates (M : SourceTM) :
    (normalizeSafeTM M).numStates = numNormStates M := rfl

@[simp] theorem normalizeSafeTM_rule (M : SourceTM) :
    (normalizeSafeTM M).rule = normSafeRule M := rfl

def normalizeSafe (M : SourceTM) (w : List Bool) : NormalizedTM × List Bool :=
  (normalizeSafeTM M, encodeMarkedWord w)

/-! ## Rule Characterization Lemmas (Constructive, No `split`) -/

theorem normSafeRule_zero (M : SourceTM) (s : Fin (numNormStates M)) (hs : s.val = 0) (bit : Bool) :
    normSafeRule M s bit = ⟨bit, .right, ⟨1, by have := numNormStates_ge_3 M; omega⟩⟩ := by
  unfold normSafeRule
  rw [dif_pos hs]

theorem normSafeRule_src_some (M : SourceTM) (s : Fin (numNormStates M))
    (hne0 : s.val ≠ 0) (hlt : s.val < M.numStates + 1) (bit : Bool)
    (act : SourceAct M.numStates)
    (hr : M.stepRule ⟨s.val - 1, by omega⟩ bit = some act) :
    normSafeRule M s bit =
      ⟨act.write,
       match act.dir with | .left => .left | .stay => .right | .right => .right,
       ⟨M.numStates + 1 + auxOffset M ⟨s.val - 1, by omega⟩ bit,
        by have := auxOffset_le_length M ⟨s.val - 1, by omega⟩ bit; unfold numNormStates; omega⟩⟩ := by
  unfold normSafeRule
  rw [dif_neg hne0, dif_pos hlt]
  dsimp only []
  rw [hr]

theorem normSafeRule_src_none (M : SourceTM) (s : Fin (numNormStates M))
    (hne0 : s.val ≠ 0) (hlt : s.val < M.numStates + 1) (bit : Bool)
    (hr : M.stepRule ⟨s.val - 1, by omega⟩ bit = none) :
    normSafeRule M s bit =
      ⟨bit, .left, ⟨numNormStates M - 1, by have := numNormStates_ge_3 M; omega⟩⟩ := by
  unfold normSafeRule
  rw [dif_neg hne0, dif_pos hlt]
  dsimp only []
  rw [hr]

private theorem getElem_eq_of_getElem? {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) (v : α) (h : xs[i]? = some v) : xs[i]'hi = v := by
  rw [List.getElem?_eq_getElem hi] at h
  injection h

theorem normSafeRule_aux (M : SourceTM) (s : Fin (numNormStates M))
    (hne0 : s.val ≠ 0) (hnot1 : ¬ (s.val < M.numStates + 1))
    (hlt2 : s.val < M.numStates + 1 + (definedActs M).length)
    (act : SourceAct M.numStates)
    (hget : (definedActs M)[s.val - (M.numStates + 1)]? = some act)
    (mbit : Bool) :
    normSafeRule M s mbit = mkAuxNormAct M act mbit := by
  unfold normSafeRule
  rw [dif_neg hne0, dif_neg hnot1, dif_pos hlt2]
  dsimp only []
  have helem : (definedActs M)[s.val - (M.numStates + 1)]'(by omega) = act :=
    getElem_eq_of_getElem? (definedActs M) _ _ act hget
  exact congrArg (fun a => mkAuxNormAct M a mbit) helem

theorem normSafeRule_halt (M : SourceTM) (s : Fin (numNormStates M))
    (hs : s.val = numNormStates M - 1) (bit : Bool) :
    normSafeRule M s bit =
      ⟨bit, .left, ⟨numNormStates M - 1, by have := numNormStates_ge_3 M; omega⟩⟩ := by
  have h3 := numNormStates_ge_3 M
  unfold normSafeRule
  rw [dif_neg (by omega), dif_neg (by unfold numNormStates at hs; omega),
      dif_neg (by unfold numNormStates at hs; omega)]

/-! ## Step & Multi-Step Simulation Proofs -/

def NormMatchesSource (M : SourceTM) (sc : SourceConfig M.numStates)
    (nc : NormConfig (normalizeSafeTM M).numStates) : Prop :=
  nc.state.val = sc.state.val + 1 ∧
  nc.head = 2 * sc.head + 1 ∧
  MarkedTapeMatches sc.tape nc.tape

theorem normalizeSafe_init_step (M : SourceTM) (w : List Bool) :
    ∃ c1, NormRun (normalizeSafeTM M) 1
        (initNormConfig (normalizeSafeTM M) (encodeMarkedWord w)) c1 ∧
      NormMatchesSource M (initSourceConfig M w) c1 := by
  let mw := encodeMarkedWord w
  have hm := encodeMarkedWord_matches w
  let c0 := initNormConfig (normalizeSafeTM M) mw
  have hrule : (normalizeSafeTM M).rule c0.state (bitAt c0.tape c0.head) =
      ⟨bitAt mw 0, .right, ⟨1, by have := numNormStates_ge_3 M; change 1 < numNormStates M; omega⟩⟩ :=
    normSafeRule_zero M c0.state rfl (bitAt mw 0)
  let c1 : NormConfig (normalizeSafeTM M).numStates :=
    ⟨⟨1, by have := numNormStates_ge_3 M; change 1 < numNormStates M; omega⟩,
     1, writeTapeList mw 0 (bitAt mw 0)⟩
  have hstep : normStepSafe (normalizeSafeTM M) c0 = some c1 := by
    unfold normStepSafe
    rw [hrule]
    rfl
  exact ⟨c1, NormRun.next hstep (NormRun.zero c1),
         ⟨rfl, rfl, markedTape_write_same w mw 0 hm⟩⟩

theorem normalizeSafe_defined_two_steps (M : SourceTM)
    {sc sc' : SourceConfig M.numStates} {nc : NormConfig (normalizeSafeTM M).numStates}
    (hmatch : NormMatchesSource M sc nc)
    (hsrc : sourceStep M sc = some sc') :
    ∃ mid nc',
      normStepSafe (normalizeSafeTM M) nc = some mid ∧
      mid.state.val < (normalizeSafeTM M).numStates - 1 ∧
      normStepSafe (normalizeSafeTM M) mid = some nc' ∧
      NormMatchesSource M sc' nc' := by
  obtain ⟨hst, hhd, hm⟩ := hmatch
  unfold sourceStep at hsrc
  cases hr : M.stepRule sc.state (bitAt sc.tape sc.head) with
  | none => rw [hr] at hsrc; cases hsrc
  | some act =>
    rw [hr] at hsrc
    injection hsrc with hsc'
    subst hsc'
    have hbit : bitAt nc.tape nc.head = bitAt sc.tape sc.head := by
      rw [hhd]; exact hm.2.2 sc.head
    have hne0 : nc.state.val ≠ 0 := by omega
    have hlt1 : nc.state.val < M.numStates + 1 := by have := sc.state.isLt; omega
    have hq_eq : (⟨nc.state.val - 1, by omega⟩ : Fin M.numStates) = sc.state := by
      apply Fin.ext; dsimp; omega
    have hr' : M.stepRule ⟨nc.state.val - 1, by omega⟩ (bitAt nc.tape nc.head) = some act := by
      rw [hq_eq, hbit]; exact hr
    have hspec := auxOffset_spec M sc.state (bitAt sc.tape sc.head) act hr
    have haux_eq : auxOffset M ⟨nc.state.val - 1, by omega⟩ (bitAt nc.tape nc.head) =
        auxOffset M sc.state (bitAt sc.tape sc.head) := by
      rw [hq_eq, hbit]
    let aIdx := M.numStates + 1 + auxOffset M sc.state (bitAt sc.tape sc.head)
    have haLt : aIdx < (normalizeSafeTM M).numStates := by
      change aIdx < numNormStates M; unfold numNormStates; have := hspec.1; omega
    let aState : Fin (normalizeSafeTM M).numStates := ⟨aIdx, haLt⟩
    have hrule1 : (normalizeSafeTM M).rule nc.state (bitAt nc.tape nc.head) =
        ⟨act.write,
         match act.dir with | .left => .left | .stay => .right | .right => .right,
         aState⟩ := by
      have h0 := normSafeRule_src_some M nc.state hne0 hlt1 (bitAt nc.tape nc.head) act hr'
      have hfin : (⟨M.numStates + 1 + auxOffset M ⟨nc.state.val - 1, by omega⟩ (bitAt nc.tape nc.head),
          by have := auxOffset_le_length M ⟨nc.state.val - 1, by omega⟩ (bitAt nc.tape nc.head); unfold numNormStates; omega⟩ :
          Fin (numNormStates M)) = aState := by
        apply Fin.ext; dsimp [aState, aIdx]; exact congrArg (M.numStates + 1 + ·) haux_eq
      rw [← hfin]
      exact h0
    have hnxtLt : act.next.val + 1 < numNormStates M := by
      have := act.next.isLt; unfold numNormStates; omega
    let nxtState : Fin (normalizeSafeTM M).numStates := ⟨act.next.val + 1, hnxtLt⟩
    have hrule2 : ∀ mbit : Bool, (normalizeSafeTM M).rule aState mbit =
        ⟨mbit,
         match act.dir with
         | .left => if mbit then .right else .left
         | .right => .right
         | .stay => .left,
         nxtState⟩ := by
      intro mbit
      apply normSafeRule_aux M aState (by dsimp [aState, aIdx]; omega)
        (by dsimp [aState, aIdx]; omega)
        (by dsimp [aState, aIdx]; have := hspec.1; omega) act
      have hsub : aState.val - (M.numStates + 1) = auxOffset M sc.state (bitAt sc.tape sc.head) := by
        dsimp [aState, aIdx]; omega
      rw [hsub]; exact hspec.2
    have hnc_pos : nc.head ≠ 0 := by omega
    have hm1 : MarkedTapeMatches (writeTapeList sc.tape sc.head act.write)
        (writeTapeList nc.tape nc.head act.write) := by
      rw [hhd]; exact markedTape_write_data sc.tape nc.tape sc.head act.write hm
    have haNonFinal : aState.val < (normalizeSafeTM M).numStates - 1 := by
      change aIdx < numNormStates M - 1; unfold numNormStates; have := hspec.1; omega
    let tape1 := writeTapeList nc.tape nc.head act.write
    cases hdir : act.dir with
    | right =>
      let mid : NormConfig (normalizeSafeTM M).numStates := ⟨aState, nc.head + 1, tape1⟩
      have hs1 : normStepSafe (normalizeSafeTM M) nc = some mid := by
        unfold normStepSafe; rw [hrule1, hdir]
      let nc' : NormConfig (normalizeSafeTM M).numStates :=
        ⟨nxtState, mid.head + 1, writeTapeList tape1 mid.head (bitAt tape1 mid.head)⟩
      have hs2 : normStepSafe (normalizeSafeTM M) mid = some nc' := by
        unfold normStepSafe; rw [hrule2 (bitAt tape1 mid.head), hdir]
      refine ⟨mid, nc', hs1, haNonFinal, hs2, ⟨rfl, ?_, markedTape_write_same _ tape1 mid.head hm1⟩⟩
      change nc.head + 1 + 1 = 2 * (sc.head + 1) + 1
      omega
    | stay =>
      let mid : NormConfig (normalizeSafeTM M).numStates := ⟨aState, nc.head + 1, tape1⟩
      have hs1 : normStepSafe (normalizeSafeTM M) nc = some mid := by
        unfold normStepSafe; rw [hrule1, hdir]
      have hmid_ne0 : mid.head ≠ 0 := by dsimp [mid]; omega
      let nc' : NormConfig (normalizeSafeTM M).numStates :=
        ⟨nxtState, mid.head - 1, writeTapeList tape1 mid.head (bitAt tape1 mid.head)⟩
      have hs2 : normStepSafe (normalizeSafeTM M) mid = some nc' := by
        unfold normStepSafe
        rw [hrule2 (bitAt tape1 mid.head), hdir]
        dsimp only []
        rw [if_neg hmid_ne0]
      refine ⟨mid, nc', hs1, haNonFinal, hs2, ⟨rfl, ?_, markedTape_write_same _ tape1 mid.head hm1⟩⟩
      change nc.head + 1 - 1 = 2 * sc.head + 1
      omega
    | left =>
      let mid : NormConfig (normalizeSafeTM M).numStates := ⟨aState, nc.head - 1, tape1⟩
      have hs1 : normStepSafe (normalizeSafeTM M) nc = some mid := by
        unfold normStepSafe
        rw [hrule1, hdir]
        dsimp only []
        rw [if_neg hnc_pos]
      have hmid_eq : mid.head = 2 * sc.head := by dsimp [mid]; omega
      by_cases hh0 : sc.head = 0
      · have hm0 : bitAt tape1 mid.head = true := by
          rw [hmid_eq, hh0]; exact hm1.1
        let nc' : NormConfig (normalizeSafeTM M).numStates :=
          ⟨nxtState, mid.head + 1, writeTapeList tape1 mid.head (bitAt tape1 mid.head)⟩
        have hs2 : normStepSafe (normalizeSafeTM M) mid = some nc' := by
          unfold normStepSafe
          change (match ((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).dir with
            | .left => if mid.head = 0 then none else some ⟨((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).next,
                mid.head - 1, writeTapeList tape1 mid.head ((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).write⟩
            | .right => some ⟨((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).next,
                mid.head + 1, writeTapeList tape1 mid.head ((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).write⟩) = some nc'
          rw [hrule2 (bitAt tape1 mid.head), hdir]
          dsimp only []
          rw [if_pos hm0]
        refine ⟨mid, nc', hs1, haNonFinal, hs2, ⟨rfl, ?_, markedTape_write_same _ tape1 mid.head hm1⟩⟩
        change nc.head - 1 + 1 = 2 * (sc.head - 1) + 1
        omega
      · have hm_false : bitAt tape1 mid.head = false := by
          rw [hmid_eq]; exact hm1.2.1 sc.head (by omega)
        have hmid_ne0 : mid.head ≠ 0 := by omega
        let nc' : NormConfig (normalizeSafeTM M).numStates :=
          ⟨nxtState, mid.head - 1, writeTapeList tape1 mid.head (bitAt tape1 mid.head)⟩
        have hs2 : normStepSafe (normalizeSafeTM M) mid = some nc' := by
          unfold normStepSafe
          change (match ((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).dir with
            | .left => if mid.head = 0 then none else some ⟨((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).next,
                mid.head - 1, writeTapeList tape1 mid.head ((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).write⟩
            | .right => some ⟨((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).next,
                mid.head + 1, writeTapeList tape1 mid.head ((normalizeSafeTM M).rule aState (bitAt tape1 mid.head)).write⟩) = some nc'
          rw [hrule2 (bitAt tape1 mid.head), hdir]
          dsimp only []
          rw [if_neg (by rw [hm_false]; exact Bool.false_ne_true), if_neg hmid_ne0]
        refine ⟨mid, nc', hs1, haNonFinal, hs2, ⟨rfl, ?_, markedTape_write_same _ tape1 mid.head hm1⟩⟩
        change nc.head - 1 - 1 = 2 * (sc.head - 1) + 1
        omega

theorem normalizeSafe_run_sim (M : SourceTM) {t : Nat}
    {sc sc' : SourceConfig M.numStates} {nc : NormConfig (normalizeSafeTM M).numStates}
    (hrun : SourceTMRun M t sc sc')
    (hmatch : NormMatchesSource M sc nc) :
    ∃ nc', NormRun (normalizeSafeTM M) (2 * t) nc nc' ∧ NormMatchesSource M sc' nc' := by
  induction hrun generalizing nc with
  | zero _ => exact ⟨nc, NormRun.zero nc, hmatch⟩
  | @next k a b c hs rest ih =>
    obtain ⟨mid, nc1, hs1, _, hs2, hm1⟩ := normalizeSafe_defined_two_steps M hmatch hs
    obtain ⟨nc', hrest, hm'⟩ := ih hm1
    have h2 : NormRun (normalizeSafeTM M) 2 nc nc1 :=
      NormRun.next hs1 (NormRun.next hs2 (NormRun.zero nc1))
    have hcomb := normRun_trans h2 hrest
    refine ⟨nc', ?_, hm'⟩
    have heq : 2 + 2 * k = 2 * (k + 1) := by omega
    rwa [heq] at hcomb

theorem normalizeSafe_multi_step_from_init (M : SourceTM) (w : List Bool)
    {t : Nat} {sc : SourceConfig M.numStates}
    (hrun : SourceTMRun M t (initSourceConfig M w) sc) :
    ∃ nc, NormRun (normalizeSafeTM M) (1 + 2 * t)
        (initNormConfig (normalizeSafeTM M) (encodeMarkedWord w)) nc ∧
      NormMatchesSource M sc nc := by
  obtain ⟨c1, hr1, hm1⟩ := normalizeSafe_init_step M w
  obtain ⟨nc, hr2, hm2⟩ := normalizeSafe_run_sim M hrun hm1
  exact ⟨nc, normRun_trans hr1 hr2, hm2⟩

private theorem haltState_walk_left (M : SourceTM) (srcTape : List Bool) :
    ∀ (k : Nat) (tape : List Bool),
      MarkedTapeMatches srcTape tape →
      ∃ final,
        NormRun (normalizeSafeTM M) k
          ⟨⟨numNormStates M - 1, by have := numNormStates_ge_3 M; change numNormStates M - 1 < numNormStates M; omega⟩,
           k, tape⟩ final ∧
        final.state.val = numNormStates M - 1 ∧
        final.head = 0 ∧
        MarkedTapeMatches srcTape final.tape ∧
        normStepSafe (normalizeSafeTM M) final = none := by
  intro k
  let hst : Fin (normalizeSafeTM M).numStates :=
    ⟨numNormStates M - 1, by have := numNormStates_ge_3 M; change numNormStates M - 1 < numNormStates M; omega⟩
  induction k with
  | zero =>
    intro tape hm
    let fin : NormConfig (normalizeSafeTM M).numStates := ⟨hst, 0, tape⟩
    have hrule : (normalizeSafeTM M).rule hst (bitAt tape 0) = ⟨bitAt tape 0, .left, hst⟩ :=
      normSafeRule_halt M hst rfl (bitAt tape 0)
    have hstop : normStepSafe (normalizeSafeTM M) fin = none := by
      unfold normStepSafe
      change (match ((normalizeSafeTM M).rule hst (bitAt tape 0)).dir with
        | .left => if (0 : Nat) = 0 then none else _
        | .right => _) = none
      rw [hrule]
      rfl
    exact ⟨fin, NormRun.zero fin, rfl, rfl, hm, hstop⟩
  | succ j ih =>
    intro tape hm
    let curr : NormConfig (normalizeSafeTM M).numStates := ⟨hst, j + 1, tape⟩
    let nxt : NormConfig (normalizeSafeTM M).numStates :=
      ⟨hst, j, writeTapeList tape (j + 1) (bitAt tape (j + 1))⟩
    have hrule : (normalizeSafeTM M).rule hst (bitAt tape (j + 1)) = ⟨bitAt tape (j + 1), .left, hst⟩ :=
      normSafeRule_halt M hst rfl (bitAt tape (j + 1))
    have hs : normStepSafe (normalizeSafeTM M) curr = some nxt := by
      unfold normStepSafe
      change (match ((normalizeSafeTM M).rule hst (bitAt tape (j + 1))).dir with
        | .left => if j + 1 = 0 then none else some ⟨((normalizeSafeTM M).rule hst (bitAt tape (j + 1))).next,
            (j + 1) - 1, writeTapeList tape (j + 1) ((normalizeSafeTM M).rule hst (bitAt tape (j + 1))).write⟩
        | .right => _) = some nxt
      rw [hrule]
      dsimp only []
      rw [if_neg (Nat.succ_ne_zero j)]
      rfl
    have hm_nxt := markedTape_write_same srcTape tape (j + 1) hm
    obtain ⟨fin, hrun, hstF, hhdF, hm_fin, hstop⟩ := ih _ hm_nxt
    exact ⟨fin, NormRun.next hs hrun, hstF, hhdF, hm_fin, hstop⟩

theorem normalizeSafe_undefined_halts_walk (M : SourceTM)
    {sc : SourceConfig M.numStates} {nc : NormConfig (normalizeSafeTM M).numStates}
    (hmatch : NormMatchesSource M sc nc)
    (hstopSrc : sourceStep M sc = none) :
    ∃ normFinal,
      NormRun (normalizeSafeTM M) (1 + 2 * sc.head) nc normFinal ∧
      normFinal.state.val = numNormStates M - 1 ∧
      normFinal.head = 0 ∧
      MarkedTapeMatches sc.tape normFinal.tape ∧
      normStepSafe (normalizeSafeTM M) normFinal = none := by
  obtain ⟨hst, hhd, hm⟩ := hmatch
  have hrNone : M.stepRule sc.state (bitAt sc.tape sc.head) = none :=
    (sourceStep_none_iff M sc).mp hstopSrc
  have hbit : bitAt nc.tape nc.head = bitAt sc.tape sc.head := by
    rw [hhd]; exact hm.2.2 sc.head
  have hne0 : nc.state.val ≠ 0 := by omega
  have hlt1 : nc.state.val < M.numStates + 1 := by have := sc.state.isLt; omega
  have hq_eq : (⟨nc.state.val - 1, by omega⟩ : Fin M.numStates) = sc.state := by
    apply Fin.ext; dsimp; omega
  have hrNone' : M.stepRule ⟨nc.state.val - 1, by omega⟩ (bitAt nc.tape nc.head) = none := by
    rw [hq_eq, hbit]; exact hrNone
  let hstFin : Fin (normalizeSafeTM M).numStates :=
    ⟨numNormStates M - 1, by have := numNormStates_ge_3 M; change numNormStates M - 1 < numNormStates M; omega⟩
  have hrule : (normalizeSafeTM M).rule nc.state (bitAt nc.tape nc.head) =
      ⟨bitAt nc.tape nc.head, .left, hstFin⟩ :=
    normSafeRule_src_none M nc.state hne0 hlt1 (bitAt nc.tape nc.head) hrNone'
  have hnc_pos : nc.head ≠ 0 := by omega
  let mid : NormConfig (normalizeSafeTM M).numStates :=
    ⟨hstFin, 2 * sc.head, writeTapeList nc.tape nc.head (bitAt nc.tape nc.head)⟩
  have hs1 : normStepSafe (normalizeSafeTM M) nc = some mid := by
    unfold normStepSafe
    rw [hrule]
    dsimp only []
    rw [if_neg hnc_pos]
    have hsub : nc.head - 1 = 2 * sc.head := by omega
    rw [hsub]
  have hm_mid := markedTape_write_same sc.tape nc.tape nc.head hm
  obtain ⟨fin, hwalk, hfinSt, hfinHd, hm_fin, hstopFin⟩ :=
    haltState_walk_left M sc.tape (2 * sc.head) _ hm_mid
  have htot : NormRun (normalizeSafeTM M) (1 + 2 * sc.head) nc fin := by
    have r := NormRun.next hs1 hwalk
    have heq : 2 * sc.head + 1 = 1 + 2 * sc.head := by omega
    rwa [heq] at r
  exact ⟨fin, htot, hfinSt, hfinHd, hm_fin, hstopFin⟩

theorem source_halt_to_norm_exit (M : SourceTM) (w : List Bool)
    {t : Nat} {srcFinal : SourceConfig M.numStates}
    (hrun : SourceTMRun M t (initSourceConfig M w) srcFinal)
    (hstop : sourceStep M srcFinal = none) :
    ∃ normFinal,
      NormRun (normalizeSafeTM M) (1 + 2 * t + (1 + 2 * srcFinal.head))
        (initNormConfig (normalizeSafeTM M) (encodeMarkedWord w)) normFinal ∧
      normFinal.state.val = numNormStates M - 1 ∧
      normFinal.head = 0 ∧
      MarkedTapeMatches srcFinal.tape normFinal.tape ∧
      normStepSafe (normalizeSafeTM M) normFinal = none := by
  obtain ⟨nc, hr1, hm1⟩ := normalizeSafe_multi_step_from_init M w hrun
  obtain ⟨normFinal, hr2, hst, hhd, hmFin, hstopFin⟩ :=
    normalizeSafe_undefined_halts_walk M hm1 hstop
  exact ⟨normFinal, normRun_trans hr1 hr2, hst, hhd, hmFin, hstopFin⟩

private theorem normRun_prefix_defined {N : NormalizedTM} {m k : Nat}
    {a b c : NormConfig N.numStates}
    (hmk : m < k) (rm : NormRun N m a b) (rk : NormRun N k a c) :
    normStepSafe N b ≠ none := by
  intro hnone
  have hle := normRun_no_extend_after_stop rm hnone rk
  omega

/-- No reachable non-final normalized configuration ever attempts a left move from cell `0`. -/
theorem normalizeSafe_nonfinal_never_exits_left (M : SourceTM) (w : List Bool)
    {m : Nat} {nc : NormConfig (normalizeSafeTM M).numStates}
    (hrun : NormRun (normalizeSafeTM M) m
      (initNormConfig (normalizeSafeTM M) (encodeMarkedWord w)) nc)
    (hnonfinal : nc.state.val ≠ (normalizeSafeTM M).numStates - 1) :
    normStepSafe (normalizeSafeTM M) nc ≠ none := by
  cases evalSourceBounded M (initSourceConfig M w) m with
  | running srcCurr hsrcRun =>
    obtain ⟨ncFuture, hnormFuture, _⟩ := normalizeSafe_multi_step_from_init M w hsrcRun
    exact normRun_prefix_defined (by omega) hrun hnormFuture
  | halted t _ srcFinal hsrcRun hsrcStop =>
    obtain ⟨normFinal, hnormExit, hfinSt, _, _, hfinStop⟩ :=
      source_halt_to_norm_exit M w hsrcRun hsrcStop
    have hle := normRun_no_extend_after_stop hnormExit hfinStop hrun
    by_cases hlt : m < 1 + 2 * t + (1 + 2 * srcFinal.head)
    · exact normRun_prefix_defined hlt hrun hnormExit
    · have heq : m = 1 + 2 * t + (1 + 2 * srcFinal.head) := by omega
      subst heq
      have hsame := normRun_deterministic hrun hnormExit
      subst hsame
      exact False.elim (hnonfinal hfinSt)

/-- Constructive exit-to-source-halt theorem with terminal odd-cell tape preservation. -/
theorem norm_exit_to_source_halt (M : SourceTM) (w : List Bool)
    {m : Nat} {normFinal : NormConfig (normalizeSafeTM M).numStates}
    (hrun : NormRun (normalizeSafeTM M) m
      (initNormConfig (normalizeSafeTM M) (encodeMarkedWord w)) normFinal)
    (hstop : normStepSafe (normalizeSafeTM M) normFinal = none) :
    ∃ t srcFinal,
      t ≤ m ∧
      SourceTMRun M t (initSourceConfig M w) srcFinal ∧
      sourceStep M srcFinal = none ∧
      normFinal.state.val = numNormStates M - 1 ∧
      normFinal.head = 0 ∧
      MarkedTapeMatches srcFinal.tape normFinal.tape := by
  cases evalSourceBounded M (initSourceConfig M w) m with
  | running srcCurr hsrcRun =>
    obtain ⟨ncFuture, hnormFuture, _⟩ := normalizeSafe_multi_step_from_init M w hsrcRun
    have hle := normRun_no_extend_after_stop hrun hstop hnormFuture
    exact False.elim (by omega)
  | halted t hle srcFinal hsrcRun hsrcStop =>
    obtain ⟨nf2, hnorm2, hst2, hhd2, hm2, hstop2⟩ :=
      source_halt_to_norm_exit M w hsrcRun hsrcStop
    obtain ⟨_, hsame⟩ := normRun_halt_unique hrun hstop hnorm2 hstop2
    subst hsame
    exact ⟨t, srcFinal, hle, hsrcRun, hsrcStop, hst2, hhd2, hm2⟩

theorem source_halts_iff_norm_exits (M : SourceTM) (w : List Bool) :
    SourceEventuallyStopsTM M w ↔
      NormEventuallyExits (normalizeSafeTM M) (encodeMarkedWord w) := by
  constructor
  · intro ⟨t, srcFinal, hrun, hstop⟩
    obtain ⟨normFinal, hnormRun, _, _, _, hnormStop⟩ :=
      source_halt_to_norm_exit M w hrun hstop
    exact ⟨_, normFinal, hnormRun, hnormStop⟩
  · intro ⟨m, normFinal, hrun, hstop⟩
    obtain ⟨t, srcFinal, _, hsrcRun, hsrcStop, _, _, _⟩ :=
      norm_exit_to_source_halt M w hrun hstop
    exact ⟨t, srcFinal, hsrcRun, hsrcStop⟩

/-! ## Concrete `#guard` Cross-Checks against `normalize_neary_safe.py` -/

private def sampleTM1 : SourceTM where
  numStates := 2
  hpos := by decide
  stepRule := fun q b =>
    if q.val = 0 && !b then some ⟨true, .stay, ⟨1, by decide⟩⟩ else none

private def sampleTM3 : SourceTM where
  numStates := 2
  hpos := by decide
  stepRule := fun q b =>
    if q.val = 0 && !b then some ⟨true, .right, ⟨1, by decide⟩⟩
    else if q.val = 1 && !b then some ⟨true, .left, ⟨0, by decide⟩⟩
    else none

#guard (normalizeSafe sampleTM1 [false, true]).1.numStates == 5
#guard (normalizeSafe sampleTM1 [false, true]).2 == [true, false, false, true]
#guard (normalizeSafe sampleTM1 []).2 == [true, false]
#guard (normalizeSafe sampleTM3 []).1.numStates == 6

#print axioms encodeMarkedWord_matches
#print axioms normalizeSafe_nonfinal_never_exits_left
#print axioms norm_exit_to_source_halt
#print axioms source_halts_iff_norm_exits
