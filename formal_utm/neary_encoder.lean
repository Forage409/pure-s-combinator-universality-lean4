import formal_utm.marked_normalizer

/-!
# Neary `U(3,11)` Universal Input Encoder, Output Decoder, and Polynomial Bound

Formalizes `neary_u3_11.py` (`encode_source`) and `neary_output_reader.py`
(`decode_halted_output`), cross-checked byte-for-byte against Python test cases
via `#guard`, together with explicit `O(M.numStates^2 + w.length)` tape size bounds
and right-padding equivalence (`UConfigEq`) for `UConfig`.
-/

abbrev symLA     : Fin 11 := 0
abbrev symLB     : Fin 11 := 1
abbrev symE      : Fin 11 := 2
abbrev symH      : Fin 11 := 3
abbrev symRE     : Fin 11 := 4
abbrev symRH     : Fin 11 := 5
abbrev symLE     : Fin 11 := 6
abbrev symLH     : Fin 11 := 7
abbrev symLAMBDA : Fin 11 := 8
abbrev symDELTA  : Fin 11 := 9
abbrev symGAMMA  : Fin 11 := 10

abbrev stateU1 : Fin 3 := 0
abbrev stateU2 : Fin 3 := 1
abbrev stateU3 : Fin 3 := 2

/-! ## Infinite Blank-`LA` Suffix Equivalence on `UConfig` -/

def uSymAt : List (Fin 11) → Nat → Fin 11
  | [], _ => symLA
  | s :: _, 0 => s
  | _ :: rest, n + 1 => uSymAt rest n

def URightEq (a b : List (Fin 11)) : Prop := ∀ i, uSymAt a i = uSymAt b i

theorem uRightEq_refl (a : List (Fin 11)) : URightEq a a := fun _ => rfl
theorem uRightEq_symm {a b : List (Fin 11)} (h : URightEq a b) : URightEq b a := fun i => (h i).symm
theorem uRightEq_trans {a b c : List (Fin 11)} (h1 : URightEq a b) (h2 : URightEq b c) : URightEq a c :=
  fun i => (h1 i).trans (h2 i)

theorem uSymAt_replicate_LA (k i : Nat) : uSymAt (List.replicate k symLA) i = symLA := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j

theorem uRightEq_cons {a b : List (Fin 11)} (x : Fin 11) (h : URightEq a b) :
    URightEq (x :: a) (x :: b) := by
  intro i
  cases i with
  | zero => rfl
  | succ j => exact h j

theorem uRightEq_pad (xs : List (Fin 11)) (k : Nat) :
    URightEq xs (xs ++ List.replicate k symLA) := by
  induction xs with
  | nil =>
    intro i
    simpa [uSymAt] using (uSymAt_replicate_LA k i).symm
  | cons x rest ih =>
    simpa using uRightEq_cons x ih

def UConfigEq (a b : UConfig) : Prop :=
  a.leftRev = b.leftRev ∧ a.symbol = b.symbol ∧ a.state = b.state ∧ URightEq a.right b.right

theorem uConfigEq_refl (u : UConfig) : UConfigEq u u := ⟨rfl, rfl, rfl, uRightEq_refl _⟩
theorem uConfigEq_symm {a b : UConfig} (h : UConfigEq a b) : UConfigEq b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, uRightEq_symm h.2.2.2⟩
theorem uConfigEq_trans {a b c : UConfig} (h1 : UConfigEq a b) (h2 : UConfigEq b c) : UConfigEq a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, uRightEq_trans h1.2.2.2 h2.2.2.2⟩

theorem uNext_respects_equiv {a b : UConfig} (h : UConfigEq a b) :
    match uNext a, uNext b with
    | none, none => True
    | some a', some b' => UConfigEq a' b'
    | _, _ => False := by
  cases a with
  | mk la sa ra qa =>
    cases b with
    | mk lb sb rb qb =>
      obtain ⟨hl, hs, hq, hr⟩ := h
      dsimp at hl hs hq hr
      subst hl; subst hs; subst hq
      unfold uNext
      dsimp only []
      cases hprog : fixedUProgram qa sa with
      | none => trivial
      | some inst =>
        dsimp only []
        cases hdir : inst.direction with
        | stay => dsimp only []; exact ⟨rfl, rfl, rfl, hr⟩
        | left =>
          dsimp only []
          cases la with
          | nil => dsimp only []; exact ⟨rfl, rfl, rfl, hr⟩
          | cons prev rest => dsimp only []; exact ⟨rfl, rfl, rfl, uRightEq_cons inst.write hr⟩
        | right =>
          dsimp only []
          cases ra with
          | nil =>
            cases rb with
            | nil => dsimp only []; exact ⟨rfl, rfl, rfl, uRightEq_refl []⟩
            | cons y ys =>
              dsimp only []
              have hy : symLA = y := hr 0
              have htail : URightEq [] ys := fun i => hr (i + 1)
              exact ⟨rfl, hy, rfl, htail⟩
          | cons x xs =>
            cases rb with
            | nil =>
              dsimp only []
              have hx : x = symLA := hr 0
              have htail : URightEq xs [] := fun i => hr (i + 1)
              exact ⟨rfl, hx, rfl, htail⟩
            | cons y ys =>
              dsimp only []
              have hxy : x = y := hr 0
              have htail : URightEq xs ys := fun i => hr (i + 1)
              exact ⟨rfl, hxy, rfl, htail⟩

theorem uRun_equiv_forward {n : Nat} {a b : UConfig} (run : URun n a b) :
    ∀ a', UConfigEq a a' → ∃ b', URun n a' b' ∧ UConfigEq b b' := by
  induction run with
  | zero _ => intro a' heq; exact ⟨a', URun.zero a', heq⟩
  | @next k x y z hs rest ih =>
    intro x' heq
    have hstep := uNext_respects_equiv heq
    rw [hs] at hstep
    cases hs' : uNext x' with
    | none => rw [hs'] at hstep; cases hstep
    | some y' =>
      rw [hs'] at hstep
      obtain ⟨z', hrun', heq'⟩ := ih y' hstep
      exact ⟨z', URun.next hs' hrun', heq'⟩

theorem uNext_none_of_equiv {a b : UConfig} (h : UConfigEq a b) (hnone : uNext a = none) :
    uNext b = none := by
  have hs := uNext_respects_equiv h
  rw [hnone] at hs
  cases hb : uNext b with
  | none => rfl
  | some _ => rw [hb] at hs; cases hs

/-! ## Neary Equations (3.3.1)–(3.3.5) & `encodeNormalizedToU` -/

def nearyB {S : Nat} (act : NormAct S) : Nat :=
  2 + 5 * act.next.val + (match act.dir with | .left => 3 | .right => 0)

def nearyA (S : Nat) (act : NormAct S) : Nat :=
  5 * S + 2 - nearyB act

def nearyETR (S : Nat) (act : NormAct S) : List (Fin 11) :=
  let b := nearyB act
  let a := nearyA S act
  match act.dir with
  | .right =>
    (if act.write then [symH] else []) ++
      List.replicate a symE ++ List.replicate b symH
  | .left =>
    List.replicate (a - 1) symE ++ List.replicate b symH ++
      (if act.write then [symE, symH, symE] else [symE, symE, symE])

def hasIncomingRightFrom (N : NormalizedTM) (q : Fin N.numStates) : Nat → Bool
  | 0 => false
  | k + 1 =>
    hasIncomingRightFrom N q k ||
      if hk : k < N.numStates then
        let t0 := N.rule ⟨k, hk⟩ false
        let t1 := N.rule ⟨k, hk⟩ true
        (decide (t0.next.val = q.val) && decide (t0.dir = .right)) ||
        (decide (t1.next.val = q.val) && decide (t1.dir = .right))
      else false

def hasIncomingRight (N : NormalizedTM) (q : Fin N.numStates) : Bool :=
  hasIncomingRightFrom N q N.numStates

private theorem hasIncomingRightFrom_of_witness (N : NormalizedTM) (p q : Fin N.numStates) (bit : Bool)
    (hnext : (N.rule p bit).next = q) (hdir : (N.rule p bit).dir = .right) :
    ∀ n, p.val < n → hasIncomingRightFrom N q n = true
  | 0, hlt => False.elim (Nat.not_lt_zero _ hlt)
  | k + 1, hlt => by
    unfold hasIncomingRightFrom
    by_cases hpk : p.val < k
    · rw [hasIncomingRightFrom_of_witness N p q bit hnext hdir k hpk, Bool.true_or]
    · have hp_eq : k = p.val := by omega
      subst hp_eq
      rw [dif_pos p.isLt]
      have hfin : (⟨p.val, p.isLt⟩ : Fin N.numStates) = p := Fin.ext rfl
      dsimp only []
      rw [hfin]
      cases bit with
      | false =>
        have h1 : decide ((N.rule p false).next.val = q.val) = true :=
          decide_eq_true (congrArg Fin.val hnext)
        have h2 : decide ((N.rule p false).dir = .right) = true :=
          decide_eq_true hdir
        rw [h1, h2]
        simp
      | true =>
        have h1 : decide ((N.rule p true).next.val = q.val) = true :=
          decide_eq_true (congrArg Fin.val hnext)
        have h2 : decide ((N.rule p true).dir = .right) = true :=
          decide_eq_true hdir
        rw [h1, h2]
        simp

theorem hasIncomingRight_of_witness (N : NormalizedTM) (p q : Fin N.numStates) (bit : Bool)
    (hnext : (N.rule p bit).next = q) (hdir : (N.rule p bit).dir = .right) :
    hasIncomingRight N q = true :=
  hasIncomingRightFrom_of_witness N p q bit hnext hdir N.numStates p.isLt

#print axioms hasIncomingRight_of_witness

def nearyExtra (N : NormalizedTM) (q : Fin N.numStates) : List (Fin 11) :=
  if q.val = 0 then
    List.replicate (5 * N.numStates - 3) symE ++ List.replicate 4 symH
  else if hasIncomingRight N q then
    List.replicate (5 * (N.numStates - q.val) - 3) symE ++ List.replicate (4 + 5 * q.val) symH
  else
    []

/-- The 5 ETR blocks of state `q` ordered from right to left:
    `[E'(f, t_{q,0}), E(t_{q,1}), E(t_{q,0}), E(t_{q,0}), E(t_{q,1})]`. -/
def nearyStateBlocksR2L (N : NormalizedTM) (q : Fin N.numStates) : List (List (Fin 11)) :=
  let t0 := N.rule q false
  let t1 := N.rule q true
  [nearyExtra N q,
   nearyETR N.numStates t1,
   nearyETR N.numStates t0,
   nearyETR N.numStates t0,
   nearyETR N.numStates t1]

/-- All `5 * N.numStates` ETR blocks ordered from right to left (`q = 0, 1, ..., |Q|-1`).
    Index `5 * q + j` (`0 ≤ j < 5`) is the `j`-th block of state `q` from the right. -/
def nearyBlocksR2L (N : NormalizedTM) : List (List (Fin 11)) :=
  (List.finRange N.numStates).flatMap (nearyStateBlocksR2L N)

def encodeRightBit (b : Bool) : List (Fin 11) :=
  [if b then symLB else symLA, symLA]

def encodeRightTape (bits : List Bool) : List (Fin 11) :=
  bits.flatMap encodeRightBit

def nearyPrefix (N : NormalizedTM) : List (Fin 11) :=
  ((nearyBlocksR2L N).reverse.flatMap fun part => symLAMBDA :: part) ++ [symLAMBDA, symE]

def encodeNormalizedToU (N : NormalizedTM) (word : List Bool) : UConfig :=
  ⟨(nearyPrefix N).reverse,
   symLA,
   List.replicate (5 * N.numStates - 1) symLA ++ [symLB, symLB] ++ encodeRightTape word,
   stateU1⟩

def encodeSourceInstance (M : SourceTM) (w : List Bool) : UConfig :=
  let (N, mw) := normalizeSafe M w
  encodeNormalizedToU N mw

/-! ## Block Indexing & Length Lemmas -/

theorem nearyStateBlocksR2L_length (N : NormalizedTM) (q : Fin N.numStates) :
    (nearyStateBlocksR2L N q).length = 5 := rfl

private theorem flatMap_five_getElem? {α β : Type} (xs : List α) (f : α → List β)
    (hf : ∀ x, (f x).length = 5) (qIdx : Nat) (hq : qIdx < xs.length) (r : Nat) (hr : r < 5) :
    (xs.flatMap f)[5 * qIdx + r]? = (f (xs[qIdx]'hq))[r]? := by
  induction xs generalizing qIdx with
  | nil => cases hq
  | cons x rest ih =>
    cases qIdx with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
      have hlen : r < (f x).length := by rw [hf x]; exact hr
      exact List.getElem?_append_left hlen
    | succ k =>
      simp only [List.flatMap_cons]
      have hge : (f x).length ≤ 5 * (k + 1) + r := by rw [hf x]; omega
      rw [List.getElem?_append_right hge]
      have hsub : 5 * (k + 1) + r - (f x).length = 5 * k + r := by rw [hf x]; omega
      rw [hsub]
      exact ih k (Nat.lt_of_succ_lt_succ hq)

private theorem flatMap_five_length {α β : Type} (xs : List α) (f : α → List β)
    (hf : ∀ x, (f x).length = 5) :
    (xs.flatMap f).length = 5 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.length_append, hf x, ih, List.length_cons]
    omega

theorem nearyBlocksR2L_length (N : NormalizedTM) :
    (nearyBlocksR2L N).length = 5 * N.numStates := by
  unfold nearyBlocksR2L
  rw [flatMap_five_length _ _ (nearyStateBlocksR2L_length N), List.length_finRange]

private theorem finRange_getElem (n i : Nat) (hi : i < (List.finRange n).length) :
    (List.finRange n)[i]'hi = ⟨i, by simpa using hi⟩ := by
  simp

theorem nearyBlocksR2L_get (N : NormalizedTM) (q : Fin N.numStates) (r : Nat) (hr : r < 5) :
    (nearyBlocksR2L N)[5 * q.val + r]? = (nearyStateBlocksR2L N q)[r]? := by
  unfold nearyBlocksR2L
  have hq : q.val < (List.finRange N.numStates).length := by simp [q.isLt]
  rw [flatMap_five_getElem? (List.finRange N.numStates) (nearyStateBlocksR2L N)
        (nearyStateBlocksR2L_length N) q.val hq r hr]
  simp

/-! ## Explicit Polynomial Encoding Length Bound `O(M.numStates^2 + w.length)` -/

def uConfigLength (u : UConfig) : Nat :=
  u.leftRev.length + 1 + u.right.length

theorem nearyETR_length_le (S : Nat) (_hS : S ≥ 2) (act : NormAct S) :
    (nearyETR S act).length ≤ 5 * S + 4 := by
  have hy := act.next.isLt
  unfold nearyETR nearyA nearyB
  cases act.dir <;> cases act.write <;> simp <;> omega

theorem nearyExtra_length_le (N : NormalizedTM) (q : Fin N.numStates) :
    (nearyExtra N q).length ≤ 5 * N.numStates + 4 := by
  have hq := q.isLt
  have hge := N.hge2
  unfold nearyExtra
  by_cases h0 : q.val = 0
  · rw [if_pos h0]; simp
  · rw [if_neg h0]
    cases hasIncomingRight N q with
    | false => simp
    | true => simp; omega

private theorem flatMap_bound_length {α β : Type} (xs : List α) (f : α → List β) (B : Nat)
    (hB : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hx := hB x List.mem_cons_self
    have hr := ih (fun y hy => hB y (List.mem_cons_of_mem x hy))
    have hd : (rest.length + 1) * B = B + rest.length * B := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    omega

theorem nearyBlocksR2L_mem_le (N : NormalizedTM) :
    ∀ blk ∈ nearyBlocksR2L N, blk.length ≤ 5 * N.numStates + 4 := by
  intro blk hmem
  unfold nearyBlocksR2L at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨q, _, hqmem⟩ := hmem
  unfold nearyStateBlocksR2L at hqmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hqmem
  rcases hqmem with rfl | rfl | rfl | rfl | rfl
  · exact nearyExtra_length_le N q
  · exact nearyETR_length_le N.numStates N.hge2 (N.rule q true)
  · exact nearyETR_length_le N.numStates N.hge2 (N.rule q false)
  · exact nearyETR_length_le N.numStates N.hge2 (N.rule q false)
  · exact nearyETR_length_le N.numStates N.hge2 (N.rule q true)

theorem encodeRightTape_length (bits : List Bool) :
    (encodeRightTape bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
    simp only [encodeRightTape, List.flatMap_cons, encodeRightBit, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

theorem encodeNormalizedToU_length_le (N : NormalizedTM) (word : List Bool) :
    uConfigLength (encodeNormalizedToU N word) ≤
      25 * (N.numStates * N.numStates) + 30 * N.numStates + 2 * word.length + 4 := by
  have hge := N.hge2
  unfold uConfigLength encodeNormalizedToU nearyPrefix
  simp only [List.length_reverse, List.length_append, List.length_replicate,
             List.length_cons, List.length_nil, encodeRightTape_length]
  have hblkLen : (nearyBlocksR2L N).reverse.length = 5 * N.numStates := by
    rw [List.length_reverse]
    exact nearyBlocksR2L_length N
  have hpref := flatMap_bound_length (nearyBlocksR2L N).reverse
    (fun part => symLAMBDA :: part) (5 * N.numStates + 5) (by
      intro part hp
      rw [List.mem_reverse] at hp
      have hb := nearyBlocksR2L_mem_le N part hp
      simp only [List.length_cons]
      omega)
  rw [hblkLen] at hpref
  have hsq : 5 * N.numStates * (5 * N.numStates) = 25 * (N.numStates * N.numStates) := by
    calc 5 * N.numStates * (5 * N.numStates)
      _ = 5 * (N.numStates * (5 * N.numStates)) := Nat.mul_assoc 5 N.numStates (5 * N.numStates)
      _ = 5 * (5 * N.numStates * N.numStates) := by rw [Nat.mul_comm N.numStates (5 * N.numStates)]
      _ = 25 * (N.numStates * N.numStates) := by rw [Nat.mul_assoc]; omega
  have hexpand : 5 * N.numStates * (5 * N.numStates + 5) =
      25 * (N.numStates * N.numStates) + 25 * N.numStates := by
    rw [Nat.mul_add, hsq]
    omega
  rw [hexpand] at hpref
  omega

/-- Explicit `O(M.numStates^2 + w.length)` upper bound on `encodeSourceInstance M w`. -/
theorem encodeSourceInstance_poly_bound (M : SourceTM) (w : List Bool) :
    uConfigLength (encodeSourceInstance M w) ≤
      225 * (M.numStates * M.numStates) + 390 * M.numStates + 4 * w.length + 172 := by
  unfold encodeSourceInstance normalizeSafe
  dsimp only []
  have hbase := encodeNormalizedToU_length_le (normalizeSafeTM M) (encodeMarkedWord w)
  have hS : (normalizeSafeTM M).numStates ≤ 3 * M.numStates + 2 := numNormStates_le M
  have hw : (encodeMarkedWord w).length ≤ 2 * w.length + 2 := encodeMarkedWord_length w
  have hS2 : (normalizeSafeTM M).numStates * (normalizeSafeTM M).numStates ≤
      (3 * M.numStates + 2) * (3 * M.numStates + 2) := Nat.mul_le_mul hS hS
  have h9 : (3 * M.numStates) * (3 * M.numStates) = 9 * (M.numStates * M.numStates) := by
    calc 3 * M.numStates * (3 * M.numStates)
      _ = 3 * (M.numStates * (3 * M.numStates)) := Nat.mul_assoc 3 M.numStates (3 * M.numStates)
      _ = 3 * (3 * M.numStates * M.numStates) := by rw [Nat.mul_comm M.numStates (3 * M.numStates)]
      _ = 9 * (M.numStates * M.numStates) := by rw [Nat.mul_assoc]; omega
  have hquad : (3 * M.numStates + 2) * (3 * M.numStates + 2) =
      9 * (M.numStates * M.numStates) + 12 * M.numStates + 4 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, h9]
    omega
  rw [hquad] at hS2
  omega

/-! ## Output Readback Decoder (`neary_output_reader.py`) -/

def decodeRightPairs : List (Fin 11) → Option (List Bool)
  | [] => some []
  | [s] =>
    if s == symLA then some [false]
    else if s == symLB then some [true]
    else none
  | s1 :: s2 :: rest =>
    if s2 == symLA then
      if s1 == symLA then Option.map (false :: ·) (decodeRightPairs rest)
      else if s1 == symLB then Option.map (true :: ·) (decodeRightPairs rest)
      else none
    else none

def extractOddData : List Bool → Option (List Bool)
  | [] => some []
  | [d] => some [d]
  | d :: m :: rest =>
    if m == false then Option.map (d :: ·) (extractOddData rest)
    else none

def decodeMarkedBits (marked : List Bool) : Option (List Bool) :=
  match marked with
  | [] => some []
  | sentinel :: rest =>
    if sentinel == true then Option.map trimRightFalse (extractOddData rest)
    else none

def decodeHaltedUConfig (u : UConfig) : Option (List Bool) :=
  if u.state == stateU3 && u.symbol == symDELTA then
    let r1 := u.right.dropWhile (· == symLA)
    let r2 := r1.dropWhile (· == symLB)
    let lbCount := r1.length - r2.length
    if lbCount ≥ 2 then
      match r2 with
      | sym :: r3 =>
        if sym == symLA then
          match decodeRightPairs r3 with
          | none => none
          | some marked => decodeMarkedBits marked
        else none
      | [] => none
    else none
  else none

/-! ## Concrete `#guard` Cross-Checks against `neary_u3_11.py` & `prize_encoder.py` -/

-- Example 3.3.1 from Neary (2008) & `neary_u3_11.py`: 3-state machine M1 on `101`
private def nearyM1 : NormalizedTM where
  numStates := 3
  hge2 := by decide
  rule := fun q b =>
    match q.val, b with
    | 0, false => ⟨true,  .right, ⟨1, by decide⟩⟩
    | 0, true  => ⟨false, .right, ⟨0, by decide⟩⟩
    | 1, false => ⟨false, .left,  ⟨1, by decide⟩⟩
    | 1, true  => ⟨true,  .left,  ⟨2, by decide⟩⟩
    | _, false => ⟨false, .left,  ⟨2, by decide⟩⟩
    | _, true  => ⟨true,  .left,  ⟨2, by decide⟩⟩
  hfinal := by intro b; cases b <;> rfl

private def expectedM1Prefix : List (Fin 11) :=
  let e31 := [symE] ++ List.replicate 15 symH ++ [symE, symH, symE]
  let e30 := [symE] ++ List.replicate 15 symH ++ [symE, symE, symE]
  let e21 := e31
  let e20 := List.replicate 6 symE ++ List.replicate 10 symH ++ [symE, symE, symE]
  let e11 := List.replicate 15 symE ++ List.replicate 2 symH
  let e10 := [symH] ++ List.replicate 10 symE ++ List.replicate 7 symH
  let etrs := [e31, e30, e30, e31, [],
               e21, e20, e20, e21, List.replicate 7 symE ++ List.replicate 9 symH,
               e11, e10, e10, e11, List.replicate 12 symE ++ List.replicate 4 symH]
  (etrs.flatMap fun part => symLAMBDA :: part) ++ [symLAMBDA, symE]

#guard nearyPrefix nearyM1 == expectedM1Prefix

-- Cross-check full `encodeSourceInstance` against `gen_crosschecks.py` (`prize_encoder.py` cases)
private def checkSample1 : SourceTM where
  numStates := 2
  hpos := by decide
  stepRule := fun q b =>
    if q.val = 0 && !b then some ⟨true, .stay, ⟨1, by decide⟩⟩ else none

private def checkSample3 : SourceTM where
  numStates := 2
  hpos := by decide
  stepRule := fun q b =>
    if q.val = 0 && !b then some ⟨true, .right, ⟨1, by decide⟩⟩
    else if q.val = 1 && !b then some ⟨true, .left, ⟨0, by decide⟩⟩
    else none

#guard uConfigLength (encodeSourceInstance checkSample1 [false, true]) == 712
#guard (encodeSourceInstance checkSample1 [false, true]).leftRev.length == 677
#guard uConfigLength (encodeSourceInstance checkSample1 []) == 708
#guard (encodeSourceInstance checkSample1 []).leftRev.length == 677
#guard ((encodeSourceInstance checkSample1 []).leftRev.reverse.take 20).map Fin.val ==
  [8, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]
#guard uConfigLength (encodeSourceInstance checkSample3 []) == 992
#guard (encodeSourceInstance checkSample3 []).leftRev.length == 956

#print axioms uRun_equiv_forward
#print axioms encodeSourceInstance_poly_bound
#print axioms decodeHaltedUConfig
