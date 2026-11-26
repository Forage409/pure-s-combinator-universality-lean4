import formal_controller.constructive_endpoint

/- S-Tape Halted Output Readback, Canonical Trajectory Invariants,
   Polynomial Initial Size Bound, and Polynomial Trajectory Size Bound. -/

/-! ## Part 1: Halted U(3,11) Output Readback from Bare Pure-S Terms -/

/-- Extract the committed cell bits along the right-spine of an S-encoded tape. -/
def readTapeBits : Term → List Bool
  | .app (.app .s version) (.app (.app .s rest) _) =>
      (cellFromVersion version).bit :: readTapeBits rest
  | _ => []

theorem readTapeBits_closed (t : Term) (h : parseFrame t = none) :
    readTapeBits t = [] := by
  unfold parseFrame at h
  unfold readTapeBits
  split <;> simp_all

theorem readTapeBits_frame (version rest junk : Term) :
    readTapeBits (frameTerm version rest junk) =
      (cellFromVersion version).bit :: readTapeBits rest := rfl

theorem readTapeBits_canonical (cells : List (List UniversalCell)) :
    ∀ d, readTapeBits (canonicalTape cells d) = cellBits cells := by
  induction cells with
  | nil =>
      intro d
      rw [canonical_tape_nil]
      exact readTapeBits_closed (depthBase d) (depth_base_closed d)
  | cons cell rest ih =>
      intro d
      rw [canonical_tape_cons, readTapeBits_frame, concrete_version_decodes, ih (d + 1)]
      rfl

def bits4Value (b0 b1 b2 b3 : Bool) : Nat :=
  (if b0 then 8 else 0) + (if b1 then 4 else 0) + (if b2 then 2 else 0) + (if b3 then 1 else 0)

def decodeSymbol4 (b0 b1 b2 b3 : Bool) : Option (Fin 11) :=
  let v := bits4Value b0 b1 b2 b3
  if h : v < 11 then some ⟨v, h⟩ else none

/-- Group a binary bit-list into 4-bit big-endian chunks (padding any partial
    trailing chunk with `false` blanks, matching `s_neary_output_reader.py`)
    and decode each chunk into `Fin 11`. -/
def decodeBitBlocks : List Bool → Option (List (Fin 11))
  | [] => some []
  | [b0] => (decodeSymbol4 b0 false false false).map (· :: [])
  | [b0, b1] => (decodeSymbol4 b0 b1 false false).map (· :: [])
  | [b0, b1, b2] => (decodeSymbol4 b0 b1 b2 false).map (· :: [])
  | b0 :: b1 :: b2 :: b3 :: rest =>
      match decodeSymbol4 b0 b1 b2 b3, decodeBitBlocks rest with
      | some s, some tail => some (s :: tail)
      | _, _ => none

/-- Read the halted U(3,11) configuration `(bitHead, symbols)` directly from a
    bare pure-S term:
    1. Verify the hub at `rootHubPath` is open and its halt flag is open (`rootHalt`);
    2. Verify no cell has a pending move (`findConcreteCell movingCell tape = none`);
    3. Read the active binary head index `bitHead` (checking `bitHead % 4 == 0`);
    4. Decode committed 4-bit symbol blocks along the S tape. -/
def readHaltedUConfigFromS (root : Term) : Option (Nat × List (Fin 11)) := do
  let hub ← termAt root rootHubPath
  let (flag, tape, _) ← parseFrame hub
  if !flagValue flag then none
  else
    match findConcreteCell movingCell tape with
    | some _ => none
    | none =>
        let bitHead ← findConcreteCell activeCell tape
        if bitHead % 4 == 0 then
          let symbols ← decodeBitBlocks (readTapeBits tape)
          some (bitHead, symbols)
        else none

def uConfigTape (u : UConfig) : List (Fin 11) :=
  u.leftRev.reverse ++ u.symbol :: u.right

def uConfigHead (u : UConfig) : Nat :=
  u.leftRev.length

def symbolAt : List (Fin 11) → Nat → Fin 11
  | [], _ => 0
  | s :: _, 0 => s
  | _ :: rest, i + 1 => symbolAt rest i

/-- Extensional tape equality modulo trailing `0 : Fin 11` blank symbols. -/
def USymbolsEqModBlanks (a b : List (Fin 11)) : Prop :=
  ∀ i : Nat, symbolAt a i = symbolAt b i

theorem decodeSymbol4_symbolBlock :
    ∀ s : Fin 11,
      decodeSymbol4 (symbolBitAt s 0) (symbolBitAt s 1) (symbolBitAt s 2) (symbolBitAt s 3) = some s := by
  decide

theorem symbolBlock_injective :
    ∀ s1 s2 : Fin 11, symbolBlock s1 = symbolBlock s2 → s1 = s2 := by
  decide

theorem symbolBlock_zero :
    symbolBlock (0 : Fin 11) = [false, false, false, false] := by
  decide

def bitQuadAt (xs : List Bool) (j : Nat) : List Bool :=
  [bitAt xs (4 * j), bitAt xs (4 * j + 1), bitAt xs (4 * j + 2), bitAt xs (4 * j + 3)]

theorem bitQuadAt_nil (j : Nat) :
    bitQuadAt [] j = symbolBlock (0 : Fin 11) := by
  rw [symbolBlock_zero]
  rfl

theorem bitQuadAt_cons4 (b0 b1 b2 b3 : Bool) (rest : List Bool) (j : Nat) :
    bitQuadAt (b0 :: b1 :: b2 :: b3 :: rest) (j + 1) = bitQuadAt rest j := by
  have h0 : 4 * (j + 1) = 4 * j + 4 := by omega
  have h1 : 4 * (j + 1) + 1 = (4 * j + 1) + 4 := by omega
  have h2 : 4 * (j + 1) + 2 = (4 * j + 2) + 4 := by omega
  have h3 : 4 * (j + 1) + 3 = (4 * j + 3) + 4 := by omega
  unfold bitQuadAt
  rw [h3, h2, h1, h0]
  rfl

theorem bitQuadAt_flattenSymbols (syms : List (Fin 11)) :
    ∀ j, bitQuadAt (flattenSymbols syms) j = symbolBlock (symbolAt syms j) := by
  induction syms with
  | nil =>
      intro j
      simp [flattenSymbols, symbolAt, bitQuadAt_nil]
  | cons s rest ih =>
      intro j
      cases j with
      | zero =>
          simp [flattenSymbols, symbolBlock, bitQuadAt, bitAt, symbolAt]
      | succ j =>
          change bitQuadAt (symbolBitAt s 0 :: symbolBitAt s 1 :: symbolBitAt s 2 :: symbolBitAt s 3 :: flattenSymbols rest) (j + 1) =
            symbolBlock (symbolAt rest j)
          rw [bitQuadAt_cons4]
          exact ih j

theorem decodeSymbol4_of_block {b0 b1 b2 b3 : Bool} {s : Fin 11}
    (h : [b0, b1, b2, b3] = symbolBlock s) :
    decodeSymbol4 b0 b1 b2 b3 = some s := by
  simp only [symbolBlock, List.cons.injEq, and_true] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  exact decodeSymbol4_symbolBlock s

theorem decodeBitBlocks_from_quads :
    ∀ (n : Nat) (xs : List Bool), xs.length ≤ n →
      (∀ j, ∃ s : Fin 11, bitQuadAt xs j = symbolBlock s) →
      ∃ syms, decodeBitBlocks xs = some syms ∧
        ∀ j, bitQuadAt xs j = symbolBlock (symbolAt syms j) := by
  intro n
  induction n with
  | zero =>
      intro xs hlen _
      cases xs with
      | nil =>
          refine ⟨[], rfl, ?_⟩
          intro j
          exact bitQuadAt_nil j
      | cons _ _ => simp at hlen
  | succ n ih =>
      intro xs hlen hquad
      match xs with
      | [] =>
          refine ⟨[], rfl, ?_⟩
          intro j
          exact bitQuadAt_nil j
      | [b0] =>
          obtain ⟨s0, hs0⟩ := hquad 0
          have hd0 : decodeSymbol4 b0 false false false = some s0 :=
            decodeSymbol4_of_block (by simpa [bitQuadAt, bitAt] using hs0)
          refine ⟨[s0], by simp [decodeBitBlocks, hd0], ?_⟩
          intro j
          cases j with
          | zero => simpa [symbolAt] using hs0
          | succ j =>
              have hnil : bitQuadAt [b0] (j + 1) = symbolBlock (0 : Fin 11) := by
                have h0 : 4 * (j + 1) = (4 * j + 3) + 1 := by omega
                have h1 : 4 * (j + 1) + 1 = (4 * j + 4) + 1 := by omega
                have h2 : 4 * (j + 1) + 2 = (4 * j + 5) + 1 := by omega
                have h3 : 4 * (j + 1) + 3 = (4 * j + 6) + 1 := by omega
                rw [symbolBlock_zero]
                unfold bitQuadAt
                rw [h3, h2, h1, h0]
                rfl
              simpa [symbolAt] using hnil
      | [b0, b1] =>
          obtain ⟨s0, hs0⟩ := hquad 0
          have hd0 : decodeSymbol4 b0 b1 false false = some s0 :=
            decodeSymbol4_of_block (by simpa [bitQuadAt, bitAt] using hs0)
          refine ⟨[s0], by simp [decodeBitBlocks, hd0], ?_⟩
          intro j
          cases j with
          | zero => simpa [symbolAt] using hs0
          | succ j =>
              have hnil : bitQuadAt [b0, b1] (j + 1) = symbolBlock (0 : Fin 11) := by
                have h0 : 4 * (j + 1) = (4 * j + 2) + 2 := by omega
                have h1 : 4 * (j + 1) + 1 = (4 * j + 3) + 2 := by omega
                have h2 : 4 * (j + 1) + 2 = (4 * j + 4) + 2 := by omega
                have h3 : 4 * (j + 1) + 3 = (4 * j + 5) + 2 := by omega
                rw [symbolBlock_zero]
                unfold bitQuadAt
                rw [h3, h2, h1, h0]
                rfl
              simpa [symbolAt] using hnil
      | [b0, b1, b2] =>
          obtain ⟨s0, hs0⟩ := hquad 0
          have hd0 : decodeSymbol4 b0 b1 b2 false = some s0 :=
            decodeSymbol4_of_block (by simpa [bitQuadAt, bitAt] using hs0)
          refine ⟨[s0], by simp [decodeBitBlocks, hd0], ?_⟩
          intro j
          cases j with
          | zero => simpa [symbolAt] using hs0
          | succ j =>
              have hnil : bitQuadAt [b0, b1, b2] (j + 1) = symbolBlock (0 : Fin 11) := by
                have h0 : 4 * (j + 1) = (4 * j + 1) + 3 := by omega
                have h1 : 4 * (j + 1) + 1 = (4 * j + 2) + 3 := by omega
                have h2 : 4 * (j + 1) + 2 = (4 * j + 3) + 3 := by omega
                have h3 : 4 * (j + 1) + 3 = (4 * j + 4) + 3 := by omega
                rw [symbolBlock_zero]
                unfold bitQuadAt
                rw [h3, h2, h1, h0]
                rfl
              simpa [symbolAt] using hnil
      | b0 :: b1 :: b2 :: b3 :: rest =>
          obtain ⟨s0, hs0⟩ := hquad 0
          have hd0 : decodeSymbol4 b0 b1 b2 b3 = some s0 :=
            decodeSymbol4_of_block (by simpa [bitQuadAt, bitAt] using hs0)
          have hrestLen : rest.length ≤ n := by
            simp only [List.length_cons] at hlen
            omega
          have hrestQuad : ∀ j, ∃ s : Fin 11, bitQuadAt rest j = symbolBlock s := by
            intro j
            obtain ⟨s, hs⟩ := hquad (j + 1)
            rw [bitQuadAt_cons4] at hs
            exact ⟨s, hs⟩
          obtain ⟨tailSyms, htailDec, htailSpec⟩ := ih rest hrestLen hrestQuad
          refine ⟨s0 :: tailSyms, by simp [decodeBitBlocks, hd0, htailDec], ?_⟩
          intro j
          cases j with
          | zero => simpa [symbolAt] using hs0
          | succ j =>
              rw [bitQuadAt_cons4, symbolAt]
              exact htailSpec j

theorem rightEq_append_prefix (pref a b : List Bool) (h : RightEq a b) :
    RightEq (pref ++ a) (pref ++ b) := by
  induction pref with
  | nil => exact h
  | cons x xs ih => exact right_eq_cons (xs ++ a) (xs ++ b) x ih

theorem flattenSymbols_length (syms : List (Fin 11)) :
    (flattenSymbols syms).length = 4 * syms.length := by
  induction syms with
  | nil => rfl
  | cons s rest ih =>
      change (symbolBlock s ++ flattenSymbols rest).length = 4 * (rest.length + 1)
      rw [List.length_append, ih]
      simp [symbolBlock]
      omega

theorem cellBits_length (cells : List (List UniversalCell)) :
    (cellBits cells).length = cells.length := by
  simp [cellBits]

theorem seed_halt_trace_intermediate_closed (program : BinaryProgram)
    (tape junk : Term) (sourcePath : List Bool) (q : Fin 132) (bit : Bool)
    (hpriority : priorityConcretePath tape = .active sourcePath)
    (hread : readCellAt tape sourcePath = some ⟨bit, .active, q.val⟩)
    (hstop : program q bit = none)
    {k2 : Nat} {a b : Term}
    (trace : SeedHaltTrace tape junk (.active sourcePath) k2 a b) :
    ∀ m mid, m < k2 → FullSelectorTrace program m (seedHubRoot a tape junk) mid →
      rootHalt mid = false := by
  induction trace with
  | zero _ =>
      intro m _ hm _
      omega
  | @next n a a1 b hstep rest ih =>
      intro m mid hm hfull
      cases m with
      | zero =>
          cases hfull
          rw [root_halt_seed]
          exact hstep.1
      | succ m' =>
          cases hfull with
          | @next _ _ mid1 _ path' hs' hd' tailTrace =>
              obtain ⟨path, hs, hd⟩ :=
                halt_seed_step_is_full_selector program tape junk sourcePath q bit hpriority hread hstop hstep
              have heq : seedHubRoot a1 tape junk = mid1 :=
                full_selector_step_unique program (seedHubRoot a tape junk) (seedHubRoot a1 tape junk) mid1
                  path path' hs hs' hd hd'
              subst mid1
              exact ih m' mid (by omega) tailTrace

theorem u_halted_binary_checkpoint (initial final : UConfig) {n : Nat}
    (urun : URun n initial final) (hstop : uNext final = none) :
    ∃ out,
      PlainRun fixedBinaryProgram (10 * n + 6) (encodeUConfig initial) out ∧
      plainNext fixedBinaryProgram out = none ∧
      out.left = flattenSymbols final.leftRev.reverse ∧
      RightEq (flattenSymbols (uConfigTape final)) (out.left ++ out.bit :: out.right) := by
  cases final with
  | mk left symbol right state =>
      have hnone : fixedUProgram state symbol = none := (u_next_none_iff_rule_none _).mp hstop
      have htest := u_undefined_exact_pair state symbol
      rw [hnone] at htest
      have hpair : state.val = 2 ∧ symbol.val = 9 := of_decide_eq_true htest.symm
      have hq : state = (2 : Fin 3) := by apply Fin.ext; exact hpair.1.trans (by decide)
      have hs : symbol = (9 : Fin 11) := by apply Fin.ext; exact hpair.2.trans (by decide)
      subst state
      subst symbol
      obtain ⟨binary, hrun1, heq1⟩ :=
        u_run_refines_binary urun (encodeUConfig initial) (plain_eq_refl _)
      have hs0 : symbolBitAt (9 : Fin 11) 0 = true := by decide
      have hs1 : symbolBitAt (9 : Fin 11) 1 = false := by decide
      have hs2 : symbolBitAt (9 : Fin 11) 2 = false := by decide
      have hs3 : symbolBitAt (9 : Fin 11) 3 = true := by decide
      have hstart : binaryStartState (2 : Fin 3) = (55 : Fin 132) := by decide
      let mid : PlainConfig :=
        ⟨flattenSymbols left.reverse, true, false :: false :: true :: flattenSymbols right, (41 : Fin 132)⟩
      have hiter : iteratePlain fixedBinaryProgram 6 (encodeUConfig ⟨left, 9, right, 2⟩) = some mid := by
        simpa [mid, encodeUConfig, hs0, hs1, hs2, hs3, hstart] using
          u_2_9_rewind (flattenSymbols left.reverse) (flattenSymbols right)
      have hmidStop : plainNext fixedBinaryProgram mid = none := by
        simp [mid, plainNext]
      have hmidRun := iterate_plain_is_run fixedBinaryProgram 6 (encodeUConfig ⟨left, 9, right, 2⟩) mid hiter
      obtain ⟨out, hrun2, houtEq⟩ := plain_run_equiv_forward fixedBinaryProgram hmidRun binary heq1
      have hnext := plain_next_respects_equiv fixedBinaryProgram mid out houtEq
      cases hstopOut : plainNext fixedBinaryProgram out with
      | some _ => simp [hmidStop, hstopOut, OptionPlainEq] at hnext
      | none =>
          rcases houtEq with ⟨hleftEq, hbitEq, _, hrightEq⟩
          have hleftOut : out.left = flattenSymbols left.reverse := hleftEq.symm
          have hbitOut : out.bit = true := hbitEq.symm
          have hfullEq :
              RightEq (flattenSymbols (uConfigTape ⟨left, 9, right, 2⟩))
                (out.left ++ out.bit :: out.right) := by
            have hflat : flattenSymbols (uConfigTape ⟨left, 9, right, 2⟩) =
                flattenSymbols left.reverse ++ true :: false :: false :: true :: flattenSymbols right := by
              simp [uConfigTape, flattenSymbols, List.flatMap_append, symbolBlock, hs0, hs1, hs2, hs3]
            rw [hflat, ← hleftOut, hbitOut]
            exact rightEq_append_prefix out.left _ _ (right_eq_cons _ _ true hrightEq)
          exact ⟨out, plain_run_trans fixedBinaryProgram hrun1 hrun2, hstopOut, hleftOut, hfullEq⟩

theorem readHaltedUConfigFromS_on_seedHub (flag : Term) (hflag : flagValue flag = true)
    (before : List (List UniversalCell)) (source : List UniversalCell) (after : List (List UniversalCell))
    (q : Fin 132) (bit : Bool)
    (hb : AllOff before) (hs : ActiveAt source q bit) (ha : AllOff after)
    (u : UConfig)
    (hhead : (cellBits before).length = 4 * uConfigHead u)
    (htape : RightEq (flattenSymbols (uConfigTape u)) (cellBits (before ++ source :: after))) :
    ∃ syms,
      readHaltedUConfigFromS (seedHubRoot flag (canonicalTape (before ++ source :: after) 1) (depthJunk 0)) =
        some (4 * uConfigHead u, syms) ∧
      USymbolsEqModBlanks syms (uConfigTape u) := by
  let cells := before ++ source :: after
  let tape := canonicalTape cells 1
  have hp := phase_at_good 1
  have hm : layoutMatches (storageTapeLayout cells) tape :=
    finite_layout_decodes (storageTapeLayout cells) (phaseAt 1).1 (phaseAt 1).2 hp.1 hp.2
  have hmoveBefore := alloff_decoded_not_moving before hb
  have hmoveAfter := alloff_decoded_not_moving after ha
  have hmoveSource : movingCell (decodedCell source) = false := by rw [hs]; rfl
  have hnoMoveList : ∀ c ∈ cells.map decodedCell, movingCell c = false := by
    intro c hc
    simp only [cells, List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact hmoveBefore c hc
    · subst c; exact hmoveSource
    · exact hmoveAfter c hc
  have hfindMove : findConcreteCell movingCell tape = none := by
    rw [scan_concrete_tape cells movingCell tape hm]
    exact scan_none_when_absent movingCell _ hnoMoveList
  have hactiveBefore := alloff_decoded_not_active before hb
  have hactiveSource : activeCell (decodedCell source) = true := by rw [hs]; rfl
  have hfindActive : findConcreteCell activeCell tape = some before.length := by
    rw [scan_concrete_tape cells activeCell tape hm]
    simpa [cells] using scan_finds_first activeCell (before.map decodedCell) (after.map decodedCell)
      (decodedCell source) hactiveBefore hactiveSource
  have hbeforeLen : before.length = 4 * uConfigHead u := by
    simpa [cellBits_length] using hhead
  have hmod4 : ((4 * uConfigHead u) % 4 == 0) = true := by
    have hm0 : (4 * uConfigHead u) % 4 = 0 := by omega
    rw [hm0]
    exact decide_eq_true rfl
  have hbits : readTapeBits tape = cellBits cells := readTapeBits_canonical cells 1
  have hquadEq : ∀ j, bitQuadAt (cellBits cells) j = bitQuadAt (flattenSymbols (uConfigTape u)) j := by
    intro j
    dsimp only [cells, bitQuadAt]
    rw [(htape (4 * j)).symm, (htape (4 * j + 1)).symm, (htape (4 * j + 2)).symm, (htape (4 * j + 3)).symm]
  have hquads : ∀ j, ∃ s : Fin 11, bitQuadAt (readTapeBits tape) j = symbolBlock s := by
    intro j
    refine ⟨symbolAt (uConfigTape u) j, ?_⟩
    rw [hbits, hquadEq j]
    exact bitQuadAt_flattenSymbols (uConfigTape u) j
  obtain ⟨syms, hdec, hsymsSpec⟩ :=
    decodeBitBlocks_from_quads (readTapeBits tape).length (readTapeBits tape) (Nat.le_refl _) hquads
  refine ⟨syms, ?_, ?_⟩
  · have hhubAt : termAt (seedHubRoot flag tape (depthJunk 0)) rootHubPath =
        some (frameTerm flag tape (depthJunk 0)) := rfl
    unfold readHaltedUConfigFromS
    rw [hhubAt]
    dsimp only [Bind.bind, Option.bind]
    rw [parse_frame]
    dsimp only []
    rw [hflag, hfindMove, hfindActive, hbeforeLen]
    dsimp only []
    rw [hmod4, hdec]
    rfl
  · intro j
    apply symbolBlock_injective
    rw [← hsymsSpec j, hbits, hquadEq j]
    exact bitQuadAt_flattenSymbols (uConfigTape u) j

/-- Main Halted Readback Theorem: whenever `initial` halts in `final` on `U(3,11)`,
    every halted S-term `reached` along the `FullSelectorTrace` from `sEncodeU initial`
    decodes via `readHaltedUConfigFromS` to `final`'s exact head index (`4 * uConfigHead final`)
    and `final`'s tape modulo trailing `0 : Fin 11` blanks. -/
theorem halted_s_term_reads_back_u_config {n k : Nat} {initial final : UConfig} {reached : Term}
    (urun : URun n initial final) (hstop : uNext final = none)
    (htrace : FullSelectorTrace fixedBinaryProgram k (sEncodeU initial) reached)
    (hhalt : rootHalt reached = true) :
    ∃ syms,
      readHaltedUConfigFromS reached = some (4 * uConfigHead final, syms) ∧
      USymbolsEqModBlanks syms (uConfigTape final) := by
  obtain ⟨out, hplainRun, houtStop, houtLeft, houtTapeEq⟩ :=
    u_halted_binary_checkpoint initial final urun hstop
  obtain ⟨finalRecords, hsourceRun, hrepFinal⟩ :=
    plain_run_lifts fixedBinaryProgram hplainRun
      (initialRecords (encodeUConfig initial)) (initial_records_represent _)
  obtain ⟨before, source, after, hrecEq, hb, hs, ha, hbitsBefore, hbitsAfter⟩ := hrepFinal
  subst finalRecords
  have hruleNone : fixedBinaryProgram out.state out.bit = none :=
    (plain_next_none_iff_rule_none fixedBinaryProgram out).mp houtStop
  obtain ⟨k1, _, _, hfirst⟩ :=
    constructive_finite_source_run_full_selector fixedBinaryProgram hsourceRun 1 (depthBase 1) (depthJunk 0)
      (depth_base_closed 1)
  let tape := canonicalTape (before ++ source :: after) 1
  let srcPath := physicalPath (List.replicate before.length true)
  obtain ⟨k2, _, _, _, hseedTrace, _, _⟩ :=
    stopped_boundary_exposes_halt fixedBinaryProgram before source after out.state out.bit
      hb hs ha hruleNone 1 1 (depthJunk 0)
  have hpriority : priorityConcretePath tape = .active srcPath :=
    canonical_boundary_priority_path before source after out.state out.bit hb hs ha 1
  have hread : readCellAt tape srcPath = some ⟨out.bit, .active, out.state.val⟩ :=
    canonical_boundary_reads_active before source after out.state out.bit hs 1
  have hlast :=
    halt_seed_trace_is_full_selector fixedBinaryProgram tape (depthJunk 0) srcPath out.state out.bit
      hpriority hread hruleNone hseedTrace
  have hnotLeK1 : ¬ k ≤ k1 := by
    intro hle
    have hclosed := canonical_root_closed_halt (before ++ source :: after) 1 1 (depthJunk 0)
    exact halt_cannot_precede_closed_checkpoint fixedBinaryProgram k k1 _ reached _ htrace hhalt hfirst hle hclosed
  have hnotLtK12 : ¬ k < k1 + k2 := by
    intro hlt
    have hkSplit : k = k1 + (k - k1) := by omega
    rw [hkSplit] at htrace
    obtain ⟨mid1, hpre, hsuf⟩ := full_selector_trace_split fixedBinaryProgram k1 (k - k1) htrace
    have hmidEq : canonicalRoot (before ++ source :: after) 1 (depthBase 1) (depthJunk 0) = mid1 :=
      full_selector_trace_unique fixedBinaryProgram hfirst mid1 hpre
    subst mid1
    have hfalse := seed_halt_trace_intermediate_closed fixedBinaryProgram tape (depthJunk 0) srcPath
      out.state out.bit hpriority hread hruleNone hseedTrace (k - k1) reached (by omega) hsuf
    rw [hfalse] at hhalt
    cases hhalt
  have hkSplit2 : k = (k1 + k2) + (k - (k1 + k2)) := by omega
  rw [hkSplit2] at htrace
  obtain ⟨midHalt, hpreHalt, hsufHalt⟩ :=
    full_selector_trace_split fixedBinaryProgram (k1 + k2) (k - (k1 + k2)) htrace
  have hcombined := full_selector_trace_trans hfirst hlast
  have hmidHaltEq := full_selector_trace_unique fixedBinaryProgram hcombined midHalt hpreHalt
  subst midHalt
  let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt 1).1 (phaseAt 1).2
  have hflagOpenVal : flagValue flagOpen = true := by
    have hd := finite_layout_decodes (.opened .unopened .unopened)
      (phaseAt 1).1 (phaseAt 1).2 (phase_at_good 1).1 (phase_at_good 1).2
    simpa [layoutIsOpen] using matched_layout_flag (.opened .unopened .unopened) flagOpen hd
  obtain ⟨finalFlag, hreachedEq, hfinalFlagVal⟩ :=
    full_selector_halt_persists_trace fixedBinaryProgram hsufHalt flagOpen tape (depthJunk 0) rfl hflagOpenVal
  rw [hreachedEq]
  have hheadLen : (cellBits before).length = 4 * uConfigHead final := by
    rw [hbitsBefore, houtLeft, flattenSymbols_length, List.length_reverse]
    rfl
  have hsourceBit : (decodedCell source).bit = out.bit := by
    rw [hs]
  have hcellBitsAll : cellBits (before ++ source :: after) = out.left ++ out.bit :: out.right := by
    unfold cellBits at hbitsBefore hbitsAfter ⊢
    simp [List.map_append, hsourceBit, hbitsBefore, hbitsAfter]
  rw [← hcellBitsAll] at houtTapeEq
  exact readHaltedUConfigFromS_on_seedHub finalFlag hfinalFlagVal before source after
    out.state out.bit hb hs ha final hheadLen houtTapeEq

/-- Existence + Readback corollary: if `initial` halts in `final` after `n` steps of `U(3,11)`,
    there is an explicit `FullSelectorTrace` reaching a halted S-term whose readback agrees
    with `final`. -/
theorem halted_u_reaches_readable_s_term {n : Nat} {initial final : UConfig}
    (urun : URun n initial final) (hstop : uNext final = none) :
    ∃ k reached syms,
      FullSelectorTrace fixedBinaryProgram k (sEncodeU initial) reached ∧
      rootHalt reached = true ∧
      readHaltedUConfigFromS reached = some (4 * uConfigHead final, syms) ∧
      USymbolsEqModBlanks syms (uConfigTape final) := by
  obtain ⟨k, reached, htrace, hhalt⟩ :=
    (constructive_fixed_u_to_s_halting initial).mp ⟨n, final, urun, hstop⟩
  obtain ⟨syms, hread, heq⟩ := halted_s_term_reads_back_u_config urun hstop htrace hhalt
  exact ⟨k, reached, syms, htrace, hhalt, hread, heq⟩


/-! ## Part 2: Logical Strict-Frame Invariant and Monotone Leaf Growth Along Trajectories -/

def isS2Term : Term → Bool
  | .app (.app .s _) _ => true
  | _ => false

def isStrictFrameBool (t : Term) : Bool :=
  match parseFrame t with
  | none => false
  | some (_, _, j) => !isS2Term j

/-- Every `F`-frame reachable along logical `L` (`[false, true]`) and `R` (`[true, false, true]`)
    slots from `t` has junk `j` satisfying `!isS2Term j`. -/
def logicalTreeStrict : Term → Bool
  | .app (.app .s l) (.app (.app .s r) j) =>
      !isS2Term j && logicalTreeStrict l && logicalTreeStrict r
  | _ => true

theorem logicalTreeStrict_closed {t : Term} (h : parseFrame t = none) :
    logicalTreeStrict t = true := by
  unfold parseFrame at h
  unfold logicalTreeStrict
  split <;> simp_all

theorem logicalTreeStrict_frame (l r j : Term) :
    logicalTreeStrict (frameTerm l r j) =
      (!isS2Term j && logicalTreeStrict l && logicalTreeStrict r) := rfl

theorem logicalTreeStrict_eq_flag {t : Term} (h : logicalTreeStrict t = true) :
    isStrictFrameBool t = flagValue t := by
  unfold isStrictFrameBool flagValue
  cases hp : parseFrame t with
  | none => rfl
  | some triple =>
      rcases triple with ⟨l, r, j⟩
      have ht := parse_frame_sound t l r j hp
      subst t
      rw [logicalTreeStrict_frame] at h
      simp only [Bool.and_eq_true] at h
      simp [h.1.1]

theorem generated_junk_not_s2 (k : Nat) (d : Term) :
    isS2Term ((numeral k ⋅ S) ⋅ d) = false := by
  cases k <;> rfl

theorem phaseJunk_not_s2 (p : Nat × Nat) : isS2Term (phaseJunk p) = false := by
  rcases p with ⟨m, n⟩
  cases m <;> exact generated_junk_not_s2 _ _

theorem layoutTerm_logicalTreeStrict (shape : Layout) :
    ∀ p : Nat × Nat, goodPhase p → logicalTreeStrict (layoutTerm shape p.1 p.2) = true := by
  induction shape with
  | unopened =>
      intro p _
      exact logicalTreeStrict_closed (parse_generator_closed p.1 p.2)
  | opened l r ihl ihr =>
      intro p hp
      rw [layout_opened_phase l r p hp, logicalTreeStrict_frame]
      have hnext := next_phase_good p hp
      simp [phaseJunk_not_s2 p, ihl (nextPhase p) hnext, ihr (nextPhase p) hnext]

theorem hub_logicalTreeStrict (flag tape : Term) (d : Nat)
    (hf : logicalTreeStrict flag = true) (ht : logicalTreeStrict tape = true) :
    logicalTreeStrict (frameTerm flag tape (depthJunk d)) = true := by
  unfold depthJunk
  rw [logicalTreeStrict_frame]
  simp [phaseJunk_not_s2 (phaseAt d), hf, ht]

theorem replaceTermAt_self (path : List Bool) :
    ∀ root focus, termAt root path = some focus → replaceTermAt root path focus = some root := by
  induction path with
  | nil =>
      intro root focus hat
      rw [term_at_nil] at hat
      cases hat
      exact replace_at_nil _ _
  | cons side rest ih =>
      intro root focus hat
      cases root with
      | s => simp [termAt] at hat
      | var _ => simp [termAt] at hat
      | app l r =>
          cases side with
          | false =>
              simp only [termAt, replaceTermAt] at hat ⊢
              rw [ih l focus hat]
              rfl
          | true =>
              simp only [termAt, replaceTermAt] at hat ⊢
              rw [ih r focus hat]
              rfl

theorem replace_physicalPath_logicalTreeStrict (path : List Bool) :
    ∀ shape p mid out,
      goodPhase p →
      subLayout shape path = some .unopened →
      replaceTermAt (layoutTerm shape p.1 p.2) (physicalPath path) mid = some out →
      logicalTreeStrict mid = true →
      logicalTreeStrict out = true := by
  induction path with
  | nil =>
      intro _ _ mid out _ _ hrep hmid
      rw [physicalPath, replace_at_nil] at hrep
      cases hrep
      exact hmid
  | cons side rest ih =>
      intro shape p mid out hp hslot hrep hmid
      cases shape with
      | unopened => simp [subLayout] at hslot
      | opened l r =>
          rw [layout_opened_phase l r p hp] at hrep
          have hnext := next_phase_good p hp
          cases side with
          | false =>
              have hlslot : subLayout l rest = some .unopened := by simpa [subLayout] using hslot
              simp only [physicalPath, List.cons_append, List.nil_append, frameTerm, replaceTermAt] at hrep
              cases hx : replaceTermAt (layoutTerm l (nextPhase p).1 (nextPhase p).2) (physicalPath rest) mid with
              | none => simp [hx] at hrep
              | some l' =>
                  simp [hx] at hrep
                  subst out
                  change logicalTreeStrict (frameTerm l' (layoutTerm r (nextPhase p).1 (nextPhase p).2) (phaseJunk p)) = true
                  rw [logicalTreeStrict_frame]
                  simp [phaseJunk_not_s2 p, ih l (nextPhase p) mid l' hnext hlslot hx hmid,
                    layoutTerm_logicalTreeStrict r (nextPhase p) hnext]
          | true =>
              have hrslot : subLayout r rest = some .unopened := by simpa [subLayout] using hslot
              simp only [physicalPath, List.cons_append, List.nil_append, frameTerm, replaceTermAt] at hrep
              cases hx : replaceTermAt (layoutTerm r (nextPhase p).1 (nextPhase p).2) (physicalPath rest) mid with
              | none => simp [hx] at hrep
              | some r' =>
                  simp [hx] at hrep
                  subst out
                  change logicalTreeStrict (frameTerm (layoutTerm l (nextPhase p).1 (nextPhase p).2) r' (phaseJunk p)) = true
                  rw [logicalTreeStrict_frame]
                  simp [phaseJunk_not_s2 p, layoutTerm_logicalTreeStrict l (nextPhase p) hnext,
                    ih r (nextPhase p) mid r' hnext hrslot hx hmid]

/-- A `ClosedOpeningTrace` where every stage satisfies `logicalTreeStrict` and `leaves a ≤ leaves b`. -/
inductive NiceOpeningTrace : Nat → Term → Term → Prop where
  | finish {a b : Term} :
      ChosenStep a b → logicalTreeStrict a = true → logicalTreeStrict b = true →
      leaves a ≤ leaves b → layoutMatches (.opened .unopened .unopened) b →
      NiceOpeningTrace 1 a b
  | more {n : Nat} {a b c : Term} :
      ChosenStep a b → logicalTreeStrict a = true → parseFrame b = none →
      leaves a ≤ leaves b → NiceOpeningTrace n b c →
      NiceOpeningTrace (n + 1) a c

theorem positive_nice_opening_trace (m n : Nat) :
    NiceOpeningTrace 6 (generator (m + 1) (n + 2))
      (frameTerm (generator m (n + 2)) (generator m (n + 2))
        ((numeral n ⋅ S) ⋅ generator m (n + 2))) := by
  let mT := numeral m
  let nT := numeral n
  let n1 := B ⋅ nT
  let n2 := B ⋅ n1
  let q := mT ⋅ n2
  let g := mT ⋅ n2 ⋅ S
  have ⟨c1, c2, c3, c4, c5, c6, _⟩ := opening_selector_six_stages mT nT
  have ⟨u0, u1, u2, u3, u4, u5⟩ := intermediate_frames_closed mT nT
  have h1 : ChosenStep ((B ⋅ mT) ⋅ n2 ⋅ S) (S ⋅ n2 ⋅ q ⋅ S) :=
    ⟨[false], c1, DirectedStep.left (DirectedStep.root S mT n2)⟩
  have h2 : ChosenStep (S ⋅ n2 ⋅ q ⋅ S) ((n2 ⋅ S) ⋅ g) :=
    ⟨[], c2, DirectedStep.root n2 q S⟩
  have h3 : ChosenStep ((n2 ⋅ S) ⋅ g) ((B ⋅ (n1 ⋅ S)) ⋅ g) :=
    ⟨[false], c3, DirectedStep.left (DirectedStep.root S n1 S)⟩
  have h4 : ChosenStep ((B ⋅ (n1 ⋅ S)) ⋅ g) (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) :=
    ⟨[], c4, DirectedStep.root S (n1 ⋅ S) g⟩
  have h5 : ChosenStep (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) (S ⋅ g ⋅ ((B ⋅ (nT ⋅ S)) ⋅ g)) :=
    ⟨[true, false], c5, DirectedStep.right (DirectedStep.left (DirectedStep.root S nT S))⟩
  have h6 : ChosenStep (S ⋅ g ⋅ ((B ⋅ (nT ⋅ S)) ⋅ g)) (S ⋅ g ⋅ (S ⋅ g ⋅ ((nT ⋅ S) ⋅ g))) :=
    ⟨[true], c6, DirectedStep.right (DirectedStep.root S (nT ⋅ S) g)⟩
  have hgClosed : parseFrame g = none := parse_generator_closed m (n + 2)
  have hgStrict : logicalTreeStrict g = true := logicalTreeStrict_closed hgClosed
  have st6 : logicalTreeStrict (frameTerm g g ((nT ⋅ S) ⋅ g)) = true := by
    dsimp only [nT]
    rw [logicalTreeStrict_frame]
    simp [generated_junk_not_s2 n g, hgStrict]
  have hf : layoutMatches (.opened .unopened .unopened) (S ⋅ g ⋅ (S ⋅ g ⋅ ((nT ⋅ S) ⋅ g))) :=
    ⟨g, g, (nT ⋅ S) ⋅ g, parse_frame _ _ _, hgClosed, hgClosed⟩
  have l01 : leaves ((B ⋅ mT) ⋅ n2 ⋅ S) ≤ leaves (S ⋅ n2 ⋅ q ⋅ S) := by
    simp [mT, nT, n1, n2, q, leaves, B, S, numeral_leaves]; omega
  have l12 : leaves (S ⋅ n2 ⋅ q ⋅ S) ≤ leaves ((n2 ⋅ S) ⋅ g) := by
    simp [mT, nT, n1, n2, q, g, leaves, B, S, numeral_leaves]; omega
  have l23 : leaves ((n2 ⋅ S) ⋅ g) ≤ leaves ((B ⋅ (n1 ⋅ S)) ⋅ g) := by
    simp [mT, nT, n1, n2, g, leaves, B, S, numeral_leaves]; omega
  have l34 : leaves ((B ⋅ (n1 ⋅ S)) ⋅ g) ≤ leaves (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) := by
    simp [mT, nT, n1, n2, g, leaves, B, S, numeral_leaves]; omega
  have l45 : leaves (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) ≤ leaves (S ⋅ g ⋅ ((B ⋅ (nT ⋅ S)) ⋅ g)) := by
    simp [mT, nT, n1, n2, g, leaves, B, S, numeral_leaves]; omega
  have l56 : leaves (S ⋅ g ⋅ ((B ⋅ (nT ⋅ S)) ⋅ g)) ≤ leaves (S ⋅ g ⋅ (S ⋅ g ⋅ ((nT ⋅ S) ⋅ g))) := by
    simp [mT, nT, n1, n2, g, leaves, B, S, numeral_leaves]; omega
  exact NiceOpeningTrace.more h1 (logicalTreeStrict_closed u0) u1 l01
    (NiceOpeningTrace.more h2 (logicalTreeStrict_closed u1) u2 l12
      (NiceOpeningTrace.more h3 (logicalTreeStrict_closed u2) u3 l23
        (NiceOpeningTrace.more h4 (logicalTreeStrict_closed u3) u4 l34
          (NiceOpeningTrace.more h5 (logicalTreeStrict_closed u4) u5 l45
            (NiceOpeningTrace.finish h6 (logicalTreeStrict_closed u5) st6 l56 hf)))))

theorem zero_nice_opening_trace (n : Nat) :
    NiceOpeningTrace 7 (generator 0 (n + 2))
      (frameTerm (generator (n + 2) (n + 3)) (generator (n + 2) (n + 3))
        ((numeral (n + 1) ⋅ S) ⋅ generator (n + 2) (n + 3))) := by
  have first : ChosenStep (generator 0 (n + 2)) (generator (n + 3) (n + 3)) :=
    ⟨[false], opening_selector_zero_phase (n + 2),
      DirectedStep.left (DirectedStep.root B B (numeral (n + 2)))⟩
  have hle : leaves (generator 0 (n + 2)) ≤ leaves (generator (n + 3) (n + 3)) := by
    simp [generator_leaves]
    omega
  exact NiceOpeningTrace.more first
    (logicalTreeStrict_closed (parse_generator_closed 0 (n + 2)))
    (parse_generator_closed (n + 3) (n + 3)) hle
    (positive_nice_opening_trace (n + 2) (n + 1))

theorem good_phase_nice_opening_trace (p : Nat × Nat) (hp : goodPhase p) :
    ∃ k, (k = 6 ∨ k = 7) ∧
      NiceOpeningTrace k (phaseBase p) (layoutTerm (.opened .unopened .unopened) p.1 p.2) := by
  rcases p with ⟨m, n⟩
  have hn : 2 ≤ n := hp.1
  cases n with
  | zero => exact False.elim (by omega)
  | succ n =>
      cases n with
      | zero => exact False.elim (by omega)
      | succ n =>
          cases m with
          | zero => exact ⟨7, Or.inr rfl, zero_nice_opening_trace n⟩
          | succ m => exact ⟨6, Or.inl rfl, positive_nice_opening_trace m n⟩

theorem replaceTermAt_leaves_mono (path : List Bool) :
    ∀ root1 root2 a b,
      replaceTermAt root1 path a = some root2 →
      termAt root1 path = some b →
      leaves b ≤ leaves a →
      leaves root1 ≤ leaves root2 := by
  induction path with
  | nil =>
      intro root1 root2 a b hrep hat hle
      rw [replace_at_nil] at hrep
      rw [term_at_nil] at hat
      cases hrep
      cases hat
      exact hle
  | cons side rest ih =>
      intro root1 root2 a b hrep hat hle
      cases root1 with
      | s => simp [termAt] at hat
      | var _ => simp [termAt] at hat
      | app l r =>
          cases side with
          | false =>
              simp only [replaceTermAt, termAt] at hrep hat
              cases hx : replaceTermAt l rest a with
              | none => simp [hx] at hrep
              | some l' =>
                  simp [hx] at hrep
                  subst root2
                  have hsub := ih l l' a b hx hat hle
                  simp [leaves]; omega
          | true =>
              simp only [replaceTermAt, termAt] at hrep hat
              cases hx : replaceTermAt r rest a with
              | none => simp [hx] at hrep
              | some r' =>
                  simp [hx] at hrep
                  subst root2
                  have hsub := ih r r' a b hx hat hle
                  simp [leaves]; omega

/-- Version-level adaptive trace carrying `logicalTreeStrict a` and `leaves a ≤ leaves b`. -/
inductive NiceStableAdaptiveTrace (width : Nat) (desired : List Bool) (old : Option (List Bool)) :
    Nat → Term → Term → Prop where
  | zero (a : Term) : NiceStableAdaptiveTrace width desired old 0 a a
  | next {n : Nat} {a b c : Term} :
      logicalTreeStrict a = true →
      leaves a ≤ leaves b →
      StableAdaptiveStep width desired old a b →
      NiceStableAdaptiveTrace width desired old n b c →
      NiceStableAdaptiveTrace width desired old (n + 1) a c

theorem niceStableAdaptive_trans {width : Nat} {desired : List Bool} {old : Option (List Bool)}
    {n m : Nat} {a b c : Term}
    (h1 : NiceStableAdaptiveTrace width desired old n a b)
    (h2 : NiceStableAdaptiveTrace width desired old m b c) :
    NiceStableAdaptiveTrace width desired old (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | next hs hle hstep _ ih =>
      have r := NiceStableAdaptiveTrace.next hs hle hstep (ih h2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem lift_nice_opening_stable_value {width n : Nat}
    {records : List {bits : List Bool // bits.length = width}} {old final : Term}
    (trace : NiceOpeningTrace n old final) :
    ∀ shape term path fuel desired p,
      goodPhase p →
      FuelAgreement fuel width desired shape →
      StableVersionValue records shape →
      layoutMatches shape term →
      subLayout shape path = some .unopened →
      termAt term (physicalPath path) = some old →
      replaceTermAt (layoutTerm shape p.1 p.2) (physicalPath path) old = some term →
      chooseSVersion fuel width desired term = some (physicalPath path) →
      ∃ target out,
        openLayoutAt shape path = some target ∧
        layoutMatches target out ∧
        replaceTermAt term (physicalPath path) final = some out ∧
        NiceStableAdaptiveTrace width desired (newestRecords records none) n term out := by
  induction trace with
  | @finish a b hchosen haStrict _ hleAB hopen =>
      intro shape term path fuel desired p hp hagree hstable hmatch hslot hat hrepBase hchoose
      obtain ⟨relpath, hlocal, hdir⟩ := hchosen
      obtain ⟨target, out, hopenLayout, hout, hmatchout, _⟩ :=
        opened_slot_step_updates_layout path shape term a b relpath hmatch hslot hat hdir hopen
      obtain ⟨out', hreplace, hout'⟩ :=
        directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
      have heq : out = out' := directed_step_unique hout out' hout'
      subst out'
      have htree : chooseSVersionTree width desired term = some (physicalPath path) := by
        rw [hagree term hmatch, hchoose]
      have htermStrict : logicalTreeStrict term = true :=
        replace_physicalPath_logicalTreeStrict path shape p a term hp hslot hrepBase haStrict
      have hleavesLe : leaves term ≤ leaves out :=
        replaceTermAt_leaves_mono (physicalPath path) term out b a hreplace hat hleAB
      have hstep : StableAdaptiveStep width desired (newestRecords records none) term out :=
        ⟨⟨path, htree, a, relpath, hat, hlocal, hout⟩, hstable term hmatch⟩
      exact ⟨target, out, hopenLayout, hmatchout, hreplace,
        NiceStableAdaptiveTrace.next htermStrict hleavesLe hstep (NiceStableAdaptiveTrace.zero out)⟩
  | @more n a b c hchosen haStrict hclosed hleAB _ ih =>
      intro shape term path fuel desired p hp hagree hstable hmatch hslot hat hrepBase hchoose
      obtain ⟨relpath, hlocal, hdir⟩ := hchosen
      obtain ⟨middle, hmiddle, hatMiddle, hchooseMiddle, hmatchMiddle⟩ :=
        restarted_selector_preserves_target shape term a b path relpath fuel width desired
          hmatch hslot hat hdir hclosed hchoose
      obtain ⟨middle', hreplaceFirst, hmiddle'⟩ :=
        directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
      have heq : middle = middle' := directed_step_unique hmiddle middle' hmiddle'
      subst middle'
      have hrepMidBase : replaceTermAt (layoutTerm shape p.1 p.2) (physicalPath path) b = some middle := by
        rw [← replace_same_path_overwrites (physicalPath path) _ a term b hrepBase]
        exact hreplaceFirst
      obtain ⟨target, out, hopenLayout, hmatchout, hreplaceRest, htrace⟩ :=
        ih shape middle path fuel desired p hp hagree hstable hmatchMiddle hslot hatMiddle hrepMidBase hchooseMiddle
      have hreplace : replaceTermAt term (physicalPath path) c = some out := by
        rw [← replace_same_path_overwrites (physicalPath path) term b middle c hreplaceFirst]
        exact hreplaceRest
      have htree : chooseSVersionTree width desired term = some (physicalPath path) := by
        rw [hagree term hmatch, hchoose]
      have htermStrict : logicalTreeStrict term = true :=
        replace_physicalPath_logicalTreeStrict path shape p a term hp hslot hrepBase haStrict
      have hleavesLe : leaves term ≤ leaves middle :=
        replaceTermAt_leaves_mono (physicalPath path) term middle b a hreplaceFirst hat hleAB
      have hstep : StableAdaptiveStep width desired (newestRecords records none) term middle :=
        ⟨⟨path, htree, a, relpath, hat, hlocal, hmiddle⟩, hstable term hmatch⟩
      exact ⟨target, out, hopenLayout, hmatchout, hreplace,
        NiceStableAdaptiveTrace.next htermStrict hleavesLe hstep htrace⟩

theorem canonical_selected_opening_nice {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (shape target : Layout) (path : List Bool) (d fuel : Nat) (desired : List Bool)
    (hagree : FuelAgreement fuel width desired shape) (hstable : StableVersionValue records shape)
    (hopen : openLayoutAt shape path = some target)
    (hchoose : chooseSVersion fuel width desired (layoutTerm shape (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath path)) :
    ∃ k, (k = 6 ∨ k = 7) ∧
      NiceStableAdaptiveTrace width desired (newestRecords records none) k
        (layoutTerm shape (phaseAt d).1 (phaseAt d).2)
        (layoutTerm target (phaseAt d).1 (phaseAt d).2) := by
  let p := phaseAt d
  let q := advancePhase path.length p
  have hp : goodPhase p := phase_at_good d
  have hq : goodPhase q := advance_phase_good path.length p hp
  have hslot : subLayout shape path = some .unopened := open_layout_targets_unopened path shape target hopen
  have hat : termAt (layoutTerm shape p.1 p.2) (physicalPath path) = some (phaseBase q) :=
    (selected_slot_is_generator shape target path p hp hopen).2
  have hrepSelf := replaceTermAt_self (physicalPath path) (layoutTerm shape p.1 p.2) (phaseBase q) hat
  have hmatch : layoutMatches shape (layoutTerm shape p.1 p.2) := finite_layout_decodes shape p.1 p.2 hp.1 hp.2
  obtain ⟨k, hk, htrace⟩ := good_phase_nice_opening_trace q hq
  obtain ⟨target', out, hopen', _, hreplace, hglobal⟩ :=
    lift_nice_opening_stable_value htrace shape (layoutTerm shape p.1 p.2)
      path fuel desired p hp hagree hstable hmatch hslot hat hrepSelf hchoose
  have htarget : target' = target := by rw [hopen] at hopen'; exact (Option.some.inj hopen').symm
  subst target'
  have hcanonical := canonical_layout_replace path shape target p hp hopen
  have hout : out = layoutTerm target p.1 p.2 := by rw [hcanonical] at hreplace; exact (Option.some.inj hreplace).symm
  subst out
  exact ⟨k, hk, hglobal⟩

theorem nice_stable_version_trace_native {width : Nat}
    {records : List {bits : List Bool // bits.length = width}} {fuel : Nat} {desired : List Bool}
    {n : Nat} {a b : Layout} (trace : StableVersionTrace records fuel desired n a b) (d : Nat) :
    ∃ k, NiceStableAdaptiveTrace width desired (newestRecords records none) k
        (layoutTerm a (phaseAt d).1 (phaseAt d).2) (layoutTerm b (phaseAt d).1 (phaseAt d).2) ∧
      6 * n ≤ k ∧ k ≤ 7 * n := by
  induction trace with
  | done _ => exact ⟨0, NiceStableAdaptiveTrace.zero _, by simp, by simp⟩
  | @next n a b c path hagree hstable hchoose hopen _ ih =>
      have hS : chooseSVersion fuel width desired (layoutTerm a (phaseAt d).1 (phaseAt d).2) =
          some (physicalPath path) := by
        rw [choose_s_version_simulates_layout fuel width desired a (phaseAt d) (phase_at_good d), hchoose]
        rfl
      obtain ⟨first, hfirst, hrun⟩ :=
        canonical_selected_opening_nice records a b path d fuel desired hagree hstable hopen hS
      obtain ⟨last, hlast, hlower, hupper⟩ := ih
      refine ⟨first + last, niceStableAdaptive_trans hrun hlast, ?_, ?_⟩
      · cases hfirst <;> omega
      · cases hfirst <;> omega

theorem nice_version_append (records : List UniversalCell) (entry : UniversalCell) (d : Nat) :
    ∃ k,
      NiceStableAdaptiveTrace 11 (encodedEntry entry).val (newestRecords (records.map encodedEntry) none) k
        (concreteVersion records d) (concreteVersion (records ++ [entry]) d) ∧
      6 ≤ k ∧ k ≤ 168 := by
  obtain ⟨n, htrace, hnlo, hnhi⟩ := stable_version_append_complete (records.map encodedEntry) (encodedEntry entry)
  obtain ⟨k, hreal, klo, khi⟩ := nice_stable_version_trace_native htrace d
  refine ⟨k, ?_, by omega, by omega⟩
  simpa [concreteVersion, List.map_append] using hreal

/-- Canonical trajectory trace recording `seedHubRoot` shape with `logicalTreeStrict`
    on the hub and step-by-step leaf monotonicity `leaves a ≤ leaves b`. -/
inductive NiceSelectorTrace (program : BinaryProgram) : Nat → Term → Term → Prop where
  | zero (a : Term) : NiceSelectorTrace program 0 a a
  | next {n : Nat} {a b c : Term} {path : List Bool} :
      (∃ flag tape,
        a = seedHubRoot flag tape (depthJunk 0) ∧
        logicalTreeStrict (frameTerm flag tape (depthJunk 0)) = true) →
      leaves a ≤ leaves b →
      fullRootSelector program a = some path →
      DirectedStep path a b →
      NiceSelectorTrace program n b c →
      NiceSelectorTrace program (n + 1) a c

theorem niceSelectorTrace_trans {program : BinaryProgram} {n m : Nat} {a b c : Term}
    (h1 : NiceSelectorTrace program n a b) (h2 : NiceSelectorTrace program m b c) :
    NiceSelectorTrace program (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | next hhub hle hsel hdir _ ih =>
      have r := NiceSelectorTrace.next hhub hle hsel hdir (ih h2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem niceSelectorTrace_leaves_le {program : BinaryProgram} {n : Nat} {a b : Term}
    (h : NiceSelectorTrace program n a b) : leaves a ≤ leaves b := by
  induction h with
  | zero _ => exact Nat.le_refl _
  | next _ hle _ _ _ ih => omega

theorem niceSelectorTrace_prefix_props {program : BinaryProgram} {M k : Nat}
    {start checkpoint reached : Term}
    (hnice : NiceSelectorTrace program M start checkpoint)
    (hfull : FullSelectorTrace program k start reached)
    (hk : k < M) :
    (∃ flag tape,
      reached = seedHubRoot flag tape (depthJunk 0) ∧
      logicalTreeStrict (frameTerm flag tape (depthJunk 0)) = true) ∧
    leaves reached ≤ leaves checkpoint := by
  induction k generalizing M start with
  | zero =>
      cases hfull
      cases hnice with
      | zero _ => exact False.elim (by omega)
      | next hhub hle _ _ rest =>
          have hrest := niceSelectorTrace_leaves_le rest
          exact ⟨hhub, by omega⟩
  | succ k ih =>
      cases hfull with
      | @next _ _ mid1 _ path1 hs1 hd1 tailFull =>
          cases hnice with
          | zero _ => exact False.elim (by omega)
          | @next _ _ b _ path2 _ _ hs2 hd2 restNice =>
              have heq : b = mid1 := full_selector_step_unique program start b mid1 path2 path1 hs2 hs1 hd2 hd1
              subst mid1
              exact ih restNice tailFull (by omega)

def StrictPrefixPairs (earlier : List (Term × Term)) : Prop :=
  ∀ x ∈ earlier, logicalTreeStrict x.1 = true ∧ isS2Term x.2 = false

theorem canonicalPrefix_strict (before : List (List UniversalCell)) :
    ∀ d, StrictPrefixPairs (canonicalPrefix before d) := by
  induction before with
  | nil => intro _ x hx; simp [canonicalPrefix] at hx
  | cons cell rest ih =>
      intro d x hx
      simp only [canonicalPrefix, List.mem_cons] at hx
      rcases hx with rfl | htail
      · exact ⟨layoutTerm_logicalTreeStrict _ _ (phase_at_good (d + 1)),
          phaseJunk_not_s2 (phaseAt d)⟩
      · exact ih (d + 1) x htail

theorem tapeAroundVersion_strict (earlier : List (Term × Term)) (v tail junk : Term)
    (he : StrictPrefixPairs earlier)
    (hv : logicalTreeStrict v = true) (ht : logicalTreeStrict tail = true)
    (hns2 : isS2Term junk = false) :
    logicalTreeStrict (tapeAroundVersion earlier v tail junk) = true := by
  induction earlier with
  | nil =>
      simp [tapeAroundVersion, logicalTreeStrict_frame, hns2, hv, ht]
  | cons pair rest ih =>
      rcases pair with ⟨pv, pj⟩
      have hp0 := he (pv, pj) (by simp)
      have hrest : StrictPrefixPairs rest := fun x hx => he x (by simp [hx])
      simp [tapeAroundVersion, logicalTreeStrict_frame, hp0.1, hp0.2, ih hrest]

theorem prependTape_strict (earlier : List (Term × Term)) (tail : Term)
    (he : StrictPrefixPairs earlier) (ht : logicalTreeStrict tail = true) :
    logicalTreeStrict (prependTape earlier tail) = true := by
  induction earlier with
  | nil => exact ht
  | cons pair rest ih =>
      rcases pair with ⟨pv, pj⟩
      have hp0 := he (pv, pj) (by simp)
      have hrest : StrictPrefixPairs rest := fun x hx => he x (by simp [hx])
      simp [prependTape, logicalTreeStrict_frame, hp0.1, hp0.2, ih hrest]

theorem tapeAroundVersion_leaves_mono (earlier : List (Term × Term)) (a b tail junk : Term)
    (hle : leaves a ≤ leaves b) :
    leaves (tapeAroundVersion earlier a tail junk) ≤ leaves (tapeAroundVersion earlier b tail junk) := by
  induction earlier with
  | nil => simp [tapeAroundVersion, frame_leaves]; omega
  | cons pair rest ih =>
      rcases pair with ⟨pv, pj⟩
      simp [tapeAroundVersion, frame_leaves]
      omega

theorem prependTape_leaves_mono (earlier : List (Term × Term)) (a b : Term)
    (hle : leaves a ≤ leaves b) :
    leaves (prependTape earlier a) ≤ leaves (prependTape earlier b) := by
  induction earlier with
  | nil => exact hle
  | cons pair rest ih =>
      rcases pair with ⟨pv, pj⟩
      simp [prependTape, frame_leaves]
      omega

theorem to_hubStableStep (earlier : List (Term × Term)) (tail junk initial flag : Term)
    (desired : List Bool) (old : Option (List Bool))
    (hinit : scanVersionTree 11 none initial = old) {a b : Term}
    (hstep : StableAdaptiveStep 11 desired old a b) :
    HubStableStep earlier tail junk initial flag (depthJunk 0) desired a b := by
  obtain ⟨⟨path, hchoose, focus, relpath, hat, hlocal, hdir⟩, hvalue⟩ := hstep
  have hcell : cellFromVersion a = cellFromVersion initial := by
    unfold cellFromVersion; rw [hvalue, hinit]
  have hpriority := priority_ignores_equivalent_version earlier a initial tail junk hcell
  have hlift := directed_protected_context (tapeFrames earlier tail junk) hdir
  have hseed := tape_step_under_seed_hub
    (by simpa [← tape_around_is_protected_context] using hlift) flag (depthJunk 0)
  refine ⟨hpriority, hcell, path, focus, relpath, hchoose, hat, hlocal, ?_⟩
  simpa [List.append_assoc] using hseed

theorem active_nice_trace (program : BinaryProgram)
    (earlier : List (Term × Term)) (tail junk initial flag : Term) (record : Cell)
    (he : StrictPrefixPairs earlier) (ht : logicalTreeStrict tail = true)
    (hns2 : isS2Term junk = false)
    (hf : logicalTreeStrict flag = true)
    (hflag : flagValue flag = false)
    (hpriority : priorityConcretePath (tapeAroundVersion earlier initial tail junk) = .active (prefixPath earlier))
    (hstate : (cellFromVersion initial).state < 132)
    (hplan : activePlan (prefixPath earlier) (prefixPath earlier).isEmpty
        (program ⟨(cellFromVersion initial).state, hstate⟩ (cellFromVersion initial).bit) =
      .append (prefixPath earlier) record)
    (old : Option (List Bool)) (hinit : scanVersionTree 11 none initial = old)
    {n : Nat} {a b : Term}
    (trace : NiceStableAdaptiveTrace 11 (encodeCellBits record (stateBits8 record.state)) old n a b) :
    NiceSelectorTrace program n
      (seedHubRoot flag (tapeAroundVersion earlier a tail junk) (depthJunk 0))
      (seedHubRoot flag (tapeAroundVersion earlier b tail junk) (depthJunk 0)) := by
  induction trace with
  | zero _ => exact NiceSelectorTrace.zero _
  | @next n a b c haStrict hleAB hstep _ ih =>
      have hhubStep := to_hubStableStep earlier tail junk initial flag _ old hinit hstep
      obtain ⟨path, hsel, hdir⟩ :=
        active_global_step_is_full_selector program earlier tail junk initial flag (depthJunk 0) record a b
          hflag hpriority hstate hplan hhubStep
      have hhubStrict := hub_logicalTreeStrict flag _ 0 hf
        (tapeAroundVersion_strict earlier a tail junk he haStrict ht hns2)
      have hrootLe :
          leaves (seedHubRoot flag (tapeAroundVersion earlier a tail junk) (depthJunk 0)) ≤
            leaves (seedHubRoot flag (tapeAroundVersion earlier b tail junk) (depthJunk 0)) := by
        have htapeLe := tapeAroundVersion_leaves_mono earlier a b tail junk hleAB
        simp [seedHubRoot, frame_leaves, leaves]; omega
      exact NiceSelectorTrace.next ⟨flag, _, rfl, hhubStrict⟩ hrootLe hsel hdir ih

theorem pending_nice_trace (program : BinaryProgram)
    (earlier : List (Term × Term)) (tail junk initial flag : Term) (record pending targetCell : Cell)
    (sourcePath targetPath : List Bool)
    (he : StrictPrefixPairs earlier) (ht : logicalTreeStrict tail = true)
    (hns2 : isS2Term junk = false)
    (hf : logicalTreeStrict flag = true)
    (hflag : flagValue flag = false)
    (hpriority : priorityConcretePath (tapeAroundVersion earlier initial tail junk) = .pending sourcePath)
    (hsource : ∀ v, cellFromVersion v = cellFromVersion initial →
      readCellAt (tapeAroundVersion earlier v tail junk) sourcePath = some pending)
    (hdestination : pendingDestinationPath pending sourcePath = some targetPath)
    (htarget : ∀ v, cellFromVersion v = cellFromVersion initial →
      ∃ targetTerm targetVersion targetTail targetJunk,
        termAt (tapeAroundVersion earlier v tail junk) targetPath = some targetTerm ∧
        parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧
        cellFromVersion targetVersion = targetCell)
    (hplan : pendingPlan sourcePath targetPath pending (some targetCell) = .append (prefixPath earlier) record)
    (old : Option (List Bool)) (hinit : scanVersionTree 11 none initial = old)
    {n : Nat} {a b : Term}
    (trace : NiceStableAdaptiveTrace 11 (encodeCellBits record (stateBits8 record.state)) old n a b) :
    NiceSelectorTrace program n
      (seedHubRoot flag (tapeAroundVersion earlier a tail junk) (depthJunk 0))
      (seedHubRoot flag (tapeAroundVersion earlier b tail junk) (depthJunk 0)) := by
  induction trace with
  | zero _ => exact NiceSelectorTrace.zero _
  | @next n a b c haStrict hleAB hstep _ ih =>
      have hhubStep := to_hubStableStep earlier tail junk initial flag _ old hinit hstep
      obtain ⟨path, hsel, hdir⟩ :=
        pending_global_step_general program earlier tail junk initial flag (depthJunk 0)
          record pending targetCell sourcePath targetPath a b
          hflag hpriority hsource hdestination htarget hplan hhubStep
      have hhubStrict := hub_logicalTreeStrict flag _ 0 hf
        (tapeAroundVersion_strict earlier a tail junk he haStrict ht hns2)
      have hrootLe :
          leaves (seedHubRoot flag (tapeAroundVersion earlier a tail junk) (depthJunk 0)) ≤
            leaves (seedHubRoot flag (tapeAroundVersion earlier b tail junk) (depthJunk 0)) := by
        have htapeLe := tapeAroundVersion_leaves_mono earlier a b tail junk hleAB
        simp [seedHubRoot, frame_leaves, leaves]; omega
      exact NiceSelectorTrace.next ⟨flag, _, rfl, hhubStrict⟩ hrootLe hsel hdir ih

theorem pending_tail_nice_trace (program : BinaryProgram)
    (earlier : List (Term × Term)) (version junk flag : Term) (bit : Bool) (q : Nat)
    (he : StrictPrefixPairs earlier) (hv : logicalTreeStrict version = true)
    (hns2 : isS2Term junk = false)
    (hf : logicalTreeStrict flag = true)
    (hflag : flagValue flag = false)
    (hprefix : ∀ x ∈ earlier, (cellFromVersion x.1).status = .off)
    (hpending : cellFromVersion version = ⟨bit, .movingRight, q⟩)
    {n : Nat} {a b : Term} (trace : NiceOpeningTrace n a b) :
    NiceSelectorTrace program n
      (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) (depthJunk 0))
      (seedHubRoot flag (prependTape earlier (frameTerm version b junk)) (depthJunk 0)) := by
  have hmoving : isMoving (cellFromVersion version).status = true := by rw [hpending]; rfl
  induction trace with
  | @finish a b hchosen haStrict _ hleAB _ =>
      have hp : priorityConcretePath (prependTape earlier (frameTerm version a junk)) = .pending (prefixPath earlier) :=
        prefixed_single_pending_priority earlier version a junk hprefix hmoving
      obtain ⟨rel, hlocal, hdir⟩ := hchosen
      have hctx := directed_protected_context (tailFrames earlier version junk) hdir
      have hroot := tape_step_under_seed_hub
        (by simpa [← tail_context_representation] using hctx) flag (depthJunk 0)
      have hhubStep : HubPendingTailStep earlier version junk flag (depthJunk 0) a b :=
        ⟨hp, rel, hlocal, by simpa [List.append_assoc] using hroot⟩
      obtain ⟨path, hsel, hd⟩ :=
        pending_tail_step_is_full_selector program earlier version junk flag (depthJunk 0) bit q a b hflag hpending hhubStep
      have hcellStrict : logicalTreeStrict (frameTerm version a junk) = true := by
        simp [logicalTreeStrict_frame, hns2, hv, haStrict]
      have hhubStrict := hub_logicalTreeStrict flag _ 0 hf (prependTape_strict earlier _ he hcellStrict)
      have hrootLe :
          leaves (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) (depthJunk 0)) ≤
            leaves (seedHubRoot flag (prependTape earlier (frameTerm version b junk)) (depthJunk 0)) := by
        have htapeLe := prependTape_leaves_mono earlier (frameTerm version a junk) (frameTerm version b junk)
          (by simp [frame_leaves]; omega)
        simp [seedHubRoot, frame_leaves, leaves]; omega
      exact NiceSelectorTrace.next ⟨flag, _, rfl, hhubStrict⟩ hrootLe hsel hd (NiceSelectorTrace.zero _)
  | @more n a b c hchosen haStrict _ hleAB _ ih =>
      have hp : priorityConcretePath (prependTape earlier (frameTerm version a junk)) = .pending (prefixPath earlier) :=
        prefixed_single_pending_priority earlier version a junk hprefix hmoving
      obtain ⟨rel, hlocal, hdir⟩ := hchosen
      have hctx := directed_protected_context (tailFrames earlier version junk) hdir
      have hroot := tape_step_under_seed_hub
        (by simpa [← tail_context_representation] using hctx) flag (depthJunk 0)
      have hhubStep : HubPendingTailStep earlier version junk flag (depthJunk 0) a b :=
        ⟨hp, rel, hlocal, by simpa [List.append_assoc] using hroot⟩
      obtain ⟨path, hsel, hd⟩ :=
        pending_tail_step_is_full_selector program earlier version junk flag (depthJunk 0) bit q a b hflag hpending hhubStep
      have hcellStrict : logicalTreeStrict (frameTerm version a junk) = true := by
        simp [logicalTreeStrict_frame, hns2, hv, haStrict]
      have hhubStrict := hub_logicalTreeStrict flag _ 0 hf (prependTape_strict earlier _ he hcellStrict)
      have hrootLe :
          leaves (seedHubRoot flag (prependTape earlier (frameTerm version a junk)) (depthJunk 0)) ≤
            leaves (seedHubRoot flag (prependTape earlier (frameTerm version b junk)) (depthJunk 0)) := by
        have htapeLe := prependTape_leaves_mono earlier (frameTerm version a junk) (frameTerm version b junk)
          (by simp [frame_leaves]; omega)
        simp [seedHubRoot, frame_leaves, leaves]; omega
      exact NiceSelectorTrace.next ⟨flag, _, rfl, hhubStrict⟩ hrootLe hsel hd ih

theorem scan_init_concrete (records : List UniversalCell) (d : Nat) :
    scanVersionTree 11 none (concreteVersion records d) = newestRecords (records.map encodedEntry) none := by
  have hp := phase_at_good d
  have hm := finite_layout_decodes (versionLayout (records.map encodedEntry)) (phaseAt d).1 (phaseAt d).2 hp.1 hp.2
  exact scan_tree_committed_records (records.map encodedEntry) _ none hm

theorem source_transition_nice_selector (program : BinaryProgram)
    {start finish : List (List UniversalCell)}
    (h : SourceTransition program start finish) :
    ∃ k, 6 ≤ k ∧ k ≤ 511 ∧
      NiceSelectorTrace program k
        (canonicalRoot start 1 (depthBase 1) (depthJunk 0))
        (canonicalRoot finish 1 (depthBase 1) (depthJunk 0)) := by
  have hfStrict : logicalTreeStrict (depthBase 1) = true :=
    logicalTreeStrict_closed (depth_base_closed 1)
  have hflagClosed : parseFrame (depthBase 1) = none := depth_base_closed 1
  have hv : flagValue (depthBase 1) = false := by simp [flagValue, hflagClosed]
  cases h with
  | stay before source after q bit inst hbefore hsource hafter hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | left => cases hdir
          | right => cases hdir
          | stay =>
              let active := activeCellRecord written nextState
              let earlier := canonicalPrefix before 1
              let sd := 1 + before.length + 1
              let sj := depthJunk (1 + before.length)
              let tail := canonicalTape after (1 + before.length + 1)
              let s0 := concreteVersion source sd
              obtain ⟨k, trace, hlo, hhi⟩ := nice_version_append source active sd
              have hprefix := canonical_prefix_off before 1 hbefore
              have htail := (canonical_tape_off_no_work after (1 + before.length + 1) hafter).1
              have hs0 : cellFromVersion s0 = ⟨bit, .active, q.val⟩ := by
                simpa [s0, concrete_version_decodes, ActiveAt] using hsource
              have hpriority : priorityConcretePath (tapeAroundVersion earlier s0 tail sj) = .active (prefixPath earlier) := by
                rw [tape_around_single]
                exact prefixed_single_active_priority earlier s0 tail sj hprefix (by rw [hs0]) htail
              have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
              have hplan : activePlan (prefixPath earlier) (prefixPath earlier).isEmpty
                  (program ⟨(cellFromVersion s0).state, hstate⟩ (cellFromVersion s0).bit) =
                    .append (prefixPath earlier) active.val := by
                have hq : (⟨(cellFromVersion s0).state, hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
                have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
                rw [hq, hbit, hrule]; rfl
              have hnice := active_nice_trace program earlier tail sj s0 (depthBase 1) active.val
                (canonicalPrefix_strict before 1)
                (layoutTerm_logicalTreeStrict (storageTapeLayout after) (phaseAt (1 + before.length + 1))
                  (phase_at_good (1 + before.length + 1)))
                (phaseJunk_not_s2 _) hfStrict
                hv hpriority hstate hplan _ (scan_init_concrete source sd)
                (by simpa [encodedEntry, active] using trace)
              rw [(canonical_single_decompose before source after 1).symm,
                  (canonical_single_decompose before (source ++ [active]) after 1).symm] at hnice
              exact ⟨k, hlo, by omega, hnice⟩
  | leftBoundary source after q bit inst hsource hafter hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | stay => cases hdir
          | right => cases hdir
          | left =>
              let emptyBefore : List (List UniversalCell) := []
              let active := activeCellRecord written nextState
              let earlier := canonicalPrefix emptyBefore 1
              let sd := 1 + emptyBefore.length + 1
              let sj := depthJunk (1 + emptyBefore.length)
              let tail := canonicalTape after (1 + emptyBefore.length + 1)
              let s0 := concreteVersion source sd
              obtain ⟨k, trace, hlo, hhi⟩ := nice_version_append source active sd
              have hoff : AllOff emptyBefore := by intro cell hc; simp [emptyBefore] at hc
              have hprefix := canonical_prefix_off emptyBefore 1 hoff
              have htail := (canonical_tape_off_no_work after (1 + emptyBefore.length + 1) hafter).1
              have hs0 : cellFromVersion s0 = ⟨bit, .active, q.val⟩ := by
                simpa [s0, concrete_version_decodes, ActiveAt] using hsource
              have hpriority : priorityConcretePath (tapeAroundVersion earlier s0 tail sj) = .active (prefixPath earlier) := by
                rw [tape_around_single]
                exact prefixed_single_active_priority earlier s0 tail sj hprefix (by rw [hs0]) htail
              have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
              have hplan : activePlan (prefixPath earlier) (prefixPath earlier).isEmpty
                  (program ⟨(cellFromVersion s0).state, hstate⟩ (cellFromVersion s0).bit) =
                    .append (prefixPath earlier) active.val := by
                have hq : (⟨(cellFromVersion s0).state, hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
                have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
                have hempty : (prefixPath earlier).isEmpty = true := rfl
                rw [hq, hbit, hrule, hempty]; rfl
              have hnice := active_nice_trace program earlier tail sj s0 (depthBase 1) active.val
                (canonicalPrefix_strict emptyBefore 1)
                (layoutTerm_logicalTreeStrict (storageTapeLayout after) (phaseAt (1 + emptyBefore.length + 1))
                  (phase_at_good (1 + emptyBefore.length + 1)))
                (phaseJunk_not_s2 _) hfStrict
                hv hpriority hstate hplan _ (scan_init_concrete source sd)
                (by simpa [encodedEntry, active] using trace)
              rw [(canonical_single_decompose emptyBefore source after 1).symm,
                  (canonical_single_decompose emptyBefore (source ++ [active]) after 1).symm] at hnice
              exact ⟨k, hlo, by omega, hnice⟩
  | rightExisting before source destination after q bit inst hbefore hsource hdestination hafter hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | stay => cases hdir
          | left => cases hdir
          | right =>
              let pending := pendingRightCell written nextState
              let active := activeCellRecord (decodedCell destination).bit nextState
              let off := offCellRecord written
              let earlier := canonicalPrefix before 1
              let sd := 1 + before.length + 1
              let dd := 1 + before.length + 2
              let sj := depthJunk (1 + before.length)
              let dj := depthJunk (1 + before.length + 1)
              let tail := canonicalTape after (1 + before.length + 2)
              let s0 := concreteVersion source sd
              let s1 := concreteVersion (source ++ [pending]) sd
              let s2 := concreteVersion (source ++ [pending, off]) sd
              let d0 := concreteVersion destination dd
              let d1 := concreteVersion (destination ++ [active]) dd
              let srcPath := prefixPath earlier
              let dstPath := srcPath ++ nextCellPath
              obtain ⟨k1, t1, lo1, hi1⟩ := nice_version_append source pending sd
              obtain ⟨k2, t2, lo2, hi2⟩ := nice_version_append destination active dd
              obtain ⟨k3, t3, lo3, hi3⟩ := nice_version_append (source ++ [pending]) off sd
              have hprefix := canonical_prefix_off before 1 hbefore
              have htail := (canonical_tape_off_no_work after (1 + before.length + 2) hafter).1
              have hs0 : cellFromVersion s0 = ⟨bit, .active, q.val⟩ := by simpa [s0, concrete_version_decodes, ActiveAt] using hsource
              have hs1 : cellFromVersion s1 = pending.val := by simp [s1, concrete_version_decodes, decoded_cell_append]
              have hd0 : cellFromVersion d0 = decodedCell destination := concrete_version_decodes destination dd
              have hd1 : cellFromVersion d1 = active.val := by simp [d1, concrete_version_decodes, decoded_cell_append]
              have heStrict := canonicalPrefix_strict before 1
              have htailStrict : logicalTreeStrict tail = true :=
                layoutTerm_logicalTreeStrict (storageTapeLayout after) (phaseAt (1 + before.length + 2))
                  (phase_at_good (1 + before.length + 2))
              have hsjNs2 : isS2Term sj = false := phaseJunk_not_s2 (phaseAt (1 + before.length))
              have hdjNs2 : isS2Term dj = false := phaseJunk_not_s2 (phaseAt (1 + before.length + 1))
              have hd0Strict : logicalTreeStrict d0 = true :=
                layoutTerm_logicalTreeStrict (versionLayout (destination.map encodedEntry)) _ (phase_at_good dd)
              have hd1Strict : logicalTreeStrict d1 = true :=
                layoutTerm_logicalTreeStrict (versionLayout ((destination ++ [active]).map encodedEntry)) _ (phase_at_good dd)
              have hs1Strict : logicalTreeStrict s1 = true :=
                layoutTerm_logicalTreeStrict (versionLayout ((source ++ [pending]).map encodedEntry)) _ (phase_at_good sd)
              have hp1 : priorityConcretePath (tapeAroundVersion earlier s0 (frameTerm d0 tail dj) sj) = .active srcPath := by
                rw [tape_around_adjacent]
                exact prefixed_adjacent_priority_initial earlier s0 d0 tail sj dj hprefix (by rw [hs0]) (by rw [hd0]; exact hdestination) htail
              have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
              have hplan1 : activePlan srcPath srcPath.isEmpty
                  (program ⟨(cellFromVersion s0).state, hstate⟩ (cellFromVersion s0).bit) = .append srcPath pending.val := by
                have hq : (⟨(cellFromVersion s0).state, hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
                have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
                rw [hq, hbit, hrule]; rfl
              have f1 := active_nice_trace program earlier (frameTerm d0 tail dj) sj s0 (depthBase 1) pending.val
                heStrict (by simp [logicalTreeStrict_frame, hdjNs2, hd0Strict, htailStrict])
                hsjNs2 hfStrict hv hp1 hstate hplan1 _ (scan_init_concrete source sd)
                (by simpa [encodedEntry, pending] using t1)
              have heS1 : StrictPrefixPairs (earlier ++ [(s1, sj)]) := by
                intro x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with hx | rfl
                · exact heStrict x hx
                · exact ⟨hs1Strict, hsjNs2⟩
              have hp2 : priorityConcretePath (tapeAroundVersion (earlier ++ [(s1, sj)]) d0 tail dj) = .pending srcPath := by
                rw [← adjacent_contexts_stitch earlier s1 d0 tail sj dj, tape_around_adjacent]
                exact prefixed_adjacent_priority_pending earlier s1 d0 tail sj dj hprefix (by rw [hs1]; rfl)
              have hsource2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
                  readCellAt (tapeAroundVersion (earlier ++ [(s1, sj)]) v tail dj) srcPath = some pending.val := by
                intro v _; rw [source_before_focused_cell_read, hs1]
              have hdest2 : pendingDestinationPath pending.val srcPath = some (prefixPath (earlier ++ [(s1, sj)])) := by
                rw [prefix_path_append_cell]; rfl
              have htarget2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
                  ∃ targetTerm targetVersion targetTail targetJunk,
                    termAt (tapeAroundVersion (earlier ++ [(s1, sj)]) v tail dj) (prefixPath (earlier ++ [(s1, sj)])) = some targetTerm ∧
                    parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion d0 := by
                intro v heq; exact ⟨frameTerm v tail dj, v, tail, dj, term_at_tape_around_cell _ _ _ _, parse_frame _ _ _, heq⟩
              have hplan2 : pendingPlan srcPath (prefixPath (earlier ++ [(s1, sj)])) pending.val (some (cellFromVersion d0)) =
                  .append (prefixPath (earlier ++ [(s1, sj)])) active.val := by
                simpa [pending, active, pendingRightCell, activeCellRecord, hd0] using
                  pending_right_off_general srcPath (prefixPath (earlier ++ [(s1, sj)])) written nextState.val (decodedCell destination) hdestination
              have f2 := pending_nice_trace program (earlier ++ [(s1, sj)]) tail dj d0 (depthBase 1)
                active.val pending.val (cellFromVersion d0) srcPath (prefixPath (earlier ++ [(s1, sj)]))
                heS1 htailStrict hdjNs2 hfStrict hv hp2 hsource2 hdest2 htarget2 hplan2
                _ (scan_init_concrete destination dd) (by simpa [encodedEntry, active] using t2)
              have hp3 : priorityConcretePath (tapeAroundVersion earlier s1 (frameTerm d1 tail dj) sj) = .pending srcPath := by
                rw [tape_around_adjacent]
                exact prefixed_adjacent_priority_pending earlier s1 d1 tail sj dj hprefix (by rw [hs1]; rfl)
              have hsource3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
                  readCellAt (tapeAroundVersion earlier v (frameTerm d1 tail dj) sj) srcPath = some pending.val := by
                intro v heq; rw [read_cell_at_tape_around, heq, hs1]
              have hdest3 : pendingDestinationPath pending.val srcPath = some dstPath := rfl
              have htarget3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
                  ∃ targetTerm targetVersion targetTail targetJunk,
                    termAt (tapeAroundVersion earlier v (frameTerm d1 tail dj) sj) dstPath = some targetTerm ∧
                    parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = active.val := by
                intro v _; exact ⟨frameTerm d1 tail dj, d1, tail, dj, target_after_focused_cell_term _ _ _ _ _ _, parse_frame _ _ _, hd1⟩
              have hplan3 : pendingPlan srcPath dstPath pending.val (some active.val) = .append srcPath off.val :=
                constructive_pending_right_done_plan srcPath dstPath written (decodedCell destination).bit nextState.val
              have f3 := pending_nice_trace program earlier (frameTerm d1 tail dj) sj s1 (depthBase 1)
                off.val pending.val active.val srcPath dstPath
                heStrict (by simp [logicalTreeStrict_frame, hdjNs2, hd1Strict, htailStrict])
                hsjNs2 hfStrict hv hp3 hsource3 hdest3 htarget3 hplan3
                _ (scan_init_concrete (source ++ [pending]) sd) (by simpa [encodedEntry, off] using t3)
              rw [← adjacent_contexts_stitch earlier s1 d0 tail sj dj, ← adjacent_contexts_stitch earlier s1 d1 tail sj dj] at f2
              have combined := niceSelectorTrace_trans f1 (niceSelectorTrace_trans f2 f3)
              have hstart : tapeAroundVersion earlier s0 (frameTerm d0 tail dj) sj = canonicalTape (before ++ source :: destination :: after) 1 := by
                rw [tape_around_adjacent]; exact (canonical_adjacent_decompose before source destination after 1).symm
              have hend : tapeAroundVersion earlier s2 (frameTerm d1 tail dj) sj =
                  canonicalTape (before ++ (source ++ [pending, off]) :: (destination ++ [active]) :: after) 1 := by
                rw [tape_around_adjacent]; exact (canonical_adjacent_decompose before (source ++ [pending, off]) (destination ++ [active]) after 1).symm
              rw [hstart, hend] at combined
              refine ⟨k1 + (k2 + k3), by omega, by omega, combined⟩
  | rightExtend before source q bit inst hbefore hsource hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | stay => cases hdir
          | left => cases hdir
          | right =>
              let pending := pendingRightCell written nextState
              let active := activeCellRecord false nextState
              let off := offCellRecord written
              let earlier := canonicalPrefix before 1
              let sd := 1 + before.length + 1
              let td := 1 + before.length + 1
              let sj := depthJunk (1 + before.length)
              let s0 := concreteVersion source sd
              let s1 := concreteVersion (source ++ [pending]) sd
              let s2 := concreteVersion (source ++ [pending, off]) sd
              let blank := depthBase (td + 1)
              let d1 := concreteVersion [active] (td + 1)
              let cell0 := frameTerm blank blank (depthJunk td)
              let cell1 := frameTerm d1 blank (depthJunk td)
              let srcPath := prefixPath earlier
              let dstPath := srcPath ++ nextCellPath
              obtain ⟨k1, t1, lo1, hi1⟩ := nice_version_append source pending sd
              obtain ⟨k2, hk2, t2raw⟩ := good_phase_nice_opening_trace (phaseAt td) (phase_at_good td)
              obtain ⟨k3, t3, lo3, hi3⟩ := nice_version_append [] active (td + 1)
              obtain ⟨k4, t4, lo4, hi4⟩ := nice_version_append (source ++ [pending]) off sd
              have hprefix := canonical_prefix_off before 1 hbefore
              have hs0 : cellFromVersion s0 = ⟨bit, .active, q.val⟩ := by simpa [s0, concrete_version_decodes, ActiveAt] using hsource
              have hs1 : cellFromVersion s1 = pending.val := by simp [s1, concrete_version_decodes, decoded_cell_append]
              have hblank : cellFromVersion blank = defaultCell := depth_child_is_blank (td + 1)
              have hd1 : cellFromVersion d1 = active.val := by
                rw [concrete_version_decodes [active] (td + 1)]
                simpa using decoded_cell_append [] active
              have heStrict := canonicalPrefix_strict before 1
              have hsjNs2 : isS2Term sj = false := phaseJunk_not_s2 (phaseAt (1 + before.length))
              have htdNs2 : isS2Term (depthJunk td) = false := phaseJunk_not_s2 (phaseAt td)
              have hblankStrict : logicalTreeStrict blank = true :=
                logicalTreeStrict_closed (depth_base_closed (td + 1))
              have hs1Strict : logicalTreeStrict s1 = true :=
                layoutTerm_logicalTreeStrict (versionLayout ((source ++ [pending]).map encodedEntry)) _ (phase_at_good sd)
              have hd1Strict : logicalTreeStrict d1 = true :=
                layoutTerm_logicalTreeStrict (versionLayout ([active].map encodedEntry)) _ (phase_at_good (td + 1))
              have hp1 : priorityConcretePath (tapeAroundVersion earlier s0 (depthBase td) sj) = .active srcPath := by
                rw [tape_around_single]
                exact prefixed_single_active_priority earlier s0 (depthBase td) sj hprefix (by rw [hs0])
                  (depth_child_has_no_pending td)
              have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
              have hplan1 : activePlan srcPath srcPath.isEmpty
                  (program ⟨(cellFromVersion s0).state, hstate⟩ (cellFromVersion s0).bit) = .append srcPath pending.val := by
                have hq : (⟨(cellFromVersion s0).state, hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
                have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
                rw [hq, hbit, hrule]; rfl
              have f1 := active_nice_trace program earlier (depthBase td) sj s0 (depthBase 1) pending.val
                heStrict (logicalTreeStrict_closed (depth_base_closed td)) hsjNs2 hfStrict hv hp1 hstate hplan1
                _ (scan_init_concrete source sd) (by simpa [encodedEntry, pending] using t1)
              have t2 : NiceOpeningTrace k2 (depthBase td) cell0 := by
                simpa [depthBase, cell0, blank, opened_empty_cell_shape] using t2raw
              have f2 := pending_tail_nice_trace program earlier s1 sj (depthBase 1) written nextState.val
                heStrict hs1Strict hsjNs2 hfStrict hv hprefix (by simpa [pending, pendingRightCell] using hs1) t2
              have heS1 : StrictPrefixPairs (earlier ++ [(s1, sj)]) := by
                intro x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with hx | rfl
                · exact heStrict x hx
                · exact ⟨hs1Strict, hsjNs2⟩
              have hmoving : isMoving (cellFromVersion s1).status = true := by rw [hs1]; rfl
              have hp3 : priorityConcretePath (tapeAroundVersion (earlier ++ [(s1, sj)]) blank blank (depthJunk td)) = .pending srcPath := by
                rw [← adjacent_contexts_stitch earlier s1 blank blank sj (depthJunk td), tape_around_adjacent]
                exact prefixed_single_pending_priority earlier s1 cell0 sj hprefix hmoving
              have hsource3 : ∀ v, cellFromVersion v = cellFromVersion blank →
                  readCellAt (tapeAroundVersion (earlier ++ [(s1, sj)]) v blank (depthJunk td)) srcPath = some pending.val := by
                intro v _; rw [source_before_focused_cell_read, hs1]
              have hdest3 : pendingDestinationPath pending.val srcPath = some (prefixPath (earlier ++ [(s1, sj)])) := by
                rw [prefix_path_append_cell]; rfl
              have htarget3 : ∀ v, cellFromVersion v = cellFromVersion blank →
                  ∃ targetTerm targetVersion targetTail targetJunk,
                    termAt (tapeAroundVersion (earlier ++ [(s1, sj)]) v blank (depthJunk td))
                      (prefixPath (earlier ++ [(s1, sj)])) = some targetTerm ∧
                    parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion blank := by
                intro v heq; exact ⟨frameTerm v blank (depthJunk td), v, blank, depthJunk td, term_at_tape_around_cell _ _ _ _, parse_frame _ _ _, heq⟩
              have hplan3 : pendingPlan srcPath (prefixPath (earlier ++ [(s1, sj)])) pending.val (some (cellFromVersion blank)) =
                  .append (prefixPath (earlier ++ [(s1, sj)])) active.val := by
                rw [hblank]; exact pending_right_off_plan srcPath (prefixPath (earlier ++ [(s1, sj)])) written false nextState.val
              have f3 := pending_nice_trace program (earlier ++ [(s1, sj)]) blank (depthJunk td) blank (depthBase 1)
                active.val pending.val (cellFromVersion blank) srcPath (prefixPath (earlier ++ [(s1, sj)]))
                heS1 hblankStrict htdNs2 hfStrict hv hp3 hsource3 hdest3 htarget3 hplan3
                _ (scan_init_concrete [] (td + 1)) (by simpa [encodedEntry, active, concreteVersion, depthBase, phaseBase, versionLayout, layoutTerm] using t3)
              have hp4 : priorityConcretePath (tapeAroundVersion earlier s1 cell1 sj) = .pending srcPath := by
                rw [tape_around_single]
                exact prefixed_single_pending_priority earlier s1 cell1 sj hprefix hmoving
              have hsource4 : ∀ v, cellFromVersion v = cellFromVersion s1 →
                  readCellAt (tapeAroundVersion earlier v cell1 sj) srcPath = some pending.val := by
                intro v heq; rw [read_cell_at_tape_around, heq, hs1]
              have hdest4 : pendingDestinationPath pending.val srcPath = some dstPath := rfl
              have htarget4 : ∀ v, cellFromVersion v = cellFromVersion s1 →
                  ∃ targetTerm targetVersion targetTail targetJunk,
                    termAt (tapeAroundVersion earlier v cell1 sj) dstPath = some targetTerm ∧
                    parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = active.val := by
                intro v _; exact ⟨cell1, d1, blank, depthJunk td, target_after_focused_cell_term _ _ _ _ _ _, parse_frame _ _ _, hd1⟩
              have hplan4 : pendingPlan srcPath dstPath pending.val (some active.val) = .append srcPath off.val :=
                constructive_pending_right_done_plan srcPath dstPath written false nextState.val
              have f4 := pending_nice_trace program earlier cell1 sj s1 (depthBase 1)
                off.val pending.val active.val srcPath dstPath
                heStrict (by dsimp only [cell1]; simp [logicalTreeStrict_frame, htdNs2, hd1Strict, hblankStrict])
                hsjNs2 hfStrict hv hp4 hsource4 hdest4 htarget4 hplan4
                _ (scan_init_concrete (source ++ [pending]) sd) (by simpa [encodedEntry, off] using t4)
              rw [← tape_around_single earlier s1 (depthBase td) sj, ← tape_around_single earlier s1 cell0 sj] at f2
              rw [show cell0 = frameTerm blank blank (depthJunk td) from rfl,
                  adjacent_contexts_stitch earlier s1 blank blank sj (depthJunk td)] at f2
              rw [show cell1 = frameTerm d1 blank (depthJunk td) from rfl,
                  adjacent_contexts_stitch earlier s1 d1 blank sj (depthJunk td)] at f4
              have combined := niceSelectorTrace_trans f1 (niceSelectorTrace_trans f2 (niceSelectorTrace_trans f3 f4))
              have hstart : tapeAroundVersion earlier s0 (depthBase td) sj = canonicalTape (before ++ [source]) 1 := by
                simpa [td, canonical_tape_nil] using (canonical_single_decompose before source [] 1).symm
              have hend : tapeAroundVersion earlier s2 (frameTerm d1 blank (depthJunk td)) sj =
                  canonicalTape (before ++ [source ++ [pending, off], [active]]) 1 := by
                rw [tape_around_adjacent]
                simpa [td, blank, d1, canonical_tape_nil] using
                  (canonical_adjacent_decompose before (source ++ [pending, off]) [active] [] 1).symm
              rw [hstart, hend] at combined
              refine ⟨k1 + (k2 + (k3 + k4)), ?_, ?_, combined⟩
              · cases hk2 <;> omega
              · cases hk2 <;> omega
  | leftExisting before destination source after q bit inst hbefore hdestination hsource hafter hrule hdir =>
      cases inst with
      | mk written nextState direction =>
          cases direction with
          | stay => cases hdir
          | right => cases hdir
          | left =>
              let pending := pendingLeftCell written nextState
              let active := activeCellRecord (decodedCell destination).bit nextState
              let off := offCellRecord written
              let earlier := canonicalPrefix before 1
              let dd := 1 + before.length + 1
              let sd := 1 + before.length + 2
              let dj := depthJunk (1 + before.length)
              let sj := depthJunk (1 + before.length + 1)
              let tail := canonicalTape after (1 + before.length + 2)
              let s0 := concreteVersion source sd
              let s1 := concreteVersion (source ++ [pending]) sd
              let s2 := concreteVersion (source ++ [pending, off]) sd
              let d0 := concreteVersion destination dd
              let d1 := concreteVersion (destination ++ [active]) dd
              let dstPath := prefixPath earlier
              let srcPath := dstPath ++ nextCellPath
              obtain ⟨k1, t1, lo1, hi1⟩ := nice_version_append source pending sd
              obtain ⟨k2, t2, lo2, hi2⟩ := nice_version_append destination active dd
              obtain ⟨k3, t3, lo3, hi3⟩ := nice_version_append (source ++ [pending]) off sd
              have hprefix := canonical_prefix_off before 1 hbefore
              have htail := (canonical_tape_off_no_work after (1 + before.length + 2) hafter).1
              have hs0 : cellFromVersion s0 = ⟨bit, .active, q.val⟩ := by simpa [s0, concrete_version_decodes, ActiveAt] using hsource
              have hs1 : cellFromVersion s1 = pending.val := by simp [s1, concrete_version_decodes, decoded_cell_append]
              have hd0 : cellFromVersion d0 = decodedCell destination := concrete_version_decodes destination dd
              have hd1 : cellFromVersion d1 = active.val := by simp [d1, concrete_version_decodes, decoded_cell_append]
              have heStrict := canonicalPrefix_strict before 1
              have htailStrict : logicalTreeStrict tail = true :=
                layoutTerm_logicalTreeStrict (storageTapeLayout after) (phaseAt (1 + before.length + 2))
                  (phase_at_good (1 + before.length + 2))
              have hdjNs2 : isS2Term dj = false := phaseJunk_not_s2 (phaseAt (1 + before.length))
              have hsjNs2 : isS2Term sj = false := phaseJunk_not_s2 (phaseAt (1 + before.length + 1))
              have hd0Strict : logicalTreeStrict d0 = true :=
                layoutTerm_logicalTreeStrict (versionLayout (destination.map encodedEntry)) _ (phase_at_good dd)
              have hd1Strict : logicalTreeStrict d1 = true :=
                layoutTerm_logicalTreeStrict (versionLayout ((destination ++ [active]).map encodedEntry)) _ (phase_at_good dd)
              have hs1Strict : logicalTreeStrict s1 = true :=
                layoutTerm_logicalTreeStrict (versionLayout ((source ++ [pending]).map encodedEntry)) _ (phase_at_good sd)
              have heD0 : StrictPrefixPairs (earlier ++ [(d0, dj)]) := by
                intro x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with hx | rfl
                · exact heStrict x hx
                · exact ⟨hd0Strict, hdjNs2⟩
              have heD1 : StrictPrefixPairs (earlier ++ [(d1, dj)]) := by
                intro x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with hx | rfl
                · exact heStrict x hx
                · exact ⟨hd1Strict, hdjNs2⟩
              have hsrc1 : prefixPath (earlier ++ [(d0, dj)]) = srcPath := by
                simpa [srcPath, dstPath] using prefix_path_append_cell earlier d0 dj
              have hp1 : priorityConcretePath (tapeAroundVersion (earlier ++ [(d0, dj)]) s0 tail sj) =
                  .active (prefixPath (earlier ++ [(d0, dj)])) := by
                rw [← adjacent_contexts_stitch earlier d0 s0 tail dj sj, tape_around_adjacent, hsrc1]
                exact prefixed_left_priority_initial earlier d0 s0 tail dj sj hprefix (by rw [hd0]; exact hdestination) (by rw [hs0]) htail
              have hstate : (cellFromVersion s0).state < 132 := by rw [hs0]; exact q.isLt
              have hplan1 : activePlan (prefixPath (earlier ++ [(d0, dj)])) (prefixPath (earlier ++ [(d0, dj)])).isEmpty
                  (program ⟨(cellFromVersion s0).state, hstate⟩ (cellFromVersion s0).bit) =
                    .append (prefixPath (earlier ++ [(d0, dj)])) pending.val := by
                have hq : (⟨(cellFromVersion s0).state, hstate⟩ : Fin 132) = q := by apply Fin.ext; simp [hs0]
                have hbit : (cellFromVersion s0).bit = bit := by rw [hs0]
                have hempty : (prefixPath (earlier ++ [(d0, dj)])).isEmpty = false := by
                  rw [hsrc1]; simp [srcPath, nextCellPath]
                rw [hq, hbit, hrule, hempty]; rfl
              have f1 := active_nice_trace program (earlier ++ [(d0, dj)]) tail sj s0 (depthBase 1) pending.val
                heD0 htailStrict hsjNs2 hfStrict hv hp1 hstate hplan1
                _ (scan_init_concrete source sd) (by simpa [encodedEntry, pending] using t1)
              have hp2 : priorityConcretePath (tapeAroundVersion earlier d0 (frameTerm s1 tail sj) dj) = .pending srcPath := by
                rw [tape_around_adjacent]
                exact prefixed_left_priority_pending earlier d0 s1 tail dj sj hprefix
                  (by simp [hd0, hdestination, isMoving]) (by rw [hs1]; rfl)
              have hsource2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
                  readCellAt (tapeAroundVersion earlier v (frameTerm s1 tail sj) dj) srcPath = some pending.val := by
                intro v _; rw [show srcPath = prefixPath earlier ++ nextCellPath from rfl, source_after_focused_cell_read, hs1]
              have hdest2 : pendingDestinationPath pending.val srcPath = some (prefixPath earlier) := by
                simpa [srcPath, dstPath, pending, pendingLeftCell] using pending_left_destination (prefixPath earlier) written nextState.val
              have htarget2 : ∀ v, cellFromVersion v = cellFromVersion d0 →
                  ∃ targetTerm targetVersion targetTail targetJunk,
                    termAt (tapeAroundVersion earlier v (frameTerm s1 tail sj) dj) (prefixPath earlier) = some targetTerm ∧
                    parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = cellFromVersion d0 := by
                intro v heq; exact ⟨frameTerm v (frameTerm s1 tail sj) dj, v, frameTerm s1 tail sj, dj,
                  term_at_tape_around_cell _ _ _ _, parse_frame _ _ _, heq⟩
              have hplan2 : pendingPlan srcPath (prefixPath earlier) pending.val (some (cellFromVersion d0)) =
                  .append (prefixPath earlier) active.val := by
                simpa [pending, active, pendingLeftCell, activeCellRecord, hd0] using
                  pending_left_off_general srcPath (prefixPath earlier) written nextState.val (decodedCell destination) hdestination
              have f2 := pending_nice_trace program earlier (frameTerm s1 tail sj) dj d0 (depthBase 1)
                active.val pending.val (cellFromVersion d0) srcPath (prefixPath earlier)
                heStrict (by simp [logicalTreeStrict_frame, hsjNs2, hs1Strict, htailStrict])
                hdjNs2 hfStrict hv hp2 hsource2 hdest2 htarget2 hplan2
                _ (scan_init_concrete destination dd) (by simpa [encodedEntry, active] using t2)
              have hsrc3 : prefixPath (earlier ++ [(d1, dj)]) = srcPath := by
                simpa [srcPath, dstPath] using prefix_path_append_cell earlier d1 dj
              have hp3 : priorityConcretePath (tapeAroundVersion (earlier ++ [(d1, dj)]) s1 tail sj) = .pending srcPath := by
                rw [← adjacent_contexts_stitch earlier d1 s1 tail dj sj, tape_around_adjacent]
                exact prefixed_left_priority_pending earlier d1 s1 tail dj sj hprefix
                  (by rw [hd1]; rfl) (by rw [hs1]; rfl)
              have hsource3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
                  readCellAt (tapeAroundVersion (earlier ++ [(d1, dj)]) v tail sj) srcPath = some pending.val := by
                intro v heq; rw [← hsrc3, read_cell_at_tape_around, heq, hs1]
              have hdest3 : pendingDestinationPath pending.val srcPath = some dstPath := by
                simpa [srcPath, dstPath, pending, pendingLeftCell] using pending_left_destination (prefixPath earlier) written nextState.val
              have htarget3 : ∀ v, cellFromVersion v = cellFromVersion s1 →
                  ∃ targetTerm targetVersion targetTail targetJunk,
                    termAt (tapeAroundVersion (earlier ++ [(d1, dj)]) v tail sj) dstPath = some targetTerm ∧
                    parseFrame targetTerm = some (targetVersion, targetTail, targetJunk) ∧ cellFromVersion targetVersion = active.val := by
                intro v _
                refine ⟨frameTerm d1 (frameTerm v tail sj) dj, d1, frameTerm v tail sj, dj, ?_, parse_frame _ _ _, hd1⟩
                rw [prepend_tape_around]
                simpa [tapeAroundVersion, dstPath] using term_at_prepend_tape earlier (frameTerm d1 (frameTerm v tail sj) dj)
              have hplan3 : pendingPlan srcPath dstPath pending.val (some active.val) =
                  .append (prefixPath (earlier ++ [(d1, dj)])) off.val := by
                rw [hsrc3]
                exact constructive_pending_left_done_plan srcPath dstPath written (decodedCell destination).bit nextState.val
              have f3 := pending_nice_trace program (earlier ++ [(d1, dj)]) tail sj s1 (depthBase 1)
                off.val pending.val active.val srcPath dstPath
                heD1 htailStrict hsjNs2 hfStrict hv hp3 hsource3 hdest3 htarget3 hplan3
                _ (scan_init_concrete (source ++ [pending]) sd) (by simpa [encodedEntry, off] using t3)
              rw [← adjacent_contexts_stitch earlier d0 s0 tail dj sj, ← adjacent_contexts_stitch earlier d0 s1 tail dj sj] at f1
              rw [← adjacent_contexts_stitch earlier d1 s1 tail dj sj, ← adjacent_contexts_stitch earlier d1 s2 tail dj sj] at f3
              have combined := niceSelectorTrace_trans f1 (niceSelectorTrace_trans f2 f3)
              have hstart : tapeAroundVersion earlier d0 (frameTerm s0 tail sj) dj = canonicalTape (before ++ destination :: source :: after) 1 := by
                rw [tape_around_adjacent]; exact (canonical_adjacent_decompose before destination source after 1).symm
              have hend : tapeAroundVersion earlier d1 (frameTerm s2 tail sj) dj =
                  canonicalTape (before ++ (destination ++ [active]) :: (source ++ [pending, off]) :: after) 1 := by
                rw [tape_around_adjacent]; exact (canonical_adjacent_decompose before (destination ++ [active]) (source ++ [pending, off]) after 1).symm
              rw [hstart, hend] at combined
              refine ⟨k1 + (k2 + k3), by omega, by omega, combined⟩

theorem source_run_nice_selector (program : BinaryProgram) {n : Nat}
    {start finish : List (List UniversalCell)} (run : SourceRun program n start finish) :
    ∃ k, 6 * n ≤ k ∧ k ≤ 511 * n ∧
      NiceSelectorTrace program k
        (canonicalRoot start 1 (depthBase 1) (depthJunk 0))
        (canonicalRoot finish 1 (depthBase 1) (depthJunk 0)) := by
  induction run with
  | zero _ => exact ⟨0, by simp, by simp, NiceSelectorTrace.zero _⟩
  | next hstep _ ih =>
      obtain ⟨k1, lo1, hi1, first⟩ := source_transition_nice_selector program hstep
      obtain ⟨k2, lo2, hi2, rest⟩ := ih
      refine ⟨k1 + k2, by omega, by omega, niceSelectorTrace_trans first rest⟩

theorem seed_halt_nice_trace (program : BinaryProgram)
    (tape : Term) (htapeStrict : logicalTreeStrict tape = true)
    (sourcePath : List Bool) (q : Fin 132) (bit : Bool)
    (hpriority : priorityConcretePath tape = .active sourcePath)
    (hread : readCellAt tape sourcePath = some ⟨bit, .active, q.val⟩)
    (hstop : program q bit = none) :
    let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt 1).1 (phaseAt 1).2
    ∃ k, (k = 6 ∨ k = 7) ∧
      NiceSelectorTrace program k
        (seedHubRoot (depthBase 1) tape (depthJunk 0))
        (seedHubRoot flagOpen tape (depthJunk 0)) := by
  obtain ⟨k, hk, htrace⟩ := good_phase_nice_opening_trace (phaseAt 1) (phase_at_good 1)
  have hlift : ∀ {m : Nat} {a b : Term},
      parseFrame a = none →
      NiceOpeningTrace m a b →
      NiceSelectorTrace program m (seedHubRoot a tape (depthJunk 0)) (seedHubRoot b tape (depthJunk 0)) := by
    intro m a b hclosed tr
    induction tr with
    | @finish a b hchosen haStrict _ hleAB _ =>
        obtain ⟨rel, hlocal, hdir⟩ := hchosen
        have hctx := directed_protected_context [.left tape (depthJunk 0)] hdir
        have hroot := DirectedStep.right (a := numeral 1 ⋅ S) hctx
        have hseedStep : SeedHaltStep tape (depthJunk 0) (.active sourcePath) a b :=
          ⟨halt_field_closed_observation a tape (depthJunk 0) hclosed, hpriority, rel, hlocal,
            by simpa [seedHubRoot, wrapProtected, contextPath, framePath, List.append_assoc] using hroot⟩
        obtain ⟨path, hsel, hd⟩ :=
          halt_seed_step_is_full_selector program tape (depthJunk 0) sourcePath q bit hpriority hread hstop hseedStep
        have hhubStrict := hub_logicalTreeStrict a tape 0 haStrict htapeStrict
        have hrootLe : leaves (seedHubRoot a tape (depthJunk 0)) ≤ leaves (seedHubRoot b tape (depthJunk 0)) := by
          simp [seedHubRoot, frame_leaves, leaves]; omega
        exact NiceSelectorTrace.next ⟨a, tape, rfl, hhubStrict⟩ hrootLe hsel hd (NiceSelectorTrace.zero _)
    | @more n a b c hchosen haStrict hbClosed hleAB _ ih =>
        obtain ⟨rel, hlocal, hdir⟩ := hchosen
        have hctx := directed_protected_context [.left tape (depthJunk 0)] hdir
        have hroot := DirectedStep.right (a := numeral 1 ⋅ S) hctx
        have hseedStep : SeedHaltStep tape (depthJunk 0) (.active sourcePath) a b :=
          ⟨halt_field_closed_observation a tape (depthJunk 0) hclosed, hpriority, rel, hlocal,
            by simpa [seedHubRoot, wrapProtected, contextPath, framePath, List.append_assoc] using hroot⟩
        obtain ⟨path, hsel, hd⟩ :=
          halt_seed_step_is_full_selector program tape (depthJunk 0) sourcePath q bit hpriority hread hstop hseedStep
        have hhubStrict := hub_logicalTreeStrict a tape 0 haStrict htapeStrict
        have hrootLe : leaves (seedHubRoot a tape (depthJunk 0)) ≤ leaves (seedHubRoot b tape (depthJunk 0)) := by
          simp [seedHubRoot, frame_leaves, leaves]; omega
        exact NiceSelectorTrace.next ⟨a, tape, rfl, hhubStrict⟩ hrootLe hsel hd (ih hbClosed)
  exact ⟨k, hk, hlift (depth_base_closed 1) htrace⟩

/-- Post-halt left-frontier layout inside `flag`: `.opened (leftSpine m) .unopened`. -/
def postHaltFlagLayout (m : Nat) : Layout :=
  .opened (leftSpine m) .unopened

theorem closedLeftFrontier_of_matched :
    ∀ (s : Layout) (t : Term), layoutMatches s t →
      closedLeftFrontier t = physicalPath (leftFrontier s) := by
  intro s
  induction s with
  | unopened =>
      intro t h
      have hp : parseFrame t = none := h
      unfold parseFrame at hp
      unfold closedLeftFrontier
      split <;> simp_all [leftFrontier, physicalPath]
  | opened l r ihl _ =>
      intro t h
      obtain ⟨tl, tr, j, hp, hl, _⟩ := h
      have ht := parse_frame_sound t tl tr j hp
      subst t
      simpa [closedLeftFrontier, frameTerm, S, leftFrontier, physicalPath] using ihl tl hl

theorem postHaltFlag_open (m : Nat) :
    openLayoutAt (postHaltFlagLayout m) (false :: List.replicate m false) = some (postHaltFlagLayout (m + 1)) := by
  simp [postHaltFlagLayout, openLayoutAt, left_spine_grows]

theorem postHaltFlag_frontier (m : Nat) :
    leftFrontier (postHaltFlagLayout m) = false :: List.replicate m false := by
  simp [postHaltFlagLayout, leftFrontier, left_frontier_of_spine]

theorem post_halt_step_nice (program : BinaryProgram) (tape : Term)
    (htapeStrict : logicalTreeStrict tape = true) (m : Nat) :
    ∃ k, (k = 6 ∨ k = 7) ∧
      NiceSelectorTrace program k
        (seedHubRoot (layoutTerm (postHaltFlagLayout m) (phaseAt 1).1 (phaseAt 1).2) tape (depthJunk 0))
        (seedHubRoot (layoutTerm (postHaltFlagLayout (m + 1)) (phaseAt 1).1 (phaseAt 1).2) tape (depthJunk 0)) := by
  let shape := postHaltFlagLayout m
  let target := postHaltFlagLayout (m + 1)
  let slot := false :: List.replicate m false
  let p := phaseAt 1
  let q := advancePhase slot.length p
  have hp : goodPhase p := phase_at_good 1
  have hq : goodPhase q := advance_phase_good slot.length p hp
  have hopen : openLayoutAt shape slot = some target := postHaltFlag_open m
  have hslot : subLayout shape slot = some .unopened := open_layout_targets_unopened slot shape target hopen
  have hat : termAt (layoutTerm shape p.1 p.2) (physicalPath slot) = some (phaseBase q) :=
    (selected_slot_is_generator shape target slot p hp hopen).2
  have hrepSelf := replaceTermAt_self (physicalPath slot) (layoutTerm shape p.1 p.2) (phaseBase q) hat
  have hmatch : layoutMatches shape (layoutTerm shape p.1 p.2) := finite_layout_decodes shape p.1 p.2 hp.1 hp.2
  obtain ⟨k, hk, htrace⟩ := good_phase_nice_opening_trace q hq
  have hlift : ∀ {n : Nat} {old final : Term},
      NiceOpeningTrace n old final →
      ∀ flagSub,
        layoutMatches shape flagSub →
        termAt flagSub (physicalPath slot) = some old →
        replaceTermAt (layoutTerm shape p.1 p.2) (physicalPath slot) old = some flagSub →
        ∃ flagOut,
          replaceTermAt flagSub (physicalPath slot) final = some flagOut ∧
          NiceSelectorTrace program n
            (seedHubRoot flagSub tape (depthJunk 0))
            (seedHubRoot flagOut tape (depthJunk 0)) := by
    intro n old final tr
    induction tr with
    | @finish a b hchosen haStrict _ hleAB _ =>
        intro flagSub hmSub hatSub hrepBase
        obtain ⟨rel, hlocal, hdir⟩ := hchosen
        obtain ⟨flagOut, hrepSub, hstepSub⟩ :=
          directed_step_replaces_subterm (physicalPath slot) flagSub a rel b hatSub hdir
        have hflagVal : flagValue flagSub = true := by
          simpa [shape, postHaltFlagLayout, layoutIsOpen] using matched_layout_flag shape flagSub hmSub
        have hfront : closedLeftFrontier flagSub = physicalPath slot := by
          rw [closedLeftFrontier_of_matched shape flagSub hmSub, postHaltFlag_frontier]
        have hfocusRoot : termAt (seedHubRoot flagSub tape (depthJunk 0)) (hubFlagPath ++ physicalPath slot) = some a := by
          rw [term_at_append, term_at_seed_flag]
          exact hatSub
        have hsel : fullRootSelector program (seedHubRoot flagSub tape (depthJunk 0)) =
            some (hubFlagPath ++ physicalPath slot ++ rel) := by
          rw [full_selector_halt_branch program flagSub tape (depthJunk 0) hflagVal]
          simp [hfront, selectOpeningAt, hfocusRoot, hlocal, List.append_assoc]
        have hdirRoot : DirectedStep (hubFlagPath ++ physicalPath slot ++ rel)
            (seedHubRoot flagSub tape (depthJunk 0)) (seedHubRoot flagOut tape (depthJunk 0)) := by
          have h1 := directed_frame_left hstepSub tape (depthJunk 0)
          have h2 := DirectedStep.right (a := numeral 1 ⋅ S) h1
          simpa [seedHubRoot, hubFlagPath, List.append_assoc] using h2
        have hflagStrict := replace_physicalPath_logicalTreeStrict slot shape p a flagSub hp hslot hrepBase haStrict
        have hhubStrict := hub_logicalTreeStrict flagSub tape 0 hflagStrict htapeStrict
        have hflagLe := replaceTermAt_leaves_mono (physicalPath slot) flagSub flagOut b a hrepSub hatSub hleAB
        have hrootLe : leaves (seedHubRoot flagSub tape (depthJunk 0)) ≤ leaves (seedHubRoot flagOut tape (depthJunk 0)) := by
          simp [seedHubRoot, frame_leaves, leaves]; omega
        exact ⟨flagOut, hrepSub,
          NiceSelectorTrace.next ⟨flagSub, tape, rfl, hhubStrict⟩ hrootLe hsel hdirRoot (NiceSelectorTrace.zero _)⟩
    | @more n a b c hchosen haStrict hbClosed hleAB _ ih =>
        intro flagSub hmSub hatSub hrepBase
        obtain ⟨rel, hlocal, hdir⟩ := hchosen
        obtain ⟨flagMid, hstepMid, hmMid, hatMid⟩ :=
          closed_slot_step_preserves_layout slot shape flagSub a b rel hmSub hslot hatSub hdir hbClosed
        obtain ⟨flagMid', hrepFirst, hstepMid'⟩ :=
          directed_step_replaces_subterm (physicalPath slot) flagSub a rel b hatSub hdir
        have heq : flagMid = flagMid' := directed_step_unique hstepMid flagMid' hstepMid'
        subst flagMid'
        have hrepMidBase : replaceTermAt (layoutTerm shape p.1 p.2) (physicalPath slot) b = some flagMid := by
          rw [← replace_same_path_overwrites (physicalPath slot) _ a flagSub b hrepBase]
          exact hrepFirst
        obtain ⟨flagOut, hrepRest, htraceRest⟩ := ih flagMid hmMid hatMid hrepMidBase
        have hrepTotal : replaceTermAt flagSub (physicalPath slot) c = some flagOut := by
          rw [← replace_same_path_overwrites (physicalPath slot) flagSub b flagMid c hrepFirst]
          exact hrepRest
        have hflagVal : flagValue flagSub = true := by
          simpa [shape, postHaltFlagLayout, layoutIsOpen] using matched_layout_flag shape flagSub hmSub
        have hfront : closedLeftFrontier flagSub = physicalPath slot := by
          rw [closedLeftFrontier_of_matched shape flagSub hmSub, postHaltFlag_frontier]
        have hfocusRoot : termAt (seedHubRoot flagSub tape (depthJunk 0)) (hubFlagPath ++ physicalPath slot) = some a := by
          rw [term_at_append, term_at_seed_flag]
          exact hatSub
        have hsel : fullRootSelector program (seedHubRoot flagSub tape (depthJunk 0)) =
            some (hubFlagPath ++ physicalPath slot ++ rel) := by
          rw [full_selector_halt_branch program flagSub tape (depthJunk 0) hflagVal]
          simp [hfront, selectOpeningAt, hfocusRoot, hlocal, List.append_assoc]
        have hdirRoot : DirectedStep (hubFlagPath ++ physicalPath slot ++ rel)
            (seedHubRoot flagSub tape (depthJunk 0)) (seedHubRoot flagMid tape (depthJunk 0)) := by
          have h1 := directed_frame_left hstepMid tape (depthJunk 0)
          have h2 := DirectedStep.right (a := numeral 1 ⋅ S) h1
          simpa [seedHubRoot, hubFlagPath, List.append_assoc] using h2
        have hflagStrict := replace_physicalPath_logicalTreeStrict slot shape p a flagSub hp hslot hrepBase haStrict
        have hhubStrict := hub_logicalTreeStrict flagSub tape 0 hflagStrict htapeStrict
        have hflagLe := replaceTermAt_leaves_mono (physicalPath slot) flagSub flagMid b a hrepFirst hatSub hleAB
        have hrootLe : leaves (seedHubRoot flagSub tape (depthJunk 0)) ≤ leaves (seedHubRoot flagMid tape (depthJunk 0)) := by
          simp [seedHubRoot, frame_leaves, leaves]; omega
        exact ⟨flagOut, hrepTotal,
          NiceSelectorTrace.next ⟨flagSub, tape, rfl, hhubStrict⟩ hrootLe hsel hdirRoot htraceRest⟩
  obtain ⟨flagOut, hrepOut, hnice⟩ := hlift htrace (layoutTerm shape p.1 p.2) hmatch hat hrepSelf
  have hcanonical := canonical_layout_replace slot shape target p hp hopen
  have houtEq : flagOut = layoutTerm target p.1 p.2 := by
    rw [hcanonical] at hrepOut
    exact (Option.some.inj hrepOut).symm
  subst flagOut
  exact ⟨k, hk, hnice⟩

theorem post_halt_run_nice (program : BinaryProgram) (tape : Term)
    (htapeStrict : logicalTreeStrict tape = true) (count : Nat) :
    ∃ k, 6 * count ≤ k ∧ k ≤ 7 * count ∧
      NiceSelectorTrace program k
        (seedHubRoot (layoutTerm (postHaltFlagLayout 0) (phaseAt 1).1 (phaseAt 1).2) tape (depthJunk 0))
        (seedHubRoot (layoutTerm (postHaltFlagLayout count) (phaseAt 1).1 (phaseAt 1).2) tape (depthJunk 0)) := by
  induction count with
  | zero => exact ⟨0, by simp, by simp, NiceSelectorTrace.zero _⟩
  | succ count ih =>
      obtain ⟨k1, lo1, hi1, first⟩ := ih
      obtain ⟨k2, hk2, second⟩ := post_halt_step_nice program tape htapeStrict count
      refine ⟨k1 + k2, ?_, ?_, niceSelectorTrace_trans first second⟩
      · cases hk2 <;> omega
      · cases hk2 <;> omega


/-! ## Part 3: Polynomial Initial Size Bound & Polynomial Trajectory Size Bound -/

def tapeLen (u : UConfig) : Nat :=
  u.leftRev.length + 1 + u.right.length

def openedCount : Layout → Nat
  | .unopened => 0
  | .opened l r => 1 + openedCount l + openedCount r

def layoutHeight : Layout → Nat
  | .unopened => 0
  | .opened l r => 1 + max (layoutHeight l) (layoutHeight r)

theorem layoutHeight_le_openedCount (s : Layout) : layoutHeight s ≤ openedCount s := by
  induction s with
  | unopened => exact Nat.le_refl 0
  | opened l r ihl ihr =>
      simp only [layoutHeight, openedCount]
      omega

theorem nextPhase_bound (p : Nat × Nat) (hp : goodPhase p) :
    (nextPhase p).1 ≤ p.2 + 1 ∧ (nextPhase p).2 ≤ p.2 + 1 := by
  rcases p with ⟨m, n⟩
  cases m <;> simp [goodPhase, nextPhase] at * <;> omega

theorem phaseAt_bound (d : Nat) :
    (phaseAt d).1 ≤ d + 2 ∧ (phaseAt d).2 ≤ d + 2 := by
  induction d with
  | zero => unfold phaseAt; decide
  | succ d ih =>
      have hnext := nextPhase_bound (phaseAt d) (phase_at_good d)
      unfold phaseAt
      omega

theorem phaseJunk_leaves_bound (p : Nat × Nat) (hp : goodPhase p) :
    leaves (phaseJunk p) ≤ 17 + 6 * p.2 := by
  rcases p with ⟨m, n⟩
  have hn : 2 ≤ n := hp.1
  have hm : m ≤ n := hp.2
  cases m <;> simp [phaseJunk, generator_junk_leaves] <;> omega

/-- Master unfolded occurrence-tree size bound for any `layoutTerm`:
    `leaves (layoutTerm s p.1 p.2) ≤ (2 * openedCount s + 1) * (19 + 6 * H)`
    whenever `p.2 + layoutHeight s ≤ H`. -/
theorem layoutTerm_leaves_bound (s : Layout) :
    ∀ (p : Nat × Nat) (H : Nat), goodPhase p → p.2 + layoutHeight s ≤ H →
      leaves (layoutTerm s p.1 p.2) ≤ (2 * openedCount s + 1) * (19 + 6 * H) := by
  induction s with
  | unopened =>
      intro p H hp hH
      have hm : p.1 ≤ p.2 := hp.2
      simp only [layoutHeight, Nat.add_zero] at hH
      simp only [layoutTerm, openedCount, generator_leaves]
      omega
  | opened l r ihl ihr =>
      intro p H hp hH
      rw [layout_opened_phase l r p hp, frame_leaves]
      have hnext := next_phase_good p hp
      have hnb := nextPhase_bound p hp
      have hHl : (nextPhase p).2 + layoutHeight l ≤ H := by
        simp only [layoutHeight] at hH
        omega
      have hHr : (nextPhase p).2 + layoutHeight r ≤ H := by
        simp only [layoutHeight] at hH
        omega
      have hlB := ihl (nextPhase p) H hnext hHl
      have hrB := ihr (nextPhase p) H hnext hHr
      have hjB : 2 + leaves (phaseJunk p) ≤ 19 + 6 * H := by
        have h1 := phaseJunk_leaves_bound p hp
        have hpH : p.2 ≤ H := by simp only [layoutHeight] at hH; omega
        omega
      have hident :
          (2 * openedCount l + 1) * (19 + 6 * H) +
          (2 * openedCount r + 1) * (19 + 6 * H) +
          1 * (19 + 6 * H) =
          (2 * openedCount (.opened l r) + 1) * (19 + 6 * H) := by
        have hc : (2 * openedCount l + 1) + (2 * openedCount r + 1) + 1 =
            2 * openedCount (.opened l r) + 1 := by
          simp [openedCount]; omega
        rw [← Nat.add_mul, ← Nat.add_mul, hc]
      simp only [Nat.one_mul] at hident
      omega

theorem openedCount_bitLayout (b : Bool) : openedCount (bitLayout b) ≤ 1 := by
  cases b <;> decide

theorem openedCount_fieldsLayout (bits : List Bool) :
    openedCount (fieldsLayout bits) ≤ 2 * bits.length + 1 := by
  induction bits with
  | nil => decide
  | cons b bs ih =>
      have hb := openedCount_bitLayout b
      simp only [fieldsLayout, openedCount, List.length_cons]
      omega

theorem openedCount_versionLayout {width : Nat}
    (recs : List {bits : List Bool // bits.length = width}) :
    openedCount (versionLayout recs) ≤ recs.length * (2 * width + 2) := by
  induction recs with
  | nil => simp [versionLayout, openedCount]
  | cons entry rest ih =>
      have hf := openedCount_fieldsLayout entry.val
      rw [entry.property] at hf
      have hstep : 1 + openedCount (versionLayout rest) + openedCount (fieldsLayout entry.val) ≤
          rest.length * (2 * width + 2) + (2 * width + 2) := by omega
      have hmul : (rest.length + 1) * (2 * width + 2) =
          rest.length * (2 * width + 2) + (2 * width + 2) := Nat.succ_mul rest.length (2 * width + 2)
      simp only [versionLayout, openedCount, List.length_cons]
      omega

def sumCellRecords : List (List UniversalCell) → Nat
  | [] => 0
  | c :: cs => c.length + sumCellRecords cs

theorem sumCellRecords_append (a b : List (List UniversalCell)) :
    sumCellRecords (a ++ b) = sumCellRecords a + sumCellRecords b := by
  induction a with
  | nil => simp [sumCellRecords]
  | cons c cs ih => simp [sumCellRecords, ih]; omega

theorem openedCount_storageTapeLayout (cells : List (List UniversalCell)) :
    openedCount (storageTapeLayout cells) ≤ cells.length + 24 * sumCellRecords cells := by
  induction cells with
  | nil => simp [storageTapeLayout, openedCount, sumCellRecords]
  | cons c cs ih =>
      have hv := openedCount_versionLayout (c.map encodedEntry)
      simp only [List.length_map] at hv
      simp only [storageTapeLayout, openedCount, List.length_cons, sumCellRecords]
      omega

theorem sumCellRecords_offRecords (bits : List Bool) :
    sumCellRecords (bits.map offRecords) ≤ bits.length := by
  induction bits with
  | nil => simp [sumCellRecords]
  | cons b bs ih =>
      cases b <;> simp [offRecords, sumCellRecords] <;> omega

theorem initialRecords_counts (u : UConfig) :
    (initialRecords (encodeUConfig u)).length = 4 * tapeLen u ∧
    sumCellRecords (initialRecords (encodeUConfig u)) ≤ 4 * tapeLen u := by
  have hl : (flattenSymbols u.leftRev.reverse).length = 4 * u.leftRev.length := by
    rw [flattenSymbols_length, List.length_reverse]
  have hr : (flattenSymbols u.right).length = 4 * u.right.length :=
    flattenSymbols_length u.right
  constructor
  · simp [initialRecords, encodeUConfig, tapeLen, hl, hr]
    omega
  · have h1 : sumCellRecords ((flattenSymbols u.leftRev.reverse).map offRecords) ≤ 4 * u.leftRev.length := by
      have hx := sumCellRecords_offRecords (flattenSymbols u.leftRev.reverse)
      omega
    have h2 : sumCellRecords (([symbolBitAt u.symbol 1, symbolBitAt u.symbol 2, symbolBitAt u.symbol 3] ++ flattenSymbols u.right).map offRecords) ≤
        3 + 4 * u.right.length := by
      have hx := sumCellRecords_offRecords
        ([symbolBitAt u.symbol 1, symbolBitAt u.symbol 2, symbolBitAt u.symbol 3] ++ flattenSymbols u.right)
      have hlen2 : ([symbolBitAt u.symbol 1, symbolBitAt u.symbol 2, symbolBitAt u.symbol 3] ++ flattenSymbols u.right).length =
          3 + 4 * u.right.length := by simp [hr]; omega
      omega
    have hmid : sumCellRecords [[activeCellRecord (symbolBitAt u.symbol 0) (binaryStartState u.state)]] = 1 := rfl
    unfold initialRecords encodeUConfig tapeLen
    dsimp only []
    rw [sumCellRecords_append, sumCellRecords_append, hmid]
    omega

theorem canonicalRoot_leaves_from_opened (cells : List (List UniversalCell)) (K : Nat)
    (hK : openedCount (storageTapeLayout cells) ≤ K) :
    leaves (canonicalRoot cells 1 (depthBase 1) (depthJunk 0)) ≤
      50 + (2 * K + 1) * (31 + 6 * K) := by
  have hp1 := phase_at_good 1
  have hh := layoutHeight_le_openedCount (storageTapeLayout cells)
  have hH : (phaseAt 1).2 + layoutHeight (storageTapeLayout cells) ≤ 2 + K := by
    have hph2 : (phaseAt 1).2 = 2 := rfl
    omega
  have htape := layoutTerm_leaves_bound (storageTapeLayout cells) (phaseAt 1) (2 + K) hp1 hH
  have htape' : leaves (canonicalTape cells 1) ≤ (2 * K + 1) * (31 + 6 * K) := by
    have heq : 19 + 6 * (2 + K) = 31 + 6 * K := by omega
    rw [heq] at htape
    have hmono1 : 2 * openedCount (storageTapeLayout cells) + 1 ≤ 2 * K + 1 := by omega
    exact Nat.le_trans htape (Nat.mul_le_mul_right (31 + 6 * K) hmono1)
  have hhead : leaves (numeral 1 ⋅ S) = 8 := rfl
  have hflag : leaves (depthBase 1) = 17 := rfl
  have hjunk : leaves (depthJunk 0) = 23 := rfl
  unfold canonicalRoot seedHubRoot
  rw [leaves, hhead, frame_leaves, hflag, hjunk]
  omega

theorem quad_bound_100 (N : Nat) :
    50 + (2 * (100 * N) + 1) * (31 + 6 * (100 * N)) ≤ 125000 * (N + 1) ^ 2 := by
  have h1 : 2 * (100 * N) + 1 ≤ 200 * (N + 1) := by omega
  have h2 : 31 + 6 * (100 * N) ≤ 600 * (N + 1) := by omega
  have hmul : (2 * (100 * N) + 1) * (31 + 6 * (100 * N)) ≤ (200 * (N + 1)) * (600 * (N + 1)) :=
    Nat.mul_le_mul h1 h2
  have hsq : (200 * (N + 1)) * (600 * (N + 1)) = 120000 * ((N + 1) ^ 2) := by
    simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hpos : 1 ≤ (N + 1) ^ 2 := by
    simp [Nat.pow_two]
    exact Nat.mul_pos (Nat.succ_pos N) (Nat.succ_pos N)
  omega

/-- Explicit polynomial constant for initial and source-boundary unfolded pure-S leaf counts. -/
def initialSizeConst : Nat := 125000

/-- **Polynomial Initial Size Bound**: the unfolded S-leaf count of `sEncodeU initial`
    is bounded by `125000 * (tapeLen initial + 1)^2`. -/
theorem polynomial_initial_size_bound (initial : UConfig) :
    leaves (sEncodeU initial) ≤ initialSizeConst * (tapeLen initial + 1) ^ 2 := by
  obtain ⟨hlen, hsum⟩ := initialRecords_counts initial
  have hopen := openedCount_storageTapeLayout (initialRecords (encodeUConfig initial))
  have hK : openedCount (storageTapeLayout (initialRecords (encodeUConfig initial))) ≤ 100 * tapeLen initial := by
    omega
  have hroot := canonicalRoot_leaves_from_opened (initialRecords (encodeUConfig initial)) (100 * tapeLen initial) hK
  exact Nat.le_trans hroot (quad_bound_100 (tapeLen initial))

theorem source_transition_counts {program : BinaryProgram} {a b : List (List UniversalCell)}
    (h : SourceTransition program a b) :
    b.length ≤ a.length + 1 ∧ sumCellRecords b ≤ sumCellRecords a + 3 := by
  cases h with
  | stay before source after _ _ _ hb hs ha hr hd =>
      clear hb hs ha hr hd
      simp only [List.length_append, List.length_cons, List.length_nil, sumCellRecords_append, sumCellRecords]
      constructor <;> omega
  | leftBoundary source after _ _ _ hs ha hr hd =>
      clear hs ha hr hd
      simp only [List.length_cons, List.length_append, List.length_nil, sumCellRecords]
      constructor <;> omega
  | rightExisting before source destination after _ _ _ hb hs hd0 ha hr hd =>
      clear hb hs hd0 ha hr hd
      simp only [List.length_append, List.length_cons, List.length_nil, sumCellRecords_append, sumCellRecords]
      constructor <;> omega
  | rightExtend before source _ _ _ hb hs hr hd =>
      clear hb hs hr hd
      simp only [List.length_append, List.length_cons, List.length_nil, sumCellRecords_append, sumCellRecords]
      constructor <;> omega
  | leftExisting before destination source after _ _ _ hb hd0 hs ha hr hd =>
      clear hb hd0 hs ha hr hd
      simp only [List.length_append, List.length_cons, List.length_nil, sumCellRecords_append, sumCellRecords]
      constructor <;> omega

theorem source_run_counts {program : BinaryProgram} {t : Nat}
    {start finish : List (List UniversalCell)} (run : SourceRun program t start finish) :
    finish.length ≤ start.length + t ∧ sumCellRecords finish ≤ sumCellRecords start + 3 * t := by
  induction run with
  | zero _ => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | next hstep hrest ih =>
      obtain ⟨hl, hs⟩ := source_transition_counts hstep
      clear hstep hrest
      constructor <;> omega

/-- **Polynomial Source-Boundary Trajectory Size Bound**: after `t` binary source transitions
    from `sEncodeU initial`, the unfolded S-leaf count is `≤ 125000 * (tapeLen initial + t + 1)^2`. -/
theorem polynomial_source_boundary_size_bound (initial : UConfig) {t : Nat}
    {cells : List (List UniversalCell)}
    (hrun : SourceRun fixedBinaryProgram t (initialRecords (encodeUConfig initial)) cells) :
    leaves (canonicalRoot cells 1 (depthBase 1) (depthJunk 0)) ≤
      initialSizeConst * (tapeLen initial + t + 1) ^ 2 := by
  obtain ⟨hlen0, hsum0⟩ := initialRecords_counts initial
  obtain ⟨hlenT, hsumT⟩ := source_run_counts hrun
  have hopen := openedCount_storageTapeLayout cells
  have hK : openedCount (storageTapeLayout cells) ≤ 100 * (tapeLen initial + t) := by omega
  have hroot := canonicalRoot_leaves_from_opened cells (100 * (tapeLen initial + t)) hK
  exact Nat.le_trans hroot (quad_bound_100 (tapeLen initial + t))

theorem openedCount_leftSpine (m : Nat) : openedCount (leftSpine m) = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [leftSpine, openedCount, ih]; omega

theorem postHaltFlag_leaves_bound (m : Nat) :
    leaves (layoutTerm (postHaltFlagLayout m) (phaseAt 1).1 (phaseAt 1).2) ≤
      200 * (m + 1) ^ 2 := by
  have hp1 := phase_at_good 1
  have hop : openedCount (postHaltFlagLayout m) = m + 1 := by
    simp [postHaltFlagLayout, openedCount, openedCount_leftSpine]; omega
  have hh := layoutHeight_le_openedCount (postHaltFlagLayout m)
  have hH : (phaseAt 1).2 + layoutHeight (postHaltFlagLayout m) ≤ m + 3 := by
    have hph2 : (phaseAt 1).2 = 2 := rfl
    omega
  have hb := layoutTerm_leaves_bound (postHaltFlagLayout m) (phaseAt 1) (m + 3) hp1 hH
  rw [hop] at hb
  have h1 : 2 * (m + 1) + 1 ≤ 3 * (m + 1) := by omega
  have h2 : 19 + 6 * (m + 3) ≤ 43 * (m + 1) := by omega
  have hmul : (2 * (m + 1) + 1) * (19 + 6 * (m + 3)) ≤ (3 * (m + 1)) * (43 * (m + 1)) :=
    Nat.mul_le_mul h1 h2
  have hsq : (3 * (m + 1)) * (43 * (m + 1)) = 129 * ((m + 1) ^ 2) := by
    simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  omega

/-- Explicit polynomial constant for arbitrary native pure-S contractions along the trajectory. -/
def trajectorySizeConst : Nat := 600000

/-- **All-Step Polynomial Trajectory Size Bound & Canonical Structural Invariant**:
    At EVERY native S contraction `k` along `FullSelectorTrace fixedBinaryProgram k (sEncodeU initial) reached`
    (including intermediate opening contractions, pending-move transactions, halt-flag opening,
    and post-halt perpetual frontier contractions):
    1. `reached = seedHubRoot flag tape (depthJunk 0)` with `logicalTreeStrict (frameTerm flag tape (depthJunk 0)) = true`;
    2. `leaves reached ≤ 600000 * (tapeLen initial + k + 1)^2`. -/
theorem polynomial_trajectory_size_bound (initial : UConfig) {k : Nat} {reached : Term}
    (htrace : FullSelectorTrace fixedBinaryProgram k (sEncodeU initial) reached) :
    (∃ flag tape,
      reached = seedHubRoot flag tape (depthJunk 0) ∧
      logicalTreeStrict (frameTerm flag tape (depthJunk 0)) = true) ∧
    leaves reached ≤ trajectorySizeConst * (tapeLen initial + k + 1) ^ 2 := by
  have hrep0 := initial_records_represent (encodeUConfig initial)
  have hspec := plainRunFor_spec fixedBinaryProgram (k + 1) (encodeUConfig initial)
  cases hr : plainRunFor fixedBinaryProgram (k + 1) (encodeUConfig initial) with
  | inr future =>
      rw [hr] at hspec
      obtain ⟨futureCells, hsourceRun, _⟩ :=
        plain_run_lifts fixedBinaryProgram hspec (initialRecords (encodeUConfig initial)) hrep0
      obtain ⟨M, hloM, _, hnice⟩ := source_run_nice_selector fixedBinaryProgram hsourceRun
      have hkM : k < M := by omega
      obtain ⟨hhub, hleavesLe⟩ := niceSelectorTrace_prefix_props hnice htrace hkM
      have hboundCheckpoint := polynomial_source_boundary_size_bound initial hsourceRun
      have hN : tapeLen initial + (k + 1) + 1 ≤ 2 * (tapeLen initial + k + 1) := by omega
      have hsq : (tapeLen initial + (k + 1) + 1) ^ 2 ≤ 4 * (tapeLen initial + k + 1) ^ 2 := by
        calc
          (tapeLen initial + (k + 1) + 1) ^ 2
              ≤ (2 * (tapeLen initial + k + 1)) ^ 2 := Nat.pow_le_pow_left hN 2
          _ = 4 * (tapeLen initial + k + 1) ^ 2 := by
              simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hfinalBound : leaves (canonicalRoot futureCells 1 (depthBase 1) (depthJunk 0)) ≤
          trajectorySizeConst * (tapeLen initial + k + 1) ^ 2 := by
        unfold initialSizeConst at hboundCheckpoint
        unfold trajectorySizeConst
        omega
      exact ⟨hhub, Nat.le_trans hleavesLe hfinalBound⟩
  | inl pair =>
      rcases pair with ⟨tHalt, stoppedCfg⟩
      rw [hr] at hspec
      rcases hspec with ⟨htLe, hplainRun, hstopPlain⟩
      obtain ⟨finalCells, hsourceRun, hrepFinal⟩ :=
        plain_run_lifts fixedBinaryProgram hplainRun (initialRecords (encodeUConfig initial)) hrep0
      obtain ⟨before, source, after, hcellsEq, hb, hs, ha, _, _⟩ := hrepFinal
      subst finalCells
      have hruleNone : fixedBinaryProgram stoppedCfg.state stoppedCfg.bit = none :=
        (plain_next_none_iff_rule_none fixedBinaryProgram stoppedCfg).mp hstopPlain
      obtain ⟨k1, lo1, _, hnice1⟩ := source_run_nice_selector fixedBinaryProgram hsourceRun
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
      obtain ⟨hhub, hleavesLe⟩ := niceSelectorTrace_prefix_props htotalNice htrace hkM
      have hboundBoundary := polynomial_source_boundary_size_bound initial hsourceRun
      have htapeLeaves : leaves tape ≤ 4 * initialSizeConst * (tapeLen initial + k + 1) ^ 2 := by
        have hb1 : leaves tape ≤ leaves (canonicalRoot (before ++ source :: after) 1 (depthBase 1) (depthJunk 0)) := by
          dsimp only [tape]
          unfold canonicalRoot seedHubRoot
          rw [leaves, frame_leaves]
          omega
        have hN : tapeLen initial + tHalt + 1 ≤ 2 * (tapeLen initial + k + 1) := by omega
        have hsq : (tapeLen initial + tHalt + 1) ^ 2 ≤ 4 * (tapeLen initial + k + 1) ^ 2 := by
          calc
            (tapeLen initial + tHalt + 1) ^ 2
                ≤ (2 * (tapeLen initial + k + 1)) ^ 2 := Nat.pow_le_pow_left hN 2
            _ = 4 * (tapeLen initial + k + 1) ^ 2 := by
                simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        have hmul := Nat.mul_le_mul_left initialSizeConst hsq
        have hassoc : initialSizeConst * (4 * (tapeLen initial + k + 1) ^ 2) =
            4 * initialSizeConst * (tapeLen initial + k + 1) ^ 2 := by
          simp [Nat.mul_left_comm, Nat.mul_comm]
        rw [hassoc] at hmul
        exact Nat.le_trans hb1 (Nat.le_trans hboundBoundary hmul)
      have hflagLeaves := postHaltFlag_leaves_bound (k + 1)
      have hflagLeaves' :
          leaves (layoutTerm (postHaltFlagLayout (k + 1)) (phaseAt 1).1 (phaseAt 1).2) ≤
            800 * (tapeLen initial + k + 1) ^ 2 := by
        have hmLe : k + 1 + 1 ≤ 2 * (tapeLen initial + k + 1) := by omega
        have hsq : (k + 1 + 1) ^ 2 ≤ 4 * (tapeLen initial + k + 1) ^ 2 := by
          calc
            (k + 1 + 1) ^ 2 ≤ (2 * (tapeLen initial + k + 1)) ^ 2 := Nat.pow_le_pow_left hmLe 2
            _ = 4 * (tapeLen initial + k + 1) ^ 2 := by
                simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        omega
      have hcheckpointLeaves :
          leaves (seedHubRoot (layoutTerm (postHaltFlagLayout (k + 1)) (phaseAt 1).1 (phaseAt 1).2) tape (depthJunk 0)) ≤
            trajectorySizeConst * (tapeLen initial + k + 1) ^ 2 := by
        have hhead : leaves (numeral 1 ⋅ S) = 8 := rfl
        have hjunk : leaves (depthJunk 0) = 23 := rfl
        have hpos : 1 ≤ (tapeLen initial + k + 1) ^ 2 := by
          simp [Nat.pow_two]
          exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
        unfold seedHubRoot initialSizeConst trajectorySizeConst at *
        rw [leaves, hhead, frame_leaves, hjunk]
        omega
      exact ⟨hhub, Nat.le_trans hleavesLe hcheckpointLeaves⟩

#print axioms halted_s_term_reads_back_u_config
#print axioms halted_u_reaches_readable_s_term
#print axioms polynomial_initial_size_bound
#print axioms polynomial_source_boundary_size_bound
#print axioms polynomial_trajectory_size_bound
