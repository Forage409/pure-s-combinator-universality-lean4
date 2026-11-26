import formal_utm.neary_cycles

/-!
# Neary `U(3,11)` Complete Simulation, Constructive Universality & Output Readback

Proves Chapter 3 of Neary (2008) for `fixedUProgram` (`uNext`) composed with
`normalizeSafe`:
- **Lemma 3.4.4** (`init_to_postIndex`): Initial `encodeNormalizedToU N word`
  reaches `PostIndexInv` in `≥ 1` steps.
- **Lemma 3.4.5** (`postIndex_step`): Every safe normalized step (`normStepSafe = some nc'`)
  transitions `PostIndexInv N nc` to `PostIndexInv N nc'` in `≥ 1` steps
  (covering R-move write `0`/`1`, Case D `E'`+`E`, and L-move read `0`/`1`).
- **Lemma 3.4.3** (`postIndex_halt`): Left-boundary exit (`normStepSafe = none`)
  halts `U(3,11)` at `(stateU3, symDELTA)` preserving the encoded output tape.
- **Constructive Master Theorem** (`source_halts_iff_u_stops`):
  `SourceEventuallyStopsTM M w ↔ UEventuallyStops (encodeSourceInstance M w)`
  proved purely constructively via bounded decidable evaluation.
- **Output Readback** (`u_halt_output_readback`):
  `decodeHaltedUConfig final = some (canonicalOutput M w hsrc)` whenever
  `URun n (encodeSourceInstance M w) final ∧ uNext final = none`.
-/

/-! ## Section 1: Block Table Splitting & Restoration Identities -/

theorem getD_eq_getElem {α : Type} (xs : List α) (k : Nat) (hk : k < xs.length) (d : α) :
    xs.getD k d = xs[k]'hk := by
  simp [List.getD, List.getElem?_eq_getElem hk]

theorem take_cons_drop {α : Type} :
    ∀ (xs : List α) (k : Nat) (hk : k < xs.length),
      xs = xs.take k ++ (xs[k]'hk) :: xs.drop (k + 1)
  | [], _, hk => by cases hk
  | x :: rest, 0, _ => rfl
  | x :: rest, k + 1, hk => by
    have ih := take_cons_drop rest k (Nat.lt_of_succ_lt_succ hk)
    exact congrArg (x :: ·) ih

theorem reverse_split_at {α : Type} (xs : List α) (k : Nat) (hk : k < xs.length) :
    xs.reverse = (xs.drop (k + 1)).reverse ++ [xs[k]'hk] ++ (xs.take k).reverse := by
  have h := congrArg List.reverse (take_cons_drop xs k hk)
  have hrhs : (xs.take k ++ (xs[k]'hk) :: xs.drop (k + 1)).reverse =
      (xs.drop (k + 1)).reverse ++ [xs[k]'hk] ++ (xs.take k).reverse := by
    have hc : (xs[k]'hk) :: xs.drop (k + 1) = [xs[k]'hk] ++ xs.drop (k + 1) := rfl
    rw [hc, List.reverse_append, List.reverse_append]
    simp [List.append_assoc]
  exact h.trans hrhs

def tableFull (N : NormalizedTM) : List (Fin 11) :=
  (nearyBlocksR2L N).reverse.flatMap (fun c => symLAMBDA :: c)

def untouchedLeft (N : NormalizedTM) (k : Nat) : List (Fin 11) :=
  ((nearyBlocksR2L N).drop (k + 1)).reverse.flatMap (fun c => symLAMBDA :: c)

def neutralizedRight (N : NormalizedTM) (k : Nat) : List (Fin 11) :=
  ((nearyBlocksR2L N).take k).reverse.flatMap (fun c => symDELTA :: c.map toArrowL)

theorem tableFull_split (N : NormalizedTM) (k : Nat) (hk : k < 5 * N.numStates) :
    tableFull N =
      untouchedLeft N k ++ [symLAMBDA] ++ (nearyBlocksR2L N).getD k [] ++
        (((nearyBlocksR2L N).take k).reverse.flatMap fun c => symLAMBDA :: c) := by
  have hkB : k < (nearyBlocksR2L N).length := by rwa [nearyBlocksR2L_length]
  rw [getD_eq_getElem (nearyBlocksR2L N) k hkB []]
  unfold tableFull untouchedLeft
  rw [reverse_split_at (nearyBlocksR2L N) k hkB]
  simp [List.flatMap_append, List.append_assoc]

private theorem mem_of_mem_take {α : Type} {x : α} {k : Nat} {xs : List α}
    (h : x ∈ xs.take k) : x ∈ xs := by
  induction xs generalizing k with
  | nil => simp at h
  | cons y ys ih =>
    cases k with
    | zero => simp at h
    | succ j =>
      simp only [List.take, List.mem_cons] at h
      rcases h with rfl | ht
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem y (ih ht)

theorem take_blocks_all_etrSym (N : NormalizedTM) (k : Nat) :
    ∀ c ∈ (nearyBlocksR2L N).take k, ∀ s ∈ c, IsETRSym s := by
  intro c hc s hs
  exact nearyBlocksR2L_all_etrSym N c (mem_of_mem_take hc) s hs

theorem take_blocks_all_bodySym (N : NormalizedTM) (k : Nat) :
    ∀ c ∈ (nearyBlocksR2L N).take k, ∀ s ∈ c, IsBodySym s := by
  intro c hc s hs
  exact isBody_of_isETR (take_blocks_all_etrSym N k c hc s hs)

theorem neutralizedRight_all_arrow (N : NormalizedTM) (k : Nat) :
    ∀ s ∈ neutralizedRight N k, IsArrowSym s := by
  intro s hs
  unfold neutralizedRight at hs
  rw [List.mem_flatMap] at hs
  obtain ⟨c, hcRev, hsC⟩ := hs
  rw [List.mem_reverse] at hcRev
  simp only [List.mem_cons, List.mem_map] at hsC
  rcases hsC with rfl | ⟨x, hx, rfl⟩
  · exact Or.inr (Or.inr rfl)
  · exact isArrow_toArrowL (take_blocks_all_bodySym N k c hcRev x hx)

private theorem flatMap_map_restore (xs : List (List (Fin 11)))
    (hxs : ∀ c ∈ xs, ∀ s ∈ c, IsETRSym s) :
    (xs.flatMap (fun c => symDELTA :: c.map toArrowL)).map restoreSym =
      xs.flatMap (fun c => symLAMBDA :: c) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_map]
    have hc : List.map (restoreSym ∘ toArrowL) c = c :=
      (List.map_congr_left fun s hs => restoreSym_toArrowL_etr (hxs c List.mem_cons_self s hs)).trans
        (List.map_id c)
    have hd : restoreSym symDELTA = symLAMBDA := rfl
    rw [hd, hc, ih (fun y hy => hxs y (List.mem_cons_of_mem c hy))]

theorem neutralizedRight_restore (N : NormalizedTM) (k : Nat) :
    (neutralizedRight N k).map restoreSym =
      ((nearyBlocksR2L N).take k).reverse.flatMap (fun c => symLAMBDA :: c) := by
  unfold neutralizedRight
  apply flatMap_map_restore
  intro c hc
  rw [List.mem_reverse] at hc
  exact take_blocks_all_etrSym N k c hc

theorem restored_table_eq_full (N : NormalizedTM) (k : Nat) (hk : k < 5 * N.numStates) :
    untouchedLeft N k ++ [symLAMBDA] ++ (nearyBlocksR2L N).getD k [] ++
        (neutralizedRight N k).map restoreSym =
      tableFull N := by
  rw [neutralizedRight_restore, ← tableFull_split N k hk]

/-! ## Section 2: ETR Lengths, Target Encodings & Block Lookups -/

theorem etrToTargetSym_E : etrToTargetSym symE = symLA := rfl
theorem etrToTargetSym_H : etrToTargetSym symH = symLB := rfl

theorem map_target_rep_E (n : Nat) :
    (List.replicate n symE).map etrToTargetSym = List.replicate n symLA := by
  rw [List.map_replicate]; rfl

theorem map_target_rep_H (n : Nat) :
    (List.replicate n symH).map etrToTargetSym = List.replicate n symLB := by
  rw [List.map_replicate]; rfl

theorem nearyETR_right_false_props (S : Nat) (_hS : S ≥ 2) (nxt : Fin S) :
    let act : NormAct S := ⟨false, .right, nxt⟩
    (nearyETR S act).length = 5 * S + 2 ∧
    nearyA S act = 5 * (S - nxt.val) ∧
    nearyB act = 2 + 5 * nxt.val ∧
    nearyA S act ≥ 5 ∧
    (nearyETR S act).map etrToTargetSym =
      symLA :: (List.replicate (5 * (S - nxt.val) - 1) symLA ++ List.replicate (2 + 5 * nxt.val) symLB) := by
  have hy := nxt.isLt
  dsimp only []
  have hb : nearyB (⟨false, .right, nxt⟩ : NormAct S) = 2 + 5 * nxt.val := rfl
  have ha : nearyA S ⟨false, .right, nxt⟩ = 5 * (S - nxt.val) := by
    unfold nearyA; rw [hb]; omega
  have ha5 : nearyA S ⟨false, .right, nxt⟩ ≥ 5 := by omega
  have hexpr : nearyETR S ⟨false, .right, nxt⟩ =
      List.replicate (nearyA S ⟨false, .right, nxt⟩) symE ++
      List.replicate (nearyB ⟨false, .right, nxt⟩) symH := rfl
  refine ⟨?_, ha, hb, ha5, ?_⟩
  · rw [hexpr, List.length_append, List.length_replicate, List.length_replicate, ha, hb]
    omega
  · rw [hexpr, List.map_append, map_target_rep_E, map_target_rep_H, ha, hb]
    have hsplit : 5 * (S - nxt.val) = 1 + (5 * (S - nxt.val) - 1) := by omega
    conv => lhs; arg 1; rw [hsplit]
    rw [replicate_add_split 1]
    rfl

theorem nearyETR_right_true_props (S : Nat) (_hS : S ≥ 2) (nxt : Fin S) :
    let act : NormAct S := ⟨true, .right, nxt⟩
    (nearyETR S act).length = 5 * S + 3 ∧
    nearyA S act = 5 * (S - nxt.val) ∧
    nearyB act = 2 + 5 * nxt.val ∧
    (nearyETR S act).map etrToTargetSym =
      symLB :: (List.replicate (5 * (S - nxt.val)) symLA ++ List.replicate (2 + 5 * nxt.val) symLB) := by
  have hy := nxt.isLt
  dsimp only []
  have hb : nearyB (⟨true, .right, nxt⟩ : NormAct S) = 2 + 5 * nxt.val := rfl
  have ha : nearyA S ⟨true, .right, nxt⟩ = 5 * (S - nxt.val) := by
    unfold nearyA; rw [hb]; omega
  have hexpr : nearyETR S ⟨true, .right, nxt⟩ =
      symH :: (List.replicate (nearyA S ⟨true, .right, nxt⟩) symE ++
      List.replicate (nearyB ⟨true, .right, nxt⟩) symH) := rfl
  refine ⟨?_, ha, hb, ?_⟩
  · rw [hexpr, List.length_cons, List.length_append, List.length_replicate, List.length_replicate, ha, hb]
    omega
  · rw [hexpr, List.map_cons, List.map_append, map_target_rep_E, map_target_rep_H, ha, hb]
    rfl

theorem nearyETR_left_props (S : Nat) (_hS : S ≥ 2) (w : Bool) (nxt : Fin S) :
    let act : NormAct S := ⟨w, .left, nxt⟩
    (nearyETR S act).length = 5 * S + 4 ∧
    nearyA S act = 5 * (S - nxt.val) - 3 ∧
    nearyB act = 5 + 5 * nxt.val ∧
    nearyA S act ≥ 2 ∧
    (nearyETR S act).map etrToTargetSym =
      symLA :: (List.replicate (5 * (S - nxt.val) - 5) symLA ++
        List.replicate (5 + 5 * nxt.val) symLB ++ [symLA] ++ encodeRightBit w) := by
  have hy := nxt.isLt
  dsimp only []
  have hb : nearyB (⟨w, .left, nxt⟩ : NormAct S) = 5 + 5 * nxt.val := by
    unfold nearyB; dsimp; omega
  have ha : nearyA S ⟨w, .left, nxt⟩ = 5 * (S - nxt.val) - 3 := by
    unfold nearyA; rw [hb]; omega
  have ha2 : nearyA S ⟨w, .left, nxt⟩ ≥ 2 := by omega
  have hexpr : nearyETR S ⟨w, .left, nxt⟩ =
      List.replicate (nearyA S ⟨w, .left, nxt⟩ - 1) symE ++
      List.replicate (nearyB ⟨w, .left, nxt⟩) symH ++
      (if w then [symE, symH, symE] else [symE, symE, symE]) := rfl
  refine ⟨?_, ha, hb, ha2, ?_⟩
  · rw [hexpr, List.length_append, List.length_append, List.length_replicate, List.length_replicate, ha, hb]
    cases w
    · change (5 * (S - nxt.val) - 3 - 1 + (5 + 5 * nxt.val)) + 3 = 5 * S + 4; omega
    · change (5 * (S - nxt.val) - 3 - 1 + (5 + 5 * nxt.val)) + 3 = 5 * S + 4; omega
  · rw [hexpr, List.map_append, List.map_append, map_target_rep_E, map_target_rep_H, ha, hb]
    have hsub : 5 * (S - nxt.val) - 3 - 1 = 1 + (5 * (S - nxt.val) - 5) := by omega
    rw [hsub, replicate_add_split 1]
    cases w
    · have htail : ([symE, symE, symE] : List (Fin 11)).map etrToTargetSym = [symLA] ++ encodeRightBit false := rfl
      change (List.replicate 1 symLA ++ List.replicate (5 * (S - nxt.val) - 5) symLA) ++
          List.replicate (5 + 5 * nxt.val) symLB ++ ([symE, symE, symE] : List (Fin 11)).map etrToTargetSym = _
      rw [htail]
      simp [List.replicate, List.append_assoc]
    · have htail : ([symE, symH, symE] : List (Fin 11)).map etrToTargetSym = [symLA] ++ encodeRightBit true := rfl
      change (List.replicate 1 symLA ++ List.replicate (5 * (S - nxt.val) - 5) symLA) ++
          List.replicate (5 + 5 * nxt.val) symLB ++ ([symE, symH, symE] : List (Fin 11)).map etrToTargetSym = _
      rw [htail]
      simp [List.replicate, List.append_assoc]

theorem nearyExtra_active_props (N : NormalizedTM) (q : Fin N.numStates)
    (hact : q.val = 0 ∨ hasIncomingRight N q = true) :
    let S := N.numStates
    nearyExtra N q = List.replicate (5 * (S - q.val) - 3) symE ++ List.replicate (4 + 5 * q.val) symH ∧
    (nearyExtra N q).length = 5 * S + 1 ∧
    5 * (S - q.val) - 3 ≥ 2 ∧
    (nearyExtra N q).map etrToTargetSym =
      symLA :: (List.replicate (5 * (S - q.val) - 4) symLA ++ List.replicate (4 + 5 * q.val) symLB) := by
  have hq := q.isLt
  have hge := N.hge2
  dsimp only []
  have hexpr : nearyExtra N q =
      List.replicate (5 * (N.numStates - q.val) - 3) symE ++ List.replicate (4 + 5 * q.val) symH := by
    unfold nearyExtra
    by_cases h0 : q.val = 0
    · rw [if_pos h0, h0]; simp
    · rw [if_neg h0]
      rcases hact with hq0 | hinc
      · exact False.elim (h0 hq0)
      · rw [hinc, if_pos rfl]
  refine ⟨hexpr, ?_, by omega, ?_⟩
  · rw [hexpr, List.length_append, List.length_replicate, List.length_replicate]
    omega
  · rw [hexpr, List.map_append, map_target_rep_E, map_target_rep_H]
    have hsplit : 5 * (N.numStates - q.val) - 3 = 1 + (5 * (N.numStates - q.val) - 4) := by omega
    conv => lhs; arg 1; rw [hsplit]
    rw [replicate_add_split 1]
    rfl

theorem block_getD_eq (N : NormalizedTM) (q : Fin N.numStates) (r : Nat) (hr : r < 5) :
    (nearyBlocksR2L N).getD (5 * q.val + r) [] =
      (nearyStateBlocksR2L N q)[r]'(by rw [nearyStateBlocksR2L_length]; exact hr) := by
  have hk : 5 * q.val + r < (nearyBlocksR2L N).length := by
    rw [nearyBlocksR2L_length]; have := q.isLt; omega
  have hr5 : r < (nearyStateBlocksR2L N q).length := by rw [nearyStateBlocksR2L_length]; exact hr
  have hopt := nearyBlocksR2L_get N q r hr
  rw [getD_eq_getElem _ _ hk []]
  rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hr5] at hopt
  injection hopt

/-! ## Section 3: Simulated Tape Encodings & `PostIndexInv` -/

def encLeftArrowBit (b : Bool) : List (Fin 11) :=
  [if b then symLH else symLE, symLE]

def encLeftCleanBit (b : Bool) : List (Fin 11) :=
  [if b then symH else symE, symE]

def leftBitsOf (tape : List Bool) (pos : Nat) : List Bool :=
  (List.range pos).map (bitAt tape)

theorem leftBitsOf_zero (tape : List Bool) : leftBitsOf tape 0 = [] := rfl

theorem leftBitsOf_succ (tape : List Bool) (pos : Nat) :
    leftBitsOf tape (pos + 1) = leftBitsOf tape pos ++ [bitAt tape pos] := by
  unfold leftBitsOf
  rw [List.range_succ, List.map_append, List.map_singleton]

theorem leftBitsOf_write_ge (tape : List Bool) (pos k : Nat) (w : Bool) (h : k ≤ pos) :
    leftBitsOf (writeTapeList tape pos w) k = leftBitsOf tape k := by
  unfold leftBitsOf
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [bitAt_writeTapeList, if_neg (by omega)]

theorem encLeftArrow_all_arrow (bits : List Bool) :
    ∀ s ∈ symLE :: bits.flatMap encLeftArrowBit, IsArrowSym s := by
  intro s hs
  rw [List.mem_cons] at hs
  rcases hs with rfl | hrest
  · exact Or.inl rfl
  · rw [List.mem_flatMap] at hrest
    obtain ⟨b, _, hb⟩ := hrest
    cases b with
    | false =>
      change s ∈ [symLE, symLE] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> exact Or.inl rfl
    | true =>
      change s ∈ [symLH, symLE] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl

theorem encLeftClean_all_body (bits : List Bool) :
    ∀ s ∈ symE :: bits.flatMap encLeftCleanBit, IsBodySym s := by
  intro s hs
  rw [List.mem_cons] at hs
  rcases hs with rfl | hrest
  · exact Or.inl rfl
  · rw [List.mem_flatMap] at hrest
    obtain ⟨b, _, hb⟩ := hrest
    cases b with
    | false =>
      change s ∈ [symE, symE] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> exact Or.inl rfl
    | true =>
      change s ∈ [symH, symE] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl

theorem encLeftArrow_restore (bits : List Bool) :
    (symLE :: bits.flatMap encLeftArrowBit).map restoreSym =
      symE :: bits.flatMap encLeftCleanBit := by
  simp only [List.map_cons]
  have he : restoreSym symLE = symE := rfl
  rw [he]
  congr 1
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.map_append, ih]
    cases b <;> rfl

theorem encLeftClean_toArrowL (bits : List Bool) :
    (symE :: bits.flatMap encLeftCleanBit).map toArrowL =
      symLE :: bits.flatMap encLeftArrowBit := by
  simp only [List.map_cons]
  have he : toArrowL symE = symLE := rfl
  rw [he]
  congr 1
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.map_append, ih]
    cases b <;> rfl

theorem uRightEq_encodeRightTape_unfold (bits : List Bool) :
    URightEq (encodeRightTape bits)
      (encodeRightBit (bitAt bits 0) ++ encodeRightTape (bits.drop 1)) := by
  cases bits with
  | nil =>
    change URightEq [] [symLA, symLA]
    exact uRightEq_pad [] 2
  | cons b bs =>
    exact uRightEq_refl _

theorem uConfigEq_uAt_right (left prefixSym r1 r2 : List (Fin 11)) (q : Fin 3)
    (hr : URightEq r1 r2) :
    UConfigEq (uAt left (prefixSym ++ r1) q) (uAt left (prefixSym ++ r2) q) := by
  have hall : URightEq (prefixSym ++ r1) (prefixSym ++ r2) := by
    induction prefixSym with
    | nil => exact hr
    | cons x xs ih => exact uRightEq_cons x ih
  cases h1 : prefixSym ++ r1 with
  | nil =>
    cases h2 : prefixSym ++ r2 with
    | nil => exact uConfigEq_refl _
    | cons y ys =>
      rw [h1, h2] at hall
      exact ⟨rfl, hall 0, rfl, fun i => hall (i + 1)⟩
  | cons x xs =>
    cases h2 : prefixSym ++ r2 with
    | nil =>
      rw [h1, h2] at hall
      exact ⟨rfl, hall 0, rfl, fun i => hall (i + 1)⟩
    | cons y ys =>
      rw [h1, h2] at hall
      exact ⟨rfl, hall 0, rfl, fun i => hall (i + 1)⟩

theorem uConfigEq_uAtRightmost_right (left : List (Fin 11)) (h : Fin 11)
    (xs r1 r2 : List (Fin 11)) (q : Fin 3) (hr : URightEq r1 r2) :
    UConfigEq (uAtRightmost left h xs r1 q) (uAtRightmost left h xs r2 q) := by
  induction xs generalizing left h with
  | nil =>
    exact uConfigEq_uAt_right left [h] r1 r2 q hr
  | cons x xs' ih =>
    exact ih (left ++ [h]) x

def postIndexConcrete (N : NormalizedTM) (k : Nat) (leftBits rightBits : List Bool) : UConfig :=
  uAtRightmost (untouchedLeft N k) symLAMBDA
    ((nearyBlocksR2L N).getD k [] ++ neutralizedRight N k ++ [symDELTA] ++
      (symLE :: leftBits.flatMap encLeftArrowBit) ++
      List.replicate (5 * N.numStates + 3) symLE)
    (symGAMMA :: encodeRightTape rightBits)
    stateU2

def PostIndexInv (N : NormalizedTM) (nc : NormConfig N.numStates) (u : UConfig) : Prop :=
  ∃ (k : Nat) (rightBits : List Bool),
    k < 5 * N.numStates ∧
    (nearyBlocksR2L N).getD k [] = nearyETR N.numStates (N.rule nc.state (bitAt nc.tape nc.head)) ∧
    (∀ j, bitAt rightBits j = bitAt nc.tape (nc.head + 1 + j)) ∧
    UConfigEq (postIndexConcrete N k (leftBitsOf nc.tape nc.head) rightBits) u

/-! ## Section 4: Reusable Subroutines (`cycle1_from_tableFull` & `execute_case_D`) -/

theorem cycle1_from_tableFull (N : NormalizedTM) (k : Nat) (hk : k < 5 * N.numStates)
    (mid leftArrow : List (Fin 11)) (extraLE a : Nat) (rs : List (Fin 11))
    (hmid : ∀ s ∈ mid, IsBodySym s)
    (hmidMap : mid.map toArrowL = leftArrow ++ List.replicate extraLE symLE) :
    ∃ steps, steps ≥ 1 ∧
      URun steps
        (uAt (tableFull N ++ [symLAMBDA] ++ mid)
          (List.replicate a symLA ++ List.replicate (k + 2) symLB ++ symLA :: rs) stateU1)
        (uAtRightmost (untouchedLeft N k) symLAMBDA
          ((nearyBlocksR2L N).getD k [] ++ neutralizedRight N k ++ [symDELTA] ++
            leftArrow ++ List.replicate (extraLE + (a + k + 2)) symLE)
          (symGAMMA :: rs) stateU2) := by
  have hkB : k < (nearyBlocksR2L N).length := by rwa [nearyBlocksR2L_length]
  have htakeLen : ((nearyBlocksR2L N).take k).length = k := by
    rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hkB)
  let chunks := (nearyBlocksR2L N).take k
  let baseLeft := untouchedLeft N k ++ [symLAMBDA] ++ (nearyBlocksR2L N).getD k []
  have hsplit := tableFull_split N k hk
  obtain ⟨st, hst, hc1⟩ := cycle1_full chunks baseLeft mid a rs
    (take_blocks_all_bodySym N k) hmid
  have hstartL : baseLeft ++ (chunks.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ mid =
      tableFull N ++ [symLAMBDA] ++ mid := by
    dsimp [baseLeft, chunks]
    rw [← hsplit]
  have hstartR : List.replicate a symLA ++ List.replicate (chunks.length + 2) symLB ++ symLA :: rs =
      List.replicate a symLA ++ List.replicate (k + 2) symLB ++ symLA :: rs := by
    dsimp [chunks]; rw [htakeLen]
  rw [hstartL, hstartR] at hc1
  have hendEq : uAtRightmost (baseLeft ++ (chunks.reverse.flatMap fun c => symDELTA :: c.map toArrowL))
        symDELTA (mid.map toArrowL ++ List.replicate (a + chunks.length + 2) symLE) (symGAMMA :: rs) stateU2 =
      uAtRightmost (untouchedLeft N k) symLAMBDA
        ((nearyBlocksR2L N).getD k [] ++ neutralizedRight N k ++ [symDELTA] ++
          leftArrow ++ List.replicate (extraLE + (a + k + 2)) symLE)
        (symGAMMA :: rs) stateU2 := by
    dsimp [baseLeft, chunks]
    rw [htakeLen, hmidMap, List.append_assoc leftArrow, ← replicate_add_split]
    have happ := uAtRightmost_append (untouchedLeft N k) symLAMBDA
      ((nearyBlocksR2L N).getD k [] ++ neutralizedRight N k)
      (symDELTA :: (leftArrow ++ List.replicate (extraLE + (a + k + 2)) symLE))
      (symGAMMA :: rs) stateU2
    dsimp only [] at happ
    have hassocL : untouchedLeft N k ++ [symLAMBDA] ++ ((nearyBlocksR2L N).getD k [] ++ neutralizedRight N k) =
        untouchedLeft N k ++ [symLAMBDA] ++ (nearyBlocksR2L N).getD k [] ++
          (((nearyBlocksR2L N).take k).reverse.flatMap fun c => symDELTA :: c.map toArrowL) := by
      simp [neutralizedRight, List.append_assoc]
    have hassocR : ((nearyBlocksR2L N).getD k [] ++ neutralizedRight N k) ++
          (symDELTA :: (leftArrow ++ List.replicate (extraLE + (a + k + 2)) symLE)) =
        (nearyBlocksR2L N).getD k [] ++ neutralizedRight N k ++ [symDELTA] ++
          leftArrow ++ List.replicate (extraLE + (a + k + 2)) symLE := by
      simp [List.append_assoc]
    rw [← hassocL, ← hassocR]
    exact happ.symm
  rw [hendEq] at hc1
  exact ⟨st, hst, hc1⟩

theorem execute_case_D (N : NormalizedTM) (q : Fin N.numStates)
    (hact : q.val = 0 ∨ hasIncomingRight N q = true)
    (mid : List (Fin 11)) (leftBits nextRight : List Bool)
    (hmid : ∀ s ∈ mid, IsBodySym s)
    (hmidMap : mid.map toArrowL = symLE :: leftBits.flatMap encLeftArrowBit) :
    ∃ steps, steps ≥ 1 ∧
      URun steps
        (uAt (tableFull N ++ [symLAMBDA] ++ mid)
          (List.replicate (5 * (N.numStates - q.val)) symLA ++
            List.replicate (5 * q.val + 2) symLB ++
            encodeRightBit false ++ encodeRightTape nextRight) stateU1)
        (postIndexConcrete N (5 * q.val + 2) leftBits nextRight) := by
  let S := N.numStates
  have hq := q.isLt
  have hge := N.hge2
  let k0 := 5 * q.val
  have hk0 : k0 < 5 * S := by omega
  have hmidMap0 : mid.map toArrowL = (symLE :: leftBits.flatMap encLeftArrowBit) ++ List.replicate 0 symLE := by
    rw [hmidMap]; simp
  obtain ⟨s1, hs1, hr1⟩ := cycle1_from_tableFull N k0 hk0 mid
    (symLE :: leftBits.flatMap encLeftArrowBit) 0 (5 * (S - q.val))
    (symLA :: encodeRightTape nextRight) hmid hmidMap0
  have hstartR : List.replicate (5 * (S - q.val)) symLA ++ List.replicate (k0 + 2) symLB ++
        symLA :: symLA :: encodeRightTape nextRight =
      List.replicate (5 * (S - q.val)) symLA ++ List.replicate (5 * q.val + 2) symLB ++
        encodeRightBit false ++ encodeRightTape nextRight := by
    simp [k0, encodeRightBit, List.append_assoc]
  rw [hstartR] at hr1
  have hblk0 : (nearyBlocksR2L N).getD k0 [] = nearyExtra N q := by
    have hk0Eq : k0 = 5 * q.val + 0 := rfl
    rw [hk0Eq, block_getD_eq N q 0 (by decide)]
    rfl
  obtain ⟨_, hextraLen, _, hextraMap⟩ := nearyExtra_active_props N q hact
  have hlenSplit : 0 + (5 * (S - q.val) + k0 + 2) = 1 + (nearyExtra N q).length := by
    rw [hextraLen]; dsimp [k0, S]; omega
  rw [hblk0, hlenSplit, replicate_add_split 1 (nearyExtra N q).length symLE] at hr1
  let midArrow := neutralizedRight N k0 ++ [symDELTA] ++
    (symLE :: leftBits.flatMap encLeftArrowBit) ++ [symLE]
  have hmidArrow : ∀ s ∈ midArrow, IsArrowSym s := by
    intro s hs
    simp only [midArrow, List.mem_append, List.mem_singleton] at hs
    rcases hs with ((hn | rfl) | hl) | rfl
    · exact neutralizedRight_all_arrow N k0 s hn
    · exact Or.inr (Or.inr rfl)
    · exact encLeftArrow_all_arrow leftBits s hl
    · exact Or.inl rfl
  have hr1Align : nearyExtra N q ++ neutralizedRight N k0 ++ [symDELTA] ++
        (symLE :: leftBits.flatMap encLeftArrowBit) ++
        (List.replicate 1 symLE ++ List.replicate (nearyExtra N q).length symLE) =
      nearyExtra N q ++ midArrow ++ List.replicate (nearyExtra N q).length symLE := by
    simp [midArrow, List.replicate, List.append_assoc]
  rw [hr1Align] at hr1
  obtain ⟨s2, _, hr2⟩ := cycle2_and_cycle3 (untouchedLeft N k0) (nearyExtra N q) midArrow
    (symLA :: encodeRightTape nextRight) (nearyExtra_all_etrSym N q) hmidArrow
  have hmidRestore : untouchedLeft N k0 ++ [symLAMBDA] ++ nearyExtra N q ++ midArrow.map restoreSym ++ [symLH] =
      (tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit)) ++ [symE, symLH] := by
    have hrestTbl := restored_table_eq_full N k0 hk0
    rw [hblk0] at hrestTbl
    have hmr : midArrow.map restoreSym =
        (neutralizedRight N k0).map restoreSym ++ [symLAMBDA] ++
          (symE :: leftBits.flatMap encLeftCleanBit) ++ [symE] := by
      simp only [midArrow, List.map_append, encLeftArrow_restore]
      rfl
    rw [hmr]
    have hassoc1 : untouchedLeft N k0 ++ [symLAMBDA] ++ nearyExtra N q ++
          ((neutralizedRight N k0).map restoreSym ++ [symLAMBDA] ++
            (symE :: leftBits.flatMap encLeftCleanBit) ++ [symE]) ++ [symLH] =
        (untouchedLeft N k0 ++ [symLAMBDA] ++ nearyExtra N q ++ (neutralizedRight N k0).map restoreSym) ++
          [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit) ++ [symE, symLH] := by
      simp [List.append_assoc]
    rw [hassoc1, hrestTbl]
  rw [hmidRestore, hextraMap] at hr2
  have hr3 := cycle4_three_steps_on_E
    (tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit))
    (List.replicate (5 * (S - q.val) - 4) symLA ++ List.replicate (4 + 5 * q.val) symLB ++
      symLA :: encodeRightTape nextRight)
  have hr2Align : symLA :: (List.replicate (5 * (S - q.val) - 4) symLA ++ List.replicate (4 + 5 * q.val) symLB) ++
        symLA :: encodeRightTape nextRight =
      symLA :: (List.replicate (5 * (S - q.val) - 4) symLA ++ List.replicate (4 + 5 * q.val) symLB ++
        symLA :: encodeRightTape nextRight) := by
    simp [List.append_assoc]
  rw [hr2Align] at hr2
  let k2 := 5 * q.val + 2
  have hk2 : k2 < 5 * S := by omega
  let mid2 := (symE :: leftBits.flatMap encLeftCleanBit) ++ [symE]
  have hmid2Body : ∀ s ∈ mid2, IsBodySym s := by
    intro s hs
    rw [List.mem_append, List.mem_singleton] at hs
    rcases hs with hl | rfl
    · exact encLeftClean_all_body leftBits s hl
    · exact Or.inl rfl
  have hmid2Map : mid2.map toArrowL =
      (symLE :: leftBits.flatMap encLeftArrowBit) ++ List.replicate 1 symLE := by
    change ((symE :: leftBits.flatMap encLeftCleanBit) ++ [symE]).map toArrowL = _
    rw [List.map_append, encLeftClean_toArrowL]
    rfl
  obtain ⟨s4, _, hr4⟩ := cycle1_from_tableFull N k2 hk2 mid2
    (symLE :: leftBits.flatMap encLeftArrowBit) 1 (5 * (S - q.val) - 2)
    (encodeRightTape nextRight) hmid2Body hmid2Map
  have hr3EndL : (tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit)) ++ [symE] =
      tableFull N ++ [symLAMBDA] ++ mid2 := by
    simp [mid2, List.append_assoc]
  have hr3EndR : symLA :: symLA :: (List.replicate (5 * (S - q.val) - 4) symLA ++
        List.replicate (4 + 5 * q.val) symLB ++ symLA :: encodeRightTape nextRight) =
      List.replicate (5 * (S - q.val) - 2) symLA ++ List.replicate (k2 + 2) symLB ++
        symLA :: encodeRightTape nextRight := by
    have ha2 : 5 * (S - q.val) - 2 = 2 + (5 * (S - q.val) - 4) := by omega
    have hb2 : 4 + 5 * q.val = k2 + 2 := by dsimp [k2]; omega
    rw [ha2, replicate_add_split 2, hb2]
    simp [List.replicate, List.append_assoc]
  rw [hr3EndL, hr3EndR] at hr3
  have hendLE : 1 + (5 * (S - q.val) - 2 + k2 + 2) = 5 * S + 3 := by
    dsimp [k2, S]; omega
  rw [hendLE] at hr4
  have htot := uRun_trans (uRun_trans (uRun_trans hr1 hr2) hr3) hr4
  exact ⟨s1 + s2 + 3 + s4, by omega, htot⟩

/-! ## Section 5: Lemma 3.4.4 (`init_to_postIndex`), Lemma 3.4.5 (`postIndex_step`), Lemma 3.4.3 (`postIndex_halt`) -/

theorem init_to_postIndex (N : NormalizedTM) (word : List Bool) :
    ∃ m u1, m ≥ 1 ∧ URun m (encodeNormalizedToU N word) u1 ∧
      PostIndexInv N (initNormConfig N word) u1 := by
  let S := N.numStates
  have hge := N.hge2
  let b0 := bitAt word 0
  let restBits := word.drop 1
  let uStart := uAt (tableFull N ++ [symLAMBDA] ++ [symE])
    (List.replicate (5 * S) symLA ++ [symLB, symLB] ++ encodeRightBit b0 ++ encodeRightTape restBits)
    stateU1
  have heqInit : UConfigEq uStart (encodeNormalizedToU N word) := by
    have h5S : 5 * S = 1 + (5 * S - 1) := by omega
    have huStart : uStart =
        ⟨(nearyPrefix N).reverse, symLA,
         List.replicate (5 * S - 1) symLA ++ [symLB, symLB] ++
           (encodeRightBit b0 ++ encodeRightTape restBits), stateU1⟩ := by
      dsimp [uStart, nearyPrefix, tableFull]
      conv => lhs; arg 2; arg 1; arg 1; arg 1; rw [h5S]
      rw [replicate_add_split 1]
      simp [uAt, List.append_assoc]
    rw [huStart]
    refine ⟨rfl, rfl, rfl, ?_⟩
    unfold encodeNormalizedToU
    dsimp only []
    have hpad := uRightEq_symm (uRightEq_encodeRightTape_unfold word)
    have hpre : ∀ (xs : List (Fin 11)), URightEq (xs ++ (encodeRightBit b0 ++ encodeRightTape restBits))
        (xs ++ encodeRightTape word) := by
      intro xs
      induction xs with
      | nil => exact hpad
      | cons x xs' ih => exact uRightEq_cons x ih
    simpa [List.append_assoc] using hpre (List.replicate (5 * S - 1) symLA ++ [symLB, symLB])
  have hmidBody : ∀ s ∈ ([symE] : List (Fin 11)), IsBodySym s := by
    intro s hs; rw [List.mem_singleton] at hs; subst hs; exact Or.inl rfl
  have hbitRight : ∀ j, bitAt restBits j = bitAt word (0 + 1 + j) := by
    intro j
    have hj : 0 + 1 + j = j + 1 := by omega
    rw [hj]
    cases word with
    | nil => simp [restBits, bitAt_nil]
    | cons x xs => rfl
  let q0 : Fin N.numStates := ⟨0, by omega⟩
  cases hb0 : b0 with
  | true =>
    have hk1 : 1 < 5 * S := by omega
    have hmidMap : ([symE] : List (Fin 11)).map toArrowL =
        (symLE :: ([] : List Bool).flatMap encLeftArrowBit) ++ List.replicate 0 symLE := rfl
    obtain ⟨st, hst, hrun⟩ := cycle1_from_tableFull N 1 hk1 [symE]
      (symLE :: ([] : List Bool).flatMap encLeftArrowBit) 0 (5 * S)
      (encodeRightTape restBits) hmidBody hmidMap
    have hstartAlign : List.replicate (5 * S) symLA ++ List.replicate (1 + 2) symLB ++
          symLA :: encodeRightTape restBits =
        List.replicate (5 * S) symLA ++ [symLB, symLB] ++
          encodeRightBit true ++ encodeRightTape restBits := by
      simp [List.replicate, encodeRightBit, List.append_assoc]
    rw [hstartAlign, ← hb0] at hrun
    have hlenAlign : 0 + (5 * S + 1 + 2) = 5 * S + 3 := by omega
    rw [hlenAlign] at hrun
    obtain ⟨u1, hrunInit, heq1⟩ := uRun_equiv_forward hrun (encodeNormalizedToU N word) heqInit
    refine ⟨st, u1, hst, hrunInit, ⟨1, restBits, hk1, ?_, hbitRight, heq1⟩⟩
    have h1Eq : (1 : Nat) = 5 * q0.val + 1 := rfl
    rw [h1Eq, block_getD_eq N q0 1 (by decide)]
    unfold initNormConfig nearyStateBlocksR2L
    dsimp only [q0]
    have hb0' : bitAt word 0 = true := hb0
    rw [hb0']
    rfl
  | false =>
    have hmidMap : ([symE] : List (Fin 11)).map toArrowL =
        symLE :: ([] : List Bool).flatMap encLeftArrowBit := rfl
    obtain ⟨st, hst, hrun⟩ := execute_case_D N q0 (Or.inl rfl) [symE] [] restBits hmidBody hmidMap
    have hstartAlign : List.replicate (5 * (N.numStates - q0.val)) symLA ++
          List.replicate (5 * q0.val + 2) symLB ++
          encodeRightBit false ++ encodeRightTape restBits =
        List.replicate (5 * S) symLA ++ [symLB, symLB] ++
          encodeRightBit b0 ++ encodeRightTape restBits := by
      rw [hb0]; simp [q0, S, List.replicate, List.append_assoc]
    rw [hstartAlign] at hrun
    obtain ⟨u1, hrunInit, heq1⟩ := uRun_equiv_forward hrun (encodeNormalizedToU N word) heqInit
    have hk2 : 2 < 5 * S := by omega
    refine ⟨st, u1, hst, hrunInit, ⟨2, restBits, hk2, ?_, hbitRight, heq1⟩⟩
    have h2Eq : (2 : Nat) = 5 * q0.val + 2 := rfl
    rw [h2Eq, block_getD_eq N q0 2 (by decide)]
    unfold initNormConfig nearyStateBlocksR2L
    dsimp only [q0]
    have hb0' : bitAt word 0 = false := hb0
    rw [hb0']
    rfl

theorem postIndex_step (N : NormalizedTM)
    {nc nc' : NormConfig N.numStates} {u : UConfig}
    (hinv : PostIndexInv N nc u)
    (hstep : normStepSafe N nc = some nc') :
    ∃ m u', m ≥ 1 ∧ URun m u u' ∧ PostIndexInv N nc' u' := by
  obtain ⟨k, rightBits, hk, hblkEq, hrightBits, huEq⟩ := hinv
  have hge := N.hge2
  let act := N.rule nc.state (bitAt nc.tape nc.head)
  let y := act.next
  have hy := y.isLt
  cases hdir : act.dir with
  | right =>
    have hnc' : nc' = ⟨y, nc.head + 1, writeTapeList nc.tape nc.head act.write⟩ := by
      unfold normStepSafe at hstep
      change (match act.dir with
        | .left => if nc.head = 0 then none else some ⟨y, nc.head - 1, writeTapeList nc.tape nc.head act.write⟩
        | .right => some ⟨y, nc.head + 1, writeTapeList nc.tape nc.head act.write⟩) = some nc' at hstep
      rw [hdir] at hstep
      injection hstep with h; exact h.symm
    let nextBit := bitAt rightBits 0
    let nextRight := rightBits.drop 1
    let bodyList := (nearyBlocksR2L N).getD k [] ++ neutralizedRight N k ++ [symDELTA] ++
      (symLE :: (leftBitsOf nc.tape nc.head).flatMap encLeftArrowBit) ++
      List.replicate (5 * N.numStates + 3) symLE
    let uPad := uAtRightmost (untouchedLeft N k) symLAMBDA bodyList
      (symGAMMA :: (encodeRightBit nextBit ++ encodeRightTape nextRight)) stateU2
    have heqPad : UConfigEq uPad u := by
      have hp := uConfigEq_uAtRightmost_right (untouchedLeft N k) symLAMBDA bodyList
        (symGAMMA :: (encodeRightBit nextBit ++ encodeRightTape nextRight))
        (symGAMMA :: encodeRightTape rightBits) stateU2
        (uRightEq_cons symGAMMA (uRightEq_symm (uRightEq_encodeRightTape_unfold rightBits)))
      exact uConfigEq_trans hp huEq
    let leftBits := leftBitsOf nc.tape nc.head
    have hleftBits' : leftBitsOf nc'.tape nc'.head = leftBits ++ [act.write] := by
      rw [hnc']; dsimp only []
      rw [leftBitsOf_succ, leftBitsOf_write_ge nc.tape nc.head nc.head act.write (Nat.le_refl _),
          bitAt_writeTapeList, if_pos rfl]
    have hnextBit_eq : bitAt nc'.tape nc'.head = nextBit := by
      rw [hnc']; dsimp only []
      rw [bitAt_writeTapeList, if_neg (by omega), ← hrightBits 0]
    have hnextRight_bits : ∀ j, bitAt nextRight j = bitAt nc'.tape (nc'.head + 1 + j) := by
      intro j
      rw [hnc']; dsimp only []
      rw [bitAt_writeTapeList, if_neg (by omega)]
      have h1 : nc.head + 1 + 1 + j = nc.head + 1 + (j + 1) := by omega
      rw [h1, ← hrightBits (j + 1)]
      cases rightBits with
      | nil => simp [nextRight, bitAt_nil]
      | cons _ _ => rfl
    have hafterC4 : ∃ stC4 midAfter, stC4 ≥ 1 ∧
        (∀ s ∈ midAfter, IsBodySym s) ∧
        midAfter.map toArrowL = symLE :: (leftBits ++ [act.write]).flatMap encLeftArrowBit ∧
        URun stC4 uPad
          (uAt (tableFull N ++ [symLAMBDA] ++ midAfter)
            (List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
              encodeRightBit nextBit ++ encodeRightTape nextRight) stateU1) := by
      cases hw : act.write with
      | false =>
        have hactEq : act = ⟨false, .right, y⟩ := by
          cases hact : act with
          | mk w0 d0 n0 =>
            have hw0 : w0 = false := by rw [hact] at hw; exact hw
            have hd0 : d0 = .right := by rw [hact] at hdir; exact hdir
            have hn0 : n0 = y := by dsimp [y]; rw [hact]
            subst hw0; subst hd0; subst hn0; rfl
        obtain ⟨hlenETR, _, _, _, hmapETR⟩ := nearyETR_right_false_props N.numStates hge y
        rw [← hactEq] at hlenETR hmapETR
        let midArr := neutralizedRight N k ++ [symDELTA] ++
          (symLE :: leftBits.flatMap encLeftArrowBit) ++ [symLE]
        have hmidArr : ∀ s ∈ midArr, IsArrowSym s := by
          intro s hs
          simp only [midArr, List.mem_append, List.mem_singleton] at hs
          rcases hs with ((hn | rfl) | hl) | rfl
          · exact neutralizedRight_all_arrow N k s hn
          · exact Or.inr (Or.inr rfl)
          · exact encLeftArrow_all_arrow leftBits s hl
          · exact Or.inl rfl
        have huPadEq : uPad = uAtRightmost (untouchedLeft N k) symLAMBDA
            (nearyETR N.numStates act ++ midArr ++ List.replicate (nearyETR N.numStates act).length symLE)
            (symGAMMA :: (encodeRightBit nextBit ++ encodeRightTape nextRight)) stateU2 := by
          dsimp [uPad, bodyList, midArr, leftBits, act]
          rw [hblkEq]
          have hrep : List.replicate (5 * N.numStates + 3) symLE =
              [symLE] ++ List.replicate (nearyETR N.numStates act).length symLE := by
            rw [hlenETR]; have h1 : 5 * N.numStates + 3 = 1 + (5 * N.numStates + 2) := by omega
            rw [h1, replicate_add_split 1]; rfl
          dsimp [act] at hrep
          rw [hrep]
          simp [List.append_assoc]
        obtain ⟨sc23, _, hrc23⟩ := cycle2_and_cycle3 (untouchedLeft N k) (nearyETR N.numStates act) midArr
          (encodeRightBit nextBit ++ encodeRightTape nextRight) (nearyETR_all_etrSym N.numStates act) hmidArr
        rw [← huPadEq, hmapETR] at hrc23
        have hrestL : untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++ midArr.map restoreSym ++ [symLH] =
            (tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit)) ++ [symE, symLH] := by
          have hrt := restored_table_eq_full N k hk
          rw [hblkEq] at hrt
          have hmr : midArr.map restoreSym =
              (neutralizedRight N k).map restoreSym ++ [symLAMBDA] ++
                (symE :: leftBits.flatMap encLeftCleanBit) ++ [symE] := by
            simp only [midArr, List.map_append, encLeftArrow_restore]; rfl
          rw [hmr]
          have ha : untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++
                ((neutralizedRight N k).map restoreSym ++ [symLAMBDA] ++
                  (symE :: leftBits.flatMap encLeftCleanBit) ++ [symE]) ++ [symLH] =
              (untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++ (neutralizedRight N k).map restoreSym) ++
                [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit) ++ [symE, symLH] := by
            simp [List.append_assoc]
          rw [ha]
          dsimp [act]
          rw [hrt]
        rw [hrestL] at hrc23
        have hrc4 := cycle4_right_write_false
          (tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit))
          (List.replicate (5 * (N.numStates - y.val) - 1) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
            (encodeRightBit nextBit ++ encodeRightTape nextRight))
        have hrAlign : symLA :: (List.replicate (5 * (N.numStates - y.val) - 1) symLA ++ List.replicate (2 + 5 * y.val) symLB) ++
              (encodeRightBit nextBit ++ encodeRightTape nextRight) =
            symLA :: (List.replicate (5 * (N.numStates - y.val) - 1) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
              (encodeRightBit nextBit ++ encodeRightTape nextRight)) := by
          simp [List.append_assoc]
        rw [hrAlign] at hrc23
        let midAfter := (symE :: leftBits.flatMap encLeftCleanBit) ++ [symE, symLE]
        have hmidAfterBody : ∀ s ∈ midAfter, IsBodySym s := by
          intro s hs
          dsimp only [midAfter] at hs
          rw [List.mem_append] at hs
          rcases hs with hl | hr2
          · exact encLeftClean_all_body leftBits s hl
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
            rcases hr2 with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl rfl))
        have hmidAfterMap : midAfter.map toArrowL =
            symLE :: (leftBits ++ [false]).flatMap encLeftArrowBit := by
          simp only [midAfter, List.map_append, encLeftClean_toArrowL, List.flatMap_append]
          rfl
        have hc4End : uAt ((tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit)) ++ [symE, symLE])
              (symLA :: (List.replicate (5 * (N.numStates - y.val) - 1) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
                (encodeRightBit nextBit ++ encodeRightTape nextRight))) stateU1 =
            uAt (tableFull N ++ [symLAMBDA] ++ midAfter)
              (List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
                encodeRightBit nextBit ++ encodeRightTape nextRight) stateU1 := by
          have ha1 : 5 * (N.numStates - y.val) = 1 + (5 * (N.numStates - y.val) - 1) := by omega
          conv => rhs; arg 2; arg 1; arg 1; arg 1; rw [ha1]
          rw [replicate_add_split 1]
          simp [midAfter, List.replicate, List.append_assoc]
        rw [hc4End] at hrc4
        exact ⟨sc23 + 4, midAfter, by omega, hmidAfterBody, hmidAfterMap, uRun_trans hrc23 hrc4⟩
      | true =>
        have hactEq : act = ⟨true, .right, y⟩ := by
          cases hact : act with
          | mk w0 d0 n0 =>
            have hw0 : w0 = true := by rw [hact] at hw; exact hw
            have hd0 : d0 = .right := by rw [hact] at hdir; exact hdir
            have hn0 : n0 = y := by dsimp [y]; rw [hact]
            subst hw0; subst hd0; subst hn0; rfl
        obtain ⟨hlenETR, _, _, hmapETR⟩ := nearyETR_right_true_props N.numStates hge y
        rw [← hactEq] at hlenETR hmapETR
        let midArr := neutralizedRight N k ++ [symDELTA] ++ (symLE :: leftBits.flatMap encLeftArrowBit)
        have hmidArr : ∀ s ∈ midArr, IsArrowSym s := by
          intro s hs
          simp only [midArr, List.mem_append, List.mem_singleton] at hs
          rcases hs with (hn | rfl) | hl
          · exact neutralizedRight_all_arrow N k s hn
          · exact Or.inr (Or.inr rfl)
          · exact encLeftArrow_all_arrow leftBits s hl
        have huPadEq : uPad = uAtRightmost (untouchedLeft N k) symLAMBDA
            (nearyETR N.numStates act ++ midArr ++ List.replicate (nearyETR N.numStates act).length symLE)
            (symGAMMA :: (encodeRightBit nextBit ++ encodeRightTape nextRight)) stateU2 := by
          dsimp [uPad, bodyList, midArr, leftBits, act]
          rw [hblkEq]
          dsimp [act] at hlenETR
          rw [hlenETR]
          simp [List.append_assoc]
        obtain ⟨sc23, _, hrc23⟩ := cycle2_and_cycle3 (untouchedLeft N k) (nearyETR N.numStates act) midArr
          (encodeRightBit nextBit ++ encodeRightTape nextRight) (nearyETR_all_etrSym N.numStates act) hmidArr
        rw [← huPadEq, hmapETR] at hrc23
        have hrestL : untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++ midArr.map restoreSym ++ [symLH] =
            (tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit)) ++ [symLH] := by
          have hrt := restored_table_eq_full N k hk
          rw [hblkEq] at hrt
          have hmr : midArr.map restoreSym =
              (neutralizedRight N k).map restoreSym ++ [symLAMBDA] ++
                (symE :: leftBits.flatMap encLeftCleanBit) := by
            simp only [midArr, List.map_append, encLeftArrow_restore]; rfl
          rw [hmr]
          have ha : untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++
                ((neutralizedRight N k).map restoreSym ++ [symLAMBDA] ++
                  (symE :: leftBits.flatMap encLeftCleanBit)) ++ [symLH] =
              (untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++ (neutralizedRight N k).map restoreSym) ++
                [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit) ++ [symLH] := by
            simp [List.append_assoc]
          rw [ha]
          dsimp [act]
          rw [hrt]
        rw [hrestL] at hrc23
        have hrc4 := cycle4_right_write_true
          (tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit))
          (List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
            (encodeRightBit nextBit ++ encodeRightTape nextRight))
        have hrAlign : symLB :: (List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (2 + 5 * y.val) symLB) ++
              (encodeRightBit nextBit ++ encodeRightTape nextRight) =
            symLB :: (List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
              (encodeRightBit nextBit ++ encodeRightTape nextRight)) := by
          simp [List.append_assoc]
        rw [hrAlign] at hrc23
        let midAfter := (symE :: leftBits.flatMap encLeftCleanBit) ++ [symLH, symE]
        have hmidAfterBody : ∀ s ∈ midAfter, IsBodySym s := by
          intro s hs
          dsimp only [midAfter] at hs
          rw [List.mem_append] at hs
          rcases hs with hl | hr2
          · exact encLeftClean_all_body leftBits s hl
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
            rcases hr2 with rfl | rfl
            · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · exact Or.inl rfl
        have hmidAfterMap : midAfter.map toArrowL =
            symLE :: (leftBits ++ [true]).flatMap encLeftArrowBit := by
          simp only [midAfter, List.map_append, encLeftClean_toArrowL, List.flatMap_append]
          rfl
        have hc4End : uAt ((tableFull N ++ [symLAMBDA] ++ (symE :: leftBits.flatMap encLeftCleanBit)) ++ [symLH, symE])
              (List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
                (encodeRightBit nextBit ++ encodeRightTape nextRight)) stateU1 =
            uAt (tableFull N ++ [symLAMBDA] ++ midAfter)
              (List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
                encodeRightBit nextBit ++ encodeRightTape nextRight) stateU1 := by
          simp [midAfter, List.append_assoc]
        rw [hc4End] at hrc4
        exact ⟨sc23 + 1, midAfter, by omega, hmidAfterBody, hmidAfterMap, uRun_trans hrc23 hrc4⟩
    obtain ⟨stC4, midAfter, hstC4, hmidBody, hmidMap, hrunC4⟩ := hafterC4
    cases hnb : nextBit with
    | true =>
      let kNext := 5 * y.val + 1
      have hkNext : kNext < 5 * N.numStates := by omega
      have hmidMap0 : midAfter.map toArrowL =
          (symLE :: (leftBits ++ [act.write]).flatMap encLeftArrowBit) ++ List.replicate 0 symLE := by
        rw [hmidMap]; simp
      obtain ⟨stC1, _, hrunC1⟩ := cycle1_from_tableFull N kNext hkNext midAfter
        (symLE :: (leftBits ++ [act.write]).flatMap encLeftArrowBit) 0 (5 * (N.numStates - y.val))
        (encodeRightTape nextRight) hmidBody hmidMap0
      have hnbAlign : List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (kNext + 2) symLB ++
            symLA :: encodeRightTape nextRight =
          List.replicate (5 * (N.numStates - y.val)) symLA ++ List.replicate (2 + 5 * y.val) symLB ++
            encodeRightBit true ++ encodeRightTape nextRight := by
        have hbEq : kNext + 2 = (2 + 5 * y.val) + 1 := by dsimp [kNext]; omega
        rw [hbEq, replicate_add_split (2 + 5 * y.val) 1 symLB]
        simp [encodeRightBit, List.replicate, List.append_assoc]
      rw [hnbAlign, ← hnb] at hrunC1
      have hlenNext : 0 + (5 * (N.numStates - y.val) + kNext + 2) = 5 * N.numStates + 3 := by dsimp [kNext]; omega
      rw [hlenNext] at hrunC1
      have htotPad := uRun_trans hrunC4 hrunC1
      obtain ⟨u', hrunU, heqU'⟩ := uRun_equiv_forward htotPad u heqPad
      refine ⟨stC4 + stC1, u', by omega, hrunU, ⟨kNext, nextRight, hkNext, ?_, hnextRight_bits, ?_⟩⟩
      · dsimp [kNext]
        rw [block_getD_eq N y 1 (by decide), hnextBit_eq, hnb]
        rw [hnc']; rfl
      · rwa [hleftBits']
    | false =>
      have hinc : hasIncomingRight N y = true :=
        hasIncomingRight_of_witness N nc.state y (bitAt nc.tape nc.head) rfl hdir
      obtain ⟨stD, _, hrunD⟩ := execute_case_D N y (Or.inr hinc) midAfter
        (leftBits ++ [act.write]) nextRight hmidBody hmidMap
      have hbComm : 5 * y.val + 2 = 2 + 5 * y.val := by omega
      have hstartEq : List.replicate (5 * (N.numStates - y.val)) symLA ++
            List.replicate (5 * y.val + 2) symLB ++
            encodeRightBit false ++ encodeRightTape nextRight =
          List.replicate (5 * (N.numStates - y.val)) symLA ++
            List.replicate (2 + 5 * y.val) symLB ++
            encodeRightBit nextBit ++ encodeRightTape nextRight := by
        rw [hbComm, hnb]
      rw [hstartEq] at hrunD
      have htotPad := uRun_trans hrunC4 hrunD
      obtain ⟨u', hrunU, heqU'⟩ := uRun_equiv_forward htotPad u heqPad
      let kNext := 5 * y.val + 2
      have hkNext : kNext < 5 * N.numStates := by omega
      refine ⟨stC4 + stD, u', by omega, hrunU, ⟨kNext, nextRight, hkNext, ?_, hnextRight_bits, ?_⟩⟩
      · dsimp [kNext]
        rw [block_getD_eq N y 2 (by decide), hnextBit_eq, hnb]
        rw [hnc']; rfl
      · rw [hleftBits']; exact heqU'
  | left =>
    have hhead_ne0 : nc.head ≠ 0 := by
      intro hh0
      unfold normStepSafe at hstep
      change (match act.dir with
        | .left => if nc.head = 0 then none else some ⟨y, nc.head - 1, writeTapeList nc.tape nc.head act.write⟩
        | .right => some ⟨y, nc.head + 1, writeTapeList nc.tape nc.head act.write⟩) = some nc' at hstep
      rw [hdir, if_pos hh0] at hstep
      cases hstep
    have hnc' : nc' = ⟨y, nc.head - 1, writeTapeList nc.tape nc.head act.write⟩ := by
      unfold normStepSafe at hstep
      change (match act.dir with
        | .left => if nc.head = 0 then none else some ⟨y, nc.head - 1, writeTapeList nc.tape nc.head act.write⟩
        | .right => some ⟨y, nc.head + 1, writeTapeList nc.tape nc.head act.write⟩) = some nc' at hstep
      rw [hdir, if_neg hhead_ne0] at hstep
      injection hstep with h; exact h.symm
    let p := nc.head - 1
    have hp_succ : nc.head = p + 1 := by omega
    let leftInit := leftBitsOf nc.tape p
    let prevBit := bitAt nc.tape p
    have hleftSplit : leftBitsOf nc.tape nc.head = leftInit ++ [prevBit] := by
      rw [hp_succ]; exact leftBitsOf_succ nc.tape p
    have hleftBits' : leftBitsOf nc'.tape nc'.head = leftInit := by
      rw [hnc']; dsimp only []
      change leftBitsOf (writeTapeList nc.tape nc.head act.write) p = leftInit
      exact leftBitsOf_write_ge nc.tape nc.head p act.write (by omega)
    have hprevBit_eq : bitAt nc'.tape nc'.head = prevBit := by
      rw [hnc']; dsimp only []
      change bitAt (writeTapeList nc.tape nc.head act.write) p = prevBit
      rw [bitAt_writeTapeList, if_neg (by omega)]
    let newRightBits := act.write :: rightBits
    have hnewRight_bits : ∀ j, bitAt newRightBits j = bitAt nc'.tape (nc'.head + 1 + j) := by
      intro j
      rw [hnc']; dsimp only []
      cases j with
      | zero =>
        have h1 : nc.head - 1 + 1 + 0 = nc.head := by omega
        rw [h1, bitAt_writeTapeList, if_pos rfl]
        rfl
      | succ j' =>
        have h1 : nc.head - 1 + 1 + (j' + 1) = nc.head + 1 + j' := by omega
        rw [h1, bitAt_writeTapeList, if_neg (by omega)]
        exact hrightBits j'
    have hactEq : act = ⟨act.write, .left, y⟩ := by
      change act.dir = .left at hdir
      cases hact : act with
      | mk w0 d0 n0 =>
        have hd0 : d0 = .left := by rw [hact] at hdir; exact hdir
        have hn0 : n0 = y := by dsimp [y]; rw [hact]
        subst hd0; subst hn0; rfl
    obtain ⟨hlenETR, _, _, _, hmapETR⟩ := nearyETR_left_props N.numStates hge act.write y
    rw [← hactEq] at hlenETR hmapETR
    let midArr := neutralizedRight N k ++ [symDELTA] ++
      (symLE :: leftInit.flatMap encLeftArrowBit) ++ [if prevBit then symLH else symLE]
    have hmidArr : ∀ s ∈ midArr, IsArrowSym s := by
      intro s hs
      simp only [midArr, List.mem_append, List.mem_singleton] at hs
      rcases hs with ((hn | rfl) | hl) | hpv
      · exact neutralizedRight_all_arrow N k s hn
      · exact Or.inr (Or.inr rfl)
      · exact encLeftArrow_all_arrow leftInit s hl
      · cases hp : prevBit with
        | false => rw [hp] at hpv; subst hpv; exact Or.inl rfl
        | true => rw [hp] at hpv; subst hpv; exact Or.inr (Or.inl rfl)
    have hconcEq : postIndexConcrete N k (leftBitsOf nc.tape nc.head) rightBits =
        uAtRightmost (untouchedLeft N k) symLAMBDA
          (nearyETR N.numStates act ++ midArr ++ List.replicate (nearyETR N.numStates act).length symLE)
          (symGAMMA :: encodeRightTape rightBits) stateU2 := by
      unfold postIndexConcrete
      rw [hblkEq, hleftSplit, List.flatMap_append]
      have penc : [prevBit].flatMap encLeftArrowBit = [if prevBit then symLH else symLE, symLE] := rfl
      have hrep : [symLE] ++ List.replicate (5 * N.numStates + 3) symLE =
          List.replicate (nearyETR N.numStates (N.rule nc.state (bitAt nc.tape nc.head))).length symLE := by
        change [symLE] ++ List.replicate (5 * N.numStates + 3) symLE =
          List.replicate (nearyETR N.numStates act).length symLE
        rw [hlenETR]; have h4 : 5 * N.numStates + 4 = 1 + (5 * N.numStates + 3) := by omega
        rw [h4, replicate_add_split 1]; rfl
      rw [penc]
      have hassoc : nearyETR N.numStates (N.rule nc.state (bitAt nc.tape nc.head)) ++
            neutralizedRight N k ++ [symDELTA] ++
            (symLE :: (leftInit.flatMap encLeftArrowBit ++ [if prevBit then symLH else symLE, symLE])) ++
            List.replicate (5 * N.numStates + 3) symLE =
          nearyETR N.numStates (N.rule nc.state (bitAt nc.tape nc.head)) ++ midArr ++
            ([symLE] ++ List.replicate (5 * N.numStates + 3) symLE) := by
        simp [midArr, List.append_assoc]
      rw [hassoc, hrep]
    obtain ⟨sc23, _, hrc23⟩ := cycle2_and_cycle3 (untouchedLeft N k) (nearyETR N.numStates act) midArr
      (encodeRightTape rightBits) (nearyETR_all_etrSym N.numStates act) hmidArr
    rw [← hconcEq, hmapETR] at hrc23
    have hrestL : untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++ midArr.map restoreSym ++ [symLH] =
        tableFull N ++ [symLAMBDA] ++ (symE :: leftInit.flatMap encLeftCleanBit) ++
          [if prevBit then symH else symE, symLH] := by
      have hrt := restored_table_eq_full N k hk
      rw [hblkEq] at hrt
      have hpRest : restoreSym (if prevBit then symLH else symLE) = (if prevBit then symH else symE) := by
        cases prevBit <;> rfl
      have hmr : midArr.map restoreSym =
          (neutralizedRight N k).map restoreSym ++ [symLAMBDA] ++
            (symE :: leftInit.flatMap encLeftCleanBit) ++ [if prevBit then symH else symE] := by
        simp only [midArr, List.map_append, encLeftArrow_restore, List.map_singleton, hpRest]
        rfl
      rw [hmr]
      have ha : untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++
            ((neutralizedRight N k).map restoreSym ++ [symLAMBDA] ++
              (symE :: leftInit.flatMap encLeftCleanBit) ++ [if prevBit then symH else symE]) ++ [symLH] =
          (untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++ (neutralizedRight N k).map restoreSym) ++
            [symLAMBDA] ++ (symE :: leftInit.flatMap encLeftCleanBit) ++
            [if prevBit then symH else symE, symLH] := by
        simp [List.append_assoc]
      rw [ha]
      dsimp [act]
      rw [hrt]
    have hnewRightEnc : encodeRightBit act.write ++ encodeRightTape rightBits = encodeRightTape newRightBits := rfl
    have hrAlign : symLA :: (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
          List.replicate (5 + 5 * y.val) symLB ++ [symLA] ++ encodeRightBit act.write) ++
          encodeRightTape rightBits =
        symLA :: (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
          List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightTape newRightBits) := by
      rw [← hnewRightEnc]; simp [List.append_assoc]
    rw [hrestL, hrAlign] at hrc23
    cases hpv : prevBit with
    | false =>
      rw [hpv, if_neg Bool.false_ne_true] at hrc23
      have hrc4 := cycle4_three_steps_on_E
        (tableFull N ++ [symLAMBDA] ++ (symE :: leftInit.flatMap encLeftCleanBit))
        (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
          List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightTape newRightBits)
      have haL : tableFull N ++ [symLAMBDA] ++ (symE :: leftInit.flatMap encLeftCleanBit) ++ [symE, symLH] =
          (tableFull N ++ [symLAMBDA] ++ (symE :: leftInit.flatMap encLeftCleanBit)) ++ [symE, symLH] := by
        simp [List.append_assoc]
      rw [haL] at hrc23
      let kNext := 5 * y.val + 3
      have hkNext : kNext < 5 * N.numStates := by omega
      let midAfter := (symE :: leftInit.flatMap encLeftCleanBit) ++ [symE]
      have hmidBody : ∀ s ∈ midAfter, IsBodySym s := by
        intro s hs
        rw [List.mem_append, List.mem_singleton] at hs
        rcases hs with hl | rfl
        · exact encLeftClean_all_body leftInit s hl
        · exact Or.inl rfl
      have hmidMap : midAfter.map toArrowL =
          (symLE :: leftInit.flatMap encLeftArrowBit) ++ List.replicate 1 symLE := by
        change ((symE :: leftInit.flatMap encLeftCleanBit) ++ [symE]).map toArrowL = _
        rw [List.map_append, encLeftClean_toArrowL]; rfl
      obtain ⟨stC1, _, hrunC1⟩ := cycle1_from_tableFull N kNext hkNext midAfter
        (symLE :: leftInit.flatMap encLeftArrowBit) 1 (5 * (N.numStates - y.val) - 3)
        (encodeRightTape newRightBits) hmidBody hmidMap
      have hc4EndL : (tableFull N ++ [symLAMBDA] ++ (symE :: leftInit.flatMap encLeftCleanBit)) ++ [symE] =
          tableFull N ++ [symLAMBDA] ++ midAfter := by
        simp [midAfter, List.append_assoc]
      have hc4EndR : symLA :: symLA :: (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
            List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightTape newRightBits) =
          List.replicate (5 * (N.numStates - y.val) - 3) symLA ++ List.replicate (kNext + 2) symLB ++
            symLA :: encodeRightTape newRightBits := by
        have ha3 : 5 * (N.numStates - y.val) - 3 = 2 + (5 * (N.numStates - y.val) - 5) := by omega
        have hb3 : 5 + 5 * y.val = kNext + 2 := by dsimp [kNext]; omega
        rw [ha3, replicate_add_split 2, hb3]
        simp [List.replicate, List.append_assoc]
      rw [hc4EndL, hc4EndR] at hrc4
      have hlenNext : 1 + (5 * (N.numStates - y.val) - 3 + kNext + 2) = 5 * N.numStates + 3 := by dsimp [kNext]; omega
      rw [hlenNext] at hrunC1
      have htot := uRun_trans (uRun_trans hrc23 hrc4) hrunC1
      obtain ⟨u', hrunU, heqU'⟩ := uRun_equiv_forward htot u huEq
      refine ⟨sc23 + 3 + stC1, u', by omega, hrunU, ⟨kNext, newRightBits, hkNext, ?_, hnewRight_bits, ?_⟩⟩
      · dsimp [kNext]
        rw [block_getD_eq N y 3 (by decide), hprevBit_eq, hpv]
        rw [hnc']; rfl
      · rwa [hleftBits']
    | true =>
      rw [hpv, if_pos rfl] at hrc23
      have haL : tableFull N ++ [symLAMBDA] ++ (symE :: leftInit.flatMap encLeftCleanBit) ++ [symH, symLH] =
          tableFull N ++ [symLAMBDA] ++ (symE :: leftInit.flatMap encLeftCleanBit) ++ [symH, symLH] := rfl
      obtain ⟨sc4, _, hrc4⟩ := cycle4_left_read_true (tableFull N)
        (symE :: leftInit.flatMap encLeftCleanBit)
        (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
          List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightTape newRightBits)
        (encLeftClean_all_body leftInit)
      rw [encLeftClean_toArrowL] at hrc4
      let kNext := 5 * y.val + 4
      have hkNext : kNext < 5 * N.numStates := by omega
      have hkNextB : kNext < (nearyBlocksR2L N).length := by rw [nearyBlocksR2L_length]; exact hkNext
      have hb0Lt : 0 < (nearyBlocksR2L N).length := by rw [nearyBlocksR2L_length]; omega
      have htakeSplit : (nearyBlocksR2L N).take kNext =
          ((nearyBlocksR2L N)[0]'hb0Lt) :: ((nearyBlocksR2L N).take kNext).drop 1 := by
        cases htk : (nearyBlocksR2L N).take kNext with
        | nil =>
          have hlen0 := congrArg List.length htk
          rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hkNextB)] at hlen0
          dsimp [kNext] at hlen0; omega
        | cons x xs =>
          have h0 : ((nearyBlocksR2L N).take kNext)[0]? = some x := by rw [htk]; rfl
          have hget0 : ((nearyBlocksR2L N).take kNext)[0]? = some ((nearyBlocksR2L N)[0]'hb0Lt) := by
            have h1 := take_cons_drop (nearyBlocksR2L N) kNext hkNextB
            have hlenTk : 0 < ((nearyBlocksR2L N).take kNext).length := by
              rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hkNextB)]; dsimp [kNext]; omega
            have h2 : (nearyBlocksR2L N)[0]? = ((nearyBlocksR2L N).take kNext)[0]? := by
              conv => lhs; rw [h1]
              exact List.getElem?_append_left hlenTk
            rw [← h2, List.getElem?_eq_getElem hb0Lt]
          have hxeq : x = (nearyBlocksR2L N)[0]'hb0Lt := Option.some.inj (h0.symm.trans hget0)
          subst hxeq
          rfl
      let b0Blk := (nearyBlocksR2L N)[0]'hb0Lt
      let chunks' := ((nearyBlocksR2L N).take kNext).drop 1
      have hchunks'Len : chunks'.length = 5 * y.val + 3 := by
        dsimp [chunks', kNext]
        rw [List.length_drop, List.length_take, Nat.min_eq_left (Nat.le_of_lt hkNextB)]
        omega
      have hchunks'Body : ∀ c ∈ chunks', ∀ s ∈ c, IsBodySym s := by
        intro c hc
        have hcTk : c ∈ (nearyBlocksR2L N).take kNext := by
          rw [htakeSplit]; exact List.mem_cons_of_mem _ hc
        exact take_blocks_all_bodySym N kNext c hcTk
      let midAfter := b0Blk ++ [symDELTA] ++ (symLE :: leftInit.flatMap encLeftArrowBit)
      have hmidBody : ∀ s ∈ midAfter, IsBodySym s := by
        intro s hs
        dsimp only [midAfter] at hs
        rw [List.mem_append, List.mem_append, List.mem_singleton] at hs
        rcases hs with (hb0 | rfl) | hl
        · have hb0Mem : b0Blk ∈ (nearyBlocksR2L N).take kNext := by
            rw [htakeSplit]; exact List.mem_cons_self
          exact take_blocks_all_bodySym N kNext b0Blk hb0Mem s hb0
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        · exact isBody_of_isArrow (encLeftArrow_all_arrow leftInit s hl)
      let baseLeft := untouchedLeft N kNext ++ [symLAMBDA] ++ (nearyBlocksR2L N).getD kNext []
      obtain ⟨stC1, _, hrunC1⟩ := cycle1_full chunks' baseLeft midAfter
        (5 * (N.numStates - y.val) - 2) (encodeRightTape newRightBits) hchunks'Body hmidBody
      have hstartL : baseLeft ++ (chunks'.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ midAfter =
          tableFull N ++ [symDELTA] ++ (symLE :: leftInit.flatMap encLeftArrowBit) := by
        have hts := tableFull_split N kNext hkNext
        have htkRev : (((nearyBlocksR2L N).take kNext).reverse.flatMap fun c => symLAMBDA :: c) =
            (chunks'.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ b0Blk := by
          conv => lhs; arg 2; arg 1; rw [htakeSplit]
          simp [chunks', b0Blk, List.reverse_cons, List.flatMap_append, List.append_assoc]
        rw [hts, htkRev]
        simp [baseLeft, midAfter, List.append_assoc]
      have hstartR : List.replicate (5 * (N.numStates - y.val) - 2) symLA ++ List.replicate (chunks'.length + 2) symLB ++
            symLA :: encodeRightTape newRightBits =
          symLA :: symLA :: symLA :: (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
            List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightTape newRightBits) := by
        rw [hchunks'Len]
        have ha2 : 5 * (N.numStates - y.val) - 2 = 3 + (5 * (N.numStates - y.val) - 5) := by omega
        have hb2 : 5 * y.val + 3 + 2 = 5 + 5 * y.val := by omega
        rw [ha2, replicate_add_split 3, hb2]
        simp [List.replicate, List.append_assoc]
      rw [hstartL, hstartR] at hrunC1
      have hendEq : uAtRightmost (baseLeft ++ (chunks'.reverse.flatMap fun c => symDELTA :: c.map toArrowL))
            symDELTA (midAfter.map toArrowL ++ List.replicate (5 * (N.numStates - y.val) - 2 + chunks'.length + 2) symLE)
            (symGAMMA :: encodeRightTape newRightBits) stateU2 =
          postIndexConcrete N kNext leftInit newRightBits := by
        unfold postIndexConcrete
        rw [hchunks'Len]
        have hlenLE : 5 * (N.numStates - y.val) - 2 + (5 * y.val + 3) + 2 = 5 * N.numStates + 3 := by omega
        rw [hlenLE]
        have hmidMap : midAfter.map toArrowL =
            b0Blk.map toArrowL ++ [symDELTA] ++ (symLE :: leftInit.flatMap encLeftArrowBit) := by
          simp only [midAfter, List.map_append, List.map_singleton]
          have h1 : (symLE :: leftInit.flatMap encLeftArrowBit).map toArrowL =
              symLE :: leftInit.flatMap encLeftArrowBit :=
            (List.map_congr_left fun s hs =>
              toArrowL_of_isArrow (encLeftArrow_all_arrow leftInit s hs)).trans (List.map_id _)
          rw [h1]; rfl
        have hnrSplit : neutralizedRight N kNext =
            (chunks'.reverse.flatMap fun c => symDELTA :: c.map toArrowL) ++ ([symDELTA] ++ b0Blk.map toArrowL) := by
          unfold neutralizedRight
          rw [htakeSplit]
          simp [chunks', b0Blk, List.reverse_cons, List.flatMap_append]
        rw [hmidMap, hnrSplit]
        let pre1 := (nearyBlocksR2L N).getD kNext [] ++
          (chunks'.reverse.flatMap fun c => symDELTA :: c.map toArrowL)
        let tail1 := b0Blk.map toArrowL ++ [symDELTA] ++
          (symLE :: leftInit.flatMap encLeftArrowBit) ++ List.replicate (5 * N.numStates + 3) symLE
        have happ := uAtRightmost_append (untouchedLeft N kNext) symLAMBDA pre1 (symDELTA :: tail1)
          (symGAMMA :: encodeRightTape newRightBits) stateU2
        dsimp only [] at happ
        have hL : untouchedLeft N kNext ++ [symLAMBDA] ++ pre1 =
            baseLeft ++ (chunks'.reverse.flatMap fun c => symDELTA :: c.map toArrowL) := by
          simp [baseLeft, pre1, List.append_assoc]
        have hR : pre1 ++ (symDELTA :: tail1) =
            (nearyBlocksR2L N).getD kNext [] ++
              ((chunks'.reverse.flatMap fun c => symDELTA :: c.map toArrowL) ++ ([symDELTA] ++ b0Blk.map toArrowL)) ++
              [symDELTA] ++ (symLE :: leftInit.flatMap encLeftArrowBit) ++
              List.replicate (5 * N.numStates + 3) symLE := by
          simp [pre1, tail1, List.append_assoc]
        rw [← hL, ← hR]
        exact happ.symm
      rw [hendEq] at hrunC1
      have htot := uRun_trans (uRun_trans hrc23 hrc4) hrunC1
      obtain ⟨u', hrunU, heqU'⟩ := uRun_equiv_forward htot u huEq
      refine ⟨sc23 + sc4 + stC1, u', by omega, hrunU, ⟨kNext, newRightBits, hkNext, ?_, hnewRight_bits, ?_⟩⟩
      · dsimp [kNext]
        rw [block_getD_eq N y 4 (by decide), hprevBit_eq, hpv]
        rw [hnc']; rfl
      · rwa [hleftBits']

theorem postIndex_halt (N : NormalizedTM)
    {nc : NormConfig N.numStates} {u : UConfig}
    (hinv : PostIndexInv N nc u)
    (hstop : normStepSafe N nc = none) :
    let act := N.rule nc.state (bitAt nc.tape 0)
    let a := 5 * (N.numStates - act.next.val) - 3
    let b := 5 + 5 * act.next.val
    ∃ m uFinal, m ≥ 1 ∧ URun m u uFinal ∧ uNext uFinal = none ∧
      ∃ rightBits,
        (∀ j, bitAt rightBits j = bitAt nc.tape (1 + j)) ∧
        UConfigEq
          (uAt (tableFull N)
            (symDELTA :: (List.replicate a symLA ++ List.replicate b symLB ++
              symLA :: encodeRightBit act.write ++ encodeRightTape rightBits))
            stateU3)
          uFinal := by
  obtain ⟨hh0, hdir⟩ := (normStepSafe_none_iff N nc).mp hstop
  obtain ⟨k, rightBits, hk, hblkEq, hrightBits, huEq⟩ := hinv
  rw [hh0] at hblkEq hrightBits huEq hdir
  have hge := N.hge2
  let act := N.rule nc.state (bitAt nc.tape 0)
  let y := act.next
  have hy := y.isLt
  have hactEq : act = ⟨act.write, .left, y⟩ := by
    change act.dir = .left at hdir
    cases hact : act with
    | mk w0 d0 n0 =>
      have hd0 : d0 = .left := by rw [hact] at hdir; exact hdir
      have hn0 : n0 = y := by dsimp [y]; rw [hact]
      subst hd0; subst hn0; rfl
  obtain ⟨hlenETR, _, _, _, hmapETR⟩ := nearyETR_left_props N.numStates hge act.write y
  rw [← hactEq] at hlenETR hmapETR
  let midArr := neutralizedRight N k ++ [symDELTA]
  have hmidArr : ∀ s ∈ midArr, IsArrowSym s := by
    intro s hs
    rw [List.mem_append, List.mem_singleton] at hs
    rcases hs with hn | rfl
    · exact neutralizedRight_all_arrow N k s hn
    · exact Or.inr (Or.inr rfl)
  have hconcEq : postIndexConcrete N k (leftBitsOf nc.tape 0) rightBits =
      uAtRightmost (untouchedLeft N k) symLAMBDA
        (nearyETR N.numStates act ++ midArr ++ List.replicate (nearyETR N.numStates act).length symLE)
        (symGAMMA :: encodeRightTape rightBits) stateU2 := by
    unfold postIndexConcrete
    rw [hblkEq, leftBitsOf_zero]
    have hrep : [symLE] ++ List.replicate (5 * N.numStates + 3) symLE =
        List.replicate (nearyETR N.numStates (N.rule nc.state (bitAt nc.tape 0))).length symLE := by
      change [symLE] ++ List.replicate (5 * N.numStates + 3) symLE =
        List.replicate (nearyETR N.numStates act).length symLE
      rw [hlenETR]; have h4 : 5 * N.numStates + 4 = 1 + (5 * N.numStates + 3) := by omega
      rw [h4, replicate_add_split 1]; rfl
    have hassoc : nearyETR N.numStates (N.rule nc.state (bitAt nc.tape 0)) ++
          neutralizedRight N k ++ [symDELTA] ++ (symLE :: ([] : List Bool).flatMap encLeftArrowBit) ++
          List.replicate (5 * N.numStates + 3) symLE =
        nearyETR N.numStates (N.rule nc.state (bitAt nc.tape 0)) ++ midArr ++
          ([symLE] ++ List.replicate (5 * N.numStates + 3) symLE) := by
      simp [midArr, List.append_assoc]
    rw [hassoc, hrep]
  obtain ⟨sc23, _, hrc23⟩ := cycle2_and_cycle3 (untouchedLeft N k) (nearyETR N.numStates act) midArr
    (encodeRightTape rightBits) (nearyETR_all_etrSym N.numStates act) hmidArr
  rw [← hconcEq, hmapETR] at hrc23
  have hrestL : untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++ midArr.map restoreSym ++ [symLH] =
      tableFull N ++ [symLAMBDA, symLH] := by
    have hrt := restored_table_eq_full N k hk
    rw [hblkEq] at hrt
    have hmr : midArr.map restoreSym = (neutralizedRight N k).map restoreSym ++ [symLAMBDA] := by
      simp only [midArr, List.map_append]; rfl
    rw [hmr]
    have ha : untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++
          ((neutralizedRight N k).map restoreSym ++ [symLAMBDA]) ++ [symLH] =
        (untouchedLeft N k ++ [symLAMBDA] ++ nearyETR N.numStates act ++ (neutralizedRight N k).map restoreSym) ++
          [symLAMBDA, symLH] := by
      simp [List.append_assoc]
    rw [ha]
    dsimp [act]
    rw [hrt]
  have hrAlign : symLA :: (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
        List.replicate (5 + 5 * y.val) symLB ++ [symLA] ++ encodeRightBit act.write) ++
        encodeRightTape rightBits =
      symLA :: (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
        List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightBit act.write ++
        encodeRightTape rightBits) := by
    simp [List.append_assoc]
  rw [hrestL, hrAlign] at hrc23
  obtain ⟨hrc4, hnoneModel⟩ := cycle4_lemma_3_4_3_halt (tableFull N)
    (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
      List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightBit act.write ++
      encodeRightTape rightBits)
  have htot := uRun_trans hrc23 hrc4
  obtain ⟨uFinal, hrunU, heqFinal⟩ := uRun_equiv_forward htot u huEq
  have hnoneFinal := uNext_none_of_equiv heqFinal hnoneModel
  have ha3 : 5 * (N.numStates - y.val) - 3 = 2 + (5 * (N.numStates - y.val) - 5) := by omega
  have hmodelEq : uAt (tableFull N)
        (symDELTA :: symLA :: symLA :: (List.replicate (5 * (N.numStates - y.val) - 5) symLA ++
          List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightBit act.write ++
          encodeRightTape rightBits)) stateU3 =
      uAt (tableFull N)
        (symDELTA :: (List.replicate (5 * (N.numStates - y.val) - 3) symLA ++
          List.replicate (5 + 5 * y.val) symLB ++ symLA :: encodeRightBit act.write ++
          encodeRightTape rightBits)) stateU3 := by
    rw [ha3, replicate_add_split 2]
    simp [List.replicate, List.append_assoc]
  rw [hmodelEq] at heqFinal
  exact ⟨sc23 + 4, uFinal, by omega, hrunU, hnoneFinal,
         ⟨rightBits, fun j => by simpa using hrightBits j, heqFinal⟩⟩

theorem normRun_to_postIndex (N : NormalizedTM) (word : List Bool) :
    ∀ {s : Nat} {nc : NormConfig N.numStates},
      NormRun N s (initNormConfig N word) nc →
      ∃ uSteps u, uSteps ≥ s + 1 ∧ URun uSteps (encodeNormalizedToU N word) u ∧ PostIndexInv N nc u := by
  intro s nc hrun
  have hchain : ∀ {s : Nat} {c1 c2 : NormConfig N.numStates} {u1 : UConfig},
      NormRun N s c1 c2 → PostIndexInv N c1 u1 →
      ∃ m u2, m ≥ s ∧ URun m u1 u2 ∧ PostIndexInv N c2 u2 := by
    intro s
    induction s with
    | zero =>
      intro c1 c2 u1 hr hinv
      cases hr
      exact ⟨0, u1, Nat.le_refl 0, URun.zero u1, hinv⟩
    | succ k ih =>
      intro c1 c2 u1 hr hinv
      cases hr with
      | next hs rest =>
        obtain ⟨m1, uMid, hm1, hr1, hinvMid⟩ := postIndex_step N hinv hs
        obtain ⟨m2, u2, hm2, hr2, hinv2⟩ := ih rest hinvMid
        exact ⟨m1 + m2, u2, by omega, uRun_trans hr1 hr2, hinv2⟩
  obtain ⟨m0, u0, hm0, hr0, hinv0⟩ := init_to_postIndex N word
  obtain ⟨ms, u, hms, hrs, hinv⟩ := hchain hrun hinv0
  exact ⟨m0 + ms, u, by omega, uRun_trans hr0 hrs, hinv⟩

/-! ## Section 6: Output Readback Proof (`decodeHaltedUConfig`) -/

private theorem uSymAt_encodeRightTape_even (bits : List Bool) (i : Nat) :
    uSymAt (encodeRightTape bits) (2 * i) = if bitAt bits i then symLB else symLA := by
  induction bits generalizing i with
  | nil =>
    rw [bitAt_nil]
    rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      have h2 : 2 * (j + 1) = (2 * j) + 2 := by omega
      rw [h2]
      exact ih j

private theorem uSymAt_encodeRightTape_odd (bits : List Bool) (i : Nat) :
    uSymAt (encodeRightTape bits) (2 * i + 1) = symLA := by
  induction bits generalizing i with
  | nil => rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      have h2 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      rw [h2]
      exact ih j

private theorem decodeRightPairs_of_uRightEq :
    ∀ (r3 : List (Fin 11)) (bits : List Bool),
      URightEq (encodeRightTape bits) r3 →
      ∃ dec, decodeRightPairs r3 = some dec ∧ ∀ i, bitAt dec i = bitAt bits i
  | [], bits, heq => by
    refine ⟨[], rfl, fun i => ?_⟩
    rw [bitAt_nil]
    have h := heq (2 * i)
    rw [uSymAt_encodeRightTape_even] at h
    cases hb : bitAt bits i with
    | false => rfl
    | true =>
      rw [hb] at h
      cases h
  | [s], bits, heq => by
    have h0 : s = if bitAt bits 0 then symLB else symLA := by
      have h := (heq 0).symm
      rw [show (0 : Nat) = 2 * 0 from rfl, uSymAt_encodeRightTape_even] at h
      exact h
    refine ⟨[bitAt bits 0], ?_, ?_⟩
    · unfold decodeRightPairs
      rw [h0]
      cases bitAt bits 0 <;> rfl
    · intro i
      cases i with
      | zero => rfl
      | succ j =>
        have hj := heq (2 * (j + 1))
        have hge2 : uSymAt [s] (2 * (j + 1)) = symLA := by
          have h2 : 2 * (j + 1) = (2 * j) + 2 := by omega
          rw [h2]; rfl
        rw [uSymAt_encodeRightTape_even, hge2] at hj
        cases hb : bitAt bits (j + 1) with
        | false => simp [bitAt]
        | true => rw [hb] at hj; cases hj
  | s1 :: s2 :: rest, bits, heq => by
    have hs1 : s1 = if bitAt bits 0 then symLB else symLA := by
      have h := (heq 0).symm
      rw [show (0 : Nat) = 2 * 0 from rfl, uSymAt_encodeRightTape_even] at h
      exact h
    have hs2 : s2 = symLA := by
      have h := (heq 1).symm
      rw [show (1 : Nat) = 2 * 0 + 1 from rfl, uSymAt_encodeRightTape_odd] at h
      exact h
    have htail : URightEq (encodeRightTape (bits.drop 1)) rest := by
      intro k
      have hunf := uRightEq_encodeRightTape_unfold bits (k + 2)
      have h2 := heq (k + 2)
      exact hunf.symm.trans h2
    obtain ⟨decRest, hdecRest, hbitsRest⟩ := decodeRightPairs_of_uRightEq rest (bits.drop 1) htail
    refine ⟨bitAt bits 0 :: decRest, ?_, ?_⟩
    · unfold decodeRightPairs
      rw [hs2, hs1, hdecRest]
      cases bitAt bits 0 <;> rfl
    · intro i
      cases i with
      | zero => rfl
      | succ j =>
        change bitAt decRest j = bitAt bits (j + 1)
        rw [hbitsRest j]
        cases bits with
        | nil => simp [bitAt_nil]
        | cons _ _ => rfl

private theorem extractOddData_spec :
    ∀ (decRest : List Bool) (srcTape : List Bool),
      (∀ i, bitAt decRest (2 * i + 1) = false) →
      (∀ i, bitAt decRest (2 * i) = bitAt srcTape i) →
      ∃ oddBits, extractOddData decRest = some oddBits ∧ ∀ i, bitAt oddBits i = bitAt srcTape i
  | [], srcTape, _, hdata => by
    refine ⟨[], rfl, fun i => ?_⟩
    rw [bitAt_nil, ← hdata i, bitAt_nil]
  | [d], srcTape, _, hdata => by
    refine ⟨[d], rfl, fun i => ?_⟩
    cases i with
    | zero =>
      have h0 := hdata 0
      simpa [bitAt] using h0
    | succ j =>
      have hj := hdata (j + 1)
      have hnil : bitAt [d] (2 * (j + 1)) = false := by
        have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
        rw [h2]; simp [bitAt]
      rw [hnil] at hj
      simpa [bitAt] using hj.symm
  | d :: m :: rest, srcTape, heven, hdata => by
    have hm0 : m = false := by
      have h := heven 0
      simpa [bitAt] using h
    have heven' : ∀ i, bitAt rest (2 * i + 1) = false := by
      intro i
      have h := heven (i + 1)
      have h2 : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
      rw [h2] at h
      exact h
    have hdata' : ∀ i, bitAt rest (2 * i) = bitAt (srcTape.drop 1) i := by
      intro i
      have h := hdata (i + 1)
      have h2 : 2 * (i + 1) = (2 * i) + 2 := by omega
      rw [h2] at h
      refine h.trans ?_
      cases srcTape with
      | nil => simp [bitAt_nil]
      | cons _ _ => rfl
    obtain ⟨oddRest, hoddRest, hbitsOdd⟩ := extractOddData_spec rest (srcTape.drop 1) heven' hdata'
    refine ⟨d :: oddRest, ?_, ?_⟩
    · unfold extractOddData
      rw [hm0, hoddRest]
      rfl
    · intro i
      cases i with
      | zero =>
        have h0 := hdata 0
        simpa [bitAt] using h0
      | succ j =>
        change bitAt oddRest j = bitAt srcTape (j + 1)
        rw [hbitsOdd j]
        cases srcTape with
        | nil => simp [bitAt_nil]
        | cons _ _ => rfl

private theorem split_exact_prefix_before_nonLA :
    ∀ (pre : List (Fin 11)) (s : Fin 11) (_hs : s ≠ symLA) (tail full : List (Fin 11)),
      URightEq (pre ++ s :: tail) full →
      ∃ fullTail, full = pre ++ s :: fullTail ∧ URightEq tail fullTail
  | [], s, hs, _, full, heq => by
    cases full with
    | nil =>
      have h0 := heq 0
      dsimp [uSymAt] at h0
      exact False.elim (hs h0)
    | cons y ys =>
      have hy : s = y := heq 0
      subst hy
      exact ⟨ys, rfl, fun i => heq (i + 1)⟩
  | p :: ps, s, hs, tail, full, heq => by
    cases full with
    | nil =>
      have hbad : uSymAt (p :: ps ++ s :: tail) (ps.length + 1) = s := by
        have haux : ∀ (xs : List (Fin 11)), uSymAt (xs ++ s :: tail) xs.length = s := by
          intro xs
          induction xs with
          | nil => rfl
          | cons _ _ ih => exact ih
        exact haux (p :: ps)
      have hnil : uSymAt [] (ps.length + 1) = symLA := rfl
      have hc := (heq (ps.length + 1)).symm.trans hbad
      rw [hnil] at hc
      exact False.elim (hs hc.symm)
    | cons y ys =>
      have hpy : p = y := heq 0
      subst hpy
      obtain ⟨fullTail, hfull, htail⟩ :=
        split_exact_prefix_before_nonLA ps s hs tail ys (fun i => heq (i + 1))
      exact ⟨fullTail, congrArg (p :: ·) hfull, htail⟩

theorem decodeHaltedUConfig_of_marked_halt
    (left : List (Fin 11)) (a b : Nat) (hb : b ≥ 2)
    (srcTape finalNormTape : List Bool) (rightBits : List Bool)
    (hm : MarkedTapeMatches srcTape finalNormTape)
    (hrbits : ∀ j, bitAt rightBits j = bitAt finalNormTape (1 + j))
    (uFinal : UConfig)
    (heq : UConfigEq
      (uAt left
        (symDELTA :: (List.replicate a symLA ++ List.replicate b symLB ++
          symLA :: encodeRightBit true ++ encodeRightTape rightBits))
        stateU3)
      uFinal) :
    decodeHaltedUConfig uFinal = some (trimRightFalse srcTape) := by
  obtain ⟨_, hsym, hst, hrightEq⟩ := heq
  dsimp [uAt] at hsym hst hrightEq
  let pre := List.replicate a symLA ++ List.replicate b symLB ++ [symLA]
  have hpreAlign : List.replicate a symLA ++ List.replicate b symLB ++
        symLA :: encodeRightBit true ++ encodeRightTape rightBits =
      pre ++ symLB :: (symLA :: encodeRightTape rightBits) := by
    simp [pre, encodeRightBit, List.append_assoc]
  rw [hpreAlign] at hrightEq
  obtain ⟨fullTail, hfullRight, htailEq⟩ :=
    split_exact_prefix_before_nonLA pre symLB (by decide) (symLA :: encodeRightTape rightBits)
      uFinal.right hrightEq
  unfold decodeHaltedUConfig
  rw [← hst, ← hsym]
  dsimp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
  have hdropLA : (pre ++ symLB :: fullTail).dropWhile (· == symLA) =
      List.replicate b symLB ++ symLA :: symLB :: fullTail := by
    have hbSplit : b = 1 + (b - 1) := by omega
    have hpreEq : pre ++ symLB :: fullTail =
        List.replicate a symLA ++ (symLB :: (List.replicate (b - 1) symLB ++ symLA :: symLB :: fullTail)) := by
      dsimp [pre]
      conv => lhs; arg 1; arg 1; arg 2; rw [hbSplit]
      rw [replicate_add_split 1]
      simp [List.replicate, List.append_assoc]
    have hdropRep : ∀ (n : Nat) (xs : List (Fin 11)),
        (List.replicate n symLA ++ xs).dropWhile (· == symLA) = xs.dropWhile (· == symLA) := by
      intro n xs
      induction n with
      | zero => rfl
      | succ _ ih => exact ih
    rw [hpreEq, hdropRep]
    conv => rhs; arg 1; rw [hbSplit]
    rw [replicate_add_split 1]
    rfl
  have hdropLB : (List.replicate b symLB ++ symLA :: symLB :: fullTail).dropWhile (· == symLB) =
      symLA :: symLB :: fullTail := by
    have hdropRepB : ∀ (n : Nat) (xs : List (Fin 11)),
        (List.replicate n symLB ++ xs).dropWhile (· == symLB) = xs.dropWhile (· == symLB) := by
      intro n xs
      induction n with
      | zero => rfl
      | succ _ ih => exact ih
    rw [hdropRepB]
    rfl
  rw [hfullRight, hdropLA, hdropLB]
  have hlbCount : (List.replicate b symLB ++ symLA :: symLB :: fullTail).length -
      (symLA :: symLB :: fullTail).length = b := by
    rw [List.length_append, List.length_replicate]
    omega
  rw [hlbCount, if_pos hb]
  dsimp only [beq_self_eq_true, ↓reduceIte]
  have hr3Eq : URightEq (encodeRightTape (true :: rightBits)) (symLB :: fullTail) :=
    uRightEq_cons symLB htailEq
  obtain ⟨dec, hdec, hdecBits⟩ := decodeRightPairs_of_uRightEq (symLB :: fullTail) (true :: rightBits) hr3Eq
  rw [hdec]
  cases dec with
  | nil =>
    have h0 := hdecBits 0
    cases h0
  | cons d0 decRest =>
    have hd0 : d0 = true := hdecBits 0
    subst hd0
    unfold decodeMarkedBits
    dsimp only [beq_self_eq_true, ↓reduceIte]
    have heven : ∀ i, bitAt decRest (2 * i + 1) = false := by
      intro i
      have h1 : bitAt (true :: decRest) (2 * i + 2) = bitAt (true :: rightBits) (2 * i + 2) :=
        hdecBits (2 * i + 2)
      change bitAt decRest (2 * i + 1) = bitAt rightBits (2 * i + 1) at h1
      rw [h1, hrbits (2 * i + 1)]
      have h2 : 1 + (2 * i + 1) = 2 * (i + 1) := by omega
      rw [h2]
      exact hm.2.1 (i + 1) (by omega)
    have hdata : ∀ i, bitAt decRest (2 * i) = bitAt srcTape i := by
      intro i
      have h1 : bitAt (true :: decRest) (2 * i + 1) = bitAt (true :: rightBits) (2 * i + 1) :=
        hdecBits (2 * i + 1)
      change bitAt decRest (2 * i) = bitAt rightBits (2 * i) at h1
      rw [h1, hrbits (2 * i)]
      have h2 : 1 + 2 * i = 2 * i + 1 := by omega
      rw [h2]
      exact hm.2.2 i
    obtain ⟨oddBits, hodd, hoddBits⟩ := extractOddData_spec decRest srcTape heven hdata
    rw [hodd]
    dsimp only [Option.map]
    exact congrArg some (trimRightFalse_eq_of_bitAt_eq hoddBits)

/-! ## Section 7: Constructive Master Universality & Output Readback Theorems -/

theorem source_halt_to_u_halt_with_output (M : SourceTM) (w : List Bool)
    {t : Nat} {srcFinal : SourceConfig M.numStates}
    (hsrcRun : SourceTMRun M t (initSourceConfig M w) srcFinal)
    (hsrcStop : sourceStep M srcFinal = none) :
    ∃ n uFinal,
      URun n (encodeSourceInstance M w) uFinal ∧
      uNext uFinal = none ∧
      decodeHaltedUConfig uFinal = some (sourceConfigOutput srcFinal) := by
  obtain ⟨normFinal, hnormRun, hfinSt, _, hmFin, hnormStop⟩ :=
    source_halt_to_norm_exit M w hsrcRun hsrcStop
  obtain ⟨uSteps1, u1, _, huRun1, hinv1⟩ :=
    normRun_to_postIndex (normalizeSafeTM M) (encodeMarkedWord w) hnormRun
  obtain ⟨uSteps2, uFinal, _, huRun2, huStop, rightBits, hrbits, heqFinal⟩ :=
    postIndex_halt (normalizeSafeTM M) hinv1 hnormStop
  have hactFinal : (normalizeSafeTM M).rule normFinal.state (bitAt normFinal.tape 0) =
      ⟨true, .left, ⟨numNormStates M - 1, by have := numNormStates_ge_3 M; omega⟩⟩ := by
    have hbit0 : bitAt normFinal.tape 0 = true := hmFin.1
    rw [hbit0]
    exact normSafeRule_halt M normFinal.state hfinSt true
  have hwTrue : ((normalizeSafeTM M).rule normFinal.state (bitAt normFinal.tape 0)).write = true := by
    rw [hactFinal]
  let act := (normalizeSafeTM M).rule normFinal.state (bitAt normFinal.tape 0)
  have hbGe2 : 5 + 5 * act.next.val ≥ 2 := by omega
  have heqTrue : UConfigEq
      (uAt (tableFull (normalizeSafeTM M))
        (symDELTA :: (List.replicate (5 * ((normalizeSafeTM M).numStates - act.next.val) - 3) symLA ++
          List.replicate (5 + 5 * act.next.val) symLB ++
          symLA :: encodeRightBit true ++ encodeRightTape rightBits))
        stateU3)
      uFinal := by
    rw [← hwTrue]
    exact heqFinal
  have hdec := decodeHaltedUConfig_of_marked_halt (tableFull (normalizeSafeTM M))
    (5 * ((normalizeSafeTM M).numStates - act.next.val) - 3) (5 + 5 * act.next.val) hbGe2
    srcFinal.tape normFinal.tape rightBits hmFin hrbits uFinal heqTrue
  exact ⟨uSteps1 + uSteps2, uFinal, uRun_trans huRun1 huRun2, huStop, hdec⟩

/-- Constructive converse: `n` steps of `uNext` bound the source execution by `n` steps,
    allowing decidable bounded evaluation `evalSourceBounded`! -/
theorem u_halt_to_source_halt_with_output (M : SourceTM) (w : List Bool)
    {n : Nat} {final : UConfig}
    (hrun : URun n (encodeSourceInstance M w) final)
    (hstop : uNext final = none) :
    ∃ t srcFinal,
      t ≤ n ∧
      SourceTMRun M t (initSourceConfig M w) srcFinal ∧
      sourceStep M srcFinal = none ∧
      decodeHaltedUConfig final = some (sourceConfigOutput srcFinal) := by
  cases evalSourceBounded M (initSourceConfig M w) n with
  | running srcCurr hsrcMore =>
    obtain ⟨ncFuture, hnormMore, _⟩ := normalizeSafe_multi_step_from_init M w hsrcMore
    obtain ⟨uSteps, uFuture, huGe, huMore, _⟩ :=
      normRun_to_postIndex (normalizeSafeTM M) (encodeMarkedWord w) hnormMore
    have hle := uRun_no_extend_after_stop hrun hstop huMore
    exact False.elim (by omega)
  | halted t hle srcFinal hsrcRun hsrcStop =>
    obtain ⟨n2, uFinal2, huRun2, huStop2, hdec2⟩ :=
      source_halt_to_u_halt_with_output M w hsrcRun hsrcStop
    obtain ⟨_, hsame⟩ := uRun_halt_unique hrun hstop huRun2 huStop2
    subst hsame
    exact ⟨t, srcFinal, hle, hsrcRun, hsrcStop, hdec2⟩

/-- **Constructive Master Theorem**: Every partial deterministic binary one-sided Turing
    machine `(M, w)` halts if and only if `fixedUProgram` (`uNext`) halts on `encodeSourceInstance M w`! -/
theorem source_halts_iff_u_stops (M : SourceTM) (w : List Bool) :
    SourceEventuallyStopsTM M w ↔ UEventuallyStops (encodeSourceInstance M w) := by
  constructor
  · intro ⟨t, srcFinal, hsrcRun, hsrcStop⟩
    obtain ⟨n, uFinal, huRun, huStop, _⟩ :=
      source_halt_to_u_halt_with_output M w hsrcRun hsrcStop
    exact ⟨n, uFinal, huRun, huStop⟩
  · intro ⟨n, uFinal, huRun, huStop⟩
    obtain ⟨t, srcFinal, _, hsrcRun, hsrcStop, _⟩ :=
      u_halt_to_source_halt_with_output M w huRun huStop
    exact ⟨t, srcFinal, hsrcRun, hsrcStop⟩

/-- **Output Readback Theorem**: Whenever `encodeSourceInstance M w` halts at `final`,
    `decodeHaltedUConfig final` equals `some (canonicalOutput M w hsrc)`! -/
theorem u_halt_output_readback (M : SourceTM) (w : List Bool)
    {n : Nat} {final : UConfig}
    (hrun : URun n (encodeSourceInstance M w) final)
    (hstop : uNext final = none) :
    decodeHaltedUConfig final =
      some (canonicalOutput M w ((source_halts_iff_u_stops M w).mpr ⟨n, final, hrun, hstop⟩)) := by
  obtain ⟨t, srcFinal, _, hsrcRun, hsrcStop, hdec⟩ :=
    u_halt_to_source_halt_with_output M w hrun hstop
  have hcan := canonicalOutput_eq_of_run
    ((source_halts_iff_u_stops M w).mpr ⟨n, final, hrun, hstop⟩) hsrcRun hsrcStop
  rw [hcan]
  exact hdec

/-- Constructive halting equivalence all the way to the compiled 132-state `fixedBinaryProgram`! -/
theorem source_halts_iff_binary_stops (M : SourceTM) (w : List Bool) :
    SourceEventuallyStopsTM M w ↔
      PlainEventuallyStops fixedBinaryProgram (encodeUConfig (encodeSourceInstance M w)) := by
  constructor
  · intro hsrc
    exact u_halt_implies_binary_halt (encodeSourceInstance M w) ((source_halts_iff_u_stops M w).mp hsrc)
  · intro ⟨m, binFinal, hbinRun, hbinStop⟩
    cases evalSourceBounded M (initSourceConfig M w) m with
    | halted t _ srcFinal hsrcRun hsrcStop =>
      exact ⟨t, srcFinal, hsrcRun, hsrcStop⟩
    | running _ hsrcMore =>
      obtain ⟨_, hnormMore, _⟩ := normalizeSafe_multi_step_from_init M w hsrcMore
      obtain ⟨uSteps, uFuture, huGe, huMore, _⟩ :=
        normRun_to_postIndex (normalizeSafeTM M) (encodeMarkedWord w) hnormMore
      obtain ⟨binFuture, hbinFuture, _⟩ :=
        u_run_refines_binary huMore (encodeUConfig (encodeSourceInstance M w)) (plain_eq_refl _)
      have hgt : 10 * uSteps = (m + 1) + (10 * uSteps - (m + 1)) := by omega
      rw [hgt] at hbinFuture
      obtain ⟨mid1, hpre1, _⟩ := plain_run_split fixedBinaryProgram (m + 1) (10 * uSteps - (m + 1)) hbinFuture
      obtain ⟨mid0, hpre0, hsuf1⟩ := plain_run_split fixedBinaryProgram m 1 hpre1
      have hsame := plain_run_unique fixedBinaryProgram hbinRun mid0 hpre0
      subst hsame
      cases hsuf1 with
      | next hstep _ =>
        rw [hbinStop] at hstep
        cases hstep

/-! ## End-to-End Executable `#guard` Verification (`encodeSourceInstance` -> `uNext` -> `decodeHaltedUConfig`) -/

private def runUBounded : Nat → UConfig → Option UConfig
  | 0, _ => none
  | k + 1, u =>
    match uNext u with
    | none => some u
    | some u' => runUBounded k u'

private def trivialHaltTM : SourceTM where
  numStates := 1
  hpos := by decide
  stepRule := fun _ _ => none

#guard (runUBounded 60000 (encodeSourceInstance trivialHaltTM [true])).bind decodeHaltedUConfig == some [true]
#guard (runUBounded 60000 (encodeSourceInstance trivialHaltTM [])).bind decodeHaltedUConfig == some []
#guard (runUBounded 80000 (encodeSourceInstance trivialHaltTM [false, true, false])).bind decodeHaltedUConfig == some [false, true]

#print axioms init_to_postIndex
#print axioms postIndex_step
#print axioms postIndex_halt
#print axioms normRun_to_postIndex
#print axioms decodeHaltedUConfig_of_marked_halt
#print axioms source_halt_to_u_halt_with_output
#print axioms u_halt_to_source_halt_with_output
#print axioms source_halts_iff_u_stops
#print axioms u_halt_output_readback
#print axioms source_halts_iff_binary_stops
#print axioms encodeSourceInstance_poly_bound
