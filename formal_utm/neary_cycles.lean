import formal_utm.neary_encoder

/-!
# Symbolic Bidirectional Scan Engine & Neary `U(3,11)` 4-Cycle Execution

Provides a clean bidirectional tape-scanning algebra on `UConfig` (`uAt` and
`uAtRightmost`) and proves symbolic multi-step lemmas for all four cycles of
Neary's `U(3,11)` universal Turing machine:
- **Cycle 1** (`cycle1_full`): Scans `LA^a ++ LB^b ++ [LA]`, neutralizes `b - 1`
  rightmost `LAMBDA` markers to `DELTA`, converts intermediate symbols via
  `toArrowL`, and enters Cycle 2 at `(stateU2, LE)` just left of `GAMMA`.
- **Cycle 2 + Cycle 3** (`cycle2_and_cycle3`): Copies an indexed ETR word over
  the `LE`-filled overlined region via `GAMMA`, restores all `RE/RH/LAMBDA`
  markers rightward in `stateU2`, and turns `GAMMA -> LH` entering `stateU3`.
- **Cycle 4** (`cycle4_*` & Lemma 3.4.3): Handles R-move writes (`[E, LE]` and
  `[LH, E]`), Case D (`E'` intermediate step), L-move reads (`E` vs `H`), and
  Lemma 3.4.3 boundary halting at `(stateU3, symDELTA)`.
-/

/-! ## Helper Lemmas on `List.replicate` and `URun` -/

theorem replicate_add_split {α : Type} (m n : Nat) (x : α) :
    List.replicate (m + n) x = List.replicate m x ++ List.replicate n x := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h : k + 1 + n = (k + n) + 1 := by omega
    rw [h, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

theorem uRun_trans {n m : Nat} {a b c : UConfig}
    (h1 : URun n a b) (h2 : URun m b c) : URun (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | @next k x y z hs rest ih =>
    have r := URun.next hs (ih h2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem uRun_snoc_trans_pos {n m : Nat} {a b c d : UConfig}
    (h1 : URun n a b) (hs : uNext b = some c) (h2 : URun m c d) :
    ∃ k, k ≥ 1 ∧ URun k a d :=
  ⟨(n + 1) + m, by omega, uRun_trans (u_run_snoc h1 hs) h2⟩

theorem uRun_deterministic {n : Nat} {a b c : UConfig}
    (h1 : URun n a b) (h2 : URun n a c) : b = c := by
  induction h1 generalizing c with
  | zero _ => cases h2; rfl
  | @next k x y z hs1 rest1 ih =>
    cases h2 with
    | @next _ _ y2 _ hs2 rest2 =>
      rw [hs1] at hs2
      injection hs2 with hy
      subst hy
      exact ih rest2

theorem uRun_halt_unique {n1 n2 : Nat} {a b1 b2 : UConfig}
    (r1 : URun n1 a b1) (s1 : uNext b1 = none)
    (r2 : URun n2 a b2) (s2 : uNext b2 = none) :
    n1 = n2 ∧ b1 = b2 := by
  induction r1 generalizing n2 b2 with
  | zero _ =>
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

theorem uRun_no_extend_after_stop {n m : Nat} {a b c : UConfig}
    (r1 : URun n a b) (s1 : uNext b = none) (r2 : URun m a c) : m ≤ n := by
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

/-! ## `uAt` & `uAtRightmost` Tape Positioning Primitives -/

def uAt (left : List (Fin 11)) (fromHead : List (Fin 11)) (q : Fin 3) : UConfig :=
  ⟨left.reverse, fromHead.headD symLA, fromHead.drop 1, q⟩

def uAtRightmost (left : List (Fin 11)) (h : Fin 11) :
    List (Fin 11) → List (Fin 11) → Fin 3 → UConfig
  | [], rs, q => uAt left (h :: rs) q
  | x :: xs, rs, q => uAtRightmost (left ++ [h]) x xs rs q

theorem uAt_cons (left : List (Fin 11)) (s : Fin 11) (rs : List (Fin 11)) (q : Fin 3) :
    uAt left (s :: rs) q = ⟨left.reverse, s, rs, q⟩ := rfl

theorem uNext_right_uAt (left : List (Fin 11)) (s w : Fin 11) (rs : List (Fin 11))
    (q q' : Fin 3) (hp : fixedUProgram q s = some ⟨w, q', .right⟩) :
    uNext (uAt left (s :: rs) q) = some (uAt (left ++ [w]) rs q') := by
  unfold uAt uNext
  dsimp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
  rw [hp]
  cases rs with
  | nil => simp [List.reverse_append]
  | cons r rs' => simp [List.reverse_append]

theorem uNext_left_uAt (left : List (Fin 11)) (prev s w : Fin 11) (rs : List (Fin 11))
    (q q' : Fin 3) (hp : fixedUProgram q s = some ⟨w, q', .left⟩) :
    uNext (uAt (left ++ [prev]) (s :: rs) q) = some (uAt left (prev :: w :: rs) q') := by
  unfold uAt uNext
  dsimp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
  rw [hp, List.reverse_append]
  rfl

theorem uNext_left_into_block (left : List (Fin 11)) (target : Fin 11)
    (xs : List (Fin 11)) (s w : Fin 11) (rs : List (Fin 11)) (q q' : Fin 3)
    (hp : fixedUProgram q s = some ⟨w, q', .left⟩) :
    uNext (uAt (left ++ [target] ++ xs) (s :: rs) q) =
      some (uAtRightmost left target xs (w :: rs) q') := by
  induction xs generalizing left target with
  | nil =>
    simp only [List.append_nil, uAtRightmost]
    exact uNext_left_uAt left target s w rs q q' hp
  | cons x xs' ih =>
    have hassoc : left ++ [target] ++ (x :: xs') = (left ++ [target]) ++ [x] ++ xs' := by
      simp [List.append_assoc]
    rw [hassoc]
    exact ih (left ++ [target]) x

theorem uAtRightmost_append (left : List (Fin 11)) (h : Fin 11)
    (xs ys rs : List (Fin 11)) (q : Fin 3) :
    uAtRightmost left h (xs ++ ys) rs q =
      match ys with
      | [] => uAtRightmost left h xs rs q
      | y :: ys' => uAtRightmost (left ++ [h] ++ xs) y ys' rs q := by
  induction xs generalizing left h with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys' => simp [uAtRightmost]
  | cons x xs' ih =>
    simp only [List.cons_append, uAtRightmost]
    rw [ih (left ++ [h]) x]
    cases ys with
    | nil => rfl
    | cons y ys' => simp [List.append_assoc]

theorem uRun_scan_right (left : List (Fin 11)) (xs rest : List (Fin 11))
    (q : Fin 3) (f : Fin 11 → Fin 11)
    (hf : ∀ s ∈ xs, fixedUProgram q s = some ⟨f s, q, .right⟩) :
    URun xs.length (uAt left (xs ++ rest) q) (uAt (left ++ xs.map f) rest q) := by
  induction xs generalizing left with
  | nil => simp [URun.zero]
  | cons s xs' ih =>
    have hs := uNext_right_uAt left s (f s) (xs' ++ rest) q q (hf s List.mem_cons_self)
    have hrest := ih (left ++ [f s]) (fun y hy => hf y (List.mem_cons_of_mem s hy))
    have hcomb := URun.next hs hrest
    simpa [List.append_assoc] using hcomb

theorem uRun_scan_left (left : List (Fin 11)) (target : Fin 11)
    (xs rs : List (Fin 11)) (q : Fin 3) (g : Fin 11 → Fin 11)
    (hg : ∀ s ∈ xs, fixedUProgram q s = some ⟨g s, q, .left⟩) :
    URun xs.length (uAtRightmost left target xs rs q)
      (uAt left (target :: (xs.map g ++ rs)) q) := by
  induction xs generalizing left target with
  | nil => exact URun.zero _
  | cons x xs' ih =>
    change URun (xs'.length + 1) (uAtRightmost (left ++ [target]) x xs' rs q) _
    have h1 := ih (left ++ [target]) x (fun y hy => hg y (List.mem_cons_of_mem x hy))
    have h2 := uNext_left_uAt left target x (g x) (xs'.map g ++ rs) q q (hg x List.mem_cons_self)
    exact u_run_snoc h1 h2

/-! ## Finite Symbol Algebra for `U(3,11)` -/

def IsETRSym (s : Fin 11) : Prop := s = symE ∨ s = symH

def IsBodySym (s : Fin 11) : Prop :=
  s = symE ∨ s = symH ∨ s = symLE ∨ s = symLH ∨ s = symDELTA

def IsArrowSym (s : Fin 11) : Prop :=
  s = symLE ∨ s = symLH ∨ s = symDELTA

def toArrowL (s : Fin 11) : Fin 11 :=
  if s == symE || s == symLE || s == symRE then symLE
  else if s == symH || s == symLH || s == symRH then symLH
  else if s == symLAMBDA || s == symDELTA then symDELTA
  else s

def u1LeftSym (s : Fin 11) : Fin 11 :=
  if s == symE || s == symLE then symRE
  else if s == symH || s == symLH then symRH
  else if s == symDELTA then symLAMBDA
  else s

def u2LeftSym (s : Fin 11) : Fin 11 :=
  if s == symLE then symRE
  else if s == symLH then symRH
  else if s == symDELTA then symLAMBDA
  else s

def restoreSym (s : Fin 11) : Fin 11 :=
  if s == symLE || s == symRE || s == symE then symE
  else if s == symLH || s == symRH || s == symH then symH
  else if s == symDELTA || s == symLAMBDA then symLAMBDA
  else s

theorem isBody_of_isETR {s : Fin 11} (h : IsETRSym s) : IsBodySym s := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem isBody_of_isArrow {s : Fin 11} (h : IsArrowSym s) : IsBodySym s := by
  rcases h with rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem isArrow_toArrowL {s : Fin 11} (h : IsBodySym s) : IsArrowSym (toArrowL s) := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem toArrowL_idem {s : Fin 11} (h : IsBodySym s) :
    toArrowL (toArrowL s) = toArrowL s := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem toArrowL_of_isArrow {s : Fin 11} (h : IsArrowSym s) : toArrowL s = s := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem toArrowL_u2LeftSym {s : Fin 11} (h : IsArrowSym s) :
    toArrowL (u2LeftSym s) = s := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem restoreSym_toArrowL_etr {s : Fin 11} (h : IsETRSym s) :
    restoreSym (toArrowL s) = s := by
  rcases h with rfl | rfl <;> rfl

theorem u1_step_left_body {s : Fin 11} (h : IsBodySym s) :
    fixedUProgram stateU1 s = some ⟨u1LeftSym s, stateU1, .left⟩ := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem u1_step_right_after_left {s : Fin 11} (h : IsBodySym s) :
    fixedUProgram stateU1 (u1LeftSym s) = some ⟨toArrowL s, stateU1, .right⟩ := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem u2_step_left_arrow {s : Fin 11} (h : IsArrowSym s) :
    fixedUProgram stateU2 s = some ⟨u2LeftSym s, stateU2, .left⟩ := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem u1_step_right_after_u2 {s : Fin 11} (h : IsArrowSym s) :
    fixedUProgram stateU1 (u2LeftSym s) = some ⟨toArrowL (u2LeftSym s), stateU1, .right⟩ := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem u3_step_right_after_u2 {s : Fin 11} (h : IsArrowSym s) :
    fixedUProgram stateU3 (u2LeftSym s) = some ⟨toArrowL (u2LeftSym s), stateU3, .right⟩ := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem u2_step_restore_after_u2 {s : Fin 11} (h : IsArrowSym s) :
    fixedUProgram stateU2 (u2LeftSym s) = some ⟨restoreSym s, stateU2, .right⟩ := by
  rcases h with rfl | rfl | rfl <;> rfl

/-! ## ETR Membership Lemmas -/

theorem mem_replicate_eq {α : Type} {n : Nat} {x y : α} (h : y ∈ List.replicate n x) : y = x :=
  List.eq_of_mem_replicate h

private theorem etrSym_of_mem_rep_append_rep {a b : Nat} {s : Fin 11}
    (hs : s ∈ List.replicate a symE ++ List.replicate b symH) : IsETRSym s := by
  rw [List.mem_append] at hs
  rcases hs with h1 | h2
  · exact Or.inl (mem_replicate_eq h1)
  · exact Or.inr (mem_replicate_eq h2)

theorem nearyETR_all_etrSym (S : Nat) (act : NormAct S) :
    ∀ s ∈ nearyETR S act, IsETRSym s := by
  intro s hs
  cases act with
  | mk w d nxt =>
    cases d with
    | right =>
      cases w with
      | false =>
        change s ∈ List.replicate (nearyA S ⟨false, .right, nxt⟩) symE ++
          List.replicate (nearyB ⟨false, .right, nxt⟩) symH at hs
        exact etrSym_of_mem_rep_append_rep hs
      | true =>
        change s ∈ symH :: (List.replicate (nearyA S ⟨true, .right, nxt⟩) symE ++
          List.replicate (nearyB ⟨true, .right, nxt⟩) symH) at hs
        rw [List.mem_cons] at hs
        rcases hs with rfl | hrest
        · exact Or.inr rfl
        · exact etrSym_of_mem_rep_append_rep hrest
    | left =>
      cases w with
      | false =>
        change s ∈ (List.replicate (nearyA S ⟨false, .left, nxt⟩ - 1) symE ++
          List.replicate (nearyB ⟨false, .left, nxt⟩) symH) ++ [symE, symE, symE] at hs
        rw [List.mem_append] at hs
        rcases hs with h12 | h3
        · exact etrSym_of_mem_rep_append_rep h12
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
          rcases h3 with rfl | rfl | rfl <;> exact Or.inl rfl
      | true =>
        change s ∈ (List.replicate (nearyA S ⟨true, .left, nxt⟩ - 1) symE ++
          List.replicate (nearyB ⟨true, .left, nxt⟩) symH) ++ [symE, symH, symE] at hs
        rw [List.mem_append] at hs
        rcases hs with h12 | h3
        · exact etrSym_of_mem_rep_append_rep h12
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
          rcases h3 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact Or.inl rfl

theorem nearyExtra_all_etrSym (N : NormalizedTM) (q : Fin N.numStates) :
    ∀ s ∈ nearyExtra N q, IsETRSym s := by
  intro s hs
  unfold nearyExtra at hs
  by_cases h0 : q.val = 0
  · rw [if_pos h0] at hs
    exact etrSym_of_mem_rep_append_rep hs
  · rw [if_neg h0] at hs
    cases hinc : hasIncomingRight N q with
    | false =>
      rw [hinc, if_neg Bool.false_ne_true] at hs
      cases hs
    | true =>
      rw [hinc, if_pos rfl] at hs
      exact etrSym_of_mem_rep_append_rep hs

theorem nearyBlocksR2L_all_etrSym (N : NormalizedTM) :
    ∀ blk ∈ nearyBlocksR2L N, ∀ s ∈ blk, IsETRSym s := by
  intro blk hblk s hs
  unfold nearyBlocksR2L at hblk
  rw [List.mem_flatMap] at hblk
  obtain ⟨q, _, hq⟩ := hblk
  unfold nearyStateBlocksR2L at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact nearyExtra_all_etrSym N q s hs
  · exact nearyETR_all_etrSym N.numStates (N.rule q true) s hs
  · exact nearyETR_all_etrSym N.numStates (N.rule q false) s hs
  · exact nearyETR_all_etrSym N.numStates (N.rule q false) s hs
  · exact nearyETR_all_etrSym N.numStates (N.rule q true) s hs

/-! ## Cycle 1: Neutralizing `LAMBDA` Markers & Indexing the Next ETR -/

theorem u1_bounce_neutralize_lambda (left mid rs : List (Fin 11))
    (hmid : ∀ s ∈ mid, IsBodySym s) :
    ∃ steps, steps ≥ 1 ∧
      URun steps (uAtRightmost left symLAMBDA mid rs stateU1)
        (uAt (left ++ [symDELTA] ++ mid.map toArrowL) rs stateU1) := by
  have h1 := uRun_scan_left left symLAMBDA mid rs stateU1 u1LeftSym
    (fun s hs => u1_step_left_body (hmid s hs))
  have hlam : uNext (uAt left (symLAMBDA :: (mid.map u1LeftSym ++ rs)) stateU1) =
      some (uAt (left ++ [symDELTA]) (mid.map u1LeftSym ++ rs) stateU1) :=
    uNext_right_uAt left symLAMBDA symDELTA _ stateU1 stateU1 rfl
  have h2 := uRun_scan_right (left ++ [symDELTA]) (mid.map u1LeftSym) rs stateU1 toArrowL (by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hr := u1_step_right_after_left (hmid s hs)
    have hid : toArrowL (u1LeftSym s) = toArrowL s := by
      rcases hmid s hs with rfl | rfl | rfl | rfl | rfl <;> rfl
    rwa [hid])
  have hmap : (mid.map u1LeftSym).map toArrowL = mid.map toArrowL := by
    rw [List.map_map]
    apply List.map_congr_left
    intro s hs
    rcases hmid s hs with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hmap] at h2
  obtain ⟨k, hk, htot⟩ := uRun_snoc_trans_pos h1 hlam h2
  exact ⟨k, hk, by simpa [List.append_assoc] using htot⟩

theorem cycle1_one_lb_pass (left mid rs : List (Fin 11))
    (hmid : ∀ s ∈ mid, IsBodySym s) :
    ∃ steps, steps ≥ 1 ∧
      URun steps (uAt (left ++ [symLAMBDA] ++ mid) (symLB :: symLB :: rs) stateU1)
        (uAt (left ++ [symDELTA] ++ mid.map toArrowL ++ [symLE]) (symLB :: rs) stateU1) := by
  have hs1 : uNext (uAt (left ++ [symLAMBDA] ++ mid) (symLB :: symLB :: rs) stateU1) =
      some (uAt (left ++ [symLAMBDA] ++ (mid ++ [symLE])) (symLB :: rs) stateU2) := by
    simpa [List.append_assoc] using
      uNext_right_uAt (left ++ [symLAMBDA] ++ mid) symLB symLE (symLB :: rs) stateU1 stateU2 rfl
  have hs2 : uNext (uAt (left ++ [symLAMBDA] ++ (mid ++ [symLE])) (symLB :: rs) stateU2) =
      some (uAtRightmost left symLAMBDA (mid ++ [symLE]) (symLB :: rs) stateU1) :=
    uNext_left_into_block left symLAMBDA (mid ++ [symLE]) symLB symLB rs stateU2 stateU1 rfl
  have hmid' : ∀ s ∈ mid ++ [symLE], IsBodySym s := by
    intro s hs
    rw [List.mem_append, List.mem_singleton] at hs
    rcases hs with hm | rfl
    · exact hmid s hm
    · exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨k, _, hbounce⟩ := u1_bounce_neutralize_lambda left (mid ++ [symLE]) (symLB :: rs) hmid'
  have hmap : (mid ++ [symLE]).map toArrowL = mid.map toArrowL ++ [symLE] := by
    rw [List.map_append]; rfl
  rw [hmap] at hbounce
  have htot := URun.next hs1 (URun.next hs2 hbounce)
  exact ⟨k + 2, by omega, by simpa [List.append_assoc] using htot⟩

theorem cycle1_neutralize_chunks :
    ∀ (chunks : List (List (Fin 11))) (left mid rs : List (Fin 11)),
      (∀ c ∈ chunks, ∀ s ∈ c, IsBodySym s) →
      (∀ s ∈ mid, IsBodySym s) →
      ∃ steps, steps ≥ 1 ∧
        URun steps
          (uAt (left ++ (chunks.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ mid)
               (List.replicate (chunks.length + 2) symLB ++ symLA :: rs) stateU1)
          (uAtRightmost
            (left ++ (chunks.reverse.flatMap fun c => symDELTA :: c.map toArrowL))
            symDELTA (mid.map toArrowL ++ List.replicate (chunks.length + 2) symLE)
            (symGAMMA :: rs) stateU2)
  | [], left, mid, rs, _, hmid => by
    obtain ⟨k1, _, hp1⟩ := cycle1_one_lb_pass left mid (symLA :: rs) hmid
    have hs1 : uNext (uAt (left ++ [symDELTA] ++ mid.map toArrowL ++ [symLE]) (symLB :: symLA :: rs) stateU1) =
        some (uAt (left ++ [symDELTA] ++ (mid.map toArrowL ++ [symLE, symLE])) (symLA :: rs) stateU2) := by
      simpa [List.append_assoc] using
        uNext_right_uAt (left ++ [symDELTA] ++ mid.map toArrowL ++ [symLE]) symLB symLE (symLA :: rs) stateU1 stateU2 rfl
    have hs2 : uNext (uAt (left ++ [symDELTA] ++ (mid.map toArrowL ++ [symLE, symLE])) (symLA :: rs) stateU2) =
        some (uAtRightmost left symDELTA (mid.map toArrowL ++ [symLE, symLE]) (symGAMMA :: rs) stateU2) :=
      uNext_left_into_block left symDELTA (mid.map toArrowL ++ [symLE, symLE]) symLA symGAMMA rs stateU2 stateU2 rfl
    have htot := u_run_snoc (u_run_snoc hp1 hs1) hs2
    exact ⟨(k1 + 1) + 1, by omega, by simpa using htot⟩
  | c0 :: cs, left, mid, rs, hchunks, hmid => by
    have hrev : ((c0 :: cs).reverse.flatMap fun c => symLAMBDA :: c) =
        (cs.reverse.flatMap fun c => symLAMBDA :: c) ++ ([symLAMBDA] ++ c0) := by
      simp [List.reverse_cons, List.flatMap_append]
    have hrep : List.replicate ((c0 :: cs).length + 2) symLB ++ symLA :: rs =
        symLB :: symLB :: (List.replicate (cs.length + 1) symLB ++ symLA :: rs) := rfl
    let pre := left ++ (cs.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ c0
    have hstart_eq : left ++ ((c0 :: cs).reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ mid =
        pre ++ [symLAMBDA] ++ mid := by
      rw [hrev]; simp [pre, List.append_assoc]
    obtain ⟨k1, _, hp1⟩ := cycle1_one_lb_pass pre mid (List.replicate (cs.length + 1) symLB ++ symLA :: rs) hmid
    let mid' := c0 ++ [symDELTA] ++ mid.map toArrowL ++ [symLE]
    have hmid' : ∀ s ∈ mid', IsBodySym s := by
      intro s hs
      simp only [mid', List.mem_append, List.mem_singleton, List.mem_map] at hs
      rcases hs with ((hc0 | rfl) | ⟨x, hx, rfl⟩) | rfl
      · exact hchunks c0 List.mem_cons_self s hc0
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exact isBody_of_isArrow (isArrow_toArrowL (hmid x hx))
      · exact Or.inr (Or.inr (Or.inl rfl))
    have hcs : ∀ c ∈ cs, ∀ s ∈ c, IsBodySym s :=
      fun c hc => hchunks c (List.mem_cons_of_mem c0 hc)
    obtain ⟨k2, _, hp2⟩ := cycle1_neutralize_chunks cs left mid' rs hcs hmid'
    have hmid_align : uAt (pre ++ [symDELTA] ++ mid.map toArrowL ++ [symLE])
          (symLB :: (List.replicate (cs.length + 1) symLB ++ symLA :: rs)) stateU1 =
        uAt (left ++ (cs.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ mid')
          (List.replicate (cs.length + 2) symLB ++ symLA :: rs) stateU1 := by
      have hl : pre ++ [symDELTA] ++ mid.map toArrowL ++ [symLE] =
          left ++ (cs.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ mid' := by
        simp [pre, mid', List.append_assoc]
      rw [hl]
      rfl
    rw [← hstart_eq, ← hrep] at hp1
    rw [hmid_align] at hp1
    have hmid'_map : mid'.map toArrowL =
        c0.map toArrowL ++ [symDELTA] ++ mid.map toArrowL ++ [symLE] := by
      simp only [mid', List.map_append, List.map_singleton, List.map_map]
      have hid : List.map (toArrowL ∘ toArrowL) mid = mid.map toArrowL := by
        apply List.map_congr_left
        intro x hx
        exact toArrowL_idem (hmid x hx)
      rw [hid]
      rfl
    have hend_eq : uAtRightmost
          (left ++ (cs.reverse.flatMap fun c => symDELTA :: c.map toArrowL))
          symDELTA (mid'.map toArrowL ++ List.replicate (cs.length + 2) symLE)
          (symGAMMA :: rs) stateU2 =
        uAtRightmost
          (left ++ ((c0 :: cs).reverse.flatMap fun c => symDELTA :: c.map toArrowL))
          symDELTA (mid.map toArrowL ++ List.replicate ((c0 :: cs).length + 2) symLE)
          (symGAMMA :: rs) stateU2 := by
      have hrevD : ((c0 :: cs).reverse.flatMap fun c => symDELTA :: c.map toArrowL) =
          (cs.reverse.flatMap fun c => symDELTA :: c.map toArrowL) ++ ([symDELTA] ++ c0.map toArrowL) := by
        simp [List.reverse_cons, List.flatMap_append]
      rw [hmid'_map, hrevD]
      have hrepLE : [symLE] ++ List.replicate (cs.length + 2) symLE =
          List.replicate ((c0 :: cs).length + 2) symLE := by
        simp [List.replicate_succ]
      have hsplit : c0.map toArrowL ++ [symDELTA] ++ mid.map toArrowL ++ [symLE] ++
            List.replicate (cs.length + 2) symLE =
          c0.map toArrowL ++ (symDELTA :: (mid.map toArrowL ++ List.replicate ((c0 :: cs).length + 2) symLE)) := by
        rw [← hrepLE]
        simp [List.append_assoc]
      rw [hsplit, uAtRightmost_append]
      simp [List.append_assoc]
    rw [hend_eq] at hp2
    exact ⟨k1 + k2, by omega, uRun_trans hp1 hp2⟩

/-- Full Cycle 1 starting at `LA^a ++ LB^(chunks.length + 2) ++ symLA :: rs` in `stateU1`. -/
theorem cycle1_full (chunks : List (List (Fin 11))) (left mid : List (Fin 11))
    (a : Nat) (rs : List (Fin 11))
    (hchunks : ∀ c ∈ chunks, ∀ s ∈ c, IsBodySym s)
    (hmid : ∀ s ∈ mid, IsBodySym s) :
    ∃ steps, steps ≥ 1 ∧
      URun steps
        (uAt (left ++ (chunks.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ mid)
             (List.replicate a symLA ++ List.replicate (chunks.length + 2) symLB ++ symLA :: rs) stateU1)
        (uAtRightmost
          (left ++ (chunks.reverse.flatMap fun c => symDELTA :: c.map toArrowL))
          symDELTA (mid.map toArrowL ++ List.replicate (a + chunks.length + 2) symLE)
          (symGAMMA :: rs) stateU2) := by
  have hscanLA := uRun_scan_right
    (left ++ (chunks.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ mid)
    (List.replicate a symLA) (List.replicate (chunks.length + 2) symLB ++ symLA :: rs)
    stateU1 (fun _ => symLE) (by
      intro s hs
      rw [mem_replicate_eq hs]
      rfl)
  have hmapLA : (List.replicate a symLA).map (fun _ => symLE) = List.replicate a symLE := by
    simp [List.map_replicate]
  rw [hmapLA] at hscanLA
  have hmidA : ∀ s ∈ mid ++ List.replicate a symLE, IsBodySym s := by
    intro s hs
    rw [List.mem_append] at hs
    rcases hs with hm | hr
    · exact hmid s hm
    · rw [mem_replicate_eq hr]; exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨k, hk, hc1⟩ := cycle1_neutralize_chunks chunks left (mid ++ List.replicate a symLE) rs hchunks hmidA
  have halign1 : left ++ (chunks.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ mid ++
        List.replicate a symLE =
      left ++ (chunks.reverse.flatMap fun c => symLAMBDA :: c) ++ [symLAMBDA] ++ (mid ++ List.replicate a symLE) := by
    simp [List.append_assoc]
  rw [halign1] at hscanLA
  have hmapMidA : (mid ++ List.replicate a symLE).map toArrowL ++ List.replicate (chunks.length + 2) symLE =
      mid.map toArrowL ++ List.replicate (a + chunks.length + 2) symLE := by
    have hle : toArrowL symLE = symLE := rfl
    have hrepMap : (List.replicate a symLE).map toArrowL = List.replicate a symLE := by
      rw [List.map_replicate, hle]
    rw [List.map_append, hrepMap, List.append_assoc, ← replicate_add_split]
    have hadd : a + (chunks.length + 2) = a + chunks.length + 2 := by omega
    rw [hadd]
  rw [hmapMidA] at hc1
  have hstartEq : List.replicate a symLA ++ (List.replicate (chunks.length + 2) symLB ++ symLA :: rs) =
      List.replicate a symLA ++ List.replicate (chunks.length + 2) symLB ++ symLA :: rs := by
    simp [List.append_assoc]
  rw [hstartEq] at hscanLA
  exact ⟨(List.replicate a symLA).length + k, by omega, uRun_trans hscanLA hc1⟩

/-! ## Cycle 2 & Cycle 3: Copying the Indexed ETR & Restoring `<M>` -/

def etrToTargetSym (s : Fin 11) : Fin 11 :=
  if s == symH then symLB else symLA

theorem cycle2_copy_one (left etrInit between rs : List (Fin 11)) (c : Fin 11)
    (hc : IsETRSym c) (hbet : ∀ s ∈ between, IsArrowSym s) :
    ∃ steps, steps ≥ 1 ∧
      URun steps
        (uAtRightmost left symLAMBDA (etrInit ++ [c] ++ between ++ [symLE]) (symGAMMA :: rs) stateU2)
        (uAtRightmost left symLAMBDA (etrInit ++ [toArrowL c] ++ between)
          (symGAMMA :: etrToTargetSym c :: rs) stateU2) := by
  have hpos : uAtRightmost left symLAMBDA (etrInit ++ [c] ++ between ++ [symLE]) (symGAMMA :: rs) stateU2 =
      uAtRightmost (left ++ [symLAMBDA] ++ etrInit) c (between ++ [symLE]) (symGAMMA :: rs) stateU2 := by
    have hsplit : etrInit ++ [c] ++ between ++ [symLE] = etrInit ++ (c :: (between ++ [symLE])) := by
      simp [List.append_assoc]
    rw [hsplit, uAtRightmost_append]
  rw [hpos]
  have hbetLE : ∀ s ∈ between ++ [symLE], IsArrowSym s := by
    intro s hs
    rw [List.mem_append, List.mem_singleton] at hs
    rcases hs with hb | rfl
    · exact hbet s hb
    · exact Or.inl rfl
  have hidMap : ((between ++ [symLE]).map u2LeftSym).map toArrowL = between ++ [symLE] := by
    rw [List.map_map]
    exact (List.map_congr_left (fun s hs => toArrowL_u2LeftSym (hbetLE s hs))).trans (List.map_id _)
  have hleft := uRun_scan_left (left ++ [symLAMBDA] ++ etrInit) c (between ++ [symLE]) (symGAMMA :: rs)
    stateU2 u2LeftSym (fun s hs => u2_step_left_arrow (hbetLE s hs))
  rcases hc with rfl | rfl
  · have hsC : uNext (uAt (left ++ [symLAMBDA] ++ etrInit)
          (symE :: ((between ++ [symLE]).map u2LeftSym ++ symGAMMA :: rs)) stateU2) =
        some (uAt (left ++ [symLAMBDA] ++ etrInit ++ [symLE])
          ((between ++ [symLE]).map u2LeftSym ++ symGAMMA :: rs) stateU1) :=
      uNext_right_uAt _ symE symLE _ stateU2 stateU1 rfl
    have hright := uRun_scan_right (left ++ [symLAMBDA] ++ etrInit ++ [symLE])
      ((between ++ [symLE]).map u2LeftSym) (symGAMMA :: rs) stateU1 toArrowL (by
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨s, hs, rfl⟩ := hy
        exact u1_step_right_after_u2 (hbetLE s hs))
    rw [hidMap] at hright
    have hsGam : uNext (uAt (left ++ [symLAMBDA] ++ etrInit ++ [symLE] ++ (between ++ [symLE]))
          (symGAMMA :: rs) stateU1) =
        some (uAt (left ++ [symLAMBDA] ++ (etrInit ++ [symLE] ++ between))
          (symLE :: symLA :: rs) stateU3) := by
      have ha : left ++ [symLAMBDA] ++ etrInit ++ [symLE] ++ (between ++ [symLE]) =
          (left ++ [symLAMBDA] ++ (etrInit ++ [symLE] ++ between)) ++ [symLE] := by
        simp [List.append_assoc]
      rw [ha]
      exact uNext_left_uAt _ symLE symGAMMA symLA rs stateU1 stateU3 rfl
    have hsLE : uNext (uAt (left ++ [symLAMBDA] ++ (etrInit ++ [symLE] ++ between))
          (symLE :: symLA :: rs) stateU3) =
        some (uAtRightmost left symLAMBDA (etrInit ++ [symLE] ++ between)
          (symGAMMA :: symLA :: rs) stateU2) :=
      uNext_left_into_block left symLAMBDA (etrInit ++ [symLE] ++ between) symLE symGAMMA (symLA :: rs) stateU3 stateU2 rfl
    obtain ⟨k0, _, hr0⟩ := uRun_snoc_trans_pos hleft hsC hright
    exact ⟨(k0 + 1) + 1, by omega, u_run_snoc (u_run_snoc hr0 hsGam) hsLE⟩
  · have hsC : uNext (uAt (left ++ [symLAMBDA] ++ etrInit)
          (symH :: ((between ++ [symLE]).map u2LeftSym ++ symGAMMA :: rs)) stateU2) =
        some (uAt (left ++ [symLAMBDA] ++ etrInit ++ [symLH])
          ((between ++ [symLE]).map u2LeftSym ++ symGAMMA :: rs) stateU3) :=
      uNext_right_uAt _ symH symLH _ stateU2 stateU3 rfl
    have hright := uRun_scan_right (left ++ [symLAMBDA] ++ etrInit ++ [symLH])
      ((between ++ [symLE]).map u2LeftSym) (symGAMMA :: rs) stateU3 toArrowL (by
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨s, hs, rfl⟩ := hy
        exact u3_step_right_after_u2 (hbetLE s hs))
    rw [hidMap] at hright
    have hsGam : uNext (uAt (left ++ [symLAMBDA] ++ etrInit ++ [symLH] ++ (between ++ [symLE]))
          (symGAMMA :: rs) stateU3) =
        some (uAt (left ++ [symLAMBDA] ++ (etrInit ++ [symLH] ++ between))
          (symLE :: symLB :: rs) stateU3) := by
      have ha : left ++ [symLAMBDA] ++ etrInit ++ [symLH] ++ (between ++ [symLE]) =
          (left ++ [symLAMBDA] ++ (etrInit ++ [symLH] ++ between)) ++ [symLE] := by
        simp [List.append_assoc]
      rw [ha]
      exact uNext_left_uAt _ symLE symGAMMA symLB rs stateU3 stateU3 rfl
    have hsLE : uNext (uAt (left ++ [symLAMBDA] ++ (etrInit ++ [symLH] ++ between))
          (symLE :: symLB :: rs) stateU3) =
        some (uAtRightmost left symLAMBDA (etrInit ++ [symLH] ++ between)
          (symGAMMA :: symLB :: rs) stateU2) :=
      uNext_left_into_block left symLAMBDA (etrInit ++ [symLH] ++ between) symLE symGAMMA (symLB :: rs) stateU3 stateU2 rfl
    obtain ⟨k0, _, hr0⟩ := uRun_snoc_trans_pos hleft hsC hright
    exact ⟨(k0 + 1) + 1, by omega, u_run_snoc (u_run_snoc hr0 hsGam) hsLE⟩

private theorem cycle2_copy_rev :
    ∀ (revEtr : List (Fin 11)) (left between rs : List (Fin 11)),
      (∀ s ∈ revEtr, IsETRSym s) →
      (∀ s ∈ between, IsArrowSym s) →
      ∃ steps,
        URun steps
          (uAtRightmost left symLAMBDA
            (revEtr.reverse ++ between ++ List.replicate revEtr.length symLE)
            (symGAMMA :: rs) stateU2)
          (uAtRightmost left symLAMBDA
            (revEtr.reverse.map toArrowL ++ between)
            (symGAMMA :: (revEtr.reverse.map etrToTargetSym ++ rs)) stateU2)
  | [], left, between, rs, _, _ => ⟨0, by simpa using URun.zero _⟩
  | c :: revRest, left, between, rs, hetr, hbet => by
    have hc : IsETRSym c := hetr c List.mem_cons_self
    have hrest : ∀ s ∈ revRest, IsETRSym s := fun s hs => hetr s (List.mem_cons_of_mem c hs)
    have hstartEq : (c :: revRest).reverse ++ between ++ List.replicate (c :: revRest).length symLE =
        revRest.reverse ++ [c] ++ (between ++ List.replicate revRest.length symLE) ++ [symLE] := by
      have hrep : List.replicate (revRest.length + 1) symLE =
          List.replicate revRest.length symLE ++ [symLE] := by
        rw [replicate_add_split]; rfl
      simp only [List.reverse_cons, List.length_cons, hrep, List.append_assoc]
    have hbetExt : ∀ s ∈ between ++ List.replicate revRest.length symLE, IsArrowSym s := by
      intro s hs
      rw [List.mem_append] at hs
      rcases hs with hb | hr
      · exact hbet s hb
      · rw [mem_replicate_eq hr]; exact Or.inl rfl
    obtain ⟨k1, _, hp1⟩ := cycle2_copy_one left revRest.reverse
      (between ++ List.replicate revRest.length symLE) rs c hc hbetExt
    rw [← hstartEq] at hp1
    have hmidEq : revRest.reverse ++ [toArrowL c] ++ (between ++ List.replicate revRest.length symLE) =
        revRest.reverse ++ ([toArrowL c] ++ between) ++ List.replicate revRest.length symLE := by
      simp [List.append_assoc]
    rw [hmidEq] at hp1
    have hbetNext : ∀ s ∈ [toArrowL c] ++ between, IsArrowSym s := by
      intro s hs
      rw [List.mem_append, List.mem_singleton] at hs
      rcases hs with rfl | hb
      · exact isArrow_toArrowL (isBody_of_isETR hc)
      · exact hbet s hb
    obtain ⟨k2, hp2⟩ := cycle2_copy_rev revRest left ([toArrowL c] ++ between)
      (etrToTargetSym c :: rs) hrest hbetNext
    have hendL : revRest.reverse.map toArrowL ++ ([toArrowL c] ++ between) =
        (c :: revRest).reverse.map toArrowL ++ between := by
      simp [List.reverse_cons, List.append_assoc]
    have hendR : revRest.reverse.map etrToTargetSym ++ etrToTargetSym c :: rs =
        (c :: revRest).reverse.map etrToTargetSym ++ rs := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hendL, hendR] at hp2
    exact ⟨k1 + k2, uRun_trans hp1 hp2⟩

theorem cycle2_and_cycle3 (left etr mid rs : List (Fin 11))
    (hetr : ∀ s ∈ etr, IsETRSym s)
    (hmid : ∀ s ∈ mid, IsArrowSym s) :
    ∃ steps, steps ≥ 1 ∧
      URun steps
        (uAtRightmost left symLAMBDA
          (etr ++ mid ++ List.replicate etr.length symLE)
          (symGAMMA :: rs) stateU2)
        (uAt (left ++ [symLAMBDA] ++ etr ++ mid.map restoreSym ++ [symLH])
          (etr.map etrToTargetSym ++ rs) stateU3) := by
  have hrevEq : etr.reverse.reverse = etr := List.reverse_reverse etr
  have hrevLen : etr.reverse.length = etr.length := List.length_reverse
  have hrevSym : ∀ s ∈ etr.reverse, IsETRSym s := by
    intro s hs; rw [List.mem_reverse] at hs; exact hetr s hs
  obtain ⟨k1, hp1⟩ := cycle2_copy_rev etr.reverse left mid rs hrevSym hmid
  rw [hrevEq, hrevLen] at hp1
  have hallArrow : ∀ s ∈ etr.map toArrowL ++ mid, IsArrowSym s := by
    intro s hs
    rw [List.mem_append, List.mem_map] at hs
    rcases hs with ⟨x, hx, rfl⟩ | hm
    · exact isArrow_toArrowL (isBody_of_isETR (hetr x hx))
    · exact hmid s hm
  have hfinC2 := uRun_scan_left left symLAMBDA (etr.map toArrowL ++ mid)
    (symGAMMA :: (etr.map etrToTargetSym ++ rs)) stateU2 u2LeftSym
    (fun s hs => u2_step_left_arrow (hallArrow s hs))
  have hsLam : uNext (uAt left
        (symLAMBDA :: ((etr.map toArrowL ++ mid).map u2LeftSym ++ symGAMMA :: (etr.map etrToTargetSym ++ rs))) stateU2) =
      some (uAt (left ++ [symLAMBDA])
        ((etr.map toArrowL ++ mid).map u2LeftSym ++ symGAMMA :: (etr.map etrToTargetSym ++ rs)) stateU2) :=
    uNext_right_uAt left symLAMBDA symLAMBDA _ stateU2 stateU2 rfl
  have hc3Scan := uRun_scan_right (left ++ [symLAMBDA])
    ((etr.map toArrowL ++ mid).map u2LeftSym) (symGAMMA :: (etr.map etrToTargetSym ++ rs))
    stateU2 restoreSym (by
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      have hr := u2_step_restore_after_u2 (hallArrow s hs)
      have hid : restoreSym (u2LeftSym s) = restoreSym s := by
        rcases hallArrow s hs with rfl | rfl | rfl <;> rfl
      rwa [hid])
  have hrestored : ((etr.map toArrowL ++ mid).map u2LeftSym).map restoreSym =
      etr ++ mid.map restoreSym := by
    rw [List.map_map, List.map_append, List.map_map]
    have hetrId : List.map ((restoreSym ∘ u2LeftSym) ∘ toArrowL) etr = etr := by
      have h1 : ∀ x ∈ etr, ((restoreSym ∘ u2LeftSym) ∘ toArrowL) x = x := by
        intro x hx; rcases hetr x hx with rfl | rfl <;> rfl
      simpa using List.map_congr_left h1
    have hmidId : List.map (restoreSym ∘ u2LeftSym) mid = mid.map restoreSym := by
      apply List.map_congr_left
      intro x hx; rcases hmid x hx with rfl | rfl | rfl <;> rfl
    rw [hetrId, hmidId]
  rw [hrestored] at hc3Scan
  have hsGam : uNext (uAt (left ++ [symLAMBDA] ++ (etr ++ mid.map restoreSym))
        (symGAMMA :: (etr.map etrToTargetSym ++ rs)) stateU2) =
      some (uAt (left ++ [symLAMBDA] ++ (etr ++ mid.map restoreSym) ++ [symLH])
        (etr.map etrToTargetSym ++ rs) stateU3) :=
    uNext_right_uAt _ symGAMMA symLH _ stateU2 stateU3 rfl
  obtain ⟨kPre, _, hPre⟩ := uRun_snoc_trans_pos (uRun_trans hp1 hfinC2) hsLam hc3Scan
  exact ⟨kPre + 1, by omega, by simpa [List.append_assoc] using u_run_snoc hPre hsGam⟩

/-! ## Cycle 4 Transitions & Lemma 3.4.3 Halting -/

theorem cycle4_three_steps_on_E (left rs : List (Fin 11)) :
    URun 3 (uAt (left ++ [symE, symLH]) (symLA :: rs) stateU3)
      (uAt (left ++ [symE]) (symLA :: symLA :: rs) stateU1) := by
  have hassoc : left ++ [symE, symLH] = (left ++ [symE]) ++ [symLH] := by
    simp [List.append_assoc]
  rw [hassoc]
  have hs1 : uNext (uAt ((left ++ [symE]) ++ [symLH]) (symLA :: rs) stateU3) =
      some (uAt (left ++ [symE]) (symLH :: symLA :: rs) stateU3) :=
    uNext_left_uAt (left ++ [symE]) symLH symLA symLA rs stateU3 stateU3 rfl
  have hs2 : uNext (uAt (left ++ [symE]) (symLH :: symLA :: rs) stateU3) =
      some (uAt left (symE :: symLA :: symLA :: rs) stateU3) :=
    uNext_left_uAt left symE symLH symLA (symLA :: rs) stateU3 stateU3 rfl
  have hs3 : uNext (uAt left (symE :: symLA :: symLA :: rs) stateU3) =
      some (uAt (left ++ [symE]) (symLA :: symLA :: rs) stateU1) :=
    uNext_right_uAt left symE symE (symLA :: symLA :: rs) stateU3 stateU1 rfl
  exact URun.next hs1 (URun.next hs2 (URun.next hs3 (URun.zero _)))

theorem cycle4_right_write_false (left rs : List (Fin 11)) :
    URun 4 (uAt (left ++ [symE, symLH]) (symLA :: rs) stateU3)
      (uAt (left ++ [symE, symLE]) (symLA :: rs) stateU1) := by
  have h3 := cycle4_three_steps_on_E left rs
  have hs4 : uNext (uAt (left ++ [symE]) (symLA :: symLA :: rs) stateU1) =
      some (uAt ((left ++ [symE]) ++ [symLE]) (symLA :: rs) stateU1) :=
    uNext_right_uAt (left ++ [symE]) symLA symLE (symLA :: rs) stateU1 stateU1 rfl
  have htot := u_run_snoc h3 hs4
  simpa [List.append_assoc] using htot

theorem cycle4_right_write_true (left rs : List (Fin 11)) :
    URun 1 (uAt (left ++ [symLH]) (symLB :: rs) stateU3)
      (uAt (left ++ [symLH, symE]) rs stateU1) := by
  have hs1 : uNext (uAt (left ++ [symLH]) (symLB :: rs) stateU3) =
      some (uAt ((left ++ [symLH]) ++ [symE]) rs stateU1) :=
    uNext_right_uAt (left ++ [symLH]) symLB symE rs stateU3 stateU1 rfl
  have htot := URun.next hs1 (URun.zero _)
  simpa [List.append_assoc] using htot

theorem cycle4_left_read_true (left mid rs : List (Fin 11))
    (hmid : ∀ s ∈ mid, IsBodySym s) :
    ∃ steps, steps ≥ 1 ∧
      URun steps
        (uAt (left ++ [symLAMBDA] ++ mid ++ [symH, symLH]) (symLA :: rs) stateU3)
        (uAt (left ++ [symDELTA] ++ mid.map toArrowL) (symLA :: symLA :: symLA :: rs) stateU1) := by
  have ha1 : left ++ [symLAMBDA] ++ mid ++ [symH, symLH] =
      (left ++ [symLAMBDA] ++ mid ++ [symH]) ++ [symLH] := by
    simp [List.append_assoc]
  rw [ha1]
  have hs1 : uNext (uAt ((left ++ [symLAMBDA] ++ mid ++ [symH]) ++ [symLH]) (symLA :: rs) stateU3) =
      some (uAt (left ++ [symLAMBDA] ++ mid ++ [symH]) (symLH :: symLA :: rs) stateU3) :=
    uNext_left_uAt _ symLH symLA symLA rs stateU3 stateU3 rfl
  have hs2 : uNext (uAt ((left ++ [symLAMBDA] ++ mid) ++ [symH]) (symLH :: symLA :: rs) stateU3) =
      some (uAt (left ++ [symLAMBDA] ++ mid) (symH :: symLA :: symLA :: rs) stateU3) :=
    uNext_left_uAt _ symH symLH symLA (symLA :: rs) stateU3 stateU3 rfl
  have hs3 : uNext (uAt (left ++ [symLAMBDA] ++ mid) (symH :: symLA :: symLA :: rs) stateU3) =
      some (uAtRightmost left symLAMBDA mid (symLA :: symLA :: symLA :: rs) stateU1) :=
    uNext_left_into_block left symLAMBDA mid symH symLA (symLA :: symLA :: rs) stateU3 stateU1 rfl
  obtain ⟨kb, _, hbounce⟩ := u1_bounce_neutralize_lambda left mid (symLA :: symLA :: symLA :: rs) hmid
  have htot := URun.next hs1 (URun.next hs2 (URun.next hs3 hbounce))
  exact ⟨kb + 3, by omega, htot⟩

theorem cycle4_lemma_3_4_3_halt (left rs : List (Fin 11)) :
    URun 4 (uAt (left ++ [symLAMBDA, symLH]) (symLA :: rs) stateU3)
      (uAt left (symDELTA :: symLA :: symLA :: rs) stateU3) ∧
    uNext (uAt left (symDELTA :: symLA :: symLA :: rs) stateU3) = none := by
  have ha : left ++ [symLAMBDA, symLH] = (left ++ [symLAMBDA]) ++ [symLH] := by
    simp [List.append_assoc]
  rw [ha]
  have hs1 : uNext (uAt ((left ++ [symLAMBDA]) ++ [symLH]) (symLA :: rs) stateU3) =
      some (uAt (left ++ [symLAMBDA]) (symLH :: symLA :: rs) stateU3) :=
    uNext_left_uAt (left ++ [symLAMBDA]) symLH symLA symLA rs stateU3 stateU3 rfl
  have hs2 : uNext (uAt (left ++ [symLAMBDA]) (symLH :: symLA :: rs) stateU3) =
      some (uAt left (symLAMBDA :: symLA :: symLA :: rs) stateU3) :=
    uNext_left_uAt left symLAMBDA symLH symLA (symLA :: rs) stateU3 stateU3 rfl
  have hs3 : uNext (uAt left (symLAMBDA :: symLA :: symLA :: rs) stateU3) =
      some (uAt (left ++ [symDELTA]) (symLA :: symLA :: rs) stateU3) :=
    uNext_right_uAt left symLAMBDA symDELTA (symLA :: symLA :: rs) stateU3 stateU3 rfl
  have hs4 : uNext (uAt (left ++ [symDELTA]) (symLA :: symLA :: rs) stateU3) =
      some (uAt left (symDELTA :: symLA :: symLA :: rs) stateU3) :=
    uNext_left_uAt left symDELTA symLA symLA (symLA :: rs) stateU3 stateU3 rfl
  refine ⟨URun.next hs1 (URun.next hs2 (URun.next hs3 (URun.next hs4 (URun.zero _)))), rfl⟩

#print axioms cycle1_full
#print axioms cycle2_and_cycle3
#print axioms cycle4_right_write_false
#print axioms cycle4_right_write_true
#print axioms cycle4_left_read_true
#print axioms cycle4_lemma_3_4_3_halt
