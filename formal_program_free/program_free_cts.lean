import phase_layout

namespace FormalProgramFree

/-!
# Zero-UTM Program-Free Pure-`S` Cyclic-Tag Simulator (`R_PF`)

This file provides a 100% machine-checked, constructive (`Classical.choice`-free)
Lean 4 formalization of the **Program-Free Root-Restarted Pure-`S` Cyclic-Tag
Simulator**:
1. **Cyclic Tag System Semantics** (`CTSProgram`, `CTSConfig`, `ctsStep`, `CTSRun`,
   `CTSEventuallyHalts`, and constructive bounded evaluator `evalCTSBounded`);
2. **Explicit 11-State Deterministic Bottom-Up Tree Automaton**
   (`BottomUpTreeAutomaton (Fin 11)`, `pfHaltAutomaton`) recognizing `pfRootHalt`;
3. **100% Program-Free Root-Restarted Selector** (`pfSelect : Term → PFOutcome`)
   taking **NO `P` or `w` parameter** and containing **ZERO UTM states / tag rules**,
   where every `.step t'` is a genuine single native `S`-contraction `Step t t'`;
4. **Polynomial-Size Pure-`S` Encoder** (`encodeProgramFreeCTS P w : Term`), proved
   reachable from the 10-leaf seed `tenLeafSeed` and bounded by an explicit
   quadratic polynomial in `|P| + |w|`;
5. **Constructive Bidirectional Halting Equivalence** (`program_free_cts_halting_iff`).
-/

/-! ## Section 1: Cyclic Tag System Semantics -/

structure CTSProgram where
  phases : List (List Bool)
  nonempty : phases ≠ []
  deriving DecidableEq

structure CTSConfig where
  phaseIdx : Nat
  queue : List Bool
  deriving DecidableEq, Repr

def initCTSConfig (w : List Bool) : CTSConfig := ⟨0, w⟩

theorem ctsProgram_length_pos (P : CTSProgram) : 0 < P.phases.length := by
  cases h : P.phases with
  | nil => exact False.elim (P.nonempty h)
  | cons _ _ => simp

def ctsStep (P : CTSProgram) (cfg : CTSConfig) : Option CTSConfig :=
  match cfg.queue with
  | [] => none
  | b :: rest =>
      let appendant := if h : cfg.phaseIdx < P.phases.length then P.phases.get ⟨cfg.phaseIdx, h⟩ else []
      some ⟨(cfg.phaseIdx + 1) % P.phases.length, if b then rest ++ appendant else rest⟩

theorem ctsStep_nil (P : CTSProgram) (idx : Nat) :
    ctsStep P ⟨idx, []⟩ = none := rfl

theorem ctsStep_cons (P : CTSProgram) (idx : Nat) (h : idx < P.phases.length) (b : Bool) (rest : List Bool) :
    ctsStep P ⟨idx, b :: rest⟩ =
      some ⟨(idx + 1) % P.phases.length, if b then rest ++ P.phases.get ⟨idx, h⟩ else rest⟩ := by
  simp [ctsStep, h]

theorem ctsStep_eq_none_iff (P : CTSProgram) (cfg : CTSConfig) :
    ctsStep P cfg = none ↔ cfg.queue = [] := by
  cases cfg with
  | mk idx q =>
      cases q <;> simp [ctsStep]

def CTSValidConfig (P : CTSProgram) (cfg : CTSConfig) : Prop :=
  cfg.phaseIdx < P.phases.length

theorem initCTSConfig_valid (P : CTSProgram) (w : List Bool) :
    CTSValidConfig P (initCTSConfig w) :=
  ctsProgram_length_pos P

theorem ctsStep_preserves_valid (P : CTSProgram) {a b : CTSConfig}
    (hstep : ctsStep P a = some b) : CTSValidConfig P b := by
  cases a with
  | mk idx q =>
      cases q with
      | nil => simp [ctsStep] at hstep
      | cons bit rest =>
          simp only [ctsStep, Option.some.injEq] at hstep
          subst b
          exact Nat.mod_lt _ (ctsProgram_length_pos P)

inductive CTSRun (P : CTSProgram) : Nat → CTSConfig → CTSConfig → Prop where
  | zero (c : CTSConfig) : CTSRun P 0 c c
  | next {n : Nat} {a b c : CTSConfig} :
      ctsStep P a = some b → CTSRun P n b c → CTSRun P (n + 1) a c

theorem ctsRun_trans (P : CTSProgram) {n m : Nat} {a b c : CTSConfig}
    (h1 : CTSRun P n a b) (h2 : CTSRun P m b c) : CTSRun P (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | next hs _ ih =>
      have r := CTSRun.next hs (ih h2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem ctsRun_preserves_valid (P : CTSProgram) {n : Nat} {a b : CTSConfig}
    (hrun : CTSRun P n a b) (ha : CTSValidConfig P a) : CTSValidConfig P b := by
  induction hrun with
  | zero _ => exact ha
  | next hs _ ih => exact ih (ctsStep_preserves_valid P hs)

def CTSEventuallyHalts (P : CTSProgram) (w : List Bool) : Prop :=
  ∃ n final, CTSRun P n (initCTSConfig w) final ∧ ctsStep P final = none

/-- Constructive bounded CTS evaluator (`Classical.choice`-free).
    Returns `.inl (steps, haltedCfg)` if `cfg` halts within `fuel` steps,
    or `.inr futureCfg` after `fuel` defined transitions. -/
def evalCTSBounded (P : CTSProgram) : Nat → CTSConfig → Sum (Nat × CTSConfig) CTSConfig
  | 0, cfg => .inr cfg
  | fuel + 1, cfg =>
      match ctsStep P cfg with
      | none => .inl (0, cfg)
      | some cfg' =>
          match evalCTSBounded P fuel cfg' with
          | .inl (n, final) => .inl (n + 1, final)
          | .inr future => .inr future

theorem evalCTSBounded_spec (P : CTSProgram) (fuel : Nat) (cfg : CTSConfig) :
    match evalCTSBounded P fuel cfg with
    | .inl (n, final) => n ≤ fuel ∧ CTSRun P n cfg final ∧ ctsStep P final = none
    | .inr future => CTSRun P fuel cfg future := by
  induction fuel generalizing cfg with
  | zero =>
      simp [evalCTSBounded]
      exact CTSRun.zero cfg
  | succ fuel ih =>
      cases hs : ctsStep P cfg with
      | none =>
          simp [evalCTSBounded, hs]
          exact CTSRun.zero cfg
      | some cfg' =>
          have ih' := ih cfg'
          cases hr : evalCTSBounded P fuel cfg' with
          | inl pair =>
              rcases pair with ⟨n, final⟩
              rw [hr] at ih'
              rcases ih' with ⟨hle, hrun, hstop⟩
              simp [evalCTSBounded, hs, hr]
              exact ⟨by omega, CTSRun.next hs hrun, hstop⟩
          | inr future =>
              rw [hr] at ih'
              simp [evalCTSBounded, hs, hr]
              exact CTSRun.next hs ih'

theorem cts_bounded_halt_or_run (P : CTSProgram) (steps : Nat) (w : List Bool) :
    CTSEventuallyHalts P w ∨ ∃ future, CTSRun P steps (initCTSConfig w) future := by
  have hspec := evalCTSBounded_spec P steps (initCTSConfig w)
  cases hr : evalCTSBounded P steps (initCTSConfig w) with
  | inl pair =>
      rcases pair with ⟨n, final⟩
      rw [hr] at hspec
      exact Or.inl ⟨n, final, hspec.2.1, hspec.2.2⟩
  | inr future =>
      rw [hr] at hspec
      exact Or.inr ⟨future, hspec⟩


/-! ## Section 2: Fuel-Free Stable Version Chain Scanner & Append -/

theorem pf_termAt_append (term : Term) (path suffix : List Bool) :
    termAt term (path ++ suffix) = (termAt term path).bind (fun focus => termAt focus suffix) := by
  induction path generalizing term with
  | nil =>
      rw [term_at_nil]
      rfl
  | cons side rest ih =>
      cases term with
      | s => simp [termAt]
      | var _ => simp [termAt]
      | app l r => cases side <;> simp [termAt, ih]

def pfScanVersion (width : Nat) (current : Option (List Bool)) : Term → Option (List Bool)
  | .app (.app .s next) (.app (.app .s fields) _) =>
      let updated := match readFields width fields with | none => current | some bits => some bits
      pfScanVersion width updated next
  | _ => current

theorem pfScanVersion_closed (width : Nat) (current : Option (List Bool)) (term : Term)
    (h : parseFrame term = none) : pfScanVersion width current term = current := by
  unfold parseFrame at h
  unfold pfScanVersion
  split <;> simp_all

theorem pfScanVersion_frame (width : Nat) (current : Option (List Bool)) (next fields junk : Term) :
    pfScanVersion width current (frameTerm next fields junk) =
      pfScanVersion width (match readFields width fields with | none => current | some bits => some bits) next :=
  rfl

theorem pfScan_committed_records {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) :
    ∀ term current, layoutMatches (versionLayout records) term →
      pfScanVersion width current term = newestRecords records current := by
  induction records with
  | nil =>
      intro term current h
      exact (pfScanVersion_closed width current term h).trans (by rfl)
  | cons entry rest ih =>
      intro term current h
      obtain ⟨tl, tr, j, hparse, hl, hr⟩ := h
      have hterm := parse_frame_sound term tl tr j hparse
      subst term
      have hread : readFields width tr = some entry.val := by
        rw [matched_fields_read width (fieldsLayout entry.val) tr hr]
        simpa [entry.property] using read_layout_fields_complete entry.val
      simpa [pfScanVersion_frame, hread, newestRecords] using ih tl (some entry.val) hl

theorem pfScan_uncommitted_fields {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (fields : Layout)
    (hfields : readLayoutFields width fields = none) :
    ∀ term current, layoutMatches (versionWithFields records fields) term →
      pfScanVersion width current term = newestRecords records current := by
  induction records with
  | nil =>
      intro term current h
      obtain ⟨tl, tr, j, hparse, hl, hr⟩ := h
      have hterm := parse_frame_sound term tl tr j hparse
      subst term
      have hread : readFields width tr = none := by
        rw [matched_fields_read width fields tr hr]
        exact hfields
      have hclosed : parseFrame tl = none := hl
      simpa [pfScanVersion_frame, hread, newestRecords] using pfScanVersion_closed width current tl hclosed
  | cons entry rest ih =>
      intro term current h
      obtain ⟨tl, tr, j, hparse, hl, hr⟩ := h
      have hterm := parse_frame_sound term tl tr j hparse
      subst term
      have hread : readFields width tr = some entry.val := by
        rw [matched_fields_read width (fieldsLayout entry.val) tr hr]
        simpa [entry.property] using read_layout_fields_complete entry.val
      simpa [pfScanVersion_frame, hread, newestRecords] using ih tl (some entry.val) hl

def PFStableVersionValue {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (shape : Layout) : Prop :=
  ∀ term, layoutMatches shape term → pfScanVersion width none term = newestRecords records none

inductive PFStableVersionTrace {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (fuel : Nat) (desired : List Bool) : Nat → Layout → Layout → Prop where
  | done (s : Layout) : PFStableVersionTrace records fuel desired 0 s s
  | next {n : Nat} {a b c : Layout} {path : List Bool} :
      FuelAgreement fuel width desired a → PFStableVersionValue records a →
      chooseVersion fuel width desired a = some path → openLayoutAt a path = some b →
      PFStableVersionTrace records fuel desired n b c → PFStableVersionTrace records fuel desired (n + 1) a c

theorem pf_lift_safe_fields_to_stable_version {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool)
    (hw : desired.length = width) {n : Nat} {a b : Layout}
    (trace : SafeFieldTrace desired n a b) :
    PFStableVersionTrace records (records.length + 1) desired n
      (versionWithFields records a) (versionWithFields records b) := by
  induction trace with
  | done _ => exact PFStableVersionTrace.done _
  | @next n a b c path hread hchoose hopen _ ih =>
      have hread' : readLayoutFields width a = none := by simpa [hw] using hread
      have hagree : FuelAgreement (records.length + 1) width desired (versionWithFields records a) :=
        tree_selector_matches_fuel_uncommitted records desired a hread'
      have hstable : PFStableVersionValue records (versionWithFields records a) :=
        fun term hm => pfScan_uncommitted_fields records a hread' term none hm
      have hchoice : chooseVersion (records.length + 1) width desired (versionWithFields records a) =
          some (List.replicate records.length false ++ true :: path) := by
        rw [choose_version_with_uncommitted_fields records desired a hread', hchoose]
        rfl
      exact PFStableVersionTrace.next hagree hstable hchoice (open_version_with_fields records a b path hopen) ih

theorem pf_stable_version_append_complete {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    ∃ k, PFStableVersionTrace records (records.length + 1) entry.val k
        (versionLayout records) (versionLayout (records ++ [entry])) ∧
      1 ≤ k ∧ k ≤ 2 * width + 2 := by
  obtain ⟨k, hfields, hbound⟩ := safe_selected_fields_complete entry.val []
  have hfields' : SafeFieldTrace entry.val k .unopened (fieldsLayout entry.val) := by
    simpa [partialFieldsLayout] using hfields
  have hrest := pf_lift_safe_fields_to_stable_version records entry.val entry.property hfields'
  have hrest' : PFStableVersionTrace records (records.length + 1) entry.val k
      (partialVersionLayout [] records) (versionLayout (records ++ [entry])) := by
    simpa [version_with_unopened_fields, version_with_complete_fields] using hrest
  refine ⟨k + 1, ?_, by omega, ?_⟩
  · exact PFStableVersionTrace.next (tree_selector_matches_fuel_committed records entry.val)
      (fun term hm => pfScan_committed_records records term none hm)
      (choose_new_version_slot records entry.val)
      (open_new_version_layout records) hrest'
  · rw [entry.property] at hbound
    omega

def PFStableAdaptiveStep (width : Nat) (desired : List Bool) (old : Option (List Bool)) (a b : Term) : Prop :=
  TreeAdaptiveNativeStep width desired a b ∧ pfScanVersion width none a = old

inductive PFStableAdaptiveTrace (width : Nat) (desired : List Bool) (old : Option (List Bool)) :
    Nat → Term → Term → Prop where
  | zero (a : Term) : PFStableAdaptiveTrace width desired old 0 a a
  | next {n : Nat} {a b c : Term} : PFStableAdaptiveStep width desired old a b →
      PFStableAdaptiveTrace width desired old n b c → PFStableAdaptiveTrace width desired old (n + 1) a c

theorem pfStableAdaptiveTrace_trans {width : Nat} {desired : List Bool} {old : Option (List Bool)}
    {n m : Nat} {a b c : Term}
    (h1 : PFStableAdaptiveTrace width desired old n a b)
    (h2 : PFStableAdaptiveTrace width desired old m b c) :
    PFStableAdaptiveTrace width desired old (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | next hab _ ih =>
      have r := PFStableAdaptiveTrace.next hab (ih h2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem pf_lift_opening_stable_value {width n : Nat}
    {records : List {bits : List Bool // bits.length = width}} {old final : Term}
    (trace : ClosedOpeningTrace n old final) :
    ∀ shape term path fuel desired,
      FuelAgreement fuel width desired shape → PFStableVersionValue records shape →
      layoutMatches shape term → subLayout shape path = some .unopened →
      termAt term (physicalPath path) = some old →
      chooseSVersion fuel width desired term = some (physicalPath path) →
      ∃ target out, openLayoutAt shape path = some target ∧ layoutMatches target out ∧
        replaceTermAt term (physicalPath path) final = some out ∧
        PFStableAdaptiveTrace width desired (newestRecords records none) n term out := by
  induction trace with
  | @finish a b hchosen hopen =>
      intro shape term path fuel desired hagree hstable hmatch hslot hat hchoose
      obtain ⟨relpath, hlocal, hdir⟩ := hchosen
      obtain ⟨target, out, hopenLayout, hout, hmatchout, _⟩ :=
        opened_slot_step_updates_layout path shape term a b relpath hmatch hslot hat hdir hopen
      obtain ⟨out', hreplace, hout'⟩ := directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
      have heq : out = out' := directed_step_unique hout out' hout'
      subst out'
      have htree : chooseSVersionTree width desired term = some (physicalPath path) := by
        rw [hagree term hmatch, hchoose]
      have hstep : PFStableAdaptiveStep width desired (newestRecords records none) term out :=
        ⟨⟨path, htree, a, relpath, hat, hlocal, hout⟩, hstable term hmatch⟩
      exact ⟨target, out, hopenLayout, hmatchout, hreplace,
        PFStableAdaptiveTrace.next hstep (PFStableAdaptiveTrace.zero out)⟩
  | @more n a b c hchosen hclosed _ ih =>
      intro shape term path fuel desired hagree hstable hmatch hslot hat hchoose
      obtain ⟨relpath, hlocal, hdir⟩ := hchosen
      obtain ⟨middle, hmiddle, hatMiddle, hchooseMiddle, hmatchMiddle⟩ :=
        restarted_selector_preserves_target shape term a b path relpath fuel width desired
          hmatch hslot hat hdir hclosed hchoose
      obtain ⟨middle', hreplaceFirst, hmiddle'⟩ :=
        directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
      have heq : middle = middle' := directed_step_unique hmiddle middle' hmiddle'
      subst middle'
      obtain ⟨target, out, hopenLayout, hmatchout, hreplaceRest, htrace⟩ :=
        ih shape middle path fuel desired hagree hstable hmatchMiddle hslot hatMiddle hchooseMiddle
      have hreplace : replaceTermAt term (physicalPath path) c = some out := by
        rw [← replace_same_path_overwrites (physicalPath path) term b middle c hreplaceFirst]
        exact hreplaceRest
      have htree : chooseSVersionTree width desired term = some (physicalPath path) := by
        rw [hagree term hmatch, hchoose]
      have hstep : PFStableAdaptiveStep width desired (newestRecords records none) term middle :=
        ⟨⟨path, htree, a, relpath, hat, hlocal, hmiddle⟩, hstable term hmatch⟩
      exact ⟨target, out, hopenLayout, hmatchout, hreplace,
        PFStableAdaptiveTrace.next hstep htrace⟩

theorem pf_canonical_selected_opening_stable {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (shape target : Layout) (path : List Bool) (d fuel : Nat) (desired : List Bool)
    (hagree : FuelAgreement fuel width desired shape) (hstable : PFStableVersionValue records shape)
    (hopen : openLayoutAt shape path = some target)
    (hchoose : chooseSVersion fuel width desired (layoutTerm shape (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath path)) :
    ∃ k, (k = 6 ∨ k = 7) ∧ PFStableAdaptiveTrace width desired (newestRecords records none) k
      (layoutTerm shape (phaseAt d).1 (phaseAt d).2)
      (layoutTerm target (phaseAt d).1 (phaseAt d).2) := by
  let p := phaseAt d
  let q := advancePhase path.length p
  have hp : goodPhase p := phase_at_good d
  have hq : goodPhase q := advance_phase_good path.length p hp
  have hslot : subLayout shape path = some .unopened := open_layout_targets_unopened path shape target hopen
  have hat : termAt (layoutTerm shape p.1 p.2) (physicalPath path) = some (phaseBase q) :=
    (selected_slot_is_generator shape target path p hp hopen).2
  have hmatch : layoutMatches shape (layoutTerm shape p.1 p.2) := finite_layout_decodes shape p.1 p.2 hp.1 hp.2
  obtain ⟨k, hk, htrace⟩ := good_phase_opening_trace q hq
  obtain ⟨target', out, hopen', _, hreplace, hglobal⟩ :=
    pf_lift_opening_stable_value htrace shape (layoutTerm shape p.1 p.2)
      path fuel desired hagree hstable hmatch hslot hat hchoose
  have htarget : target' = target := by rw [hopen] at hopen'; exact (Option.some.inj hopen').symm
  subst target'
  have hcanonical := canonical_layout_replace path shape target p hp hopen
  have hout : out = layoutTerm target p.1 p.2 := by rw [hcanonical] at hreplace; exact (Option.some.inj hreplace).symm
  subst out
  exact ⟨k, hk, hglobal⟩

theorem pf_stable_version_trace_native {width : Nat}
    {records : List {bits : List Bool // bits.length = width}} {fuel : Nat} {desired : List Bool}
    {n : Nat} {a b : Layout} (trace : PFStableVersionTrace records fuel desired n a b) (d : Nat) :
    ∃ k, PFStableAdaptiveTrace width desired (newestRecords records none) k
        (layoutTerm a (phaseAt d).1 (phaseAt d).2) (layoutTerm b (phaseAt d).1 (phaseAt d).2) ∧
      6 * n ≤ k ∧ k ≤ 7 * n := by
  induction trace with
  | done _ => exact ⟨0, PFStableAdaptiveTrace.zero _, by simp, by simp⟩
  | @next n a b c path hagree hstable hchoose hopen _ ih =>
      have hS : chooseSVersion fuel width desired (layoutTerm a (phaseAt d).1 (phaseAt d).2) =
          some (physicalPath path) := by
        rw [choose_s_version_simulates_layout fuel width desired a (phaseAt d) (phase_at_good d), hchoose]
        rfl
      obtain ⟨first, hfirst, hrun⟩ :=
        pf_canonical_selected_opening_stable records a b path d fuel desired hagree hstable hopen hS
      obtain ⟨last, hlast, hlower, hupper⟩ := ih
      refine ⟨first + last, pfStableAdaptiveTrace_trans hrun hlast, ?_, ?_⟩
      · cases hfirst <;> omega
      · cases hfirst <;> omega

def pfVerTerm {width : Nat} (records : List {bits : List Bool // bits.length = width}) (d : Nat) : Term :=
  layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2

theorem pfVerTerm_scan {width : Nat} (records : List {bits : List Bool // bits.length = width}) (d : Nat) :
    pfScanVersion width none (pfVerTerm records d) = newestRecords records none := by
  have hp := phase_at_good d
  exact pfScan_committed_records records _ none (finite_layout_decodes (versionLayout records) _ _ hp.1 hp.2)

theorem pf_fully_stable_version_append {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (d : Nat) :
    ∃ k, PFStableAdaptiveTrace width entry.val (newestRecords records none) k
        (pfVerTerm records d) (pfVerTerm (records ++ [entry]) d) ∧
      6 ≤ k ∧ k ≤ 7 * (2 * width + 2) := by
  obtain ⟨n, htrace, hnlo, hnhi⟩ := pf_stable_version_append_complete records entry
  obtain ⟨k, hreal, klo, khi⟩ := pf_stable_version_trace_native htrace d
  exact ⟨k, hreal, by omega, by omega⟩


/-! ## Section 3: Regular Halting Predicate `pfRootHalt` & 11-State Bottom-Up Tree Automaton -/

def pfRootHalt : Term → Bool
  | .app _ hub => haltObserved hub
  | _ => false

structure BottomUpTreeAutomaton (Q : Type) where
  leafState : Q
  varState : Nat → Q
  appState : Q → Q → Q
  accept : Q → Bool

namespace BottomUpTreeAutomaton

def eval {Q : Type} (A : BottomUpTreeAutomaton Q) : Term → Q
  | .s => A.leafState
  | .var i => A.varState i
  | .app l r => A.appState (A.eval l) (A.eval r)

def evalAccepts {Q : Type} (A : BottomUpTreeAutomaton Q) (t : Term) : Bool :=
  A.accept (A.eval t)

end BottomUpTreeAutomaton

structure PFHaltFeatures where
  isS : Bool
  isS1 : Bool
  isS1F : Bool
  isS2 : Bool
  isF : Bool
  isHaltHub : Bool
  isRootHalt : Bool
  deriving DecidableEq, Repr

def pfIsSTerm : Term → Bool
  | .s => true
  | _ => false

def pfIsS1Term : Term → Bool
  | .app .s _ => true
  | _ => false

def pfIsS1FTerm : Term → Bool
  | .app .s x => flagValue x
  | _ => false

def pfIsS2Shape : Term → Bool
  | .app (.app .s _) _ => true
  | _ => false

def pfFeaturesOf (t : Term) : PFHaltFeatures :=
  { isS := pfIsSTerm t
    isS1 := pfIsS1Term t
    isS1F := pfIsS1FTerm t
    isS2 := pfIsS2Shape t
    isF := flagValue t
    isHaltHub := haltObserved t
    isRootHalt := pfRootHalt t }

def pfCombineFeatures (fl fr : PFHaltFeatures) : PFHaltFeatures :=
  { isS := false
    isS1 := fl.isS
    isS1F := fl.isS && fr.isF
    isS2 := fl.isS1
    isF := fl.isS1 && fr.isS2
    isHaltHub := fl.isS1F && fr.isS2
    isRootHalt := fr.isHaltHub }

theorem pf_flagValue_eq_s1_s2 (l r : Term) :
    flagValue (l ⋅ r) = (pfIsS1Term l && pfIsS2Shape r) := by
  cases l with
  | s => rfl
  | var _ => rfl
  | app ll lr =>
      cases ll with
      | s =>
          cases r with
          | s => rfl
          | var _ => rfl
          | app rl rr =>
              cases rl with
              | s => rfl
              | var _ => rfl
              | app rll _ => cases rll <;> rfl
      | var _ => rfl
      | app _ _ => rfl

theorem pf_haltObserved_eq_s1f_s2 (l r : Term) :
    haltObserved (l ⋅ r) = (pfIsS1FTerm l && pfIsS2Shape r) := by
  cases l with
  | s => rfl
  | var _ => rfl
  | app ll lr =>
      cases ll with
      | s =>
          cases r with
          | s => simp [haltObserved, parseFrame, pfIsS1FTerm, pfIsS2Shape]
          | var _ => simp [haltObserved, parseFrame, pfIsS1FTerm, pfIsS2Shape]
          | app rl rr =>
              cases rl with
              | s => simp [haltObserved, parseFrame, pfIsS1FTerm, pfIsS2Shape]
              | var _ => simp [haltObserved, parseFrame, pfIsS1FTerm, pfIsS2Shape]
              | app rll _ =>
                  cases rll <;> simp [haltObserved, parseFrame, pfIsS1FTerm, pfIsS2Shape]
      | var _ => rfl
      | app _ _ => rfl

theorem pfFeaturesOf_app (l r : Term) :
    pfFeaturesOf (l ⋅ r) = pfCombineFeatures (pfFeaturesOf l) (pfFeaturesOf r) := by
  unfold pfFeaturesOf pfCombineFeatures
  have h1 : pfIsSTerm (l ⋅ r) = false := rfl
  have h2 : pfIsS1Term (l ⋅ r) = pfIsSTerm l := by cases l <;> rfl
  have h3 : pfIsS1FTerm (l ⋅ r) = (pfIsSTerm l && flagValue r) := by cases l <;> rfl
  have h4 : pfIsS2Shape (l ⋅ r) = pfIsS1Term l := by
    cases l with
    | s => rfl
    | var _ => rfl
    | app ll _ => cases ll <;> rfl
  have h5 := pf_flagValue_eq_s1_s2 l r
  have h6 := pf_haltObserved_eq_s1f_s2 l r
  have h7 : pfRootHalt (l ⋅ r) = haltObserved r := rfl
  rw [h1, h2, h3, h4, h5, h6, h7]

def pfStateFeatures : Fin 11 → PFHaltFeatures
  | ⟨0, _⟩  => ⟨true,  false, false, false, false, false, false⟩
  | ⟨1, _⟩  => ⟨false, true,  false, false, false, false, false⟩
  | ⟨2, _⟩  => ⟨false, true,  true,  false, false, false, false⟩
  | ⟨3, _⟩  => ⟨false, true,  true,  false, false, false, true⟩
  | ⟨4, _⟩  => ⟨false, false, false, true,  false, false, false⟩
  | ⟨5, _⟩  => ⟨false, false, false, true,  true,  false, false⟩
  | ⟨6, _⟩  => ⟨false, false, false, true,  true,  false, true⟩
  | ⟨7, _⟩  => ⟨false, false, false, true,  true,  true,  false⟩
  | ⟨8, _⟩  => ⟨false, false, false, true,  true,  true,  true⟩
  | ⟨9, _⟩  => ⟨false, false, false, false, false, false, false⟩
  | ⟨10, _⟩ => ⟨false, false, false, false, false, false, true⟩

def pfEncodeFeatures (f : PFHaltFeatures) : Fin 11 :=
  if f.isS then 0
  else if f.isS1 then
    if f.isS1F then (if f.isRootHalt then 3 else 2)
    else 1
  else if f.isS2 then
    if f.isF then
      if f.isHaltHub then (if f.isRootHalt then 8 else 7)
      else (if f.isRootHalt then 6 else 5)
    else 4
  else
    if f.isRootHalt then 10 else 9

def pfHaltAutomaton : BottomUpTreeAutomaton (Fin 11) where
  leafState := 0
  varState := fun _ => 9
  appState := fun ql qr => pfEncodeFeatures (pfCombineFeatures (pfStateFeatures ql) (pfStateFeatures qr))
  accept := fun q => (pfStateFeatures q).isRootHalt

theorem pfHaltAutomaton_app_coherent :
    ∀ ql qr : Fin 11,
      pfStateFeatures (pfHaltAutomaton.appState ql qr) =
        pfCombineFeatures (pfStateFeatures ql) (pfStateFeatures qr) := by
  decide

theorem pfHaltAutomaton_eval_features (t : Term) :
    pfStateFeatures (pfHaltAutomaton.eval t) = pfFeaturesOf t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app l r ihl ihr =>
      calc
        pfStateFeatures (pfHaltAutomaton.eval (l ⋅ r))
            = pfStateFeatures (pfHaltAutomaton.appState (pfHaltAutomaton.eval l) (pfHaltAutomaton.eval r)) := rfl
        _ = pfCombineFeatures (pfStateFeatures (pfHaltAutomaton.eval l)) (pfStateFeatures (pfHaltAutomaton.eval r)) :=
              pfHaltAutomaton_app_coherent (pfHaltAutomaton.eval l) (pfHaltAutomaton.eval r)
        _ = pfCombineFeatures (pfFeaturesOf l) (pfFeaturesOf r) := by rw [ihl, ihr]
        _ = pfFeaturesOf (l ⋅ r) := (pfFeaturesOf_app l r).symm

theorem pfHaltAutomaton_accepts_eq_pfRootHalt (t : Term) :
    pfHaltAutomaton.evalAccepts t = pfRootHalt t :=
  congrArg PFHaltFeatures.isRootHalt (pfHaltAutomaton_eval_features t)


/-! ## Section 4: Program-Free Root-Restarted Selector `pfSelect` & Generic Lifting -/

def contractRedex : Term → Option Term
  | .app (.app (.app .s x) y) z => some ((x ⋅ z) ⋅ (y ⋅ z))
  | _ => none

def contractAt : Term → List Bool → Option Term
  | t, [] => contractRedex t
  | .app l r, false :: p => (contractAt l p).map (· ⋅ r)
  | .app l r, true :: p => (contractAt r p).map (l ⋅ ·)
  | _, _ :: _ => none

theorem contractRedex_sound {t t' : Term} (h : contractRedex t = some t') : Step t t' := by
  unfold contractRedex at h
  split at h <;> simp at h
  subst t'
  exact Step.root _ _ _

theorem contractAt_sound : ∀ {t : Term} {path : List Bool} {t' : Term},
    contractAt t path = some t' → Step t t'
  | t, [], _, h => contractRedex_sound (by simpa [contractAt] using h)
  | .app l r, false :: p, _, h => by
      unfold contractAt at h
      cases hl : contractAt l p with
      | none => simp [hl] at h
      | some l' =>
          simp only [hl, Option.map, Option.some.injEq] at h
          subst h
          exact Step.left (contractAt_sound hl)
  | .app l r, true :: p, _, h => by
      unfold contractAt at h
      cases hr : contractAt r p with
      | none => simp [hr] at h
      | some r' =>
          simp only [hr, Option.map, Option.some.injEq] at h
          subst h
          exact Step.right (contractAt_sound hr)
  | .s, _ :: _, _, h => by simp [contractAt] at h
  | .var _, _ :: _, _, h => by simp [contractAt] at h

theorem directedStep_to_contractAt {path : List Bool} {a b : Term}
    (h : DirectedStep path a b) : contractAt a path = some b := by
  induction h with
  | root x y z => rfl
  | left _ ih => simp [contractAt, ih]
  | right _ ih => simp [contractAt, ih]

def pfHubPath : List Bool := [true]
def pfFlagPath : List Bool := [true, false, true]
def pfPayloadPath : List Bool := [true, true, false, true]
def pfProgRingPath : List Bool := [true, true, false, true, false, true]
def pfQueueRootPath : List Bool := [true, true, false, true, true, false, true]
def pfLeftChildPath : List Bool := [false, true]
def pfRightChildPath : List Bool := [true, false, true]

def pfSelectOpeningAt (root : Term) (path : List Bool) : Option (List Bool) := do
  let focus ← termAt root path
  let rel ← nextOpeningAddress focus
  some (path ++ rel)

def pfSelectVersionWriteAt (root : Term) (verPath : List Bool) (width : Nat) (desired : List Bool) :
    Option (List Bool) := do
  let verTerm ← termAt root verPath
  let slot ← chooseSVersionTree width desired verTerm
  pfSelectOpeningAt root (verPath ++ slot)

structure QueueScan where
  consuming : Option (List Bool × Bool)
  unconsumed : Option (List Bool × Bool)
  staging : Option (List Bool × Bool)
  uninit : Option (List Bool)
  tailPath : List Bool
  deriving DecidableEq, Repr

def shiftPathBool (o : Option (List Bool × Bool)) : Option (List Bool × Bool) :=
  o.map (fun pb => (pfRightChildPath ++ pb.1, pb.2))

def shiftOptPath (o : Option (List Bool)) : Option (List Bool) :=
  o.map (fun p => pfRightChildPath ++ p)

def scanQueue : Term → QueueScan
  | .app (.app .s qVer) (.app (.app .s rest) _) =>
      let sub := scanQueue rest
      let nextTail := pfRightChildPath ++ sub.tailPath
      match pfScanVersion 3 none qVer with
      | none =>
          { consuming := shiftPathBool sub.consuming
            unconsumed := shiftPathBool sub.unconsumed
            staging := shiftPathBool sub.staging
            uninit := some pfLeftChildPath
            tailPath := nextTail }
      | some [false, true, b] =>
          { consuming := shiftPathBool sub.consuming
            unconsumed := shiftPathBool sub.unconsumed
            staging := some (pfLeftChildPath, b)
            uninit := shiftOptPath sub.uninit
            tailPath := nextTail }
      | some [false, false, b] =>
          { consuming := shiftPathBool sub.consuming
            unconsumed := some (pfLeftChildPath, b)
            staging := shiftPathBool sub.staging
            uninit := shiftOptPath sub.uninit
            tailPath := nextTail }
      | some [true, false, b] =>
          { consuming := some (pfLeftChildPath, b)
            unconsumed := shiftPathBool sub.unconsumed
            staging := shiftPathBool sub.staging
            uninit := shiftOptPath sub.uninit
            tailPath := nextTail }
      | _ =>
          { consuming := shiftPathBool sub.consuming
            unconsumed := shiftPathBool sub.unconsumed
            staging := shiftPathBool sub.staging
            uninit := shiftOptPath sub.uninit
            tailPath := nextTail }
  | _ => ⟨none, none, none, none, []⟩

structure TemplateScan where
  firstIdle : Option (List Bool × Bool)
  firstArmed : Option (List Bool × Bool)
  firstAppending : Option (List Bool × Bool)
  deriving DecidableEq, Repr

def scanTemplates : Term → TemplateScan
  | .app (.app .s tVer) (.app (.app .s rest) _) =>
      let sub := scanTemplates rest
      match pfScanVersion 3 none tVer with
      | some [false, false, sbit] =>
          { firstIdle := some (pfLeftChildPath, sbit)
            firstArmed := shiftPathBool sub.firstArmed
            firstAppending := shiftPathBool sub.firstAppending }
      | some [true, false, sbit] =>
          { firstIdle := shiftPathBool sub.firstIdle
            firstArmed := some (pfLeftChildPath, sbit)
            firstAppending := shiftPathBool sub.firstAppending }
      | some [true, true, sbit] =>
          { firstIdle := shiftPathBool sub.firstIdle
            firstArmed := shiftPathBool sub.firstArmed
            firstAppending := some (pfLeftChildPath, sbit) }
      | _ =>
          { firstIdle := shiftPathBool sub.firstIdle
            firstArmed := shiftPathBool sub.firstArmed
            firstAppending := shiftPathBool sub.firstAppending }
  | _ => ⟨none, none, none⟩

structure PhaseEntry where
  verPath : List Bool
  tListPath : List Bool
  status : Option (List Bool)
  templates : TemplateScan
  deriving DecidableEq, Repr

def shiftPhaseEntry (e : PhaseEntry) : PhaseEntry :=
  { e with
    verPath := pfRightChildPath ++ e.verPath
    tListPath := pfRightChildPath ++ e.tListPath }

def scanPhases : Term → List PhaseEntry
  | .app (.app .s (.app (.app .s pVer) (.app (.app .s tList) _))) (.app (.app .s rest) _) =>
      { verPath := [false, true, false, true]
        tListPath := [false, true, true, false, true]
        status := pfScanVersion 2 none pVer
        templates := scanTemplates tList } :: (scanPhases rest).map shiftPhaseEntry
  | _ => []

def findIdxPred {α : Type} (p : α → Bool) : List α → Option (Nat × α)
  | [] => none
  | x :: xs => if p x then some (0, x) else (findIdxPred p xs).map (fun iy => (iy.1 + 1, iy.2))

def listGetOpt {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => listGetOpt xs i

inductive PFDecision where
  | openSlot (path : List Bool)
  | writeVer (verPath : List Bool) (width : Nat) (desired : List Bool)
  | none
  deriving DecidableEq, Repr

def pfReadState (root : Term) : Option (List PhaseEntry × QueueScan) := do
  let hub ← termAt root pfHubPath
  let (_, payload, _) ← parseFrame hub
  let (progRing, queueRoot, _) ← parseFrame payload
  some (scanPhases progRing, scanQueue queueRoot)

def pfDecideAction (phases : List PhaseEntry) (q : QueueScan) : PFDecision :=
  match findIdxPred (fun pe => pe.status == some [true, true]) phases with
  | some (hIdx, hEntry) =>
      match q.consuming with
      | some (cRelPath, b) =>
          .writeVer (pfQueueRootPath ++ cRelPath) 3 [true, true, b]
      | none =>
          if phases.length == 1 then
            .writeVer (pfProgRingPath ++ hEntry.verPath) 2 [true, false]
          else
            let nxtIdx := (hIdx + 1) % phases.length
            match listGetOpt phases nxtIdx with
            | some nxtEntry =>
                if nxtEntry.status == some [true, false] then
                  .writeVer (pfProgRingPath ++ hEntry.verPath) 2 [false, false]
                else
                  .writeVer (pfProgRingPath ++ nxtEntry.verPath) 2 [true, false]
            | none => .none
  | none =>
      match findIdxPred (fun pe => pe.status == some [true, false]) phases with
      | none => .none
      | some (_, actEntry) =>
          let tmpl := actEntry.templates
          match q.consuming with
          | none =>
              match q.unconsumed with
              | none => .openSlot pfFlagPath
              | some (uRelPath, b) =>
                  if b then
                    match tmpl.firstIdle with
                    | some (tRelPath, sbit) =>
                        .writeVer (pfProgRingPath ++ actEntry.tListPath ++ tRelPath) 3 [true, false, sbit]
                    | none =>
                        .writeVer (pfQueueRootPath ++ uRelPath) 3 [true, false, true]
                  else
                    .writeVer (pfQueueRootPath ++ uRelPath) 3 [true, false, false]
          | some _ =>
              match tmpl.firstAppending with
              | some (tRelPath, sbit) =>
                  match q.staging with
                  | some _ =>
                      .writeVer (pfProgRingPath ++ actEntry.tListPath ++ tRelPath) 3 [false, false, sbit]
                  | none =>
                      match q.uninit with
                      | some uInitRelPath =>
                          .writeVer (pfQueueRootPath ++ uInitRelPath) 3 [false, true, sbit]
                      | none =>
                          .openSlot (pfQueueRootPath ++ q.tailPath)
              | none =>
                  match q.staging with
                  | some (stRelPath, sbit) =>
                      .writeVer (pfQueueRootPath ++ stRelPath) 3 [false, false, sbit]
                  | none =>
                      match tmpl.firstArmed with
                      | some (tRelPath, sbit) =>
                          .writeVer (pfProgRingPath ++ actEntry.tListPath ++ tRelPath) 3 [true, true, sbit]
                      | none =>
                          .writeVer (pfProgRingPath ++ actEntry.verPath) 2 [true, true]

def pfSelectAddress (root : Term) : Option (List Bool) := do
  let (phases, q) ← pfReadState root
  match pfDecideAction phases q with
  | .openSlot path => pfSelectOpeningAt root path
  | .writeVer verPath width desired => pfSelectVersionWriteAt root verPath width desired
  | .none => none

inductive PFOutcome where
  | halt : PFOutcome
  | step : Term → PFOutcome
  | stuck : PFOutcome
  deriving DecidableEq, Repr

/-- **100% Program-Free Root-Restarted Selector `pfSelect`**:
    Takes ONLY the bare unannotated `Term` `t` (ZERO `P` or `w` parameter,
    ZERO UTM states, ZERO tag rules!). -/
def pfSelect (t : Term) : PFOutcome :=
  if pfRootHalt t then .halt
  else
    match pfSelectAddress t with
    | some path =>
        match contractAt t path with
        | some t' => .step t'
        | none => .stuck
    | none => .stuck

theorem pfSelect_step_sound {t t' : Term} (h : pfSelect t = .step t') : Step t t' := by
  unfold pfSelect at h
  cases hh : pfRootHalt t with
  | true => simp [hh] at h
  | false =>
      simp only [hh, Bool.false_eq_true, ↓reduceIte] at h
      cases ha : pfSelectAddress t with
      | none => simp [ha] at h
      | some path =>
          simp only [ha] at h
          cases hc : contractAt t path with
          | none => simp [hc] at h
          | some next =>
              simp only [hc, PFOutcome.step.injEq] at h
              subst t'
              exact contractAt_sound hc

theorem pfSelect_halt_iff (t : Term) : pfSelect t = .halt ↔ pfRootHalt t = true := by
  unfold pfSelect
  cases hh : pfRootHalt t with
  | true => simp
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h
        cases ha : pfSelectAddress t with
        | none => simp [ha] at h
        | some path =>
            simp only [ha] at h
            cases hc : contractAt t path <;> simp [hc] at h
      · intro h
        cases h

theorem pfSelect_of_directedStep {a b : Term} {path : List Bool}
    (hhalt : pfRootHalt a = false)
    (hsel : pfSelectAddress a = some path)
    (hdir : DirectedStep path a b) :
    pfSelect a = .step b := by
  unfold pfSelect
  rw [hhalt]
  simp [hsel, directedStep_to_contractAt hdir]

inductive PFTrace : Nat → Term → Term → Prop where
  | zero (a : Term) : PFTrace 0 a a
  | next {n : Nat} {a b c : Term} :
      pfSelect a = .step b → PFTrace n b c → PFTrace (n + 1) a c

theorem pfTrace_trans {n m : Nat} {a b c : Term}
    (h1 : PFTrace n a b) (h2 : PFTrace m b c) : PFTrace (n + m) a c := by
  induction h1 with
  | zero _ => simpa using h2
  | next hs _ ih =>
      have r := PFTrace.next hs (ih h2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem pfTrace_reduces {k : Nat} {a b : Term} (h : PFTrace k a b) : Reduces a b := by
  induction h with
  | zero x => exact Reduces.refl x
  | next hs _ ih => exact Reduces.next (pfSelect_step_sound hs) ih

theorem pfTrace_exactSteps {k : Nat} {a b : Term} (h : PFTrace k a b) : ExactSteps k a b := by
  induction h with
  | zero x => exact ExactSteps.zero x
  | next hs _ ih => exact ExactSteps.next (pfSelect_step_sound hs) ih

theorem pfTrace_unique {k : Nat} {a b : Term} (h : PFTrace k a b) :
    ∀ c, PFTrace k a c → b = c := by
  induction h with
  | zero _ =>
      intro c hc
      cases hc
      rfl
  | @next n a b _ hs1 _ ih =>
      intro c hc
      cases hc with
      | @next _ _ mid _ hs2 rest2 =>
          rw [hs1] at hs2
          have hbm : b = mid := PFOutcome.step.inj hs2
          subst mid
          exact ih c rest2

theorem pfTrace_split (n m : Nat) {a b : Term} (h : PFTrace (n + m) a b) :
    ∃ mid, PFTrace n a mid ∧ PFTrace m mid b := by
  induction n generalizing a b with
  | zero =>
      exact ⟨a, PFTrace.zero a, by simpa using h⟩
  | succ n ih =>
      have heq : (n + 1) + m = (n + m) + 1 := by omega
      rw [heq] at h
      cases h with
      | next hs rest =>
          obtain ⟨mid, hpre, hsuf⟩ := ih rest
          exact ⟨mid, PFTrace.next hs hpre, hsuf⟩

theorem pf_halt_cannot_precede_longer_trace {k M : Nat} {start reached checkpoint : Term}
    (hreach : PFTrace k start reached)
    (hhalt : pfRootHalt reached = true)
    (hlonger : PFTrace M start checkpoint)
    (hlt : k < M) : False := by
  have heq : M = k + ((M - k - 1) + 1) := by omega
  rw [heq] at hlonger
  obtain ⟨mid, hpre, hsuf⟩ := pfTrace_split k ((M - k - 1) + 1) hlonger
  have hsame : reached = mid := pfTrace_unique hreach mid hpre
  subst mid
  cases hsuf with
  | next hs _ =>
      have hh := (pfSelect_halt_iff reached).mpr hhalt
      rw [hh] at hs
      cases hs

/-- Generic slot-opening lifting lemma: lifts `good_phase_opening_trace` at any unopened
    generator slot `slotPath` inside context `C` into a `PFTrace` of `6` or `7` steps. -/
theorem lift_closed_opening_to_pfTrace (C : Term → Term) (slotPath : List Bool) (sd : Nat)
    (hat : ∀ u, termAt (C u) slotPath = some u)
    (hdir : ∀ p u u', DirectedStep p u u' → DirectedStep (slotPath ++ p) (C u) (C u'))
    (hhalt : ∀ u, parseFrame u = none → pfRootHalt (C u) = false)
    (hdecide : ∀ u, parseFrame u = none →
      ∃ phases q, pfReadState (C u) = some (phases, q) ∧ pfDecideAction phases q = .openSlot slotPath) :
    ∃ k, (k = 6 ∨ k = 7) ∧
      PFTrace k (C (depthBase sd))
        (C (layoutTerm (.opened .unopened .unopened) (phaseAt sd).1 (phaseAt sd).2)) := by
  obtain ⟨k, hk, htrace⟩ := good_phase_opening_trace (phaseAt sd) (phase_at_good sd)
  have haux : ∀ {n : Nat} {a b : Term},
      parseFrame a = none → ClosedOpeningTrace n a b → PFTrace n (C a) (C b) := by
    intro n a b haClosed tr
    induction tr with
    | @finish a b hchosen _ =>
        obtain ⟨rel, hlocal, hd⟩ := hchosen
        obtain ⟨phases, q, hread, hact⟩ := hdecide a haClosed
        have hsel : pfSelectAddress (C a) = some (slotPath ++ rel) := by
          unfold pfSelectAddress
          rw [hread]
          simp [hact, pfSelectOpeningAt, hat a, hlocal]
        have hstep := pfSelect_of_directedStep (hhalt a haClosed) hsel (hdir rel a b hd)
        exact PFTrace.next hstep (PFTrace.zero (C b))
    | @more n a b c hchosen hbClosed _ ih =>
        obtain ⟨rel, hlocal, hd⟩ := hchosen
        obtain ⟨phases, q, hread, hact⟩ := hdecide a haClosed
        have hsel : pfSelectAddress (C a) = some (slotPath ++ rel) := by
          unfold pfSelectAddress
          rw [hread]
          simp [hact, pfSelectOpeningAt, hat a, hlocal]
        have hstep := pfSelect_of_directedStep (hhalt a haClosed) hsel (hdir rel a b hd)
        exact PFTrace.next hstep (ih hbClosed)
  exact ⟨k, hk, haux (depth_base_closed sd) htrace⟩

/-- Generic version-append lifting lemma: lifts `pf_fully_stable_version_append` at any
    version-chain slot `verPath` inside context `C` into a `PFTrace` of `6 ≤ k ≤ 7*(2*w+2)` steps. -/
theorem lift_stable_version_append_to_pfTrace {width : Nat}
    (C : Term → Term) (verPath : List Bool)
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width})
    (vd : Nat)
    (hat : ∀ v, termAt (C v) verPath = some v)
    (hdir : ∀ p v v', DirectedStep p v v' → DirectedStep (verPath ++ p) (C v) (C v'))
    (hhalt : ∀ v, pfRootHalt (C v) = false)
    (hdecide : ∀ v, pfScanVersion width none v = newestRecords records none →
      ∃ phases q, pfReadState (C v) = some (phases, q) ∧
        pfDecideAction phases q = .writeVer verPath width entry.val) :
    ∃ k, 6 ≤ k ∧ k ≤ 7 * (2 * width + 2) ∧
      PFTrace k (C (pfVerTerm records vd)) (C (pfVerTerm (records ++ [entry]) vd)) := by
  obtain ⟨k, htrace, klo, khi⟩ := pf_fully_stable_version_append records entry vd
  have haux : ∀ {n : Nat} {a b : Term},
      PFStableAdaptiveTrace width entry.val (newestRecords records none) n a b →
      PFTrace n (C a) (C b) := by
    intro n a b tr
    induction tr with
    | zero x => exact PFTrace.zero (C x)
    | @next n a b c hstep _ ih =>
        obtain ⟨⟨slot, hchoose, focus, rel, hfocusAt, hlocal, hd⟩, hscan⟩ := hstep
        obtain ⟨phases, q, hread, hact⟩ := hdecide a hscan
        have hfocusRoot : termAt (C a) (verPath ++ physicalPath slot) = some focus := by
          rw [pf_termAt_append, hat a]
          exact hfocusAt
        have hsel : pfSelectAddress (C a) = some (verPath ++ physicalPath slot ++ rel) := by
          unfold pfSelectAddress
          rw [hread]
          simp [hact, pfSelectVersionWriteAt, pfSelectOpeningAt, hat a, hchoose, hfocusRoot, hlocal,
            List.append_assoc]
        have hdRoot : DirectedStep (verPath ++ physicalPath slot ++ rel) (C a) (C b) := by
          simpa [List.append_assoc] using hdir (physicalPath slot ++ rel) a b hd
        exact PFTrace.next (pfSelect_of_directedStep (hhalt a) hsel hdRoot) ih
  exact ⟨k, klo, khi, haux htrace⟩


/-! ## Section 5: Pure-`S` CTS Layout, Encoder, Polynomial Size Bound, and Scanners -/

abbrev Rec2 := {bits : List Bool // bits.length = 2}
abbrev Rec3 := {bits : List Bool // bits.length = 3}

def recInactive : Rec2 := ⟨[false, false], rfl⟩
def recActive   : Rec2 := ⟨[true, false], rfl⟩
def recHandoff  : Rec2 := ⟨[true, true], rfl⟩

def recIdle      (b : Bool) : Rec3 := ⟨[false, false, b], rfl⟩
def recArmed     (b : Bool) : Rec3 := ⟨[true, false, b], rfl⟩
def recAppending (b : Bool) : Rec3 := ⟨[true, true, b], rfl⟩

def recStaging    (b : Bool) : Rec3 := ⟨[false, true, b], rfl⟩
def recUnconsumed (b : Bool) : Rec3 := ⟨[false, false, b], rfl⟩
def recConsuming  (b : Bool) : Rec3 := ⟨[true, false, b], rfl⟩
def recConsumed   (b : Bool) : Rec3 := ⟨[true, true, b], rfl⟩

structure PhaseState where
  pRecs : List Rec2
  tCells : List (List Rec3)

def templateListLayout : List (List Rec3) → Layout
  | [] => .unopened
  | recs :: rest => .opened (versionLayout recs) (templateListLayout rest)

def templateListTerm : List (List Rec3) → Nat → Term
  | [], d => depthBase d
  | recs :: rest, d => frameTerm (pfVerTerm recs (d + 1)) (templateListTerm rest (d + 1)) (depthJunk d)

theorem templateListLayout_term (cells : List (List Rec3)) :
    ∀ d, layoutTerm (templateListLayout cells) (phaseAt d).1 (phaseAt d).2 = templateListTerm cells d := by
  induction cells with
  | nil => intro _; rfl
  | cons recs rest ih =>
      intro d
      rw [templateListLayout, layout_opened_phase _ _ _ (phase_at_good d)]
      change frameTerm (pfVerTerm recs (d + 1))
        (layoutTerm (templateListLayout rest) (phaseAt (d + 1)).1 (phaseAt (d + 1)).2) (depthJunk d) =
        templateListTerm (recs :: rest) d
      rw [ih (d + 1)]
      rfl

def progRingLayout : List PhaseState → Layout
  | [] => .unopened
  | ph :: rest =>
      .opened (.opened (versionLayout ph.pRecs) (templateListLayout ph.tCells)) (progRingLayout rest)

def phaseBodyTerm (ph : PhaseState) (d : Nat) : Term :=
  frameTerm (pfVerTerm ph.pRecs (d + 1)) (templateListTerm ph.tCells (d + 1)) (depthJunk d)

def progRingTerm : List PhaseState → Nat → Term
  | [], d => depthBase d
  | ph :: rest, d => frameTerm (phaseBodyTerm ph (d + 1)) (progRingTerm rest (d + 1)) (depthJunk d)

theorem progRingLayout_term (phases : List PhaseState) :
    ∀ d, layoutTerm (progRingLayout phases) (phaseAt d).1 (phaseAt d).2 = progRingTerm phases d := by
  induction phases with
  | nil => intro _; rfl
  | cons ph rest ih =>
      intro d
      rw [progRingLayout, layout_opened_phase _ _ _ (phase_at_good d)]
      change frameTerm
        (layoutTerm (.opened (versionLayout ph.pRecs) (templateListLayout ph.tCells))
          (phaseAt (d + 1)).1 (phaseAt (d + 1)).2)
        (layoutTerm (progRingLayout rest) (phaseAt (d + 1)).1 (phaseAt (d + 1)).2)
        (depthJunk d) = progRingTerm (ph :: rest) d
      rw [layout_opened_phase _ _ _ (phase_at_good (d + 1)), ih (d + 1)]
      change frameTerm
        (frameTerm (pfVerTerm ph.pRecs (d + 2))
          (layoutTerm (templateListLayout ph.tCells) (phaseAt (d + 2)).1 (phaseAt (d + 2)).2)
          (depthJunk (d + 1)))
        (progRingTerm rest (d + 1)) (depthJunk d) = progRingTerm (ph :: rest) d
      rw [templateListLayout_term ph.tCells (d + 2)]
      rfl

def queueListLayout : List (List Rec3) → Layout
  | [] => .unopened
  | recs :: rest => .opened (versionLayout recs) (queueListLayout rest)

def queueListTerm : List (List Rec3) → Nat → Term
  | [], d => depthBase d
  | recs :: rest, d => frameTerm (pfVerTerm recs (d + 1)) (queueListTerm rest (d + 1)) (depthJunk d)

theorem queueListLayout_term (cells : List (List Rec3)) :
    ∀ d, layoutTerm (queueListLayout cells) (phaseAt d).1 (phaseAt d).2 = queueListTerm cells d := by
  induction cells with
  | nil => intro _; rfl
  | cons recs rest ih =>
      intro d
      rw [queueListLayout, layout_opened_phase _ _ _ (phase_at_good d)]
      change frameTerm (pfVerTerm recs (d + 1))
        (layoutTerm (queueListLayout rest) (phaseAt (d + 1)).1 (phaseAt (d + 1)).2) (depthJunk d) =
        queueListTerm (recs :: rest) d
      rw [ih (d + 1)]
      rfl

def pfHubLayout (flagShape : Layout) (phases : List PhaseState) (qCells : List (List Rec3)) : Layout :=
  .opened flagShape (.opened (progRingLayout phases) (queueListLayout qCells))

def pfRootTerm (flag progRing queueRoot : Term) : Term :=
  (numeral 1 ⋅ S) ⋅ frameTerm flag (frameTerm progRing queueRoot (depthJunk 1)) (depthJunk 0)

def pfMachineTerm (phases : List PhaseState) (qCells : List (List Rec3)) : Term :=
  pfRootTerm (depthBase 1) (progRingTerm phases 2) (queueListTerm qCells 2)

theorem pfHubLayout_unopened_term (phases : List PhaseState) (qCells : List (List Rec3)) :
    (numeral 1 ⋅ S) ⋅ layoutTerm (pfHubLayout .unopened phases qCells) 2 2 =
      pfMachineTerm phases qCells := by
  have h0 : (2, 2) = phaseAt 0 := rfl
  change (numeral 1 ⋅ S) ⋅
    layoutTerm (pfHubLayout .unopened phases qCells) (phaseAt 0).1 (phaseAt 0).2 =
    pfMachineTerm phases qCells
  rw [pfHubLayout, layout_opened_phase _ _ _ (phase_at_good 0)]
  change (numeral 1 ⋅ S) ⋅ frameTerm (depthBase 1)
    (layoutTerm (.opened (progRingLayout phases) (queueListLayout qCells))
      (phaseAt 1).1 (phaseAt 1).2) (depthJunk 0) = pfMachineTerm phases qCells
  rw [layout_opened_phase _ _ _ (phase_at_good 1)]
  change (numeral 1 ⋅ S) ⋅ frameTerm (depthBase 1)
    (frameTerm (layoutTerm (progRingLayout phases) (phaseAt 2).1 (phaseAt 2).2)
      (layoutTerm (queueListLayout qCells) (phaseAt 2).1 (phaseAt 2).2) (depthJunk 1))
    (depthJunk 0) = pfMachineTerm phases qCells
  rw [progRingLayout_term phases 2, queueListLayout_term qCells 2]
  rfl

def initTemplateCells (appendant : List Bool) : List (List Rec3) :=
  appendant.map (fun b => [recIdle b])

def initPhaseStatesAux : Bool → List (List Bool) → List PhaseState
  | _, [] => []
  | isFirst, app :: rest =>
      { pRecs := [if isFirst then recActive else recInactive]
        tCells := initTemplateCells app } :: initPhaseStatesAux false rest

def initPhaseStates (P : CTSProgram) : List PhaseState :=
  initPhaseStatesAux true P.phases

def initQueueCells (w : List Bool) : List (List Rec3) :=
  w.map (fun b => [recUnconsumed b])

def encodeCTSLayout (P : CTSProgram) (w : List Bool) : Layout :=
  pfHubLayout .unopened (initPhaseStates P) (initQueueCells w)

/-- **Polynomial-Size Pure-`S` Encoder `encodeProgramFreeCTS`**:
    Encodes BOTH an arbitrary Cyclic Tag System program `P` and input queue `w`
    into a single closed pure-`S` combinator term. -/
def encodeProgramFreeCTS (P : CTSProgram) (w : List Bool) : Term :=
  pfMachineTerm (initPhaseStates P) (initQueueCells w)

theorem encodeProgramFreeCTS_eq_layout (P : CTSProgram) (w : List Bool) :
    encodeProgramFreeCTS P w = (numeral 1 ⋅ S) ⋅ layoutTerm (encodeCTSLayout P w) 2 2 :=
  (pfHubLayout_unopened_term (initPhaseStates P) (initQueueCells w)).symm

/-- Every encoded CTS instance is constructively reachable by genuine native `S`-reductions
    from the 10-leaf seed `tenLeafSeed = S(SB)(SB)BS`. -/
theorem seed_reduces_to_encodeProgramFreeCTS (P : CTSProgram) (w : List Bool) :
    Reduces tenLeafSeed (encodeProgramFreeCTS P w) := by
  rw [encodeProgramFreeCTS_eq_layout]
  exact reduces_trans seed_bootstraps_generator
    (reduces_right (any_finite_layout_reachable (encodeCTSLayout P w) 2 2 (by decide) (by decide))
      (numeral 1 ⋅ S))

/-- Pure-`S` closedness (zero free variables `.var _`). -/
def isClosedPureS : Term → Bool
  | .s => true
  | .var _ => false
  | .app l r => isClosedPureS l && isClosedPureS r

theorem numeral_isClosedPureS (n : Nat) : isClosedPureS (numeral n) = true := by
  induction n with
  | zero => rfl
  | succ _ ih => simp [numeral, B, S, isClosedPureS, ih]

theorem generator_isClosedPureS (m n : Nat) : isClosedPureS (generator m n) = true := by
  simp [generator, S, isClosedPureS, numeral_isClosedPureS]

theorem phaseJunk_isClosedPureS (p : Nat × Nat) : isClosedPureS (phaseJunk p) = true := by
  rcases p with ⟨m, n⟩
  cases m <;> simp [phaseJunk, S, isClosedPureS, numeral_isClosedPureS, generator_isClosedPureS]

theorem layoutTerm_isClosedPureS (s : Layout) :
    ∀ p, goodPhase p → isClosedPureS (layoutTerm s p.1 p.2) = true := by
  induction s with
  | unopened =>
      intro p _
      exact generator_isClosedPureS p.1 p.2
  | opened l r ihl ihr =>
      intro p hp
      rw [layout_opened_phase l r p hp]
      have hn := next_phase_good p hp
      simp [frameTerm, S, isClosedPureS, ihl _ hn, ihr _ hn, phaseJunk_isClosedPureS]

theorem encodeProgramFreeCTS_isClosedPureS (P : CTSProgram) (w : List Bool) :
    isClosedPureS (encodeProgramFreeCTS P w) = true := by
  rw [encodeProgramFreeCTS_eq_layout]
  have hg : goodPhase (2, 2) := by unfold goodPhase; decide
  simp [isClosedPureS, numeral_isClosedPureS, S, layoutTerm_isClosedPureS _ _ hg]

/-! ### Polynomial Unfolded Leaf Count Bound for `encodeProgramFreeCTS P w` -/

def pfOpenedCount : Layout → Nat
  | .unopened => 0
  | .opened l r => 1 + pfOpenedCount l + pfOpenedCount r

def pfLayoutHeight : Layout → Nat
  | .unopened => 0
  | .opened l r => 1 + max (pfLayoutHeight l) (pfLayoutHeight r)

theorem pfLayoutHeight_le_openedCount (s : Layout) : pfLayoutHeight s ≤ pfOpenedCount s := by
  induction s with
  | unopened => exact Nat.le_refl 0
  | opened l r ihl ihr => simp only [pfLayoutHeight, pfOpenedCount]; omega

theorem pf_nextPhase_bound (p : Nat × Nat) (hp : goodPhase p) :
    (nextPhase p).1 ≤ p.2 + 1 ∧ (nextPhase p).2 ≤ p.2 + 1 := by
  rcases p with ⟨m, n⟩
  cases m <;> simp [goodPhase, nextPhase] at * <;> omega

theorem pf_phaseJunk_leaves_bound (p : Nat × Nat) (hp : goodPhase p) :
    leaves (phaseJunk p) ≤ 17 + 6 * p.2 := by
  rcases p with ⟨m, n⟩
  have hn : 2 ≤ n := hp.1
  have hm : m ≤ n := hp.2
  cases m <;> simp [phaseJunk, generator_junk_leaves] <;> omega

theorem pf_layoutTerm_leaves_bound (s : Layout) :
    ∀ (p : Nat × Nat) (H : Nat), goodPhase p → p.2 + pfLayoutHeight s ≤ H →
      leaves (layoutTerm s p.1 p.2) ≤ (2 * pfOpenedCount s + 1) * (19 + 6 * H) := by
  induction s with
  | unopened =>
      intro p H hp hH
      have hm : p.1 ≤ p.2 := hp.2
      simp only [pfLayoutHeight, Nat.add_zero] at hH
      simp only [layoutTerm, pfOpenedCount, generator_leaves]
      omega
  | opened l r ihl ihr =>
      intro p H hp hH
      rw [layout_opened_phase l r p hp, frame_leaves]
      have hnext := next_phase_good p hp
      have hnb := pf_nextPhase_bound p hp
      have hHl : (nextPhase p).2 + pfLayoutHeight l ≤ H := by
        simp only [pfLayoutHeight] at hH; omega
      have hHr : (nextPhase p).2 + pfLayoutHeight r ≤ H := by
        simp only [pfLayoutHeight] at hH; omega
      have hlB := ihl (nextPhase p) H hnext hHl
      have hrB := ihr (nextPhase p) H hnext hHr
      have hjB : 2 + leaves (phaseJunk p) ≤ 19 + 6 * H := by
        have h1 := pf_phaseJunk_leaves_bound p hp
        have hpH : p.2 ≤ H := by simp only [pfLayoutHeight] at hH; omega
        omega
      have hident :
          (2 * pfOpenedCount l + 1) * (19 + 6 * H) +
          (2 * pfOpenedCount r + 1) * (19 + 6 * H) +
          1 * (19 + 6 * H) =
          (2 * pfOpenedCount (.opened l r) + 1) * (19 + 6 * H) := by
        have hc : (2 * pfOpenedCount l + 1) + (2 * pfOpenedCount r + 1) + 1 =
            2 * pfOpenedCount (.opened l r) + 1 := by
          simp [pfOpenedCount]; omega
        rw [← Nat.add_mul, ← Nat.add_mul, hc]
      simp only [Nat.one_mul] at hident
      omega

theorem pfOpenedCount_bitLayout (b : Bool) : pfOpenedCount (bitLayout b) ≤ 1 := by
  cases b <;> decide

theorem pfOpenedCount_fieldsLayout (bits : List Bool) :
    pfOpenedCount (fieldsLayout bits) ≤ 2 * bits.length + 1 := by
  induction bits with
  | nil => decide
  | cons b bs ih =>
      have hb := pfOpenedCount_bitLayout b
      simp only [fieldsLayout, pfOpenedCount, List.length_cons]
      omega

theorem pfOpenedCount_versionLayout {width : Nat}
    (recs : List {bits : List Bool // bits.length = width}) :
    pfOpenedCount (versionLayout recs) ≤ recs.length * (2 * width + 2) := by
  induction recs with
  | nil => simp [versionLayout, pfOpenedCount]
  | cons entry rest ih =>
      have hf := pfOpenedCount_fieldsLayout entry.val
      rw [entry.property] at hf
      have hmul : (rest.length + 1) * (2 * width + 2) =
          rest.length * (2 * width + 2) + (2 * width + 2) := Nat.succ_mul rest.length (2 * width + 2)
      simp only [versionLayout, pfOpenedCount, List.length_cons]
      omega

theorem pfOpenedCount_single_rec2 (e : Rec2) :
    pfOpenedCount (versionLayout [e]) ≤ 6 := by
  simpa using pfOpenedCount_versionLayout [e]

theorem pfOpenedCount_single_rec3 (e : Rec3) :
    pfOpenedCount (versionLayout [e]) ≤ 8 := by
  simpa using pfOpenedCount_versionLayout [e]

theorem pfOpenedCount_initQueueCells (w : List Bool) :
    pfOpenedCount (queueListLayout (initQueueCells w)) ≤ 9 * w.length := by
  induction w with
  | nil => simp [initQueueCells, queueListLayout, pfOpenedCount]
  | cons b bs ih =>
      have hv := pfOpenedCount_single_rec3 (recUnconsumed b)
      simp only [initQueueCells, List.map_cons, queueListLayout, pfOpenedCount, List.length_cons] at *
      omega

theorem pfOpenedCount_initTemplateCells (app : List Bool) :
    pfOpenedCount (templateListLayout (initTemplateCells app)) ≤ 9 * app.length := by
  induction app with
  | nil => simp [initTemplateCells, templateListLayout, pfOpenedCount]
  | cons b bs ih =>
      have hv := pfOpenedCount_single_rec3 (recIdle b)
      simp only [initTemplateCells, List.map_cons, templateListLayout, pfOpenedCount, List.length_cons] at *
      omega

def sumAppendantLengths : List (List Bool) → Nat
  | [] => 0
  | app :: rest => app.length + sumAppendantLengths rest

def ctsInputSize (P : CTSProgram) (w : List Bool) : Nat :=
  P.phases.length + sumAppendantLengths P.phases + w.length

theorem pfOpenedCount_initPhaseStatesAux (phases : List (List Bool)) :
    ∀ isFirst,
      pfOpenedCount (progRingLayout (initPhaseStatesAux isFirst phases)) ≤
        8 * phases.length + 9 * sumAppendantLengths phases := by
  induction phases with
  | nil => intro _; simp [initPhaseStatesAux, progRingLayout, pfOpenedCount, sumAppendantLengths]
  | cons app rest ih =>
      intro isFirst
      have hv := pfOpenedCount_single_rec2 (if isFirst then recActive else recInactive)
      have ht := pfOpenedCount_initTemplateCells app
      have hr := ih false
      simp only [initPhaseStatesAux, progRingLayout, pfOpenedCount, List.length_cons, sumAppendantLengths] at *
      omega

/-- Linear `O(|P| + |w|)` bound on the number of generator openings in `encodeCTSLayout P w`. -/
theorem encodeCTSLayout_openedCount_linear (P : CTSProgram) (w : List Bool) :
    pfOpenedCount (encodeCTSLayout P w) ≤ 2 + 9 * ctsInputSize P w := by
  have hp := pfOpenedCount_initPhaseStatesAux P.phases true
  have hq := pfOpenedCount_initQueueCells w
  unfold encodeCTSLayout pfHubLayout initPhaseStates ctsInputSize
  simp only [pfOpenedCount]
  omega

/-- Explicit polynomial constant for unfolded initial leaf counts. -/
def pfInitialSizeConst : Nat := 2500

/-- **Polynomial Initial Unfolded Size Bound**:
    `leaves (encodeProgramFreeCTS P w) ≤ 2500 * (ctsInputSize P w + 1)^2`. -/
theorem encodeProgramFreeCTS_leaves_poly (P : CTSProgram) (w : List Bool) :
    leaves (encodeProgramFreeCTS P w) ≤ pfInitialSizeConst * (ctsInputSize P w + 1) ^ 2 := by
  have hopen : pfOpenedCount (encodeCTSLayout P w) ≤ 2 + 9 * ctsInputSize P w :=
    encodeCTSLayout_openedCount_linear P w
  have hh := pfLayoutHeight_le_openedCount (encodeCTSLayout P w)
  have hg : goodPhase (2, 2) := by unfold goodPhase; decide
  have hH : (2, 2).2 + pfLayoutHeight (encodeCTSLayout P w) ≤ 2 + (2 + 9 * ctsInputSize P w) := by
    dsimp only []
    omega
  have hlay := pf_layoutTerm_leaves_bound (encodeCTSLayout P w) (2, 2)
    (2 + (2 + 9 * ctsInputSize P w)) hg hH
  dsimp only [] at hlay
  have h1 : 2 * pfOpenedCount (encodeCTSLayout P w) + 1 ≤ 23 * (ctsInputSize P w + 1) := by omega
  have h2 : 19 + 6 * (2 + (2 + 9 * ctsInputSize P w)) ≤ 97 * (ctsInputSize P w + 1) := by omega
  have hmul : (2 * pfOpenedCount (encodeCTSLayout P w) + 1) *
      (19 + 6 * (2 + (2 + 9 * ctsInputSize P w))) ≤
      (23 * (ctsInputSize P w + 1)) * (97 * (ctsInputSize P w + 1)) := Nat.mul_le_mul h1 h2
  have hsq : (23 * (ctsInputSize P w + 1)) * (97 * (ctsInputSize P w + 1)) =
      2231 * ((ctsInputSize P w + 1) ^ 2) := by
    simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hpos : 1 ≤ (ctsInputSize P w + 1) ^ 2 := by
    simp [Nat.pow_two]
    exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hhead : leaves (numeral 1 ⋅ S) = 8 := rfl
  rw [encodeProgramFreeCTS_eq_layout, leaves, hhead]
  unfold pfInitialSizeConst
  omega


/-! ### Section 5B: Pure Spec Scanners & Context Decomposition Lemmas -/

def repeatRightPath : Nat → List Bool
  | 0 => []
  | n + 1 => pfRightChildPath ++ repeatRightPath n

def specScanQueue : List (Option (List Bool)) → QueueScan
  | [] => ⟨none, none, none, none, []⟩
  | st :: rest =>
      let sub := specScanQueue rest
      let nextTail := pfRightChildPath ++ sub.tailPath
      match st with
      | none =>
          { consuming := shiftPathBool sub.consuming
            unconsumed := shiftPathBool sub.unconsumed
            staging := shiftPathBool sub.staging
            uninit := some pfLeftChildPath
            tailPath := nextTail }
      | some [false, true, b] =>
          { consuming := shiftPathBool sub.consuming
            unconsumed := shiftPathBool sub.unconsumed
            staging := some (pfLeftChildPath, b)
            uninit := shiftOptPath sub.uninit
            tailPath := nextTail }
      | some [false, false, b] =>
          { consuming := shiftPathBool sub.consuming
            unconsumed := some (pfLeftChildPath, b)
            staging := shiftPathBool sub.staging
            uninit := shiftOptPath sub.uninit
            tailPath := nextTail }
      | some [true, false, b] =>
          { consuming := some (pfLeftChildPath, b)
            unconsumed := shiftPathBool sub.unconsumed
            staging := shiftPathBool sub.staging
            uninit := shiftOptPath sub.uninit
            tailPath := nextTail }
      | _ =>
          { consuming := shiftPathBool sub.consuming
            unconsumed := shiftPathBool sub.unconsumed
            staging := shiftPathBool sub.staging
            uninit := shiftOptPath sub.uninit
            tailPath := nextTail }

theorem scanQueue_closed (t : Term) (h : parseFrame t = none) :
    scanQueue t = ⟨none, none, none, none, []⟩ := by
  unfold parseFrame at h
  unfold scanQueue
  split <;> simp_all

theorem scanQueue_queueListTerm (cells : List (List Rec3)) :
    ∀ d, scanQueue (queueListTerm cells d) =
      specScanQueue (cells.map (fun r => newestRecords r none)) := by
  induction cells with
  | nil =>
      intro d
      exact scanQueue_closed (depthBase d) (depth_base_closed d)
  | cons recs rest ih =>
      intro d
      unfold queueListTerm frameTerm S
      dsimp only [scanQueue, List.map]
      rw [pfVerTerm_scan recs (d + 1), ih (d + 1)]
      rfl

def specScanTemplates : List (Option (List Bool)) → TemplateScan
  | [] => ⟨none, none, none⟩
  | st :: rest =>
      let sub := specScanTemplates rest
      match st with
      | some [false, false, sbit] =>
          { firstIdle := some (pfLeftChildPath, sbit)
            firstArmed := shiftPathBool sub.firstArmed
            firstAppending := shiftPathBool sub.firstAppending }
      | some [true, false, sbit] =>
          { firstIdle := shiftPathBool sub.firstIdle
            firstArmed := some (pfLeftChildPath, sbit)
            firstAppending := shiftPathBool sub.firstAppending }
      | some [true, true, sbit] =>
          { firstIdle := shiftPathBool sub.firstIdle
            firstArmed := shiftPathBool sub.firstArmed
            firstAppending := some (pfLeftChildPath, sbit) }
      | _ =>
          { firstIdle := shiftPathBool sub.firstIdle
            firstArmed := shiftPathBool sub.firstArmed
            firstAppending := shiftPathBool sub.firstAppending }

theorem scanTemplates_closed (t : Term) (h : parseFrame t = none) :
    scanTemplates t = ⟨none, none, none⟩ := by
  unfold parseFrame at h
  unfold scanTemplates
  split <;> simp_all

theorem scanTemplates_templateListTerm (cells : List (List Rec3)) :
    ∀ d, scanTemplates (templateListTerm cells d) =
      specScanTemplates (cells.map (fun r => newestRecords r none)) := by
  induction cells with
  | nil =>
      intro d
      exact scanTemplates_closed (depthBase d) (depth_base_closed d)
  | cons recs rest ih =>
      intro d
      unfold templateListTerm frameTerm S
      dsimp only [scanTemplates, List.map]
      rw [pfVerTerm_scan recs (d + 1), ih (d + 1)]
      rfl

def specScanPhases : List (Option (List Bool) × List (Option (List Bool))) → List PhaseEntry
  | [] => []
  | (pst, tsts) :: rest =>
      { verPath := [false, true, false, true]
        tListPath := [false, true, true, false, true]
        status := pst
        templates := specScanTemplates tsts } :: (specScanPhases rest).map shiftPhaseEntry

theorem scanPhases_closed (t : Term) (h : parseFrame t = none) :
    scanPhases t = [] := by
  unfold parseFrame at h
  unfold scanPhases
  split <;> simp_all

theorem scanPhases_progRingTerm (phases : List PhaseState) :
    ∀ d, scanPhases (progRingTerm phases d) =
      specScanPhases (phases.map (fun ph =>
        (newestRecords ph.pRecs none, ph.tCells.map (fun r => newestRecords r none)))) := by
  induction phases with
  | nil =>
      intro d
      exact scanPhases_closed (depthBase d) (depth_base_closed d)
  | cons ph rest ih =>
      intro d
      unfold progRingTerm phaseBodyTerm frameTerm S
      dsimp only [scanPhases]
      rw [pfVerTerm_scan ph.pRecs (d + 2), scanTemplates_templateListTerm ph.tCells (d + 2), ih (d + 1)]
      rfl

/-! ### Context Builders & Congruence Lemmas for Lifting -/

def queueAroundVer : List (List Rec3) → Term → List (List Rec3) → Nat → Term
  | [], v, after, d => frameTerm v (queueListTerm after (d + 1)) (depthJunk d)
  | r :: bs, v, after, d => frameTerm (pfVerTerm r (d + 1)) (queueAroundVer bs v after (d + 1)) (depthJunk d)

theorem queueAroundVer_eq (before : List (List Rec3)) (focus : List Rec3) (after : List (List Rec3)) :
    ∀ d, queueAroundVer before (pfVerTerm focus (d + before.length + 1)) after d =
      queueListTerm (before ++ focus :: after) d := by
  induction before with
  | nil => intro d; rfl
  | cons r bs ih =>
      intro d
      simp only [queueAroundVer, List.length_cons, queueListTerm, List.cons_append]
      have hd : d + (bs.length + 1) + 1 = (d + 1) + bs.length + 1 := by omega
      rw [hd, ih (d + 1)]

theorem queueAroundVer_termAt (before : List (List Rec3)) (v : Term) (after : List (List Rec3)) :
    ∀ d, termAt (queueAroundVer before v after d) (repeatRightPath before.length ++ pfLeftChildPath) = some v := by
  induction before with
  | nil => intro d; simp [queueAroundVer, repeatRightPath, pfLeftChildPath, frameTerm, termAt, term_at_nil]
  | cons r bs ih =>
      intro d
      simpa [queueAroundVer, repeatRightPath, pfRightChildPath, frameTerm, termAt, List.append_assoc] using ih (d + 1)

theorem queueAroundVer_directed (before : List (List Rec3)) (after : List (List Rec3))
    {p : List Bool} {v v' : Term} (h : DirectedStep p v v') :
    ∀ d, DirectedStep ((repeatRightPath before.length ++ pfLeftChildPath) ++ p)
      (queueAroundVer before v after d) (queueAroundVer before v' after d) := by
  induction before with
  | nil =>
      intro d
      simpa [queueAroundVer, repeatRightPath, pfLeftChildPath] using directed_frame_left h _ _
  | cons r bs ih =>
      intro d
      simpa [queueAroundVer, repeatRightPath, pfRightChildPath, List.append_assoc] using
        directed_frame_right (ih (d + 1)) _ _

theorem queueAroundVer_scan_congr (before : List (List Rec3)) (v1 v2 : Term) (after : List (List Rec3))
    (hscan : pfScanVersion 3 none v1 = pfScanVersion 3 none v2) :
    ∀ d, scanQueue (queueAroundVer before v1 after d) = scanQueue (queueAroundVer before v2 after d) := by
  induction before with
  | nil =>
      intro d
      unfold queueAroundVer frameTerm S
      dsimp only [scanQueue]
      rw [hscan]
  | cons r bs ih =>
      intro d
      unfold queueAroundVer frameTerm S
      dsimp only [scanQueue]
      rw [ih (d + 1)]

def queueAroundTail : List (List Rec3) → Term → Nat → Term
  | [], tail, _ => tail
  | r :: bs, tail, d => frameTerm (pfVerTerm r (d + 1)) (queueAroundTail bs tail (d + 1)) (depthJunk d)

theorem queueAroundTail_closed_eq (before : List (List Rec3)) :
    ∀ d, queueAroundTail before (depthBase (d + before.length)) d = queueListTerm before d := by
  induction before with
  | nil => intro d; simp [queueAroundTail, queueListTerm]
  | cons r bs ih =>
      intro d
      simp only [queueAroundTail, List.length_cons, queueListTerm]
      have hd : d + (bs.length + 1) = (d + 1) + bs.length := by omega
      rw [hd, ih (d + 1)]

theorem queueAroundTail_opened_eq (before : List (List Rec3)) :
    ∀ d, queueAroundTail before
      (layoutTerm (.opened .unopened .unopened) (phaseAt (d + before.length)).1 (phaseAt (d + before.length)).2) d =
      queueListTerm (before ++ [[]]) d := by
  induction before with
  | nil =>
      intro d
      simp only [queueAroundTail, List.length_nil, Nat.add_zero, List.nil_append]
      rw [layout_opened_phase _ _ _ (phase_at_good d)]
      rfl
  | cons r bs ih =>
      intro d
      simp only [queueAroundTail, List.length_cons, List.cons_append, queueListTerm]
      have hd : d + (bs.length + 1) = (d + 1) + bs.length := by omega
      rw [hd, ih (d + 1)]

theorem queueAroundTail_termAt (before : List (List Rec3)) (u : Term) :
    ∀ d, termAt (queueAroundTail before u d) (repeatRightPath before.length) = some u := by
  induction before with
  | nil => intro d; simpa [queueAroundTail, repeatRightPath] using term_at_nil u
  | cons r bs ih =>
      intro d
      simpa [queueAroundTail, repeatRightPath, pfRightChildPath, frameTerm, termAt] using ih (d + 1)

theorem queueAroundTail_directed (before : List (List Rec3)) {p : List Bool} {u u' : Term}
    (h : DirectedStep p u u') :
    ∀ d, DirectedStep (repeatRightPath before.length ++ p)
      (queueAroundTail before u d) (queueAroundTail before u' d) := by
  induction before with
  | nil => intro d; simpa [queueAroundTail, repeatRightPath] using h
  | cons r bs ih =>
      intro d
      simpa [queueAroundTail, repeatRightPath, pfRightChildPath, List.append_assoc] using
        directed_frame_right (ih (d + 1)) _ _

theorem queueAroundTail_scan_closed (before : List (List Rec3)) (u : Term)
    (hu : parseFrame u = none) :
    ∀ d, scanQueue (queueAroundTail before u d) = scanQueue (queueListTerm before d) := by
  induction before with
  | nil =>
      intro d
      rw [queueAroundTail, scanQueue_closed u hu, queueListTerm,
        scanQueue_closed (depthBase d) (depth_base_closed d)]
  | cons r bs ih =>
      intro d
      unfold queueAroundTail queueListTerm frameTerm S
      dsimp only [scanQueue]
      rw [ih (d + 1)]

def templateAroundVer : List (List Rec3) → Term → List (List Rec3) → Nat → Term
  | [], v, after, d => frameTerm v (templateListTerm after (d + 1)) (depthJunk d)
  | r :: bs, v, after, d => frameTerm (pfVerTerm r (d + 1)) (templateAroundVer bs v after (d + 1)) (depthJunk d)

theorem templateAroundVer_eq (before : List (List Rec3)) (focus : List Rec3) (after : List (List Rec3)) :
    ∀ d, templateAroundVer before (pfVerTerm focus (d + before.length + 1)) after d =
      templateListTerm (before ++ focus :: after) d := by
  induction before with
  | nil => intro d; rfl
  | cons r bs ih =>
      intro d
      simp only [templateAroundVer, List.length_cons, templateListTerm, List.cons_append]
      have hd : d + (bs.length + 1) + 1 = (d + 1) + bs.length + 1 := by omega
      rw [hd, ih (d + 1)]

theorem templateAroundVer_termAt (before : List (List Rec3)) (v : Term) (after : List (List Rec3)) :
    ∀ d, termAt (templateAroundVer before v after d) (repeatRightPath before.length ++ pfLeftChildPath) = some v := by
  induction before with
  | nil => intro d; simp [templateAroundVer, repeatRightPath, pfLeftChildPath, frameTerm, termAt, term_at_nil]
  | cons r bs ih =>
      intro d
      simpa [templateAroundVer, repeatRightPath, pfRightChildPath, frameTerm, termAt, List.append_assoc] using ih (d + 1)

theorem templateAroundVer_directed (before : List (List Rec3)) (after : List (List Rec3))
    {p : List Bool} {v v' : Term} (h : DirectedStep p v v') :
    ∀ d, DirectedStep ((repeatRightPath before.length ++ pfLeftChildPath) ++ p)
      (templateAroundVer before v after d) (templateAroundVer before v' after d) := by
  induction before with
  | nil =>
      intro d
      simpa [templateAroundVer, repeatRightPath, pfLeftChildPath] using directed_frame_left h _ _
  | cons r bs ih =>
      intro d
      simpa [templateAroundVer, repeatRightPath, pfRightChildPath, List.append_assoc] using
        directed_frame_right (ih (d + 1)) _ _

theorem templateAroundVer_scan_congr (before : List (List Rec3)) (v1 v2 : Term) (after : List (List Rec3))
    (hscan : pfScanVersion 3 none v1 = pfScanVersion 3 none v2) :
    ∀ d, scanTemplates (templateAroundVer before v1 after d) =
      scanTemplates (templateAroundVer before v2 after d) := by
  induction before with
  | nil =>
      intro d
      unfold templateAroundVer frameTerm S
      dsimp only [scanTemplates]
      rw [hscan]
  | cons r bs ih =>
      intro d
      unfold templateAroundVer frameTerm S
      dsimp only [scanTemplates]
      rw [ih (d + 1)]

def progAroundPhaseVer : List PhaseState → Term → List (List Rec3) → List PhaseState → Nat → Term
  | [], v, tCells, after, d =>
      frameTerm (frameTerm v (templateListTerm tCells (d + 2)) (depthJunk (d + 1)))
        (progRingTerm after (d + 1)) (depthJunk d)
  | ph :: bs, v, tCells, after, d =>
      frameTerm (phaseBodyTerm ph (d + 1)) (progAroundPhaseVer bs v tCells after (d + 1)) (depthJunk d)

theorem progAroundPhaseVer_eq (before : List PhaseState) (pRecs : List Rec2)
    (tCells : List (List Rec3)) (after : List PhaseState) :
    ∀ d, progAroundPhaseVer before (pfVerTerm pRecs (d + before.length + 2)) tCells after d =
      progRingTerm (before ++ ⟨pRecs, tCells⟩ :: after) d := by
  induction before with
  | nil => intro d; rfl
  | cons ph bs ih =>
      intro d
      simp only [progAroundPhaseVer, List.length_cons, progRingTerm, List.cons_append]
      have hd : d + (bs.length + 1) + 2 = (d + 1) + bs.length + 2 := by omega
      rw [hd, ih (d + 1)]

theorem progAroundPhaseVer_termAt (before : List PhaseState) (v : Term)
    (tCells : List (List Rec3)) (after : List PhaseState) :
    ∀ d, termAt (progAroundPhaseVer before v tCells after d)
      (repeatRightPath before.length ++ [false, true, false, true]) = some v := by
  induction before with
  | nil => intro d; simp [progAroundPhaseVer, repeatRightPath, frameTerm, termAt, term_at_nil]
  | cons ph bs ih =>
      intro d
      simpa [progAroundPhaseVer, repeatRightPath, pfRightChildPath, frameTerm, termAt, List.append_assoc] using ih (d + 1)

theorem progAroundPhaseVer_directed (before : List PhaseState) (tCells : List (List Rec3))
    (after : List PhaseState) {p : List Bool} {v v' : Term} (h : DirectedStep p v v') :
    ∀ d, DirectedStep ((repeatRightPath before.length ++ [false, true, false, true]) ++ p)
      (progAroundPhaseVer before v tCells after d)
      (progAroundPhaseVer before v' tCells after d) := by
  induction before with
  | nil =>
      intro d
      simpa [progAroundPhaseVer, repeatRightPath, List.append_assoc] using
        directed_frame_left (directed_frame_left h _ _) _ _
  | cons ph bs ih =>
      intro d
      simpa [progAroundPhaseVer, repeatRightPath, pfRightChildPath, List.append_assoc] using
        directed_frame_right (ih (d + 1)) _ _

theorem progAroundPhaseVer_scan_congr (before : List PhaseState) (v1 v2 : Term)
    (tCells : List (List Rec3)) (after : List PhaseState)
    (hscan : pfScanVersion 2 none v1 = pfScanVersion 2 none v2) :
    ∀ d, scanPhases (progAroundPhaseVer before v1 tCells after d) =
      scanPhases (progAroundPhaseVer before v2 tCells after d) := by
  induction before with
  | nil =>
      intro d
      unfold progAroundPhaseVer frameTerm S
      dsimp only [scanPhases]
      rw [hscan]
  | cons ph bs ih =>
      intro d
      unfold progAroundPhaseVer phaseBodyTerm frameTerm S
      dsimp only [scanPhases]
      rw [ih (d + 1)]

def progAroundTList : List PhaseState → List Rec2 → Term → List PhaseState → Nat → Term
  | [], pRecs, tTerm, after, d =>
      frameTerm (frameTerm (pfVerTerm pRecs (d + 2)) tTerm (depthJunk (d + 1)))
        (progRingTerm after (d + 1)) (depthJunk d)
  | ph :: bs, pRecs, tTerm, after, d =>
      frameTerm (phaseBodyTerm ph (d + 1)) (progAroundTList bs pRecs tTerm after (d + 1)) (depthJunk d)

theorem progAroundTList_eq (before : List PhaseState) (pRecs : List Rec2)
    (tCells : List (List Rec3)) (after : List PhaseState) :
    ∀ d, progAroundTList before pRecs (templateListTerm tCells (d + before.length + 2)) after d =
      progRingTerm (before ++ ⟨pRecs, tCells⟩ :: after) d := by
  induction before with
  | nil => intro d; rfl
  | cons ph bs ih =>
      intro d
      simp only [progAroundTList, List.length_cons, progRingTerm, List.cons_append]
      have hd : d + (bs.length + 1) + 2 = (d + 1) + bs.length + 2 := by omega
      rw [hd, ih (d + 1)]

theorem progAroundTList_termAt (before : List PhaseState) (pRecs : List Rec2)
    (tTerm : Term) (after : List PhaseState) :
    ∀ d, termAt (progAroundTList before pRecs tTerm after d)
      (repeatRightPath before.length ++ [false, true, true, false, true]) = some tTerm := by
  induction before with
  | nil => intro d; simp [progAroundTList, repeatRightPath, frameTerm, termAt, term_at_nil]
  | cons ph bs ih =>
      intro d
      simpa [progAroundTList, repeatRightPath, pfRightChildPath, frameTerm, termAt, List.append_assoc] using ih (d + 1)

theorem progAroundTList_directed (before : List PhaseState) (pRecs : List Rec2)
    (after : List PhaseState) {p : List Bool} {t1 t2 : Term} (h : DirectedStep p t1 t2) :
    ∀ d, DirectedStep ((repeatRightPath before.length ++ [false, true, true, false, true]) ++ p)
      (progAroundTList before pRecs t1 after d)
      (progAroundTList before pRecs t2 after d) := by
  induction before with
  | nil =>
      intro d
      simpa [progAroundTList, repeatRightPath, List.append_assoc] using
        directed_frame_left (directed_frame_right h _ _) _ _
  | cons ph bs ih =>
      intro d
      simpa [progAroundTList, repeatRightPath, pfRightChildPath, List.append_assoc] using
        directed_frame_right (ih (d + 1)) _ _

theorem progAroundTList_scan_congr (before : List PhaseState) (pRecs : List Rec2)
    (t1 t2 : Term) (after : List PhaseState)
    (hscan : scanTemplates t1 = scanTemplates t2) :
    ∀ d, scanPhases (progAroundTList before pRecs t1 after d) =
      scanPhases (progAroundTList before pRecs t2 after d) := by
  induction before with
  | nil =>
      intro d
      unfold progAroundTList frameTerm S
      dsimp only [scanPhases]
      rw [hscan]
  | cons ph bs ih =>
      intro d
      unfold progAroundTList phaseBodyTerm frameTerm S
      dsimp only [scanPhases]
      rw [ih (d + 1)]

/-! ### Root-Level `pfRootTerm` Lookup, Step, and `pfReadState` Lemmas -/

theorem pfRootTerm_halt_closed (flag progRing queueRoot : Term) (hf : parseFrame flag = none) :
    pfRootHalt (pfRootTerm flag progRing queueRoot) = false := by
  simp [pfRootHalt, pfRootTerm, haltObserved, parse_frame, flagValue, hf]

theorem pfMachineTerm_halt_false (phases : List PhaseState) (qCells : List (List Rec3)) :
    pfRootHalt (pfMachineTerm phases qCells) = false :=
  pfRootTerm_halt_closed _ _ _ (depth_base_closed 1)

theorem pfRootTerm_readState (flag progRing queueRoot : Term) :
    pfReadState (pfRootTerm flag progRing queueRoot) =
      some (scanPhases progRing, scanQueue queueRoot) := by
  simp [pfReadState, pfRootTerm, pfHubPath, termAt, parse_frame]

theorem pfRootTerm_termAt_flag (flag progRing queueRoot : Term) :
    termAt (pfRootTerm flag progRing queueRoot) pfFlagPath = some flag := by
  simp [pfRootTerm, pfFlagPath, frameTerm, termAt, term_at_nil]

theorem pfRootTerm_termAt_prog (flag progRing queueRoot : Term) (p : List Bool) :
    termAt (pfRootTerm flag progRing queueRoot) (pfProgRingPath ++ p) = termAt progRing p := by
  simp [pfRootTerm, pfProgRingPath, frameTerm, termAt]

theorem pfRootTerm_termAt_queue (flag progRing queueRoot : Term) (p : List Bool) :
    termAt (pfRootTerm flag progRing queueRoot) (pfQueueRootPath ++ p) = termAt queueRoot p := by
  simp [pfRootTerm, pfQueueRootPath, frameTerm, termAt]

theorem pfRootTerm_directed_flag (progRing queueRoot : Term) {p : List Bool} {f1 f2 : Term}
    (h : DirectedStep p f1 f2) :
    DirectedStep (pfFlagPath ++ p) (pfRootTerm f1 progRing queueRoot) (pfRootTerm f2 progRing queueRoot) := by
  simpa [pfRootTerm, pfFlagPath, List.append_assoc] using
    DirectedStep.right (a := numeral 1 ⋅ S) (directed_frame_left h _ _)

theorem pfRootTerm_directed_prog (flag queueRoot : Term) {p : List Bool} {pr1 pr2 : Term}
    (h : DirectedStep p pr1 pr2) :
    DirectedStep (pfProgRingPath ++ p) (pfRootTerm flag pr1 queueRoot) (pfRootTerm flag pr2 queueRoot) := by
  simpa [pfRootTerm, pfProgRingPath, List.append_assoc] using
    DirectedStep.right (a := numeral 1 ⋅ S) (directed_frame_right (directed_frame_left h _ _) _ _)

theorem pfRootTerm_directed_queue (flag progRing : Term) {p : List Bool} {q1 q2 : Term}
    (h : DirectedStep p q1 q2) :
    DirectedStep (pfQueueRootPath ++ p) (pfRootTerm flag progRing q1) (pfRootTerm flag progRing q2) := by
  simpa [pfRootTerm, pfQueueRootPath, List.append_assoc] using
    DirectedStep.right (a := numeral 1 ⋅ S) (directed_frame_right (directed_frame_right h _ _) _ _)


/-! ## Section 6: Spec Scanner Algebra, Micro-Transactions, and Bidirectional Universality -/

theorem repeatRightPath_add (m n : Nat) :
    repeatRightPath (m + n) = repeatRightPath m ++ repeatRightPath n := by
  induction m with
  | zero => simp [repeatRightPath]
  | succ m ih => simp [repeatRightPath, Nat.succ_add, ih, List.append_assoc]

theorem shiftPathBool_repeat (n : Nat) (o : Option (List Bool × Bool)) :
    shiftPathBool (o.map (fun pb => (repeatRightPath n ++ pb.1, pb.2))) =
      o.map (fun pb => (repeatRightPath (n + 1) ++ pb.1, pb.2)) := by
  cases o <;> simp [shiftPathBool, repeatRightPath, List.append_assoc]

theorem shiftOptPath_repeat (n : Nat) (o : Option (List Bool)) :
    shiftOptPath (o.map (fun p => repeatRightPath n ++ p)) =
      o.map (fun p => repeatRightPath (n + 1) ++ p) := by
  cases o <;> simp [shiftOptPath, repeatRightPath, List.append_assoc]

def shiftQueueScanBy (n : Nat) (qs : QueueScan) : QueueScan :=
  { consuming := qs.consuming.map (fun pb => (repeatRightPath n ++ pb.1, pb.2))
    unconsumed := qs.unconsumed.map (fun pb => (repeatRightPath n ++ pb.1, pb.2))
    staging := qs.staging.map (fun pb => (repeatRightPath n ++ pb.1, pb.2))
    uninit := qs.uninit.map (fun p => repeatRightPath n ++ p)
    tailPath := repeatRightPath n ++ qs.tailPath }

def IsConsumedCell (r : List Rec3) : Prop :=
  ∃ b, newestRecords r none = some [true, true, b]

abbrev IsUnconsumedFor (r : List Rec3) (b : Bool) : Prop :=
  newestRecords r none = some [false, false, b]

def AllUnconsumed (uCells : List (List Rec3)) : Prop :=
  ∀ r ∈ uCells, ∃ b, newestRecords r none = some [false, false, b]

def QueueMatchesWord : List (List Rec3) → List Bool → Prop
  | [], [] => True
  | r :: rs, b :: bs => IsUnconsumedFor r b ∧ QueueMatchesWord rs bs
  | _, _ => False

theorem queueMatchesWord_allUnconsumed {uCells : List (List Rec3)} {w : List Bool}
    (h : QueueMatchesWord uCells w) : AllUnconsumed uCells := by
  induction uCells generalizing w with
  | nil => intro _ hm; simp at hm
  | cons r rs ih =>
      cases w with
      | nil => simp [QueueMatchesWord] at h
      | cons b bs =>
          rcases h with ⟨hr, hrs⟩
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx'
          · exact ⟨b, hr⟩
          · exact ih hrs x hx'

theorem queueMatchesWord_append {u1 u2 : List (List Rec3)} {w1 w2 : List Bool}
    (h1 : QueueMatchesWord u1 w1) (h2 : QueueMatchesWord u2 w2) :
    QueueMatchesWord (u1 ++ u2) (w1 ++ w2) := by
  induction u1 generalizing w1 with
  | nil =>
      cases w1 with
      | nil => exact h2
      | cons _ _ => simp [QueueMatchesWord] at h1
  | cons r rs ih =>
      cases w1 with
      | nil => simp [QueueMatchesWord] at h1
      | cons b bs =>
          rcases h1 with ⟨hr, hrs⟩
          exact ⟨hr, ih hrs⟩

theorem initQueueCells_matches (w : List Bool) :
    QueueMatchesWord (initQueueCells w) w := by
  induction w with
  | nil => trivial
  | cons b bs ih =>
      exact ⟨rfl, ih⟩

theorem specScanQueue_cons_consumed_eq (b : Bool) (xs : List (Option (List Bool))) :
    specScanQueue (some [true, true, b] :: xs) =
      let sub := specScanQueue xs
      { consuming := shiftPathBool sub.consuming
        unconsumed := shiftPathBool sub.unconsumed
        staging := shiftPathBool sub.staging
        uninit := shiftOptPath sub.uninit
        tailPath := pfRightChildPath ++ sub.tailPath } := rfl

theorem specScanQueue_consumed_prefix (consumed suffix : List (List Rec3))
    (hc : ∀ r ∈ consumed, IsConsumedCell r) :
    specScanQueue ((consumed ++ suffix).map (fun r => newestRecords r none)) =
      shiftQueueScanBy consumed.length (specScanQueue (suffix.map (fun r => newestRecords r none))) := by
  induction consumed with
  | nil =>
      cases h : specScanQueue (suffix.map (fun r => newestRecords r none)) with
      | mk c u s ui tp =>
          cases c <;> cases u <;> cases s <;> cases ui <;>
            simp [shiftQueueScanBy, repeatRightPath, h]
  | cons r rs ih =>
      obtain ⟨b, hb⟩ := hc r (by simp)
      have hrs : ∀ x ∈ rs, IsConsumedCell x := fun x hx => hc x (by simp [hx])
      simp only [List.cons_append, List.map_cons, hb, List.length_cons]
      rw [specScanQueue_cons_consumed_eq, ih hrs]
      dsimp only [shiftQueueScanBy]
      rw [shiftPathBool_repeat, shiftPathBool_repeat, shiftPathBool_repeat, shiftOptPath_repeat]
      simp [repeatRightPath, List.append_assoc]

theorem specScanQueue_unconsumed_fields (uCells tail : List (List Rec3))
    (hu : AllUnconsumed uCells) :
    let qs := specScanQueue ((uCells ++ tail).map (fun r => newestRecords r none))
    let qt := specScanQueue (tail.map (fun r => newestRecords r none))
    qs.consuming = qt.consuming.map (fun pb => (repeatRightPath uCells.length ++ pb.1, pb.2)) ∧
    qs.staging = qt.staging.map (fun pb => (repeatRightPath uCells.length ++ pb.1, pb.2)) ∧
    qs.uninit = qt.uninit.map (fun p => repeatRightPath uCells.length ++ p) ∧
    qs.tailPath = repeatRightPath uCells.length ++ qt.tailPath := by
  induction uCells with
  | nil =>
      dsimp only [List.nil_append, List.length_nil]
      cases h : specScanQueue (tail.map (fun r => newestRecords r none)) with
      | mk c u s ui tp =>
          cases c <;> cases s <;> cases ui <;> simp [repeatRightPath]
  | cons r rs ih =>
      obtain ⟨b, hb⟩ := hu r (by simp)
      have hrs : AllUnconsumed rs := fun x hx => hu x (by simp [hx])
      obtain ⟨hc, hs, hui, htp⟩ := ih hrs
      simp only [List.cons_append, List.map_cons, hb, List.length_cons, specScanQueue]
      rw [hc, hs, hui, htp, shiftPathBool_repeat, shiftPathBool_repeat, shiftOptPath_repeat]
      exact ⟨rfl, rfl, rfl, by simp [repeatRightPath, List.append_assoc]⟩

theorem scanQueue_halted_shape (consumed : List (List Rec3))
    (hc : ∀ r ∈ consumed, IsConsumedCell r) :
    (scanQueue (queueListTerm consumed 2)).consuming = none ∧
    (scanQueue (queueListTerm consumed 2)).unconsumed = none := by
  rw [scanQueue_queueListTerm]
  have h := specScanQueue_consumed_prefix consumed [] hc
  rw [List.append_nil] at h
  rw [h]
  simp [specScanQueue, shiftQueueScanBy]

theorem scanQueue_front_unconsumed_shape (consumed : List (List Rec3)) (u0 : List Rec3)
    (uRest : List (List Rec3)) (b : Bool)
    (hc : ∀ r ∈ consumed, IsConsumedCell r)
    (hu0 : IsUnconsumedFor u0 b)
    (huRest : AllUnconsumed uRest) :
    (scanQueue (queueListTerm (consumed ++ u0 :: uRest) 2)).consuming = none ∧
    (scanQueue (queueListTerm (consumed ++ u0 :: uRest) 2)).unconsumed =
      some (repeatRightPath consumed.length ++ pfLeftChildPath, b) := by
  rw [scanQueue_queueListTerm, specScanQueue_consumed_prefix consumed (u0 :: uRest) hc]
  have hrest := (specScanQueue_unconsumed_fields uRest [] huRest).1
  rw [List.append_nil] at hrest
  dsimp only [List.map, specScanQueue, Option.map] at hrest
  simp [List.map_cons, hu0, specScanQueue, shiftQueueScanBy, hrest, shiftPathBool]

theorem scanQueue_consuming_clean_shape (consumed : List (List Rec3)) (c0 : List Rec3)
    (uCells : List (List Rec3)) (b : Bool)
    (hc : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b])
    (hu : AllUnconsumed uCells) :
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells) 2)).consuming =
      some (repeatRightPath consumed.length ++ pfLeftChildPath, b) ∧
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells) 2)).staging = none ∧
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells) 2)).uninit = none ∧
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells) 2)).tailPath =
      repeatRightPath (consumed ++ c0 :: uCells).length := by
  rw [scanQueue_queueListTerm, specScanQueue_consumed_prefix consumed (c0 :: uCells) hc]
  obtain ⟨_, hst, hui, htp⟩ := specScanQueue_unconsumed_fields uCells [] hu
  rw [List.append_nil] at hst hui htp
  dsimp only [List.map, specScanQueue, Option.map] at hst hui htp
  rw [List.append_nil] at htp
  have hlen : (consumed ++ c0 :: uCells).length = consumed.length + (uCells.length + 1) := by
    simp [List.length_append]
  rw [hlen, repeatRightPath_add]
  simp [List.map_cons, hc0, specScanQueue, shiftQueueScanBy, hst, hui, htp,
    shiftPathBool, shiftOptPath, repeatRightPath]

theorem scanQueue_consuming_uninit_shape (consumed : List (List Rec3)) (c0 : List Rec3)
    (uCells : List (List Rec3)) (b : Bool)
    (hc : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b])
    (hu : AllUnconsumed uCells) :
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells ++ [[]]) 2)).consuming =
      some (repeatRightPath consumed.length ++ pfLeftChildPath, b) ∧
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells ++ [[]]) 2)).staging = none ∧
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells ++ [[]]) 2)).uninit =
      some (repeatRightPath (consumed ++ c0 :: uCells).length ++ pfLeftChildPath) := by
  have hassoc : consumed ++ c0 :: uCells ++ [[]] = consumed ++ (c0 :: (uCells ++ [[]])) := by
    simp [List.append_assoc]
  rw [hassoc, scanQueue_queueListTerm,
    specScanQueue_consumed_prefix consumed (c0 :: (uCells ++ [[]])) hc]
  obtain ⟨_, hst, hui, _⟩ := specScanQueue_unconsumed_fields uCells [[]] hu
  have htail : specScanQueue (([[]] : List (List Rec3)).map (fun r => newestRecords r none)) =
      ⟨none, none, none, some pfLeftChildPath, pfRightChildPath⟩ := rfl
  rw [htail] at hst hui
  simp only [Option.map, List.map_append, List.map_cons, List.map_nil] at hst hui
  have hlen : (consumed ++ c0 :: uCells).length = consumed.length + (uCells.length + 1) := by
    simp [List.length_append]
  rw [hlen, repeatRightPath_add]
  simp [List.map_cons, hc0, specScanQueue, shiftQueueScanBy, hst, hui,
    shiftPathBool, shiftOptPath, repeatRightPath, List.append_assoc]

theorem scanQueue_consuming_staging_shape (consumed : List (List Rec3)) (c0 : List Rec3)
    (uCells : List (List Rec3)) (b sbit : Bool)
    (hc : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b])
    (hu : AllUnconsumed uCells) :
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells ++ [[recStaging sbit]]) 2)).consuming =
      some (repeatRightPath consumed.length ++ pfLeftChildPath, b) ∧
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells ++ [[recStaging sbit]]) 2)).staging =
      some (repeatRightPath (consumed ++ c0 :: uCells).length ++ pfLeftChildPath, sbit) ∧
    (scanQueue (queueListTerm (consumed ++ c0 :: uCells ++ [[recStaging sbit]]) 2)).uninit = none := by
  have hassoc : consumed ++ c0 :: uCells ++ [[recStaging sbit]] =
      consumed ++ (c0 :: (uCells ++ [[recStaging sbit]])) := by
    simp [List.append_assoc]
  rw [hassoc, scanQueue_queueListTerm,
    specScanQueue_consumed_prefix consumed (c0 :: (uCells ++ [[recStaging sbit]])) hc]
  obtain ⟨_, hst, hui, _⟩ := specScanQueue_unconsumed_fields uCells [[recStaging sbit]] hu
  have htail : specScanQueue (([[recStaging sbit]] : List (List Rec3)).map (fun r => newestRecords r none)) =
      ⟨none, none, some (pfLeftChildPath, sbit), none, pfRightChildPath⟩ := rfl
  rw [htail] at hst hui
  simp only [Option.map, List.map_append, List.map_cons, List.map_nil] at hst hui
  have hlen : (consumed ++ c0 :: uCells).length = consumed.length + (uCells.length + 1) := by
    simp [List.length_append]
  rw [hlen, repeatRightPath_add]
  simp [List.map_cons, hc0, specScanQueue, shiftQueueScanBy, hst, hui,
    shiftPathBool, shiftOptPath, repeatRightPath, List.append_assoc]

/-! ### Template Scanner Spec Lemmas -/

abbrev IsIdleFor (r : List Rec3) (b : Bool) : Prop :=
  newestRecords r none = some [false, false, b]

abbrev IsArmedFor (r : List Rec3) (b : Bool) : Prop :=
  newestRecords r none = some [true, false, b]

abbrev IsAppendingFor (r : List Rec3) (b : Bool) : Prop :=
  newestRecords r none = some [true, true, b]

def TemplateMatchesIdle : List (List Rec3) → List Bool → Prop
  | [], [] => True
  | r :: rs, b :: bs => IsIdleFor r b ∧ TemplateMatchesIdle rs bs
  | _, _ => False

def TemplateMatchesArmed : List (List Rec3) → List Bool → Prop
  | [], [] => True
  | r :: rs, b :: bs => IsArmedFor r b ∧ TemplateMatchesArmed rs bs
  | _, _ => False

theorem initTemplateCells_matches (app : List Bool) :
    TemplateMatchesIdle (initTemplateCells app) app := by
  induction app with
  | nil => trivial
  | cons b bs ih => exact ⟨rfl, ih⟩

theorem templateMatchesIdle_append {t1 t2 : List (List Rec3)} {a1 a2 : List Bool}
    (h1 : TemplateMatchesIdle t1 a1) (h2 : TemplateMatchesIdle t2 a2) :
    TemplateMatchesIdle (t1 ++ t2) (a1 ++ a2) := by
  induction t1 generalizing a1 with
  | nil =>
      cases a1 with
      | nil => exact h2
      | cons _ _ => simp [TemplateMatchesIdle] at h1
  | cons r rs ih =>
      cases a1 with
      | nil => simp [TemplateMatchesIdle] at h1
      | cons b bs => exact ⟨h1.1, ih h1.2⟩

theorem templateMatchesArmed_append {t1 t2 : List (List Rec3)} {a1 a2 : List Bool}
    (h1 : TemplateMatchesArmed t1 a1) (h2 : TemplateMatchesArmed t2 a2) :
    TemplateMatchesArmed (t1 ++ t2) (a1 ++ a2) := by
  induction t1 generalizing a1 with
  | nil =>
      cases a1 with
      | nil => exact h2
      | cons _ _ => simp [TemplateMatchesArmed] at h1
  | cons r rs ih =>
      cases a1 with
      | nil => simp [TemplateMatchesArmed] at h1
      | cons b bs => exact ⟨h1.1, ih h1.2⟩

theorem specScanTemplates_allArmed_noIdle_noApp {tCells : List (List Rec3)} {app : List Bool}
    (h : TemplateMatchesArmed tCells app) :
    (specScanTemplates (tCells.map (fun r => newestRecords r none))).firstIdle = none ∧
    (specScanTemplates (tCells.map (fun r => newestRecords r none))).firstAppending = none := by
  induction tCells generalizing app with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih =>
      cases app with
      | nil => simp [TemplateMatchesArmed] at h
      | cons b bs =>
          rcases h with ⟨hr, hrs⟩
          obtain ⟨hi, ha⟩ := ih hrs
          simp [List.map_cons, hr, specScanTemplates, hi, ha, shiftPathBool]

theorem specScanTemplates_allIdle_noArmed_noApp {tCells : List (List Rec3)} {app : List Bool}
    (h : TemplateMatchesIdle tCells app) :
    (specScanTemplates (tCells.map (fun r => newestRecords r none))).firstArmed = none ∧
    (specScanTemplates (tCells.map (fun r => newestRecords r none))).firstAppending = none := by
  induction tCells generalizing app with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih =>
      cases app with
      | nil => simp [TemplateMatchesIdle] at h
      | cons b bs =>
          rcases h with ⟨hr, hrs⟩
          obtain ⟨har, hap⟩ := ih hrs
          simp [List.map_cons, hr, specScanTemplates, har, hap, shiftPathBool]

theorem specScanTemplates_armed_then_idle (armedPre : List (List Rec3)) (appPre : List Bool)
    (focus : List Rec3) (rest : List (List Rec3)) (sbit : Bool)
    (hpre : TemplateMatchesArmed armedPre appPre)
    (hf : IsIdleFor focus sbit) :
    (specScanTemplates ((armedPre ++ focus :: rest).map (fun r => newestRecords r none))).firstIdle =
      some (repeatRightPath armedPre.length ++ pfLeftChildPath, sbit) := by
  induction armedPre generalizing appPre with
  | nil =>
      simp [List.nil_append, List.map_cons, hf, specScanTemplates, repeatRightPath]
  | cons r rs ih =>
      cases appPre with
      | nil => simp [TemplateMatchesArmed] at hpre
      | cons b bs =>
          rcases hpre with ⟨hr, hrs⟩
          simp only [List.cons_append, List.map_cons, hr, List.length_cons, specScanTemplates]
          rw [ih bs hrs]
          simp [shiftPathBool, repeatRightPath, List.append_assoc]

theorem specScanTemplates_idle_then_armed (idlePre : List (List Rec3)) (appPre : List Bool)
    (focus : List Rec3) (armedRest : List (List Rec3)) (appRest : List Bool) (sbit : Bool)
    (hpre : TemplateMatchesIdle idlePre appPre)
    (hf : IsArmedFor focus sbit)
    (hrest : TemplateMatchesArmed armedRest appRest) :
    (specScanTemplates ((idlePre ++ focus :: armedRest).map (fun r => newestRecords r none))).firstArmed =
      some (repeatRightPath idlePre.length ++ pfLeftChildPath, sbit) ∧
    (specScanTemplates ((idlePre ++ focus :: armedRest).map (fun r => newestRecords r none))).firstAppending =
      none := by
  induction idlePre generalizing appPre with
  | nil =>
      have hr := (specScanTemplates_allArmed_noIdle_noApp hrest).2
      simp [List.nil_append, List.map_cons, hf, specScanTemplates, hr, shiftPathBool, repeatRightPath]
  | cons r rs ih =>
      cases appPre with
      | nil => simp [TemplateMatchesIdle] at hpre
      | cons b bs =>
          rcases hpre with ⟨hr, hrs⟩
          obtain ⟨har, hap⟩ := ih bs hrs
          simp only [List.cons_append, List.map_cons, hr, List.length_cons, specScanTemplates]
          rw [har, hap]
          simp [shiftPathBool, repeatRightPath, List.append_assoc]

theorem specScanTemplates_idle_then_appending (idlePre : List (List Rec3)) (appPre : List Bool)
    (focus : List Rec3) (rest : List (List Rec3)) (sbit : Bool)
    (hpre : TemplateMatchesIdle idlePre appPre)
    (hf : IsAppendingFor focus sbit) :
    (specScanTemplates ((idlePre ++ focus :: rest).map (fun r => newestRecords r none))).firstAppending =
      some (repeatRightPath idlePre.length ++ pfLeftChildPath, sbit) := by
  induction idlePre generalizing appPre with
  | nil =>
      simp [List.nil_append, List.map_cons, hf, specScanTemplates, repeatRightPath]
  | cons r rs ih =>
      cases appPre with
      | nil => simp [TemplateMatchesIdle] at hpre
      | cons b bs =>
          rcases hpre with ⟨hr, hrs⟩
          simp only [List.cons_append, List.map_cons, hr, List.length_cons, specScanTemplates]
          rw [ih bs hrs]
          simp [shiftPathBool, repeatRightPath, List.append_assoc]

/-! ### Phase Ring Spec Lemmas (`specScanPhases`, `findIdxPred`, `listGetOpt`) -/

def shiftPhaseBy (n : Nat) (e : PhaseEntry) : PhaseEntry :=
  { e with
    verPath := repeatRightPath n ++ e.verPath
    tListPath := repeatRightPath n ++ e.tListPath }

theorem shiftPhaseBy_zero (e : PhaseEntry) : shiftPhaseBy 0 e = e := by
  cases e; rfl

theorem shiftPhaseEntry_shiftPhaseBy (n : Nat) (e : PhaseEntry) :
    shiftPhaseEntry (shiftPhaseBy n e) = shiftPhaseBy (n + 1) e := by
  cases e
  simp [shiftPhaseEntry, shiftPhaseBy, repeatRightPath, List.append_assoc]

theorem repeatRightPath_snoc (n : Nat) :
    repeatRightPath n ++ pfRightChildPath = repeatRightPath (n + 1) := by
  induction n with
  | zero => simp [repeatRightPath]
  | succ n ih => simp [repeatRightPath, List.append_assoc, ih]

theorem shiftPhaseBy_shiftPhaseEntry (n : Nat) (e : PhaseEntry) :
    shiftPhaseBy n (shiftPhaseEntry e) = shiftPhaseBy (n + 1) e := by
  cases e
  simp [shiftPhaseBy, shiftPhaseEntry, ← List.append_assoc, repeatRightPath_snoc]

theorem map_shiftPhaseBy_zero (es : List PhaseEntry) :
    es.map (shiftPhaseBy 0) = es := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp [shiftPhaseBy_zero, ih]

theorem map_shiftPhaseEntry_comp (n : Nat) (es : List PhaseEntry) :
    (es.map (shiftPhaseBy n)).map shiftPhaseEntry = es.map (shiftPhaseBy (n + 1)) := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp [shiftPhaseEntry_shiftPhaseBy, ih]

theorem map_shiftPhaseBy_shiftPhaseEntry (n : Nat) (es : List PhaseEntry) :
    (es.map shiftPhaseEntry).map (shiftPhaseBy n) = es.map (shiftPhaseBy (n + 1)) := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp [shiftPhaseBy_shiftPhaseEntry, ih]

theorem specScanPhases_length (xs : List (Option (List Bool) × List (Option (List Bool)))) :
    (specScanPhases xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => simp [specScanPhases, ih]

theorem specScanPhases_append (xs ys : List (Option (List Bool) × List (Option (List Bool)))) :
    specScanPhases (xs ++ ys) =
      specScanPhases xs ++ (specScanPhases ys).map (shiftPhaseBy xs.length) := by
  induction xs with
  | nil =>
      simp [specScanPhases, map_shiftPhaseBy_zero]
  | cons x rest ih =>
      rcases x with ⟨pst, tsts⟩
      simp only [List.cons_append, specScanPhases, ih, List.map_append, List.length_cons]
      rw [map_shiftPhaseEntry_comp]

theorem findIdxPred_all_false {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = false) : findIdxPred p xs = none := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      have hx := h x (by simp)
      have hrest : ∀ y ∈ rest, p y = false := fun y hy => h y (by simp [hy])
      simp [findIdxPred, hx, ih hrest]

theorem findIdxPred_append_skip {α : Type} (p : α → Bool) (xs : List α) (focus : α) (ys : List α)
    (hxs : ∀ x ∈ xs, p x = false) (hf : p focus = true) :
    findIdxPred p (xs ++ focus :: ys) = some (xs.length, focus) := by
  induction xs with
  | nil => simp [findIdxPred, hf]
  | cons x rest ih =>
      have hx := hxs x (by simp)
      have hrest : ∀ y ∈ rest, p y = false := fun y hy => hxs y (by simp [hy])
      simp [findIdxPred, hx, ih hrest]

theorem listGetOpt_append_focus {α : Type} (xs : List α) (focus : α) (ys : List α) :
    listGetOpt (xs ++ focus :: ys) xs.length = some focus := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => simpa [listGetOpt] using ih

def phaseSummary (ph : PhaseState) : Option (List Bool) × List (Option (List Bool)) :=
  (newestRecords ph.pRecs none, ph.tCells.map (fun r => newestRecords r none))

def entryOfPhaseAt (idx : Nat) (ph : PhaseState) : PhaseEntry :=
  { verPath := repeatRightPath idx ++ [false, true, false, true]
    tListPath := repeatRightPath idx ++ [false, true, true, false, true]
    status := newestRecords ph.pRecs none
    templates := specScanTemplates (ph.tCells.map (fun r => newestRecords r none)) }

theorem scanPhases_decompose (before : List PhaseState) (focus : PhaseState) (after : List PhaseState) :
    scanPhases (progRingTerm (before ++ focus :: after) 2) =
      specScanPhases (before.map phaseSummary) ++
        entryOfPhaseAt before.length focus ::
          (specScanPhases (after.map phaseSummary)).map (shiftPhaseBy (before.length + 1)) := by
  rw [scanPhases_progRingTerm]
  change specScanPhases ((before ++ focus :: after).map phaseSummary) = _
  have hmap : (before ++ focus :: after).map phaseSummary =
      before.map phaseSummary ++ phaseSummary focus :: after.map phaseSummary := by
    simp [phaseSummary]
  rw [hmap, specScanPhases_append]
  have hlen : (before.map phaseSummary).length = before.length := by simp
  rw [hlen]
  have hcons : specScanPhases (phaseSummary focus :: after.map phaseSummary) =
      entryOfPhaseAt 0 focus :: (specScanPhases (after.map phaseSummary)).map shiftPhaseEntry := rfl
  rw [hcons, List.map_cons, map_shiftPhaseBy_shiftPhaseEntry]
  rfl

theorem specScanPhases_status_ne (phs : List PhaseState) (target : Option (List Bool))
    (h : ∀ ph ∈ phs, newestRecords ph.pRecs none ≠ target) :
    ∀ e ∈ specScanPhases (phs.map phaseSummary), (e.status == target) = false := by
  induction phs with
  | nil => intro _ hm; simp [specScanPhases] at hm
  | cons ph rest ih =>
      intro e hm
      have h0 : newestRecords ph.pRecs none ≠ target := h ph (by simp)
      have hrest : ∀ p2 ∈ rest, newestRecords p2.pRecs none ≠ target :=
        fun p2 hp2 => h p2 (by simp [hp2])
      simp only [List.map_cons, specScanPhases, List.mem_cons, List.mem_map] at hm
      rcases hm with rfl | ⟨e0, he0, rfl⟩
      · exact beq_eq_false_iff_ne.mpr h0
      · simpa [shiftPhaseEntry] using ih hrest e0 he0

theorem scanPhases_unique_active (before : List PhaseState) (actPh : PhaseState) (after : List PhaseState)
    (hb : ∀ ph ∈ before, newestRecords ph.pRecs none = some [false, false])
    (hact : newestRecords actPh.pRecs none = some [true, false])
    (ha : ∀ ph ∈ after, newestRecords ph.pRecs none = some [false, false]) :
    findIdxPred (fun pe => pe.status == some [true, true])
      (scanPhases (progRingTerm (before ++ actPh :: after) 2)) = none ∧
    findIdxPred (fun pe => pe.status == some [true, false])
      (scanPhases (progRingTerm (before ++ actPh :: after) 2)) =
      some (before.length, entryOfPhaseAt before.length actPh) := by
  rw [scanPhases_decompose]
  have hbNoH : ∀ e ∈ specScanPhases (before.map phaseSummary), (e.status == some [true, true]) = false :=
    specScanPhases_status_ne before _ (fun ph hp => by rw [hb ph hp]; decide)
  have haNoH0 : ∀ e ∈ specScanPhases (after.map phaseSummary), (e.status == some [true, true]) = false :=
    specScanPhases_status_ne after _ (fun ph hp => by rw [ha ph hp]; decide)
  have hbNoA : ∀ e ∈ specScanPhases (before.map phaseSummary), (e.status == some [true, false]) = false :=
    specScanPhases_status_ne before _ (fun ph hp => by rw [hb ph hp]; decide)
  have hactNoH : ((entryOfPhaseAt before.length actPh).status == some [true, true]) = false := by
    simp [entryOfPhaseAt, hact]
  have hactIsA : ((entryOfPhaseAt before.length actPh).status == some [true, false]) = true := by
    simp [entryOfPhaseAt, hact]
  constructor
  · apply findIdxPred_all_false
    intro e he
    simp only [List.mem_append, List.mem_cons, List.mem_map] at he
    rcases he with he | rfl | ⟨e0, he0, rfl⟩
    · exact hbNoH e he
    · exact hactNoH
    · simpa [shiftPhaseBy] using haNoH0 e0 he0
  · have hlen : (specScanPhases (before.map phaseSummary)).length = before.length := by
      rw [specScanPhases_length, List.length_map]
    rw [findIdxPred_append_skip _ _ _ _ hbNoA hactIsA, hlen]

theorem scanPhases_handoff_find (before : List PhaseState) (handPh : PhaseState) (after : List PhaseState)
    (hb : ∀ ph ∈ before, newestRecords ph.pRecs none ≠ some [true, true])
    (hh : newestRecords handPh.pRecs none = some [true, true]) :
    findIdxPred (fun pe => pe.status == some [true, true])
      (scanPhases (progRingTerm (before ++ handPh :: after) 2)) =
      some (before.length, entryOfPhaseAt before.length handPh) := by
  rw [scanPhases_decompose]
  have hbNoH := specScanPhases_status_ne before _ hb
  have hhIsH : ((entryOfPhaseAt before.length handPh).status == some [true, true]) = true := by
    simp [entryOfPhaseAt, hh]
  have hlen : (specScanPhases (before.map phaseSummary)).length = before.length := by
    rw [specScanPhases_length, List.length_map]
  rw [findIdxPred_append_skip _ _ _ _ hbNoH hhIsH, hlen]

theorem scanPhases_get_at (before : List PhaseState) (focus : PhaseState) (after : List PhaseState) :
    listGetOpt (scanPhases (progRingTerm (before ++ focus :: after) 2)) before.length =
      some (entryOfPhaseAt before.length focus) := by
  rw [scanPhases_decompose]
  have hlen : (specScanPhases (before.map phaseSummary)).length = before.length := by
    rw [specScanPhases_length, List.length_map]
  rw [← hlen]
  exact listGetOpt_append_focus _ _ _

theorem scanPhases_len (phases : List PhaseState) :
    (scanPhases (progRingTerm phases 2)).length = phases.length := by
  rw [scanPhases_progRingTerm, specScanPhases_length, List.length_map]


/-! ### Section 6B: Specialized Context-Lifting Wrappers for the 4 Slot Kinds -/

/-- Lift a version append on a **Queue Cell** inside `pfMachineTerm`. -/
theorem pf_lift_queue_ver_append (phases : List PhaseState)
    (qBefore : List (List Rec3)) (qFocus : List Rec3) (qAfter : List (List Rec3))
    (entry : Rec3)
    (hact : pfDecideAction (scanPhases (progRingTerm phases 2))
      (scanQueue (queueListTerm (qBefore ++ qFocus :: qAfter) 2)) =
      .writeVer (pfQueueRootPath ++ (repeatRightPath qBefore.length ++ pfLeftChildPath)) 3 entry.val) :
    ∃ k, 6 ≤ k ∧ k ≤ 56 ∧
      PFTrace k
        (pfMachineTerm phases (qBefore ++ qFocus :: qAfter))
        (pfMachineTerm phases (qBefore ++ (qFocus ++ [entry]) :: qAfter)) := by
  let verPath := pfQueueRootPath ++ (repeatRightPath qBefore.length ++ pfLeftChildPath)
  let vd := 2 + qBefore.length + 1
  let C : Term → Term := fun v =>
    pfRootTerm (depthBase 1) (progRingTerm phases 2) (queueAroundVer qBefore v qAfter 2)
  have hstart : C (pfVerTerm qFocus vd) = pfMachineTerm phases (qBefore ++ qFocus :: qAfter) := by
    dsimp [C, pfMachineTerm, vd]
    rw [queueAroundVer_eq]
  have hend : C (pfVerTerm (qFocus ++ [entry]) vd) =
      pfMachineTerm phases (qBefore ++ (qFocus ++ [entry]) :: qAfter) := by
    dsimp [C, pfMachineTerm, vd]
    rw [queueAroundVer_eq]
  obtain ⟨k, klo, khi, htr⟩ := lift_stable_version_append_to_pfTrace C verPath qFocus entry vd
    (fun v => by
      dsimp [C, verPath]
      rw [pfRootTerm_termAt_queue]
      exact queueAroundVer_termAt qBefore v qAfter 2)
    (fun p v v' hd => by
      dsimp [C, verPath]
      rw [List.append_assoc]
      exact pfRootTerm_directed_queue _ _ (queueAroundVer_directed qBefore qAfter hd 2))
    (fun v => pfRootTerm_halt_closed _ _ _ (depth_base_closed 1))
    (fun v hscan => by
      refine ⟨scanPhases (progRingTerm phases 2), scanQueue (queueListTerm (qBefore ++ qFocus :: qAfter) 2), ?_, hact⟩
      dsimp [C]
      rw [pfRootTerm_readState]
      have hscan0 : pfScanVersion 3 none v = pfScanVersion 3 none (pfVerTerm qFocus vd) :=
        hscan.trans (pfVerTerm_scan qFocus vd).symm
      have hqCongr := queueAroundVer_scan_congr qBefore v (pfVerTerm qFocus vd) qAfter hscan0 2
      rw [queueAroundVer_eq] at hqCongr
      rw [hqCongr])
  rw [hstart, hend] at htr
  exact ⟨k, klo, khi, htr⟩

/-- Lift opening a fresh **Queue Tail Cell** inside `pfMachineTerm`. -/
theorem pf_lift_queue_tail_open (phases : List PhaseState) (qCells : List (List Rec3))
    (hact : pfDecideAction (scanPhases (progRingTerm phases 2))
      (scanQueue (queueListTerm qCells 2)) =
      .openSlot (pfQueueRootPath ++ repeatRightPath qCells.length)) :
    ∃ k, (k = 6 ∨ k = 7) ∧
      PFTrace k
        (pfMachineTerm phases qCells)
        (pfMachineTerm phases (qCells ++ [[]])) := by
  let slotPath := pfQueueRootPath ++ repeatRightPath qCells.length
  let sd := 2 + qCells.length
  let C : Term → Term := fun u =>
    pfRootTerm (depthBase 1) (progRingTerm phases 2) (queueAroundTail qCells u 2)
  have hstart : C (depthBase sd) = pfMachineTerm phases qCells := by
    dsimp [C, pfMachineTerm, sd]
    rw [queueAroundTail_closed_eq]
  have hend : C (layoutTerm (.opened .unopened .unopened) (phaseAt sd).1 (phaseAt sd).2) =
      pfMachineTerm phases (qCells ++ [[]]) := by
    dsimp [C, pfMachineTerm, sd]
    rw [queueAroundTail_opened_eq]
  obtain ⟨k, hk, htr⟩ := lift_closed_opening_to_pfTrace C slotPath sd
    (fun u => by
      dsimp [C, slotPath]
      rw [pfRootTerm_termAt_queue]
      exact queueAroundTail_termAt qCells u 2)
    (fun p u u' hd => by
      dsimp [C, slotPath]
      rw [List.append_assoc]
      exact pfRootTerm_directed_queue _ _ (queueAroundTail_directed qCells hd 2))
    (fun _ _ => pfRootTerm_halt_closed _ _ _ (depth_base_closed 1))
    (fun u hu => by
      refine ⟨scanPhases (progRingTerm phases 2), scanQueue (queueListTerm qCells 2), ?_, hact⟩
      dsimp [C]
      rw [pfRootTerm_readState, queueAroundTail_scan_closed qCells u hu 2])
  rw [hstart, hend] at htr
  exact ⟨k, hk, htr⟩

/-- Lift a version append on a **Template Cell** inside `pfMachineTerm`. -/
theorem pf_lift_template_ver_append
    (pBefore : List PhaseState) (pRecs : List Rec2)
    (tBefore : List (List Rec3)) (tFocus : List Rec3) (tAfter : List (List Rec3))
    (pAfter : List PhaseState) (qCells : List (List Rec3))
    (entry : Rec3)
    (hact : pfDecideAction
      (scanPhases (progRingTerm (pBefore ++ ⟨pRecs, tBefore ++ tFocus :: tAfter⟩ :: pAfter) 2))
      (scanQueue (queueListTerm qCells 2)) =
      .writeVer (pfProgRingPath ++ (repeatRightPath pBefore.length ++ [false, true, true, false, true]) ++
        (repeatRightPath tBefore.length ++ pfLeftChildPath)) 3 entry.val) :
    ∃ k, 6 ≤ k ∧ k ≤ 56 ∧
      PFTrace k
        (pfMachineTerm (pBefore ++ ⟨pRecs, tBefore ++ tFocus :: tAfter⟩ :: pAfter) qCells)
        (pfMachineTerm (pBefore ++ ⟨pRecs, tBefore ++ (tFocus ++ [entry]) :: tAfter⟩ :: pAfter) qCells) := by
  let tListRel := repeatRightPath pBefore.length ++ [false, true, true, false, true]
  let tCellRel := repeatRightPath tBefore.length ++ pfLeftChildPath
  let verPath := pfProgRingPath ++ tListRel ++ tCellRel
  let td := 2 + pBefore.length + 2
  let vd := td + tBefore.length + 1
  let C : Term → Term := fun v =>
    pfRootTerm (depthBase 1)
      (progAroundTList pBefore pRecs (templateAroundVer tBefore v tAfter td) pAfter 2)
      (queueListTerm qCells 2)
  have hstart : C (pfVerTerm tFocus vd) =
      pfMachineTerm (pBefore ++ ⟨pRecs, tBefore ++ tFocus :: tAfter⟩ :: pAfter) qCells := by
    dsimp [C, pfMachineTerm, vd, td]
    rw [templateAroundVer_eq, progAroundTList_eq]
  have hend : C (pfVerTerm (tFocus ++ [entry]) vd) =
      pfMachineTerm (pBefore ++ ⟨pRecs, tBefore ++ (tFocus ++ [entry]) :: tAfter⟩ :: pAfter) qCells := by
    dsimp [C, pfMachineTerm, vd, td]
    rw [templateAroundVer_eq, progAroundTList_eq]
  obtain ⟨k, klo, khi, htr⟩ := lift_stable_version_append_to_pfTrace C verPath tFocus entry vd
    (fun v => by
      dsimp [C, verPath, tListRel, tCellRel]
      rw [List.append_assoc, pfRootTerm_termAt_prog, pf_termAt_append,
        progAroundTList_termAt]
      exact templateAroundVer_termAt tBefore v tAfter td)
    (fun p v v' hd => by
      dsimp [C, verPath, tListRel, tCellRel]
      have h1 := templateAroundVer_directed tBefore tAfter hd td
      have h2 := progAroundTList_directed pBefore pRecs pAfter h1 2
      have h3 := pfRootTerm_directed_prog (depthBase 1) (queueListTerm qCells 2) h2
      simpa [List.append_assoc] using h3)
    (fun _ => pfRootTerm_halt_closed _ _ _ (depth_base_closed 1))
    (fun v hscan => by
      refine ⟨scanPhases (progRingTerm (pBefore ++ ⟨pRecs, tBefore ++ tFocus :: tAfter⟩ :: pAfter) 2),
        scanQueue (queueListTerm qCells 2), ?_, hact⟩
      dsimp [C]
      rw [pfRootTerm_readState]
      have hscan0 : pfScanVersion 3 none v = pfScanVersion 3 none (pfVerTerm tFocus vd) :=
        hscan.trans (pfVerTerm_scan tFocus vd).symm
      have htCongr := templateAroundVer_scan_congr tBefore v (pfVerTerm tFocus vd) tAfter hscan0 td
      rw [templateAroundVer_eq] at htCongr
      have hpCongr := progAroundTList_scan_congr pBefore pRecs _ _ pAfter htCongr 2
      rw [progAroundTList_eq] at hpCongr
      rw [hpCongr])
  rw [hstart, hend] at htr
  exact ⟨k, klo, khi, htr⟩

/-- Lift a version append on a **Phase Status Chain** inside `pfMachineTerm`. -/
theorem pf_lift_phase_ver_append
    (pBefore : List PhaseState) (pRecs : List Rec2) (tCells : List (List Rec3))
    (pAfter : List PhaseState) (qCells : List (List Rec3))
    (entry : Rec2)
    (hact : pfDecideAction
      (scanPhases (progRingTerm (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) 2))
      (scanQueue (queueListTerm qCells 2)) =
      .writeVer (pfProgRingPath ++ (repeatRightPath pBefore.length ++ [false, true, false, true])) 2 entry.val) :
    ∃ k, 6 ≤ k ∧ k ≤ 42 ∧
      PFTrace k
        (pfMachineTerm (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) qCells)
        (pfMachineTerm (pBefore ++ ⟨pRecs ++ [entry], tCells⟩ :: pAfter) qCells) := by
  let verPath := pfProgRingPath ++ (repeatRightPath pBefore.length ++ [false, true, false, true])
  let vd := 2 + pBefore.length + 2
  let C : Term → Term := fun v =>
    pfRootTerm (depthBase 1) (progAroundPhaseVer pBefore v tCells pAfter 2) (queueListTerm qCells 2)
  have hstart : C (pfVerTerm pRecs vd) =
      pfMachineTerm (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) qCells := by
    dsimp [C, pfMachineTerm, vd]
    rw [progAroundPhaseVer_eq]
  have hend : C (pfVerTerm (pRecs ++ [entry]) vd) =
      pfMachineTerm (pBefore ++ ⟨pRecs ++ [entry], tCells⟩ :: pAfter) qCells := by
    dsimp [C, pfMachineTerm, vd]
    rw [progAroundPhaseVer_eq]
  obtain ⟨k, klo, khi, htr⟩ := lift_stable_version_append_to_pfTrace C verPath pRecs entry vd
    (fun v => by
      dsimp [C, verPath]
      rw [pfRootTerm_termAt_prog]
      exact progAroundPhaseVer_termAt pBefore v tCells pAfter 2)
    (fun p v v' hd => by
      dsimp [C, verPath]
      rw [List.append_assoc]
      exact pfRootTerm_directed_prog _ _ (progAroundPhaseVer_directed pBefore tCells pAfter hd 2))
    (fun _ => pfRootTerm_halt_closed _ _ _ (depth_base_closed 1))
    (fun v hscan => by
      refine ⟨scanPhases (progRingTerm (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) 2),
        scanQueue (queueListTerm qCells 2), ?_, hact⟩
      dsimp [C]
      rw [pfRootTerm_readState]
      have hscan0 : pfScanVersion 2 none v = pfScanVersion 2 none (pfVerTerm pRecs vd) :=
        hscan.trans (pfVerTerm_scan pRecs vd).symm
      have hpCongr := progAroundPhaseVer_scan_congr pBefore v (pfVerTerm pRecs vd) tCells pAfter hscan0 2
      rw [progAroundPhaseVer_eq] at hpCongr
      rw [hpCongr])
  rw [hstart, hend] at htr
  exact ⟨k, klo, khi, htr⟩

/-- Lift opening the **Halt Flag** inside `pfMachineTerm` when the queue is empty. -/
theorem pf_lift_halt_flag_open (phases : List PhaseState) (qCells : List (List Rec3))
    (hact : pfDecideAction (scanPhases (progRingTerm phases 2)) (scanQueue (queueListTerm qCells 2)) =
      .openSlot pfFlagPath) :
    ∃ k reached, (k = 6 ∨ k = 7) ∧
      PFTrace k (pfMachineTerm phases qCells) reached ∧
      pfRootHalt reached = true := by
  let C : Term → Term := fun f =>
    pfRootTerm f (progRingTerm phases 2) (queueListTerm qCells 2)
  obtain ⟨k, hk, htr⟩ := lift_closed_opening_to_pfTrace C pfFlagPath 1
    (fun f => pfRootTerm_termAt_flag f _ _)
    (fun p f1 f2 hd => pfRootTerm_directed_flag _ _ hd)
    (fun f hf => pfRootTerm_halt_closed f _ _ hf)
    (fun f _ => ⟨scanPhases (progRingTerm phases 2), scanQueue (queueListTerm qCells 2),
      pfRootTerm_readState f _ _, hact⟩)
  refine ⟨k, C (layoutTerm (.opened .unopened .unopened) (phaseAt 1).1 (phaseAt 1).2), hk, htr, ?_⟩
  dsimp [C, pfRootTerm, pfRootHalt]
  rw [layout_opened_phase _ _ _ (phase_at_good 1)]
  simp [haltObserved, parse_frame, flagValue]


/-! ### Section 6C: Complete CTS Macro-Step Simulation from `PFConfigRep` -/

def PhaseMatchesSpec (ph : PhaseState) (isActive : Bool) (app : List Bool) : Prop :=
  newestRecords ph.pRecs none = some (if isActive then [true, false] else [false, false]) ∧
  TemplateMatchesIdle ph.tCells app

def PhasesInactiveMatch : List PhaseState → List (List Bool) → Prop
  | [], [] => True
  | ph :: phs, app :: apps => PhaseMatchesSpec ph false app ∧ PhasesInactiveMatch phs apps
  | _, _ => False

theorem phasesInactiveMatch_length {phs : List PhaseState} {apps : List (List Bool)}
    (h : PhasesInactiveMatch phs apps) : phs.length = apps.length := by
  induction phs generalizing apps with
  | nil =>
      cases apps with
      | nil => rfl
      | cons _ _ => simp [PhasesInactiveMatch] at h
  | cons _ rs ih =>
      cases apps with
      | nil => simp [PhasesInactiveMatch] at h
      | cons _ as => simp [ih h.2]

theorem phasesInactiveMatch_append {p1 p2 : List PhaseState} {a1 a2 : List (List Bool)}
    (h1 : PhasesInactiveMatch p1 a1) (h2 : PhasesInactiveMatch p2 a2) :
    PhasesInactiveMatch (p1 ++ p2) (a1 ++ a2) := by
  induction p1 generalizing a1 with
  | nil =>
      cases a1 with
      | nil => exact h2
      | cons _ _ => simp [PhasesInactiveMatch] at h1
  | cons _ _ ih =>
      cases a1 with
      | nil => simp [PhasesInactiveMatch] at h1
      | cons _ _ => exact ⟨h1.1, ih h1.2⟩

theorem phasesInactiveMatch_status {phs : List PhaseState} {apps : List (List Bool)}
    (h : PhasesInactiveMatch phs apps) :
    ∀ ph ∈ phs, newestRecords ph.pRecs none = some [false, false] := by
  induction phs generalizing apps with
  | nil => intro _ hm; simp at hm
  | cons p0 rs ih =>
      cases apps with
      | nil => simp [PhasesInactiveMatch] at h
      | cons a0 as =>
          intro ph hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm'
          · exact h.1.1
          · exact ih h.2 ph hm'

def PhasesMatchProgram (progPhases : List (List Bool)) (activeIdx : Nat) (phases : List PhaseState) : Prop :=
  ∃ pBefore actPh pAfter appBefore appAct appAfter,
    phases = pBefore ++ actPh :: pAfter ∧
    progPhases = appBefore ++ appAct :: appAfter ∧
    pBefore.length = activeIdx ∧
    appBefore.length = activeIdx ∧
    PhasesInactiveMatch pBefore appBefore ∧
    PhaseMatchesSpec actPh true appAct ∧
    PhasesInactiveMatch pAfter appAfter

theorem initPhaseStatesAux_false_matches (apps : List (List Bool)) :
    PhasesInactiveMatch (initPhaseStatesAux false apps) apps := by
  induction apps with
  | nil => trivial
  | cons app rest ih =>
      exact ⟨⟨rfl, initTemplateCells_matches app⟩, ih⟩

theorem initPhaseStates_matches (P : CTSProgram) :
    PhasesMatchProgram P.phases 0 (initPhaseStates P) := by
  cases hp : P.phases with
  | nil => exact False.elim (P.nonempty hp)
  | cons app0 rest =>
      refine ⟨[], ⟨[recActive], initTemplateCells app0⟩, initPhaseStatesAux false rest,
        [], app0, rest, ?_, rfl, rfl, rfl, trivial, ⟨rfl, initTemplateCells_matches app0⟩,
        initPhaseStatesAux_false_matches rest⟩
      simp [initPhaseStates, hp, initPhaseStatesAux]

theorem list_get_at_split {α : Type} (before : List α) (focus : α) (after : List α)
    (idx : Nat) (hidx : before.length = idx) (hlt : idx < (before ++ focus :: after).length) :
    (before ++ focus :: after).get ⟨idx, hlt⟩ = focus := by
  subst idx
  induction before with
  | nil => rfl
  | cons _ rest ih => exact ih (by simp only [List.cons_append, List.length_cons] at hlt; omega)

def PFConfigRep (P : CTSProgram) (cfg : CTSConfig)
    (phases : List PhaseState) (qCells : List (List Rec3)) : Prop :=
  cfg.phaseIdx < P.phases.length ∧
  PhasesMatchProgram P.phases cfg.phaseIdx phases ∧
  ∃ consumed unconsumed,
    qCells = consumed ++ unconsumed ∧
    (∀ r ∈ consumed, IsConsumedCell r) ∧
    QueueMatchesWord unconsumed cfg.queue

theorem initProgramFreeCTS_rep (P : CTSProgram) (w : List Bool) :
    PFConfigRep P (initCTSConfig w) (initPhaseStates P) (initQueueCells w) :=
  ⟨ctsProgram_length_pos P, initPhaseStates_matches P, [], initQueueCells w, rfl,
    fun _ hm => by simp at hm, initQueueCells_matches w⟩

/-- Halting simulation at clean empty-queue boundary (`cfg.queue = []`). -/
theorem cts_halt_simulated_by_pfTrace (P : CTSProgram) (idx : Nat)
    (phases : List PhaseState) (qCells : List (List Rec3))
    (hrep : PFConfigRep P ⟨idx, []⟩ phases qCells) :
    ∃ k reached, (k = 6 ∨ k = 7) ∧
      PFTrace k (pfMachineTerm phases qCells) reached ∧
      pfRootHalt reached = true := by
  obtain ⟨_, ⟨pBefore, actPh, pAfter, appBefore, appAct, appAfter,
    rfl, _, _, _, hbInact, hactSpec, haInact⟩, consumed, unconsumed, rfl, hcons, hqWord⟩ := hrep
  cases unconsumed with
  | cons _ _ => simp [QueueMatchesWord] at hqWord
  | nil =>
      rw [List.append_nil]
      obtain ⟨hnoH, hfindA⟩ := scanPhases_unique_active pBefore actPh pAfter
        (phasesInactiveMatch_status hbInact) hactSpec.1 (phasesInactiveMatch_status haInact)
      obtain ⟨hnoCons, hnoUncons⟩ := scanQueue_halted_shape consumed hcons
      apply pf_lift_halt_flag_open
      unfold pfDecideAction
      rw [hnoH, hfindA, hnoCons, hnoUncons]

/-- Stage A helper: Arm all `IDLE` template cells left-to-right when front queue bit is `true`. -/
theorem pf_trace_arm_templates
    (pBefore : List PhaseState) (pRecs : List Rec2) (pAfter : List PhaseState)
    (consumed : List (List Rec3)) (u0 : List Rec3) (uRest : List (List Rec3))
    (hbInact : ∀ ph ∈ pBefore, newestRecords ph.pRecs none = some [false, false])
    (hpAct : newestRecords pRecs none = some [true, false])
    (haInact : ∀ ph ∈ pAfter, newestRecords ph.pRecs none = some [false, false])
    (hcons : ∀ r ∈ consumed, IsConsumedCell r)
    (hu0 : IsUnconsumedFor u0 true)
    (huRest : AllUnconsumed uRest) :
    ∀ (tIdle : List (List Rec3)) (appIdle : List Bool)
      (tArmed : List (List Rec3)) (appArmed : List Bool),
      TemplateMatchesArmed tArmed appArmed →
      TemplateMatchesIdle tIdle appIdle →
      ∃ k tArmedOut,
        PFTrace k
          (pfMachineTerm (pBefore ++ ⟨pRecs, tArmed ++ tIdle⟩ :: pAfter) (consumed ++ u0 :: uRest))
          (pfMachineTerm (pBefore ++ ⟨pRecs, tArmedOut⟩ :: pAfter) (consumed ++ u0 :: uRest)) ∧
        TemplateMatchesArmed tArmedOut (appArmed ++ appIdle) := by
  intro tIdle
  induction tIdle with
  | nil =>
      intro appIdle tArmed appArmed hArmed hIdle
      cases appIdle with
      | cons _ _ => simp [TemplateMatchesIdle] at hIdle
      | nil =>
          simp only [List.append_nil]
          exact ⟨0, tArmed, PFTrace.zero _, hArmed⟩
  | cons t0 tRest ih =>
      intro appIdle tArmed appArmed hArmed hIdle
      cases appIdle with
      | nil => simp [TemplateMatchesIdle] at hIdle
      | cons sbit sRest =>
          rcases hIdle with ⟨ht0, htRest⟩
          obtain ⟨hnoH, hfindA⟩ := scanPhases_unique_active pBefore ⟨pRecs, tArmed ++ t0 :: tRest⟩ pAfter
            hbInact hpAct haInact
          obtain ⟨hqCons, hqUncons⟩ := scanQueue_front_unconsumed_shape consumed u0 uRest true hcons hu0 huRest
          have htIdle := specScanTemplates_armed_then_idle tArmed appArmed t0 tRest sbit hArmed ht0
          obtain ⟨k1, _, _, htr1⟩ := pf_lift_template_ver_append pBefore pRecs tArmed t0 tRest pAfter
            (consumed ++ u0 :: uRest) (recArmed sbit) (by
              unfold pfDecideAction
              rw [hnoH, hfindA, hqCons, hqUncons]
              dsimp only [ ↓reduceIte, entryOfPhaseAt]
              rw [htIdle]
              simp [List.append_assoc, recArmed])
          have ht0Armed : IsArmedFor (t0 ++ [recArmed sbit]) sbit :=
            newest_records_append t0 (recArmed sbit) none
          have hArmedNext : TemplateMatchesArmed (tArmed ++ [t0 ++ [recArmed sbit]]) (appArmed ++ [sbit]) :=
            templateMatchesArmed_append hArmed ⟨ht0Armed, trivial⟩
          have hlistEq : tArmed ++ (t0 ++ [recArmed sbit]) :: tRest =
              (tArmed ++ [t0 ++ [recArmed sbit]]) ++ tRest := by simp [List.append_assoc]
          rw [hlistEq] at htr1
          obtain ⟨k2, tArmedOut, htr2, hArmedFinal⟩ :=
            ih sRest (tArmed ++ [t0 ++ [recArmed sbit]]) (appArmed ++ [sbit]) hArmedNext htRest
          have happEq : (appArmed ++ [sbit]) ++ sRest = appArmed ++ sbit :: sRest := by simp [List.append_assoc]
          rw [happEq] at hArmedFinal
          exact ⟨k1 + k2, tArmedOut, pfTrace_trans htr1 htr2, hArmedFinal⟩

/-- Stage B helper: Copy ONE `ARMED` template bit `sbit` to the tail of the queue via the
    5-subphase atomic handshake (`ARMED -> APPENDING -> OPEN_TAIL -> STAGING -> IDLE -> UNCONSUMED`). -/
theorem pf_trace_copy_one_bit
    (pBefore : List PhaseState) (pRecs : List Rec2) (pAfter : List PhaseState)
    (tDone : List (List Rec3)) (appDone : List Bool)
    (tFocus : List Rec3) (sbit : Bool)
    (tRem : List (List Rec3)) (appRem : List Bool)
    (consumed : List (List Rec3)) (c0 : List Rec3) (b : Bool) (uCells : List (List Rec3))
    (hbInact : ∀ ph ∈ pBefore, newestRecords ph.pRecs none = some [false, false])
    (hpAct : newestRecords pRecs none = some [true, false])
    (haInact : ∀ ph ∈ pAfter, newestRecords ph.pRecs none = some [false, false])
    (htDone : TemplateMatchesIdle tDone appDone)
    (htFocus : IsArmedFor tFocus sbit)
    (htRem : TemplateMatchesArmed tRem appRem)
    (hcons : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b])
    (huCells : AllUnconsumed uCells) :
    ∃ k,
      PFTrace k
        (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tFocus :: tRem⟩ :: pAfter)
          (consumed ++ c0 :: uCells))
        (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ (tFocus ++ [recAppending sbit, recIdle sbit]) :: tRem⟩ :: pAfter)
          (consumed ++ c0 :: (uCells ++ [[recStaging sbit, recUnconsumed sbit]]))) := by
  -- Sub-phase B1: tFocus ARMED -> APPENDING
  let tFocus1 := tFocus ++ [recAppending sbit]
  let tFocus2 := tFocus1 ++ [recIdle sbit]
  obtain ⟨hnoH1, hfindA1⟩ := scanPhases_unique_active pBefore ⟨pRecs, tDone ++ tFocus :: tRem⟩ pAfter
    hbInact hpAct haInact
  obtain ⟨hqC1, hqSt1, _, hqTp1⟩ := scanQueue_consuming_clean_shape consumed c0 uCells b hcons hc0 huCells
  obtain ⟨htArm1, htApp1⟩ := specScanTemplates_idle_then_armed tDone appDone tFocus tRem appRem sbit
    htDone htFocus htRem
  obtain ⟨k1, _, _, htr1⟩ := pf_lift_template_ver_append pBefore pRecs tDone tFocus tRem pAfter
    (consumed ++ c0 :: uCells) (recAppending sbit) (by
      unfold pfDecideAction
      rw [hnoH1, hfindA1, hqC1, hqSt1]
      dsimp only [entryOfPhaseAt]
      rw [htApp1, htArm1]
      simp [List.append_assoc, recAppending])
  have htFocus1App : IsAppendingFor tFocus1 sbit := newest_records_append tFocus (recAppending sbit) none
  have htApp2 := specScanTemplates_idle_then_appending tDone appDone tFocus1 tRem sbit htDone htFocus1App
  obtain ⟨hnoH2, hfindA2⟩ := scanPhases_unique_active pBefore ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ pAfter
    hbInact hpAct haInact
  -- Sub-phase B2: Open fresh queue tail cell
  obtain ⟨_, hqSt2, hqUi2, _⟩ := scanQueue_consuming_clean_shape consumed c0 uCells b hcons hc0 huCells
  obtain ⟨k2, _, htr2⟩ := pf_lift_queue_tail_open (pBefore ++ ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ :: pAfter)
    (consumed ++ c0 :: uCells) (by
      unfold pfDecideAction
      rw [hnoH2, hfindA2, hqC1, hqSt1, hqUi2, hqTp1]
      dsimp only [entryOfPhaseAt]
      rw [htApp2])
  -- Sub-phase B3: Write STAGING sbit to uninit tail cell `[]`
  obtain ⟨hqC3, hqSt3, hqUi3⟩ := scanQueue_consuming_uninit_shape consumed c0 uCells b hcons hc0 huCells
  obtain ⟨k3, _, _, htr3⟩ := pf_lift_queue_ver_append (pBefore ++ ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ :: pAfter)
    (consumed ++ c0 :: uCells) [] [] (recStaging sbit) (by
      unfold pfDecideAction
      rw [hnoH2, hfindA2, hqC3, hqSt3, hqUi3]
      dsimp only [entryOfPhaseAt]
      rw [htApp2]
      rfl)
  -- Sub-phase B4: Reset tFocus1 APPENDING -> IDLE
  obtain ⟨hqC4, hqSt4, _⟩ := scanQueue_consuming_staging_shape consumed c0 uCells b sbit hcons hc0 huCells
  obtain ⟨k4, _, _, htr4⟩ := pf_lift_template_ver_append pBefore pRecs tDone tFocus1 tRem pAfter
    (consumed ++ c0 :: uCells ++ [[recStaging sbit]]) (recIdle sbit) (by
      unfold pfDecideAction
      rw [hnoH2, hfindA2, hqC4, hqSt4]
      dsimp only [entryOfPhaseAt]
      rw [htApp2]
      simp [List.append_assoc, recIdle])
  -- Sub-phase B5: Commit tail cell STAGING -> UNCONSUMED
  have htFocus2Idle : IsIdleFor tFocus2 sbit := newest_records_append tFocus1 (recIdle sbit) none
  obtain ⟨hnoH5, hfindA5⟩ := scanPhases_unique_active pBefore ⟨pRecs, tDone ++ tFocus2 :: tRem⟩ pAfter
    hbInact hpAct haInact
  have htApp5 : (specScanTemplates ((tDone ++ tFocus2 :: tRem).map (fun r => newestRecords r none))).firstAppending = none := by
    have hsplit : tDone ++ tFocus2 :: tRem = (tDone ++ [tFocus2]) ++ tRem := by simp [List.append_assoc]
    rw [hsplit]
    have hd2 : TemplateMatchesIdle (tDone ++ [tFocus2]) (appDone ++ [sbit]) :=
      templateMatchesIdle_append htDone ⟨htFocus2Idle, trivial⟩
    cases htrm : tRem with
    | nil =>
        rw [List.append_nil]
        exact (specScanTemplates_allIdle_noArmed_noApp hd2).2
    | cons tr0 trs =>
        cases appRem with
        | nil => rw [htrm] at htRem; simp [TemplateMatchesArmed] at htRem
        | cons sb0 sbs =>
            rw [htrm] at htRem
            exact (specScanTemplates_idle_then_armed (tDone ++ [tFocus2]) (appDone ++ [sbit])
              tr0 trs sbs sb0 hd2 htRem.1 htRem.2).2
  obtain ⟨k5, _, _, htr5⟩ := pf_lift_queue_ver_append (pBefore ++ ⟨pRecs, tDone ++ tFocus2 :: tRem⟩ :: pAfter)
    (consumed ++ c0 :: uCells) [recStaging sbit] [] (recUnconsumed sbit) (by
      unfold pfDecideAction
      rw [hnoH5, hfindA5, hqC4, hqSt4]
      dsimp only [entryOfPhaseAt]
      rw [htApp5]
      rfl)
  have hqEq : (consumed ++ c0 :: uCells) ++ [[recStaging sbit, recUnconsumed sbit]] =
      consumed ++ c0 :: (uCells ++ [[recStaging sbit, recUnconsumed sbit]]) := by
    simp [List.append_assoc]
  have htr3' : PFTrace k3
      (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ :: pAfter) (consumed ++ c0 :: uCells ++ [[]]))
      (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ :: pAfter) (consumed ++ c0 :: uCells ++ [[recStaging sbit]])) := by
    simpa [List.append_assoc] using htr3
  have htr5' : PFTrace k5
      (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tFocus2 :: tRem⟩ :: pAfter) (consumed ++ c0 :: uCells ++ [[recStaging sbit]]))
      (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ (tFocus ++ [recAppending sbit, recIdle sbit]) :: tRem⟩ :: pAfter)
        (consumed ++ c0 :: (uCells ++ [[recStaging sbit, recUnconsumed sbit]]))) := by
    simpa [tFocus2, tFocus1, List.append_assoc] using htr5
  exact ⟨k1 + (k2 + (k3 + (k4 + k5))),
    pfTrace_trans htr1 (pfTrace_trans htr2 (pfTrace_trans htr3' (pfTrace_trans htr4 htr5')))⟩

/-- Stage B loop: Copy ALL `ARMED` template cells one-by-one to the queue tail. -/
theorem pf_trace_copy_all_bits
    (pBefore : List PhaseState) (pRecs : List Rec2) (pAfter : List PhaseState)
    (consumed : List (List Rec3)) (c0 : List Rec3) (b : Bool)
    (hbInact : ∀ ph ∈ pBefore, newestRecords ph.pRecs none = some [false, false])
    (hpAct : newestRecords pRecs none = some [true, false])
    (haInact : ∀ ph ∈ pAfter, newestRecords ph.pRecs none = some [false, false])
    (hcons : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b]) :
    ∀ (tRem : List (List Rec3)) (appRem : List Bool)
      (tDone : List (List Rec3)) (appDone : List Bool)
      (uCells : List (List Rec3)) (qWord : List Bool),
      TemplateMatchesIdle tDone appDone →
      TemplateMatchesArmed tRem appRem →
      QueueMatchesWord uCells qWord →
      ∃ k tIdleOut uCellsOut,
        PFTrace k
          (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tRem⟩ :: pAfter) (consumed ++ c0 :: uCells))
          (pfMachineTerm (pBefore ++ ⟨pRecs, tIdleOut⟩ :: pAfter) (consumed ++ c0 :: uCellsOut)) ∧
        TemplateMatchesIdle tIdleOut (appDone ++ appRem) ∧
        QueueMatchesWord uCellsOut (qWord ++ appRem) := by
  intro tRem
  induction tRem with
  | nil =>
      intro appRem tDone appDone uCells qWord htDone htRem hqWord
      cases appRem with
      | cons _ _ => simp [TemplateMatchesArmed] at htRem
      | nil =>
          simp only [List.append_nil]
          exact ⟨0, tDone, uCells, PFTrace.zero _, htDone, hqWord⟩
  | cons t0 tRest ih =>
      intro appRem tDone appDone uCells qWord htDone htRem hqWord
      cases appRem with
      | nil => simp [TemplateMatchesArmed] at htRem
      | cons sbit sRest =>
          rcases htRem with ⟨ht0, htRest⟩
          obtain ⟨k1, htr1⟩ := pf_trace_copy_one_bit pBefore pRecs pAfter tDone appDone t0 sbit tRest sRest
            consumed c0 b uCells hbInact hpAct haInact htDone ht0 htRest hcons hc0
            (queueMatchesWord_allUnconsumed hqWord)
          let t0Done := t0 ++ [recAppending sbit, recIdle sbit]
          let newQCell := [recStaging sbit, recUnconsumed sbit]
          have ht0Idle : IsIdleFor t0Done sbit := by
            have hassoc : t0Done = (t0 ++ [recAppending sbit]) ++ [recIdle sbit] := by
              simp [t0Done, List.append_assoc]
            rw [hassoc]
            exact newest_records_append _ (recIdle sbit) none
          have htDoneNext : TemplateMatchesIdle (tDone ++ [t0Done]) (appDone ++ [sbit]) :=
            templateMatchesIdle_append htDone ⟨ht0Idle, trivial⟩
          have hqNew : QueueMatchesWord (uCells ++ [newQCell]) (qWord ++ [sbit]) :=
            queueMatchesWord_append hqWord ⟨rfl, trivial⟩
          have htSplit : tDone ++ t0Done :: tRest = (tDone ++ [t0Done]) ++ tRest := by
            simp [List.append_assoc]
          rw [htSplit] at htr1
          obtain ⟨k2, tIdleOut, uCellsOut, htr2, htFinal, hqFinal⟩ :=
            ih sRest (tDone ++ [t0Done]) (appDone ++ [sbit]) (uCells ++ [newQCell]) (qWord ++ [sbit])
              htDoneNext htRest hqNew
          have happEq : (appDone ++ [sbit]) ++ sRest = appDone ++ sbit :: sRest := by simp [List.append_assoc]
          have hqwEq : (qWord ++ [sbit]) ++ sRest = qWord ++ sbit :: sRest := by simp [List.append_assoc]
          rw [happEq] at htFinal
          rw [hqwEq] at hqFinal
          exact ⟨k1 + k2, tIdleOut, uCellsOut, pfTrace_trans htr1 htr2, htFinal, hqFinal⟩

/-- Stage C helper: Advance active phase `idx ↦ (idx + 1) % P.phases.length` via `HANDOFF`
    while marking the front `CONSUMING` queue cell as `CONSUMED`. -/
theorem pf_trace_handoff_and_advance (P : CTSProgram) (idx : Nat)
    (pBefore : List PhaseState) (pRecs : List Rec2) (tCells : List (List Rec3)) (pAfter : List PhaseState)
    (appBefore : List (List Bool)) (appAct : List Bool) (appAfter : List (List Bool))
    (consumed : List (List Rec3)) (c0 : List Rec3) (b : Bool) (uCells : List (List Rec3)) (nextWord : List Bool)
    (hprog : P.phases = appBefore ++ appAct :: appAfter)
    (hpIdx : pBefore.length = idx)
    (haIdx : appBefore.length = idx)
    (hbMatch : PhasesInactiveMatch pBefore appBefore)
    (hpAct : newestRecords pRecs none = some [true, false])
    (htIdle : TemplateMatchesIdle tCells appAct)
    (haMatch : PhasesInactiveMatch pAfter appAfter)
    (hcons : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b])
    (hqWord : QueueMatchesWord uCells nextWord) :
    ∃ k phasesOut qCellsOut, 18 ≤ k ∧
      PFTrace k
        (pfMachineTerm (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) (consumed ++ c0 :: uCells))
        (pfMachineTerm phasesOut qCellsOut) ∧
      PFConfigRep P ⟨(idx + 1) % P.phases.length, nextWord⟩ phasesOut qCellsOut := by
  have hbInact := phasesInactiveMatch_status hbMatch
  have haInact := phasesInactiveMatch_status haMatch
  have huAll := queueMatchesWord_allUnconsumed hqWord
  -- C1: Mark active phase HANDOFF ([true, true])
  obtain ⟨hnoH1, hfindA1⟩ := scanPhases_unique_active pBefore ⟨pRecs, tCells⟩ pAfter hbInact hpAct haInact
  obtain ⟨hqC1, hqSt1, _, _⟩ := scanQueue_consuming_clean_shape consumed c0 uCells b hcons hc0 huAll
  obtain ⟨htNoArm, htNoApp⟩ := specScanTemplates_allIdle_noArmed_noApp htIdle
  obtain ⟨k1, klo1, _, htr1⟩ := pf_lift_phase_ver_append pBefore pRecs tCells pAfter
    (consumed ++ c0 :: uCells) recHandoff (by
      unfold pfDecideAction
      rw [hnoH1, hfindA1, hqC1, hqSt1]
      dsimp only [entryOfPhaseAt]
      rw [htNoApp, htNoArm]
      rfl)
  let pRecsH := pRecs ++ [recHandoff]
  let handPh : PhaseState := ⟨pRecsH, tCells⟩
  have hpHand : newestRecords pRecsH none = some [true, true] :=
    newest_records_append pRecs recHandoff none
  have hbNeH : ∀ ph ∈ pBefore, newestRecords ph.pRecs none ≠ some [true, true] :=
    fun ph hp => by rw [hbInact ph hp]; decide
  have hfindH2 := scanPhases_handoff_find pBefore handPh pAfter hbNeH hpHand
  -- C2: Mark consuming queue cell c0 as CONSUMED ([true, true, b])
  obtain ⟨k2, klo2, _, htr2⟩ := pf_lift_queue_ver_append (pBefore ++ handPh :: pAfter)
    consumed c0 uCells (recConsumed b) (by
      unfold pfDecideAction
      rw [hfindH2, hqC1]
      rfl)
  let c0Done := c0 ++ [recConsumed b]
  have hc0Cons : IsConsumedCell c0Done := ⟨b, newest_records_append c0 (recConsumed b) none⟩
  have hconsNext : ∀ r ∈ consumed ++ [c0Done], IsConsumedCell r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | rfl
    · exact hcons r hr
    · exact hc0Cons
  have hqShift : consumed ++ c0Done :: uCells = (consumed ++ [c0Done]) ++ uCells := by
    simp [List.append_assoc]
  have hqNoCons : (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)).consuming = none := by
    cases uCells with
    | nil =>
        rw [List.append_nil]
        exact (scanQueue_halted_shape (consumed ++ [c0Done]) hconsNext).1
    | cons u0 urs =>
        cases nextWord with
        | nil => simp [QueueMatchesWord] at hqWord
        | cons nb nbs =>
            exact (scanQueue_front_unconsumed_shape (consumed ++ [c0Done]) u0 urs nb
              hconsNext hqWord.1 (queueMatchesWord_allUnconsumed hqWord.2)).1
  rw [hqShift] at htr2
  -- C3: Split on single-phase vs non-wraparound vs wraparound
  have hlenBefore := phasesInactiveMatch_length hbMatch
  have hlenAfter := phasesInactiveMatch_length haMatch
  cases pAfter with
  | cons nxtPh pAfterRest =>
      cases appAfter with
      | nil => simp [PhasesInactiveMatch] at haMatch
      | cons nxtApp appAfterRest =>
          rcases haMatch with ⟨hnxtSpec, haRestMatch⟩
          have hlenGe2 : ((scanPhases (progRingTerm (pBefore ++ handPh :: nxtPh :: pAfterRest) 2)).length == 1) = false := by
            rw [scanPhases_len]
            simp only [List.length_append, List.length_cons]
            exact beq_eq_false_iff_ne.mpr (by omega)
          have hmodEq : (pBefore.length + 1) % (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPh :: pAfterRest) 2)).length =
              (pBefore ++ [handPh]).length := by
            rw [scanPhases_len]
            simp only [List.length_append, List.length_cons, List.length_nil]
            exact Nat.mod_eq_of_lt (by omega)
          have hgetNxt : listGetOpt (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPh :: pAfterRest) 2))
              (pBefore ++ [handPh]).length =
              some (entryOfPhaseAt (pBefore ++ [handPh]).length nxtPh) := by
            have heq : pBefore ++ handPh :: nxtPh :: pAfterRest =
                (pBefore ++ [handPh]) ++ nxtPh :: pAfterRest := by simp [List.append_assoc]
            rw [heq]
            exact scanPhases_get_at (pBefore ++ [handPh]) nxtPh pAfterRest
          have hnxtNotAct : ((entryOfPhaseAt (pBefore ++ [handPh]).length nxtPh).status == some [true, false]) = false := by
            simp [entryOfPhaseAt, hnxtSpec.1]
          -- C3a: Activate nxtPh
          have htr3a_pre : pfDecideAction
              (scanPhases (progRingTerm ((pBefore ++ [handPh]) ++ ⟨nxtPh.pRecs, nxtPh.tCells⟩ :: pAfterRest) 2))
              (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)) =
              .writeVer (pfProgRingPath ++ (repeatRightPath (pBefore ++ [handPh]).length ++ [false, true, false, true]))
                2 recActive.val := by
            have heq : (pBefore ++ [handPh]) ++ ⟨nxtPh.pRecs, nxtPh.tCells⟩ :: pAfterRest =
                pBefore ++ handPh :: nxtPh :: pAfterRest := by
              cases nxtPh; simp [List.append_assoc]
            rw [heq]
            unfold pfDecideAction
            rw [hfindH2, hqNoCons, hlenGe2]
            simp only [Bool.false_eq_true, ↓reduceIte, hmodEq, hgetNxt, hnxtNotAct]
            rfl
          obtain ⟨k3, klo3, _, htr3⟩ := pf_lift_phase_ver_append (pBefore ++ [handPh])
            nxtPh.pRecs nxtPh.tCells pAfterRest ((consumed ++ [c0Done]) ++ uCells) recActive htr3a_pre
          let nxtPhAct : PhaseState := ⟨nxtPh.pRecs ++ [recActive], nxtPh.tCells⟩
          have hnxtAct : newestRecords nxtPhAct.pRecs none = some [true, false] :=
            newest_records_append nxtPh.pRecs recActive none
          -- C3b: Deactivate handoff phase -> INACTIVE
          have hfindH3b := scanPhases_handoff_find pBefore handPh (nxtPhAct :: pAfterRest) hbNeH hpHand
          have hlenGe2b : ((scanPhases (progRingTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) 2)).length == 1) = false := by
            rw [scanPhases_len]; simp only [List.length_append, List.length_cons]
            exact beq_eq_false_iff_ne.mpr (by omega)
          have hmodEqb : (pBefore.length + 1) % (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) 2)).length =
              (pBefore ++ [handPh]).length := by
            rw [scanPhases_len]; simp only [List.length_append, List.length_cons, List.length_nil]
            exact Nat.mod_eq_of_lt (by omega)
          have hgetNxtb : listGetOpt (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) 2))
              (pBefore ++ [handPh]).length =
              some (entryOfPhaseAt (pBefore ++ [handPh]).length nxtPhAct) := by
            have heq : pBefore ++ handPh :: nxtPhAct :: pAfterRest =
                (pBefore ++ [handPh]) ++ nxtPhAct :: pAfterRest := by simp [List.append_assoc]
            rw [heq]
            exact scanPhases_get_at (pBefore ++ [handPh]) nxtPhAct pAfterRest
          have hnxtIsAct : ((entryOfPhaseAt (pBefore ++ [handPh]).length nxtPhAct).status == some [true, false]) = true := by
            simp [entryOfPhaseAt, hnxtAct]
          obtain ⟨k4, klo4, _, htr4⟩ := pf_lift_phase_ver_append pBefore pRecsH tCells (nxtPhAct :: pAfterRest)
            ((consumed ++ [c0Done]) ++ uCells) recInactive (by
              change pfDecideAction (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) 2))
                (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)) = _
              unfold pfDecideAction
              rw [hfindH3b, hqNoCons, hlenGe2b]
              dsimp only [Bool.false_eq_true, ↓reduceIte]
              rw [hmodEqb, hgetNxtb]
              dsimp only []
              rw [hnxtIsAct]
              rfl)
          let oldDone : PhaseState := ⟨pRecsH ++ [recInactive], tCells⟩
          have holdInact : PhaseMatchesSpec oldDone false appAct :=
            ⟨newest_records_append pRecsH recInactive none, htIdle⟩
          have htr3' : PFTrace k3
              (pfMachineTerm (pBefore ++ handPh :: nxtPh :: pAfterRest) ((consumed ++ [c0Done]) ++ uCells))
              (pfMachineTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) ((consumed ++ [c0Done]) ++ uCells)) := by
            cases nxtPh; simpa [nxtPhAct, List.append_assoc] using htr3
          have hpLen : P.phases.length = idx + 1 + (appAfterRest.length + 1) := by
            rw [hprog]; simp [List.length_append, haIdx]; omega
          have hidxMod : (idx + 1) % P.phases.length = idx + 1 := Nat.mod_eq_of_lt (by omega)
          refine ⟨k1 + (k2 + (k3 + k4)), (pBefore ++ [oldDone]) ++ nxtPhAct :: pAfterRest,
            (consumed ++ [c0Done]) ++ uCells, by omega, ?_, ?_⟩
          · have hfinalEq : pBefore ++ oldDone :: nxtPhAct :: pAfterRest =
                (pBefore ++ [oldDone]) ++ nxtPhAct :: pAfterRest := by simp [List.append_assoc]
            rw [← hfinalEq]
            exact pfTrace_trans htr1 (pfTrace_trans htr2 (pfTrace_trans htr3' htr4))
          · refine ⟨Nat.mod_lt _ (ctsProgram_length_pos P), ?_,
              consumed ++ [c0Done], uCells, rfl, hconsNext, hqWord⟩
            dsimp only []
            rw [hidxMod]
            refine ⟨pBefore ++ [oldDone], nxtPhAct, pAfterRest, appBefore ++ [appAct], nxtApp, appAfterRest,
              rfl, by rw [hprog]; simp [List.append_assoc], by simp [hpIdx], by simp [haIdx],
              phasesInactiveMatch_append hbMatch ⟨holdInact, trivial⟩,
              ⟨hnxtAct, hnxtSpec.2⟩, haRestMatch⟩
  | nil =>
      cases appAfter with
      | cons _ _ => simp [PhasesInactiveMatch] at haMatch
      | nil =>
          cases pBefore with
          | nil =>
              -- Single-phase program (`p = 1`)!
              cases appBefore with
              | cons _ _ => simp [PhasesInactiveMatch] at hbMatch
              | nil =>
                  have hlen1 : ((scanPhases (progRingTerm ([] ++ handPh :: []) 2)).length == 1) = true := by
                    rw [scanPhases_len]; rfl
                  obtain ⟨k3, klo3, _, htr3⟩ := pf_lift_phase_ver_append [] pRecsH tCells []
                    ((consumed ++ [c0Done]) ++ uCells) recActive (by
                      unfold pfDecideAction
                      rw [hfindH2, hqNoCons, hlen1]
                      rfl)
                  let pRecsFinal := pRecsH ++ [recActive]
                  have hpFinalAct : newestRecords pRecsFinal none = some [true, false] :=
                    newest_records_append pRecsH recActive none
                  have hpLen1 : P.phases.length = 1 := by rw [hprog]; rfl
                  have hmod0 : (idx + 1) % P.phases.length = 0 := by rw [hpLen1, Nat.mod_one]
                  refine ⟨k1 + (k2 + k3), [⟨pRecsFinal, tCells⟩], (consumed ++ [c0Done]) ++ uCells,
                    by omega, pfTrace_trans htr1 (pfTrace_trans htr2 htr3), ?_⟩
                  refine ⟨Nat.mod_lt _ (ctsProgram_length_pos P), ?_,
                    consumed ++ [c0Done], uCells, rfl, hconsNext, hqWord⟩
                  dsimp only []
                  rw [hmod0]
                  exact ⟨[], ⟨pRecsFinal, tCells⟩, [], [], appAct, [],
                    rfl, hprog, rfl, rfl, trivial, ⟨hpFinalAct, htIdle⟩, trivial⟩
          | cons firstPh pBeforeRest =>
              -- Wraparound from last phase `idx = p - 1` back to `0` (`p ≥ 2`)!
              cases appBefore with
              | nil => simp [PhasesInactiveMatch] at hbMatch
              | cons firstApp appBeforeRest =>
                  rcases hbMatch with ⟨hfirstSpec, hbRestMatch⟩
                  have hlenGe2 : ((scanPhases (progRingTerm ((firstPh :: pBeforeRest) ++ handPh :: []) 2)).length == 1) = false := by
                    rw [scanPhases_len]; simp only [List.length_append, List.length_cons]
                    exact beq_eq_false_iff_ne.mpr (by omega)
                  have hmod0 : ((firstPh :: pBeforeRest).length + 1) %
                      (scanPhases (progRingTerm ((firstPh :: pBeforeRest) ++ handPh :: []) 2)).length = 0 := by
                    rw [scanPhases_len]
                    have heqLen : ((firstPh :: pBeforeRest) ++ [handPh]).length =
                        (firstPh :: pBeforeRest).length + 1 := by simp
                    rw [heqLen, Nat.mod_self]
                  have hget0 : listGetOpt (scanPhases (progRingTerm ((firstPh :: pBeforeRest) ++ handPh :: []) 2)) 0 =
                      some (entryOfPhaseAt 0 firstPh) := by
                    have heq : (firstPh :: pBeforeRest) ++ handPh :: [] =
                        [] ++ firstPh :: (pBeforeRest ++ [handPh]) := rfl
                    rw [heq]
                    exact scanPhases_get_at [] firstPh (pBeforeRest ++ [handPh])
                  have hfirstNotAct : ((entryOfPhaseAt 0 firstPh).status == some [true, false]) = false := by
                    simp [entryOfPhaseAt, hfirstSpec.1]
                  -- C3a: Activate phase 0 (`firstPh`)
                  have htr3a_pre : pfDecideAction
                      (scanPhases (progRingTerm ([] ++ ⟨firstPh.pRecs, firstPh.tCells⟩ :: (pBeforeRest ++ [handPh])) 2))
                      (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)) =
                      .writeVer (pfProgRingPath ++ (repeatRightPath ([] : List PhaseState).length ++ [false, true, false, true]))
                        2 recActive.val := by
                    have heq : [] ++ ⟨firstPh.pRecs, firstPh.tCells⟩ :: (pBeforeRest ++ [handPh]) =
                        (firstPh :: pBeforeRest) ++ handPh :: [] := by
                      cases firstPh; rfl
                    rw [heq]
                    unfold pfDecideAction
                    rw [hfindH2, hqNoCons, hlenGe2]
                    simp only [Bool.false_eq_true, ↓reduceIte, hmod0, hget0, hfirstNotAct]
                    rfl
                  obtain ⟨k3, klo3, _, htr3⟩ := pf_lift_phase_ver_append [] firstPh.pRecs firstPh.tCells
                    (pBeforeRest ++ [handPh]) ((consumed ++ [c0Done]) ++ uCells) recActive htr3a_pre
                  let firstPhAct : PhaseState := ⟨firstPh.pRecs ++ [recActive], firstPh.tCells⟩
                  have hfirstAct : newestRecords firstPhAct.pRecs none = some [true, false] :=
                    newest_records_append firstPh.pRecs recActive none
                  -- C3b: Deactivate `pRecsH` at end of ring -> INACTIVE
                  have hbNeHb : ∀ ph ∈ firstPhAct :: pBeforeRest, newestRecords ph.pRecs none ≠ some [true, true] := by
                    intro ph hm
                    simp only [List.mem_cons] at hm
                    rcases hm with rfl | hm'
                    · rw [hfirstAct]; decide
                    · rw [phasesInactiveMatch_status hbRestMatch ph hm']; decide
                  have hfindH3b := scanPhases_handoff_find (firstPhAct :: pBeforeRest) handPh [] hbNeHb hpHand
                  have hlenGe2b : ((scanPhases (progRingTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) 2)).length == 1) = false := by
                    rw [scanPhases_len]; simp only [List.length_append, List.length_cons]
                    exact beq_eq_false_iff_ne.mpr (by omega)
                  have hmod0b : ((firstPhAct :: pBeforeRest).length + 1) %
                      (scanPhases (progRingTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) 2)).length = 0 := by
                    rw [scanPhases_len]
                    have heqLen : ((firstPhAct :: pBeforeRest) ++ [handPh]).length =
                        (firstPhAct :: pBeforeRest).length + 1 := by simp
                    rw [heqLen, Nat.mod_self]
                  have hget0b : listGetOpt (scanPhases (progRingTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) 2)) 0 =
                      some (entryOfPhaseAt 0 firstPhAct) := by
                    have heq : (firstPhAct :: pBeforeRest) ++ handPh :: [] =
                        [] ++ firstPhAct :: (pBeforeRest ++ [handPh]) := rfl
                    rw [heq]
                    exact scanPhases_get_at [] firstPhAct (pBeforeRest ++ [handPh])
                  have hfirstIsAct : ((entryOfPhaseAt 0 firstPhAct).status == some [true, false]) = true := by
                    simp [entryOfPhaseAt, hfirstAct]
                  obtain ⟨k4, klo4, _, htr4⟩ := pf_lift_phase_ver_append (firstPhAct :: pBeforeRest)
                    pRecsH tCells [] ((consumed ++ [c0Done]) ++ uCells) recInactive (by
                      change pfDecideAction (scanPhases (progRingTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) 2))
                        (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)) = _
                      unfold pfDecideAction
                      rw [hfindH3b, hqNoCons, hlenGe2b]
                      dsimp only [Bool.false_eq_true, ↓reduceIte]
                      rw [hmod0b, hget0b]
                      dsimp only []
                      rw [hfirstIsAct]
                      rfl)
                  let oldDone : PhaseState := ⟨pRecsH ++ [recInactive], tCells⟩
                  have holdInact : PhaseMatchesSpec oldDone false appAct :=
                    ⟨newest_records_append pRecsH recInactive none, htIdle⟩
                  have htr3' : PFTrace k3
                      (pfMachineTerm ((firstPh :: pBeforeRest) ++ handPh :: []) ((consumed ++ [c0Done]) ++ uCells))
                      (pfMachineTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) ((consumed ++ [c0Done]) ++ uCells)) := by
                    cases firstPh; exact htr3
                  have hpLenEq : P.phases.length = idx + 1 := by
                    rw [hprog, ← haIdx]; simp
                  have hidxMod0 : (idx + 1) % P.phases.length = 0 := by rw [hpLenEq, Nat.mod_self]
                  refine ⟨k1 + (k2 + (k3 + k4)), firstPhAct :: (pBeforeRest ++ [oldDone]),
                    (consumed ++ [c0Done]) ++ uCells, by omega, ?_, ?_⟩
                  · exact pfTrace_trans htr1 (pfTrace_trans htr2 (pfTrace_trans htr3' htr4))
                  · refine ⟨Nat.mod_lt _ (ctsProgram_length_pos P), ?_,
                      consumed ++ [c0Done], uCells, rfl, hconsNext, hqWord⟩
                    dsimp only []
                    rw [hidxMod0]
                    exact ⟨[], firstPhAct, pBeforeRest ++ [oldDone], [], firstApp, appBeforeRest ++ [appAct],
                      rfl, by rw [hprog]; rfl, rfl, rfl, trivial, ⟨hfirstAct, hfirstSpec.2⟩,
                      phasesInactiveMatch_append hbRestMatch ⟨holdInact, trivial⟩⟩

theorem list_get_of_eq {α : Type} {xs ys : List α} (h : xs = ys) (i : Nat) (hi : i < xs.length) :
    xs.get ⟨i, hi⟩ = ys.get ⟨i, h ▸ hi⟩ := by
  subst h
  rfl

/-- **Single CTS Step Simulation Theorem**:
    Every defined CTS step `ctsStep P cfg = some cfg'` from `PFConfigRep P cfg phases qCells`
    is simulated by `PFTrace k` (`k ≥ 24 ≥ 6`) reaching `PFConfigRep P cfg' phases' qCells'`. -/
theorem cts_step_simulated_by_pfTrace (P : CTSProgram) {cfg cfg' : CTSConfig}
    (phases : List PhaseState) (qCells : List (List Rec3))
    (hrep : PFConfigRep P cfg phases qCells)
    (hstep : ctsStep P cfg = some cfg') :
    ∃ k phases' qCells', 6 ≤ k ∧
      PFTrace k (pfMachineTerm phases qCells) (pfMachineTerm phases' qCells') ∧
      PFConfigRep P cfg' phases' qCells' := by
  cases cfg with
  | mk idx queue =>
      cases queue with
      | nil => simp [ctsStep] at hstep
      | cons b rest =>
          obtain ⟨hidxLt, ⟨pBefore, actPh, pAfter, appBefore, appAct, appAfter,
            rfl, hprog, hpIdx, haIdx, hbMatch, hactSpec, haMatch⟩,
            consumed, unconsumed, rfl, hcons, hqWord⟩ := hrep
          cases actPh with
          | mk pRecs tCells =>
              rcases hactSpec with ⟨hpAct, htIdle⟩
              cases unconsumed with
              | nil => simp [QueueMatchesWord] at hqWord
              | cons u0 uRest =>
                  rcases hqWord with ⟨hu0, huRestWord⟩
                  have hbInact := phasesInactiveMatch_status hbMatch
                  have haInact := phasesInactiveMatch_status haMatch
                  have huRestAll := queueMatchesWord_allUnconsumed huRestWord
                  have happGet : P.phases.get ⟨idx, hidxLt⟩ = appAct := by
                    rw [list_get_of_eq hprog idx hidxLt]
                    exact list_get_at_split appBefore appAct appAfter idx haIdx (hprog ▸ hidxLt)
                  rw [ctsStep_cons P idx hidxLt b rest, happGet, Option.some.injEq] at hstep
                  subst cfg'
                  cases b with
                  | false =>
                      -- Case `b = false`: directly mark `u0` CONSUMING, then handoff!
                      obtain ⟨hnoH, hfindA⟩ := scanPhases_unique_active pBefore ⟨pRecs, tCells⟩ pAfter
                        hbInact hpAct haInact
                      obtain ⟨hqCons, hqUncons⟩ := scanQueue_front_unconsumed_shape consumed u0 uRest false
                        hcons hu0 huRestAll
                      obtain ⟨k1, klo1, _, htr1⟩ := pf_lift_queue_ver_append
                        (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) consumed u0 uRest (recConsuming false) (by
                          unfold pfDecideAction
                          rw [hnoH, hfindA, hqCons, hqUncons]
                          rfl)
                      have hu0Cons : newestRecords (u0 ++ [recConsuming false]) none = some [true, false, false] :=
                        newest_records_append u0 (recConsuming false) none
                      obtain ⟨k2, phasesOut, qCellsOut, klo2, htr2, hrepOut⟩ :=
                        pf_trace_handoff_and_advance P idx pBefore pRecs tCells pAfter
                          appBefore appAct appAfter consumed (u0 ++ [recConsuming false]) false uRest rest
                          hprog hpIdx haIdx hbMatch hpAct htIdle haMatch hcons hu0Cons huRestWord
                      exact ⟨k1 + k2, phasesOut, qCellsOut, by omega, pfTrace_trans htr1 htr2,
                        by simpa using hrepOut⟩
                  | true =>
                      -- Case `b = true`: arm all template cells, mark `u0` CONSUMING, copy all bits, handoff!
                      have htSplit0 : tCells = [] ++ tCells := rfl
                      rw [htSplit0]
                      obtain ⟨kA, tArmed, htrA, htArmed⟩ := pf_trace_arm_templates
                        pBefore pRecs pAfter consumed u0 uRest hbInact hpAct haInact hcons hu0 huRestAll
                        tCells appAct [] [] trivial htIdle
                      rw [List.nil_append] at htArmed
                      obtain ⟨hnoHA, hfindAA⟩ := scanPhases_unique_active pBefore ⟨pRecs, tArmed⟩ pAfter
                        hbInact hpAct haInact
                      obtain ⟨hqCons, hqUncons⟩ := scanQueue_front_unconsumed_shape consumed u0 uRest true
                        hcons hu0 huRestAll
                      have htNoIdle := (specScanTemplates_allArmed_noIdle_noApp htArmed).1
                      obtain ⟨kM, kloM, _, htrM⟩ := pf_lift_queue_ver_append
                        (pBefore ++ ⟨pRecs, tArmed⟩ :: pAfter) consumed u0 uRest (recConsuming true) (by
                          unfold pfDecideAction
                          rw [hnoHA, hfindAA, hqCons, hqUncons]
                          dsimp only [↓reduceIte, entryOfPhaseAt]
                          rw [htNoIdle]
                          rfl)
                      let c0 := u0 ++ [recConsuming true]
                      have hc0 : newestRecords c0 none = some [true, false, true] :=
                        newest_records_append u0 (recConsuming true) none
                      have htArmedSplit : tArmed = [] ++ tArmed := rfl
                      rw [htArmedSplit] at htrM
                      obtain ⟨kB, tIdleOut, uCellsOut, htrB, htIdleOut, hqWordOut⟩ :=
                        pf_trace_copy_all_bits pBefore pRecs pAfter consumed c0 true
                          hbInact hpAct haInact hcons hc0 tArmed appAct [] [] uRest rest
                          trivial htArmed huRestWord
                      rw [List.nil_append] at htIdleOut
                      obtain ⟨kC, phasesOut, qCellsOut, kloC, htrC, hrepOut⟩ :=
                        pf_trace_handoff_and_advance P idx pBefore pRecs tIdleOut pAfter
                          appBefore appAct appAfter consumed c0 true uCellsOut (rest ++ appAct)
                          hprog hpIdx haIdx hbMatch hpAct htIdleOut haMatch hcons hc0 hqWordOut
                      exact ⟨kA + (kM + (kB + kC)), phasesOut, qCellsOut, by omega,
                        pfTrace_trans htrA (pfTrace_trans htrM (pfTrace_trans htrB htrC)),
                        by simpa using hrepOut⟩

/-- **Multi-Step CTS Run Simulation Theorem**:
    Every `n`-step CTS run `CTSRun P n cfg cfg'` lifts to `PFTrace k` with `6 * n ≤ k`. -/
theorem cts_run_simulated_by_pfTrace (P : CTSProgram) {n : Nat} {cfg cfg' : CTSConfig}
    (hrun : CTSRun P n cfg cfg') :
    ∀ phases qCells, PFConfigRep P cfg phases qCells →
      ∃ k phases' qCells', 6 * n ≤ k ∧
        PFTrace k (pfMachineTerm phases qCells) (pfMachineTerm phases' qCells') ∧
        PFConfigRep P cfg' phases' qCells' := by
  induction hrun with
  | zero _ =>
      intro phases qCells hrep
      exact ⟨0, phases, qCells, by simp, PFTrace.zero _, hrep⟩
  | @next n a b c hstep _ ih =>
      intro phases qCells hrep
      obtain ⟨k1, phases1, qCells1, klo1, htr1, hrep1⟩ :=
        cts_step_simulated_by_pfTrace P phases qCells hrep hstep
      obtain ⟨k2, phases2, qCells2, klo2, htr2, hrep2⟩ := ih phases1 qCells1 hrep1
      exact ⟨k1 + k2, phases2, qCells2, by omega, pfTrace_trans htr1 htr2, hrep2⟩


/-! ## Section 7: Main Theorem — Constructive Bidirectional Program-Free CTS Universality -/

/-- **Constructive Bidirectional Universality of the Program-Free Pure-`S` Selector (`R_PF`)**:
    For EVERY Cyclic Tag System program `P` and EVERY binary input word `w : List Bool`,
    `CTS(P, w)` eventually halts (empties its queue) **if and only if** iterating the
    single fixed, program-free selector `pfSelect : Term → PFOutcome` from the bare
    polynomial-size pure-`S` term `encodeProgramFreeCTS P w` reaches a term accepted by
    `pfRootHalt` (`pfHaltAutomaton : BottomUpTreeAutomaton (Fin 11)`). -/
theorem program_free_cts_halting_iff (P : CTSProgram) (w : List Bool) :
    CTSEventuallyHalts P w ↔
      ∃ k reached, PFTrace k (encodeProgramFreeCTS P w) reached ∧ pfRootHalt reached = true := by
  constructor
  · intro ⟨n, final, hrun, hstop⟩
    obtain ⟨k1, phases, qCells, _, htr1, hrepFinal⟩ :=
      cts_run_simulated_by_pfTrace P hrun (initPhaseStates P) (initQueueCells w)
        (initProgramFreeCTS_rep P w)
    have hqEmpty : final.queue = [] := (ctsStep_eq_none_iff P final).mp hstop
    cases final with
    | mk fIdx fQueue =>
        simp only at hqEmpty
        subst fQueue
        obtain ⟨k2, reached, _, htr2, hhalt⟩ :=
          cts_halt_simulated_by_pfTrace P fIdx phases qCells hrepFinal
        exact ⟨k1 + k2, reached, pfTrace_trans htr1 htr2, hhalt⟩
  · intro ⟨k, reached, htrace, hhalt⟩
    rcases cts_bounded_halt_or_run P (k + 1) w with hhalts | ⟨future, hrun⟩
    · exact hhalts
    · obtain ⟨M, phases', qCells', hloM, hlonger, _⟩ :=
        cts_run_simulated_by_pfTrace P hrun (initPhaseStates P) (initQueueCells w)
          (initProgramFreeCTS_rep P w)
      exact False.elim (pf_halt_cannot_precede_longer_trace htrace hhalt hlonger (by omega))

/-- Tree-automaton formulation of `program_free_cts_halting_iff`: halting is recognized by
    the explicit 11-state deterministic bottom-up tree automaton `pfHaltAutomaton`. -/
theorem program_free_cts_halting_iff_automaton (P : CTSProgram) (w : List Bool) :
    CTSEventuallyHalts P w ↔
      ∃ k reached, PFTrace k (encodeProgramFreeCTS P w) reached ∧
        pfHaltAutomaton.evalAccepts reached = true := by
  simp only [pfHaltAutomaton_accepts_eq_pfRootHalt]
  exact program_free_cts_halting_iff P w


/-! ## Section 8: Executable `#guard` Verification & `#print axioms` Audit -/

/-- Bounded executable runner for `pfSelect` on bare pure-`S` terms. -/
def runPFBounded : Nat → Term → Option Nat
  | 0, t => if pfRootHalt t then some 0 else none
  | fuel + 1, t =>
      match pfSelect t with
      | .halt => some 0
      | .step t' => (runPFBounded fuel t').map (· + 1)
      | .stuck => none

def ctsExampleEmptyHalt : CTSProgram := ⟨[[true]], by decide⟩
def ctsExampleSingle0Halt : CTSProgram := ⟨[[true, false]], by decide⟩
def ctsExampleCopyAndDrain : CTSProgram := ⟨[[true], []], by decide⟩
def ctsExampleThreePhase : CTSProgram := ⟨[[false, true], [false], []], by decide⟩
def ctsExampleNonhalting : CTSProgram := ⟨[[true]], by decide⟩

-- 1. Reference CTS evaluator checks:
#guard evalCTSBounded ctsExampleEmptyHalt 10 (initCTSConfig []) == .inl (0, ⟨0, []⟩)
#guard evalCTSBounded ctsExampleSingle0Halt 10 (initCTSConfig [false]) == .inl (1, ⟨0, []⟩)
#guard evalCTSBounded ctsExampleCopyAndDrain 20 (initCTSConfig [true, false, true]) == .inl (6, ⟨0, []⟩)
#guard evalCTSBounded ctsExampleThreePhase 20 (initCTSConfig [true, false]) == .inl (6, ⟨0, []⟩)
#guard evalCTSBounded ctsExampleNonhalting 10 (initCTSConfig [true]) == .inr ⟨0, [true]⟩

-- 2. End-to-end bare pure-S execution via `pfSelect` (zero program passed to `runPFBounded`!):
#guard (runPFBounded 20 (encodeProgramFreeCTS ctsExampleEmptyHalt [])).isSome
#guard (runPFBounded 200 (encodeProgramFreeCTS ctsExampleSingle0Halt [false])).isSome
#guard (runPFBounded 2000 (encodeProgramFreeCTS ctsExampleCopyAndDrain [true, false, true])).isSome
#guard (runPFBounded 2500 (encodeProgramFreeCTS ctsExampleThreePhase [true, false])).isSome
#guard (runPFBounded 250 (encodeProgramFreeCTS ctsExampleNonhalting [true])).isNone


/-! ## Section 9: Bare-Term Clean-State & Halted Output Decoder (`decodeProgramFreeCTS`) -/

/-- Syntactic check for an unopened generator `(numeral m ⋅ numeral n ⋅ S)`, matching
    Wolfram's `PFUnopenedGenQ` (`First[nd] === s && BoundedSpineArity5[nd] === 4`). -/
def pfIsUnopenedGen : Term → Bool
  | .app (.app (.app (.app .s _) _) _) .s => true
  | _ => false

/-- True iff `t` is neither an opened protected frame nor an unopened generator
    (i.e. `t` is in an intermediate stage of a 6/7-step slot opening). -/
def pfMidOpeningQ (t : Term) : Bool :=
  !flagValue t && !pfIsUnopenedGen t

/-- Check whether a version chain has any uncommitted record frame or mid-opening tail,
    matching Wolfram's `PFHasUncommittedVerQ`. -/
def pfHasUncommittedVer (width : Nat) : Term → Bool
  | .app (.app .s next) (.app (.app .s fields) _) =>
      match readFields width fields with
      | none => true
      | some _ => pfHasUncommittedVer width next
  | tail => pfMidOpeningQ tail

/-- Verify all template cells of a phase are cleanly committed in `IDLE` (`[false, false, b]`). -/
def pfTemplatesCleanIdle : Term → Bool
  | .app (.app .s tVer) (.app (.app .s rest) _) =>
      if pfHasUncommittedVer 3 tVer then false
      else
        match pfScanVersion 3 none tVer with
        | some [false, false, _] => pfTemplatesCleanIdle rest
        | _ => false
  | tail => !pfMidOpeningQ tail

/-- Decode clean phase statuses (`true` = `ACTIVE` `[true, false]`,
    `false` = `INACTIVE` `[false, false]`) along `progRing`. -/
def pfDecodePhaseStatuses : Term → Option (List Bool)
  | .app (.app .s pBody) (.app (.app .s rest) _) =>
      match parseFrame pBody with
      | none => none
      | some (pVer, tList, _) =>
          if pfHasUncommittedVer 2 pVer || !pfTemplatesCleanIdle tList then none
          else
            match pfScanVersion 2 none pVer with
            | some [false, false] => (pfDecodePhaseStatuses rest).map (false :: ·)
            | some [true, false] => (pfDecodePhaseStatuses rest).map (true :: ·)
            | _ => none
  | tail => if pfMidOpeningQ tail then none else some []

/-- Return the unique 0-based index `actIdx` where `statuses[actIdx] = true`,
    or `none` if zero or multiple entries are `true`. -/
def uniqueTrueIdx : List Bool → Option Nat
  | [] => none
  | true :: rest => if rest.any id then none else some 0
  | false :: rest => (uniqueTrueIdx rest).map (· + 1)

/-- Decode unconsumed queue bits (`[false, false, b]`), skipping consumed cells
    (`[true, true, _]`) and rejecting any mid-transaction queue state. -/
def pfDecodeQueueWord : Term → Option (List Bool)
  | .app (.app .s qVer) (.app (.app .s rest) _) =>
      if pfHasUncommittedVer 3 qVer then none
      else
        match pfScanVersion 3 none qVer with
        | some [false, false, b] => (pfDecodeQueueWord rest).map (b :: ·)
        | some [true, true, _] => pfDecodeQueueWord rest
        | _ => none
  | tail => if pfMidOpeningQ tail then none else some []

/-- **Bare-Term Clean-State & Halted Output Decoder `decodeProgramFreeCTS`**:
    Reads `(actIdx, queue)` directly from a bare pure-`S` term at clean CTS step
    boundaries (including initial encodings and halted terms), matching Wolfram's
    `DecodeProgramFreeCTSState`. -/
def decodeProgramFreeCTS (root : Term) : Option (Nat × List Bool) := do
  let hub ← termAt root pfHubPath
  let (flag, _, _) ← parseFrame hub
  if pfMidOpeningQ flag then none
  else
    let payload ← termAt root pfPayloadPath
    let (progRing, queueRoot, _) ← parseFrame payload
    let statuses ← pfDecodePhaseStatuses progRing
    let actIdx ← uniqueTrueIdx statuses
    let word ← pfDecodeQueueWord queueRoot
    some (actIdx, word)

theorem pfIsUnopenedGen_generator (m n : Nat) : pfIsUnopenedGen (generator m n) = true := by
  cases m <;> rfl

theorem pfMidOpeningQ_depthBase (d : Nat) : pfMidOpeningQ (depthBase d) = false := by
  unfold pfMidOpeningQ depthBase phaseBase
  rw [pfIsUnopenedGen_generator]
  simp

theorem pfMidOpeningQ_frameTerm (l r j : Term) : pfMidOpeningQ (frameTerm l r j) = false := by
  simp [pfMidOpeningQ, flagValue, parse_frame]

theorem pfHasUncommittedVer_closed (width : Nat) (t : Term) (h : parseFrame t = none) :
    pfHasUncommittedVer width t = pfMidOpeningQ t := by
  unfold parseFrame at h
  unfold pfHasUncommittedVer
  split <;> simp_all

theorem pfHasUncommittedVer_frame (width : Nat) (next fields junk : Term) :
    pfHasUncommittedVer width (frameTerm next fields junk) =
      match readFields width fields with
      | none => true
      | some _ => pfHasUncommittedVer width next := rfl

theorem pfHasUncommittedVer_pfVerTerm {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) :
    ∀ d, pfHasUncommittedVer width (pfVerTerm records d) = false := by
  induction records with
  | nil =>
      intro d
      change pfHasUncommittedVer width (depthBase d) = false
      rw [pfHasUncommittedVer_closed width (depthBase d) (depth_base_closed d)]
      exact pfMidOpeningQ_depthBase d
  | cons entry rest ih =>
      intro d
      unfold pfVerTerm
      rw [versionLayout, layout_opened_phase _ _ _ (phase_at_good d)]
      have hread : readFields width
          (layoutTerm (fieldsLayout entry.val) (phaseAt (d + 1)).1 (phaseAt (d + 1)).2) = some entry.val := by
        simpa [entry.property] using actual_layout_fields_decode entry.val (d + 1)
      change pfHasUncommittedVer width
        (frameTerm (pfVerTerm rest (d + 1))
          (layoutTerm (fieldsLayout entry.val) (phaseAt (d + 1)).1 (phaseAt (d + 1)).2)
          (depthJunk d)) = false
      rw [pfHasUncommittedVer_frame, hread]
      exact ih (d + 1)

theorem pfTemplatesCleanIdle_closed (t : Term) (h : parseFrame t = none) :
    pfTemplatesCleanIdle t = !pfMidOpeningQ t := by
  unfold parseFrame at h
  unfold pfTemplatesCleanIdle
  split <;> simp_all

theorem pfTemplatesCleanIdle_frame (tVer rest junk : Term) :
    pfTemplatesCleanIdle (frameTerm tVer rest junk) =
      if pfHasUncommittedVer 3 tVer then false
      else
        match pfScanVersion 3 none tVer with
        | some [false, false, _] => pfTemplatesCleanIdle rest
        | _ => false := rfl

theorem pfTemplatesCleanIdle_templateListTerm {tCells : List (List Rec3)} {app : List Bool}
    (h : TemplateMatchesIdle tCells app) :
    ∀ d, pfTemplatesCleanIdle (templateListTerm tCells d) = true := by
  induction tCells generalizing app with
  | nil =>
      intro d
      change pfTemplatesCleanIdle (depthBase d) = true
      rw [pfTemplatesCleanIdle_closed (depthBase d) (depth_base_closed d), pfMidOpeningQ_depthBase]
      rfl
  | cons r rs ih =>
      cases app with
      | nil => simp [TemplateMatchesIdle] at h
      | cons b bs =>
          intro d
          rcases h with ⟨hr, hrs⟩
          unfold templateListTerm
          rw [pfTemplatesCleanIdle_frame, pfHasUncommittedVer_pfVerTerm r (d + 1),
            pfVerTerm_scan r (d + 1), hr]
          exact ih hrs (d + 1)

theorem pfDecodePhaseStatuses_closed (t : Term) (h : parseFrame t = none) :
    pfDecodePhaseStatuses t = if pfMidOpeningQ t then none else some [] := by
  unfold parseFrame at h
  unfold pfDecodePhaseStatuses
  split <;> simp_all

theorem pfDecodePhaseStatuses_frame (pBody rest junk : Term) :
    pfDecodePhaseStatuses (frameTerm pBody rest junk) =
      match parseFrame pBody with
      | none => none
      | some (pVer, tList, _) =>
          if pfHasUncommittedVer 2 pVer || !pfTemplatesCleanIdle tList then none
          else
            match pfScanVersion 2 none pVer with
            | some [false, false] => (pfDecodePhaseStatuses rest).map (false :: ·)
            | some [true, false] => (pfDecodePhaseStatuses rest).map (true :: ·)
            | _ => none := rfl

theorem pfDecodePhaseStatuses_cons {ph : PhaseState} {isAct : Bool} {app : List Bool}
    (hspec : PhaseMatchesSpec ph isAct app) (rest : List PhaseState) (d : Nat) :
    pfDecodePhaseStatuses (progRingTerm (ph :: rest) d) =
      (pfDecodePhaseStatuses (progRingTerm rest (d + 1))).map (isAct :: ·) := by
  rcases hspec with ⟨hpst, htIdle⟩
  change pfDecodePhaseStatuses
    (frameTerm (phaseBodyTerm ph (d + 1)) (progRingTerm rest (d + 1)) (depthJunk d)) =
    (pfDecodePhaseStatuses (progRingTerm rest (d + 1))).map (isAct :: ·)
  rw [pfDecodePhaseStatuses_frame]
  unfold phaseBodyTerm
  rw [parse_frame]
  dsimp only []
  rw [pfHasUncommittedVer_pfVerTerm ph.pRecs (d + 1 + 1),
    pfTemplatesCleanIdle_templateListTerm htIdle (d + 1 + 1),
    pfVerTerm_scan ph.pRecs (d + 1 + 1), hpst]
  cases isAct <;> rfl

theorem pfDecodePhaseStatuses_inactive {phs : List PhaseState} {apps : List (List Bool)}
    (h : PhasesInactiveMatch phs apps) :
    ∀ d, pfDecodePhaseStatuses (progRingTerm phs d) = some (List.replicate phs.length false) := by
  induction phs generalizing apps with
  | nil =>
      intro d
      change pfDecodePhaseStatuses (depthBase d) = some []
      rw [pfDecodePhaseStatuses_closed (depthBase d) (depth_base_closed d), pfMidOpeningQ_depthBase]
      rfl
  | cons p0 rs ih =>
      cases apps with
      | nil => simp [PhasesInactiveMatch] at h
      | cons a0 as =>
          intro d
          rw [pfDecodePhaseStatuses_cons h.1 rs d, ih h.2 (d + 1)]
          simp [List.replicate_succ]

theorem pfDecodePhaseStatuses_split {pBefore : List PhaseState} {appBefore : List (List Bool)}
    (hb : PhasesInactiveMatch pBefore appBefore)
    {actPh : PhaseState} {appAct : List Bool} (hact : PhaseMatchesSpec actPh true appAct)
    {pAfter : List PhaseState} {appAfter : List (List Bool)} (ha : PhasesInactiveMatch pAfter appAfter) :
    ∀ d, pfDecodePhaseStatuses (progRingTerm (pBefore ++ actPh :: pAfter) d) =
      some (List.replicate pBefore.length false ++ true :: List.replicate pAfter.length false) := by
  induction pBefore generalizing appBefore with
  | nil =>
      intro d
      simp only [List.nil_append, List.length_nil, List.replicate]
      rw [pfDecodePhaseStatuses_cons hact pAfter d, pfDecodePhaseStatuses_inactive ha (d + 1)]
      rfl
  | cons p0 rs ih =>
      cases appBefore with
      | nil => simp [PhasesInactiveMatch] at hb
      | cons a0 as =>
          intro d
          simp only [List.cons_append, List.length_cons, List.replicate_succ]
          rw [pfDecodePhaseStatuses_cons hb.1 (rs ++ actPh :: pAfter) d, ih hb.2 (d + 1)]
          rfl

theorem any_replicate_false : ∀ m : Nat, (List.replicate m false).any id = false
  | 0 => rfl
  | m + 1 => any_replicate_false m

theorem uniqueTrueIdx_split : ∀ k m : Nat,
    uniqueTrueIdx (List.replicate k false ++ true :: List.replicate m false) = some k
  | 0, m => by simp [uniqueTrueIdx]
  | k + 1, m => by simp [List.replicate_succ, uniqueTrueIdx, uniqueTrueIdx_split k m]

theorem pfDecodeQueueWord_closed (t : Term) (h : parseFrame t = none) :
    pfDecodeQueueWord t = if pfMidOpeningQ t then none else some [] := by
  unfold parseFrame at h
  unfold pfDecodeQueueWord
  split <;> simp_all

theorem pfDecodeQueueWord_frame (qVer rest junk : Term) :
    pfDecodeQueueWord (frameTerm qVer rest junk) =
      if pfHasUncommittedVer 3 qVer then none
      else
        match pfScanVersion 3 none qVer with
        | some [false, false, b] => (pfDecodeQueueWord rest).map (b :: ·)
        | some [true, true, _] => pfDecodeQueueWord rest
        | _ => none := rfl

theorem pfDecodeQueueWord_unconsumed {uCells : List (List Rec3)} {w : List Bool}
    (h : QueueMatchesWord uCells w) :
    ∀ d, pfDecodeQueueWord (queueListTerm uCells d) = some w := by
  induction uCells generalizing w with
  | nil =>
      cases w with
      | cons _ _ => simp [QueueMatchesWord] at h
      | nil =>
          intro d
          change pfDecodeQueueWord (depthBase d) = some []
          rw [pfDecodeQueueWord_closed (depthBase d) (depth_base_closed d), pfMidOpeningQ_depthBase]
          rfl
  | cons r rs ih =>
      cases w with
      | nil => simp [QueueMatchesWord] at h
      | cons b bs =>
          intro d
          rcases h with ⟨hr, hrs⟩
          unfold queueListTerm
          rw [pfDecodeQueueWord_frame, pfHasUncommittedVer_pfVerTerm r (d + 1),
            pfVerTerm_scan r (d + 1), hr, ih hrs (d + 1)]
          rfl

theorem pfDecodeQueueWord_consumed_prefix (consumed uCells : List (List Rec3))
    (hc : ∀ r ∈ consumed, IsConsumedCell r) :
    ∀ d, pfDecodeQueueWord (queueListTerm (consumed ++ uCells) d) =
      pfDecodeQueueWord (queueListTerm uCells (d + consumed.length)) := by
  induction consumed with
  | nil =>
      intro d
      simp
  | cons r rs ih =>
      intro d
      obtain ⟨b, hb⟩ := hc r (by simp)
      have hrs : ∀ x ∈ rs, IsConsumedCell x := fun x hx => hc x (by simp [hx])
      simp only [List.cons_append, queueListTerm, List.length_cons]
      rw [pfDecodeQueueWord_frame, pfHasUncommittedVer_pfVerTerm r (d + 1),
        pfVerTerm_scan r (d + 1), hb, ih hrs (d + 1)]
      have hd : d + (rs.length + 1) = (d + 1) + rs.length := by omega
      rw [hd]
      rfl

/-- Clean-state decoding on any `pfRootTerm` whose `flag` is not mid-opening (`pfMidOpeningQ flag = false`). -/
theorem decodeProgramFreeCTS_pfRootTerm (P : CTSProgram) (cfg : CTSConfig)
    (phases : List PhaseState) (qCells : List (List Rec3)) (flag : Term)
    (hflag : pfMidOpeningQ flag = false)
    (hrep : PFConfigRep P cfg phases qCells) :
    decodeProgramFreeCTS (pfRootTerm flag (progRingTerm phases 2) (queueListTerm qCells 2)) =
      some (cfg.phaseIdx, cfg.queue) := by
  obtain ⟨_, ⟨pBefore, actPh, pAfter, appBefore, appAct, appAfter,
    rfl, _, hpIdx, _, hbMatch, hactSpec, haMatch⟩, consumed, unconsumed, rfl, hcons, hqWord⟩ := hrep
  have hhub : termAt (pfRootTerm flag (progRingTerm (pBefore ++ actPh :: pAfter) 2)
      (queueListTerm (consumed ++ unconsumed) 2)) pfHubPath =
      some (frameTerm flag (frameTerm (progRingTerm (pBefore ++ actPh :: pAfter) 2)
        (queueListTerm (consumed ++ unconsumed) 2) (depthJunk 1)) (depthJunk 0)) := rfl
  have hpay : termAt (pfRootTerm flag (progRingTerm (pBefore ++ actPh :: pAfter) 2)
      (queueListTerm (consumed ++ unconsumed) 2)) pfPayloadPath =
      some (frameTerm (progRingTerm (pBefore ++ actPh :: pAfter) 2)
        (queueListTerm (consumed ++ unconsumed) 2) (depthJunk 1)) := rfl
  have hstat := pfDecodePhaseStatuses_split hbMatch hactSpec haMatch 2
  have hidx := uniqueTrueIdx_split pBefore.length pAfter.length
  have hq : pfDecodeQueueWord (queueListTerm (consumed ++ unconsumed) 2) = some cfg.queue := by
    rw [pfDecodeQueueWord_consumed_prefix consumed unconsumed hcons 2]
    exact pfDecodeQueueWord_unconsumed hqWord (2 + consumed.length)
  unfold decodeProgramFreeCTS
  rw [hhub]
  dsimp only [Bind.bind, Option.bind]
  rw [parse_frame]
  dsimp only []
  rw [hflag]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hpay]
  dsimp only [Bind.bind, Option.bind]
  rw [parse_frame]
  dsimp only []
  rw [hstat]
  dsimp only [Bind.bind, Option.bind]
  rw [hidx]
  dsimp only [Bind.bind, Option.bind]
  rw [hq, hpIdx]

/-- Clean-state decoding at every CTS macro-step boundary `pfMachineTerm phases qCells`. -/
theorem decodeProgramFreeCTS_pfMachineTerm (P : CTSProgram) (cfg : CTSConfig)
    (phases : List PhaseState) (qCells : List (List Rec3))
    (hrep : PFConfigRep P cfg phases qCells) :
    decodeProgramFreeCTS (pfMachineTerm phases qCells) = some (cfg.phaseIdx, cfg.queue) :=
  decodeProgramFreeCTS_pfRootTerm P cfg phases qCells (depthBase 1) (pfMidOpeningQ_depthBase 1) hrep

/-- **Initial Clean-State Readback Theorem**:
    `decodeProgramFreeCTS` recovers `(0, w)` directly from the bare encoded term
    `encodeProgramFreeCTS P w`. -/
theorem decodeProgramFreeCTS_encode (P : CTSProgram) (w : List Bool) :
    decodeProgramFreeCTS (encodeProgramFreeCTS P w) = some (0, w) :=
  decodeProgramFreeCTS_pfMachineTerm P (initCTSConfig w) (initPhaseStates P) (initQueueCells w)
    (initProgramFreeCTS_rep P w)

/-- Exact uniqueness of the halting step count and halted term along `PFTrace`. -/
theorem pfTrace_halt_unique {k1 k2 : Nat} {start r1 r2 : Term}
    (htr1 : PFTrace k1 start r1) (hh1 : pfRootHalt r1 = true)
    (htr2 : PFTrace k2 start r2) (hh2 : pfRootHalt r2 = true) :
    k1 = k2 ∧ r1 = r2 := by
  have hnot12 : ¬ k1 < k2 := fun hlt => pf_halt_cannot_precede_longer_trace htr1 hh1 htr2 hlt
  have hnot21 : ¬ k2 < k1 := fun hlt => pf_halt_cannot_precede_longer_trace htr2 hh2 htr1 hlt
  have hk : k1 = k2 := by omega
  subst hk
  exact ⟨rfl, pfTrace_unique htr1 r2 htr2⟩

/-- Explicit halted-term simulation exposing the exact `pfRootTerm` shape with opened halt flag. -/
theorem cts_halt_simulated_by_pfTrace_exact (P : CTSProgram) (idx : Nat)
    (phases : List PhaseState) (qCells : List (List Rec3))
    (hrep : PFConfigRep P ⟨idx, []⟩ phases qCells) :
    let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt 1).1 (phaseAt 1).2
    ∃ k, (k = 6 ∨ k = 7) ∧
      PFTrace k (pfMachineTerm phases qCells)
        (pfRootTerm flagOpen (progRingTerm phases 2) (queueListTerm qCells 2)) ∧
      pfRootHalt (pfRootTerm flagOpen (progRingTerm phases 2) (queueListTerm qCells 2)) = true := by
  intro flagOpen
  obtain ⟨_, ⟨pBefore, actPh, pAfter, appBefore, appAct, appAfter,
    hphEq, _, _, _, hbInact, hactSpec, haInact⟩, consumed, unconsumed, hqEq, hcons, hqWord⟩ := hrep
  cases unconsumed with
  | cons _ _ => simp [QueueMatchesWord] at hqWord
  | nil =>
      rw [List.append_nil] at hqEq
      have hact : pfDecideAction (scanPhases (progRingTerm phases 2)) (scanQueue (queueListTerm qCells 2)) =
          .openSlot pfFlagPath := by
        rw [hphEq, hqEq]
        obtain ⟨hnoH, hfindA⟩ := scanPhases_unique_active pBefore actPh pAfter
          (phasesInactiveMatch_status hbInact) hactSpec.1 (phasesInactiveMatch_status haInact)
        obtain ⟨hnoCons, hnoUncons⟩ := scanQueue_halted_shape consumed hcons
        unfold pfDecideAction
        rw [hnoH, hfindA, hnoCons, hnoUncons]
      let C : Term → Term := fun f =>
        pfRootTerm f (progRingTerm phases 2) (queueListTerm qCells 2)
      obtain ⟨k, hk, htr⟩ := lift_closed_opening_to_pfTrace C pfFlagPath 1
        (fun f => pfRootTerm_termAt_flag f _ _)
        (fun p f1 f2 hd => pfRootTerm_directed_flag _ _ hd)
        (fun f hf => pfRootTerm_halt_closed f _ _ hf)
        (fun f _ => ⟨scanPhases (progRingTerm phases 2), scanQueue (queueListTerm qCells 2),
          pfRootTerm_readState f _ _, hact⟩)
      refine ⟨k, hk, htr, ?_⟩
      dsimp [C, flagOpen, pfRootTerm, pfRootHalt]
      rw [layout_opened_phase _ _ _ (phase_at_good 1)]
      simp [haltObserved, parse_frame, flagValue]

/-- Given any CTS run to empty queue `⟨finalIdx, []⟩` and any halted `PFTrace` reaching `reached`,
    `decodeProgramFreeCTS reached` equals `some (finalIdx, [])`. -/
theorem decodeProgramFreeCTS_of_cts_run_and_halted_trace (P : CTSProgram) (w : List Bool)
    {n finalIdx k : Nat} {reached : Term}
    (hrun : CTSRun P n (initCTSConfig w) ⟨finalIdx, []⟩)
    (htrace : PFTrace k (encodeProgramFreeCTS P w) reached)
    (hhalt : pfHaltAutomaton.evalAccepts reached = true) :
    decodeProgramFreeCTS reached = some (finalIdx, []) := by
  have hhaltRoot : pfRootHalt reached = true := by
    rw [← pfHaltAutomaton_accepts_eq_pfRootHalt]; exact hhalt
  obtain ⟨k1, phases, qCells, _, htr1, hrepFinal⟩ :=
    cts_run_simulated_by_pfTrace P hrun (initPhaseStates P) (initQueueCells w)
      (initProgramFreeCTS_rep P w)
  obtain ⟨k2, _, htr2, hhalt0⟩ :=
    cts_halt_simulated_by_pfTrace_exact P finalIdx phases qCells hrepFinal
  let flagOpen := layoutTerm (.opened .unopened .unopened) (phaseAt 1).1 (phaseAt 1).2
  have hfull0 : PFTrace (k1 + k2) (encodeProgramFreeCTS P w)
      (pfRootTerm flagOpen (progRingTerm phases 2) (queueListTerm qCells 2)) :=
    pfTrace_trans htr1 htr2
  have hsame : reached = pfRootTerm flagOpen (progRingTerm phases 2) (queueListTerm qCells 2) :=
    (pfTrace_halt_unique htrace hhaltRoot hfull0 hhalt0).2
  have hflagClean : pfMidOpeningQ flagOpen = false := by
    dsimp [flagOpen]
    rw [layout_opened_phase _ _ _ (phase_at_good 1)]
    exact pfMidOpeningQ_frameTerm _ _ _
  rw [hsame]
  exact decodeProgramFreeCTS_pfRootTerm P ⟨finalIdx, []⟩ phases qCells flagOpen hflagClean hrepFinal

/-- Universal halted-trace readback: for **any** `k` and `reached` accepted by `pfHaltAutomaton`
    along `PFTrace k (encodeProgramFreeCTS P w) reached`, `decodeProgramFreeCTS reached`
    decodes the exact halted CTS configuration `⟨finalIdx, []⟩`. -/
theorem decodeProgramFreeCTS_of_halted_trace (P : CTSProgram) (w : List Bool)
    {k : Nat} {reached : Term}
    (htrace : PFTrace k (encodeProgramFreeCTS P w) reached)
    (hhalt : pfHaltAutomaton.evalAccepts reached = true) :
    ∃ n finalIdx,
      CTSRun P n (initCTSConfig w) ⟨finalIdx, []⟩ ∧
      ctsStep P ⟨finalIdx, []⟩ = none ∧
      decodeProgramFreeCTS reached = some (finalIdx, []) := by
  have hcts : CTSEventuallyHalts P w :=
    (program_free_cts_halting_iff_automaton P w).mpr ⟨k, reached, htrace, hhalt⟩
  obtain ⟨n, final, hrun, hstop⟩ := hcts
  have hqEmpty : final.queue = [] := (ctsStep_eq_none_iff P final).mp hstop
  cases final with
  | mk finalIdx fQueue =>
      simp only at hqEmpty
      subst fQueue
      exact ⟨n, finalIdx, hrun, hstop,
        decodeProgramFreeCTS_of_cts_run_and_halted_trace P w hrun htrace hhalt⟩

/-- **Halted Pure-`S` Output Readback Theorem (`decodeProgramFreeCTS_halted`)**:
    Whenever `CTSEventuallyHalts P w`, the halted pure-`S` term `reached` accepted by
    `pfHaltAutomaton` along `PFTrace` decodes via `decodeProgramFreeCTS` to `some (finalIdx, [])`,
    matching the halted CTS run `CTSRun P n (initCTSConfig w) ⟨finalIdx, []⟩`. -/
theorem decodeProgramFreeCTS_halted (P : CTSProgram) (w : List Bool)
    (h : CTSEventuallyHalts P w) :
    ∃ n finalIdx k reached,
      CTSRun P n (initCTSConfig w) ⟨finalIdx, []⟩ ∧
      ctsStep P ⟨finalIdx, []⟩ = none ∧
      PFTrace k (encodeProgramFreeCTS P w) reached ∧
      pfHaltAutomaton.evalAccepts reached = true ∧
      decodeProgramFreeCTS reached = some (finalIdx, []) := by
  obtain ⟨k, reached, htrace, hhalt⟩ := (program_free_cts_halting_iff_automaton P w).mp h
  obtain ⟨n, finalIdx, hrun, hstop, hdec⟩ := decodeProgramFreeCTS_of_halted_trace P w htrace hhalt
  exact ⟨n, finalIdx, k, reached, hrun, hstop, htrace, hhalt, hdec⟩


/-! ## Section 10: All-Step Polynomial Trajectory Leaf Bound (`encodeProgramFreeCTS_trajectory_leaves_poly`) -/

/-- Every `Term` has at least one leaf. -/
theorem leaves_pos : ∀ t : Term, 1 ≤ leaves t
  | .s => Nat.le_refl 1
  | .var _ => Nat.le_refl 1
  | .app a b => by
      have ha := leaves_pos a
      have hb := leaves_pos b
      simp only [leaves]
      omega

/-- Because pure `S` is non-erasing (`S x y z → (x z)(y z)` replaces the head `S` leaf with a
    second copy of `z`, where `leaves z ≥ 1`), **every** native `Step` is leaf-monotone! -/
theorem step_leaves_mono {a b : Term} (h : Step a b) : leaves a ≤ leaves b := by
  induction h with
  | root x y z =>
      have hz := leaves_pos z
      simp only [S, leaves]
      omega
  | left _ ih =>
      simp only [leaves]
      omega
  | right _ ih =>
      simp only [leaves]
      omega

theorem pfTrace_leaves_mono {k : Nat} {a b : Term} (h : PFTrace k a b) :
    leaves a ≤ leaves b := by
  induction h with
  | zero _ => exact Nat.le_refl _
  | next hs _ ih => exact Nat.le_trans (step_leaves_mono (pfSelect_step_sound hs)) ih

theorem pfTrace_prefix_leaves_le {k M : Nat} {start reached checkpoint : Term}
    (htrace : PFTrace k start reached)
    (hcheck : PFTrace M start checkpoint)
    (hle : k ≤ M) :
    leaves reached ≤ leaves checkpoint := by
  have hsplitEq : M = k + (M - k) := by omega
  rw [hsplitEq] at hcheck
  obtain ⟨mid, hpre, hsuf⟩ := pfTrace_split k (M - k) hcheck
  have hsame : reached = mid := pfTrace_unique htrace mid hpre
  subst mid
  exact pfTrace_leaves_mono hsuf

/-! ### Exact Additive `pfOpenedCount` Algebra Across Layout Constructors -/

theorem pfOpenedCount_versionLayout_append {width : Nat}
    (r1 r2 : List {bits : List Bool // bits.length = width}) :
    pfOpenedCount (versionLayout (r1 ++ r2)) =
      pfOpenedCount (versionLayout r1) + pfOpenedCount (versionLayout r2) := by
  induction r1 with
  | nil => simp [versionLayout, pfOpenedCount]
  | cons entry rest ih =>
      simp only [List.cons_append, versionLayout, pfOpenedCount, ih]
      omega

theorem pfOpenedCount_templateListLayout_append (c1 c2 : List (List Rec3)) :
    pfOpenedCount (templateListLayout (c1 ++ c2)) =
      pfOpenedCount (templateListLayout c1) + pfOpenedCount (templateListLayout c2) := by
  induction c1 with
  | nil => simp [templateListLayout, pfOpenedCount]
  | cons r rest ih =>
      simp only [List.cons_append, templateListLayout, pfOpenedCount, ih]
      omega

theorem pfOpenedCount_queueListLayout_append (c1 c2 : List (List Rec3)) :
    pfOpenedCount (queueListLayout (c1 ++ c2)) =
      pfOpenedCount (queueListLayout c1) + pfOpenedCount (queueListLayout c2) := by
  induction c1 with
  | nil => simp [queueListLayout, pfOpenedCount]
  | cons r rest ih =>
      simp only [List.cons_append, queueListLayout, pfOpenedCount, ih]
      omega

theorem pfOpenedCount_progRingLayout_append (p1 p2 : List PhaseState) :
    pfOpenedCount (progRingLayout (p1 ++ p2)) =
      pfOpenedCount (progRingLayout p1) + pfOpenedCount (progRingLayout p2) := by
  induction p1 with
  | nil => simp [progRingLayout, pfOpenedCount]
  | cons ph rest ih =>
      simp only [List.cons_append, progRingLayout, pfOpenedCount, ih]
      omega

def pfStateOpenCount (phases : List PhaseState) (qCells : List (List Rec3)) : Nat :=
  pfOpenedCount (pfHubLayout .unopened phases qCells)

theorem pfStateOpenCount_queue_ver_append (phases : List PhaseState)
    (qBefore : List (List Rec3)) (qFocus : List Rec3) (qAfter : List (List Rec3)) (entry : Rec3) :
    pfStateOpenCount phases (qBefore ++ (qFocus ++ [entry]) :: qAfter) ≤
      pfStateOpenCount phases (qBefore ++ qFocus :: qAfter) + 8 := by
  have he := pfOpenedCount_single_rec3 entry
  simp only [pfStateOpenCount, pfHubLayout, pfOpenedCount_queueListLayout_append,
    queueListLayout, pfOpenedCount_versionLayout_append, pfOpenedCount]
  omega

theorem pfStateOpenCount_queue_tail_open (phases : List PhaseState) (qCells : List (List Rec3)) :
    pfStateOpenCount phases (qCells ++ [[]]) = pfStateOpenCount phases qCells + 1 := by
  simp only [pfStateOpenCount, pfHubLayout, pfOpenedCount_queueListLayout_append,
    queueListLayout, versionLayout, pfOpenedCount]
  omega

theorem pfStateOpenCount_template_ver_append
    (pBefore : List PhaseState) (pRecs : List Rec2)
    (tBefore : List (List Rec3)) (tFocus : List Rec3) (tAfter : List (List Rec3))
    (pAfter : List PhaseState) (qCells : List (List Rec3)) (entry : Rec3) :
    pfStateOpenCount (pBefore ++ ⟨pRecs, tBefore ++ (tFocus ++ [entry]) :: tAfter⟩ :: pAfter) qCells ≤
      pfStateOpenCount (pBefore ++ ⟨pRecs, tBefore ++ tFocus :: tAfter⟩ :: pAfter) qCells + 8 := by
  have he := pfOpenedCount_single_rec3 entry
  simp only [pfStateOpenCount, pfHubLayout, pfOpenedCount_progRingLayout_append,
    progRingLayout, pfOpenedCount_templateListLayout_append, templateListLayout,
    pfOpenedCount_versionLayout_append, pfOpenedCount]
  omega

theorem pfStateOpenCount_phase_ver_append
    (pBefore : List PhaseState) (pRecs : List Rec2) (tCells : List (List Rec3))
    (pAfter : List PhaseState) (qCells : List (List Rec3)) (entry : Rec2) :
    pfStateOpenCount (pBefore ++ ⟨pRecs ++ [entry], tCells⟩ :: pAfter) qCells ≤
      pfStateOpenCount (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) qCells + 6 := by
  have he := pfOpenedCount_single_rec2 entry
  simp only [pfStateOpenCount, pfHubLayout, pfOpenedCount_progRingLayout_append,
    progRingLayout, pfOpenedCount_versionLayout_append, pfOpenedCount]
  omega

theorem pfStateOpenCount_copy_one_bit
    (pBefore : List PhaseState) (pRecs : List Rec2) (pAfter : List PhaseState)
    (tDone : List (List Rec3)) (tFocus : List Rec3) (tRem : List (List Rec3))
    (consumed : List (List Rec3)) (c0 : List Rec3) (uCells : List (List Rec3)) (sbit : Bool) :
    pfStateOpenCount
        (pBefore ++ ⟨pRecs, tDone ++ (tFocus ++ [recAppending sbit, recIdle sbit]) :: tRem⟩ :: pAfter)
        (consumed ++ c0 :: (uCells ++ [[recStaging sbit, recUnconsumed sbit]])) ≤
      pfStateOpenCount
        (pBefore ++ ⟨pRecs, tDone ++ tFocus :: tRem⟩ :: pAfter)
        (consumed ++ c0 :: uCells) + 33 := by
  have ht : pfOpenedCount (versionLayout [recAppending sbit, recIdle sbit]) ≤ 16 := by
    simpa using pfOpenedCount_versionLayout [recAppending sbit, recIdle sbit]
  have hq : pfOpenedCount (versionLayout [recStaging sbit, recUnconsumed sbit]) ≤ 16 := by
    simpa using pfOpenedCount_versionLayout [recStaging sbit, recUnconsumed sbit]
  simp only [pfStateOpenCount, pfHubLayout, pfOpenedCount_progRingLayout_append,
    progRingLayout, pfOpenedCount_templateListLayout_append, templateListLayout,
    pfOpenedCount_queueListLayout_append, queueListLayout,
    pfOpenedCount_versionLayout_append, pfOpenedCount]
  omega

theorem sumAppendantLengths_append (xs ys : List (List Bool)) :
    sumAppendantLengths (xs ++ ys) = sumAppendantLengths xs + sumAppendantLengths ys := by
  induction xs with
  | nil => simp [sumAppendantLengths]
  | cons a rest ih => simp only [List.cons_append, sumAppendantLengths, ih]; omega

theorem appAct_length_le_ctsInputSize (P : CTSProgram) (w : List Bool)
    (appBefore : List (List Bool)) (appAct : List Bool) (appAfter : List (List Bool))
    (hprog : P.phases = appBefore ++ appAct :: appAfter) :
    appAct.length ≤ ctsInputSize P w := by
  unfold ctsInputSize
  rw [hprog, sumAppendantLengths_append, sumAppendantLengths]
  omega

theorem pfHubLayout_halted_term (phases : List PhaseState) (qCells : List (List Rec3)) :
    (numeral 1 ⋅ S) ⋅ layoutTerm (pfHubLayout (.opened .unopened .unopened) phases qCells) 2 2 =
      pfRootTerm (layoutTerm (.opened .unopened .unopened) (phaseAt 1).1 (phaseAt 1).2)
        (progRingTerm phases 2) (queueListTerm qCells 2) := by
  change (numeral 1 ⋅ S) ⋅
    layoutTerm (pfHubLayout (.opened .unopened .unopened) phases qCells) (phaseAt 0).1 (phaseAt 0).2 = _
  rw [pfHubLayout, layout_opened_phase _ _ _ (phase_at_good 0)]
  change (numeral 1 ⋅ S) ⋅ frameTerm
    (layoutTerm (.opened .unopened .unopened) (phaseAt 1).1 (phaseAt 1).2)
    (layoutTerm (.opened (progRingLayout phases) (queueListLayout qCells))
      (phaseAt 1).1 (phaseAt 1).2) (depthJunk 0) = _
  rw [layout_opened_phase _ _ _ (phase_at_good 1)]
  change (numeral 1 ⋅ S) ⋅ frameTerm
    (layoutTerm (.opened .unopened .unopened) (phaseAt 1).1 (phaseAt 1).2)
    (frameTerm (layoutTerm (progRingLayout phases) (phaseAt 2).1 (phaseAt 2).2)
      (layoutTerm (queueListLayout qCells) (phaseAt 2).1 (phaseAt 2).2) (depthJunk 1))
    (depthJunk 0) = _
  rw [progRingLayout_term phases 2, queueListLayout_term qCells 2]
  rfl

theorem pfOpenedCount_halted_hub (phases : List PhaseState) (qCells : List (List Rec3)) :
    pfOpenedCount (pfHubLayout (.opened .unopened .unopened) phases qCells) =
      pfStateOpenCount phases qCells + 1 := by
  simp only [pfStateOpenCount, pfHubLayout, pfOpenedCount]
  omega

/-! ### Bounded Micro-Step & Macro-Step Simulation Lemmas -/

theorem pf_trace_arm_templates_bounded
    (pBefore : List PhaseState) (pRecs : List Rec2) (pAfter : List PhaseState)
    (consumed : List (List Rec3)) (u0 : List Rec3) (uRest : List (List Rec3))
    (hbInact : ∀ ph ∈ pBefore, newestRecords ph.pRecs none = some [false, false])
    (hpAct : newestRecords pRecs none = some [true, false])
    (haInact : ∀ ph ∈ pAfter, newestRecords ph.pRecs none = some [false, false])
    (hcons : ∀ r ∈ consumed, IsConsumedCell r)
    (hu0 : IsUnconsumedFor u0 true)
    (huRest : AllUnconsumed uRest) :
    ∀ (tIdle : List (List Rec3)) (appIdle : List Bool)
      (tArmed : List (List Rec3)) (appArmed : List Bool),
      TemplateMatchesArmed tArmed appArmed →
      TemplateMatchesIdle tIdle appIdle →
      ∃ k tArmedOut, 6 * appIdle.length ≤ k ∧
        PFTrace k
          (pfMachineTerm (pBefore ++ ⟨pRecs, tArmed ++ tIdle⟩ :: pAfter) (consumed ++ u0 :: uRest))
          (pfMachineTerm (pBefore ++ ⟨pRecs, tArmedOut⟩ :: pAfter) (consumed ++ u0 :: uRest)) ∧
        TemplateMatchesArmed tArmedOut (appArmed ++ appIdle) ∧
        pfStateOpenCount (pBefore ++ ⟨pRecs, tArmedOut⟩ :: pAfter) (consumed ++ u0 :: uRest) ≤
          pfStateOpenCount (pBefore ++ ⟨pRecs, tArmed ++ tIdle⟩ :: pAfter) (consumed ++ u0 :: uRest) +
            8 * appIdle.length := by
  intro tIdle
  induction tIdle with
  | nil =>
      intro appIdle tArmed appArmed hArmed hIdle
      cases appIdle with
      | cons _ _ => simp [TemplateMatchesIdle] at hIdle
      | nil =>
          simp only [List.append_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
          exact ⟨0, tArmed, Nat.le_refl 0, PFTrace.zero _, hArmed, Nat.le_refl _⟩
  | cons t0 tRest ih =>
      intro appIdle tArmed appArmed hArmed hIdle
      cases appIdle with
      | nil => simp [TemplateMatchesIdle] at hIdle
      | cons sbit sRest =>
          rcases hIdle with ⟨ht0, htRest⟩
          obtain ⟨hnoH, hfindA⟩ := scanPhases_unique_active pBefore ⟨pRecs, tArmed ++ t0 :: tRest⟩ pAfter
            hbInact hpAct haInact
          obtain ⟨hqCons, hqUncons⟩ := scanQueue_front_unconsumed_shape consumed u0 uRest true hcons hu0 huRest
          have htIdle := specScanTemplates_armed_then_idle tArmed appArmed t0 tRest sbit hArmed ht0
          obtain ⟨k1, klo1, _, htr1⟩ := pf_lift_template_ver_append pBefore pRecs tArmed t0 tRest pAfter
            (consumed ++ u0 :: uRest) (recArmed sbit) (by
              unfold pfDecideAction
              rw [hnoH, hfindA, hqCons, hqUncons]
              dsimp only [↓reduceIte, entryOfPhaseAt]
              rw [htIdle]
              simp [List.append_assoc, recArmed])
          have hb1 := pfStateOpenCount_template_ver_append pBefore pRecs tArmed t0 tRest pAfter
            (consumed ++ u0 :: uRest) (recArmed sbit)
          have ht0Armed : IsArmedFor (t0 ++ [recArmed sbit]) sbit :=
            newest_records_append t0 (recArmed sbit) none
          have hArmedNext : TemplateMatchesArmed (tArmed ++ [t0 ++ [recArmed sbit]]) (appArmed ++ [sbit]) :=
            templateMatchesArmed_append hArmed ⟨ht0Armed, trivial⟩
          have hlistEq : tArmed ++ (t0 ++ [recArmed sbit]) :: tRest =
              (tArmed ++ [t0 ++ [recArmed sbit]]) ++ tRest := by simp [List.append_assoc]
          rw [hlistEq] at htr1 hb1
          obtain ⟨k2, tArmedOut, klo2, htr2, hArmedFinal, hb2⟩ :=
            ih sRest (tArmed ++ [t0 ++ [recArmed sbit]]) (appArmed ++ [sbit]) hArmedNext htRest
          have happEq : (appArmed ++ [sbit]) ++ sRest = appArmed ++ sbit :: sRest := by simp [List.append_assoc]
          rw [happEq] at hArmedFinal
          refine ⟨k1 + k2, tArmedOut, ?_, pfTrace_trans htr1 htr2, hArmedFinal, ?_⟩
          · simp only [List.length_cons]; omega
          · simp only [List.length_cons]; omega

theorem pf_trace_copy_one_bit_bounded
    (pBefore : List PhaseState) (pRecs : List Rec2) (pAfter : List PhaseState)
    (tDone : List (List Rec3)) (appDone : List Bool)
    (tFocus : List Rec3) (sbit : Bool)
    (tRem : List (List Rec3)) (appRem : List Bool)
    (consumed : List (List Rec3)) (c0 : List Rec3) (b : Bool) (uCells : List (List Rec3))
    (hbInact : ∀ ph ∈ pBefore, newestRecords ph.pRecs none = some [false, false])
    (hpAct : newestRecords pRecs none = some [true, false])
    (haInact : ∀ ph ∈ pAfter, newestRecords ph.pRecs none = some [false, false])
    (htDone : TemplateMatchesIdle tDone appDone)
    (htFocus : IsArmedFor tFocus sbit)
    (htRem : TemplateMatchesArmed tRem appRem)
    (hcons : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b])
    (huCells : AllUnconsumed uCells) :
    ∃ k, 30 ≤ k ∧
      PFTrace k
        (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tFocus :: tRem⟩ :: pAfter)
          (consumed ++ c0 :: uCells))
        (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ (tFocus ++ [recAppending sbit, recIdle sbit]) :: tRem⟩ :: pAfter)
          (consumed ++ c0 :: (uCells ++ [[recStaging sbit, recUnconsumed sbit]]))) := by
  let tFocus1 := tFocus ++ [recAppending sbit]
  let tFocus2 := tFocus1 ++ [recIdle sbit]
  obtain ⟨hnoH1, hfindA1⟩ := scanPhases_unique_active pBefore ⟨pRecs, tDone ++ tFocus :: tRem⟩ pAfter
    hbInact hpAct haInact
  obtain ⟨hqC1, hqSt1, _, hqTp1⟩ := scanQueue_consuming_clean_shape consumed c0 uCells b hcons hc0 huCells
  obtain ⟨htArm1, htApp1⟩ := specScanTemplates_idle_then_armed tDone appDone tFocus tRem appRem sbit
    htDone htFocus htRem
  obtain ⟨k1, klo1, _, htr1⟩ := pf_lift_template_ver_append pBefore pRecs tDone tFocus tRem pAfter
    (consumed ++ c0 :: uCells) (recAppending sbit) (by
      unfold pfDecideAction
      rw [hnoH1, hfindA1, hqC1, hqSt1]
      dsimp only [entryOfPhaseAt]
      rw [htApp1, htArm1]
      simp [List.append_assoc, recAppending])
  have htFocus1App : IsAppendingFor tFocus1 sbit := newest_records_append tFocus (recAppending sbit) none
  have htApp2 := specScanTemplates_idle_then_appending tDone appDone tFocus1 tRem sbit htDone htFocus1App
  obtain ⟨hnoH2, hfindA2⟩ := scanPhases_unique_active pBefore ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ pAfter
    hbInact hpAct haInact
  obtain ⟨_, _, hqUi2, _⟩ := scanQueue_consuming_clean_shape consumed c0 uCells b hcons hc0 huCells
  obtain ⟨k2, hk2, htr2⟩ := pf_lift_queue_tail_open (pBefore ++ ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ :: pAfter)
    (consumed ++ c0 :: uCells) (by
      unfold pfDecideAction
      rw [hnoH2, hfindA2, hqC1, hqSt1, hqUi2, hqTp1]
      dsimp only [entryOfPhaseAt]
      rw [htApp2])
  have klo2 : 6 ≤ k2 := by cases hk2 <;> omega
  obtain ⟨hqC3, hqSt3, hqUi3⟩ := scanQueue_consuming_uninit_shape consumed c0 uCells b hcons hc0 huCells
  obtain ⟨k3, klo3, _, htr3⟩ := pf_lift_queue_ver_append (pBefore ++ ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ :: pAfter)
    (consumed ++ c0 :: uCells) [] [] (recStaging sbit) (by
      unfold pfDecideAction
      rw [hnoH2, hfindA2, hqC3, hqSt3, hqUi3]
      dsimp only [entryOfPhaseAt]
      rw [htApp2]
      rfl)
  obtain ⟨hqC4, hqSt4, _⟩ := scanQueue_consuming_staging_shape consumed c0 uCells b sbit hcons hc0 huCells
  obtain ⟨k4, klo4, _, htr4⟩ := pf_lift_template_ver_append pBefore pRecs tDone tFocus1 tRem pAfter
    (consumed ++ c0 :: uCells ++ [[recStaging sbit]]) (recIdle sbit) (by
      unfold pfDecideAction
      rw [hnoH2, hfindA2, hqC4, hqSt4]
      dsimp only [entryOfPhaseAt]
      rw [htApp2]
      simp [List.append_assoc, recIdle])
  have htFocus2Idle : IsIdleFor tFocus2 sbit := newest_records_append tFocus1 (recIdle sbit) none
  obtain ⟨hnoH5, hfindA5⟩ := scanPhases_unique_active pBefore ⟨pRecs, tDone ++ tFocus2 :: tRem⟩ pAfter
    hbInact hpAct haInact
  have htApp5 : (specScanTemplates ((tDone ++ tFocus2 :: tRem).map (fun r => newestRecords r none))).firstAppending = none := by
    have hsplit : tDone ++ tFocus2 :: tRem = (tDone ++ [tFocus2]) ++ tRem := by simp [List.append_assoc]
    rw [hsplit]
    have hd2 : TemplateMatchesIdle (tDone ++ [tFocus2]) (appDone ++ [sbit]) :=
      templateMatchesIdle_append htDone ⟨htFocus2Idle, trivial⟩
    cases htrm : tRem with
    | nil =>
        rw [List.append_nil]
        exact (specScanTemplates_allIdle_noArmed_noApp hd2).2
    | cons tr0 trs =>
        cases appRem with
        | nil => rw [htrm] at htRem; simp [TemplateMatchesArmed] at htRem
        | cons sb0 sbs =>
            rw [htrm] at htRem
            exact (specScanTemplates_idle_then_armed (tDone ++ [tFocus2]) (appDone ++ [sbit])
              tr0 trs sbs sb0 hd2 htRem.1 htRem.2).2
  obtain ⟨k5, klo5, _, htr5⟩ := pf_lift_queue_ver_append (pBefore ++ ⟨pRecs, tDone ++ tFocus2 :: tRem⟩ :: pAfter)
    (consumed ++ c0 :: uCells) [recStaging sbit] [] (recUnconsumed sbit) (by
      unfold pfDecideAction
      rw [hnoH5, hfindA5, hqC4, hqSt4]
      dsimp only [entryOfPhaseAt]
      rw [htApp5]
      rfl)
  have htr3' : PFTrace k3
      (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ :: pAfter) (consumed ++ c0 :: uCells ++ [[]]))
      (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tFocus1 :: tRem⟩ :: pAfter) (consumed ++ c0 :: uCells ++ [[recStaging sbit]])) := by
    simpa [List.append_assoc] using htr3
  have htr5' : PFTrace k5
      (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tFocus2 :: tRem⟩ :: pAfter) (consumed ++ c0 :: uCells ++ [[recStaging sbit]]))
      (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ (tFocus ++ [recAppending sbit, recIdle sbit]) :: tRem⟩ :: pAfter)
        (consumed ++ c0 :: (uCells ++ [[recStaging sbit, recUnconsumed sbit]]))) := by
    simpa [tFocus2, tFocus1, List.append_assoc] using htr5
  exact ⟨k1 + (k2 + (k3 + (k4 + k5))), by omega,
    pfTrace_trans htr1 (pfTrace_trans htr2 (pfTrace_trans htr3' (pfTrace_trans htr4 htr5')))⟩

theorem pf_trace_copy_all_bits_bounded
    (pBefore : List PhaseState) (pRecs : List Rec2) (pAfter : List PhaseState)
    (consumed : List (List Rec3)) (c0 : List Rec3) (b : Bool)
    (hbInact : ∀ ph ∈ pBefore, newestRecords ph.pRecs none = some [false, false])
    (hpAct : newestRecords pRecs none = some [true, false])
    (haInact : ∀ ph ∈ pAfter, newestRecords ph.pRecs none = some [false, false])
    (hcons : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b]) :
    ∀ (tRem : List (List Rec3)) (appRem : List Bool)
      (tDone : List (List Rec3)) (appDone : List Bool)
      (uCells : List (List Rec3)) (qWord : List Bool),
      TemplateMatchesIdle tDone appDone →
      TemplateMatchesArmed tRem appRem →
      QueueMatchesWord uCells qWord →
      ∃ k tIdleOut uCellsOut, 30 * appRem.length ≤ k ∧
        PFTrace k
          (pfMachineTerm (pBefore ++ ⟨pRecs, tDone ++ tRem⟩ :: pAfter) (consumed ++ c0 :: uCells))
          (pfMachineTerm (pBefore ++ ⟨pRecs, tIdleOut⟩ :: pAfter) (consumed ++ c0 :: uCellsOut)) ∧
        TemplateMatchesIdle tIdleOut (appDone ++ appRem) ∧
        QueueMatchesWord uCellsOut (qWord ++ appRem) ∧
        pfStateOpenCount (pBefore ++ ⟨pRecs, tIdleOut⟩ :: pAfter) (consumed ++ c0 :: uCellsOut) ≤
          pfStateOpenCount (pBefore ++ ⟨pRecs, tDone ++ tRem⟩ :: pAfter) (consumed ++ c0 :: uCells) +
            33 * appRem.length := by
  intro tRem
  induction tRem with
  | nil =>
      intro appRem tDone appDone uCells qWord htDone htRem hqWord
      cases appRem with
      | cons _ _ => simp [TemplateMatchesArmed] at htRem
      | nil =>
          simp only [List.append_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
          exact ⟨0, tDone, uCells, Nat.le_refl 0, PFTrace.zero _, htDone, hqWord, Nat.le_refl _⟩
  | cons t0 tRest ih =>
      intro appRem tDone appDone uCells qWord htDone htRem hqWord
      cases appRem with
      | nil => simp [TemplateMatchesArmed] at htRem
      | cons sbit sRest =>
          rcases htRem with ⟨ht0, htRest⟩
          obtain ⟨k1, klo1, htr1⟩ := pf_trace_copy_one_bit_bounded pBefore pRecs pAfter tDone appDone
            t0 sbit tRest sRest consumed c0 b uCells hbInact hpAct haInact htDone ht0 htRest hcons hc0
            (queueMatchesWord_allUnconsumed hqWord)
          have hb1 := pfStateOpenCount_copy_one_bit pBefore pRecs pAfter tDone t0 tRest consumed c0 uCells sbit
          let t0Done := t0 ++ [recAppending sbit, recIdle sbit]
          let newQCell := [recStaging sbit, recUnconsumed sbit]
          have ht0Idle : IsIdleFor t0Done sbit := by
            have hassoc : t0Done = (t0 ++ [recAppending sbit]) ++ [recIdle sbit] := by
              simp [t0Done, List.append_assoc]
            rw [hassoc]
            exact newest_records_append _ (recIdle sbit) none
          have htDoneNext : TemplateMatchesIdle (tDone ++ [t0Done]) (appDone ++ [sbit]) :=
            templateMatchesIdle_append htDone ⟨ht0Idle, trivial⟩
          have hqNew : QueueMatchesWord (uCells ++ [newQCell]) (qWord ++ [sbit]) :=
            queueMatchesWord_append hqWord ⟨rfl, trivial⟩
          have htSplit : tDone ++ t0Done :: tRest = (tDone ++ [t0Done]) ++ tRest := by
            simp [List.append_assoc]
          rw [htSplit] at htr1 hb1
          obtain ⟨k2, tIdleOut, uCellsOut, klo2, htr2, htFinal, hqFinal, hb2⟩ :=
            ih sRest (tDone ++ [t0Done]) (appDone ++ [sbit]) (uCells ++ [newQCell]) (qWord ++ [sbit])
              htDoneNext htRest hqNew
          have happEq : (appDone ++ [sbit]) ++ sRest = appDone ++ sbit :: sRest := by simp [List.append_assoc]
          have hqwEq : (qWord ++ [sbit]) ++ sRest = qWord ++ sbit :: sRest := by simp [List.append_assoc]
          rw [happEq] at htFinal
          rw [hqwEq] at hqFinal
          refine ⟨k1 + k2, tIdleOut, uCellsOut, ?_, pfTrace_trans htr1 htr2, htFinal, hqFinal, ?_⟩
          · simp only [List.length_cons]; omega
          · dsimp only [newQCell] at hb2
            simp only [List.length_cons]
            omega

theorem pf_trace_handoff_and_advance_bounded (P : CTSProgram) (idx : Nat)
    (pBefore : List PhaseState) (pRecs : List Rec2) (tCells : List (List Rec3)) (pAfter : List PhaseState)
    (appBefore : List (List Bool)) (appAct : List Bool) (appAfter : List (List Bool))
    (consumed : List (List Rec3)) (c0 : List Rec3) (b : Bool) (uCells : List (List Rec3)) (nextWord : List Bool)
    (hprog : P.phases = appBefore ++ appAct :: appAfter)
    (hpIdx : pBefore.length = idx)
    (haIdx : appBefore.length = idx)
    (hbMatch : PhasesInactiveMatch pBefore appBefore)
    (hpAct : newestRecords pRecs none = some [true, false])
    (htIdle : TemplateMatchesIdle tCells appAct)
    (haMatch : PhasesInactiveMatch pAfter appAfter)
    (hcons : ∀ r ∈ consumed, IsConsumedCell r)
    (hc0 : newestRecords c0 none = some [true, false, b])
    (hqWord : QueueMatchesWord uCells nextWord) :
    ∃ k phasesOut qCellsOut, 18 ≤ k ∧
      PFTrace k
        (pfMachineTerm (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) (consumed ++ c0 :: uCells))
        (pfMachineTerm phasesOut qCellsOut) ∧
      PFConfigRep P ⟨(idx + 1) % P.phases.length, nextWord⟩ phasesOut qCellsOut ∧
      pfStateOpenCount phasesOut qCellsOut ≤
        pfStateOpenCount (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) (consumed ++ c0 :: uCells) + 26 := by
  have hbInact := phasesInactiveMatch_status hbMatch
  have haInact := phasesInactiveMatch_status haMatch
  have huAll := queueMatchesWord_allUnconsumed hqWord
  obtain ⟨hnoH1, hfindA1⟩ := scanPhases_unique_active pBefore ⟨pRecs, tCells⟩ pAfter hbInact hpAct haInact
  obtain ⟨hqC1, hqSt1, _, _⟩ := scanQueue_consuming_clean_shape consumed c0 uCells b hcons hc0 huAll
  obtain ⟨htNoArm, htNoApp⟩ := specScanTemplates_allIdle_noArmed_noApp htIdle
  obtain ⟨k1, klo1, _, htr1⟩ := pf_lift_phase_ver_append pBefore pRecs tCells pAfter
    (consumed ++ c0 :: uCells) recHandoff (by
      unfold pfDecideAction
      rw [hnoH1, hfindA1, hqC1, hqSt1]
      dsimp only [entryOfPhaseAt]
      rw [htNoApp, htNoArm]
      rfl)
  have hb1 := pfStateOpenCount_phase_ver_append pBefore pRecs tCells pAfter
    (consumed ++ c0 :: uCells) recHandoff
  let pRecsH := pRecs ++ [recHandoff]
  let handPh : PhaseState := ⟨pRecsH, tCells⟩
  have hpHand : newestRecords pRecsH none = some [true, true] :=
    newest_records_append pRecs recHandoff none
  have hbNeH : ∀ ph ∈ pBefore, newestRecords ph.pRecs none ≠ some [true, true] :=
    fun ph hp => by rw [hbInact ph hp]; decide
  have hfindH2 := scanPhases_handoff_find pBefore handPh pAfter hbNeH hpHand
  obtain ⟨k2, klo2, _, htr2⟩ := pf_lift_queue_ver_append (pBefore ++ handPh :: pAfter)
    consumed c0 uCells (recConsumed b) (by
      unfold pfDecideAction
      rw [hfindH2, hqC1]
      rfl)
  have hb2 := pfStateOpenCount_queue_ver_append (pBefore ++ handPh :: pAfter)
    consumed c0 uCells (recConsumed b)
  let c0Done := c0 ++ [recConsumed b]
  have hc0Cons : IsConsumedCell c0Done := ⟨b, newest_records_append c0 (recConsumed b) none⟩
  have hconsNext : ∀ r ∈ consumed ++ [c0Done], IsConsumedCell r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | rfl
    · exact hcons r hr
    · exact hc0Cons
  have hqShift : consumed ++ c0Done :: uCells = (consumed ++ [c0Done]) ++ uCells := by
    simp [List.append_assoc]
  have hqNoCons : (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)).consuming = none := by
    cases uCells with
    | nil =>
        rw [List.append_nil]
        exact (scanQueue_halted_shape (consumed ++ [c0Done]) hconsNext).1
    | cons u0 urs =>
        cases nextWord with
        | nil => simp [QueueMatchesWord] at hqWord
        | cons nb nbs =>
            exact (scanQueue_front_unconsumed_shape (consumed ++ [c0Done]) u0 urs nb
              hconsNext hqWord.1 (queueMatchesWord_allUnconsumed hqWord.2)).1
  rw [hqShift] at htr2 hb2
  cases pAfter with
  | cons nxtPh pAfterRest =>
      cases appAfter with
      | nil => simp [PhasesInactiveMatch] at haMatch
      | cons nxtApp appAfterRest =>
          rcases haMatch with ⟨hnxtSpec, haRestMatch⟩
          have hlenGe2 : ((scanPhases (progRingTerm (pBefore ++ handPh :: nxtPh :: pAfterRest) 2)).length == 1) = false := by
            rw [scanPhases_len]
            simp only [List.length_append, List.length_cons]
            exact beq_eq_false_iff_ne.mpr (by omega)
          have hmodEq : (pBefore.length + 1) % (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPh :: pAfterRest) 2)).length =
              (pBefore ++ [handPh]).length := by
            rw [scanPhases_len]
            simp only [List.length_append, List.length_cons, List.length_nil]
            exact Nat.mod_eq_of_lt (by omega)
          have hgetNxt : listGetOpt (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPh :: pAfterRest) 2))
              (pBefore ++ [handPh]).length =
              some (entryOfPhaseAt (pBefore ++ [handPh]).length nxtPh) := by
            have heq : pBefore ++ handPh :: nxtPh :: pAfterRest =
                (pBefore ++ [handPh]) ++ nxtPh :: pAfterRest := by simp [List.append_assoc]
            rw [heq]
            exact scanPhases_get_at (pBefore ++ [handPh]) nxtPh pAfterRest
          have hnxtNotAct : ((entryOfPhaseAt (pBefore ++ [handPh]).length nxtPh).status == some [true, false]) = false := by
            simp [entryOfPhaseAt, hnxtSpec.1]
          have htr3a_pre : pfDecideAction
              (scanPhases (progRingTerm ((pBefore ++ [handPh]) ++ ⟨nxtPh.pRecs, nxtPh.tCells⟩ :: pAfterRest) 2))
              (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)) =
              .writeVer (pfProgRingPath ++ (repeatRightPath (pBefore ++ [handPh]).length ++ [false, true, false, true]))
                2 recActive.val := by
            have heq : (pBefore ++ [handPh]) ++ ⟨nxtPh.pRecs, nxtPh.tCells⟩ :: pAfterRest =
                pBefore ++ handPh :: nxtPh :: pAfterRest := by
              cases nxtPh; simp [List.append_assoc]
            rw [heq]
            unfold pfDecideAction
            rw [hfindH2, hqNoCons, hlenGe2]
            simp only [Bool.false_eq_true, ↓reduceIte, hmodEq, hgetNxt, hnxtNotAct]
            rfl
          obtain ⟨k3, klo3, _, htr3⟩ := pf_lift_phase_ver_append (pBefore ++ [handPh])
            nxtPh.pRecs nxtPh.tCells pAfterRest ((consumed ++ [c0Done]) ++ uCells) recActive htr3a_pre
          have hb3 := pfStateOpenCount_phase_ver_append (pBefore ++ [handPh])
            nxtPh.pRecs nxtPh.tCells pAfterRest ((consumed ++ [c0Done]) ++ uCells) recActive
          let nxtPhAct : PhaseState := ⟨nxtPh.pRecs ++ [recActive], nxtPh.tCells⟩
          have hnxtAct : newestRecords nxtPhAct.pRecs none = some [true, false] :=
            newest_records_append nxtPh.pRecs recActive none
          have hfindH3b := scanPhases_handoff_find pBefore handPh (nxtPhAct :: pAfterRest) hbNeH hpHand
          have hlenGe2b : ((scanPhases (progRingTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) 2)).length == 1) = false := by
            rw [scanPhases_len]; simp only [List.length_append, List.length_cons]
            exact beq_eq_false_iff_ne.mpr (by omega)
          have hmodEqb : (pBefore.length + 1) % (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) 2)).length =
              (pBefore ++ [handPh]).length := by
            rw [scanPhases_len]; simp only [List.length_append, List.length_cons, List.length_nil]
            exact Nat.mod_eq_of_lt (by omega)
          have hgetNxtb : listGetOpt (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) 2))
              (pBefore ++ [handPh]).length =
              some (entryOfPhaseAt (pBefore ++ [handPh]).length nxtPhAct) := by
            have heq : pBefore ++ handPh :: nxtPhAct :: pAfterRest =
                (pBefore ++ [handPh]) ++ nxtPhAct :: pAfterRest := by simp [List.append_assoc]
            rw [heq]
            exact scanPhases_get_at (pBefore ++ [handPh]) nxtPhAct pAfterRest
          have hnxtIsAct : ((entryOfPhaseAt (pBefore ++ [handPh]).length nxtPhAct).status == some [true, false]) = true := by
            simp [entryOfPhaseAt, hnxtAct]
          obtain ⟨k4, klo4, _, htr4⟩ := pf_lift_phase_ver_append pBefore pRecsH tCells (nxtPhAct :: pAfterRest)
            ((consumed ++ [c0Done]) ++ uCells) recInactive (by
              change pfDecideAction (scanPhases (progRingTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) 2))
                (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)) = _
              unfold pfDecideAction
              rw [hfindH3b, hqNoCons, hlenGe2b]
              dsimp only [Bool.false_eq_true, ↓reduceIte]
              rw [hmodEqb, hgetNxtb]
              dsimp only []
              rw [hnxtIsAct]
              rfl)
          have hb4 := pfStateOpenCount_phase_ver_append pBefore pRecsH tCells (nxtPhAct :: pAfterRest)
            ((consumed ++ [c0Done]) ++ uCells) recInactive
          let oldDone : PhaseState := ⟨pRecsH ++ [recInactive], tCells⟩
          have holdInact : PhaseMatchesSpec oldDone false appAct :=
            ⟨newest_records_append pRecsH recInactive none, htIdle⟩
          have htr3' : PFTrace k3
              (pfMachineTerm (pBefore ++ handPh :: nxtPh :: pAfterRest) ((consumed ++ [c0Done]) ++ uCells))
              (pfMachineTerm (pBefore ++ handPh :: nxtPhAct :: pAfterRest) ((consumed ++ [c0Done]) ++ uCells)) := by
            cases nxtPh; simpa [nxtPhAct, List.append_assoc] using htr3
          have hb3' : pfStateOpenCount (pBefore ++ handPh :: nxtPhAct :: pAfterRest) ((consumed ++ [c0Done]) ++ uCells) ≤
              pfStateOpenCount (pBefore ++ handPh :: nxtPh :: pAfterRest) ((consumed ++ [c0Done]) ++ uCells) + 6 := by
            cases nxtPh; simpa [nxtPhAct, List.append_assoc] using hb3
          have hpLen : P.phases.length = idx + 1 + (appAfterRest.length + 1) := by
            rw [hprog]; simp [List.length_append, haIdx]; omega
          have hidxMod : (idx + 1) % P.phases.length = idx + 1 := Nat.mod_eq_of_lt (by omega)
          have hfinalEq : pBefore ++ oldDone :: nxtPhAct :: pAfterRest =
              (pBefore ++ [oldDone]) ++ nxtPhAct :: pAfterRest := by simp [List.append_assoc]
          refine ⟨k1 + (k2 + (k3 + k4)), (pBefore ++ [oldDone]) ++ nxtPhAct :: pAfterRest,
            (consumed ++ [c0Done]) ++ uCells, by omega, ?_, ?_, ?_⟩
          · rw [← hfinalEq]
            exact pfTrace_trans htr1 (pfTrace_trans htr2 (pfTrace_trans htr3' htr4))
          · refine ⟨Nat.mod_lt _ (ctsProgram_length_pos P), ?_,
              consumed ++ [c0Done], uCells, rfl, hconsNext, hqWord⟩
            dsimp only []
            rw [hidxMod]
            refine ⟨pBefore ++ [oldDone], nxtPhAct, pAfterRest, appBefore ++ [appAct], nxtApp, appAfterRest,
              rfl, by rw [hprog]; simp [List.append_assoc], by simp [hpIdx], by simp [haIdx],
              phasesInactiveMatch_append hbMatch ⟨holdInact, trivial⟩,
              ⟨hnxtAct, hnxtSpec.2⟩, haRestMatch⟩
          · rw [← hfinalEq]
            change pfStateOpenCount (pBefore ++ oldDone :: nxtPhAct :: pAfterRest)
              ((consumed ++ [c0Done]) ++ uCells) ≤ _
            dsimp only [handPh, pRecsH, oldDone] at hb1 hb2 hb3' hb4 ⊢
            omega
  | nil =>
      cases appAfter with
      | cons _ _ => simp [PhasesInactiveMatch] at haMatch
      | nil =>
          cases pBefore with
          | nil =>
              cases appBefore with
              | cons _ _ => simp [PhasesInactiveMatch] at hbMatch
              | nil =>
                  have hlen1 : ((scanPhases (progRingTerm ([] ++ handPh :: []) 2)).length == 1) = true := by
                    rw [scanPhases_len]; rfl
                  obtain ⟨k3, klo3, _, htr3⟩ := pf_lift_phase_ver_append [] pRecsH tCells []
                    ((consumed ++ [c0Done]) ++ uCells) recActive (by
                      unfold pfDecideAction
                      rw [hfindH2, hqNoCons, hlen1]
                      rfl)
                  have hb3 := pfStateOpenCount_phase_ver_append [] pRecsH tCells []
                    ((consumed ++ [c0Done]) ++ uCells) recActive
                  let pRecsFinal := pRecsH ++ [recActive]
                  have hpFinalAct : newestRecords pRecsFinal none = some [true, false] :=
                    newest_records_append pRecsH recActive none
                  have hpLen1 : P.phases.length = 1 := by rw [hprog]; rfl
                  have hmod0 : (idx + 1) % P.phases.length = 0 := by rw [hpLen1, Nat.mod_one]
                  refine ⟨k1 + (k2 + k3), [⟨pRecsFinal, tCells⟩], (consumed ++ [c0Done]) ++ uCells,
                    by omega, pfTrace_trans htr1 (pfTrace_trans htr2 htr3), ?_, ?_⟩
                  · refine ⟨Nat.mod_lt _ (ctsProgram_length_pos P), ?_,
                      consumed ++ [c0Done], uCells, rfl, hconsNext, hqWord⟩
                    dsimp only []
                    rw [hmod0]
                    exact ⟨[], ⟨pRecsFinal, tCells⟩, [], [], appAct, [],
                      rfl, hprog, rfl, rfl, trivial, ⟨hpFinalAct, htIdle⟩, trivial⟩
                  · dsimp only [List.nil_append, handPh, pRecsH, pRecsFinal] at hb1 hb2 hb3 ⊢
                    omega
          | cons firstPh pBeforeRest =>
              cases appBefore with
              | nil => simp [PhasesInactiveMatch] at hbMatch
              | cons firstApp appBeforeRest =>
                  rcases hbMatch with ⟨hfirstSpec, hbRestMatch⟩
                  have hlenGe2 : ((scanPhases (progRingTerm ((firstPh :: pBeforeRest) ++ handPh :: []) 2)).length == 1) = false := by
                    rw [scanPhases_len]; simp only [List.length_append, List.length_cons]
                    exact beq_eq_false_iff_ne.mpr (by omega)
                  have hmod0 : ((firstPh :: pBeforeRest).length + 1) %
                      (scanPhases (progRingTerm ((firstPh :: pBeforeRest) ++ handPh :: []) 2)).length = 0 := by
                    rw [scanPhases_len]
                    have heqLen : ((firstPh :: pBeforeRest) ++ [handPh]).length =
                        (firstPh :: pBeforeRest).length + 1 := by simp
                    rw [heqLen, Nat.mod_self]
                  have hget0 : listGetOpt (scanPhases (progRingTerm ((firstPh :: pBeforeRest) ++ handPh :: []) 2)) 0 =
                      some (entryOfPhaseAt 0 firstPh) := by
                    have heq : (firstPh :: pBeforeRest) ++ handPh :: [] =
                        [] ++ firstPh :: (pBeforeRest ++ [handPh]) := rfl
                    rw [heq]
                    exact scanPhases_get_at [] firstPh (pBeforeRest ++ [handPh])
                  have hfirstNotAct : ((entryOfPhaseAt 0 firstPh).status == some [true, false]) = false := by
                    simp [entryOfPhaseAt, hfirstSpec.1]
                  have htr3a_pre : pfDecideAction
                      (scanPhases (progRingTerm ([] ++ ⟨firstPh.pRecs, firstPh.tCells⟩ :: (pBeforeRest ++ [handPh])) 2))
                      (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)) =
                      .writeVer (pfProgRingPath ++ (repeatRightPath ([] : List PhaseState).length ++ [false, true, false, true]))
                        2 recActive.val := by
                    have heq : [] ++ ⟨firstPh.pRecs, firstPh.tCells⟩ :: (pBeforeRest ++ [handPh]) =
                        (firstPh :: pBeforeRest) ++ handPh :: [] := by
                      cases firstPh; rfl
                    rw [heq]
                    unfold pfDecideAction
                    rw [hfindH2, hqNoCons, hlenGe2]
                    simp only [Bool.false_eq_true, ↓reduceIte, hmod0, hget0, hfirstNotAct]
                    rfl
                  obtain ⟨k3, klo3, _, htr3⟩ := pf_lift_phase_ver_append [] firstPh.pRecs firstPh.tCells
                    (pBeforeRest ++ [handPh]) ((consumed ++ [c0Done]) ++ uCells) recActive htr3a_pre
                  have hb3 := pfStateOpenCount_phase_ver_append [] firstPh.pRecs firstPh.tCells
                    (pBeforeRest ++ [handPh]) ((consumed ++ [c0Done]) ++ uCells) recActive
                  let firstPhAct : PhaseState := ⟨firstPh.pRecs ++ [recActive], firstPh.tCells⟩
                  have hfirstAct : newestRecords firstPhAct.pRecs none = some [true, false] :=
                    newest_records_append firstPh.pRecs recActive none
                  have hbNeHb : ∀ ph ∈ firstPhAct :: pBeforeRest, newestRecords ph.pRecs none ≠ some [true, true] := by
                    intro ph hm
                    simp only [List.mem_cons] at hm
                    rcases hm with rfl | hm'
                    · rw [hfirstAct]; decide
                    · rw [phasesInactiveMatch_status hbRestMatch ph hm']; decide
                  have hfindH3b := scanPhases_handoff_find (firstPhAct :: pBeforeRest) handPh [] hbNeHb hpHand
                  have hlenGe2b : ((scanPhases (progRingTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) 2)).length == 1) = false := by
                    rw [scanPhases_len]; simp only [List.length_append, List.length_cons]
                    exact beq_eq_false_iff_ne.mpr (by omega)
                  have hmod0b : ((firstPhAct :: pBeforeRest).length + 1) %
                      (scanPhases (progRingTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) 2)).length = 0 := by
                    rw [scanPhases_len]
                    have heqLen : ((firstPhAct :: pBeforeRest) ++ [handPh]).length =
                        (firstPhAct :: pBeforeRest).length + 1 := by simp
                    rw [heqLen, Nat.mod_self]
                  have hget0b : listGetOpt (scanPhases (progRingTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) 2)) 0 =
                      some (entryOfPhaseAt 0 firstPhAct) := by
                    have heq : (firstPhAct :: pBeforeRest) ++ handPh :: [] =
                        [] ++ firstPhAct :: (pBeforeRest ++ [handPh]) := rfl
                    rw [heq]
                    exact scanPhases_get_at [] firstPhAct (pBeforeRest ++ [handPh])
                  have hfirstIsAct : ((entryOfPhaseAt 0 firstPhAct).status == some [true, false]) = true := by
                    simp [entryOfPhaseAt, hfirstAct]
                  obtain ⟨k4, klo4, _, htr4⟩ := pf_lift_phase_ver_append (firstPhAct :: pBeforeRest)
                    pRecsH tCells [] ((consumed ++ [c0Done]) ++ uCells) recInactive (by
                      change pfDecideAction (scanPhases (progRingTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) 2))
                        (scanQueue (queueListTerm ((consumed ++ [c0Done]) ++ uCells) 2)) = _
                      unfold pfDecideAction
                      rw [hfindH3b, hqNoCons, hlenGe2b]
                      dsimp only [Bool.false_eq_true, ↓reduceIte]
                      rw [hmod0b, hget0b]
                      dsimp only []
                      rw [hfirstIsAct]
                      rfl)
                  have hb4 := pfStateOpenCount_phase_ver_append (firstPhAct :: pBeforeRest)
                    pRecsH tCells [] ((consumed ++ [c0Done]) ++ uCells) recInactive
                  let oldDone : PhaseState := ⟨pRecsH ++ [recInactive], tCells⟩
                  have holdInact : PhaseMatchesSpec oldDone false appAct :=
                    ⟨newest_records_append pRecsH recInactive none, htIdle⟩
                  have htr3' : PFTrace k3
                      (pfMachineTerm ((firstPh :: pBeforeRest) ++ handPh :: []) ((consumed ++ [c0Done]) ++ uCells))
                      (pfMachineTerm ((firstPhAct :: pBeforeRest) ++ handPh :: []) ((consumed ++ [c0Done]) ++ uCells)) := by
                    cases firstPh; exact htr3
                  have hb3' : pfStateOpenCount ((firstPhAct :: pBeforeRest) ++ handPh :: []) ((consumed ++ [c0Done]) ++ uCells) ≤
                      pfStateOpenCount ((firstPh :: pBeforeRest) ++ handPh :: []) ((consumed ++ [c0Done]) ++ uCells) + 6 := by
                    cases firstPh; exact hb3
                  have hpLenEq : P.phases.length = idx + 1 := by
                    rw [hprog, ← haIdx]; simp
                  have hidxMod0 : (idx + 1) % P.phases.length = 0 := by rw [hpLenEq, Nat.mod_self]
                  refine ⟨k1 + (k2 + (k3 + k4)), firstPhAct :: (pBeforeRest ++ [oldDone]),
                    (consumed ++ [c0Done]) ++ uCells, by omega, ?_, ?_, ?_⟩
                  · exact pfTrace_trans htr1 (pfTrace_trans htr2 (pfTrace_trans htr3' htr4))
                  · refine ⟨Nat.mod_lt _ (ctsProgram_length_pos P), ?_,
                      consumed ++ [c0Done], uCells, rfl, hconsNext, hqWord⟩
                    dsimp only []
                    rw [hidxMod0]
                    exact ⟨[], firstPhAct, pBeforeRest ++ [oldDone], [], firstApp, appBeforeRest ++ [appAct],
                      rfl, by rw [hprog]; rfl, rfl, rfl, trivial, ⟨hfirstAct, hfirstSpec.2⟩,
                      phasesInactiveMatch_append hbRestMatch ⟨holdInact, trivial⟩⟩
                  · change pfStateOpenCount ((firstPhAct :: pBeforeRest) ++ oldDone :: [])
                      ((consumed ++ [c0Done]) ++ uCells) ≤ _
                    dsimp only [handPh, pRecsH, oldDone] at hb1 hb2 hb3' hb4 ⊢
                    omega

theorem cts_step_simulated_by_pfTrace_bounded (P : CTSProgram) (w : List Bool) {cfg cfg' : CTSConfig}
    (phases : List PhaseState) (qCells : List (List Rec3))
    (hrep : PFConfigRep P cfg phases qCells)
    (hstep : ctsStep P cfg = some cfg') :
    ∃ k phases' qCells', 6 ≤ k ∧
      PFTrace k (pfMachineTerm phases qCells) (pfMachineTerm phases' qCells') ∧
      PFConfigRep P cfg' phases' qCells' ∧
      pfStateOpenCount phases' qCells' ≤ pfStateOpenCount phases qCells + 2 * k ∧
      pfStateOpenCount phases' qCells' ≤ pfStateOpenCount phases qCells + 34 + 41 * ctsInputSize P w := by
  cases cfg with
  | mk idx queue =>
      cases queue with
      | nil => simp [ctsStep] at hstep
      | cons b rest =>
          obtain ⟨hidxLt, ⟨pBefore, actPh, pAfter, appBefore, appAct, appAfter,
            rfl, hprog, hpIdx, haIdx, hbMatch, hactSpec, haMatch⟩,
            consumed, unconsumed, rfl, hcons, hqWord⟩ := hrep
          cases actPh with
          | mk pRecs tCells =>
              rcases hactSpec with ⟨hpAct, htIdle⟩
              cases unconsumed with
              | nil => simp [QueueMatchesWord] at hqWord
              | cons u0 uRest =>
                  rcases hqWord with ⟨hu0, huRestWord⟩
                  have hbInact := phasesInactiveMatch_status hbMatch
                  have haInact := phasesInactiveMatch_status haMatch
                  have huRestAll := queueMatchesWord_allUnconsumed huRestWord
                  have happGet : P.phases.get ⟨idx, hidxLt⟩ = appAct := by
                    rw [list_get_of_eq hprog idx hidxLt]
                    exact list_get_at_split appBefore appAct appAfter idx haIdx (hprog ▸ hidxLt)
                  have happLe : appAct.length ≤ ctsInputSize P w :=
                    appAct_length_le_ctsInputSize P w appBefore appAct appAfter hprog
                  rw [ctsStep_cons P idx hidxLt b rest, happGet, Option.some.injEq] at hstep
                  subst cfg'
                  cases b with
                  | false =>
                      obtain ⟨hnoH, hfindA⟩ := scanPhases_unique_active pBefore ⟨pRecs, tCells⟩ pAfter
                        hbInact hpAct haInact
                      obtain ⟨hqCons, hqUncons⟩ := scanQueue_front_unconsumed_shape consumed u0 uRest false
                        hcons hu0 huRestAll
                      obtain ⟨k1, klo1, _, htr1⟩ := pf_lift_queue_ver_append
                        (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) consumed u0 uRest (recConsuming false) (by
                          unfold pfDecideAction
                          rw [hnoH, hfindA, hqCons, hqUncons]
                          rfl)
                      have hb1 := pfStateOpenCount_queue_ver_append
                        (pBefore ++ ⟨pRecs, tCells⟩ :: pAfter) consumed u0 uRest (recConsuming false)
                      have hu0Cons : newestRecords (u0 ++ [recConsuming false]) none = some [true, false, false] :=
                        newest_records_append u0 (recConsuming false) none
                      obtain ⟨k2, phasesOut, qCellsOut, klo2, htr2, hrepOut, hb2⟩ :=
                        pf_trace_handoff_and_advance_bounded P idx pBefore pRecs tCells pAfter
                          appBefore appAct appAfter consumed (u0 ++ [recConsuming false]) false uRest rest
                          hprog hpIdx haIdx hbMatch hpAct htIdle haMatch hcons hu0Cons huRestWord
                      exact ⟨k1 + k2, phasesOut, qCellsOut, by omega, pfTrace_trans htr1 htr2,
                        by simpa using hrepOut, by omega, by omega⟩
                  | true =>
                      have htSplit0 : tCells = [] ++ tCells := rfl
                      rw [htSplit0]
                      obtain ⟨kA, tArmed, kloA, htrA, htArmed, hbA⟩ := pf_trace_arm_templates_bounded
                        pBefore pRecs pAfter consumed u0 uRest hbInact hpAct haInact hcons hu0 huRestAll
                        tCells appAct [] [] trivial htIdle
                      rw [List.nil_append] at htArmed
                      obtain ⟨hnoHA, hfindAA⟩ := scanPhases_unique_active pBefore ⟨pRecs, tArmed⟩ pAfter
                        hbInact hpAct haInact
                      obtain ⟨hqCons, hqUncons⟩ := scanQueue_front_unconsumed_shape consumed u0 uRest true
                        hcons hu0 huRestAll
                      have htNoIdle := (specScanTemplates_allArmed_noIdle_noApp htArmed).1
                      obtain ⟨kM, kloM, _, htrM⟩ := pf_lift_queue_ver_append
                        (pBefore ++ ⟨pRecs, tArmed⟩ :: pAfter) consumed u0 uRest (recConsuming true) (by
                          unfold pfDecideAction
                          rw [hnoHA, hfindAA, hqCons, hqUncons]
                          dsimp only [↓reduceIte, entryOfPhaseAt]
                          rw [htNoIdle]
                          rfl)
                      have hbM := pfStateOpenCount_queue_ver_append
                        (pBefore ++ ⟨pRecs, tArmed⟩ :: pAfter) consumed u0 uRest (recConsuming true)
                      let c0 := u0 ++ [recConsuming true]
                      have hc0 : newestRecords c0 none = some [true, false, true] :=
                        newest_records_append u0 (recConsuming true) none
                      have htArmedSplit : tArmed = [] ++ tArmed := rfl
                      rw [htArmedSplit] at htrM hbM
                      obtain ⟨kB, tIdleOut, uCellsOut, kloB, htrB, htIdleOut, hqWordOut, hbB⟩ :=
                        pf_trace_copy_all_bits_bounded pBefore pRecs pAfter consumed c0 true
                          hbInact hpAct haInact hcons hc0 tArmed appAct [] [] uRest rest
                          trivial htArmed huRestWord
                      rw [List.nil_append] at htIdleOut
                      obtain ⟨kC, phasesOut, qCellsOut, kloC, htrC, hrepOut, hbC⟩ :=
                        pf_trace_handoff_and_advance_bounded P idx pBefore pRecs tIdleOut pAfter
                          appBefore appAct appAfter consumed c0 true uCellsOut (rest ++ appAct)
                          hprog hpIdx haIdx hbMatch hpAct htIdleOut haMatch hcons hc0 hqWordOut
                      dsimp only [c0, List.nil_append] at hbA hbM hbB hbC ⊢
                      exact ⟨kA + (kM + (kB + kC)), phasesOut, qCellsOut, by omega,
                        pfTrace_trans htrA (pfTrace_trans htrM (pfTrace_trans htrB htrC)),
                        by simpa using hrepOut, by omega, by omega⟩

theorem nat_lt_or_ge : ∀ a b : Nat, a < b ∨ b ≤ a
  | _, 0 => Or.inr (Nat.zero_le _)
  | 0, _ + 1 => Or.inl (Nat.succ_pos _)
  | a + 1, b + 1 =>
      match nat_lt_or_ge a b with
      | .inl h => Or.inl (Nat.succ_lt_succ h)
      | .inr h => Or.inr (Nat.succ_le_succ h)

theorem nat_le_of_not_lt {a b : Nat} (hnot : ¬ b < a) : a ≤ b :=
  match nat_lt_or_ge b a with
  | .inl h => False.elim (hnot h)
  | .inr h => h

theorem cts_bounding_checkpoint_aux (P : CTSProgram) (w : List Bool)
    {k : Nat} {reached : Term} (htrace : PFTrace k (encodeProgramFreeCTS P w) reached) :
    ∀ (fuel : Nat) (cfg : CTSConfig) (phases : List PhaseState) (qCells : List (List Rec3)) (kAcc : Nat),
      PFConfigRep P cfg phases qCells →
      PFTrace kAcc (encodeProgramFreeCTS P w) (pfMachineTerm phases qCells) →
      pfStateOpenCount phases qCells ≤ (2 + 9 * ctsInputSize P w) + 2 * kAcc →
      kAcc ≤ k →
      k < kAcc + 6 * fuel →
      ∃ M s,
        k ≤ M ∧
        PFTrace M (encodeProgramFreeCTS P w) ((numeral 1 ⋅ S) ⋅ layoutTerm s 2 2) ∧
        pfOpenedCount s ≤ 36 + 50 * ctsInputSize P w + 2 * k := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ _ _ kAcc _ _ _ hle hlt
      exact False.elim (by omega)
  | succ fuel ih =>
      intro cfg phases qCells kAcc hrep htrAcc hopenAcc hle hlt
      cases hs : ctsStep P cfg with
      | none =>
          have hqEmpty : cfg.queue = [] := (ctsStep_eq_none_iff P cfg).mp hs
          cases cfg with
          | mk idx fQueue =>
              simp only at hqEmpty
              subst fQueue
              obtain ⟨kHalt, _, htrHalt, hhalt⟩ :=
                cts_halt_simulated_by_pfTrace_exact P idx phases qCells hrep
              let sHalt := pfHubLayout (.opened .unopened .unopened) phases qCells
              have htermEq := pfHubLayout_halted_term phases qCells
              have hM : PFTrace (kAcc + kHalt) (encodeProgramFreeCTS P w)
                  ((numeral 1 ⋅ S) ⋅ layoutTerm sHalt 2 2) := by
                rw [htermEq]
                exact pfTrace_trans htrAcc htrHalt
              have hhaltLayout : pfRootHalt ((numeral 1 ⋅ S) ⋅ layoutTerm sHalt 2 2) = true := by
                rw [htermEq]
                exact hhalt
              have hnotLt : ¬ kAcc + kHalt < k := fun hbad =>
                pf_halt_cannot_precede_longer_trace hM hhaltLayout htrace hbad
              have hkLe : k ≤ kAcc + kHalt := nat_le_of_not_lt hnotLt
              have hsCount := pfOpenedCount_halted_hub phases qCells
              exact ⟨kAcc + kHalt, sHalt, hkLe, hM, by dsimp [sHalt]; omega⟩
      | some cfg' =>
          obtain ⟨kStep, phases', qCells', hkStep, htrStep, hrep', hopen2k, hopenN⟩ :=
            cts_step_simulated_by_pfTrace_bounded P w phases qCells hrep hs
          rcases nat_lt_or_ge k (kAcc + kStep) with hcross | hge
          · let sNext := pfHubLayout .unopened phases' qCells'
            have hM : PFTrace (kAcc + kStep) (encodeProgramFreeCTS P w)
                ((numeral 1 ⋅ S) ⋅ layoutTerm sNext 2 2) := by
              rw [pfHubLayout_unopened_term]
              exact pfTrace_trans htrAcc htrStep
            have hsCount : pfOpenedCount sNext = pfStateOpenCount phases' qCells' := rfl
            exact ⟨kAcc + kStep, sNext, Nat.le_of_lt hcross, hM, by omega⟩
          · exact ih cfg' phases' qCells' (kAcc + kStep) hrep'
              (pfTrace_trans htrAcc htrStep) (by omega) hge (by omega)

/-- Explicit polynomial constant for all-step unfolded trajectory leaf counts. -/
def pfTrajectorySizeConst : Nat := 35000

/-- **All-Step Polynomial Trajectory Leaf Bound (`encodeProgramFreeCTS_trajectory_leaves_poly`)**:
    Every term `reached` along `PFTrace k (encodeProgramFreeCTS P w) reached` has unfolded
    pure-`S` leaf count bounded quadratically by `35000 * (ctsInputSize P w + k + 1)^2`. -/
theorem encodeProgramFreeCTS_trajectory_leaves_poly (P : CTSProgram) (w : List Bool)
    {k : Nat} {reached : Term}
    (htrace : PFTrace k (encodeProgramFreeCTS P w) reached) :
    leaves reached ≤ pfTrajectorySizeConst * (ctsInputSize P w + k + 1) ^ 2 := by
  have hinitOpen : pfStateOpenCount (initPhaseStates P) (initQueueCells w) ≤
      (2 + 9 * ctsInputSize P w) + 2 * 0 := by
    simpa [pfStateOpenCount, encodeCTSLayout] using encodeCTSLayout_openedCount_linear P w
  obtain ⟨M, s, hkM, hM, hsOpen⟩ :=
    cts_bounding_checkpoint_aux P w htrace (k + 1) (initCTSConfig w)
      (initPhaseStates P) (initQueueCells w) 0
      (initProgramFreeCTS_rep P w) (PFTrace.zero _) hinitOpen (Nat.zero_le k) (by omega)
  have hleavesLe : leaves reached ≤ leaves ((numeral 1 ⋅ S) ⋅ layoutTerm s 2 2) :=
    pfTrace_prefix_leaves_le htrace hM hkM
  have hsBound : pfOpenedCount s ≤ 50 * (ctsInputSize P w + k + 1) := by omega
  have hh := pfLayoutHeight_le_openedCount s
  have hg : goodPhase (2, 2) := by unfold goodPhase; decide
  have hH : (2, 2).2 + pfLayoutHeight s ≤ 2 + 50 * (ctsInputSize P w + k + 1) := by
    dsimp only []
    omega
  have hlay := pf_layoutTerm_leaves_bound s (2, 2)
    (2 + 50 * (ctsInputSize P w + k + 1)) hg hH
  dsimp only [] at hlay
  have h1 : 2 * pfOpenedCount s + 1 ≤ 101 * (ctsInputSize P w + k + 1) := by omega
  have h2 : 19 + 6 * (2 + 50 * (ctsInputSize P w + k + 1)) ≤
      331 * (ctsInputSize P w + k + 1) := by omega
  have hmul : (2 * pfOpenedCount s + 1) *
      (19 + 6 * (2 + 50 * (ctsInputSize P w + k + 1))) ≤
      (101 * (ctsInputSize P w + k + 1)) * (331 * (ctsInputSize P w + k + 1)) :=
    Nat.mul_le_mul h1 h2
  have hsq : (101 * (ctsInputSize P w + k + 1)) * (331 * (ctsInputSize P w + k + 1)) =
      33431 * ((ctsInputSize P w + k + 1) ^ 2) := by
    simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hpos : 1 ≤ (ctsInputSize P w + k + 1) ^ 2 := by
    simp [Nat.pow_two]
    exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hhead : leaves ((numeral 1 ⋅ S) ⋅ layoutTerm s 2 2) = 8 + leaves (layoutTerm s 2 2) := rfl
  rw [hhead] at hleavesLe
  unfold pfTrajectorySizeConst
  omega

/-- Bounded executable runner returning the halted pure-`S` term for `#guard` readback checks. -/
def runPFBoundedTerm : Nat → Term → Option Term
  | 0, t => if pfRootHalt t then some t else none
  | fuel + 1, t =>
      match pfSelect t with
      | .halt => some t
      | .step t' => runPFBoundedTerm fuel t'
      | .stuck => none

-- 3. Bare-term decoder `#guard` checks (initial encodings & halted pure-S terms, including non-zero `finalIdx`):
#guard decodeProgramFreeCTS (encodeProgramFreeCTS ctsExampleEmptyHalt []) == some (0, [])
#guard decodeProgramFreeCTS (encodeProgramFreeCTS ctsExampleCopyAndDrain [true, false, true]) ==
  some (0, [true, false, true])
#guard decodeProgramFreeCTS (encodeProgramFreeCTS ctsExampleThreePhase [true, false]) ==
  some (0, [true, false])
#guard ((runPFBoundedTerm 20 (encodeProgramFreeCTS ctsExampleEmptyHalt [])).bind decodeProgramFreeCTS) ==
  some (0, [])
#guard ((runPFBoundedTerm 200 (encodeProgramFreeCTS ctsExampleCopyAndDrain [false])).bind decodeProgramFreeCTS) ==
  some (1, [])
#guard ((runPFBoundedTerm 2000 (encodeProgramFreeCTS ctsExampleCopyAndDrain [true, false, true])).bind
  decodeProgramFreeCTS) == some (0, [])
#guard ((runPFBoundedTerm 2500 (encodeProgramFreeCTS ctsExampleThreePhase [true, false])).bind
  decodeProgramFreeCTS) == some (0, [])

end FormalProgramFree

-- 4. Axiom audit on all public theorems (must contain ZERO `Classical.choice` and ZERO `sorry`):
#print axioms FormalProgramFree.pfSelect_step_sound
#print axioms FormalProgramFree.pfSelect_halt_iff
#print axioms FormalProgramFree.pfHaltAutomaton_accepts_eq_pfRootHalt
#print axioms FormalProgramFree.seed_reduces_to_encodeProgramFreeCTS
#print axioms FormalProgramFree.encodeProgramFreeCTS_isClosedPureS
#print axioms FormalProgramFree.encodeCTSLayout_openedCount_linear
#print axioms FormalProgramFree.encodeProgramFreeCTS_leaves_poly
#print axioms FormalProgramFree.cts_step_simulated_by_pfTrace
#print axioms FormalProgramFree.cts_run_simulated_by_pfTrace
#print axioms FormalProgramFree.cts_halt_simulated_by_pfTrace
#print axioms FormalProgramFree.program_free_cts_halting_iff
#print axioms FormalProgramFree.program_free_cts_halting_iff_automaton
#print axioms FormalProgramFree.decodeProgramFreeCTS_pfMachineTerm
#print axioms FormalProgramFree.decodeProgramFreeCTS_encode
#print axioms FormalProgramFree.decodeProgramFreeCTS_of_halted_trace
#print axioms FormalProgramFree.decodeProgramFreeCTS_halted
#print axioms FormalProgramFree.step_leaves_mono
#print axioms FormalProgramFree.encodeProgramFreeCTS_trajectory_leaves_poly
