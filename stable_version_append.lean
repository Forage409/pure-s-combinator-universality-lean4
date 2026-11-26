import root_tape_scanner

/- Every source of one native opening in this trace decodes to the old
   committed record. No claim about the global head search is assumed here. -/

def StableVersionValue {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (shape : Layout) : Prop :=
  ∀ term, layoutMatches shape term → scanVersionTree width none term = newestRecords records none

theorem stable_committed_version {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) :
    StableVersionValue records (versionLayout records) := by
  intro term h
  exact scan_tree_committed_records records term none h

theorem stable_uncommitted_version {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (fields : Layout)
    (hfields : readLayoutFields width fields = none) :
    StableVersionValue records (versionWithFields records fields) := by
  intro term h
  exact scan_tree_uncommitted_fields records fields hfields term none h

inductive StableVersionTrace {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (fuel : Nat) (desired : List Bool) : Nat → Layout → Layout → Prop where
  | done (s : Layout) : StableVersionTrace records fuel desired 0 s s
  | next {n : Nat} {a b c : Layout} {path : List Bool} :
      FuelAgreement fuel width desired a → StableVersionValue records a →
      chooseVersion fuel width desired a = some path → openLayoutAt a path = some b →
      StableVersionTrace records fuel desired n b c → StableVersionTrace records fuel desired (n+1) a c

theorem lift_safe_fields_to_stable_version {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool)
    (hw : desired.length = width) {n : Nat} {a b : Layout}
    (trace : SafeFieldTrace desired n a b) :
    StableVersionTrace records (records.length+1) desired n
      (versionWithFields records a) (versionWithFields records b) := by
  induction trace with
  | done fields => exact StableVersionTrace.done _
  | @next n a b c path hread hchoose hopen rest ih =>
    have hread' : readLayoutFields width a = none := by simpa [hw] using hread
    have hagree : FuelAgreement (records.length+1) width desired (versionWithFields records a) :=
      tree_selector_matches_fuel_uncommitted records desired a hread'
    have hstable := stable_uncommitted_version records a hread'
    have hchoice : chooseVersion (records.length+1) width desired (versionWithFields records a) =
        some (List.replicate records.length false ++ true :: path) := by
      rw [choose_version_with_uncommitted_fields records desired a hread',hchoose]
      rfl
    exact StableVersionTrace.next hagree hstable hchoice (open_version_with_fields records a b path hopen) ih

theorem stable_version_append_complete {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    ∃ k, StableVersionTrace records (records.length+1) entry.val k
        (versionLayout records) (versionLayout (records ++ [entry])) ∧
      1 ≤ k ∧ k ≤ 2*width+2 := by
  obtain ⟨k,hfields,hbound⟩ := safe_selected_fields_complete entry.val []
  have hfields' : SafeFieldTrace entry.val k .unopened (fieldsLayout entry.val) := by
    simpa [partialFieldsLayout] using hfields
  have hrest := lift_safe_fields_to_stable_version records entry.val entry.property hfields'
  have hrest' : StableVersionTrace records (records.length+1) entry.val k
      (partialVersionLayout [] records) (versionLayout (records ++ [entry])) := by
    simpa [version_with_unopened_fields,version_with_complete_fields] using hrest
  refine ⟨k+1, ?_, by omega, ?_⟩
  · exact StableVersionTrace.next (tree_selector_matches_fuel_committed records entry.val)
      (stable_committed_version records) (choose_new_version_slot records entry.val)
      (open_new_version_layout records) hrest'
  · rw [entry.property] at hbound
    omega

#print axioms stable_committed_version
#print axioms stable_uncommitted_version
#print axioms lift_safe_fields_to_stable_version
#print axioms stable_version_append_complete

inductive StableTreeRestartTrace (path : List Bool) (width : Nat) (desired : List Bool)
    (old : Option (List Bool)) : Nat → Term → Term → Prop where
  | zero (a : Term) : StableTreeRestartTrace path width desired old 0 a a
  | next {n : Nat} {a b c : Term} : TreeRestartedNativeStep path width desired a b →
      scanVersionTree width none a = old → StableTreeRestartTrace path width desired old n b c →
      StableTreeRestartTrace path width desired old (n+1) a c

theorem lift_opening_stable_value {width n : Nat}
    {records : List {bits : List Bool // bits.length = width}} {old final : Term}
    (trace : ClosedOpeningTrace n old final) :
    ∀ shape term path fuel desired,
      FuelAgreement fuel width desired shape → StableVersionValue records shape →
      layoutMatches shape term → subLayout shape path = some .unopened →
      termAt term (physicalPath path) = some old →
      chooseSVersion fuel width desired term = some (physicalPath path) →
      ∃ target out, openLayoutAt shape path = some target ∧ layoutMatches target out ∧
        termAt out (physicalPath path) = some final ∧
        replaceTermAt term (physicalPath path) final = some out ∧
        StableTreeRestartTrace path width desired (newestRecords records none) n term out := by
  induction trace with
  | @finish a b hchosen hopen =>
    intro shape term path fuel desired hagree hstable hmatch hslot hat hchoose
    obtain ⟨relpath,hlocal,hdir⟩ := hchosen
    obtain ⟨target,out,hopenLayout,hout,hmatchout,hfinal⟩ :=
      opened_slot_step_updates_layout path shape term a b relpath hmatch hslot hat hdir hopen
    obtain ⟨out',hreplace,hout'⟩ := directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
    have heq : out = out' := directed_step_unique hout out' hout'
    subst out'
    have htree : chooseSVersionTree width desired term = some (physicalPath path) := by
      rw [hagree term hmatch,hchoose]
    have hglobal : TreeRestartedNativeStep path width desired term out :=
      ⟨htree,a,relpath,hat,hlocal,hout⟩
    exact ⟨target,out,hopenLayout,hmatchout,hfinal,hreplace,
      StableTreeRestartTrace.next hglobal (hstable term hmatch) (StableTreeRestartTrace.zero out)⟩
  | @more n a b c hchosen hclosed rest ih =>
    intro shape term path fuel desired hagree hstable hmatch hslot hat hchoose
    obtain ⟨relpath,hlocal,hdir⟩ := hchosen
    obtain ⟨middle,hmiddle,hatMiddle,hchooseMiddle,hmatchMiddle⟩ :=
      restarted_selector_preserves_target shape term a b path relpath fuel width desired
        hmatch hslot hat hdir hclosed hchoose
    obtain ⟨middle',hreplaceFirst,hmiddle'⟩ :=
      directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
    have heq : middle = middle' := directed_step_unique hmiddle middle' hmiddle'
    subst middle'
    obtain ⟨target,out,hopenLayout,hmatchout,hfinal,hreplaceRest,htrace⟩ :=
      ih shape middle path fuel desired hagree hstable hmatchMiddle hslot hatMiddle hchooseMiddle
    have hreplace : replaceTermAt term (physicalPath path) c = some out := by
      rw [← replace_same_path_overwrites (physicalPath path) term b middle c hreplaceFirst]
      exact hreplaceRest
    have htree : chooseSVersionTree width desired term = some (physicalPath path) := by
      rw [hagree term hmatch,hchoose]
    have hglobal : TreeRestartedNativeStep path width desired term middle :=
      ⟨htree,a,relpath,hat,hlocal,hmiddle⟩
    exact ⟨target,out,hopenLayout,hmatchout,hfinal,hreplace,
      StableTreeRestartTrace.next hglobal (hstable term hmatch) htrace⟩

#print axioms lift_opening_stable_value

theorem canonical_selected_opening_stable {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (shape target : Layout) (path : List Bool) (d fuel : Nat) (desired : List Bool)
    (hagree : FuelAgreement fuel width desired shape) (hstable : StableVersionValue records shape)
    (hopen : openLayoutAt shape path = some target)
    (hchoose : chooseSVersion fuel width desired (layoutTerm shape (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath path)) :
    ∃ k, (k=6 ∨ k=7) ∧ StableTreeRestartTrace path width desired (newestRecords records none) k
      (layoutTerm shape (phaseAt d).1 (phaseAt d).2)
      (layoutTerm target (phaseAt d).1 (phaseAt d).2) := by
  let p := phaseAt d
  let q := advancePhase path.length p
  have hp : goodPhase p := phase_at_good d
  have hq : goodPhase q := advance_phase_good path.length p hp
  have hslot : subLayout shape path = some .unopened := open_layout_targets_unopened path shape target hopen
  have hat : termAt (layoutTerm shape p.1 p.2) (physicalPath path) = some (phaseBase q) := by
    exact (selected_slot_is_generator shape target path p hp hopen).2
  have hmatch : layoutMatches shape (layoutTerm shape p.1 p.2) := finite_layout_decodes shape p.1 p.2 hp.1 hp.2
  obtain ⟨k,hk,htrace⟩ := good_phase_opening_trace q hq
  obtain ⟨target',out,hopen',_,_,hreplace,hglobal⟩ :=
    lift_opening_stable_value htrace shape (layoutTerm shape p.1 p.2)
      path fuel desired hagree hstable hmatch hslot hat hchoose
  have htarget : target' = target := by rw [hopen] at hopen'; exact (Option.some.inj hopen').symm
  subst target'
  have hcanonical := canonical_layout_replace path shape target p hp hopen
  have hout : out = layoutTerm target p.1 p.2 := by rw [hcanonical] at hreplace; exact (Option.some.inj hreplace).symm
  subst out
  exact ⟨k,hk,hglobal⟩

#print axioms canonical_selected_opening_stable

def StableAdaptiveStep (width : Nat) (desired : List Bool) (old : Option (List Bool)) (a b : Term) : Prop :=
  TreeAdaptiveNativeStep width desired a b ∧ scanVersionTree width none a = old

inductive StableAdaptiveTrace (width : Nat) (desired : List Bool) (old : Option (List Bool)) :
    Nat → Term → Term → Prop where
  | zero (a : Term) : StableAdaptiveTrace width desired old 0 a a
  | next {n : Nat} {a b c : Term} : StableAdaptiveStep width desired old a b →
      StableAdaptiveTrace width desired old n b c → StableAdaptiveTrace width desired old (n+1) a c

theorem stable_restarted_is_adaptive {path : List Bool} {width : Nat} {desired : List Bool}
    {old : Option (List Bool)} {n : Nat} {a b : Term}
    (h : StableTreeRestartTrace path width desired old n a b) : StableAdaptiveTrace width desired old n a b := by
  induction h with
  | zero x => exact StableAdaptiveTrace.zero x
  | next hab hold _ ih => exact StableAdaptiveTrace.next ⟨⟨path,hab⟩,hold⟩ ih

theorem stable_adaptive_trans {width : Nat} {desired : List Bool} {old : Option (List Bool)}
    {n m : Nat} {a b c : Term} (h : StableAdaptiveTrace width desired old n a b)
    (k : StableAdaptiveTrace width desired old m b c) : StableAdaptiveTrace width desired old (n+m) a c := by
  induction h with
  | zero _ => simpa using k
  | @next n a b c hab _ ih =>
    have result := StableAdaptiveTrace.next hab (ih k)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem stable_version_trace_native {width : Nat}
    {records : List {bits : List Bool // bits.length = width}} {fuel : Nat} {desired : List Bool}
    {n : Nat} {a b : Layout} (trace : StableVersionTrace records fuel desired n a b) (d : Nat) :
    ∃ k, StableAdaptiveTrace width desired (newestRecords records none) k
        (layoutTerm a (phaseAt d).1 (phaseAt d).2) (layoutTerm b (phaseAt d).1 (phaseAt d).2) ∧
      6*n ≤ k ∧ k ≤ 7*n := by
  induction trace with
  | done s => exact ⟨0,StableAdaptiveTrace.zero _,by simp,by simp⟩
  | @next n a b c path hagree hstable hchoose hopen rest ih =>
    have hS : chooseSVersion fuel width desired (layoutTerm a (phaseAt d).1 (phaseAt d).2) =
        some (physicalPath path) := by
      rw [choose_s_version_simulates_layout fuel width desired a (phaseAt d) (phase_at_good d),hchoose]
      rfl
    obtain ⟨first,hfirst,hrun⟩ :=
      canonical_selected_opening_stable records a b path d fuel desired hagree hstable hopen hS
    obtain ⟨last,hlast,hlower,hupper⟩ := ih
    refine ⟨first+last, stable_adaptive_trans (stable_restarted_is_adaptive hrun) hlast, ?_, ?_⟩
    · cases hfirst <;> omega
    · cases hfirst <;> omega

theorem fully_stable_fuel_free_version_append {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (d : Nat) :
    ∃ k, StableAdaptiveTrace width entry.val (newestRecords records none) k
        (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2)
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) ∧
      6 ≤ k ∧ k ≤ 7*(2*width+2) ∧
      scanVersionTree width none
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) = some entry.val := by
  obtain ⟨n,htrace,hnlower,hnupper⟩ := stable_version_append_complete records entry
  obtain ⟨k,hreal,klower,kupper⟩ := stable_version_trace_native htrace d
  have hp := phase_at_good d
  have hm := finite_layout_decodes (versionLayout (records ++ [entry]))
    (phaseAt d).1 (phaseAt d).2 hp.1 hp.2
  refine ⟨k,hreal,?_,?_,?_⟩
  · omega
  · omega
  · rw [scan_tree_committed_records (records ++ [entry]) _ none hm]
    exact newest_records_append records entry none

#print axioms stable_version_trace_native
#print axioms fully_stable_fuel_free_version_append
