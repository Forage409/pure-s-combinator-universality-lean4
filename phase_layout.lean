import protected_opening

/- Depth-indexed phases link arbitrary opened layouts to concrete S terms.
   Initial phase (2,2) is the body reached by the ten-leaf seed. -/

def nextPhase (p : Nat × Nat) : Nat × Nat :=
  if p.1 = 0 then (p.2,p.2+1) else (p.1-1,p.2)

def goodPhase (p : Nat × Nat) : Prop := 2 ≤ p.2 ∧ p.1 ≤ p.2

def phaseAt : Nat → Nat × Nat
  | 0 => (2,2)
  | n+1 => nextPhase (phaseAt n)

def phaseBase (p : Nat × Nat) : Term := generator p.1 p.2

def phaseJunk (p : Nat × Nat) : Term :=
  if p.1 = 0 then (numeral (p.2-1) ⋅ S) ⋅ generator p.2 (p.2+1)
  else (numeral (p.2-2) ⋅ S) ⋅ generator (p.1-1) p.2

theorem next_phase_good (p : Nat × Nat) (h : goodPhase p) : goodPhase (nextPhase p) := by
  unfold goodPhase nextPhase at *
  split <;> simp_all <;> omega

theorem phase_at_good (d : Nat) : goodPhase (phaseAt d) := by
  induction d with
  | zero => unfold goodPhase phaseAt; decide
  | succ d ih => exact next_phase_good (phaseAt d) ih

theorem layout_opened_phase (l r : Layout) (p : Nat × Nat) (h : goodPhase p) :
    layoutTerm (.opened l r) p.1 p.2 =
      frameTerm (layoutTerm l (nextPhase p).1 (nextPhase p).2)
        (layoutTerm r (nextPhase p).1 (nextPhase p).2) (phaseJunk p) := by
  rcases p with ⟨m,n⟩
  cases n with
  | zero => exfalso; simp [goodPhase] at h
  | succ n =>
    cases n with
    | zero => exfalso; simp [goodPhase] at h
    | succ n =>
      cases m with
      | zero => simp [layoutTerm, nextPhase, phaseJunk]
      | succ m => simp [layoutTerm, nextPhase, phaseJunk]

#print axioms next_phase_good
#print axioms phase_at_good
#print axioms layout_opened_phase

def depthBase (d : Nat) : Term := phaseBase (phaseAt d)
def depthJunk (d : Nat) : Term := phaseJunk (phaseAt d)

def bitLayout (b : Bool) : Layout := if b then .opened .unopened .unopened else .unopened

def fieldsLayout : List Bool → Layout
  | [] => .opened .unopened .unopened
  | b :: bs => .opened (bitLayout b) (fieldsLayout bs)

theorem depth_base_closed (d : Nat) : parseFrame (depthBase d) = none := by
  exact parse_generator_closed (phaseAt d).1 (phaseAt d).2

theorem bit_layout_term (d : Nat) (b : Bool) :
    layoutTerm (bitLayout b) (phaseAt d).1 (phaseAt d).2 = indexedFlag depthBase depthJunk d b := by
  cases b with
  | false => rfl
  | true =>
    simp [bitLayout, indexedFlag, depthBase, depthJunk, phaseBase,
      layout_opened_phase _ _ _ (phase_at_good d), phaseAt, layoutTerm]

theorem fields_layout_term (bits : List Bool) : ∀ d,
    layoutTerm (fieldsLayout bits) (phaseAt d).1 (phaseAt d).2 = indexedFields depthBase depthJunk d bits := by
  induction bits with
  | nil =>
    intro d
    simp [fieldsLayout, indexedFields, depthBase, depthJunk, phaseBase,
      layout_opened_phase _ _ _ (phase_at_good d), phaseAt, layoutTerm]
  | cons b bs ih =>
    intro d
    simp only [fieldsLayout, layout_opened_phase _ _ _ (phase_at_good d), indexedFields, depthJunk]
    change frameTerm (layoutTerm (bitLayout b) (phaseAt (d+1)).1 (phaseAt (d+1)).2)
      (layoutTerm (fieldsLayout bs) (phaseAt (d+1)).1 (phaseAt (d+1)).2) (phaseJunk (phaseAt d)) =
      frameTerm (indexedFlag depthBase depthJunk (d+1) b) (indexedFields depthBase depthJunk (d+1) bs)
        (phaseJunk (phaseAt d))
    rw [bit_layout_term, ih]

#print axioms depth_base_closed
#print axioms bit_layout_term
#print axioms fields_layout_term

theorem actual_layout_fields_decode (bits : List Bool) (d : Nat) :
    readFields bits.length (layoutTerm (fieldsLayout bits) (phaseAt d).1 (phaseAt d).2) = some bits := by
  rw [fields_layout_term]
  exact read_indexed_fields depthBase depthJunk depth_base_closed bits d

#print axioms actual_layout_fields_decode

def versionLayout {width : Nat} : List {bits : List Bool // bits.length = width} → Layout
  | [] => .unopened
  | entry :: rest => .opened (versionLayout rest) (fieldsLayout entry.val)

theorem version_layout_term {width : Nat} (records : List {bits : List Bool // bits.length = width}) :
    ∀ d, layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2 =
      versionChain depthBase depthJunk width d records := by
  induction records with
  | nil => intro d; rfl
  | cons entry rest ih =>
    intro d
    simp only [versionLayout, layout_opened_phase _ _ _ (phase_at_good d), versionChain, indexedVersion, depthJunk]
    change frameTerm (layoutTerm (versionLayout rest) (phaseAt (d+1)).1 (phaseAt (d+1)).2)
      (layoutTerm (fieldsLayout entry.val) (phaseAt (d+1)).1 (phaseAt (d+1)).2) (phaseJunk (phaseAt d)) =
      frameTerm (versionChain depthBase depthJunk width (d+1) rest)
        (indexedFields depthBase depthJunk (d+1) entry.val) (phaseJunk (phaseAt d))
    rw [ih, fields_layout_term]

theorem actual_layout_chain_scan {width : Nat} (records : List {bits : List Bool // bits.length = width})
    (d : Nat) (current : Option (List Bool)) :
    scanVersions (records.length+1) width
      (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2) current = newestRecords records current := by
  rw [version_layout_term]
  exact scan_committed_version_chain depthBase depthJunk depth_base_closed width records d current

#print axioms version_layout_term
#print axioms actual_layout_chain_scan

def partialFieldsLayout : List Bool → Layout
  | [] => .unopened
  | b :: bs => .opened (bitLayout b) (partialFieldsLayout bs)

def partialVersionLayout {width : Nat} (pref : List Bool) :
    List {bits : List Bool // bits.length = width} → Layout
  | [] => .opened .unopened (partialFieldsLayout pref)
  | entry :: rest => .opened (partialVersionLayout pref rest) (fieldsLayout entry.val)

theorem partial_fields_layout_term (pref : List Bool) : ∀ d,
    layoutTerm (partialFieldsLayout pref) (phaseAt d).1 (phaseAt d).2 =
      indexedPartialFields depthBase depthJunk d pref := by
  induction pref with
  | nil => intro d; rfl
  | cons b bs ih =>
    intro d
    simp only [partialFieldsLayout, layout_opened_phase _ _ _ (phase_at_good d), indexedPartialFields, depthJunk]
    change frameTerm (layoutTerm (bitLayout b) (phaseAt (d+1)).1 (phaseAt (d+1)).2)
      (layoutTerm (partialFieldsLayout bs) (phaseAt (d+1)).1 (phaseAt (d+1)).2) (phaseJunk (phaseAt d)) =
      frameTerm (indexedFlag depthBase depthJunk (d+1) b)
        (indexedPartialFields depthBase depthJunk (d+1) bs) (phaseJunk (phaseAt d))
    rw [bit_layout_term, ih]

theorem partial_version_layout_term {width : Nat} (pref : List Bool)
    (records : List {bits : List Bool // bits.length = width}) : ∀ d,
    layoutTerm (partialVersionLayout pref records) (phaseAt d).1 (phaseAt d).2 =
      versionChainPartial depthBase depthJunk width pref d records := by
  induction records with
  | nil =>
    intro d
    simp only [partialVersionLayout, layout_opened_phase _ _ _ (phase_at_good d),
      versionChainPartial, indexedPartialVersion, depthJunk]
    change frameTerm (depthBase (d+1))
      (layoutTerm (partialFieldsLayout pref) (phaseAt (d+1)).1 (phaseAt (d+1)).2) (phaseJunk (phaseAt d)) =
      frameTerm (depthBase (d+1)) (indexedPartialFields depthBase depthJunk (d+1) pref) (phaseJunk (phaseAt d))
    rw [partial_fields_layout_term]
  | cons entry rest ih =>
    intro d
    simp only [partialVersionLayout, layout_opened_phase _ _ _ (phase_at_good d),
      versionChainPartial, indexedVersion, depthJunk]
    change frameTerm (layoutTerm (partialVersionLayout pref rest) (phaseAt (d+1)).1 (phaseAt (d+1)).2)
      (layoutTerm (fieldsLayout entry.val) (phaseAt (d+1)).1 (phaseAt (d+1)).2) (phaseJunk (phaseAt d)) =
      frameTerm (versionChainPartial depthBase depthJunk width pref (d+1) rest)
        (indexedFields depthBase depthJunk (d+1) entry.val) (phaseJunk (phaseAt d))
    rw [ih, fields_layout_term]

theorem actual_layout_partial_scan {width : Nat} (pref : List Bool) (hpref : pref.length ≤ width)
    (records : List {bits : List Bool // bits.length = width}) (d : Nat) (current : Option (List Bool)) :
    scanVersions (records.length+2) width
      (layoutTerm (partialVersionLayout pref records) (phaseAt d).1 (phaseAt d).2) current = newestRecords records current := by
  rw [partial_version_layout_term]
  exact scan_chain_ignores_partial_tail depthBase depthJunk depth_base_closed width pref hpref records d current

#print axioms partial_fields_layout_term
#print axioms partial_version_layout_term
#print axioms actual_layout_partial_scan

theorem version_layout_append_grows {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    LayoutGrowth (versionLayout records) (versionLayout (records ++ [entry])) := by
  induction records with
  | nil => exact LayoutGrowth.fromUnopened _
  | cons old rest ih =>
    change LayoutGrowth (.opened (versionLayout rest) (fieldsLayout old.val))
      (.opened (versionLayout (rest ++ [entry])) (fieldsLayout old.val))
    exact LayoutGrowth.opened ih (layout_growth_refl _)

theorem version_append_native_reduces {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (d : Nat) :
    Reduces (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2)
      (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) := by
  have h := phase_at_good d
  exact layout_growth_reduces (version_layout_append_grows records entry)
    (phaseAt d).1 (phaseAt d).2 h.1 h.2

#print axioms version_layout_append_grows
#print axioms version_append_native_reduces

theorem newest_records_append {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (current : Option (List Bool)) :
    newestRecords (records ++ [entry]) current = some entry.val := by
  induction records generalizing current with
  | nil => rfl
  | cons old rest ih => simp [newestRecords, ih]

theorem native_append_then_read {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (d : Nat) :
    ∃ term,
      Reduces (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2) term ∧
      scanVersions ((records ++ [entry]).length+1) width term none = some entry.val := by
  refine ⟨layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2,
    version_append_native_reduces records entry d, ?_⟩
  rw [actual_layout_chain_scan]
  exact newest_records_append records entry none

#print axioms newest_records_append
#print axioms native_append_then_read

def applyLayoutOps : Layout → List (List Bool) → Option Layout
  | shape, [] => some shape
  | shape, path :: rest => (openLayoutAt shape path).bind (fun next => applyLayoutOps next rest)

def fieldOps : List Bool → List (List Bool)
  | [] => [[]]
  | bit :: rest =>
      [[]] ++ (if bit then [[false]] else []) ++ (fieldOps rest).map (fun p => true :: p)

theorem apply_right_ops (l r : Layout) (ops : List (List Bool)) :
    applyLayoutOps (.opened l r) (ops.map (fun p => true :: p)) =
      (applyLayoutOps r ops).map (fun r' => .opened l r') := by
  induction ops generalizing r with
  | nil => rfl
  | cons path rest ih =>
    simp only [List.map_cons, applyLayoutOps, openLayoutAt]
    cases h : openLayoutAt r path with
    | none => simp
    | some r' => simp [ih]

theorem field_ops_build (bits : List Bool) :
    applyLayoutOps .unopened (fieldOps bits) = some (fieldsLayout bits) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => simp [fieldOps, applyLayoutOps, openLayoutAt, fieldsLayout, bitLayout, apply_right_ops, ih]
    | true => simp [fieldOps, applyLayoutOps, openLayoutAt, fieldsLayout, bitLayout, apply_right_ops, ih]

#print axioms apply_right_ops
#print axioms field_ops_build

def countOnes : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countOnes bs

theorem ones_bounded (bits : List Bool) : countOnes bits ≤ bits.length := by
  induction bits with
  | nil => decide
  | cons b bs ih => cases b <;> simp [countOnes] <;> omega

theorem field_ops_count (bits : List Bool) :
    (fieldOps bits).length = bits.length + countOnes bits + 1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [fieldOps, countOnes, ih] <;> omega

theorem field_ops_upper_bound (bits : List Bool) :
    (fieldOps bits).length ≤ 2*bits.length + 1 := by
  rw [field_ops_count]
  have h := ones_bounded bits
  omega

#print axioms field_ops_count
#print axioms field_ops_upper_bound

theorem layout_ops_native (ops : List (List Bool)) :
    ∀ shape target m n, 2 ≤ n → m ≤ n → applyLayoutOps shape ops = some target →
      Reduces (layoutTerm shape m n) (layoutTerm target m n) := by
  induction ops with
  | nil =>
    intro shape target m n hn hm h
    simp [applyLayoutOps] at h
    subst target
    exact Reduces.refl _
  | cons path rest ih =>
    intro shape target m n hn hm h
    cases hx : openLayoutAt shape path with
    | none => simp [applyLayoutOps, hx] at h
    | some next =>
      have hrest : applyLayoutOps next rest = some target := by simpa [applyLayoutOps, hx] using h
      exact reduces_trans (selected_layout_opening path shape next m n hn hm hx)
        (ih next target m n hn hm hrest)

theorem fields_build_by_native_s (bits : List Bool) (m n : Nat) (hn : 2 ≤ n) (hm : m ≤ n) :
    Reduces (layoutTerm .unopened m n) (layoutTerm (fieldsLayout bits) m n) :=
  layout_ops_native (fieldOps bits) .unopened (fieldsLayout bits) m n hn hm (field_ops_build bits)

#print axioms layout_ops_native
#print axioms fields_build_by_native_s

theorem layout_ops_exact_bounds (ops : List (List Bool)) :
    ∀ shape target m n, 2 ≤ n → m ≤ n → applyLayoutOps shape ops = some target →
      ∃ k, ExactSteps k (layoutTerm shape m n) (layoutTerm target m n) ∧
        6*ops.length ≤ k ∧ k ≤ 7*ops.length := by
  induction ops with
  | nil =>
    intro shape target m n hn hm h
    simp [applyLayoutOps] at h
    subst target
    exact ⟨0, ExactSteps.zero _, by simp, by simp⟩
  | cons path rest ih =>
    intro shape target m n hn hm h
    cases hx : openLayoutAt shape path with
    | none => simp [applyLayoutOps, hx] at h
    | some next =>
      have hrest : applyLayoutOps next rest = some target := by simpa [applyLayoutOps, hx] using h
      obtain ⟨k, hk, klower, kupper⟩ := ih next target m n hn hm hrest
      have hshort := selected_layout_opening_short path shape next m n hn hm hx
      cases hshort with
      | inl hs =>
        refine ⟨6+k, exact_steps_trans hs hk, ?_, ?_⟩ <;> simp only [List.length_cons] <;> omega
      | inr hs =>
        refine ⟨7+k, exact_steps_trans hs hk, ?_, ?_⟩ <;> simp only [List.length_cons] <;> omega

theorem fields_build_with_explicit_native_bound (bits : List Bool) (m n : Nat)
    (hn : 2 ≤ n) (hm : m ≤ n) :
    ∃ k, ExactSteps k (layoutTerm .unopened m n) (layoutTerm (fieldsLayout bits) m n) ∧
      k ≤ 7*(2*bits.length+1) := by
  obtain ⟨k,hk,_,hbound⟩ := layout_ops_exact_bounds (fieldOps bits) .unopened (fieldsLayout bits)
    m n hn hm (field_ops_build bits)
  refine ⟨k,hk,?_⟩
  have hcount := field_ops_upper_bound bits
  omega

#print axioms layout_ops_exact_bounds
#print axioms fields_build_with_explicit_native_bound

theorem apply_left_ops (l r : Layout) (ops : List (List Bool)) :
    applyLayoutOps (.opened l r) (ops.map (fun p => false :: p)) =
      (applyLayoutOps l ops).map (fun l' => .opened l' r) := by
  induction ops generalizing l with
  | nil => rfl
  | cons path rest ih =>
    simp only [List.map_cons, applyLayoutOps, openLayoutAt]
    cases h : openLayoutAt l path with
    | none => simp
    | some l' => simp [ih]

def versionOps (bits : List Bool) : List (List Bool) :=
  [] :: (fieldOps bits).map (fun p => true :: p)

def versionAppendOps {width : Nat} :
    List {bits : List Bool // bits.length = width} →
    {bits : List Bool // bits.length = width} → List (List Bool)
  | [], entry => versionOps entry.val
  | _ :: rest, entry => (versionAppendOps rest entry).map (fun p => false :: p)

theorem version_ops_build {width : Nat} (entry : {bits : List Bool // bits.length = width}) :
    applyLayoutOps .unopened (versionOps entry.val) = some (versionLayout [entry]) := by
  simp [versionOps, applyLayoutOps, openLayoutAt, apply_right_ops, field_ops_build, versionLayout]

theorem version_append_ops_build {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    applyLayoutOps (versionLayout records) (versionAppendOps records entry) =
      some (versionLayout (records ++ [entry])) := by
  induction records with
  | nil => exact version_ops_build entry
  | cons old rest ih =>
    simp [versionAppendOps, versionLayout, apply_left_ops, ih]

theorem version_append_ops_count {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    (versionAppendOps records entry).length = 1 + (fieldOps entry.val).length := by
  induction records with
  | nil => simp [versionAppendOps, versionOps, Nat.add_comm]
  | cons old rest ih => simp [versionAppendOps, ih]

theorem version_append_ops_bound {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    (versionAppendOps records entry).length ≤ 2*width + 2 := by
  rw [version_append_ops_count]
  have h := field_ops_upper_bound entry.val
  rw [entry.property] at h
  omega

#print axioms apply_left_ops
#print axioms version_ops_build
#print axioms version_append_ops_build
#print axioms version_append_ops_bound

theorem native_version_append_bounded {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (d : Nat) :
    ∃ k, ExactSteps k
        (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2)
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) ∧
      6 ≤ k ∧ k ≤ 7*(2*width+2) := by
  have hp := phase_at_good d
  obtain ⟨k,hk,klower,kupper⟩ := layout_ops_exact_bounds (versionAppendOps records entry)
    (versionLayout records) (versionLayout (records ++ [entry]))
    (phaseAt d).1 (phaseAt d).2 hp.1 hp.2 (version_append_ops_build records entry)
  have hops := version_append_ops_bound records entry
  have hcount := version_append_ops_count records entry
  refine ⟨k,hk,?_,?_⟩ <;> omega

#print axioms native_version_append_bounded

theorem partial_field_open (pref : List Bool) :
    openLayoutAt (partialFieldsLayout pref) (List.replicate pref.length true) =
      some (partialFieldsLayout (pref ++ [false])) := by
  induction pref with
  | nil => rfl
  | cons b bs ih =>
    simp [partialFieldsLayout, openLayoutAt, List.replicate_succ, ih]

theorem partial_flag_open (pref : List Bool) :
    openLayoutAt (partialFieldsLayout (pref ++ [false]))
      (List.replicate pref.length true ++ [false]) =
      some (partialFieldsLayout (pref ++ [true])) := by
  induction pref with
  | nil => rfl
  | cons b bs ih =>
    simp [partialFieldsLayout, openLayoutAt, List.replicate_succ, ih]

theorem partial_commit_open (bits : List Bool) :
    openLayoutAt (partialFieldsLayout bits) (List.replicate bits.length true) =
      some (fieldsLayout bits) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp [partialFieldsLayout, fieldsLayout, openLayoutAt, List.replicate_succ, ih]

#print axioms partial_field_open
#print axioms partial_flag_open
#print axioms partial_commit_open

def layoutIsOpen : Layout → Bool
  | .unopened => false
  | .opened _ _ => true

def chooseFields : List Bool → Layout → Option (List Bool)
  | [], .unopened => some []
  | [], .opened _ _ => none
  | _ :: _, .unopened => some []
  | b :: bs, .opened flag rest =>
      if b && !(layoutIsOpen flag) then some [false]
      else (chooseFields bs rest).map (fun p => true :: p)

theorem choose_after_correct_prefix (pref remaining : List Bool) :
    chooseFields (pref ++ remaining) (partialFieldsLayout pref) =
      some (List.replicate pref.length true) := by
  induction pref with
  | nil => cases remaining <;> rfl
  | cons b bs ih =>
    cases b <;>
      simp [partialFieldsLayout, bitLayout, chooseFields, layoutIsOpen, List.replicate_succ, ih]

theorem choose_incomplete_one_flag (pref remaining : List Bool) :
    chooseFields (pref ++ true :: remaining) (partialFieldsLayout (pref ++ [false])) =
      some (List.replicate pref.length true ++ [false]) := by
  induction pref with
  | nil => rfl
  | cons b bs ih =>
    cases b <;>
      simp [partialFieldsLayout, bitLayout, chooseFields, layoutIsOpen, List.replicate_succ, ih]

#print axioms choose_after_correct_prefix
#print axioms choose_incomplete_one_flag

def readLayoutFields : Nat → Layout → Option (List Bool)
  | 0, .opened _ _ => some []
  | 0, .unopened => none
  | n+1, .opened flag rest => (readLayoutFields n rest).map (fun bs => layoutIsOpen flag :: bs)
  | _+1, .unopened => none

theorem read_layout_fields_complete (bits : List Bool) :
    readLayoutFields bits.length (fieldsLayout bits) = some bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [readLayoutFields, fieldsLayout, bitLayout, layoutIsOpen, ih]

theorem read_layout_fields_incomplete (pref : List Bool) :
    ∀ remaining, readLayoutFields (pref.length+remaining) (partialFieldsLayout pref) = none := by
  induction pref with
  | nil => intro remaining; cases remaining <;> rfl
  | cons b bs ih =>
    intro remaining
    simp only [List.length_cons]
    have rearrange : bs.length + 1 + remaining = (bs.length + remaining) + 1 := by omega
    rw [rearrange]
    simp [readLayoutFields, partialFieldsLayout, ih]

#print axioms read_layout_fields_complete
#print axioms read_layout_fields_incomplete

def chooseVersion : Nat → Nat → List Bool → Layout → Option (List Bool)
  | 0, _, _, _ => none
  | _+1, _, _, .unopened => some []
  | fuel+1, width, desired, .opened next fields =>
      match readLayoutFields width fields with
      | some _ => (chooseVersion fuel width desired next).map (fun p => false :: p)
      | none => (chooseFields desired fields).map (fun p => true :: p)

theorem choose_new_version_slot {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool) :
    chooseVersion (records.length+1) width desired (versionLayout records) =
      some (List.replicate records.length false) := by
  induction records with
  | nil => rfl
  | cons entry rest ih =>
    have hread : readLayoutFields width (fieldsLayout entry.val) = some entry.val := by
      simpa [entry.property] using read_layout_fields_complete entry.val
    simp [versionLayout, chooseVersion, hread, ih, List.replicate_succ]

theorem choose_partial_version_next {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (pref remaining : List Bool) (hw : (pref ++ remaining).length = width) :
    chooseVersion (records.length+1) width (pref ++ remaining) (partialVersionLayout pref records) =
      some (List.replicate records.length false ++ true :: List.replicate pref.length true) := by
  induction records with
  | nil =>
    have hread : readLayoutFields width (partialFieldsLayout pref) = none := by
      have hw' : pref.length + remaining.length = width := by simpa [List.length_append] using hw
      rw [← hw']
      exact read_layout_fields_incomplete pref remaining.length
    simp [partialVersionLayout, chooseVersion, hread, choose_after_correct_prefix]
  | cons entry rest ih =>
    have hread : readLayoutFields width (fieldsLayout entry.val) = some entry.val := by
      simpa [entry.property] using read_layout_fields_complete entry.val
    simp [partialVersionLayout, chooseVersion, hread, ih, List.replicate_succ]

#print axioms choose_new_version_slot
#print axioms choose_partial_version_next

theorem choose_partial_version_flag {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (pref remaining : List Bool) (hw : (pref ++ true :: remaining).length = width) :
    chooseVersion (records.length+1) width (pref ++ true :: remaining)
      (partialVersionLayout (pref ++ [false]) records) =
      some (List.replicate records.length false ++ true :: (List.replicate pref.length true ++ [false])) := by
  induction records with
  | nil =>
    have hw' : (pref ++ [false]).length + remaining.length = width := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hw ⊢
      omega
    have hread : readLayoutFields width (partialFieldsLayout (pref ++ [false])) = none := by
      rw [← hw']
      exact read_layout_fields_incomplete (pref ++ [false]) remaining.length
    simp [partialVersionLayout, chooseVersion, hread, choose_incomplete_one_flag]
  | cons entry rest ih =>
    have hread : readLayoutFields width (fieldsLayout entry.val) = some entry.val := by
      simpa [entry.property] using read_layout_fields_complete entry.val
    simp [partialVersionLayout, chooseVersion, hread, ih, List.replicate_succ]

#print axioms choose_partial_version_flag

def physicalPath : List Bool → List Bool
  | [] => []
  | false :: rest => [false,true] ++ physicalPath rest
  | true :: rest => [true,false,true] ++ physicalPath rest

def chooseSFields : List Bool → Term → Option (List Bool)
  | [], term => if flagValue term then none else some []
  | b :: bs, term =>
    match parseFrame term with
    | none => some []
    | some (flag, rest, _) =>
      if b && !(flagValue flag) then some [false,true]
      else (chooseSFields bs rest).map (fun p => [true,false,true] ++ p)

theorem flag_value_of_layout (shape : Layout) (p : Nat × Nat) (h : goodPhase p) :
    flagValue (layoutTerm shape p.1 p.2) = layoutIsOpen shape := by
  cases shape with
  | unopened => simp [flagValue, layoutTerm, parse_generator_closed, layoutIsOpen]
  | opened l r =>
    simp [flagValue, layout_opened_phase l r p h, parse_frame, layoutIsOpen]

theorem choose_s_fields_simulates_layout (desired : List Bool) :
    ∀ shape p, goodPhase p →
      chooseSFields desired (layoutTerm shape p.1 p.2) = (chooseFields desired shape).map physicalPath := by
  induction desired with
  | nil =>
    intro shape p hp
    cases shape with
    | unopened => simp [chooseSFields, chooseFields, flagValue, layoutTerm, parse_generator_closed, physicalPath]
    | opened l r =>
      simp [chooseSFields, chooseFields, flagValue, layout_opened_phase l r p hp, parse_frame]
  | cons b bs ih =>
    intro shape p hp
    cases shape with
    | unopened => simp [chooseSFields, chooseFields, layoutTerm, parse_generator_closed, physicalPath]
    | opened l r =>
      have hchild := next_phase_good p hp
      cases b <;> cases hl : layoutIsOpen l <;>
        simp [chooseSFields, chooseFields, layout_opened_phase l r p hp, parse_frame,
          flag_value_of_layout l (nextPhase p) hchild, ih r (nextPhase p) hchild, physicalPath,
          Option.map_map, Function.comp_def, hl]

#print axioms flag_value_of_layout
#print axioms choose_s_fields_simulates_layout

theorem read_s_fields_simulates_layout (width : Nat) :
    ∀ shape p, goodPhase p →
      readFields width (layoutTerm shape p.1 p.2) = readLayoutFields width shape := by
  induction width with
  | zero =>
    intro shape p hp
    cases shape with
    | unopened => simp [readFields, readLayoutFields, flagValue, layoutTerm, parse_generator_closed]
    | opened l r => simp [readFields, readLayoutFields, flagValue, layout_opened_phase l r p hp, parse_frame]
  | succ width ih =>
    intro shape p hp
    cases shape with
    | unopened => simp [readFields, readLayoutFields, layoutTerm, parse_generator_closed]
    | opened l r =>
      have hchild := next_phase_good p hp
      simp [readFields, readLayoutFields, layout_opened_phase l r p hp, parse_frame,
        flag_value_of_layout l (nextPhase p) hchild, ih r (nextPhase p) hchild]

def chooseSVersion : Nat → Nat → List Bool → Term → Option (List Bool)
  | 0, _, _, _ => none
  | fuel+1, width, desired, term =>
    match parseFrame term with
    | none => some []
    | some (next, fields, _) =>
      match readFields width fields with
      | some _ => (chooseSVersion fuel width desired next).map (fun p => [false,true] ++ p)
      | none => (chooseSFields desired fields).map (fun p => [true,false,true] ++ p)

theorem choose_s_version_simulates_layout (fuel width : Nat) (desired : List Bool) :
    ∀ shape p, goodPhase p →
      chooseSVersion fuel width desired (layoutTerm shape p.1 p.2) =
        (chooseVersion fuel width desired shape).map physicalPath := by
  induction fuel with
  | zero => intro shape p hp; rfl
  | succ fuel ih =>
    intro shape p hp
    cases shape with
    | unopened => simp [chooseSVersion, chooseVersion, layoutTerm, parse_generator_closed, physicalPath]
    | opened l r =>
      have hchild := next_phase_good p hp
      simp [chooseSVersion, chooseVersion, layout_opened_phase l r p hp, parse_frame,
        read_s_fields_simulates_layout width r (nextPhase p) hchild,
        choose_s_fields_simulates_layout desired r (nextPhase p) hchild,
        ih l (nextPhase p) hchild, Option.map_map, Function.comp_def]
      cases hh : readLayoutFields width r <;> simp [physicalPath, Option.map_map, Function.comp_def]

#print axioms read_s_fields_simulates_layout
#print axioms choose_s_version_simulates_layout

theorem s_select_new_version_slot {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool) (d : Nat) :
    chooseSVersion (records.length+1) width desired
      (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath (List.replicate records.length false)) := by
  rw [choose_s_version_simulates_layout _ _ _ _ _ (phase_at_good d), choose_new_version_slot]
  rfl

theorem s_select_partial_next {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (pref remaining : List Bool) (hw : (pref ++ remaining).length = width) (d : Nat) :
    chooseSVersion (records.length+1) width (pref ++ remaining)
      (layoutTerm (partialVersionLayout pref records) (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath (List.replicate records.length false ++ true :: List.replicate pref.length true)) := by
  rw [choose_s_version_simulates_layout _ _ _ _ _ (phase_at_good d), choose_partial_version_next records pref remaining hw]
  rfl

theorem s_select_partial_flag {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (pref remaining : List Bool) (hw : (pref ++ true :: remaining).length = width) (d : Nat) :
    chooseSVersion (records.length+1) width (pref ++ true :: remaining)
      (layoutTerm (partialVersionLayout (pref ++ [false]) records) (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath (List.replicate records.length false ++ true :: (List.replicate pref.length true ++ [false]))) := by
  rw [choose_s_version_simulates_layout _ _ _ _ _ (phase_at_good d), choose_partial_version_flag records pref remaining hw]
  rfl

#print axioms s_select_new_version_slot
#print axioms s_select_partial_next
#print axioms s_select_partial_flag

def subLayout : Layout → List Bool → Option Layout
  | shape, [] => some shape
  | .unopened, _ :: _ => none
  | .opened l _, false :: path => subLayout l path
  | .opened _ r, true :: path => subLayout r path

def termAt : Term → List Bool → Option Term
  | term, [] => some term
  | .app l _, false :: path => termAt l path
  | .app _ r, true :: path => termAt r path
  | _, _ :: _ => none

def advancePhase : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n+1, p => advancePhase n (nextPhase p)

theorem layout_subterm_at_physical_path (path : List Bool) :
    ∀ shape result p, goodPhase p → subLayout shape path = some result →
      termAt (layoutTerm shape p.1 p.2) (physicalPath path) =
        some (layoutTerm result (advancePhase path.length p).1 (advancePhase path.length p).2) := by
  induction path with
  | nil =>
    intro shape result p hp h
    simp [subLayout] at h
    subst result
    cases ht : layoutTerm shape p.1 p.2 <;> simp [physicalPath, termAt, advancePhase, ht]
  | cons side path ih =>
    intro shape result p hp h
    cases shape with
    | unopened => simp [subLayout] at h
    | opened l r =>
      have hchild := next_phase_good p hp
      cases side with
      | false =>
        have hl : subLayout l path = some result := by simpa [subLayout] using h
        simpa [layout_opened_phase l r p hp, physicalPath, termAt, frameTerm,
          advancePhase] using ih l result (nextPhase p) hchild hl
      | true =>
        have hr : subLayout r path = some result := by simpa [subLayout] using h
        simpa [layout_opened_phase l r p hp, physicalPath, termAt, frameTerm,
          advancePhase] using ih r result (nextPhase p) hchild hr

#print axioms layout_subterm_at_physical_path

theorem open_layout_targets_unopened (path : List Bool) :
    ∀ shape target, openLayoutAt shape path = some target → subLayout shape path = some .unopened := by
  induction path with
  | nil =>
    intro shape target h
    cases shape with
    | unopened => rfl
    | opened l r => simp [openLayoutAt] at h
  | cons side path ih =>
    intro shape target h
    cases shape with
    | unopened => simp [openLayoutAt] at h
    | opened l r =>
      cases side with
      | false =>
        cases hx : openLayoutAt l path with
        | none => simp [openLayoutAt, hx] at h
        | some next =>
          have hh := ih l next hx
          simpa [subLayout] using hh
      | true =>
        cases hx : openLayoutAt r path with
        | none => simp [openLayoutAt, hx] at h
        | some next =>
          have hh := ih r next hx
          simpa [subLayout] using hh

#print axioms open_layout_targets_unopened

theorem advance_phase_good (n : Nat) (p : Nat × Nat) (hp : goodPhase p) : goodPhase (advancePhase n p) := by
  induction n generalizing p with
  | zero => exact hp
  | succ n ih => exact ih (nextPhase p) (next_phase_good p hp)

theorem selected_slot_is_generator (shape target : Layout) (path : List Bool) (p : Nat × Nat)
    (hp : goodPhase p) (hopen : openLayoutAt shape path = some target) :
    let q := advancePhase path.length p
    goodPhase q ∧
      termAt (layoutTerm shape p.1 p.2) (physicalPath path) = some (generator q.1 q.2) := by
  constructor
  · exact advance_phase_good path.length p hp
  · have hslot := open_layout_targets_unopened path shape target hopen
    have hterm := layout_subterm_at_physical_path path shape .unopened p hp hslot
    exact hterm

#print axioms advance_phase_good
#print axioms selected_slot_is_generator

theorem open_new_version_layout {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) :
    openLayoutAt (versionLayout records) (List.replicate records.length false) =
      some (partialVersionLayout [] records) := by
  induction records with
  | nil => rfl
  | cons entry rest ih => simp [versionLayout, partialVersionLayout, openLayoutAt, List.replicate_succ, ih]

theorem open_next_field_layout {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (pref : List Bool) :
    openLayoutAt (partialVersionLayout pref records)
      (List.replicate records.length false ++ true :: List.replicate pref.length true) =
      some (partialVersionLayout (pref ++ [false]) records) := by
  induction records with
  | nil => simp [partialVersionLayout, openLayoutAt, partial_field_open]
  | cons entry rest ih =>
    simp [partialVersionLayout, openLayoutAt, List.replicate_succ, ih]

theorem open_needed_flag_layout {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (pref : List Bool) :
    openLayoutAt (partialVersionLayout (pref ++ [false]) records)
      (List.replicate records.length false ++ true :: (List.replicate pref.length true ++ [false])) =
      some (partialVersionLayout (pref ++ [true]) records) := by
  induction records with
  | nil => simp [partialVersionLayout, openLayoutAt, partial_flag_open]
  | cons entry rest ih =>
    simp [partialVersionLayout, openLayoutAt, List.replicate_succ, ih]

theorem open_version_commit_layout {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    openLayoutAt (partialVersionLayout entry.val records)
      (List.replicate records.length false ++ true :: List.replicate entry.val.length true) =
      some (versionLayout (records ++ [entry])) := by
  induction records with
  | nil => simp [partialVersionLayout, versionLayout, openLayoutAt, partial_commit_open]
  | cons old rest ih =>
    simp [partialVersionLayout, versionLayout, openLayoutAt, List.replicate_succ, ih]

#print axioms open_new_version_layout
#print axioms open_next_field_layout
#print axioms open_needed_flag_layout
#print axioms open_version_commit_layout

theorem s_selected_open_certificate (shape target : Layout) (path : List Bool) (d fuel width : Nat)
    (desired : List Bool)
    (hchoose : chooseSVersion fuel width desired (layoutTerm shape (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath path))
    (hopen : openLayoutAt shape path = some target) :
    ∃ q, chooseSVersion fuel width desired (layoutTerm shape (phaseAt d).1 (phaseAt d).2) = some (physicalPath path) ∧
      goodPhase q ∧
      termAt (layoutTerm shape (phaseAt d).1 (phaseAt d).2) (physicalPath path) = some (generator q.1 q.2) ∧
      ShortSteps (layoutTerm shape (phaseAt d).1 (phaseAt d).2)
        (layoutTerm target (phaseAt d).1 (phaseAt d).2) := by
  have hp := phase_at_good d
  have hslot := selected_slot_is_generator shape target path (phaseAt d) hp hopen
  refine ⟨advancePhase path.length (phaseAt d), hchoose, hslot.1, hslot.2, ?_⟩
  exact selected_layout_opening_short path shape target (phaseAt d).1 (phaseAt d).2 hp.1 hp.2 hopen

theorem certify_new_version_slot {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool) (d : Nat) :
    ∃ q, chooseSVersion (records.length+1) width desired
        (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2) = some (physicalPath (List.replicate records.length false)) ∧
      goodPhase q ∧
      termAt (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2)
        (physicalPath (List.replicate records.length false)) = some (generator q.1 q.2) ∧
      ShortSteps (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2)
        (layoutTerm (partialVersionLayout [] records) (phaseAt d).1 (phaseAt d).2) := by
  exact s_selected_open_certificate (versionLayout records) (partialVersionLayout [] records)
    (List.replicate records.length false) d (records.length+1) width desired
    (s_select_new_version_slot records desired d) (open_new_version_layout records)

#print axioms s_selected_open_certificate
#print axioms certify_new_version_slot

theorem good_generator_first_directed (m n : Nat) (hn : 2 ≤ n) :
    ∃ next, nextOpeningAddress (generator m n) = some [false] ∧
      DirectedStep [false] (generator m n) next := by
  cases m with
  | zero =>
    refine ⟨generator (n+1) (n+1), opening_selector_zero_phase n, ?_⟩
    exact DirectedStep.left (DirectedStep.root B B (numeral n))
  | succ m =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases n with
      | zero => exfalso; omega
      | succ n =>
        refine ⟨S ⋅ numeral (n+2) ⋅ (numeral m ⋅ numeral (n+2)) ⋅ S,
          opening_selector_positive_phase m n, ?_⟩
        exact DirectedStep.left (DirectedStep.root S (numeral m) (numeral (n+2)))

#print axioms good_generator_first_directed

theorem directed_step_at_subterm (path : List Bool) :
    ∀ root focus relpath next, termAt root path = some focus → DirectedStep relpath focus next →
      ∃ root', DirectedStep (path ++ relpath) root root' := by
  induction path with
  | nil =>
    intro root focus relpath next hat hd
    cases root with
    | s => simp [termAt] at hat; subst focus; exact ⟨next,hd⟩
    | var x => simp [termAt] at hat; subst focus; exact ⟨next,hd⟩
    | app l r => simp [termAt] at hat; subst focus; exact ⟨next,hd⟩
  | cons side path ih =>
    intro root focus relpath next hat hd
    cases root with
    | s => simp [termAt] at hat
    | var x => simp [termAt] at hat
    | app l r =>
      cases side with
      | false =>
        have hchild : termAt l path = some focus := by simpa [termAt] using hat
        obtain ⟨out,hout⟩ := ih l focus relpath next hchild hd
        exact ⟨out ⋅ r, DirectedStep.left hout⟩
      | true =>
        have hchild : termAt r path = some focus := by simpa [termAt] using hat
        obtain ⟨out,hout⟩ := ih r focus relpath next hchild hd
        exact ⟨l ⋅ out, DirectedStep.right hout⟩

#print axioms directed_step_at_subterm

theorem s_selected_open_first_step (shape target : Layout) (path : List Bool) (d fuel width : Nat)
    (desired : List Bool)
    (hchoose : chooseSVersion fuel width desired (layoutTerm shape (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath path))
    (hopen : openLayoutAt shape path = some target) :
    ∃ (q : Nat × Nat) (root' : Term),
      termAt (layoutTerm shape (phaseAt d).1 (phaseAt d).2) (physicalPath path) = some (generator q.1 q.2) ∧
      nextOpeningAddress (generator q.1 q.2) = some [false] ∧
      DirectedStep (physicalPath path ++ [false]) (layoutTerm shape (phaseAt d).1 (phaseAt d).2) root' := by
  obtain ⟨q,_,hgood,hat,_⟩ := s_selected_open_certificate shape target path d fuel width desired hchoose hopen
  obtain ⟨focusNext,hselect,hstep⟩ := good_generator_first_directed q.1 q.2 hgood.1
  obtain ⟨root',hroot⟩ := directed_step_at_subterm (physicalPath path)
    (layoutTerm shape (phaseAt d).1 (phaseAt d).2) (generator q.1 q.2) [false] focusNext hat hstep
  exact ⟨q,root',hat,hselect,hroot⟩

#print axioms s_selected_open_first_step

theorem parse_frame_sound (term l r j : Term)
    (h : parseFrame term = some (l,r,j)) : term = frameTerm l r j := by
  unfold parseFrame at h
  split at h <;> simp_all [frameTerm, S]

#print axioms parse_frame_sound

theorem matched_layout_flag (shape : Layout) (term : Term) (h : layoutMatches shape term) :
    flagValue term = layoutIsOpen shape := by
  cases shape with
  | unopened => simpa [layoutMatches, flagValue, layoutIsOpen] using h
  | opened l r =>
    obtain ⟨tl,tr,j,hp,_,_⟩ := h
    simp [flagValue,layoutIsOpen,hp]

theorem matched_fields_read (width : Nat) :
    ∀ shape term, layoutMatches shape term → readFields width term = readLayoutFields width shape := by
  induction width with
  | zero =>
    intro shape term h
    cases shape with
    | unopened => simp [readFields, readLayoutFields, matched_layout_flag .unopened term h, layoutIsOpen]
    | opened l r => simp [readFields, readLayoutFields, matched_layout_flag (.opened l r) term h, layoutIsOpen]
  | succ width ih =>
    intro shape term h
    cases shape with
    | unopened =>
      have hp : parseFrame term = none := h
      simp [readFields, readLayoutFields, hp]
    | opened l r =>
      obtain ⟨tl,tr,j,hp,hl,hr⟩ := h
      simp [readFields, readLayoutFields, hp, matched_layout_flag l tl hl, ih r tr hr]

theorem matched_fields_choice (desired : List Bool) :
    ∀ shape term, layoutMatches shape term →
      chooseSFields desired term = (chooseFields desired shape).map physicalPath := by
  induction desired with
  | nil =>
    intro shape term h
    cases shape with
    | unopened => simp [chooseSFields, chooseFields, matched_layout_flag .unopened term h, layoutIsOpen, physicalPath]
    | opened l r => simp [chooseSFields, chooseFields, matched_layout_flag (.opened l r) term h, layoutIsOpen]
  | cons b bs ih =>
    intro shape term h
    cases shape with
    | unopened =>
      have hp : parseFrame term = none := h
      simp [chooseSFields, chooseFields, hp, physicalPath]
    | opened l r =>
      obtain ⟨tl,tr,j,hp,hl,hr⟩ := h
      cases b <;> cases hv : layoutIsOpen l <;>
        simp [chooseSFields, chooseFields, hp, matched_layout_flag l tl hl, ih r tr hr,
          physicalPath, Option.map_map, Function.comp_def, hv]

#print axioms matched_layout_flag
#print axioms matched_fields_read
#print axioms matched_fields_choice

theorem matched_version_choice (fuel width : Nat) (desired : List Bool) :
    ∀ shape term, layoutMatches shape term →
      chooseSVersion fuel width desired term = (chooseVersion fuel width desired shape).map physicalPath := by
  induction fuel with
  | zero => intro shape term h; rfl
  | succ fuel ih =>
    intro shape term h
    cases shape with
    | unopened =>
      have hp : parseFrame term = none := h
      simp [chooseSVersion, chooseVersion, hp, physicalPath]
    | opened l r =>
      obtain ⟨tl,tr,j,hp,hl,hr⟩ := h
      simp [chooseSVersion, chooseVersion, hp, matched_fields_read width r tr hr,
        matched_fields_choice desired r tr hr, ih l tl hl, Option.map_map, Function.comp_def]
      cases hx : readLayoutFields width r <;> simp [physicalPath, Option.map_map, Function.comp_def]

#print axioms matched_version_choice

theorem term_at_nil (term : Term) : termAt term [] = some term := by
  cases term <;> rfl

theorem closed_slot_step_preserves_layout (path : List Bool) :
    ∀ shape term old new relpath,
      layoutMatches shape term → subLayout shape path = some .unopened →
      termAt term (physicalPath path) = some old → DirectedStep relpath old new →
      parseFrame new = none →
      ∃ out, DirectedStep (physicalPath path ++ relpath) term out ∧ layoutMatches shape out ∧
        termAt out (physicalPath path) = some new := by
  induction path with
  | nil =>
    intro shape term old new relpath hmatch hslot hat hd hclosed
    simp [subLayout] at hslot
    subst shape
    simp [physicalPath, term_at_nil] at hat
    subst old
    exact ⟨new,hd,hclosed,term_at_nil new⟩
  | cons side path ih =>
    intro shape term old new relpath hmatch hslot hat hd hclosed
    cases shape with
    | unopened => simp [subLayout] at hslot
    | opened l r =>
      obtain ⟨tl,tr,j,hp,hl,hr⟩ := hmatch
      have hterm := parse_frame_sound term tl tr j hp
      subst term
      cases side with
      | false =>
        have hlslot : subLayout l path = some .unopened := by simpa [subLayout] using hslot
        have hlat : termAt tl (physicalPath path) = some old := by simpa [physicalPath,termAt,frameTerm] using hat
        obtain ⟨out,hout,houtmatch,houtat⟩ := ih l tl old new relpath hl hlslot hlat hd hclosed
        refine ⟨frameTerm out tr j, ?_, ?_, ?_⟩
        · simpa [physicalPath, List.append_assoc] using directed_frame_left hout tr j
        · exact ⟨out,tr,j,parse_frame out tr j,houtmatch,hr⟩
        · simpa [physicalPath,termAt,frameTerm] using houtat
      | true =>
        have hrslot : subLayout r path = some .unopened := by simpa [subLayout] using hslot
        have hrat : termAt tr (physicalPath path) = some old := by simpa [physicalPath,termAt,frameTerm] using hat
        obtain ⟨out,hout,houtmatch,houtat⟩ := ih r tr old new relpath hr hrslot hrat hd hclosed
        refine ⟨frameTerm tl out j, ?_, ?_, ?_⟩
        · simpa [physicalPath, List.append_assoc] using directed_frame_right hout tl j
        · exact ⟨tl,out,j,parse_frame tl out j,hl,houtmatch⟩
        · simpa [physicalPath,termAt,frameTerm] using houtat

#print axioms term_at_nil
#print axioms closed_slot_step_preserves_layout

theorem restarted_selector_preserves_target (shape : Layout) (term old new : Term)
    (path relpath : List Bool) (fuel width : Nat) (desired : List Bool)
    (hmatch : layoutMatches shape term) (hslot : subLayout shape path = some .unopened)
    (hat : termAt term (physicalPath path) = some old) (hstep : DirectedStep relpath old new)
    (hclosed : parseFrame new = none)
    (hchoose : chooseSVersion fuel width desired term = some (physicalPath path)) :
    ∃ out, DirectedStep (physicalPath path ++ relpath) term out ∧
      termAt out (physicalPath path) = some new ∧
      chooseSVersion fuel width desired out = some (physicalPath path) ∧
      layoutMatches shape out := by
  obtain ⟨out,hout,houtmatch,houtat⟩ :=
    closed_slot_step_preserves_layout path shape term old new relpath hmatch hslot hat hstep hclosed
  refine ⟨out,hout,houtat,?_,houtmatch⟩
  calc
    chooseSVersion fuel width desired out = (chooseVersion fuel width desired shape).map physicalPath :=
      matched_version_choice fuel width desired shape out houtmatch
    _ = chooseSVersion fuel width desired term :=
      (matched_version_choice fuel width desired shape term hmatch).symm
    _ = some (physicalPath path) := hchoose

#print axioms restarted_selector_preserves_target

theorem opened_slot_step_updates_layout (path : List Bool) :
    ∀ shape term old new relpath,
      layoutMatches shape term → subLayout shape path = some .unopened →
      termAt term (physicalPath path) = some old → DirectedStep relpath old new →
      layoutMatches (.opened .unopened .unopened) new →
      ∃ target out, openLayoutAt shape path = some target ∧
        DirectedStep (physicalPath path ++ relpath) term out ∧ layoutMatches target out ∧
        termAt out (physicalPath path) = some new := by
  induction path with
  | nil =>
    intro shape term old new relpath hmatch hslot hat hd hnew
    simp [subLayout] at hslot
    subst shape
    simp [physicalPath, term_at_nil] at hat
    subst old
    exact ⟨.opened .unopened .unopened,new,rfl,hd,hnew,term_at_nil new⟩
  | cons side path ih =>
    intro shape term old new relpath hmatch hslot hat hd hnew
    cases shape with
    | unopened => simp [subLayout] at hslot
    | opened l r =>
      obtain ⟨tl,tr,j,hp,hl,hr⟩ := hmatch
      have hterm := parse_frame_sound term tl tr j hp
      subst term
      cases side with
      | false =>
        have hlslot : subLayout l path = some .unopened := by simpa [subLayout] using hslot
        have hlat : termAt tl (physicalPath path) = some old := by simpa [physicalPath,termAt,frameTerm] using hat
        obtain ⟨next,out,hopen,hout,houtmatch,houtat⟩ := ih l tl old new relpath hl hlslot hlat hd hnew
        refine ⟨.opened next r,frameTerm out tr j,?_,?_,?_,?_⟩
        · simp [openLayoutAt,hopen]
        · simpa [physicalPath,List.append_assoc] using directed_frame_left hout tr j
        · exact ⟨out,tr,j,parse_frame out tr j,houtmatch,hr⟩
        · simpa [physicalPath,termAt,frameTerm] using houtat
      | true =>
        have hrslot : subLayout r path = some .unopened := by simpa [subLayout] using hslot
        have hrat : termAt tr (physicalPath path) = some old := by simpa [physicalPath,termAt,frameTerm] using hat
        obtain ⟨next,out,hopen,hout,houtmatch,houtat⟩ := ih r tr old new relpath hr hrslot hrat hd hnew
        refine ⟨.opened l next,frameTerm tl out j,?_,?_,?_,?_⟩
        · simp [openLayoutAt,hopen]
        · simpa [physicalPath,List.append_assoc] using directed_frame_right hout tl j
        · exact ⟨tl,out,j,parse_frame tl out j,hl,houtmatch⟩
        · simpa [physicalPath,termAt,frameTerm] using houtat

#print axioms opened_slot_step_updates_layout

theorem generated_frame_has_open_layout (m n : Nat) (junk : Term) :
    layoutMatches (.opened .unopened .unopened)
      (frameTerm (generator m n) (generator m n) junk) := by
  exact ⟨generator m n,generator m n,junk,parse_frame _ _ _,
    parse_generator_closed m n,parse_generator_closed m n⟩

#print axioms generated_frame_has_open_layout

inductive ClosedOpeningTrace : Nat → Term → Term → Prop where
  | finish {a b : Term} : ChosenStep a b → layoutMatches (.opened .unopened .unopened) b →
      ClosedOpeningTrace 1 a b
  | more {n : Nat} {a b c : Term} : ChosenStep a b → parseFrame b = none →
      ClosedOpeningTrace n b c → ClosedOpeningTrace (n+1) a c

theorem generic_closed_opening_trace (m n : Term) :
    ClosedOpeningTrace 6 ((B ⋅ m) ⋅ (B ⋅ (B ⋅ n)) ⋅ S)
      (S ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S) ⋅
       (S ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S) ⋅
        ((n ⋅ S) ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S)))) := by
  let n1 := B ⋅ n
  let n2 := B ⋅ n1
  let g := m ⋅ n2 ⋅ S
  let q := m ⋅ n2
  have ⟨c1,c2,c3,c4,c5,c6,_⟩ := opening_selector_six_stages m n
  have ⟨_,u1,u2,u3,u4,u5⟩ := intermediate_frames_closed m n
  have h1 : ChosenStep ((B ⋅ m) ⋅ n2 ⋅ S) (S ⋅ n2 ⋅ q ⋅ S) :=
    ⟨[false],c1,DirectedStep.left (DirectedStep.root S m n2)⟩
  have h2 : ChosenStep (S ⋅ n2 ⋅ q ⋅ S) ((n2 ⋅ S) ⋅ g) :=
    ⟨[],c2,DirectedStep.root n2 q S⟩
  have h3 : ChosenStep ((n2 ⋅ S) ⋅ g) ((B ⋅ (n1 ⋅ S)) ⋅ g) :=
    ⟨[false],c3,DirectedStep.left (DirectedStep.root S n1 S)⟩
  have h4 : ChosenStep ((B ⋅ (n1 ⋅ S)) ⋅ g) (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) :=
    ⟨[],c4,DirectedStep.root S (n1 ⋅ S) g⟩
  have h5 : ChosenStep (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) (S ⋅ g ⋅ ((B ⋅ (n ⋅ S)) ⋅ g)) :=
    ⟨[true,false],c5,DirectedStep.right (DirectedStep.left (DirectedStep.root S n S))⟩
  have h6 : ChosenStep (S ⋅ g ⋅ ((B ⋅ (n ⋅ S)) ⋅ g))
      (S ⋅ g ⋅ (S ⋅ g ⋅ ((n ⋅ S) ⋅ g))) :=
    ⟨[true],c6,DirectedStep.right (DirectedStep.root S (n ⋅ S) g)⟩
  have hg : parseFrame g = none := by simp [g,parseFrame,S]
  have hf : layoutMatches (.opened .unopened .unopened) (S ⋅ g ⋅ (S ⋅ g ⋅ ((n ⋅ S) ⋅ g))) :=
    ⟨g,g,(n ⋅ S) ⋅ g,parse_frame _ _ _,hg,hg⟩
  exact ClosedOpeningTrace.more h1 u1 (ClosedOpeningTrace.more h2 u2 (ClosedOpeningTrace.more h3 u3
    (ClosedOpeningTrace.more h4 u4 (ClosedOpeningTrace.more h5 u5 (ClosedOpeningTrace.finish h6 hf)))))

theorem positive_closed_opening_trace (m n : Nat) :
    ClosedOpeningTrace 6 (generator (m+1) (n+2))
      (frameTerm (generator m (n+2)) (generator m (n+2))
        ((numeral n ⋅ S) ⋅ generator m (n+2))) := by
  exact generic_closed_opening_trace (numeral m) (numeral n)

theorem zero_closed_opening_trace (n : Nat) :
    ClosedOpeningTrace 7 (generator 0 (n+2))
      (frameTerm (generator (n+2) (n+3)) (generator (n+2) (n+3))
        ((numeral (n+1) ⋅ S) ⋅ generator (n+2) (n+3))) := by
  have first : ChosenStep (generator 0 (n+2)) (generator (n+3) (n+3)) :=
    ⟨[false], opening_selector_zero_phase (n+2),
      DirectedStep.left (DirectedStep.root B B (numeral (n+2)))⟩
  exact ClosedOpeningTrace.more first (parse_generator_closed (n+3) (n+3))
    (positive_closed_opening_trace (n+2) (n+1))

#print axioms generic_closed_opening_trace
#print axioms positive_closed_opening_trace
#print axioms zero_closed_opening_trace

def RestartedNativeStep (path : List Bool) (fuel width : Nat) (desired : List Bool) (a b : Term) : Prop :=
  chooseSVersion fuel width desired a = some (physicalPath path) ∧
    ∃ focus relpath, termAt a (physicalPath path) = some focus ∧
      nextOpeningAddress focus = some relpath ∧ DirectedStep (physicalPath path ++ relpath) a b

inductive RestartedNativeTrace (path : List Bool) (fuel width : Nat) (desired : List Bool) : Nat → Term → Term → Prop where
  | zero (a : Term) : RestartedNativeTrace path fuel width desired 0 a a
  | next {n : Nat} {a b c : Term} : RestartedNativeStep path fuel width desired a b →
      RestartedNativeTrace path fuel width desired n b c → RestartedNativeTrace path fuel width desired (n+1) a c

theorem lift_closed_opening_to_restarted_selector {n : Nat} {old final : Term}
    (trace : ClosedOpeningTrace n old final) :
    ∀ shape term path fuel width desired,
      layoutMatches shape term → subLayout shape path = some .unopened →
      termAt term (physicalPath path) = some old →
      chooseSVersion fuel width desired term = some (physicalPath path) →
      ∃ target out, openLayoutAt shape path = some target ∧ layoutMatches target out ∧
        termAt out (physicalPath path) = some final ∧
        RestartedNativeTrace path fuel width desired n term out := by
  induction trace with
  | @finish a b hchosen hopen =>
    intro shape term path fuel width desired hmatch hslot hat hchoose
    obtain ⟨relpath,hlocal,hdir⟩ := hchosen
    obtain ⟨target,out,hopenLayout,hout,hmatchout,hfinal⟩ :=
      opened_slot_step_updates_layout path shape term a b relpath hmatch hslot hat hdir hopen
    have hglobal : RestartedNativeStep path fuel width desired term out :=
      ⟨hchoose,a,relpath,hat,hlocal,hout⟩
    exact ⟨target,out,hopenLayout,hmatchout,hfinal,
      RestartedNativeTrace.next hglobal (RestartedNativeTrace.zero out)⟩
  | @more n a b c hchosen hclosed rest ih =>
    intro shape term path fuel width desired hmatch hslot hat hchoose
    obtain ⟨relpath,hlocal,hdir⟩ := hchosen
    obtain ⟨middle,hmiddle,hatMiddle,hchooseMiddle,hmatchMiddle⟩ :=
      restarted_selector_preserves_target shape term a b path relpath fuel width desired
        hmatch hslot hat hdir hclosed hchoose
    obtain ⟨target,out,hopenLayout,hmatchout,hfinal,htrace⟩ :=
      ih shape middle path fuel width desired hmatchMiddle hslot hatMiddle hchooseMiddle
    have hglobal : RestartedNativeStep path fuel width desired term middle :=
      ⟨hchoose,a,relpath,hat,hlocal,hmiddle⟩
    exact ⟨target,out,hopenLayout,hmatchout,hfinal,RestartedNativeTrace.next hglobal htrace⟩

#print axioms lift_closed_opening_to_restarted_selector

theorem restarted_selected_generator_opens (shape : Layout) (term : Term) (path : List Bool)
    (fuel width : Nat) (desired : List Bool) (m n : Nat)
    (hn : 2 ≤ n) (hmatch : layoutMatches shape term)
    (hslot : subLayout shape path = some .unopened)
    (hat : termAt term (physicalPath path) = some (generator m n))
    (hchoose : chooseSVersion fuel width desired term = some (physicalPath path)) :
    ∃ k target out, (k=6 ∨ k=7) ∧ openLayoutAt shape path = some target ∧
      layoutMatches target out ∧ RestartedNativeTrace path fuel width desired k term out := by
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero =>
        obtain ⟨target,out,hopen,hout,_,htrace⟩ :=
          lift_closed_opening_to_restarted_selector (zero_closed_opening_trace n)
            shape term path fuel width desired hmatch hslot hat hchoose
        exact ⟨7,target,out,Or.inr rfl,hopen,hout,htrace⟩
      | succ m =>
        obtain ⟨target,out,hopen,hout,_,htrace⟩ :=
          lift_closed_opening_to_restarted_selector (positive_closed_opening_trace m n)
            shape term path fuel width desired hmatch hslot hat hchoose
        exact ⟨6,target,out,Or.inl rfl,hopen,hout,htrace⟩

#print axioms restarted_selected_generator_opens

def replaceTermAt : Term → List Bool → Term → Option Term
  | _, [], replacement => some replacement
  | .app l r, false :: path, replacement => (replaceTermAt l path replacement).map (fun next => next ⋅ r)
  | .app l r, true :: path, replacement => (replaceTermAt r path replacement).map (fun next => l ⋅ next)
  | _, _ :: _, _ => none

theorem replace_at_nil (term replacement : Term) : replaceTermAt term [] replacement = some replacement := by
  cases term <;> rfl

theorem directed_step_replaces_subterm (path : List Bool) :
    ∀ root focus localPath next, termAt root path = some focus → DirectedStep localPath focus next →
      ∃ out, replaceTermAt root path next = some out ∧ DirectedStep (path ++ localPath) root out := by
  induction path with
  | nil =>
    intro root focus localPath next hat hd
    rw [term_at_nil] at hat
    simp at hat
    subst focus
    exact ⟨next,replace_at_nil root next,hd⟩
  | cons side path ih =>
    intro root focus localPath next hat hd
    cases root with
    | s => simp [termAt] at hat
    | var x => simp [termAt] at hat
    | app l r =>
      cases side with
      | false =>
        have hchild : termAt l path = some focus := by simpa [termAt] using hat
        obtain ⟨out,hreplace,hout⟩ := ih l focus localPath next hchild hd
        refine ⟨out ⋅ r, ?_, DirectedStep.left hout⟩
        simp [replaceTermAt,hreplace]
      | true =>
        have hchild : termAt r path = some focus := by simpa [termAt] using hat
        obtain ⟨out,hreplace,hout⟩ := ih r focus localPath next hchild hd
        refine ⟨l ⋅ out, ?_, DirectedStep.right hout⟩
        simp [replaceTermAt,hreplace]

#print axioms directed_step_replaces_subterm

theorem replace_same_path_overwrites (path : List Bool) :
    ∀ root first middle second,
      replaceTermAt root path first = some middle →
      replaceTermAt middle path second = replaceTermAt root path second := by
  induction path with
  | nil =>
    intro root first middle second h
    rw [replace_at_nil] at h
    simp at h
    subst middle
    rw [replace_at_nil,replace_at_nil]
  | cons side path ih =>
    intro root first middle second h
    cases root with
    | s => simp [replaceTermAt] at h
    | var x => simp [replaceTermAt] at h
    | app l r =>
      cases side with
      | false =>
        cases hx : replaceTermAt l path first with
        | none => simp [replaceTermAt,hx] at h
        | some child =>
          have hm : child ⋅ r = middle := by simpa [replaceTermAt,hx] using h
          subst middle
          simp only [replaceTermAt]
          rw [ih l first child second hx]
      | true =>
        cases hx : replaceTermAt r path first with
        | none => simp [replaceTermAt,hx] at h
        | some child =>
          have hm : l ⋅ child = middle := by simpa [replaceTermAt,hx] using h
          subst middle
          simp only [replaceTermAt]
          rw [ih r first child second hx]

#print axioms replace_same_path_overwrites

theorem lift_opening_preserves_outer_context {n : Nat} {old final : Term}
    (trace : ClosedOpeningTrace n old final) :
    ∀ shape term path fuel width desired,
      layoutMatches shape term → subLayout shape path = some .unopened →
      termAt term (physicalPath path) = some old →
      chooseSVersion fuel width desired term = some (physicalPath path) →
      ∃ target out, openLayoutAt shape path = some target ∧ layoutMatches target out ∧
        termAt out (physicalPath path) = some final ∧
        replaceTermAt term (physicalPath path) final = some out ∧
        RestartedNativeTrace path fuel width desired n term out := by
  induction trace with
  | @finish a b hchosen hopen =>
    intro shape term path fuel width desired hmatch hslot hat hchoose
    obtain ⟨relpath,hlocal,hdir⟩ := hchosen
    obtain ⟨target,out,hopenLayout,hout,hmatchout,hfinal⟩ :=
      opened_slot_step_updates_layout path shape term a b relpath hmatch hslot hat hdir hopen
    obtain ⟨out',hreplace,hout'⟩ := directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
    have heq : out = out' := directed_step_unique hout out' hout'
    subst out'
    have hglobal : RestartedNativeStep path fuel width desired term out :=
      ⟨hchoose,a,relpath,hat,hlocal,hout⟩
    exact ⟨target,out,hopenLayout,hmatchout,hfinal,hreplace,
      RestartedNativeTrace.next hglobal (RestartedNativeTrace.zero out)⟩
  | @more n a b c hchosen hclosed rest ih =>
    intro shape term path fuel width desired hmatch hslot hat hchoose
    obtain ⟨relpath,hlocal,hdir⟩ := hchosen
    obtain ⟨middle,hmiddle,hatMiddle,hchooseMiddle,hmatchMiddle⟩ :=
      restarted_selector_preserves_target shape term a b path relpath fuel width desired
        hmatch hslot hat hdir hclosed hchoose
    obtain ⟨middle',hreplaceFirst,hmiddle'⟩ :=
      directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
    have heq : middle = middle' := directed_step_unique hmiddle middle' hmiddle'
    subst middle'
    obtain ⟨target,out,hopenLayout,hmatchout,hfinal,hreplaceRest,htrace⟩ :=
      ih shape middle path fuel width desired hmatchMiddle hslot hatMiddle hchooseMiddle
    have hreplace : replaceTermAt term (physicalPath path) c = some out := by
      rw [← replace_same_path_overwrites (physicalPath path) term b middle c hreplaceFirst]
      exact hreplaceRest
    have hglobal : RestartedNativeStep path fuel width desired term middle :=
      ⟨hchoose,a,relpath,hat,hlocal,hmiddle⟩
    exact ⟨target,out,hopenLayout,hmatchout,hfinal,hreplace,RestartedNativeTrace.next hglobal htrace⟩

#print axioms lift_opening_preserves_outer_context

theorem canonical_layout_replace (path : List Bool) :
    ∀ shape target p, goodPhase p → openLayoutAt shape path = some target →
      let q := advancePhase path.length p
      replaceTermAt (layoutTerm shape p.1 p.2) (physicalPath path)
        (layoutTerm (.opened .unopened .unopened) q.1 q.2) = some (layoutTerm target p.1 p.2) := by
  induction path with
  | nil =>
    intro shape target p hp hopen
    cases shape with
    | unopened =>
      simp [openLayoutAt] at hopen
      subst target
      simp [physicalPath,advancePhase,replace_at_nil]
    | opened l r => simp [openLayoutAt] at hopen
  | cons side path ih =>
    intro shape target p hp hopen
    cases shape with
    | unopened => simp [openLayoutAt] at hopen
    | opened l r =>
      have hnext := next_phase_good p hp
      cases side with
      | false =>
        cases hx : openLayoutAt l path with
        | none => simp [openLayoutAt,hx] at hopen
        | some next =>
          simp [openLayoutAt,hx] at hopen
          subst target
          have hchild := ih l next (nextPhase p) hnext hx
          simpa [layout_opened_phase, hp, physicalPath, replaceTermAt, frameTerm, advancePhase] using
            congrArg (Option.map (fun x => frameTerm x (layoutTerm r (nextPhase p).1 (nextPhase p).2) (phaseJunk p))) hchild
      | true =>
        cases hx : openLayoutAt r path with
        | none => simp [openLayoutAt,hx] at hopen
        | some next =>
          simp [openLayoutAt,hx] at hopen
          subst target
          have hchild := ih r next (nextPhase p) hnext hx
          simpa [layout_opened_phase, hp, physicalPath, replaceTermAt, frameTerm, advancePhase] using
            congrArg (Option.map (fun x => frameTerm (layoutTerm l (nextPhase p).1 (nextPhase p).2) x (phaseJunk p))) hchild

#print axioms canonical_layout_replace

theorem good_phase_opening_trace (p : Nat × Nat) (hp : goodPhase p) :
    ∃ k, (k=6 ∨ k=7) ∧ ClosedOpeningTrace k (phaseBase p)
      (layoutTerm (.opened .unopened .unopened) p.1 p.2) := by
  rcases p with ⟨m,n⟩
  have hn : 2 ≤ n := hp.1
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero => exact ⟨7,Or.inr rfl,zero_closed_opening_trace n⟩
      | succ m => exact ⟨6,Or.inl rfl,positive_closed_opening_trace m n⟩

#print axioms good_phase_opening_trace

theorem canonical_selected_opening_restarts (shape target : Layout) (path : List Bool)
    (d fuel width : Nat) (desired : List Bool)
    (hopen : openLayoutAt shape path = some target)
    (hchoose : chooseSVersion fuel width desired (layoutTerm shape (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath path)) :
    ∃ k, (k=6 ∨ k=7) ∧ RestartedNativeTrace path fuel width desired k
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
    lift_opening_preserves_outer_context htrace shape (layoutTerm shape p.1 p.2)
      path fuel width desired hmatch hslot hat hchoose
  have htarget : target' = target := by rw [hopen] at hopen'; exact (Option.some.inj hopen').symm
  subst target'
  have hcanonical := canonical_layout_replace path shape target p hp hopen
  have hout : out = layoutTerm target p.1 p.2 := by rw [hcanonical] at hreplace; exact (Option.some.inj hreplace).symm
  subst out
  exact ⟨k,hk,hglobal⟩

#print axioms canonical_selected_opening_restarts

inductive SelectedFieldTrace (desired : List Bool) : Nat → Layout → Layout → Prop where
  | done (s : Layout) : SelectedFieldTrace desired 0 s s
  | next {n : Nat} {a b c : Layout} {path : List Bool} :
      chooseFields desired a = some path → openLayoutAt a path = some b →
      SelectedFieldTrace desired n b c → SelectedFieldTrace desired (n+1) a c

theorem selected_fields_complete (remaining : List Bool) :
    ∀ pref, ∃ k,
      SelectedFieldTrace (pref ++ remaining) k (partialFieldsLayout pref) (fieldsLayout (pref ++ remaining)) ∧
      k ≤ 2*remaining.length+1 := by
  induction remaining with
  | nil =>
    intro pref
    refine ⟨1, ?_, by simp⟩
    simpa using SelectedFieldTrace.next (choose_after_correct_prefix pref [])
      (partial_commit_open pref) (SelectedFieldTrace.done (fieldsLayout pref))
  | cons bit rest ih =>
    intro pref
    cases bit with
    | false =>
      obtain ⟨k, hk, hbound⟩ := ih (pref ++ [false])
      have hs : SelectedFieldTrace (pref ++ false :: rest) k
          (partialFieldsLayout (pref ++ [false])) (fieldsLayout (pref ++ false :: rest)) := by
        simpa [List.append_assoc] using hk
      refine ⟨k+1, ?_, ?_⟩
      · exact SelectedFieldTrace.next (choose_after_correct_prefix pref (false :: rest))
          (partial_field_open pref) hs
      · simp only [List.length_cons]
        omega
    | true =>
      obtain ⟨k, hk, hbound⟩ := ih (pref ++ [true])
      have hs : SelectedFieldTrace (pref ++ true :: rest) k
          (partialFieldsLayout (pref ++ [true])) (fieldsLayout (pref ++ true :: rest)) := by
        simpa [List.append_assoc] using hk
      have hflag : SelectedFieldTrace (pref ++ true :: rest) (k+1)
          (partialFieldsLayout (pref ++ [false])) (fieldsLayout (pref ++ true :: rest)) :=
        SelectedFieldTrace.next (choose_incomplete_one_flag pref rest) (partial_flag_open pref) hs
      refine ⟨k+2, ?_, ?_⟩
      · exact SelectedFieldTrace.next (choose_after_correct_prefix pref (true :: rest))
          (partial_field_open pref) hflag
      · simp only [List.length_cons]
        omega

#print axioms selected_fields_complete

theorem partial_fields_uncommitted_for (pref remaining : List Bool) :
    readLayoutFields (pref ++ remaining).length (partialFieldsLayout pref) = none := by
  simpa [List.length_append] using read_layout_fields_incomplete pref remaining.length

inductive SafeFieldTrace (desired : List Bool) : Nat → Layout → Layout → Prop where
  | done (s : Layout) : SafeFieldTrace desired 0 s s
  | next {n : Nat} {a b c : Layout} {path : List Bool} :
      readLayoutFields desired.length a = none →
      chooseFields desired a = some path → openLayoutAt a path = some b →
      SafeFieldTrace desired n b c → SafeFieldTrace desired (n+1) a c

theorem safe_selected_fields_complete (remaining : List Bool) :
    ∀ pref, ∃ k,
      SafeFieldTrace (pref ++ remaining) k (partialFieldsLayout pref) (fieldsLayout (pref ++ remaining)) ∧
      k ≤ 2*remaining.length+1 := by
  induction remaining with
  | nil =>
    intro pref
    refine ⟨1, ?_, by simp⟩
    simpa using SafeFieldTrace.next (partial_fields_uncommitted_for pref [])
      (choose_after_correct_prefix pref []) (partial_commit_open pref) (SafeFieldTrace.done (fieldsLayout pref))
  | cons bit rest ih =>
    intro pref
    cases bit with
    | false =>
      obtain ⟨k, hk, hbound⟩ := ih (pref ++ [false])
      have hs : SafeFieldTrace (pref ++ false :: rest) k
          (partialFieldsLayout (pref ++ [false])) (fieldsLayout (pref ++ false :: rest)) := by
        simpa [List.append_assoc] using hk
      refine ⟨k+1, ?_, ?_⟩
      · exact SafeFieldTrace.next (partial_fields_uncommitted_for pref (false :: rest))
          (choose_after_correct_prefix pref (false :: rest)) (partial_field_open pref) hs
      · simp only [List.length_cons]; omega
    | true =>
      obtain ⟨k, hk, hbound⟩ := ih (pref ++ [true])
      have hs : SafeFieldTrace (pref ++ true :: rest) k
          (partialFieldsLayout (pref ++ [true])) (fieldsLayout (pref ++ true :: rest)) := by
        simpa [List.append_assoc] using hk
      have huncommitted : readLayoutFields (pref ++ true :: rest).length
          (partialFieldsLayout (pref ++ [false])) = none := by
        have hx := partial_fields_uncommitted_for (pref ++ [false]) rest
        simpa [List.length_append] using hx
      have hflag : SafeFieldTrace (pref ++ true :: rest) (k+1)
          (partialFieldsLayout (pref ++ [false])) (fieldsLayout (pref ++ true :: rest)) :=
        SafeFieldTrace.next huncommitted (choose_incomplete_one_flag pref rest) (partial_flag_open pref) hs
      refine ⟨k+2, ?_, ?_⟩
      · exact SafeFieldTrace.next (partial_fields_uncommitted_for pref (true :: rest))
          (choose_after_correct_prefix pref (true :: rest)) (partial_field_open pref) hflag
      · simp only [List.length_cons]; omega

#print axioms partial_fields_uncommitted_for
#print axioms safe_selected_fields_complete

def versionWithFields {width : Nat} :
    List {bits : List Bool // bits.length = width} → Layout → Layout
  | [], fields => .opened .unopened fields
  | entry :: rest, fields => .opened (versionWithFields rest fields) (fieldsLayout entry.val)

theorem choose_version_with_uncommitted_fields {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool)
    (fields : Layout) (hread : readLayoutFields width fields = none) :
    chooseVersion (records.length+1) width desired (versionWithFields records fields) =
      (chooseFields desired fields).map (fun p => List.replicate records.length false ++ true :: p) := by
  induction records with
  | nil => simp [versionWithFields,chooseVersion,hread]
  | cons entry rest ih =>
    have hentry : readLayoutFields width (fieldsLayout entry.val) = some entry.val := by
      simpa [entry.property] using read_layout_fields_complete entry.val
    simp [versionWithFields,chooseVersion,hentry,ih,List.replicate_succ,Option.map_map,Function.comp_def]

theorem open_version_with_fields {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (fields fields' : Layout) (path : List Bool) (h : openLayoutAt fields path = some fields') :
    openLayoutAt (versionWithFields records fields) (List.replicate records.length false ++ true :: path) =
      some (versionWithFields records fields') := by
  induction records with
  | nil => simp [versionWithFields,openLayoutAt,h]
  | cons entry rest ih => simp [versionWithFields,openLayoutAt,List.replicate_succ,ih]

theorem version_with_unopened_fields {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) :
    versionWithFields records .unopened = partialVersionLayout [] records := by
  induction records with
  | nil => rfl
  | cons entry rest ih => simp [versionWithFields,partialVersionLayout,ih]

theorem version_with_complete_fields {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    versionWithFields records (fieldsLayout entry.val) = versionLayout (records ++ [entry]) := by
  induction records with
  | nil => rfl
  | cons old rest ih => simp [versionWithFields,versionLayout,ih]

#print axioms choose_version_with_uncommitted_fields
#print axioms open_version_with_fields
#print axioms version_with_unopened_fields
#print axioms version_with_complete_fields

inductive SelectedVersionTrace (fuel width : Nat) (desired : List Bool) : Nat → Layout → Layout → Prop where
  | done (s : Layout) : SelectedVersionTrace fuel width desired 0 s s
  | next {n : Nat} {a b c : Layout} {path : List Bool} :
      chooseVersion fuel width desired a = some path → openLayoutAt a path = some b →
      SelectedVersionTrace fuel width desired n b c → SelectedVersionTrace fuel width desired (n+1) a c

theorem lift_safe_fields_to_version {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool)
    (hw : desired.length = width) {n : Nat} {a b : Layout}
    (trace : SafeFieldTrace desired n a b) :
    SelectedVersionTrace (records.length+1) width desired n
      (versionWithFields records a) (versionWithFields records b) := by
  induction trace with
  | done fields => exact SelectedVersionTrace.done _
  | @next n a b c path hread hchoose hopen rest ih =>
    have hread' : readLayoutFields width a = none := by simpa [hw] using hread
    have hchoice : chooseVersion (records.length+1) width desired (versionWithFields records a) =
        some (List.replicate records.length false ++ true :: path) := by
      rw [choose_version_with_uncommitted_fields records desired a hread', hchoose]
      rfl
    have hopen' := open_version_with_fields records a b path hopen
    exact SelectedVersionTrace.next hchoice hopen' ih

#print axioms lift_safe_fields_to_version

theorem selected_version_append_complete {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    ∃ k, SelectedVersionTrace (records.length+1) width entry.val k
        (versionLayout records) (versionLayout (records ++ [entry])) ∧
      1 ≤ k ∧ k ≤ 2*width+2 := by
  obtain ⟨k,hfields,hbound⟩ := safe_selected_fields_complete entry.val []
  have hfields' : SafeFieldTrace entry.val k .unopened (fieldsLayout entry.val) := by
    simpa [partialFieldsLayout] using hfields
  have hrest := lift_safe_fields_to_version records entry.val entry.property hfields'
  have hrest' : SelectedVersionTrace (records.length+1) width entry.val k
      (partialVersionLayout [] records) (versionLayout (records ++ [entry])) := by
    simpa [version_with_unopened_fields,version_with_complete_fields] using hrest
  refine ⟨k+1, ?_, by omega, ?_⟩
  · exact SelectedVersionTrace.next (choose_new_version_slot records entry.val)
      (open_new_version_layout records) hrest'
  · rw [entry.property] at hbound
    omega

#print axioms selected_version_append_complete

def AdaptiveNativeStep (fuel width : Nat) (desired : List Bool) (a b : Term) : Prop :=
  ∃ path, RestartedNativeStep path fuel width desired a b

inductive AdaptiveNativeTrace (fuel width : Nat) (desired : List Bool) : Nat → Term → Term → Prop where
  | zero (a : Term) : AdaptiveNativeTrace fuel width desired 0 a a
  | next {n : Nat} {a b c : Term} : AdaptiveNativeStep fuel width desired a b →
      AdaptiveNativeTrace fuel width desired n b c → AdaptiveNativeTrace fuel width desired (n+1) a c

theorem restarted_trace_is_adaptive {path : List Bool} {fuel width : Nat} {desired : List Bool}
    {n : Nat} {a b : Term} (h : RestartedNativeTrace path fuel width desired n a b) :
    AdaptiveNativeTrace fuel width desired n a b := by
  induction h with
  | zero x => exact AdaptiveNativeTrace.zero x
  | next hab _ ih => exact AdaptiveNativeTrace.next ⟨path,hab⟩ ih

theorem adaptive_trace_trans {fuel width : Nat} {desired : List Bool} {n m : Nat} {a b c : Term}
    (h : AdaptiveNativeTrace fuel width desired n a b) (k : AdaptiveNativeTrace fuel width desired m b c) :
    AdaptiveNativeTrace fuel width desired (n+m) a c := by
  induction h with
  | zero _ => simpa using k
  | @next n a b c hab _ ih =>
    have result := AdaptiveNativeTrace.next hab (ih k)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem selected_version_trace_native {fuel width : Nat} {desired : List Bool}
    {n : Nat} {a b : Layout} (trace : SelectedVersionTrace fuel width desired n a b) (d : Nat) :
    ∃ k, AdaptiveNativeTrace fuel width desired k
        (layoutTerm a (phaseAt d).1 (phaseAt d).2) (layoutTerm b (phaseAt d).1 (phaseAt d).2) ∧
      6*n ≤ k ∧ k ≤ 7*n := by
  induction trace with
  | done s => exact ⟨0,AdaptiveNativeTrace.zero _,by simp,by simp⟩
  | @next n a b c path hchoose hopen rest ih =>
    have hS : chooseSVersion fuel width desired (layoutTerm a (phaseAt d).1 (phaseAt d).2) =
        some (physicalPath path) := by
      rw [choose_s_version_simulates_layout fuel width desired a (phaseAt d) (phase_at_good d),hchoose]
      rfl
    obtain ⟨first,hfirst,hrun⟩ := canonical_selected_opening_restarts a b path d fuel width desired hopen hS
    obtain ⟨last,hlast,hlower,hupper⟩ := ih
    refine ⟨first+last, adaptive_trace_trans (restarted_trace_is_adaptive hrun) hlast, ?_, ?_⟩
    · cases hfirst <;> omega
    · cases hfirst <;> omega

#print axioms restarted_trace_is_adaptive
#print axioms adaptive_trace_trans
#print axioms selected_version_trace_native

theorem restarted_native_version_append {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (d : Nat) :
    ∃ k, AdaptiveNativeTrace (records.length+1) width entry.val k
        (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2)
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) ∧
      6 ≤ k ∧ k ≤ 7*(2*width+2) ∧
      scanVersions ((records ++ [entry]).length+1) width
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) none = some entry.val := by
  obtain ⟨n,htrace,hnlower,hnupper⟩ := selected_version_append_complete records entry
  obtain ⟨k,hreal,klower,kupper⟩ := selected_version_trace_native htrace d
  refine ⟨k,hreal,?_,?_,?_⟩
  · omega
  · omega
  · rw [actual_layout_chain_scan]
    exact newest_records_append records entry none

#print axioms restarted_native_version_append

def ContextAdaptiveStep (frames : List ProtectedFrame) (fuel width : Nat) (desired : List Bool)
    (a b : Term) : Prop :=
  ∃ path focus relpath,
    chooseSVersion fuel width desired a = some (physicalPath path) ∧
    termAt a (physicalPath path) = some focus ∧ nextOpeningAddress focus = some relpath ∧
    DirectedStep (contextPath frames ++ (physicalPath path ++ relpath))
      (wrapProtected frames a) (wrapProtected frames b)

inductive ContextAdaptiveTrace (frames : List ProtectedFrame) (fuel width : Nat) (desired : List Bool) :
    Nat → Term → Term → Prop where
  | zero (a : Term) : ContextAdaptiveTrace frames fuel width desired 0 a a
  | next {n : Nat} {a b c : Term} : ContextAdaptiveStep frames fuel width desired a b →
      ContextAdaptiveTrace frames fuel width desired n b c → ContextAdaptiveTrace frames fuel width desired (n+1) a c

theorem lift_adaptive_trace_to_context (frames : List ProtectedFrame)
    {fuel width : Nat} {desired : List Bool} {n : Nat} {a b : Term}
    (h : AdaptiveNativeTrace fuel width desired n a b) :
    ContextAdaptiveTrace frames fuel width desired n a b := by
  induction h with
  | zero x => exact ContextAdaptiveTrace.zero x
  | @next n a b c hstep _ ih =>
    obtain ⟨path,hchoose,focus,relpath,hat,hlocal,hdir⟩ := hstep
    have lifted := directed_protected_context frames hdir
    exact ContextAdaptiveTrace.next ⟨path,focus,relpath,hchoose,hat,hlocal,lifted⟩ ih

#print axioms lift_adaptive_trace_to_context

def chooseSVersionTree (width : Nat) (desired : List Bool) : Term → Option (List Bool)
  | .app (.app .s next) (.app (.app .s fields) _) =>
      match readFields width fields with
      | some _ => (chooseSVersionTree width desired next).map (fun p => [false,true] ++ p)
      | none => (chooseSFields desired fields).map (fun p => [true,false,true] ++ p)
  | _ => some []

theorem choose_tree_closed (width : Nat) (desired : List Bool) (term : Term)
    (h : parseFrame term = none) : chooseSVersionTree width desired term = some [] := by
  unfold parseFrame at h
  unfold chooseSVersionTree
  split <;> simp_all

theorem choose_tree_frame (width : Nat) (desired : List Bool) (next fields junk : Term) :
    chooseSVersionTree width desired (frameTerm next fields junk) =
      match readFields width fields with
      | some _ => (chooseSVersionTree width desired next).map (fun p => [false,true] ++ p)
      | none => (chooseSFields desired fields).map (fun p => [true,false,true] ++ p) := by
  rfl

#print axioms choose_tree_closed
#print axioms choose_tree_frame

theorem tree_selector_matches_fuel_committed {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool) :
    ∀ term, layoutMatches (versionLayout records) term →
      chooseSVersionTree width desired term = chooseSVersion (records.length+1) width desired term := by
  induction records with
  | nil =>
    intro term h
    have hclosed : parseFrame term = none := h
    simp [choose_tree_closed width desired term hclosed,chooseSVersion,hclosed]
  | cons entry rest ih =>
    intro term h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hread : readFields width tr = some entry.val := by
      rw [matched_fields_read width (fieldsLayout entry.val) tr hr]
      simpa [entry.property] using read_layout_fields_complete entry.val
    simp [choose_tree_frame,chooseSVersion,parse_frame,hread,ih tl hl]

theorem tree_selector_matches_fuel_partial {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired pref : List Bool)
    (hpref : pref.length ≤ width) :
    ∀ term, layoutMatches (partialVersionLayout pref records) term →
      chooseSVersionTree width desired term = chooseSVersion (records.length+1) width desired term := by
  induction records with
  | nil =>
    intro term h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hw : pref.length + (width-pref.length) = width := by omega
    have hread : readFields width tr = none := by
      rw [matched_fields_read width (partialFieldsLayout pref) tr hr]
      rw [← hw]
      exact read_layout_fields_incomplete pref (width-pref.length)
    simp [choose_tree_frame,chooseSVersion,parse_frame,hread]
  | cons entry rest ih =>
    intro term h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hread : readFields width tr = some entry.val := by
      rw [matched_fields_read width (fieldsLayout entry.val) tr hr]
      simpa [entry.property] using read_layout_fields_complete entry.val
    simp [choose_tree_frame,chooseSVersion,parse_frame,hread,ih tl hl]

#print axioms tree_selector_matches_fuel_committed
#print axioms tree_selector_matches_fuel_partial

theorem tree_selector_matches_fuel_uncommitted {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool) (fields : Layout)
    (hfields : readLayoutFields width fields = none) :
    ∀ term, layoutMatches (versionWithFields records fields) term →
      chooseSVersionTree width desired term = chooseSVersion (records.length+1) width desired term := by
  induction records with
  | nil =>
    intro term h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hread : readFields width tr = none := by
      rw [matched_fields_read width fields tr hr]
      exact hfields
    simp [choose_tree_frame,chooseSVersion,parse_frame,hread]
  | cons entry rest ih =>
    intro term h
    obtain ⟨tl,tr,j,hparse,hl,hr⟩ := h
    have hterm := parse_frame_sound term tl tr j hparse
    subst term
    have hread : readFields width tr = some entry.val := by
      rw [matched_fields_read width (fieldsLayout entry.val) tr hr]
      simpa [entry.property] using read_layout_fields_complete entry.val
    simp [choose_tree_frame,chooseSVersion,parse_frame,hread,ih tl hl]

#print axioms tree_selector_matches_fuel_uncommitted

def FuelAgreement (fuel width : Nat) (desired : List Bool) (shape : Layout) : Prop :=
  ∀ term, layoutMatches shape term →
    chooseSVersionTree width desired term = chooseSVersion fuel width desired term

inductive SafeVersionTrace (fuel width : Nat) (desired : List Bool) : Nat → Layout → Layout → Prop where
  | done (s : Layout) : SafeVersionTrace fuel width desired 0 s s
  | next {n : Nat} {a b c : Layout} {path : List Bool} :
      FuelAgreement fuel width desired a → chooseVersion fuel width desired a = some path →
      openLayoutAt a path = some b → SafeVersionTrace fuel width desired n b c →
      SafeVersionTrace fuel width desired (n+1) a c

theorem lift_safe_fields_to_fuel_safe_version {width : Nat}
    (records : List {bits : List Bool // bits.length = width}) (desired : List Bool)
    (hw : desired.length = width) {n : Nat} {a b : Layout}
    (trace : SafeFieldTrace desired n a b) :
    SafeVersionTrace (records.length+1) width desired n
      (versionWithFields records a) (versionWithFields records b) := by
  induction trace with
  | done fields => exact SafeVersionTrace.done _
  | @next n a b c path hread hchoose hopen rest ih =>
    have hread' : readLayoutFields width a = none := by simpa [hw] using hread
    have hagree : FuelAgreement (records.length+1) width desired (versionWithFields records a) :=
      tree_selector_matches_fuel_uncommitted records desired a hread'
    have hchoice : chooseVersion (records.length+1) width desired (versionWithFields records a) =
        some (List.replicate records.length false ++ true :: path) := by
      rw [choose_version_with_uncommitted_fields records desired a hread', hchoose]
      rfl
    exact SafeVersionTrace.next hagree hchoice (open_version_with_fields records a b path hopen) ih

theorem fuel_safe_version_append_complete {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) :
    ∃ k, SafeVersionTrace (records.length+1) width entry.val k
        (versionLayout records) (versionLayout (records ++ [entry])) ∧
      1 ≤ k ∧ k ≤ 2*width+2 := by
  obtain ⟨k,hfields,hbound⟩ := safe_selected_fields_complete entry.val []
  have hfields' : SafeFieldTrace entry.val k .unopened (fieldsLayout entry.val) := by
    simpa [partialFieldsLayout] using hfields
  have hrest := lift_safe_fields_to_fuel_safe_version records entry.val entry.property hfields'
  have hrest' : SafeVersionTrace (records.length+1) width entry.val k
      (partialVersionLayout [] records) (versionLayout (records ++ [entry])) := by
    simpa [version_with_unopened_fields,version_with_complete_fields] using hrest
  refine ⟨k+1, ?_, by omega, ?_⟩
  · exact SafeVersionTrace.next (tree_selector_matches_fuel_committed records entry.val)
      (choose_new_version_slot records entry.val) (open_new_version_layout records) hrest'
  · rw [entry.property] at hbound
    omega

#print axioms lift_safe_fields_to_fuel_safe_version
#print axioms fuel_safe_version_append_complete

def TreeRestartedNativeStep (path : List Bool) (width : Nat) (desired : List Bool) (a b : Term) : Prop :=
  chooseSVersionTree width desired a = some (physicalPath path) ∧
    ∃ focus relpath, termAt a (physicalPath path) = some focus ∧
      nextOpeningAddress focus = some relpath ∧ DirectedStep (physicalPath path ++ relpath) a b

inductive TreeRestartedNativeTrace (path : List Bool) (width : Nat) (desired : List Bool) : Nat → Term → Term → Prop where
  | zero (a : Term) : TreeRestartedNativeTrace path width desired 0 a a
  | next {n : Nat} {a b c : Term} : TreeRestartedNativeStep path width desired a b →
      TreeRestartedNativeTrace path width desired n b c → TreeRestartedNativeTrace path width desired (n+1) a c

theorem lift_opening_with_fuel_free_selector {n : Nat} {old final : Term}
    (trace : ClosedOpeningTrace n old final) :
    ∀ shape term path fuel width desired,
      FuelAgreement fuel width desired shape →
      layoutMatches shape term → subLayout shape path = some .unopened →
      termAt term (physicalPath path) = some old →
      chooseSVersion fuel width desired term = some (physicalPath path) →
      ∃ target out, openLayoutAt shape path = some target ∧ layoutMatches target out ∧
        termAt out (physicalPath path) = some final ∧
        replaceTermAt term (physicalPath path) final = some out ∧
        TreeRestartedNativeTrace path width desired n term out := by
  induction trace with
  | @finish a b hchosen hopen =>
    intro shape term path fuel width desired hagree hmatch hslot hat hchoose
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
      TreeRestartedNativeTrace.next hglobal (TreeRestartedNativeTrace.zero out)⟩
  | @more n a b c hchosen hclosed rest ih =>
    intro shape term path fuel width desired hagree hmatch hslot hat hchoose
    obtain ⟨relpath,hlocal,hdir⟩ := hchosen
    obtain ⟨middle,hmiddle,hatMiddle,hchooseMiddle,hmatchMiddle⟩ :=
      restarted_selector_preserves_target shape term a b path relpath fuel width desired
        hmatch hslot hat hdir hclosed hchoose
    obtain ⟨middle',hreplaceFirst,hmiddle'⟩ :=
      directed_step_replaces_subterm (physicalPath path) term a relpath b hat hdir
    have heq : middle = middle' := directed_step_unique hmiddle middle' hmiddle'
    subst middle'
    obtain ⟨target,out,hopenLayout,hmatchout,hfinal,hreplaceRest,htrace⟩ :=
      ih shape middle path fuel width desired hagree hmatchMiddle hslot hatMiddle hchooseMiddle
    have hreplace : replaceTermAt term (physicalPath path) c = some out := by
      rw [← replace_same_path_overwrites (physicalPath path) term b middle c hreplaceFirst]
      exact hreplaceRest
    have htree : chooseSVersionTree width desired term = some (physicalPath path) := by
      rw [hagree term hmatch,hchoose]
    have hglobal : TreeRestartedNativeStep path width desired term middle :=
      ⟨htree,a,relpath,hat,hlocal,hmiddle⟩
    exact ⟨target,out,hopenLayout,hmatchout,hfinal,hreplace,TreeRestartedNativeTrace.next hglobal htrace⟩

#print axioms lift_opening_with_fuel_free_selector

theorem canonical_selected_opening_tree (shape target : Layout) (path : List Bool)
    (d fuel width : Nat) (desired : List Bool)
    (hagree : FuelAgreement fuel width desired shape)
    (hopen : openLayoutAt shape path = some target)
    (hchoose : chooseSVersion fuel width desired (layoutTerm shape (phaseAt d).1 (phaseAt d).2) =
      some (physicalPath path)) :
    ∃ k, (k=6 ∨ k=7) ∧ TreeRestartedNativeTrace path width desired k
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
    lift_opening_with_fuel_free_selector htrace shape (layoutTerm shape p.1 p.2)
      path fuel width desired hagree hmatch hslot hat hchoose
  have htarget : target' = target := by rw [hopen] at hopen'; exact (Option.some.inj hopen').symm
  subst target'
  have hcanonical := canonical_layout_replace path shape target p hp hopen
  have hout : out = layoutTerm target p.1 p.2 := by rw [hcanonical] at hreplace; exact (Option.some.inj hreplace).symm
  subst out
  exact ⟨k,hk,hglobal⟩


#print axioms canonical_selected_opening_tree

def TreeAdaptiveNativeStep (width : Nat) (desired : List Bool) (a b : Term) : Prop :=
  ∃ path, TreeRestartedNativeStep path width desired a b

inductive TreeAdaptiveNativeTrace (width : Nat) (desired : List Bool) : Nat → Term → Term → Prop where
  | zero (a : Term) : TreeAdaptiveNativeTrace width desired 0 a a
  | next {n : Nat} {a b c : Term} : TreeAdaptiveNativeStep width desired a b →
      TreeAdaptiveNativeTrace width desired n b c → TreeAdaptiveNativeTrace width desired (n+1) a c

theorem tree_restarted_trace_is_adaptive {path : List Bool} {width : Nat} {desired : List Bool}
    {n : Nat} {a b : Term} (h : TreeRestartedNativeTrace path width desired n a b) :
    TreeAdaptiveNativeTrace width desired n a b := by
  induction h with
  | zero x => exact TreeAdaptiveNativeTrace.zero x
  | next hab _ ih => exact TreeAdaptiveNativeTrace.next ⟨path,hab⟩ ih

theorem tree_adaptive_trace_trans {width : Nat} {desired : List Bool} {n m : Nat} {a b c : Term}
    (h : TreeAdaptiveNativeTrace width desired n a b) (k : TreeAdaptiveNativeTrace width desired m b c) :
    TreeAdaptiveNativeTrace width desired (n+m) a c := by
  induction h with
  | zero _ => simpa using k
  | @next n a b c hab _ ih =>
    have result := TreeAdaptiveNativeTrace.next hab (ih k)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem safe_version_trace_tree_native {fuel width : Nat} {desired : List Bool}
    {n : Nat} {a b : Layout} (trace : SafeVersionTrace fuel width desired n a b) (d : Nat) :
    ∃ k, TreeAdaptiveNativeTrace width desired k
        (layoutTerm a (phaseAt d).1 (phaseAt d).2) (layoutTerm b (phaseAt d).1 (phaseAt d).2) ∧
      6*n ≤ k ∧ k ≤ 7*n := by
  induction trace with
  | done s => exact ⟨0,TreeAdaptiveNativeTrace.zero _,by simp,by simp⟩
  | @next n a b c path hagree hchoose hopen rest ih =>
    have hS : chooseSVersion fuel width desired (layoutTerm a (phaseAt d).1 (phaseAt d).2) =
        some (physicalPath path) := by
      rw [choose_s_version_simulates_layout fuel width desired a (phaseAt d) (phase_at_good d),hchoose]
      rfl
    obtain ⟨first,hfirst,hrun⟩ := canonical_selected_opening_tree a b path d fuel width desired hagree hopen hS
    obtain ⟨last,hlast,hlower,hupper⟩ := ih
    refine ⟨first+last, tree_adaptive_trace_trans (tree_restarted_trace_is_adaptive hrun) hlast, ?_, ?_⟩
    · cases hfirst <;> omega
    · cases hfirst <;> omega

#print axioms tree_restarted_trace_is_adaptive
#print axioms tree_adaptive_trace_trans
#print axioms safe_version_trace_tree_native

theorem fuel_free_native_version_append {width : Nat}
    (records : List {bits : List Bool // bits.length = width})
    (entry : {bits : List Bool // bits.length = width}) (d : Nat) :
    ∃ k, TreeAdaptiveNativeTrace width entry.val k
        (layoutTerm (versionLayout records) (phaseAt d).1 (phaseAt d).2)
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) ∧
      6 ≤ k ∧ k ≤ 7*(2*width+2) ∧
      scanVersions ((records ++ [entry]).length+1) width
        (layoutTerm (versionLayout (records ++ [entry])) (phaseAt d).1 (phaseAt d).2) none = some entry.val := by
  obtain ⟨n,htrace,hnlower,hnupper⟩ := fuel_safe_version_append_complete records entry
  obtain ⟨k,hreal,klower,kupper⟩ := safe_version_trace_tree_native htrace d
  refine ⟨k,hreal,?_,?_,?_⟩
  · omega
  · omega
  · rw [actual_layout_chain_scan]
    exact newest_records_append records entry none

#print axioms fuel_free_native_version_append
