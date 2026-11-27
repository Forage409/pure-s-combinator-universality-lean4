import Std

/- Pure S protected opening: machine-checkable local reduction witness.
   Local identities are credited to Filin (2026), Appendix C.4.
   This file proves only the generic local opening, not universality. -/

inductive Term where
  | s : Term
  | var : Nat → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

infixl:70 " ⋅ " => Term.app

def S : Term := Term.s
def B : Term := S ⋅ S

inductive Step : Term → Term → Prop where
  | root (x y z : Term) : Step (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {a a' b : Term} : Step a a' → Step (a ⋅ b) (a' ⋅ b)
  | right {a b b' : Term} : Step b b' → Step (a ⋅ b) (a ⋅ b')

inductive Reduces : Term → Term → Prop where
  | refl (a : Term) : Reduces a a
  | next {a b c : Term} : Step a b → Reduces b c → Reduces a c

theorem generic_protected_opening (m n : Term) :
    Reduces ((B ⋅ m) ⋅ (B ⋅ (B ⋅ n)) ⋅ S)
      (S ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S) ⋅
       (S ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S) ⋅
        ((n ⋅ S) ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S)))) := by
  let n1 := B ⋅ n
  let n2 := B ⋅ n1
  let g := m ⋅ n2 ⋅ S
  let q := m ⋅ n2
  have h1 : Step ((B ⋅ m) ⋅ n2 ⋅ S) (S ⋅ n2 ⋅ q ⋅ S) := by
    exact Step.left (Step.root S m n2)
  have h2 : Step (S ⋅ n2 ⋅ q ⋅ S) ((n2 ⋅ S) ⋅ g) := by
    exact Step.root n2 q S
  have h3 : Step ((n2 ⋅ S) ⋅ g) ((B ⋅ (n1 ⋅ S)) ⋅ g) := by
    exact Step.left (Step.root S n1 S)
  have h4 : Step ((B ⋅ (n1 ⋅ S)) ⋅ g) (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) := by
    exact Step.root S (n1 ⋅ S) g
  have h5 : Step (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) (S ⋅ g ⋅ ((B ⋅ (n ⋅ S)) ⋅ g)) := by
    exact Step.right (Step.left (Step.root S n S))
  have h6 : Step (S ⋅ g ⋅ ((B ⋅ (n ⋅ S)) ⋅ g))
      (S ⋅ g ⋅ (S ⋅ g ⋅ ((n ⋅ S) ⋅ g))) := by
    exact Step.right (Step.root S (n ⋅ S) g)
  exact Reduces.next h1 (Reduces.next h2 (Reduces.next h3
    (Reduces.next h4 (Reduces.next h5 (Reduces.next h6 (Reduces.refl _))))))

theorem zero_phase_reset (n : Term) :
    Step ((S ⋅ B ⋅ B) ⋅ n ⋅ S) ((B ⋅ n) ⋅ (B ⋅ n) ⋅ S) := by
  exact Step.left (Step.root B B n)

#print axioms generic_protected_opening
#print axioms zero_phase_reset

def numeral : Nat → Term
  | 0 => S ⋅ B ⋅ B
  | n + 1 => B ⋅ numeral n

theorem numeral_not_s (n : Nat) : numeral n ≠ S := by
  cases n <;> intro h <;> cases h

theorem right_child_wrapper_not_protected (r c d : Term) (hc : c ≠ S) :
    ¬ ∃ l u j, (S ⋅ r ⋅ ((c ⋅ S) ⋅ d)) = (S ⋅ l ⋅ (S ⋅ u ⋅ j)) := by
  intro ⟨l, u, j, h⟩
  have hleft : c ⋅ S = S ⋅ u := by
    injection h with _ hright
    injection hright with hleft _
  have hhead : c = S := by
    injection hleft with hhead _
  exact hc hhead

theorem generated_right_wrapper_not_protected (r d : Term) (n : Nat) :
    ¬ ∃ l u j, (S ⋅ r ⋅ ((numeral n ⋅ S) ⋅ d)) = (S ⋅ l ⋅ (S ⋅ u ⋅ j)) :=
  right_child_wrapper_not_protected r (numeral n) d (numeral_not_s n)

#print axioms numeral_not_s
#print axioms generated_right_wrapper_not_protected

def leaves : Term → Nat
  | .s => 1
  | .var _ => 1
  | .app a b => leaves a + leaves b

theorem numeral_leaves (n : Nat) : leaves (numeral n) = 5 + 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [numeral, leaves, B, S, ih]
    omega

#print axioms numeral_leaves

def generator (m n : Nat) : Term := numeral m ⋅ numeral n ⋅ S
def frameTerm (l r j : Term) : Term := S ⋅ l ⋅ (S ⋅ r ⋅ j)

theorem positive_phase_open (m n : Nat) :
    Reduces (generator (m+1) (n+2))
      (frameTerm (generator m (n+2)) (generator m (n+2))
        ((numeral n ⋅ S) ⋅ (generator m (n+2)))) := by
  exact generic_protected_opening (numeral m) (numeral n)

theorem zero_phase_reduction (n : Nat) :
    Step (generator 0 (n+2)) (generator (n+3) (n+3)) := by
  exact zero_phase_reset (numeral (n+2))

#print axioms positive_phase_open
#print axioms zero_phase_reduction

theorem zero_phase_open (n : Nat) :
    Reduces (generator 0 (n+2))
      (frameTerm (generator (n+2) (n+3)) (generator (n+2) (n+3))
        ((numeral (n+1) ⋅ S) ⋅ (generator (n+2) (n+3)))) := by
  exact Reduces.next (zero_phase_reduction n) (positive_phase_open (n+2) (n+1))

#print axioms zero_phase_open

theorem frame_has_no_root_redex (l r j : Term) :
    ¬ ∃ x y z, frameTerm l r j = S ⋅ x ⋅ y ⋅ z := by
  intro ⟨x, y, z, h⟩
  cases h

#print axioms frame_has_no_root_redex

theorem generator_leaves (m n : Nat) :
    leaves (generator m n) = 11 + 2*m + 2*n := by
  simp [generator, leaves, S, numeral_leaves]
  omega

theorem generator_junk_leaves (k m n : Nat) :
    leaves ((numeral k ⋅ S) ⋅ generator m n) = 17 + 2*k + 2*m + 2*n := by
  simp [leaves, S, numeral_leaves, generator_leaves]
  omega

theorem frame_leaves (l r j : Term) :
    leaves (frameTerm l r j) = 2 + leaves l + leaves r + leaves j := by
  simp [frameTerm, leaves, S]
  omega

#print axioms generator_leaves
#print axioms generator_junk_leaves
#print axioms frame_leaves

def parseFrame : Term → Option (Term × Term × Term)
  | .app (.app .s l) (.app (.app .s r) j) => some (l,r,j)
  | _ => none

theorem parse_frame (l r j : Term) : parseFrame (frameTerm l r j) = some (l,r,j) := by
  rfl

theorem parse_generator_closed (m n : Nat) : parseFrame (generator m n) = none := by
  simp [parseFrame, generator, S]

theorem intermediate_frames_closed (m n : Term) :
    let n1 := B ⋅ n
    let n2 := B ⋅ n1
    let q := m ⋅ n2
    let g := m ⋅ n2 ⋅ S
    parseFrame ((B ⋅ m) ⋅ n2 ⋅ S) = none ∧
    parseFrame (S ⋅ n2 ⋅ q ⋅ S) = none ∧
    parseFrame ((n2 ⋅ S) ⋅ g) = none ∧
    parseFrame ((B ⋅ (n1 ⋅ S)) ⋅ g) = none ∧
    parseFrame (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) = none ∧
    parseFrame (S ⋅ g ⋅ ((B ⋅ (n ⋅ S)) ⋅ g)) = none := by
  simp [parseFrame, B, S]

#print axioms parse_frame
#print axioms parse_generator_closed
#print axioms intermediate_frames_closed

def flagValue (t : Term) : Bool := (parseFrame t).isSome

def flagTerm (base junk : Term) (b : Bool) : Term :=
  if b then frameTerm base base junk else base

def encodedFields (base junk : Term) : List Bool → Term
  | [] => frameTerm base base junk
  | b :: bs => frameTerm (flagTerm base junk b) (encodedFields base junk bs) junk

def readFields : Nat → Term → Option (List Bool)
  | 0, t => if flagValue t then some [] else none
  | n+1, t =>
    match parseFrame t with
    | none => none
    | some (flag, rest, _) => (readFields n rest).map (fun bits => flagValue flag :: bits)

theorem read_flag_term (base junk : Term) (hbase : parseFrame base = none) (b : Bool) :
    flagValue (flagTerm base junk b) = b := by
  cases b <;> simp [flagValue, flagTerm, parse_frame, hbase]

theorem read_encoded_fields (base junk : Term) (hbase : parseFrame base = none)
    (bits : List Bool) : readFields bits.length (encodedFields base junk bits) = some bits := by
  induction bits with
  | nil => simp [encodedFields, readFields, flagValue, parse_frame]
  | cons b bs ih =>
    simp [encodedFields, readFields, parse_frame, read_flag_term base junk hbase b, ih]

#print axioms read_flag_term
#print axioms read_encoded_fields

def indexedFlag (base junk : Nat → Term) (depth : Nat) (b : Bool) : Term :=
  if b then frameTerm (base (depth+1)) (base (depth+1)) (junk depth) else base depth

def indexedFields (base junk : Nat → Term) : Nat → List Bool → Term
  | depth, [] => frameTerm (base (depth+1)) (base (depth+1)) (junk depth)
  | depth, b :: bs =>
      frameTerm (indexedFlag base junk (depth+1) b) (indexedFields base junk (depth+1) bs) (junk depth)

theorem read_indexed_flag (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (depth : Nat) (b : Bool) :
    flagValue (indexedFlag base junk depth b) = b := by
  cases b <;> simp [flagValue, indexedFlag, parse_frame, hbase]

theorem read_indexed_fields (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (bits : List Bool) :
    ∀ depth, readFields bits.length (indexedFields base junk depth bits) = some bits := by
  induction bits with
  | nil => intro depth; simp [indexedFields, readFields, flagValue, parse_frame]
  | cons b bs ih =>
    intro depth
    simp [indexedFields, readFields, parse_frame, read_indexed_flag base junk hbase, ih]

#print axioms read_indexed_flag
#print axioms read_indexed_fields

def indexedPartialFields (base junk : Nat → Term) : Nat → List Bool → Term
  | depth, [] => base depth
  | depth, b :: bs =>
      frameTerm (indexedFlag base junk (depth+1) b) (indexedPartialFields base junk (depth+1) bs) (junk depth)

theorem read_partial_fields_none (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (pref : List Bool) :
    ∀ depth remaining,
      readFields (pref.length + remaining) (indexedPartialFields base junk depth pref) = none := by
  induction pref with
  | nil =>
    intro depth remaining
    cases remaining with
    | zero => simp [indexedPartialFields, readFields, flagValue, hbase]
    | succ n => simp [indexedPartialFields, readFields, hbase]
  | cons b bs ih =>
    intro depth remaining
    simp only [List.length_cons]
    have rearrange : bs.length + 1 + remaining = (bs.length + remaining) + 1 := by omega
    rw [rearrange]
    simp [indexedPartialFields, readFields, parse_frame, ih]

#print axioms read_partial_fields_none

def readVersion (width : Nat) (term : Term) : Option (List Bool) :=
  match parseFrame term with
  | none => none
  | some (_, fields, _) => readFields width fields

def indexedVersion (base junk : Nat → Term) (depth : Nat) (next : Term)
    (bits : List Bool) : Term :=
  frameTerm next (indexedFields base junk (depth+1) bits) (junk depth)

def indexedPartialVersion (base junk : Nat → Term) (depth : Nat) (next : Term)
    (pref : List Bool) : Term :=
  frameTerm next (indexedPartialFields base junk (depth+1) pref) (junk depth)

theorem committed_version_readable (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (depth : Nat)
    (next : Term) (bits : List Bool) :
    readVersion bits.length (indexedVersion base junk depth next bits) = some bits := by
  simp [readVersion, indexedVersion, parse_frame, read_indexed_fields base junk hbase]

theorem incomplete_version_invisible (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (depth remaining : Nat)
    (next : Term) (pref : List Bool) :
    readVersion (pref.length + remaining) (indexedPartialVersion base junk depth next pref) = none := by
  simp [readVersion, indexedPartialVersion, parse_frame, read_partial_fields_none base junk hbase]

#print axioms committed_version_readable
#print axioms incomplete_version_invisible

def versionChain (base junk : Nat → Term) (width : Nat) : Nat → List {bits : List Bool // bits.length = width} → Term
  | depth, [] => base depth
  | depth, entry :: rest =>
      indexedVersion base junk depth (versionChain base junk width (depth+1) rest) entry.val

def scanVersions : Nat → Nat → Term → Option (List Bool) → Option (List Bool)
  | 0, _, _, current => current
  | fuel+1, width, term, current =>
      match parseFrame term with
      | none => current
      | some (next, _, _) =>
          let value := readVersion width term
          let updated := match value with | none => current | some bits => some bits
          scanVersions fuel width next updated

def newestRecords : List {bits : List Bool // bits.length = width} → Option (List Bool) → Option (List Bool)
  | [], current => current
  | entry :: rest, _ => newestRecords rest (some entry.val)

theorem scan_committed_version_chain (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (width : Nat)
    (records : List {bits : List Bool // bits.length = width}) :
    ∀ depth current,
      scanVersions (records.length+1) width (versionChain base junk width depth records) current =
        newestRecords records current := by
  induction records with
  | nil => intro depth current; simp [versionChain, scanVersions, newestRecords, hbase]
  | cons entry rest ih =>
    intro depth current
    have hread : readVersion width
        (indexedVersion base junk depth (versionChain base junk width (depth+1) rest) entry.val) = some entry.val := by
      simpa [entry.property] using
        committed_version_readable base junk hbase depth (versionChain base junk width (depth+1) rest) entry.val
    have hreadFrame : readVersion width
        (frameTerm (versionChain base junk width (depth+1) rest)
          (indexedFields base junk (depth+1) entry.val) (junk depth)) = some entry.val := by
      simpa [indexedVersion] using hread
    simp [versionChain, scanVersions, indexedVersion, parse_frame, newestRecords, hreadFrame, ih]

#print axioms scan_committed_version_chain

def versionChainPartial (base junk : Nat → Term) (width : Nat) (pref : List Bool) :
    Nat → List {bits : List Bool // bits.length = width} → Term
  | depth, [] => indexedPartialVersion base junk depth (base (depth+1)) pref
  | depth, entry :: rest =>
      indexedVersion base junk depth (versionChainPartial base junk width pref (depth+1) rest) entry.val

theorem scan_chain_ignores_partial_tail (base junk : Nat → Term)
    (hbase : ∀ depth, parseFrame (base depth) = none) (width : Nat)
    (pref : List Bool) (hpref : pref.length ≤ width)
    (records : List {bits : List Bool // bits.length = width}) :
    ∀ depth current,
      scanVersions (records.length+2) width (versionChainPartial base junk width pref depth records) current =
        newestRecords records current := by
  induction records with
  | nil =>
    intro depth current
    have hwidth : pref.length + (width - pref.length) = width := by omega
    have hread : readVersion width
        (indexedPartialVersion base junk depth (base (depth+1)) pref) = none := by
      simpa [hwidth] using incomplete_version_invisible base junk hbase depth (width-pref.length) (base (depth+1)) pref
    have hframe : readVersion width
        (frameTerm (base (depth+1)) (indexedPartialFields base junk (depth+1) pref) (junk depth)) = none := by
      simpa [indexedPartialVersion] using hread
    simp [versionChainPartial, indexedPartialVersion, scanVersions, parse_frame, hframe, hbase, newestRecords]
  | cons entry rest ih =>
    intro depth current
    have hread : readVersion width
        (indexedVersion base junk depth (versionChainPartial base junk width pref (depth+1) rest) entry.val) = some entry.val := by
      simpa [entry.property] using
        committed_version_readable base junk hbase depth (versionChainPartial base junk width pref (depth+1) rest) entry.val
    have hframe : readVersion width
        (frameTerm (versionChainPartial base junk width pref (depth+1) rest)
          (indexedFields base junk (depth+1) entry.val) (junk depth)) = some entry.val := by
      simpa [indexedVersion] using hread
    have fuel : (entry :: rest).length + 2 = (rest.length + 2) + 1 := by simp
    rw [fuel]
    change scanVersions ((rest.length+2)+1) width
      (indexedVersion base junk depth (versionChainPartial base junk width pref (depth+1) rest) entry.val) current =
        newestRecords rest (some entry.val)
    rw [scanVersions]
    simp only [indexedVersion, parse_frame, hframe]
    exact ih (depth+1) (some entry.val)

#print axioms scan_chain_ignores_partial_tail

theorem reduces_left {a b : Term} (h : Reduces a b) (c : Term) :
    Reduces (a ⋅ c) (b ⋅ c) := by
  induction h with
  | refl x => exact Reduces.refl (x ⋅ c)
  | next hab _ ih => exact Reduces.next (Step.left hab) ih

theorem reduces_right {a b : Term} (h : Reduces a b) (c : Term) :
    Reduces (c ⋅ a) (c ⋅ b) := by
  induction h with
  | refl x => exact Reduces.refl (c ⋅ x)
  | next hab _ ih => exact Reduces.next (Step.right hab) ih

theorem frame_left_independent {l l' : Term} (h : Reduces l l') (r j : Term) :
    Reduces (frameTerm l r j) (frameTerm l' r j) := by
  unfold frameTerm
  exact reduces_left (reduces_right h S) (S ⋅ r ⋅ j)

theorem frame_right_independent {r r' : Term} (h : Reduces r r') (l j : Term) :
    Reduces (frameTerm l r j) (frameTerm l r' j) := by
  unfold frameTerm
  exact reduces_right (reduces_left (reduces_right h S) j) (S ⋅ l)

#print axioms frame_left_independent
#print axioms frame_right_independent

inductive ProtectedFrame where
  | left : Term → Term → ProtectedFrame
  | right : Term → Term → ProtectedFrame

def wrapProtected (frames : List ProtectedFrame) (hole : Term) : Term :=
  frames.foldl (fun current f => match f with
    | .left r j => frameTerm current r j
    | .right l j => frameTerm l current j) hole

theorem protected_context_preserves_reduction (frames : List ProtectedFrame)
    {a b : Term} (h : Reduces a b) : Reduces (wrapProtected frames a) (wrapProtected frames b) := by
  induction frames generalizing a b with
  | nil => exact h
  | cons f rest ih =>
    cases f with
    | left r j =>
      apply ih
      exact frame_left_independent h r j
    | right l j =>
      apply ih
      exact frame_right_independent h l j

#print axioms protected_context_preserves_reduction

theorem every_good_generator_opens (m n : Nat) (hn : 2 ≤ n) (hm : m ≤ n) :
    ∃ m' n' j, Reduces (generator m n) (frameTerm (generator m' n') (generator m' n') j) ∧
      2 ≤ n' ∧ m' ≤ n' := by
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero =>
        refine ⟨n+2,n+3,(numeral (n+1) ⋅ S) ⋅ generator (n+2) (n+3), ?_, ?_, ?_⟩
        · exact zero_phase_open n
        · omega
        · omega
      | succ m =>
        refine ⟨m,n+2,(numeral n ⋅ S) ⋅ generator m (n+2), ?_, ?_, ?_⟩
        · exact positive_phase_open m n
        · omega
        · omega

#print axioms every_good_generator_opens

theorem reduces_trans {a b c : Term} (h : Reduces a b) (k : Reduces b c) : Reduces a c := by
  induction h with
  | refl _ => exact k
  | next hab _ ih => exact Reduces.next hab (ih k)

inductive Layout where
  | unopened : Layout
  | opened : Layout → Layout → Layout

def layoutTerm : Layout → Nat → Nat → Term
  | .unopened, m, n => generator m n
  | .opened l r, 0, Nat.succ (Nat.succ n) =>
      let childM := n+2
      let childN := n+3
      let g := generator childM childN
      frameTerm (layoutTerm l childM childN) (layoutTerm r childM childN)
        ((numeral (n+1) ⋅ S) ⋅ g)
  | .opened l r, Nat.succ m, Nat.succ (Nat.succ n) =>
      let childN := n+2
      let g := generator m childN
      frameTerm (layoutTerm l m childN) (layoutTerm r m childN)
        ((numeral n ⋅ S) ⋅ g)
  | .opened _ _, m, n => generator m n

theorem any_finite_layout_reachable (shape : Layout) (m n : Nat)
    (hn : 2 ≤ n) (hm : m ≤ n) : Reduces (generator m n) (layoutTerm shape m n) := by
  induction shape generalizing m n with
  | unopened => exact Reduces.refl _
  | opened l r ihl ihr =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases n with
      | zero => exfalso; omega
      | succ n =>
        cases m with
        | zero =>
          have hl : Reduces (generator (n+2) (n+3)) (layoutTerm l (n+2) (n+3)) :=
            ihl (n+2) (n+3) (by omega) (by omega)
          have hr : Reduces (generator (n+2) (n+3)) (layoutTerm r (n+2) (n+3)) :=
            ihr (n+2) (n+3) (by omega) (by omega)
          exact reduces_trans (zero_phase_open n)
            (reduces_trans (frame_left_independent hl _ _) (frame_right_independent hr _ _))
        | succ m =>
          have hl : Reduces (generator m (n+2)) (layoutTerm l m (n+2)) :=
            ihl m (n+2) (by omega) (by omega)
          have hr : Reduces (generator m (n+2)) (layoutTerm r m (n+2)) :=
            ihr m (n+2) (by omega) (by omega)
          exact reduces_trans (positive_phase_open m n)
            (reduces_trans (frame_left_independent hl _ _) (frame_right_independent hr _ _))

#print axioms reduces_trans
#print axioms any_finite_layout_reachable

def layoutMatches : Layout → Term → Prop
  | .unopened, term => parseFrame term = none
  | .opened l r, term =>
      ∃ lt rt j, parseFrame term = some (lt,rt,j) ∧ layoutMatches l lt ∧ layoutMatches r rt

theorem finite_layout_decodes (shape : Layout) (m n : Nat)
    (hn : 2 ≤ n) (hm : m ≤ n) : layoutMatches shape (layoutTerm shape m n) := by
  induction shape generalizing m n with
  | unopened => exact parse_generator_closed m n
  | opened l r ihl ihr =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases n with
      | zero => exfalso; omega
      | succ n =>
        cases m with
        | zero =>
          refine ⟨layoutTerm l (n+2) (n+3), layoutTerm r (n+2) (n+3),
            (numeral (n+1) ⋅ S) ⋅ generator (n+2) (n+3), ?_, ?_, ?_⟩
          · exact parse_frame _ _ _
          · exact ihl (n+2) (n+3) (by omega) (by omega)
          · exact ihr (n+2) (n+3) (by omega) (by omega)
        | succ m =>
          refine ⟨layoutTerm l m (n+2), layoutTerm r m (n+2),
            (numeral n ⋅ S) ⋅ generator m (n+2), ?_, ?_, ?_⟩
          · exact parse_frame _ _ _
          · exact ihl m (n+2) (by omega) (by omega)
          · exact ihr m (n+2) (by omega) (by omega)

#print axioms finite_layout_decodes

theorem arbitrary_storage_shape (shape : Layout) :
    ∃ term, Reduces (generator 2 2) term ∧ layoutMatches shape term := by
  exact ⟨layoutTerm shape 2 2,
    any_finite_layout_reachable shape 2 2 (by decide) (by decide),
    finite_layout_decodes shape 2 2 (by decide) (by decide)⟩

#print axioms arbitrary_storage_shape

def tenLeafSeed : Term := S ⋅ (S ⋅ B) ⋅ (S ⋅ B) ⋅ B ⋅ S

theorem seed_has_ten_leaves : leaves tenLeafSeed = 10 := by rfl

theorem seed_bootstraps_generator :
    Reduces tenLeafSeed ((numeral 1 ⋅ S) ⋅ generator 2 2) := by
  have h1 : Step tenLeafSeed (generator 0 0) := by
    exact Step.left (Step.root (S ⋅ B) (S ⋅ B) B)
  have h2 : Step (generator 0 0) (generator 1 1) := by
    exact Step.left (Step.root B B (numeral 0))
  have h3 : Step (generator 1 1) (S ⋅ numeral 1 ⋅ (numeral 0 ⋅ numeral 1) ⋅ S) := by
    exact Step.left (Step.root S (numeral 0) (numeral 1))
  have h4 : Step (S ⋅ numeral 1 ⋅ (numeral 0 ⋅ numeral 1) ⋅ S)
      ((numeral 1 ⋅ S) ⋅ (numeral 0 ⋅ numeral 1 ⋅ S)) := by
    exact Step.root (numeral 1) (numeral 0 ⋅ numeral 1) S
  have h5 : Step ((numeral 1 ⋅ S) ⋅ (numeral 0 ⋅ numeral 1 ⋅ S))
      ((numeral 1 ⋅ S) ⋅ generator 2 2) := by
    exact Step.right (Step.left (Step.root B B (numeral 1)))
  exact Reduces.next h1 (Reduces.next h2 (Reduces.next h3
    (Reduces.next h4 (Reduces.next h5 (Reduces.refl _)))))

theorem seed_reaches_any_storage_layout (shape : Layout) :
    ∃ term, Reduces tenLeafSeed ((numeral 1 ⋅ S) ⋅ term) ∧ layoutMatches shape term := by
  refine ⟨layoutTerm shape 2 2, ?_, finite_layout_decodes shape 2 2 (by decide) (by decide)⟩
  exact reduces_trans seed_bootstraps_generator
    (reduces_right (any_finite_layout_reachable shape 2 2 (by decide) (by decide)) (numeral 1 ⋅ S))

#print axioms seed_has_ten_leaves
#print axioms seed_bootstraps_generator
#print axioms seed_reaches_any_storage_layout

def arityFuel : Nat → Term → Nat
  | 0, _ => 0
  | fuel+1, .app l _ => 1 + arityFuel fuel l
  | _+1, _ => 0

def nextOpeningAddress (term : Term) : Option (List Bool) :=
  if (parseFrame term).isSome then none
  else
    match arityFuel 5 term with
    | 4 => some [false]
    | 3 => some []
    | 2 => match term with
      | .app _ r =>
        match arityFuel 5 r with
        | 4 => some [true,false]
        | 3 => some [true]
        | _ => none
      | _ => none
    | _ => none

theorem opening_selector_six_stages (m n : Term) :
    let n1 := B ⋅ n
    let n2 := B ⋅ n1
    let q := m ⋅ n2
    let g := m ⋅ n2 ⋅ S
    nextOpeningAddress ((B ⋅ m) ⋅ n2 ⋅ S) = some [false] ∧
    nextOpeningAddress (S ⋅ n2 ⋅ q ⋅ S) = some [] ∧
    nextOpeningAddress ((n2 ⋅ S) ⋅ g) = some [false] ∧
    nextOpeningAddress ((B ⋅ (n1 ⋅ S)) ⋅ g) = some [] ∧
    nextOpeningAddress (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) = some [true,false] ∧
    nextOpeningAddress (S ⋅ g ⋅ ((B ⋅ (n ⋅ S)) ⋅ g)) = some [true] ∧
    nextOpeningAddress (S ⋅ g ⋅ (S ⋅ g ⋅ ((n ⋅ S) ⋅ g))) = none := by
  simp [nextOpeningAddress, arityFuel, parseFrame, B, S]

#print axioms opening_selector_six_stages

theorem opening_selector_zero_phase (n : Nat) :
    nextOpeningAddress (generator 0 n) = some [false] := by
  simp [nextOpeningAddress, arityFuel, parseFrame, generator, numeral, B, S]

#print axioms opening_selector_zero_phase

theorem opening_selector_positive_phase (m n : Nat) :
    nextOpeningAddress (generator (m+1) (n+2)) = some [false] := by
  exact (opening_selector_six_stages (numeral m) (numeral n)).1

#print axioms opening_selector_positive_phase

def openLayoutAt : Layout → List Bool → Option Layout
  | .unopened, [] => some (.opened .unopened .unopened)
  | .opened _ _, [] => none
  | .unopened, _ :: _ => none
  | .opened l r, false :: path => (openLayoutAt l path).map (fun l' => .opened l' r)
  | .opened l r, true :: path => (openLayoutAt r path).map (fun r' => .opened l r')

theorem layout_open_root (m n : Nat) (hn : 2 ≤ n) :
    Reduces (layoutTerm .unopened m n) (layoutTerm (.opened .unopened .unopened) m n) := by
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero => exact zero_phase_open n
      | succ m => exact positive_phase_open m n

#print axioms layout_open_root

theorem layout_lift_left (l l' r : Layout) (m n : Nat) (hn : 2 ≤ n) (hm : m ≤ n)
    (h : ∀ x y, 2 ≤ y → x ≤ y → Reduces (layoutTerm l x y) (layoutTerm l' x y)) :
    Reduces (layoutTerm (.opened l r) m n) (layoutTerm (.opened l' r) m n) := by
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero => exact frame_left_independent (h (n+2) (n+3) (by omega) (by omega)) _ _
      | succ m => exact frame_left_independent (h m (n+2) (by omega) (by omega)) _ _

theorem layout_lift_right (l r r' : Layout) (m n : Nat) (hn : 2 ≤ n) (hm : m ≤ n)
    (h : ∀ x y, 2 ≤ y → x ≤ y → Reduces (layoutTerm r x y) (layoutTerm r' x y)) :
    Reduces (layoutTerm (.opened l r) m n) (layoutTerm (.opened l r') m n) := by
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero => exact frame_right_independent (h (n+2) (n+3) (by omega) (by omega)) _ _
      | succ m => exact frame_right_independent (h m (n+2) (by omega) (by omega)) _ _

#print axioms layout_lift_left
#print axioms layout_lift_right

theorem selected_layout_opening (path : List Bool) :
    ∀ (shape target : Layout) (m n : Nat),
      2 ≤ n → m ≤ n → openLayoutAt shape path = some target →
      Reduces (layoutTerm shape m n) (layoutTerm target m n) := by
  induction path with
  | nil =>
    intro shape target m n hn hm h
    cases shape with
    | unopened =>
      simp [openLayoutAt] at h
      subst target
      exact layout_open_root m n hn
    | opened l r => simp [openLayoutAt] at h
  | cons side path ih =>
    intro shape target m n hn hm h
    cases shape with
    | unopened => simp [openLayoutAt] at h
    | opened l r =>
      cases side with
      | false =>
        cases hx : openLayoutAt l path with
        | none => simp [openLayoutAt, hx] at h
        | some updated =>
          simp [openLayoutAt, hx] at h
          subst target
          apply layout_lift_left l updated r m n hn hm
          intro x y hy hxbound
          exact ih l updated x y hy hxbound hx
      | true =>
        cases hx : openLayoutAt r path with
        | none => simp [openLayoutAt, hx] at h
        | some updated =>
          simp [openLayoutAt, hx] at h
          subst target
          apply layout_lift_right l r updated m n hn hm
          intro x y hy hxbound
          exact ih r updated x y hy hxbound hx

#print axioms selected_layout_opening

inductive ExactSteps : Nat → Term → Term → Prop where
  | zero (a : Term) : ExactSteps 0 a a
  | next {n : Nat} {a b c : Term} : Step a b → ExactSteps n b c → ExactSteps (n+1) a c

theorem generic_protected_opening_six (m n : Term) :
    ExactSteps 6 ((B ⋅ m) ⋅ (B ⋅ (B ⋅ n)) ⋅ S)
      (S ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S) ⋅
       (S ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S) ⋅
        ((n ⋅ S) ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S)))) := by
  let n1 := B ⋅ n
  let n2 := B ⋅ n1
  let g := m ⋅ n2 ⋅ S
  let q := m ⋅ n2
  have h1 : Step ((B ⋅ m) ⋅ n2 ⋅ S) (S ⋅ n2 ⋅ q ⋅ S) := by
    exact Step.left (Step.root S m n2)
  have h2 : Step (S ⋅ n2 ⋅ q ⋅ S) ((n2 ⋅ S) ⋅ g) := by
    exact Step.root n2 q S
  have h3 : Step ((n2 ⋅ S) ⋅ g) ((B ⋅ (n1 ⋅ S)) ⋅ g) := by
    exact Step.left (Step.root S n1 S)
  have h4 : Step ((B ⋅ (n1 ⋅ S)) ⋅ g) (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) := by
    exact Step.root S (n1 ⋅ S) g
  have h5 : Step (S ⋅ g ⋅ ((n1 ⋅ S) ⋅ g)) (S ⋅ g ⋅ ((B ⋅ (n ⋅ S)) ⋅ g)) := by
    exact Step.right (Step.left (Step.root S n S))
  have h6 : Step (S ⋅ g ⋅ ((B ⋅ (n ⋅ S)) ⋅ g))
      (S ⋅ g ⋅ (S ⋅ g ⋅ ((n ⋅ S) ⋅ g))) := by
    exact Step.right (Step.root S (n ⋅ S) g)
  exact ExactSteps.next h1 (ExactSteps.next h2 (ExactSteps.next h3
    (ExactSteps.next h4 (ExactSteps.next h5 (ExactSteps.next h6 (ExactSteps.zero _))))))


#print axioms generic_protected_opening_six

theorem positive_phase_six (m n : Nat) :
    ExactSteps 6 (generator (m+1) (n+2))
      (frameTerm (generator m (n+2)) (generator m (n+2))
        ((numeral n ⋅ S) ⋅ generator m (n+2))) := by
  exact generic_protected_opening_six (numeral m) (numeral n)

theorem zero_phase_seven (n : Nat) :
    ExactSteps 7 (generator 0 (n+2))
      (frameTerm (generator (n+2) (n+3)) (generator (n+2) (n+3))
        ((numeral (n+1) ⋅ S) ⋅ generator (n+2) (n+3))) := by
  exact ExactSteps.next (zero_phase_reduction n) (positive_phase_six (n+2) (n+1))

theorem exact_steps_left {n : Nat} {a b : Term} (h : ExactSteps n a b) (c : Term) :
    ExactSteps n (a ⋅ c) (b ⋅ c) := by
  induction h with
  | zero x => exact ExactSteps.zero (x ⋅ c)
  | next hab _ ih => exact ExactSteps.next (Step.left hab) ih

theorem exact_steps_right {n : Nat} {a b : Term} (h : ExactSteps n a b) (c : Term) :
    ExactSteps n (c ⋅ a) (c ⋅ b) := by
  induction h with
  | zero x => exact ExactSteps.zero (c ⋅ x)
  | next hab _ ih => exact ExactSteps.next (Step.right hab) ih

theorem exact_frame_left {n : Nat} {a b : Term} (h : ExactSteps n a b) (r j : Term) :
    ExactSteps n (frameTerm a r j) (frameTerm b r j) := by
  unfold frameTerm
  exact exact_steps_left (exact_steps_right h S) (S ⋅ r ⋅ j)

theorem exact_frame_right {n : Nat} {a b : Term} (h : ExactSteps n a b) (l j : Term) :
    ExactSteps n (frameTerm l a j) (frameTerm l b j) := by
  unfold frameTerm
  exact exact_steps_right (exact_steps_left (exact_steps_right h S) j) (S ⋅ l)

#print axioms positive_phase_six
#print axioms zero_phase_seven
#print axioms exact_frame_left
#print axioms exact_frame_right

def ShortSteps (a b : Term) : Prop := ExactSteps 6 a b ∨ ExactSteps 7 a b

theorem short_frame_left {a b : Term} (h : ShortSteps a b) (r j : Term) :
    ShortSteps (frameTerm a r j) (frameTerm b r j) := by
  cases h with
  | inl h => exact Or.inl (exact_frame_left h r j)
  | inr h => exact Or.inr (exact_frame_left h r j)

theorem short_frame_right {a b : Term} (h : ShortSteps a b) (l j : Term) :
    ShortSteps (frameTerm l a j) (frameTerm l b j) := by
  cases h with
  | inl h => exact Or.inl (exact_frame_right h l j)
  | inr h => exact Or.inr (exact_frame_right h l j)

theorem layout_open_root_short (m n : Nat) (hn : 2 ≤ n) :
    ShortSteps (layoutTerm .unopened m n) (layoutTerm (.opened .unopened .unopened) m n) := by
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero => exact Or.inr (zero_phase_seven n)
      | succ m => exact Or.inl (positive_phase_six m n)

theorem layout_lift_left_short (l l' r : Layout) (m n : Nat) (hn : 2 ≤ n) (hm : m ≤ n)
    (h : ∀ x y, 2 ≤ y → x ≤ y → ShortSteps (layoutTerm l x y) (layoutTerm l' x y)) :
    ShortSteps (layoutTerm (.opened l r) m n) (layoutTerm (.opened l' r) m n) := by
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero => exact short_frame_left (h (n+2) (n+3) (by omega) (by omega)) _ _
      | succ m => exact short_frame_left (h m (n+2) (by omega) (by omega)) _ _

theorem layout_lift_right_short (l r r' : Layout) (m n : Nat) (hn : 2 ≤ n) (hm : m ≤ n)
    (h : ∀ x y, 2 ≤ y → x ≤ y → ShortSteps (layoutTerm r x y) (layoutTerm r' x y)) :
    ShortSteps (layoutTerm (.opened l r) m n) (layoutTerm (.opened l r') m n) := by
  cases n with
  | zero => exfalso; omega
  | succ n =>
    cases n with
    | zero => exfalso; omega
    | succ n =>
      cases m with
      | zero => exact short_frame_right (h (n+2) (n+3) (by omega) (by omega)) _ _
      | succ m => exact short_frame_right (h m (n+2) (by omega) (by omega)) _ _

#print axioms layout_open_root_short
#print axioms layout_lift_left_short
#print axioms layout_lift_right_short

theorem selected_layout_opening_short (path : List Bool) :
    ∀ (shape target : Layout) (m n : Nat),
      2 ≤ n → m ≤ n → openLayoutAt shape path = some target →
      ShortSteps (layoutTerm shape m n) (layoutTerm target m n) := by
  induction path with
  | nil =>
    intro shape target m n hn hm h
    cases shape with
    | unopened =>
      simp [openLayoutAt] at h
      subst target
      exact layout_open_root_short m n hn
    | opened l r => simp [openLayoutAt] at h
  | cons side path ih =>
    intro shape target m n hn hm h
    cases shape with
    | unopened => simp [openLayoutAt] at h
    | opened l r =>
      cases side with
      | false =>
        cases hx : openLayoutAt l path with
        | none => simp [openLayoutAt, hx] at h
        | some updated =>
          simp [openLayoutAt, hx] at h
          subst target
          apply layout_lift_left_short l updated r m n hn hm
          intro x y hy hxbound
          exact ih l updated x y hy hxbound hx
      | true =>
        cases hx : openLayoutAt r path with
        | none => simp [openLayoutAt, hx] at h
        | some updated =>
          simp [openLayoutAt, hx] at h
          subst target
          apply layout_lift_right_short l r updated m n hn hm
          intro x y hy hxbound
          exact ih r updated x y hy hxbound hx


#print axioms selected_layout_opening_short

inductive DirectedStep : List Bool → Term → Term → Prop where
  | root (x y z : Term) : DirectedStep [] (S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))
  | left {p : List Bool} {a a' b : Term} :
      DirectedStep p a a' → DirectedStep (false :: p) (a ⋅ b) (a' ⋅ b)
  | right {p : List Bool} {a b b' : Term} :
      DirectedStep p b b' → DirectedStep (true :: p) (a ⋅ b) (a ⋅ b')

def ChosenStep (a b : Term) : Prop :=
  ∃ p, nextOpeningAddress a = some p ∧ DirectedStep p a b

inductive ChosenSteps : Nat → Term → Term → Prop where
  | zero (a : Term) : ChosenSteps 0 a a
  | next {n : Nat} {a b c : Term} : ChosenStep a b → ChosenSteps n b c → ChosenSteps (n+1) a c

theorem generic_opening_six_selected (m n : Term) :
    ChosenSteps 6 ((B ⋅ m) ⋅ (B ⋅ (B ⋅ n)) ⋅ S)
      (S ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S) ⋅
       (S ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S) ⋅
        ((n ⋅ S) ⋅ (m ⋅ (B ⋅ (B ⋅ n)) ⋅ S)))) := by
  let n1 := B ⋅ n
  let n2 := B ⋅ n1
  let g := m ⋅ n2 ⋅ S
  let q := m ⋅ n2
  have ⟨c1,c2,c3,c4,c5,c6,_⟩ := opening_selector_six_stages m n
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
  exact ChosenSteps.next h1 (ChosenSteps.next h2 (ChosenSteps.next h3
    (ChosenSteps.next h4 (ChosenSteps.next h5 (ChosenSteps.next h6 (ChosenSteps.zero _))))))

#print axioms generic_opening_six_selected

theorem positive_phase_six_selected (m n : Nat) :
    ChosenSteps 6 (generator (m+1) (n+2))
      (frameTerm (generator m (n+2)) (generator m (n+2))
        ((numeral n ⋅ S) ⋅ generator m (n+2))) := by
  exact generic_opening_six_selected (numeral m) (numeral n)

theorem zero_phase_seven_selected (n : Nat) :
    ChosenSteps 7 (generator 0 (n+2))
      (frameTerm (generator (n+2) (n+3)) (generator (n+2) (n+3))
        ((numeral (n+1) ⋅ S) ⋅ generator (n+2) (n+3))) := by
  have first : ChosenStep (generator 0 (n+2)) (generator (n+3) (n+3)) :=
    ⟨[false], opening_selector_zero_phase (n+2),
      DirectedStep.left (DirectedStep.root B B (numeral (n+2)))⟩
  exact ChosenSteps.next first (positive_phase_six_selected (n+2) (n+1))

#print axioms positive_phase_six_selected
#print axioms zero_phase_seven_selected

def framePath : ProtectedFrame → List Bool
  | .left _ _ => [false,true]
  | .right _ _ => [true,false,true]

def contextPath : List ProtectedFrame → List Bool
  | [] => []
  | f :: rest => contextPath rest ++ framePath f

theorem directed_frame_left {p : List Bool} {a b : Term}
    (h : DirectedStep p a b) (r j : Term) :
    DirectedStep ([false,true] ++ p) (frameTerm a r j) (frameTerm b r j) := by
  exact DirectedStep.left (DirectedStep.right h)

theorem directed_frame_right {p : List Bool} {a b : Term}
    (h : DirectedStep p a b) (l j : Term) :
    DirectedStep ([true,false,true] ++ p) (frameTerm l a j) (frameTerm l b j) := by
  exact DirectedStep.right (DirectedStep.left (DirectedStep.right h))

theorem directed_protected_context (frames : List ProtectedFrame)
    {p : List Bool} {a b : Term} (h : DirectedStep p a b) :
    DirectedStep (contextPath frames ++ p) (wrapProtected frames a) (wrapProtected frames b) := by
  induction frames generalizing p a b with
  | nil => exact h
  | cons f rest ih =>
    cases f with
    | left r j =>
      simpa [contextPath, framePath, wrapProtected, List.append_assoc] using
        (ih (directed_frame_left h r j))
    | right l j =>
      simpa [contextPath, framePath, wrapProtected, List.append_assoc] using
        (ih (directed_frame_right h l j))

theorem selected_step_in_protected_context (frames : List ProtectedFrame) {a b : Term}
    (h : ChosenStep a b) :
    ∃ p, nextOpeningAddress a = some p ∧
      DirectedStep (contextPath frames ++ p) (wrapProtected frames a) (wrapProtected frames b) := by
  obtain ⟨p, hs, hd⟩ := h
  exact ⟨p,hs,directed_protected_context frames hd⟩

#print axioms directed_protected_context
#print axioms selected_step_in_protected_context

def FocusedStep (frames : List ProtectedFrame) (a b : Term) : Prop :=
  ∃ p, nextOpeningAddress a = some p ∧
    DirectedStep (contextPath frames ++ p) (wrapProtected frames a) (wrapProtected frames b)

inductive FocusedSteps (frames : List ProtectedFrame) : Nat → Term → Term → Prop where
  | zero (a : Term) : FocusedSteps frames 0 a a
  | next {n : Nat} {a b c : Term} : FocusedStep frames a b → FocusedSteps frames n b c →
      FocusedSteps frames (n+1) a c

theorem chosen_steps_in_protected_context (frames : List ProtectedFrame) {n : Nat} {a b : Term}
    (h : ChosenSteps n a b) : FocusedSteps frames n a b := by
  induction h with
  | zero x => exact FocusedSteps.zero x
  | next hab _ ih => exact FocusedSteps.next (selected_step_in_protected_context frames hab) ih

theorem positive_opening_selected_in_context (frames : List ProtectedFrame) (m n : Nat) :
    FocusedSteps frames 6 (generator (m+1) (n+2))
      (frameTerm (generator m (n+2)) (generator m (n+2))
        ((numeral n ⋅ S) ⋅ generator m (n+2))) :=
  chosen_steps_in_protected_context frames (positive_phase_six_selected m n)

theorem zero_opening_selected_in_context (frames : List ProtectedFrame) (n : Nat) :
    FocusedSteps frames 7 (generator 0 (n+2))
      (frameTerm (generator (n+2) (n+3)) (generator (n+2) (n+3))
        ((numeral (n+1) ⋅ S) ⋅ generator (n+2) (n+3))) :=
  chosen_steps_in_protected_context frames (zero_phase_seven_selected n)

#print axioms chosen_steps_in_protected_context
#print axioms positive_opening_selected_in_context
#print axioms zero_opening_selected_in_context

def leftSpine : Nat → Layout
  | 0 => .unopened
  | n+1 => .opened (leftSpine n) .unopened

theorem left_spine_grows (n : Nat) :
    openLayoutAt (leftSpine n) (List.replicate n false) = some (leftSpine (n+1)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, leftSpine, openLayoutAt, ih]

def haltedLayout (tape : Layout) (n : Nat) : Layout :=
  .opened (.opened (leftSpine n) .unopened) tape

theorem halted_layout_grows (tape : Layout) (n : Nat) :
    openLayoutAt (haltedLayout tape n) (false :: false :: List.replicate n false) =
      some (haltedLayout tape (n+1)) := by
  simp [haltedLayout, openLayoutAt, left_spine_grows]

theorem halted_layout_continues (tape : Layout) (n m phase : Nat)
    (hn : 2 ≤ phase) (hm : m ≤ phase) :
    ShortSteps (layoutTerm (haltedLayout tape n) m phase)
      (layoutTerm (haltedLayout tape (n+1)) m phase) := by
  exact selected_layout_opening_short (false :: false :: List.replicate n false)
    (haltedLayout tape n) (haltedLayout tape (n+1)) m phase hn hm (halted_layout_grows tape n)

#print axioms left_spine_grows
#print axioms halted_layout_grows
#print axioms halted_layout_continues

def haltObserved (term : Term) : Bool :=
  match parseFrame term with
  | none => false
  | some (left, _, _) => flagValue left

theorem halted_layout_observed (tape : Layout) (n m phase : Nat)
    (hn : 2 ≤ phase) (hm : m ≤ phase) :
    haltObserved (layoutTerm (haltedLayout tape n) m phase) = true := by
  have decoded := finite_layout_decodes (haltedLayout tape n) m phase hn hm
  change ∃ left right j, parseFrame (layoutTerm (haltedLayout tape n) m phase) = some (left,right,j) ∧
    layoutMatches (.opened (leftSpine n) .unopened) left ∧ layoutMatches tape right at decoded
  obtain ⟨left,right,j,hroot,hleft,_⟩ := decoded
  obtain ⟨ll,lr,lj,hflag,_,_⟩ := hleft
  simp [haltObserved,hroot,flagValue,hflag]

#print axioms halted_layout_observed

theorem halted_perpetual_checkpoints (tape : Layout) (m phase : Nat)
    (hn : 2 ≤ phase) (hm : m ≤ phase) :
    ∀ n, haltObserved (layoutTerm (haltedLayout tape n) m phase) = true ∧
      ShortSteps (layoutTerm (haltedLayout tape n) m phase)
        (layoutTerm (haltedLayout tape (n+1)) m phase) := by
  intro n
  exact ⟨halted_layout_observed tape n m phase hn hm,
    halted_layout_continues tape n m phase hn hm⟩

#print axioms halted_perpetual_checkpoints

theorem halt_flag_observed_independent_of_left_subtree (a b tape flagJunk hubJunk : Term) :
    haltObserved (frameTerm (frameTerm a b flagJunk) tape hubJunk) = true := by
  simp [haltObserved, parse_frame, flagValue]

theorem halt_flag_preserved_during_local_step {a b : Term} (h : Step a b)
    (right tape flagJunk hubJunk : Term) :
    Step (frameTerm (frameTerm a right flagJunk) tape hubJunk)
         (frameTerm (frameTerm b right flagJunk) tape hubJunk) ∧
    haltObserved (frameTerm (frameTerm a right flagJunk) tape hubJunk) = true ∧
    haltObserved (frameTerm (frameTerm b right flagJunk) tape hubJunk) = true := by
  constructor
  · exact Step.left (Step.right (Step.left (Step.right h)))
  · exact ⟨halt_flag_observed_independent_of_left_subtree _ _ _ _ _,
      halt_flag_observed_independent_of_left_subtree _ _ _ _ _⟩

#print axioms halt_flag_observed_independent_of_left_subtree
#print axioms halt_flag_preserved_during_local_step

def leftFrontier : Layout → List Bool
  | .unopened => []
  | .opened l _ => false :: leftFrontier l

theorem left_frontier_of_spine (n : Nat) :
    leftFrontier (leftSpine n) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftSpine, leftFrontier, List.replicate_succ, ih]

theorem left_frontier_is_openable (shape : Layout) :
    ∃ next, openLayoutAt shape (leftFrontier shape) = some next := by
  induction shape with
  | unopened => exact ⟨.opened .unopened .unopened, rfl⟩
  | opened l r ih =>
    obtain ⟨next, h⟩ := ih
    exact ⟨.opened next r, by simp [leftFrontier, openLayoutAt, h]⟩

#print axioms left_frontier_of_spine
#print axioms left_frontier_is_openable

theorem halt_context_always_observed (inner : List ProtectedFrame) (a right tape flagJunk hubJunk : Term) :
    haltObserved (wrapProtected
      (inner ++ [.left right flagJunk, .left tape hubJunk]) a) = true := by
  simpa [wrapProtected, List.foldl_append] using
    halt_flag_observed_independent_of_left_subtree (wrapProtected inner a) right tape flagJunk hubJunk

#print axioms halt_context_always_observed

inductive ObservedFocusedSteps (frames : List ProtectedFrame) : Nat → Term → Term → Prop where
  | zero (a : Term) (observed : haltObserved (wrapProtected frames a) = true) :
      ObservedFocusedSteps frames 0 a a
  | next {n : Nat} {a b c : Term} :
      FocusedStep frames a b → haltObserved (wrapProtected frames a) = true →
      ObservedFocusedSteps frames n b c → ObservedFocusedSteps frames (n+1) a c

theorem focused_steps_preserve_halt (inner : List ProtectedFrame) (right tape flagJunk hubJunk : Term)
    {n : Nat} {a b : Term}
    (h : FocusedSteps (inner ++ [.left right flagJunk, .left tape hubJunk]) n a b) :
    ObservedFocusedSteps (inner ++ [.left right flagJunk, .left tape hubJunk]) n a b := by
  have always : ∀ x, haltObserved (wrapProtected
      (inner ++ [.left right flagJunk, .left tape hubJunk]) x) = true := by
    intro x
    exact halt_context_always_observed inner x right tape flagJunk hubJunk
  induction h with
  | zero x => exact ObservedFocusedSteps.zero x (always x)
  | @next n a b c hab _ ih => exact ObservedFocusedSteps.next hab (always a) ih

#print axioms focused_steps_preserve_halt

inductive LayoutGrowth : Layout → Layout → Prop where
  | fromUnopened (target : Layout) : LayoutGrowth .unopened target
  | opened {l l' r r' : Layout} : LayoutGrowth l l' → LayoutGrowth r r' →
      LayoutGrowth (.opened l r) (.opened l' r')

theorem layout_growth_reduces {a b : Layout} (h : LayoutGrowth a b) :
    ∀ m n, 2 ≤ n → m ≤ n → Reduces (layoutTerm a m n) (layoutTerm b m n) := by
  induction h with
  | fromUnopened target =>
    intro m n hn hm
    exact any_finite_layout_reachable target m n hn hm
  | @opened l l' r r' hl hr ihl ihr =>
    intro m n hn hm
    exact reduces_trans (layout_lift_left l l' r m n hn hm ihl)
      (layout_lift_right l' r r' m n hn hm ihr)

#print axioms layout_growth_reduces

theorem layout_growth_refl (shape : Layout) : LayoutGrowth shape shape := by
  induction shape with
  | unopened => exact LayoutGrowth.fromUnopened _
  | opened _ _ ihl ihr => exact LayoutGrowth.opened ihl ihr

#print axioms layout_growth_refl

theorem exact_steps_trans {n m : Nat} {a b c : Term}
    (h : ExactSteps n a b) (k : ExactSteps m b c) : ExactSteps (n+m) a c := by
  induction h with
  | zero _ => simpa using k
  | @next n a b c hab _ ih =>
    have result := ExactSteps.next hab (ih k)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

#print axioms exact_steps_trans

theorem directed_step_unique {p : List Bool} {a b : Term} (h : DirectedStep p a b) :
    ∀ c, DirectedStep p a c → b = c := by
  induction h with
  | root x y z =>
    intro c hc
    cases hc
    rfl
  | @left p a a' b hab ih =>
    intro c hc
    cases hc with
    | left hc =>
      have eq := ih _ hc
      subst a'
      rfl
  | @right p a b b' hbb ih =>
    intro c hc
    cases hc with
    | right hc =>
      have eq := ih _ hc
      subst b'
      rfl

#print axioms directed_step_unique
