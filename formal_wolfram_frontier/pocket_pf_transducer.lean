import formal_program_free.program_free_cts

/-!
# Wolfram Frontier Part I: Minimal `(Fin 25, Fin 23, Fin 136)` Pocket Tree Transducer for the Program-Free Pure-`S` Cyclic Tag Simulator

Machine-checked in Lean 4.33.1 in pure constructive kernel logic (`#print axioms` uses at most
`[propext, Quot.sound]`, zero `Classical.choice`, zero kernel-bypassing reduction axioms, zero custom postulates),
resolving the finite-state helper complexity question for Stephen Wolfram's $20,000 `S` Combinator
Challenge (`wolfram_announcement.txt`, lines 116–195):

1. **Generic Two-Pass Finite-State Contextual Tree Transducer (`PocketTreeTransducer R Q P`)**:
   - Pass 1 (`annotate`) performs a single bottom-up pass assigning one state `q : Q` to every node
     under a static top-down structural role `r : R` in **exact** `2 * leaves t - 1` node transitions.
   - Pass 2 (`locateRedex`) descends from the root using `stepTD : P → Q → Q → TDAction P`
     (which inspects **only** `(p, ql, qr)` — zero role input, zero subtree re-scanning, zero fuel,
     zero unbounded arithmetic) in `≤ treeDepth t` transitions (`+ 2 ≤ treeDepth t` whenever a
     redex is contracted).
   - Consequently, **every** invocation halts in `≤ 2 * leaves t - 1 + treeDepth t` steps on **every**
     input tree `t : Term`, and in **strictly** `< 2 * leaves t - 1 + treeDepth t` steps on every
     `.step t'` contraction and every non-atomic `.halt` tree!

2. **Exact Minimal Explicit Instance `pocketPFTransducer : PocketTreeTransducer (Fin 25) (Fin 23) (Fin 136)`**:
   - `|R| = 25` static structural roles (`Fin 25`),
   - `|Q| = 23` bottom-up states per node (`Fin 23`, `< 5` bits per node; only `271` reachable
     `(role, state)` pairs across all 25 roles, compressing the `4,376,490,905`-state `U_{3,11}`
     occurrence walker by `> 10,750,000×`),
   - `|P| = 136` irreducible 1-binary-edge top-down pointer states (`Fin 136`, factored into `54`
     core macro-states + `50` `STEP_R` + `32` `STEP_LR` edge-stepping states),
   - **Zero universal Turing/tag transition table** inside the transducer: program phases live
     entirely inside the pure-`S` term reachable from the 10-leaf seed `tenLeafSeed = S(S(SS))(S(SS))(SS)S`.

3. **100% Extensional Equality with `pfSelect` on All Closed Pure-`S` Trees & End-to-End CTS Universality**:
   - `pocketPFSelect_eq_pfSelect : ∀ t : Term, isClosedPureS t = true → pocketPFSelect t = pfSelect t`,
   - `pocketPFTrace_iff_pfTrace : isClosedPureS a = true → (PocketPFTrace k a b ↔ PFTrace k a b)`,
   - `pocket_transducer_cts_universality`: 10-leaf seed reachability + bidirectional halting
     equivalence + bare-term output readback `decodeProgramFreeCTS` + quadratic trajectory leaf
     bound + unconditional `≤ 2 * leaves t - 1 + treeDepth t` linear step bound per step!
-/

namespace FormalWolframFrontier

open FormalProgramFree

local instance (priority := 10000) : ReflBEq Nat := ⟨fun {_} => decide_eq_true rfl⟩

/-! ## Section 1: Explicit Finite-State Contextual Tree Transducer & Exact Linear Step Bounds -/

/-- Binary tree height (`0` on leaves `.s` and `.var _`, `1 + max` on `.app`). -/
def treeDepth : Term → Nat
  | .s => 0
  | .var _ => 0
  | .app l r => 1 + max (treeDepth l) (treeDepth r)

/-- Top-down pointer action emitted at an internal binary application node. -/
inductive TDAction (P : Type) where
  | goLeft (next : P)
  | goRight (next : P)
  | contractHere
  | stuck
  deriving DecidableEq, Repr

/-- Pass-1 annotated binary tree storing one bottom-up state `q : Q` at every node. -/
inductive AnnotTree (Q : Type) where
  | leaf (q : Q)
  | var (q : Q) (i : Nat)
  | app (q : Q) (l r : AnnotTree Q)
  deriving DecidableEq, Repr

namespace AnnotTree

def state {Q : Type} : AnnotTree Q → Q
  | .leaf q => q
  | .var q _ => q
  | .app q _ _ => q

end AnnotTree

/-- Explicit two-pass finite-state contextual tree transducer:
    - `R`: finite set of static top-down structural roles,
    - `Q`: finite set of bottom-up node states,
    - `P`: finite set of top-down redex-locator pointer states.
    Notice `stepTD : P → Q → Q → TDAction P` inspects **only** `(p, ql, qr)` — not even `R`! -/
structure PocketTreeTransducer (R Q P : Type) where
  rootRole : R
  childRoles : R → R × R
  leafBU : R → Q
  varBU : R → Nat → Q
  appBU : R → Q → Q → Q
  acceptHalt : Q → Bool
  initTD : P
  stepTD : P → Q → Q → TDAction P

namespace PocketTreeTransducer

/-- Pass 1: single-pass bottom-up state annotation returning `(annotatedTree, nodeSteps)`. -/
def annotate {R Q P : Type} (M : PocketTreeTransducer R Q P) (role : R) : Term → AnnotTree Q × Nat
  | .s => (.leaf (M.leafBU role), 1)
  | .var i => (.var (M.varBU role i) i, 1)
  | .app l r =>
      let cr := M.childRoles role
      let al := M.annotate cr.1 l
      let ar := M.annotate cr.2 r
      (.app (M.appBU role al.1.state ar.1.state) al.1 ar.1, 1 + al.2 + ar.2)

/-- Pass 2: single-pass top-down pointer descent returning `(selectedRedexPath?, edgeSteps)`. -/
def locateRedex {R Q P : Type} (M : PocketTreeTransducer R Q P) (p : P) :
    AnnotTree Q → Option (List Bool) × Nat
  | .leaf _ => (none, 0)
  | .var _ _ => (none, 0)
  | .app _ al ar =>
      match M.stepTD p al.state ar.state with
      | .goLeft p' =>
          let sub := M.locateRedex p' al
          (sub.1.map (false :: ·), sub.2 + 1)
      | .goRight p' =>
          let sub := M.locateRedex p' ar
          (sub.1.map (true :: ·), sub.2 + 1)
      | .contractHere => (some [], 1)
      | .stuck => (none, 1)

/-- Full single-invocation execution of `M` on `t`, returning `(PFOutcome, totalTransitions)`. -/
def runTransducer {R Q P : Type} (M : PocketTreeTransducer R Q P) (t : Term) : PFOutcome × Nat :=
  let (atree, s1) := M.annotate M.rootRole t
  if M.acceptHalt atree.state then
    (.halt, s1)
  else
    let (optPath, s2) := M.locateRedex M.initTD atree
    match optPath with
    | some path =>
        match contractAt t path with
        | some t' => (.step t', s1 + s2)
        | none => (.stuck, s1 + s2)
    | none => (.stuck, s1 + s2)

def select {R Q P : Type} (M : PocketTreeTransducer R Q P) (t : Term) : PFOutcome :=
  (M.runTransducer t).1

def steps {R Q P : Type} (M : PocketTreeTransducer R Q P) (t : Term) : Nat :=
  (M.runTransducer t).2

private theorem leaves_pos_pure : ∀ t : Term, 1 ≤ leaves t
  | .s => Nat.le_refl 1
  | .var _ => Nat.le_refl 1
  | .app l r => Nat.le_trans (leaves_pos_pure l) (Nat.le_add_right _ (leaves r))

/-- Pass 1 executes **exact** `2 * leaves t - 1` node transitions on **every** `t : Term`. -/
theorem annotate_steps_exact {R Q P : Type} (M : PocketTreeTransducer R Q P) :
    ∀ (role : R) (t : Term), (M.annotate role t).2 = 2 * leaves t - 1
  | _, .s => rfl
  | _, .var _ => rfl
  | role, .app l r => by
      have hl := leaves_pos_pure l
      have hr := leaves_pos_pure r
      have ihl := M.annotate_steps_exact (M.childRoles role).1 l
      have ihr := M.annotate_steps_exact (M.childRoles role).2 r
      simp only [annotate, leaves]
      rw [ihl, ihr]
      clear ihl ihr
      omega

/-- Pass 2 executes at most `treeDepth t` transitions on **every** `t : Term`. -/
theorem locateRedex_steps_le_depth {R Q P : Type} (M : PocketTreeTransducer R Q P) :
    ∀ (role : R) (t : Term) (p : P),
      (M.locateRedex p (M.annotate role t).1).2 ≤ treeDepth t
  | _, .s, _ => Nat.le_refl 0
  | _, .var _, _ => Nat.le_refl 0
  | role, .app l r, p => by
      simp only [annotate, locateRedex, treeDepth]
      cases M.stepTD p (M.annotate (M.childRoles role).1 l).1.state
          (M.annotate (M.childRoles role).2 r).1.state with
      | goLeft p' =>
          dsimp only []
          have ih := M.locateRedex_steps_le_depth (M.childRoles role).1 l p'
          rw [Nat.add_comm 1 _]
          exact Nat.succ_le_succ (Nat.le_trans ih (Nat.le_max_left _ _))
      | goRight p' =>
          dsimp only []
          have ih := M.locateRedex_steps_le_depth (M.childRoles role).2 r p'
          rw [Nat.add_comm 1 _]
          exact Nat.succ_le_succ (Nat.le_trans ih (Nat.le_max_right _ _))
      | contractHere =>
          exact Nat.le_add_right 1 _
      | stuck =>
          exact Nat.le_add_right 1 _

private theorem contractRedex_depth_ge_3 {t t' : Term} (h : contractRedex t = some t') :
    3 ≤ treeDepth t := by
  unfold contractRedex at h
  split at h
  · rename_i x y z
    simp only [treeDepth]
    have h1 : 1 ≤ 1 + max 0 (treeDepth x) := by rw [Nat.add_comm 1]; exact Nat.succ_le_succ (Nat.zero_le _)
    have h2 : 2 ≤ 1 + max (1 + max 0 (treeDepth x)) (treeDepth y) := by
      rw [Nat.add_comm 1]
      exact Nat.succ_le_succ (Nat.le_trans h1 (Nat.le_max_left _ _))
    rw [Nat.add_comm 1]
    exact Nat.succ_le_succ (Nat.le_trans h2 (Nat.le_max_left _ _))
  · cases h

/-- Whenever `locateRedex` selects a valid redex (`contractAt t path = some t'`), Pass 2 stops
    above a redex of height `≥ 3`, taking **at most `treeDepth t - 2`** transitions! -/
theorem locateRedex_some_contract_strict {R Q P : Type} (M : PocketTreeTransducer R Q P) :
    ∀ (role : R) (t : Term) (p : P) {path : List Bool} {t' : Term},
      (M.locateRedex p (M.annotate role t).1).1 = some path →
      contractAt t path = some t' →
      (M.locateRedex p (M.annotate role t).1).2 + 2 ≤ treeDepth t
  | _, .s, _, _, _, hloc, _ => by cases hloc
  | _, .var _, _, _, _, hloc, _ => by cases hloc
  | role, .app l r, p, path, t', hloc, hcon => by
      simp only [annotate, locateRedex] at hloc ⊢
      cases hact : M.stepTD p (M.annotate (M.childRoles role).1 l).1.state
          (M.annotate (M.childRoles role).2 r).1.state with
      | goLeft p' =>
          try rw [hact] at hloc
          dsimp only [] at hloc ⊢
          cases hsub : (M.locateRedex p' (M.annotate (M.childRoles role).1 l).1).1 with
          | none => try rw [hsub] at hloc; cases hloc
          | some rest =>
              try rw [hsub] at hloc
              injection hloc with hp_eq
              subst hp_eq
              simp only [contractAt] at hcon
              cases hcl : contractAt l rest with
              | none => try rw [hcl] at hcon; cases hcon
              | some l' =>
                  have ih := M.locateRedex_some_contract_strict (M.childRoles role).1 l p' hsub hcl
                  have hle : (M.locateRedex p' (M.annotate (M.childRoles role).1 l).1).2 + 2 ≤
                      max (treeDepth l) (treeDepth r) :=
                    Nat.le_trans ih (Nat.le_max_left _ _)
                  simp only [treeDepth]
                  clear hcon hact hsub hcl ih
                  omega
      | goRight p' =>
          try rw [hact] at hloc
          dsimp only [] at hloc ⊢
          cases hsub : (M.locateRedex p' (M.annotate (M.childRoles role).2 r).1).1 with
          | none => try rw [hsub] at hloc; cases hloc
          | some rest =>
              try rw [hsub] at hloc
              injection hloc with hp_eq
              subst hp_eq
              simp only [contractAt] at hcon
              cases hcr : contractAt r rest with
              | none => try rw [hcr] at hcon; cases hcon
              | some r' =>
                  have ih := M.locateRedex_some_contract_strict (M.childRoles role).2 r p' hsub hcr
                  have hle : (M.locateRedex p' (M.annotate (M.childRoles role).2 r).1).2 + 2 ≤
                      max (treeDepth l) (treeDepth r) :=
                    Nat.le_trans ih (Nat.le_max_right _ _)
                  simp only [treeDepth]
                  clear hcon hact hsub hcr ih
                  omega
      | contractHere =>
          try rw [hact] at hloc
          dsimp only [] at hloc ⊢
          injection hloc with hp_eq
          subst hp_eq
          exact contractRedex_depth_ge_3 hcon
      | stuck =>
          try rw [hact] at hloc
          cases hloc

/-- **Unconditional Linear Step Bound (`transducer_steps_linear_bound`)**:
    On **every** input tree `t : Term` (closed or open, valid or malformed), `M` terminates in
    `≤ 2 * leaves t - 1 + treeDepth t` transitions (strictly `< 2 * leaves t + treeDepth t`). -/
theorem transducer_steps_linear_bound {R Q P : Type} (M : PocketTreeTransducer R Q P) (t : Term) :
    M.steps t ≤ 2 * leaves t - 1 + treeDepth t ∧
    M.steps t < 2 * leaves t + treeDepth t := by
  have hl := leaves_pos_pure t
  have hs1 := M.annotate_steps_exact M.rootRole t
  have hs2 := M.locateRedex_steps_le_depth M.rootRole t M.initTD
  unfold steps runTransducer
  dsimp only []
  cases M.acceptHalt (M.annotate M.rootRole t).1.state with
  | true =>
      simp only [↓reduceIte]
      rw [hs1]
      clear hs1 hs2
      exact ⟨(by omega), (by omega)⟩
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases (M.locateRedex M.initTD (M.annotate M.rootRole t).1).1 with
      | none =>
          dsimp only []
          rw [hs1]
          clear hs1
          exact ⟨(by omega), (by omega)⟩
      | some path =>
          dsimp only []
          cases contractAt t path <;>
          · dsimp only []
            rw [hs1]
            clear hs1
            exact ⟨(by omega), (by omega)⟩

/-- **Strict Linear Step Bound on Active Reductions (`transducer_steps_strict_on_step`)**:
    Whenever `M.select t = .step t'`, `M.steps t + 2 ≤ 2 * leaves t - 1 + treeDepth t`, hence
    **strictly** `M.steps t < 2 * leaves t - 1 + treeDepth t`! -/
theorem transducer_steps_strict_on_step {R Q P : Type} (M : PocketTreeTransducer R Q P)
    {t t' : Term} (h : M.select t = .step t') :
    M.steps t + 2 ≤ 2 * leaves t - 1 + treeDepth t ∧
    M.steps t < 2 * leaves t - 1 + treeDepth t := by
  have hs1 := M.annotate_steps_exact M.rootRole t
  unfold select runTransducer at h
  unfold steps runTransducer
  dsimp only [] at h ⊢
  cases hh : M.acceptHalt (M.annotate M.rootRole t).1.state with
  | true => try rw [hh] at h; cases h
  | false =>
      try rw [hh] at h
      try rw [hh]
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hloc : (M.locateRedex M.initTD (M.annotate M.rootRole t).1).1 with
      | none => try rw [hloc] at h; cases h
      | some path =>
          try rw [hloc] at h
          try rw [hloc]
          dsimp only [] at h ⊢
          cases hcon : contractAt t path with
          | none => try rw [hcon] at h; cases h
          | some u =>
              try rw [hcon] at h
              try rw [hcon]
              dsimp only []
              have hstrict := M.locateRedex_some_contract_strict M.rootRole t M.initTD hloc hcon
              rw [hs1]
              clear h hh hloc hcon hs1
              exact ⟨(by omega), (by omega)⟩

/-- Every `.step t'` emitted by `M.select` is a genuine single pure-`S` contraction `Step t t'`. -/
theorem transducer_select_step_sound {R Q P : Type} (M : PocketTreeTransducer R Q P)
    {t t' : Term} (h : M.select t = .step t') : Step t t' := by
  unfold select runTransducer at h
  dsimp only [] at h
  cases hh : M.acceptHalt (M.annotate M.rootRole t).1.state with
  | true => try rw [hh] at h; cases h
  | false =>
      try rw [hh] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hloc : (M.locateRedex M.initTD (M.annotate M.rootRole t).1).1 with
      | none => try rw [hloc] at h; cases h
      | some path =>
          try rw [hloc] at h
          dsimp only [] at h
          cases hcon : contractAt t path with
          | none => try rw [hcon] at h; cases h
          | some u =>
              try rw [hcon] at h
              dsimp only [] at h
              injection h with hu
              subst hu
              exact contractAt_sound hcon

end PocketTreeTransducer


/-! ## Section 2: Explicit `(Fin 25, Fin 23, Fin 136)` Pocket Transducer `pocketPFTransducer` -/

@[simp] private theorem fin_instOfNat_val {m : Nat} [inst : NeZero m] (n : Nat) :
    (no_index (@OfNat.ofNat (Fin m) n (@Fin.instOfNat m inst n))).val = n % m := rfl

@[inline] def fin25 (n : Nat) : Fin 25 := if h : n < 25 then ⟨n, h⟩ else 0
@[inline] def fin23 (n : Nat) : Fin 23 := if h : n < 23 then ⟨n, h⟩ else 0
@[inline] def fin136 (n : Nat) : Fin 136 := if h : n < 136 then ⟨n, h⟩ else 0

@[simp] private theorem fin136_val (n : Nat) :
    (fin136 n).val = if n < 136 then n else 0 := by
  unfold fin136; split <;> rfl

/-- Uniform left-child spine-arity projection (`SPINE` and openable `S1_*` roles). -/
def pocketSpLeft (q : Fin 23) : Nat :=
  if q.val ≤ 5 then q.val else if q.val == 6 then 2 else 1

/-- Uniform right-child spine-arity projection (`SPINE` and openable `S2_*` roles). -/
def pocketSpRight (q : Fin 23) : Nat :=
  if q.val ≤ 5 then q.val else 2

/-- Static 25-state top-down structural role grammar (`Fin 25 → Fin 25 × Fin 25`). -/
@[simp] def pocketChildRoles : Fin 25 → Fin 25 × Fin 25
  | 0  => (10, 1)   -- ROOT         -> (SPINE, HUB)
  | 1  => (11, 20)  -- HUB          -> (S1_SPINE, S2_PAYLOAD)
  | 2  => (13, 23)  -- PAYLOAD      -> (S1_PROG_RING, S2_QUEUE)
  | 3  => (14, 21)  -- PROG_RING    -> (S1_BODY, S2_PROG_RING)
  | 4  => (17, 22)  -- BODY         -> (S1_VER2, S2_TMPL)
  | 5  => (18, 22)  -- TMPL         -> (S1_VER3, S2_TMPL)
  | 6  => (18, 23)  -- QUEUE        -> (S1_VER3, S2_QUEUE)
  | 7  => (17, 24)  -- VER2         -> (S1_VER2, S2_FIELDS)
  | 8  => (18, 24)  -- VER3         -> (S1_VER3, S2_FIELDS)
  | 9  => (11, 24)  -- FIELDS       -> (S1_SPINE, S2_FIELDS)
  | 10 => (10, 10)  -- SPINE        -> (SPINE, SPINE)
  | 11 => (10, 10)  -- S1_SPINE     -> (SPINE, SPINE)
  | 12 => (10, 2)   -- S1_PAYLOAD   -> (SPINE, PAYLOAD)
  | 13 => (10, 3)   -- S1_PROG_RING -> (SPINE, PROG_RING)
  | 14 => (10, 4)   -- S1_BODY      -> (SPINE, BODY)
  | 15 => (10, 5)   -- S1_TMPL      -> (SPINE, TMPL)
  | 16 => (10, 6)   -- S1_QUEUE     -> (SPINE, QUEUE)
  | 17 => (10, 7)   -- S1_VER2      -> (SPINE, VER2)
  | 18 => (10, 8)   -- S1_VER3      -> (SPINE, VER3)
  | 19 => (10, 9)   -- S1_FIELDS    -> (SPINE, FIELDS)
  | 20 => (12, 10)  -- S2_PAYLOAD   -> (S1_PAYLOAD, SPINE)
  | 21 => (13, 10)  -- S2_PROG_RING -> (S1_PROG_RING, SPINE)
  | 22 => (15, 10)  -- S2_TMPL      -> (S1_TMPL, SPINE)
  | 23 => (16, 10)  -- S2_QUEUE     -> (S1_QUEUE, SPINE)
  | _  => (19, 10)  -- 24: S2_FIELDS-> (S1_FIELDS, SPINE)

/-- Explicit 23-state bottom-up node transition `pocketAppBU : Fin 25 → Fin 23 → Fin 23 → Fin 23`. -/
def pocketAppBU (r : Fin 25) (ql qr : Fin 23) : Fin 23 :=
  let rv := r.val
  let l := ql.val
  let rv_q := qr.val
  if rv == 0 then qr
  else if rv == 1 then
    if l == 13 && rv_q ≥ 7 then 1 else 0
  else if rv == 10 then
    if l == 1 && pocketSpRight qr == 2 then 6
    else fin23 (min 5 (pocketSpLeft ql + 1))
  else if rv == 13 then
    if pocketSpLeft ql == 0 then fin23 (1 + rv_q) else 0
  else if rv == 21 then
    if l ≥ 1 then ql else 0
  else if 11 ≤ rv && rv ≤ 19 then
    if pocketSpLeft ql == 0 then fin23 (7 + rv_q)
    else fin23 (min 5 (pocketSpLeft ql + 1))
  else if 20 ≤ rv then
    if l ≥ 7 then ql
    else fin23 (min 5 (pocketSpLeft ql + 1))
  else if rv == 2 then
    if l == 0 || rv_q < 7 then 0
    else
      let ph := l - 1
      let qv := rv_q - 7
      if ph ≥ 6 && qv < 3 then 2 else 1
  else if rv == 3 then
    if l < 7 || rv_q == 0 then 0
    else
      let body := l - 7
      if body == 0 then 0
      else
        let rest := rv_q - 1
        let bEmpty := rest == 0
        if body == 1 then
          fin23 (1 + (if bEmpty then 1 else 0))
        else
          let firstAct := if body ≥ 3 then 1 else 0
          if 1 ≤ rest && rest ≤ 4 then
            let bHL := (rest - 1) % 2
            fin23 (1 + 2 * firstAct + bHL)
          else if firstAct == 1 then
            fin23 (14 + (body - 3))
          else if rest ≥ 6 then
            fin23 (6 + (rest - 6) % 8)
          else 5
  else
    -- Frame roles `4..9` (`BODY`, `TMPL`, `QUEUE`, `VER2`, `VER3`, `FIELDS`):
    if l < 7 || rv_q < 7 then 0
    else
      let a := l - 7
      let b := rv_q - 7
      if rv == 9 then -- FIELDS
        let aFr := if a == 6 then 1 else 0
        if b == 0 then 1
        else if b == 1 then fin23 (2 + aFr)
        else if b ≤ 3 then fin23 (4 + 2 * aFr + (b - 2))
        else if b ≤ 7 then fin23 (8 + 4 * aFr + (b - 4))
        else fin23 (8 + 4 * aFr + (b - 8) / 2)
      else if rv == 7 then -- VER2
        if a != 0 then fin23 a
        else if b ≥ 4 then
          let top2 := if b < 8 then b - 4 else (b - 8) / 2
          if top2 == 3 then 1 else if top2 == 2 then 2 else 3
        else 0
      else if rv == 8 then -- VER3
        if a != 0 then fin23 a
        else if b ≥ 8 then fin23 (1 + (b - 8))
        else 0
      else if rv == 5 then -- TMPL
        let idle0 := b / 4
        let c4_0 := b % 4
        if a ≥ 1 then
          let bits := a - 1
          let hi2 := bits / 2
          let sbit := bits % 2
          let idle := if hi2 == 0 then 1 else idle0
          let c4 := if hi2 == 2 && c4_0 < 2 then 1
                    else if hi2 == 3 then 2 + sbit
                    else c4_0
          fin23 (4 * idle + c4)
        else fin23 (4 * idle0 + c4_0)
      else if rv == 6 then -- QUEUE
        let cons0 := b ≥ 9
        let rem := if cons0 then b - 9 else b
        let unc0 := if cons0 then 0 else rem / 3
        let su0 := rem % 3
        if a == 0 then
          let su := if su0 == 0 then 1 else su0
          fin23 (if cons0 then 9 + su else 3 * unc0 + su)
        else
          let bits := a - 1
          let hi2 := bits / 2
          let sbit := bits % 2
          if hi2 == 1 then
            fin23 (if cons0 then 9 + 2 else 3 * unc0 + 2)
          else if hi2 == 0 then
            let unc := if cons0 then 0 else (1 + sbit)
            fin23 (if cons0 then 9 + su0 else 3 * unc + su0)
          else if hi2 == 2 then
            fin23 (9 + su0)
          else
            fin23 (if cons0 then 9 + su0 else 3 * unc0 + su0)
      else -- rv == 4: BODY
        if a == 1 then 1
        else if a == 2 then fin23 (3 + b)
        else 2

/-- Frame-left / frame-right macro-edge helpers (`[false, true]` and `[true, false, true]`). -/
@[inline] def pocketGoFL (c : Nat) : TDAction (Fin 136) := .goLeft (fin136 (54 + c))
@[inline] def pocketGoFR (c : Nat) : TDAction (Fin 136) := .goRight (fin136 (104 + c))

/-- Shared `nextOpeningAddress` top-down step (`p = 1`, and fallback on unopened generator slots). -/
def pocketStepOpen (ql qr : Fin 23) : TDAction (Fin 136) :=
  let spl := pocketSpLeft ql
  let spr := pocketSpRight qr
  if spl == 1 && spr == 2 then .stuck
  else if spl == 3 then .goLeft 53
  else if spl == 2 then .contractHere
  else if spl == 1 then
    if spr == 4 then .goRight 52
    else if spr == 3 then .goRight 53
    else .stuck
  else .stuck

/-- Explicit 136-state role-free top-down transition `pocketStepTD : Fin 136 → Fin 23 → Fin 23 → TDAction (Fin 136)`. -/
def pocketStepTD (p : Fin 136) (ql qr : Fin 23) : TDAction (Fin 136) :=
  let pv := p.val
  let l := ql.val
  let r := qr.val
  if pv ≥ 104 then .goLeft (fin136 (pv - 50))
  else if pv ≥ 54 then .goRight (fin136 (pv - 54))
  else if pv == 50 then .goRight 51
  else if pv == 51 then
    if l < 7 || r < 7 then .stuck
    else
      let pay := r - 7
      if pay == 0 then .stuck
      else if pay == 2 then pocketGoFL 1 else pocketGoFR 0
  else if pv == 52 then
    if pocketSpLeft ql == 3 then .goLeft 53 else .stuck
  else if pv == 53 then
    if pocketSpLeft ql == 2 then .contractHere else .stuck
  else if pv == 0 then -- PAYLOAD
    if l == 0 || r < 7 then .stuck
    else
      let ph := l - 1
      let qv := r - 7
      if 1 ≤ ph && ph ≤ 4 then
        if qv ≥ 9 then pocketGoFR 17 else pocketGoFL 32
      else if ph < 6 then .stuck
      else
        let tmpl := (ph - 6) % 8
        let idleHas := tmpl / 4 == 1
        let c4 := tmpl % 4
        if qv < 9 then
          let uncons := qv / 3
          if uncons == 0 then .stuck
          else if uncons == 2 && idleHas then pocketGoFL 29 else pocketGoFR 18
        else
          let su := qv - 9
          if c4 ≥ 2 then
            let sbit := c4 - 2
            if su == 2 then pocketGoFL 31
            else if su == 1 then pocketGoFR (20 + sbit)
            else pocketGoFR 16
          else
            if su == 2 then pocketGoFR 19
            else if c4 == 1 then pocketGoFL 30
            else pocketGoFL 28
  else if pv == 1 then pocketStepOpen ql qr
  else if 2 ≤ pv && pv ≤ 15 then -- CHOOSE_FIELDS
    if l < 7 || r < 7 then pocketStepOpen ql qr
    else
      let aIsFr := (l - 7) == 6
      if pv ≤ 3 then
        let b0 := pv - 2
        if b0 == 1 && !aIsFr then pocketGoFL 1 else pocketGoFR 1
      else if pv ≤ 7 then
        let b0 := (pv - 4) / 2
        let rem1 := 2 + (pv - 4) % 2
        if b0 == 1 && !aIsFr then pocketGoFL 1 else pocketGoFR rem1
      else
        let b0 := (pv - 8) / 4
        let rem2 := 4 + (pv - 8) % 4
        if b0 == 1 && !aIsFr then pocketGoFL 1 else pocketGoFR rem2
  else if 16 ≤ pv && pv ≤ 21 then -- Q_SEEK
    if pv == 16 then
      if l ≥ 7 && r ≥ 7 then pocketGoFR 16 else pocketStepOpen ql qr
    else if l < 7 || r < 7 then .stuck
    else
      let a := l - 7
      if pv == 17 then
        if a ≥ 1 && (a - 1) / 2 == 2 then pocketGoFL (48 + (a - 1) % 2) else pocketGoFR 17
      else if pv == 18 then
        if a ≥ 1 && (a - 1) / 2 == 0 then pocketGoFL (46 + (a - 1) % 2) else pocketGoFR 18
      else if pv == 19 then
        if a ≥ 1 && (a - 1) / 2 == 1 then pocketGoFL (42 + (a - 1) % 2) else pocketGoFR 19
      else
        let sbit := pv - 20
        if a == 0 then pocketGoFL (44 + sbit) else pocketGoFR pv
  else if 22 ≤ pv && pv ≤ 24 then -- T_SEEK
    if l < 7 || r < 7 then .stuck
    else
      let a := l - 7
      if pv == 22 then
        if a ≥ 1 && (a - 1) / 2 == 0 then pocketGoFL (46 + (a - 1) % 2) else pocketGoFR 22
      else if pv == 23 then
        if a ≥ 1 && (a - 1) / 2 == 2 then pocketGoFL (48 + (a - 1) % 2) else pocketGoFR 23
      else
        if a ≥ 1 && (a - 1) / 2 == 3 then pocketGoFL (42 + (a - 1) % 2) else pocketGoFR 24
  else if 25 ≤ pv && pv ≤ 32 then -- PH_SEEK
    if l < 7 || r == 0 then .stuck
    else
      let body := l - 7
      if body == 0 then .stuck
      else
        let rest := r - 1
        let bEmpty := rest == 0
        let bFA := if 1 ≤ rest && rest ≤ 4 then (rest - 1) / 2 == 1
                   else if rest ≥ 6 then (rest - 6) / 8 == 1
                   else false
        let bHL := if 1 ≤ rest && rest ≤ 4 then (rest - 1) % 2 == 1 else false
        if pv == 25 then pocketGoFL 34
        else if pv == 26 then
          if body == 1 then pocketGoFL 33 else pocketGoFR 26
        else if pv == 27 then
          if body == 1 then (if bFA then pocketGoFL 33 else pocketGoFR 25)
          else pocketGoFR 27
        else if pv == 28 then
          if body ≥ 3 then pocketGoFL 35 else pocketGoFR 28
        else if pv ≤ 31 then
          if body ≥ 3 then pocketGoFL (36 + (pv - 29)) else pocketGoFR pv
        else -- pv == 32: HANDOFF_ROOT
          if body == 1 then
            if bEmpty then pocketGoFL 34
            else if bFA then pocketGoFL 33 else pocketGoFR 25
          else
            if bHL then (if body ≥ 3 then pocketGoFR 26 else pocketGoFL 34)
            else pocketGoFR 27
  else if 33 ≤ pv && pv ≤ 35 then -- BODY_VER
    if l ≥ 7 && r ≥ 7 then pocketGoFL (39 + (pv - 33)) else .stuck
  else if 36 ≤ pv && pv ≤ 38 then -- BODY_TMPL
    if l ≥ 7 && r ≥ 7 then pocketGoFR (22 + (pv - 36)) else .stuck
  else if 39 ≤ pv && pv ≤ 41 then -- WRITE_VER 2
    if l < 7 || r < 7 then pocketStepOpen ql qr
    else
      let b := r - 7
      let cfIdx := if pv == 39 then 4 else if pv == 40 then 6 else 7
      if b ≥ 4 then pocketGoFL pv else pocketGoFR cfIdx
  else -- 42 ≤ pv ≤ 49: WRITE_VER 3
    if l < 7 || r < 7 then pocketStepOpen ql qr
    else
      let b := r - 7
      let cfIdx := 8 + (pv - 42)
      if b ≥ 8 then pocketGoFL pv else pocketGoFR cfIdx

/-- **The Minimal `(Fin 25, Fin 23, Fin 136)` Program-Free Pure-`S` Pocket Tree Transducer**. -/
def pocketPFTransducer : PocketTreeTransducer (Fin 25) (Fin 23) (Fin 136) where
  rootRole := 0
  childRoles := pocketChildRoles
  leafBU := fun _ => 0
  varBU := fun _ _ => 0
  appBU := pocketAppBU
  acceptHalt := fun q => q.val == 1
  initTD := 50
  stepTD := pocketStepTD

def pocketPFSelect (t : Term) : PFOutcome := pocketPFTransducer.select t
def pocketPFSteps (t : Term) : Nat := pocketPFTransducer.steps t


/-! ## Section 3: Exact Pass-1 Characterization (`annotate = specBU` on All Closed Pure-`S` Trees) -/

@[inline] private def fin16 (n : Nat) : Fin 16 := if h : n < 16 then ⟨n, h⟩ else 0
@[inline] private def fin12 (n : Nat) : Fin 12 := if h : n < 12 then ⟨n, h⟩ else 0
@[inline] private def fin11 (n : Nat) : Fin 11 := if h : n < 11 then ⟨n, h⟩ else 0
@[inline] private def fin9  (n : Nat) : Fin 9  := if h : n < 9  then ⟨n, h⟩ else 0
@[inline] private def fin8  (n : Nat) : Fin 8  := if h : n < 8  then ⟨n, h⟩ else 0
@[inline] private def fin4  (n : Nat) : Fin 4  := if h : n < 4  then ⟨n, h⟩ else 0
@[inline] private def fin3  (n : Nat) : Fin 3  := if h : n < 3  then ⟨n, h⟩ else 0
@[inline] private def fin22 (n : Nat) : Fin 22 := if h : n < 22 then ⟨n, h⟩ else 0
@[inline] private def bitNat (b : Bool) : Nat := if b then 1 else 0

private theorem arityFuel_le : ∀ (k : Nat) (t : Term), arityFuel k t ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, .s => Nat.zero_le _
  | k + 1, .var _ => Nat.zero_le _
  | k + 1, .app l _ => by
      simp only [arityFuel]
      rw [Nat.add_comm 1 _]
      exact Nat.succ_le_succ (arityFuel_le k l)

private theorem arityFuel_cap : ∀ (k : Nat) (t : Term), arityFuel k t = min k (arityFuel (k + 1) t)
  | 0, _ => by simp [arityFuel]
  | _ + 1, .s => by simp [arityFuel]
  | _ + 1, .var _ => by simp [arityFuel]
  | k + 1, .app l _ => by
      have ih := arityFuel_cap k l
      simp only [arityFuel]
      rw [ih]
      clear ih
      omega

private theorem arityFuel5_app (l r : Term) :
    arityFuel 5 (l ⋅ r) = min 5 (arityFuel 5 l + 1) := by
  change 1 + arityFuel 4 l = min 5 (arityFuel 5 l + 1)
  rw [arityFuel_cap 4 l]
  change 1 + min 4 (arityFuel 5 l) = min 5 (arityFuel 5 l + 1)
  omega

private theorem closed_arityFuel_zero_iff {t : Term} (ht : isClosedPureS t = true) :
    arityFuel 5 t = 0 ↔ t = .s := by
  cases t with
  | s => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | var _ => cases ht
  | app l _ =>
      simp only [arityFuel, Nat.add_comm 1 _]
      exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

private theorem closed_isS1_iff_arity5 {t : Term} (ht : isClosedPureS t = true) :
    pfIsS1Term t = true ↔ arityFuel 5 t = 1 := by
  cases t with
  | s => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | var _ => cases ht
  | app l r =>
      have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp ht).1
      cases l with
      | s => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | var _ => cases hl
      | app ll _ =>
          simp only [pfIsS1Term, arityFuel]
          constructor
          · intro h; cases h
          · intro h; omega

private theorem closed_isS2_iff_arity5 {t : Term} (ht : isClosedPureS t = true) :
    pfIsS2Shape t = true ↔ arityFuel 5 t = 2 := by
  cases t with
  | s => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | var _ => cases ht
  | app l r =>
      have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp ht).1
      cases l with
      | s => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
      | var _ => cases hl
      | app ll lr =>
          have hll : isClosedPureS ll = true := ((Bool.and_eq_true _ _).mp hl).1
          cases ll with
          | s => exact ⟨fun _ => rfl, fun _ => rfl⟩
          | var _ => cases hll
          | app _ _ =>
              simp only [pfIsS2Shape, arityFuel]
              constructor
              · intro h; cases h
              · intro h; omega

private theorem flagValue_imp_arity5_eq_2 {t : Term} (hf : flagValue t = true) :
    arityFuel 5 t = 2 := by
  unfold flagValue parseFrame at hf
  split at hf
  · rfl
  · cases hf

/-! ### 3.1 Inner Specification Codes (`FIELDS`, `VER2`, `VER3`, `TMPL`, `QUEUE`, `BODY`, `PROG_RING`, `PAYLOAD`) -/

def combFields (b0 : Bool) (c : Fin 16) : Fin 16 :=
  let aFr := bitNat b0
  let cv := c.val
  if cv == 0 then 1
  else if cv == 1 then fin16 (2 + aFr)
  else if cv ≤ 3 then fin16 (4 + 2 * aFr + (cv - 2))
  else if cv ≤ 7 then fin16 (8 + 4 * aFr + (cv - 4))
  else fin16 (8 + 4 * aFr + (cv - 8) / 2)

def fieldsCode : Term → Fin 16
  | .app (.app .s fl) (.app (.app .s rest) _) => combFields (flagValue fl) (fieldsCode rest)
  | _ => 0

def decodeFields1 (c : Fin 16) : Option (List Bool) :=
  let v := c.val
  if v < 2 then none
  else if v ≤ 3 then some [v == 3]
  else if v ≤ 7 then some [(v - 4) / 2 == 1]
  else some [(v - 8) / 4 == 1]

def decodeFields2 (c : Fin 16) : Option (List Bool) :=
  let v := c.val
  if v < 4 then none
  else if v ≤ 7 then some [(v - 4) / 2 == 1, (v - 4) % 2 == 1]
  else some [(v - 8) / 4 == 1, ((v - 8) / 2) % 2 == 1]

def decodeFields3 (c : Fin 16) : Option (List Bool) :=
  let v := c.val
  if v < 8 then none
  else some [(v - 8) / 4 == 1, ((v - 8) / 2) % 2 == 1, (v - 8) % 2 == 1]

private theorem combFields_coherent :
    ∀ (b0 : Bool) (c : Fin 16),
      let c' := combFields b0 c
      (decide (c'.val ≠ 0) = true) ∧
      (decodeFields1 c' = (if decide (c.val ≠ 0) then some [] else none).map (b0 :: ·)) ∧
      (decodeFields2 c' = (decodeFields1 c).map (b0 :: ·)) ∧
      (decodeFields3 c' = (decodeFields2 c).map (b0 :: ·)) := by
  decide

private theorem parseFrame_some_decomp {t tl tr tj : Term}
    (h : parseFrame t = some (tl, tr, tj)) :
    t = (.s ⋅ tl) ⋅ ((.s ⋅ tr) ⋅ tj) ∧
    leaves tl < leaves t ∧
    leaves tr < leaves t := by
  have hj := PocketTreeTransducer.leaves_pos_pure tj
  have hl := PocketTreeTransducer.leaves_pos_pure tl
  have hr := PocketTreeTransducer.leaves_pos_pure tr
  unfold parseFrame at h
  split at h
  · rename_i fl rest j
    injection h with h1
    injection h1 with htl h2
    injection h2 with htr htj
    subst fl; subst rest; subst j
    refine ⟨rfl, ?_, ?_⟩
    · simp only [leaves]; omega
    · simp only [leaves]; omega
  · cases h

theorem fieldsCode_spec (t : Term) :
    flagValue t = decide ((fieldsCode t).val ≠ 0) ∧
    readFields 1 t = decodeFields1 (fieldsCode t) ∧
    readFields 2 t = decodeFields2 (fieldsCode t) ∧
    readFields 3 t = decodeFields3 (fieldsCode t) := by
  have haux : ∀ (B : Nat) (u : Term), leaves u ≤ B →
      flagValue u = decide ((fieldsCode u).val ≠ 0) ∧
      readFields 1 u = decodeFields1 (fieldsCode u) ∧
      readFields 2 u = decodeFields2 (fieldsCode u) ∧
      readFields 3 u = decodeFields3 (fieldsCode u) := by
    intro B
    induction B with
    | zero =>
        intro u hle
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure u))
    | succ B ih =>
        intro u hle
        cases hpf : parseFrame u with
        | none =>
            have hfv : flagValue u = false := by simp [flagValue, hpf]
            have hfc : fieldsCode u = 0 := by
              unfold fieldsCode
              split
              · cases hpf
              · rfl
            have hr1 : readFields 1 u = none := by simp [readFields, hpf]
            have hr2 : readFields 2 u = none := by simp [readFields, hpf]
            have hr3 : readFields 3 u = none := by simp [readFields, hpf]
            rw [hfv, hfc, hr1, hr2, hr3]
            exact ⟨rfl, rfl, rfl, rfl⟩
        | some triple =>
            rcases triple with ⟨fl, rest, j⟩
            obtain ⟨hu_eq, _, hrest_lt⟩ := parseFrame_some_decomp hpf
            have hrest_le : leaves rest ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrest_lt hle)
            obtain ⟨ih0, ih1, ih2, _⟩ := ih rest hrest_le
            have hcoh := combFields_coherent (flagValue fl) (fieldsCode rest)
            subst hu_eq
            have hfc_eq : fieldsCode ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) =
                combFields (flagValue fl) (fieldsCode rest) := rfl
            have hfv_top : flagValue ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) = true := rfl
            have hr1_eq : readFields 1 ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) =
                (if flagValue rest then some [] else none).map (flagValue fl :: ·) := rfl
            have hr2_eq : readFields 2 ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) =
                (readFields 1 rest).map (flagValue fl :: ·) := rfl
            have hr3_eq : readFields 3 ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) =
                (readFields 2 rest).map (flagValue fl :: ·) := rfl
            rw [hfc_eq, hfv_top, hr1_eq, hr2_eq, hr3_eq, ih0, ih1, ih2]
            exact ⟨hcoh.1.symm, hcoh.2.1.symm, hcoh.2.2.1.symm, hcoh.2.2.2.symm⟩
  exact haux (leaves t) t (Nat.le_refl _)


/-! ### 3.2 Compositional Laws for `pfScanVersion`, `scanTemplates`, `scanQueue`, and `scanPhases` -/

private theorem pfScanVersion_acc (width : Nat) (t : Term) (cur : Option (List Bool)) :
    pfScanVersion width cur t = match pfScanVersion width none t with
      | some res => some res
      | none => cur := by
  have haux : ∀ (B : Nat) (u : Term), leaves u ≤ B → ∀ (c : Option (List Bool)),
      pfScanVersion width c u = match pfScanVersion width none u with
        | some res => some res
        | none => c := by
    intro B
    induction B with
    | zero =>
        intro u hle
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure u))
    | succ B ih =>
        intro u hle c
        cases hpf : parseFrame u with
        | none =>
            rw [pfScanVersion_closed width c u hpf, pfScanVersion_closed width none u hpf]
        | some triple =>
            rcases triple with ⟨next, fields, j⟩
            obtain ⟨hu_eq, hnext_lt, _⟩ := parseFrame_some_decomp hpf
            have hnext_le : leaves next ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hnext_lt hle)
            subst hu_eq
            change pfScanVersion width (match readFields width fields with | none => c | some bits => some bits) next =
              match pfScanVersion width (match readFields width fields with | none => none | some bits => some bits) next with
              | some res => some res
              | none => c
            rw [ih next hnext_le (match readFields width fields with | none => c | some bits => some bits),
                ih next hnext_le (match readFields width fields with | none => none | some bits => some bits)]
            cases pfScanVersion width none next with
            | some _ => rfl
            | none => cases readFields width fields <;> rfl
  exact haux (leaves t) t (Nat.le_refl _) cur

private theorem readFields_length : ∀ (w : Nat) (t : Term) {bits : List Bool},
    readFields w t = some bits → bits.length = w
  | 0, t, bits, h => by
      simp only [readFields] at h
      split at h
      · injection h with hb; subst hb; rfl
      · cases h
  | w + 1, t, bits, h => by
      simp only [readFields] at h
      cases hpf : parseFrame t with
      | none => rw [hpf] at h; cases h
      | some triple =>
          rcases triple with ⟨fl, rest, _⟩
          rw [hpf] at h
          dsimp only [] at h
          cases hr : readFields w rest with
          | none => rw [hr] at h; cases h
          | some sub =>
              rw [hr] at h
              injection h with hb
              subst hb
              simp [readFields_length w rest hr]

private theorem pfScanVersion_length (width : Nat) (t : Term) :
    ∀ {bits : List Bool}, pfScanVersion width none t = some bits → bits.length = width := by
  intro bits
  have haux : ∀ (B : Nat) (u : Term), leaves u ≤ B →
      ∀ {b : List Bool}, pfScanVersion width none u = some b → b.length = width := by
    intro B
    induction B with
    | zero =>
        intro u hle
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure u))
    | succ B ih =>
        intro u hle b hscan
        cases hpf : parseFrame u with
        | none =>
            rw [pfScanVersion_closed width none u hpf] at hscan
            cases hscan
        | some triple =>
            rcases triple with ⟨next, fields, j⟩
            obtain ⟨hu_eq, hnext_lt, _⟩ := parseFrame_some_decomp hpf
            have hnext_le : leaves next ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hnext_lt hle)
            subst hu_eq
            change pfScanVersion width (match readFields width fields with | none => none | some fb => some fb) next =
              some b at hscan
            rw [pfScanVersion_acc width next] at hscan
            cases hsn : pfScanVersion width none next with
            | some res =>
                rw [hsn] at hscan
                injection hscan with hres
                subst hres
                exact ih next hnext_le hsn
            | none =>
                rw [hsn] at hscan
                cases hrf : readFields width fields with
                | none => rw [hrf] at hscan; cases hscan
                | some fbits =>
                    rw [hrf] at hscan
                    injection hscan with hf
                    subst hf
                    exact readFields_length width fields hrf
  exact haux (leaves t) t (Nat.le_refl _)

def ver2Code (t : Term) : Fin 4 :=
  match pfScanVersion 2 none t with
  | some [true, true]  => 1
  | some [true, false] => 2
  | some [false, _]    => 3
  | _                  => 0

theorem ver2Code_spec (t : Term) :
    (pfScanVersion 2 none t == none) = (ver2Code t == 0) ∧
    (pfScanVersion 2 none t == some [true, true]) = (ver2Code t == 1) ∧
    (pfScanVersion 2 none t == some [true, false]) = (ver2Code t == 2) := by
  unfold ver2Code
  cases hs : pfScanVersion 2 none t with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some bits =>
      have hlen := pfScanVersion_length 2 t hs
      cases bits with
      | nil => cases hlen
      | cons b0 rest1 =>
          cases rest1 with
          | nil => cases hlen
          | cons b1 rest2 =>
              cases rest2 with
              | nil => cases b0 <;> cases b1 <;> exact ⟨rfl, rfl, rfl⟩
              | cons _ _ => cases hlen

def ver3Code (t : Term) : Fin 9 :=
  match pfScanVersion 3 none t with
  | some [b0, b1, b2] => fin9 (1 + 4 * bitNat b0 + 2 * bitNat b1 + bitNat b2)
  | _ => 0

def decodeVer3 (a : Fin 9) : Option (List Bool) :=
  if a.val == 0 then none
  else
    let v := a.val - 1
    some [v / 4 == 1, (v / 2) % 2 == 1, v % 2 == 1]

private theorem decodeVer3_roundtrip :
    ∀ b0 b1 b2 : Bool,
      decodeVer3 (fin9 (1 + 4 * bitNat b0 + 2 * bitNat b1 + bitNat b2)) = some [b0, b1, b2] := by
  decide

theorem ver3Code_spec (t : Term) :
    pfScanVersion 3 none t = decodeVer3 (ver3Code t) := by
  unfold ver3Code
  cases hs : pfScanVersion 3 none t with
  | none => rfl
  | some bits =>
      have hlen := pfScanVersion_length 3 t hs
      cases bits with
      | nil => cases hlen
      | cons b0 r1 =>
          cases r1 with
          | nil => cases hlen
          | cons b1 r2 =>
              cases r2 with
              | nil => cases hlen
              | cons b2 r3 =>
                  cases r3 with
                  | nil => exact (decodeVer3_roundtrip b0 b1 b2).symm
                  | cons _ _ => cases hlen

def tmplSummaryCode (ts : TemplateScan) : Fin 8 :=
  let idle := bitNat ts.firstIdle.isSome
  let c4 := match ts.firstAppending with
    | some (_, false) => 2
    | some (_, true)  => 3
    | none => bitNat ts.firstArmed.isSome
  fin8 (4 * idle + c4)

def tmplCode (t : Term) : Fin 8 := tmplSummaryCode (scanTemplates t)

def queueSummaryCode (qs : QueueScan) : Fin 12 :=
  let su := if qs.staging.isSome then 2 else if qs.uninit.isSome then 1 else 0
  if qs.consuming.isSome then
    fin12 (9 + su)
  else
    let unc := match qs.unconsumed with
      | none => 0
      | some (_, false) => 1
      | some (_, true)  => 2
    fin12 (3 * unc + su)

def queueCode (t : Term) : Fin 12 := queueSummaryCode (scanQueue t)

def bodyCode : Term → Fin 11
  | .app (.app .s pVer) (.app (.app .s tList) _) =>
      let vc := (ver2Code pVer).val
      if vc == 1 then 1
      else if vc == 2 then fin11 (3 + (tmplCode tList).val)
      else 2
  | _ => 0

def phasesSummaryCode (ps : List PhaseEntry) : Fin 22 :=
  match ps with
  | [] => 0
  | e0 :: _ =>
      let firstAct := bitNat (e0.status == some [true, false])
      match findIdxPred (fun pe => pe.status == some [true, true]) ps with
      | some (hIdx, _) =>
          let hLast := bitNat (hIdx + 1 == ps.length)
          fin22 (1 + 2 * firstAct + hLast)
      | none =>
          match findIdxPred (fun pe => pe.status == some [true, false]) ps with
          | none => 5
          | some (_, actEntry) =>
              fin22 (6 + 8 * firstAct + (tmplSummaryCode actEntry.templates).val)

def progRingCode (t : Term) : Fin 22 := phasesSummaryCode (scanPhases t)

def payloadCode : Term → Fin 3
  | .app (.app .s progRing) (.app (.app .s queueRoot) _) =>
      let ph := (progRingCode progRing).val
      let qv := (queueCode queueRoot).val
      if ph ≥ 6 && qv < 3 then 2 else 1
  | _ => 0

/-- Exact semantic specification of all 25 bottom-up roles `Fin 25 → Term → Fin 23`. -/
def specBU : Fin 25 → Term → Fin 23
  | 0,  t => if pfRootHalt t then 1 else 0
  | 1,  t => if haltObserved t then 1 else 0
  | 2,  t => fin23 (payloadCode t).val
  | 3,  t => fin23 (progRingCode t).val
  | 4,  t => fin23 (bodyCode t).val
  | 5,  t => fin23 (tmplCode t).val
  | 6,  t => fin23 (queueCode t).val
  | 7,  t => fin23 (ver2Code t).val
  | 8,  t => fin23 (ver3Code t).val
  | 9,  t => fin23 (fieldsCode t).val
  | 10, t => if flagValue t then 6 else fin23 (arityFuel 5 t)
  | 13, t => match t with | .app .s x => fin23 (1 + (progRingCode x).val) | _ => 0
  | 21, t => match t with | .app (.app .s x) _ => fin23 (1 + (progRingCode x).val) | _ => 0
  | 11, t => match t with | .app .s x => fin23 (7 + (if flagValue x then 6 else arityFuel 5 x)) | _ => fin23 (arityFuel 5 t)
  | 12, t => match t with | .app .s x => fin23 (7 + (payloadCode x).val) | _ => fin23 (arityFuel 5 t)
  | 14, t => match t with | .app .s x => fin23 (7 + (bodyCode x).val)    | _ => fin23 (arityFuel 5 t)
  | 15, t => match t with | .app .s x => fin23 (7 + (tmplCode x).val)    | _ => fin23 (arityFuel 5 t)
  | 16, t => match t with | .app .s x => fin23 (7 + (queueCode x).val)   | _ => fin23 (arityFuel 5 t)
  | 17, t => match t with | .app .s x => fin23 (7 + (ver2Code x).val)    | _ => fin23 (arityFuel 5 t)
  | 18, t => match t with | .app .s x => fin23 (7 + (ver3Code x).val)    | _ => fin23 (arityFuel 5 t)
  | 19, t => match t with | .app .s x => fin23 (7 + (fieldsCode x).val)  | _ => fin23 (arityFuel 5 t)
  | 20, t => match t with | .app (.app .s x) _ => fin23 (7 + (payloadCode x).val) | _ => fin23 (arityFuel 5 t)
  | 22, t => match t with | .app (.app .s x) _ => fin23 (7 + (tmplCode x).val)    | _ => fin23 (arityFuel 5 t)
  | 23, t => match t with | .app (.app .s x) _ => fin23 (7 + (queueCode x).val)   | _ => fin23 (arityFuel 5 t)
  | _,  t => match t with | .app (.app .s x) _ => fin23 (7 + (fieldsCode x).val)  | _ => fin23 (arityFuel 5 t)

/-! ### 3.3 Spine-Projection Invariants & Finite Transition Coherences -/

private theorem fin23_val_of_lt {n : Nat} (h : n < 23) : (fin23 n).val = n := by
  simp [fin23, h]

private theorem pocketSpLeft_spine {t : Term} :
    pocketSpLeft (specBU 10 t) = arityFuel 5 t := by
  have har := arityFuel_le 5 t
  simp only [specBU]
  cases hf : flagValue t with
  | true =>
      rw [flagValue_imp_arity5_eq_2 hf]
      rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pocketSpLeft]
      have hlt23 : arityFuel 5 t < 23 := by omega
      rw [fin23_val_of_lt hlt23, if_pos har]

private theorem pocketSpRight_spine {t : Term} :
    pocketSpRight (specBU 10 t) = arityFuel 5 t := by
  have har := arityFuel_le 5 t
  simp only [specBU]
  cases hf : flagValue t with
  | true =>
      rw [flagValue_imp_arity5_eq_2 hf]
      rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pocketSpRight]
      have hlt23 : arityFuel 5 t < 23 := by omega
      rw [fin23_val_of_lt hlt23, if_pos har]

private theorem s1Open_spLeft_helper {t : Term} (v : Term → Nat) (hv : ∀ x, v x ≤ 15) :
    pocketSpLeft (match t with | .app .s x => fin23 (7 + v x) | _ => fin23 (arityFuel 5 t)) =
      arityFuel 5 t := by
  cases t with
  | s => rfl
  | var _ => rfl
  | app l r =>
      cases l with
      | s =>
          have hxv := hv r
          have hlt23 : 7 + v r < 23 := by omega
          have hgt6 : ¬ (7 + v r ≤ 5) := by omega
          have hne6 : (7 + v r == 6) = false := by
            cases heq : (7 + v r == 6) with
            | false => rfl
            | true => have hbad := of_decide_eq_true heq; omega
          simp only [pocketSpLeft, fin23_val_of_lt hlt23, if_neg hgt6, hne6, Bool.false_eq_true,
            ↓reduceIte, arityFuel]
      | var i =>
          have har : arityFuel 5 (.var i ⋅ r) ≤ 5 := arityFuel_le 5 _
          have hlt23 : arityFuel 5 (.var i ⋅ r) < 23 := by omega
          simp only [pocketSpLeft, fin23_val_of_lt hlt23, if_pos har]
      | app ll lr =>
          have har : arityFuel 5 ((ll ⋅ lr) ⋅ r) ≤ 5 := arityFuel_le 5 _
          have hlt23 : arityFuel 5 ((ll ⋅ lr) ⋅ r) < 23 := by omega
          simp only [pocketSpLeft, fin23_val_of_lt hlt23, if_pos har]

private theorem s2Open_spRight_helper {t : Term} (v : Term → Nat) (hv : ∀ x, v x ≤ 15) :
    pocketSpRight (match t with | .app (.app .s x) _ => fin23 (7 + v x) | _ => fin23 (arityFuel 5 t)) =
      arityFuel 5 t := by
  cases t with
  | s => rfl
  | var _ => rfl
  | app l r =>
      cases l with
      | s =>
          have har : arityFuel 5 (.s ⋅ r) ≤ 5 := arityFuel_le 5 _
          have hlt23 : arityFuel 5 (.s ⋅ r) < 23 := by omega
          simp only [pocketSpRight, fin23_val_of_lt hlt23, if_pos har]
      | var i =>
          have har : arityFuel 5 (.var i ⋅ r) ≤ 5 := arityFuel_le 5 _
          have hlt23 : arityFuel 5 (.var i ⋅ r) < 23 := by omega
          simp only [pocketSpRight, fin23_val_of_lt hlt23, if_pos har]
      | app ll lr =>
          cases ll with
          | s =>
              have hxv := hv lr
              have hlt23 : 7 + v lr < 23 := by omega
              have hgt5 : ¬ (7 + v lr ≤ 5) := by omega
              simp only [pocketSpRight, fin23_val_of_lt hlt23, if_neg hgt5, arityFuel]
          | var i =>
              have har : arityFuel 5 ((.var i ⋅ lr) ⋅ r) ≤ 5 := arityFuel_le 5 _
              have hlt23 : arityFuel 5 ((.var i ⋅ lr) ⋅ r) < 23 := by omega
              simp only [pocketSpRight, fin23_val_of_lt hlt23, if_pos har]
          | app lll llr =>
              have har : arityFuel 5 (((lll ⋅ llr) ⋅ lr) ⋅ r) ≤ 5 := arityFuel_le 5 _
              have hlt23 : arityFuel 5 (((lll ⋅ llr) ⋅ lr) ⋅ r) < 23 := by omega
              simp only [pocketSpRight, fin23_val_of_lt hlt23, if_pos har]

private theorem s1Open_ge7_iff {t : Term} (v : Term → Nat) (hv : ∀ x, v x ≤ 15) :
    (match t with | .app .s x => fin23 (7 + v x) | _ => fin23 (arityFuel 5 t)).val ≥ 7 ↔
      ∃ x, t = .s ⋅ x := by
  cases t with
  | s => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | var _ => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | app l r =>
      cases l with
      | s =>
          have hxv := hv r
          have hlt23 : 7 + v r < 23 := by omega
          rw [fin23_val_of_lt hlt23]
          exact ⟨fun _ => ⟨r, rfl⟩, fun _ => (by omega)⟩
      | var i =>
          have har := arityFuel_le 5 (.var i ⋅ r)
          have hlt23 : arityFuel 5 (.var i ⋅ r) < 23 := by omega
          rw [fin23_val_of_lt hlt23]
          exact ⟨fun h => False.elim (by omega), fun ⟨_, h⟩ => (by cases h)⟩
      | app ll lr =>
          have har := arityFuel_le 5 ((ll ⋅ lr) ⋅ r)
          have hlt23 : arityFuel 5 ((ll ⋅ lr) ⋅ r) < 23 := by omega
          rw [fin23_val_of_lt hlt23]
          exact ⟨fun h => False.elim (by omega), fun ⟨_, h⟩ => (by cases h)⟩

private theorem s2Open_ge7_iff {t : Term} (v : Term → Nat) (hv : ∀ x, v x ≤ 15) :
    (match t with | .app (.app .s x) _ => fin23 (7 + v x) | _ => fin23 (arityFuel 5 t)).val ≥ 7 ↔
      ∃ x j, t = (.s ⋅ x) ⋅ j := by
  cases t with
  | s => exact ⟨fun h => (by cases h), fun ⟨_, _, h⟩ => (by cases h)⟩
  | var _ => exact ⟨fun h => (by cases h), fun ⟨_, _, h⟩ => (by cases h)⟩
  | app l r =>
      cases l with
      | s =>
          have har := arityFuel_le 5 (.s ⋅ r)
          have hlt23 : arityFuel 5 (.s ⋅ r) < 23 := by omega
          rw [fin23_val_of_lt hlt23]
          exact ⟨fun h => False.elim (by omega), fun ⟨_, _, h⟩ => (by cases h)⟩
      | var i =>
          have har := arityFuel_le 5 (.var i ⋅ r)
          have hlt23 : arityFuel 5 (.var i ⋅ r) < 23 := by omega
          rw [fin23_val_of_lt hlt23]
          exact ⟨fun h => False.elim (by omega), fun ⟨_, _, h⟩ => (by cases h)⟩
      | app ll lr =>
          cases ll with
          | s =>
              have hxv := hv lr
              have hlt23 : 7 + v lr < 23 := by omega
              rw [fin23_val_of_lt hlt23]
              exact ⟨fun _ => ⟨lr, r, rfl⟩, fun _ => (by omega)⟩
          | var i =>
              have har := arityFuel_le 5 ((.var i ⋅ lr) ⋅ r)
              have hlt23 : arityFuel 5 ((.var i ⋅ lr) ⋅ r) < 23 := by omega
              rw [fin23_val_of_lt hlt23]
              exact ⟨fun h => False.elim (by omega), fun ⟨_, _, h⟩ => (by cases h)⟩
          | app lll llr =>
              have har := arityFuel_le 5 (((lll ⋅ llr) ⋅ lr) ⋅ r)
              have hlt23 : arityFuel 5 (((lll ⋅ llr) ⋅ lr) ⋅ r) < 23 := by omega
              rw [fin23_val_of_lt hlt23]
              exact ⟨fun h => False.elim (by omega), fun ⟨_, _, h⟩ => (by cases h)⟩

-- Finite kernel transition coherences for all frame roles (`decide` on tiny `Fin` domains):
private theorem pocketAppBU_fields_coherent :
    ∀ (b0 : Bool) (c : Fin 16),
      pocketAppBU 9 (fin23 (7 + if b0 then 6 else 0)) (fin23 (7 + c.val)) =
        fin23 (combFields b0 c).val ∧
      ∀ (a : Fin 6), pocketAppBU 9 (fin23 (7 + a.val)) (fin23 (7 + c.val)) =
        fin23 (combFields false c).val := by
  decide

private theorem pocketAppBU_ver2_coherent :
    ∀ (a : Fin 4) (b : Fin 16),
      pocketAppBU 7 (fin23 (7 + a.val)) (fin23 (7 + b.val)) =
        (if a.val != 0 then fin23 a.val
         else match decodeFields2 b with
           | some [true, true]  => 1
           | some [true, false] => 2
           | some [false, _]    => 3
           | _                  => 0) := by
  decide

private theorem pocketAppBU_ver3_coherent :
    ∀ (a : Fin 9) (b : Fin 16),
      pocketAppBU 8 (fin23 (7 + a.val)) (fin23 (7 + b.val)) =
        (if a.val != 0 then fin23 a.val
         else match decodeFields3 b with
           | some [b0, b1, b2] => fin23 (1 + 4 * bitNat b0 + 2 * bitNat b1 + bitNat b2)
           | _ => 0) := by
  decide

private theorem pocketAppBU_body_coherent :
    ∀ (a : Fin 4) (b : Fin 8),
      pocketAppBU 4 (fin23 (7 + a.val)) (fin23 (7 + b.val)) =
        (if a.val == 1 then 1
         else if a.val == 2 then fin23 (3 + b.val)
         else 2) := by
  decide

private theorem pocketAppBU_payload_coherent :
    ∀ (ph : Fin 22) (qv : Fin 12),
      pocketAppBU 2 (fin23 (1 + ph.val)) (fin23 (7 + qv.val)) =
        fin23 (if ph.val ≥ 6 && qv.val < 3 then (2 : Fin 3) else 1).val := by
  decide

private def stepTmplSummary (v3 : Option (List Bool)) (b : Fin 8) : Fin 8 :=
  let idle0 := b.val / 4 == 1
  let appd0 : Option Bool :=
    if b.val % 4 == 2 then some false
    else if b.val % 4 == 3 then some true
    else none
  let arm0 := b.val % 4 == 1
  let (idle, arm, appd) := match v3 with
    | some [false, false, _]   => (true, arm0, appd0)
    | some [true, false, _]    => (idle0, true, appd0)
    | some [true, true, sbit]  => (idle0, arm0, some sbit)
    | _                        => (idle0, arm0, appd0)
  let c4 := match appd with
    | some false => 2
    | some true  => 3
    | none => bitNat arm
  fin8 (4 * bitNat idle + c4)

private theorem pocketAppBU_tmpl_coherent :
    ∀ (a : Fin 9) (b : Fin 8),
      pocketAppBU 5 (fin23 (7 + a.val)) (fin23 (7 + b.val)) =
        fin23 (stepTmplSummary (decodeVer3 a) b).val := by
  decide

private theorem shiftPathBool_isSome (o : Option (List Bool × Bool)) :
    (shiftPathBool o).isSome = o.isSome := by
  cases o <;> rfl

private theorem shiftOptPath_isSome (o : Option (List Bool)) :
    (shiftOptPath o).isSome = o.isSome := by
  cases o <;> rfl

private theorem shiftPathBool_snd (o : Option (List Bool × Bool)) :
    o.map Prod.snd = (shiftPathBool o).map Prod.snd := by
  cases o <;> rfl

private def tmplSummaryFrom (fi fa : Bool) (fap : Option Bool) : Fin 8 :=
  let idle := bitNat fi
  let c4 := match fap with
    | some false => 2
    | some true  => 3
    | none => bitNat fa
  fin8 (4 * idle + c4)

private theorem tmplSummaryCode_eq_from (ts : TemplateScan) :
    tmplSummaryCode ts =
      tmplSummaryFrom ts.firstIdle.isSome ts.firstArmed.isSome (ts.firstAppending.map Prod.snd) := by
  unfold tmplSummaryCode tmplSummaryFrom
  cases ts.firstAppending with
  | none => rfl
  | some p => rcases p with ⟨_, b⟩; cases b <;> rfl

private theorem tmplSummaryCode_frame (tVer rest j : Term) :
    tmplCode ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j)) =
      stepTmplSummary (decodeVer3 (ver3Code tVer)) (tmplCode rest) := by
  have hv3 := ver3Code_spec tVer
  have hfin : ∀ (v3 : Fin 9) (fi fa : Bool) (fap : Option Bool),
      let b := tmplSummaryFrom fi fa fap
      let newSummary := match decodeVer3 v3 with
        | some [false, false, _]  => tmplSummaryFrom true fa fap
        | some [true, false, _]   => tmplSummaryFrom fi true fap
        | some [true, true, sbit] => tmplSummaryFrom fi fa (some sbit)
        | _                       => tmplSummaryFrom fi fa fap
      newSummary = stepTmplSummary (decodeVer3 v3) b := by
    intro v3 fi fa fap
    cases fap with
    | none => revert v3 fi fa; decide
    | some sb => revert v3 fi fa sb; decide
  unfold tmplCode
  change tmplSummaryCode (scanTemplates ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j))) =
    stepTmplSummary (decodeVer3 (ver3Code tVer)) (tmplSummaryCode (scanTemplates rest))
  rw [tmplSummaryCode_eq_from, tmplSummaryCode_eq_from (scanTemplates rest),
      ← hfin (ver3Code tVer) (scanTemplates rest).firstIdle.isSome
          (scanTemplates rest).firstArmed.isSome ((scanTemplates rest).firstAppending.map Prod.snd)]
  simp only [scanTemplates]
  rw [hv3]
  cases hdv : decodeVer3 (ver3Code tVer) with
  | none =>
      repeat' first | rw [shiftPathBool_isSome] | rw [← shiftPathBool_snd]
      try rfl
  | some bits =>
      have hlen3 : bits.length = 3 := by
        have hall : ∀ q : Fin 9, ∀ bs, decodeVer3 q = some bs → bs.length = 3 := by decide
        exact hall (ver3Code tVer) bits hdv
      rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | _⟩⟩⟩ <;> try cases hlen3
      cases b0 <;> cases b1 <;> cases b2 <;>
      · dsimp only []
        repeat' first | rw [shiftPathBool_isSome] | rw [← shiftPathBool_snd]
        try rfl

private def stepQueueSummary (v3 : Option (List Bool)) (b : Fin 12) : Fin 12 :=
  let cons0 := b.val ≥ 9
  let rem := if cons0 then b.val - 9 else b.val
  let unc0 := if cons0 then 0 else rem / 3
  let su0 := rem % 3
  match v3 with
  | none =>
      let su := if su0 == 0 then 1 else su0
      fin12 (if cons0 then 9 + su else 3 * unc0 + su)
  | some [false, true, _] =>
      fin12 (if cons0 then 9 + 2 else 3 * unc0 + 2)
  | some [false, false, sbit] =>
      let unc := if cons0 then 0 else (1 + bitNat sbit)
      fin12 (if cons0 then 9 + su0 else 3 * unc + su0)
  | some [true, false, _] =>
      fin12 (9 + su0)
  | _ =>
      fin12 (if cons0 then 9 + su0 else 3 * unc0 + su0)

private theorem pocketAppBU_queue_coherent :
    ∀ (a : Fin 9) (b : Fin 12),
      pocketAppBU 6 (fin23 (7 + a.val)) (fin23 (7 + b.val)) =
        fin23 (stepQueueSummary (decodeVer3 a) b).val := by
  decide

private def queueSummaryFrom (co st ui : Bool) (unc : Option Bool) : Fin 12 :=
  let su := if st then 2 else if ui then 1 else 0
  if co then fin12 (9 + su)
  else
    let u := match unc with
      | none => 0
      | some false => 1
      | some true  => 2
    fin12 (3 * u + su)

private theorem queueSummaryCode_eq_from (qs : QueueScan) :
    queueSummaryCode qs =
      queueSummaryFrom qs.consuming.isSome qs.staging.isSome qs.uninit.isSome
        (qs.unconsumed.map Prod.snd) := by
  unfold queueSummaryCode queueSummaryFrom
  cases qs.consuming with
  | some _ => rfl
  | none =>
      cases qs.unconsumed with
      | none => rfl
      | some p => rcases p with ⟨_, b⟩; cases b <;> rfl

private theorem queueSummaryCode_frame (qVer rest j : Term) :
    queueCode ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j)) =
      stepQueueSummary (decodeVer3 (ver3Code qVer)) (queueCode rest) := by
  have hv3 := ver3Code_spec qVer
  have hfin : ∀ (v3 : Fin 9) (co st ui : Bool) (unc : Option Bool),
      let b := queueSummaryFrom co st ui unc
      let newSummary := match decodeVer3 v3 with
        | none                    => queueSummaryFrom co st true unc
        | some [false, true, _]   => queueSummaryFrom co true ui unc
        | some [false, false, sb] => queueSummaryFrom co st ui (some sb)
        | some [true, false, _]   => queueSummaryFrom true st ui unc
        | _                       => queueSummaryFrom co st ui unc
      newSummary = stepQueueSummary (decodeVer3 v3) b := by
    intro v3 co st ui unc
    cases unc with
    | none => revert v3 co st ui; decide
    | some sb => revert v3 co st ui sb; decide
  unfold queueCode
  change queueSummaryCode (scanQueue ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))) =
    stepQueueSummary (decodeVer3 (ver3Code qVer)) (queueSummaryCode (scanQueue rest))
  rw [queueSummaryCode_eq_from, queueSummaryCode_eq_from (scanQueue rest),
      ← hfin (ver3Code qVer) (scanQueue rest).consuming.isSome (scanQueue rest).staging.isSome
          (scanQueue rest).uninit.isSome ((scanQueue rest).unconsumed.map Prod.snd)]
  simp only [scanQueue]
  rw [hv3]
  cases hdv : decodeVer3 (ver3Code qVer) with
  | none =>
      dsimp only []
      repeat' first | rw [shiftPathBool_isSome] | rw [shiftOptPath_isSome] | rw [← shiftPathBool_snd]
      try rfl
  | some bits =>
      have hlen3 : bits.length = 3 := by
        have hall : ∀ q : Fin 9, ∀ bs, decodeVer3 q = some bs → bs.length = 3 := by decide
        exact hall (ver3Code qVer) bits hdv
      rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | _⟩⟩⟩ <;> try cases hlen3
      cases b0 <;> cases b1 <;> cases b2 <;>
      · dsimp only []
        repeat' first | rw [shiftPathBool_isSome] | rw [shiftOptPath_isSome] | rw [← shiftPathBool_snd]
        try rfl

private theorem findIdxPred_map_shift (pred : Option (List Bool) → Bool) (ps : List PhaseEntry) :
    findIdxPred (fun pe => pred pe.status) (ps.map shiftPhaseEntry) =
      (findIdxPred (fun pe => pred pe.status) ps).map (fun ie => (ie.1, shiftPhaseEntry ie.2)) := by
  induction ps with
  | nil => rfl
  | cons x xs ih =>
      change (if pred x.status then some (0, shiftPhaseEntry x)
        else (findIdxPred (fun pe => pred pe.status) (xs.map shiftPhaseEntry)).map (fun iy => (iy.1 + 1, iy.2))) =
        (if pred x.status then some (0, x)
        else (findIdxPred (fun pe => pred pe.status) xs).map (fun iy => (iy.1 + 1, iy.2))).map
          (fun ie => (ie.1, shiftPhaseEntry ie.2))
      cases pred x.status with
      | true => rfl
      | false =>
          rw [ih]
          cases findIdxPred (fun pe => pred pe.status) xs <;> rfl

private theorem phasesSummaryCode_map_shift (ps : List PhaseEntry) :
    phasesSummaryCode (ps.map shiftPhaseEntry) = phasesSummaryCode ps := by
  cases ps with
  | nil => rfl
  | cons e0 es =>
      unfold phasesSummaryCode
      simp only [List.map_cons]
      have hst0 : (shiftPhaseEntry e0).status = e0.status := rfl
      rw [hst0]
      have hh := findIdxPred_map_shift (· == some [true, true]) (e0 :: es)
      have ha := findIdxPred_map_shift (· == some [true, false]) (e0 :: es)
      simp only [List.map_cons] at hh ha
      rw [hh]
      cases findIdxPred (fun pe => pe.status == some [true, true]) (e0 :: es) with
      | some pair =>
          simp only [Option.map, List.length_cons, List.length_map]
      | none =>
          rw [ha]
          cases findIdxPred (fun pe => pe.status == some [true, false]) (e0 :: es) with
          | none => rfl
          | some pair =>
              rcases pair with ⟨_, actE⟩
              simp only [Option.map, shiftPhaseEntry]

private theorem phasesSummaryCode_range (ps : List PhaseEntry) :
    (ps = [] ↔ phasesSummaryCode ps = 0) ∧
    ((findIdxPred (fun pe => pe.status == some [true, true]) ps).isSome = true ↔
      1 ≤ (phasesSummaryCode ps).val ∧ (phasesSummaryCode ps).val ≤ 4) ∧
    ((findIdxPred (fun pe => pe.status == some [true, true]) ps = none ∧
      findIdxPred (fun pe => pe.status == some [true, false]) ps = none ∧ ps ≠ []) ↔
      phasesSummaryCode ps = 5) ∧
    ((findIdxPred (fun pe => pe.status == some [true, true]) ps = none ∧
      (findIdxPred (fun pe => pe.status == some [true, false]) ps).isSome = true) ↔
      6 ≤ (phasesSummaryCode ps).val) := by
  cases ps with
  | nil =>
      unfold phasesSummaryCode findIdxPred
      decide
  | cons e0 es =>
      unfold phasesSummaryCode
      cases hh : findIdxPred (fun pe => pe.status == some [true, true]) (e0 :: es) with
      | some pair =>
          rcases pair with ⟨hIdx, _⟩
          have h14 : ∀ (b1 b2 : Bool),
              let c := fin22 (1 + 2 * bitNat b1 + bitNat b2)
              c ≠ 0 ∧ (1 ≤ c.val ∧ c.val ≤ 4) ∧ c ≠ 5 ∧ ¬ (6 ≤ c.val) := by decide
          obtain ⟨hc0, hc14, hc5, hc6⟩ :=
            h14 (e0.status == some [true, false]) (hIdx + 1 == (e0 :: es).length)
          refine ⟨⟨fun h => (by cases h), fun h => False.elim (hc0 h)⟩,
                  ⟨fun _ => hc14, fun _ => rfl⟩,
                  ⟨fun ⟨h, _, _⟩ => (by cases h), fun h => False.elim (hc5 h)⟩,
                  ⟨fun ⟨h, _⟩ => (by cases h), fun h => False.elim (hc6 h)⟩⟩
      | none =>
          cases ha : findIdxPred (fun pe => pe.status == some [true, false]) (e0 :: es) with
          | none =>
              have h5 : (5 : Fin 22) ≠ 0 ∧ ¬ (1 ≤ (5 : Fin 22).val ∧ (5 : Fin 22).val ≤ 4) ∧
                  ¬ (6 ≤ (5 : Fin 22).val) := by decide
              refine ⟨⟨fun h => (by cases h), fun h => False.elim (h5.1 h)⟩,
                      ⟨fun h => (by cases h), fun h => False.elim (h5.2.1 h)⟩,
                      ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, fun h => (by cases h)⟩⟩,
                      ⟨fun ⟨_, h⟩ => (by cases h), fun h => False.elim (h5.2.2 h)⟩⟩
          | some pair =>
              rcases pair with ⟨_, actE⟩
              have h6 : ∀ (b1 : Bool) (t : Fin 8),
                  let c := fin22 (6 + 8 * bitNat b1 + t.val)
                  c ≠ 0 ∧ ¬ (1 ≤ c.val ∧ c.val ≤ 4) ∧ c ≠ 5 ∧ 6 ≤ c.val := by decide
              obtain ⟨hc0, hc14, hc5, hc6⟩ :=
                h6 (e0.status == some [true, false]) (tmplSummaryCode actE.templates)
              refine ⟨⟨fun h => (by cases h), fun h => False.elim (hc0 h)⟩,
                      ⟨fun h => (by cases h), fun h => False.elim (hc14 h)⟩,
                      ⟨fun ⟨_, h, _⟩ => (by cases h), fun h => False.elim (hc5 h)⟩,
                      ⟨fun _ => hc6, fun _ => ⟨rfl, rfl⟩⟩⟩

private theorem nat_beq_eq_true {a b : Nat} (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

private theorem nat_beq_eq_false {a b : Nat} (h : (a == b) = false) : a ≠ b :=
  of_decide_eq_false h

private theorem nat_beq_of_eq {a b : Nat} (h : a = b) : (a == b) = true :=
  decide_eq_true h

private theorem nat_beq_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false :=
  decide_eq_false h

private theorem progRing_step_eq (pVer tList jb rest jr : Term) :
    fin23 (progRingCode (((.s ⋅ ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))) ⋅ ((.s ⋅ rest) ⋅ jr)))).val =
      pocketAppBU 3
        (fin23 (7 + (bodyCode ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))).val))
        (fin23 (1 + (progRingCode rest).val)) := by
  let e0 : PhaseEntry :=
    { verPath := [false, true, false, true]
      tListPath := [false, true, true, false, true]
      status := pfScanVersion 2 none pVer
      templates := scanTemplates tList }
  have hps_code : phasesSummaryCode ((scanPhases rest).map shiftPhaseEntry) = progRingCode rest :=
    phasesSummaryCode_map_shift (scanPhases rest)
  have hscan_top : scanPhases (((.s ⋅ ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))) ⋅ ((.s ⋅ rest) ⋅ jr))) =
      e0 :: (scanPhases rest).map shiftPhaseEntry := rfl
  have hv2 := ver2Code_spec pVer
  have hfin_v2 : ∀ (vc : Fin 4),
      ((vc.val == 1) = (vc == 1)) ∧
      ((vc.val == 2) = (vc == 2)) ∧
      ((vc.val == 1) = true → (vc.val == 2) = false) := by decide
  have hv2_1 : ((ver2Code pVer).val == 1) = (e0.status == some [true, true]) :=
    (hfin_v2 (ver2Code pVer)).1.trans hv2.2.1.symm
  have hv2_2 : ((ver2Code pVer).val == 2) = (e0.status == some [true, false]) :=
    (hfin_v2 (ver2Code pVer)).2.1.trans hv2.2.2.symm
  have hbody_def : bodyCode ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)) =
      (if (ver2Code pVer).val == 1 then 1
       else if (ver2Code pVer).val == 2 then fin11 (3 + (tmplSummaryCode e0.templates).val)
       else 2) := rfl
  unfold progRingCode at hps_code ⊢
  rw [hscan_top, ← hps_code]
  generalize (scanPhases rest).map shiftPhaseEntry = ps
  have hrange := phasesSummaryCode_range ps
  cases hh_e0 : (e0.status == some [true, true]) with
  | true =>
      have hvc1 : ((ver2Code pVer).val == 1) = true := hv2_1.trans hh_e0
      have hvc_ne2 : ((ver2Code pVer).val == 2) = false := (hfin_v2 (ver2Code pVer)).2.2 hvc1
      have hnot_act : (e0.status == some [true, false]) = false := hv2_2.symm.trans hvc_ne2
      have hbd1 : (bodyCode ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))).val = 1 := by
        rw [hbody_def, hvc1]; rfl
      conv => lhs; unfold phasesSummaryCode; dsimp only []
      rw [hnot_act]
      simp only [findIdxPred, hh_e0, ↓reduceIte, bitNat, Bool.false_eq_true]
      cases ps with
      | nil =>
          have hlen1 : (if (0 + 1 == [e0].length) = true then 1 else 0) = 1 := rfl
          have hpsc0 : (phasesSummaryCode []).val = 0 := rfl
          rw [hlen1, hbd1, hpsc0]
          decide
      | cons e1 es1 =>
          have hne0 : (phasesSummaryCode (e1 :: es1)).val ≠ 0 := by
            intro h0; have h := hrange.1.mpr (Fin.ext h0); cases h
          have hlen0 : (if (0 + 1 == (e0 :: e1 :: es1).length) = true then 1 else 0) = 0 := rfl
          rw [hlen0, hbd1]
          have hfin : ∀ (psc : Fin 22), psc.val ≠ 0 →
              fin23 (fin22 (1 + 2 * 0 + 0)).val =
                pocketAppBU 3 (fin23 (7 + 1)) (fin23 (1 + psc.val)) := by decide
          exact hfin (phasesSummaryCode (e1 :: es1)) hne0
  | false =>
      have hvc_ne1 : ((ver2Code pVer).val == 1) = false := hv2_1.trans hh_e0
      cases ha_e0 : (e0.status == some [true, false]) with
      | true =>
          have hvc2 : ((ver2Code pVer).val == 2) = true := hv2_2.trans ha_e0
          have hbd_eq : (bodyCode ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))).val =
              3 + (tmplSummaryCode e0.templates).val := by
            rw [hbody_def, hvc_ne1, hvc2]
            simp only [Bool.false_eq_true, ↓reduceIte, fin11]
            have ht8 := (tmplSummaryCode e0.templates).isLt
            have hlt11 : 3 + (tmplSummaryCode e0.templates).val < 11 := by omega
            simp [hlt11]
          conv => lhs; unfold phasesSummaryCode; dsimp only []
          rw [ha_e0]
          simp only [findIdxPred, hh_e0, ha_e0, Bool.false_eq_true, ↓reduceIte, bitNat]
          cases hh_ps : findIdxPred (fun pe => pe.status == some [true, true]) ps with
          | some pair =>
              rcases pair with ⟨hIdx, hE⟩
              simp only [Option.map]
              have hlen_eq : (if (hIdx + 1 + 1 == (e0 :: ps).length) = true then 1 else 0) =
                  bitNat (hIdx + 1 == ps.length) := by
                have hbeq : (hIdx + 1 + 1 == (e0 :: ps).length) = (hIdx + 1 == ps.length) := by
                  simp only [List.length_cons]
                  cases h1 : (hIdx + 1 == ps.length) with
                  | true => have he := nat_beq_eq_true h1; exact nat_beq_of_eq (by omega)
                  | false => have hne := nat_beq_eq_false h1; exact nat_beq_of_ne (by omega)
                unfold bitNat
                rw [hbeq]
              rw [hlen_eq, hbd_eq]
              cases ps with
              | nil => cases hh_ps
              | cons e1 es1 =>
                  have hps_val : (phasesSummaryCode (e1 :: es1)).val =
                      1 + 2 * bitNat (e1.status == some [true, false]) + bitNat (hIdx + 1 == (e1 :: es1).length) := by
                    unfold phasesSummaryCode
                    dsimp only []
                    rw [hh_ps]
                    dsimp only []
                    cases (e1.status == some [true, false]) <;> cases (hIdx + 1 == (e1 :: es1).length) <;> rfl
                  have hfin : ∀ (t : Fin 8) (fa1 hl : Bool),
                      fin23 (fin22 (1 + 2 * 1 + bitNat hl)).val =
                        pocketAppBU 3 (fin23 (7 + (3 + t.val)))
                          (fin23 (1 + (1 + 2 * bitNat fa1 + bitNat hl))) := by decide
                  rw [hps_val]
                  exact hfin (tmplSummaryCode e0.templates) (e1.status == some [true, false])
                    (hIdx + 1 == (e1 :: es1).length)
          | none =>
              simp only [Option.map]
              have hnot14 : ¬ (1 ≤ (phasesSummaryCode ps).val ∧ (phasesSummaryCode ps).val ≤ 4) := by
                intro h14
                have hsome := hrange.2.1.mpr h14
                rw [hh_ps] at hsome; cases hsome
              rw [hbd_eq]
              have hfin : ∀ (t : Fin 8) (rest : Fin 22),
                  (¬ (1 ≤ rest.val ∧ rest.val ≤ 4)) →
                  fin23 (fin22 (6 + 8 * 1 + t.val)).val =
                    pocketAppBU 3 (fin23 (7 + (3 + t.val))) (fin23 (1 + rest.val)) := by decide
              exact hfin (tmplSummaryCode e0.templates) (phasesSummaryCode ps) hnot14
      | false =>
          have hvc_ne2 : ((ver2Code pVer).val == 2) = false := hv2_2.trans ha_e0
          have hbd2 : (bodyCode ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))).val = 2 := by
            rw [hbody_def, hvc_ne1, hvc_ne2]; rfl
          conv => lhs; unfold phasesSummaryCode; dsimp only []
          rw [ha_e0]
          simp only [findIdxPred, hh_e0, ha_e0, Bool.false_eq_true, ↓reduceIte, bitNat]
          cases hh_ps : findIdxPred (fun pe => pe.status == some [true, true]) ps with
          | some pair =>
              rcases pair with ⟨hIdx, hE⟩
              simp only [Option.map]
              have hlen_eq : (if (hIdx + 1 + 1 == (e0 :: ps).length) = true then 1 else 0) =
                  bitNat (hIdx + 1 == ps.length) := by
                have hbeq : (hIdx + 1 + 1 == (e0 :: ps).length) = (hIdx + 1 == ps.length) := by
                  simp only [List.length_cons]
                  cases h1 : (hIdx + 1 == ps.length) with
                  | true => have he := nat_beq_eq_true h1; exact nat_beq_of_eq (by omega)
                  | false => have hne := nat_beq_eq_false h1; exact nat_beq_of_ne (by omega)
                unfold bitNat
                rw [hbeq]
              rw [hlen_eq, hbd2]
              cases ps with
              | nil => cases hh_ps
              | cons e1 es1 =>
                  have hps_val : (phasesSummaryCode (e1 :: es1)).val =
                       1 + 2 * bitNat (e1.status == some [true, false]) + bitNat (hIdx + 1 == (e1 :: es1).length) := by
                    unfold phasesSummaryCode
                    dsimp only []
                    rw [hh_ps]
                    dsimp only []
                    cases (e1.status == some [true, false]) <;> cases (hIdx + 1 == (e1 :: es1).length) <;> rfl
                  have hfin : ∀ (fa1 hl : Bool),
                      fin23 (fin22 (1 + 2 * 0 + bitNat hl)).val =
                        pocketAppBU 3 (fin23 (7 + 2))
                          (fin23 (1 + (1 + 2 * bitNat fa1 + bitNat hl))) := by decide
                  rw [hps_val]
                  exact hfin (e1.status == some [true, false]) (hIdx + 1 == (e1 :: es1).length)
          | none =>
              simp only [Option.map]
              rw [hbd2]
              cases ha_ps : findIdxPred (fun pe => pe.status == some [true, false]) ps with
              | none =>
                  have hps_0_or_5 : (phasesSummaryCode ps).val = 0 ∨ (phasesSummaryCode ps).val = 5 := by
                    cases ps with
                    | nil => exact Or.inl rfl
                    | cons e1 es1 =>
                        have h5 := hrange.2.2.1.mp ⟨hh_ps, ha_ps, fun h => (by cases h)⟩
                        exact Or.inr (congrArg Fin.val h5)
                  rcases hps_0_or_5 with h0 | h5
                  · rw [h0]; decide
                  · rw [h5]; decide
              | some pair =>
                  rcases pair with ⟨aIdx, actE⟩
                  cases ps with
                  | nil => cases ha_ps
                  | cons e1 es1 =>
                      have hps_val : (phasesSummaryCode (e1 :: es1)).val =
                          6 + 8 * bitNat (e1.status == some [true, false]) +
                            (tmplSummaryCode actE.templates).val := by
                        unfold phasesSummaryCode
                        dsimp only []
                        rw [hh_ps, ha_ps]
                        have hfin2 : ∀ (t : Fin 8) (fa1 : Bool),
                            (fin22 (6 + 8 * bitNat fa1 + t.val)).val = 6 + 8 * bitNat fa1 + t.val := by decide
                        exact hfin2 (tmplSummaryCode actE.templates) (e1.status == some [true, false])
                      have hfin : ∀ (t : Fin 8) (fa1 : Bool),
                          fin23 (fin22 (6 + 8 * 0 + t.val)).val =
                            pocketAppBU 3 (fin23 (7 + 2))
                              (fin23 (1 + (6 + 8 * bitNat fa1 + t.val))) := by decide
                      rw [hps_val]
                      exact hfin (tmplSummaryCode actE.templates) (e1.status == some [true, false])

private theorem flag_or_arity_le15 (x : Term) :
    (if flagValue x then 6 else arityFuel 5 x) ≤ 15 := by
  have har := arityFuel_le 5 x
  cases flagValue x <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

private theorem parseFrame_eq_none_cases {u : Term} (hpf : parseFrame u = none) :
    payloadCode u = 0 ∧ bodyCode u = 0 ∧ tmplCode u = 0 ∧ queueCode u = 0 ∧
    fieldsCode u = 0 ∧ progRingCode u = 0 ∧
    scanTemplates u = ⟨none, none, none⟩ ∧
    scanQueue u = ⟨none, none, none, none, []⟩ := by
  have hp : payloadCode u = 0 := by
    unfold payloadCode; split
    · cases hpf
    · rfl
  have hb : bodyCode u = 0 := by
    unfold bodyCode; split
    · cases hpf
    · rfl
  have hf : fieldsCode u = 0 := by
    unfold fieldsCode; split
    · cases hpf
    · rfl
  have hpr : progRingCode u = 0 := by
    unfold progRingCode scanPhases; split
    · cases hpf
    · rfl
  have hst : scanTemplates u = ⟨none, none, none⟩ := by
    unfold scanTemplates; split
    · cases hpf
    · rfl
  have hsq : scanQueue u = ⟨none, none, none, none, []⟩ := by
    unfold scanQueue; split
    · cases hpf
    · rfl
  have ht : tmplCode u = 0 := by unfold tmplCode; rw [hst]; rfl
  have hq : queueCode u = 0 := by unfold queueCode; rw [hsq]; rfl
  exact ⟨hp, hb, ht, hq, hf, hpr, hst, hsq⟩

private theorem progRingCode_of_parseFrame_none {u : Term} (hpf : parseFrame u = none) :
    progRingCode u = 0 :=
  (parseFrame_eq_none_cases hpf).2.2.2.2.2.1

private theorem progRingCode_of_body_none {body rest jr : Term} (hpfb : parseFrame body = none) :
    progRingCode ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) = 0 := by
  rcases body with _ | _ | ⟨_ | _ | ⟨_ | _ | _, pVer⟩, _ | _ | ⟨_ | _ | ⟨_ | _ | _, tList⟩, jb⟩⟩ <;>
    cases hpfb <;> rfl

private theorem pocketAppBU_zero_cases :
    (∀ ql qr : Fin 23, qr.val < 7 → pocketAppBU 2 ql qr = 0) ∧
    (∀ ql qr : Fin 23, ql.val < 7 → pocketAppBU 3 ql qr = 0) ∧
    (∀ ql : Fin 23, pocketAppBU 3 ql 0 = 0) ∧
    (∀ qr : Fin 23, pocketAppBU 3 7 qr = 0) ∧
    (∀ ql qr : Fin 23, ql.val < 7 → pocketAppBU 4 ql qr = 0) ∧
    (∀ ql qr : Fin 23, qr.val < 7 → pocketAppBU 4 ql qr = 0) ∧
    (∀ ql qr : Fin 23, ql.val < 7 → pocketAppBU 5 ql qr = 0) ∧
    (∀ ql qr : Fin 23, qr.val < 7 → pocketAppBU 5 ql qr = 0) ∧
    (∀ ql qr : Fin 23, ql.val < 7 → pocketAppBU 6 ql qr = 0) ∧
    (∀ ql qr : Fin 23, qr.val < 7 → pocketAppBU 6 ql qr = 0) ∧
    (∀ ql qr : Fin 23, ql.val < 7 → pocketAppBU 7 ql qr = 0) ∧
    (∀ ql qr : Fin 23, qr.val < 7 → pocketAppBU 7 ql qr = 0) ∧
    (∀ ql qr : Fin 23, ql.val < 7 → pocketAppBU 8 ql qr = 0) ∧
    (∀ ql qr : Fin 23, qr.val < 7 → pocketAppBU 8 ql qr = 0) ∧
    (∀ ql qr : Fin 23, ql.val < 7 → pocketAppBU 9 ql qr = 0) ∧
    (∀ ql qr : Fin 23, qr.val < 7 → pocketAppBU 9 ql qr = 0) := by
  decide

set_option maxHeartbeats 800000 in

/-- **Master Pass-1 Characterization Theorem (`annotate_state_eq_specBU`)**:
    On **every** closed pure-`S` tree `t` and **every** role `r : Fin 25`, Pass 1 of
    `pocketPFTransducer` computes the exact specification state `specBU r t`! -/
theorem annotate_state_eq_specBU :
    ∀ (t : Term), isClosedPureS t = true →
      ∀ (r : Fin 25), (pocketPFTransducer.annotate r t).1.state = specBU r t := by
  intro t ht role
  induction t generalizing role with
  | s =>
      revert role
      decide
  | var _ => cases ht
  | app l r ihl_ind ihr_ind =>
      have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp ht).1
      have hr : isClosedPureS r = true := ((Bool.and_eq_true _ _).mp ht).2
      have ihl := ihl_ind hl (pocketChildRoles role).1
      have ihr := ihr_ind hr (pocketChildRoles role).2
      change pocketAppBU role (pocketPFTransducer.annotate (pocketChildRoles role).1 l).1.state
          (pocketPFTransducer.annotate (pocketChildRoles role).2 r).1.state = specBU role (l ⋅ r)
      rw [ihl, ihr]
      clear ihl ihr ihl_ind ihr_ind
      -- Generic helper for `11..19` (except `13`):
      have hs1_gen : ∀ (rv : Fin 25) (rIn : Fin 25) (v : Term → Nat)
          (hv : ∀ x, v x ≤ 15)
          (hcr : pocketChildRoles rv = (10, rIn))
          (hrIn : ∀ u, (specBU rIn u).val = v u)
          (hrv_spec : ∀ u, specBU rv u = match u with | .app .s x => fin23 (7 + v x) | _ => fin23 (arityFuel 5 u))
          (hpock : ∀ ql qr : Fin 23, pocketAppBU rv ql qr =
            if pocketSpLeft ql == 0 then fin23 (7 + qr.val) else fin23 (min 5 (pocketSpLeft ql + 1))),
          pocketAppBU rv (specBU (pocketChildRoles rv).1 l) (specBU (pocketChildRoles rv).2 r) =
            specBU rv (l ⋅ r) := by
        intro rv rIn v _ hcr hrIn hrv_spec hpock
        rw [hcr, hpock, pocketSpLeft_spine, hrIn r, hrv_spec (l ⋅ r)]
        cases l with
        | s => rfl
        | var _ => cases hl
        | app ll lr =>
            have hne0 : (arityFuel 5 (ll ⋅ lr) == 0) = false :=
              nat_beq_of_ne (fun h0 => by cases (closed_arityFuel_zero_iff hl).mp h0)
            have hmatch : (match (ll ⋅ lr) ⋅ r with
                | .s ⋅ x => fin23 (7 + v x)
                | u => fin23 (arityFuel 5 u)) = fin23 (arityFuel 5 ((ll ⋅ lr) ⋅ r)) := rfl
            rw [if_neg (by rw [hne0]; decide), hmatch, arityFuel5_app ((ll ⋅ lr)) r]
      -- Generic helper for `20..24` (except `21`):
      have hs2_gen : ∀ (rv : Fin 25) (s1R : Fin 25) (v : Term → Nat)
          (hv : ∀ x, v x ≤ 15)
          (hcr : pocketChildRoles rv = (s1R, 10))
          (hs1_spec : ∀ u, specBU s1R u = match u with | .app .s x => fin23 (7 + v x) | _ => fin23 (arityFuel 5 u))
          (hrv_spec : ∀ u, specBU rv u = match u with | .app (.app .s x) _ => fin23 (7 + v x) | _ => fin23 (arityFuel 5 u))
          (hpock : ∀ ql qr : Fin 23, pocketAppBU rv ql qr =
            if ql.val ≥ 7 then ql else fin23 (min 5 (pocketSpLeft ql + 1))),
          pocketAppBU rv (specBU (pocketChildRoles rv).1 l) (specBU (pocketChildRoles rv).2 r) =
            specBU rv (l ⋅ r) := by
        intro rv s1R v hv hcr hs1_spec hrv_spec hpock
        rw [hcr, hpock, hs1_spec l, hrv_spec (l ⋅ r)]
        cases l with
        | s => rfl
        | var _ => cases hl
        | app ll lr =>
            cases ll with
            | s =>
                have hlt23 : 7 + v lr < 23 := by have h := hv lr; omega
                have hge7 : (fin23 (7 + v lr)).val ≥ 7 := by rw [fin23_val_of_lt hlt23]; omega
                rw [if_pos hge7]
            | var _ =>
                have hll : isClosedPureS (.var _) = true := ((Bool.and_eq_true _ _).mp hl).1
                cases hll
            | app lll llr =>
                have har := arityFuel_le 5 ((lll ⋅ llr) ⋅ lr)
                have hlt23 : arityFuel 5 ((lll ⋅ llr) ⋅ lr) < 23 := by omega
                have hlt7 : ¬ ((fin23 (arityFuel 5 ((lll ⋅ llr) ⋅ lr))).val ≥ 7) := by
                  rw [fin23_val_of_lt hlt23]; omega
                rw [if_neg hlt7]
                have hsp := s1Open_spLeft_helper (t := (lll ⋅ llr) ⋅ lr) v hv
                dsimp only [] at hsp
                rw [hsp, ← arityFuel5_app (((lll ⋅ llr) ⋅ lr)) r]
      -- Dispatch on `role.val` (`0..24`):
      rcases role with ⟨rv, hrv_lt⟩
      match rv with
      | 0 => rfl
      | 1 =>
          change pocketAppBU 1 (specBU 11 l) (specBU 20 r) = (if haltObserved (l ⋅ r) then 1 else 0)
          rw [pf_haltObserved_eq_s1f_s2 l r]
          have hl13 : ((specBU 11 l).val == 13) = pfIsS1FTerm l := by
            simp only [specBU]
            cases l with
            | s => rfl
            | var _ => cases hl
            | app ll lr =>
                cases ll with
                | s =>
                    simp only [pfIsS1FTerm]
                    cases hf : flagValue lr with
                    | true => rfl
                    | false =>
                        have har := arityFuel_le 5 lr
                        have hlt23 : 7 + arityFuel 5 lr < 23 := by omega
                        simp only [Bool.false_eq_true, ↓reduceIte, fin23_val_of_lt hlt23]
                        exact nat_beq_of_ne (by omega)
                | var _ =>
                    have hll : isClosedPureS (.var _) = true := ((Bool.and_eq_true _ _).mp hl).1
                    cases hll
                | app lll llr =>
                    have har := arityFuel_le 5 ((lll ⋅ llr) ⋅ lr)
                    have hlt23 : arityFuel 5 ((lll ⋅ llr) ⋅ lr) < 23 := by omega
                    simp only [pfIsS1FTerm, fin23_val_of_lt hlt23]
                    exact nat_beq_of_ne (by omega)
          have hr7 : decide ((specBU 20 r).val ≥ 7) = pfIsS2Shape r := by
            have hge := s2Open_ge7_iff (t := r) (fun x => (payloadCode x).val)
              (fun x => Nat.le_trans (Nat.le_of_lt_succ (payloadCode x).isLt) (by decide))
            simp only [specBU]
            cases hs2 : pfIsS2Shape r with
            | true =>
                unfold pfIsS2Shape at hs2
                split at hs2
                · rename_i x j
                  exact decide_eq_true (hge.mpr ⟨x, j, rfl⟩)
                · cases hs2
            | false =>
                refine decide_eq_false (fun hbad => ?_)
                obtain ⟨x, j, rfl⟩ := hge.mp hbad
                cases hs2
          change (if ((specBU 11 l).val == 13 && decide ((specBU 20 r).val ≥ 7)) = true then (1 : Fin 23) else 0) =
            (if (pfIsS1FTerm l && pfIsS2Shape r) = true then 1 else 0)
          rw [hl13, hr7]
      | 10 =>
          change (if (specBU 10 l).val == 1 && pocketSpRight (specBU 10 r) == 2 then 6
            else fin23 (min 5 (pocketSpLeft (specBU 10 l) + 1))) = specBU 10 (l ⋅ r)
          have hspR := pocketSpRight_spine (t := r)
          have hspL := pocketSpLeft_spine (t := l)
          have hl1 : ((specBU 10 l).val == 1) = pfIsS1Term l := by
            simp only [specBU]
            cases hf : flagValue l with
            | true =>
                have hnot1 : pfIsS1Term l = false := by
                  unfold flagValue parseFrame at hf
                  split at hf
                  · rfl
                  · cases hf
                rw [hnot1]; rfl
            | false =>
                have har := arityFuel_le 5 l
                have hlt23 : arityFuel 5 l < 23 := by omega
                simp only [Bool.false_eq_true, ↓reduceIte, fin23_val_of_lt hlt23]
                cases hs1 : pfIsS1Term l with
                | true => exact nat_beq_of_eq ((closed_isS1_iff_arity5 hl).mp hs1)
                | false =>
                    exact nat_beq_of_ne (fun h1 => by
                      rw [(closed_isS1_iff_arity5 hl).mpr h1] at hs1; cases hs1)
          have hr2 : (pocketSpRight (specBU 10 r) == 2) = pfIsS2Shape r := by
            rw [hspR]
            cases hs2 : pfIsS2Shape r with
            | true => exact nat_beq_of_eq ((closed_isS2_iff_arity5 hr).mp hs2)
            | false =>
                exact nat_beq_of_ne (fun h2 => by
                  rw [(closed_isS2_iff_arity5 hr).mpr h2] at hs2; cases hs2)
          rw [hl1, hr2, ← pf_flagValue_eq_s1_s2 l r, hspL, ← arityFuel5_app l r]
          simp only [specBU]
      | 13 =>
          change (if pocketSpLeft (specBU 10 l) == 0 then fin23 (1 + (specBU 3 r).val) else 0) =
            specBU 13 (l ⋅ r)
          rw [pocketSpLeft_spine]
          have hlt23 : (progRingCode r).val < 23 := by have h := (progRingCode r).isLt; omega
          simp only [specBU, fin23_val_of_lt hlt23]
          cases l with
          | s => rfl
          | var _ => cases hl
          | app ll lr =>
              have hne0 : (arityFuel 5 (ll ⋅ lr) == 0) = false :=
                nat_beq_of_ne (fun h0 => by cases (closed_arityFuel_zero_iff hl).mp h0)
              rw [if_neg (by rw [hne0]; decide)]
      | 21 =>
          change (if (specBU 13 l).val ≥ 1 then specBU 13 l else 0) = specBU 21 (l ⋅ r)
          simp only [specBU]
          cases l with
          | s => rfl
          | var _ => cases hl
          | app ll lr =>
              cases ll with
              | s =>
                  have hlt23 : 1 + (progRingCode lr).val < 23 := by
                    have h := (progRingCode lr).isLt; omega
                  have hge1 : (fin23 (1 + (progRingCode lr).val)).val ≥ 1 := by
                    rw [fin23_val_of_lt hlt23]; omega
                  rw [if_pos hge1]
              | var _ =>
                  have hll : isClosedPureS (.var _) = true := ((Bool.and_eq_true _ _).mp hl).1
                  cases hll
              | app _ _ => rfl
      | 11 =>
          exact hs1_gen 11 10 (fun x => if flagValue x then 6 else arityFuel 5 x)
            flag_or_arity_le15
            rfl
            (fun u => by
              simp only [specBU]
              cases flagValue u with
              | true => rfl
              | false =>
                  have hlt : arityFuel 5 u < 23 := Nat.lt_of_le_of_lt (arityFuel_le 5 u) (by decide)
                  exact fin23_val_of_lt hlt)
            (fun _ => rfl) (fun _ _ => rfl)
      | 12 =>
          exact hs1_gen 12 2 (fun x => (payloadCode x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (payloadCode x).isLt (by decide)))
            rfl (fun u => fin23_val_of_lt (Nat.lt_of_lt_of_le (payloadCode u).isLt (by decide)))
            (fun _ => rfl) (fun _ _ => rfl)
      | 14 =>
          exact hs1_gen 14 4 (fun x => (bodyCode x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (bodyCode x).isLt (by decide)))
            rfl (fun u => fin23_val_of_lt (Nat.lt_of_lt_of_le (bodyCode u).isLt (by decide)))
            (fun _ => rfl) (fun _ _ => rfl)
      | 15 =>
          exact hs1_gen 15 5 (fun x => (tmplCode x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (tmplCode x).isLt (by decide)))
            rfl (fun u => fin23_val_of_lt (Nat.lt_of_lt_of_le (tmplCode u).isLt (by decide)))
            (fun _ => rfl) (fun _ _ => rfl)
      | 16 =>
          exact hs1_gen 16 6 (fun x => (queueCode x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (queueCode x).isLt (by decide)))
            rfl (fun u => fin23_val_of_lt (Nat.lt_of_lt_of_le (queueCode u).isLt (by decide)))
            (fun _ => rfl) (fun _ _ => rfl)
      | 17 =>
          exact hs1_gen 17 7 (fun x => (ver2Code x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver2Code x).isLt (by decide)))
            rfl (fun u => fin23_val_of_lt (Nat.lt_of_lt_of_le (ver2Code u).isLt (by decide)))
            (fun _ => rfl) (fun _ _ => rfl)
      | 18 =>
          exact hs1_gen 18 8 (fun x => (ver3Code x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver3Code x).isLt (by decide)))
            rfl (fun u => fin23_val_of_lt (Nat.lt_of_lt_of_le (ver3Code u).isLt (by decide)))
            (fun _ => rfl) (fun _ _ => rfl)
      | 19 =>
          exact hs1_gen 19 9 (fun x => (fieldsCode x).val)
            (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)
            rfl (fun u => fin23_val_of_lt (Nat.lt_of_lt_of_le (fieldsCode u).isLt (by decide)))
            (fun _ => rfl) (fun _ _ => rfl)
      | 20 =>
          exact hs2_gen 20 12 (fun x => (payloadCode x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (payloadCode x).isLt (by decide)))
            rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      | 22 =>
          exact hs2_gen 22 15 (fun x => (tmplCode x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (tmplCode x).isLt (by decide)))
            rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      | 23 =>
          exact hs2_gen 23 16 (fun x => (queueCode x).val)
            (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (queueCode x).isLt (by decide)))
            rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      | 24 =>
          exact hs2_gen 24 19 (fun x => (fieldsCode x).val)
            (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)
            rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      | 2 =>
          change pocketAppBU 2 (specBU 13 l) (specBU 23 r) = fin23 (payloadCode (l ⋅ r)).val
          cases hpf : parseFrame (l ⋅ r) with
          | none =>
              have hpc : payloadCode (l ⋅ r) = 0 := (parseFrame_eq_none_cases hpf).1
              rw [hpc]
              cases l with
              | s => rfl
              | var _ => cases hl
              | app ll progRing =>
                  cases ll with
                  | s =>
                      have hnot_s2 : ¬ ∃ qRoot j, r = (.s ⋅ qRoot) ⋅ j := by
                        rintro ⟨qRoot, j, rfl⟩; cases hpf
                      have hn7 := mt (s2Open_ge7_iff (t := r) (fun x => (queueCode x).val)
                        (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (queueCode x).isLt (by decide)))).mp hnot_s2
                      have hlt7 : (specBU 23 r).val < 7 := Nat.lt_of_not_le hn7
                      exact pocketAppBU_zero_cases.1 _ _ hlt7
                  | var _ =>
                      have hll : isClosedPureS (.var _) = true := ((Bool.and_eq_true _ _).mp hl).1
                      cases hll
                  | app _ _ => rfl
          | some triple =>
              rcases triple with ⟨progRing, queueRoot, j⟩
              obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
              injection heq with hl_eq hr_eq
              subst hl_eq; subst hr_eq
              exact pocketAppBU_payload_coherent (progRingCode progRing) (queueCode queueRoot)
      | 3 =>
          change pocketAppBU 3 (specBU 14 l) (specBU 21 r) = fin23 (progRingCode (l ⋅ r)).val
          cases hpf : parseFrame (l ⋅ r) with
          | none =>
              rw [progRingCode_of_parseFrame_none hpf]
              have hl_v : ∀ x, (bodyCode x).val ≤ 15 :=
                fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (bodyCode x).isLt (by decide))
              cases hge7 : decide ((specBU 14 l).val ≥ 7) with
              | false =>
                  have hlt7 : (specBU 14 l).val < 7 := Nat.lt_of_not_le (of_decide_eq_false hge7)
                  exact pocketAppBU_zero_cases.2.1 _ _ hlt7
              | true =>
                  obtain ⟨body, rfl⟩ := (s1Open_ge7_iff _ hl_v).mp (of_decide_eq_true hge7)
                  have hr0 : specBU 21 r = 0 := by
                    rcases r with _ | _ | ⟨_ | _ | ⟨_ | _ | _, rest⟩, jr⟩ <;> cases hpf <;> rfl
                  rw [hr0]
                  exact pocketAppBU_zero_cases.2.2.1 _
          | some triple =>
              rcases triple with ⟨body, rest, jr⟩
              obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
              injection heq with hl_eq hr_eq
              subst hl_eq; subst hr_eq
              cases hpfb : parseFrame body with
              | none =>
                  have hbc0 : bodyCode body = 0 := (parseFrame_eq_none_cases hpfb).2.1
                  rw [progRingCode_of_body_none hpfb]
                  have hql7 : specBU 14 (.s ⋅ body) = 7 := by
                    change fin23 (7 + (bodyCode body).val) = 7; rw [hbc0]; rfl
                  rw [hql7]
                  exact pocketAppBU_zero_cases.2.2.2.1 _
              | some btriple =>
                  rcases btriple with ⟨pVer, tList, jb⟩
                  obtain ⟨hbeq, _, _⟩ := parseFrame_some_decomp hpfb
                  subst hbeq
                  exact (progRing_step_eq pVer tList jb rest jr).symm
      | 4 =>
          change pocketAppBU 4 (specBU 17 l) (specBU 22 r) = fin23 (bodyCode (l ⋅ r)).val
          cases hpf : parseFrame (l ⋅ r) with
          | none =>
              have hbc0 : bodyCode (l ⋅ r) = 0 := (parseFrame_eq_none_cases hpf).2.1
              rw [hbc0]
              cases hge7 : decide ((specBU 17 l).val ≥ 7) with
              | false =>
                  have hlt7 : (specBU 17 l).val < 7 := Nat.lt_of_not_le (of_decide_eq_false hge7)
                  exact pocketAppBU_zero_cases.2.2.2.2.1 _ _ hlt7
              | true =>
                  obtain ⟨pVer, rfl⟩ := (s1Open_ge7_iff (fun x => (ver2Code x).val)
                    (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver2Code x).isLt (by decide)))).mp
                    (of_decide_eq_true hge7)
                  have hnot_s2 : ¬ ∃ tList j, r = (.s ⋅ tList) ⋅ j := by
                    rintro ⟨tList, j, rfl⟩; cases hpf
                  have hlt7 : (specBU 22 r).val < 7 := Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                    (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (tmplCode x).isLt (by decide)))).mp hnot_s2)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.1 _ _ hlt7
          | some triple =>
              rcases triple with ⟨pVer, tList, jb⟩
              obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
              injection heq with hl_eq hr_eq
              subst hl_eq; subst hr_eq
              simp only [specBU]
              rw [pocketAppBU_body_coherent (ver2Code pVer) (tmplCode tList)]
              dsimp only [bodyCode]
              have hfin : ∀ (vc : Fin 4) (tc : Fin 8),
                  (if vc.val == 1 then (1 : Fin 23)
                   else if vc.val == 2 then fin23 (3 + tc.val) else 2) =
                  fin23 (if vc.val == 1 then (1 : Fin 11)
                         else if vc.val == 2 then fin11 (3 + tc.val) else 2).val := by decide
              exact hfin (ver2Code pVer) (tmplCode tList)
      | 5 =>
          change pocketAppBU 5 (specBU 18 l) (specBU 22 r) = fin23 (tmplCode (l ⋅ r)).val
          cases hpf : parseFrame (l ⋅ r) with
          | none =>
              have htc0 : tmplCode (l ⋅ r) = 0 := (parseFrame_eq_none_cases hpf).2.2.1
              rw [htc0]
              cases hge7 : decide ((specBU 18 l).val ≥ 7) with
              | false =>
                  have hlt7 : (specBU 18 l).val < 7 := Nat.lt_of_not_le (of_decide_eq_false hge7)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.1 _ _ hlt7
              | true =>
                  obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => (ver3Code x).val)
                    (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver3Code x).isLt (by decide)))).mp
                    (of_decide_eq_true hge7)
                  have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                    rintro ⟨sub, j, rfl⟩; cases hpf
                  have hlt7 : (specBU 22 r).val < 7 := Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                    (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (tmplCode x).isLt (by decide)))).mp hnot_s2)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.1 _ _ hlt7
          | some triple =>
              rcases triple with ⟨tVer, rest, j⟩
              obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
              injection heq with hl_eq hr_eq
              subst hl_eq; subst hr_eq
              rw [tmplSummaryCode_frame tVer rest j]
              exact pocketAppBU_tmpl_coherent (ver3Code tVer) (tmplCode rest)
      | 6 =>
          change pocketAppBU 6 (specBU 18 l) (specBU 23 r) = fin23 (queueCode (l ⋅ r)).val
          cases hpf : parseFrame (l ⋅ r) with
          | none =>
              have hqc0 : queueCode (l ⋅ r) = 0 := (parseFrame_eq_none_cases hpf).2.2.2.1
              rw [hqc0]
              cases hge7 : decide ((specBU 18 l).val ≥ 7) with
              | false =>
                  have hlt7 : (specBU 18 l).val < 7 := Nat.lt_of_not_le (of_decide_eq_false hge7)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.2.1 _ _ hlt7
              | true =>
                  obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => (ver3Code x).val)
                    (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver3Code x).isLt (by decide)))).mp
                    (of_decide_eq_true hge7)
                  have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                    rintro ⟨sub, j, rfl⟩; cases hpf
                  have hlt7 : (specBU 23 r).val < 7 := Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                    (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (queueCode x).isLt (by decide)))).mp hnot_s2)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.2.2.1 _ _ hlt7
          | some triple =>
              rcases triple with ⟨qVer, rest, j⟩
              obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
              injection heq with hl_eq hr_eq
              subst hl_eq; subst hr_eq
              rw [queueSummaryCode_frame qVer rest j]
              exact pocketAppBU_queue_coherent (ver3Code qVer) (queueCode rest)
      | 7 =>
          change pocketAppBU 7 (specBU 17 l) (specBU 24 r) = fin23 (ver2Code (l ⋅ r)).val
          cases hpf : parseFrame (l ⋅ r) with
          | none =>
              have hvc0 : ver2Code (l ⋅ r) = 0 := by
                unfold ver2Code; rw [pfScanVersion_closed 2 none _ hpf]
              rw [hvc0]
              cases hge7 : decide ((specBU 17 l).val ≥ 7) with
              | false =>
                  have hlt7 : (specBU 17 l).val < 7 := Nat.lt_of_not_le (of_decide_eq_false hge7)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.2.2.2.1 _ _ hlt7
              | true =>
                  obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => (ver2Code x).val)
                    (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver2Code x).isLt (by decide)))).mp
                    (of_decide_eq_true hge7)
                  have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                    rintro ⟨sub, j, rfl⟩; cases hpf
                  have hlt7 : (specBU 24 r).val < 7 := Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                    (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)).mp hnot_s2)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.2.2.2.2.1 _ _ hlt7
          | some triple =>
              rcases triple with ⟨next, fields, j⟩
              obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
              injection heq with hl_eq hr_eq
              subst hl_eq; subst hr_eq
              simp only [specBU]
              rw [pocketAppBU_ver2_coherent (ver2Code next) (fieldsCode fields)]
              -- Relate RHS to `ver2Code (frameTerm next fields j)`:
              have hscan : pfScanVersion 2 none ((.s ⋅ next) ⋅ ((.s ⋅ fields) ⋅ j)) =
                  match pfScanVersion 2 none next with
                  | some res => some res
                  | none => readFields 2 fields := by
                change pfScanVersion 2 (match readFields 2 fields with | none => none | some b => some b) next = _
                rw [pfScanVersion_acc 2 next]
                cases pfScanVersion 2 none next <;> cases readFields 2 fields <;> rfl
              unfold ver2Code
              rw [hscan, (fieldsCode_spec fields).2.2.1]
              cases hsn : pfScanVersion 2 none next with
              | none =>
                  generalize fieldsCode fields = fc
                  revert fc; decide
              | some bits =>
                  have hlen := pfScanVersion_length 2 next hsn
                  rcases bits with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> try cases hlen
                  cases b0 <;> cases b1 <;> rfl
      | 8 =>
          change pocketAppBU 8 (specBU 18 l) (specBU 24 r) = fin23 (ver3Code (l ⋅ r)).val
          cases hpf : parseFrame (l ⋅ r) with
          | none =>
              have hvc0 : ver3Code (l ⋅ r) = 0 := by
                unfold ver3Code; rw [pfScanVersion_closed 3 none _ hpf]
              rw [hvc0]
              cases hge7 : decide ((specBU 18 l).val ≥ 7) with
              | false =>
                  have hlt7 : (specBU 18 l).val < 7 := Nat.lt_of_not_le (of_decide_eq_false hge7)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.2.2.2.2.2.1 _ _ hlt7
              | true =>
                  obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => (ver3Code x).val)
                    (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver3Code x).isLt (by decide)))).mp
                    (of_decide_eq_true hge7)
                  have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                    rintro ⟨sub, j, rfl⟩; cases hpf
                  have hlt7 : (specBU 24 r).val < 7 := Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                    (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)).mp hnot_s2)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ _ hlt7
          | some triple =>
              rcases triple with ⟨next, fields, j⟩
              obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
              injection heq with hl_eq hr_eq
              subst hl_eq; subst hr_eq
              simp only [specBU]
              rw [pocketAppBU_ver3_coherent (ver3Code next) (fieldsCode fields)]
              have hscan : pfScanVersion 3 none ((.s ⋅ next) ⋅ ((.s ⋅ fields) ⋅ j)) =
                  match pfScanVersion 3 none next with
                  | some res => some res
                  | none => readFields 3 fields := by
                change pfScanVersion 3 (match readFields 3 fields with | none => none | some b => some b) next = _
                rw [pfScanVersion_acc 3 next]
                cases pfScanVersion 3 none next <;> cases readFields 3 fields <;> rfl
              unfold ver3Code
              rw [hscan, (fieldsCode_spec fields).2.2.2]
              cases hsn : pfScanVersion 3 none next with
              | none =>
                  generalize fieldsCode fields = fc
                  revert fc; decide
              | some bits =>
                  have hlen := pfScanVersion_length 3 next hsn
                  rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | _⟩⟩⟩ <;> try cases hlen
                  cases b0 <;> cases b1 <;> cases b2 <;> rfl
      | 9 =>
          change pocketAppBU 9 (specBU 11 l) (specBU 24 r) = fin23 (fieldsCode (l ⋅ r)).val
          cases hpf : parseFrame (l ⋅ r) with
          | none =>
              have hfc0 : fieldsCode (l ⋅ r) = 0 := (parseFrame_eq_none_cases hpf).2.2.2.2.1
              rw [hfc0]
              cases hge7 : decide ((specBU 11 l).val ≥ 7) with
              | false =>
                  have hlt7 : (specBU 11 l).val < 7 := Nat.lt_of_not_le (of_decide_eq_false hge7)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ _ hlt7
              | true =>
                  obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => if flagValue x then 6 else arityFuel 5 x)
                    flag_or_arity_le15).mp
                    (of_decide_eq_true hge7)
                  have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                    rintro ⟨sub, j, rfl⟩; cases hpf
                  have hlt7 : (specBU 24 r).val < 7 := Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                    (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)).mp hnot_s2)
                  exact pocketAppBU_zero_cases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ _ hlt7
          | some triple =>
              rcases triple with ⟨fl, rest, j⟩
              obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
              injection heq with hl_eq hr_eq
              subst hl_eq; subst hr_eq
              have hfc_top : fieldsCode ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) =
                  combFields (flagValue fl) (fieldsCode rest) := rfl
              rw [hfc_top]
              simp only [specBU]
              cases hfl : flagValue fl with
              | true =>
                  exact (pocketAppBU_fields_coherent true (fieldsCode rest)).1
              | false =>
                  have har := arityFuel_le 5 fl
                  exact (pocketAppBU_fields_coherent false (fieldsCode rest)).2 ⟨arityFuel 5 fl, by omega⟩
      | _ + 25 => exact False.elim (by omega)

/-- **Root Halting Equivalence (`pocketPF_acceptHalt_eq_pfRootHalt`)**:
    On every closed pure-`S` tree `t`, `pocketPFTransducer` accepts at the root iff `pfRootHalt t = true`! -/
theorem pocketPF_acceptHalt_eq_pfRootHalt {t : Term} (ht : isClosedPureS t = true) :
    pocketPFTransducer.acceptHalt (pocketPFTransducer.annotate 0 t).1.state = pfRootHalt t := by
  rw [annotate_state_eq_specBU t ht 0]
  simp only [pocketPFTransducer, specBU]
  cases pfRootHalt t <;> rfl


/-! ## Section 4: Exact Pass-2 Characterization (`locateRedex = pfSelectAddress`) -/

private def ann (r : Fin 25) (t : Term) : AnnotTree (Fin 23) :=
  (pocketPFTransducer.annotate r t).1

private def loc (p : Fin 136) (a : AnnotTree (Fin 23)) : Option (List Bool) :=
  (pocketPFTransducer.locateRedex p a).1

private theorem ann_app (r : Fin 25) (l rt : Term) :
    ann r (l ⋅ rt) =
      .app (pocketAppBU r (ann (pocketChildRoles r).1 l).state (ann (pocketChildRoles r).2 rt).state)
        (ann (pocketChildRoles r).1 l) (ann (pocketChildRoles r).2 rt) := rfl

private theorem loc_ann_app (p : Fin 136) (r : Fin 25) (l rt : Term) :
    loc p (ann r (l ⋅ rt)) =
      match pocketStepTD p (ann (pocketChildRoles r).1 l).state (ann (pocketChildRoles r).2 rt).state with
      | .goLeft p'    => (loc p' (ann (pocketChildRoles r).1 l)).map (false :: ·)
      | .goRight p'   => (loc p' (ann (pocketChildRoles r).2 rt)).map (true :: ·)
      | .contractHere => some []
      | .stuck        => none := by
  conv => lhs; rw [ann_app]; unfold loc PocketTreeTransducer.locateRedex
  dsimp only [pocketPFTransducer]
  cases pocketStepTD p (ann (pocketChildRoles r).1 l).state (ann (pocketChildRoles r).2 rt).state <;> rfl

private theorem ann_state_eq {r : Fin 25} {t : Term} (ht : isClosedPureS t = true) :
    (ann r t).state = specBU r t :=
  annotate_state_eq_specBU t ht r

private theorem ann_state_eq_expl (t : Term) (ht : isClosedPureS t = true) {r : Fin 25} :
    (ann r t).state = specBU r t :=
  annotate_state_eq_specBU t ht r

private theorem pfSelectOpeningAt_nil (t : Term) :
    pfSelectOpeningAt t [] = nextOpeningAddress t := by
  unfold pfSelectOpeningAt
  rw [term_at_nil]
  dsimp only [Bind.bind, Option.bind]
  cases nextOpeningAddress t with
  | none => rfl
  | some rel => simp

private theorem pfSelectOpeningAt_append (root : Term) (p1 p2 : List Bool) :
    pfSelectOpeningAt root (p1 ++ p2) =
      (termAt root p1).bind (fun sub => (pfSelectOpeningAt sub p2).map (p1 ++ ·)) := by
  unfold pfSelectOpeningAt
  rw [pf_termAt_append root p1 p2]
  cases termAt root p1 with
  | none => rfl
  | some sub =>
      dsimp only [ Bind.bind, Option.bind ]
      cases termAt sub p2 with
      | none => rfl
      | some foc =>
          dsimp only []
          cases nextOpeningAddress foc with
          | none => rfl
          | some rel => simp [Option.map, List.append_assoc]

private theorem pfSelectVersionWriteAt_nil (t : Term) (w : Nat) (d : List Bool) :
    pfSelectVersionWriteAt t [] w d =
      (chooseSVersionTree w d t).bind (pfSelectOpeningAt t) := by
  unfold pfSelectVersionWriteAt
  rw [term_at_nil]
  dsimp only [Bind.bind, Option.bind]
  cases chooseSVersionTree w d t <;> rfl

private theorem pfSelectVersionWriteAt_shift (root : Term) (p1 p2 : List Bool) (w : Nat) (d : List Bool) :
    pfSelectVersionWriteAt root (p1 ++ p2) w d =
      (termAt root p1).bind (fun sub => (pfSelectVersionWriteAt sub p2 w d).map (p1 ++ ·)) := by
  unfold pfSelectVersionWriteAt
  rw [pf_termAt_append root p1 p2]
  cases ht1 : termAt root p1 with
  | none => rfl
  | some sub =>
      dsimp only [Bind.bind, Option.bind]
      cases ht2 : termAt sub p2 with
      | none => rfl
      | some verTerm =>
          dsimp only []
          cases hch : chooseSVersionTree w d verTerm with
          | none => rfl
          | some slot =>
              dsimp only []
              rw [List.append_assoc p1 p2 slot, pfSelectOpeningAt_append root p1 (p2 ++ slot), ht1]
              rfl

set_option maxHeartbeats 800000

private theorem pfSelectOpeningAt_left_nil (root : Term) :
    pfSelectOpeningAt root [false, true] =
      (termAt root [false, true]).bind (fun sub => (pfSelectOpeningAt sub []).map ([false, true] ++ ·)) :=
  pfSelectOpeningAt_append root [false, true] []

private theorem pfSelectOpeningAt_flag_nil (root : Term) :
    pfSelectOpeningAt root pfFlagPath =
      (termAt root [true, false, true]).bind (fun sub => (pfSelectOpeningAt sub []).map ([true, false, true] ++ ·)) :=
  pfSelectOpeningAt_append root [true, false, true] []

private theorem pfSelectVersionWriteAt_left_nil (root : Term) (w : Nat) (d : List Bool) :
    pfSelectVersionWriteAt root [false, true] w d =
      (termAt root [false, true]).bind (fun sub => (pfSelectVersionWriteAt sub [] w d).map ([false, true] ++ ·)) :=
  pfSelectVersionWriteAt_shift root [false, true] [] w d

private theorem pfSelectVersionWriteAt_pfLeft_nil (root : Term) (w : Nat) (d : List Bool) :
    pfSelectVersionWriteAt root pfLeftChildPath w d =
      (termAt root pfLeftChildPath).bind (fun sub => (pfSelectVersionWriteAt sub [] w d).map (pfLeftChildPath ++ ·)) :=
  pfSelectVersionWriteAt_shift root pfLeftChildPath [] w d

private theorem pfSelectVersionWriteAt_left2 (root : Term) (w : Nat) (d : List Bool) :
    pfSelectVersionWriteAt root [false, true, false, true] w d =
      (termAt root pfLeftChildPath).bind (fun sub => (pfSelectVersionWriteAt sub [false, true] w d).map (pfLeftChildPath ++ ·)) :=
  pfSelectVersionWriteAt_shift root pfLeftChildPath [false, true] w d

private def frameParentRole (rl rr : Fin 25) : Fin 25 :=
  match rl.val, rr.val with
  | 11, 20 => 1
  | 13, 23 => 2
  | 14, 21 => 3
  | 17, 22 => 4
  | 18, 22 => 5
  | 18, 23 => 6
  | 17, 24 => 7
  | 18, 24 => 8
  | 11, 24 => 9
  | _, _   => 0

private theorem frameParentRole_11_20 : frameParentRole 11 20 = 1 := rfl
private theorem frameParentRole_13_23 : frameParentRole 13 23 = 2 := rfl
private theorem frameParentRole_14_21 : frameParentRole 14 21 = 3 := rfl
private theorem frameParentRole_17_22 : frameParentRole 17 22 = 4 := rfl
private theorem frameParentRole_18_22 : frameParentRole 18 22 = 5 := rfl
private theorem frameParentRole_18_23 : frameParentRole 18 23 = 6 := rfl
private theorem frameParentRole_17_24 : frameParentRole 17 24 = 7 := rfl
private theorem frameParentRole_18_24 : frameParentRole 18 24 = 8 := rfl
private theorem frameParentRole_11_24 : frameParentRole 11 24 = 9 := rfl

private theorem loc_goFL {p : Fin 136} {c : Nat} (hc : c < 50)
    {rl rr : Fin 25} {tl tr : Term}
    (hstep : pocketStepTD p (ann rl (.s ⋅ tl)).state (ann rr tr).state = pocketGoFL c)
    (hcr : pocketChildRoles (frameParentRole rl rr) = (rl, rr) := by decide) :
    loc p (ann (frameParentRole rl rr) ((.s ⋅ tl) ⋅ tr)) =
      (loc (fin136 c) (ann (pocketChildRoles rl).2 tl)).map (pfLeftChildPath ++ ·) := by
  have hcr1 : (pocketChildRoles (frameParentRole rl rr)).1 = rl := congrArg Prod.fst hcr
  have hcr2 : (pocketChildRoles (frameParentRole rl rr)).2 = rr := congrArg Prod.snd hcr
  have h54_lt : 54 + c < 136 := by omega
  have h54_not104 : ¬ (54 + c ≥ 104) := by omega
  have h54_ge54 : 54 + c ≥ 54 := by omega
  have hsub54 : (54 + c) - 54 = c := by omega
  rw [loc_ann_app, hcr1, hcr2, hstep]
  dsimp only [pocketGoFL]
  rw [loc_ann_app]
  have hstep2 : pocketStepTD (fin136 (54 + c))
      (ann (pocketChildRoles rl).1 .s).state
      (ann (pocketChildRoles rl).2 tl).state =
      .goRight (fin136 c) := by
    unfold pocketStepTD
    have hv : (fin136 (54 + c)).val = 54 + c := by simp [fin136, h54_lt]
    rw [hv, if_neg h54_not104, if_pos h54_ge54, hsub54]
  rw [hstep2]
  dsimp only []
  cases loc (fin136 c) (ann (pocketChildRoles rl).2 tl) <;> rfl

private theorem loc_goFR {p : Fin 136} {c : Nat} (hc : c < 32)
    {rl rr : Fin 25} {tl tr tj : Term}
    (hstep : pocketStepTD p (ann rl tl).state
      (ann rr ((.s ⋅ tr) ⋅ tj)).state = pocketGoFR c)
    (hcr : pocketChildRoles (frameParentRole rl rr) = (rl, rr) := by decide) :
    loc p (ann (frameParentRole rl rr) (tl ⋅ ((.s ⋅ tr) ⋅ tj))) =
      (loc (fin136 c)
        (ann (pocketChildRoles (pocketChildRoles rr).1).2 tr)).map
          (pfRightChildPath ++ ·) := by
  have hcr1 : (pocketChildRoles (frameParentRole rl rr)).1 = rl := congrArg Prod.fst hcr
  have hcr2 : (pocketChildRoles (frameParentRole rl rr)).2 = rr := congrArg Prod.snd hcr
  have h104_lt : 104 + c < 136 := by omega
  have h104_ge : 104 + c ≥ 104 := by omega
  have hsub50 : (104 + c) - 50 = 54 + c := by omega
  have h54_lt : 54 + c < 136 := by omega
  have h54_not104 : ¬ (54 + c ≥ 104) := by omega
  have h54_ge54 : 54 + c ≥ 54 := by omega
  have hsub54 : (54 + c) - 54 = c := by omega
  rw [loc_ann_app, hcr1, hcr2, hstep]
  dsimp only [pocketGoFR]
  rw [loc_ann_app]
  have hstep2 : pocketStepTD (fin136 (104 + c))
      (ann (pocketChildRoles rr).1 (.s ⋅ tr)).state
      (ann (pocketChildRoles rr).2 tj).state =
      .goLeft (fin136 (54 + c)) := by
    unfold pocketStepTD
    have hv : (fin136 (104 + c)).val = 104 + c := by simp [fin136, h104_lt]
    rw [hv, if_pos h104_ge, hsub50]
  rw [hstep2]
  dsimp only []
  rw [loc_ann_app]
  have hstep3 : pocketStepTD (fin136 (54 + c))
      (ann (pocketChildRoles (pocketChildRoles rr).1).1 .s).state
      (ann (pocketChildRoles (pocketChildRoles rr).1).2 tr).state =
      .goRight (fin136 c) := by
    unfold pocketStepTD
    have hv : (fin136 (54 + c)).val = 54 + c := by simp [fin136, h54_lt]
    rw [hv, if_neg h54_not104, if_pos h54_ge54, hsub54]
  rw [hstep3]
  dsimp only []
  cases loc (fin136 c)
    (ann (pocketChildRoles (pocketChildRoles rr).1).2 tr) <;> rfl

local macro "rw_goFL" hc:term:max hstep:term:max : tactic =>
  `(tactic| (have h_fl := loc_goFL $hc $hstep
             simp only [frameParentRole_11_20, frameParentRole_13_23, frameParentRole_14_21,
               frameParentRole_17_22, frameParentRole_18_22, frameParentRole_18_23,
               frameParentRole_17_24, frameParentRole_18_24, frameParentRole_11_24] at h_fl
             try dsimp only [] at h_fl
             try (conv => lhs; dsimp only [])
             rw [h_fl]
             clear h_fl))

local macro "rw_goFR" hc:term:max hstep:term:max : tactic =>
  `(tactic| (have h_fr := loc_goFR $hc $hstep
             simp only [frameParentRole_11_20, frameParentRole_13_23, frameParentRole_14_21,
               frameParentRole_17_22, frameParentRole_18_22, frameParentRole_18_23,
               frameParentRole_17_24, frameParentRole_18_24, frameParentRole_11_24] at h_fr
             try dsimp only [] at h_fr
             try (conv => lhs; dsimp only [])
             rw [h_fr]
             clear h_fr))

/-! ### 4.1 Correctness of `OPEN` (`p = 1`), `LEFT_CONTRACT` (`p = 52`), and `CONTRACT_NOW` (`p = 53`) -/

private def isOpenSpLeftRole (r : Fin 25) : Bool :=
  r.val == 10 || r.val == 11 || r.val == 16 || r.val == 17 || r.val == 18 || r.val == 19

private def isOpenSpRightRole (r : Fin 25) : Bool :=
  r.val == 10 || r.val == 23 || r.val == 24

private theorem openSpLeftRole_props {r : Fin 25} (hr : isOpenSpLeftRole r = true) :
    (pocketChildRoles r).1 = 10 ∧
    ∀ u : Term, pocketSpLeft (specBU r u) = arityFuel 5 u := by
  refine ⟨?_, ?_⟩
  · revert r hr; decide
  · intro u
    rcases r with ⟨rv, hlt⟩
    match rv with
    | 10 => exact pocketSpLeft_spine
    | 11 =>
        exact s1Open_spLeft_helper (fun x => if flagValue x then 6 else arityFuel 5 x)
          flag_or_arity_le15
    | 16 =>
        exact s1Open_spLeft_helper (fun x => (queueCode x).val)
          (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (queueCode x).isLt (by decide)))
    | 17 =>
        exact s1Open_spLeft_helper (fun x => (ver2Code x).val)
          (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver2Code x).isLt (by decide)))
    | 18 =>
        exact s1Open_spLeft_helper (fun x => (ver3Code x).val)
          (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver3Code x).isLt (by decide)))
    | 19 =>
        exact s1Open_spLeft_helper (fun x => (fieldsCode x).val)
          (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 12 | 13 | 14 | 15 | 20 | 21 | 22 | 23 | 24 =>
        cases hr
    | _ + 25 => omega

private theorem openSpRightRole_props {r : Fin 25} (hr : isOpenSpRightRole r = true) :
    isOpenSpLeftRole (pocketChildRoles r).1 = true ∧
    ∀ u : Term, pocketSpRight (specBU r u) = arityFuel 5 u := by
  refine ⟨?_, ?_⟩
  · revert r hr; decide
  · intro u
    rcases r with ⟨rv, hlt⟩
    match rv with
    | 10 => exact pocketSpRight_spine
    | 23 =>
        exact s2Open_spRight_helper (fun x => (queueCode x).val)
          (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (queueCode x).isLt (by decide)))
    | 24 =>
        exact s2Open_spRight_helper (fun x => (fieldsCode x).val)
          (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 =>
        cases hr
    | _ + 25 => omega

private theorem loc_53_eq {r : Fin 25} (hrl : isOpenSpLeftRole (pocketChildRoles r).1 = true)
    {u : Term} (hu : isClosedPureS u = true) :
    loc 53 (ann r u) = if arityFuel 5 u == 3 then some [] else none := by
  cases u with
  | s => rfl
  | var _ => cases hu
  | app ul ur =>
      have hul : isClosedPureS ul = true := ((Bool.and_eq_true _ _).mp hu).1
      have hsp := (openSpLeftRole_props hrl).2 ul
      rw [loc_ann_app, ann_state_eq hul]
      have hstep : pocketStepTD 53 (specBU (pocketChildRoles r).1 ul)
          (ann (pocketChildRoles r).2 ur).state =
          if arityFuel 5 ul == 2 then .contractHere else .stuck := by
        unfold pocketStepTD
        dsimp only []
        rw [hsp]
        rfl
      rw [hstep, arityFuel5_app]
      have har := arityFuel_le 5 ul
      have heq32 : (min 5 (arityFuel 5 ul + 1) == 3) = (arityFuel 5 ul == 2) := by
        cases h2 : (arityFuel 5 ul == 2) with
        | true => have hv := nat_beq_eq_true h2; rw [hv]; rfl
        | false => have hne := nat_beq_eq_false h2; exact nat_beq_of_ne (by omega)
      rw [heq32]
      cases (arityFuel 5 ul == 2) <;> rfl

private theorem loc_52_eq {r : Fin 25} (hrr : isOpenSpRightRole r = true)
    {u : Term} (hu : isClosedPureS u = true) :
    loc 52 (ann r u) = if arityFuel 5 u == 4 then some [false] else none := by
  have hrl := (openSpRightRole_props hrr).1
  cases u with
  | s => rfl
  | var _ => cases hu
  | app ul ur =>
      have hul : isClosedPureS ul = true := ((Bool.and_eq_true _ _).mp hu).1
      have hsp := (openSpLeftRole_props hrl).2 ul
      have hc10 := (openSpLeftRole_props hrl).1
      have hrl_ul : isOpenSpLeftRole (pocketChildRoles (pocketChildRoles r).1).1 = true := by
        rw [hc10]; rfl
      have h53 := loc_53_eq hrl_ul hul
      rw [loc_ann_app, ann_state_eq hul]
      have hstep : pocketStepTD 52 (specBU (pocketChildRoles r).1 ul)
          (ann (pocketChildRoles r).2 ur).state =
          if arityFuel 5 ul == 3 then .goLeft 53 else .stuck := by
        unfold pocketStepTD
        dsimp only []
        rw [hsp]
        rfl
      rw [hstep, arityFuel5_app]
      have har := arityFuel_le 5 ul
      have heq43 : (min 5 (arityFuel 5 ul + 1) == 4) = (arityFuel 5 ul == 3) := by
        cases h3 : (arityFuel 5 ul == 3) with
        | true => have hv := nat_beq_eq_true h3; rw [hv]; rfl
        | false => have hne := nat_beq_eq_false h3; exact nat_beq_of_ne (by omega)
      rw [heq43]
      cases h3 : (arityFuel 5 ul == 3) with
      | false => rfl
      | true =>
          simp only [↓reduceIte]
          rw [h53, h3]
          rfl

private theorem loc_stepOpen_eq {p : Fin 136} {r : Fin 25}
    (hrl : isOpenSpLeftRole (pocketChildRoles r).1 = true)
    (hrr : isOpenSpRightRole (pocketChildRoles r).2 = true)
    {l rt : Term} (hl : isClosedPureS l = true) (hrt : isClosedPureS rt = true)
    (hopen : pocketStepTD p (specBU (pocketChildRoles r).1 l) (specBU (pocketChildRoles r).2 rt) =
      pocketStepOpen (specBU (pocketChildRoles r).1 l) (specBU (pocketChildRoles r).2 rt)) :
    loc p (ann r (l ⋅ rt)) = nextOpeningAddress (l ⋅ rt) := by
  have hspL := (openSpLeftRole_props hrl).2 l
  have hspR := (openSpRightRole_props hrr).2 rt
  have hrl_l : isOpenSpLeftRole (pocketChildRoles (pocketChildRoles r).1).1 = true := by
    rw [(openSpLeftRole_props hrl).1]; rfl
  have hrl_r : isOpenSpLeftRole (pocketChildRoles (pocketChildRoles r).2).1 = true :=
    (openSpRightRole_props hrr).1
  rw [loc_ann_app, ann_state_eq hl, ann_state_eq hrt, hopen]
  unfold pocketStepOpen nextOpeningAddress
  dsimp only []
  rw [hspL, hspR]
  have hflag_eq : (arityFuel 5 l == 1 && arityFuel 5 rt == 2) = (parseFrame (l ⋅ rt)).isSome := by
    change (arityFuel 5 l == 1 && arityFuel 5 rt == 2) = flagValue (l ⋅ rt)
    rw [pf_flagValue_eq_s1_s2 l rt]
    have h1 : (arityFuel 5 l == 1) = pfIsS1Term l := by
      cases hs1 : pfIsS1Term l with
      | true => exact nat_beq_of_eq ((closed_isS1_iff_arity5 hl).mp hs1)
      | false => exact nat_beq_of_ne (fun h => by rw [(closed_isS1_iff_arity5 hl).mpr h] at hs1; cases hs1)
    have h2 : (arityFuel 5 rt == 2) = pfIsS2Shape rt := by
      cases hs2 : pfIsS2Shape rt with
      | true => exact nat_beq_of_eq ((closed_isS2_iff_arity5 hrt).mp hs2)
      | false => exact nat_beq_of_ne (fun h => by rw [(closed_isS2_iff_arity5 hrt).mpr h] at hs2; cases hs2)
    rw [h1, h2]
  rw [hflag_eq]
  cases hpf : (parseFrame (l ⋅ rt)).isSome with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [arityFuel5_app]
      have harL := arityFuel_le 5 l
      -- Case-split on `arityFuel 5 l ∈ {0, 1, 2, 3, 4, 5}`:
      have hcases : arityFuel 5 l = 0 ∨ arityFuel 5 l = 1 ∨ arityFuel 5 l = 2 ∨
          arityFuel 5 l = 3 ∨ arityFuel 5 l = 4 ∨ arityFuel 5 l = 5 := by omega
      rcases hcases with hL | hL | hL | hL | hL | hL
      · rw [hL]; rfl
      · rw [hL]
        have harR := arityFuel_le 5 rt
        have hrcases : arityFuel 5 rt = 0 ∨ arityFuel 5 rt = 1 ∨ arityFuel 5 rt = 2 ∨
            arityFuel 5 rt = 3 ∨ arityFuel 5 rt = 4 ∨ arityFuel 5 rt = 5 := by omega
        rcases hrcases with hR | hR | hR | hR | hR | hR
        · rw [hR]; rfl
        · rw [hR]; rfl
        · rw [hR]; rfl
        · rw [hR]
          change (loc 53 (ann (pocketChildRoles r).2 rt)).map (true :: ·) = some [true]
          rw [loc_53_eq hrl_r hrt, hR]; rfl
        · rw [hR]
          change (loc 52 (ann (pocketChildRoles r).2 rt)).map (true :: ·) = some [true, false]
          rw [loc_52_eq hrr hrt, hR]; rfl
        · rw [hR]; rfl
      · rw [hL]; rfl
      · rw [hL]
        change (loc 53 (ann (pocketChildRoles r).1 l)).map (false :: ·) = some [false]
        rw [loc_53_eq hrl_l hl, hL]; rfl
      · rw [hL]; rfl
      · rw [hL]; rfl

private theorem loc_1_open_eq {r : Fin 25}
    (hrl : isOpenSpLeftRole (pocketChildRoles r).1 = true)
    (hrr : isOpenSpRightRole (pocketChildRoles r).2 = true)
    {u : Term} (hu : isClosedPureS u = true) :
    loc 1 (ann r u) = nextOpeningAddress u := by
  cases u with
  | s => rfl
  | var _ => cases hu
  | app l rt =>
      exact loc_stepOpen_eq hrl hrr (((Bool.and_eq_true _ _).mp hu).1)
        (((Bool.and_eq_true _ _).mp hu).2) rfl

/-! ### 4.2 Correctness of `CHOOSE_FIELDS` (`p = 2..15`) and `WRITE_VER` (`p = 39..49`) -/

private def cfCode : List Bool → Fin 136
  | [b0] => fin136 (2 + bitNat b0)
  | [b0, b1] => fin136 (4 + 2 * bitNat b0 + bitNat b1)
  | [b0, b1, b2] => fin136 (8 + 4 * bitNat b0 + 2 * bitNat b1 + bitNat b2)
  | _ => 1

private theorem chooseFields_nil_open (u : Term) :
    (chooseSFields [] u).bind (pfSelectOpeningAt u) = nextOpeningAddress u := by
  simp only [chooseSFields]
  cases hf : flagValue u with
  | true =>
      have hnone : nextOpeningAddress u = none := by
        unfold nextOpeningAddress; simp [flagValue] at hf; simp [hf]
      rw [hnone]; rfl
  | false =>
      simp [pfSelectOpeningAt_nil]

private theorem specBU11_s_props (fl : Term) :
    (((specBU 11 (.s ⋅ fl)).val - 7) == 6) = flagValue fl ∧
    ¬ ((specBU 11 (.s ⋅ fl)).val < 7) := by
  simp only [specBU]
  cases hf : flagValue fl with
  | true => simp only [↓reduceIte]; decide
  | false =>
      have har := arityFuel_le 5 fl
      have hlt23 : 7 + arityFuel 5 fl < 23 := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, fin23_val_of_lt hlt23]
      exact ⟨nat_beq_of_ne (by omega), by omega⟩

private theorem loc_chooseFields_len1 (b0 : Bool) {u : Term} (hu : isClosedPureS u = true) :
    loc (cfCode [b0]) (ann 9 u) = (chooseSFields [b0] u).bind (pfSelectOpeningAt u) := by
  cases u with
  | s => rfl
  | var _ => cases hu
  | app l r =>
      have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp hu).1
      have hr : isClosedPureS r = true := ((Bool.and_eq_true _ _).mp hu).2
      cases hpf : parseFrame (l ⋅ r) with
      | none =>
          have hch : chooseSFields [b0] (l ⋅ r) = some [] := by simp [chooseSFields, hpf]
          rw [hch]
          dsimp only [Bind.bind, Option.bind]
          rw [pfSelectOpeningAt_nil]
          have hnot_both : (specBU 11 l).val < 7 ∨ (specBU 24 r).val < 7 := by
            cases hge7 : decide ((specBU 11 l).val ≥ 7) with
            | false => exact Or.inl (Nat.lt_of_not_le (of_decide_eq_false hge7))
            | true =>
                obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => if flagValue x then 6 else arityFuel 5 x)
                  flag_or_arity_le15).mp
                  (of_decide_eq_true hge7)
                have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                  rintro ⟨sub, j, rfl⟩; simp [parseFrame] at hpf
                exact Or.inr (Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                  (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)).mp hnot_s2))
          refine loc_stepOpen_eq (r := 9) rfl rfl hl hr ?_
          rcases hnot_both with h | h <;> cases b0 <;>
          · unfold cfCode pocketStepTD; dsimp only [bitNat, pocketChildRoles]; simp [h]
      | some triple =>
          rcases triple with ⟨fl, rest, j⟩
          obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
          injection heq with hl_eq hr_eq
          subst hl_eq; subst hr_eq
          have hfl_closed : isClosedPureS fl = true := ((Bool.and_eq_true _ _).mp hl).2
          have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
          have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
          obtain ⟨ha_fr, hql_ge7⟩ := specBU11_s_props fl
          have hqr_ge7 : ¬ ((specBU 24 ((.s ⋅ rest) ⋅ j)).val < 7) := by
            simp only [specBU]
            have hc := (fieldsCode rest).isLt
            rw [fin23_val_of_lt (by omega)]; omega
          cases hb_cond : (b0 && !(flagValue fl)) with
          | true =>
              have hstep : pocketStepTD (cfCode [b0])
                  (ann 11 (.s ⋅ fl)).state (ann 24 ((.s ⋅ rest) ⋅ j)).state = pocketGoFL 1 := by
                rw [ann_state_eq hl, ann_state_eq hr]
                cases b0 with
                | false => cases hb_cond
                | true =>
                    simp only [Bool.true_and, Bool.not_eq_true'] at hb_cond
                    unfold cfCode pocketStepTD
                    dsimp only [bitNat]
                    simp [hql_ge7, hqr_ge7, ha_fr, hb_cond]
              rw_goFL (by decide : 1 < 50) hstep
              change (loc 1 (ann 10 fl)).map (pfLeftChildPath ++ ·) = _
              rw [loc_1_open_eq (r := 10) rfl rfl hfl_closed]
              simp only [chooseSFields, parseFrame, hb_cond, ↓reduceIte, Option.bind]
              rw [pfSelectOpeningAt_left_nil ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j))]
              simp [termAt, pfSelectOpeningAt_nil, pfLeftChildPath, Option.map]
          | false =>
              have hstep : pocketStepTD (cfCode [b0])
                  (ann 11 (.s ⋅ fl)).state (ann 24 ((.s ⋅ rest) ⋅ j)).state = pocketGoFR 1 := by
                rw [ann_state_eq hl, ann_state_eq hr]
                cases b0 with
                | false =>
                    unfold cfCode pocketStepTD
                    dsimp only [bitNat]
                    simp [hql_ge7, hqr_ge7]
                | true =>
                    simp at hb_cond
                    unfold cfCode pocketStepTD
                    dsimp only [bitNat]
                    simp [hql_ge7, hqr_ge7, ha_fr, hb_cond]
              rw_goFR (by decide : 1 < 32) hstep
              change (loc 1 (ann 9 rest)).map (pfRightChildPath ++ ·) = _
              rw [loc_1_open_eq (r := 9) rfl rfl hrest_closed, ← chooseFields_nil_open rest]
              have hch_step : chooseSFields [b0] ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) =
                  (chooseSFields [] rest).map ([true, false, true] ++ ·) := by
                conv => lhs; unfold chooseSFields; simp only [parseFrame, hb_cond, Bool.false_eq_true, ↓reduceIte]
              rw [hch_step]
              cases hcs : chooseSFields [] rest with
              | none => rfl
              | some subPath =>
                  simp only [Option.map, Option.bind]
                  rw [pfSelectOpeningAt_append ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) [true, false, true] subPath]
                  simp [termAt, pfRightChildPath, Option.map]

private theorem loc_chooseFields_len2 (b0 b1 : Bool) {u : Term} (hu : isClosedPureS u = true) :
    loc (cfCode [b0, b1]) (ann 9 u) = (chooseSFields [b0, b1] u).bind (pfSelectOpeningAt u) := by
  cases u with
  | s => rfl
  | var _ => cases hu
  | app l r =>
      have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp hu).1
      have hr : isClosedPureS r = true := ((Bool.and_eq_true _ _).mp hu).2
      cases hpf : parseFrame (l ⋅ r) with
      | none =>
          have hch : chooseSFields [b0, b1] (l ⋅ r) = some [] := by simp [chooseSFields, hpf]
          rw [hch]; dsimp only [Bind.bind, Option.bind]; rw [pfSelectOpeningAt_nil]
          have hnot_both : (specBU 11 l).val < 7 ∨ (specBU 24 r).val < 7 := by
            cases hge7 : decide ((specBU 11 l).val ≥ 7) with
            | false => exact Or.inl (Nat.lt_of_not_le (of_decide_eq_false hge7))
            | true =>
                obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => if flagValue x then 6 else arityFuel 5 x)
                  flag_or_arity_le15).mp
                  (of_decide_eq_true hge7)
                have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                  rintro ⟨sub, j, rfl⟩; simp [parseFrame] at hpf
                exact Or.inr (Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                  (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)).mp hnot_s2))
          refine loc_stepOpen_eq (r := 9) rfl rfl hl hr ?_
          rcases hnot_both with h | h <;> cases b0 <;> cases b1 <;>
          · unfold cfCode pocketStepTD; dsimp only [bitNat, pocketChildRoles]; simp [h]
      | some triple =>
          rcases triple with ⟨fl, rest, j⟩
          obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
          injection heq with hl_eq hr_eq
          subst hl_eq; subst hr_eq
          have hfl_closed : isClosedPureS fl = true := ((Bool.and_eq_true _ _).mp hl).2
          have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
          have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
          obtain ⟨ha_fr, hql_ge7⟩ := specBU11_s_props fl
          have hqr_ge7 : ¬ ((specBU 24 ((.s ⋅ rest) ⋅ j)).val < 7) := by
            simp only [specBU]; have hc := (fieldsCode rest).isLt; rw [fin23_val_of_lt (by omega)]; omega
          cases hb_cond : (b0 && !(flagValue fl)) with
          | true =>
              have hstep : pocketStepTD (cfCode [b0, b1])
                  (ann 11 (.s ⋅ fl)).state (ann 24 ((.s ⋅ rest) ⋅ j)).state = pocketGoFL 1 := by
                rw [ann_state_eq hl, ann_state_eq hr]
                cases b0 with
                | false => cases hb_cond
                | true =>
                    simp only [Bool.true_and, Bool.not_eq_true'] at hb_cond
                    cases b1 <;>
                    · unfold cfCode pocketStepTD; dsimp only [bitNat]
                      simp [hql_ge7, hqr_ge7, ha_fr, hb_cond]
              rw_goFL (by decide : 1 < 50) hstep
              change (loc 1 (ann 10 fl)).map (pfLeftChildPath ++ ·) = _
              rw [loc_1_open_eq (r := 10) rfl rfl hfl_closed]
              simp only [chooseSFields, parseFrame, hb_cond, ↓reduceIte, Option.bind]
              rw [pfSelectOpeningAt_left_nil ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j))]
              simp [termAt, pfSelectOpeningAt_nil, pfLeftChildPath, Option.map]
          | false =>
              have hc_lt : 2 + bitNat b1 < 32 := by cases b1 <;> decide
              have hstep : pocketStepTD (cfCode [b0, b1])
                  (ann 11 (.s ⋅ fl)).state (ann 24 ((.s ⋅ rest) ⋅ j)).state = pocketGoFR (2 + bitNat b1) := by
                rw [ann_state_eq hl, ann_state_eq hr]
                cases b0 with
                | false =>
                    cases b1 <;>
                    · unfold cfCode pocketStepTD; dsimp only [bitNat]
                      simp [hql_ge7, hqr_ge7]
                | true =>
                    simp at hb_cond
                    cases b1 <;>
                    · unfold cfCode pocketStepTD; dsimp only [bitNat]
                      simp [hql_ge7, hqr_ge7, ha_fr, hb_cond]
              rw_goFR hc_lt hstep
              change (loc (cfCode [b1]) (ann 9 rest)).map (pfRightChildPath ++ ·) = _
              rw [loc_chooseFields_len1 b1 hrest_closed]
              have hch_step : chooseSFields [b0, b1] ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) =
                  (chooseSFields [b1] rest).map ([true, false, true] ++ ·) := by
                conv => lhs; unfold chooseSFields; simp only [parseFrame, hb_cond, Bool.false_eq_true, ↓reduceIte]
              rw [hch_step]
              cases chooseSFields [b1] rest with
              | none => rfl
              | some subPath =>
                  simp only [Option.map, Option.bind]
                  rw [pfSelectOpeningAt_append ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) [true, false, true] subPath]
                  simp [termAt, pfRightChildPath, Option.map]

private theorem loc_chooseFields_len3 (b0 b1 b2 : Bool) {u : Term} (hu : isClosedPureS u = true) :
    loc (cfCode [b0, b1, b2]) (ann 9 u) = (chooseSFields [b0, b1, b2] u).bind (pfSelectOpeningAt u) := by
  cases u with
  | s => rfl
  | var _ => cases hu
  | app l r =>
      have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp hu).1
      have hr : isClosedPureS r = true := ((Bool.and_eq_true _ _).mp hu).2
      cases hpf : parseFrame (l ⋅ r) with
      | none =>
          have hch : chooseSFields [b0, b1, b2] (l ⋅ r) = some [] := by simp [chooseSFields, hpf]
          rw [hch]; dsimp only [Bind.bind, Option.bind]; rw [pfSelectOpeningAt_nil]
          have hnot_both : (specBU 11 l).val < 7 ∨ (specBU 24 r).val < 7 := by
            cases hge7 : decide ((specBU 11 l).val ≥ 7) with
            | false => exact Or.inl (Nat.lt_of_not_le (of_decide_eq_false hge7))
            | true =>
                obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => if flagValue x then 6 else arityFuel 5 x)
                  flag_or_arity_le15).mp
                  (of_decide_eq_true hge7)
                have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                  rintro ⟨sub, j, rfl⟩; simp [parseFrame] at hpf
                exact Or.inr (Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                  (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)).mp hnot_s2))
          refine loc_stepOpen_eq (r := 9) rfl rfl hl hr ?_
          rcases hnot_both with h | h <;> cases b0 <;> cases b1 <;> cases b2 <;>
          · unfold cfCode pocketStepTD; dsimp only [bitNat, pocketChildRoles]; simp [h]
      | some triple =>
          rcases triple with ⟨fl, rest, j⟩
          obtain ⟨heq, _, _⟩ := parseFrame_some_decomp hpf
          injection heq with hl_eq hr_eq
          subst hl_eq; subst hr_eq
          have hfl_closed : isClosedPureS fl = true := ((Bool.and_eq_true _ _).mp hl).2
          have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
          have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
          obtain ⟨ha_fr, hql_ge7⟩ := specBU11_s_props fl
          have hqr_ge7 : ¬ ((specBU 24 ((.s ⋅ rest) ⋅ j)).val < 7) := by
            simp only [specBU]; have hc := (fieldsCode rest).isLt; rw [fin23_val_of_lt (by omega)]; omega
          cases hb_cond : (b0 && !(flagValue fl)) with
          | true =>
              have hstep : pocketStepTD (cfCode [b0, b1, b2])
                  (ann 11 (.s ⋅ fl)).state (ann 24 ((.s ⋅ rest) ⋅ j)).state = pocketGoFL 1 := by
                rw [ann_state_eq hl, ann_state_eq hr]
                cases b0 with
                | false => cases hb_cond
                | true =>
                    simp only [Bool.true_and, Bool.not_eq_true'] at hb_cond
                    cases b1 <;> cases b2 <;>
                    · unfold cfCode pocketStepTD; dsimp only [bitNat]
                      simp [hql_ge7, hqr_ge7, ha_fr, hb_cond]
              rw_goFL (by decide : 1 < 50) hstep
              change (loc 1 (ann 10 fl)).map (pfLeftChildPath ++ ·) = _
              rw [loc_1_open_eq (r := 10) rfl rfl hfl_closed]
              simp only [chooseSFields, parseFrame, hb_cond, ↓reduceIte, Option.bind]
              rw [pfSelectOpeningAt_left_nil ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j))]
              simp [termAt, pfSelectOpeningAt_nil, pfLeftChildPath, Option.map]
          | false =>
              have hc_lt : 4 + 2 * bitNat b1 + bitNat b2 < 32 := by cases b1 <;> cases b2 <;> decide
              have hstep : pocketStepTD (cfCode [b0, b1, b2])
                  (ann 11 (.s ⋅ fl)).state (ann 24 ((.s ⋅ rest) ⋅ j)).state =
                  pocketGoFR (4 + 2 * bitNat b1 + bitNat b2) := by
                rw [ann_state_eq hl, ann_state_eq hr]
                cases b0 with
                | false =>
                    cases b1 <;> cases b2 <;>
                    · unfold cfCode pocketStepTD; dsimp only [bitNat]
                      simp [hql_ge7, hqr_ge7]
                | true =>
                    simp at hb_cond
                    cases b1 <;> cases b2 <;>
                    · unfold cfCode pocketStepTD; dsimp only [bitNat]
                      simp [hql_ge7, hqr_ge7, ha_fr, hb_cond]
              rw_goFR hc_lt hstep
              change (loc (cfCode [b1, b2]) (ann 9 rest)).map (pfRightChildPath ++ ·) = _
              rw [loc_chooseFields_len2 b1 b2 hrest_closed]
              have hch_step : chooseSFields [b0, b1, b2] ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) =
                  (chooseSFields [b1, b2] rest).map ([true, false, true] ++ ·) := by
                conv => lhs; unfold chooseSFields; simp only [parseFrame, hb_cond, Bool.false_eq_true, ↓reduceIte]
              rw [hch_step]
              cases chooseSFields [b1, b2] rest with
              | none => rfl
              | some subPath =>
                  simp only [Option.map, Option.bind]
                  rw [pfSelectOpeningAt_append ((.s ⋅ fl) ⋅ ((.s ⋅ rest) ⋅ j)) [true, false, true] subPath]
                  simp [termAt, pfRightChildPath, Option.map]

private def wv2TargetBits : Fin 3 → List Bool
  | ⟨0, _⟩ => [false, false]
  | ⟨1, _⟩ => [true, false]
  | _      => [true, true]

private theorem loc_writeVer2 (k : Fin 3) {u : Term} (hu : isClosedPureS u = true) :
    loc (fin136 (39 + k.val)) (ann 7 u) = pfSelectVersionWriteAt u [] 2 (wv2TargetBits k) := by
  have haux : ∀ (B : Nat) (v : Term), leaves v ≤ B → isClosedPureS v = true →
      loc (fin136 (39 + k.val)) (ann 7 v) = pfSelectVersionWriteAt v [] 2 (wv2TargetBits k) := by
    intro B
    induction B with
    | zero =>
        intro v hle _
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure v))
    | succ B ih =>
        intro v hle hv
        cases v with
        | s =>
            rw [pfSelectVersionWriteAt_nil]
            simp [chooseSVersionTree, pfSelectOpeningAt_nil, nextOpeningAddress, parseFrame, arityFuel]
            rfl
        | var _ => cases hv
        | app l r =>
            have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp hv).1
            have hr : isClosedPureS r = true := ((Bool.and_eq_true _ _).mp hv).2
            cases hpf : parseFrame (l ⋅ r) with
            | none =>
                rw [pfSelectVersionWriteAt_nil, choose_tree_closed 2 (wv2TargetBits k) (l ⋅ r) hpf]
                dsimp only [Bind.bind, Option.bind]
                rw [pfSelectOpeningAt_nil]
                have hnot_both : (specBU 17 l).val < 7 ∨ (specBU 24 r).val < 7 := by
                  cases hge7 : decide ((specBU 17 l).val ≥ 7) with
                  | false => exact Or.inl (Nat.lt_of_not_le (of_decide_eq_false hge7))
                  | true =>
                      obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => (ver2Code x).val)
                        (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver2Code x).isLt (by decide)))).mp
                        (of_decide_eq_true hge7)
                      have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                        rintro ⟨sub, j, rfl⟩; simp [parseFrame] at hpf
                      exact Or.inr (Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                        (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)).mp hnot_s2))
                refine loc_stepOpen_eq (r := 7) rfl rfl hl hr ?_
                rcases k with ⟨kv, hkv⟩
                match kv with
                | 0 | 1 | 2 =>
                    rcases hnot_both with h | h <;>
                    · unfold pocketStepTD; dsimp only [pocketChildRoles]; simp [h]
                | _ + 3 => omega
            | some triple =>
                rcases triple with ⟨next, fields, j⟩
                obtain ⟨heq, hnext_lt, _⟩ := parseFrame_some_decomp hpf
                have hnext_le : leaves next ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hnext_lt hle)
                injection heq with hl_eq hr_eq
                subst hl_eq; subst hr_eq
                have hnext_closed : isClosedPureS next = true := ((Bool.and_eq_true _ _).mp hl).2
                have hsf_closed : isClosedPureS (.s ⋅ fields) = true := ((Bool.and_eq_true _ _).mp hr).1
                have hfields_closed : isClosedPureS fields = true := ((Bool.and_eq_true _ _).mp hsf_closed).2
                have hrf2 := (fieldsCode_spec fields).2.2.1
                have hge4_iff : decide ((fieldsCode fields).val ≥ 4) = (readFields 2 fields).isSome := by
                  rw [hrf2]
                  have hall : ∀ c : Fin 16, decide (c.val ≥ 4) = (decodeFields2 c).isSome := by decide
                  exact hall (fieldsCode fields)
                have hql_ge7 : ¬ ((specBU 17 (.s ⋅ next)).val < 7) := by
                  simp only [specBU]; have hc := (ver2Code next).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hqr_ge7 : ¬ ((specBU 24 ((.s ⋅ fields) ⋅ j)).val < 7) := by
                  simp only [specBU]; have hc := (fieldsCode fields).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hqr_sub : (specBU 24 ((.s ⋅ fields) ⋅ j)).val - 7 = (fieldsCode fields).val := by
                  simp only [specBU]; have hc := (fieldsCode fields).isLt; rw [fin23_val_of_lt (by omega)]; omega
                cases hsome2 : (readFields 2 fields).isSome with
                | true =>
                    have hge4 : (fieldsCode fields).val ≥ 4 := of_decide_eq_true (hge4_iff.trans hsome2)
                    have h39_lt : 39 + k.val < 50 := by have hk := k.isLt; omega
                    have hstep : pocketStepTD (fin136 (39 + k.val))
                        (ann 17 (.s ⋅ next)).state (ann 24 ((.s ⋅ fields) ⋅ j)).state =
                        pocketGoFL (39 + k.val) := by
                      rw [ann_state_eq hl, ann_state_eq hr]
                      rcases k with ⟨kv, hkv⟩
                      match kv with
                      | 0 | 1 | 2 =>
                          unfold pocketStepTD; simp [hql_ge7, hqr_ge7, hqr_sub, hge4]
                      | _ + 3 => omega
                    rw_goFL h39_lt hstep
                    change (loc (fin136 (39 + k.val)) (ann 7 next)).map (pfLeftChildPath ++ ·) = _
                    rw [ih next hnext_le hnext_closed, pfSelectVersionWriteAt_nil, pfSelectVersionWriteAt_nil]
                    cases hrf_val : readFields 2 fields with
                    | none => rw [hrf_val] at hsome2; cases hsome2
                    | some bits =>
                        simp only [chooseSVersionTree, hrf_val]
                        cases chooseSVersionTree 2 (wv2TargetBits k) next with
                        | none => rfl
                        | some slot =>
                            simp only [Option.map, Option.bind]
                            rw [pfSelectOpeningAt_append ((.s ⋅ next) ⋅ ((.s ⋅ fields) ⋅ j)) [false, true] slot]
                            simp [termAt, pfLeftChildPath, Option.map]
                | false =>
                    have hlt4 : ¬ ((fieldsCode fields).val ≥ 4) :=
                      of_decide_eq_false (hge4_iff.trans hsome2)
                    have hcf_lt : (if k.val == 0 then 4 else if k.val == 1 then 6 else 7) < 32 :=
                      (by decide : ∀ x : Fin 3, (if x.val == 0 then 4 else if x.val == 1 then 6 else 7) < 32) k
                    have hstep : pocketStepTD (fin136 (39 + k.val))
                        (ann 17 (.s ⋅ next)).state (ann 24 ((.s ⋅ fields) ⋅ j)).state =
                        pocketGoFR (if k.val == 0 then 4 else if k.val == 1 then 6 else 7) := by
                      rw [ann_state_eq hl, ann_state_eq hr]
                      rcases k with ⟨kv, hkv⟩
                      match kv with
                      | 0 | 1 | 2 => unfold pocketStepTD; simp [hql_ge7, hqr_ge7, hqr_sub, hlt4]
                      | _ + 3 => omega
                    rw_goFR hcf_lt hstep
                    have hcf_eq : fin136 (if k.val == 0 then 4 else if k.val == 1 then 6 else 7) =
                        cfCode (wv2TargetBits k) :=
                      (by decide : ∀ x : Fin 3,
                        fin136 (if x.val == 0 then 4 else if x.val == 1 then 6 else 7) = cfCode (wv2TargetBits x)) k
                    change (loc (fin136 (if k.val == 0 then 4 else if k.val == 1 then 6 else 7)) (ann 9 fields)).map
                      (pfRightChildPath ++ ·) = _
                    rw [hcf_eq]
                    have hcf_run : loc (cfCode (wv2TargetBits k)) (ann 9 fields) =
                        (chooseSFields (wv2TargetBits k) fields).bind (pfSelectOpeningAt fields) := by
                      rcases k with ⟨kv, hkv⟩
                      match kv with
                      | 0 => exact loc_chooseFields_len2 false false hfields_closed
                      | 1 => exact loc_chooseFields_len2 true false hfields_closed
                      | 2 => exact loc_chooseFields_len2 true true hfields_closed
                      | _ + 3 => omega
                    rw [hcf_run, pfSelectVersionWriteAt_nil]
                    cases hrf_val : readFields 2 fields with
                    | some _ => rw [hrf_val] at hsome2; cases hsome2
                    | none =>
                        simp only [chooseSVersionTree, hrf_val]
                        cases chooseSFields (wv2TargetBits k) fields with
                        | none => rfl
                        | some slot =>
                            simp only [Option.map, Option.bind]
                            rw [pfSelectOpeningAt_append ((.s ⋅ next) ⋅ ((.s ⋅ fields) ⋅ j)) [true, false, true] slot]
                            simp [termAt, pfRightChildPath, Option.map]
  exact haux (leaves u) u (Nat.le_refl _) hu

private theorem loc_writeVer3 (b0 b1 b2 : Bool) {u : Term} (hu : isClosedPureS u = true) :
    let idx := 4 * bitNat b0 + 2 * bitNat b1 + bitNat b2
    loc (fin136 (42 + idx)) (ann 8 u) = pfSelectVersionWriteAt u [] 3 [b0, b1, b2] := by
  intro idx
  have haux : ∀ (B : Nat) (v : Term), leaves v ≤ B → isClosedPureS v = true →
      loc (fin136 (42 + idx)) (ann 8 v) = pfSelectVersionWriteAt v [] 3 [b0, b1, b2] := by
    intro B
    induction B with
    | zero =>
        intro v hle _
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure v))
    | succ B ih =>
        intro v hle hv
        cases v with
        | s =>
            rw [pfSelectVersionWriteAt_nil]
            simp [chooseSVersionTree, pfSelectOpeningAt_nil, nextOpeningAddress, parseFrame, arityFuel]
            rfl
        | var _ => cases hv
        | app l r =>
            have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp hv).1
            have hr : isClosedPureS r = true := ((Bool.and_eq_true _ _).mp hv).2
            cases hpf : parseFrame (l ⋅ r) with
            | none =>
                rw [pfSelectVersionWriteAt_nil, choose_tree_closed 3 [b0, b1, b2] (l ⋅ r) hpf]
                dsimp only [Bind.bind, Option.bind]
                rw [pfSelectOpeningAt_nil]
                have hnot_both : (specBU 18 l).val < 7 ∨ (specBU 24 r).val < 7 := by
                  cases hge7 : decide ((specBU 18 l).val ≥ 7) with
                  | false => exact Or.inl (Nat.lt_of_not_le (of_decide_eq_false hge7))
                  | true =>
                      obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => (ver3Code x).val)
                        (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver3Code x).isLt (by decide)))).mp
                        (of_decide_eq_true hge7)
                      have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                        rintro ⟨sub, j, rfl⟩; simp [parseFrame] at hpf
                      exact Or.inr (Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                        (fun x => Nat.le_of_lt_succ (fieldsCode x).isLt)).mp hnot_s2))
                refine loc_stepOpen_eq (r := 8) rfl rfl hl hr ?_
                rcases hnot_both with h | h <;> cases b0 <;> cases b1 <;> cases b2 <;>
                · dsimp only [idx, bitNat, pocketChildRoles]; unfold pocketStepTD; simp [h]
            | some triple =>
                rcases triple with ⟨next, fields, j⟩
                obtain ⟨heq, hnext_lt, _⟩ := parseFrame_some_decomp hpf
                have hnext_le : leaves next ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hnext_lt hle)
                injection heq with hl_eq hr_eq
                subst hl_eq; subst hr_eq
                have hnext_closed : isClosedPureS next = true := ((Bool.and_eq_true _ _).mp hl).2
                have hsf_closed : isClosedPureS (.s ⋅ fields) = true := ((Bool.and_eq_true _ _).mp hr).1
                have hfields_closed : isClosedPureS fields = true := ((Bool.and_eq_true _ _).mp hsf_closed).2
                have hrf3 := (fieldsCode_spec fields).2.2.2
                have hge8_iff : decide ((fieldsCode fields).val ≥ 8) = (readFields 3 fields).isSome := by
                  rw [hrf3]
                  have hall : ∀ c : Fin 16, decide (c.val ≥ 8) = (decodeFields3 c).isSome := by decide
                  exact hall (fieldsCode fields)
                have hql_ge7 : ¬ ((specBU 18 (.s ⋅ next)).val < 7) := by
                  simp only [specBU]; have hc := (ver3Code next).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hqr_ge7 : ¬ ((specBU 24 ((.s ⋅ fields) ⋅ j)).val < 7) := by
                  simp only [specBU]; have hc := (fieldsCode fields).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hqr_sub : (specBU 24 ((.s ⋅ fields) ⋅ j)).val - 7 = (fieldsCode fields).val := by
                  simp only [specBU]; have hc := (fieldsCode fields).isLt; rw [fin23_val_of_lt (by omega)]; omega
                cases hsome3 : (readFields 3 fields).isSome with
                | true =>
                    have hge8 : (fieldsCode fields).val ≥ 8 := of_decide_eq_true (hge8_iff.trans hsome3)
                    have h42_lt : 42 + idx < 50 := by cases b0 <;> cases b1 <;> cases b2 <;> decide
                    have hstep : pocketStepTD (fin136 (42 + idx))
                        (ann 18 (.s ⋅ next)).state (ann 24 ((.s ⋅ fields) ⋅ j)).state =
                        pocketGoFL (42 + idx) := by
                      rw [ann_state_eq hl, ann_state_eq hr]
                      cases b0 <;> cases b1 <;> cases b2 <;>
                      · dsimp only [idx, bitNat]; unfold pocketStepTD
                        simp [hql_ge7, hqr_ge7, hqr_sub, hge8]
                    rw_goFL h42_lt hstep
                    change (loc (fin136 (42 + idx)) (ann 8 next)).map (pfLeftChildPath ++ ·) = _
                    rw [ih next hnext_le hnext_closed, pfSelectVersionWriteAt_nil, pfSelectVersionWriteAt_nil]
                    cases hrf_val : readFields 3 fields with
                    | none => rw [hrf_val] at hsome3; cases hsome3
                    | some _ =>
                        simp only [chooseSVersionTree, hrf_val]
                        cases chooseSVersionTree 3 [b0, b1, b2] next with
                        | none => rfl
                        | some slot =>
                            simp only [Option.map, Option.bind]
                            rw [pfSelectOpeningAt_append ((.s ⋅ next) ⋅ ((.s ⋅ fields) ⋅ j)) [false, true] slot]
                            simp [termAt, pfLeftChildPath, Option.map]
                | false =>
                    have hlt8 : ¬ ((fieldsCode fields).val ≥ 8) :=
                      of_decide_eq_false (hge8_iff.trans hsome3)
                    have h8_lt : 8 + idx < 32 := by cases b0 <;> cases b1 <;> cases b2 <;> decide
                    have hstep : pocketStepTD (fin136 (42 + idx))
                        (ann 18 (.s ⋅ next)).state (ann 24 ((.s ⋅ fields) ⋅ j)).state =
                        pocketGoFR (8 + idx) := by
                      rw [ann_state_eq hl, ann_state_eq hr]
                      cases b0 <;> cases b1 <;> cases b2 <;>
                      · dsimp only [idx, bitNat]; unfold pocketStepTD
                        simp [hql_ge7, hqr_ge7, hqr_sub, hlt8]
                    rw_goFR h8_lt hstep
                    have hcf_eq : fin136 (8 + idx) = cfCode [b0, b1, b2] := by
                      dsimp only [idx]; cases b0 <;> cases b1 <;> cases b2 <;> rfl
                    change (loc (fin136 (8 + idx)) (ann 9 fields)).map (pfRightChildPath ++ ·) = _
                    rw [hcf_eq, loc_chooseFields_len3 b0 b1 b2 hfields_closed, pfSelectVersionWriteAt_nil]
                    cases hrf_val : readFields 3 fields with
                    | some _ => rw [hrf_val] at hsome3; cases hsome3
                    | none =>
                        simp only [chooseSVersionTree, hrf_val]
                        cases chooseSFields [b0, b1, b2] fields with
                        | none => rfl
                        | some slot =>
                            simp only [Option.map, Option.bind]
                            rw [pfSelectOpeningAt_append ((.s ⋅ next) ⋅ ((.s ⋅ fields) ⋅ j)) [true, false, true] slot]
                            simp [termAt, pfRightChildPath, Option.map]
  exact haux (leaves u) u (Nat.le_refl _) hu

/-! ### 4.3 Correctness of `T_SEEK` (`p = 22..24`) and `Q_SEEK` (`p = 16..21`) -/

private theorem ver3_match_hi2 (tVer : Term) :
    let a := (ver3Code tVer).val
    ((a == 0) = (pfScanVersion 3 none tVer == none)) ∧
    ((a ≥ 1 && (a - 1) / 2 == 0) =
      match pfScanVersion 3 none tVer with | some [false, false, _] => true | _ => false) ∧
    ((a ≥ 1 && (a - 1) / 2 == 1) =
      match pfScanVersion 3 none tVer with | some [false, true, _] => true | _ => false) ∧
    ((a ≥ 1 && (a - 1) / 2 == 2) =
      match pfScanVersion 3 none tVer with | some [true, false, _] => true | _ => false) ∧
    ((a ≥ 1 && (a - 1) / 2 == 3) =
      match pfScanVersion 3 none tVer with | some [true, true, _] => true | _ => false) ∧
    (∀ b0 b1 sbit : Bool, pfScanVersion 3 none tVer = some [b0, b1, sbit] →
      (a - 1) % 2 = bitNat sbit) := by
  rw [ver3Code_spec tVer]
  have hall : ∀ q : Fin 9,
      let a := q.val
      ((a == 0) = (decodeVer3 q == none)) ∧
      ((a ≥ 1 && (a - 1) / 2 == 0) =
        match decodeVer3 q with | some [false, false, _] => true | _ => false) ∧
      ((a ≥ 1 && (a - 1) / 2 == 1) =
        match decodeVer3 q with | some [false, true, _] => true | _ => false) ∧
      ((a ≥ 1 && (a - 1) / 2 == 2) =
        match decodeVer3 q with | some [true, false, _] => true | _ => false) ∧
      ((a ≥ 1 && (a - 1) / 2 == 3) =
        match decodeVer3 q with | some [true, true, _] => true | _ => false) ∧
      (∀ b0 b1 sbit : Bool, decodeVer3 q = some [b0, b1, sbit] →
        (a - 1) % 2 = bitNat sbit) := by decide
  exact hall (ver3Code tVer)

private theorem loc_tSeek {u : Term} (hu : isClosedPureS u = true) :
    (loc 22 (ann 5 u) = match (scanTemplates u).firstIdle with
      | some (tRel, sbit) => pfSelectVersionWriteAt u tRel 3 [true, false, sbit]
      | none => none) ∧
    (loc 23 (ann 5 u) = match (scanTemplates u).firstArmed with
      | some (tRel, sbit) => pfSelectVersionWriteAt u tRel 3 [true, true, sbit]
      | none => none) ∧
    (loc 24 (ann 5 u) = match (scanTemplates u).firstAppending with
      | some (tRel, sbit) => pfSelectVersionWriteAt u tRel 3 [false, false, sbit]
      | none => none) := by
  have haux : ∀ (B : Nat) (v : Term), leaves v ≤ B → isClosedPureS v = true →
      (loc 22 (ann 5 v) = match (scanTemplates v).firstIdle with
        | some (tRel, sbit) => pfSelectVersionWriteAt v tRel 3 [true, false, sbit]
        | none => none) ∧
      (loc 23 (ann 5 v) = match (scanTemplates v).firstArmed with
        | some (tRel, sbit) => pfSelectVersionWriteAt v tRel 3 [true, true, sbit]
        | none => none) ∧
      (loc 24 (ann 5 v) = match (scanTemplates v).firstAppending with
        | some (tRel, sbit) => pfSelectVersionWriteAt v tRel 3 [false, false, sbit]
        | none => none) := by
    intro B
    induction B with
    | zero =>
        intro v hle _
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure v))
    | succ B ih =>
        intro v hle hv
        cases v with
        | s => exact ⟨rfl, rfl, rfl⟩
        | var _ => cases hv
        | app l r =>
            have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp hv).1
            have hr : isClosedPureS r = true := ((Bool.and_eq_true _ _).mp hv).2
            cases hpf : parseFrame (l ⋅ r) with
            | none =>
                have hst_none : scanTemplates (l ⋅ r) = ⟨none, none, none⟩ :=
                  (parseFrame_eq_none_cases hpf).2.2.2.2.2.2.1
                rw [hst_none]
                have hnot_both : (specBU 18 l).val < 7 ∨ (specBU 22 r).val < 7 := by
                  cases hge7 : decide ((specBU 18 l).val ≥ 7) with
                  | false => exact Or.inl (Nat.lt_of_not_le (of_decide_eq_false hge7))
                  | true =>
                      obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => (ver3Code x).val)
                        (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver3Code x).isLt (by decide)))).mp
                        (of_decide_eq_true hge7)
                      have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                        rintro ⟨sub, j, rfl⟩; simp [parseFrame] at hpf
                      exact Or.inr (Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                        (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (tmplCode x).isLt (by decide)))).mp hnot_s2))
                have hstuck : ∀ p : Fin 136, (p = 22 ∨ p = 23 ∨ p = 24) →
                    loc p (ann 5 (l ⋅ r)) = none := by
                  intro p hp
                  rw [loc_ann_app, ann_state_eq hl, ann_state_eq hr]
                  rcases hp with rfl | rfl | rfl <;> rcases hnot_both with h | h <;>
                  · unfold pocketStepTD; dsimp only [pocketChildRoles]; simp [h]
                exact ⟨hstuck 22 (Or.inl rfl), hstuck 23 (Or.inr (Or.inl rfl)),
                       hstuck 24 (Or.inr (Or.inr rfl))⟩
            | some triple =>
                rcases triple with ⟨tVer, rest, j⟩
                obtain ⟨heq, _, hrest_lt⟩ := parseFrame_some_decomp hpf
                have hrest_le : leaves rest ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrest_lt hle)
                injection heq with hl_eq hr_eq
                subst hl_eq; subst hr_eq
                have htver_closed : isClosedPureS tVer = true := ((Bool.and_eq_true _ _).mp hl).2
                have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
                have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
                obtain ⟨ih22, ih23, ih24⟩ := ih rest hrest_le hrest_closed
                have hql_ge7 : ¬ ((specBU 18 (.s ⋅ tVer)).val < 7) := by
                  simp only [specBU]; have hc := (ver3Code tVer).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hqr_ge7 : ¬ ((specBU 22 ((.s ⋅ rest) ⋅ j)).val < 7) := by
                  simp only [specBU]; have hc := (tmplCode rest).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hql_sub : (specBU 18 (.s ⋅ tVer)).val - 7 = (ver3Code tVer).val := by
                  simp only [specBU]; have hc := (ver3Code tVer).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hm := ver3_match_hi2 tVer
                -- Prove each of `22`, `23`, `24`:
                refine ⟨?_, ?_, ?_⟩
                · -- `22` (IDLE -> `some [false, false, sbit]`):
                  simp only [scanTemplates]
                  cases hmatch : (match pfScanVersion 3 none tVer with | some [false, false, _] => true | _ => false) with
                  | true =>
                      -- Extract `sbit` from `pfScanVersion 3 none tVer`:
                      cases hsc : pfScanVersion 3 none tVer with
                      | none => rw [hsc] at hmatch; cases hmatch
                      | some bits =>
                          have hlen := pfScanVersion_length 3 tVer hsc
                          rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨sbit, _ | _⟩⟩⟩ <;> try cases hlen
                          cases b0 with
                          | true => rw [hsc] at hmatch; cases hmatch
                          | false =>
                              cases b1 with
                              | true => rw [hsc] at hmatch; cases hmatch
                              | false =>
                                  have hcond_a : ((ver3Code tVer).val ≥ 1 && ((ver3Code tVer).val - 1) / 2 == 0) = true := by
                                    rw [hm.2.1, hsc]
                                  have hsbit_eq := hm.2.2.2.2.2 false false sbit hsc
                                  have hlt50 : 46 + bitNat sbit < 50 := by cases sbit <;> decide
                                  have hstep : pocketStepTD 22
                                      (ann 18 (.s ⋅ tVer)).state (ann 22 ((.s ⋅ rest) ⋅ j)).state =
                                      pocketGoFL (46 + bitNat sbit) := by
                                    rw [ann_state_eq hl, ann_state_eq hr]
                                    unfold pocketStepTD; dsimp only []
                                    simp [hql_ge7, hqr_ge7, hql_sub, hcond_a, hsbit_eq]
                                  rw_goFL hlt50 hstep
                                  change (loc (fin136 (46 + bitNat sbit)) (ann 8 tVer)).map (pfLeftChildPath ++ ·) = _
                                  have hw3 := loc_writeVer3 true false sbit htver_closed
                                  dsimp only [] at hw3
                                  have hfin_eq : fin136 (46 + bitNat sbit) =
                                      fin136 (42 + (4 * bitNat true + 2 * bitNat false + bitNat sbit)) := by
                                    cases sbit <;> rfl
                                  rw [hfin_eq, hw3]
                                  dsimp only []
                                  rw [pfSelectVersionWriteAt_pfLeft_nil ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j))]
                                  simp [pfLeftChildPath, termAt, Option.map]
                  | false =>
                      have hcond_a : ((ver3Code tVer).val ≥ 1 && ((ver3Code tVer).val - 1) / 2 == 0) = false :=
                        hm.2.1.trans hmatch
                      have hstep : pocketStepTD 22
                          (ann 18 (.s ⋅ tVer)).state (ann 22 ((.s ⋅ rest) ⋅ j)).state =
                          pocketGoFR 22 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_ge7, hqr_ge7, hql_sub, hcond_a]
                      rw_goFR (by decide : 22 < 32) hstep
                      change (loc 22 (ann 5 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih22]
                      have hfi_eq : (match pfScanVersion 3 none tVer with
                          | some [false, false, sbit] => some (pfLeftChildPath, sbit)
                          | some [true, false, _] => shiftPathBool (scanTemplates rest).firstIdle
                          | some [true, true, _] => shiftPathBool (scanTemplates rest).firstIdle
                          | _ => shiftPathBool (scanTemplates rest).firstIdle) =
                          shiftPathBool (scanTemplates rest).firstIdle := by
                        cases hsc : pfScanVersion 3 none tVer with
                        | none => rfl
                        | some bits =>
                            have hlen := pfScanVersion_length 3 tVer hsc
                            rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨sbit, _ | _⟩⟩⟩ <;> try cases hlen
                            cases b0 <;> cases b1 <;> first | rfl | (rw [hsc] at hmatch; cases hmatch)
                      -- Match on `pfScanVersion 3 none tVer` in goal to collapse `.firstIdle`:
                      have hproj : (scanTemplates ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j))).firstIdle =
                          shiftPathBool (scanTemplates rest).firstIdle := by
                        simp only [scanTemplates]
                        rw [← hfi_eq]
                        cases hsc : pfScanVersion 3 none tVer with
                        | none => rfl
                        | some bits =>
                            have hlen := pfScanVersion_length 3 tVer hsc
                            rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨sbit, _ | _⟩⟩⟩ <;> try cases hlen
                            cases b0 <;> cases b1 <;> rfl
                      change _ = match (scanTemplates ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j))).firstIdle with
                        | some (tRel, sbit) => pfSelectVersionWriteAt _ tRel 3 [true, false, sbit]
                        | none => none
                      rw [hproj]
                      cases (scanTemplates rest).firstIdle with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨tRel, sbit⟩
                          simp only [shiftPathBool, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j)) pfRightChildPath tRel]
                          simp [pfRightChildPath, termAt, Option.map]
                · -- `23` (ARMED -> `some [true, false, sbit]`):
                  cases hmatch : (match pfScanVersion 3 none tVer with | some [true, false, _] => true | _ => false) with
                  | true =>
                      cases hsc : pfScanVersion 3 none tVer with
                      | none => rw [hsc] at hmatch; cases hmatch
                      | some bits =>
                          have hlen := pfScanVersion_length 3 tVer hsc
                          rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨sbit, _ | _⟩⟩⟩ <;> try cases hlen
                          cases b0 with
                          | false => rw [hsc] at hmatch; cases hmatch
                          | true =>
                              cases b1 with
                              | true => rw [hsc] at hmatch; cases hmatch
                              | false =>
                                  have hcond_a : ((ver3Code tVer).val ≥ 1 && ((ver3Code tVer).val - 1) / 2 == 2) = true := by
                                    rw [hm.2.2.2.1, hsc]
                                  have hsbit_eq := hm.2.2.2.2.2 true false sbit hsc
                                  have hlt50 : 48 + bitNat sbit < 50 := by cases sbit <;> decide
                                  have hstep : pocketStepTD 23
                                      (ann 18 (.s ⋅ tVer)).state (ann 22 ((.s ⋅ rest) ⋅ j)).state =
                                      pocketGoFL (48 + bitNat sbit) := by
                                    rw [ann_state_eq hl, ann_state_eq hr]
                                    unfold pocketStepTD; dsimp only []
                                    simp [hql_ge7, hqr_ge7, hql_sub, hcond_a, hsbit_eq]
                                  rw_goFL hlt50 hstep
                                  change (loc (fin136 (48 + bitNat sbit)) (ann 8 tVer)).map (pfLeftChildPath ++ ·) = _
                                  have hw3 := loc_writeVer3 true true sbit htver_closed
                                  dsimp only [] at hw3
                                  have hfin_eq : fin136 (48 + bitNat sbit) =
                                      fin136 (42 + (4 * bitNat true + 2 * bitNat true + bitNat sbit)) := by
                                    cases sbit <;> rfl
                                  rw [hfin_eq, hw3]
                                  simp only [scanTemplates, hsc]
                                  rw [pfSelectVersionWriteAt_pfLeft_nil ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j))]
                                  simp [pfLeftChildPath, termAt, Option.map]
                  | false =>
                      have hcond_a : ((ver3Code tVer).val ≥ 1 && ((ver3Code tVer).val - 1) / 2 == 2) = false :=
                        hm.2.2.2.1.trans hmatch
                      have hstep : pocketStepTD 23
                          (ann 18 (.s ⋅ tVer)).state (ann 22 ((.s ⋅ rest) ⋅ j)).state =
                          pocketGoFR 23 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_ge7, hqr_ge7, hql_sub, hcond_a]
                      rw_goFR (by decide : 23 < 32) hstep
                      change (loc 23 (ann 5 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih23]
                      have hproj : (scanTemplates ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j))).firstArmed =
                          shiftPathBool (scanTemplates rest).firstArmed := by
                        simp only [scanTemplates]
                        cases hsc : pfScanVersion 3 none tVer with
                        | none => rfl
                        | some bits =>
                            have hlen := pfScanVersion_length 3 tVer hsc
                            rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨sbit, _ | _⟩⟩⟩ <;> try cases hlen
                            cases b0 <;> cases b1 <;> first | rfl | (rw [hsc] at hmatch; cases hmatch)
                      rw [hproj]
                      cases (scanTemplates rest).firstArmed with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨tRel, sbit⟩
                          simp only [shiftPathBool, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j)) pfRightChildPath tRel]
                          simp [pfRightChildPath, termAt, Option.map]
                · -- `24` (APPD -> `some [true, true, sbit]`):
                  cases hmatch : (match pfScanVersion 3 none tVer with | some [true, true, _] => true | _ => false) with
                  | true =>
                      cases hsc : pfScanVersion 3 none tVer with
                      | none => rw [hsc] at hmatch; cases hmatch
                      | some bits =>
                          have hlen := pfScanVersion_length 3 tVer hsc
                          rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨sbit, _ | _⟩⟩⟩ <;> try cases hlen
                          cases b0 with
                          | false => rw [hsc] at hmatch; cases hmatch
                          | true =>
                              cases b1 with
                              | false => rw [hsc] at hmatch; cases hmatch
                              | true =>
                                  have hcond_a : ((ver3Code tVer).val ≥ 1 && ((ver3Code tVer).val - 1) / 2 == 3) = true := by
                                    rw [hm.2.2.2.2.1, hsc]
                                  have hsbit_eq := hm.2.2.2.2.2 true true sbit hsc
                                  have hlt50 : 42 + bitNat sbit < 50 := by cases sbit <;> decide
                                  have hstep : pocketStepTD 24
                                      (ann 18 (.s ⋅ tVer)).state (ann 22 ((.s ⋅ rest) ⋅ j)).state =
                                      pocketGoFL (42 + bitNat sbit) := by
                                    rw [ann_state_eq hl, ann_state_eq hr]
                                    unfold pocketStepTD; dsimp only []
                                    simp [hql_ge7, hqr_ge7, hql_sub, hcond_a, hsbit_eq]
                                  rw_goFL hlt50 hstep
                                  change (loc (fin136 (42 + bitNat sbit)) (ann 8 tVer)).map (pfLeftChildPath ++ ·) = _
                                  have hw3 := loc_writeVer3 false false sbit htver_closed
                                  dsimp only [] at hw3
                                  have hfin_eq : fin136 (42 + bitNat sbit) =
                                      fin136 (42 + (4 * bitNat false + 2 * bitNat false + bitNat sbit)) := by
                                    cases sbit <;> rfl
                                  rw [hfin_eq, hw3]
                                  simp only [scanTemplates, hsc]
                                  rw [pfSelectVersionWriteAt_pfLeft_nil ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j))]
                                  simp [pfLeftChildPath, termAt, Option.map]
                  | false =>
                      have hcond_a : ((ver3Code tVer).val ≥ 1 && ((ver3Code tVer).val - 1) / 2 == 3) = false :=
                        hm.2.2.2.2.1.trans hmatch
                      have hstep : pocketStepTD 24
                          (ann 18 (.s ⋅ tVer)).state (ann 22 ((.s ⋅ rest) ⋅ j)).state =
                          pocketGoFR 24 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_ge7, hqr_ge7, hql_sub, hcond_a]
                      rw_goFR (by decide : 24 < 32) hstep
                      change (loc 24 (ann 5 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih24]
                      have hproj : (scanTemplates ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j))).firstAppending =
                          shiftPathBool (scanTemplates rest).firstAppending := by
                        simp only [scanTemplates]
                        cases hsc : pfScanVersion 3 none tVer with
                        | none => rfl
                        | some bits =>
                            have hlen := pfScanVersion_length 3 tVer hsc
                            rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨sbit, _ | _⟩⟩⟩ <;> try cases hlen
                            cases b0 <;> cases b1 <;> first | rfl | (rw [hsc] at hmatch; cases hmatch)
                      rw [hproj]
                      cases (scanTemplates rest).firstAppending with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨tRel, sbit⟩
                          simp only [shiftPathBool, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ tVer) ⋅ ((.s ⋅ rest) ⋅ j)) pfRightChildPath tRel]
                          simp [pfRightChildPath, termAt, Option.map]
  exact haux (leaves u) u (Nat.le_refl _) hu

private theorem loc_qSeek {u : Term} (hu : isClosedPureS u = true) :
    (loc 16 (ann 6 u) = pfSelectOpeningAt u (scanQueue u).tailPath) ∧
    (loc 17 (ann 6 u) = match (scanQueue u).consuming with
      | some (cRel, b) => pfSelectVersionWriteAt u cRel 3 [true, true, b]
      | none => none) ∧
    (loc 18 (ann 6 u) = match (scanQueue u).unconsumed with
      | some (uRel, b) => pfSelectVersionWriteAt u uRel 3 [true, false, b]
      | none => none) ∧
    (loc 19 (ann 6 u) = match (scanQueue u).staging with
      | some (stRel, b) => pfSelectVersionWriteAt u stRel 3 [false, false, b]
      | none => none) ∧
    (∀ sbit : Bool, loc (fin136 (20 + bitNat sbit)) (ann 6 u) = match (scanQueue u).uninit with
      | some uiRel => pfSelectVersionWriteAt u uiRel 3 [false, true, sbit]
      | none => none) := by
  have haux : ∀ (B : Nat) (v : Term), leaves v ≤ B → isClosedPureS v = true →
      (loc 16 (ann 6 v) = pfSelectOpeningAt v (scanQueue v).tailPath) ∧
      (loc 17 (ann 6 v) = match (scanQueue v).consuming with
        | some (cRel, b) => pfSelectVersionWriteAt v cRel 3 [true, true, b]
        | none => none) ∧
      (loc 18 (ann 6 v) = match (scanQueue v).unconsumed with
        | some (uRel, b) => pfSelectVersionWriteAt v uRel 3 [true, false, b]
        | none => none) ∧
      (loc 19 (ann 6 v) = match (scanQueue v).staging with
        | some (stRel, b) => pfSelectVersionWriteAt v stRel 3 [false, false, b]
        | none => none) ∧
      (∀ sbit : Bool, loc (fin136 (20 + bitNat sbit)) (ann 6 v) = match (scanQueue v).uninit with
        | some uiRel => pfSelectVersionWriteAt v uiRel 3 [false, true, sbit]
        | none => none) := by
    intro B
    induction B with
    | zero =>
        intro v hle _
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure v))
    | succ B ih =>
        intro v hle hv
        cases v with
        | s =>
            refine ⟨?_, rfl, rfl, rfl, fun sb => by cases sb <;> rfl⟩
            change none = pfSelectOpeningAt .s []
            rw [pfSelectOpeningAt_nil]; rfl
        | var _ => cases hv
        | app l r =>
            have hl : isClosedPureS l = true := ((Bool.and_eq_true _ _).mp hv).1
            have hr : isClosedPureS r = true := ((Bool.and_eq_true _ _).mp hv).2
            cases hpf : parseFrame (l ⋅ r) with
            | none =>
                have hsq_none : scanQueue (l ⋅ r) = ⟨none, none, none, none, []⟩ :=
                  (parseFrame_eq_none_cases hpf).2.2.2.2.2.2.2
                rw [hsq_none]
                dsimp only []
                rw [pfSelectOpeningAt_nil]
                have hnot_both : (specBU 18 l).val < 7 ∨ (specBU 23 r).val < 7 := by
                  cases hge7 : decide ((specBU 18 l).val ≥ 7) with
                  | false => exact Or.inl (Nat.lt_of_not_le (of_decide_eq_false hge7))
                  | true =>
                      obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => (ver3Code x).val)
                        (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (ver3Code x).isLt (by decide)))).mp
                        (of_decide_eq_true hge7)
                      have hnot_s2 : ¬ ∃ sub j, r = (.s ⋅ sub) ⋅ j := by
                        rintro ⟨sub, j, rfl⟩; simp [parseFrame] at hpf
                      exact Or.inr (Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                        (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (queueCode x).isLt (by decide)))).mp hnot_s2))
                have h16 : loc 16 (ann 6 (l ⋅ r)) = nextOpeningAddress (l ⋅ r) := by
                  refine loc_stepOpen_eq (r := 6) rfl rfl hl hr ?_
                  rcases hnot_both with h1 | h2
                  · have hn : ¬ ((specBU 18 l).val ≥ 7) := by omega
                    unfold pocketStepTD; dsimp only [pocketChildRoles]; simp [hn]
                  · have hn : ¬ ((specBU 23 r).val ≥ 7) := by omega
                    unfold pocketStepTD; dsimp only [pocketChildRoles]; simp [hn]
                have hstuck : ∀ p : Fin 136, (p = 17 ∨ p = 18 ∨ p = 19 ∨ p = 20 ∨ p = 21) →
                    loc p (ann 6 (l ⋅ r)) = none := by
                  intro p hp
                  rw [loc_ann_app, ann_state_eq hl, ann_state_eq hr]
                  rcases hp with rfl | rfl | rfl | rfl | rfl <;> rcases hnot_both with h | h <;>
                  · unfold pocketStepTD; dsimp only [pocketChildRoles]; simp [h]
                refine ⟨h16, hstuck 17 (Or.inl rfl), hstuck 18 (Or.inr (Or.inl rfl)),
                  hstuck 19 (Or.inr (Or.inr (Or.inl rfl))), fun sb => ?_⟩
                cases sb
                · exact hstuck 20 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                · exact hstuck 21 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
            | some triple =>
                rcases triple with ⟨qVer, rest, j⟩
                obtain ⟨heq, _, hrest_lt⟩ := parseFrame_some_decomp hpf
                have hrest_le : leaves rest ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrest_lt hle)
                injection heq with hl_eq hr_eq
                subst hl_eq; subst hr_eq
                have hqver_closed : isClosedPureS qVer = true := ((Bool.and_eq_true _ _).mp hl).2
                have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
                have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
                obtain ⟨ih16, ih17, ih18, ih19, ih20⟩ := ih rest hrest_le hrest_closed
                have hql_ge7 : (specBU 18 (.s ⋅ qVer)).val ≥ 7 := by
                  simp only [specBU]; have hc := (ver3Code qVer).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hqr_ge7 : (specBU 23 ((.s ⋅ rest) ⋅ j)).val ≥ 7 := by
                  simp only [specBU]; have hc := (queueCode rest).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hql_nlt : ¬ ((specBU 18 (.s ⋅ qVer)).val < 7) := by omega
                have hqr_nlt : ¬ ((specBU 23 ((.s ⋅ rest) ⋅ j)).val < 7) := by omega
                have hql_sub : (specBU 18 (.s ⋅ qVer)).val - 7 = (ver3Code qVer).val := by
                  simp only [specBU]; have hc := (ver3Code qVer).isLt; rw [fin23_val_of_lt (by omega)]; omega
                have hm := ver3_match_hi2 qVer
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · -- `16` (TAIL):
                  have hstep : pocketStepTD 16
                      (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state = pocketGoFR 16 := by
                    rw [ann_state_eq hl, ann_state_eq hr]
                    unfold pocketStepTD; dsimp only []
                    simp [hql_ge7, hqr_ge7]
                  rw_goFR (by decide : 16 < 32) hstep
                  change (loc 16 (ann 6 rest)).map (pfRightChildPath ++ ·) = _
                  rw [ih16]
                  have htail_eq : (scanQueue ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))).tailPath =
                      pfRightChildPath ++ (scanQueue rest).tailPath := by
                    simp only [scanQueue]
                    cases hsc : pfScanVersion 3 none qVer with
                    | none => rfl
                    | some bits =>
                        have hlen := pfScanVersion_length 3 qVer hsc
                        rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | _⟩⟩⟩ <;> try cases hlen
                        cases b0 <;> cases b1 <;> rfl
                  rw [htail_eq, pfSelectOpeningAt_append ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j)) pfRightChildPath]
                  simp [pfRightChildPath, termAt, Option.map]
                · -- `17` (CONS -> `some [true, false, b]`):
                  cases hmatch : (match pfScanVersion 3 none qVer with | some [true, false, _] => true | _ => false) with
                  | true =>
                      cases hsc : pfScanVersion 3 none qVer with
                      | none => rw [hsc] at hmatch; cases hmatch
                      | some bits =>
                          have hlen := pfScanVersion_length 3 qVer hsc
                          rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b, _ | _⟩⟩⟩ <;> try cases hlen
                          cases b0 with
                          | false => rw [hsc] at hmatch; cases hmatch
                          | true =>
                              cases b1 with
                              | true => rw [hsc] at hmatch; cases hmatch
                              | false =>
                                  have hcond_a : ((ver3Code qVer).val ≥ 1 && ((ver3Code qVer).val - 1) / 2 == 2) = true := by
                                    rw [hm.2.2.2.1, hsc]
                                  have hb_eq := hm.2.2.2.2.2 true false b hsc
                                  have hlt50 : 48 + bitNat b < 50 := by cases b <;> decide
                                  have hstep : pocketStepTD 17
                                      (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state =
                                      pocketGoFL (48 + bitNat b) := by
                                    rw [ann_state_eq hl, ann_state_eq hr]
                                    unfold pocketStepTD; dsimp only []
                                    simp [hql_nlt, hqr_nlt, hql_sub, hcond_a, hb_eq]
                                  rw_goFL hlt50 hstep
                                  change (loc (fin136 (48 + bitNat b)) (ann 8 qVer)).map (pfLeftChildPath ++ ·) = _
                                  have hw3 := loc_writeVer3 true true b hqver_closed
                                  dsimp only [] at hw3
                                  have hfin_eq : fin136 (48 + bitNat b) =
                                      fin136 (42 + (4 * bitNat true + 2 * bitNat true + bitNat b)) := by
                                    cases b <;> rfl
                                  rw [hfin_eq, hw3]
                                  simp only [scanQueue, hsc]
                                  rw [pfSelectVersionWriteAt_pfLeft_nil ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))]
                                  simp [pfLeftChildPath, termAt, Option.map]
                  | false =>
                      have hcond_a : ((ver3Code qVer).val ≥ 1 && ((ver3Code qVer).val - 1) / 2 == 2) = false :=
                        hm.2.2.2.1.trans hmatch
                      have hstep : pocketStepTD 17
                          (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state = pocketGoFR 17 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_nlt, hqr_nlt, hql_sub, hcond_a]
                      rw_goFR (by decide : 17 < 32) hstep
                      change (loc 17 (ann 6 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih17]
                      have hproj : (scanQueue ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))).consuming =
                          shiftPathBool (scanQueue rest).consuming := by
                        simp only [scanQueue]
                        cases hsc : pfScanVersion 3 none qVer with
                        | none => rfl
                        | some bits =>
                            have hlen := pfScanVersion_length 3 qVer hsc
                            rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b, _ | _⟩⟩⟩ <;> try cases hlen
                            cases b0 <;> cases b1 <;> first | rfl | (rw [hsc] at hmatch; cases hmatch)
                      rw [hproj]
                      cases (scanQueue rest).consuming with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨cRel, b⟩
                          simp only [shiftPathBool, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j)) pfRightChildPath cRel]
                          simp [pfRightChildPath, termAt, Option.map]
                · -- `18` (UNCONS -> `some [false, false, b]`):
                  cases hmatch : (match pfScanVersion 3 none qVer with | some [false, false, _] => true | _ => false) with
                  | true =>
                      cases hsc : pfScanVersion 3 none qVer with
                      | none => rw [hsc] at hmatch; cases hmatch
                      | some bits =>
                          have hlen := pfScanVersion_length 3 qVer hsc
                          rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b, _ | _⟩⟩⟩ <;> try cases hlen
                          cases b0 with
                          | true => rw [hsc] at hmatch; cases hmatch
                          | false =>
                              cases b1 with
                              | true => rw [hsc] at hmatch; cases hmatch
                              | false =>
                                  have hcond_a : ((ver3Code qVer).val ≥ 1 && ((ver3Code qVer).val - 1) / 2 == 0) = true := by
                                    rw [hm.2.1, hsc]
                                  have hb_eq := hm.2.2.2.2.2 false false b hsc
                                  have hlt50 : 46 + bitNat b < 50 := by cases b <;> decide
                                  have hstep : pocketStepTD 18
                                      (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state =
                                      pocketGoFL (46 + bitNat b) := by
                                    rw [ann_state_eq hl, ann_state_eq hr]
                                    unfold pocketStepTD; dsimp only []
                                    simp [hql_nlt, hqr_nlt, hql_sub, hcond_a, hb_eq]
                                  rw_goFL hlt50 hstep
                                  change (loc (fin136 (46 + bitNat b)) (ann 8 qVer)).map (pfLeftChildPath ++ ·) = _
                                  have hw3 := loc_writeVer3 true false b hqver_closed
                                  dsimp only [] at hw3
                                  have hfin_eq : fin136 (46 + bitNat b) =
                                      fin136 (42 + (4 * bitNat true + 2 * bitNat false + bitNat b)) := by
                                    cases b <;> rfl
                                  rw [hfin_eq, hw3]
                                  simp only [scanQueue, hsc]
                                  rw [pfSelectVersionWriteAt_pfLeft_nil ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))]
                                  simp [pfLeftChildPath, termAt, Option.map]
                  | false =>
                      have hcond_a : ((ver3Code qVer).val ≥ 1 && ((ver3Code qVer).val - 1) / 2 == 0) = false :=
                        hm.2.1.trans hmatch
                      have hstep : pocketStepTD 18
                          (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state = pocketGoFR 18 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_nlt, hqr_nlt, hql_sub, hcond_a]
                      rw_goFR (by decide : 18 < 32) hstep
                      change (loc 18 (ann 6 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih18]
                      have hproj : (scanQueue ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))).unconsumed =
                          shiftPathBool (scanQueue rest).unconsumed := by
                        simp only [scanQueue]
                        cases hsc : pfScanVersion 3 none qVer with
                        | none => rfl
                        | some bits =>
                            have hlen := pfScanVersion_length 3 qVer hsc
                            rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b, _ | _⟩⟩⟩ <;> try cases hlen
                            cases b0 <;> cases b1 <;> first | rfl | (rw [hsc] at hmatch; cases hmatch)
                      rw [hproj]
                      cases (scanQueue rest).unconsumed with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨uRel, b⟩
                          simp only [shiftPathBool, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j)) pfRightChildPath uRel]
                          simp [pfRightChildPath, termAt, Option.map]
                · -- `19` (STAG -> `some [false, true, b]`):
                  cases hmatch : (match pfScanVersion 3 none qVer with | some [false, true, _] => true | _ => false) with
                  | true =>
                      cases hsc : pfScanVersion 3 none qVer with
                      | none => rw [hsc] at hmatch; cases hmatch
                      | some bits =>
                          have hlen := pfScanVersion_length 3 qVer hsc
                          rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b, _ | _⟩⟩⟩ <;> try cases hlen
                          cases b0 with
                          | true => rw [hsc] at hmatch; cases hmatch
                          | false =>
                              cases b1 with
                              | false => rw [hsc] at hmatch; cases hmatch
                              | true =>
                                  have hcond_a : ((ver3Code qVer).val ≥ 1 && ((ver3Code qVer).val - 1) / 2 == 1) = true := by
                                    rw [hm.2.2.1, hsc]
                                  have hb_eq := hm.2.2.2.2.2 false true b hsc
                                  have hlt50 : 42 + bitNat b < 50 := by cases b <;> decide
                                  have hstep : pocketStepTD 19
                                      (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state =
                                      pocketGoFL (42 + bitNat b) := by
                                    rw [ann_state_eq hl, ann_state_eq hr]
                                    unfold pocketStepTD; dsimp only []
                                    simp [hql_nlt, hqr_nlt, hql_sub, hcond_a, hb_eq]
                                  rw_goFL hlt50 hstep
                                  change (loc (fin136 (42 + bitNat b)) (ann 8 qVer)).map (pfLeftChildPath ++ ·) = _
                                  have hw3 := loc_writeVer3 false false b hqver_closed
                                  dsimp only [] at hw3
                                  have hfin_eq : fin136 (42 + bitNat b) =
                                      fin136 (42 + (4 * bitNat false + 2 * bitNat false + bitNat b)) := by
                                    cases b <;> rfl
                                  rw [hfin_eq, hw3]
                                  simp only [scanQueue, hsc]
                                  rw [pfSelectVersionWriteAt_pfLeft_nil ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))]
                                  simp [pfLeftChildPath, termAt, Option.map]
                  | false =>
                      have hcond_a : ((ver3Code qVer).val ≥ 1 && ((ver3Code qVer).val - 1) / 2 == 1) = false :=
                        hm.2.2.1.trans hmatch
                      have hstep : pocketStepTD 19
                          (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state = pocketGoFR 19 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_nlt, hqr_nlt, hql_sub, hcond_a]
                      rw_goFR (by decide : 19 < 32) hstep
                      change (loc 19 (ann 6 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih19]
                      have hproj : (scanQueue ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))).staging =
                          shiftPathBool (scanQueue rest).staging := by
                        simp only [scanQueue]
                        cases hsc : pfScanVersion 3 none qVer with
                        | none => rfl
                        | some bits =>
                            have hlen := pfScanVersion_length 3 qVer hsc
                            rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b, _ | _⟩⟩⟩ <;> try cases hlen
                            cases b0 <;> cases b1 <;> first | rfl | (rw [hsc] at hmatch; cases hmatch)
                      rw [hproj]
                      cases (scanQueue rest).staging with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨stRel, b⟩
                          simp only [shiftPathBool, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j)) pfRightChildPath stRel]
                          simp [pfRightChildPath, termAt, Option.map]
                · -- `20 + bitNat sbit` (UNINIT -> `none`):
                  intro sbit
                  cases hsc : pfScanVersion 3 none qVer with
                  | none =>
                      have ha0 : ((ver3Code qVer).val == 0) = true := by rw [hm.1, hsc]; rfl
                      have hlt50 : 44 + bitNat sbit < 50 := by cases sbit <;> decide
                      have hstep : pocketStepTD (fin136 (20 + bitNat sbit))
                          (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state =
                          pocketGoFL (44 + bitNat sbit) := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        cases sbit <;>
                        · unfold pocketStepTD; dsimp only [bitNat]
                          simp [hql_nlt, hqr_nlt, hql_sub, ha0]
                      rw_goFL hlt50 hstep
                      change (loc (fin136 (44 + bitNat sbit)) (ann 8 qVer)).map (pfLeftChildPath ++ ·) = _
                      have hw3 := loc_writeVer3 false true sbit hqver_closed
                      dsimp only [] at hw3
                      have hfin_eq : fin136 (44 + bitNat sbit) =
                          fin136 (42 + (4 * bitNat false + 2 * bitNat true + bitNat sbit)) := by
                        cases sbit <;> rfl
                      rw [hfin_eq, hw3]
                      simp only [scanQueue, hsc]
                      rw [pfSelectVersionWriteAt_pfLeft_nil ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))]
                      simp [pfLeftChildPath, termAt, Option.map]
                  | some bits =>
                      have ha0 : ((ver3Code qVer).val == 0) = false := by rw [hm.1, hsc]; rfl
                      have hlt32 : 20 + bitNat sbit < 32 := by cases sbit <;> decide
                      have hstep : pocketStepTD (fin136 (20 + bitNat sbit))
                          (ann 18 (.s ⋅ qVer)).state (ann 23 ((.s ⋅ rest) ⋅ j)).state =
                          pocketGoFR (20 + bitNat sbit) := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        cases sbit <;>
                        · unfold pocketStepTD; dsimp only [bitNat]
                          simp [hql_nlt, hqr_nlt, hql_sub, ha0]
                      rw_goFR hlt32 hstep
                      change (loc (fin136 (20 + bitNat sbit)) (ann 6 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih20 sbit]
                      have hproj : (scanQueue ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j))).uninit =
                          shiftOptPath (scanQueue rest).uninit := by
                        have hlen := pfScanVersion_length 3 qVer hsc
                        simp only [scanQueue, hsc]
                        rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b, _ | _⟩⟩⟩ <;> try cases hlen
                        cases b0 <;> cases b1 <;> rfl
                      rw [hproj]
                      cases (scanQueue rest).uninit with
                      | none => rfl
                      | some uiRel =>
                          simp only [shiftOptPath, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ qVer) ⋅ ((.s ⋅ rest) ⋅ j)) pfRightChildPath uiRel]
                          simp [pfRightChildPath, termAt, Option.map]
  exact haux (leaves u) u (Nat.le_refl _) hu

/-! ### 4.4 Correctness of `BODY` (`p = 33..38`) and `PH_SEEK` (`p = 25..32`) -/

private theorem loc_bodyVer (k : Fin 3) {pVer tList jb : Term}
    (hb : isClosedPureS ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)) = true) :
    loc (fin136 (33 + k.val)) (ann 4 ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))) =
      pfSelectVersionWriteAt ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)) [false, true] 2 (wv2TargetBits k) := by
  have hl : isClosedPureS (.s ⋅ pVer) = true := ((Bool.and_eq_true _ _).mp hb).1
  have hr : isClosedPureS ((.s ⋅ tList) ⋅ jb) = true := ((Bool.and_eq_true _ _).mp hb).2
  have hpv : isClosedPureS pVer = true := ((Bool.and_eq_true _ _).mp hl).2
  have hql_ge7 : (specBU 17 (.s ⋅ pVer)).val ≥ 7 := by
    simp only [specBU]; have hc := (ver2Code pVer).isLt; rw [fin23_val_of_lt (by omega)]; omega
  have hqr_ge7 : (specBU 22 ((.s ⋅ tList) ⋅ jb)).val ≥ 7 := by
    simp only [specBU]; have hc := (tmplCode tList).isLt; rw [fin23_val_of_lt (by omega)]; omega
  have h39_lt : 39 + k.val < 50 := by have hk := k.isLt; omega
  have hstep : pocketStepTD (fin136 (33 + k.val))
      (ann 17 (.s ⋅ pVer)).state (ann 22 ((.s ⋅ tList) ⋅ jb)).state =
      pocketGoFL (39 + k.val) := by
    rw [ann_state_eq hl, ann_state_eq hr]
    rcases k with ⟨kv, hkv⟩
    match kv with
    | 0 | 1 | 2 => unfold pocketStepTD; simp [hql_ge7, hqr_ge7]
    | _ + 3 => omega
  rw_goFL h39_lt hstep
  change (loc (fin136 (39 + k.val)) (ann 7 pVer)).map (pfLeftChildPath ++ ·) = _
  rw [loc_writeVer2 k hpv]
  rw [pfSelectVersionWriteAt_left_nil ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))]
  simp [pfLeftChildPath, termAt, Option.map]

private theorem loc_bodyTmpl (k : Fin 3) {pVer tList jb : Term}
    (hb : isClosedPureS ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)) = true) :
    loc (fin136 (36 + k.val)) (ann 4 ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))) =
      (loc (fin136 (22 + k.val)) (ann 5 tList)).map (pfRightChildPath ++ ·) := by
  have hl : isClosedPureS (.s ⋅ pVer) = true := ((Bool.and_eq_true _ _).mp hb).1
  have hr : isClosedPureS ((.s ⋅ tList) ⋅ jb) = true := ((Bool.and_eq_true _ _).mp hb).2
  have hql_ge7 : (specBU 17 (.s ⋅ pVer)).val ≥ 7 := by
    simp only [specBU]; have hc := (ver2Code pVer).isLt; rw [fin23_val_of_lt (by omega)]; omega
  have hqr_ge7 : (specBU 22 ((.s ⋅ tList) ⋅ jb)).val ≥ 7 := by
    simp only [specBU]; have hc := (tmplCode tList).isLt; rw [fin23_val_of_lt (by omega)]; omega
  have h22_lt : 22 + k.val < 32 := by have hk := k.isLt; omega
  have hstep : pocketStepTD (fin136 (36 + k.val))
      (ann 17 (.s ⋅ pVer)).state (ann 22 ((.s ⋅ tList) ⋅ jb)).state =
      pocketGoFR (22 + k.val) := by
    rw [ann_state_eq hl, ann_state_eq hr]
    rcases k with ⟨kv, hkv⟩
    match kv with
    | 0 | 1 | 2 => unfold pocketStepTD; simp [hql_ge7, hqr_ge7]
    | _ + 3 => omega
  rw_goFR h22_lt hstep; rfl

private theorem findIdxPred_lt_length {α : Type} (p : α → Bool) :
    ∀ (xs : List α) {idx : Nat} {val : α},
      findIdxPred p xs = some (idx, val) → idx < xs.length
  | [], _, _, h => by cases h
  | x :: xs, idx, val, h => by
      simp only [findIdxPred] at h
      cases hp : p x with
      | true =>
          rw [hp] at h; injection h with hp_eq
          injection hp_eq with hidx _; subst hidx
          exact Nat.zero_lt_succ _
      | false =>
          rw [hp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hsub : findIdxPred p xs with
          | none => rw [hsub] at h; cases h
          | some pair =>
              rw [hsub] at h
              injection h with hp_eq
              injection hp_eq with hidx _
              subst hidx
              exact Nat.succ_lt_succ (findIdxPred_lt_length p xs hsub)

private theorem listGetOpt_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Nat), listGetOpt (xs.map f) i = (listGetOpt xs i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => listGetOpt_map f xs i

private theorem progRing_flags_decode (ps : List PhaseEntry) :
    let rest := (phasesSummaryCode ps).val
    let bEmpty := rest == 0
    let bFA := if 1 ≤ rest && rest ≤ 4 then (rest - 1) / 2 == 1
               else if rest ≥ 6 then (rest - 6) / 8 == 1
               else false
    let bHL := if 1 ≤ rest && rest ≤ 4 then (rest - 1) % 2 == 1 else false
    (bEmpty = decide (ps = [])) ∧
    (∀ e0 es, ps = e0 :: es → bFA = (e0.status == some [true, false])) ∧
    (∀ hIdx hE, findIdxPred (fun pe => pe.status == some [true, true]) ps = some (hIdx, hE) →
      bHL = (hIdx + 1 == ps.length)) := by
  have hr := phasesSummaryCode_range ps
  refine ⟨?_, ?_, ?_⟩
  · cases ps with
    | nil => rfl
    | cons e0 es =>
        have hne0 : (phasesSummaryCode (e0 :: es)).val ≠ 0 := by
          intro h0; cases hr.1.mpr (Fin.ext h0)
        exact nat_beq_of_ne hne0
  · intro e0 es hps
    subst hps
    unfold phasesSummaryCode
    dsimp only []
    cases hh : findIdxPred (fun pe => pe.status == some [true, true]) (e0 :: es) with
    | some pair =>
        rcases pair with ⟨hIdx, _⟩
        have hall : ∀ (fa hl : Bool),
            (let rest := (fin22 (1 + 2 * bitNat fa + bitNat hl)).val
             if 1 ≤ rest && rest ≤ 4 then (rest - 1) / 2 == 1
             else if rest ≥ 6 then (rest - 6) / 8 == 1
             else false) = fa := by decide
        exact hall (e0.status == some [true, false]) (hIdx + 1 == (e0 :: es).length)
    | none =>
        cases ha : findIdxPred (fun pe => pe.status == some [true, false]) (e0 :: es) with
        | none =>
            simp only [findIdxPred] at ha
            cases hb : (e0.status == some [true, false]) with
            | true => simp [hb] at ha
            | false =>
                exact (by decide :
                  (let rest := (5 : Fin 22).val
                   if 1 ≤ rest && rest ≤ 4 then (rest - 1) / 2 == 1
                   else if rest ≥ 6 then (rest - 6) / 8 == 1
                   else false) = false)
        | some pair =>
            rcases pair with ⟨_, actE⟩
            have hall : ∀ (t : Fin 8) (fa : Bool),
                (let rest := (fin22 (6 + 8 * bitNat fa + t.val)).val
                 if 1 ≤ rest && rest ≤ 4 then (rest - 1) / 2 == 1
                 else if rest ≥ 6 then (rest - 6) / 8 == 1
                 else false) = fa := by decide
            exact hall (tmplSummaryCode actE.templates) (e0.status == some [true, false])
  · intro hIdx hE hh
    cases ps with
    | nil => cases hh
    | cons e0 es =>
        unfold phasesSummaryCode
        dsimp only []
        rw [hh]
        have hall : ∀ (fa hl : Bool),
            (let rest := (fin22 (1 + 2 * bitNat fa + bitNat hl)).val
             if 1 ≤ rest && rest ≤ 4 then (rest - 1) % 2 == 1 else false) = hl := by decide
        exact hall (e0.status == some [true, false]) (hIdx + 1 == (e0 :: es).length)

private theorem scanPhases_nonempty_decomp {u : Term} {e0 : PhaseEntry} {es : List PhaseEntry}
    (hsp : scanPhases u = e0 :: es) :
    ∃ pVer tList jb rest jr,
      u = (.s ⋅ ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))) ⋅ ((.s ⋅ rest) ⋅ jr) ∧
      e0 = { verPath := [false, true, false, true]
             tListPath := [false, true, true, false, true]
             status := pfScanVersion 2 none pVer
             templates := scanTemplates tList } ∧
      es = (scanPhases rest).map shiftPhaseEntry ∧
      leaves rest < leaves u := by
  unfold scanPhases at hsp
  split at hsp
  · rename_i pVer tList jb rest jr
    injection hsp with he0 hes
    have h1 := PocketTreeTransducer.leaves_pos_pure pVer
    have h2 := PocketTreeTransducer.leaves_pos_pure tList
    have h3 := PocketTreeTransducer.leaves_pos_pure jb
    have h4 := PocketTreeTransducer.leaves_pos_pure jr
    refine ⟨pVer, tList, jb, rest, jr, rfl, he0.symm, hes.symm, ?_⟩
    simp only [leaves]; omega
  · cases hsp

private theorem loc_ph_headSetActive {u : Term} (hu : isClosedPureS u = true)
    {e0 : PhaseEntry} {es : List PhaseEntry} (hsp : scanPhases u = e0 :: es) :
    loc 25 (ann 3 u) = pfSelectVersionWriteAt u e0.verPath 2 [true, false] := by
  obtain ⟨pVer, tList, jb, rest, jr, rfl, rfl, _, _⟩ := scanPhases_nonempty_decomp hsp
  let body := (.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)
  have hl : isClosedPureS (.s ⋅ body) = true := ((Bool.and_eq_true _ _).mp hu).1
  have hr : isClosedPureS ((.s ⋅ rest) ⋅ jr) = true := ((Bool.and_eq_true _ _).mp hu).2
  have hb_closed : isClosedPureS body = true := ((Bool.and_eq_true _ _).mp hl).2
  have hbc_pos : (bodyCode body).val ≠ 0 := by
    dsimp only [body, bodyCode]
    have hall : ∀ (vc : Fin 4) (tc : Fin 8),
        (if vc.val == 1 then (1 : Fin 11) else if vc.val == 2 then fin11 (3 + tc.val) else 2).val ≠ 0 := by decide
    exact hall (ver2Code pVer) (tmplCode tList)
  have hql_nlt : ¬ ((specBU 14 (.s ⋅ body)).val < 7) := by
    simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
  have hql_sub : (specBU 14 (.s ⋅ body)).val - 7 = (bodyCode body).val := by
    simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
  have hqr_ne0 : ((specBU 21 ((.s ⋅ rest) ⋅ jr)).val == 0) = false := by
    simp only [specBU]; have hc := (progRingCode rest).isLt
    rw [fin23_val_of_lt (by omega)]; exact nat_beq_of_ne (by omega)
  have hbc_ne0 : ((bodyCode body).val == 0) = false := nat_beq_of_ne hbc_pos
  have hstep : pocketStepTD 25 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
      pocketGoFL 34 := by
    rw [ann_state_eq hl, ann_state_eq hr]
    unfold pocketStepTD; dsimp only []
    simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0]
  rw_goFL (by decide : 34 < 50) hstep
  change (loc (fin136 (33 + 1)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
  rw [loc_bodyVer ⟨1, by decide⟩ hb_closed]
  try dsimp only []
  rw [pfSelectVersionWriteAt_left2 ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr))]
  simp [pfLeftChildPath, termAt, wv2TargetBits, Option.map, body]
  try rfl

private theorem bodyCode_status_iff (pVer tList jb : Term) :
    let b := (bodyCode ((.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb))).val
    (b ≠ 0) ∧
    ((b == 1) = (pfScanVersion 2 none pVer == some [true, true])) ∧
    (decide (b ≥ 3) = (pfScanVersion 2 none pVer == some [true, false])) := by
  have hv2 := ver2Code_spec pVer
  dsimp only [bodyCode]
  have hall : ∀ (vc : Fin 4) (tc : Fin 8),
      let b := (if vc.val == 1 then (1 : Fin 11) else if vc.val == 2 then fin11 (3 + tc.val) else 2).val
      (b ≠ 0) ∧ ((b == 1) = (vc == 1)) ∧ (decide (b ≥ 3) = (vc == 2)) := by decide
  obtain ⟨h1, h2, h3⟩ := hall (ver2Code pVer) (tmplCode tList)
  exact ⟨h1, h2.trans hv2.2.1.symm, h3.trans hv2.2.2.symm⟩

private theorem loc_ph_handoffZero {u : Term} (hu : isClosedPureS u = true)
    {hIdx : Nat} {hEntry : PhaseEntry}
    (hh : findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases u) = some (hIdx, hEntry)) :
    loc 26 (ann 3 u) = pfSelectVersionWriteAt u hEntry.verPath 2 [false, false] := by
  have haux : ∀ (B : Nat) (v : Term), leaves v ≤ B → isClosedPureS v = true →
      ∀ {idx : Nat} {entry : PhaseEntry},
        findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases v) = some (idx, entry) →
        loc 26 (ann 3 v) = pfSelectVersionWriteAt v entry.verPath 2 [false, false] := by
    intro B
    induction B with
    | zero =>
        intro v hle _
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure v))
    | succ B ih =>
        intro v hle hv idx entry hfind
        cases hsp : scanPhases v with
        | nil => rw [hsp] at hfind; cases hfind
        | cons e0 es =>
            rw [hsp] at hfind
            obtain ⟨pVer, tList, jb, rest, jr, rfl, he0, hes, hrest_lt⟩ := scanPhases_nonempty_decomp hsp
            have hrest_le : leaves rest ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrest_lt hle)
            let body := (.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)
            have hl : isClosedPureS (.s ⋅ body) = true := ((Bool.and_eq_true _ _).mp hv).1
            have hr : isClosedPureS ((.s ⋅ rest) ⋅ jr) = true := ((Bool.and_eq_true _ _).mp hv).2
            have hb_closed : isClosedPureS body = true := ((Bool.and_eq_true _ _).mp hl).2
            have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
            have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
            obtain ⟨hb_ne0, hb_eq1, _⟩ := bodyCode_status_iff pVer tList jb
            have hql_nlt : ¬ ((specBU 14 (.s ⋅ body)).val < 7) := by
              simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
            have hql_sub : (specBU 14 (.s ⋅ body)).val - 7 = (bodyCode body).val := by
              simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
            have hqr_ne0 : ((specBU 21 ((.s ⋅ rest) ⋅ jr)).val == 0) = false := by
              simp only [specBU]; have hc := (progRingCode rest).isLt
              rw [fin23_val_of_lt (by omega)]; exact nat_beq_of_ne (by omega)
            have hbc_ne0 : ((bodyCode body).val == 0) = false := nat_beq_of_ne hb_ne0
            simp only [findIdxPred, he0] at hfind
            cases hh0 : (pfScanVersion 2 none pVer == some [true, true]) with
            | true =>
                rw [hh0] at hfind
                simp only [↓reduceIte] at hfind
                have hp_eq := Option.some.inj hfind
                have hent := congrArg Prod.snd hp_eq
                subst hent
                have hb1 : ((bodyCode body).val == 1) = true := hb_eq1.trans hh0
                have hstep : pocketStepTD 26 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                    pocketGoFL 33 := by
                  rw [ann_state_eq hl, ann_state_eq hr]
                  unfold pocketStepTD; dsimp only []
                  simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb1]
                rw_goFL (by decide : 33 < 50) hstep
                change (loc (fin136 (33 + 0)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
                rw [loc_bodyVer ⟨0, by decide⟩ hb_closed]
                try dsimp only []
                rw [pfSelectVersionWriteAt_left2 ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr))]
                simp [pfLeftChildPath, termAt, wv2TargetBits, Option.map, body]
                try rfl
            | false =>
                rw [hh0] at hfind
                simp only [Bool.false_eq_true, ↓reduceIte] at hfind
                rw [hes, findIdxPred_map_shift (· == some [true, true]) (scanPhases rest)] at hfind
                cases hsub : findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases rest) with
                | none => rw [hsub] at hfind; cases hfind
                | some spair =>
                    rcases spair with ⟨sIdx, sEntry⟩
                    rw [hsub] at hfind
                    simp only [Option.map] at hfind
                    have hp_eq := Option.some.inj hfind
                    have hent := congrArg Prod.snd hp_eq
                    subst hent
                    have hb1 : ((bodyCode body).val == 1) = false := hb_eq1.trans hh0
                    have hstep : pocketStepTD 26 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                        pocketGoFR 26 := by
                      rw [ann_state_eq hl, ann_state_eq hr]
                      unfold pocketStepTD; dsimp only []
                      simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb1]
                    rw_goFR (by decide : 26 < 32) hstep
                    change (loc 26 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                    rw [ih rest hrest_le hrest_closed hsub]
                    simp only [shiftPhaseEntry]
                    rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath sEntry.verPath]
                    simp [pfRightChildPath, termAt, Option.map]
  exact haux (leaves u) u (Nat.le_refl _) hu hh

private theorem loc_ph_handoffInner {u : Term} (hu : isClosedPureS u = true)
    {hIdx : Nat} {hEntry : PhaseEntry}
    (hh : findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases u) = some (hIdx, hEntry))
    (hlt : hIdx + 1 < (scanPhases u).length) :
    loc 27 (ann 3 u) =
      match listGetOpt (scanPhases u) (hIdx + 1) with
      | some nxtEntry =>
          if nxtEntry.status == some [true, false] then
            pfSelectVersionWriteAt u hEntry.verPath 2 [false, false]
          else
            pfSelectVersionWriteAt u nxtEntry.verPath 2 [true, false]
      | none => none := by
  have haux : ∀ (B : Nat) (v : Term), leaves v ≤ B → isClosedPureS v = true →
      ∀ {idx : Nat} {entry : PhaseEntry},
        findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases v) = some (idx, entry) →
        idx + 1 < (scanPhases v).length →
        loc 27 (ann 3 v) =
          match listGetOpt (scanPhases v) (idx + 1) with
          | some nxtEntry =>
              if nxtEntry.status == some [true, false] then
                pfSelectVersionWriteAt v entry.verPath 2 [false, false]
              else
                pfSelectVersionWriteAt v nxtEntry.verPath 2 [true, false]
          | none => none := by
    intro B
    induction B with
    | zero =>
        intro v hle _
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure v))
    | succ B ih =>
        intro v hle hv idx entry hfind hidx_lt
        cases hsp : scanPhases v with
        | nil => try rw [hsp] at hfind; cases hfind
        | cons e0 es =>
            try rw [hsp] at hfind
            try rw [hsp] at hidx_lt
            try rw [hsp]
            obtain ⟨pVer, tList, jb, rest, jr, rfl, he0, hes, hrest_lt⟩ := scanPhases_nonempty_decomp hsp
            have hrest_le : leaves rest ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrest_lt hle)
            let body := (.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)
            have hl : isClosedPureS (.s ⋅ body) = true := ((Bool.and_eq_true _ _).mp hv).1
            have hr : isClosedPureS ((.s ⋅ rest) ⋅ jr) = true := ((Bool.and_eq_true _ _).mp hv).2
            have hb_closed : isClosedPureS body = true := ((Bool.and_eq_true _ _).mp hl).2
            have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
            have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
            obtain ⟨hb_ne0, hb_eq1, _⟩ := bodyCode_status_iff pVer tList jb
            have hql_nlt : ¬ ((specBU 14 (.s ⋅ body)).val < 7) := by
              simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
            have hql_sub : (specBU 14 (.s ⋅ body)).val - 7 = (bodyCode body).val := by
              simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
            have hqr_ne0 : ((specBU 21 ((.s ⋅ rest) ⋅ jr)).val == 0) = false := by
              simp only [specBU]; have hc := (progRingCode rest).isLt
              rw [fin23_val_of_lt (by omega)]; exact nat_beq_of_ne (by omega)
            have hqr_sub : (specBU 21 ((.s ⋅ rest) ⋅ jr)).val - 1 = (progRingCode rest).val := by
              simp only [specBU]; have hc := (progRingCode rest).isLt; rw [fin23_val_of_lt (by omega)]; omega
            have hbc_ne0 : ((bodyCode body).val == 0) = false := nat_beq_of_ne hb_ne0
            simp only [findIdxPred, he0] at hfind
            cases hh0 : (pfScanVersion 2 none pVer == some [true, true]) with
            | true =>
                rw [hh0] at hfind
                simp only [↓reduceIte] at hfind
                have hp_eq := Option.some.inj hfind
                have hidx0 := congrArg Prod.fst hp_eq
                have hent := congrArg Prod.snd hp_eq
                subst hidx0; subst hent
                have hb1 : ((bodyCode body).val == 1) = true := hb_eq1.trans hh0
                -- Since `0 + 1 < (e0 :: es).length`, `scanPhases rest` is non-empty!
                cases hsp_rest : scanPhases rest with
                | nil => rw [hes, hsp_rest] at hidx_lt; cases Nat.lt_of_succ_lt_succ hidx_lt
                | cons r1 rs1 =>
                    rw [hes, hsp_rest]
                    simp only [List.map_cons, listGetOpt]
                    have hfa := (progRing_flags_decode (scanPhases rest)).2.1 r1 rs1 hsp_rest
                    have hst_eq : (shiftPhaseEntry r1).status = r1.status := rfl
                    rw [hst_eq]
                    cases hr1_act : (r1.status == some [true, false]) with
                    | true =>
                        have hstep : pocketStepTD 27 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                            pocketGoFL 33 := by
                          rw [ann_state_eq hl, ann_state_eq hr]
                          unfold pocketStepTD; dsimp only []
                          simp only [hql_nlt, hqr_ne0, ↓reduceIte, Bool.false_eq_true,
                            hql_sub, hbc_ne0, hb1, hqr_sub]
                          unfold progRingCode at *
                          rw [hfa, hr1_act]; rfl
                        rw_goFL (by decide : 33 < 50) hstep
                        change (loc (fin136 (33 + 0)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
                        rw [loc_bodyVer ⟨0, by decide⟩ hb_closed]
                        simp only [↓reduceIte]
                        try dsimp only []
                        rw [pfSelectVersionWriteAt_left2 ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr))]
                        simp [pfLeftChildPath, termAt, wv2TargetBits, Option.map, body]
                        try rfl
                    | false =>
                        have hstep : pocketStepTD 27 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                            pocketGoFR 25 := by
                          rw [ann_state_eq hl, ann_state_eq hr]
                          unfold pocketStepTD; dsimp only []
                          simp only [hql_nlt, hqr_ne0, ↓reduceIte, Bool.false_eq_true,
                            hql_sub, hbc_ne0, hb1, hqr_sub]
                          unfold progRingCode at *
                          rw [hfa, hr1_act]; rfl
                        rw_goFR (by decide : 25 < 32) hstep
                        change (loc 25 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                        rw [loc_ph_headSetActive hrest_closed hsp_rest]
                        simp only [Bool.false_eq_true, ↓reduceIte, shiftPhaseEntry]
                        rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath r1.verPath]
                        simp [pfRightChildPath, termAt, Option.map]
            | false =>
                rw [hh0] at hfind
                simp only [Bool.false_eq_true, ↓reduceIte] at hfind
                rw [hes, findIdxPred_map_shift (· == some [true, true]) (scanPhases rest)] at hfind
                cases hsub : findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases rest) with
                | none => rw [hsub] at hfind; cases hfind
                | some spair =>
                    rcases spair with ⟨sIdx, sEntry⟩
                    rw [hsub] at hfind
                    simp only [Option.map] at hfind
                    have hp_eq := Option.some.inj hfind
                    have hidx_s := congrArg Prod.fst hp_eq
                    have hent := congrArg Prod.snd hp_eq
                    subst hidx_s; subst hent
                    have hs_lt : sIdx + 1 < (scanPhases rest).length := by
                      rw [hes, List.length_cons, List.length_map] at hidx_lt
                      exact Nat.lt_of_succ_lt_succ hidx_lt
                    have hb1 : ((bodyCode body).val == 1) = false := hb_eq1.trans hh0
                    have hstep : pocketStepTD 27 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                        pocketGoFR 27 := by
                      rw [ann_state_eq hl, ann_state_eq hr]
                      unfold pocketStepTD; dsimp only []
                      simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb1]
                    rw_goFR (by decide : 27 < 32) hstep
                    change (loc 27 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                    rw [ih rest hrest_le hrest_closed hsub hs_lt]
                    rw [hes]
                    change _ = match listGetOpt ((scanPhases rest).map shiftPhaseEntry) (sIdx + 1) with
                      | some nxtE => _ | none => none
                    rw [listGetOpt_map]
                    cases listGetOpt (scanPhases rest) (sIdx + 1) with
                    | none => rfl
                    | some nxtR =>
                        simp only [Option.map]
                        have hst_eq : (shiftPhaseEntry nxtR).status = nxtR.status := rfl
                        rw [hst_eq]
                        cases (nxtR.status == some [true, false]) <;>
                        · simp only [↓reduceIte, Bool.false_eq_true, shiftPhaseEntry]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath]
                          simp [pfRightChildPath, termAt, Option.map]
  exact haux (leaves u) u (Nat.le_refl _) hu hh hlt

private theorem loc_ph_handoffRoot {u : Term} (hu : isClosedPureS u = true)
    {hIdx : Nat} {hEntry : PhaseEntry}
    (hh : findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases u) = some (hIdx, hEntry)) :
    loc 32 (ann 3 u) =
      if (scanPhases u).length == 1 then
        pfSelectVersionWriteAt u hEntry.verPath 2 [true, false]
      else
        match listGetOpt (scanPhases u) ((hIdx + 1) % (scanPhases u).length) with
        | some nxtEntry =>
            if nxtEntry.status == some [true, false] then
              pfSelectVersionWriteAt u hEntry.verPath 2 [false, false]
            else
              pfSelectVersionWriteAt u nxtEntry.verPath 2 [true, false]
        | none => none := by
  cases hsp : scanPhases u with
  | nil => try rw [hsp] at hh; cases hh
  | cons e0 es =>
      try rw [hsp] at hh
      try rw [hsp]
      obtain ⟨pVer, tList, jb, rest, jr, rfl, he0, hes, _⟩ := scanPhases_nonempty_decomp hsp
      let body := (.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)
      have hl : isClosedPureS (.s ⋅ body) = true := ((Bool.and_eq_true _ _).mp hu).1
      have hr : isClosedPureS ((.s ⋅ rest) ⋅ jr) = true := ((Bool.and_eq_true _ _).mp hu).2
      have hb_closed : isClosedPureS body = true := ((Bool.and_eq_true _ _).mp hl).2
      have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
      have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
      obtain ⟨hb_ne0, hb_eq1, hb_ge3⟩ := bodyCode_status_iff pVer tList jb
      have hql_nlt : ¬ ((specBU 14 (.s ⋅ body)).val < 7) := by
        simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
      have hql_sub : (specBU 14 (.s ⋅ body)).val - 7 = (bodyCode body).val := by
        simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
      have hqr_ne0 : ((specBU 21 ((.s ⋅ rest) ⋅ jr)).val == 0) = false := by
        simp only [specBU]; have hc := (progRingCode rest).isLt
        rw [fin23_val_of_lt (by omega)]; exact nat_beq_of_ne (by omega)
      have hqr_sub : (specBU 21 ((.s ⋅ rest) ⋅ jr)).val - 1 = (progRingCode rest).val := by
        simp only [specBU]; have hc := (progRingCode rest).isLt; rw [fin23_val_of_lt (by omega)]; omega
      have hbc_ne0 : ((bodyCode body).val == 0) = false := nat_beq_of_ne hb_ne0
      have hflags := progRing_flags_decode (scanPhases rest)
      simp only [findIdxPred, he0] at hh
      cases hh0 : (pfScanVersion 2 none pVer == some [true, true]) with
      | true =>
          rw [hh0] at hh; simp only [↓reduceIte] at hh
          have hp_eq := Option.some.inj hh
          have hidx0 := congrArg Prod.fst hp_eq
          have hent := congrArg Prod.snd hp_eq
          subst hidx0; subst hent
          have hb1 : ((bodyCode body).val == 1) = true := hb_eq1.trans hh0
          cases hsp_rest : scanPhases rest with
          | nil =>
              rw [hes, hsp_rest]
              simp only [List.map_nil, List.length_singleton]
              have h11 : ((1 : Nat) == 1) = true := rfl
              rw [h11, if_pos rfl]
              have hstep : pocketStepTD 32 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                  pocketGoFL 34 := by
                rw [ann_state_eq hl, ann_state_eq hr]
                unfold pocketStepTD; dsimp only []
                simp only [hql_nlt, hqr_ne0, ↓reduceIte, Bool.false_eq_true,
                  hql_sub, hbc_ne0, hb1, hqr_sub]
                unfold progRingCode
                rw [hsp_rest]; rfl
              rw_goFL (by decide : 34 < 50) hstep
              change (loc (fin136 (33 + 1)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
              rw [loc_bodyVer ⟨1, by decide⟩ hb_closed]
              try dsimp only []
              rw [pfSelectVersionWriteAt_left2 ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr))]
              simp [pfLeftChildPath, termAt, wv2TargetBits, Option.map, body]
              try rfl
          | cons r1 rs1 =>
              rw [hes, hsp_rest]
              simp only [List.map_cons, List.length_cons, List.length_map]
              have hlen_ne1 : (rs1.length + 1 + 1 == 1) = false :=
                nat_beq_of_ne (by omega)
              have hmod1 : (0 + 1) % (rs1.length + 1 + 1) = 1 :=
                Nat.mod_eq_of_lt (by omega)
              simp only [hlen_ne1, Bool.false_eq_true, ↓reduceIte, hmod1, listGetOpt]
              have hfa := hflags.2.1 r1 rs1 hsp_rest
              have hbe : decide (scanPhases rest = []) = false := by rw [hsp_rest]; rfl
              have hst_eq : (shiftPhaseEntry r1).status = r1.status := rfl
              rw [hst_eq]
              cases hr1_act : (r1.status == some [true, false]) with
              | true =>
                  have hstep : pocketStepTD 32 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                      pocketGoFL 33 := by
                    rw [ann_state_eq hl, ann_state_eq hr]
                    unfold pocketStepTD; dsimp only []
                    simp only [hql_nlt, hqr_ne0, ↓reduceIte, Bool.false_eq_true,
                      hql_sub, hbc_ne0, hb1, hqr_sub]
                    unfold progRingCode at *
                    rw [hflags.1, hbe, hfa, hr1_act]; rfl
                  rw_goFL (by decide : 33 < 50) hstep
                  change (loc (fin136 (33 + 0)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
                  rw [loc_bodyVer ⟨0, by decide⟩ hb_closed]
                  simp only [↓reduceIte]
                  try dsimp only []
                  rw [pfSelectVersionWriteAt_left2 ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr))]
                  simp [pfLeftChildPath, termAt, wv2TargetBits, Option.map, body]
                  try rfl
              | false =>
                  have hstep : pocketStepTD 32 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                      pocketGoFR 25 := by
                    rw [ann_state_eq hl, ann_state_eq hr]
                    unfold pocketStepTD; dsimp only []
                    simp only [hql_nlt, hqr_ne0, ↓reduceIte, Bool.false_eq_true,
                      hql_sub, hbc_ne0, hb1, hqr_sub]
                    unfold progRingCode at *
                    rw [hflags.1, hbe, hfa, hr1_act]; rfl
                  rw_goFR (by decide : 25 < 32) hstep
                  change (loc 25 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                  rw [loc_ph_headSetActive hrest_closed hsp_rest]
                  simp only [Bool.false_eq_true, ↓reduceIte, shiftPhaseEntry]
                  rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath r1.verPath]
                  simp [pfRightChildPath, termAt, Option.map]
      | false =>
          rw [hh0] at hh; simp only [Bool.false_eq_true, ↓reduceIte] at hh
          rw [hes, findIdxPred_map_shift (· == some [true, true]) (scanPhases rest)] at hh
          cases hsub : findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases rest) with
          | none => rw [hsub] at hh; cases hh
          | some spair =>
              rcases spair with ⟨sIdx, sEntry⟩
              rw [hsub] at hh; simp only [Option.map] at hh
              have hp_eq := Option.some.inj hh
              have hidx_s := congrArg Prod.fst hp_eq
              have hent := congrArg Prod.snd hp_eq
              subst hidx_s; subst hent
              have hb1 : ((bodyCode body).val == 1) = false := hb_eq1.trans hh0
              have hs_lt_len : sIdx < (scanPhases rest).length := findIdxPred_lt_length _ _ hsub
              have hlen_ne1 : ((e0 :: es).length == 1) = false := by
                rw [hes, List.length_cons, List.length_map]
                exact nat_beq_of_ne (by omega)
              simp only [hlen_ne1, Bool.false_eq_true, ↓reduceIte]
              have hhl := hflags.2.2 sIdx sEntry hsub
              cases hlast : (sIdx + 1 == (scanPhases rest).length) with
              | true =>
                  have heq_len := nat_beq_eq_true hlast
                  have hmod0 : (sIdx + 1 + 1) % (e0 :: es).length = 0 := by
                    rw [hes, List.length_cons, List.length_map, ← heq_len]
                    exact Nat.mod_self _
                  rw [hmod0]
                  simp only [listGetOpt, he0]
                  cases he0_act : (pfScanVersion 2 none pVer == some [true, false]) with
                  | true =>
                      have hb_ge : (bodyCode body).val ≥ 3 := of_decide_eq_true (hb_ge3.trans he0_act)
                      have hstep : pocketStepTD 32 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                          pocketGoFR 26 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp only [hql_nlt, hqr_ne0, ↓reduceIte, Bool.false_eq_true,
                          hql_sub, hbc_ne0, hb1, hqr_sub]
                        unfold progRingCode at *
                        rw [hhl, hlast]; simp [hb_ge]
                      rw_goFR (by decide : 26 < 32) hstep
                      change (loc 26 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                      rw [loc_ph_handoffZero hrest_closed hsub]
                      simp only [↓reduceIte, shiftPhaseEntry]
                      rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath sEntry.verPath]
                      simp [pfRightChildPath, termAt, Option.map]
                  | false =>
                      have hb_nge : ¬ ((bodyCode body).val ≥ 3) :=
                        of_decide_eq_false (hb_ge3.trans he0_act)
                      have hstep : pocketStepTD 32 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                          pocketGoFL 34 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp only [hql_nlt, hqr_ne0, ↓reduceIte, Bool.false_eq_true,
                          hql_sub, hbc_ne0, hb1, hqr_sub]
                        unfold progRingCode at *
                        rw [hhl, hlast]; simp [hb_nge]
                      rw_goFL (by decide : 34 < 50) hstep
                      change (loc (fin136 (33 + 1)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
                      rw [loc_bodyVer ⟨1, by decide⟩ hb_closed]
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      try dsimp only []
                      rw [pfSelectVersionWriteAt_left2 ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr))]
                      simp [pfLeftChildPath, termAt, wv2TargetBits, Option.map, body]
                      try rfl
              | false =>
                  have hne_len := nat_beq_eq_false hlast
                  have hs1_lt : sIdx + 1 < (scanPhases rest).length := by omega
                  have hmod_id : (sIdx + 1 + 1) % (e0 :: es).length = sIdx + 1 + 1 := by
                    rw [hes, List.length_cons, List.length_map]
                    exact Nat.mod_eq_of_lt (Nat.succ_lt_succ hs1_lt)
                  rw [hmod_id]
                  have hstep : pocketStepTD 32 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                      pocketGoFR 27 := by
                    rw [ann_state_eq hl, ann_state_eq hr]
                    unfold pocketStepTD; dsimp only []
                    simp only [hql_nlt, hqr_ne0, ↓reduceIte, Bool.false_eq_true,
                      hql_sub, hbc_ne0, hb1, hqr_sub]
                    unfold progRingCode at *
                    rw [hhl, hlast]; rfl
                  rw_goFR (by decide : 27 < 32) hstep
                  change (loc 27 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                  rw [loc_ph_handoffInner hrest_closed hsub hs1_lt]
                  simp only [listGetOpt, hes, listGetOpt_map]
                  cases listGetOpt (scanPhases rest) (sIdx + 1) with
                  | none => rfl
                  | some nxtR =>
                      simp only [Option.map]
                      have hst_eq : (shiftPhaseEntry nxtR).status = nxtR.status := rfl
                      rw [hst_eq]
                      cases (nxtR.status == some [true, false]) <;>
                      · simp only [↓reduceIte, Bool.false_eq_true, shiftPhaseEntry]
                        rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath]
                        simp [pfRightChildPath, termAt, Option.map]

private theorem loc_ph_active {u : Term} (hu : isClosedPureS u = true)
    {aIdx : Nat} {actEntry : PhaseEntry}
    (ha : findIdxPred (fun pe => pe.status == some [true, false]) (scanPhases u) = some (aIdx, actEntry)) :
    (loc 28 (ann 3 u) = pfSelectVersionWriteAt u actEntry.verPath 2 [true, true]) ∧
    (loc 29 (ann 3 u) = match actEntry.templates.firstIdle with
      | some (tRel, sbit) => pfSelectVersionWriteAt u (actEntry.tListPath ++ tRel) 3 [true, false, sbit]
      | none => none) ∧
    (loc 30 (ann 3 u) = match actEntry.templates.firstArmed with
      | some (tRel, sbit) => pfSelectVersionWriteAt u (actEntry.tListPath ++ tRel) 3 [true, true, sbit]
      | none => none) ∧
    (loc 31 (ann 3 u) = match actEntry.templates.firstAppending with
      | some (tRel, sbit) => pfSelectVersionWriteAt u (actEntry.tListPath ++ tRel) 3 [false, false, sbit]
      | none => none) := by
  have haux : ∀ (B : Nat) (v : Term), leaves v ≤ B → isClosedPureS v = true →
      ∀ {idx : Nat} {entry : PhaseEntry},
        findIdxPred (fun pe => pe.status == some [true, false]) (scanPhases v) = some (idx, entry) →
        (loc 28 (ann 3 v) = pfSelectVersionWriteAt v entry.verPath 2 [true, true]) ∧
        (loc 29 (ann 3 v) = match entry.templates.firstIdle with
          | some (tRel, sbit) => pfSelectVersionWriteAt v (entry.tListPath ++ tRel) 3 [true, false, sbit]
          | none => none) ∧
        (loc 30 (ann 3 v) = match entry.templates.firstArmed with
          | some (tRel, sbit) => pfSelectVersionWriteAt v (entry.tListPath ++ tRel) 3 [true, true, sbit]
          | none => none) ∧
        (loc 31 (ann 3 v) = match entry.templates.firstAppending with
          | some (tRel, sbit) => pfSelectVersionWriteAt v (entry.tListPath ++ tRel) 3 [false, false, sbit]
          | none => none) := by
    intro B
    induction B with
    | zero =>
        intro v hle _
        exact False.elim (Nat.not_lt.mpr hle (PocketTreeTransducer.leaves_pos_pure v))
    | succ B ih =>
        intro v hle hv idx entry hfind
        cases hsp : scanPhases v with
        | nil => rw [hsp] at hfind; cases hfind
        | cons e0 es =>
            rw [hsp] at hfind
            obtain ⟨pVer, tList, jb, rest, jr, rfl, he0, hes, hrest_lt⟩ := scanPhases_nonempty_decomp hsp
            have hrest_le : leaves rest ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrest_lt hle)
            let body := (.s ⋅ pVer) ⋅ ((.s ⋅ tList) ⋅ jb)
            have hl : isClosedPureS (.s ⋅ body) = true := ((Bool.and_eq_true _ _).mp hv).1
            have hr : isClosedPureS ((.s ⋅ rest) ⋅ jr) = true := ((Bool.and_eq_true _ _).mp hv).2
            have hb_closed : isClosedPureS body = true := ((Bool.and_eq_true _ _).mp hl).2
            have hstl_closed : isClosedPureS ((.s ⋅ tList) ⋅ jb) = true := ((Bool.and_eq_true _ _).mp hb_closed).2
            have htl_closed1 : isClosedPureS (.s ⋅ tList) = true := ((Bool.and_eq_true _ _).mp hstl_closed).1
            have htlist_closed : isClosedPureS tList = true := ((Bool.and_eq_true _ _).mp htl_closed1).2
            have hsr_closed : isClosedPureS (.s ⋅ rest) = true := ((Bool.and_eq_true _ _).mp hr).1
            have hrest_closed : isClosedPureS rest = true := ((Bool.and_eq_true _ _).mp hsr_closed).2
            obtain ⟨hb_ne0, _, hb_ge3⟩ := bodyCode_status_iff pVer tList jb
            have hql_nlt : ¬ ((specBU 14 (.s ⋅ body)).val < 7) := by
              simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
            have hql_sub : (specBU 14 (.s ⋅ body)).val - 7 = (bodyCode body).val := by
              simp only [specBU]; have hc := (bodyCode body).isLt; rw [fin23_val_of_lt (by omega)]; omega
            have hqr_ne0 : ((specBU 21 ((.s ⋅ rest) ⋅ jr)).val == 0) = false := by
              simp only [specBU]; have hc := (progRingCode rest).isLt
              rw [fin23_val_of_lt (by omega)]; exact nat_beq_of_ne (by omega)
            have hbc_ne0 : ((bodyCode body).val == 0) = false := nat_beq_of_ne hb_ne0
            simp only [findIdxPred, he0] at hfind
            cases ha0 : (pfScanVersion 2 none pVer == some [true, false]) with
            | true =>
                rw [ha0] at hfind; simp only [↓reduceIte] at hfind
                have hp_eq := Option.some.inj hfind
                have hent := congrArg Prod.snd hp_eq
                subst hent
                have hb_ge : (bodyCode body).val ≥ 3 := of_decide_eq_true (hb_ge3.trans ha0)
                obtain ⟨ht22, ht23, ht24⟩ := loc_tSeek htlist_closed
                refine ⟨?_, ?_, ?_, ?_⟩
                · have hstep : pocketStepTD 28 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                      pocketGoFL 35 := by
                    rw [ann_state_eq hl, ann_state_eq hr]
                    unfold pocketStepTD; dsimp only []
                    simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb_ge]
                  rw_goFL (by decide : 35 < 50) hstep
                  change (loc (fin136 (33 + 2)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
                  rw [loc_bodyVer ⟨2, by decide⟩ hb_closed]
                  try dsimp only []
                  rw [pfSelectVersionWriteAt_left2 ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr))]
                  simp [pfLeftChildPath, termAt, wv2TargetBits, Option.map, body]
                  try rfl
                · have hstep : pocketStepTD 29 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                      pocketGoFL 36 := by
                    rw [ann_state_eq hl, ann_state_eq hr]
                    unfold pocketStepTD; dsimp only []
                    simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb_ge]
                  rw_goFL (by decide : 36 < 50) hstep
                  change (loc (fin136 (36 + 0)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
                  rw [loc_bodyTmpl ⟨0, by decide⟩ hb_closed]
                  change ((loc 22 (ann 5 tList)).map (pfRightChildPath ++ ·)).map (pfLeftChildPath ++ ·) = _
                  rw [ht22]
                  dsimp only []
                  cases (scanTemplates tList).firstIdle with
                  | none => rfl
                  | some pair =>
                      rcases pair with ⟨tRel, sbit⟩
                      simp only [Option.map]
                      have hpath : ([false, true, true, false, true] : List Bool) ++ tRel =
                          pfLeftChildPath ++ (pfRightChildPath ++ tRel) := rfl
                      rw [hpath,
                          pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfLeftChildPath]
                      dsimp only [pfLeftChildPath, termAt]
                      rw [term_at_nil]
                      dsimp only [Bind.bind, Option.bind]
                      rw [pfSelectVersionWriteAt_shift body pfRightChildPath]
                      simp [pfRightChildPath, termAt, body, Option.map]
                · have hstep : pocketStepTD 30 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                      pocketGoFL 37 := by
                    rw [ann_state_eq hl, ann_state_eq hr]
                    unfold pocketStepTD; dsimp only []
                    simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb_ge]
                  rw_goFL (by decide : 37 < 50) hstep
                  change (loc (fin136 (36 + 1)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
                  rw [loc_bodyTmpl ⟨1, by decide⟩ hb_closed]
                  change ((loc 23 (ann 5 tList)).map (pfRightChildPath ++ ·)).map (pfLeftChildPath ++ ·) = _
                  rw [ht23]
                  dsimp only []
                  cases (scanTemplates tList).firstArmed with
                  | none => rfl
                  | some pair =>
                      rcases pair with ⟨tRel, sbit⟩
                      simp only [Option.map]
                      have hpath : ([false, true, true, false, true] : List Bool) ++ tRel =
                          pfLeftChildPath ++ (pfRightChildPath ++ tRel) := rfl
                      rw [hpath,
                          pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfLeftChildPath]
                      dsimp only [pfLeftChildPath, termAt]
                      rw [term_at_nil]
                      dsimp only [Bind.bind, Option.bind]
                      rw [pfSelectVersionWriteAt_shift body pfRightChildPath]
                      simp [pfRightChildPath, termAt, body, Option.map]
                · have hstep : pocketStepTD 31 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                      pocketGoFL 38 := by
                    rw [ann_state_eq hl, ann_state_eq hr]
                    unfold pocketStepTD; dsimp only []
                    simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb_ge]
                  rw_goFL (by decide : 38 < 50) hstep
                  change (loc (fin136 (36 + 2)) (ann 4 body)).map (pfLeftChildPath ++ ·) = _
                  rw [loc_bodyTmpl ⟨2, by decide⟩ hb_closed]
                  change ((loc 24 (ann 5 tList)).map (pfRightChildPath ++ ·)).map (pfLeftChildPath ++ ·) = _
                  rw [ht24]
                  dsimp only []
                  cases (scanTemplates tList).firstAppending with
                  | none => rfl
                  | some pair =>
                      rcases pair with ⟨tRel, sbit⟩
                      simp only [Option.map]
                      have hpath : ([false, true, true, false, true] : List Bool) ++ tRel =
                          pfLeftChildPath ++ (pfRightChildPath ++ tRel) := rfl
                      rw [hpath,
                          pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfLeftChildPath]
                      dsimp only [pfLeftChildPath, termAt]
                      rw [term_at_nil]
                      dsimp only [Bind.bind, Option.bind]
                      rw [pfSelectVersionWriteAt_shift body pfRightChildPath]
                      simp [pfRightChildPath, termAt, body, Option.map]
            | false =>
                rw [ha0] at hfind; simp only [Bool.false_eq_true, ↓reduceIte] at hfind
                rw [hes, findIdxPred_map_shift (· == some [true, false]) (scanPhases rest)] at hfind
                cases hsub : findIdxPred (fun pe => pe.status == some [true, false]) (scanPhases rest) with
                | none => rw [hsub] at hfind; cases hfind
                | some spair =>
                    rcases spair with ⟨sIdx, sEntry⟩
                    rw [hsub] at hfind; simp only [Option.map] at hfind
                    have hp_eq := Option.some.inj hfind
                    have hent := congrArg Prod.snd hp_eq
                    subst hent
                    have hb_nge : ¬ ((bodyCode body).val ≥ 3) := of_decide_eq_false (hb_ge3.trans ha0)
                    obtain ⟨ih28, ih29, ih30, ih31⟩ := ih rest hrest_le hrest_closed hsub
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · have hstep : pocketStepTD 28 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                          pocketGoFR 28 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb_nge]
                      rw_goFR (by decide : 28 < 32) hstep
                      change (loc 28 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih28]
                      simp only [shiftPhaseEntry]
                      rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath]
                      simp [pfRightChildPath, termAt, Option.map]
                    · have hstep : pocketStepTD 29 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                          pocketGoFR 29 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb_nge]
                      rw_goFR (by decide : 29 < 32) hstep
                      change (loc 29 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih29]
                      simp only [shiftPhaseEntry]
                      cases sEntry.templates.firstIdle with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨tRel, sbit⟩
                          simp only [List.append_assoc, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath]
                          simp [pfRightChildPath, termAt, Option.map]
                    · have hstep : pocketStepTD 30 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                          pocketGoFR 30 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb_nge]
                      rw_goFR (by decide : 30 < 32) hstep
                      change (loc 30 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih30]
                      simp only [shiftPhaseEntry]
                      cases sEntry.templates.firstArmed with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨tRel, sbit⟩
                          simp only [List.append_assoc, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath]
                          simp [pfRightChildPath, termAt, Option.map]
                    · have hstep : pocketStepTD 31 (ann 14 (.s ⋅ body)).state (ann 21 ((.s ⋅ rest) ⋅ jr)).state =
                          pocketGoFR 31 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_nlt, hqr_ne0, hql_sub, hbc_ne0, hb_nge]
                      rw_goFR (by decide : 31 < 32) hstep
                      change (loc 31 (ann 3 rest)).map (pfRightChildPath ++ ·) = _
                      rw [ih31]
                      simp only [shiftPhaseEntry]
                      cases sEntry.templates.firstAppending with
                      | none => rfl
                      | some pair =>
                          rcases pair with ⟨tRel, sbit⟩
                          simp only [List.append_assoc, Option.map]
                          rw [pfSelectVersionWriteAt_shift ((.s ⋅ body) ⋅ ((.s ⋅ rest) ⋅ jr)) pfRightChildPath]
                          simp [pfRightChildPath, termAt, Option.map]
  exact haux (leaves u) u (Nat.le_refl _) hu ha

/-! ### 4.5 Correctness of `PAYLOAD` (`p = 0`), `HUB` (`p = 51`), and `ROOT` (`p = 50`) -/

private theorem queueCode_decode (qs : QueueScan) :
    let qv := (queueSummaryCode qs).val
    (decide (qv ≥ 9) = qs.consuming.isSome) ∧
    (decide (qv < 3) = (qs.consuming.isNone && qs.unconsumed.isNone)) ∧
    (qs.consuming = none →
      ((qv / 3 == 0) = qs.unconsumed.isNone) ∧
      ((qv / 3 == 2) = match qs.unconsumed with | some (_, true) => true | _ => false)) ∧
    (qs.consuming.isSome = true →
      ((qv - 9 == 2) = qs.staging.isSome) ∧
      (qs.staging = none → (qv - 9 == 1) = qs.uninit.isSome)) := by
  have hfin : ∀ (co st ui : Bool) (unc : Option Bool),
      let qv := (queueSummaryFrom co st ui unc).val
      (decide (qv ≥ 9) = co) ∧
      (decide (qv < 3) = (!co && unc.isNone)) ∧
      (co = false →
        ((qv / 3 == 0) = unc.isNone) ∧
        ((qv / 3 == 2) = (unc == some true))) ∧
      (co = true →
        ((qv - 9 == 2) = st) ∧
        (st = false → (qv - 9 == 1) = ui)) := by
    intro co st ui unc
    cases unc with
    | none => revert co st ui; decide
    | some sb => revert co st ui sb; decide
  have hf := hfin qs.consuming.isSome qs.staging.isSome qs.uninit.isSome (qs.unconsumed.map Prod.snd)
  dsimp only [] at hf ⊢
  rw [queueSummaryCode_eq_from]
  refine ⟨hf.1, ?_, ?_, ?_⟩
  · rw [hf.2.1]
    cases qs.consuming <;> cases qs.unconsumed <;> rfl
  · intro hco
    have hco_f : qs.consuming.isSome = false := by rw [hco]; rfl
    obtain ⟨h1, h2⟩ := hf.2.2.1 hco_f
    refine ⟨?_, ?_⟩
    · rw [h1]; cases qs.unconsumed <;> rfl
    · rw [h2]; cases qs.unconsumed with
      | none => rfl
      | some p => rcases p with ⟨_, b⟩; cases b <;> rfl
  · intro hco
    obtain ⟨h1, h2⟩ := hf.2.2.2 hco
    refine ⟨h1, fun hst => ?_⟩
    exact h2 (by rw [hst]; rfl)

private theorem tmplCode_decode (ts : TemplateScan) :
    let tmpl := (tmplSummaryCode ts).val
    ((tmpl / 4 == 1) = ts.firstIdle.isSome) ∧
    (decide (tmpl % 4 ≥ 2) = ts.firstAppending.isSome) ∧
    (∀ tRel sbit, ts.firstAppending = some (tRel, sbit) → tmpl % 4 - 2 = bitNat sbit) ∧
    (ts.firstAppending = none → (tmpl % 4 == 1) = ts.firstArmed.isSome) := by
  have hfin : ∀ (fi fa : Bool) (fap : Option Bool),
      let tmpl := (tmplSummaryFrom fi fa fap).val
      ((tmpl / 4 == 1) = fi) ∧
      (decide (tmpl % 4 ≥ 2) = fap.isSome) ∧
      (∀ sbit : Bool, fap = some sbit → tmpl % 4 - 2 = bitNat sbit) ∧
      (fap = none → (tmpl % 4 == 1) = fa) := by
    intro fi fa fap
    cases fap with
    | none => revert fi fa; decide
    | some sb => revert fi fa sb; decide
  have hf := hfin ts.firstIdle.isSome ts.firstArmed.isSome (ts.firstAppending.map Prod.snd)
  dsimp only [] at hf ⊢
  rw [tmplSummaryCode_eq_from]
  refine ⟨hf.1, ?_, ?_, ?_⟩
  · rw [hf.2.1]; cases ts.firstAppending <;> rfl
  · intro tRel sbit hap
    exact hf.2.2.1 sbit (by rw [hap]; rfl)
  · intro hap
    exact hf.2.2.2 (by rw [hap]; rfl)

private theorem drop4_pfQueueRootPath (x : List Bool) :
    (pfQueueRootPath ++ x).drop 4 = pfRightChildPath ++ x := rfl

private theorem drop4_pfProgRingPath (x : List Bool) :
    (pfProgRingPath ++ x).drop 4 = pfLeftChildPath ++ x := rfl

private theorem drop4_pfProgRingPath2 (x y : List Bool) :
    (pfProgRingPath ++ x ++ y).drop 4 = pfLeftChildPath ++ (x ++ y) := by
  simp [pfProgRingPath, pfLeftChildPath]

private theorem loc_payload_eq {progRing queueRoot jp : Term}
    (hp : isClosedPureS ((.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp)) = true)
    (hnot_openFlag : ¬ ((progRingCode progRing).val ≥ 6 ∧ (queueCode queueRoot).val < 3)) :
    let pay := (.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp)
    loc 0 (ann 2 pay) =
      match pfDecideAction (scanPhases progRing) (scanQueue queueRoot) with
      | .openSlot path =>
          -- Note `pfQueueRootPath = pfPayloadPath ++ [true, false, true]`!
          if path == pfFlagPath then none
          else pfSelectOpeningAt pay ([true, false, true] ++ (scanQueue queueRoot).tailPath)
      | .writeVer verPath width desired =>
          -- Strip `pfPayloadPath` (`[true, true, false, true]`):
          pfSelectVersionWriteAt pay (verPath.drop 4) width desired
      | .none => none := by
  intro pay
  have hl : isClosedPureS (.s ⋅ progRing) = true := ((Bool.and_eq_true _ _).mp hp).1
  have hr : isClosedPureS ((.s ⋅ queueRoot) ⋅ jp) = true := ((Bool.and_eq_true _ _).mp hp).2
  have hpr_closed : isClosedPureS progRing = true := ((Bool.and_eq_true _ _).mp hl).2
  have hsqr_closed : isClosedPureS (.s ⋅ queueRoot) = true := ((Bool.and_eq_true _ _).mp hr).1
  have hqr_closed : isClosedPureS queueRoot = true := ((Bool.and_eq_true _ _).mp hsqr_closed).2
  have hql_ne0 : ((specBU 13 (.s ⋅ progRing)).val == 0) = false := by
    clear hnot_openFlag
    simp only [specBU]; have hc := (progRingCode progRing).isLt
    rw [fin23_val_of_lt (by omega)]; exact nat_beq_of_ne (by omega)
  have hql_sub : (specBU 13 (.s ⋅ progRing)).val - 1 = (progRingCode progRing).val := by
    clear hnot_openFlag
    simp only [specBU]; have hc := (progRingCode progRing).isLt; rw [fin23_val_of_lt (by omega)]; omega
  have hqr_nlt : ¬ ((specBU 23 ((.s ⋅ queueRoot) ⋅ jp)).val < 7) := by
    clear hnot_openFlag
    simp only [specBU]; have hc := (queueCode queueRoot).isLt; rw [fin23_val_of_lt (by omega)]; omega
  have hqr_sub : (specBU 23 ((.s ⋅ queueRoot) ⋅ jp)).val - 7 = (queueCode queueRoot).val := by
    clear hnot_openFlag
    simp only [specBU]; have hc := (queueCode queueRoot).isLt; rw [fin23_val_of_lt (by omega)]; omega
  let ps := scanPhases progRing
  let q := scanQueue queueRoot
  have hrange := phasesSummaryCode_range ps
  have hqd := queueCode_decode q
  obtain ⟨hq16, hq17, hq18, hq19, hq20⟩ := loc_qSeek hqr_closed
  unfold pfDecideAction
  cases hh : findIdxPred (fun pe => pe.status == some [true, true]) ps with
  | some pair =>
      rcases pair with ⟨hIdx, hEntry⟩
      have h14 : 1 ≤ (progRingCode progRing).val ∧ (progRingCode progRing).val ≤ 4 :=
        hrange.2.1.mp (by rw [hh]; rfl)
      cases hqc : q.consuming with
      | some cpair =>
          rcases cpair with ⟨cRel, b⟩
          have hqv9 : (queueCode queueRoot).val ≥ 9 :=
            of_decide_eq_true (hqd.1.trans (by rw [hqc]; rfl))
          have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
              pocketGoFR 17 := by
            rw [ann_state_eq hl, ann_state_eq hr]
            unfold pocketStepTD; dsimp only []
            simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, h14.1, h14.2, hqv9]
          rw_goFR (by decide : 17 < 32) hstep
          change (loc 17 (ann 6 queueRoot)).map (pfRightChildPath ++ ·) = _
          rw [hq17]
          change (match q.consuming with | some (cr, bit) => _ | none => none).map (pfRightChildPath ++ ·) = _
          rw [hqc]
          dsimp only []
          rw [drop4_pfQueueRootPath, pfSelectVersionWriteAt_shift pay pfRightChildPath cRel]
          simp [pay, pfRightChildPath, termAt, Option.map]
      | none =>
          have hqv_lt9 : ¬ ((queueCode queueRoot).val ≥ 9) :=
            of_decide_eq_false (hqd.1.trans (by rw [hqc]; rfl))
          have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
              pocketGoFL 32 := by
            rw [ann_state_eq hl, ann_state_eq hr]
            unfold pocketStepTD; dsimp only []
            simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, h14.1, h14.2, hqv_lt9]
          rw_goFL (by decide : 32 < 50) hstep
          change (loc 32 (ann 3 progRing)).map (pfLeftChildPath ++ ·) = _
          rw [loc_ph_handoffRoot hpr_closed hh]
          dsimp only []
          cases (ps.length == 1) with
          | true =>
              simp only [↓reduceIte]
              rw [drop4_pfProgRingPath, pfSelectVersionWriteAt_shift pay pfLeftChildPath hEntry.verPath]
              simp [pay, pfLeftChildPath, termAt, Option.map]
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              cases listGetOpt ps ((hIdx + 1) % ps.length) with
              | none => rfl
              | some nxtE =>
                  dsimp only []
                  cases hnxt : (nxtE.status == some [true, false]) <;>
                  · simp only [↓reduceIte, Bool.false_eq_true]
                    rw [drop4_pfProgRingPath, pfSelectVersionWriteAt_shift pay pfLeftChildPath]
                    simp [pay, pfLeftChildPath, termAt, Option.map]
  | none =>
      have hnot14 : ¬ (1 ≤ (progRingCode progRing).val ∧ (progRingCode progRing).val ≤ 4) := by
        intro hc; have hs := hrange.2.1.mpr hc; rw [hh] at hs; cases hs
      cases ha : findIdxPred (fun pe => pe.status == some [true, false]) ps with
      | none =>
          have hlt6 : (progRingCode progRing).val < 6 := by
            if h6 : 6 ≤ (progRingCode progRing).val then
              have hs := (hrange.2.2.2.mpr h6).2; rw [ha] at hs; cases hs
            else
              exact Nat.lt_of_not_le h6
          have hb14 : (decide (1 ≤ (progRingCode progRing).val) && decide ((progRingCode progRing).val ≤ 4)) = false := by
            cases h1 : decide (1 ≤ (progRingCode progRing).val) <;>
            cases h2 : decide ((progRingCode progRing).val ≤ 4) <;> try rfl
            exact False.elim (hnot14 ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩)
          rw [loc_ann_app, ann_state_eq hl, ann_state_eq hr]
          have hstep0 : pocketStepTD 0 (specBU 13 (.s ⋅ progRing)) (specBU 23 ((.s ⋅ queueRoot) ⋅ jp)) = .stuck := by
            unfold pocketStepTD; dsimp only []
            simp [hql_ne0, hqr_nlt, hql_sub, hb14, hlt6]
          simp only [pocketChildRoles]
          rw [hstep0]
      | some apair =>
          rcases apair with ⟨aIdx, actEntry⟩
          have hge6 : 6 ≤ (progRingCode progRing).val :=
            hrange.2.2.2.mp ⟨hh, by rw [ha]; rfl⟩
          have hph_nlt6 : ¬ ((progRingCode progRing).val < 6) := Nat.not_lt.mpr hge6
          have hb14 : (decide (1 ≤ (progRingCode progRing).val) && decide ((progRingCode progRing).val ≤ 4)) = false := by
            cases h1 : decide (1 ≤ (progRingCode progRing).val) <;>
            cases h2 : decide ((progRingCode progRing).val ≤ 4) <;> try rfl
            exact False.elim (hnot14 ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩)
          -- Extract `(progRingCode progRing - 6) % 8 = (tmplSummaryCode actEntry.templates).val`:
          have hph_mod8 : ((progRingCode progRing).val - 6) % 8 =
              (tmplSummaryCode actEntry.templates).val := by
            cases hsp_ps : ps with
            | nil => rw [hsp_ps] at ha; cases ha
            | cons e0 es =>
                have hpsc_eq : progRingCode progRing = phasesSummaryCode (e0 :: es) := by
                  unfold progRingCode; rw [← hsp_ps]
                rw [hpsc_eq]
                unfold phasesSummaryCode
                rw [hsp_ps] at hh ha
                rw [hh, ha]
                have hall : ∀ (t : Fin 8) (fa : Bool),
                    ((fin22 (6 + 8 * bitNat fa + t.val)).val - 6) % 8 = t.val := by decide
                exact hall (tmplSummaryCode actEntry.templates) (e0.status == some [true, false])
          have htd := tmplCode_decode actEntry.templates
          obtain ⟨hph28, hph29, hph30, hph31⟩ := loc_ph_active hpr_closed ha
          dsimp only [ps, q] at *
          cases hqc : (scanQueue queueRoot).consuming with
          | none =>
              have hqv_lt9 : (queueCode queueRoot).val < 9 :=
                Nat.lt_of_not_le (of_decide_eq_false (hqd.1.trans (by rw [hqc]; rfl)))
              have hqd_none := hqd.2.2.1 hqc
              cases hqu : (scanQueue queueRoot).unconsumed with
              | none =>
                  have hqv_lt3 : (queueCode queueRoot).val < 3 :=
                    of_decide_eq_true (hqd.2.1.trans (by rw [hqc, hqu]; rfl))
                  exact False.elim (hnot_openFlag ⟨hge6, hqv_lt3⟩)
              | some upair =>
                  rcases upair with ⟨uRel, b⟩
                  have hunc_ne0 : ((queueCode queueRoot).val / 3 == 0) = false :=
                    hqd_none.1.trans (by rw [hqu]; rfl)
                  cases b with
                  | false =>
                      have hunc_ne2 : ((queueCode queueRoot).val / 3 == 2) = false :=
                        hqd_none.2.trans (by rw [hqu])
                      have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                          pocketGoFR 18 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_lt9, hunc_ne0, hunc_ne2]
                      rw_goFR (by decide : 18 < 32) hstep
                      change (loc 18 (ann 6 queueRoot)).map (pfRightChildPath ++ ·) = _
                      rw [hq18, hqu]
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      rw [drop4_pfQueueRootPath, pfSelectVersionWriteAt_shift pay pfRightChildPath uRel]
                      simp [pay, pfRightChildPath, termAt, Option.map]
                  | true =>
                      have hunc_eq2 : ((queueCode queueRoot).val / 3 == 2) = true :=
                        hqd_none.2.trans (by rw [hqu])
                      cases hti : actEntry.templates.firstIdle with
                      | some ipair =>
                          rcases ipair with ⟨tRel, sbit⟩
                          have hidle_true : ((tmplSummaryCode actEntry.templates).val / 4 == 1) = true :=
                            htd.1.trans (by rw [hti]; rfl)
                          have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                              pocketGoFL 29 := by
                            rw [ann_state_eq hl, ann_state_eq hr]
                            unfold pocketStepTD; dsimp only []
                            simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_lt9,
                              hunc_ne0, hunc_eq2, hph_mod8, hidle_true]
                          rw_goFL (by decide : 29 < 50) hstep
                          change (loc 29 (ann 3 progRing)).map (pfLeftChildPath ++ ·) = _
                          rw [hph29, hti]
                          simp only [↓reduceIte]
                          rw [drop4_pfProgRingPath2, pfSelectVersionWriteAt_shift pay pfLeftChildPath]
                          simp [pay, pfLeftChildPath, termAt, Option.map]
                      | none =>
                          have hidle_false : ((tmplSummaryCode actEntry.templates).val / 4 == 1) = false :=
                            htd.1.trans (by rw [hti]; rfl)
                          have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                              pocketGoFR 18 := by
                            rw [ann_state_eq hl, ann_state_eq hr]
                            unfold pocketStepTD; dsimp only []
                            simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_lt9,
                              hunc_ne0, hunc_eq2, hph_mod8, hidle_false]
                          rw_goFR (by decide : 18 < 32) hstep
                          change (loc 18 (ann 6 queueRoot)).map (pfRightChildPath ++ ·) = _
                          rw [hq18, hqu]
                          simp only [↓reduceIte]
                          rw [drop4_pfQueueRootPath, pfSelectVersionWriteAt_shift pay pfRightChildPath uRel]
                          simp [pay, pfRightChildPath, termAt, Option.map]
          | some _ =>
              have hqv_nlt9 : ¬ ((queueCode queueRoot).val < 9) :=
                Nat.not_lt.mpr (of_decide_eq_true (hqd.1.trans (by rw [hqc]; rfl)))
              have hqd_some := hqd.2.2.2 (by rw [hqc]; rfl)
              cases hta : actEntry.templates.firstAppending with
              | some ap_pair =>
                  rcases ap_pair with ⟨tRel, sbit⟩
                  have hc4_ge2 : (tmplSummaryCode actEntry.templates).val % 4 ≥ 2 :=
                    of_decide_eq_true (htd.2.1.trans (by rw [hta]; rfl))
                  have hsbit_val := htd.2.2.1 tRel sbit hta
                  cases hqst : (scanQueue queueRoot).staging with
                  | some _ =>
                      have hsu2 : ((queueCode queueRoot).val - 9 == 2) = true :=
                        hqd_some.1.trans (by rw [hqst]; rfl)
                      have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                          pocketGoFL 31 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_nlt9,
                          hph_mod8, hc4_ge2, hsu2]
                      rw_goFL (by decide : 31 < 50) hstep
                      change (loc 31 (ann 3 progRing)).map (pfLeftChildPath ++ ·) = _
                      rw [hph31, hta]
                      dsimp only []
                      rw [drop4_pfProgRingPath2, pfSelectVersionWriteAt_shift pay pfLeftChildPath]
                      simp [pay, pfLeftChildPath, termAt, Option.map]
                  | none =>
                      have hsu_ne2 : ((queueCode queueRoot).val - 9 == 2) = false :=
                        hqd_some.1.trans (by rw [hqst]; rfl)
                      cases hqui : (scanQueue queueRoot).uninit with
                      | some uiRel =>
                          have hsu1 : ((queueCode queueRoot).val - 9 == 1) = true :=
                            (hqd_some.2 hqst).trans (by rw [hqui]; rfl)
                          have hlt32 : 20 + bitNat sbit < 32 := by cases sbit <;> decide
                          have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                              pocketGoFR (20 + bitNat sbit) := by
                            rw [ann_state_eq hl, ann_state_eq hr]
                            unfold pocketStepTD; dsimp only []
                            simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_nlt9,
                              hph_mod8, hc4_ge2, hsu_ne2, hsu1, hsbit_val]
                          rw_goFR hlt32 hstep
                          change (loc (fin136 (20 + bitNat sbit)) (ann 6 queueRoot)).map (pfRightChildPath ++ ·) = _
                          rw [hq20 sbit, hqui]
                          dsimp only []
                          rw [drop4_pfQueueRootPath, pfSelectVersionWriteAt_shift pay pfRightChildPath uiRel]
                          simp [pay, pfRightChildPath, termAt, Option.map]
                      | none =>
                          have hsu_ne1 : ((queueCode queueRoot).val - 9 == 1) = false :=
                            (hqd_some.2 hqst).trans (by rw [hqui]; rfl)
                          have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                              pocketGoFR 16 := by
                            rw [ann_state_eq hl, ann_state_eq hr]
                            unfold pocketStepTD; dsimp only []
                            simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_nlt9,
                              hph_mod8, hc4_ge2, hsu_ne2, hsu_ne1]
                          rw_goFR (by decide : 16 < 32) hstep
                          change (loc 16 (ann 6 queueRoot)).map (pfRightChildPath ++ ·) = _
                          rw [hq16]
                          have hpath_ne : ((pfQueueRootPath ++ (scanQueue queueRoot).tailPath) == pfFlagPath) = false := rfl
                          dsimp only []
                          simp only [hpath_ne, Bool.false_eq_true, ↓reduceIte]
                          rw [pfSelectOpeningAt_append pay [true, false, true] (scanQueue queueRoot).tailPath]
                          simp [pay, pfRightChildPath, termAt, Option.map]
              | none =>
                  have hc4_lt2 : ¬ ((tmplSummaryCode actEntry.templates).val % 4 ≥ 2) :=
                    of_decide_eq_false (htd.2.1.trans (by rw [hta]; rfl))
                  cases hqst : (scanQueue queueRoot).staging with
                  | some stpair =>
                      rcases stpair with ⟨stRel, sbit⟩
                      have hsu2 : ((queueCode queueRoot).val - 9 == 2) = true :=
                        hqd_some.1.trans (by rw [hqst]; rfl)
                      have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                          pocketGoFR 19 := by
                        rw [ann_state_eq hl, ann_state_eq hr]
                        unfold pocketStepTD; dsimp only []
                        simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_nlt9,
                          hph_mod8, hc4_lt2, hsu2]
                      rw_goFR (by decide : 19 < 32) hstep
                      change (loc 19 (ann 6 queueRoot)).map (pfRightChildPath ++ ·) = _
                      rw [hq19, hqst]
                      dsimp only []
                      rw [drop4_pfQueueRootPath, pfSelectVersionWriteAt_shift pay pfRightChildPath stRel]
                      simp [pay, pfRightChildPath, termAt, Option.map]
                  | none =>
                      have hsu_ne2 : ((queueCode queueRoot).val - 9 == 2) = false :=
                        hqd_some.1.trans (by rw [hqst]; rfl)
                      cases htarm : actEntry.templates.firstArmed with
                      | some armpair =>
                          rcases armpair with ⟨tRel, sbit⟩
                          have hc4_eq1 : ((tmplSummaryCode actEntry.templates).val % 4 == 1) = true :=
                            (htd.2.2.2 hta).trans (by rw [htarm]; rfl)
                          have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                              pocketGoFL 30 := by
                            rw [ann_state_eq hl, ann_state_eq hr]
                            unfold pocketStepTD; dsimp only []
                            simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_nlt9,
                              hph_mod8, hc4_lt2, hsu_ne2, hc4_eq1]
                          rw_goFL (by decide : 30 < 50) hstep
                          change (loc 30 (ann 3 progRing)).map (pfLeftChildPath ++ ·) = _
                          rw [hph30, htarm]
                          dsimp only []
                          rw [drop4_pfProgRingPath2, pfSelectVersionWriteAt_shift pay pfLeftChildPath]
                          simp [pay, pfLeftChildPath, termAt, Option.map]
                      | none =>
                          have hc4_ne1 : ((tmplSummaryCode actEntry.templates).val % 4 == 1) = false :=
                            (htd.2.2.2 hta).trans (by rw [htarm]; rfl)
                          have hstep : pocketStepTD 0 (ann 13 (.s ⋅ progRing)).state (ann 23 ((.s ⋅ queueRoot) ⋅ jp)).state =
                              pocketGoFL 28 := by
                            rw [ann_state_eq hl, ann_state_eq hr]
                            unfold pocketStepTD; dsimp only []
                            simp [hql_ne0, hqr_nlt, hql_sub, hqr_sub, hb14, hph_nlt6, hqv_nlt9,
                              hph_mod8, hc4_lt2, hsu_ne2, hc4_ne1]
                          rw_goFL (by decide : 28 < 50) hstep
                          change (loc 28 (ann 3 progRing)).map (pfLeftChildPath ++ ·) = _
                          rw [hph28]
                          dsimp only []
                          rw [drop4_pfProgRingPath, pfSelectVersionWriteAt_shift pay pfLeftChildPath]
                          simp [pay, pfLeftChildPath, termAt, Option.map]

/-- **Master Pass-2 Redex-Address Equivalence (`pocketPF_locate_eq_pfSelectAddress`)**:
    On **every** closed pure-`S` tree `t`, Pass 2 of `pocketPFTransducer` returns the **exact**
    `Option (List Bool)` redex address computed by `pfSelectAddress t`! -/
theorem pocketPF_locate_eq_pfSelectAddress {t : Term} (ht : isClosedPureS t = true) :
    loc 50 (ann 0 t) = pfSelectAddress t := by
  cases t with
  | s => rfl
  | var _ => cases ht
  | app a hub =>
      have ha_cl : isClosedPureS a = true := ((Bool.and_eq_true _ _).mp ht).1
      have hhub_cl : isClosedPureS hub = true := ((Bool.and_eq_true _ _).mp ht).2
      -- Step 1 at root (`p = 50 -> .goRight 51`):
      have hroot_step : loc 50 (ann 0 (a ⋅ hub)) = (loc 51 (ann 1 hub)).map (true :: ·) := rfl
      rw [hroot_step]
      cases hpf_hub : parseFrame hub with
      | none =>
          have hrs_none : pfSelectAddress (a ⋅ hub) = none := by
            unfold pfSelectAddress pfReadState
            simp [pfHubPath, termAt, hpf_hub]
          rw [hrs_none]
          cases hub with
          | s => rfl
          | var _ => cases hhub_cl
          | app hl hr_hub =>
              have hhl : isClosedPureS hl = true := ((Bool.and_eq_true _ _).mp hhub_cl).1
              have hhr : isClosedPureS hr_hub = true := ((Bool.and_eq_true _ _).mp hhub_cl).2
              have hnot_both : (specBU 11 hl).val < 7 ∨ (specBU 20 hr_hub).val < 7 := by
                cases hge7 : decide ((specBU 11 hl).val ≥ 7) with
                | false => exact Or.inl (Nat.lt_of_not_le (of_decide_eq_false hge7))
                | true =>
                    obtain ⟨_, rfl⟩ := (s1Open_ge7_iff (fun x => if flagValue x then 6 else arityFuel 5 x)
                      flag_or_arity_le15).mp
                      (of_decide_eq_true hge7)
                    have hnot_s2 : ¬ ∃ sub j, hr_hub = (.s ⋅ sub) ⋅ j := by
                      rintro ⟨sub, j, rfl⟩; simp [parseFrame] at hpf_hub
                    exact Or.inr (Nat.lt_of_not_le (mt (s2Open_ge7_iff _
                      (fun x => Nat.le_of_lt (Nat.lt_of_lt_of_le (payloadCode x).isLt (by decide)))).mp hnot_s2))
              rw [loc_ann_app, ann_state_eq hhl, ann_state_eq hhr]
              simp only [pocketChildRoles]
              have hstep51 : pocketStepTD 51 (specBU 11 hl) (specBU 20 hr_hub) = .stuck := by
                rcases hnot_both with h1 | h2
                · unfold pocketStepTD; dsimp only []; simp [h1]
                · unfold pocketStepTD; dsimp only []; simp [h2]
              rw [hstep51]; rfl
      | some htriple =>
          rcases htriple with ⟨flag, payload, jh⟩
          obtain ⟨hhub_eq, _, _⟩ := parseFrame_some_decomp hpf_hub
          subst hhub_eq
          have hhl : isClosedPureS (.s ⋅ flag) = true := ((Bool.and_eq_true _ _).mp hhub_cl).1
          have hhr : isClosedPureS ((.s ⋅ payload) ⋅ jh) = true := ((Bool.and_eq_true _ _).mp hhub_cl).2
          have hflag_cl : isClosedPureS flag = true := ((Bool.and_eq_true _ _).mp hhl).2
          have hspay_cl : isClosedPureS (.s ⋅ payload) = true := ((Bool.and_eq_true _ _).mp hhr).1
          have hpay_cl : isClosedPureS payload = true := ((Bool.and_eq_true _ _).mp hspay_cl).2
          have hql_nlt : ¬ ((specBU 11 (.s ⋅ flag)).val < 7) := (specBU11_s_props flag).2
          have hqr_nlt : ¬ ((specBU 20 ((.s ⋅ payload) ⋅ jh)).val < 7) := by
            simp only [specBU]; have hc := (payloadCode payload).isLt; rw [fin23_val_of_lt (by omega)]; omega
          have hqr_sub : (specBU 20 ((.s ⋅ payload) ⋅ jh)).val - 7 = (payloadCode payload).val := by
            simp only [specBU]; have hc := (payloadCode payload).isLt; rw [fin23_val_of_lt (by omega)]; omega
          cases hpf_pay : parseFrame payload with
          | none =>
              have hpc0 : payloadCode payload = 0 := (parseFrame_eq_none_cases hpf_pay).1
              have hrs_none : pfSelectAddress (a ⋅ ((.s ⋅ flag) ⋅ ((.s ⋅ payload) ⋅ jh))) = none := by
                have hr_none : pfReadState (a ⋅ ((.s ⋅ flag) ⋅ ((.s ⋅ payload) ⋅ jh))) = none := by
                  unfold pfReadState
                  have ht_hub : termAt (a ⋅ ((.s ⋅ flag) ⋅ ((.s ⋅ payload) ⋅ jh))) pfHubPath =
                      some ((.s ⋅ flag) ⋅ ((.s ⋅ payload) ⋅ jh)) := rfl
                  have hpf1 : parseFrame ((.s ⋅ flag) ⋅ ((.s ⋅ payload) ⋅ jh)) = some (flag, payload, jh) := rfl
                  rw [ht_hub]
                  dsimp only [Bind.bind, Option.bind]
                  rw [hpf1]
                  dsimp only [Bind.bind, Option.bind]
                  rw [hpf_pay]
                unfold pfSelectAddress
                rw [hr_none]
                rfl
              rw [hrs_none, loc_ann_app, ann_state_eq hhl, ann_state_eq hhr]
              simp only [pocketChildRoles]
              have hstep51 : pocketStepTD 51 (specBU 11 (.s ⋅ flag)) (specBU 20 ((.s ⋅ payload) ⋅ jh)) = .stuck := by
                unfold pocketStepTD; dsimp only []
                simp [hql_nlt, hqr_nlt, hqr_sub, hpc0]
              rw [hstep51]; rfl
          | some ptriple =>
              rcases ptriple with ⟨progRing, queueRoot, jp⟩
              obtain ⟨hpay_eq, _, _⟩ := parseFrame_some_decomp hpf_pay
              subst hpay_eq
              have hread_eq : pfReadState (a ⋅ ((.s ⋅ flag) ⋅ ((.s ⋅ ((.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp))) ⋅ jh))) =
                  some (scanPhases progRing, scanQueue queueRoot) := rfl
              if hopen_flag : (progRingCode progRing).val ≥ 6 ∧ (queueCode queueRoot).val < 3 then
                have hpc2 : (payloadCode ((.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp))).val = 2 := by
                  simp [payloadCode, hopen_flag.1, hopen_flag.2]
                have hstep : pocketStepTD 51
                    (ann 11 (.s ⋅ flag)).state
                    (ann 20 ((.s ⋅ ((.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp))) ⋅ jh)).state =
                    pocketGoFL 1 := by
                  rw [ann_state_eq hhl, ann_state_eq hhr]
                  unfold pocketStepTD; dsimp only []
                  simp [hql_nlt, hqr_nlt, hqr_sub, hpc2]
                rw_goFL (by decide : 1 < 50) hstep
                change ((loc 1 (ann 10 flag)).map (pfLeftChildPath ++ ·)).map (true :: ·) = _
                rw [loc_1_open_eq (r := 10) rfl rfl hflag_cl]
                -- Also show `pfDecideAction (scanPhases progRing) (scanQueue queueRoot) = .openSlot pfFlagPath`!
                have hrange := phasesSummaryCode_range (scanPhases progRing)
                obtain ⟨hh_none, ha_some⟩ := hrange.2.2.2.mpr hopen_flag.1
                have hqd := queueCode_decode (scanQueue queueRoot)
                have hboth_none := (Bool.and_eq_true _ _).mp (hqd.2.1.symm.trans (decide_eq_true hopen_flag.2))
                cases hqc : (scanQueue queueRoot).consuming with
                | some _ => rw [hqc] at hboth_none; cases hboth_none.1
                | none =>
                    cases hqu : (scanQueue queueRoot).unconsumed with
                    | some _ => rw [hqu] at hboth_none; cases hboth_none.2
                    | none =>
                        cases ha : findIdxPred (fun pe => pe.status == some [true, false]) (scanPhases progRing) with
                        | none => rw [ha] at ha_some; cases ha_some
                        | some _ =>
                            unfold pfSelectAddress
                            rw [hread_eq]
                            dsimp only [Bind.bind, Option.bind]
                            unfold pfDecideAction
                            rw [hh_none, ha, hqc, hqu]
                            dsimp only []
                            rw [pfSelectOpeningAt_flag_nil]
                            dsimp only [termAt]
                            rw [term_at_nil]
                            dsimp only [Bind.bind, Option.bind]
                            rw [pfSelectOpeningAt_nil]
                            cases nextOpeningAddress flag <;> rfl
              else
                have hpc1 : (payloadCode ((.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp))).val = 1 := by
                  simp only [payloadCode]
                  cases h1 : decide ((progRingCode progRing).val ≥ 6) <;>
                  cases h2 : decide ((queueCode queueRoot).val < 3) <;> try rfl
                  exact False.elim (hopen_flag ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩)
                have hstep : pocketStepTD 51
                    (ann 11 (.s ⋅ flag)).state
                    (ann 20 ((.s ⋅ ((.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp))) ⋅ jh)).state =
                    pocketGoFR 0 := by
                  rw [ann_state_eq hhl, ann_state_eq hhr]
                  unfold pocketStepTD; dsimp only []
                  simp [hql_nlt, hqr_nlt, hqr_sub, hpc1]
                rw_goFR (by decide : 0 < 32) hstep
                let pay := (.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp)
                let root := a ⋅ ((.s ⋅ flag) ⋅ ((.s ⋅ pay) ⋅ jh))
                change ((loc 0 (ann 2 pay)).map (pfRightChildPath ++ ·)).map (true :: ·) =
                  pfSelectAddress root
                rw [loc_payload_eq hpay_cl hopen_flag]
                unfold pfSelectAddress
                have hr_eq : pfReadState root = some (scanPhases progRing, scanQueue queueRoot) := rfl
                rw [hr_eq]
                dsimp only [Bind.bind, Option.bind]
                -- Check that every action emitted by `pfDecideAction` (under `¬ hopen_flag`) has prefix `[true, true, false, true]`:
                have hact_shape :
                    match pfDecideAction (scanPhases progRing) (scanQueue queueRoot) with
                    | .openSlot path =>
                        path = pfPayloadPath ++ ([true, false, true] ++ (scanQueue queueRoot).tailPath) ∧
                        (path == pfFlagPath) = false
                    | .writeVer verPath _ _ =>
                        verPath = pfPayloadPath ++ verPath.drop 4
                    | .none => True := by
                  unfold pfDecideAction
                  cases hh : findIdxPred (fun pe => pe.status == some [true, true]) (scanPhases progRing) with
                  | some pair =>
                      rcases pair with ⟨hIdx, hE⟩
                      cases (scanQueue queueRoot).consuming with
                      | some cp => rcases cp with ⟨_, _⟩; rfl
                      | none =>
                          cases ((scanPhases progRing).length == 1) with
                          | true => rfl
                          | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              cases listGetOpt (scanPhases progRing) ((hIdx + 1) % (scanPhases progRing).length) with
                              | none => trivial
                              | some nxtE =>
                                  dsimp only []
                                  cases hnxt : (nxtE.status == some [true, false]) <;>
                                  · simp only [↓reduceIte, Bool.false_eq_true]; rfl
                  | none =>
                      cases ha : findIdxPred (fun pe => pe.status == some [true, false]) (scanPhases progRing) with
                      | none => trivial
                      | some ap =>
                          rcases ap with ⟨_, actE⟩
                          dsimp only []
                          cases hqc : (scanQueue queueRoot).consuming with
                          | none =>
                              cases hqu : (scanQueue queueRoot).unconsumed with
                              | none =>
                                  have hge6 : (progRingCode progRing).val ≥ 6 :=
                                    (phasesSummaryCode_range (scanPhases progRing)).2.2.2.mp
                                      ⟨hh, by rw [ha]; rfl⟩
                                  have hlt3 : (queueCode queueRoot).val < 3 :=
                                    of_decide_eq_true ((queueCode_decode (scanQueue queueRoot)).2.1.trans
                                      (by rw [hqc, hqu]; rfl))
                                  exact False.elim (hopen_flag ⟨hge6, hlt3⟩)
                              | some up =>
                                  rcases up with ⟨_, b⟩
                                  cases b with
                                  | false => rfl
                                  | true => cases actE.templates.firstIdle <;> rfl
                          | some _ =>
                              cases actE.templates.firstAppending with
                              | some ap2 =>
                                  rcases ap2 with ⟨_, _⟩
                                  cases (scanQueue queueRoot).staging with
                                  | some _ => rfl
                                  | none =>
                                      cases (scanQueue queueRoot).uninit with
                                      | some _ => rfl
                                      | none => exact ⟨rfl, rfl⟩
                              | none =>
                                  cases (scanQueue queueRoot).staging with
                                  | some sp => rcases sp with ⟨_, _⟩; rfl
                                  | none => cases actE.templates.firstArmed <;> rfl
                cases hd : pfDecideAction (scanPhases progRing) (scanQueue queueRoot) with
                | none => rfl
                | openSlot path =>
                    rw [hd] at hact_shape
                    obtain ⟨hp_eq, hnf⟩ := hact_shape
                    simp only [hnf, Bool.false_eq_true, ↓reduceIte]
                    rw [hp_eq]
                    rw [pfSelectOpeningAt_append root pfPayloadPath]
                    have ht_pay : termAt root pfPayloadPath = some pay := rfl
                    rw [ht_pay]
                    dsimp only [Bind.bind, Option.bind, pay]
                    cases pfSelectOpeningAt ((.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp))
                      ([true, false, true] ++ (scanQueue queueRoot).tailPath) <;> rfl
                | writeVer verPath width desired =>
                    rw [hd] at hact_shape
                    dsimp only [] at hact_shape ⊢
                    conv => rhs; rw [hact_shape]
                    rw [pfSelectVersionWriteAt_shift root pfPayloadPath (verPath.drop 4) width desired]
                    have ht_pay : termAt root pfPayloadPath = some pay := rfl
                    rw [ht_pay]
                    dsimp only [Bind.bind, Option.bind, pay]
                    cases pfSelectVersionWriteAt ((.s ⋅ progRing) ⋅ ((.s ⋅ queueRoot) ⋅ jp))
                      (verPath.drop 4) width desired <;> rfl


/-! ## Section 5: 100% Extensional Equality with `pfSelect` & Grand CTS Universality Theorem -/

/-- **100% Extensional Equality Theorem (`pocketPFSelect_eq_pfSelect`)**:
    On **every** closed pure-`S` tree `t`, the explicit `(Fin 25, Fin 23, Fin 136)` finite-state
    transducer `pocketPFTransducer` produces the **exact same `PFOutcome`** as `pfSelect t`! -/
theorem pocketPFSelect_eq_pfSelect (t : Term) (ht : isClosedPureS t = true) :
    pocketPFSelect t = pfSelect t := by
  unfold pocketPFSelect PocketTreeTransducer.select PocketTreeTransducer.runTransducer pfSelect
  have hrr : pocketPFTransducer.rootRole = 0 := rfl
  have hitd : pocketPFTransducer.initTD = 50 := rfl
  rw [hrr, hitd]
  dsimp only []
  rw [pocketPF_acceptHalt_eq_pfRootHalt ht]
  cases pfRootHalt t with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hloc_def : (pocketPFTransducer.locateRedex 50 (pocketPFTransducer.annotate 0 t).1).1 =
          loc 50 (ann 0 t) := rfl
      rw [hloc_def, pocketPF_locate_eq_pfSelectAddress ht]
      cases pfSelectAddress t with
      | none => rfl
      | some path =>
          dsimp only []
          cases contractAt t path <;> rfl

theorem isClosedPureS_step {a b : Term} (hs : Step a b) (ha : isClosedPureS a = true) :
    isClosedPureS b = true := by
  induction hs with
  | root x y z =>
      have h1 : isClosedPureS (.s ⋅ x ⋅ y) = true := ((Bool.and_eq_true _ _).mp ha).1
      have hz : isClosedPureS z = true := ((Bool.and_eq_true _ _).mp ha).2
      have h2 : isClosedPureS (.s ⋅ x) = true := ((Bool.and_eq_true _ _).mp h1).1
      have hy : isClosedPureS y = true := ((Bool.and_eq_true _ _).mp h1).2
      have hx : isClosedPureS x = true := ((Bool.and_eq_true _ _).mp h2).2
      simp [isClosedPureS, hx, hy, hz]
  | left _ ih =>
      have hl := ((Bool.and_eq_true _ _).mp ha).1
      have hr := ((Bool.and_eq_true _ _).mp ha).2
      simp [isClosedPureS, ih hl, hr]
  | right _ ih =>
      have hl := ((Bool.and_eq_true _ _).mp ha).1
      have hr := ((Bool.and_eq_true _ _).mp ha).2
      simp [isClosedPureS, hl, ih hr]

/-- Multi-step pure-`S` trace driven exclusively by `pocketPFTransducer` (`(Fin 25, Fin 23, Fin 136)`). -/
inductive PocketPFTrace : Nat → Term → Term → Prop where
  | zero (a : Term) : PocketPFTrace 0 a a
  | next {n : Nat} {a b c : Term} :
      pocketPFSelect a = .step b → PocketPFTrace n b c → PocketPFTrace (n + 1) a c

theorem pocketPFTrace_reduces {k : Nat} {a b : Term} (h : PocketPFTrace k a b) : Reduces a b := by
  induction h with
  | zero x => exact Reduces.refl x
  | next hs _ ih =>
      exact Reduces.next (PocketTreeTransducer.transducer_select_step_sound pocketPFTransducer hs) ih

theorem pocketPFTrace_preserves_closed {k : Nat} {a b : Term}
    (h : PocketPFTrace k a b) (ha : isClosedPureS a = true) : isClosedPureS b = true := by
  induction h with
  | zero _ => exact ha
  | next hs _ ih =>
      have hstep := PocketTreeTransducer.transducer_select_step_sound pocketPFTransducer hs
      exact ih (isClosedPureS_step hstep ha)

/-- **Exact Trace Equivalence (`pocketPFTrace_iff_pfTrace`)**:
    From any closed pure-`S` start term `a`, `k`-step evolution under `pocketPFSelect` is
    **identical** to `k`-step evolution under `pfSelect`! -/
theorem pocketPFTrace_iff_pfTrace {k : Nat} {a b : Term} (ha : isClosedPureS a = true) :
    PocketPFTrace k a b ↔ PFTrace k a b := by
  induction k generalizing a with
  | zero =>
      constructor
      · intro h; cases h; exact PFTrace.zero _
      · intro h; cases h; exact PocketPFTrace.zero _
  | succ n ih =>
      constructor
      · intro h
        cases h with
        | @next _ _ mid _ hs hrest =>
            have hs_pf : pfSelect a = .step mid := (pocketPFSelect_eq_pfSelect a ha).symm.trans hs
            have hmid_cl : isClosedPureS mid = true :=
              isClosedPureS_step (pfSelect_step_sound hs_pf) ha
            exact PFTrace.next hs_pf ((ih hmid_cl).mp hrest)
      · intro h
        cases h with
        | @next _ _ mid _ hs_pf hrest =>
            have hs : pocketPFSelect a = .step mid := (pocketPFSelect_eq_pfSelect a ha).trans hs_pf
            have hmid_cl : isClosedPureS mid = true :=
              isClosedPureS_step (pfSelect_step_sound hs_pf) ha
            exact PocketPFTrace.next hs ((ih hmid_cl).mpr hrest)

/-- **Grand Pocket Transducer CTS Universality & Output Readback Theorem (`pocket_transducer_cts_universality`)**:
    A **single 10-leaf pure-`S` seed** (`tenLeafSeed = S(S(SS))(S(SS))(SS)S`) together with the
    explicit **`(Fin 25, Fin 23, Fin 136)` program-free finite-state pocket tree transducer**
    `pocketPFTransducer` simulates **every** Cyclic Tag System `(P, w)` via genuine single-redex
    pure `S x y z → (x z)(y z)` reductions:
    1. **10-Leaf Seed Reachability & Closedness**: `leaves tenLeafSeed = 10`,
       `Reduces tenLeafSeed (encodeProgramFreeCTS P w)`, and `isClosedPureS (encodeProgramFreeCTS P w) = true`.
    2. **Bidirectional Halting Equivalence**: `CTSEventuallyHalts P w` holds **if and only if**
       `PocketPFTrace` reaches a pure-`S` term `reached` where `pocketPFSelect reached = .halt`.
    3. **Exact Halted Output Readback**: Whenever `CTSEventuallyHalts P w`, the halted pure-`S`
       term `reached` decodes via `decodeProgramFreeCTS` to `some (finalIdx, [])` matching `CTSRun`.
    4. **Unconditional Linear Transducer Complexity & Quadratic Trajectory Size**:
       - On **every** tree `t : Term`, `pocketPFSteps t ≤ 2 * leaves t - 1 + treeDepth t`
         (and **strictly** `pocketPFSteps t + 2 ≤ 2 * leaves t - 1 + treeDepth t` on every `.step`),
       - Every intermediate term `reached` at step `k` satisfies
         `leaves reached ≤ 35000 * (ctsInputSize P w + k + 1) ^ 2`. -/
theorem pocket_transducer_cts_universality (P : CTSProgram) (w : List Bool) :
    (leaves tenLeafSeed = 10 ∧
     Reduces tenLeafSeed (encodeProgramFreeCTS P w) ∧
     isClosedPureS (encodeProgramFreeCTS P w) = true) ∧
    (CTSEventuallyHalts P w ↔
      ∃ k reached, PocketPFTrace k (encodeProgramFreeCTS P w) reached ∧
        pocketPFSelect reached = .halt) ∧
    (CTSEventuallyHalts P w →
      ∃ n finalIdx k reached,
        CTSRun P n (initCTSConfig w) ⟨finalIdx, []⟩ ∧
        ctsStep P ⟨finalIdx, []⟩ = none ∧
        PocketPFTrace k (encodeProgramFreeCTS P w) reached ∧
        pocketPFSelect reached = .halt ∧
        decodeProgramFreeCTS reached = some (finalIdx, [])) ∧
    (∀ t : Term,
      pocketPFSteps t ≤ 2 * leaves t - 1 + treeDepth t ∧
      (∀ t', pocketPFSelect t = .step t' → pocketPFSteps t + 2 ≤ 2 * leaves t - 1 + treeDepth t)) ∧
    (∀ k reached, PocketPFTrace k (encodeProgramFreeCTS P w) reached →
      leaves reached ≤ pfTrajectorySizeConst * (ctsInputSize P w + k + 1) ^ 2) := by
  have hcl0 := encodeProgramFreeCTS_isClosedPureS P w
  refine ⟨⟨seed_has_ten_leaves, seed_reduces_to_encodeProgramFreeCTS P w, hcl0⟩, ?_, ?_, ?_, ?_⟩
  · rw [program_free_cts_halting_iff P w]
    constructor
    · rintro ⟨k, reached, htr, hhalt⟩
      have htr_p := (pocketPFTrace_iff_pfTrace hcl0).mpr htr
      have hr_cl := pocketPFTrace_preserves_closed htr_p hcl0
      have hsel_halt : pocketPFSelect reached = .halt := by
        rw [pocketPFSelect_eq_pfSelect reached hr_cl]
        exact (pfSelect_halt_iff reached).mpr hhalt
      exact ⟨k, reached, htr_p, hsel_halt⟩
    · rintro ⟨k, reached, htr_p, hsel_halt⟩
      have hr_cl := pocketPFTrace_preserves_closed htr_p hcl0
      have htr := (pocketPFTrace_iff_pfTrace hcl0).mp htr_p
      rw [pocketPFSelect_eq_pfSelect reached hr_cl] at hsel_halt
      exact ⟨k, reached, htr, (pfSelect_halt_iff reached).mp hsel_halt⟩
  · intro hhalts
    obtain ⟨n, finalIdx, k, reached, hrun, hstop, htr, hauto, hdec⟩ :=
      decodeProgramFreeCTS_halted P w hhalts
    have htr_p := (pocketPFTrace_iff_pfTrace hcl0).mpr htr
    have hr_cl := pocketPFTrace_preserves_closed htr_p hcl0
    have hhalt : pfRootHalt reached = true :=
      (pfHaltAutomaton_accepts_eq_pfRootHalt reached).symm.trans hauto
    have hsel_halt : pocketPFSelect reached = .halt := by
      rw [pocketPFSelect_eq_pfSelect reached hr_cl]
      exact (pfSelect_halt_iff reached).mpr hhalt
    exact ⟨n, finalIdx, k, reached, hrun, hstop, htr_p, hsel_halt, hdec⟩
  · intro t
    exact ⟨(PocketTreeTransducer.transducer_steps_linear_bound pocketPFTransducer t).1,
           fun t' hs => (PocketTreeTransducer.transducer_steps_strict_on_step pocketPFTransducer hs).1⟩
  · intro k reached htr_p
    exact encodeProgramFreeCTS_trajectory_leaves_poly P w ((pocketPFTrace_iff_pfTrace hcl0).mp htr_p)


/-! ## Section 6: Executable `#guard` Sanity Checks & `#print axioms` Kernel Audit -/

/-- Bounded executable runner driven solely by `pocketPFSelect` (`(Fin 25, Fin 23, Fin 136)`). -/
def runPocketPFBoundedTerm : Nat → Term → Option Term
  | 0, t => if pocketPFSelect t == .halt then some t else none
  | fuel + 1, t =>
      match pocketPFSelect t with
      | .halt => some t
      | .step t' => runPocketPFBoundedTerm fuel t'
      | .stuck => none

#guard ((runPocketPFBoundedTerm 20 (encodeProgramFreeCTS ctsExampleEmptyHalt [])).bind decodeProgramFreeCTS) ==
  some (0, [])
#guard ((runPocketPFBoundedTerm 200 (encodeProgramFreeCTS ctsExampleCopyAndDrain [false])).bind decodeProgramFreeCTS) ==
  some (1, [])
#guard ((runPocketPFBoundedTerm 2500 (encodeProgramFreeCTS ctsExampleThreePhase [true, false])).bind
  decodeProgramFreeCTS) == some (0, [])

end FormalWolframFrontier

#print axioms FormalWolframFrontier.PocketTreeTransducer.annotate_steps_exact
#print axioms FormalWolframFrontier.PocketTreeTransducer.locateRedex_steps_le_depth
#print axioms FormalWolframFrontier.PocketTreeTransducer.transducer_steps_linear_bound
#print axioms FormalWolframFrontier.PocketTreeTransducer.transducer_steps_strict_on_step
#print axioms FormalWolframFrontier.annotate_state_eq_specBU
#print axioms FormalWolframFrontier.pocketPF_acceptHalt_eq_pfRootHalt
#print axioms FormalWolframFrontier.pocketPF_locate_eq_pfSelectAddress
#print axioms FormalWolframFrontier.pocketPFSelect_eq_pfSelect
#print axioms FormalWolframFrontier.pocketPFTrace_iff_pfTrace
#print axioms FormalWolframFrontier.pocket_transducer_cts_universality
