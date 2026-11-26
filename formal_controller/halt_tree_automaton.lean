import full_root_selector

/- Explicit 11-state deterministic bottom-up tree automaton (`Q = Fin 11`)
   recognizing `rootHalt` on all `Term`s.

   `rootHalt t` holds iff `t = header ⋅ hub` where `hub` is an opened
   `F`-frame `(S ⋅ flag) ⋅ ((S ⋅ tape) ⋅ junk)` whose left slot `flag` is also
   an opened `F`-frame `(S ⋅ l) ⋅ ((S ⋅ r) ⋅ j)`. -/

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

/-- Local syntactic features sufficient to compute `rootHalt` bottom-up. -/
structure HaltFeatures where
  isS : Bool
  isS1 : Bool
  isS1F : Bool
  isS2 : Bool
  isF : Bool
  isHaltHub : Bool
  isRootHalt : Bool
  deriving DecidableEq, Repr

def isSTerm : Term → Bool
  | .s => true
  | _ => false

def isS1Term : Term → Bool
  | .app .s _ => true
  | _ => false

def isS1FTerm : Term → Bool
  | .app .s x => flagValue x
  | _ => false

def isS2Shape : Term → Bool
  | .app (.app .s _) _ => true
  | _ => false

def featuresOf (t : Term) : HaltFeatures :=
  { isS := isSTerm t
    isS1 := isS1Term t
    isS1F := isS1FTerm t
    isS2 := isS2Shape t
    isF := flagValue t
    isHaltHub := haltObserved t
    isRootHalt := rootHalt t }

def combineFeatures (fl fr : HaltFeatures) : HaltFeatures :=
  { isS := false
    isS1 := fl.isS
    isS1F := fl.isS && fr.isF
    isS2 := fl.isS1
    isF := fl.isS1 && fr.isS2
    isHaltHub := fl.isS1F && fr.isS2
    isRootHalt := fr.isHaltHub }

theorem flagValue_eq_s1_s2 (l r : Term) :
    flagValue (l ⋅ r) = (isS1Term l && isS2Shape r) := by
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

theorem haltObserved_eq_s1f_s2 (l r : Term) :
    haltObserved (l ⋅ r) = (isS1FTerm l && isS2Shape r) := by
  cases l with
  | s => rfl
  | var _ => rfl
  | app ll lr =>
      cases ll with
      | s =>
          cases r with
          | s => simp [haltObserved, parseFrame, isS1FTerm, isS2Shape]
          | var _ => simp [haltObserved, parseFrame, isS1FTerm, isS2Shape]
          | app rl rr =>
              cases rl with
              | s => simp [haltObserved, parseFrame, isS1FTerm, isS2Shape]
              | var _ => simp [haltObserved, parseFrame, isS1FTerm, isS2Shape]
              | app rll rlr =>
                  cases rll <;> simp [haltObserved, parseFrame, isS1FTerm, isS2Shape]
      | var _ => rfl
      | app _ _ => rfl

theorem featuresOf_app (l r : Term) :
    featuresOf (l ⋅ r) = combineFeatures (featuresOf l) (featuresOf r) := by
  unfold featuresOf combineFeatures
  have h1 : isSTerm (l ⋅ r) = false := rfl
  have h2 : isS1Term (l ⋅ r) = isSTerm l := by cases l <;> rfl
  have h3 : isS1FTerm (l ⋅ r) = (isSTerm l && flagValue r) := by cases l <;> rfl
  have h4 : isS2Shape (l ⋅ r) = isS1Term l := by
    cases l with
    | s => rfl
    | var _ => rfl
    | app ll lr => cases ll <;> rfl
  have h5 := flagValue_eq_s1_s2 l r
  have h6 := haltObserved_eq_s1f_s2 l r
  have h7 : rootHalt (l ⋅ r) = haltObserved r := rfl
  rw [h1, h2, h3, h4, h5, h6, h7]

/- The 11 reachable feature states (`Fin 11`):
   0 : `t = S`
   1 : `t = S ⋅ x` with `flagValue x = false`
   2 : `t = S ⋅ x` with `flagValue x = true`, `haltObserved x = false`
   3 : `t = S ⋅ x` with `flagValue x = true`, `haltObserved x = true` (`rootHalt t = true`)
   4 : `t = (S ⋅ x) ⋅ y` with `flagValue t = false`
   5 : `t = (S ⋅ x) ⋅ y` with `flagValue t = true`, `haltObserved t = false`, `rootHalt t = false`
   6 : `t = (S ⋅ x) ⋅ y` with `flagValue t = true`, `haltObserved t = false`, `rootHalt t = true`
   7 : `t = (S ⋅ x) ⋅ y` with `flagValue t = true`, `haltObserved t = true`, `rootHalt t = false`
   8 : `t = (S ⋅ x) ⋅ y` with `flagValue t = true`, `haltObserved t = true`, `rootHalt t = true`
   9 : other shape with `rootHalt t = false`
   10 : other shape with `rootHalt t = true` -/
def stateFeatures : Fin 11 → HaltFeatures
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

def encodeFeatures (f : HaltFeatures) : Fin 11 :=
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

def haltAutomaton : BottomUpTreeAutomaton (Fin 11) where
  leafState := 0
  varState := fun _ => 9
  appState := fun ql qr => encodeFeatures (combineFeatures (stateFeatures ql) (stateFeatures qr))
  accept := fun q => (stateFeatures q).isRootHalt

theorem haltAutomaton_app_coherent :
    ∀ ql qr : Fin 11,
      stateFeatures (haltAutomaton.appState ql qr) =
        combineFeatures (stateFeatures ql) (stateFeatures qr) := by
  decide

theorem haltAutomaton_eval_features (t : Term) :
    stateFeatures (haltAutomaton.eval t) = featuresOf t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app l r ihl ihr =>
      calc
        stateFeatures (haltAutomaton.eval (l ⋅ r))
            = stateFeatures (haltAutomaton.appState (haltAutomaton.eval l) (haltAutomaton.eval r)) := rfl
        _ = combineFeatures (stateFeatures (haltAutomaton.eval l)) (stateFeatures (haltAutomaton.eval r)) :=
              haltAutomaton_app_coherent (haltAutomaton.eval l) (haltAutomaton.eval r)
        _ = combineFeatures (featuresOf l) (featuresOf r) := by rw [ihl, ihr]
        _ = featuresOf (l ⋅ r) := (featuresOf_app l r).symm

theorem haltAutomaton_accepts_eq_rootHalt (t : Term) :
    haltAutomaton.evalAccepts t = rootHalt t := by
  unfold BottomUpTreeAutomaton.evalAccepts
  have h := congrArg HaltFeatures.isRootHalt (haltAutomaton_eval_features t)
  exact h

#print axioms haltAutomaton
#print axioms haltAutomaton_eval_features
#print axioms haltAutomaton_accepts_eq_rootHalt
