import formal_q32_equational.q32_backward_cones

/-!
# Negative Resolution of Open Question 32 (Barendregt, Endrullis, Klop & Waldmann 2017, p. 95)

Formalizes equational derivability `EqTheoryDerives E` over `CL(S)` extended by an arbitrary
finite list `E : List (Term × Term)` of schematic pure-`S` equations closed under arbitrary
substitutions, congruence, symmetry, reflexivity, and transitivity, and proves:

1. **Soundness (`eqTheoryDerives_sound`)**: If every equation in `E` is `λβ`-sound
   (`IsLambdaBetaSound E`), then `EqTheoryDerives E M N → ConvBeta (toLam M) (toLam N)`.
2. **Closed Basis Impossibility (`no_finite_closed_beta_sound_basis`)**: For every finite list
   `E` of closed `λβ`-sound equations, there exist closed `CL(S)` normal forms `M, N` such that
   `ConvBeta (toLam M) (toLam N) ∧ ¬ EqTheoryDerives E M N`.
3. **Full Negative Resolution of Open Question 32 (`question_32_negative_resolution`)**:
   For **every** finite list `E : List (Term × Term)` of `λβ`-sound pure-`S` equations
   (including open schematic axioms with arbitrary variables), there exist `CL(S)` normal forms
   `M, N : Term` (`isIsolatedSNFBool M = true`, `isSNFBool N = true`) such that
   `ConvBeta (toLam M) (toLam N) ∧ ¬ EqTheoryDerives E M N`.
4. **Corollary (`no_finite_equational_axiomatization_of_lambda_beta`)**: No finite set `E` of
   equations between `S`-terms satisfies `∀ M N, EqTheoryDerives E M N ↔ ConvBeta (toLam M) (toLam N)`.

Zero `sorry`, zero `Classical.choice`, zero `native_decide`, zero custom axioms.
-/

namespace FormalQ32

open FormalAlgebra

/-! ## 1. Equational Derivability `CL(S) + E` and `λβ`-Soundness -/

/-- Equational derivability `CL(S) + E ⊢ a = b` from pure-`S` reduction plus schematic
    substitution instances of `E`, closed under equivalence and application congruence. -/
inductive EqTheoryDerives (E : List (Term × Term)) : Term → Term → Prop where
  | step {a b : Term} : Step a b → EqTheoryDerives E a b
  | ax {p : Term × Term} : p ∈ E → (σ : Nat → Term) →
      EqTheoryDerives E (subst σ p.1) (subst σ p.2)
  | refl (a : Term) : EqTheoryDerives E a a
  | symm {a b : Term} : EqTheoryDerives E a b → EqTheoryDerives E b a
  | trans {a b c : Term} : EqTheoryDerives E a b → EqTheoryDerives E b c →
      EqTheoryDerives E a c
  | left {a1 a2 b : Term} : EqTheoryDerives E a1 a2 →
      EqTheoryDerives E (a1 ⋅ b) (a2 ⋅ b)
  | right {a b1 b2 : Term} : EqTheoryDerives E b1 b2 →
      EqTheoryDerives E (a ⋅ b1) (a ⋅ b2)

/-- Every equation `(l, r) ∈ E` is valid modulo `=_{λβ}` under `toLam`. -/
def IsLambdaBetaSound (E : List (Term × Term)) : Prop :=
  ∀ p ∈ E, ConvBeta (toLam p.1) (toLam p.2)

/-- Every equation `(l, r) ∈ E` consists of closed `S`-terms (`noVars = true`). -/
def IsClosedAxiomSet (E : List (Term × Term)) : Prop :=
  ∀ p ∈ E, noVars p.1 = true ∧ noVars p.2 = true

theorem convS_implies_eqTheoryDerives (E : List (Term × Term)) {a b : Term}
    (h : ConvS a b) : EqTheoryDerives E a b := by
  induction h with
  | refl m => exact .refl m
  | step hs => exact .step hs
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- **Soundness of `CL(S) + E` with respect to `λβ`-Convertibility**. -/
theorem eqTheoryDerives_sound {E : List (Term × Term)} (hsound : IsLambdaBetaSound E)
    {a b : Term} (hd : EqTheoryDerives E a b) :
    ConvBeta (toLam a) (toLam b) := by
  induction hd with
  | step hs => exact convS_to_convBeta (.step hs)
  | ax hp σ => exact convBeta_subst_term σ (hsound _ hp)
  | refl m => exact .refl (toLam m)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | left _ ih => exact convBeta_left ih _
  | right _ ih => exact convBeta_right _ ih

/-! ## 2. Subterm Relation & Isolated-Subterm Equational Rigidity Invariant -/

inductive IsSubterm : Term → Term → Prop where
  | refl (t : Term) : IsSubterm t t
  | left {u a b : Term} : IsSubterm u a → IsSubterm u (a ⋅ b)
  | right {u a b : Term} : IsSubterm u b → IsSubterm u (a ⋅ b)

theorem isSubterm_trans {u v w : Term} (h1 : IsSubterm u v) (h2 : IsSubterm v w) :
    IsSubterm u w := by
  induction h2 with
  | refl => exact h1
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem isNormalForm_of_subterm {u t : Term} (hsub : IsSubterm u t) (hnf : IsNormalForm t) :
    IsNormalForm u := by
  induction hsub with
  | refl => exact hnf
  | @left a b _ ih => exact ih (fun a' ha' => hnf (a' ⋅ b) (.left ha'))
  | @right a b _ ih => exact ih (fun b' hb' => hnf (a ⋅ b') (.right hb'))

private theorem hasAntiRedex_children {a b : Term} (h : hasAntiRedex (a ⋅ b) = false) :
    hasAntiRedex a = false ∧ hasAntiRedex b = false := by
  unfold hasAntiRedex at h
  simp only [Bool.or_eq_false_iff] at h
  exact ⟨h.1.2, h.2⟩

theorem hasAntiRedex_false_of_subterm {u t : Term}
    (hsub : IsSubterm u t) (hno : hasAntiRedex t = false) :
    hasAntiRedex u = false := by
  induction hsub with
  | refl => exact hno
  | left _ ih => exact ih (hasAntiRedex_children hno).1
  | right _ ih => exact ih (hasAntiRedex_children hno).2

theorem leaves_le_of_subterm {u t : Term} (hsub : IsSubterm u t) :
    leaves u ≤ leaves t := by
  induction hsub with
  | refl => exact Nat.le_refl _
  | left _ ih => simp only [leaves]; omega
  | right _ ih => simp only [leaves]; omega

theorem hasVar_false_of_subterm {v : Nat} {u t : Term}
    (hsub : IsSubterm u t) (hno : hasVar v t = false) :
    hasVar v u = false := by
  induction hsub with
  | refl => exact hno
  | left _ ih =>
    simp only [hasVar, Bool.or_eq_false_iff] at hno
    exact ih hno.1
  | right _ ih =>
    simp only [hasVar, Bool.or_eq_false_iff] at hno
    exact ih hno.2

theorem subterm_subst_of_hasVar {σ : Nat → Term} {v : Nat} {P : Term}
    (hv : hasVar v P = true) :
    IsSubterm (σ v) (subst σ P) := by
  induction P with
  | s => cases hv
  | var k =>
    simp only [hasVar, decide_eq_true_eq] at hv
    subst hv
    exact .refl _
  | app a b iha ihb =>
    simp only [hasVar, Bool.or_eq_true] at hv
    rcases hv with hva | hvb
    · exact .left (iha hva)
    · exact .right (ihb hvb)

/-- **Isolated-Subterm Equational Rigidity Lemma**:
    If `t` is an isolated `CL(S)` normal form (`IsNormalForm t` and `hasAntiRedex t = false`)
    and every axiom instance matching a subterm of `t` is reflexive, then `[t]_{CL(S)+E} = {t}`. -/
theorem eqTheoryDerives_subterm_rigid {E : List (Term × Term)} {t : Term}
    (hnf : IsNormalForm t) (hno : hasAntiRedex t = false)
    (hax : ∀ p ∈ E, ∀ σ : Nat → Term,
      (IsSubterm (subst σ p.1) t → subst σ p.2 = subst σ p.1) ∧
      (IsSubterm (subst σ p.2) t → subst σ p.1 = subst σ p.2))
    {a b : Term} (hd : EqTheoryDerives E a b) :
    (IsSubterm a t → b = a) ∧ (IsSubterm b t → a = b) := by
  induction hd with
  | step hs =>
    refine ⟨fun hsub => False.elim (isNormalForm_of_subterm hsub hnf _ hs),
            fun hsub => False.elim (no_step_into_of_no_antiRedex
              (hasAntiRedex_false_of_subterm hsub hno) hs)⟩
  | ax hp σ => exact hax _ hp σ
  | refl _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 =>
    refine ⟨fun hsub => ?_, fun hsub => ?_⟩
    · have hm := ih1.1 hsub
      rw [hm] at ih2
      exact (ih2.1 hsub)
    · have hm := ih2.2 hsub
      rw [hm] at ih1
      exact (ih1.2 hsub)
  | left _ ih =>
    refine ⟨fun hsub => ?_, fun hsub => ?_⟩
    · rw [ih.1 (isSubterm_trans (.left (.refl _)) hsub)]
    · rw [ih.2 (isSubterm_trans (.left (.refl _)) hsub)]
  | right _ ih =>
    refine ⟨fun hsub => ?_, fun hsub => ?_⟩
    · rw [ih.1 (isSubterm_trans (.right (.refl _)) hsub)]
    · rw [ih.2 (isSubterm_trans (.right (.refl _)) hsub)]

/-! ## 3. Normal-Form, Anti-Redex, and Leaf-Separation Properties of `(A_open, B_open)` -/

theorem isSNFBool_s1 {a : Term} (ha : isSNFBool a = true) :
    isSNFBool (S ⋅ a) = true := by
  simp only [S, isSNFBool, isSRedexPrefix, ha, Bool.not_false, Bool.and_self]

theorem isSNFBool_s2 {a b : Term} (ha : isSNFBool a = true) (hb : isSNFBool b = true) :
    isSNFBool (S ⋅ a ⋅ b) = true := by
  simp only [S, isSNFBool, isSRedexPrefix, ha, hb, Bool.not_false, Bool.and_self]

theorem isSNFBool_sTower (k : Nat) {u : Term} (hu : isSNFBool u = true) :
    isSNFBool (sTower k u) = true := by
  induction k with
  | zero => exact hu
  | succ _ ih => exact isSNFBool_s1 ih

theorem isSNFBool_A_open (m : Nat) {y : Term} (hy : isSNFBool y = true) :
    isSNFBool (A_open (m + 1) y) = true := by
  simp only [A_open, Nat.add_sub_cancel]
  exact isSNFBool_s2
    (isSNFBool_s2 (isSNFBool_sTower (m + 1) rfl) hy)
    (isSNFBool_s2 (isSNFBool_sTower m rfl) hy)

theorem isSNFBool_B_open (m : Nat) {y : Term} (hy : isSNFBool y = true) :
    isSNFBool (B_open (m + 1) y) = true := by
  simp only [B_open, Nat.add_sub_cancel]
  exact isSNFBool_s2
    (isSNFBool_s2 (isSNFBool_sTower m rfl) hy)
    (isSNFBool_s2 (isSNFBool_sTower (m + 1) rfl) hy)

theorem hasAntiRedex_s_right {a : Term} (ha : hasAntiRedex a = false) :
    hasAntiRedex (a ⋅ S) = false :=
  hasAntiRedex_app_eq_false (fun _ _ _ h => by cases h) ha rfl

theorem hasAntiRedex_A_open_var (m v : Nat) :
    hasAntiRedex (A_open (m + 1) (.var v)) = false := by
  simp only [A_open, Nat.add_sub_cancel]
  have hL : hasAntiRedex (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var v) = false :=
    hasAntiRedex_var_right v (hasAntiRedex_s_left (hasAntiRedex_sTower_SS (m + 1)))
  have hR : hasAntiRedex (S ⋅ sTower m (S ⋅ S) ⋅ .var v) = false :=
    hasAntiRedex_var_right v (hasAntiRedex_s_left (hasAntiRedex_sTower_SS m))
  refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_) (hasAntiRedex_s_left hL) hR
  injection hz1 with hz1'
  injection hz2 with hz2'
  rw [← hz1', ← hz2']
  intro hh
  have hl := congrArg leaves hh
  simp only [S, leaves, leaves_sTower] at hl
  omega

theorem hasAntiRedex_M_closed (m : Nat) :
    hasAntiRedex (M_closed (m + 1)) = false := by
  simp only [M_closed, A_open, Nat.add_sub_cancel]
  have hL : hasAntiRedex (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ S) = false :=
    hasAntiRedex_s_right (hasAntiRedex_s_left (hasAntiRedex_sTower_SS (m + 1)))
  have hR : hasAntiRedex (S ⋅ sTower m (S ⋅ S) ⋅ S) = false :=
    hasAntiRedex_s_right (hasAntiRedex_s_left (hasAntiRedex_sTower_SS m))
  refine hasAntiRedex_app_eq_false (fun z1 z2 hz1 hz2 => ?_) (hasAntiRedex_s_left hL) hR
  injection hz1 with hz1'
  injection hz2 with hz2'
  rw [← hz1', ← hz2']
  intro hh
  have hl := congrArg leaves hh
  simp only [S, leaves, leaves_sTower] at hl
  omega

theorem A_open_ne_B_open (m : Nat) (y : Term) :
    A_open (m + 1) y ≠ B_open (m + 1) y := by
  intro heq
  have hl := congrArg leaves heq
  simp only [A_open, B_open, Nat.add_sub_cancel, S, leaves, leaves_sTower] at hl
  omega

/-! ## 4. Closed Axiom Set Impossibility (`no_finite_closed_beta_sound_basis`) -/

def maxLeavesAxioms : List (Term × Term) → Nat
  | [] => 0
  | p :: ps => Nat.max (Nat.max (leaves p.1) (leaves p.2)) (maxLeavesAxioms ps)

theorem leaves_le_maxLeavesAxioms {E : List (Term × Term)} {p : Term × Term} (hp : p ∈ E) :
    leaves p.1 ≤ maxLeavesAxioms E ∧ leaves p.2 ≤ maxLeavesAxioms E := by
  induction E with
  | nil => cases hp
  | cons q qs ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hmem
    · simp only [maxLeavesAxioms]
      exact ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
             Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)⟩
    · obtain ⟨h1, h2⟩ := ih hmem
      simp only [maxLeavesAxioms]
      exact ⟨Nat.le_trans h1 (Nat.le_max_right _ _),
             Nat.le_trans h2 (Nat.le_max_right _ _)⟩

private theorem subterm_sTower_SS {u : Term} (k : Nat) (h : IsSubterm u (sTower k (S ⋅ S))) :
    u = S ∨ ∃ j, u = sTower j (S ⋅ S) := by
  induction k with
  | zero =>
    cases h with
    | refl => exact Or.inr ⟨0, rfl⟩
    | left hl => cases hl; exact Or.inl rfl
    | right hr => cases hr; exact Or.inl rfl
  | succ k' ih =>
    cases h with
    | refl => exact Or.inr ⟨k' + 1, rfl⟩
    | left hl => cases hl; exact Or.inl rfl
    | right hr => exact ih hr

private theorem subterm_M_closed_small {m : Nat} {u : Term}
    (hsub : IsSubterm u (M_closed (m + 1))) (hle : leaves u ≤ m + 2) :
    u = S ∨ ∃ j, u = sTower j (S ⋅ S) := by
  simp only [M_closed, A_open, Nat.add_sub_cancel] at hsub
  cases hsub with
  | refl =>
    exfalso
    simp only [S, leaves, leaves_sTower] at hle
    omega
  | left hSL =>
    cases hSL with
    | refl =>
      exfalso
      simp only [S, leaves, leaves_sTower] at hle
      omega
    | left hS => cases hS; exact Or.inl rfl
    | right hL =>
      cases hL with
      | refl =>
        exfalso
        simp only [S, leaves, leaves_sTower] at hle
        omega
      | right hS => cases hS; exact Or.inl rfl
      | left hSt =>
        exact subterm_sTower_SS (m + 2) hSt
  | right hR =>
    cases hR with
    | refl =>
      exfalso
      simp only [S, leaves, leaves_sTower] at hle
      omega
    | right hS => cases hS; exact Or.inl rfl
    | left hSt =>
      exact subterm_sTower_SS (m + 1) hSt

private theorem rigidity_S_eq {R : Term} (hconv : ConvBeta (toLam S) (toLam R)) : R = S :=
  (convS_iff_eq_of_isolated (t := S) rfl).mp ((theoremA_rigidity_S R).mp hconv)

private theorem rigidity_var_eq (v : Nat) {R : Term}
    (hconv : ConvBeta (toLam (.var v)) (toLam R)) : R = .var v := by
  have hiso : isIsolatedSNFBool (.var v) = true := rfl
  exact (convS_iff_eq_of_isolated hiso).mp ((theoremA_rigidity_var v R).mp hconv)

/-- **Closed Axiom Set Impossibility Theorem**:
    For every finite list `E` of closed `λβ`-sound equations between `S`-terms, there exist
    closed `CL(S)` normal forms `M, N` such that `ConvBeta (toLam M) (toLam N)` and
    `¬ EqTheoryDerives E M N`. -/
theorem no_finite_closed_beta_sound_basis (E : List (Term × Term))
    (hclosed : IsClosedAxiomSet E) (hsound : IsLambdaBetaSound E) :
    ∃ M N : Term,
      noVars M = true ∧
      noVars N = true ∧
      IsNormalForm M ∧
      IsNormalForm N ∧
      ConvBeta (toLam M) (toLam N) ∧
      ¬ EqTheoryDerives E M N := by
  let m := maxLeavesAxioms E
  refine ⟨M_closed (m + 1), N_closed (m + 1), ?_, ?_,
    isNormalForm_of_bool (isSNFBool_A_open m rfl),
    isNormalForm_of_bool (isSNFBool_B_open m rfl),
    convBeta_M_N_closed m, ?_⟩
  · simp only [M_closed, A_open, Nat.add_sub_cancel, S, noVars,
               noVars_sTower (m + 1) (u := .s ⋅ .s) rfl,
               noVars_sTower m (u := .s ⋅ .s) rfl, Bool.and_self]
  · simp only [N_closed, B_open, Nat.add_sub_cancel, S, noVars,
               noVars_sTower m (u := (.s ⋅ .s) ⋅ (.s ⋅ .s)) rfl,
               noVars_sTower (m + 1) (u := .s ⋅ .s ⋅ .s) rfl, Bool.and_self]
  · intro hder
    have hnfM : IsNormalForm (M_closed (m + 1)) :=
      isNormalForm_of_bool (isSNFBool_A_open m rfl)
    have hnoM : hasAntiRedex (M_closed (m + 1)) = false := hasAntiRedex_M_closed m
    have hrig := eqTheoryDerives_subterm_rigid hnfM hnoM (fun p hp σ => ?_) hder
    · exact A_open_ne_B_open m S (hrig.1 (.refl _)).symm
    · obtain ⟨hc1, hc2⟩ := hclosed p hp
      obtain ⟨hl1, hl2⟩ := leaves_le_maxLeavesAxioms hp
      have hsub1 : subst σ p.1 = p.1 := subst_noVars σ p.1 hc1
      have hsub2 : subst σ p.2 = p.2 := subst_noVars σ p.2 hc2
      have hcb := hsound p hp
      rw [hsub1, hsub2]
      refine ⟨fun hs1 => ?_, fun hs2 => ?_⟩
      · rcases subterm_M_closed_small hs1 (by omega) with hp1 | ⟨j, hp1⟩
        · rw [hp1] at hcb ⊢
          exact rigidity_S_eq hcb
        · rw [hp1] at hcb ⊢
          exact rigidity_sTower_SS j p.2 hcb
      · rcases subterm_M_closed_small hs2 (by omega) with hp2 | ⟨j, hp2⟩
        · rw [hp2] at hcb ⊢
          exact rigidity_S_eq hcb.symm
        · rw [hp2] at hcb ⊢
          exact rigidity_sTower_SS j p.1 hcb.symm

/-! ## 5. `repSS` Core Abstraction & Full Schematic Resolution of Open Question 32 -/

def isExactSS : Term → Bool
  | .app .s .s => true
  | _ => false

def repSS (z : Term) : Term → Term
  | .s => .s
  | .var k => .var k
  | .app a b => if isExactSS (.app a b) then z else repSS z a ⋅ repSS z b

def noSSAtDepth : Nat → Term → Prop
  | 0, _ => True
  | _ + 1, .s => True
  | _ + 1, .var _ => True
  | d + 1, .app a b => isExactSS (.app a b) = false ∧ noSSAtDepth d a ∧ noSSAtDepth d b

private theorem noSSAtDepth_s : ∀ d, noSSAtDepth d .s
  | 0 => trivial
  | _ + 1 => trivial

private theorem noSSAtDepth_var (v : Nat) : ∀ d, noSSAtDepth d (.var v)
  | 0 => trivial
  | _ + 1 => trivial

private theorem noSSAtDepth_mono {d1 d2 : Nat} (hle : d1 ≤ d2) {t : Term}
    (h : noSSAtDepth d2 t) : noSSAtDepth d1 t := by
  induction d1 generalizing d2 t with
  | zero => exact trivial
  | succ d1' ih =>
    cases d2 with
    | zero => exfalso; omega
    | succ d2' =>
      cases t with
      | s => exact trivial
      | var _ => exact trivial
      | app a b =>
        rcases h with ⟨hnss, ha, hb⟩
        exact ⟨hnss, ih (by omega) ha, ih (by omega) hb⟩

private theorem isExactSS_s_sTower (k : Nat) :
    isExactSS (S ⋅ sTower k (S ⋅ S)) = false := by
  cases k <;> rfl

private theorem noSSAtDepth_sTower_SS (k : Nat) :
    noSSAtDepth k (sTower k (S ⋅ S)) := by
  induction k with
  | zero => exact trivial
  | succ k' ih =>
    exact ⟨isExactSS_s_sTower k', noSSAtDepth_s k', ih⟩

private theorem noSSAtDepth_A_open (m v : Nat) :
    noSSAtDepth (m + 3) (A_open (m + 1) (.var v)) := by
  simp only [A_open, Nat.add_sub_cancel]
  have hStL : noSSAtDepth (m + 2) (S ⋅ sTower (m + 1) (S ⋅ S)) :=
    ⟨isExactSS_s_sTower (m + 1), noSSAtDepth_s (m + 1), noSSAtDepth_sTower_SS (m + 1)⟩
  have hLA : noSSAtDepth (m + 3) (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var v) :=
    ⟨rfl, hStL, noSSAtDepth_var v (m + 2)⟩
  have hSLA : noSSAtDepth (m + 4) (S ⋅ (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var v)) :=
    ⟨rfl, noSSAtDepth_s (m + 3), hLA⟩
  have hStR : noSSAtDepth (m + 1) (S ⋅ sTower m (S ⋅ S)) :=
    ⟨isExactSS_s_sTower m, noSSAtDepth_s m, noSSAtDepth_sTower_SS m⟩
  have hRA : noSSAtDepth (m + 2) (S ⋅ sTower m (S ⋅ S) ⋅ .var v) :=
    ⟨rfl, hStR, noSSAtDepth_var v (m + 1)⟩
  exact ⟨rfl, noSSAtDepth_mono (by omega) hSLA, hRA⟩

private theorem repSS_sTower_SS (z : Term) (k : Nat) :
    repSS z (sTower k (S ⋅ S)) = sTower k z := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    have hnss := isExactSS_s_sTower k'
    change (if isExactSS (S ⋅ sTower k' (S ⋅ S)) then z
            else repSS z S ⋅ repSS z (sTower k' (S ⋅ S))) = S ⋅ sTower k' z
    rw [hnss]
    simp only [Bool.false_eq_true, ↓reduceIte, ih]
    rfl

private theorem repSS_A_open_eq_A_var (m u y : Nat) :
    repSS (.var u) (A_open (m + 1) (.var y)) = A_var (m + 1) u y := by
  simp only [A_open, A_var, Nat.add_sub_cancel]
  have hL : repSS (.var u) (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y) =
      S ⋅ sTower (m + 1) (.var u) ⋅ .var y := by
    change repSS (.var u) (S ⋅ sTower (m + 1) (S ⋅ S)) ⋅ .var y = _
    change S ⋅ repSS (.var u) (sTower (m + 1) (S ⋅ S)) ⋅ .var y = _
    rw [repSS_sTower_SS]
  have hR : repSS (.var u) (S ⋅ sTower m (S ⋅ S) ⋅ .var y) =
      S ⋅ sTower m (.var u) ⋅ .var y := by
    change repSS (.var u) (S ⋅ sTower m (S ⋅ S)) ⋅ .var y = _
    change (if isExactSS (S ⋅ sTower m (S ⋅ S)) then .var u
            else S ⋅ repSS (.var u) (sTower m (S ⋅ S))) ⋅ .var y = _
    rw [isExactSS_s_sTower m]
    simp only [Bool.false_eq_true, ↓reduceIte, repSS_sTower_SS]
  change (S ⋅ repSS (.var u) (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y)) ⋅
      repSS (.var u) (S ⋅ sTower m (S ⋅ S) ⋅ .var y) = _
  rw [hL, hR]

private theorem subst_repSS_comm (z : Term) (σ : Nat → Term) {P : Term} {d : Nat}
    (hld : leaves P ≤ d) (hno : noSSAtDepth d (subst σ P)) :
    subst (fun v => repSS z (σ v)) P = repSS z (subst σ P) := by
  induction P generalizing d with
  | s => rfl
  | var _ => rfl
  | app P1 P2 ih1 ih2 =>
    have hp1 := leaves_pos P1
    have hp2 := leaves_pos P2
    simp only [leaves] at hld
    cases d with
    | zero => exfalso; omega
    | succ d' =>
      rcases hno with ⟨hnss, hno1, hno2⟩
      have r1 := ih1 (d := d') (by omega) hno1
      have r2 := ih2 (d := d') (by omega) hno2
      simp only [subst]
      change _ = (if isExactSS (subst σ P1 ⋅ subst σ P2) then z
                  else repSS z (subst σ P1) ⋅ repSS z (subst σ P2))
      rw [hnss]
      simp only [Bool.false_eq_true, ↓reduceIte, r1, r2]

private def unrepSubst : Nat → Term :=
  fun v => if v = 0 then S ⋅ S else .var v

private theorem subst_unrepSubst_repSS {u : Term} (hno : hasVar 0 u = false) :
    subst unrepSubst (repSS (.var 0) u) = u := by
  induction u with
  | s => rfl
  | var k =>
    simp only [hasVar, decide_eq_false_iff_not] at hno
    simp only [repSS, subst, unrepSubst, if_neg hno]
  | app a b iha ihb =>
    simp only [hasVar, Bool.or_eq_false_iff] at hno
    change subst unrepSubst (if isExactSS (a ⋅ b) then .var 0 else repSS (.var 0) a ⋅ repSS (.var 0) b) = a ⋅ b
    cases hss : isExactSS (a ⋅ b)
    · simp only [Bool.false_eq_true, ↓reduceIte, subst, iha hno.1, ihb hno.2]
    · cases a with
      | var _ => cases hss
      | app _ _ => cases hss
      | s =>
        cases b with
        | var _ => cases hss
        | app _ _ => cases hss
        | s => rfl

private theorem subst_unrepSubst_sTower (k : Nat) :
    subst unrepSubst (sTower k (.var 0)) = sTower k (S ⋅ S) := by
  induction k with
  | zero => rfl
  | succ _ ih => simp only [sTower, S, subst, ih]

private theorem subst_unrepSubst_A_var (m : Nat) :
    subst unrepSubst (A_var (m + 1) 0 1) = A_open (m + 1) (.var 1) := by
  simp only [A_var, A_open, Nat.add_sub_cancel, S, subst,
             subst_unrepSubst_sTower (m + 1), subst_unrepSubst_sTower m, unrepSubst]
  rfl

private theorem subst_comp (ρ τ : Nat → Term) (t : Term) :
    subst ρ (subst τ t) = subst (fun v => subst ρ (τ v)) t := by
  induction t with
  | s => rfl
  | var _ => rfl
  | app a b iha ihb => simp only [subst, iha, ihb]

private theorem subst_congr {σ1 σ2 : Nat → Term} {t : Term}
    (h : ∀ v, hasVar v t = true → σ1 v = σ2 v) :
    subst σ1 t = subst σ2 t := by
  induction t with
  | s => rfl
  | var v => exact h v (by simp only [hasVar, decide_true])
  | app a b iha ihb =>
    have ha := iha (fun v hv => h v (by simp only [hasVar, hv, Bool.true_or]))
    have hb := ihb (fun v hv => h v (by simp only [hasVar, hv, Bool.or_true]))
    simp only [subst, ha, hb]

private theorem hasVar_zero_A_open_one (m : Nat) :
    hasVar 0 (A_open (m + 1) (.var 1)) = false := by
  have ht1 : hasVar 0 (sTower (m + 1) (S ⋅ S)) = false :=
    hasVar_of_noVars 0 (noVars_sTower (m + 1) rfl)
  have ht2 : hasVar 0 (sTower m (S ⋅ S)) = false :=
    hasVar_of_noVars 0 (noVars_sTower m rfl)
  have happ : ∀ {u v : Term}, hasVar 0 u = false → hasVar 0 v = false → hasVar 0 (u ⋅ v) = false := by
    intro u v hu hv; unfold hasVar; rw [hu, hv]; rfl
  simp only [A_open, Nat.add_sub_cancel]
  exact happ (happ rfl (happ (happ rfl ht1) rfl)) (happ (happ rfl ht2) rfl)

private theorem hasVar_two_A_var_01 (m : Nat) :
    hasVar 2 (A_var (m + 1) 0 1) = false := by
  have hst : ∀ k, hasVar 2 (sTower k (.var 0)) = false := by
    intro k
    induction k with
    | zero => rfl
    | succ _ ih => unfold sTower S hasVar; rw [ih]; rfl
  have happ : ∀ {u v : Term}, hasVar 2 u = false → hasVar 2 v = false → hasVar 2 (u ⋅ v) = false := by
    intro u v hu hv; unfold hasVar; rw [hu, hv]; rfl
  simp only [A_var, Nat.add_sub_cancel]
  exact happ (happ rfl (happ (happ rfl (hst (m + 1))) rfl))
             (happ (happ rfl (hst m)) rfl)

/-- **Root-Match Axiom Collapse**: If `ConvBeta (toLam P) (toLam Q)`, `leaves P ≤ m + 2`,
    and `subst σ P = A_open (m + 1) (.var 1)`, then `subst σ Q = subst σ P`. -/
private theorem root_match_A_open_eq {m : Nat} {P Q : Term} {σ : Nat → Term}
    (hconv : ConvBeta (toLam P) (toLam Q))
    (hlP : leaves P ≤ m + 2)
    (hmatch : subst σ P = A_open (m + 1) (.var 1)) :
    subst σ Q = subst σ P := by
  let τ : Nat → Term := fun v => if hasVar v P then repSS (.var 0) (σ v) else .var 2
  have hτ_on_P : subst τ P = subst (fun v => repSS (.var 0) (σ v)) P :=
    subst_congr (fun v hv => by simp only [τ, hv, ↓reduceIte])
  have hnoSS : noSSAtDepth (m + 3) (subst σ P) := by
    rw [hmatch]
    exact noSSAtDepth_A_open m 1
  have hτP : subst τ P = A_var (m + 1) 0 1 := by
    rw [hτ_on_P, subst_repSS_comm (.var 0) σ (by omega) hnoSS, hmatch, repSS_A_open_eq_A_var]
  have hconvτ : ConvBeta (toLam (A_var (m + 1) 0 1)) (toLam (subst τ Q)) := by
    rw [← hτP]
    exact convBeta_subst_term τ hconv
  have hτQ : subst τ Q = A_var (m + 1) 0 1 :=
    rigidity_A_var m 0 1 (by decide) (subst τ Q) hconvτ
  have hvars_QP : ∀ v, hasVar v Q = true → hasVar v P = true := by
    intro v hvQ
    cases hvP : hasVar v P
    · exfalso
      have hsub2 : IsSubterm (τ v) (subst τ Q) := subterm_subst_of_hasVar hvQ
      have hτv : τ v = .var 2 := by simp only [τ, hvP, Bool.false_eq_true, ↓reduceIte]
      rw [hτv, hτQ] at hsub2
      have hfalse : hasVar 2 (.var 2) = false :=
        hasVar_false_of_subterm hsub2 (hasVar_two_A_var_01 m)
      cases hfalse
    · rfl
  have hrecover : subst unrepSubst (subst τ Q) = subst σ Q := by
    rw [subst_comp]
    refine subst_congr (fun v hvQ => ?_)
    have hvP := hvars_QP v hvQ
    have hτv : τ v = repSS (.var 0) (σ v) := by simp only [τ, hvP, ↓reduceIte]
    rw [hτv]
    have hsub_σ : IsSubterm (σ v) (A_open (m + 1) (.var 1)) := by
      rw [← hmatch]
      exact subterm_subst_of_hasVar hvP
    have hno0 : hasVar 0 (σ v) = false :=
      hasVar_false_of_subterm hsub_σ (hasVar_zero_A_open_one m)
    exact subst_unrepSubst_repSS hno0
  rw [← hrecover, hτQ, subst_unrepSubst_A_var, hmatch]

private theorem subterm_A_open_classify {m y : Nat} {U : Term}
    (hsub : IsSubterm U (A_open (m + 1) (.var y))) :
    U = A_open (m + 1) (.var y) ∨
    U = S ∨
    U = .var y ∨
    (∃ j, U = sTower j (S ⋅ S)) ∨
    (∃ k, U = S ⋅ sTower k (S ⋅ S) ⋅ .var y) ∨
    U = S ⋅ (S ⋅ sTower (m + 1) (S ⋅ S) ⋅ .var y) := by
  simp only [A_open, Nat.add_sub_cancel] at hsub
  cases hsub with
  | refl =>
    simp only [A_open, Nat.add_sub_cancel]
    exact Or.inl trivial
  | left hSL =>
    cases hSL with
    | refl => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    | left hS => cases hS; exact Or.inr (Or.inl rfl)
    | right hL =>
      cases hL with
      | refl => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m + 1, rfl⟩))))
      | right hy => cases hy; exact Or.inr (Or.inr (Or.inl rfl))
      | left hSt =>
        rcases subterm_sTower_SS (m + 2) hSt with rfl | ⟨j, rfl⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))
  | right hR =>
    cases hR with
    | refl => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))
    | right hy => cases hy; exact Or.inr (Or.inr (Or.inl rfl))
    | left hSt =>
      rcases subterm_sTower_SS (m + 1) hSt with rfl | ⟨j, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))

private theorem subterm_axiom_collapse_A_open {m : Nat} {P Q : Term} {σ : Nat → Term}
    (hconv : ConvBeta (toLam P) (toLam Q))
    (hlP : leaves P ≤ m + 2)
    (hsub : IsSubterm (subst σ P) (A_open (m + 1) (.var 1))) :
    subst σ Q = subst σ P := by
  have hconv_σ : ConvBeta (toLam (subst σ P)) (toLam (subst σ Q)) :=
    convBeta_subst_term σ hconv
  rcases subterm_A_open_classify hsub with hroot | hS | hvar | ⟨j, hst⟩ | ⟨k, harm⟩ | hsarm
  · exact root_match_A_open_eq hconv hlP hroot
  · rw [hS] at hconv_σ ⊢
    exact rigidity_S_eq hconv_σ
  · rw [hvar] at hconv_σ ⊢
    exact rigidity_var_eq 1 hconv_σ
  · rw [hst] at hconv_σ ⊢
    exact rigidity_sTower_SS j (subst σ Q) hconv_σ
  · rw [harm] at hconv_σ ⊢
    exact rigidity_arm_SS k 1 (subst σ Q) hconv_σ
  · rw [hsarm] at hconv_σ ⊢
    exact rigidity_s_arm_SS m 1 (subst σ Q) hconv_σ

/-- **Full Negative Resolution of Open Question 32 (Barendregt, Endrullis, Klop & Waldmann 2017, p. 95)**:
    For **every** finite list `E : List (Term × Term)` of `λβ`-sound pure-`S` equations
    (schematic equations allowing arbitrarily many variables), there exist pure-`S` normal forms
    `M, N : Term` (`isIsolatedSNFBool M = true`, `isSNFBool N = true`) whose `λ`-translations
    are `λβ`-convertible (`ConvBeta (toLam M) (toLam N)`) yet `¬ EqTheoryDerives E M N`. -/
theorem question_32_negative_resolution (E : List (Term × Term))
    (hsound : IsLambdaBetaSound E) :
    ∃ M N : Term,
      isIsolatedSNFBool M = true ∧
      isSNFBool N = true ∧
      IsNormalForm M ∧
      IsNormalForm N ∧
      ConvBeta (toLam M) (toLam N) ∧
      ¬ EqTheoryDerives E M N := by
  let m := maxLeavesAxioms E
  let M := A_open (m + 1) (.var 1)
  let N := B_open (m + 1) (.var 1)
  have hsnfM : isSNFBool M = true := isSNFBool_A_open m rfl
  have hsnfN : isSNFBool N = true := isSNFBool_B_open m rfl
  have hnoM : hasAntiRedex M = false := hasAntiRedex_A_open_var m 1
  have hisoM : isIsolatedSNFBool M = true := by
    simp only [isIsolatedSNFBool, hsnfM, hnoM, Bool.not_false, Bool.and_self]
  refine ⟨M, N, hisoM, hsnfN,
    isNormalForm_of_bool hsnfM,
    isNormalForm_of_bool hsnfN,
    convBeta_A_B_open m (.var 1), ?_⟩
  intro hder
  have hrig := eqTheoryDerives_subterm_rigid
    (isNormalForm_of_bool hsnfM) hnoM
    (fun p hp σ => by
      obtain ⟨hl1, hl2⟩ := leaves_le_maxLeavesAxioms hp
      have hcb := hsound p hp
      exact ⟨subterm_axiom_collapse_A_open hcb (by omega),
             subterm_axiom_collapse_A_open hcb.symm (by omega)⟩)
    hder
  exact A_open_ne_B_open m (.var 1) (hrig.1 (.refl _)).symm

/-- **Non-Finite Equational Axiomatizability of `=_{λβ}` on `Ter(CL(S))` (Question 32 Direct Form)**:
    There does NOT exist any finite list `E : List (Term × Term)` of equations between `S`-terms
    such that `CL(S) + E ⊢ M = N ⇔ λβ ⊢ φ(M) = φ(N)` for all `M, N : Term`. -/
theorem no_finite_equational_axiomatization_of_lambda_beta :
    ¬ ∃ E : List (Term × Term),
        ∀ M N : Term, EqTheoryDerives E M N ↔ ConvBeta (toLam M) (toLam N) := by
  rintro ⟨E, hiff⟩
  have hsound : IsLambdaBetaSound E := by
    intro p hp
    have hax : EqTheoryDerives E (subst Term.var p.1) (subst Term.var p.2) := .ax hp Term.var
    have hid : ∀ t : Term, subst Term.var t = t := by
      intro t
      induction t with
      | s => rfl
      | var _ => rfl
      | app a b iha ihb => simp only [subst, iha, ihb]
    rw [hid p.1, hid p.2] at hax
    exact (hiff p.1 p.2).mp hax
  obtain ⟨M, N, _, _, _, _, hbeta, hnot⟩ := question_32_negative_resolution E hsound
  exact hnot ((hiff M N).mpr hbeta)

end FormalQ32
