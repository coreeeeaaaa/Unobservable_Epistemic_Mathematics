import UemProofs.UEM.UEM_MetaStrata

namespace UEM

/-!
Theorems extracted from structure fields (proof‑ready, no axioms).
-/

theorem boundary_idempotent (S : StrataSystem) (s : S.Stratum) :
    S.boundary (S.boundary s) = S.boundary s :=
  S.boundary_idem s

theorem closure_idempotent (S : StrataSystem) (s : S.Stratum) :
    S.closure (S.closure s) = S.closure s :=
  S.closure_idem s

theorem interior_idempotent (S : StrataSystem) (s : S.Stratum) :
    S.interior (S.interior s) = S.interior s :=
  S.interior_idem s

theorem boundary_monotone (S : StrataSystem) {a b : S.Stratum} (h : a ≤ b) :
    S.boundary a ≤ S.boundary b :=
  S.boundary_mono h

theorem closure_monotone (S : StrataSystem) {a b : S.Stratum} (h : a ≤ b) :
    S.closure a ≤ S.closure b :=
  S.closure_mono h

theorem interior_monotone (S : StrataSystem) {a b : S.Stratum} (h : a ≤ b) :
    S.interior a ≤ S.interior b :=
  S.interior_mono h

/-- Boundary of possible region lies in impossible region (structure law). -/
theorem boundary_possible_subset_impossible
    (S : StrataSystem) (T : ImpossibilityTopology S) {x : S.Stratum}
    (hx : x ∈ ((@closure _ T.topo T.possible) \ T.possible)) :
    x ∈ T.impossible :=
by
  exact T.boundary_possible_subset_impossible x hx

/-- Admissible morphisms preserve recognizability. -/
theorem admissible_preserves_recognizable
    (C : CognitionSystem) (A : Admissible C) (c : C.CognitiveState) (ctx : C.Context) :
    Recognizable C c ctx → Recognizable C (A.map c) ctx :=
  A.preserves_recognizable c ctx

/-! ### Function-based recognizability (admissible contexts) -/

theorem recognizable_fn_by_left_inverse
    (C : CognitionSystemFn) (A : AdmissibleContext C.Context)
    (h : LeftInverseOn C A) (c : C.CognitiveState) (ctx : C.Context) :
    A.ok ctx → RecognizableFn C c ctx :=
  h c ctx

/-! ### Observer complementarity -/

theorem complementarity_exclusion
    {O T Time : Type} (C : Complementarity O T Time) (o : O) (t : T) (τ : Time) :
    ¬ (C.observe o t τ ∧ C.unobserve o t τ) :=
  C.excl o t τ

/-! ### Intent volume / actyon collapse -/

theorem actyon_le_volume
    (W Time : Type) (A : ActyonSystem W Time) (ctx : A.Context) (t : Time) :
    A.Actyon ctx t ≤ A.Volume ctx t :=
  A.collapse_le ctx t

end UEM
