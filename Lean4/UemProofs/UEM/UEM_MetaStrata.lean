import Mathlib.MeasureTheory.OuterMeasure.OfFunction
import Mathlib.Topology.Basic
import Mathlib.Order.Lattice

noncomputable section
open scoped ENNReal

namespace UEM

/-!
Meta‑strata formal system (non‑linear, structure‑first).
This file defines structures and invariants without enumerating cases.
-/

/-- Time system with an order (for existence flow). -/
structure TimeSystem where
  Time : Type
  inst : Preorder Time

attribute [instance] TimeSystem.inst

/-- Strata system as a non‑linear lattice. -/
structure StrataSystem where
  Stratum : Type
  inst : Lattice Stratum
  boundary : Stratum → Stratum
  closure : Stratum → Stratum
  interior : Stratum → Stratum
  boundary_idem : ∀ s, boundary (boundary s) = boundary s
  closure_idem : ∀ s, closure (closure s) = closure s
  interior_idem : ∀ s, interior (interior s) = interior s
  boundary_mono : ∀ {a b}, a ≤ b → boundary a ≤ boundary b
  closure_mono : ∀ {a b}, a ≤ b → closure a ≤ closure b
  interior_mono : ∀ {a b}, a ≤ b → interior a ≤ interior b

attribute [instance] StrataSystem.inst

/-- Impossibility topology on a stratum. -/
structure ImpossibilityTopology (S : StrataSystem) where
  topo : TopologicalSpace S.Stratum
  possible : Set S.Stratum
  impossible : Set S.Stratum
  possible_open : IsOpen possible
  impossible_closed : IsClosed impossible
  boundary_possible_subset_impossible :
    ∀ x, x ∈ (closure possible \ possible) → x ∈ impossible

attribute [instance] ImpossibilityTopology.topo

/-- Absence as structured region (not empty enumeration). -/
structure AbsenceStructure (S : StrataSystem) where
  absence : Set S.Stratum
  absence_nontrivial : ∃ x, x ∈ absence

/-- Strata‑indexed thickness measure. -/
structure StrataThickness (S : StrataSystem) where
  thickness : S.Stratum → (Set S.Stratum → ℝ≥0∞)
  empty_zero : ∀ s, thickness s ∅ = 0
  mono : ∀ s {A B : Set S.Stratum}, A ⊆ B → thickness s A ≤ thickness s B

/-- Existence flow over time and strata. -/
structure ExistenceFlow (S : StrataSystem) (T : TimeSystem) where
  exist : T.Time → S.Stratum → ℝ≥0∞

/-- Change operator for existence flow. -/
def existenceDelta {S : StrataSystem} {T : TimeSystem}
    (F : ExistenceFlow S T) (t1 t2 : T.Time) (s : S.Stratum) : ℝ≥0∞ :=
  F.exist t2 s - F.exist t1 s

/-- Cognition‑first semantics: meaning and recognition are primary. -/
structure CognitionSystem where
  CognitiveState : Type
  Context : Type
  Symbol : Type
  Encode : CognitiveState → Context → Symbol → Prop
  Decode : Symbol → Context → CognitiveState → Prop

/-- Function-based cognition system (Lean-proof-ready). -/
structure CognitionSystemFn where
  CognitiveState : Type
  Context : Type
  Symbol : Type
  Encode : CognitiveState → Context → Symbol
  Decode : Symbol → Context → Set CognitiveState

/-- Recognizability under a cognition system. -/
def Recognizable (C : CognitionSystem)
    (c : C.CognitiveState) (ctx : C.Context) : Prop :=
  ∃ s, C.Encode c ctx s ∧ C.Decode s ctx c

/-- Recognizability for function-based systems. -/
def RecognizableFn (C : CognitionSystemFn)
    (c : C.CognitiveState) (ctx : C.Context) : Prop :=
  c ∈ C.Decode (C.Encode c ctx) ctx

/-- Admissible context constraint. -/
structure AdmissibleContext (Ctx : Type u) where
  ok : Ctx → Prop

/-- Left-inverse property on admissible contexts. -/
def LeftInverseOn (C : CognitionSystemFn) (A : AdmissibleContext C.Context) : Prop :=
  ∀ c ctx, A.ok ctx → RecognizableFn C c ctx

/-- Decode fiber for ambiguity. -/
def DecodeFiber (C : CognitionSystem) (s : C.Symbol) (ctx : C.Context) :
    Set C.CognitiveState :=
  {c | C.Decode s ctx c}

/-- Ambiguity measure on cognitive states. -/
structure AmbiguityMeasure (C : CognitionSystem) where
  μ : Set C.CognitiveState → ℝ≥0∞
  empty_zero : μ ∅ = 0
  mono : ∀ {A B}, A ⊆ B → μ A ≤ μ B

/-- Ambiguity of a symbol under context. -/
def Ambiguity (C : CognitionSystem) (M : AmbiguityMeasure C)
    (s : C.Symbol) (ctx : C.Context) : ℝ≥0∞ :=
  M.μ (DecodeFiber C s ctx)

/-- Admissible morphisms preserve recognizability. -/
structure Admissible (C : CognitionSystem) where
  map : C.CognitiveState → C.CognitiveState
  preserves_recognizable :
    ∀ c ctx, Recognizable C c ctx → Recognizable C (map c) ctx

/-- Observer setting (no global observer assumed). -/
structure ObserverSetting (O T Time : Type u) where
  observe : O → T → Time → Prop

/-- Complementarity: observed and unobserved are exclusive on same target/time. -/
structure Complementarity (O T Time : Type u) extends ObserverSetting O T Time where
  unobserve : O → T → Time → Prop
  excl : ∀ o t τ, ¬ (observe o t τ ∧ unobserve o t τ)

/-- No universal observer (definition-level). -/
def NoUniversalObserver {O T Time : Type u} (C : Complementarity O T Time) : Prop :=
  ¬ ∃ o, ∀ t τ, C.observe o t τ

/-- Multi-axis impossibility state (non-linear coordinate). -/
structure AxisIndex where
  Axis : Type
  Level : Axis → Type

structure ImpossibilityState (A : AxisIndex) where
  coord : ∀ a, A.Level a

/-- Material vs cognitive dimension systems (non‑identical). -/
structure DimensionSystems where
  Dim_material : Type
  Dim_cognitive : Type
  mat_le : Dim_material → Dim_material → Prop
  cog_le : Dim_cognitive → Dim_cognitive → Prop
  mat_inst : Preorder Dim_material
  cog_inst : Preorder Dim_cognitive

/-- Invariant witness for non-reducibility of two dimension systems. -/
structure Invariant (D : Type u) where
  val : D → Nat

def NotIsomorphic (D1 D2 : Type u) (I1 : Invariant D1) (I2 : Invariant D2) : Prop :=
  ¬ ∃ f : D1 → D2, ∀ x, I1.val x = I2.val (f x)

/-- Intent volume system: intent is a volume over context/time. -/
structure IntentVolumeSystem (W Time : Type u) where
  Context : Type
  Possible : W → Prop
  Volume : Context → Time → ℝ≥0∞

/-- Actyon is a collapse/section of intent volume (bounded by volume). -/
structure ActyonSystem (W Time : Type u) extends IntentVolumeSystem W Time where
  Actyon : Context → Time → ℝ≥0∞
  collapse_le : ∀ ctx t, Actyon ctx t ≤ Volume ctx t

attribute [instance] DimensionSystems.mat_inst
attribute [instance] DimensionSystems.cog_inst

end UEM
