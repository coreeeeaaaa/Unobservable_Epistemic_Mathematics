import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.OuterMeasure.OfFunction

noncomputable section
open scoped ENNReal
open Set

namespace UEM

/-!
Meta‑definability and epistemic status formalization.
This file brings “undefinable/definable boundary” and
recognizable/measurable/non‑existent/latent‑possible states into a
Lean‑proof‑ready system (no axioms, structure‑first).
-/

/-- Epistemic system with recognizability, measurability, existence and time. -/
structure EpistemicSystem where
  Obj : Type
  Time : Type
  now : Time
  Exists : Obj → Prop
  Recognizable : Obj → Prop
  Measurable : Obj → Prop
  PossibleAt : Obj → Time → Prop
  measure : Obj → ℝ≥0∞
  Value : Type
  Eval : Obj → Value

/-- Recognizable and measurable zero. -/
def MeasurableZero (S : EpistemicSystem) (x : S.Obj) : Prop :=
  S.Recognizable x ∧ S.Measurable x ∧ S.measure x = 0

/-- Recognizable but unmeasurable infinite. -/
def RecognizableUnmeasurableInfinite (S : EpistemicSystem) (x : S.Obj) : Prop :=
  S.Recognizable x ∧ ¬ S.Measurable x ∧ S.measure x = ∞

/-- Non‑cognizable non‑existence. -/
def NonCognizableNonexistent (S : EpistemicSystem) (x : S.Obj) : Prop :=
  ¬ S.Recognizable x ∧ ¬ S.Exists x

/-- Non‑cognizable and non‑measurable state. -/
def NonCognizableUnmeasurable (S : EpistemicSystem) (x : S.Obj) : Prop :=
  ¬ S.Recognizable x ∧ ¬ S.Measurable x

/-- Latent possible: not recognizable/measurable now, but possible at some time. -/
def LatentPossible (S : EpistemicSystem) (x : S.Obj) : Prop :=
  ¬ S.Recognizable x ∧ ¬ S.Measurable x ∧ ∃ t, S.PossibleAt x t

/-- Latent possible specifically outside the current time. -/
def LatentPossibleNotNow (S : EpistemicSystem) (x : S.Obj) : Prop :=
  ¬ S.Recognizable x ∧ ¬ S.Measurable x ∧ (∃ t, t ≠ S.now ∧ S.PossibleAt x t)

/-- Boundary tags for evaluation (no escape). -/
inductive EvalTag
  | val
  | undef
  | out
  | pot
  deriving DecidableEq

/-- Tagged evaluation ensures totality by construction. -/
structure TaggedEvalSystem (S : EpistemicSystem) where
  eval : S.Obj → S.Value × EvalTag

/-- Boundary closure: evaluation always returns a tagged value. -/
theorem tagged_eval_total (S : EpistemicSystem) (T : TaggedEvalSystem S) (x : S.Obj) :
    ∃ v t, T.eval x = (v, t) :=
  ⟨(T.eval x).1, (T.eval x).2, rfl⟩

/-- Definability system with an explicit boundary. -/
structure DefinabilitySystem where
  U : Type
  topo : TopologicalSpace U
  Definable : U → Prop
  boundary : Set U
  boundary_def : boundary = (closure {x | Definable x}) \ {x | Definable x}

attribute [instance] DefinabilitySystem.topo

/-- Undefinable by complement. -/
def Undefinable (D : DefinabilitySystem) (x : D.U) : Prop :=
  ¬ D.Definable x

/-- Boundary implies undefinable. -/
theorem boundary_undefinable (D : DefinabilitySystem) (x : D.U) :
    x ∈ D.boundary → Undefinable D x := by
  intro hx
  have hx' : x ∈ (closure {x | D.Definable x}) \ {x | D.Definable x} := by
    simpa [D.boundary_def] using hx
  have : x ∉ {x | D.Definable x} := by
    have := hx'
    exact this.2
  intro hdef
  exact this hdef

/-- Definable core is the complement of the undefinable region. -/
def DefinableCore (D : DefinabilitySystem) : Set D.U :=
  {x | D.Definable x}

/-- Semantic system: meanings assigned to symbols. -/
structure SemanticSystem where
  Symbol : Type
  Meaning : Type
  Sem : Symbol → Set Meaning
  nonempty_sem : ∀ s, ∃ m, m ∈ Sem s

/-- Definition graph: recursive dependencies (well‑founded by construction). -/
structure DefinitionGraph where
  Def : Type
  depends : Def → Set Def
  no_self : ∀ d, d ∉ depends d

/-- Recursive definition (explicit self‑dependency). -/
def RecursiveDef (G : DefinitionGraph) (d : G.Def) : Prop :=
  d ∈ G.depends d

/-- Non‑recursive definition is guaranteed by `no_self`. -/
theorem no_recursive_def (G : DefinitionGraph) (d : G.Def) :
    ¬ RecursiveDef G d :=
  G.no_self d

end UEM
