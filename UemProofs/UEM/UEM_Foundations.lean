import Mathlib.MeasureTheory.OuterMeasure.OfFunction
import Mathlib.Data.Set.Lattice

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal

universe u v w

namespace UEM

/-- In UEM, a `World` is the ambient type in which we reason. -/
abbrev World : Type (w + 1) := Type w

/--
An `Observer` packages a projection into observable objects together with the
induced observational kernel.
-/
class Observer (O : Type u) where
  ObsObject : Type v
  observe : O → ObsObject
  kernel : O → O → Prop
  kernel_spec : ∀ {x y : O}, kernel x y ↔ observe x = observe y

namespace Observer

variable {O : Type u} [Observer O]

/-- The observational kernel is an equivalence relation because it is defined by equality. -/
theorem kernel_is_equivalence : Equivalence (Observer.kernel (O := O)) := by
  constructor
  · intro x
    exact (Observer.kernel_spec (x := x) (y := x)).2 rfl
  · intro x y hxy
    have hxy' := (Observer.kernel_spec (x := x) (y := y)).1 hxy
    exact (Observer.kernel_spec (x := y) (y := x)).2 hxy'.symm
  · intro x y z hxy hyz
    have hxy' := (Observer.kernel_spec (x := x) (y := y)).1 hxy
    have hyz' := (Observer.kernel_spec (x := y) (y := z)).1 hyz
    exact (Observer.kernel_spec (x := x) (y := z)).2 (hxy'.trans hyz')

/-- The `Setoid` induced by an observer kernel. -/
def setoid : Setoid O :=
  ⟨Observer.kernel, kernel_is_equivalence⟩

/-- The observational margin (kernel quotient) for an observer. -/
abbrev Margin : Type u := Quotient (setoid (O := O))

/-- The kernel equivalence class of an element. -/
def kernelClass (x : O) : Set O := {y | Observer.kernel y x}

end Observer

/--
Data used to induce a Carathéodory outer measure. This is the formal home for
UEM's thickness primitive `τ`.
-/
structure ThicknessBasis (O : Type u) where
  cost : Set O → ℝ≥0∞
  empty_cost : cost ∅ = 0

namespace ThicknessBasis

variable {O : Type u}

/-- The outer measure induced from a thickness basis via Carathéodory's construction. -/
def outerMeasure (basis : ThicknessBasis O) : OuterMeasure O :=
  OuterMeasure.ofFunction basis.cost basis.empty_cost

/-- The induced thickness function `τ`. -/
def thickness (basis : ThicknessBasis O) (S : Set O) : ℝ≥0∞ :=
  basis.outerMeasure S

/-- `τ` satisfies the outer measure axioms by construction. -/
theorem thickness_is_outer_measure (basis : ThicknessBasis O) :
    (basis.thickness ∅ = 0) ∧
      (∀ ⦃s t : Set O⦄, s ⊆ t → basis.thickness s ≤ basis.thickness t) ∧
      (∀ s : ℕ → Set O,
        basis.thickness (⋃ n, s n) ≤ ∑' n, basis.thickness (s n)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [thickness, outerMeasure]
  · intro s t hst
    exact measure_mono hst
  · intro s
    simpa using (measure_iUnion_le (μ := basis.outerMeasure) s)

end ThicknessBasis

end UEM
