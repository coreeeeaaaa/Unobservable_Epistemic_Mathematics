import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Data.Set.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
Formal abstraction of the overlap/projection system described in
`docs/UEM_formal_spec_v2.md` §§1–3. Encodes the overlap monoid (A1), projection
homomorphism (A3), and registers a pseudo-metric structure on the ambient space
so classical geometric lemmas are available directly from mathlib.
-/
namespace UEM

open Metric
open MeasureTheory

universe u v w

/--
`YeobaekLayeredSpace` formalizes the 삼중 중첩 구조 described in the UEM spec.
It keeps the internal 잠재 공간 `Internal` as a complex normed space, the 외부
관측 공간 `External` as a real normed space equipped with a measurable
structure, and an intermediate 경계 공간 `Boundary`.  The observable region is a
measurable subset of the external space and every observable/측정 가능한 양은
이 집합에서만 정의된다는 철학을 반영한다.
-/
structure YeobaekLayeredSpace
    (Internal External Boundary : Type _)
    [MeasurableSpace Internal] [MeasurableSpace External] [MeasurableSpace Boundary] : Type _ where
  embedInternal : Internal → External
  embedBoundary : Boundary → External
  projectionCR : Internal → External
  observable : Set External
  measureExternal : Measure External
  projection_measurable : Measurable projectionCR
  boundary_measurable : Measurable embedBoundary
  observable_measurable : MeasurableSet observable
  projection_observable : ∀ z, projectionCR z ∈ observable
  boundary_observable : ∀ b, embedBoundary b ∈ observable
  internal_hidden : ∀ z, embedInternal z ∉ observable

namespace YeobaekLayeredSpace

variable {Internal External Boundary : Type _}
variable [MeasurableSpace Internal] [MeasurableSpace External] [MeasurableSpace Boundary]

@[simp]
theorem projection_in_observable
    (Λ : YeobaekLayeredSpace Internal External Boundary)
    (z : Internal) : Λ.projectionCR z ∈ Λ.observable :=
  Λ.projection_observable z

@[simp]
theorem boundary_in_observable
    (Λ : YeobaekLayeredSpace Internal External Boundary)
    (b : Boundary) : Λ.embedBoundary b ∈ Λ.observable :=
  Λ.boundary_observable b

@[simp]
theorem internal_not_observable
    (Λ : YeobaekLayeredSpace Internal External Boundary)
    (z : Internal) : Λ.embedInternal z ∉ Λ.observable :=
  Λ.internal_hidden z

end YeobaekLayeredSpace

structure OverlapSystem where
  Obj : Type u
  ProjectionSpace : Type v
  Space : Type w
  instPseudo : PseudoMetricSpace Space
  overlap : Obj → Obj → Obj
  identity : Obj
  phi : ProjectionSpace → ProjectionSpace → ProjectionSpace
  projection : Obj → ProjectionSpace
  support : Obj → Set Space
  embed : Obj → Space
  measure : Obj → ℝ
  perimeter : Obj → ℝ
  thickness : Obj → Complex
  g : ℝ → ℝ → ℝ
  kernel : Space → Space → ℝ
  overlap_assoc : ∀ {A B C : Obj}, overlap (overlap A B) C = overlap A (overlap B C)
  overlap_comm : ∀ {A B : Obj}, overlap A B = overlap B A
  overlap_id : ∀ {A : Obj}, overlap A identity = A
  phi_assoc : ∀ {x y z : ProjectionSpace}, phi (phi x y) z = phi x (phi y z)
  projection_hom : ∀ {A B : Obj}, projection (overlap A B) = phi (projection A) (projection B)
  support_subset_overlap : ∀ {A B : Obj},
    support (overlap A B) ⊆ support A ∪ support B
  measure_nonneg : ∀ {A : Obj}, 0 ≤ measure A
  measure_identity_zero : measure identity = 0
  kernel_symm : ∀ {x y : Space}, kernel x y = kernel y x
  perimeter_nonneg : ∀ {A : Obj}, 0 ≤ perimeter A
  thickness_spec : ∀ A : Obj,
    thickness A = Complex.mk (measure A) (perimeter A)
  g_nonneg : ∀ x y : ℝ, 0 ≤ g x y
  g_symm : ∀ x y : ℝ, g x y = g y x

namespace OverlapSystem

variable (S : OverlapSystem)

instance : PseudoMetricSpace S.Space := S.instPseudo

@[simp] theorem overlap_id_left (A : S.Obj) :
    S.overlap S.identity A = A := by
  have h := S.overlap_comm (A := S.identity) (B := A)
  simpa [h] using S.overlap_id (A := A)

@[simp] theorem dist_self (x : S.Space) : dist x x = 0 := by
  simpa using dist_self x

@[simp] theorem measure_id : S.measure S.identity = 0 :=
  S.measure_identity_zero

lemma support_overlap_subset (A B : S.Obj) :
    S.support (S.overlap A B) ⊆ S.support A ∪ S.support B :=
  S.support_subset_overlap

end OverlapSystem

end UEM
