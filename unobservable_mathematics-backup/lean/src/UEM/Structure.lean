import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Data.Set.Basic
import Mathlib.Data.Complex.Basic

/-!
Formal abstraction of the overlap/projection system described in
`docs/UEM_formal_spec_v2.md` §§1–3. Encodes the overlap monoid (A1), projection
homomorphism (A3), and registers a pseudo-metric structure on the ambient space
so classical geometric lemmas are available directly from mathlib.
-/
namespace UEM

open Metric

universe u v w

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
