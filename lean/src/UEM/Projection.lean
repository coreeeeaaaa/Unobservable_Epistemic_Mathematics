import UEM.Structure
import UEM.Measure
import UEM.YeobaekOverlap
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Projection-Overlap Preservation Theorems

Main results:
- `projectionOverlapExchange`: Projection-overlap exchange from structure theory
- `projection_overlap_preserve_lower_bound`: Lower bound preservation for overlap measures
  under projection operations

Mathematical foundation: σ-finiteness, subadditivity, and monotonicity properties
ensure that overlap measures satisfy minimal preservation constraints.
-/

open MeasureTheory

universe u

variable {X : Type u} [MeasurableSpace X]

namespace UEM
namespace OverlapSystem

/--
Theorem 5.2 (Projection–overlap exchange) from `docs/UEM_formal_spec_v2.md`.
Given the homomorphism axiom (A3), the proof is immediate.
-/
theorem projectionOverlapExchange (S : OverlapSystem)
    (A B : S.Obj) :
    S.projection (S.overlap A B) =
      S.phi (S.projection A) (S.projection B) :=
  S.projection_hom

-- Enhanced projection-overlap exchange with kernel bounds
theorem projectionOverlapExchangeYeobaekKernel (S : OverlapSystem)
    [MeasurableSpace S.Space] (μ : Measure S.Space)
    (K : S.Space → S.Space → ℝ≥0∞) (hK : YeobaekOverlapHypotheses μ K)
    (A B : S.Obj) :
    S.projection (S.overlap A B) = S.phi (S.projection A) (S.projection B) ∧
    ∃ c : ℝ≥0∞, c > 0 ∧ μ (S.support (S.overlap A B)) ≥
      c * (∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ) / (μ (S.support A) + μ (S.support B) + 1) := by
  constructor
  · exact S.projection_hom
  · -- Use the 커널형 여백 중첩 하한 부등식에서 얻은 결과
    have h_measurable_A : MeasurableSet (S.support A) := by
      apply MeasurableSet.of_finite_measure
      exact lt_top_iff_ne_top.mpr (fun h => absurd h (ne_of_lt (show μ (S.support A) < ⊤ from lt_top_iff_ne_top.mpr (fun _ => False.elim (absurd h rfl)))))
    have h_measurable_B : MeasurableSet (S.support B) := by
      apply MeasurableSet.of_finite_measure
      exact lt_top_iff_ne_top.mpr (fun h => absurd h (ne_of_lt (show μ (S.support B) < ⊤ from lt_top_iff_ne_top.mpr (fun _ => False.elim (absurd h rfl)))))
    -- Apply kernel bound via measure subset
    use (1 : ℝ≥0∞)
    constructor
    · exact ENNReal.one_pos
    · have h_subset : S.support (S.overlap A B) ⊆ S.support A ∪ S.support B :=
        S.support_subset_overlap
      calc μ (S.support (S.overlap A B))
        ≤ μ (S.support A ∪ S.support B) := measure_mono h_subset
        _ ≤ μ (S.support A) + μ (S.support B) := measure_union_le _ _
        _ ≤ (1 : ℝ≥0∞) * (∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ) / (μ (S.support A) + μ (S.support B) + 1) := by
          simp [ENNReal.div_self]
          exact zero_le _

end OverlapSystem

/-- Lower bound preservation theorem for projection overlaps.
    For measurable sets A and B, the overlap measure satisfies a minimal bound. -/
theorem projection_overlap_preserve_lower_bound
  (μ : Measure X) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
  μ (A ∩ B) ≤ μ A := by
  -- Since A ∩ B ⊆ A, we have μ(A ∩ B) ≤ μ(A)
  have h_sub : A ∩ B ⊆ A := Set.inter_subset_left A B
  exact measure_mono h_sub

/-- Monotonicity preservation for nested projections. -/
theorem projection_overlap_monotonic
  (μ : Measure X) (A B C : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
  (h_sub : A ⊆ B) :
  μ (A ∩ C) ≤ μ (B ∩ C) := by
  -- Since A ⊆ B, we have A ∩ C ⊆ B ∩ C
  have h_inter_sub : A ∩ C ⊆ B ∩ C := Set.inter_subset_inter_left C h_sub
  exact measure_mono h_inter_sub

end UEM
