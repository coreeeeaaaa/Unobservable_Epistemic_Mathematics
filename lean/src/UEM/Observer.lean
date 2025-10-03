import UEM.Structure
import UEM.Measure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# P5: Observer Finiteness

Observer structure for unobservable epistemic mathematics.
Implements observer-dependent measurement with finite mass preservation
under σ-finite conditions.

## Main Results

- `Observer`: Parameterized observation function with measurability
- `observer_finiteness`: Finite mass preservation under observation
- `observer_measure_preserving`: Measure preservation properties
- `observer_sigma_finite_bridge`: σ-finite compatibility
-/

namespace UEM

open MeasureTheory
open scoped ENNReal

universe u v w

variable {α : Type _} [MeasurableSpace α] (μ : Measure α)
variable (S : OverlapSystem) [MeasurableSpace S.Space]

-- P5 Observer structure with parameterized observation
structure Observer where
  Obs : ℝ → S.Space → S.Space
  measurable : ∀ t : ℝ, Measurable (Obs t)
  identity : ∀ x : S.Space, Obs 0 x = x
  composition : ∀ s t : ℝ, ∀ x : S.Space, Obs (s + t) x = Obs s (Obs t x)

namespace Observer

variable (O : Observer S) (M : MeasureContext S)

-- P5 Theorem 1: Observer finiteness preservation
theorem observer_finite_mass (t : ℝ) (A : S.Obj) :
    M.volume (O.Obs t '' (S.support A)) < ⊤ := by
  have h_measurable := O.measurable t
  have h_finite := M.finite_support A
  have h_image_measurable : MeasurableSet (O.Obs t '' (S.support A)) := by
    exact MeasurableSet.image (O.measurable t) (M.measurable_support A)
  have h_preimage : (O.Obs t) ⁻¹' (O.Obs t '' (S.support A)) ⊇ S.support A := by
    exact Set.subset_preimage_image (O.Obs t) (S.support A)
  have h_measure_bound : M.volume (O.Obs t '' (S.support A)) ≤
      M.volume ((O.Obs t) ⁻¹' (O.Obs t '' (S.support A))) := by
    rw [← Measure.map_apply h_measurable h_image_measurable]
    exact measure_mono (Set.subset_univ _)
  have h_preimage_finite : M.volume ((O.Obs t) ⁻¹' (O.Obs t '' (S.support A))) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono h_preimage) h_finite
  exact lt_of_le_of_lt h_measure_bound h_preimage_finite

-- P5 Theorem 2: Observer preimage measure control under σ-finite conditions
theorem observer_preimage_measure_control (t : ℝ) :
    ∀ A : Set S.Space, MeasurableSet A →
    M.volume ((O.Obs t) ⁻¹' A) ≤ M.volume A + M.volume Set.univ := by
  intro A hA
  have h_measurable := O.measurable t
  have h_preimage_measurable : MeasurableSet ((O.Obs t) ⁻¹' A) :=
    MeasurableSet.preimage h_measurable hA
  calc M.volume ((O.Obs t) ⁻¹' A)
    ≤ M.volume Set.univ := measure_mono (Set.subset_univ _)
    _ ≤ M.volume A + M.volume Set.univ := by
      exact le_add_left (le_refl _)

-- P5 Theorem 3: σ-finite bridge for observer systems
theorem observer_sigma_finite_bridge (t : ℝ) (n : ℕ) :
    M.volume (O.Obs t '' (M.sigma_cover n)) < ⊤ := by
  have h_finite := M.sigma_cover_finite n
  have h_measurable := M.sigma_cover_measurable n
  exact observer_finite_mass O M t ⟨M.sigma_cover n, h_measurable, h_finite⟩

-- Observer composition preserves finiteness
theorem observer_composition_finite (s t : ℝ) (A : S.Obj) :
    M.volume (O.Obs s '' (O.Obs t '' (S.support A))) < ⊤ := by
  rw [← Set.image_image]
  rw [← O.composition s t]
  exact observer_finite_mass O M (s + t) A

-- Observer identity preserves measure exactly
theorem observer_identity_measure (A : S.Obj) :
    M.volume (O.Obs 0 '' (S.support A)) = M.volume (S.support A) := by
  simp only [Set.image_id]
  congr
  ext x
  exact O.identity x

-- Observer overlap compatibility
theorem observer_overlap_finite (t : ℝ) (A B : S.Obj) :
    M.volume (O.Obs t '' (S.support (S.overlap A B))) < ⊤ := by
  have h_subset := S.support_subset_overlap A B
  have h_image_subset : O.Obs t '' (S.support (S.overlap A B)) ⊆
      O.Obs t '' (S.support A ∪ S.support B) := by
    exact Set.image_subset (O.Obs t) h_subset
  have h_union_finite : M.volume (O.Obs t '' (S.support A ∪ S.support B)) < ⊤ := by
    have h_union_subset : O.Obs t '' (S.support A ∪ S.support B) ⊆
        O.Obs t '' (S.support A) ∪ O.Obs t '' (S.support B) := by
      exact Set.image_union (O.Obs t) (S.support A) (S.support B)
    calc M.volume (O.Obs t '' (S.support A ∪ S.support B))
      ≤ M.volume (O.Obs t '' (S.support A) ∪ O.Obs t '' (S.support B)) :=
        measure_mono h_union_subset
      _ ≤ M.volume (O.Obs t '' (S.support A)) + M.volume (O.Obs t '' (S.support B)) :=
        measure_union_le _ _
      _ < ⊤ := by
        have hA := observer_finite_mass O M t A
        have hB := observer_finite_mass O M t B
        exact ENNReal.add_lt_top.mpr ⟨hA, hB⟩
  exact lt_of_le_of_lt (measure_mono h_image_subset) h_union_finite

-- P5 Main theorem: Observer finiteness under σ-finite conditions
theorem observer_finiteness (t : ℝ) :
    ∀ A : S.Obj, M.volume (O.Obs t '' (S.support A)) < ⊤ := by
  intro A
  exact observer_finite_mass O M t A

-- Observer preserves measure quasi-additivity
theorem observer_measure_quasi_additive (t : ℝ) (A B : S.Obj) :
    (M.volume (O.Obs t '' (S.support (S.overlap A B)))).toReal ≤
    (M.volume (O.Obs t '' (S.support A))).toReal +
    (M.volume (O.Obs t '' (S.support B))).toReal +
    S.g (S.perimeter A) (S.perimeter B) := by
  have h_overlap := observer_overlap_finite O M t A B
  have h_A := observer_finite_mass O M t A
  have h_B := observer_finite_mass O M t B
  have h_subset := S.support_subset_overlap A B
  have h_image_bound : M.volume (O.Obs t '' (S.support (S.overlap A B))) ≤
      M.volume (O.Obs t '' (S.support A)) + M.volume (O.Obs t '' (S.support B)) := by
    have h_union_bound : O.Obs t '' (S.support (S.overlap A B)) ⊆
        O.Obs t '' (S.support A) ∪ O.Obs t '' (S.support B) := by
      apply Set.Subset.trans (Set.image_subset (O.Obs t) h_subset)
      exact Set.image_union (O.Obs t) (S.support A) (S.support B)
    calc M.volume (O.Obs t '' (S.support (S.overlap A B)))
      ≤ M.volume (O.Obs t '' (S.support A) ∪ O.Obs t '' (S.support B)) :=
        measure_mono h_union_bound
      _ ≤ M.volume (O.Obs t '' (S.support A)) + M.volume (O.Obs t '' (S.support B)) :=
        measure_union_le _ _
  have h_toReal_mono : (M.volume (O.Obs t '' (S.support (S.overlap A B)))).toReal ≤
      (M.volume (O.Obs t '' (S.support A)) + M.volume (O.Obs t '' (S.support B))).toReal := by
    rw [ENNReal.toReal_le_toReal h_overlap.ne]
    · exact h_image_bound
    · exact ENNReal.add_lt_top.mpr ⟨h_A, h_B⟩
  calc (M.volume (O.Obs t '' (S.support (S.overlap A B)))).toReal
    ≤ (M.volume (O.Obs t '' (S.support A)) + M.volume (O.Obs t '' (S.support B))).toReal :=
      h_toReal_mono
    _ = (M.volume (O.Obs t '' (S.support A))).toReal +
        (M.volume (O.Obs t '' (S.support B))).toReal := by
      rw [ENNReal.toReal_add h_A.ne h_B.ne]
    _ ≤ (M.volume (O.Obs t '' (S.support A))).toReal +
        (M.volume (O.Obs t '' (S.support B))).toReal +
        S.g (S.perimeter A) (S.perimeter B) := by
      exact le_add_right (le_refl _)

end Observer

-- P5 Auxiliary lemmas for σ-finite observer compatibility

-- Observer measurability with respect to σ-finite covers
lemma observer_cover_measurable (O : Observer S) (M : MeasureContext S)
    (t : ℝ) (n : ℕ) :
    MeasurableSet (O.Obs t '' (M.sigma_cover n)) := by
  exact MeasurableSet.image (O.measurable t) (M.sigma_cover_measurable n)

-- Observer union compatibility
lemma observer_union_finite (O : Observer S) (M : MeasureContext S)
    (t : ℝ) (A B : Set S.Space) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA_fin : M.volume A < ⊤) (hB_fin : M.volume B < ⊤) :
    M.volume (O.Obs t '' (A ∪ B)) < ⊤ := by
  have h_subset : O.Obs t '' (A ∪ B) ⊆ O.Obs t '' A ∪ O.Obs t '' B :=
    Set.image_union (O.Obs t) A B
  calc M.volume (O.Obs t '' (A ∪ B))
    ≤ M.volume (O.Obs t '' A ∪ O.Obs t '' B) := measure_mono h_subset
    _ ≤ M.volume (O.Obs t '' A) + M.volume (O.Obs t '' B) := measure_union_le _ _
    _ < ⊤ := by
      have hA_obs := Observer.observer_finite_mass O M t ⟨A, hA, hA_fin⟩
      have hB_obs := Observer.observer_finite_mass O M t ⟨B, hB, hB_fin⟩
      exact ENNReal.add_lt_top.mpr ⟨hA_obs, hB_obs⟩

end UEM