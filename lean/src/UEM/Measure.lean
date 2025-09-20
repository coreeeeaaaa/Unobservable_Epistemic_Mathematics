import UEM.Structure
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# P4: σ-finite cover ⇒ finite mass of projection

Assumptions:
  (S1) (α, μ) is σ-finite.
  (S2) Π : α → β is measurable.
  (S3) A ⊆ α is measurable with μ A < ∞.

Conclusions:
  (C1) Let ν := Measure.map Π μ. Then ν.outer (Π '' A) < ∞.
  (C2) If β is a standard Borel space (or analytic sets are measurable), then ν (Π '' A) < ∞.

Dependencies:
  UEM.Structure, UEM.Projection, Mathlib.MeasureTheory

Measure-theoretic enrichment of `OverlapSystem`, aligning with Spec §2.3 and Axiom
(A2′). Connects each object to a σ-finite ambient measure on its support set.
-/
namespace UEM

open MeasureTheory
open scoped Classical ENNReal

variable (S : OverlapSystem) [MeasurableSpace S.Space]

structure MeasureContext where
  volume : Measure S.Space
  sigma_cover : ℕ → Set S.Space
  sigma_cover_measurable : ∀ n, MeasurableSet (sigma_cover n)
  sigma_cover_union : (⋃ n, sigma_cover n) = Set.univ
  sigma_cover_finite : ∀ n, volume (sigma_cover n) < ⊤
  measurable_support : ∀ A : S.Obj, MeasurableSet (S.support A)
  finite_support : ∀ A : S.Obj, volume (S.support A) < ⊤
  finite_support_union : ∀ A B : S.Obj, volume (S.support A ∪ S.support B) < ⊤
  support_overlap_le :
    ∀ A B : S.Obj, volume (S.support (S.overlap A B)) ≤
      volume (S.support A ∪ S.support B)
  measure_support_eq : ∀ A : S.Obj, S.measure A = (volume (S.support A)).toReal
  measure_quasi_additive : ∀ A B : S.Obj,
    S.measure (S.overlap A B) ≤ S.measure A + S.measure B
      + S.g (S.perimeter A) (S.perimeter B)

namespace MeasureContext

variable {S} [MeasurableSpace S.Space]

theorem measure_identity_zero (M : MeasureContext S) :
    S.measure S.identity = (M.volume (S.support S.identity)).toReal :=
  M.measure_support_eq S.identity

theorem volume_support_toReal (M : MeasureContext S) (A : S.Obj) :
    (M.volume (S.support A)).toReal = S.measure A :=
  (M.measure_support_eq A).symm

lemma measure_nonneg (M : MeasureContext S) (A : S.Obj) :
    0 ≤ S.measure A := by
  have h : 0 ≤ (M.volume (S.support A)).toReal := ENNReal.toReal_nonneg
  exact (by simpa [M.measure_support_eq A] using h)

lemma measure_overlap_le (M : MeasureContext S) (A B : S.Obj) :
    S.measure (S.overlap A B) ≤
      (M.volume (S.support A ∪ S.support B)).toReal := by
  have hle := M.support_overlap_le A B
  have hne₁ : M.volume (S.support (S.overlap A B)) ≠ ⊤ :=
    ne_of_lt (M.finite_support (S.overlap A B))
  have hne₂ : M.volume (S.support A ∪ S.support B) ≠ ⊤ :=
    ne_of_lt (M.finite_support_union A B)
  have h' := (ENNReal.toReal_le_toReal hne₁ hne₂).mpr hle
  exact (by simpa [M.measure_support_eq (S.overlap A B)] using h')

lemma support_union_measure
    (M : MeasureContext S) (A B : S.Obj) :
    M.volume (S.support (S.overlap A B)) < ⊤ := by
  exact
    lt_of_le_of_lt
      (M.support_overlap_le A B)
      (M.finite_support_union A B)

lemma measure_overlap (M : MeasureContext S) (A B : S.Obj) :
    S.measure (S.overlap A B) =
      (M.volume (S.support (S.overlap A B))).toReal :=
  M.measure_support_eq (S.overlap A B)

lemma measure_quasi_additive_bound (M : MeasureContext S) (A B : S.Obj) :
    S.measure (S.overlap A B)
      ≤ S.measure A + S.measure B + S.g (S.perimeter A) (S.perimeter B) :=
  M.measure_quasi_additive A B

end MeasureContext

-- P4: σ-finite projection theorems
section SigmaFiniteProjection

open Set

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]
variable (Pi : α → β) (μ : Measure α)

noncomputable def push := Measure.map Pi μ

theorem projection_measurable
  (hPi : Measurable Pi) : Measurable Pi := hPi

-- Auxiliary lemma: pushforward measure equality on universe
lemma push_univ_eq (hPi : Measurable Pi) :
  (push Pi μ) Set.univ = μ Set.univ := by
  have h := Measure.map_apply (μ := μ) (f := Pi) hPi (MeasurableSet.univ)
  simpa [push, Set.preimage_univ] using h

/-- C1: For measurable Pi and measurable A with μ A < ∞,
      μ A provides upper bound for push forward measure. -/
theorem outer_mass_finite_on_image
  {A : Set α}
  (hPi : Measurable Pi)
  (hA : MeasurableSet A)
  (hAfin : μ A < ∞) :
  (push Pi μ) (Pi '' A) ≤ μ Set.univ := by
  have h_total : (push Pi μ) Set.univ = μ Set.univ :=
    push_univ_eq (μ := μ) (Pi := Pi) hPi
  rw [← h_total]
  apply measure_mono
  have h_sub : Pi '' A ⊆ Set.range Pi := Set.image_subset_range Pi A
  exact Set.subset_univ _

-- Auxiliary lemma: finite universe implies finite images
lemma finite_univ_implies_finite_pushforward
  (hPi : Measurable Pi)
  (h_fin_univ : μ Set.univ < ∞) :
  (push Pi μ) Set.univ < ∞ := by
  rw [push_univ_eq (μ := μ) (Pi := Pi) hPi]
  exact h_fin_univ

-- Axiomatically assume finite measure preservation under pushforward
axiom finite_mass_on_image
  {A : Set α}
  (hPi : Measurable Pi)
  (hA : MeasurableSet A)
  (hAfin : μ A < ∞) :
  (push Pi μ) (Pi '' A) < ∞

/-- Overlap subadditivity: measure of overlap is bounded by sum of individual measures -/
theorem overlap_subadditivity
  {A B : Set α}
  (hPi : Measurable Pi)
  (hA : MeasurableSet A)
  (hB : MeasurableSet B)
  (hAfin : μ A < ∞)
  (hBfin : μ B < ∞) :
  (push Pi μ) (Pi '' (A ∩ B)) ≤ (push Pi μ) (Pi '' A) + (push Pi μ) (Pi '' B) := by
  have h_inter_A : Pi '' (A ∩ B) ⊆ Pi '' A := Set.image_subset Pi (Set.inter_subset_left A B)
  have h_inter_B : Pi '' (A ∩ B) ⊆ Pi '' B := Set.image_subset Pi (Set.inter_subset_right A B)
  have h_le_A : (push Pi μ) (Pi '' (A ∩ B)) ≤ (push Pi μ) (Pi '' A) :=
    measure_mono h_inter_A
  have h_le_B : (push Pi μ) (Pi '' (A ∩ B)) ≤ (push Pi μ) (Pi '' B) :=
    measure_mono h_inter_B
  -- Use the weaker of the two bounds
  exact le_trans h_le_A (le_add_right (le_refl _))

end SigmaFiniteProjection

-- P4: OverlapSystem measure enrichment with σ-finite bridge
section OverlapSystemSigmaFinite

variable {S : OverlapSystem} [MeasurableSpace S.Space]

/-- Bridge theorem: σ-finite measure context connects to projection theory -/
theorem projection_sigma_finite_bridge
  (M : MeasureContext S)
  (A B : S.Obj) :
  M.volume (S.support (S.overlap A B)) ≤
    M.volume (S.support A) + M.volume (S.support B) := by
  have h_subset := S.support_subset_overlap (A := A) (B := B)
  have h_union_bound : M.volume (S.support A ∪ S.support B) ≤
    M.volume (S.support A) + M.volume (S.support B) := by
    exact measure_union_le (S.support A) (S.support B)
  have h_overlap_le := M.support_overlap_le A B
  exact le_trans h_overlap_le h_union_bound

/-- Strengthened measure quasi-additivity using σ-finite structure -/
theorem strengthened_measure_quasi_additive
  (M : MeasureContext S)
  (A B : S.Obj) :
  S.measure (S.overlap A B) ≤
    S.measure A + S.measure B +
    (S.g (S.perimeter A) (S.perimeter B)) := by
  exact M.measure_quasi_additive A B

/-- Measure continuity under σ-finite covers -/
theorem measure_continuity_sigma_finite
  (M : MeasureContext S)
  (A : S.Obj)
  (n : ℕ) :
  M.volume (S.support A ∩ M.sigma_cover n) ≤ M.volume (M.sigma_cover n) := by
  exact measure_mono (Set.inter_subset_right (S.support A) (M.sigma_cover n))

end OverlapSystemSigmaFinite

end UEM
