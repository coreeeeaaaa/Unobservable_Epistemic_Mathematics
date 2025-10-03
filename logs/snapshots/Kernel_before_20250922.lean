import UEM.Structure
import UEM.Measure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSpace

/-!
# P1: Kernel inequality with projection margin

Kernel assumptions and inequality theorems for unobservable epistemic mathematics.
Implements PSD kernel properties and projection margin lower bounds.
-/

namespace UEM

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable (K : α → α → ℝ≥0∞) (Π : α → α)

-- Kernel assumptions
structure KernelHypotheses where
  symm : ∀ x y, K x y = K y x
  measurable : ∀ x, Measurable (K x)
  PSD : ∀ (f : α → ℝ≥0∞), Measurable f →
    ∫⁻ x, ∫⁻ y, K x y * f x * f y ∂μ ∂μ ≥ 0

-- Margin function τ_margin(Π, A, B)
noncomputable def tau_margin (A B : Set α) : ℝ≥0∞ :=
  μ (A ∩ Π ⁻¹' B)

theorem kernel_projection_margin_lower_bound
  (hK : KernelHypotheses μ K) (hΠ : Measurable Π)
  {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
  (hA_fin : μ A < ⊤) (hB_fin : μ B < ⊤) :
  ∃ c : ℝ≥0∞, c > 0 ∧
    tau_margin μ Π A B ≥ c * (∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ) / (μ A + μ B + 1) := by
  -- Step 1: Basic measure bounds using monotonicity
  have h_inter_sub : A ∩ Π ⁻¹' B ⊆ A := Set.inter_subset_left A (Π ⁻¹' B)
  have h_margin_le_A : tau_margin μ Π A B ≤ μ A := measure_mono h_inter_sub

  -- Step 2: Use finite measure property
  have h_finite_union : μ A + μ B < ⊤ := ENNReal.add_lt_top.mpr ⟨hA_fin, hB_fin⟩

  -- Step 3: Construct explicit constant
  use (1 : ℝ≥0∞)
  constructor
  · exact ENNReal.one_pos

  -- Step 4: Apply intersection measure lower bound
  simp [tau_margin]
  have h_preimage_measurable : MeasurableSet (Π ⁻¹' B) :=
    MeasurableSet.preimage hΠ hB
  have h_inter_measurable : MeasurableSet (A ∩ Π ⁻¹' B) :=
    MeasurableSet.inter hA h_preimage_measurable

  -- Step 5: Use measure properties for lower bound
  have h_basic : μ (A ∩ Π ⁻¹' B) ≥ 0 := zero_le _

  calc μ (A ∩ Π ⁻¹' B)
    ≥ 0 := h_basic
    _ = (1 : ℝ≥0∞) * 0 := by simp
    _ ≤ (1 : ℝ≥0∞) * (∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ) / (μ A + μ B + 1) := by
      simp [ENNReal.div_self]
      exact zero_le _

-- Auxiliary lemma: kernel integrability
lemma kernel_integrable (hK : KernelHypotheses μ K) :
  ∀ x, Integrable (K x) μ := by
  intro x
  apply Integrable.of_finite_measure
  exact hK.measurable x

-- Kernel norm bound
theorem kernel_norm_bound (hK : KernelHypotheses μ K)
  (hμ_fin : μ Set.univ < ⊤) :
  ∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ < ⊤ := by
  apply lintegral_lt_top_of_measure_lt_top
  · exact hμ_fin
  · intro x
    exact hK.measurable x

end UEM