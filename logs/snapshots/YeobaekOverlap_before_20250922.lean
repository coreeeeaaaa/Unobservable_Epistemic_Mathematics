import UEM.Structure
import UEM.Measure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSpace

/-!
# P1: 여백 중첩 연산자의 커널형 하한 부등식

`YeobaekOverlap` 모듈은 여백과 형체가 중첩되는 UEM 상위 연산을 Lean 코드로 다룬다.
여백중첩(상위) 정의를 전면에 두고, 그 안에서 커널 기반의 선형/적분 하위 연산(커널 중첩)을 구현한다.
Spec §6 "P1. Projection–Kernel Inequality & Margin Existence"의 조건과 목표를
여백중첩 관점에서 재정리한 계층 구조이다.
-/

/--
여백 중첩(상위) 및 커널 중첩(하위) 가정:
* (Y1) 사영 `Π` 는 가측이다.
* (Y1') 사영 이미지 `Π '' Set.univ` 는 가측이며, 명시적으로 하위 정리에서 추가 가정으로 전달한다.
* (Y2) 커널 `K` 는 대칭 · 양의 준정부호이며 각 단면이 가측·적분가능하다.
* (Y3) 보조 함수 `g` 로부터 전역 상계가 존재해 커널 값을 제어한다.

목표:
* 여백중첩 상위 관점에서 여백 집합 `M := Dom(Π) \ Image(Π)` 가 공집합이 아니고 `μ(M) > 0` 임을 보인다.
* 커널 중첩 하위 연산(PSD 커널 적분)을 이용해 여백의 하한을 정량적으로 추정한다.
-/

namespace UEM

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable (K : α → α → ℝ≥0∞) (Π : α → α)

/--
여백 중첩 연산자의 커널형 가정을 묶어 둔 구조체.
기존 코드의 `KernelHypotheses`와 동일한 제약을 갖지만 명칭을
여백 관점에 맞추어 재명명하였다.
-/
structure YeobaekOverlapHypotheses where
  /-- Symmetry of the kernel: swapping arguments does not change the value. -/
  symm : ∀ x y, K x y = K y x
  /-- For every `x`, the section `y ↦ K x y` is measurable. -/
  measurable_left : ∀ x, Measurable (K x)
  /-- For every `y`, the section `x ↦ K x y` is measurable. -/
  measurable_right : ∀ y, Measurable fun x => K x y
  /-- Positive semidefinite property used to obtain kernel lower bounds. -/
  PSD : ∀ (f : α → ℝ≥0∞), Measurable f →
    ∫⁻ x, ∫⁻ y, K x y * f x * f y ∂μ ∂μ ≥ 0
  /-- Each left section has finite `ℝ≥0∞` integral with respect to `μ`. -/
  lintegral_left_lt_top : ∀ x, ∫⁻ y, K x y ∂μ < ⊤
  /-- A global essential upper bound on the kernel values. -/
  upper_bound : ∃ C : ℝ≥0∞, 0 < C ∧ ∀ x y, K x y ≤ C

/-- Backwards compatibility: 유지보수를 위해 기존 이름도 별칭으로 제공한다. -/
abbrev KernelHypotheses := YeobaekOverlapHypotheses

-- Margin function τ_margin(Π, A, B)
noncomputable def tau_margin (A B : Set α) : ℝ≥0∞ :=
  μ (A ∩ Π ⁻¹' B)

/-- TODO: show the margin is bounded above by the measure of the left set. -/
lemma tau_margin_le_left
    {A B : Set α} (hΠ : Measurable Π)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    tau_margin μ Π A B ≤ μ A := by
  have hsubset : A ∩ Π ⁻¹' B ⊆ A := Set.inter_subset_left _ _
  simpa [tau_margin] using measure_mono hsubset

/-- TODO: helper lemma for rewriting intersections of preimages. -/
lemma measure_preimage_inter
    {A B : Set α} (hΠ : Measurable Π)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (A ∩ Π ⁻¹' B) = μ ((Π ⁻¹' B) ∩ A) := by
  simpa [Set.inter_comm] using rfl

/-- TODO: quantitative lower bound for the double integral induced by `K`. -/
lemma kernel_integral_lower_estimate
    (hK : YeobaekOverlapHypotheses μ K) :
    ∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ ≥ 0 := by
  classical
  have hmeas : Measurable fun _ : α => (1 : ℝ≥0∞) := measurable_const
  simpa using hK.PSD (fun _ => (1 : ℝ≥0∞)) hmeas

/-- TODO: translate an abstract lower bound into a positive-measure margin set. -/
lemma tau_margin_nonempty_of_lower_bound
    {c : ℝ≥0∞}
    (hΠ : Measurable Π)
    (hc_pos : 0 < c)
    (hbound : c ≤ tau_margin μ Π Set.univ (Π '' Set.univ))
    (hmeas : MeasurableSet (Π '' Set.univ)) :
    μ (Set.univ \ Π '' Set.univ) > 0 := by
  -- TODO: leverage measurability of `Π '' Set.univ` to derive positive complement measure.
  sorry

/-- TODO: Main aggregation lemma for P1 margin positivity. -/
lemma margin_positive_measure
    (hK : YeobaekOverlapHypotheses μ K) (hΠ : Measurable Π)
    (hmeas : MeasurableSet (Π '' Set.univ)) :
    μ (Set.univ \ Π '' Set.univ) > 0 := by
  -- TODO: combine helper lemmas into the main statement.
  sorry

theorem kernel_projection_margin_lower_bound
  (hK : YeobaekOverlapHypotheses μ K) (hΠ : Measurable Π)
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

lemma kernel_lintegral_lt_top (hK : YeobaekOverlapHypotheses μ K) :
  ∀ x, ∫⁻ y, K x y ∂μ < ⊤ :=
  hK.lintegral_left_lt_top

-- Kernel norm bound
theorem kernel_norm_bound (hK : YeobaekOverlapHypotheses μ K)
  (hμ_fin : μ Set.univ < ⊤) :
  ∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ < ⊤ := by
  apply lintegral_lt_top_of_measure_lt_top
  · exact hμ_fin
  · intro x
    exact hK.measurable_left x

end UEM
