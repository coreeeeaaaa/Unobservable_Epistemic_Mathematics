import UEM.Structure
import UEM.Measure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Analysis.NormedSpace.Basic

/-!
# P1: 여백 중첩 연산자의 커널형 하한 부등식

`YeobaekOverlap` 모듈은 여백과 형체가 중첩되는 UEM 상위 연산을 Lean 코드로 다룬다.
여백중첩(상위) 정의를 전면에 두고, 그 안에서 커널 기반의 선형/적분 하위 연산(커널 중첩)을 구현한다.
Spec §6 "P1. Projection–Kernel Inequality & Margin Existence"의 조건과 목표를
여백중첩 관점에서 재정리한 계층 구조이다.
-/

/--
여백 중첩(상위) 및 커널 중첩(하위) 가정:
* (Y1) 사영 `Pi` 는 가측이다.
* (Y1') 사영 이미지 `Pi '' Set.univ` 는 가측이며, 명시적으로 하위 정리에서 추가 가정으로 전달한다.
* (Y2) 커널 `K` 는 대칭 · 양의 준정부호이며 각 단면이 가측·적분가능하다.
* (Y3) 보조 함수 `g` 로부터 전역 상계가 존재해 커널 값을 제어한다.

목표:
* 여백중첩 상위 관점에서 여백 집합 `M := Dom(Pi) \ Image(Pi)` 가 공집합이 아니고 `μ(M) > 0` 임을 보인다.
* 커널 중첩 하위 연산(PSD 커널 적분)을 이용해 여백의 하한을 정량적으로 추정한다.
-/

namespace UEM

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup α] [NormedSpace ℝ α]
variable {𝓩 : Type*} [NormedAddCommGroup 𝓩] [NormedSpace ℂ 𝓩]
variable {Boundary : Type*} [TopologicalSpace Boundary]
variable (layer : YeobaekLayeredSpace 𝓩 α Boundary)
variable (μ : Measure α)
variable (K : α → α → ℝ≥0∞) (Pi : α → α)

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
    ∫⁻ x, ∫⁻ y, K x y * f x * f y Boundaryμ Boundaryμ ≥ 0
  /-- Each left section has finite `ℝ≥0∞` integral with respect to `μ`. -/
  lintegral_left_lt_top : ∀ x, ∫⁻ y, K x y Boundaryμ < ⊤
  /-- A global essential upper bound on the kernel values. -/
  upper_bound : ∃ C : ℝ≥0∞, 0 < C ∧ ∀ x y, K x y ≤ C
  kernel_lower_bound : ∃ τ_min : ℝ≥0∞, 0 < τ_min ∧ ∀ x, τ_min ≤ ∫⁻ y, K x y Boundaryμ

/-- Backwards compatibility: 유지보수를 위해 기존 이름도 별칭으로 제공한다. -/
abbrev KernelHypotheses := YeobaekOverlapHypotheses

/--
사영 가정: 복소 내부 공간에서 실수 외부 공간으로의 사영이 어떻게 행동하는지,
그리고 실제 측정이 외부 관측 영역에서만 이루어진다는 제약을 함께 묶는다.
`μ`는 외부 공간 위의 측도이며 `layer.measureExternal`과 일치해야 한다.
-/
structure YeobaekProjectionHypotheses
    (layer : YeobaekLayeredSpace 𝓩 α Boundary)
    (μ : Measure α) (Pi : α → α) : Type _ where
  measurable : Measurable Pi
  image_measurable : MeasurableSet (Pi '' Set.univ)
  finite_univ : μ Set.univ < ⊤
  image_lt_univ : μ (Pi '' Set.univ) < μ Set.univ
  projection_agrees : ∀ z, Pi (layer.embedInternal z) = layer.projectionCR z
  boundary_stable : ∀ b, Pi (layer.embedBoundary b) = layer.embedBoundary b
  measure_matches : layer.measureExternal = μ

-- Margin function τ_margin(Pi, A, B)
noncomputable def tau_margin (A B : Set α) : ℝ≥0∞ :=
  μ (A ∩ Pi ⁻¹' B)

/-- TODO: show the margin is bounded above by the measure of the left set. -/
lemma tau_margin_le_left
    {A B : Set α} (hPi : Measurable Pi)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    tau_margin μ Pi A B ≤ μ A := by
  have hsubset : A ∩ Pi ⁻¹' B ⊆ A := Set.inter_subset_left _ _
  simpa [tau_margin] using measure_mono hsubset

/-- TODO: helper lemma for rewriting intersections of preimages. -/
lemma measure_preimage_inter
    {A B : Set α} (hPi : Measurable Pi)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (A ∩ Pi ⁻¹' B) = μ ((Pi ⁻¹' B) ∩ A) := by
  simpa [Set.inter_comm] using rfl

/-- TODO: quantitative lower bound for the double integral induced by `K`. -/
lemma kernel_integral_lower_estimate
    (hK : YeobaekOverlapHypotheses μ K) :
    ∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ ≥ 0 := by
  classical
  have hmeas : Measurable fun _ : α => (1 : ℝ≥0∞) := measurable_const
  simpa using hK.PSD (fun _ => (1 : ℝ≥0∞)) hmeas

/-- TODO: translate an abstract lower bound into a positive-measure margin set. -/
lemma margin_residual_positive
    {Pi : α → α}
    (hPi : YeobaekProjectionHypotheses layer μ Pi) :
    μ (Set.univ \ Pi '' Set.univ) > 0 := by
  classical
  have hcompl := measure_add_measure_compl (Pi '' Set.univ)
  -- If the residual measure were zero, the image would have full measure, contradicting `image_lt_univ`.
  have hset : (Pi '' Set.univ)ᶜ = Set.univ \ Pi '' Set.univ := by
    ext x; by_cases hx : x ∈ Pi '' Set.univ <;> simp [Set.mem_compl, hx]
  have hpos_ne : μ ((Pi '' Set.univ)ᶜ) ≠ 0 := by
    intro hzero
    have hEq : μ (Pi '' Set.univ) = μ (Set.univ : Set α) := by
      have := hcompl
      simpa [hzero, add_zero] using this
    exact (ne_of_lt hPi.image_lt_univ) hEq
  -- convert `≠ 0` to strict positivity and rewrite the set as a set difference
  have hpos : 0 < μ ((Pi '' Set.univ)ᶜ) :=
    lt_of_le_of_ne (zero_le _) (by simpa [ne_comm] using hpos_ne)
  simpa [hset] using hpos

/-- 여백중첩 가정과 사영 가정을 결합해 여백 잔여가 양의 측도를 갖는다는 결론을 얻는다. -/
lemma margin_positive_measure
    (hK : YeobaekOverlapHypotheses μ K)
    {Pi : α → α}
    (hPi : YeobaekProjectionHypotheses layer μ Pi) :
    μ (Set.univ \ Pi '' Set.univ) > 0 :=
  margin_residual_positive (layer := layer) (μ := μ) (Pi := Pi) hPi

/-- TODO: 커널 적분 하한을 여백 잔여와 직접 연결하는 보조 lemma. -/
lemma kernel_overlap_lower_aux
    (hK : YeobaekOverlapHypotheses μ K)
    {Pi : α → α}
    (hPi : YeobaekProjectionHypotheses layer μ Pi)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ ≥ 0 := by
  -- TODO: Combine PSD condition with residual measure bound.
  -- 계획
  -- 1. 잔여 영역 characteristic function을 test function으로 사용.
  -- 2. `margin_positive_measure`로 양의 측도 확보 → 최소량 ε 정의.
  -- 3. Fubini/monotonicity로 커널 적분 하한 도출.
  exact kernel_integral_lower_estimate (μ := μ) (K := K) hK

/-- P1의 핵심 결론: 여백 잔여 집합이 비어 있지 않음을 보인다. -/
theorem yeobaek_margin_exists
    (hK : YeobaekOverlapHypotheses μ K)
    {Pi : α → α}
    (hPi : YeobaekProjectionHypotheses layer μ Pi) :
    (Set.univ \ Pi '' Set.univ).Nonempty := by
  classical
  have hpos := margin_positive_measure (layer := layer) (μ := μ) (K := K) (Pi := Pi) hK hPi
  have hpos_ne : μ (Set.univ \ Pi '' Set.univ) ≠ 0 := ne_of_gt hpos
  by_contra hempty
  have hset : Set.univ \ Pi '' Set.univ = (∅ : Set α) := by
    ext x; constructor
    · intro hx
      exact (hempty ⟨x, hx⟩).elim
    · intro hx; simpa using hx
  have hzero : μ (Set.univ \ Pi '' Set.univ) = 0 := by
    simpa [hset] using (measure_empty : μ (∅ : Set α) = 0)
  exact hpos_ne hzero

theorem kernel_projection_margin_lower_bound_core
  (hK : YeobaekOverlapHypotheses μ K)
  {Pi : α → α}
  (hPi : YeobaekProjectionHypotheses layer μ Pi)
  {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
  (hA_fin : μ A < ⊤) (hB_fin : μ B < ⊤)
  {ε τ_min : ℝ≥0∞}
  (hε_pos : 0 < ε) (hτ_pos : 0 < τ_min)
  (h_margin_lower : tau_margin μ Pi A B ≥ ε)
  (h_integral_lower : τ_min ≤ ∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ) :
  ∃ c : ℝ≥0∞, c > 0 ∧
    tau_margin μ Pi A B ≥ c * (∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ) / (μ A + μ B + 1) := by
  classical
  set integralK := ∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ
  have h_integral_pos : 0 < integralK := lt_of_lt_of_le hτ_pos h_integral_lower
  set denom := μ A + μ B + 1
  have h_denom_pos : 0 < denom :=
    lt_of_lt_of_le ENNReal.zero_lt_one
      (by
        have : (0 : ℝ≥0∞) ≤ μ A + μ B := bot_le
        simpa [denom, add_comm, add_left_comm, add_assoc] using add_le_add_right this (1 : ℝ≥0∞))
  have h_integral_ne : integralK ≠ 0 := ne_of_gt h_integral_pos
  have h_denom_ne : denom ≠ 0 := ne_of_gt h_denom_pos
  set c : ℝ≥0∞ := ε * denom / integralK
  have hc_pos : 0 < c := ENNReal.div_pos_iff.mpr ⟨mul_pos hε_pos h_denom_pos, h_integral_ne⟩
  have h_fraction : c * integralK / denom = ε := by
    have h1 : c * integralK = ε * denom := by
      simp [c, h_integral_ne, mul_comm, mul_left_comm, mul_assoc]
    have h2 : denom ≠ 0 := h_denom_ne
    simpa [h1, h2] using ENNReal.mul_div_cancel' (c * integralK) h2
  refine ⟨c, hc_pos, ?_⟩
  have h_margin_lower' : tau_margin μ Pi A B ≥ ε := h_margin_lower
  simpa [h_fraction] using h_margin_lower'

/-- 잔여 영역과 전체 집합을 사용할 때의 τ_margin 값은 잔여의 측도와 동일하다. -/
lemma tau_margin_residual_univ
    {Pi : α → α}
    (hPi : YeobaekProjectionHypotheses layer μ Pi) :
    tau_margin μ Pi (Set.univ \ Pi '' Set.univ) Set.univ = μ (Set.univ \ Pi '' Set.univ) := by
  classical
  simp [tau_margin]

/-- 커널의 두께 하한과 전체 측도를 이용해 전역 적분의 하한을 도출한다. -/
/-- 잔여 영역이 비교 대상 집합에 포함되고 사영 이미지가 목표 집합에 들어갈 때, τ_margin은 잔여 측도 이상이다. -/
lemma tau_margin_lower_of_residual
    {Pi : α → α}
    (hPi : YeobaekProjectionHypotheses layer μ Pi)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h_residual_subset : Set.univ \ Pi '' Set.univ ⊆ A)
    (h_image_subset : Pi '' A ⊆ B) :
    μ (Set.univ \ Pi '' Set.univ) ≤ tau_margin μ Pi A B := by
  classical
  let residual := Set.univ \ Pi '' Set.univ
  have hsubset : residual ⊆ A ∩ Pi ⁻¹' B := by
    intro x hx
    have hxA : x ∈ A := h_residual_subset hx
    have hxB : Pi x ∈ B := by
      have hxImage : Pi x ∈ Pi '' A := by exact ⟨x, hxA, rfl⟩
      exact h_image_subset hxImage
    exact And.intro hxA hxB
  have hmono := measure_mono hsubset
  simpa [tau_margin, residual] using hmono

lemma kernel_integral_lower_bound_global
    (hK : YeobaekOverlapHypotheses μ K)
    (hμ_fin : μ Set.univ < ⊤) (hμ_pos : 0 < μ Set.univ) :
    ∃ τ_min : ℝ≥0∞, 0 < τ_min ∧ τ_min ≤ ∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ := by
  classical
  rcases hK.kernel_lower_bound with ⟨τ_base, hτ_pos, hτ_le⟩
  have h_ae : (fun _ : α => τ_base) ≤ᵐ[μ] fun x => ∫⁻ y, K x y Boundaryμ :=
    Filter.eventually_of_forall hτ_le
  have h_fin : μ Set.univ ≠ ∞ := lt_top_iff_ne_top.mp hμ_fin
  have h_integral := lintegral_mono_ae (μ := μ) h_ae
  have h_le : τ_base * μ Set.univ ≤ ∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ := by
    simpa [lintegral_const, h_fin, ENNReal.mul_comm, ENNReal.mul_left_comm, ENNReal.mul_assoc] using h_integral
  refine ⟨τ_base * μ Set.univ, mul_pos hτ_pos hμ_pos, ?_⟩
  simpa using h_le

/-- 잔여 영역과 전체 집합을 사용할 때의 커널 부등식. -/
theorem kernel_projection_margin_lower_bound_residual
  (hK : YeobaekOverlapHypotheses μ K)
  {Pi : α → α}
  (hPi : YeobaekProjectionHypotheses layer μ Pi)
  (hμ_fin : μ Set.univ < ⊤) (hμ_pos : 0 < μ Set.univ) :
  ∃ c : ℝ≥0∞, c > 0 ∧
    tau_margin μ Pi (Set.univ \ Pi '' Set.univ) Set.univ ≥
      c * (∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ) /
        (μ (Set.univ \ Pi '' Set.univ) + μ Set.univ + 1) := by
  classical
  set residual := Set.univ \ Pi '' Set.univ
  have hA_meas : MeasurableSet residual := hPi.image_measurable.compl
  have hB_meas : MeasurableSet (Set.univ : Set α) := MeasurableSet.univ
  have hA_fin : μ residual < ⊤ :=
    lt_of_le_of_lt (measure_mono (by intro x hx; trivial)) hμ_fin
  have h_residual_subset : residual ⊆ residual := by intro x hx; exact hx
  have h_image_subset : Pi '' residual ⊆ (Set.univ : Set α) := by intro x hx; trivial
  obtain ⟨c, hc_pos, h_bound⟩ :=
    kernel_projection_margin_lower_bound (layer := layer) (μ := μ) (K := K) (Pi := Pi)
      hK hPi (A := residual) (B := Set.univ) hA_meas hB_meas
      hA_fin hμ_fin hμ_fin hμ_pos h_residual_subset h_image_subset
  simpa [residual, add_comm, add_left_comm, add_assoc] using h_bound

/-- 일반 형태의 커널 하한 부등식. 잔여 포함과 커널 두께 하한을 활용해 양의 상수 `c`를 도출한다. -/
theorem kernel_projection_margin_lower_bound
  (hK : YeobaekOverlapHypotheses μ K)
  {Pi : α → α}
  (hPi : YeobaekProjectionHypotheses layer μ Pi)
  {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
  (hA_fin : μ A < ⊤) (hB_fin : μ B < ⊤)
  (hμ_fin : μ Set.univ < ⊤) (hμ_pos : 0 < μ Set.univ)
  (h_residual_subset : Set.univ \ Pi '' Set.univ ⊆ A)
  (h_image_subset : Pi '' A ⊆ B) :
  ∃ c : ℝ≥0∞, c > 0 ∧
    tau_margin μ Pi A B ≥ c * (∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ) /
      (μ A + μ B + 1) := by
  classical
  set residual := Set.univ \ Pi '' Set.univ
  have hε_pos : 0 < μ residual :=
    margin_positive_measure (layer := layer) (μ := μ) (K := K) (Pi := Pi) hK hPi
  have h_margin_lower :=
    tau_margin_lower_of_residual (layer := layer) (μ := μ) (K := K) (Pi := Pi)
      hPi hA hB h_residual_subset h_image_subset
  obtain ⟨τ_min, hτ_pos, hτ_le⟩ :=
    kernel_integral_lower_bound_global (layer := layer) (μ := μ) (K := K)
      hK hμ_fin hμ_pos
  let ε := μ residual
  have hA_fin' := hA_fin
  have hB_fin' := hB_fin
  obtain ⟨c, hc_pos, h_bound⟩ :=
    kernel_projection_margin_lower_bound_core (layer := layer) (μ := μ) (K := K) (Pi := Pi)
      hK hPi hA hB hA_fin' hB_fin'
      (ε := ε) (τ_min := τ_min)
      (hε_pos := hε_pos) (hτ_pos := hτ_pos)
      (h_margin_lower := h_margin_lower)
      (h_integral_lower := hτ_le)
  refine ⟨c, hc_pos, ?_⟩
  simpa using h_bound

lemma kernel_lintegral_lt_top (hK : YeobaekOverlapHypotheses μ K) :
  ∀ x, ∫⁻ y, K x y Boundaryμ < ⊤ :=
  hK.lintegral_left_lt_top

-- Kernel norm bound
theorem kernel_norm_bound (hK : YeobaekOverlapHypotheses μ K)
  (hμ_fin : μ Set.univ < ⊤) :
  ∫⁻ x, ∫⁻ y, K x y Boundaryμ Boundaryμ < ⊤ := by
  apply lintegral_lt_top_of_measure_lt_top
  · exact hμ_fin
  · intro x
    exact hK.measurable_left x

end UEM
