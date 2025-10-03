import UEM.Structure
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Phase P1: projection primitives (Lean 4.8 bootstrap)

Minimal reconstruction of projection lemmas required for the Phase P1 rebuild.
Kernel inequalities will return once the projection side compiles cleanly.
-/

namespace UEM

open MeasureTheory Set
open scoped Classical ENNReal

variable {α : Type*} [MeasurableSpace α]
variable {𝓩 : Type*} [MeasurableSpace 𝓩]
variable {Boundary : Type*} [MeasurableSpace Boundary]

noncomputable def tau_margin (μ : Measure α) (Pi : α → α)
    (A B : Set α) : ℝ≥0∞ := μ (A ∩ Pi ⁻¹' B)

/-- Residual margin associated with a projection. -/
def residual (Pi : α → α) : Set α := (Pi '' Set.univ)ᶜ

@[simp] lemma residual_def (Pi : α → α) :
    residual Pi = (Pi '' Set.univ)ᶜ := rfl

/-- Bootstrap projection hypotheses. -/
structure YeobaekProjectionHypotheses
    (layer : YeobaekLayeredSpace 𝓩 α Boundary)
    (μ : Measure α) (Pi : α → α) : Type _ where
  measurable : Measurable Pi
  image_measurable : MeasurableSet (Pi '' Set.univ)
  finite_univ : μ Set.univ < ∞
  image_lt_univ : μ (Pi '' Set.univ) < μ Set.univ
  residual_pos : 0 < μ (residual Pi)
  residual_nonempty : (residual Pi).Nonempty

namespace YeobaekProjectionHypotheses

variable {layer : YeobaekLayeredSpace 𝓩 α Boundary}
variable {μ : Measure α} {Pi : α → α}

lemma residual_measurable
    (h : YeobaekProjectionHypotheses layer μ Pi) :
    MeasurableSet (residual Pi) :=
  h.image_measurable.compl

lemma residual_measure_pos
    (h : YeobaekProjectionHypotheses layer μ Pi) :
    0 < μ (residual Pi) :=
  h.residual_pos

lemma residual_nonempty'
    (h : YeobaekProjectionHypotheses layer μ Pi) :
    (residual Pi).Nonempty :=
  h.residual_nonempty

lemma residual_tau_margin_pos
    (h : YeobaekProjectionHypotheses layer μ Pi) :
    0 < tau_margin μ Pi (residual Pi) Set.univ := by
  simpa [tau_margin, residual, Set.preimage_univ]
    using h.residual_pos

lemma residual_tau_margin_eq
    (h : YeobaekProjectionHypotheses layer μ Pi) :
    tau_margin μ Pi (residual Pi) Set.univ
      = μ (residual Pi) := by
  classical
  simp [tau_margin, residual, Set.preimage_univ]

lemma tau_margin_le_left {A B : Set α} :
    tau_margin μ Pi A B ≤ μ A :=
  measure_mono (Set.inter_subset_left _ _)

lemma measure_univ_pos
    (h : YeobaekProjectionHypotheses layer μ Pi) : 0 < μ Set.univ :=
  lt_of_le_of_lt bot_le h.image_lt_univ

lemma tau_margin_lower_of_residual
    (h : YeobaekProjectionHypotheses layer μ Pi)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsubset : residual Pi ⊆ A) (himage : Pi '' A ⊆ B) :
    μ (residual Pi) ≤ tau_margin μ Pi A B := by
  classical
  have hsubset' : residual Pi ⊆ A ∩ Pi ⁻¹' B := by
    intro x hx
    have hxA : x ∈ A := hsubset hx
    have hxB : Pi x ∈ B := himage ⟨x, hxA, rfl⟩
    exact And.intro hxA hxB
  have : μ (residual Pi) ≤ μ (A ∩ Pi ⁻¹' B) := measure_mono hsubset'
  simpa [tau_margin]
    using this

end YeobaekProjectionHypotheses

lemma margin_residual_positive
    (layer : YeobaekLayeredSpace 𝓩 α Boundary)
    (μ : Measure α) (Pi : α → α)
    (h : YeobaekProjectionHypotheses layer μ Pi) :
    0 < μ (residual Pi) :=
  h.residual_measure_pos

structure YeobaekKernelHypotheses (μ : Measure α) (K : α → α → ℝ≥0∞) : Type _ where
  dummy : True := True.intro

abbrev YeobaekOverlapHypotheses (μ : Measure α) (K : α → α → ℝ≥0∞) : Type _ :=
  YeobaekKernelHypotheses μ K

abbrev KernelHypotheses (μ : Measure α) (K : α → α → ℝ≥0∞) : Type _ :=
  YeobaekKernelHypotheses μ K

end UEM
