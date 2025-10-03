import UEM.Structure
import UEM.Measure
import UEM.YeobaekOverlap
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# P2: Measure-preserving flows

Spec §3.4 models the time-evolution operator `Φₜ` as a measurable semigroup of
bijections on the observable space that preserves the external measure.  Rather
than constructing such a flow analytically, we encapsulate the required axioms in
`FlowSystem` and derive the invariance results that drive the “margin persistence”
argument used after Phase P1.
-/

namespace UEM

open MeasureTheory Function Set

universe u

variable {α : Type u} [MeasurableSpace α]
variable {μ : Measure α}

/--
Abstract interface for a Spec §3.4 flow.  The map `flow t` represents the state
transition after time `t`.  The structure records the axioms stated in the spec:

* `measurable_flow` — joint measurability of the time slices;
* `flow_zero` and `flow_semigroup` — semigroup laws for the evolution operator;
* `flow_left_inverse`, `flow_right_inverse` — reversible dynamics obtained by
  reversing time (`flow (-t)`);
* `measure_preserving_flow` — preservation of the reference measure.

These fields are sufficient to derive the margin persistence lemmas used in
Phases P1 and P2.
-/
structure FlowSystem (μ : Measure α) where
  flow : ℝ → α → α
  measurable_flow : ∀ t, Measurable (flow t)
  flow_zero : flow 0 = id
  flow_semigroup : ∀ s t, flow (s + t) = flow s ∘ flow t
  flow_left_inverse : ∀ t, LeftInverse (flow (-t)) (flow t)
  flow_right_inverse : ∀ t, RightInverse (flow (-t)) (flow t)
  measure_preserving_flow : ∀ t, MeasurePreserving (flow t) μ μ

namespace FlowSystem

variable (F : FlowSystem μ)

@[simp] lemma flow_zero_eq_id : F.flow 0 = id := F.flow_zero

@[simp] lemma flow_zero_apply (x : α) : F.flow 0 x = x :=
  congrArg (fun g : α → α => g x) (flow_zero_eq_id F)

lemma flow_comp (s t : ℝ) : F.flow (s + t) = F.flow s ∘ F.flow t :=
  F.flow_semigroup s t

@[simp] lemma flow_left_inverse_apply (t : ℝ) (x : α) :
    F.flow (-t) (F.flow t x) = x :=
  (F.flow_left_inverse t) x

@[simp] lemma flow_right_inverse_apply (t : ℝ) (x : α) :
    F.flow t (F.flow (-t) x) = x :=
  (F.flow_right_inverse t) x

lemma flow_injective (t : ℝ) : Injective (F.flow t) := by
  intro x y hxy
  have hx := congrArg (F.flow (-t)) hxy
  simpa [F.flow_left_inverse_apply t x, F.flow_left_inverse_apply t y] using hx

lemma flow_surjective (t : ℝ) : Surjective (F.flow t) := by
  intro y
  refine ⟨F.flow (-t) y, ?_⟩
  simpa using F.flow_right_inverse_apply t y

lemma flow_bijective (t : ℝ) : Bijective (F.flow t) :=
  ⟨F.flow_injective t, F.flow_surjective t⟩

/-- Every time-slice `flow t` is measurable.  This exposes the Spec §3.4
`measurable` requirement as a standalone lemma for downstream automation. -/
lemma slice_measurable (t : ℝ) : Measurable (F.flow t) :=
  F.measurable_flow t

/-- Divergence-free generator encoded as `Measure.map (flow t) μ = μ`.
This reformulates Spec §3.4's Jacobian=1 axiom in Lean. -/
lemma flow_map_eq (t : ℝ) : Measure.map (F.flow t) μ = μ :=
  (F.measure_preserving_flow t).map_eq

lemma flow_image_eq_preimage (t : ℝ) (A : Set α) :
    F.flow t '' A = (F.flow (-t)) ⁻¹' A := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩
    change F.flow (-t) (F.flow t x) ∈ A
    simpa [F.flow_left_inverse_apply t x] using hx
  · intro hy
    refine ⟨F.flow (-t) y, hy, ?_⟩
    simpa using F.flow_right_inverse_apply t y

lemma measure_preimage_eq (t : ℝ) {A : Set α} (hA : MeasurableSet A) :
    μ (F.flow t ⁻¹' A) = μ A :=
  (F.measure_preserving_flow t).measure_preimage hA

lemma measure_image_eq (t : ℝ) {A : Set α} (hA : MeasurableSet A) :
    μ (F.flow t '' A) = μ A := by
  have h := F.measure_preimage_eq (-t) (A := A) hA
  simpa [F.flow_image_eq_preimage t A] using h

/-- Margin persistence: the measure of a measurable set is invariant under the flow. -/
lemma margin_persistence {A : Set α} (hA : MeasurableSet A) (t : ℝ) :
    μ (F.flow t '' A) = μ A :=
  F.measure_image_eq t hA

lemma margin_positive_invariant {A : Set α} (hA : MeasurableSet A)
    (hpos : μ A ≠ 0) (t : ℝ) : μ (F.flow t '' A) ≠ 0 := by
  simpa [F.margin_persistence hA t] using hpos

lemma margin_positive_gt_zero {A : Set α} (hA : MeasurableSet A)
    (hpos : 0 < μ A) (t : ℝ) : 0 < μ (F.flow t '' A) := by
  simpa [F.margin_persistence hA t] using hpos

end FlowSystem

/-! ### Yeobaek-layered flows -/

section Yeobaek

variable {𝓩 : Type _} {Boundary : Type _}
variable [MeasurableSpace 𝓩]
variable [MeasurableSpace Boundary]

/--
Specialised flow hypotheses for a `YeobaekLayeredSpace`.  In addition to a
`FlowSystem` on the external space, we assume that the observable region is
stable under the flow.  This is the condition labelled “observable domain
conservation” in Spec §3.4.
-/
structure YeobaekFlowHypotheses
    (layer : YeobaekLayeredSpace 𝓩 α Boundary) : Type _ where
  system : FlowSystem layer.measureExternal
  observable_stable : ∀ t, system.flow t '' layer.observable = layer.observable

namespace YeobaekFlowHypotheses

variable {layer : YeobaekLayeredSpace 𝓩 α Boundary}
variable (H : YeobaekFlowHypotheses layer)

@[simp] lemma observable_image_eq (t : ℝ) :
    H.system.flow t '' layer.observable = layer.observable :=
  H.observable_stable t

lemma observable_subset_image (t : ℝ) :
    layer.observable ⊆ H.system.flow t '' layer.observable := by
  simpa [observable_image_eq H t] using Subset.rfl

lemma measure_invariant_of_subset_observable
    {A : Set α} (hA : MeasurableSet A) (_hsubset : A ⊆ layer.observable) (t : ℝ) :
    layer.measureExternal (H.system.flow t '' A) = layer.measureExternal A :=
  H.system.margin_persistence (μ := layer.measureExternal) hA t

lemma flow_semigroup (s t : ℝ) :
    H.system.flow (s + t) = H.system.flow s ∘ H.system.flow t :=
  H.system.flow_semigroup s t

lemma measure_preserving (t : ℝ) :
    MeasurePreserving (H.system.flow t) layer.measureExternal layer.measureExternal :=
  H.system.measure_preserving_flow t

/-! #### Projection residual sets -/

variable {Pi : α → α}
variable {K : α → α → ℝ≥0∞}

def residual (Pi : α → α) : Set α := Set.univ \ Pi '' Set.univ

lemma residual_eq_compl (Pi : α → α) : residual Pi = (Pi '' Set.univ)ᶜ := by
  ext x; by_cases hx : x ∈ Pi '' Set.univ
  · simp [residual, Set.diff_eq, hx]
  · simp [residual, Set.diff_eq, hx]

lemma measurable_residual
    (hPi : YeobaekProjectionHypotheses (layer := layer) layer.measureExternal Pi) :
    MeasurableSet (residual Pi) := by
  have h : MeasurableSet (Pi '' Set.univ) := hPi.image_measurable
  have hcompl : MeasurableSet ((Pi '' Set.univ)ᶜ) := h.compl
  simpa [residual_eq_compl (α := α) Pi] using hcompl

lemma residual_measure_invariant
    (hPi : YeobaekProjectionHypotheses (layer := layer) layer.measureExternal Pi)
    (t : ℝ) :
    layer.measureExternal (H.system.flow t '' residual Pi)
      = layer.measureExternal (residual Pi) :=
  H.system.margin_persistence
    (μ := layer.measureExternal)
    (t := t)
    (A := residual Pi)
    (hA := YeobaekProjectionHypotheses.residual_measurable
      (layer := layer) (μ := layer.measureExternal) (Pi := Pi) hPi)

lemma residual_positive_invariant
    (hPi : YeobaekProjectionHypotheses (layer := layer) layer.measureExternal Pi)
    (t : ℝ) :
    0 < layer.measureExternal (H.system.flow t '' residual Pi) := by
  classical
  have hpos' :=
    margin_residual_positive (layer := layer) (μ := layer.measureExternal)
      (Pi := Pi) hPi
  have hpos : 0 < layer.measureExternal (residual Pi) := by
    simpa [residual] using hpos'
  simpa using H.system.margin_positive_gt_zero
    (μ := layer.measureExternal)
    (A := residual Pi)
    (hA := YeobaekProjectionHypotheses.residual_measurable
      (layer := layer) (μ := layer.measureExternal) (Pi := Pi) hPi)
    (t := t)
    hpos

/--
Combined hypotheses for Phase P1 and P2: a measurable, measure-preserving flow
acting on the observable region together with a projection that leaves a
positive-measure residual margin.  Spec §3.4 additionally assumes the residual
domain is σ-finite; we record it explicitly as `residualSigmaFinite`.
-/
structure FlowProjectionHypotheses
    (layer : YeobaekLayeredSpace 𝓩 α Boundary)
    (Pi : α → α) (K : α → α → ℝ≥0∞) where
  flow : YeobaekFlowHypotheses (layer := layer)
  projection : YeobaekProjectionHypotheses (layer := layer) layer.measureExternal Pi
  overlap : YeobaekOverlapHypotheses layer.measureExternal K
  residualSigmaFinite :
    SigmaFinite
      (layer.measureExternal.restrict (residual Pi))

namespace FlowProjectionHypotheses

/-! ### Main P2 lemmas and corollaries -/

variable {layer Pi K}
variable (H : FlowProjectionHypotheses (layer := layer) (Pi := Pi) (K := K))

/-- σ-finiteness of the residual margin, mirroring Spec §3.4. -/
lemma residual_sigmaFinite :
    SigmaFinite
      (layer.measureExternal.restrict (residual Pi)) :=
  H.residualSigmaFinite

/-- Time-slice measurability specialised to the combined hypotheses. -/
lemma slice_measurable (t : ℝ) :
    Measurable (H.flow.system.flow t) :=
  H.flow.system.slice_measurable t

/-- The flow map preserves the external measure; encoded as a Jacobian=1 assertion. -/
lemma flow_map_eq (t : ℝ) :
    Measure.map (H.flow.system.flow t) layer.measureExternal
      = layer.measureExternal :=
  H.flow.system.flow_map_eq t

theorem residual_margin_persistence (t : ℝ) :
    layer.measureExternal
        (H.flow.system.flow t '' residual Pi) =
      layer.measureExternal (residual Pi) :=
  H.flow.residual_measure_invariant (layer := layer) (Pi := Pi) H.projection t

theorem residual_margin_positive (t : ℝ) :
    0 < layer.measureExternal
        (H.flow.system.flow t '' residual Pi) :=
  H.flow.residual_positive_invariant
    (layer := layer) (Pi := Pi) (K := K)
    H.projection H.overlap t

@[simp] theorem flow_measure_preserving (t : ℝ) :
    MeasurePreserving (H.flow.system.flow t)
      layer.measureExternal layer.measureExternal :=
  H.flow.measure_preserving (layer := layer) t

theorem flow_semigroup (s t : ℝ) :
    H.flow.system.flow (s + t)
      = H.flow.system.flow s ∘ H.flow.system.flow t :=
  H.flow.flow_semigroup s t

theorem measure_preserving_of_subset
    {A : Set α} (hA : MeasurableSet A) (hsubset : A ⊆ layer.observable) (t : ℝ) :
    layer.measureExternal (H.flow.system.flow t '' A) = layer.measureExternal A :=
  H.flow.measure_invariant_of_subset_observable (layer := layer)
    (A := A) (hA := hA) (t := t) (hsubset := hsubset)

/-- Margin persistence, recorded explicitly for downstream use. -/
theorem margin_persistence_main (t : ℝ) :
    layer.measureExternal
        (H.flow.system.flow t '' residual Pi) =
      layer.measureExternal (residual Pi) :=
  H.residual_margin_persistence (layer := layer) (Pi := Pi) (K := K) t

end FlowProjectionHypotheses

end YeobaekFlowHypotheses

end Yeobaek

end UEM
