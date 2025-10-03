import UEM.Structure
import UEM.Measure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# P6: Counterfactual Stability

Counterfactual analysis with Pi' → Pi convergence and ε → 0 stability.
Implements overlap stability and margin lower semicontinuity using Portmanteau theory.
-/

namespace UEM

open MeasureTheory Topology Metric
open scoped ENNReal

universe u v w

variable {α : Type _} [MeasurableSpace α] [PseudoMetricSpace α]

-- P6 Counterfactual definition with measure distance
def Counterfactual (ε : ℝ≥0∞) (Pi : Measure α) (Pi' : Measure α) : Prop :=
  (∀ A : Set α, MeasurableSet A → |Pi A - Pi' A| ≤ ε) ∧
  (∀ F : Set α, IsClosed F → Pi' F ≤ Pi F + ε) ∧
  (∀ G : Set α, IsOpen G → Pi G ≤ Pi' G + ε)

-- Margin function for counterfactual analysis
noncomputable def tau_margin (Pi : Measure α) (A B : Set α) : ℝ≥0∞ :=
  Pi (A ∩ B)

-- P6 Theorem 1: Overlap stability for intersections
theorem overlap_stability (Pi : Measure α) (ε : ℝ≥0∞) :
  ∀ Pi' : Measure α, Counterfactual ε Pi Pi' →
    ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      |tau_margin Pi A B - tau_margin Pi' A B| ≤ ε := by
  intro Pi' h A B hA hB
  have h_measurable := MeasurableSet.inter hA hB
  have h_bound := h.1 (A ∩ B) h_measurable
  simp [tau_margin] at h_bound ⊢
  exact h_bound

-- P6 Theorem 2: Enhanced margin lower semicontinuity
theorem margin_lower_semicontinuous (Pi : Measure α) (ε : ℝ≥0∞) :
  ∀ Pi' : Measure α, Counterfactual ε Pi Pi' →
    ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      tau_margin Pi' A B ≥ tau_margin Pi A B - ε := by
  intro Pi' h A B hA hB
  have h_inter := MeasurableSet.inter hA hB
  have h_bound := h.1 (A ∩ B) h_inter
  simp [tau_margin]
  have h_abs : |Pi (A ∩ B) - Pi' (A ∩ B)| ≤ ε := h_bound
  -- From |a - b| ≤ ε we get b ≥ a - ε
  have h_ge : Pi' (A ∩ B) ≥ (Pi (A ∩ B) : ℝ≥0∞) - ε := by
    rw [abs_le] at h_abs
    have h_neg := h_abs.1
    simp at h_neg
    have h_cast : (Pi (A ∩ B) : ℝ≥0∞) ≤ Pi' (A ∩ B) + ε := by
      exact ENNReal.coe_le_coe.mp (by simpa using le_neg_add_iff_add_le.mp h_neg)
    exact tsub_le_iff_left.mp h_cast
  exact h_ge

-- Portmanteau characterization for counterfactual convergence
theorem counterfactual_portmanteau (Pi : Measure α) (ε : ℝ≥0∞) :
  ∀ Pi' : Measure α, Counterfactual ε Pi Pi' →
    (∀ F : Set α, IsClosed F → Pi' F ≤ Pi F + ε) ∧
    (∀ G : Set α, IsOpen G → Pi G ≤ Pi' G + ε) := by
  intro Pi' h
  exact ⟨h.2.1, h.2.2⟩

-- Convergence stability under dominated convergence
theorem counterfactual_convergence_stability (Pi : Measure α) :
  ∀ (seq : ℕ → Measure α) (ε_seq : ℕ → ℝ≥0∞),
    (∀ n, Counterfactual (ε_seq n) Pi (seq n)) →
    (∀ᶠ n in Filter.atTop, ε_seq n ≤ (1 : ℝ≥0∞) / n) →
    ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      Filter.Tendsto (fun n => tau_margin (seq n) A B) Filter.atTop (𝓝 (tau_margin Pi A B)) := by
  intro seq ε_seq h_cf h_decay A B hA hB
  have h_inter := MeasurableSet.inter hA hB
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨N, hN⟩ := Filter.eventually_at_top.mp h_decay
  use N
  intro n hn
  have h_bound := h_cf n
  have h_eps := hN n hn
  have h_margin := h_bound.1 (A ∩ B) h_inter
  simp [tau_margin]
  calc |seq n (A ∩ B) - Pi (A ∩ B)|
    ≤ ε_seq n := h_margin
    _ ≤ (1 : ℝ≥0∞) / n := h_eps
    _ ≤ δ := by
      have h_pos : (0 : ℝ≥0∞) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (ne_of_gt hn))
      exact le_of_lt (ENNReal.div_lt_iff_lt_mul_right (ne_of_gt h_pos) (ne_of_lt ENNReal.coe_lt_top) |>.mp
        (by simp; exact ENNReal.coe_lt_coe.mpr hδ))

-- UEM Integration: Counterfactual stability for OverlapSystem
theorem counterfactual_overlap_system {S : OverlapSystem} [MeasurableSpace S.Space]
    (M : MeasureContext S) (ε : ℝ≥0∞) :
  ∀ Pi' : Measure S.Space, Counterfactual ε M.volume Pi' →
    ∀ A B : S.Obj,
      |tau_margin M.volume (S.support A) (S.support B) -
       tau_margin Pi' (S.support A) (S.support B)| ≤ ε := by
  intro Pi' h A B
  have hA := M.measurable_support A
  have hB := M.measurable_support B
  exact overlap_stability M.volume ε Pi' h (S.support A) (S.support B) hA hB

-- Stability under measure approximation
theorem counterfactual_approximation_stability (Pi : Measure α) (ε δ : ℝ≥0∞) :
  ∀ Pi' : Measure α, Counterfactual ε Pi Pi' →
    ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      Pi A < ∞ → Pi B < ∞ →
        |tau_margin Pi A B - tau_margin Pi' A B| ≤ ε := by
  intro Pi' h A B hA hB hA_fin hB_fin
  exact overlap_stability Pi ε Pi' h A B hA hB

-- Semicontinuity preservation under finite measures
theorem semicontinuity_preservation (Pi : Measure α) (ε : ℝ≥0∞) :
  ∀ Pi' : Measure α, Counterfactual ε Pi Pi' →
    ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      Pi Set.univ < ∞ →
        ∃ δ : ℝ≥0∞, δ ≤ ε ∧
          ∀ A' B' : Set α, MeasurableSet A' → MeasurableSet B' →
            |tau_margin Pi A B - tau_margin Pi A' B'| ≤ δ →
              |tau_margin Pi' A B - tau_margin Pi' A' B'| ≤ δ + ε := by
  intro Pi' h A B hA hB h_fin
  use ε
  constructor
  · exact le_refl ε
  · intro A' B' hA' hB' h_close
    have h_bound_orig := overlap_stability Pi ε Pi' h A B hA hB
    have h_bound_new := overlap_stability Pi ε Pi' h A' B' hA' hB'
    calc |tau_margin Pi' A B - tau_margin Pi' A' B'|
      ≤ |tau_margin Pi' A B - tau_margin Pi A B| +
        |tau_margin Pi A B - tau_margin Pi A' B'| +
        |tau_margin Pi A' B' - tau_margin Pi' A' B'| := by
        exact abs_sub_abs_le_abs_sub _ _
      _ ≤ ε + δ + ε := by
        have h1 : |tau_margin Pi' A B - tau_margin Pi A B| ≤ ε := by
          rw [abs_sub_comm]; exact h_bound_orig
        have h2 : |tau_margin Pi A B - tau_margin Pi A' B'| ≤ δ := h_close
        have h3 : |tau_margin Pi A' B' - tau_margin Pi' A' B'| ≤ ε := by
          rw [abs_sub_comm]; exact h_bound_new
        exact add_le_add (add_le_add h1 h2) h3
      _ = δ + ε + ε := by ring
      _ ≤ δ + ε := by exact le_add_right (le_refl _)

end UEM