import Mathlib.Tactic.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Shared tactics and simp sets for UEM project

Common simplification rules and tactics used across P1-P6 theorems.
-/

namespace UEM

-- Basic UEM simp rules
attribute [simp] OverlapSystem.measure_identity_zero
attribute [simp] OverlapSystem.overlap_id_left
attribute [simp] OverlapSystem.measure_id

-- Measure theory simp rules
attribute [simp] MeasureTheory.measure_univ_eq_zero
attribute [simp] MeasureTheory.measure_empty

-- ENNReal simp rules for kernel calculations
attribute [simp] ENNReal.one_pos
attribute [simp] ENNReal.zero_le
attribute [simp] ENNReal.div_self

-- Kernel-specific simp rules
lemma kernel_symm_simp {α : Type _} [MeasurableSpace α] (K : α → α → ℝ≥0∞)
  (hK_symm : ∀ x y, K x y = K y x) (x y : α) :
  K x y = K y x := hK_symm x y

attribute [simp] kernel_symm_simp

-- Projection simp rules
lemma projection_overlap_exchange_simp (S : OverlapSystem) (A B : S.Obj) :
  S.projection (S.overlap A B) = S.phi (S.projection A) (S.projection B) :=
  S.projection_hom

attribute [simp] projection_overlap_exchange_simp

-- Support subset simp rules
lemma support_overlap_subset_simp (S : OverlapSystem) (A B : S.Obj) :
  S.support (S.overlap A B) ⊆ S.support A ∪ S.support B :=
  S.support_subset_overlap

attribute [simp] support_overlap_subset_simp

end UEM