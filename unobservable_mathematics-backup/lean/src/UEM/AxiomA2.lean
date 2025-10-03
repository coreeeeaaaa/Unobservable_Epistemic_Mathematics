import UEM.Measure

/-!
Formalises the quasi-additivity requirement (A2′) for the thickness operation.
`AxiomA2` records the assumptions about kernel-induced perimeter bounds and
provides a target theorem `thickness_quasi_additive` ready to be proved once the
analytic lemmas are in place.
-/
namespace UEM

noncomputable section

open Complex
open MeasureTheory
open scoped Classical

structure AxiomA2 (S : OverlapSystem)
    [MeasurableSpace S.Space] (M : MeasureContext S) where
  kernelBound : S.Obj → S.Obj → ℝ
  kernelBound_nonneg : ∀ A B, 0 ≤ kernelBound A B
  perimeter_over_bound : ∀ A B,
    S.g (S.perimeter A) (S.perimeter B) ≤ kernelBound A B
  real_quasi_additive : ∀ A B,
    S.measure (S.overlap A B) ≤ S.measure A + S.measure B + kernelBound A B

namespace AxiomA2

variable {S : OverlapSystem} [MeasurableSpace S.Space]

lemma thickness_quasi_additive
    (M : MeasureContext S) (A2 : AxiomA2 S M) (A B : S.Obj) :
    Complex.abs (S.thickness (S.overlap A B)
      - S.thickness A - S.thickness B)
      ≤ A2.kernelBound A B := by
  have hm := A2.real_quasi_additive A B
  have him := M.measure_quasi_additive_bound A B
  have hnonneg := A2.kernelBound_nonneg A B
  -- TODO: expand thickness components once perimeter bounds are available.
  sorry

end AxiomA2

end UEM
