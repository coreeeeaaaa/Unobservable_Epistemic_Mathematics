import Mathlib
import UEM.Foundations.State

namespace UEM.Foundations

/-!
## 여백 사영 정의
-/

-- Keep/Null 공간 정의
structure KeepNullDecomposition (X : Type _) [TopologicalSpace X] where
  keep : Subspace X
  null : Subspace X
  direct_sum : keep ⊕ null = ⊤

-- 여백 사영 연산자
structure NullProjection (X : Type _) [TopologicalSpace X] [AddCommGroup X]
  [Module ℝ X] where
  toFun : State X → State X
  linear' : IsLinearMap ℝ toFun
  idempotent' : toFun ∘ toFun = toFun
  range_keep : ∀ s, (toFun s).phys ∈ (decomposition.keep : Set X)

-- 여백 로그 갱신
def UpdateMarginLog (proj : NullProjection X) (s : State X) : State X :=
  let old_phys := s.phys
  let new_phys := proj.toFun s.phys
  let loss := old_phys - new_phys
  let timestamp := 0.0  -- 실제 시간은 외부에서
  let entry := (timestamp, s!"Projection loss: {loss}")
  { s with
    phys := new_phys,
    margin := {s.margin with entries := entry :: s.margin.entries} }

-- 기본 공리들
namespace ProjectionAxioms

variable {X : Type _} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
variable (Π : NullProjection X)

-- 멱등성 (정의에 포함됨)
theorem idempotent : Π.toFun ∘ Π.toFun = Π.toFun := Π.idempotent'

-- 선형성 (정의에 포함됨)
theorem linear : IsLinearMap ℝ Π.toFun := Π.linear'

-- 여백 정보 보존
theorem margin_preservation (s : State X) :
  (UpdateMarginLog Π s).margin.entries ≠ s.margin.entries := by
  unfold UpdateMarginLog
  simp

-- 사영의 상은 keep 공간에 속함
theorem range_in_keep (s : State X) :
  (Π.toFun s).phys ∈ (Π.decomposition.keep : Set X) := Π.range_keep s

end ProjectionAxioms

end UEM.Foundations