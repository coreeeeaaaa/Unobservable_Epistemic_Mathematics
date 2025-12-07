import Mathlib
import UEM.Foundations.Dimensions
import UEM.Foundations.State

namespace UEM.Foundations.BasicAxioms

/-!
## UEM 기초 공리 시스템

최소한의 공리로부터 시작하여 점진적 확장
-/

-- 1. 기본 타입 존재 공리
universe u v w

variable (X_phys : Type u) [TopologicalSpace X_phys] [MeasureSpace X_phys]
variable (Dimension : Type v) [Finite Dimension]
variable (Coord : Dimension → Type w) [∀ d, TopologicalSpace (Coord d)]

-- 2. State 공간 정의
def State (X_phys Dimension Coord) :=
  X_phys × (∏ d : Dimension, Coord d) × MarginLog

-- 3. 기본 공리들
namespace BaseAxioms

variable {X_phys Dimension Coord}

axiom state_nonempty : Nonempty (State X_phys Dimension Coord)

axiom phys_space_hausdorff : T2Space X_phys

axiom coord_spaces_discrete : ∀ d, DiscreteTopology (Coord d)

-- 4. 측도 공리 (선택적)
variable [μ : Measure X_phys] [SigmaFinite μ]

axiom measure_borel : IsBorel μ

end BaseAxioms

end UEM.Foundations.BasicAxioms