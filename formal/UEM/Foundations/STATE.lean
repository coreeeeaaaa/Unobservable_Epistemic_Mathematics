import Mathlib
import UEM.Foundations.Dimensions

namespace UEM.Foundations

/-!
## UEM State 정의 및 기본 성질
-/

-- 여백 로그 정의
structure MarginLog where
  entries : List (ℝ × String)  -- (timestamp, description)
  deriving Decidable, Inhabited

-- State 공간 정의
def State (X : Type _) [TopologicalSpace X] :=
  X × (∏ d : Dimension, d.coord) × MarginLog

-- State 생성자
def State.mk
  {X} [TopologicalSpace X]
  (phys : X)
  (coords : ∏ d : Dimension, d.coord)
  (margin : MarginLog) : State X :=
  (phys, coords, margin)

-- State 접근자
def State.phys {X} [TopologicalSpace X] (s : State X) : X := s.1
def State.coords {X} [TopologicalSpace X] (s : State X) : ∏ d : Dimension, d.coord := s.2.1
def State.margin {X} [TopologicalSpace X] (s : State X) : MarginLog := s.2.2

-- 위상 구조
instance {X} [TopologicalSpace X] : TopologicalSpace (State X) :=
  instTopologicalSpaceProd

-- 기본 연산
def State.update_phys {X} [TopologicalSpace X] (f : X → X) (s : State X) : State X :=
  (f s.phys, s.coords, s.margin)

def State.update_coord {X} [TopologicalSpace X]
  (d : Dimension) (f : d.coord → d.coord) (s : State X) : State X :=
  (s.phys, Function.update s.coords d (f (s.coords d)), s.margin)

def State.add_margin_entry {X} [TopologicalSpace X]
  (time : ℝ) (desc : String) (s : State X) : State X :=
  (s.phys, s.coords, {s.margin with entries := (time, desc) :: s.margin.entries})

-- 기본 정리들
@[simp] theorem State.phys_mk {X} [TopologicalSpace X]
  (phys coords margin) : (State.mk phys coords margin).phys = phys := rfl

@[simp] theorem State.coords_mk {X} [TopologicalSpace X]
  (phys coords margin) : (State.mk phys coords margin).coords = coords := rfl

@[simp] theorem State.margin_mk {X} [TopologicalSpace X]
  (phys coords margin) : (State.mk phys coords margin).margin = margin := rfl

-- 차원 독립성이 State update에도 적용됨을 보여주는 정리
theorem State.coord_update_comm {X} [TopologicalSpace X]
  (s : State X) (d₁ d₂ : Dimension) (h : d₁ ≠ d₂)
  (f₁ : d₁.coord → d₁.coord) (f₂ : d₂.coord → d₂.coord) :
  State.update_coord d₁ f₁ (State.update_coord d₂ f₂ s) =
  State.update_coord d₂ f₂ (State.update_coord d₁ f₁ s) := by
  unfold State.update_coord
  have := dimension_independence s.1 d₁ d₂ h f₁ f₂
  simp [this]

end UEM.Foundations