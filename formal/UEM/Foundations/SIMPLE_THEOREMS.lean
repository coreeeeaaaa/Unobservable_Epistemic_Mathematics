import Mathlib
import UEM.Foundations.State

namespace UEM.Foundations.SimpleTheorems

/-!
## 기본 증명들 - UEM 시작점
-/

-- State 공간의 기본 성질들
variable {X : Type _} [TopologicalSpace X]

-- State 생성이 가능함
theorem state_nonempty : Nonempty (State X) := by
  have h : Nonempty X := inferInstance
  have h2 : Nonempty MarginLog := inferInstance
  exact ⟨⟨Classical.choose h, fun _ => default, default⟩⟩

-- State 좌표 업데이트의 기본 성질
theorem coord_update_idempotent
  (s : State X) (d : Dimension) (f : d.coord → d.coord) :
  State.update_coord d f (State.update_coord d id s) =
  State.update_coord d f s := by
  unfold State.update_coord
  simp only [Function.update_comp, Function.update_id]

-- 두 개의 다른 차원 업데이트는 교환 가능
theorem coord_update_comm_simple
  (s : State X) (d₁ d₂ : Dimension) (h : d₁ ≠ d₂)
  (f₁ : d₁.coord → d₁.coord) (f₂ : d₂.coord → d₂.coord) :
  State.update_coord d₁ f₁ (State.update_coord d₂ f₂ s) =
  State.update_coord d₂ f₂ (State.update_coord d₁ f₁ s) := by
  unfold State.update_coord
  ext ⟨phys, coords, margin⟩
  simp only [Function.update_apply]
  by_cases h_eq : d₁ = d₁
  . simp [h_eq]
  . simp [Function.update_noteq (Ne.symm h_eq)]

end UEM.Foundations.SimpleTheorems