import UEM.Basic.NullProjection
import Mathlib.Data.Set.Basic

namespace UEM

section

-- Re-introduce Zero instances here to get a concrete '0' value.
variable (V_keep V_null : Type _) [Zero V_keep] [Zero V_null]

/-- 편의상 V = V_keep × V_null 로 표기 -/
abbrev V : Type _ := V_prod V_keep V_null

/-- Nullification projection의 kernel:
    Pi_null_lift v = (0,0) 이 되는 v들의 집합 -/
def kernelPiNull : Set (V V_keep V_null) :=
  -- Pass the explicit zero value to Pi_null_lift
  { v | Pi_null_lift (0 : V_null) v = ((0 : V_keep), (0 : V_null)) }

/-- (vk, vn)이 kernel에 속한다는 것은 vk = 0 과 동치 -/
lemma mem_kernel_iff (vk : V_keep) (vn : V_null) :
  (vk, vn) ∈ @kernelPiNull V_keep V_null _ _ ↔ vk = 0 := by
  unfold kernelPiNull
  simp [Pi_null_lift, Pi_null]

/-- 모든 null 성분 (0, vn)은 kernel에 속한다. -/
lemma all_null_in_kernel (vn : V_null) :
  ((0 : V_keep), vn) ∈ @kernelPiNull V_keep V_null _ _ := by
  unfold kernelPiNull
  simp [Pi_null_lift, Pi_null]

end

end UEM
