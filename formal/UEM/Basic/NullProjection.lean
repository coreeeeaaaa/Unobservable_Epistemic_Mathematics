import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Prod
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range

namespace UEM

variable {R V_keep V_null : Type _}
variable [Semiring R] [AddCommMonoid V_keep] [AddCommMonoid V_null]
variable [Module R V_keep] [Module R V_null]

/-- Product 공간 V_prod = V_keep × V_null (R-모듈). -/
abbrev V_prod (V_keep V_null : Type _) : Type _ := V_keep × V_null

/-- Nullification Projection: 선형사상으로 keep 축에 대한 사영. -/
def Pi_null : V_prod V_keep V_null →ₗ[R] V_keep where
  toFun := fun v => v.1
  map_add' := by intro a b; rfl
  map_smul' := by intro a b; rfl

/-- Keep 포함선형사상 (null 축을 0으로 설정). -/
def inc_keep : V_keep →ₗ[R] V_prod V_keep V_null where
  toFun := fun vk => (vk, 0)
  map_add' := by intro a b; ext <;> simp
  map_smul' := by intro a b; ext <;> simp

/-- Null 포함선형사상 (keep 축을 0으로 설정). -/
def inc_null : V_null →ₗ[R] V_prod V_keep V_null where
  toFun := fun vn => (0, vn)
  map_add' := by intro a b; ext <;> simp
  map_smul' := by intro a b; ext <;> simp

@[simp] lemma Pi_null_apply (v : V_prod V_keep V_null) :
    Pi_null (R := R) (V_keep := V_keep) (V_null := V_null) v = v.1 := rfl

@[simp] lemma Pi_null_inc_keep (vk : V_keep) :
    Pi_null (R := R) (V_keep := V_keep) (V_null := V_null) (inc_keep (R := R) (V_null := V_null) vk) = vk := by
  rfl

@[simp] lemma Pi_null_inc_null :
    Pi_null (R := R) (V_keep := V_keep) (V_null := V_null) ∘ₗ inc_null (R := R) (V_keep := V_keep) (V_null := V_null)
      = 0 := by
  ext vn; rfl

/-- 여백 사영을 lift하여 null 축을 0으로 설정. -/
def Pi_null_lift (v : V_prod V_keep V_null) : V_prod V_keep V_null :=
  (Pi_null (R := R) (V_keep := V_keep) (V_null := V_null) v, (0 : V_null))

@[simp] lemma Pi_null_lift_idempotent (v : V_prod V_keep V_null) :
    Pi_null_lift (R := R) (V_keep := V_keep) (V_null := V_null)
      (Pi_null_lift (R := R) (V_keep := V_keep) (V_null := V_null) v)
    =
    Pi_null_lift (R := R) (V_keep := V_keep) (V_null := V_null) v := by
  simp [Pi_null_lift, Pi_null]

/-- 커널은 keep 축이 0인 성분. -/
@[simp] lemma mem_kernel_iff (v : V_prod V_keep V_null) :
    v ∈ LinearMap.ker (Pi_null (R := R) (V_keep := V_keep) (V_null := V_null)) ↔ v.1 = 0 := by
  rfl

/-- 모든 순수 null 성분은 커널에 속함. -/
@[simp] lemma all_null_in_kernel (vn : V_null) :
    ((0 : V_keep), vn) ∈ LinearMap.ker (Pi_null (R := R) (V_keep := V_keep) (V_null := V_null)) := by
  simp

/-- 사영의 상은 전체 keep 공간과 같다 (전사). -/
lemma range_Pi_null : LinearMap.range (Pi_null (R := R) (V_keep := V_keep) (V_null := V_null)) = ⊤ := by
  refine top_unique ?_
  intro vk _
  exact ⟨(vk, 0), by simp⟩

end UEM
