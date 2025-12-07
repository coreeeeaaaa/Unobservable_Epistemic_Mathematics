import UEM.Basic.NullProjection
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace UEM

section

variable (R V_keep V_null : Type _)
variable [Semiring R] [AddCommMonoid V_keep] [AddCommMonoid V_null]
variable [Module R V_keep] [Module R V_null]

/-- (vk, vn)이 kernel에 속한다는 것은 vk = 0 과 동치 -/
lemma mem_kernel_iff_keep_zero (vk : V_keep) (vn : V_null) :
  (vk, vn) ∈ LinearMap.ker (Pi_null (R := R) (V_keep := V_keep) (V_null := V_null)) ↔ vk = 0 := by
  simp [Pi_null]

/-- 모든 null 성분 (0, vn)은 kernel에 속한다. -/
lemma all_null_in_kernel' (vn : V_null) :
  ((0 : V_keep), vn) ∈ LinearMap.ker (Pi_null (R := R) (V_keep := V_keep) (V_null := V_null)) := by
  simp

/-- 사영의 상은 전체 keep 공간. -/
lemma range_top :
  LinearMap.range (Pi_null (R := R) (V_keep := V_keep) (V_null := V_null)) = (⊤ : Submodule R V_keep) :=
  range_Pi_null (R := R) (V_keep := V_keep) (V_null := V_null)

/-- keep 포함 후 사영은 항등. -/
@[simp] lemma Pi_null_inc_keep_id (vk : V_keep) :
  Pi_null (R := R) (V_keep := V_keep) (V_null := V_null) (inc_keep (R := R) (V_null := V_null) vk) = vk := by
  simp [inc_keep, Pi_null]

/-- null 포함 후 사영은 0. -/
@[simp] lemma Pi_null_inc_null_zero (vn : V_null) :
  Pi_null (R := R) (V_keep := V_keep) (V_null := V_null) (inc_null (R := R) (V_keep := V_keep) (V_null := V_null) vn) = 0 := by
  simp [inc_null, Pi_null]

end

section

variable {𝕜 : Type _} [RCLike 𝕜]
variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
/-- 커널–여백 피타고라스:
  Hilbert 공간 `V`와 자기수반 사영 `P`에 대해 `‖v‖^2 = ‖P v‖^2 + ‖(I-P) v‖^2`. -/
theorem pythagoras_projection
  (P : V →ₗ[𝕜] V)
  (hIdem : P.comp P = P)
  (hSelfAdj : P.adjoint = P) :
  ∀ v : V, ‖v‖^2 = ‖P v‖^2 + ‖((LinearMap.id : V →ₗ[𝕜] V) - P) v‖^2 := by
  intro v
  -- 보조 사상 Q := I - P
  let Q : V →ₗ[𝕜] V := (LinearMap.id : V →ₗ[𝕜] V) - P
  -- P ∘ (I - P) = 0 using idempotence.
  have h_comp_zero : P.comp Q = 0 := by
    -- derive P (P x) = P x from hIdem
    have hPP : ∀ x, P (P x) = P x := by
      intro x
      simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hIdem
    ext x
    have hPPx := hPP x
    -- P (x - P x) = P x - P (P x) = 0
    simp [LinearMap.comp_apply, Q, map_sub, hPPx]
  -- Orthogonality: ⟪P v, (I - P) v⟫ = 0.
  have h_orth :
      inner (𝕜:=𝕜) (E:=V) (P v) (Q v) = 0 := by
    -- move P using self-adjointness
    have h_adj :
        inner (𝕜:=𝕜) (E:=V) (P (Q v)) v = inner (𝕜:=𝕜) (E:=V) (Q v) (P v) := by
      simpa [hSelfAdj] using
        (LinearMap.adjoint_inner_left (A := P) (x := v) (y := Q v))
    have hzero : P (Q v) = 0 := by
      simpa [LinearMap.comp_apply] using congrArg (fun f => f v) h_comp_zero
    have hinner_zero : inner (Q v) (P v) = 0 := by
      have : inner (𝕜:=𝕜) (E:=V) (P (Q v)) v = 0 := by simp [hzero]
      simpa [h_adj] using this
    -- flip using conjugate symmetry
    simpa [hinner_zero] using inner_conj_symm (P v) (Q v)
  -- Decomposition v = P v + (I - P) v
  have hv : P v + Q v = v := by
    -- unfold Q and simplify
    change P v + (v - P v) = v
    simp
  calc
    ‖v‖^2 = ‖P v + Q v‖^2 := by simpa [hv]
    _ = ‖P v‖^2 + ‖Q v‖^2 :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h_orth
    _ := by simpa [Q]

end

end UEM
