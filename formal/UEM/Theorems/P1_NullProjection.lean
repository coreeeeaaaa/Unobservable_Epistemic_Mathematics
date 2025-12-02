import UEM.Basic.NullProjection
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

namespace UEM

variable {V_keep V_null W : Type _}
variable [AddCommGroup V_keep] [AddCommGroup V_null] [AddCommGroup W]

def V_full := V_keep × V_null

variable (A : V_full →+ W) (b : W)

/-- Condition: The null space V_null is in the kernel of A. -/
def nullInKernel : Prop :=
  ∀ vn : V_null, A (0, vn) = 0

/-- Theorem P1: Nullification Projection preserves the solution set. -/
theorem P1_null_projection_solutions
  (hnull : nullInKernel A) :
  { vk : V_keep | ∃ vn : V_null, A (vk, vn) = b } =
  { vk : V_keep | A (vk, 0) = b } := by
  ext vk
  constructor
  · intro h
    rcases h with ⟨vn, ha⟩
    -- A(vk, vn) = A(vk, 0) + A(0, vn)
    have split : A (vk, vn) = A (vk, 0) + A (0, vn) := by
      rw [← A.map_add]
      congr
      ext
      · simp
      · simp
    rw [split, hnull vn, add_zero] at ha
    exact ha
  · intro h
    use 0
    exact h

end UEM
