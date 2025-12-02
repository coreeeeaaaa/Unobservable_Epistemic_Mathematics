import UEM.Basic.DirectSum
import Mathlib.Algebra.Group.Defs

namespace UEM

variable {V_keep V_null : Type _}
variable [AddCommGroup V_keep] [AddCommGroup V_null]

def V := DirectSum V_keep V_null

/-- Nullification Projection: Projects (vk, vn) to vk. -/
def Pi_null : V → V_keep := fun v => v.1

/-- Inclusion of Keep space -/
def inc_keep : V_keep → V := fun vk => (vk, 0)

/-- Inclusion of Null space -/
def inc_null : V_null → V := fun vn => (0, vn)

theorem Pi_null_inc_keep_id (vk : V_keep) :
  Pi_null (inc_keep vk) = vk := by
  rfl

theorem Pi_null_inc_null_zero (vn : V_null) :
  Pi_null (inc_null vn) = 0 := by
  rfl

/-- Idempotence of Null Projection (lifted to V -> V) -/
def Pi_null_lift : V → V := fun v => (v.1, 0)

theorem Pi_null_lift_idempotent (v : V) :
  Pi_null_lift (Pi_null_lift v) = Pi_null_lift v := by
  rfl

end UEM
