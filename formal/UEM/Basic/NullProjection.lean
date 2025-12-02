namespace UEM

variable {V_keep V_null : Type _}

/-- Product 공간 V_prod = V_keep × V_null -/
abbrev V_prod (V_keep V_null : Type _) : Type _ :=
  V_keep × V_null

/-- Nullification Projection: Projects (vk, vn) to vk. -/
def Pi_null (v : V_prod V_keep V_null) : V_keep :=
  v.1

/-- Inclusion of Keep space, with 주어진 null 축 기본값 -/
def inc_keep (zero_null : V_null) (vk : V_keep) : V_prod V_keep V_null :=
  (vk, zero_null)

/-- Inclusion of Null space, with 주어진 keep 축 기본값 -/
def inc_null (zero_keep : V_keep) (vn : V_null) : V_prod V_keep V_null :=
  (zero_keep, vn)

/-- Null projection of keep inclusion is identity. -/
 @[simp] theorem Pi_null_inc_keep_id
    (zero_null : V_null) (vk : V_keep) :
  Pi_null (V_keep := V_keep) (V_null := V_null)
    (inc_keep (V_keep := V_keep) (V_null := V_null) zero_null vk)
  = vk := by
  rfl

/-- Null projection of null inclusion is 주어진 상수 zero_keep. -/
 @[simp] theorem Pi_null_inc_null_const
    (zero_keep : V_keep) (vn : V_null) :
  Pi_null (V_keep := V_keep) (V_null := V_null)
    (inc_null (V_keep := V_keep) (V_null := V_null) zero_keep vn)
  = zero_keep := by
  rfl

/-- Idempotence of Null Projection (lifted to V_prod -> V_prod).
    null 축 기본값을 인자로 받는다. -/
def Pi_null_lift (zero_null : V_null)
    (v : V_prod V_keep V_null) : V_prod V_keep V_null :=
  (Pi_null (V_keep := V_keep) (V_null := V_null) v, zero_null)

 @[simp] theorem Pi_null_lift_idempotent
    (zero_null : V_null) (v : V_prod V_keep V_null) :
  Pi_null_lift (V_keep := V_keep) (V_null := V_null) zero_null
    (Pi_null_lift (V_keep := V_keep) (V_null := V_null) zero_null v)
  =
  Pi_null_lift (V_keep := V_keep) (V_null := V_null) zero_null v := by
  rfl

end UEM
