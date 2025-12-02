import UEM.Objects.Sparke
import Mathlib.Algebra.Group.Defs

namespace UEM

variable {Val : Type _} [AddCommMonoid Val]

instance : AddSemigroup (Sparke Val) := by
  apply AddSemigroup.mk
  intros a b c
  simp [Add.add, sparkeAdd]
  constructor
  . apply add_assoc
  . apply Set.union_assoc

instance : AddMonoid (Sparke Val) := by
  apply AddMonoid.mk
  . intros a
    simp [Add.add, sparkeAdd, Zero.zero, sparkeZero]
    constructor
    . apply zero_add
    . apply Set.empty_union
  . intros a
    simp [Add.add, sparkeAdd, Zero.zero, sparkeZero]
    constructor
    . apply add_zero
    . apply Set.union_empty

instance : AddCommMonoid (Sparke Val) := by
  apply AddCommMonoid.mk
  intros a b
  simp [Add.add, sparkeAdd]
  constructor
  . apply add_comm
  . apply Set.union_comm

end UEM
