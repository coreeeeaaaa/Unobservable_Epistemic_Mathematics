import UEM.Objects.Sparke
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

namespace UEM

variable {Val : Type _} [AddCommMonoid Val]

@[simp] lemma sparke_add_X (s1 s2 : Sparke Val) : (s1 + s2).X = s1.X + s2.X := rfl
@[simp] lemma sparke_add_T (s1 s2 : Sparke Val) : (s1 + s2).T = s1.T ∪ s2.T := rfl
@[simp] lemma sparke_zero_X : (0 : Sparke Val).X = 0 := rfl
@[simp] lemma sparke_zero_T : (0 : Sparke Val).T = ∅ := rfl

-- `Sparke` inherits additive structure pointwise on `X` and unions on `T`.
-- `nsmul` is the usual natural multiplication via repeated addition.
instance : AddCommMonoid (Sparke Val) where
  add_assoc := by
    intro s1 s2 s3
    ext x
    · simp [sparke_add_X, add_assoc]
    · simp [sparke_add_T, Set.union_assoc]
    · rfl
  zero_add := by
    intro s
    ext x
    · simp [sparke_add_X, sparke_zero_X]
    · simp [sparke_add_T, sparke_zero_T]
    · rfl
  add_zero := by
    intro s
    ext x
    · simp [sparke_add_X, sparke_zero_X]
    · simp [sparke_add_T, sparke_zero_T]
    · rfl
  add_comm := by
    intro s1 s2
    ext x
    · simp [sparke_add_X, add_comm]
    · simp [sparke_add_T, Set.union_comm]
    · rfl
  nsmul := fun n s => Nat.recOn n (0 : Sparke Val) (fun _ acc => acc + s)
  nsmul_zero := by
    intro s; rfl
  nsmul_succ := by
    intro n s; rfl

end UEM
