import UEM.Objects.Sparke
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

namespace UEM

variable {Val : Type _} [AddCommMonoid Val]

-- Consolidate all proofs into one instance, using the explicit `calc` style.
-- `nsmul` fields are `sorry`'d to isolate the problem.
instance : AddCommMonoid (Sparke Val) where
  add_assoc := by
    intros s1 s2 s3; ext
    · calc (s1 + s2 + s3).X = ((s1.X + s2.X) + s3.X) := by rfl; _ = (s1.X + (s2.X + s3.X)) := by rw [add_assoc]; _ = (s1 + (s2 + s3)).X := by rfl
    · calc (s1 + s2 + s3).T = ((s1.T ∪ s2.T) ∪ s3.T) := by rfl; _ = (s1.T ∪ (s2.T ∪ s3.T)) := by rw [Set.union_assoc]; _ = (s1 + (s2 + s3)).T := by rfl
    · rfl
  zero_add := by
    intros s; ext
    · calc (0 + s).X = 0 + s.X := by rfl; _ = s.X := by rw [zero_add]
    · calc (0 + s).T = ∅ ∪ s.T := by rfl; _ = s.T := by rw [Set.empty_union]
    · rfl
  add_zero := by
    intros s; ext
    · calc (s + 0).X = s.X + 0 := by rfl; _ = s.X := by rw [add_zero]
    · calc (s + 0).T = s.T ∪ ∅ := by rfl; _ = s.T := by rw [Set.union_empty]
    · rfl
  add_comm := by
    intros s1 s2; ext
    · calc (s1 + s2).X = s1.X + s2.X := by rfl; _ = s2.X + s1.X := by rw [add_comm]; _ = (s2 + s1).X := by rfl
    · calc (s1 + s2).T = s1.T ∪ s2.T := by rfl; _ = s2.T ∪ s1.T := by rw [Set.union_comm]; _ = (s2 + s1).T := by rfl
    · rfl
  nsmul := fun n s => sorry
  nsmul_zero := sorry
  nsmul_succ := sorry

end UEM
