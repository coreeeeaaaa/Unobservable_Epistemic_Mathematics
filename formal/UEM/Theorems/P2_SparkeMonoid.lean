import UEM.Objects.Sparke
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

namespace UEM

variable {Val : Type _} [AddCommMonoid Val]

-- Trying a proof with `simp only` to be as explicit as possible
-- about the lemmas and definitions to use.
instance instSparkeAddSemigroup : AddSemigroup (Sparke Val) where
  add_assoc := by
    intros s1 s2 s3
    ext
    case X =>
      simp only [sparkeAdd, add_assoc]
    case T =>
      simp only [sparkeAdd, Set.union_assoc]
    case margin =>
      simp only [sparkeAdd]

end UEM
