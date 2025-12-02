import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

namespace UEM

structure Time := (dummy : Unit)
def Margin := Unit

/-- Sparke: The atomic unit of an event in UEM. -/
@[ext]
structure Sparke (Val : Type _) where
  X : Val
  T : Set Time
  margin : Margin

variable {Val : Type _} [AddCommMonoid Val]

/-- Sparke Addition (Merging) -/
@[simp]
def sparkeAdd (s1 s2 : Sparke Val) : Sparke Val :=
  { X := s1.X + s2.X,
    T := s1.T ∪ s2.T,
    margin := () }

/-- Zero Sparke (Identity) -/
@[simp]
def sparkeZero : Sparke Val :=
  { X := 0,
    T := ∅,
    margin := () }

instance : Add (Sparke Val) := ⟨sparkeAdd⟩
instance : Zero (Sparke Val) := ⟨sparkeZero⟩

end UEM
