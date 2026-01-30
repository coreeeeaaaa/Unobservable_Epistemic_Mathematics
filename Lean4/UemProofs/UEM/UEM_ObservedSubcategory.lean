import UemProofs.UEM.UEM_Structure
import UemProofs.UEM.UEM_Calculus
import UemProofs.UEM.UEM_Conservativity
import Mathlib.CategoryTheory.Functor.FullyFaithful

namespace UEM

open CategoryTheory

/-!
Observed fragment as a full subcategory with a fully faithful inclusion functor.
This is a categorical statement about the observed types inside ObjType.
-/

instance : Category ObservedObjType where
  Hom a b := Operator a.1 b.1
  id a := ⟨fun x => x⟩
  comp f g := Operator.comp g f
  id_comp := by
    intro a b f
    ext x
    rfl
  comp_id := by
    intro a b f
    ext x
    rfl
  assoc := by
    intro a b c d f g h
    ext x
    rfl

def observedInclusion : ObservedObjType ⥤ ObjType where
  obj := fun a => a.1
  map := fun {a b} f => f
  map_id := by
    intro a
    rfl
  map_comp := by
    intro a b c f g
    rfl

instance : CategoryTheory.Functor.Faithful observedInclusion where
  map_injective := by
    intro a b f g h
    exact h

instance : CategoryTheory.Functor.Full observedInclusion where
  map_surjective := by
    intro a b f
    exact ⟨f, rfl⟩

end UEM
