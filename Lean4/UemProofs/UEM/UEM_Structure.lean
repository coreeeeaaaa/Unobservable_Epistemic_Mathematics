import Mathlib.CategoryTheory.Category.Basic
import UemProofs.UEM.UEM_Calculus

namespace UEM

/-!
# UEM Structure

This module records that UEM objects and operators form a (small) category.
It is a purely formal result derived from `Operator.comp` and identity.
-/

open CategoryTheory

instance : Category ObjType where
  Hom a b := Operator a b
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

end UEM
