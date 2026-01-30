import UemProofs.UEM.UEM_Foundations

namespace UEM

/-!
Core model existence. This file provides a concrete, non-empty model
for the foundational structures without adding axioms.
-/

/-! ## Canonical Observer -/

instance unitObserver : Observer Unit where
  ObsObject := Unit
  observe := fun x => x
  kernel := fun x y => x = y
  kernel_spec := by
    intro x y
    rfl

/-! ## Canonical Thickness Basis -/

def zeroThicknessBasis (O : Type u) : ThicknessBasis O where
  cost := fun _ => 0
  empty_cost := rfl

/-! ## Core Model Bundle -/

structure CoreModel where
  O : Type u
  obs : Observer O
  basis : ThicknessBasis O

def unitCoreModel : CoreModel :=
  { O := Unit
    obs := (inferInstance : Observer Unit)
    basis := zeroThicknessBasis Unit }

theorem coreModel_nonempty : Nonempty (CoreModel.{0, 0}) :=
  ⟨unitCoreModel⟩

end UEM
