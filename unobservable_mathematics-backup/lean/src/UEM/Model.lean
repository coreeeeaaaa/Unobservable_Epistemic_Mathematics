import UEM.Structure

/-!
Packaging of the abstract overlap system with metadata referencing
`docs/UEM_formal_spec_v2.md` Example 6.1. Serves as a placeholder for the
full metric–measure model on $(\mathbb{R}^3, \mathrm{Lebesgue})`.
-/
namespace UEM

structure ProjectionModel where
  system : OverlapSystem
  specReference : String := "Spec Example 6.1"

namespace ProjectionModel

@[simp] theorem projection_exchange
    (M : ProjectionModel) (A B : M.system.Obj) :
    M.system.projection (M.system.overlap A B) =
      M.system.phi (M.system.projection A) (M.system.projection B) :=
  M.system.projection_hom

end ProjectionModel

end UEM
