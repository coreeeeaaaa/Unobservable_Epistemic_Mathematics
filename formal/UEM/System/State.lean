import UEM.Basic.Val
import UEM.Basic.Dimensions

namespace UEM

variable {V_phys : Type _} -- Physical Space (Vector/Tensor)

/-- Total State Space: X_phys × X_rec -/
structure State (V_phys : Type _) where
  phys : V_phys
  epistemic : X_rec
  margin : Unit -- Global Margin

end UEM
