import UEM.Basic.Val
import UEM.Basic.Dimensions

namespace UEM

variable {V_phys : Type _} -- Physical Space (Vector/Tensor)

/-- Epistemic Coordinate System (Simplified) -/
structure X_rec where
  d1_time : Int
  d2_ontic : Float
  d3_logic : Bool
  -- ... other dimensions abstracted

/-- Total State Space: X_phys × X_rec -/
structure State (V_phys : Type _) where
  phys : V_phys
  epistemic : X_rec
  margin : Unit -- Global Margin

end UEM
