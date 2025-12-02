import UEM.Basic.Val
import UEM.Basic.Dimensions

namespace UEM

variable {V_phys : Type _} -- Physical Space (Vector/Tensor)

/-- Epistemic Coordinate System -/
structure X_rec :=
  (d1 : Int)          -- Time
  (d2 : Float)        -- Ontic
  (d3 : Bool)         -- Logic
  -- ... other dimensions simplified

/-- Total State Space: X_phys × X_rec -/
structure State (V_phys : Type _) :=
  (phys : V_phys)
  (rec : X_rec)
  (margin : Unit)     -- Global Margin

end UEM
