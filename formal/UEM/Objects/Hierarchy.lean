import UEM.Objects.Sparke
import UEM.Basic.Dimensions

namespace UEM

variable {Val : Type _}

/-- Actyon: Set of Sparkes with Agency -/
structure Actyon (Val : Type _) :=
  (sparkes : List (Sparke Val))
  (agent : String)
  (role : String)
  (weight : Float)
  (margin : Margin)

/-- Escalade: Dynamics and Flow -/
structure Escalade (S : Type _) :=
  (flow : S → S)
  (time_domain : Set Int)
  (margin : Margin)

/-- Secare: World and Boundary -/
structure Secare (S : Type _) :=
  (sub_world : Set S)
  (boundary : S → Prop)
  (margin : Margin)

end UEM
