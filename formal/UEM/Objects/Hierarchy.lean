import UEM.Objects.Sparke
import UEM.Basic.Dimensions

namespace UEM

variable {Val : Type _}

/-- Actyon: A set of Sparkes with agency and role. -/
structure Actyon (Val : Type _) where
  sparkes : List (Sparke Val)
  agent : String
  role : String
  weight : Float
  margin : Margin

/-- Escalade: Dynamics and Flow over time. -/
structure Escalade (S : Type _) where
  flow : S → S
  time_domain : Set Int
  margin : Margin

/-- Secare: A sub-world with boundaries. -/
structure Secare (S : Type _) where
  sub_world : Set S
  boundary : S → Prop
  margin : Margin

end UEM
