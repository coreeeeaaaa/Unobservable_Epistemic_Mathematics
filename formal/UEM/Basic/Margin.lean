namespace UEM

/-- Margin log captures what was sent to "M": source/context plus payload and entropy. -/
structure MarginLog (α : Type _) where
  source   : String
  context  : String
  payload  : α
  weight   : Float := 1.0
  entropy  : Float := 0.0
deriving Repr

/-- Simple loss/entropy metric placeholder. -/
abbrev LossMetric := Float

/-- Record a projection event into the margin log. -/
def logProjection {α : Type _} (src ctx : String) (loss : LossMetric) (a : α) : MarginLog α :=
  { source := src, context := ctx, payload := a, weight := 1.0, entropy := loss }

end UEM
