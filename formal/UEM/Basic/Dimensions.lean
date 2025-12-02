namespace UEM

/-- 9 Epistemic Dimensions -/
inductive Dimension
| Time        -- d1: Physical/Epistemic Time
| Ontic       -- d2: Existence Strength [0,1]
| Logic       -- d3: Truth Value {T, F, U, C}
| Modality    -- d4: Possible Worlds {Box, Dia, Bot}
| Agency      -- d5: Agent * Role
| Epistemic   -- d6: Knowledge State {K, U, E, X}
| Value       -- d7: Utility * Norm
| Repr        -- d8: Theory * Language
| Limit       -- d9: Meta-limit (l, k, r)

/-- Coordinate Space for Dimensions (Abstract placeholder) -/
def Coord (d : Dimension) : Type :=
  match d with
  | .Time => Int -- Discrete time for now
  | .Ontic => Float -- [0,1] (Float for now, maybe Real later)
  | .Logic => Bool -- Simplified T/F
  | _ => Unit -- Placeholders for complex types

end UEM