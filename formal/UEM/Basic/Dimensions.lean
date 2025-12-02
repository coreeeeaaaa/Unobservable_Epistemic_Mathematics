namespace UEM

/-- 9 Epistemic Dimensions -/
inductive Dimension
| Time        -- d1
| Ontic       -- d2
| Logic       -- d3
| Modality    -- d4
| Agency      -- d5
| Epistemic   -- d6
| Value       -- d7
| Repr        -- d8
| Limit       -- d9

/-- Coordinate Space for Dimensions (Abstract) -/
def Coord (d : Dimension) : Type :=
  match d with
  | .Time => Int -- Discrete time for simplicity
  | .Ontic => Float -- [0,1]
  | .Logic => Bool -- Simple T/F
  | _ => Unit -- Others as abstract placeholders for now

end UEM
