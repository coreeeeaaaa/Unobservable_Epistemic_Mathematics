import UemProofs.UEM.UEM_Calculus

namespace UEM

/-- A discrete-time flow on cubes. -/
structure Flow (side height depth : Nat) where
  step : Cube side height depth → Cube side height depth

/-- Iterate a flow for `n` steps. -/
def Flow.iter {side height depth : Nat} (f : Flow side height depth) (n : Nat) :
    Cube side height depth → Cube side height depth :=
  Nat.iterate f.step n

/-- A dynamics package: flow plus an invariant predicate. -/
structure Dynamics (side height depth : Nat) where
  flow : Flow side height depth
  invariant : Cube side height depth → Prop

/-- One-step evolution. -/
def Dynamics.next {side height depth : Nat} (d : Dynamics side height depth) :
    Cube side height depth → Cube side height depth :=
  d.flow.step

end UEM
