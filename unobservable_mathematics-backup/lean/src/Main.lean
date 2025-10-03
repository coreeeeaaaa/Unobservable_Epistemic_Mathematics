import UEM.Prelude

open UEM

/-- Temporary CLI hook so `lake build` has a main entry point. -/
def main : IO Unit := do
  let sample := Observer.mk "boot" -- TODO: replace with data from spec once formalised.
  IO.println s!"UEM formalisation environment ready for {sample.id}."
