import Mathlib.Topology.MetricSpace.Lipschitz

namespace UEM

/-!
Persistence stability is captured as a Lipschitz condition on a diagram map.
Purely metric: no external interpretation.
-/

structure PHSystem (X Y : Type*) [PseudoMetricSpace X] [PseudoMetricSpace Y] where
  ph : X → Y
  lip : LipschitzWith 1 ph

theorem PHSystem.stability {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (S : PHSystem X Y) (x y : X) :
    dist (S.ph x) (S.ph y) ≤ dist x y := by
  simpa [NNReal.coe_one, one_mul] using (S.lip.dist_le_mul x y)

end UEM
