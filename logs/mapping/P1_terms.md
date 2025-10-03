| Spec Symbol | Description | Lean Identifier | Notes |
| --- | --- | --- | --- |
| `(α, μ)` | External measurable space hosting observable states | `α : Type`, `μ : Measure α` | Declared with `[MeasurableSpace α]` and used throughout P1 |
| `Π` | Observable projection operator | `Π : α → α` | Lives in `YeobaekProjectionHypotheses`; measurable with strict loss |
| `residual Π` | Residual margin `Dom \ Image` | `YeobaekFlowHypotheses.residual Π` (to be relocated to P1 namespace) | Main measurable set of interest |
| `K` | Kernel sub-operator | `K : α → α → ℝ≥0∞` | Fields supplied by `YeobaekOverlapHypotheses` (symmetry, PSD, bounds) |
| `τ_min` | Kernel integral lower bound | Part of `YeobaekOverlapHypotheses.kernel_lower_bound` | Ensures positive mass through PSD arguments |
| `tau_margin` | Margin measure functional | `tau_margin μ Π A B` | Defined in `YeobaekOverlap.lean`; measures overlap of `A` and `Π⁻¹' B` |
| `observable` | Observable region of the layered space | `layer.observable` in `YeobaekLayeredSpace` | Provides context for residual measurability |
| `M` | Residual margin witness | `residual Π` or explicit constant | Target for non-emptiness and positivity |
| `A`, `B` | Auxiliary measurable sets used in inequality | `A B : Set α` | Must satisfy measurability + finite measure hypotheses |
| `g` | Auxiliary control function | Not yet encoded (will be a field or assumption) | Provides perimeter bounds in the overlap inequality |
