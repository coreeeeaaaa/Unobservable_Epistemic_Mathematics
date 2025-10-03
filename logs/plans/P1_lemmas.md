| Lemma | Goal (Lean statement sketch) | Required Hypotheses | 예상 tactic / notes | 의존성 |
| --- | --- | --- | --- | --- |
| `residual_measurable` | `MeasurableSet (residual Π)` | `YeobaekProjectionHypotheses layer μ Π` | rewrite residual as complement, use measurability of image | Spec §3.2 |
| `residual_measure_positive` | `0 < μ (residual Π)` | same projection hypotheses + `μ (Π '' Set.univ) < μ Set.univ` | complement measure inequality, `lt_of_le_of_ne` | `residual_measurable` |
| `residual_nonempty` | `(residual Π).Nonempty` | combine measure positivity with `measure_ne_zero_iff` | non-trivial set deduced from positive measure | `residual_measure_positive` |
| `kernel_integral_lower` | `τ_min ≤ ∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ` | `YeobaekOverlapHypotheses μ K` with lower-bound field | apply PSD with constant function, integrate inequality | Spec §6.1 |
| `tau_margin_lower_bound` | `tau_margin μ Π A B ≥ c * ...` | measurability + inclusion hypotheses, kernel overlap fields | expand definition, use residual subset, combine PSD bound | depends on previous lemmas |
| `kernel_projection_margin_lower_bound` | main inequality capturing positive constant | all hypotheses above | pack constants, ensure positivity, algebraic manipulation | culmination |
