| Condition | Description | Verification Method | Notes |
| --- | --- | --- | --- |
| Semigroup | `Φ_{s+t} = Φ_s ∘ Φ_t` with `Φ_0 = id` | algebraic rewriting in Lean (`flow_semigroup`) | Spec §3.4 (1), ensures time composition |
| Measurable flow | each map `Φ_t` measurable and has measurable inverse | use `MeasurePreserving` + `Measurable` fields | required for change-of-variables |
| Measure preserving | `μ (Φ_t^{-1}(A)) = μ(A)` for measurable `A` | `MeasurePreserving.measure_preimage` | derives margin invariance |
| Observable domain stability | flow stays inside observable set of layered space | TODO: express via future `YeobaekFlowHypotheses` | ensures compatibility with YeobaekLayeredSpace |
