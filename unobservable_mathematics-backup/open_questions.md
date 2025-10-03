# Open Questions — Formalisation Track

These items collect outstanding issues encountered while porting the UEM/YJG
specification to Lean. Update this file whenever a blocking assumption or gap is
identified.

1. **Metric refinements (Spec §1.1).**
   - `OverlapSystem` now carries mathlib's `PseudoMetricSpace`, but the spec also
     references curvature/compactness assumptions. Determine which additional
     properties must be encoded to support Example 6.1.
   - Analyse whether the overlap kernel needs positivity/decay hypotheses beyond
     symmetry to mirror the analytic model.
2. **Measure semantics (Spec §2.3, A2′).**
   - `MeasureContext` supplies a σ-cover, support inclusions, 그리고 추상적인
     `error_bound`. 이제 kernel/geometry 기반 경계를 증명해 `error_bound` 가정을
     실제 불평등으로 대체해야 한다.
   - Derive σ-가산성 consequences from the cover and relate them to the object
     measure to unlock P4.
3. **Projection data (Spec §2.3, A3).**
   - The feature map $\Pi$ remains abstract; determine whether to model it as a
     tuple (`ℝ^n`) or a structured record (centroid, volume, inertia tensors).
4. **Flow operators (Spec §3.3, A6).**
   - No representation yet for semigroup actions; blocking P2 (margin persistence).
     Draft an API for `Flow` interacting with overlap and measure operations.
5. **Legacy document reconciliation.**
   - Audit historical proofs for compatibility with the new formal encoding and mark
     deprecated arguments explicitly once Lean counterparts exist.
