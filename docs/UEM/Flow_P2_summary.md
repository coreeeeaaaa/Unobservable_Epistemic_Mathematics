# P2 Flow Preservation & Margin Persistence (Summary)

- Spec §3.4 assumptions:
  * Semigroup flow `Φ_{s+t} = Φ_s ∘ Φ_t`, `Φ_0 = id`.
  * Each `Φ_t` is measurable with measurable inverse `Φ_{-t}`.
  * Measure-preserving: `μ(Φ_t⁻¹(A)) = μ(A)` for analytical measure `μ`.
  * Flow acts on observable region (Yeobaek layer) and preserves observable set.
  * Generator is divergence-free (operationally encoded by measure-preserving axiom).

- Lean implementation:
  * `FlowSystem` encapsulates semigroup, inverse, measurability, measure preserving.
  * `YeobaekFlowHypotheses` specialises to the layered structure and states observable stability.
  * `FlowProjectionHypotheses` combines P1 projection assumptions with the flow system and records `residualSigmaFinite`.

- Main lemmas:
  * `margin_persistence`: `μ(Φ_t '' A) = μ(A)` for measurable `A`.
  * `residual_measure_invariant`: invariance on residual margin.
  * `residual_margin_positive`: residual measure remains positive under the flow.
  * `flow_measure_preserving`: measurable equivalence preserves `μ` for all `t`.
  * `flow_map_eq`: Jacobian = 1 formulation (`Measure.map (Φ_t) μ = μ`).
  * `slice_measurable`: Spec measurability exposed for automation.
  * `residual_sigmaFinite`: σ-finite residual margin assumption bundled with the hypotheses.
  * `margin_persistence_main`: P2 headline theorem `μ(Φ_t(M)) = μ(M)` for residual margin `M`.
