# UEM Project Team Structure

## Current Configuration (2025-09-20)

### Agent Assignments
1. **ClaudeCode-1**: P1 여백중첩 하한 부등식(커널 하위 연산 포함)
   - Files: lean/src/UEM/YeobaekOverlap.lean, lean/src/UEM/Projection.lean
   - Responsibilities: 여백중첩 상위 연산 정의, 커널 중첩 하위 연산, projection margin bounds, tau_margin function

2. **ClaudeCode-2**: P2 Flow preservation
   - Files: lean/src/UEM/Flow.lean
   - Responsibilities: Semigroup properties, measure preservation, dynamical systems

3. **ClaudeCode-3**: P4 Measure/σ-finite theory
   - Files: lean/src/UEM/Measure.lean, lean/src/UEM/AxiomA2.lean
   - Responsibilities: σ-finite covers, pushforward measures, finite mass theorems

4. **ClaudeCode-4**: Meta-coordination (M1, M3)
   - Files: meta/, design_docs/, rules/
   - Responsibilities: Inter-agent coordination, consistency checks, build gates

5. **ClaudeCode-5**: P6 Counterfactual stability
   - Files: lean/src/UEM/Counterfactual.lean
   - Responsibilities: ε-approximation, stability bounds, semicontinuity

### File Ownership Matrix
```
lean/src/UEM/Structure.lean    : Shared (read-only for CC2-5)
lean/src/UEM/YeobaekOverlap.lean : ClaudeCode-1 (exclusive)
lean/src/UEM/Projection.lean   : ClaudeCode-1 (exclusive)
lean/src/UEM/Flow.lean         : ClaudeCode-2 (exclusive)
lean/src/UEM/Measure.lean      : ClaudeCode-3 (exclusive)
lean/src/UEM/Counterfactual.lean : ClaudeCode-5 (exclusive)
lean/src/UEM/Tactics.lean     : Shared (simp rules only)
```

## Change History
- 2025-09-20: OpenCode (Grok) removed, ClaudeCode-5 added
- 2025-09-20: P1 implementation completed by ClaudeCode-1

## Conflict Resolution
- File locks prevent simultaneous editing
- Branch naming prevents merge conflicts
- .internal/GATES/ system tracks completion status
- Meta-coordination agent (CC-4) resolves disputes
