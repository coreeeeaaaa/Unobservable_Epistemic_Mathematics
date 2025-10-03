# UEM Formalization Roadmap Overview

## System Snapshot
- **Project scope**: Formalization of Unobservable Epistemic Mathematics (UEM) in Lean 4.
- **Core components**: layered projection spaces, kernel-based overlap operators, flow preservation,
  observer/measure constraints, and counterfactual stability.
- **Current proof state**: Phase P1 (kernel–margin inequality) completed with `sorry = 0`.

## Phase Goals (P1–P6)
| Phase | Focus | Target Lean modules | Current status |
|-------|-------|--------------------|----------------|
| P1 | Margin existence & kernel lower bounds | `lean/src/UEM/YeobaekOverlap.lean` | ✅ Proof complete (this release) |
| P2 | Flow preservation & margin persistence | `lean/src/UEM/Flow.lean` | ▢ Pending full proof (placeholders remain) |
| P3 | Hangul interpreter completeness | `lean/src/UEM/Interpreter.lean` | ▢ Parser lemmas present; bijection proofs outstanding |
| P4 | σ-finite margin measure | `lean/src/UEM/Measure.lean` | ▢ Context defined; finite-mass theorem not yet proved |
| P5 | Observer finiteness bounds | `lean/src/UEM/Observer.lean` | ▢ Image bounds partially implemented |
| P6 | Counterfactual stability | `lean/src/UEM/Counterfactual.lean` | ▢ Portmanteau estimates unfinished |

## Meta Objectives (M0–M3)
| Meta | Description | Planned deliverable |
|------|-------------|---------------------|
| M0 | Consistency transfer (Con(ZFC) ⇒ Con(UEM)) | New Lean module `UEM/Meta/Consistency.lean` |
| M1 | Conservativity over base logic | `UEM/Meta/Conservativity.lean` with model-theoretic argument |
| M2 | Translation round-trip between specs and Lean | `UEM/Meta/Translation.lean` with encode/decode proofs |
| M3 | Independence results via countermodels | `UEM/Meta/Independence.lean` |

All meta phases are roadmap items; implementation has not yet started in this repository snapshot.

## Relationship to P1
- P1 supplies the foundational margin gap used by P2 (flow preservation) and P4 (measure bounds).
- Later phases depend on the positive residual measure and quantitative kernel lower bounds proved in
  P1 to establish invariants under dynamics (P2) and observer constraints (P5).
- The current release focuses on solidifying P1 before extending automation to the remaining phases.

## Key References
1. `docs/UEM/UEM통합.txt` — master specification (Korean) defining phases and axioms.
2. `docs/UEM/Nat(Hom(-, A), F) ≅ F(A) _ 비관측인식수학의 근간과 선언.txt` — philosophical declaration of UEM.
3. `reports/CC1/2025-09-22-p1-formal-summary.md` — technical summary of the completed P1 proof.

## Next Steps
- Extend the Lean build to pass `lake build` for the entire project by eliminating outstanding
  placeholders in P2–P6.
- Begin formal development of the meta objectives (M0–M3) once phase proofs stabilize.
