# UEM Canonical Mapping Table (Docs ↔ Lean)

Scope: `UEM-GitHub-Release` (public, pure math only)
Sources of Truth (priority):
1) `UEM_CONSTITUTION.md`
2) `Lean4/UemProofs/UEM/*.lean`
3) `UEM_CANONICAL_SPEC.md`

---

## A) Constitution → Lean mapping

| Doc Item | Lean Symbol | File | Status |
|---|---|---|---|
| World := Type u | `World` | `Lean4/UemProofs/UEM/UEM_Foundations.lean` | OK |
| Observer (observe/kernel/kernel_spec) | `class Observer` | `Lean4/UemProofs/UEM/UEM_Foundations.lean` | OK |
| kernel equivalence | `Observer.kernel_is_equivalence` | `Lean4/UemProofs/UEM/UEM_Foundations.lean` | OK |
| Thickness outer measure | `ThicknessBasis.outerMeasure`, `ThicknessBasis.thickness` | `Lean4/UemProofs/UEM/UEM_Foundations.lean` | OK |
| Thickness axioms | `thickness_is_outer_measure` | `Lean4/UemProofs/UEM/UEM_Foundations.lean` | OK |
| Object types list | `ObjType` + `Carrier` | `Lean4/UemProofs/UEM/UEM_Calculus.lean` | OK |
| Core operator signatures | `CreateSpark`, `Ignite`, `Escalate`, `Commit` | `Lean4/UemProofs/UEM/UEM_Calculus.lean` | OK |
| Hangul calculus (C/V/F) | `Syllable`, `CMap`, `VMap`, `FMap`, `OpTerm` | `Lean4/UemProofs/UEM/UEM_Calculus.lean` | OK |
| Hangul matrix relation | `MatrixRel` + soundness lemmas | `Lean4/UemProofs/UEM/UEM_HangulMatrix.lean` | OK |
| Slot/Cube + coord counts | `Coord`, `Slot`, `Cube`, `coord_card_*` | `Lean4/UemProofs/UEM/UEM_Calculus.lean` | OK |
| Category structure | `instance : Category ObjType` | `Lean4/UemProofs/UEM/UEM_Structure.lean` | OK |

---

## B) Proof Docs → Lean mapping

| Doc | Lean Theorem(s) | File |
|---|---|---|
| `D1_A7_Axiom_Proof.md` | `thickness_countable_subadditivity` | `Lean4/UemProofs/UEM/UEM_Foundations.lean` |
| `D2_Kernel_Margin_Inequality_Proof.md` | `thickness_margin_inequality` | `Lean4/UemProofs/UEM/UEM_Foundations.lean` |
| `D3_Projection_Exchange_Proof.md` | `projObj_idempotent`, `projSet_idempotent`, `projCoord_idempotent`, `DimReduction_idempotent`, `kernel_iff_alias` | `Lean4/UemProofs/UEM/UEM_Extensions/UEM_ProjectionGeometry.lean` |
| `D4_Church_Rosser_Proof.md` | `Slot.eval_deterministic`, `Slot.eval_preserves_type` | `Lean4/UemProofs/UEM/UEM_Calculus.lean` |
| `D5_Margin_Persistence_Proof.md` | `margin_union` | `Lean4/UemProofs/UEM/UEM_Foundations.lean` |
| `D6_SCD_Stability_Proof.md` | `SCDSystem.stable_step'`, `stable_in_phase`, `unstable_in_phase` | `Lean4/UemProofs/UEM/UEM_Extensions/UEM_SCD_AHS.lean` |
| `D8_Fractal_Convergence_Proof.md` | `FractalCube.refine_level`, `EscalateCube_level_const`, `EscalateCube_refine_fixed` | `Lean4/UemProofs/UEM/UEM_Extensions/UEM_Fractal.lean`, `UEM_Fractal_Theorems.lean` |
| `D10_PH_Stability_Proof.md` | `PHSystem.stability` | `Lean4/UemProofs/UEM/UEM_Extensions/UEM_PH_Stability.lean` |

---

## C) No unresolved mismatches

All public docs align with Lean symbols in this repository.
