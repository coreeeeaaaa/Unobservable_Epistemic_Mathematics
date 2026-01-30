# UEM Canonical Mapping Table (Docs ↔ Lean)

Scope: /Users/a/dev/01-수학시스템
Sources of Truth (priority):
1) UEM_CONSTITUTION.md
2) UEM_Lean4_Proofs/UemProofs/UEM/*.lean
3) UEM_CANONICAL_SPEC.md
4) UEM_Lean4_Proofs/UEM_PROGRESS.md

---

## A) Constitution → Lean mapping

| Doc Item | Lean Symbol | File | Status | Notes |
|---|---|---|---|---|
| World := Type u | `World` abbrev | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Foundations.lean` | OK | `World : Type (w+1)` in code (universe level differs in name only). |
| Observer class (observe/kernel/kernel_spec) | `class Observer` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Foundations.lean` | OK | Fields match. |
| kernel equivalence theorem | `Observer.kernel_is_equivalence` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Foundations.lean` | OK | Present. |
| Thickness as OuterMeasure | `ThicknessBasis.outerMeasure`, `ThicknessBasis.thickness` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Foundations.lean` | OK | Formalized via Carathéodory. |
| Thickness axioms proved | `thickness_is_outer_measure` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Foundations.lean` | OK | Proof present. |
| Object types list | `ObjType` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | OK | Contains scalar/vector/tensor/spark/actyon/escalade/secare/world/observer/margin/... |
| Operator signatures | `CreateSpark`, `Ignite`, `Escalate`, `Commit` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | MISMATCH | Docs say `Collapse`, code defines `Commit`. |
| Hangul calculus (C/V/F) | `Syllable`, `CMap`, `VMap`, `FMap`, `OpTerm`, `syllableTerm` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | OK | Partial/totality properties are not fully proved. |
| Hangul matrix relation | `MatrixRel` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_HangulMatrix.lean` | OK | Soundness lemmas only. |
| Slot/Cube definitions | `Coord`, `Slot`, `Cube` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | OK | Cardinality theorems present. |
| Coordinate cardinality | `coord_card_3x3`, `coord_card_3x3x3` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | OK | Theorems present. |
| Category structure | `instance : Category ObjType` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Structure.lean` | OK | Proofs present. |

---

## B) Canonical Spec → Lean mapping

| Spec Item | Lean Symbol | File | Status | Notes |
|---|---|---|---|---|
| World / Observer / Kernel | `World`, `Observer`, `kernel_is_equivalence` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Foundations.lean` | OK | Matches. |
| Thickness OuterMeasure | `ThicknessBasis.outerMeasure`, `thickness_is_outer_measure` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Foundations.lean` | OK | Matches. |
| Objects as types | `ObjType` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | OK | Matches list. |
| Operator signatures | `CreateSpark`, `Ignite`, `Escalate`, `Commit` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | MISMATCH | Spec uses `Collapse`; code uses `Commit`. |
| Operator structure/comp/par | `Operator`, `Operator.comp`, `Operator.par` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | OK | Present. |
| Hangul calculus (C/V/F, OpTerm) | `CMap`, `VMap`, `FMap`, `OpTerm`, `syllableTerm` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | OK | Partiality/totality still needs proofs. |
| MatrixRel and classes | `MatrixRel` + class predicates | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_HangulMatrix.lean` | OK | Soundness only. |
| Slot/Cube definitions | `Coord`, `Slot`, `Cube` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean` | OK | Present. |
| Category structure claim | `instance : Category ObjType` | `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Structure.lean` | OK | Present. |

---

## C) Known mismatches / unresolved mappings
- Collapse vs Commit operator name mismatch between docs and code.
  - Evidence: `UEM_CONSTITUTION.md`, `UEM_CANONICAL_SPEC.md`,
    `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean`

