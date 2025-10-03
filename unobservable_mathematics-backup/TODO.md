# Consolidated TODO Checklist

## Phase 1 — Legacy Document Alignment
- [x] `analysis/UEM_core_axioms_spec_kr_v1.md`: rewrite definitions/axioms to reference `docs/UEM_formal_spec_v2.md`, add TODO for unmatched claims.
- [x] `analysis/UEM_operations_and_proofs_v1.md`: update operator descriptions, remove ad-hoc proofs, point to `docs/UEM_proof_sketches_v2.md`.
- [x] `analysis/UEM_case_studies_v1.md`: harmonise notation with v2 spec (optional but recommended).
- [x] `main.tex`: insert explicit reference to v2 spec; prune redundant signatures.
- [x] `UEM_preface.md`: reorganise philosophical discussion with citations to `docs/UEM_philosophy_mapping.md`.

## Phase 2 — Formal Proof Development
- [x] Lean/Isabelle environment setup under `formalization/` (Lean 4.8.0 + mathlib pinned; `lake build` verified 2025-09-18).
- [ ] Prove P1–P6 from `formalization/proof_plan.md` (P1 scaffolded via `src/UEM/Structure.lean`, `src/UEM/Projection.lean`, `src/UEM/Model.lean`; integrate kernel-based bounds to eliminate the abstract `error_bound` in `MeasureContext` and discharge Axiom A2′).

## Phase 3 — Testing & Verification
- [ ] Extend `tests/test_uem_spec.py` for additional syllable compositions and observer bound cases.
- [ ] Capture test/verification logs in `reports/`.

Mark tasks as they are completed.
