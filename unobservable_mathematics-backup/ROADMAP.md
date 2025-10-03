# UEM/YJG Completion Roadmap
- **Generated:** 2025-09-17T12:15 (KST)
- **Purpose:** Detailed checklist and verification plan required for the UEM/YJG system to be recognised as a complete, rigorous mathematical framework.

## Phase 1 — Legacy Document Alignment (Status: ✅ Complete)
- Standardise all legacy descriptions to reference `docs/UEM_formal_spec_v2.md`.
- Ensure every document declares the v2 spec as authoritative and flags unresolved issues with TODO tags.

## Phase 2 — Formal Proof Development (Open)
1. **Environment Setup**
   - Install and configure Lean 4 or Isabelle under `formalization/`.
   - Record setup instructions (`formalization/lean/README.md` or `formalization/isabelle/README.md`).
   - Status (2025-09-17): Lean 4.8.0 project initialised under `formalization/lean` with mathlib v4.8.0; `lake update`, `lake build`, `lake exe uemCli` verified.
2. **Proof Obligations (P1–P6)**
   - P1: Projection–overlap exchange
   - P2: Margin persistence
   - P3: Syllable monoid completeness
   - P4: σ-finiteness of margins
   - P5: Observer bound
   - P6: Scenario composition stability
   - Status (2025-09-17): P1 scaffolded via `OverlapSystem` and `ProjectionModel` in `src/UEM/Structure.lean`, `src/UEM/Projection.lean`, `src/UEM/Model.lean`; remaining obligations pending.
   - For each: create proof file, document references back to the spec, mark status in `formalization/proof_plan.md`.
3. **Deliverables**
   - Machine-checked proofs in version control.
   - Summary of lemmas and how they map to the v2 spec.

## Phase 3 — Testing & Verification (Open)
1. **Test Expansion**
   - Extend `tests/test_uem_spec.py` to include counterfactual scenarios, complex syllable compositions, observer bound cases.
2. **Verification Logs**
   - Run all tests; log outputs in `reports/` (e.g., `reports/testlog_YYYYMMDD.md`).
   - Possibly add CI for automated testing.

## Phase 4 — Scholarly Documentation (Open)
1. Restructure `main.tex` into a formal paper referencing the new spec.
2. Write supplementary materials summarising definitions, proofs, and tests.
3. Prepare preprints or journal submissions; include appendices for proofs.

## Phase 5 — External Validation (Open)
1. Prepare presentations, seminar materials, curriculum notes.
2. Submit papers to journals; gather peer review.
3. Update documentation based on feedback.

## Verification Criteria Summary
- All definitions/proofs must reference the spec.
- Each result must have a certified proof or an explicit TODO.
- Regression tests must cover key scenarios; logs must be archived.

## Status Tracking
- Keep `formalization/TODO.md` updated.
- Use `formalization/OPERATIONS_MANUAL.md` for workflow guidance.
- Create `formalization/open_questions.md` for issues.

