# Formalisation Workspace

This directory collects all artefacts that must eventually witness the UEM/YJG system as a mathematically closed, machine-verifiable theory. It complements the informal historical material that still lives across the repository.

## Contents
- `axiomatics.md` — canonical list of symbols, domains, and axioms, extracted from `docs/UEM_formal_spec_v2.md` and kept in a compact form for reference while proving.
- `proof_plan.md` — roadmap for migrating the current proof sketches to machine-checked proofs (Lean/Isabelle) together with task ownership and open issues.
- `implementation_notes.md` — guidelines for aligning code/tests with the specification and for eliminating legacy inconsistencies.
- `lean/` — Lean 4.8.0 project scaffold with mathlib v4.8.0 pinned; see `lean/README.md` for setup and verification steps.
- `tools/` — automation helpers (e.g., `record_toolchain.py` for logging Lean toolchain runs).
- `open_questions.md` — rolling list of unresolved mathematical issues encountered during formalisation.

### Lean modules in scope
- `src/UEM/Structure.lean` — overlap algebra, support sets, pseudo-metric context, perimeter and $g$ function.
- `src/UEM/Measure.lean` — σ-cover measure context with quasi-additivity bound for Axiom (A2′).
- `src/UEM/AxiomA2.lean` — analytic interface for the error term $g(P(A),P(B))$ and the target thickness lemma.
- `src/UEM/Projection.lean` — projection/overlap exchange lemma (P1 skeleton).

As further results become certified, additional subfolders (e.g. `isabelle/`) may be added here.

## Usage
Work inside this folder when refining definitions, attaching formal proofs, or porting to proof assistants. Update `proof_plan.md` after each milestone so that we maintain a single source of truth regarding proof status.
