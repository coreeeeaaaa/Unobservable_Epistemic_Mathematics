# UEM 0.1 — Sealed Pure‑Math Core

**Release tag:** `uem-0.1`  
**Date:** 2026-01-31

## Summary
This release seals the UEM‑0 pure‑math core. The following components are formally defined and checked in Lean4:

- **UEM‑0 fragment**: `UEM0OpTerm`, `eval`, `Derives` (equational + product fragment)
- **Semantics & models**: `Model`, `evalM`, `coreModel`
- **Soundness**: `soundness` (Derives ⇒ semantic equality)
- **Model existence**: `NontrivialModel`, `model_exists`
- **Additional results**:
  - Observed fragment as a full & faithful inclusion (`UEM_ObservedSubcategory`)
  - Cartesian product universal property in `ObjType` (`UEM_CartesianProduct`)
  - Hangul cardinality & direction (`UEM_HangulCardinality`, `UEM_HangulDirection`)

## Status
- All listed theorems are fully formalized and checked by Lean4 (lake build succeeded).
- No `sorry` or unproven axioms remain in the UEM‑0 core proofs.

## How to cite
Use the included `CITATION.cff`.

## Notes
- This release seals the formal core only. Any expository or non‑core discussion is kept outside the core and is not part of this release.
- Zenodo DOI: pending (add once minted).
