# Unobservable Epistemic Mathematics (UEM) — Pure Mathematics Core

This repository contains the **pure mathematical core** of UEM:
formal definitions, theorems, and Lean4-checked proofs.
Non-mathematical materials (philosophical, literary, application/system notes)
are intentionally excluded.

## Contents
- `Lean4/` — Lean4 formalization (core definitions and proofs)
- `D1_*.md` ... `D10_*.md` — proof notes for core theorems
- `UEM_CONSTITUTION.md` — canonical constraints for the formal system
- `UEM_CANONICAL_SPEC.md` — canonical spec aligned with Lean code
- `UEM_CANONICAL_MAPPING_TABLE.md` — document ↔ code mapping
- `UEM_v12_Type_Specification.md` — type/operator specification (pure math)
- `UEM_Foundations_v12.tex` — LaTeX math-only document

## Build (Lean4)
```bash
cd Lean4
lake build
```

## Policy
Only pure mathematical content is published here. Any applications,
implementation details, or non-mathematical narrative are out of scope
for this repository.
