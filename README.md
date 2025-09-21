# Unobservable Epistemic Mathematics — Public Release Bundle

This bundle contains the artefacts that certify **Phase P1 – Kernel–Margin Inequality & Margin
Existence** of the Unobservable Epistemic Mathematics (UEM) programme. The layout is designed so
future phases (P1–P6) and meta objectives (M0–M3) can be published by adding content to the existing
slots without restructuring the repository.

## Package Highlights

- **Lean proof** (sorry-free): `phases/P1/lean/src/UEM/YeobaekOverlap.lean`
- **Verification evidence**:
  - Coverage snapshot `phases/P1/artifacts/proof_coverage.txt`
  - Proof gate summary `phases/P1/artifacts/P1_OK`
  - Execution log `phases/P1/logs/run/P1_coverage_20250922_3.log`
- **Documentation**:
  - Phase report & PDF summary `phases/P1/reports/P1/`
  - Programme roadmap `docs/UEM/RoadmapOverview.md`

## Philosophical Declaration

The foundational manifesto of UEM is recorded in
`docs/UEM/Nat(Hom(-, A), F) ≅ F(A) _ 비관측인식수학의 근간과 선언.txt`. It articulates the guiding
principles—categorical dualities, observer boundaries, and epistemic consistency—that motivate the
formal development. Readers who want the conceptual background beyond the Lean artefacts should start
with this declaration.

## Repository Layout

```
release/
├── README.md                 # This document
├── LICENSE.txt               # Apache License 2.0
├── docs/UEM/
│   ├── Nat(Hom(-, A), F) ≅ F(A) _ … 선언.txt
│   └── RoadmapOverview.md
└── phases/
    ├── P1/
    │   ├── README.md
    │   ├── artifacts/   # Coverage snapshot, gate file
    │   ├── lean/        # Lean source for P1
    │   ├── logs/        # Proof progress, coverage run, mathlib references
    │   └── reports/P1/  # Completion report and PDF summary
    ├── P2/README.md     # Placeholders for upcoming phases
    ├── P3/README.md
    ├── P4/README.md
    ├── P5/README.md
    └── P6/README.md
```

## Reproducing the P1 Checks

```bash
bash tools/proof_coverage.sh
cat phases/P1/logs/run/P1_coverage_20250922_3.log
```

> Note: other phases are still under development, so a full `lake build` may fail at this snapshot.
> Restrict verification to the P1 module or run the coverage script as shown above.

## Roadmap & Extensibility

- High-level goals for P1–P6 and M0–M3 are tracked in `docs/UEM/RoadmapOverview.md`.
- Each phase directory mirrors the structure used for P1. To publish a new phase, populate the
  corresponding folder with Lean proofs, logs, and reports following the same conventions.

## Licence

This bundle is licensed under the [Apache License 2.0](LICENSE.txt).
