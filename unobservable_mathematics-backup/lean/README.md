# Lean 4 Environment Setup (Phase 2)

This folder hosts the Lean 4 project referenced by Phase 2 of `formalization/ROADMAP.md`. Completing the steps below satisfies the "Environment Setup" deliverable and prepares the workspace for the P1–P6 proof obligations.

## Prerequisites
- **elan** (Lean toolchain manager) ≥ 1.5.0
- **git** and **curl** (for dependency downloads)
- **lake** (ships with Lean 4; verified via `lake --version`)

## Installation Steps
1. Install Lean 4 via elan:
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```
   Accept the default toolchain when prompted.
2. Enter this directory and pull dependencies:
   ```bash
   cd unobservable_mathematics/formalization/lean
   elan toolchain install leanprover/lean4:4.8.0
   lake update
   ```
   This downloads `mathlib4` pinned at `v4.8.0` per `lakefile.lean`.
3. Build the scaffold project:
   ```bash
   lake build
   ```
   Successful compilation confirms the environment.
4. Run the CLI stub to check runtime linkage:
   ```bash
   lake exe uemCli
   ```
   Expected output: `UEM formalisation environment ready for boot.`
5. (Optional) Use the logging helper to capture the above steps:
   ```bash
   python3 ../tools/record_toolchain.py
   ```
   Results are appended to `unobservable_mathematics/reports/toolchain_log_YYYYMMDD.md`.
6. Open the Lean files in your editor (VS Code with the Lean extension or `lake env code .`) to begin the proofs.

## Project Layout
- `lean-toolchain` pins Lean to `leanprover/lean4:4.8.0` for deterministic builds.
- `lakefile.lean` registers the `mathlib4` dependency and declares the `UEM` Lean library/executable.
- `src/UEM/Prelude.lean` records initial definitions tied to `docs/UEM_formal_spec_v2.md`.
- `src/UEM/Structure.lean` captures the overlap monoid, projection homomorphism (A1, A3), the ambient pseudo-metric via mathlib's `PseudoMetricSpace`, and records object supports.
- `src/UEM/Measure.lean` encodes a σ-cover-based `MeasureContext` that links object measures to ambient supports and exposes an abstract error bound mirroring Axiom (A2′).
- `src/UEM/Projection.lean` implements Theorem 5.2 (`projectionOverlapExchange`) using the structure axioms.
- `src/UEM/Model.lean` wraps an `OverlapSystem` with spec metadata (Example 6.1) for future instantiation work.
- `src/UEM.lean` exposes shared definitions for downstream modules.
- `src/Main.lean` provides a minimal executable so the build can be sanity-checked.

## Next Steps
- Use `MeasureContext.measure_quasi_additive` (with `error_bound`) to derive quasi-additivity (A2′) once kernel estimates are formalised and bind the abstract measure to the ambient σ-cover.
- Record progress and file locations in `formalization/proof_plan.md`.
- Capture outstanding questions in `formalization/open_questions.md` once it is created per the roadmap guidance.

## Verification Checklist
- `lake update`, `lake build`, and `lake exe uemCli` must succeed on a clean checkout.
- `python3 ../tools/record_toolchain.py` may be used to automate logging of the above commands.
- `lake test` (or dedicated scripts) should be added once proof files exist.
- Update this README if the toolchain or dependency versions change.
