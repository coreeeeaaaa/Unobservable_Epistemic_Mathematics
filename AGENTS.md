# Repository Guidelines

## Project Structure & Module Organization
- `formal/`: Lean Lake root (`lakefile.lean`, `lean-toolchain`, `lake-manifest.json`). Core modules live under `formal/UEM/` (`Axioms`, `Basic`, `Objects`, `System`, `Theorems`) with the umbrella entry `formal/UEM.lean`.
- `docs/`: Specifications, design principles, paper draft, and examples; keep Lean definitions aligned with these texts.
- `2_ARCHITECTURE`, `4_OPERATIONS`, `lean/`, and the `여백중첩기하학/` notes folder: reference materials; do not assume they are build inputs.

## Build, Test, and Development Commands
- `cd formal && lake build`: Full project build; must succeed before merging.
- `cd formal && lake build UEM`: Rebuild the main library target when iterating; use narrower targets when available.
- `cd formal && rg "sorry" .`: Fail the review if any `sorry` remains.
- `cd formal && lake clean`: Remove build artifacts; run periodically to control disk usage (<15 GB total repo footprint).
- `du -sh .`: Check workspace size after large builds.

## Coding Style & Naming Conventions
- Lean style: types/structures/modules in `CamelCase`, definitions/lemmas/theorems in `snake_case`; prefer descriptive names (`null_projection_overlap`, `sparke_monoid_assoc`).
- Indent with spaces (Lean defaults), keep proofs readable with `by` blocks and explicit steps over heavy automation; open definitions and use `cases` + `simp/rw` when automation stalls.
- Imports: keep module headers minimal and sorted; avoid circular dependencies across `Axioms/Basic/Objects/System/Theorems`.
- No `sorry` or placeholder axioms; redesign statements if they do not admit proof.

## Testing Guidelines
- Proofs are tests: `lake build` must pass. When debugging, build the smallest affected module first, then the whole project.
- Add lemmas near their concepts; keep simp-normal forms stable and avoid fragile rewrite orders.
- Provide comments only where intent is non-obvious (e.g., explaining an induction measure or a nontrivial rewrite).

## Commit & Pull Request Guidelines
- Commits: small, focused, imperative mood (`Prove null projection overlap`, `Refine Sparke monoid laws`). Run `lake build` and `rg "sorry"` before committing.
- PRs/patches: include a brief problem statement, summary of changes, and verification steps (`lake build`, targeted builds). Link related specs in `docs/` if semantics change.
- Review diff before pushing; avoid wholesale file moves without necessity.

## Resource & Security Hygiene
- Keep caches trimmed (`lake clean`); avoid large binaries in the repo.
- Do not introduce new trusted axioms; stay within standard Lean math libraries and the project’s modules.
