# Implementation Alignment Notes

To keep the code/tests consistent with the formal specification, follow these guidelines:

1. **Reference specification**: Any new code must cite `docs/UEM_formal_spec_v2.md` and the symbols in `formalization/axiomatics.md` rather than legacy descriptions.
2. **Tests**: Expand `tests/test_uem_spec.py` or add new modules under `tests/` to cover:
   - Additional syllable compositions.
   - Observer bounds from axiom D1.
   - Error tolerances in projection exchange.
3. **Legacy clean-up**: When editing historical documents (e.g. `main.tex`, `analysis/*`), add a header noting that the formal v2 specification supersedes earlier informal claims and reconcile conflicting definitions.
4. **Proof integrations**: Once Lean/Isabelle artefacts exist, place them under `formalization/lean/` or `formalization/isabelle/` with a README explaining build instructions.

