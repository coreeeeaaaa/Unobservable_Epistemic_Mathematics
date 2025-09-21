# Phase P1: Kernel–Margin Inequality & Margin Existence

**Version**: 2025-09-22 07:15 KST  
**Location**: `phases/P1/lean/src/UEM/YeobaekOverlap.lean`  
**Status**: Formal proof completed in Lean 4 (`tools/proof_coverage.sh` → `status=SORRY_FREE`).

---

## 0. Abstract
Phase P1 of the UEM project formalizes the interaction between a layered projection system and a
positive-semidefinite kernel. The goal is to show that the residual margin between the domain and the
projection image is non-empty and carries a quantitative lower bound determined by the kernel
thickness hypothesis. All statements summarized below are implemented and verified in Lean without
`sorry` placeholders.

## 1. Mathematical Setting

### 1.1 Layered geometry
*Structure:* `YeobaekLayeredSpace` (`lean/src/UEM/Structure.lean:27`) packages three spaces:
- Internal space `Internal`: complex normed additive group; represents latent states.
- External space `External`: real normed additive group with measurable structure; represents
  observable configurations.
- Boundary space `Boundary`: topological space embedded into `External` for observable boundaries.

*Key components:*
- `embedInternal`, `embedBoundary`, `projectionCR` describe how each layer sits inside the external
  world.
- `observable` ⊆ `External` together with `observable_measurable` encodes the measurable region
  where observations take place.
- `measureExternal : Measure External` provides the base measure used in P1; the projection
  hypotheses require this to agree with the measure `μ` used downstream.

### 1.2 Kernel and projection hypotheses
*Kernel block:* `YeobaekOverlapHypotheses μ K` (`lean/src/UEM/YeobaekOverlap.lean:46`) assumes
- symmetry `K x y = K y x`;
- measurability of each section `K x` and `fun x ↦ K x y`;
- PSD condition: `∫∫ K x y · f x · f y ≥ 0` for all measurable `f : α → ℝ≥0∞`;
- finiteness of the left integrals, a uniform essential upper bound, and a global thickness lower
  bound `τ_min` such that `τ_min ≤ ∫ K x y dμ y`.

*Projection block:* `YeobaekProjectionHypotheses layer μ Π` (`lean/src/UEM/YeobaekOverlap.lean:70`)
requires
- `Π` is measurable with measurable image;
- the whole space has finite measure and the image measure is strictly smaller: `μ (Π '' Set.univ)
  < μ Set.univ`;
- `Π` agrees with the layered projection and fixes boundary embeddings;
- `layer.measureExternal = μ` to tie the structure to the ambient measure.

These hypotheses capture Spec §3.2/§6 (docs `docs/UEM/UEM통합.txt`).

## 2. Core Lean Theorems

| # | Lean identifier | Statement (informal) | Location |
|---|----------------|----------------------|----------|
| 1 | `margin_residual_positive` | The residual set `Set.univ \\ Π '' Set.univ` has strictly positive `μ`-measure. | `lean/src/UEM/YeobaekOverlap.lean:109` |
| 2 | `yeobaek_margin_exists` | The residual set is non-empty. | `lean/src/UEM/YeobaekOverlap.lean:152` |
| 3 | `kernel_projection_margin_lower_bound_core` | Given ε and τ_min positives, produce `c > 0` with the advertised inequality. | `lean/src/UEM/YeobaekOverlap.lean:170` |
| 4 | `kernel_projection_margin_lower_bound_residual` | Specialize the core lemma to the residual set. | `lean/src/UEM/YeobaekOverlap.lean:248` |
| 5 | `kernel_projection_margin_lower_bound` | General inequality: for measurable `A ⊇ residual` and `Π '' A ⊆ B`, we obtain `τ_margin ≥ c * (∫∫K)/(μA + μB + 1)`. | `lean/src/UEM/YeobaekOverlap.lean:273` |

### 2.1 Proof sketches
1. *Residual positivity*: apply `measure_add_measure_compl` to the measurable image and exploit the
   strict measure gap `image_lt_univ` to show the complement cannot have zero measure.
2. *Residual non-emptiness*: positive measure implies non-emptiness; negating leads to
   `μ (∅) = 0`, contradicting the previous step.
3. *Quantitative bound*: instantiate the PSD inequality with the residual characteristic function,
   combine the kernel lower bound and the ε margin lower bound obtained from the residual inclusion,
   and algebraically solve for `c`.

All details are encoded in Lean; no steps rely on informal reasoning beyond standard mathlib lemmas.

## 3. Implementation Notes
- `tau_margin μ Π A B` is defined as `μ (A ∩ Π ⁻¹' B)` and reused throughout the file with helper
  lemmas (`tau_margin_le_left`, `measure_preimage_inter`).
- The kernel lower bound assumption is lifted to the double integral via
  `kernel_integral_lower_bound_global`.
- Compatibility abbreviations (`abbrev KernelHypotheses := YeobaekOverlapHypotheses`) are retained to
  ease migration from earlier code.

## 4. Verification Pipeline
1. **Lean compilation**: `lake build` (note: other phases currently contain unfinished pieces; P1
   compiles and checks independently).
2. **Coverage audit**: `bash tools/proof_coverage.sh` → snapshot stored at
   `phases/P1/logs/run/P1_coverage_20250922_3.log`.
3. **Gate summary**: `phases/P1/artifacts/P1_OK` enumerates the key theorems together with the
   coverage evidence.

The latest run reports `defs=14`, `theorems=74`, `sorry=0`, hence status `SORRY_FREE`.

## 5. Reproduction Checklist
```bash
cd /path/to/unobservable_mathematics
# Optional: clean previous builds
rm -rf lean/.lake/build

# Build P1 (and other modules that compile)
cd lean
lake build UEM.YeobaekOverlap
cd ..

# Coverage
bash tools/proof_coverage.sh
cat phases/P1/logs/run/P1_coverage_20250922_3.log
```

For CI integration, restrict the Lake target to `UEM.YeobaekOverlap` (or a dedicated package) until
later phases are fully implemented.

## 6. Outstanding Assumptions & Future Work
- The strict image gap `μ (Π '' Set.univ) < μ Set.univ` comes from the spec but should be justified by
  constructing concrete layered spaces or by referencing upstream lemmas once available.
- `kernel_overlap_lower_aux` currently wraps `kernel_integral_lower_estimate`; a more direct link
  between PSD kernels and characteristic functions can strengthen the explanation.
- Integration with P2–P6 should export compatible hypotheses (e.g., flow invariants that guarantee
  the margin hypotheses remain valid over time).

## 7. References
1. `docs/UEM/UEM통합.txt`, Spec §3.2/§6 “P1. Projection–Kernel Inequality & Margin Existence”.
2. `docs/UEM/RoadmapOverview.md` — summary of phases P1–P6 and meta objectives M0–M3.
3. `docs/UEM/Nat(Hom(-, A), F) ≅ F(A) _ 비관측인식수학의 근간과 선언.txt` — philosophical basis of
   the UEM program.
4. `phases/P1/logs/mapping/P1_mathlib.md` — enumerates mathlib lemmas relied upon (measure
   monotonicity, `lintegral_lt_top_of_measure_lt_top`, etc.).
5. Lean source `phases/P1/lean/src/UEM/YeobaekOverlap.lean` — authoritative implementation of all
   proofs.

---

*Prepared for GitHub publication together with the Lean source, coverage logs, and gate file. No
internal checklists or proprietary materials are included in this report.*
