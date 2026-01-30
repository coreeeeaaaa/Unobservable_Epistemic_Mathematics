## 정리 (Theorem)

**Fractal Refinement Laws**:

Let $f$ be a `FractalCube`. Then refinement shifts the level index by 1:

$$
(\mathrm{refine}(f)).\mathrm{level}(n) = f.\mathrm{level}(n+1).
$$

For a cube $c$, `EscalateCube` is constant across levels, and is a fixed point
of refinement:

$$
(\mathrm{EscalateCube}(c)).\mathrm{level}(n) = c,\qquad
\mathrm{refine}(\mathrm{EscalateCube}(c)) = \mathrm{EscalateCube}(c).
$$

---

## 증명 (Proof)

All statements are definitional equalities.

**Lean references**:
- `FractalCube.refine_level`
- `EscalateCube_level_const`
- `EscalateCube_refine_fixed`
