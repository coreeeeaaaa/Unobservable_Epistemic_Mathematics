## 정리 (Theorem)

**PHSystem Lipschitz Stability**:

Let $S$ be a `PHSystem` between pseudo‑metric spaces, with
$\mathrm{LipschitzWith}\;1$ map $S.ph$. Then for all $x,y$:

$$
\mathrm{dist}(S.ph\;x,\;S.ph\;y) \le \mathrm{dist}(x,y).
$$

---

## 증명 (Proof)

Directly from the `LipschitzWith` inequality.

**Lean reference**: `PHSystem.stability`.
