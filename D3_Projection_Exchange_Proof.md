## 정리 (Theorem)

**Projection/Reduction Idempotence and Kernel–Alias Equivalence**:

Let $P$ be a `ProjectionSystem`.
Then for all objects $a$ and sets $S$:

1) $P.\mathrm{projObj}(P.\mathrm{projObj}(a)) = P.\mathrm{projObj}(a)$.
2) $\mathrm{projSet}(P,\mathrm{projSet}(P,S)) = \mathrm{projSet}(P,S)$.
3) $P.\mathrm{projCoord}(P.\mathrm{projCoord}(c)) = P.\mathrm{projCoord}(c)$.

Let $D$ be a `DimReduction`. Then $D.\mathrm{reduce}(D.\mathrm{reduce}(n)) = D.\mathrm{reduce}(n)$.

Let $P$ be a `KernelizedProjection`. Then:

$$
\mathrm{kernel}(x,y) \iff \mathrm{proj}(x) = \mathrm{proj}(y).
$$

---

## 증명 (Proof)

All are structural laws (idempotence and kernel specification) carried
as fields in the corresponding structures.

**Lean references**:
- `projObj_idempotent`
- `projSet_idempotent`
- `projCoord_idempotent`
- `DimReduction_idempotent`
- `kernel_iff_alias`
