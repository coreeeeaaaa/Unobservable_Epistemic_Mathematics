## 정리 (Theorem)

**Margin Decomposition (Set‑theoretic)**:

For sets $S, T \subseteq O$, define

- $\mathrm{marginSet}(S,T) := S \setminus T$
- $\mathrm{coreSet}(S,T) := S \cap T$

Then

$$
\mathrm{marginSet}(S,T) \cup \mathrm{coreSet}(S,T) = S.
$$

---

## 증명 (Proof)

Elementary set‑theoretic case split on membership in $S$ and $T$.

**Lean reference**: `UEM.Margin.margin_union`.
