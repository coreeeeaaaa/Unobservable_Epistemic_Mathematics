## 정리 (Theorem)

**Margin Decomposition Inequality**:

Let $O$ be a type and $	ext{basis} : \mathrm{ThicknessBasis}\; O$.
For sets $S, T \subseteq O$, define:

- $\mathrm{marginSet}(S, T) := S \setminus T$
- $\mathrm{coreSet}(S, T) := S \cap T$

Then

$$
	au(S) \le 	au(\mathrm{marginSet}(S,T)) + 	au(\mathrm{coreSet}(S,T)).
$$

---

## 증명 (Proof)

Use the union inequality for outer measures on
$\mathrm{marginSet}(S,T) \cup \mathrm{coreSet}(S,T) = S$.

**Lean reference**: `UEM_Foundations.thickness_margin_inequality`.
