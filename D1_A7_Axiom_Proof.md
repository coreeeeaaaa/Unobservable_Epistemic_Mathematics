## 정리 (Theorem)

**Thickness Countable Subadditivity (A7)**:

Let $O$ be a type and let $	ext{basis} : \mathrm{ThicknessBasis}\; O$.
For any countable family of sets $s : \mathbb{N} 	o \mathcal{P}(O)$,

$$
	au\Big(igcup_{n} s(n)\Big) \le \sum_{n=0}^\infty 	au(s(n))
$$

where $	au = 	ext{basis.thickness}$.

---

## 증명 (Proof)

This is exactly the outer‑measure countable subadditivity derived from
Carathéodory's construction.

**Lean reference**: `UEM_Foundations.thickness_countable_subadditivity`.
