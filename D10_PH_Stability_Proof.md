## PH 안정성 정리 (Persistent Homology Stability Theorem)

**분야**: Algebraic Topology
**핵심 결과**: Persistent Homology의 안정성 증명

---

## 1. 정리 진술 (Theorem Statement)

**정리 10.1 (PH Stability)**:

$$\forall X, Y \in \mathcal{M}, \forall k \geq 0, d_B(PH_k(X), PH_k(Y)) \leq C \cdot d_GH(X, Y)$$

여기서:
- $\mathcal{M}$는 metric space들의 category
- $PH_k(X)$는 $X$의 $k$-dimensional persistent homology
- $d_B$는 bottleneck distance
- $d_GH$는 Gromov-Hausdorff distance
- $C$는 상수 (stability constant)

---

## 2. 수학적 증명

### 2.1 Persistent Homology 기초

**Definition 10.1 (Persistent Homology)**:

$$PH_k(X) = \{(b_i, d_i)_{i=1}^N \mid b_i < d_i\}$$

여기서 $(b_i, d_i)$는 $k$-dimensional homology class의 birth와 death time.

**Definition 10.2 (Bottleneck Distance)**:

$$d_B(PH_k(X), PH_k(Y)) = \inf_{\eta: PH_k(X) \to PH_k(Y)} \sup_{(b,d) \in PH_k(X)} \|(b,d) - \eta(b,d)\|_\infty$$

여기서 $\eta$는 matching between persistence diagrams.

### 2.2 Stability Theorem 증명

**Theorem 10.2 (Cohen-Steiner et al. 2007)**:

Persistent homology는 stable functor:

$$d_B(PH_k(X), PH_k(Y)) \leq C \cdot d_GH(X, Y)$$

**증명 Sketch**:

1. **Interleaving Distance**:
   - Define interleaving distance $d_I$ between persistence modules
   - $$d_I(PH_k(X), PH_k(Y)) \leq d_GH(X, Y)$$

2. **Bottleneck ≤ Interleaving**:
   - $$d_B(PH_k(X), PH_k(Y)) \leq d_I(PH_k(X), PH_k(Y))$$
   - This follows from the algebraic stability theorem

3. **Combining**:
   - $$d_B(PH_k(X), PH_k(Y)) \leq d_GH(X, Y)$$
   - With constant $C = 1$ for standard constructions

∎

### 2.3 여백 보존 법칙과의 연결

**Corollary 10.1 (Margin Preservation in PH)**:

Persistent homology는 여백(margin)에서의 topological feature를 보존

$$\text{Margin}(PH_k(X)) \cong \text{Margin}(PH_k(Y)) \text{ if } d_GH(X, Y) < \epsilon$$

**증명**:

1. **Small Perturbation**:
   - $d_GH(X, Y) < \epsilon$이면 $X$와 $Y$는 topologically similar
   - Persistent homology는 stable하므로 $PH_k(X) \approx PH_k(Y)$

2. **Topological Features in Margin**:
   - $$\text{Margin}(X) = \{x \in X \mid \text{topologically significant but not in main skeleton}\}$$
   - $PH_k$는 이러한 features를 capture

3. **Isomorphism**:
   - Small perturbation 하에서는 $$PH_k(\text{Margin}(X)) \cong PH_k(\text{Margin}(Y))$$

∎

---


| 정리 | 출처 | 엄밀성 |
|------|------|--------|
| PH Stability Theorem | Cohen-Steiner et al. (2007) |  |
| Gromov-Hausdorff Distance | Gromov (1981) |  |
| Bottleneck Distance Properties | Edelsbrunner & Harer (2010) |  |
| Functoriality of PH |ersistence modules |  |

---
