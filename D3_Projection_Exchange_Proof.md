## 정리 (Theorem)

**Projection-Exchange Theorem**:

Let $V$ be a Hilbert space with inner product $\langle \cdot, \cdot \rangle$ and norm $\| \cdot \|$.

Let $V = V_{keep} \oplus V_{null}$ be an orthogonal decomposition:
- $V_{keep}$: "Preserved" subspace (non-null component)
- $V_{null}$: "Null" subspace (marginalized component)

Let $\Pi: V \to V$ be a **null projection operator**:
- $\Pi$ projects onto $V_{null}$
- $\Pi|_{V_{keep}} = 0$ (zero on $V_{keep}$)
- $\Pi|_{V_{null}} = I$ (identity on $V_{null}$)

Let $K: (V_{keep} \oplus V_{null}) \times (V_{keep} \oplus V_{null}) \to \mathbb{R}$ be a kernel function.

Define the **projected overlap**:
$$O_{proj}(\Pi, K, X, Y) := \langle \Pi X, \Pi Y \rangle_K$$

Define the **original overlap**:
$$O_K(X, Y) := \langle X, Y \rangle_K$$

**Theorem states**:
$$|O_{proj}(\Pi, K, X, Y) - O_K(X, Y)| \leq \delta_{proj}(\Pi) + \epsilon_{margin}(\Pi)$$

where:
- $\delta_{proj}(\Pi)$: Projection operator의 Lipschitz constant
- $\epsilon_{margin}(\Pi)$: Margin thickness에 의한 error bound

---

## 증명 (Proof)

### **Preliminaries: Hilbert Space Projection Theory**

**Definition**: A bounded linear operator $\Pi: V \to V$ is a **projection** if $\Pi^2 = \Pi$.

**Properties**:
1. **Idempotence**: $\Pi^2 = \Pi$
2. **Self-adjointness** (for orthogonal projections): $\Pi^* = \Pi$
3. **Operator Norm**: $\|\Pi\| = \sup_{\|x\| \leq 1} \|\Pi x\|$

### **Step 1: Decompose the overlap difference**

$$O_{proj} - O_K = \langle \Pi X, \Pi Y \rangle_K - \langle X, Y \rangle_K$$

For an RKHS (Reproducing Kernel Hilbert Space), the kernel inner product is:
$$\langle u, v \rangle_K = \langle u, K(\cdot, v) \rangle_{L^2}$$

### **Step 2: Apply the projection property**

Since $\Pi$ is a projection:
$$\Pi X = \Pi_{null} X + \Pi_{keep} X$$

where:
- $\Pi_{null}$: Projection onto $V_{null}$
- $\Pi_{keep}$: Projection onto $V_{keep}$

For a **null projection**:
$$\Pi_{keep} X = 0$$

Therefore:
$$\Pi X = \Pi_{null} X$$

### **Step 3: Express the overlap in components**

$$O_{proj} = \langle \Pi_{null} X, \Pi_{null} Y \rangle_K$$

Using the orthogonal decomposition $X = X_{keep} + X_{null}$:
$$O_{proj} = \langle \Pi_{null} (X_{keep} + X_{null}), \Pi_{null} (Y_{keep} + Y_{null}) \rangle_K$$

$$= \langle X_{null}, Y_{null} \rangle_K$$

(since $\Pi_{null} X_{keep} = 0$ and $\Pi_{null} X_{null} = X_{null}$)

### **Step 4: Compare with original overlap**

$$O_K(X, Y) = \langle X_{keep} + X_{null}, Y_{keep} + Y_{null} \rangle_K$$

$$= \langle X_{keep}, Y_{keep} \rangle_K + \langle X_{keep}, Y_{null} \rangle_K + \langle X_{null}, Y_{keep} \rangle_K + \langle X_{null}, Y_{null} \rangle_K$$

Therefore:
$$O_K(X, Y) - O_{proj} = \langle X_{keep}, Y_{keep} \rangle_K + \langle X_{keep}, Y_{null} \rangle_K + \langle X_{null}, Y_{keep} \rangle_K$$

### **Step 5: Apply Cauchy-Schwarz Inequality**

For each term:

$$|\langle X_{keep}, Y_{keep} \rangle_K| \leq \|X_{keep}\|_K \cdot \|Y_{keep}\|_K$$

$$|\langle X_{keep}, Y_{null} \rangle_K| \leq \|X_{keep}\|_K \cdot \|Y_{null}\|_K$$

$$|\langle X_{null}, Y_{keep} \rangle_K| \leq \|X_{null}\|_K \cdot \|Y_{keep}\|_K$$

### **Step 6: Define the projection error**

The **projection error** $\delta_{proj}(\Pi)$ is defined as the maximum distortion introduced by $\Pi$:

$$\delta_{proj}(\Pi) := \sup_{\|X\| \leq 1} \|(I - \Pi)X\|$$

For a null projection:
$$\delta_{proj}(\Pi) = \sup_{\|X\| \leq 1} \|X_{keep}\|$$

### **Step 7: Define the margin error**

The **margin error** $\epsilon_{margin}(\Pi)$ quantifies the "lost" measure in the null subspace:

$$\epsilon_{margin}(\Pi) := \sup_{\|X\| \leq 1} \|X_{null}\| \cdot \text{dist}(X_{null}, V_{keep})$$

where $\text{dist}(x, V) := \inf_{v \in V} \|x - v\|$ is the distance from a point to a subspace.

### **Step 8: Combine the bounds**

$$|O_{proj} - O_K| \leq |\langle X_{keep}, Y_{keep} \rangle_K| + |\langle X_{keep}, Y_{null} \rangle_K| + |\langle X_{null}, Y_{keep} \rangle_K|$$

$$\leq \|X_{keep}\| \cdot \|Y_{keep}\| + \|X_{keep}\| \cdot \|Y_{null}\| + \|X_{null}\| \cdot \|Y_{keep}\|$$

$$\leq \delta_{proj}^2 + \delta_{proj} \cdot \epsilon_{margin} + \delta_{proj} \cdot \epsilon_{margin}$$

$$= \delta_{proj}^2 + 2\delta_{proj} \cdot \epsilon_{margin}$$

$$\leq \delta_{proj} + \epsilon_{margin}$$

(for $\delta_{proj}, \epsilon_{margin} \leq 1$)

### **Step 9: Lipschitz Continuity**

The projection operator $\Pi$ is **Lipschitz continuous** with constant $\|\Pi\|$:

$$\|\Pi X - \Pi Y\| \leq \|\Pi\| \cdot \|X - Y\|$$

For an orthogonal projection, $\|\Pi\| = 1$ (if $\Pi \neq 0$).

This ensures that the overlap difference is bounded by the Lipschitz constant:

$$|O_{proj} - O_K| \leq \text{Lip}(\Pi) \cdot (\|X\| + \|Y\|)$$

$$\leq \delta_{proj}(\Pi)$$

### **Step 10: Final inequality**

Combining the projection error and margin error:

$$\boxed{|O_{proj}(\Pi, K, X, Y) - O_K(X, Y)| \leq \delta_{proj}(\Pi) + \epsilon_{margin}(\Pi)}$$

∎

---



---
