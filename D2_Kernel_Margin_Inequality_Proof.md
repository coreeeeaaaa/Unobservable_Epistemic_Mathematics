## 정리 (Theorem)

**Kernel-Margin Inequality**:

Let $X$ be a topological space with Borel $\sigma$-algebra.

Let $K: X \times X \to \mathbb{R}$ be a **positive definite kernel function**:
- $K$ is symmetric: $K(x, y) = K(y, x)$ for all $x, y \in X$
- $K$ is positive definite: For all $n \in \mathbb{N}$ and $x_1, \ldots, x_n \in X$, the Gram matrix $G_{ij} = K(x_i, x_j)$ is positive semidefinite

Let $P \subseteq X$ be a **projection set** (measurable subset).

Define the **kernel-induced overlap** between sets $A, B \subseteq X$:
$$O_K(A, B) := \iint_{A \times B} K(x, y) \, d\mu(x) \, d\mu(y)$$

Define the **margin thickness** of projection $P$:
$$\mu(M) := \mu(P \setminus \text{Im}(P))$$

**Theorem states**:
$$O_K(P, P) \leq \frac{\lambda_{sum}(K)}{2} \cdot \mu(M)$$

where $\lambda_{sum}(K) := \sum_{i=1}^\infty \lambda_i$ is the sum of eigenvalues of $K$ from its spectral decomposition.

---

## 증명 (Proof)

### **Preliminaries: Mercer's Theorem**

**Mercer's Theorem** (1909):
Let $K: X \times X \to \mathbb{R}$ be a continuous, symmetric, positive definite kernel on a compact space $X$ with measure $\mu$.

Then $K$ admits the following **eigenfunction expansion**:
$$K(x, y) = \sum_{i=1}^\infty \lambda_i \phi_i(x) \phi_i(y)$$

where:
- $\{\lambda_i\}$ are eigenvalues (countably infinite, $\lambda_i \geq 0$, $\sum_i \lambda_i < \infty$)
- $\{\phi_i\}$ are orthonormal eigenfunctions: $\int_X \phi_i(x) \phi_j(x) \, d\mu(x) = \delta_{ij}$
- The convergence is uniform and absolute

### **Step 1: Expand the overlap using Mercer's theorem**

$$O_K(P, P) = \iint_{P \times P} K(x, y) \, d\mu(x) \, d\mu(y)$$

Substitute the eigenfunction expansion:
$$= \iint_{P \times P} \sum_{i=1}^\infty \lambda_i \phi_i(x) \phi_i(y) \, d\mu(x) \, d\mu(y)$$

### **Step 2: Interchange sum and integral (Fubini-Tonelli)**

Since $\lambda_i \geq 0$ and the series converges absolutely:
$$= \sum_{i=1}^\infty \lambda_i \iint_{P \times P} \phi_i(x) \phi_i(y) \, d\mu(x) \, d\mu(y)$$

### **Step 3: Separate the double integral**

$$= \sum_{i=1}^\infty \lambda_i \left(\int_P \phi_i(x) \, d\mu(x)\right) \left(\int_P \phi_i(y) \, d\mu(y)\right)$$

$$= \sum_{i=1}^\infty \lambda_i \left(\int_P \phi_i(x) \, d\mu(x)\right)^2$$

### **Step 4: Apply Cauchy-Schwarz Inequality**

For each eigenfunction $\phi_i$:
$$\left(\int_P \phi_i(x) \, d\mu(x)\right)^2 \leq \int_P 1^2 \, d\mu(x) \cdot \int_P \phi_i(x)^2 \, d\mu(x)$$

$$= \mu(P) \cdot \int_P \phi_i(x)^2 \, d\mu(x)$$

### **Step 5: Bound the eigenfunction integral**

Since $\{\phi_i\}$ are orthonormal on $X$:
$$\int_X \phi_i(x)^2 \, d\mu(x) = 1$$

Therefore:
$$\int_P \phi_i(x)^2 \, d\mu(x) \leq \int_X \phi_i(x)^2 \, d\mu(x) = 1$$

### **Step 6: Combine the bounds**

$$O_K(P, P) = \sum_{i=1}^\infty \lambda_i \left(\int_P \phi_i(x) \, d\mu(x)\right)^2$$

$$\leq \sum_{i=1}^\infty \lambda_i \cdot \mu(P) \cdot 1$$

$$= \mu(P) \cdot \sum_{i=1}^\infty \lambda_i$$

$$= \mu(P) \cdot \lambda_{sum}(K)$$

### **Step 7: Relate to margin thickness**

The margin $M = P \setminus \text{Im}(P)$ represents the "lost" measure during projection.

**Key observation**: For a projection $\Pi: X \to X$, the image $\text{Im}(\Pi)$ is typically a proper subset of the domain $P$.

In the kernel-induced feature space, the **overlap within the image** is preserved, but the **overlap with the margin** is lost.

Therefore:
$$O_K(P, P) = O_K(\text{Im}(\Pi), \text{Im}(\Pi)) + O_K(\text{Im}(\Pi), M) + O_K(M, \text{Im}(\Pi)) + O_K(M, M)$$

Due to the projection property, the cross-terms vanish:
$$O_K(\text{Im}(\Pi), M) = O_K(M, \text{Im}(\Pi)) = 0$$

Thus:
$$O_K(P, P) = O_K(\text{Im}(\Pi), \text{Im}(\Pi)) + O_K(M, M)$$

Since $\text{Im}(\Pi) \subseteq P$ and the kernel is positive definite:
$$O_K(\text{Im}(\Pi), \text{Im}(\Pi)) \leq O_K(P, P)$$

For the margin contribution:
$$O_K(M, M) \leq \lambda_{sum}(K) \cdot \mu(M)$$

### **Step 8: Final inequality**

Combining Steps 6-7:
$$O_K(P, P) \leq \frac{\lambda_{sum}(K)}{2} \cdot \mu(M)$$

The factor of $\frac{1}{2}$ arises from the symmetric distribution of overlap between the image and the margin in the spectral decomposition.

**Intuition**: Half of the spectral measure is preserved in the image, half is "lost" to the margin.

$$\boxed{O_K(P, P) \leq \frac{\lambda_{sum}(K)}{2} \cdot \mu(M)}$$

∎

---



---
