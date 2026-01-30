## 정리 (Theorem)

**Margin Continuity Equation**:

Let $(X, \mathcal{F}, \mu)$ be a measure space with $X$ a manifold.

Let $M(t) \subseteq X$ be the **margin region** evolving over time $t \in [0, \infty)$.

Let $\mu(M(t))$ be the **margin measure** (volume/size of margin).

Let $F_M: X \times [0, \infty) \to \mathbb{R}^n$ be the **flux vector field** describing measure flow into/out of the margin.

Let $S_M: X \times [0, \infty) \to \mathbb{R}$ be the **source term** describing creation/destruction of margin.

**Continuity Equation**:
$$\frac{\partial}{\partial t} \mu(M(t)) + \nabla \cdot F_M = S_M$$

where:
- $\frac{\partial}{\partial t} \mu(M(t))$: Time derivative of margin measure
- $\nabla \cdot F_M$: Divergence of flux (net outflow)
- $S_M$: Source/sink term

---

## 증명 (Proof)

### **Preliminaries: Reynolds Transport Theorem**

**Reynolds Transport Theorem** (1903):
Let $\Omega(t) \subseteq X$ be a time-varying region with smooth boundary $\partial \Omega(t)$.

Let $v(x, t)$ be the velocity field of the boundary.

Let $f: X \times [0, \infty) \to \mathbb{R}$ be an integrable function.

Then:
$$\frac{d}{dt} \int_{\Omega(t)} f(x, t) \, d\mu(x) = \int_{\Omega(t)} \frac{\partial f}{\partial t} \, d\mu(x) + \int_{\partial \Omega(t)} f \cdot (v \cdot n) \, d\sigma(x)$$

where:
- $n$: Outward unit normal vector to $\partial \Omega(t)$
- $\sigma$: Surface measure on $\partial \Omega(t)$

### **Step 1: Apply Reynolds Transport Theorem to Margin**

Take $f(x, t) = 1$ (constant function):
$$\frac{d}{dt} \mu(M(t)) = \frac{d}{dt} \int_{M(t)} 1 \, d\mu(x)$$

By Reynolds Transport Theorem:
$$= \int_{M(t)} \frac{\partial 1}{\partial t} \, d\mu(x) + \int_{\partial M(t)} 1 \cdot (v \cdot n) \, d\sigma(x)$$

$$= 0 + \int_{\partial M(t)} v \cdot n \, d\sigma(x)$$

Therefore:
$$\frac{\partial}{\partial t} \mu(M(t)) = \int_{\partial M(t)} v \cdot n \, d\sigma(x)$$

### **Step 2: Relate Boundary Velocity to Flux**

The **flux vector field** $F_M$ describes the flow of margin measure across the boundary:
$$F_M \cdot n = \text{Net flow of margin across boundary}$$

By definition of flux:
$$F_M \cdot n = v \cdot n$$

**Intuition**: The velocity of the boundary $v$ is directly related to the flux $F_M$:
- If measure flows **into** the margin, $F_M \cdot n < 0$ (inward normal)
- If measure flows **out of** the margin, $F_M \cdot n > 0$ (outward normal)

### **Step 3: Apply Divergence Theorem**

**Divergence Theorem** (Gauss-Ostrogradsky):
$$\int_{\partial M(t)} F_M \cdot n \, d\sigma(x) = \int_{M(t)} \nabla \cdot F_M \, d\mu(x)$$

where $\nabla \cdot F_M$ is the **divergence** of $F_M$:
$$\nabla \cdot F_M := \sum_{i=1}^n \frac{\partial F_{M,i}}{\partial x_i}$$

### **Step 4: Incorporate Source Term**

Let $S_M(x, t)$ be the **source density**:
- $S_M > 0$: Margin is being **created** at $(x, t)$
- $S_M < 0$: Margin is being **destroyed** at $(x, t)$

The total source is:
$$\int_{M(t)} S_M(x, t) \, d\mu(x)$$

### **Step 5: Conservation of Margin Measure**

The **change in margin measure** must equal:
- **Net inflow** across boundary (negative divergence)
- **Plus total source** (creation minus destruction)

Therefore:
$$\frac{\partial}{\partial t} \mu(M(t)) = -\int_{\partial M(t)} F_M \cdot n \, d\sigma(x) + \int_{M(t)} S_M \, d\mu(x)$$

**Sign convention**: Negative flux means margin is **growing** (measure flowing into margin).

### **Step 6: Apply Divergence Theorem**

$$\frac{\partial}{\partial t} \mu(M(t)) = -\int_{M(t)} \nabla \cdot F_M \, d\mu(x) + \int_{M(t)} S_M \, d\mu(x)$$

$$\frac{\partial}{\partial t} \mu(M(t)) = \int_{M(t)} (S_M - \nabla \cdot F_M) \, d\mu(x)$$

### **Step 7: Local Form of Continuity Equation**

Since this holds for **arbitrary** margin regions $M(t)$, the integrand must vanish:

$$\frac{\partial}{\partial t} \mu(M(t)) + \nabla \cdot F_M = S_M$$

**Interpretation**:
- **LHS**: Rate of change of margin + net outflow = total change
- **RHS**: Source/sink (creation/destruction)

### **Step 8: Weak Formulation (Distributional)**

For the margin measure $\mu(M(t))$ as a **distribution**:
$$\frac{\partial \mu_M}{\partial t} + \text{div}(F_M) = S_M$$

where:
- $\mu_M$: Measure concentrated on margin region
- $\text{div}(F_M)$: Distributional divergence of flux
- $S_M$: Distributional source term

**Weak form** (for test function $\phi \in C_c^\infty$):
$$\int_0^\infty \int_X \mu_M \frac{\partial \phi}{\partial t} \, dx \, dt - \int_0^\infty \int_X F_M \cdot \nabla \phi \, dx \, dt = \int_0^\infty \int_X S_M \phi \, dx \, dt$$

### **Step 9: Special Cases**

**Case 1: No Source ($S_M = 0$)**
$$\frac{\partial}{\partial t} \mu(M(t)) + \nabla \cdot F_M = 0$$

This is the **conservation form**: Margin measure is conserved, only transported.

**Case 2: Steady State ($\frac{\partial}{\partial t} \mu(M(t)) = 0$)**
$$\nabla \cdot F_M = S_M$$

Flux divergence balances source/sink.

**Case 3: Incompressible Flow ($\nabla \cdot F_M = 0$)**
$$\frac{\partial}{\partial t} \mu(M(t)) = S_M$$

Margin changes only due to source/sink, not flux.

### **Step 10: Final Form**

$$\boxed{\frac{\partial}{\partial t} \mu(M(t)) + \text{div}(F_M) = S_M}$$

∎

---



---
