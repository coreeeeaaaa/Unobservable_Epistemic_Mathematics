## 정리 (Theorem)

**SCD Stability Theorem**:

Let $\tau: [0, \infty) \to \mathbb{R}$ be the **compression parameter** of a Stable Compressed Dynamics (SCD) structure.

Let $\tau_{target} > 0$ be the **target compression** parameter.

Let $e(t) := \tau(t) - \tau_{target}$ be the **tracking error**.

An **SCD feedback map** is:
$$\dot{\tau}(t) = u(e(t))$$

where $u: \mathbb{R} \to \mathbb{R}$ is the **feedback map**.

**Theorem**: There exists a feedback map $u$ and an initial condition $\tau_0$ such that:
$$\exists \tau: [0, \infty) \to \mathbb{R}, \tau(0) = \tau_0 \land \lim_{t \to \infty} e(t) = 0$$

---

## 증명 (Proof)

### **Step 1: Define Lyapunov Function**

A **Lyapunov function** $V: \mathbb{R} \to \mathbb{R}_{\geq 0}$ measures the magnitude of the error:
$$V(e) := \frac{1}{2} e^2$$

Properties:
1. $V(e) \geq 0$ (positive semidefinite)
2. $V(0) = 0$ (zero at equilibrium)
3. $V(e) \to \infty$ as $|e| \to \infty$ (radially unbounded)

### **Step 2: Specify Feedback Map (Proportional Form)**

Use **proportional feedback**:
$$u(e) := -k \cdot e$$

where $k > 0$ is the **gain parameter**.

The induced dynamics:
$$\dot{\tau} = u(e) = -k \cdot e = -k \cdot (\tau - \tau_{target})$$

### **Step 3: Analyze Induced Dynamics**

Define the error dynamics:
$$\dot{e} = \frac{d}{dt}(\tau - \tau_{target}) = \dot{\tau} = -k \cdot e$$

This is a **first-order linear ODE**:
$$\dot{e} + k e = 0$$

**Solution**:
$$e(t) = e(0) \cdot e^{-kt}$$

where $e(0) = \tau_0 - \tau_{target}$.

### **Step 4: Verify Lyapunov Stability**

Evaluate the **time derivative** of $V$:
$$\dot{V}(e) = \frac{d}{dt} \left( \frac{1}{2} e^2 \right) = e \cdot \dot{e}$$

Substitute the error dynamics:
$$= e \cdot (-k e) = -k e^2$$

Since $k > 0$ and $e^2 \geq 0$:
$$\dot{V}(e) = -k e^2 \leq 0$$

**Conclusion**: $\dot{V}(e) \leq 0$ for all $e$, so the structure is **stable** in the sense of Lyapunov.

### **Step 5: Apply LaSalle's Invariance Principle**

**LaSalle's Theorem** (1960):
If $\dot{V}(e) \leq 0$ and the only invariant set where $\dot{V}(e) = 0$ is $e = 0$, then:
$$\lim_{t \to \infty} e(t) = 0$$

**Verification**:
- $\dot{V}(e) = -k e^2 = 0$ iff $e = 0$
- The set $\{e = 0\}$ is invariant (if $e(0) = 0$, then $e(t) = 0$ for all $t$)

Therefore:
$$\lim_{t \to \infty} e(t) = 0$$

### **Step 6: Exponential Convergence**

From the solution $e(t) = e(0) e^{-kt}$:
$$|e(t)| = |e(0)| \cdot e^{-kt}$$

Taking the limit:
$$\lim_{t \to \infty} |e(t)| = \lim_{t \to \infty} |e(0)| \cdot e^{-kt} = 0$$

**Convergence rate**: Exponential with rate $k > 0$.

### **Step 7: Existence of Solution**

For any initial condition $\tau_0 \in \mathbb{R}$, define:
$$\tau(t) := \tau_{target} + (\tau_0 - \tau_{target}) e^{-kt}$$

**Verification**:
1. $\tau(0) = \tau_{target} + (\tau_0 - \tau_{target}) = \tau_0$ ✓
2. $\dot{\tau}(t) = -k (\tau_0 - \tau_{target}) e^{-kt} = -k (\tau(t) - \tau_{target}) = u(e(t))$ ✓
3. $\lim_{t \to \infty} \tau(t) = \tau_{target}$ (since $e^{-kt} \to 0$) ✓

### **Step 8: Formal Statement**

$$\boxed{\exists \tau: [0, \infty) \to \mathbb{R}, \tau(0) = \tau_0 \land \lim_{t \to \infty} (\tau(t) - \tau_{target}) = 0}$$

where $\tau(t) = \tau_{target} + (\tau_0 - \tau_{target}) e^{-kt}$ with $k > 0$.

∎

---



---
