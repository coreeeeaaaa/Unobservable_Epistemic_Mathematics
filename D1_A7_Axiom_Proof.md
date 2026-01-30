## 정리 (Theorem)

**Axiom A7 (Observation Failure)**:

Let $(X, \Sigma, \mu)$ be a measure space with $\mu(X) = 1$ (probability measure).

Let $\mathcal{O} = \{E_i\}_{i \in I}$ be a countable collection of **observable sets** with $E_i \in \Sigma$.

Define the **observable region** as:
$$\Omega_{obs} := \bigcup_{i \in I} E_i$$

Define the **non-observable region** as:
$$\Omega_{unobs} := X \setminus \Omega_{obs}$$

**Axiom A7 states**:
If $\sum_{i \in I} \mu(E_i) < 1$, then $\mu(\Omega_{unobs}) > 0$.

---

## 증명 (Proof)

### **Step 1: Establish the measure of observable region**

From countable subadditivity of measure $\mu$:

$$\mu(\Omega_{obs}) = \mu\left(\bigcup_{i \in I} E_i\right) \leq \sum_{i \in I} \mu(E_i)$$

**Proof of subadditivity**:
- By definition of measure, for disjoint sets: $\mu(A \cup B) = \mu(A) + \mu(B)$ when $A \cap B = \emptyset$
- For non-disjoint sets, we use the inclusion-exclusion principle
- For countable unions: $\mu(\bigcup_i E_i) \leq \sum_i \mu(E_i)$ (standard measure theory result)

### **Step 2: Apply the hypothesis**

Given: $\sum_{i \in I} \mu(E_i) < 1$

From Step 1:
$$\mu(\Omega_{obs}) \leq \sum_{i \in I} \mu(E_i) < 1$$

Therefore:
$$\mu(\Omega_{obs}) < 1$$

### **Step 3: Use probability measure property**

Since $\mu(X) = 1$ (probability measure):

$$\mu(X) = \mu(\Omega_{obs} \cup \Omega_{unobs}) = \mu(\Omega_{obs}) + \mu(\Omega_{unobs})$$

This holds because $\Omega_{obs} \cap \Omega_{unobs} = \emptyset$ (by definition of complement).

### **Step 4: Derive the non-observable measure**

$$1 = \mu(\Omega_{obs}) + \mu(\Omega_{unobs})$$

$$\mu(\Omega_{unobs}) = 1 - \mu(\Omega_{obs})$$

From Step 2, $\mu(\Omega_{obs}) < 1$, therefore:

$$\mu(\Omega_{unobs}) = 1 - \mu(\Omega_{obs}) > 0$$

### **Step 5: Conclusion**

$$\boxed{\mu(\Omega_{unobs}) > 0}$$

∎

---



---
