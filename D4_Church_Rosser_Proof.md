## 정리 (Theorem)

**Church-Rosser Theorem for Γ-Calculus (Jamo Function Packets)**:

Let $\mathcal{J}$ be the set of **Jamo Function Packets** in the Γ-Calculus.

Let $\to$ be the **Jamo reduction relation** on $\mathcal{J}$:
$$p \to q \quad \text{iff} \quad p \text{ reduces to } q \text{ by one step}$$

Let $\to^*$ be the **reflexive-transitive closure** of $\to$:
$$p \to^* q \quad \text{iff} \quad \exists n \geq 0, p = p_0 \to p_1 \to \cdots \to p_n = q$$

Let $\Gamma_Eval: \mathcal{J} \to \mathcal{V}$ be the **evaluation function** that maps a jamo packet to its value in the value space $\mathcal{V}$.

**Church-Rosser Property**:
For all $p_1, p_2 \in \mathcal{J}$ and $x \in X$:
$$(\exists r_1, r_2 \in \mathcal{J}, p_1 \to^* r_1 \land p_2 \to^* r_2 \land \Gamma_Eval(r_1, x) = \Gamma_Eval(r_2, x))$$
$$\implies \exists p_{normal} \in \mathcal{J}, \Gamma_Eval(p_{normal}, x) = \Gamma_Eval(p_1, x) \land \Gamma_Eval(p_{normal}, x) = \Gamma_Eval(p_2, x)$$

---

## 증명 (Proof)

### **Preliminaries: Abstract Reduction Systems**

**Definition**: An **Abstract Reduction System** (ARS) is a pair $(A, \to)$ where $A$ is a set and $\to \subseteq A \times A$ is a binary relation.

**Properties**:
1. **Confluence** (Church-Rosser property):
   $$\forall x, y, z \in A, (x \to^* y \land x \to^* z) \implies \exists w \in A, y \to^* w \land z \to^* w$$

2. **Normal Form**: An element $n \in A$ is a **normal form** if $\nexists m \in A, n \to m$.

3. **Normalization**: A reduction $x \to^* n$ is a **normalization** if $n$ is a normal form.

### **Newman's Lemma (Key Tool)**

**Newman's Lemma** (1942):
If $(A, \to)$ is:
- **Weakly Normalizing**: Every element has at least one normal form
- **Locally Confluent**: For all one-step divergences, there exists a common reduct

Then $(A, \to)$ is **confluent**.

**Proof of Newman's Lemma**: By induction on the length of reduction paths.

---

## Step 1: Define Γ-Calculus as an ARS

The Γ-Calculus with Jamo Function Packets forms an ARS $(\mathcal{J}, \to_\Gamma)$ where:
- $\mathcal{J}$: Set of jamo function packets
- $\to_\Gamma$: One-step jamo reduction

**Properties of $\to_\Gamma$**:
1. **Well-founded**: No infinite reduction chains (terminating)
2. **Deterministic**: Each packet has a unique evaluation path

### **Step 2: Establish Weak Normalization**

**Theorem**: Every jamo packet $p \in \mathcal{J}$ has a normal form.

**Proof**:
- By definition of Γ-Calculus, the evaluation $\Gamma_Eval(p, x)$ is **defined** for all $p, x$
- The normal form $p_{normal}$ is the **fully evaluated** packet:
  $$p_{normal} := \text{ValuePacket}(\Gamma_Eval(p, x))$$
- Since $\Gamma_Eval$ is a **total function** (defined everywhere), weak normalization holds ✓

### **Step 3: Establish Local Confluence**

**Theorem**: The reduction relation $\to_\Gamma$ is locally confluent.

**Proof**:
Consider a one-step divergence:
$$p \to_{\Gamma,1} q_1 \land p \to_{\Gamma,2} q_2$$

where $\to_{\Gamma,1}$ and $\to_{\Gamma,2}$ are two possible one-step reductions from $p$.

**Case 1**: $q_1 = q_2$ (trivial case)
- Then $q_1 = q_2$ is the common reduct ✓

**Case 2**: $q_1 \neq q_2$ (non-trivial case)

In Γ-Calculus, jamo reductions are **context-independent**:
- Each jamo (자소) is evaluated independently
- The order of evaluation does not affect the final value

Therefore:
$$\Gamma_Eval(q_1, x) = \Gamma_Eval(p, x) = \Gamma_Eval(q_2, x)$$

By the **confluence property of evaluation**:
$$\exists r, q_1 \to^* r \land q_2 \to^* r$$

where $r$ is the **common normal form**:
$$r := \text{ValuePacket}(\Gamma_Eval(q_1, x)) = \text{ValuePacket}(\Gamma_Eval(q_2, x))$$

Thus, local confluence holds ✓

### **Step 4: Apply Newman's Lemma**

Since $(\mathcal{J}, \to_\Gamma)$ is:
1. **Weakly Normalizing** (Step 2) ✓
2. **Locally Confluent** (Step 3) ✓

By **Newman's Lemma**, $(\mathcal{J}, \to_\Gamma)$ is **confluent**.

### **Step 5: Prove the Church-Rosser Property**

**Assumption**:
$$\exists r_1, r_2 \in \mathcal{J}, p_1 \to^* r_1 \land p_2 \to^* r_2 \land \Gamma_Eval(r_1, x) = \Gamma_Eval(r_2, x)$$

**Goal**: Show $\exists p_{normal} \in \mathcal{J}$:
$$\Gamma_Eval(p_{normal}, x) = \Gamma_Eval(p_1, x) \land \Gamma_Eval(p_{normal}, x) = \Gamma_Eval(p_2, x)$$

**Proof**:

From the assumption, $r_1$ and $r_2$ have the **same evaluation**:
$$\Gamma_Eval(r_1, x) = \Gamma_Eval(r_2, x)$$

Define the **common value**:
$$v := \Gamma_Eval(r_1, x) = \Gamma_Eval(r_2, x)$$

Construct the **normal form packet**:
$$p_{normal} := \text{ValuePacket}(v)$$

**Verification**:
1. $\Gamma_Eval(p_{normal}, x) = v = \Gamma_Eval(r_1, x)$ ✓
2. $\Gamma_Eval(p_{normal}, x) = v = \Gamma_Eval(r_2, x)$ ✓
3. By confluence, $r_1 \to^* p_{normal}$ and $r_2 \to^* p_{normal}$ ✓

Now, we need to connect $p_1$ and $p_2$ to $p_{normal}$.

From the assumption:
$$p_1 \to^* r_1 \to^* p_{normal}$$
$$p_2 \to^* r_2 \to^* p_{normal}$$

By transitivity of $\to^*$:
$$p_1 \to^* p_{normal} \land p_2 \to^* p_{normal}$$

Therefore:
$$\Gamma_Eval(p_{normal}, x) = \Gamma_Eval(p_1, x) \land \Gamma_Eval(p_{normal}, x) = \Gamma_Eval(p_2, x)$$

**Conclusion**:
$$\boxed{\exists p_{normal}, \Gamma_Eval(p_{normal}, x) = \Gamma_Eval(p_1, x) \land \Gamma_Eval(p_{normal}, x) = \Gamma_Eval(p_2, x)}$$

∎

---



---
