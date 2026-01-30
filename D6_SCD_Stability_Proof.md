## 정리 (Theorem)

**SCD Stability Step**:

Let $S$ be an `SCDSystem` and $x$ an invariant state.
Then one step of dynamics does not increase compression:

$$
\mathrm{compression}(\mathrm{next}(x)) \le \mathrm{compression}(x).
$$

**AHS Phase Inclusion**:
If $x$ is in the stable or unstable bundle, then $x$ lies in the phase space.

---

## 증명 (Proof)

All statements are structural laws carried by the `SCDSystem` and
`QuasiHyperbolicStructure` fields.

**Lean references**:
- `SCDSystem.stable_step'`
- `stable_in_phase`
- `unstable_in_phase`
