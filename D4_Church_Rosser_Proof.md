## 정리 (Theorem)

**Deterministic Slot Evaluation and Type Preservation**:

Let `Slot.eval` be the evaluation function for a slot.
For any slot $s$:

1) **Determinism**:
   If $\mathrm{eval}(s)=\mathrm{some}\;o_1$ and $\mathrm{eval}(s)=\mathrm{some}\;o_2$,
   then $o_1 = o_2$.

2) **Type Preservation**:
   If $\mathrm{eval}(s)=\mathrm{some}\;o$, then either
   - $o.\mathrm{ty} = s.\mathrm{payload.ty}$, or
   - there exists a well‑typed syllable whose target type equals $o.\mathrm{ty}$.

---

## 증명 (Proof)

(1) follows from uniqueness of `Option.some`.
(2) follows by case analysis on the slot glyph and the syllable typing.

**Lean references**:
- `Slot.eval_deterministic`
- `Slot.eval_preserves_type`
