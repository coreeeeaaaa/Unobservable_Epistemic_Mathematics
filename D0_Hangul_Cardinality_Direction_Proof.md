## 정리 (Theorem)

**Hangul Syllable Cardinality and Direction Mapping**:

Let `Choseong`, `Jungseong`, `Jongseong`, and `Syllable` be the core
finite types defined in `UEM_Calculus`.

1) Cardinalities:
- `|Choseong| = 19`
- `|Jungseong| = 21`
- `|Jongseong| = 27`
- `|Syllable| = 19 * 21 * 28 = 11172`

2) Direction mapping:
There is a total function

`directionOfVowel : Jungseong → Direction`

and the syllable direction is defined by

`syllableDirection s = directionOfVowel s.v`.

---

## 증명 (Proof)

1) Cardinality is computed by a product equivalence:

`Syllable ≃ Choseong × Jungseong × Option Jongseong`

and by `Fintype.card_option`.

2) Direction mapping is a total function by definition; totality is immediate.

**Lean references**:
- `card_choseong`, `card_jungseong`, `card_jongseong`, `card_syllable`
  (`Lean4/UemProofs/UEM/UEM_HangulCardinality.lean`)
- `directionOfVowel_total`, `syllableDirection_def`
  (`Lean4/UemProofs/UEM/UEM_HangulDirection.lean`)
