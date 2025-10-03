# UEM/YJG Canonical Axiomatics

This note restates the definitions and axioms from `docs/UEM_formal_spec_v2.md` in a compact table so that proof developments can reference a single source.

## Typed Universes
| Symbol | Description |
|--------|-------------|
| `Obj` | Finite-perimeter Borel subsets of the ambient metric–measure space `(X,d,μ)` |
| `Margin` | Pairs `(A,ε)` with `A∈Obj`, `ε>0` |
| `Obs` | Measurable maps `Obj→{true,false,⊥}` |
| `Dir` | Lipschitz vector fields with ‖·‖∞≤1 |
| `Flow` | Measure-preserving flows `(Φ_t)` |
| `Ker` | Positive symmetric kernels `K:X×X→ℝ_{≥0}` with compact support |

## Primitive Operators
- `seed():Obj`.
- `select(A,P):Obj×B(X)→Obj`.
- `lin`, `disc`, `cycle`, `margin`, `volume`, `zero`, `central`, `scale`, `curve`, `expand`, `eliminate`.
- Directional operator `dir_v` for each `v∈Dir`.
- Integrals `int_x`, `int_t`.
- `outerMargin`, `innerMargin`.

The Hangul interpreter `Γ(C,V,F)=final_F∘vowel_V∘consonant_C` uses these primitives exactly as listed.

## Overlap and Margins
- Kernel overlap: `A⊙_K B = A ∪ B ∪ {x:∫K(x,y)1_A(y)1_B(y)dμ>θ}`.
- Outer margin `M^{out}_ε(A)`, inner margin `M^{in}_ε(A)`.
- Thickness `τ(A,ε)=μ(M^{out}_ε(A)ackslash A)`.

## Axioms (abbreviated)
1. **A0 Non self-observation.** `O(A)=⊥ ⇒ O(seed())=⊥`.
2. **A1 Decomposition.** Each `A` decomposes into `B ∪ M^{in}_ε(A)` uniquely.
3. **A2′ σ-finite margins.** Existence of `(ε_n)` with finite boundary measure.
4. **A3 Overlap existence.** Every non-empty object overlaps with some object.
5. **A4 Boundary connectivity.** Connected interior ⇒ connected boundary.
6. **A5 Positive thickness.** Non-empty boundary ⇒ `τ(A,ε)>0`.
7. **A6 Observable preservation.** Observable projection commutes with structural operators.
8. **A7 Margin closure.** `M^{in}_ε(M^{in}_δ(A))⊆M^{in}_ε(A)`.
9. **A8 Type separation.** Mixed-type terms rejected.
10. **A9 Thickness monotonicity.** `A⊆B ⇒ τ(A,ε)≤τ(B,ε)`.
11. **A10 Projection exchange.** Directional operators commute up to Lipschitz error.
12. **A11 σ-closure.** `Obj` closed under countable syllable compositions with bounded kernels.
13. **B1 Hangul completeness.** `Γ` surjective onto the generated monoid.
14. **B2 Semantic preservation.** Double consonants correspond to overlap.
15. **C1 Margin topology.** `M^{out}_ε(A)` form a basis.
16. **D1 Recognition bound.** Observers recognise ≤6 syllables simultaneously.

Any future formalisation must use these exact statements; modifications require updating this file and the main spec together.

