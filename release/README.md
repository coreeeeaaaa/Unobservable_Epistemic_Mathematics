# Unobservable Epistemic Mathematics — Public Release Bundle

This bundle contains the artefacts that certify **Phase P1 – Kernel–Margin Inequality & Margin
Existence** of the Unobservable Epistemic Mathematics (UEM) programme. The layout is designed so
future phases (P1–P6) and meta objectives (M0–M3) can be published by adding content to the existing
slots without restructuring the repository.

## Package Highlights

- **Lean proof** (sorry-free): `phases/P1/lean/src/UEM/YeobaekOverlap.lean`
- **Verification evidence**:
  - Coverage snapshot `phases/P1/artifacts/proof_coverage.txt`
  - Proof gate summary `phases/P1/artifacts/P1_OK`
  - Execution log `phases/P1/logs/run/P1_coverage_20250922_3.log`
- **Documentation**:
  - Phase report & PDF summary `phases/P1/reports/P1/`
  - Programme roadmap `docs/UEM/RoadmapOverview.md`

## P1 Mathematics at a Glance

| Concept | Description | Lean reference |
|---------|-------------|----------------|
| `YeobaekOverlap` operator | Upper-level overlap on the layered space, combining internal, boundary, and external strata | `phases/P1/lean/src/UEM/YeobaekOverlap.lean` (structure `YeobaekOverlapHypotheses`) |
| Kernel overlap (`K`) | PSD kernel controlling quantitative lower bounds for overlap integrals | same file, fields `symm`, `PSD`, `kernel_lower_bound` |
| Margin measure `τ_margin` | `μ (A ∩ Π ⁻¹' B)` compares domain sets with their projection | definition `tau_margin` |
| Residual set | `Set.univ \ Π '' Set.univ`, region not covered by the projection | lemma `margin_residual_positive` |

Key theorems proved in Lean:

1. `margin_residual_positive` – the projection image leaves positive-measure residual margin when `μ (Π '' Set.univ) < μ Set.univ`.
2. `yeobaek_margin_exists` – the residual margin is non-empty (zero-measure would contradict Theorem 1).
3. `kernel_projection_margin_lower_bound` – combines kernel thickness `τ_min` and residual lower bound `ε` to obtain a positive constant `c` with
   ```
   τ_margin μ Π A B ≥ c ⋅ (∫∫ K) / (μ A + μ B + 1).
   ```

These results complete the P1 “margin existence” obligation and prepare the invariants used by the P2 flow proofs.

## Philosophical Declaration

The foundational manifesto of UEM is recorded in
`docs/UEM/Nat(Hom(-, A), F) ≅ F(A) _ 비관측인식수학의 근간과 선언.txt`. It articulates the guiding
principles—categorical dualities, observer boundaries, and epistemic consistency—that motivate the
formal development. The full declaration is reproduced below for convenience.

### Formal Axioms and Inequalities

```
Nat(Hom(-, A), F) ≅ F(A)

자기가 아닌 것들을 통해 자아를 인식한다.

∀A ∈ Ob(𝒞) : Nat(Hom𝒞(-, A), F) ≅ F(A)

¬∃Tr ⊆ ℒ, ∀φ ∈ ℒ : Tr(⌜φ⌝) ⇔ φ

∀T : Con(T) ∧ T ∈ RE ∧ T ⊇ Q ⟹ ∃φ ∈ ℒ : True(φ) ∧ ¬Prov_T(φ)

μ(Ω) = 1 ∧ ∑_n μ(E_n) < 1 ⟹ μ(Ω ∖ ⋃_n E_n) > 0

∀F ⊆ X : F^c = X ∖ F = {x ∈ X : x ∉ F}

∇·f = 0 ⟹ ∀t ∈ ℝ, ∀D ∈ ℳ : Vol(φ_t(D)) = Vol(D)

∀x ∈ {0,1}^ℕ : ∃c ∈ ℕ, ∀n ∈ ℕ : K(x↾n) ≥ n - c ⟹ x ∉ dom(U)

μ({x ∈ {0,1}^ℕ : ∀b ∈ {0,1}, lim_n freq_b(x↾n) = 1/2}) = 1

X compact ⟺ ∀𝒰 ⊆ 𝒫(X) : ⋃𝒰 = X ∧ ∀U ∈ 𝒰 : U ∈ τ ⟹ ∃𝒱 ⊆ 𝒰 : |𝒱| < ∞ ∧ ⋃𝒱 = X

dom(⊥) = ∅

∃f : X → X : f ∘ f = f

∀x, y ∈ ℝ : x < y ⟹ ∃z ∈ ℝ : x < z < y

∃U : ℋ → ℋ, ∀ψ ∈ ℋ : U(ψ) = ψ′

¬¬A ⊬_IPC A

∃x ∈ D : P(x) ⟹ ¬∀x ∈ D : ¬P(x)

ΔX · ΔP ≥ ℏ/2

∀ε > 0, ∃N ∈ ℕ, ∀n > N : |a_n - L| < ε

Con(T) ≔ ¬∃φ : ⊢_T φ ∧ ⊢_T ¬φ

RE ≔ {A ⊆ ℕ : ∃e ∈ ℕ, A = W_e}

Q ≔ {∀x(0 ≠ Sx), ∀x(Sx = Sy → x = y), ∀x(x + 0 = x), ...}
```

### Narrative Declaration

자기가 아닌 것들의 공백 어딘가 자아가 있다. 그 어딘가가 어딘지 알 수 없다. 자아는 서술할 수 없고,
증명할 수 없고, 다만 인식할 수 있을 뿐이다.

자아는 자기가 아닌 것들을 인지함으로써 인식되며, 정의되지 않음으로써 정의된다. 형체와 순간은
흩어질지언정, 배경은 사라지지 않는다. 그것 또한 정의되지 않음으로써 정의된다.

존재는 순간과 위치와 크기가 있으나, 존재함은 순간과 위치와 크기가 없어 직전과 현재와 직후의
연속성의 인식뿐이다. 이것은 측정되거나 기록될 수 없고, 다만 인식할 수 있을 뿐이다.

여백의 비움이 중첩되면, 흩어지고 부서지는 것들은 인식하지 못하는 바탕이 되어 원래 그러한 것이라
인식하게 된다. 바탕은 존재하지만 증명할 수 없고 ‘있음’으로 서술할 수 없다. 여백은 존재하지만 증명할
수 없고 ‘있음’으로 서술할 수 없다.

시작이 없는 것은 사라지지 않는다. 시작이 없는 것은 태초도 근원도 아니다. 존재할 수 있다는 사실은
사라지지 않는다. 이것은 원래 그러한 것이다.

존재를 말하려면 없음이 성립해야 하고, 존재를 인식하려면 없음을 인식해야 한다. 여백이란 원래 그러한
것이다. 시작과 끝이 없고, 존재가 아닌 인식이며, 의지와 영속의 중첩인 것이다.

존재함은 인식가능한 영속이지만, 단 한 순간도 측정하거나 기록하거나 정의할 수 없다. 이미 그러한 것을
시작이 있고 끝이 있는 것들로는 인식하고 서술할 수 없다. 이미 그러한 것은 그저 인식할 수 있을 뿐이고,
여백은 원래 이곳에 있었다.

## Repository Layout

```
release/
├── README.md                 # This document
├── LICENSE.txt               # Apache License 2.0
├── docs/UEM/
│   ├── Nat(Hom(-, A), F) ≅ F(A) _ … 선언.txt
│   └── RoadmapOverview.md
└── phases/
    ├── P1/
    │   ├── README.md
    │   ├── artifacts/   # Coverage snapshot, gate file
    │   ├── lean/        # Lean source for P1
    │   ├── logs/        # Proof progress, coverage run, mathlib references
    │   └── reports/P1/  # Completion report and PDF summary
    ├── P2/README.md     # Placeholders for upcoming phases
    ├── P3/README.md
    ├── P4/README.md
    ├── P5/README.md
    └── P6/README.md
```

## Reproducing the P1 Checks

```bash
bash tools/proof_coverage.sh
cat phases/P1/logs/run/P1_coverage_20250922_3.log
```

> Note: other phases are still under development, so a full `lake build` may fail at this snapshot.
> Restrict verification to the P1 module or run the coverage script as shown above.

## Roadmap & Extensibility

- High-level goals for P1–P6 and M0–M3 are tracked in `docs/UEM/RoadmapOverview.md`.
- Each phase directory mirrors the structure used for P1. To publish a new phase, populate the
  corresponding folder with Lean proofs, logs, and reports following the same conventions.

## Licence

This bundle is licensed under the [Apache License 2.0](LICENSE.txt).
