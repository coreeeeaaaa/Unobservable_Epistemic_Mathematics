# UEM Changelog

## v0.1.0 (2025-12-02)
- Lean 정리 검증: `P1_NullProjection`, `P2_SparkeMonoid`가 `lake build`로 통과.
- `Sparke`에 대한 `AddCommMonoid` 인스턴스에서 `sorry` 제거, `nsmul`을 표준 Nat 재귀로 정의.
- 증명 단순화: `ext`/`simp` 중심으로 가독성 향상.
- 권장 빌드: `cd formal && lake build` (Lean 4.26.0-rc2 toolchain).
