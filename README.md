# Unobservable Epistemic Mathematics

**Reproduce**: `git clone https://github.com/coreeeeaaaa/unobservable_mathematics.git && cd unobservable_mathematics && bash tools/reproduce.sh`

**Toolchain**: toolchain은 lean/lean-toolchain(leanprover/lean4:v4.8.0)을 사용

> ⚠️ **필수**: 작업 전 반드시 [`RULES.md`](RULES.md)를 읽고 지침을 준수하세요. 규칙 문서는 잠금 상태이며 삭제/수정 금지입니다.

**Status**: see `proof_coverage.txt`

## 여백중첩 연산자 계층

- **여백중첩 연산자 (Yeobaek Overlap Operator)**: 내부(잠재)·경계·외부 영역을 동시 추적하는 상위 개념. 사영 `Π`, 여백 잔여 `ㆁ`, 복소 두께 `\tilde{\tau}` 등 UEM 핵심 기호를 결합해 영역 간 중첩을 기술한다.
- **커널 중첩 연산자 (Kernel Overlap Operator)**: 여백중첩 연산자의 선형/적분형 하위 연산. PSD 커널 `K`와 test function을 이용해 여백중첩의 정량적 하한을 계산하며, Lean 구현에서는 `YeobaekOverlapHypotheses`로 캡슐화된다.
- **연결 규칙**: 모든 증명 문서와 체크리스트는 “여백중첩(상위) → 커널중첩(하위) → τ_margin 결과” 흐름을 따라야 하며, 용어 혼선을 방지하기 위해 해당 명칭을 일관되게 사용한다.
- **하한 가정**: P1 부등식을 마무리하려면 잔여 영역 하한(`ε`)과 커널 두께 하한(`τ_min`)이 필요하며, 현재 정리는 이 값을 외부 가정으로 받아들여 진행한다.
