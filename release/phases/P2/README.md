# Phase P2 — Flow Preservation & Margin Persistence

## Lean Artifacts
- `lean/src/UEM/Flow.lean`
  - `FlowSystem`, `YeobaekFlowHypotheses`, `FlowProjectionHypotheses` 구조체
  - 핵심 정리: `flow_semigroup`, `flow_measure_preserving`, `residual_margin_persistence`,
    `margin_persistence_main`, `flow_map_eq` (Jacobian=1), `slice_measurable`
- 문서/로그: `docs/UEM/Flow_P2_summary.md`, `logs/proof_progress.md`

## 상태
- Skeleton 및 주요 정리 증명 완료 (Lean `sorry` 없음).
- `lake build`, `tools/proof_coverage.sh` 재실행 필요 — `Structure.lean` 타입클래스 정합성 문제 해결 후 진행 예정.
- `CHECKLIST.md`, `CHECKLIST_ATOMIC.md`의 P2-A~E 항목 최신화 완료 (P2-F 대기).

## TODO (릴리즈 전)
1. `Structure.lean` 빌드 오류 해결 후 전체 `lake build` 성공 기록.
2. `tools/proof_coverage.sh` 실행 로그(`logs/run/P2_coverage_*.log`) 업데이트.
3. `proof_coverage.txt`, `sorry_count.txt` 갱신 및 README 링크 추가.
4. 릴리즈 노트에 검증 로그/요약 첨부.

