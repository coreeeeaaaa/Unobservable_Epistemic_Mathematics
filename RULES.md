# Mandatory Agent Rules

> 모든 작업자는 아래 규칙을 수행하고 확인한 후에만 코드를 변경하거나 푸시할 수 있습니다.

## 1. 진입 절차
1. `tools/checklist_lock.sh unlock`으로 체크리스트 잠금을 임시 해제합니다 (필요한 경우에만).
2. `CHECKLIST.md`와 `CHECKLIST_ATOMIC.md`의 해당 단계 지침을 먼저 읽습니다.
3. 세션 시작 직후 `logs/proof_progress.md`에 날짜·정리 코드·목표를 기록합니다.

## 2. 필수 보호 장치
1. `.git/hooks/pre-commit`에 `tools/hooks/pre-commit-checklist-guard.sh`를 연결합니다.
   ```bash
   ln -sf ../../tools/hooks/pre-commit-checklist-guard.sh .git/hooks/pre-commit
   ```
2. 작업 후에는 항상 `tools/checklist_lock.sh lock`으로 체크리스트를 다시 잠급니다.
3. 체크리스트/규칙 문서를 삭제·이동·비우는 행동은 금지됩니다.

## 3. 작업 진행 규칙
1. 작업은 항상 `CHECKLIST_ATOMIC.md`에 명시된 순서와 Success/Measurement 기준을 따라야 합니다.
2. Task 완료 후 `logs/proof_progress.md`에 `YYYY-MM-DD 단계ID ✅ ...` 형식으로 기록합니다.
3. 증명 코드 변경 시 `lake build`와 필요 시 `tools/proof_coverage.sh`를 실행하고 로그에 결과를 남깁니다.
4. Spec 인용이 필요한 경우 `docs/excerpts/` 아래에 캡처 파일을 만들고 경로를 로그에 기록합니다.

## 4. 협업 수칙
1. 새로운 파일이나 스크립트를 추가하면 README 또는 관련 문서에 사용법을 명시합니다.
2. 미완 작업을 중단할 때는 로그에 `❌` 또는 `♻️`를 사용해 상태와 다음 조치를 남깁니다.
3. 커밋 전에는 `tools/checklist_lock.sh lock`이 적용되어 있는지, 체크리스트 항목이 올바르게 업데이트되었는지 확인합니다.

## 5. 금지 사항
- 보호 문서(`RULES.md`, `CHECKLIST.md`, `CHECKLIST_ATOMIC.md`)의 무단 수정, 삭제, 이동.
- 로그 없이 Task 상태를 변경하거나 체크 표시만 하는 행위.
- 증명 검증(`lake build` 등) 없이 코드를 제출하는 행위.

이 문서는 모든 에이전트가 준수해야 하는 최소한의 강제 규칙입니다. 위반시 작업을 중단하고 원상복구 조치를 진행해야 합니다.
