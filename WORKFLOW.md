# UEM Proof Workflow

이 문서는 Lean 증명 작업을 다시 시작할 때 따라야 할 절차를 요약합니다. 설계/기획 자료와 실제 증명 구현을 명확히 구분하고, 혼선을 방지하기 위한 체크리스트를 제공합니다.

## 0. 참고 문서 구분
- 설계·기획: `STATUS.md` 1번 섹션의 파일들
- 검증 필요 보고: `STATUS.md` 2번 섹션
- 실제 구현 대상: `STATUS.md` 3번 섹션 (P1–P6, M0–M3)

작업 전 `STATUS.md`를 확인하고, 설계 문서를 증명 완료로 간주하지 마세요.

## 1. 세션 시작 체크리스트
1. `git status`로 작업 트리 확인 (바뀐 파일 파악).
2. `elan`/`lake` 버전 확인: `cat lean-toolchain`, `cat lake-manifest.json` (수정 금지).
3. `bash tools/proof_coverage.sh` 실행 → 결과는 참고용, 핵심 정리는 직접 확인.
4. `STATUS.md`의 “Implementation Gap” 표에서 오늘 다룰 정리 선택.

## 2. 작업 진행 절차
1. 대응 Lean 파일 열기 (예: P1 → `lean/src/UEM/YeobaekOverlap.lean`).
2. 파일 상단에 Assumptions/Conclusion 블록이 명세와 일치하는지 확인, 없으면 추가.
3. 기존 자명한 정리를 `lemma`로 이동하거나 삭제 후 실제 목표 정리(`theorem …`) 선언.
4. 필요한 보조 정의·정리를 `UEM/` 네임스페이스 안에서 작성.
5. 증명은 가능한 mathlib 정리 의존 관계를 명시하고, 완성 후 `sorry`가 남지 않도록 확인.
6. 변경된 파일에서 `lake build` 실행 → 컴파일 성공 시 다음 단계로 이동.

## 3. 증명 완료 체크
- `lake build`
- `lake exe uem` (필요 시)
- `bash tools/proof_coverage.sh` 재실행 → 핵심 정리 증명 여부를 수동 확인.
- 증명 완료 시 `STATUS.md` 3번 섹션의 해당 항목 메모를 업데이트 (예: “P1: proved in commit …”).

## 4. 커밋 규칙
1. 메시지: `chore: proof P1 kernel inequality` 등 핵심 내용을 간결히 요약.
2. 커밋 전 `git diff --stat`로 변경 범위 확인.
3. 불필요한 설계 문서 수정이 포함되지 않았는지 검토.
4. `proof_coverage.txt`가 의미 있는 변경일 경우에만 커밋.

## 5. 세션 종료 전
- README/STATUS 갱신 여부 확인.
- `git status`로 깨끗한지 확인.
- 메모: 다음 작업 후보를 `STATUS.md` 또는 이슈 트래커에 기입.
- 필요 시 `git push`.

## 6. 주의사항
- 설계 문서(Section 1)는 **기획 참고용**: 증명 결과 보고에 사용하지 말 것.
- `proof_coverage.txt` 수치만 믿지 말고 실제 Lean 코드에서 목표 정리 유무를 직접 확인.
- M0–M3는 아직 Lean 파일조차 없으므로, 새 파일을 만들 때 `UEM/Meta/…` 구조를 지키고, 명세에 맞는 정리 이름을 선언.
- 커널, 측도, 반사실 등에 필요한 외부 정의는 mathlib 최신 문서를 참조해 정식 정의로 교체.

## 7. 릴리스 준비 (모든 정리 완료 시)
1. `STATUS.md`에서 모든 항목이 “proved”로 표시되는지 확인.
2. 교차 검증 결과를 `docs/verification.md`에 기록.
3. `tools/proof_coverage.sh` 출력이 실제 증명 수치와 일치하도록 확인.
4. 태그 릴리스 → 저장소 보호/아카이브 설정 검토.
