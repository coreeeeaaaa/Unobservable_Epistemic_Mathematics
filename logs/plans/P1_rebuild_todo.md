# P1 복구 TODO (Lean 4.8 대응)

## 공통 준비
- **P1-Prep-01 환경 스냅샷 정리**
  - Action: `git status -sb`, `lean --version`, `cat lean/lean-toolchain` 결과를 `logs/proof_progress.md`에 P1 복구 세션으로 기록
  - Success Criteria: 로그에 명령어 출력 전체 포함, toolchain이 `leanprover/lean4:v4.8.*`로 명시
  - Measurement/Verification: `tail -n 20 logs/proof_progress.md`

- **P1-Prep-02 스펙 및 스냅샷 확보**
  - Action: `docs/excerpts/P1_spec.txt` 최신화 확인, `logs/snapshots/YeobaekOverlap_before_<date>.lean` 새 스냅샷 생성
  - Success Criteria: 스냅샷 ≥ 2KB, Spec에서 `τ_margin` 등장 (`rg "τ_margin"`)
  - Measurement/Verification: `ls -lh logs/snapshots/YeobaekOverlap_before_*.lean`, `wc -l docs/excerpts/P1_spec.txt`

## 구조 복원
- **P1-Struct-01 Projection 가정 구조 복원**
  - Action: `YeobaekProjectionHypotheses`를 Lean 4.8 문법으로 복원 (`Type`/`Prop` 정리, 주석 포함)
  - Success Criteria: `lake build` 통과, 관련 경고 없음
  - Measurement/Verification: `cd lean && lake build`, `rg "YeobaekProjectionHypotheses"`

- **P1-Struct-02 Kernel 가정 구조 복원**
  - Action: `YeobaekOverlapHypotheses`/`YeobaekKernelHypotheses` 필드·lemma 복구
  - Success Criteria: `kernel_integral_lower_bound` 등 핵심 lemma 컴파일
  - Measurement/Verification: `cd lean && lake build`, `rg "kernel_integral_lower_bound"`

## 핵심 lemma 재구성
- **P1-Core-01 Residual margin lemma 복원**
  - Action: `margin_residual_positive`, `margin_positive_measure`, `yeobaek_margin_exists` 증명 복귀
  - Success Criteria: 파일 내 `sorry` 없음, 경고 없음
  - Measurement/Verification: `cd lean && lake build`, `rg "yeobaek_margin_exists"`

- **P1-Core-02 Kernel-margin 부등식 복원**
  - Action: `kernel_projection_margin_lower_bound_residual` 및 일반형 부등식 복원
  - Success Criteria: ε/τ 최소값 추론 부분이 Lean 4.8에서 컴파일
  - Measurement/Verification: `cd lean && lake build`, `rg "kernel_projection_margin_lower_bound"`

- **P1-Core-03 결과 패키지 정비**
  - Action: `ProjectionKernelResult` 등 결과 구조체 재도입, Flow와 호환 확인
  - Success Criteria: 구조체 필드 초기화 시 오류 없음
  - Measurement/Verification: `cd lean && lake build`, `rg "ProjectionKernelResult"`

## Flow 연계
- **P1-Flow-Compat Flow 재연결**
  - Action: `Flow.lean`에서 P1 lemma 참조 부분을 새 시그니처에 맞게 수정
  - Success Criteria: Flow 모듈 컴파일 성공, margin lemma 참조 정상
  - Measurement/Verification: `cd lean && lake build`, `rg "residual Pi" lean/src/UEM/Flow.lean`

## 검증 & 문서화
- **P1-Verify-01 빌드/커버리지 실행**
  - Action: `cd lean && lake build`, `bash tools/proof_coverage.sh`
  - Success Criteria: 빌드 성공, `status=SORRY_FREE`, 로그 저장
  - Measurement/Verification: `logs/run/P1_coverage_*.log`, `proof_coverage.txt`, `sorry_count.txt`

- **P1-Docs-01 체크리스트/상태 갱신**
  - Action: `CHECKLIST.md`, `CHECKLIST_ATOMIC.md`, `STATUS.md`, `logs/proof_progress.md`를 새 상태로 업데이트
  - Success Criteria: 체크리스트 잠금 유지(`tools/checklist_lock.sh lock`), 로그에 각 태스크 기록
  - Measurement/Verification: `git diff` 관련 파일, `tools/checklist_lock.sh status`

- **P1-Docs-02 릴리즈/보고서 반영**
  - Action: `release/phases/P1/`, `reports/CC1/…` 필요 시 갱신
  - Success Criteria: 릴리즈 폴더 구조 보존, 새 검증 결과 첨부
  - Measurement/Verification: `ls release/phases/P1`, `git status`
