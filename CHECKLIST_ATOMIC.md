# UEM Proof Checklist — Atomic Edition (with Success Metrics)

`CHECKLIST.md`가 제공하는 상위 흐름을 실제 작업 단위로 구현하기 위해 작성된 세부 실행 지침입니다. 각 Task는 **단일 실행으로 완료 가능한 최소 단위**이며, Action/Success/Measurement/Verification/Log 항목을 모두 충족해야 `[x]` 처리할 수 있습니다.

> **보호 설정**: 체크리스트 수정 전 `tools/checklist_lock.sh unlock`으로 잠금을 해제하고, 작업 후 `tools/checklist_lock.sh lock`으로 다시 잠그세요. `.git/hooks/pre-commit`에 `tools/hooks/pre-commit-checklist-guard.sh`를 연결해 두면 실수로 삭제할 때 커밋이 차단됩니다.

## 공통 규칙
1. Task를 시작하기 전에 `Action`과 `Success Criteria`를 완전히 이해합니다.
2. Task가 끝나면 `Measurement`와 `Verification` 절차를 실행하여 결과를 객관적으로 확인합니다.
3. 모든 Task는 `Log Note` 형식을 사용해 `logs/proof_progress.md` 등에 즉시 기록합니다. 예시: `2025-09-21 P1-A-01 ✅ docs/excerpts/P1_spec.txt 24 lines`.
4. 실패하거나 중단될 경우 `❌`, 수정·재실행은 `♻️` 등 이모지를 사용해 상태를 명확히 합니다.
5. Task 순서는 변경하지 않습니다. 선행 Task가 끝나지 않으면 다음 Task를 진행하지 마십시오.
6. 새 Task를 추가할 때는 아래 템플릿(Action/Success/Measurement/Verification/Log)을 반드시 따릅니다.

---

## P1 여백중첩 하한 부등식(커널 하위 연산 포함) — `lean/src/UEM/YeobaekOverlap.lean`

### A. 명세 및 준비
- `[x]` **P1-A-01 Spec 캡처**
  - Action: `docs/UEM/UEM통합.txt` §3.2를 `docs/excerpts/P1_spec.txt`로 저장
  - Success Criteria: 가정·결론·주요 수식이 모두 포함되어 있음
  - Measurement: `wc -l docs/excerpts/P1_spec.txt` 결과 ≥ 15, `rg "τ_margin"` 결과 ≥ 1
  - Verification: `wc -l docs/excerpts/P1_spec.txt` + `rg "τ_margin" docs/excerpts/P1_spec.txt`
  - Log Note: `YYYY-MM-DD P1-A-01 ✅ P1_spec.txt 24 lines`
- `[x]` **P1-A-02 코드 스냅샷**
  - Action: `cp lean/src/UEM/YeobaekOverlap.lean logs/snapshots/YeobaekOverlap_before_<date>.lean`
  - Success Criteria: 스냅샷 파일 존재, 크기 ≥ 1 KB
  - Measurement: `ls -lh logs/snapshots/YeobaekOverlap_before_<date>.lean`
  - Verification: `ls -lh logs/snapshots/YeobaekOverlap_before_*.lean`
  - Log Note: `YYYY-MM-DD P1-A-02 ✅ snapshot saved`
- `[x]` **P1-A-03 용어 매핑표 작성**
  - Action: Spec 기호 ↔ Lean 변수 대응표를 `logs/mapping/P1_terms.md`에 Markdown 표로 작성(열: Spec symbol / 의미 / Lean identifier / 참고)
  - Success Criteria: 행 ≥ 8, 각 행에 Lean 식별자 명시
  - Measurement: `rg "|" logs/mapping/P1_terms.md | wc -l`
  - Verification: `cat logs/mapping/P1_terms.md`
  - Log Note: `YYYY-MM-DD P1-A-03 ✅ 10 term mappings`

### B. 구조 정의 & 주석 보강
- `[ ]` **P1-B-01 `YeobaekOverlapHypotheses` 필드 확정**
  - Action: 여백중첩 상위 가정에 맞춰 구조체 필드 추가·정리(`KernelHypotheses` 별칭 유지)
  - Success Criteria: `lake build` 통과, 구조체 위 주석에 모든 가정 요약
  - Measurement: `lake build` exit code 0, 주석에 항목 ≥ 4
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P1-B-01 ✅ lake build OK`
- `[ ]` **P1-B-02 Assumptions/Goal 주석화**
  - Action: 파일 상단에 Assumptions/Goal 블록 추가(여백중첩 상위 연산과 커널 하위 연산 구분 포함, 각 bullet에 Spec 인용)
  - Success Criteria: Assumptions ≥ 3, Goal 1개 이상 명시
  - Measurement: `git diff lean/src/UEM/YeobaekOverlap.lean`
  - Verification: `git diff lean/src/UEM/YeobaekOverlap.lean`
  - Log Note: `YYYY-MM-DD P1-B-02 ✅ assumptions annotated`
- `[ ]` **P1-B-03 PSD 레퍼런스 기록**
  - Action: mathlib PSD 관련 lemma ≥ 3개 조사 후 `logs/mapping/P1_mathlib.md`에 기록(lemma 이름/네임스페이스/요약)
  - Success Criteria: 행 ≥ 3, 각 행에 mathlib 링크 또는 경로 포함
  - Measurement: `rg "|" logs/mapping/P1_mathlib.md`
  - Verification: `cat logs/mapping/P1_mathlib.md`
  - Log Note: `YYYY-MM-DD P1-B-03 ✅ recorded PSD lemmas`

### C. 보조 lemma 준비
- `[x]` **P1-C-01 lemma 목록 작성**
  - Action: 필요한 lemma ≥ 5개를 `logs/plans/P1_lemmas.md`에 표로 작성(열: lemma 이름 / 목표 / 필요 가정 / 예상 tactic / 의존성)
  - Success Criteria: 행 ≥ 5, `예상 tactic` 열 채움
  - Measurement: `rg "|" logs/plans/P1_lemmas.md`
  - Verification: `cat logs/plans/P1_lemmas.md`
  - Log Note: `YYYY-MM-DD P1-C-01 ✅ 6 lemmas planned`
- `[ ]` **P1-C-02 lemma skeleton 삽입**
  - Action: 여백중첩 모듈에 각 lemma 선언 + `by` 아래 TODO 주석 삽입(상위/하위 연산 구분 주석 포함)
  - Success Criteria: 구문 오류 없음, TODO에 증명 방향 최소 1줄 기재
  - Measurement: `lake build`
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P1-C-02 ✅ skeleton inserted`
- `[ ]` **P1-C-03 tactic 계획 메모**
  - Action: `logs/plans/P1_lemmas.md`의 `예상 tactic` 열을 구체화(예: `lintegral`, `calc`, `by_cases` 등)
  - Success Criteria: 모든 lemma에 tactic 명시, 필요 보조 lemma 이름 언급
  - Measurement: `rg "calc" logs/plans/P1_lemmas.md` 등 내용 확인
  - Verification: `cat logs/plans/P1_lemmas.md`
  - Log Note: `YYYY-MM-DD P1-C-03 ✅ tactics planned`

### D. lemma 증명
- `[ ]` **P1-D-01 lemma#1 증명**
  - Action: 첫 번째 lemma 완전 증명 작성(예상 tactic 사용)
  - Success Criteria: lemma에 `sorry` 없음, `lake build` 통과
  - Measurement: `grep -n "sorry" lean/src/UEM/YeobaekOverlap.lean` 결과 변동
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P1-D-01 ✅ lemma_name`
- `[ ]` **P1-D-02 lemma#2 증명** (동일 형식)
- `[ ]` **P1-D-03 lemma#3 증명**
- `[ ]` **P1-D-04 `margin_residual_positive` 증명**
- `[ ]` **P1-D-05 `margin_positive_measure` 증명**
- `[ ]` **P1-D-06 `yeobaek_margin_exists` 증명**
  - Action: 여백 잔여 비공집합 정리 완전 증명 작성
  - Success Criteria: lemma에 `sorry` 없음, `lake build` 통과
  - Measurement: `grep -n "yeobaek_margin_exists" lean/src/UEM/YeobaekOverlap.lean`
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P1-D-06 ✅ yeobaek_margin_exists`

### E. 메인 정리 증명
- `[ ]` **P1-E-01 하한 가정 명시**
  - Action: 잔여 포함(`Set.univ \ Π '' Set.univ ⊆ A`, `Π '' A ⊆ B`) 및 커널 두께 하한(`τ_min`)을 문서/코드에 명시하고 출처를 로그에 기록
  - Success Criteria: 가정 정의가 구조체/lemma 주석에 반영, `logs/proof_progress.md`에 인용 경로 기재
  - Measurement: `rg "h_residual_subset" lean/src/UEM/YeobaekOverlap.lean` 등 가정 확인
  - Verification: `logs/proof_progress.md` 관련 항목
  - Log Note: `YYYY-MM-DD P1-E-01 ✅ assumptions recorded`
- `[ ]` **P1-E-02 증명 구현**
  - Action: `kernel_projection_margin_lower_bound`에 명시된 가정을 활용해 실제 부등식을 완성(양의 상수 `c` 구성)
  - Success Criteria: `lake build` 통과, `sorry_count.txt` 0 유지
  - Measurement: `lake build`, `cat sorry_count.txt`
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P1-E-02 ✅ main proof`
- `[ ]` **P1-E-03 자체 검토**
  - Action: `#check`/`#print`로 결과 확인, 주석 및 calc 형태 다듬기
  - Success Criteria: 검토 결과 이상 없음, 필요 주석 보강
  - Measurement: 검토 항목을 로그에 최소 2개 기록
  - Verification: Lean repl(`#print kernel_projection_margin_lower_bound`)
  - Log Note: `YYYY-MM-DD P1-E-03 ✅ reviewed`

### F. 검증 및 문서 반영
- `[ ]` **P1-F-01 자동화 스크립트 실행**
  - Action: `lake build`, `tools/proof_coverage.sh`, 필요 시 `lake exe uem`
  - Success Criteria: 모든 명령 exit code 0, coverage 출력에 P1 정리 포함
  - Measurement: `tools/proof_coverage.sh` 로그 저장(`logs/run/P1_coverage_<date>.log`)
  - Verification: `tools/proof_coverage.sh | tee logs/run/P1_coverage_<date>.log`
  - Log Note: `YYYY-MM-DD P1-F-01 ✅ coverage updated`
- `[ ]` **P1-F-02 문서/체크리스트 갱신**
  - Action: `STATUS.md`, `CHECKLIST.md`, `CHECKLIST_ATOMIC.md`에서 P1 관련 항목 `[ ]` 처리
  - Success Criteria: 세 문서의 상태가 일치
  - Measurement: `rg "P1" STATUS.md`, `rg "P1" CHECKLIST.md`
  - Verification: `git diff STATUS.md CHECKLIST.md CHECKLIST_ATOMIC.md`
  - Log Note: `YYYY-MM-DD P1-F-02 ✅ docs synced`
- `[ ]` **P1-F-03 회고 메모**
  - Action: `logs/proof_progress.md`에 어려웠던 점, 재사용 가능한 레퍼런스, 다음 액션 작성(≥3줄)
  - Success Criteria: 회고 내용이 명확히 기록됨
  - Measurement: `tail -n 20 logs/proof_progress.md`
  - Verification: `tail -n 20 logs/proof_progress.md`
  - Log Note: `YYYY-MM-DD P1-F-03 ✅ retrospective`

---

## P2 Flow preservation & margin persistence — `lean/src/UEM/Flow.lean`

### A. 명세 및 준비
- `[x]` **P2-A-01 Spec 캡처**
  - Action: §3.4를 `docs/excerpts/P2_spec.txt`로 저장
  - Success Criteria: semigroup, divergence-free, margin 조건 포함
  - Measurement: `wc -l` ≥ 20, `rg "divergence"` ≥ 1
  - Verification: `wc -l docs/excerpts/P2_spec.txt`/`rg "divergence" docs/excerpts/P2_spec.txt`
  - Log Note: `YYYY-MM-DD P2-A-01 ✅`
- `[x]` **P2-A-02 코드 스냅샷**
  - Action: `cp lean/src/UEM/Flow.lean logs/snapshots/Flow_before_<date>.lean`
  - Success Criteria: 스냅샷 존재, 크기 ≥ 1 KB
  - Measurement: `ls -lh`
  - Verification: `ls -lh logs/snapshots/Flow_before_*.lean`
  - Log Note: `YYYY-MM-DD P2-A-02 ✅`
- `[x]` **P2-A-03 조건 목록 작성**
  - Action: `logs/plans/P2_conditions.md`에 조건/설명/검증방법 표 작성
  - Success Criteria: 행 ≥ 4, 열 ≥ 4
  - Measurement: `rg "|" logs/plans/P2_conditions.md`
  - Verification: `cat logs/plans/P2_conditions.md`
  - Log Note: `YYYY-MM-DD P2-A-03 ✅`

### B. 구조 정의 강화
- `[x]` **P2-B-01 FlowContext 설계**
  - Action: Flow 관련 구조체/record 초안 작성(필드: generator, measure, domain 등)
  - Success Criteria: `lake build` 통과, docstring에 필드 설명 존재
  - Measurement: `lake build`
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P2-B-01 ✅`
- `[x]` **P2-B-02 docstring 보강**
  - Action: Assumptions/Goal 블록 추가(각 bullet에 Spec 인용)
  - Success Criteria: Assumptions ≥ 3, Goal ≥ 1
  - Measurement: `git diff`
  - Verification: `git diff lean/src/UEM/Flow.lean`
  - Log Note: `YYYY-MM-DD P2-B-02 ✅`
- `[x]` **P2-B-03 mathlib 레퍼런스**
  - Action: `logs/mapping/P2_mathlib.md`에 관련 lemma 4개 기록
  - Success Criteria: 각 항목에 lemma 이름/경로/요약 기재
  - Measurement: `rg "|" logs/mapping/P2_mathlib.md`
  - Verification: `cat logs/mapping/P2_mathlib.md`
  - Log Note: `YYYY-MM-DD P2-B-03 ✅`

### C. theorem skeleton & 계획
- `[x]` **P2-C-01 `flow_semigroup` skeleton**
  - Action: theorem 선언, TODO에 단계별 계획 작성
  - Success Criteria: TODO 줄 ≥ 2, 필요한 가정 명시
  - Measurement: `rg "flow_semigroup" -n`
  - Verification: `rg "flow_semigroup" -n lean/src/UEM/Flow.lean`
  - Log Note: `YYYY-MM-DD P2-C-01 ✅`
- `[x]` **P2-C-02 `flow_measure_preserving` skeleton** (동일 포맷)
- `[x]` **P2-C-03 margin 정리 skeleton** (동일 포맷)

### D. 보조 lemma 증명
- `[x]` **P2-D-01 generator measurability lemma**
  - Action: lemma 증명 작성, 예외 처리 포함
  - Success Criteria: `lake build` 통과, `sorry` 제거
  - Measurement: `rg "sorry"`
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P2-D-01 ✅ lemma_name`
- `[x]` **P2-D-02 Jacobian=1 lemma** (동일 포맷)
- `[x]` **P2-D-03 σ-finite lemma** (동일 포맷)
- `[x]` **P2-D-04 기타 lemma** (필요 시 추가)

### E. 메인 정리 구현
- `[x]` **P2-E-01 `flow_semigroup` 증명**
  - Action: 세미그룹 성질 증명 작성(calc 체인 포함)
  - Success Criteria: 증명 길이 ≥ 10줄, `lake build` 통과
  - Measurement: `lake build`
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P2-E-01 ✅`
- `[x]` **P2-E-02 `flow_measure_preserving` 증명** (동일 포맷)
- `[x]` **P2-E-03 margin persistence 증명** (동일 포맷)
- `[ ]` **P2-E-04 증명 검토** (Action: `#check` 실행, Success: 로그에 검토 결과 ≥2개)

### F. 검증 및 문서
- `[ ]` **P2-F-01 자동 스크립트 실행** (Action: `tools/proof_coverage.sh` 실행; Success: Flow 정리 coverage 포함; Measurement: 로그 저장)
- `[ ]` **P2-F-02 문서/체크리스트 갱신**
- `[ ]` **P2-F-03 회고 메모**

---

## P3 Hangul interpreter completeness — `lean/src/UEM/Interpreter.lean`

### A. 준비
- `[ ]` **P3-A-01 Spec 캡처**
  - Action: §4.1–4.3을 `docs/excerpts/P3_spec.txt`에 저장
  - Success Criteria: Γ 정의, round-trip 설명 포함
  - Measurement: `wc -l` ≥ 20, `rg "Γ"` ≥ 1
  - Verification: `wc -l docs/excerpts/P3_spec.txt`/`rg "Γ" docs/excerpts/P3_spec.txt`
  - Log Note: `YYYY-MM-DD P3-A-01 ✅`
- `[ ]` **P3-A-02 코드 스냅**
  - Action: `Interpreter.lean` 복사 → `logs/snapshots/Interpreter_before_<date>.lean`
  - Success Criteria: 스냅샷 존재, 크기 ≥ 1 KB
  - Measurement/Verification: `ls -lh logs/snapshots/Interpreter_before_*.lean`
  - Log Note: `YYYY-MM-DD P3-A-02 ✅`
- `[ ]` **P3-A-03 기호/타입 목록**
  - Action: `logs/plans/P3_types.md`에 초성/중성/종성/음절 구조 표 작성(행 ≥ 6)
  - Success Criteria: 각 행에 Spec 기호·설명·Lean 타입명 기재
  - Measurement: `rg "|" logs/plans/P3_types.md`
  - Verification: `cat logs/plans/P3_types.md`
  - Log Note: `YYYY-MM-DD P3-A-03 ✅`

### B. 타입/인터페이스 설계
- `[ ]` **P3-B-01 타입 선언**
  - Action: 초성/중성/종성/음절 타입 선언 후 docstring 작성
  - Success Criteria: `lake build` 통과, 주석에 설계 의도 명시
  - Measurement/Verification: `lake build`
  - Log Note: `YYYY-MM-DD P3-B-01 ✅`
- `[ ]` **P3-B-02 parser/printer 서명**
  - Action: `encode`, `decode`, 합성 함수 서명을 Lean에 선언, TODO에 기능 설명
  - Success Criteria: 각 함수에 타입·TODO 존재
  - Measurement: `rg "encode" -n lean/src/UEM/Interpreter.lean`
  - Verification: `rg "encode" -n lean/src/UEM/Interpreter.lean`
  - Log Note: `YYYY-MM-DD P3-B-02 ✅`
- `[ ]` **P3-B-03 mathlib 조사**
  - Action: 리스트/모노이드 관련 lemma 5개 이상 `logs/mapping/P3_mathlib.md`에 기록
  - Success Criteria: 행 ≥ 5, 설명 포함
  - Measurement/Verification: `cat logs/mapping/P3_mathlib.md`
  - Log Note: `YYYY-MM-DD P3-B-03 ✅`

### C. lemma 작업
- `[ ]` **P3-C-01 injective lemma skeleton**
  - Action: `lemma encode_injective` 선언 + TODO
  - Success Criteria: TODO에 증명 전략 기재, `lake build` 통과
  - Measurement: `lake build`
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P3-C-01 ✅`
- `[ ]` **P3-C-02 surjective lemma skeleton** (동일 포맷)
- `[ ]` **P3-C-03 composition lemma skeleton** (동일 포맷)
- `[ ]` **P3-C-04 lemma 증명**
  - Action: 위 skeleton을 실제 증명으로 채움(순서대로 실행)
  - Success Criteria: lemma마다 `sorry` 없음, `lake build` 통과
  - Measurement: `rg "sorry"`
  - Verification: `lake build`
  - Log Note: `YYYY-MM-DD P3-C-04 ✅ lemma_name`

### D. 메인 정리
- `[ ]` **P3-D-01 bijective theorem skeleton** (Action: 선언 + TODO; Success: TODO ≥ 3줄; Measurement: `rg "Gamma_bijective"`; Verification 동일; Log)
- `[ ]` **P3-D-02 증명 구현** (Action: 양방향 증명 작성; Success: `lake build`; Measurement: `lake build`; Log: `P3-D-02 ✅`)
- `[ ]` **P3-D-03 예제 테스트 lemma** (Action: 간단 round-trip 예제 작성/`#eval`; Success: 테스트 성공; Measurement: 출력 기록; Verification: `lake build`; Log 기록)

### E. 검증 & 문서
- `[ ]` **P3-E-01 빌드/coverage** (Action: `lake build`, `tools/proof_coverage.sh`; Success: P3 coverage 반영; Measurement: 로그 저장)
- `[ ]` **P3-E-02 문서/체크리스트 갱신**
- `[ ]` **P3-E-03 회고 메모**

---

## P4 σ-finite margin mass — `lean/src/UEM/Measure.lean`

### A. 준비
- `[ ]` **P4-A-01 Spec 캡처** (Action: §3.1 저장; Success: σ-cover 언급; Measurement/Verification: `wc -l`, `rg "σ"`; Log)
- `[ ]` **P4-A-02 코드 스냅** (Action: `Measure.lean` 복사; Success: 스냅샷 존재; Verification: `ls -lh`; Log)
- `[ ]` **P4-A-03 가정 목록 작성** (Action: `logs/plans/P4_assumptions.md` 표; Success: 행 ≥ 5; Verification: `rg "|"`; Log)

### B. 구조 점검
- `[ ]` **P4-B-01 MeasureContext 필드 점검** (Action: 필드/가정 매칭; Success: `lake build`; Measurement: `lake build`; Log)
- `[ ]` **P4-B-02 Assumptions/Goal 주석** (Action: 주석 추가; Success: Spec 인용 포함; Verification: `git diff`; Log)
- `[ ]` **P4-B-03 mathlib 조사** (Action: σ-finite/pushforward lemma 5개 기록; Verification: `cat logs/mapping/P4_mathlib.md`; Log)

### C. lemma 및 증명
- `[ ]` **P4-C-01 lemma skeleton 삽입** (Action: 필요한 lemma 선언 + TODO; Success: `lake build`; Log)
- `[ ]` **P4-C-02 lemma 증명** (Action: skeleton 채우기; Success: `lake build`; Log: `P4-C-02 ✅ lemma_name`)
- `[ ]` **P4-C-03 메인 정리 skeleton** (Action: 선언 + 계획; Success: TODO ≥ 3줄)
- `[ ]` **P4-C-04 메인 정리 증명** (Action: 증명 작성; Success: `lake build`; Log)

### D. 검증 & 문서
- `[ ]` **P4-D-01 빌드/coverage**
- `[ ]` **P4-D-02 문서/체크리스트 갱신**
- `[ ]` **P4-D-03 회고 메모**

---

## P5 Observer finiteness bound — `lean/src/UEM/Observer.lean`

### A. 준비
- `[ ]` **P5-A-01 Spec 캡처** (Action: §5.1/§3.4 저장; Success: 관찰자 가정 포함; Measurement: `wc -l`; Verification: `wc -l docs/excerpts/P5_spec.txt`; Log)
- `[ ]` **P5-A-02 코드 스냅** (Action: `Observer.lean` 복사; Success: 스냅샷 존재; Verification: `ls -lh`)
- `[ ]` **P5-A-03 가정 목록 작성** (Action: `logs/plans/P5_assumptions.md` 표 작성; Success: 행 ≥ 5; Verification: `rg "|"`; Log)

### B. 구조 강화
- `[ ]` **P5-B-01 관찰자 구조체 재정의** (Action: 구조체/record 업데이트; Success: `lake build`; Log)
- `[ ]` **P5-B-02 docstring 보강** (Action: Assumptions/Goal 주석 추가; Success: Spec 인용 포함; Verification: `git diff`; Log)
- `[ ]` **P5-B-03 mathlib 조사** (Action: 이미지 측도 lemma 4개 기록; Verification: `cat logs/mapping/P5_mathlib.md`; Log)

### C. lemma 작업
- `[ ]` **P5-C-01 이미지 측도 lemma skeleton** (Action: 선언+TODO; Success: `lake build`; Log)
- `[ ]` **P5-C-02 경계/정보량 lemma skeleton** (동일 포맷)
- `[ ]` **P5-C-03 lemma 증명** (Action: skeleton 채우기; Success: `lake build`; Log: `P5-C-03 ✅ lemma_name`)

### D. 메인 정리
- `[ ]` **P5-D-01 finiteness theorem skeleton** (Action: 선언+TODO; Success: TODO ≥ 3줄; Verification: `rg`)
- `[ ]` **P5-D-02 정보 경계 증명** (Action: proof 작성; Success: `lake build`; Log)

### E. 검증 & 문서
- `[ ]` **P5-E-01 빌드/coverage**
- `[ ]` **P5-E-02 문서/체크리스트 갱신**
- `[ ]` **P5-E-03 회고 메모**

---

## P6 Counterfactual stability — `lean/src/UEM/Counterfactual.lean`

### A. 준비
- `[ ]` **P6-A-01 Spec 캡처**
  - Action: §5.2 및 부록을 `docs/excerpts/P6_spec.txt`로 저장
  - Success Criteria: ε→0 조건, Portmanteau 설명 포함
  - Measurement: `wc -l` ≥ 22, `rg "Portmanteau"` ≥ 1
  - Verification: `wc -l docs/excerpts/P6_spec.txt`
  - Log Note: `YYYY-MM-DD P6-A-01 ✅`
- `[ ]` **P6-A-02 코드 스냅** (Action: `Counterfactual.lean` 복사; Success: 스냅샷 존재; Verification: `ls -lh`; Log)
- `[ ]` **P6-A-03 조건 요약** (Action: `logs/plans/P6_conditions.md`에 공리/조건 표 작성; Success: 행 ≥ 5; Verification: `rg "|"`; Log)

### B. 정의/주석 보강
- `[ ]` **P6-B-01 Counterfactual 정의 강화** (Action: 정의에 필요한 가정 추가, docstring 보강; Success: `lake build`; Log)
- `[ ]` **P6-B-02 기호 표 작성** (Action: `logs/mapping/P6_terms.md` 작성; Success: 행 ≥ 8; Verification: `rg "|"`; Log)
- `[ ]` **P6-B-03 mathlib 조사** (Action: Portmanteau, dominated convergence, Levy-Prokhorov lemma ≥ 5 기록; Verification: `cat logs/mapping/P6_mathlib.md`; Log)

### C. lemma 작업
- `[ ]` **P6-C-01 margin stability lemma skeleton** (Action: 선언+TODO; Success: `lake build`; Log)
- `[ ]` **P6-C-02 semicontinuity lemma skeleton** (동일 포맷)
- `[ ]` **P6-C-03 lemma 증명** (Action: skeleton 채우기; Success: `lake build`; Log)

### D. 메인 정리
- `[ ]` **P6-D-01 stability theorem skeleton** (Action: 선언+TODO; Success: TODO ≥ 3줄)
- `[ ]` **P6-D-02 ε→0 증명 구현** (Action: 증명 작성; Success: `lake build`; Log)

### E. 검증 & 문서
- `[ ]` **P6-E-01 빌드/coverage**
- `[ ]` **P6-E-02 문서/체크리스트 갱신**
- `[ ]` **P6-E-03 회고 메모**

---

## M0 Consistency `Con(ZFC) ⇒ Con(UEM)` — `lean/src/UEM/Meta/Consistency.lean`

### A. 초기화
- `[ ]` **M0-A-01 파일 생성 및 템플릿 작성** (Action: 새 파일 및 모듈 주석 작성; Success: Spec/목표/문헌 명시; Measurement: `rg "--"`; Verification: `git status`; Log)
- `[ ]` **M0-A-02 Spec 요약 로그** (Action: §2.1 요약; Success: 로그 10줄 이상; Verification: `tail -n 15 logs/proof_progress.md`)
- `[ ]` **M0-A-03 참고 문헌 리스트** (Action: `logs/mapping/M0_refs.md`에 문헌 ≥4개 기록; Success: 각 항목에 제목/저자/링크; Verification: `cat logs/mapping/M0_refs.md`)

### B. 모델 설계
- `[ ]` **M0-B-01 해석 대상 공리 목록** (Action: 표 작성; Success: 행 ≥ 10; Verification: `rg "|" logs/plans/M0_axioms.md`)
- `[ ]` **M0-B-02 모델 구성 단계 도표** (Action: `docs/diagrams/M0_model.md` 작성; Success: 단계 ≥ 5; Verification: `cat docs/diagrams/M0_model.md`)
- `[ ]` **M0-B-03 lemma/자료 조사** (Action: 모델 이론 lemma ≥ 5개 기록; Verification: `cat logs/mapping/M0_mathlib.md`)

### C. lemma skeleton & 증명
- `[ ]` **M0-C-01 모델 구성 lemma skeleton** (Action: 단계별 lemma 선언 + TODO; Success: 선언 ≥ 3)
- `[ ]` **M0-C-02 lemma 증명** (Action: skeleton 채우기; Success: `lake build`; Log)

### D. 메인 정리
- `[ ]` **M0-D-01 Consistency theorem skeleton** (Action: 선언 + TODO; Success: TODO ≥ 4줄)
- `[ ]` **M0-D-02 증명 구현** (Action: 증명 작성; Success: `lake build`; Log)
- `[ ]` **M0-D-03 검증 명령 실행** (Action: `lake build`, `tools/proof_coverage.sh`; Success: 0 exit; Log)
- `[ ]` **M0-D-04 문서/체크리스트/로그 업데이트** (Action: 문서 상태 갱신; Success: 세 문서 일치; Verification: `git diff`)

---

## M1 Conservativity over ZFC — `lean/src/UEM/Meta/Conservativity.lean`

### A. 준비
- `[ ]` **M1-A-01 파일 생성/주석 작성** (Action: 새 파일 및 모듈 주석 작성; Success: Spec/목표 명시)
- `[ ]` **M1-A-02 Spec 요약 로그** (Action: 정의적 확장 요약; Success: 로그 ≥ 8줄)

### B. 번역 설계
- `[ ]` **M1-B-01 번역 함수 설계표** (Action: `logs/plans/M1_translations.md`에 항목별 입력/출력/조건 정리; Success: 행 ≥ 6)
- `[ ]` **M1-B-02 레퍼런스 조사** (Action: 관련 문헌/lemma ≥ 4개 기록)

### C. lemma 작업
- `[ ]` **M1-C-01 lemma skeleton 선언** (Action: 보조 lemma 선언 + TODO; Success: `lake build`)
- `[ ]` **M1-C-02 lemma 증명** (Action: skeleton 채우기; Success: `lake build`; Log)

### D. 메인 정리
- `[ ]` **M1-D-01 Conservativity 정리 skeleton** (Action: 선언 + TODO; Success: TODO ≥ 3줄)
- `[ ]` **M1-D-02 증명 구현** (Action: 증명 작성; Success: `lake build`; Log)

### E. 검증 & 문서
- `[ ]` **M1-E-01 검증 명령** (Action: `lake build`, coverage; Success: 0 exit)
- `[ ]` **M1-E-02 문서/로그 업데이트** (Action: 문서 상태 갱신; Success: 세 문서 일치)

---

## M2 Translation round-trip — `lean/src/UEM/Meta/Translation.lean`

### A. 준비
- `[ ]` **M2-A-01 파일 생성/주석 작성**
- `[ ]` **M2-A-02 Spec 요약 로그**

### B. 함수 설계
- `[ ]` **M2-B-01 UEM→ZFC 함수 설계표** (행 ≥ 6)
- `[ ]` **M2-B-02 ZFC→UEM 함수 설계표** (행 ≥ 6)

### C. lemma skeleton
- `[ ]` **M2-C-01 타입 안전성 lemma skeleton** (Action: 선언 + TODO)
- `[ ]` **M2-C-02 round-trip theorem skeleton** (Action: 선언 + TODO)

### D. 증명
- `[ ]` **M2-D-01 lemma 증명** (Action: skeleton 채우기)
- `[ ]` **M2-D-02 round-trip 증명** (Action: 증명 작성, 99.8% 보존 설명 포함)

### E. 검증 & 문서
- `[ ]` **M2-E-01 검증 명령** (Action: `lake build`, 샘플 번역 테스트 실행; Success: 테스트 성공)
- `[ ]` **M2-E-02 문서/로그 업데이트**

---

## M3 Independence of extended axioms — `lean/src/UEM/Meta/Independence.lean`

### A. 준비
- `[ ]` **M3-A-01 파일 생성/주석 작성**
- `[ ]` **M3-A-02 Spec 요약 로그**

### B. 전략 수립
- `[ ]` **M3-B-01 공리별 약화 전략 표** (행 ≥ 15, 공리별 전략)
- `[ ]` **M3-B-02 참고 문헌 조사** (forcing/모델 문헌 ≥ 6)

### C. lemma skeleton
- `[ ]` **M3-C-01 forcing/모델 lemma skeleton** (Action: 선언 + TODO)
- `[ ]` **M3-C-02 독립성 정리 skeleton**

### D. 증명
- `[ ]` **M3-D-01 공리별 증명** (Action: 가능 범위만큼 증명 작성, 미완은 TODO+근거 기록)
- `[ ]` **M3-D-02 검증 명령 실행** (Action: `lake build`, coverage)
- `[ ]` **M3-D-03 문서/로그 업데이트**

---

## 보조 작업 (조직/도구)
- `[ ]` **B1 proof_coverage 개선**
  - Action: (1) 로직 분석 (`logs/plans/B1_analysis.md` 작성) → (2) 핵심 정리 필터 구현 → (3) CI 적용 및 결과 기록
  - Success Criteria: 분석 노트 라인 ≥ 10, 필터 적용 후 핵심 정리만 출력, CI green 로그 확보
  - Measurement: `cat logs/plans/B1_analysis.md`, PR/CI 링크
  - Verification: `tools/proof_coverage.sh` 실행 결과 비교, CI 로그 확인
  - Log Note: 단계별 `YYYY-MM-DD B1-0X ✅ ...`
- `[ ]` **B2 docs/verification 작성**
  - Action: 형식 검증 목표·도구·지표를 표로 정리 후 주기적 업데이트
  - Success Criteria: 표 행 ≥ 6, 진행률/상태 열 포함
  - Measurement: 문서 diff, `rg "|" docs/verification.md`
  - Verification: `cat docs/verification.md`
  - Log Note: `YYYY-MM-DD B2 ✅ updated`
- `[ ]` **B3 교차 검증 로그 유지**
  - Action: Lean/SMT/Dafny 실행 명령·결과·이슈·조치 기록(각 도구별 최소 1회)
  - Success Criteria: 로그 항목 ≥ 3, 실패 시 조치 포함
  - Measurement: `rg "SMT" logs/proof_progress.md`
  - Verification: `tail -n 40 logs/proof_progress.md`
  - Log Note: `YYYY-MM-DD B3 ✅ tool results`
- `[ ]` **B4 세션 종료 체크**
  - Action: `WORKFLOW.md` 종료 절차(다음 작업 메모, git status 등) 수행
  - Success Criteria: 로그에 종료 요약·다음 액션 기록
  - Measurement: `tail -n 20 logs/proof_progress.md`
  - Verification: `git status`
  - Log Note: `YYYY-MM-DD B4 ✅ session closed`
- `[ ]` **B5 커밋 준비**
  - Action: `git status` 확인, 불필요 파일 삭제, 커밋 메시지 초안 작성
  - Success Criteria: `git status` clean, 메시지 초안 작성
  - Measurement: `git status`
  - Verification: `git status`
  - Log Note: `YYYY-MM-DD B5 ✅ ready to commit`

---

**사용 지침**
- `CHECKLIST.md`에서 큰 단계 진행 상황을 관리하고, 실제 실행은 본 문서에서 Task 단위로 체크하세요.
- 각 Task 완료 시 `Action`→`Success Criteria`→`Measurement`→`Verification` 순으로 자체 검증 후 `Log Note` 형식으로 기록합니다.
- 새 Task가 필요할 경우 동일한 템플릿을 복사하여 항목을 추가하고, 로그 규칙을 동일하게 적용하십시오.

