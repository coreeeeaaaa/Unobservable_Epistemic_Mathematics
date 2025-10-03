# UEM Proof Checklist (micro-granular)

UEM P/M 정리를 Lean으로 완전히 구현하기 위한 단계별 지침입니다. **모든 항목은 순서를 지키고**, 선행 단계가 완료되기 전에는 다음 단계로 넘어가지 마세요. 각 단계에는 반드시 충족해야 할 검증 기준과 확인 대상이 포함되어 있습니다.

## Checklist Protection
- 파일 삭제/이동 방지: `tools/hooks/pre-commit-checklist-guard.sh`를 `.git/hooks/pre-commit`에 링크하거나 복사하세요. 예)
  ```bash
  ln -s ../../tools/hooks/pre-commit-checklist-guard.sh .git/hooks/pre-commit
  ```
  커밋 시 체크리스트가 삭제·비우기 되면 자동으로 차단됩니다.
- 편집 전/후 잠금 제어: `tools/checklist_lock.sh unlock`으로 쓰기 권한을 잠시 열고, 수정 후 `tools/checklist_lock.sh lock`으로 다시 봉인하세요. 현재 상태는 `tools/checklist_lock.sh status`로 확인할 수 있습니다.
- Task 완료 기록은 반드시 `logs/proof_progress.md`에 남겨 나중에 감사를 거칠 수 있도록 합니다.

## 공통 준비 (각 정리 작업을 시작할 때마다 반복)
1. `[x]` **환경 확인**
   - 검증 기준: `git status`, `lake --version`, `cat lean-toolchain` 결과가 Spec에서 요구하는 브랜치/버전과 일치하고, 작업 트리가 깨끗하거나 의도한 변경만 존재함.
   - 검증 대상: 터미널 출력, `lean-toolchain` 파일.
2. `[x]` **작업 로그 오픈**
   - 검증 기준: `logs/proof_progress.md` (없으면 생성)에 날짜·정리 코드(P1 등)·목표·담당자를 기입하고 저장.
   - 검증 대상: `logs/proof_progress.md` 최신 기록.
3. `[x]` **레퍼런스 위치 기록**
   - 검증 기준: Spec 위치(`docs/UEM/UEM통합.txt`의 섹션 번호)와 참조할 설계 문서, 관련 문장 페이지를 로그에 명시.
   - 검증 대상: `logs/proof_progress.md`.

> 공통 준비가 끝난 뒤 해당 P/M 정리 섹션으로 이동하십시오.

## P-시리즈 (객체 정리)

### P1 여백중첩 하한 부등식(커널 하위 연산 포함) — `lean/src/UEM/YeobaekOverlap.lean`
1. `[ ]` **원본 코드 정리**
   - 검증 기준: 기존 형식적 증명(`use 1`, `≥ 0` 등) 삭제 또는 `TODO` 코멘트로 치환, 파일 상단 헤더에 Spec §3.2 출처 명시. 여백중첩 상위 연산과 커널 하위 연산의 관계를 주석으로 추가.
   - 검증 대상: `git diff lean/src/UEM/YeobaekOverlap.lean`.
2. `[ ]` **명세 분석 노트 작성**
   - 검증 기준: P1 가정·결론·필수 수식 요약을 `logs/proof_progress.md`에 작성, 이해되지 않는 부분은 질문 형식으로 기록.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **기호 매핑표 작성**
   - 검증 기준: Spec 기호(여백중첩 연산자, 커널 하위 연산자, τ_margin, Π, K, μ 등)와 Lean 변수 이름, 타입을 정리한 표를 코드 주석에 추가.
   - 검증 대상: `lean/src/UEM/YeobaekOverlap.lean` 주석 블록.
4. `[ ]` **mathlib 레퍼런스 수집**
   - 검증 기준: 사용할 lemma 최소 5개(예: `Measure.mono`, `lintegral`, PSD 관련)를 찾고 lemma 경로와 링크를 주석·로그에 기록. 여백중첩 상위 정의와 커널 하위 정의에 필요한 참고를 구분.
   - 검증 대상: 코드 주석, `logs/proof_progress.md`.
5. `[ ]` **보조 구조 확정**
   - 검증 기준: `YeobaekOverlapHypotheses` 구조(구 `KernelHypotheses` 별칭 포함)와 사영 전용 가정 구조(`YeobaekProjectionHypotheses`)에 필요한 필드 추가, 불필요 필드는 제거. `lake build`로 타입 체크(실패 시 원인 기록).
   - 검증 대상: `lean/src/UEM/YeobaekOverlap.lean`, 빌드 로그.
6. `[ ]` **보조 lemma skeleton 선언**
   - 검증 기준: 필요한 lemma(여백중첩 상위 연산과 커널 하위 연산을 명확히 구분하는 이름 포함) 선언, 모든 인자/반환형 명시, `by` 내부에 TODO 코멘트로 증명 계획 적기.
   - 검증 대상: `lean/src/UEM/YeobaekOverlap.lean`.
7. `[ ]` **보조 lemma 증명**
   - 검증 기준: skeleton lemma들의 `sorry` 제거. 증명 과정에서 막히면 로그에 실패 원인과 다음 시도 계획 기록. 커널 하위 연산 용어와 여백중첩 상위 개념 용어가 혼재하지 않도록 확인.
   - 검증 대상: `lean/src/UEM/YeobaekOverlap.lean`, `logs/proof_progress.md`.
8. `[ ]` **메인 정리 증명**
   - 검증 기준: `kernel_projection_margin_lower_bound`에 잔여 하한(`ε`)과 커널 두께 하한(`τ_min`) 가정을 명시하고, 이를 제공하는 보조정리(잔여 포함·커널 하한)를 통해 부등식을 완성. 남은 `sorry` 없음.
   - 검증 대상: `lean/src/UEM/YeobaekOverlap.lean`, `logs/proof_progress.md`.
9. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, `tools/proof_coverage.sh`, `sorry_count.txt` 실행/확인. 출력 내용을 로그에 붙여넣기. 여백중첩/커널 명칭이 CI 로그에도 일관되게 반영되는지 확인.
   - 검증 대상: 빌드 로그, `tools/proof_coverage.sh` 결과, `sorry_count.txt`.
10. `[ ]` **문서·체크리스트 갱신**
    - 검증 기준: `STATUS.md` P1 항목에 여백중첩 상위 개념 명칭을 반영한 진행 상황 명시, `CHECKLIST.md` 관련 항목 `[ ]` 처리, 로그에 완료 시각 기록.
    - 검증 대상: `STATUS.md`, `CHECKLIST.md`, `logs/proof_progress.md`.

### P2 Flow preservation & margin persistence — `lean/src/UEM/Flow.lean`
1. `[x]` **원본 코드 정리**
   - 검증 기준: `Flow t := id` 정의 및 자명한 정리 삭제 또는 TODO 처리, Spec §3.4 출처 주석 추가.
   - 검증 대상: `git diff lean/src/UEM/Flow.lean`.
2. `[x]` **Spec 요약 로그**
   - 검증 기준: 시간분리 가정, divergence-free 조건, margin persistence 목표를 로그에 요약.
   - 검증 대상: `logs/proof_progress.md`.
3. `[x]` **구조 설계 문서화**
   - 검증 기준: Flow 구조(예: `structure FlowContext`), generator, semigroup 조건을 Lean 구조/record로 정의하고 주석에 설명.
   - 검증 대상: `lean/src/UEM/Flow.lean`.
4. `[x]` **mathlib 레퍼런스 수집**
   - 검증 기준: `MeasurePreserving`, `Semigroup`, Jacobian 관련 lemma 최소 4개 기록.
   - 검증 대상: 코드 주석, 로그.
5. `[x]` **새 Flow 정의 확정**
   - 검증 기준: `Flow` 또는 보조 구조가 명시적 가정을 포함하도록 정의. `lake build`로 타입 검사 수행.
   - 검증 대상: `lean/src/UEM/Flow.lean`, 빌드 로그.
6. `[x]` **semigroup lemma skeleton**
   - 검증 기준: `theorem flow_semigroup` 선언, 필요한 가정/결론 정확히 표기, TODO 주석에 증명 전략 작성.
   - 검증 대상: `lean/src/UEM/Flow.lean`.
7. `[x]` **measure-preserving skeleton**
   - 검증 기준: `theorem flow_measure_preserving`, margin persistence 정리 선언, 가정 명시.
   - 검증 대상: `lean/src/UEM/Flow.lean`.
8. `[x]` **보조 lemma 증명**
   - 검증 기준: generator measurability, Jacobian=1, σ-finite 사용 lemma 등 보조 정리 증명 완료.
   - 검증 대상: `lean/src/UEM/Flow.lean`.
9. `[x]` **margin persistence 증명**
   - 검증 기준: 여백이 시간에 따라 줄지 않는다는 증명 완성, 필요한 적분/부등식 계산 명확히 기재.
   - 검증 대상: `lean/src/UEM/Flow.lean`.
10. `[ ]` **검증 명령**
    - 검증 기준: `lake build`, `tools/proof_coverage.sh`, `sorry_count.txt` 확인 및 로그 기록.
    - 검증 대상: 빌드 로그, coverage 출력.
11. `[ ]` **문서·로그 갱신**
    - 검증 기준: `STATUS.md` P2 업데이트, 본 문서 상태 변경, 작업 로그에 완료 메모.
    - 검증 대상: `STATUS.md`, `CHECKLIST.md`, `logs/proof_progress.md`.

### P3 Hangul interpreter completeness — `lean/src/UEM/Interpreter.lean`
1. `[ ]` **현재 코드 제거 및 주석 보강**
   - 검증 기준: 기존 `interpret` 한 줄 정의 삭제/TODO 처리, Spec §4.1 출처 주석 추가.
   - 검증 대상: `git diff lean/src/UEM/Interpreter.lean`.
2. `[ ]` **Spec 요약 로그 작성**
   - 검증 기준: Γ 전역 총함수, round-trip 조건, 연산자 의미를 로그에 요약.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **타입/자료 구조 설계**
   - 검증 기준: 초성/중성/종성 타입과 음절 구조 정의, Lean 코드 및 주석으로 명시.
   - 검증 대상: `lean/src/UEM/Interpreter.lean`.
4. `[ ]` **parser/printer 인터페이스 선언**
   - 검증 기준: `encode`, `decode`, 합성 함수 서명을 선언하고, 타입이 맞는지 `lake build`로 확인.
   - 검증 대상: `lean/src/UEM/Interpreter.lean`, 빌드 로그.
5. `[ ]` **mathlib/구조 레퍼런스 기록**
   - 검증 기준: 리스트, 모노이드, 재귀 관련 lemma 최소 4개 목록화.
   - 검증 대상: 주석, 로그.
6. `[ ]` **보조 lemma skeleton 작성**
   - 검증 기준: injective, surjective, soundness lemma 선언, TODO에 증명 전략 기재.
   - 검증 대상: `lean/src/UEM/Interpreter.lean`.
7. `[ ]` **보조 lemma 증명**
   - 검증 기준: skeleton lemma 증명 완료, 막힌 부분은 로그 기록.
   - 검증 대상: 코드, 로그.
8. `[ ]` **메인 정리 증명 (`Gamma.bijective`)**
   - 검증 기준: encode/decode round-trip 양방향 증명 완료, 예제 lemma/테스트 추가 가능.
   - 검증 대상: `lean/src/UEM/Interpreter.lean`.
9. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, 필요 시 간단 테스트 lemma 실행, coverage 확인.
   - 검증 대상: 빌드 로그, coverage 출력.
10. `[ ]` **문서·로그 갱신**
    - 검증 기준: `STATUS.md` P3 업데이트, 체크리스트 상태 변경, 로그에 완료 메모.
    - 검증 대상: `STATUS.md`, `CHECKLIST.md`, `logs/proof_progress.md`.

### P4 σ-finite margin mass — `lean/src/UEM/Measure.lean`
1. `[ ]` **코드/주석 정비**
   - 검증 기준: Spec §3.1 출처 주석 추가, 기존 자명한 설명 정리.
   - 검증 대상: `git diff lean/src/UEM/Measure.lean`.
2. `[ ]` **Spec 요약 로그 작성**
   - 검증 기준: σ-cover 정의, finite mass 목표를 로그에 서술.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **mathlib 레퍼런스 수집**
   - 검증 기준: σ-finite, pushforward, outer measure 관련 lemma 최소 5개 기록.
   - 검증 대상: 코드 주석, 로그.
4. `[ ]` **보조 lemma skeleton 선언**
   - 검증 기준: σ-cover 처리, finite union 등 필요한 lemma 선언 및 TODO 주석.
   - 검증 대상: `lean/src/UEM/Measure.lean`.
5. `[ ]` **보조 lemma 증명**
   - 검증 기준: skeleton lemma 증명 완료, 실패 시 원인 기록.
   - 검증 대상: `lean/src/UEM/Measure.lean`, 로그.
6. `[ ]` **메인 정리 증명**
   - 검증 기준: σ-finite margin mass 정리 선언·증명, `sorry` 없음.
   - 검증 대상: `lean/src/UEM/Measure.lean`.
7. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, coverage, `sorry_count.txt` 확인.
   - 검증 대상: 빌드 로그 등.
8. `[ ]` **문서·로그 갱신**
   - 검증 기준: `STATUS.md` P4 업데이트, 체크리스트 변경, 로그 메모.
   - 검증 대상: 문서·로그.

### P5 Observer finiteness bound — `lean/src/UEM/Observer.lean`
1. `[ ]` **Spec 요약 및 주석 정비**
   - 검증 기준: Spec §5.1/§3.4 가정을 주석으로 명시, 기존 자명한 설명 정리.
   - 검증 대상: `git diff lean/src/UEM/Observer.lean`.
2. `[ ]` **로그 기록**
   - 검증 기준: 관찰자 가정(정보량·해상도·σ-finite), 목표 정리를 로그에 정리.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **구조 재정의**
   - 검증 기준: 관찰자 구조체/record를 재정의, 필요한 가정/변수 포함.
   - 검증 대상: `lean/src/UEM/Observer.lean`.
4. `[ ]` **mathlib 레퍼런스 수집**
   - 검증 기준: 이미지 측도, measure bounds 관련 lemma 4개 이상 기록.
   - 검증 대상: 주석, 로그.
5. `[ ]` **보조 lemma skeleton 선언**
   - 검증 기준: 이미지 측도 bounds, 조합 경계 lemma 선언 및 TODO 주석.
   - 검증 대상: `lean/src/UEM/Observer.lean`.
6. `[ ]` **보조 lemma 증명**
   - 검증 기준: skeleton lemma 증명 완료, 실패 시 로그.
   - 검증 대상: 코드, 로그.
7. `[ ]` **메인 정리 증명**
   - 검증 기준: 관찰자 유한성 및 정보 경계 정량화 정리 증명.
   - 검증 대상: `lean/src/UEM/Observer.lean`.
8. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, coverage, `sorry_count.txt` 확인.
   - 검증 대상: 빌드 로그 등.
9. `[ ]` **문서·로그 갱신**
   - 검증 기준: `STATUS.md` P5 업데이트, 체크리스트 변경, 로그 메모.
   - 검증 대상: 문서·로그.

### P6 Counterfactual stability — `lean/src/UEM/Counterfactual.lean`
1. `[ ]` **Spec 요약/주석 정비**
   - 검증 기준: Spec §5.2, Portmanteau 관련 가정 주석 추가, 기존 단순 정리 TODO 처리.
   - 검증 대상: `git diff lean/src/UEM/Counterfactual.lean`.
2. `[ ]` **로그 기록**
   - 검증 기준: ε→0 조건, 안정성 목표, 필요 도구를 로그에 서술.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **mathlib 레퍼런스 수집**
   - 검증 기준: Portmanteau, dominated convergence, Levy-Prokhorov lemma 최소 5개 기록.
   - 검증 대상: 주석, 로그.
4. `[ ]` **보조 lemma skeleton 선언**
   - 검증 기준: stability/semicontinuity 준비 lemma 선언 및 TODO.
   - 검증 대상: `lean/src/UEM/Counterfactual.lean`.
5. `[ ]` **보조 lemma 증명**
   - 검증 기준: skeleton lemma 증명 완료, 실패 시 로그.
   - 검증 대상: 코드, 로그.
6. `[ ]` **메인 안정성 정리 증명**
   - 검증 기준: ε→0 안정성(세미연속성 포함) 정리 증명 완성.
   - 검증 대상: `lean/src/UEM/Counterfactual.lean`.
7. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, coverage, `sorry_count.txt` 확인.
   - 검증 대상: 빌드 로그 등.
8. `[ ]` **문서·로그 갱신**
   - 검증 기준: `STATUS.md` P6 업데이트, 체크리스트 변경, 로그 메모.
   - 검증 대상: 문서·로그.

## M-시리즈 (메타 정리)

### M0 Consistency `Con(ZFC) ⇒ Con(UEM)` — `lean/src/UEM/Meta/Consistency.lean`
1. `[ ]` **파일 생성 및 주석 스텁 작성**
   - 검증 기준: 새 파일 생성 후 모듈 설명(목표, 참고 문헌, Spec 섹션) 주석으로 기재.
   - 검증 대상: `lean/src/UEM/Meta/Consistency.lean`.
2. `[ ]` **Spec 요약 로그**
   - 검증 기준: 상대적 일관성에 필요한 가정/절차를 로그에 정리.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **모델 설계 노트**
   - 검증 기준: 해석 모델 구성 단계, 필요한 구조/추상화를 로그 또는 주석으로 문서화.
   - 검증 대상: `logs/proof_progress.md`, 코드 주석.
4. `[ ]` **레퍼런스 조사**
   - 검증 기준: 모델 이론/정의적 확장 lemma 이름과 출처를 기록.
   - 검증 대상: 로그, 주석.
5. `[ ]` **Consistency 정리 skeleton 선언**
   - 검증 기준: 정리 서명에 가정/결론 명확히 표기, TODO로 증명 계획 작성.
   - 검증 대상: `lean/src/UEM/Meta/Consistency.lean`.
6. `[ ]` **보조 lemma skeleton 선언 및 TODO 작성**
   - 검증 기준: 모델 구성 단계별 lemma 선언, 각 단계별 필요 조건을 TODO로 기재.
   - 검증 대상: 코드.
7. `[ ]` **보조 lemma 증명**
   - 검증 기준: 가능한 부분부터 증명, 미완 부분은 `admit` 대신 명시적 TODO와 로그 기록.
   - 검증 대상: 코드, 로그.
8. `[ ]` **메인 증명 완성**
   - 검증 기준: Con(ZFC)→Con(UEM) 증명 완료, `sorry` 없음.
   - 검증 대상: 코드.
9. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, coverage, `sorry_count.txt` 확인.
   - 검증 대상: 빌드 로그 등.
10. `[ ]` **문서·로그 갱신**
    - 검증 기준: `STATUS.md` M0 업데이트, 체크리스트 변경, 로그 완료 메모.
    - 검증 대상: 문서·로그.

### M1 Conservativity over ZFC — `lean/src/UEM/Meta/Conservativity.lean`
1. `[ ]` **파일 생성 및 주석 작성**
   - 검증 기준: 모듈 헤더에 Spec 요약·목표·참고 문헌 기재.
   - 검증 대상: `lean/src/UEM/Meta/Conservativity.lean`.
2. `[ ]` **Spec 요약 로그**
   - 검증 기준: 정의적 확장 조건을 로그에 정리.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **번역 함수 스켈레톤 정의**
   - 검증 기준: UEM→ZFC 번역 함수 서명과 기본 성질 lemma 선언, TODO 주석 작성.
   - 검증 대상: 코드.
4. `[ ]` **레퍼런스 조사**
   - 검증 기준: 보수성 관련 lemma, definitional extension 자료 출처 기록.
   - 검증 대상: 로그, 주석.
5. `[ ]` **Conservativity 정리 skeleton 선언**
   - 검증 기준: 정리 서명, 가정, 결론 명시. 증명 전략을 TODO로 기재.
   - 검증 대상: 코드.
6. `[ ]` **보조 lemma 선언·증명**
   - 검증 기준: 필요한 중간 lemma 정의 후 증명, 실패 시 로그 기록.
   - 검증 대상: 코드, 로그.
7. `[ ]` **메인 증명 완성**
   - 검증 기준: 정리 증명 완료, `sorry` 없음.
   - 검증 대상: 코드.
8. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, coverage, `sorry_count.txt` 확인.
   - 검증 대상: 빌드 로그 등.
9. `[ ]` **문서·로그 갱신**
   - 검증 기준: `STATUS.md` M1 업데이트, 체크리스트 변경, 로그 메모.
   - 검증 대상: 문서·로그.

### M2 Translation round-trip — `lean/src/UEM/Meta/Translation.lean`
1. `[ ]` **파일 생성 및 주석 작성**
   - 검증 기준: TR1/TR2 요약, 목표, 참고 문헌 주석.
   - 검증 대상: 코드.
2. `[ ]` **Spec 요약 로그**
   - 검증 기준: 라운드트립 조건(99.8% 보존 등) 로그에 작성.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **UEM→ZFC/역함수 skeleton 정의**
   - 검증 기준: 두 함수의 타입 선언 및 TODO 작성, 타입 체크.
   - 검증 대상: 코드, 빌드 로그.
4. `[ ]` **타입 안전성 lemma 선언**
   - 검증 기준: 타입 보존, 닫힘성 lemma 선언 및 TODO.
   - 검증 대상: 코드.
5. `[ ]` **round-trip theorem skeleton 선언**
   - 검증 기준: 정리 서명, 성공률 조건 명시. 증명 전략 TODO 작성.
   - 검증 대상: 코드.
6. `[ ]` **보조 lemma 증명 및 메인 증명**
   - 검증 기준: 보조 lemma→메인 정리 순서대로 증명, 실패 시 로그 기록.
   - 검증 대상: 코드, 로그.
7. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, (필요 시) 샘플 번역 테스트 작성, 결과 로그 저장.
   - 검증 대상: 빌드 로그, 테스트 출력.
8. `[ ]` **문서·로그 갱신**
   - 검증 기준: `STATUS.md` M2 업데이트, 체크리스트 변경, 로그 메모.
   - 검증 대상: 문서·로그.

### M3 Independence of extended axioms — `lean/src/UEM/Meta/Independence.lean`
1. `[ ]` **파일 생성 및 주석 작성**
   - 검증 기준: 대상 공리 목록, 전략, 참고 문헌을 주석으로 기록.
   - 검증 대상: 코드.
2. `[ ]` **Spec 요약 로그**
   - 검증 기준: 독립성 요구사항, 반모델 전략을 로그에 작성.
   - 검증 대상: `logs/proof_progress.md`.
3. `[ ]` **모델/forcing 전략 설계**
   - 검증 기준: 공리별 약화/반모델 구성 아이디어를 노트로 정리.
   - 검증 대상: 로그 또는 주석.
4. `[ ]` **레퍼런스 조사**
   - 검증 기준: independence/forcing 관련 lemma 출처 기록.
   - 검증 대상: 로그, 주석.
5. `[ ]` **independence theorem skeleton 선언**
   - 검증 기준: 각 공리별 독립성 정리 선언, 증명 전략 TODO 기록.
   - 검증 대상: 코드.
6. `[ ]` **증명/구현 진행**
   - 검증 기준: 가능한 독립성 증명부터 작성. 미완성일 경우 근거와 TODO 명시.
   - 검증 대상: 코드, 로그.
7. `[ ]` **검증 명령 실행**
   - 검증 기준: `lake build`, coverage, `sorry_count.txt` 확인.
   - 검증 대상: 빌드 로그 등.
8. `[ ]` **문서·로그 갱신**
   - 검증 기준: `STATUS.md` M3 업데이트, 체크리스트 변경, 로그 메모.
   - 검증 대상: 문서·로그.

## 보조 작업 (조직/도구)
- `[ ]` **`tools/proof_coverage.sh` 개선**
  1. `[ ]` 현재 스크립트 구조·출력 분석 후 로그 기록.
  2. `[ ]` 핵심 정리만 집계하도록 필터/옵션 구현, 테스트 결과 로그 첨부.
  3. `[ ]` CI에 적용(PR 또는 설정 변경), CI 로그 확인.
- `[ ]` **`docs/verification.md` 작성**
  1. `[ ]` 형식 검증 목표와 도구별 계획(Lean/SMT/Dafny)을 표로 정리.
  2. `[ ]` 진행 상황 업데이트, 외부 검증 로그 링크 추가.
- `[ ]` **교차 검증 로그**
  - 검증 기준: 각 도구 실행 명령·결과·오류·조치 기록.
  - 검증 대상: `logs/proof_progress.md` 또는 별도 로그.
- `[ ]` **세션 종료 체크**
  - 검증 기준: `WORKFLOW.md`의 종료 절차(다음 작업 메모, git 상태 확인 등) 수행 후 로그 작성.
- `[ ]` **커밋 준비**
  - 검증 기준: `git status` 깨끗함 확인, 커밋 메시지 초안 작성, 필요 시 `proof_coverage.txt`/`docs` 변경 검토.

## 진행 규칙
1. 선행 단계가 완료되지 않았을 경우 다음 단계 체크 금지.
2. 중단/실패한 단계는 즉시 로그에 이유와 후속 계획을 남김.
3. `lake build` 실행 시 명령·버전·시간을 기록하여 재현 가능성 확보.
4. 문서 업데이트는 `STATUS.md`·`CHECKLIST.md`·`logs/proof_progress.md`가 항상 일치하도록 확인.
5. 추가 의문이나 참고 사항은 로그나 주석에 즉시 기록하고, 해결 시 체크.

이 문서를 순서대로 따르면 P-시리즈와 M-시리즈 정리를 체계적으로 완료할 수 있습니다.
