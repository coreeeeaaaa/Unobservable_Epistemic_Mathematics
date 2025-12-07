# UEM Constitution (Common Rules for All Agents/Developers)

모든 작업자/에이전트는 아래 규칙을 무조건 준수한다. 강제 주입 훅이 없더라도, 이 문서와 `MANDATORY_ONBOARDING.md`를 읽었다고 간주한다.

## 1) 필수 문서
- `MANDATORY_ONBOARDING.md` (진입점, 필독)
- `AGENTS.md` (repo 규칙, 빌드/검증/스타일)
- `docs/blueprint/FINAL_INDEX.md` (최신 문서 위치 인덱스)
- `docs/roadmap/UEM_HARDENING_PLAN_v0.1.md` (고도화 대상/우선순위)
- `docs/roadmap/Hangul_Hyperparallel_Spec_v0.1.md` (한글 연산자/초병렬 스펙 초안)
- `docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` (스펙 본문; Part I/II 복원 필요 여부 확인)

## 2) 금지/강제 규칙
- 내용 축약·삭제·간소화 금지: 기존 설계/문서/버전/처리 내용을 줄이지 않는다.
- trusted axiom 금지, `sorry` 금지 (Lean).
- 새 가정/정의 추가 시 문서 먼저 보강, 코드 후 반영.
- 한글 연산자/초병렬 변경 시 `Hangul_Hyperparallel_Spec_v0.1.md` 준수 (C/V/F, ⊗_par, ∇_hangul, MarginLog).

## 3) 빌드/검증
- `cd formal && rg "sorry" .`
- `cd formal && lake build UEM` (또는 영향 모듈 우선 빌드).

## 4) 작업 절차
- 시작 전: 위 필수 문서 훑기 → 최신 경로/버전 확인.
- 변경 전: 설계-코드 정합성 검토, 필요한 경우 문서 먼저 업데이트.
- 변경 후: 빌드/검증 실행, 관련 문서에 반영/링크.

## 5) 용어/기호
- Π_null, MarginLog, L_proj 등 스펙 기호는 문서 매핑 테이블을 따른다. 새 기호 도입 시 문서에 추가.

본 문서는 “범용/공통 규칙”을 선언한 헌법적 위치의 파일이다. 모든 에이전트/개발자는 준수 의무가 있다.
