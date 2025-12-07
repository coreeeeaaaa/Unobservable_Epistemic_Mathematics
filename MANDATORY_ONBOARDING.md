# UEM Mandatory Onboarding (Read Before Any Work)
모든 작업자/에이전트는 코드를 읽거나 수정하기 전에 아래 문서를 반드시 확인하고, 규칙을 따라야 합니다. 이 절차를 건너뛰면 안 됩니다.

필수 문서 (순서대로 읽기)
1) `AGENTS.md` — 리포 전반 규칙, 빌드/검증/스타일 지침.
2) `docs/blueprint/FINAL_INDEX.md` — 최신 스펙·청사진·철학·응용 위치 인덱스.
3) `docs/roadmap/UEM_HARDENING_PLAN_v0.1.md` — 고도화 대상과 우선순위.
4) `docs/roadmap/Hangul_Hyperparallel_Spec_v0.1.md` — 한글 연산자/초병렬 스펙 초안.

필수 체크 (작업 전)
- 스펙/설계 내용 **축약·삭제 금지** (내용 줄이거나 요약 금지 규칙 준수).
- 코드/문서 작업 전 최신 문서 경로 확인: `docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` (Part I/II 복원 필요 여부 파악), `docs/blueprint/TODO_DEPTH.md`.
- 빌드/검증: `cd formal && rg "sorry" .` → `lake build UEM` (또는 영향 모듈).

작업 중 지침
- 한글 연산자/초병렬 관련 변경 시: `docs/roadmap/Hangul_Hyperparallel_Spec_v0.1.md`의 구조(C/V/F, ⊗_par, ∇_hangul, MarginLog)와 “절대 축약 금지” 규칙을 따른다.
- 설계/철학-코드 정합성 유지: 문서에 없는 가정을 새로 만들면 문서를 먼저 보강한 뒤 코드에 반영.
- Lean: trusted axiom 금지, `sorry` 금지, 증명/정의는 모듈 간 순환 없이 작성.

이 문서는 리포의 “입구”입니다. 다른 에이전트/개발자도 동일하게 준수해야 합니다. 작업 전에 반드시 이 파일을 읽었다고 간주하고 진행하십시오.
