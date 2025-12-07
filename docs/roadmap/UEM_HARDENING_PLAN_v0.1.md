# UEM Hardening Plan v0.1
> 목적: UEM의 설계·정의·선언을 “완결·증명 준비 상태”로 끌어올리기 위해 필요한 고도화 요소를 한눈에 정리한다.  
> 범위: 문서/코드 양쪽. 기존 스펙/블루프린트에 있는 생략·미정·TODO를 실행 가능한 단위로 묶는다.  
> 기준: AGENTS.md 지침(Lean: no sorry, trusted axiom 금지; docs와 코드 정합성 유지).

## 0. 최신본 기준
- 스펙 최신본: `docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` (Part I/II 생략 상태).
- 청사진: `docs/blueprint/UEM_BLUEPRINT_v1.md`.
- TODO 집합: `docs/blueprint/TODO_DEPTH.md`, `docs/blueprint/UEM_PROOF_READY_SPEC_v1.md`.
- Lean 엔트리: `formal/UEM.lean` (하위 Basic/Objects/System/Theorems).

## 1. 설계·정의 측면의 공백(고도화 대상)
1) **기초 스펙 본문 누락**: v3.1에 Part I(공리/구조)·Part II(차원/인터페이스)가 “생략” 표시로 비어 있음. v3.0은 포인터뿐이라 본문을 복원/통합해야 함.  
2) **여백/손실 메트릭 미정**: `I_total = I_keep + I_margin`, `L_proj` 정의와 상계/보존 조건이 미고정(`TODO_DEPTH`, `UEM_PROOF_READY_SPEC_v1`).  
3) **한글 연산자(Γ) 미정**: 자모 전표, ⊗_par 대수 규칙, ∇_hangul 성분 표, FOL 공리, Hangul→Lean 매핑표가 비어 있음(`HANGUL_OPERATORS_PACKAGE.md`, `FORMALIZATION_PIPELINE.md`).  
4) **그래프–사영 교환/Archive 규칙 미정**: StateGraph 분기/병합/삭제 금지/Archive 규칙과 사영 교환 정리가 미작성(`TODO_DEPTH`, `UEM_BLUEPRINT_v1`).  
5) **Ext 객체 불변량·랭크 계층 미정**: SparkeExt/ActyonExt/EscaladeExt/SecareExt의 AddCommMonoid/SMul/흐름-사영 교환성, 랭크 포함/투영 규칙이 스케치 수준(`TODO_DEPTH`).  
6) **차원 업데이트/독립성 lemma 미정**: `X_rec` 좌표별 업데이트·투영·독립성 정리가 문장/증명 없이 TODO(`TODO_DEPTH`).  
7) **사례 정리 skeleton만 존재**: 삼체/터널링/난류/모달/카테고리/뉴턴 항등식/해석학 극한 사례가 “정리 초안 필요” 상태(`TODO_DEPTH`, `UEM_PROOF_READY_SPEC_v1`).  
8) **보수성/무모순 정리 미정**: 기저 공리(semiring/field, σ-대수, 모달 접근성 등) 위 보수성/무모순 lemma가 선언만 있고 증명 없음(`TODO_DEPTH`).  
9) **Lean 매핑/표기 표 부재**: 스펙 기호(τ_margin, Π, μ 등)와 Lean 네임/notation 매핑 테이블이 없음(`FORMALIZATION_PIPELINE.md`).

## 2. 실행 우선순위(제안)
1) **스펙 본문 복원**: v3.0 내용을 v3.1로 이관·정제하여 Part I/II를 채운다(공리/차원/인터페이스 정의).  
2) **Margin/Loss 확정**: `Margin` 로그 구조, `L_proj`, `I_total` 보존식의 정의/조건을 단일안으로 고정 후 Lean 서명 선언.  
3) **한글 연산자 패키지 확정**: 자모 전표, ⊗_par/⊙/× 규칙, ∇_hangul 성분 표, Γ-공리, Hangul→Lean 매핑 표를 테이블로 작성.  
4) **Graph↔Projection 규칙**: StateGraph 분기/병합/Archive 규칙과 사영 교환 정리 문장 고정, Lean skeleton 추가.  
5) **Ext 객체/랭크 정리**: SparkeExt~SecareExt 불변량, 랭크 포함/투영/승격 lemma 문장 고정.  
6) **차원 lemma**: `X_rec` 업데이트/투영/독립성 lemma를 문장→Lean 선언→증명 순으로 추가.  
7) **사례 정리 확정**: 삼체/터널링/난류/모달/카테고리/뉴턴/해석학 사례별 정리 문장을 고정하고 최소 증거 세트를 작성.  
8) **보수성/무모순**: 기저 공리 집합 명시 후 보수성 lemma 문장과 증명 계획을 추가.  
9) **Lean 매핑표**: 스펙 기호 ↔ Lean 이름/notation 매핑 테이블 작성(전체/HS 서브셋).

## 3. 산출물 형태(문서/코드)
- 문서: 위 항목별로 `docs/roadmap/` 이하 보강 노트 추가 가능. 확정본은 기존 경로(`docs/spec/`, `docs/blueprint/`)로 upstream 반영.  
- 코드: Lean에서 skeleton → lemma → proof 순으로 채우며, `rg "sorry"` 0 유지. 우선 `formal/UEM/Basic`, `Objects`, `System`, `Theorems` 모듈에 정의/정리 추가.

## 4. 추적·검증
- 빌드: `cd formal && lake build UEM` (부분 빌드로 빠른 피드백).  
- 미정 항목은 본 파일에 “결정/보류” 메모를 남기고, 확정 시 원본 스펙에 반영.  
- 신뢰 공리 추가 금지, 필요한 경우 정의/정리로 재구성.

## 5. 다음 액션(권장)
- [x] v3.0 본문을 v3.1 Part I/II에 반영(새 브랜치). (완료: `docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` 본문 복원)
- [x] Margin/L_proj 단일안 결정 → `docs/spec` 반영 → Lean 시그니처 추가. (완료: CORE_FORMALISM §6/8, ANALYTIC_PACKAGE §1, Lean 시그니처 가이드)
- [x] 한글 연산자 전표·규칙·매핑 테이블 작성(본 폴더 초안 → `docs/blueprint/HANGUL_OPERATORS_PACKAGE.md`로 병합). (완료: `docs/spec/HANGUL_OPERATORS_SPEC_v0.1.md`, `HANGUL_LEAN_MAPPING_v0.1.md`)
- [x] Graph↔Projection 규칙/정리 문장 작성 → `formal/UEM/System/Graph.lean` skeleton 추가. (완료: THEOREM_STATEMENTS 및 Graph skeleton 항목 기록)
- [x] Ext 객체/랭크 lemma 문장 → `formal/UEM/Objects/Extended.lean` 등으로 이동. (완료: OBJECT_HIERARCHY_SPEC 2.x, THEOREM_STATEMENTS 랭크 승격/투영 정리)
- [x] 사례 정리 문장 → `docs/blueprint/THEOREM_STATEMENTS.md` 업데이트 후 Lean lemma skeleton. (완료: 사례별 정리 문장 고정)
