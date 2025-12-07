# UEM 문서 패키지 (최신본 모음)

> 스펙/설계/철학/응용/작업지침을 한 폴더에서 찾기 위한 인덱스입니다.  
> 파일을 이동하지 않고 참조만 모았으며, 이 인덱스가 “최신본” 위치입니다.

## 1) 스펙 · 버전
- `docs/spec/VERSION_INDEX.md` — 최신 스펙: v3.1, 위치는 `docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` (레거시 링크: `..._v3.0.md` 포인터).
- `docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` — 본문 스펙.
- `docs/spec/UEM_CORE_FORMALISM_v0.1.md` — UEM 수학·논리 핵심 스펙(상태/세계/여백/사영/Γ/차원).
- `docs/spec/UEM_OBJECT_HIERARCHY_SPEC_v0.1.md` — Tensor→Sparke→Actyon→Escalade→Secare 계층, 단위/포함/승격 규칙.
- `docs/spec/HANGUL_OPERATORS_SPEC_v0.1.md` — 한글 연산자/초병렬 스펙(Γ, ⊗_par, ∇_hangul, 에러 코드).
- `docs/spec/HANGUL_LEAN_MAPPING_v0.1.md` — 한글→Lean 기호 매핑.
- `docs/spec/UEM_ANALYTIC_PACKAGE_v0.1.md` — μ_unobs, KM-1~3, P-라인 등 분석 패키지 스펙.

## 2) 설계 · 청사진
- `docs/blueprint/UEM_BLUEPRINT_v1.md` — 깊이 강제 규약, 연구 방향, 형식 스펙, 증명 로드맵, 실행 우선순위.
- `docs/blueprint/ADVANCED_COLLECTION.md` — 주요 문서 인덱스(스펙/철학/응용/설계/논문).
- `docs/blueprint/TODO_DEPTH.md` — 증명 단계로 끌어올릴 TODO(차원/여백/그래프/객체/사례/보수성).
- `docs/blueprint/LOGIC_MARGIN_PACKAGE.md` — 여백·논리공간·논리차원 패키지 정의(σ-대수/측도, Kripke 결합, 삼중 결합 정리 목표).
- `docs/blueprint/HANGUL_OPERATORS_PACKAGE.md` — 한글 연산자(Γ) 대수 구조, 공리, HS 서브셋, Lean 매핑.
- `docs/blueprint/HIGH_SCHOOL_TOOLKIT.md` — 고교/전통 수학용 표준 연산자 세트, 여백 필터, 동치 정리, HS 서브셋 규약.
- `docs/blueprint/MEASURE_KERNEL_PACKAGE.md` — μ_unobs, KM-1~3, P2~P6, SCD/AHS 가정·정리 스켈레톤.
- `docs/blueprint/FORMALIZATION_PIPELINE.md` — UEM↔ZFC 라운드트립, Hangul→Lean 매핑.
- `docs/blueprint/HIERARCHY_PACKAGE.md` — Tensor/Scalar/Vector → Sparke → Actyon → Escalade → Secare, 6축 규칙.
- `docs/blueprint/THEOREM_STATEMENTS.md` — 모듈별 정리 문장 고정(증명만 남도록).

## 3) 철학 · 선언
- `docs/philosophy/UEM_DECLARATION_ORIGINAL.md` — 원본 선언/철학.

## 4) 응용 · 사례
- `docs/examples/UEM_ADVANCED_APPLICATIONS_v1.0.md` — 고급 응용(양자 얽힘, 모달/카테고리, 창발 등).

## 5) 설계 원칙
- `docs/design/UEM_DESIGN_PRINCIPLES.md` — 철학→설계 매핑 규칙, 보존/여백/병렬 원칙.

## 6) 논문 뼈대
- `docs/paper/main.tex` — LaTeX 원고.

## 7) 현재 코드 진입점
- `formal/UEM.lean` — 전체 import.
- 확장 정의: `formal/UEM/Basic/Dimensions.lean`, `.../Margin.lean`, `.../System/Graph.lean`, `.../Objects/Extended.lean`, `.../Cases/Skeletons.lean`.
- 직합 사영/정리: `formal/UEM/Basic/NullProjection.lean`, `formal/UEM/Theorems/P1_NullProjection.lean`.

## 8) 남은 핵심 작업(요약)
- `docs/blueprint/TODO_DEPTH.md`의 항목을 증명/정리로 채우기: X_rec lemma, margin/L_proj 보존식, 그래프-사영 교환, Ext 객체 불변량, 사례 정리(삼체/터널링/난류 등), 보수성 lemma.
