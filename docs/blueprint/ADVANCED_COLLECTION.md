# UEM 고도화 자료 모음 (Advanced Set)

> 가장 심화된 스펙·철학·응용·설계 자료를 한곳에서 찾도록 묶은 인덱스입니다.  
> 기존 파일은 이동하지 않고 참조만 제공합니다. (2025-03 기준)

## 핵심 청사진
- `docs/blueprint/UEM_BLUEPRINT_v1.md` — 스펙·철학·증명 로드맵·단기 TODO를 통합한 최신 청사진.

## 스펙 · 설계
- `docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` — v3.1 주요 스펙(Part I/II/III, dated).
- `docs/spec/VERSION_INDEX.md` — 현재 최신 스펙 버전 및 파일 위치 명시(최신= v3.1, 레거시 포인터는 v3.0 파일).
- `docs/design/UEM_DESIGN_PRINCIPLES.md` — 설계 원칙/지침.

## 철학 · 선언
- `docs/philosophy/UEM_DECLARATION_ORIGINAL.md` — 원본 선언문(존재/한계/보수성 철학).

## 응용 · 사례
- `docs/examples/UEM_ADVANCED_APPLICATIONS_v1.0.md` — 양자 얽힘, 범주론, 창발 등 고급 응용 예시.

## 논문 원고
- `docs/paper/main.tex` — LaTeX 논문 뼈대(추후 청사진을 반영해 업데이트 필요).

## 사용 가이드
- 개념·목표 파악: BLUEPRINT → SPEC → DESIGN 순서로 읽기.
- 철학적 배경: DECLARATION 참조 후 BLUEPRINT의 보수성/한계 규율 확인.
- 응용 아이디어: ADVANCED_APPLICATIONS를 예제로 참고.
- 구현/증명: BLUEPRINT의 단기 TODO와 증명 로드맵에 맞춰 Lean 코드를 강화. 원하는 차원/객체/사영 정의가 없는 경우, BLUEPRINT 섹션 3을 우선 반영.
