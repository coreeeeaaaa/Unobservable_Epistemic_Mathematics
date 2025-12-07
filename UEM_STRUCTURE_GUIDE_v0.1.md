# UEM Structure Guide (백서/총괄서) v0.1
> 목적: 선언문·청사진·로드맵에 흩어진 핵심 구조/목차를 “궁극적 사전/지침/총괄서”로 묶어, 단계적으로 고도화할 기준틀을 제공한다.  
> 상태: v0.1 — 스켈레톤. (축약 금지: 기존 내용을 줄이지 않고 확장/정밀화만 허용)

## 0. 원칙
- 축약 금지: 기존 내용은 줄이지 않고, 필요한 세부만 추가/정밀화한다.
- 문서-코드 정합: 설계/목차에 새 항목을 넣으면 해당 문서/코드 위치를 지정한다.
- 필수 규칙 준수: `MANDATORY_ONBOARDING.md`, `CONSTITUTION.md`, `AGENTS.md`를 먼저 읽고 따른다.

## 1. 상위 아키텍처 목차 (채워 넣을 구조)
- 서문/철학: `docs/philosophy/UEM_DECLARATION_ORIGINAL.md`
- 스펙: `docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` (Part I/II 복원 필요)
- 핵심 스펙: `docs/spec/UEM_CORE_FORMALISM_v0.1.md`
- 객체 계층: `docs/spec/UEM_OBJECT_HIERARCHY_SPEC_v0.1.md`
- 한글 연산자: `docs/spec/HANGUL_OPERATORS_SPEC_v0.1.md`, `docs/spec/HANGUL_LEAN_MAPPING_v0.1.md`
- 분석 패키지: `docs/spec/UEM_ANALYTIC_PACKAGE_v0.1.md`
- 청사진/인덱스: `docs/blueprint/FINAL_INDEX.md`, `docs/blueprint/UEM_BLUEPRINT_v1.md`
- TODO/Proof-ready: `docs/blueprint/TODO_DEPTH.md`, `docs/blueprint/UEM_PROOF_READY_SPEC_v1.md`
- 강화 계획: `docs/roadmap/UEM_HARDENING_PLAN_v0.1.md`
- 한글 초병렬 스펙: `docs/roadmap/Hangul_Hyperparallel_Spec_v0.1.md`
- 헌법/온보딩: `CONSTITUTION.md`, `MANDATORY_ONBOARDING.md`, `README.md`(입구), `AGENTS.md`

## 2. 선언문/대화에서 뽑은 설계 지침 (고도화 대상)
1) 한글 연산자(음절=4축 튜플)  
   - (C,V,F,I) = (초성, 중성, 종성, 위치). 네 축 각각을 “기하/값/인식/위치” 레이어로 매핑.  
   - 병렬 레지스터/병합 규칙 정의 → 한 음절 = 1급 연산자 Oσ: S → S 로 해석.
   - TODO: C/V/F LUT, 금지 조합, ⊗_par/∇_hangul 규칙, MarginLog 확정(스켈레톤은 `Hangul_Hyperparallel_Spec_v0.1.md` 참조).
2) 큐브 계층 (3/5/7/9/11…)  
   - 각 큐브 = 격자(i,j)에 상태 필드 Φ(i,j) (시간/공간/인식/차원/가능/여백/변화량 Δx,Δy,Δz,Δt,Δc,Δd,ΔΩ 포함).  
   - 결정론적 갱신 U_N(Φ_N) → Φ_N′, 프랙탈 합성: Φ^{k+1} = U_{N_k}(Φ^k).  
   - TODO: 축/의미(예: 궯/욜/휵), 5×5 블록 의미, 상태/변화량 필드 정의를 문서화.
3) 좌표/차원 설정  
   - 기본 (x,y), 종속 z = x−y 관점; 격자점 (i,j) ↦ (x=i,y=j,z=i−j).  
   - 상태/변화량 필드를 이 좌표계 위에 올리는 규칙 명시.  
4) 초병렬·여백/사영 연산  
   - 입력 단위 = 큐브 전체 상태; Δ 패턴을 병렬로 읽어 결정론적 규칙으로 갱신.  
   - 여백/중첩/사영 규칙과 MarginLog 결합.
5) 고차 문제(예: 5차 방정식) 상위 표현  
   - 기존 불가능/한계를 인정하되, UEM 상위 연산자로 표현/추적/선택 가능한 구조를 정의.  
   - TODO: 정리/공리 문장과 사용 연산자(음절·큐브·여백/사영)를 문서화.

## 3. 작업 지침 (반복 고도화 루프)
- 문서 우선: 위 항목별로 문서 위치를 지정하고, 스켈레톤 → 확정표/정의 → 코드/증명 순으로 보강.
- 인덱스 반영: 추가/수정 시 `docs/blueprint/FINAL_INDEX.md`에 최신 위치 링크.
- Lean 연계: 정의/연산은 Lean skeleton(시그니처)부터 추가, 증명 목표를 리스트업.

## 4. 단계적 고도화 플랜 (A–D 단계)
- A단계 (기초 복원): 스펙 Part I/II 본문 복원, Margin/L_proj 정의·보존식 확정.
- B단계 (한글/초병렬 코어): C/V/F LUT·금지 조합·⊗_par/∇_hangul 규칙·MarginLog 확정, Lean skeleton 선언.
- C단계 (큐브/Δ 필드 최소본): 3/5큐브 의미·상태/변화량(Δx,Δy,Δz,Δt,Δc,Δd,ΔΩ) 정의, 고차 큐브(7/9/11)는 후순위.
- D단계 (응용/고차 문제): 5차 등 고차 문제 상위 표현 정리 문장, 사례/정리 초안.

## 6. 진행 현황 (요약)
- Part I/II 복원: 완료(스펙 v3.1에 채움).
- 핵심 스펙/계층/한글/분석 패키지: v0.1 문서 추가 완료.
- 남은 필수: 랭크/축 세부 표, Γ LUT/규칙 완성, 여백·논리공간 모델 정식화, μ_unobs/KM/P2~P6 정리 문장, UEM↔ZFC 라운드트립, Hangul→Lean 매핑 확장.

## 5. 용어/관념 TODO (추가 기록)
- 한글 4축 음절 병렬 레지스터/병합 규칙: 문서화 필요.
- 큐브 격자 상태 Φ_N, 결정론적 갱신 U_N, 프랙탈 합성 규칙: 문서화 필요.
- z 종속좌표(z=x−y) 관점과 Δ 필드 정의: 문서화 필요.
- 고차 문제(5차 등) 상위 연산자/정리: 문장·규칙·사용 연산자 명시 필요.
