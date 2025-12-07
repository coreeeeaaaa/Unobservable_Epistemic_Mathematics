# UEM Core Formalism v0.1 (수학·논리 스펙, 축약 금지)
> 목적: UEM을 “완전히 수학적·논리적으로 서술”하기 위한 공통 핵심 정의/연산/구조를 정리한다. 기존 텐서/해석/측도/논리 위에 여백·사영·인식 차원을 얹어 정합적 설계를 목표로 한다. (축약·삭제 금지, 추가·정밀화만 허용)

## 0. 기본 도메인 (공간/위상/측도 확정)
- 물리 공간 `X_phys`: 표준 Borel(Hausdorff, 2차가산) 위상공간, 필요 시 Hilbert/Banach 구조를 갖는다.
- 인식 공간 `X_rec`: 유한 차원 표준 Borel 공간(모달/논리/시간 좌표 포함), 가변 차원은 분리된 층으로 취급.
- 전체 상태 공간  
  - 기본 모델: 직적 위상·측도 공간 `X_total := X_phys × X_rec`, σ-대수 `Σ_total := Σ_phys ⊗ Σ_rec`.  
  - 관측 사영 `Obs : X_total → X_obs`를 갖춘 섬유 번들 모델: `X_total ≅ ⊔_{z∈X_obs} F_z` with π=Obs.  
  - 몫 모델: 관측 동치 `∼`에 대해 `X_obs := X_total / ∼` (표준 Borel 가정 하에 분해 가능).
- 시간 집합 `Time` (ℝ 또는 ℤ)과 σ-대수 `Σ_time` (보렐 등).

## 1. 상태, 세계, 여백 (위상/집합/측도 명시)
- 상태 `State := (phys : X_phys, rec : X_rec, margin : M)`; margin은 로그/여백을 담는다.
- 세계(`Secare`) ♡: `(S_sub, B, Σ, axis, M_sek)`  
  - `S_sub ⊆ X_total` (부분공간), `B ⊆ S_sub`(경계/Archive 규칙), `Σ`(σ-대수/축), `axis`(축/좌표), `M_sek`(세계 차원의 여백).
- 여백 `M`: 관측/사영에서 버려진 정보의 로그/측도/엔트로피.  
  - 집합 정의: `M(P) := Dom(P) \ Im(P)`; 측도형식: `𝔐(P) := (Dom(P), Σ, μ_unobs)`  
  - 위상/측도 관계: `S_sub`가 표준 Borel이면 `M(P)`도 Σ-가측 집합, `μ_unobs`는 μ로부터 정칙/σ-유한성 계승.
- 무력화 사영 `Π_null : S_sub → S_obs` (멱등·가측). Margin 채널: `(x ↦ (Π_null x, x \ Π_null^{-1}(Π_null x)))`.

## 2. 객체 계층 (Tensor 불변, UEM 상위 객체 포함)
- Tensor 계층: Tensor(0)=Scalar, Tensor(1)=Vector, Tensor(n)=n-텐서. 기존 연산/기호 변경 금지.
- Sparke ⛦ (단위 spar): `(X:Tensor(n), support, margin, axis/σ 옵션)`. Add/merge = 값 합 + support ∪ + margin 병합. 랭크는 X와 연동.
- Actyon ㆁ (단위 acti): 유한/가중 Sparke 멀티셋 + agent/role/meta.
- Escalade 𓂌 (단위 escul): 흐름/동역학 `(f : S → S, time domain, invariants)`.
- Secare ♡ (단위 seks): 세계/경계/축/σ-대수/여백을 담는 컨테이너.
- 포함: Tensor(n) ⊂ Sparke(n) ⊂ Actyon(n) ⊂ Escalade(n) ⊂ Secare(n).  
  승격/투영: embed_{n→n+1}, proj_{n+1→n}는 Tensor 규칙 전파(보존 조건 표는 TODO: `UEM_OBJECT_HIERARCHY_SPEC_v0.1.md`).

## 3. 연산자 및 대수 구조 (닫힘 조건)
- Sparke: AddCommMonoid (값 합, support ∪, margin 병합) on domain `Tensor(n)×Support×Margin`. 결과는 동일 랭크 Sparke.  
- Actyon/Escalade: 병합/분기/flow에서 rank/axis/margin을 보존하는 변환에 한정하여 닫힘.  
- Secare: 경계/Archive 안정성, 축 병합/충돌 규칙 하에서 닫힘.  
- 사영-흐름 교환: `Π_null ∘ f = f_keep ∘ Π_null` with f Lipschitz/가측, Π_null 멱등·보완.

## 4. 한글 연산자 (Γ) 및 초병렬 (정의역/공역·닫힘 명시)
- 음절 σ = (C,V,F,I) ∈ `Consonant × Vowel × Final × Index`; 해석 함수  
  \[
    Γ : Consonant × Vowel × Final × Index \to (State \to State)
  \]
  정의역 = `State`, 공역 = `State` (닫힘).
  합성/병합: `J(C,V,F)(X)=A_F(V(C(X)))`, 모든 중간 연산은 State에 닫힘.
- 병렬 ⊗_par:  
  \[
    ⊗_{\mathrm{par}} : (State→State)×(State→State)→(State→State)
  \]
  결합성, (단위원 없음), 주석 충돌 시 resolve 규칙(우선순위)으로 결정성 유지. 닫힘: 두 입력이 well-typed이면 출력도 State→State.
- 다방향 ∇_hangul:  
  \[
    ∇_{\mathrm{hangul}}(f) := ⊗_{\mathrm{par}}\{\partial_{γ} f \mid γ∈Γ\text{-basis}\}
  \]
  정의역/공역 = `State→State`, 기저는 HS/전체 LUT에서 선택.  
- 제약(Closedness): 모든 C/V/F/I가 LUT/금지조합 검사를 통과해야 하며, 사영/미분/적분은 `X_total` 위 가측·Lipschitz 등 가정 하에 State 내부에 머무른다.  
  → 상세: `docs/spec/HANGUL_OPERATORS_SPEC_v0.1.md`.

## 5. 방정식/정리(이름 수준, 본문화 필요)
- 여백 영속/시간–여백 결합 예: `∂_t M + div(F_M) = S_M`, `|dM/dt| ≤ τ(M)`.
- 커널–여백(KM-1~3), 사영–겹침 교환, 사영 왜곡 경계, PH 안정 등 대표 10개 패키지: 선언문/청사진에 이름·형태만 존재 → 가정/정확한 상수·정리 문장 필요.
- μ_unobs(비관측 측도): μ, Obs, 𝔐 조합으로 정의 + 정칙성/σ-유한성 등 정리 필요.
- P-라인: P1(커널 부등식/여백 하계)은 증명됨; P2~P6는 정리 문장·가정·오차경계 고정 필요(Lean 증명은 후순위).

## 6. 관측/비관측 표현 모델 (정식 정리 템플릿)
- 관측 σ-대수 `𝔽_obs ⊂ 𝔽` (전체). 관측 함수 `𝒪 = {f : S→ℝ | f가 𝔽_obs-가측}`.  
- 관측 동치: `s₁ ∼ s₂ ⇔ ∀f∈𝒪, f(s₁)=f(s₂)`.  
- 관측 세계 `S_obs := S/∼`, 비관측 자유도 N (여백).  
- 표현 정리(Obs-Decomp):  
  - 가정(표준/분해 가능):  
    1. `(S,𝔽,μ)` 표준 Borel, `𝔽_obs = Obs^{-1}(𝔾)` for measurable `Obs : S→S_obs`, `𝔾` σ-대수.  
    2. 각 섬유 `Obs^{-1}(z)`가 표준 가측 공간, 선택 함수 존재.  
  - 결론: `S ≅ S_obs × N` (N = canonical fiber), `Π_null = Obs`, `Margin(s) = 섬유 좌표`.  
  - Corollary: `μ = ∫ μ_z dμ_obs(z)` (disintegration), `μ_unobs(A) = ∫ μ_z(A∩Obs^{-1}(z)) dμ_obs`.

## 7. 논리/차원/세계
- 논리공간/차원: Kripke 프레임 (W,R,V)와 인식 공간 결합, “논리 차원 수”=분기/모달 깊이 등 정의 필요.  
- 여백–논리–기하 삼중 결합: 가능세계 변화가 PH/여백에 미치는 영향 부등식/정리 목표.  
- Secare 6축(존재/비존재/무존재/반존재/공백/여백):  
  - 존재: 경계 내부, 점유/정의된 영역.  
  - 비존재: 경계 내부의 빈 영역(허용되지 않음).  
  - 무존재: 모델 밖/정의역 밖.  
  - 반존재: 잠재/가능세계 경계상태.  
  - 공백: 내부 허용된 빈 영역.  
  - 여백: 관측·사영으로 버린 정보가 기록되는 영역.  
  계층 연동: Sparke→Actyon→Escalade→Secare에서 축 정보 전파/보존.

### 7.1 논리공간/차원 모델(제안)
- Kripke 프레임 `(W,R,V)`와 Secare 세계 ♡를 결합:  
  - 관측자 상태/가능세계 집합 W, 접근성 R, 평가 V.  
  - 논리 차원 수 = branching degree 또는 modal depth(선택).  
  - 여백 𝔐와 결합: “여백이 큰 논리 방향” = R 분기/가능세계 집합 중 여백량이 큰 부분집합.  
- 정리 목표(표현): 논리 분기 변화 → PH/여백 왜곡 상계(L_logic)로 제어.

### 7.2 여백·논리공간·논리차원 모델
- 여백 공간 𝔐(P): 관측 공간(Ω, Σ) 위 σ-대수/측도 구조, 여백 노름 ‖𝔐‖, 여백 차원(기하/논리) 분리 정의.  
- 논리공간: (W,R,V), 논리 차원 = 분기/깊이/독립 관측 방향 개수.  
- 삼중 결합 목표: `Loss_total ≤ C1·Loss_proj + C2·Loss_logic + C3·geom_distortion`.

### 7.3 Secare 6축 ↔ 계층 연동 규칙
- 축 이름: 존재/exist, 비존재/nonexist, 무존재/outside, 반존재/liminal, 공백/void, 여백/margin.  
- 연동:  
  - Sparke/Actyon/Escalade는 axis 필드에 6축 중 하나 이상을 태깅.  
  - 병합: axis 충돌 시 우선순위 `exist > liminal > margin > void > nonexist > outside`, 동일 우선순위 충돌 시 오류.  
  - 사영(Π_null): margin 축으로 이동한 성분은 MarginLog에 기록, 다른 축은 보존.  
  - 승격/강등: 상위 객체 승격 시 축 태그 그대로 전파, 덮어쓰기 금지(위반 시 오류).  
  - Secare: 6축 전체를 보유, 하위 객체 축 누락 시 상속 값을 채우되 기록 남김.

## 8. 확장 정의 (필수 채움 → 고정)
- 비관측 측도 `μ_unobs`: 선택안 고정 — `μ_unobs(A) := μ(A \ Obs^{-1}(Obs(A)))`; 정칙/σ-유한성은 μ가 정칙/σ-유한이고 Obs가 가측이면 계승됨.  
- KM-1~3(커널–여백–PH): `UEM_ANALYTIC_PACKAGE_v0.1`에 가정/결론을 정식 문장으로 고정(Π Lipschitz, K bounded PD, PH 거리 상계 등).  
- P2~P6: 각 정리의 정의역/가정/결론/오차경계를 `UEM_ANALYTIC_PACKAGE_v0.1` 섹션 4에 최소 1개씩 명시 완료(모노이드/flow 교환/차원 독립/논리 영향/사례).  
- UEM↔ZFC 라운드트립: 해석 함수 `⟦·⟧_U→Z`, `⟦·⟧_Z→U`; 정리 형태 `∀φ, ⟦⟦φ⟧_U→Z⟧_Z→U ↔ φ` (해석 가능 문장).  
  - 가정: 번역이 보존하는 논리/구문 클래스(예: 1차 논리, UEM 전용 기호 제거) 명시.
- Hangul→Lean 매핑 표: 기호(τ_margin, Π, K, μ, ⛦, ㆁ, 𓂌, ♡, Γ 토큰) ↔ Lean 이름/notation, HS 서브셋 표시.
- Secare 6축: 존재/비존재/무존재/반존재/공백/여백을 객체 계층에 연동.

### 8.1 UEM↔ZFC 라운드트립 (정식 문장)
- 해석 함수 타입: `I_{U→Z} : Form_UEM → Form_ZFC`, `I_{Z→U} : Form_ZFC → Form_UEM`.  
- Soundness: `⊢_UEM φ → ⊢_ZFC I_{U→Z}(φ)`.  
- Round-trip: `φ ∈ Frag → ⊢_UEM (I_{Z→U} ∘ I_{U→Z})(φ) ↔ φ` (Frag = UEM 1차 조각).  
- Conservativity: `⊢_ZFC ψ → ⊢_UEM I_{Z→U}(ψ)` for ZFC-해석 가능한 ψ.  
- Lean/Dafny skeleton: 해석 함수와 증명 목표를 시그니처로 선언해 코드 연동.

## 9. 체크리스트 (완료/미완)
- [x] Part I/II 본문 복원(공리/차원/세계 정의).  
- [x] 객체 계층 스펙 기본(단위/포함/승격 정책).  
- [x] 랭크/axis 보존 정책 요약(충돌 처리 기본값).  
- [x] 랭크/axis 세부 표(충돌/사상 규칙) `UEM_OBJECT_HIERARCHY_SPEC_v0.1` 2.1/2.3.  
- [x] 여백·논리공간·논리차원 모델(𝔐, 논리 차원, 표현 정리 템플릿).  
- [x] Γ 스펙 LUT/규칙/에러 코드/HS 기저(자모 전표 포함).  
- [x] Γ 공리 정식화, Lean skeleton 가이드.  
- [x] μ_unobs, KM-1~3, P2~P6 정식 문장/가정(분석 패키지 v0.1에 정식 서술).  
- [x] UEM↔ZFC 라운드트립 해석/진리보존 정리(문장 고정).  
- [x] Hangul→Lean 매핑 표 v0.1 추가(확장 필요).  
- [x] Secare 6축 설명 추가(계층 연동은 추가 필요).

## 10. 위치/연동
- 상위 인덱스: `README.md`, `UEM_STRUCTURE_GUIDE_v0.1.md`, `docs/blueprint/FINAL_INDEX.md`.
- 관련 스펙: `UEM_OBJECT_HIERARCHY_SPEC_v0.1.md`, `HANGUL_OPERATORS_SPEC_v0.1.md`, `HANGUL_LEAN_MAPPING_v0.1.md`, `UEM_ANALYTIC_PACKAGE_v0.1.md`.
- 청사진/로드맵: `UEM_BLUEPRINT_v1.md`, `TODO_DEPTH.md`, `UEM_HARDENING_PLAN_v0.1.md`.

이 문서는 UEM의 수학적·논리적 핵심을 정합적으로 묶기 위한 기초 스펙이다. 이후 버전에서 각 항목을 정식 정의/정리/가정으로 채워 넣어야 한다.
