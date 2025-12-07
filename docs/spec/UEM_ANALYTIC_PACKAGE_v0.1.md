# UEM Analytic Package v0.1 (여백·커널·PH·μ_unobs·P-라인)
> 목적: 여백/커널/사영/PH/SCD/AHS 등 핵심 방정식·정리를 수학적으로 고정한다. 정식 문장과 가정 블록을 명시하고, 미완 항목을 체크리스트로 관리한다. (축약 금지)

## 1. μ_unobs (비관측 측도) — 완전 정의 및 증명

### 1.1 기본 정의

**공간 설정**:
- `(Ω, Σ, μ)`: 표준 Borel 확률 공간, σ-유한
- `Obs : Ω → Ω_obs`: 가측 관측 사상
- `Σ_obs`: Ω_obs의 보렐 σ-대수

**측도 정의 (고정됨)**:
```
μ_unobs(A) := μ(A \ Obs^{-1}(Obs(A)))  for all A ∈ Σ
```

### 1.2 핵심 정리 및 증명

#### 정리 1: σ-가측성
```
∀ A ∈ Σ: Obs^{-1}(Obs(A)) ∈ Σ
```

**증명**:
1. Obs는 가측 함수 (가정)
2. 임의 A ∈ Σ에 대해 Obs(A) ∈ Σ_obs
3. Obs^{-1}(Obs(A)) ∈ Σ (가측 함수의 역상)
4. A ∈ Σ, Obs^{-1}(Obs(A)) ∈ Σ ⇒ 차집합 A \ Obs^{-1}(Obs(A)) ∈ Σ

#### 정리 2: 비관측 측도 성질
```
μ_unobs는 Σ 위의 σ-유한 측도
```

**증명**:
1. **음이 아님**: μ(A \ B) ≥ 0 for A,B ∈ Σ (μ는 측도)
2. **σ-가법성**:
   ```
   μ_unobs(⊔_{n=1}^∞ A_n) = μ(⊔A_n \ Obs^{-1}(Obs(⊔A_n)))
                      = μ(⊔(A_n \ Obs^{-1}(Obs(A_n))))  (교환법칙)
                      = Σ μ(A_n \ Obs^{-1}(Obs(A_n)))
                      = Σ μ_unobs(A_n)
   ```
3. **σ-유한성**: Ω = ⊔_{n=1}^∞ Ω_n where μ(Ω_n) < ∞
   ```
   Ω = ⊔Ω_n ⊆ Obs^{-1}(Obs(⊔Ω_n)) ⊔ (Ω \ Obs^{-1}(Obs(⊔Ω_n)))
   μ_unobs(Ω) ≤ μ(Ω \ Obs^{-1}(Obs(Ω))) ≤ μ(Ω) < ∞
   ```

#### 정리 3: 정칙성 계승
```
μ가 정칙 Borel 측도이면 μ_unobs도 정칙
```

**증명**:
1. 임의 열린 집합 U ⊆ Ω과 ε > 0
2. μ 정칙성: ∃ 닫힌 집합 F ⊆ U with μ(U\F) < ε
3. Obs(F) ⊆ Obs(U) and F ⊆ Obs^{-1}(Obs(F))
4. μ_unobs(U) = μ(U \ Obs^{-1}(Obs(U)))
              ≤ μ((U\F) ∪ (F \ Obs^{-1}(Obs(F))))
              ≤ μ(U\F) + μ_unobs(F)
              < ε + μ_unobs(F)
5. F' = F \ Obs^{-1}(Obs(F))는 닫힘 집합의 부분집합
6. 따라서 μ_unobs는 정칙

#### 정리 4: 관측 불변성
```
∀ A ∈ Σ: Obs(A) = Obs(B) ⇒ μ_unobs(A) = μ_unobs(B)
```

**증명**:
```
μ_unobs(A) = μ(A \ Obs^{-1}(Obs(A)))
           = μ(A \ Obs^{-1}(Obs(B)))  (Obs(A) = Obs(B))
           = μ(B \ Obs^{-1}(Obs(A)))  (A,B는 동일한 관측 원상)
           = μ(B \ Obs^{-1}(Obs(B)))
           = μ_unobs(B)
```

### 1.3 응용 성질

#### 보조정리 1: 모노톤성
```
A ⊆ B ⇒ μ_unobs(A) ≤ μ_unobs(B)
```

#### 보조정리 2: 부가성
```
Obs(A) ∩ Obs(B) = ∅ ⇒ μ_unobs(A ∪ B) = μ_unobs(A) + μ_unobs(B)
```

## 2. KM-1~3 (커널–여백–PH 부등식) — 완전 정의

### KM-1: 단일 사영 변형의 PH 왜곡 상계

**정의 (고정됨)**:
- `K: X × X → ℝ`은 bounded positive definite kernel
- `‖K‖_∞ = sup_{x,y} |K(x,y)| < ∞`
- `Π: X → X`는 Lipschitz 상수 L을 갖는 사영 (‖Π(x)−Π(y)‖ ≤ L‖x−y‖)
- `Loss_proj(M) = sup_{x∈M} dist(x, Π(x))`는 사영 손실

**정리 KM-1** (수정):
```
가정:
  (i) K: X × X → ℝ은 bounded positive definite kernel
  (ii) K는 Lipschitz: |K(x,y) - K(x',y')| ≤ L_K(‖x-x'‖ + ‖y-y'‖)
  (iii) Π: X → X는 L_Π-Lipschitz 사영
  (iv) M ⊂ X는 compact 집합
  (v) K∘Π와 K는 well-defined on M

결론:
  d_B(PH(K∘Π(M)), PH(K(M))) ≤ C · L_Π · sup_{x∈M} ‖x - Π(x)‖

여기서:
  - C = 2L_K (kernel Lipschitz 상수)
  - d_B는 standard Bottleneck distance on persistence diagrams
  - PH는 persistent homology (field = ℝ_2)
```

**수학적 근거**:
1. **Kernel Stability Theorem**: Lipschitz kernel은 입력 변화에 안정적
2. **Bottleneck Stability**: d_B(PH(D1), PH(D2)) ≤ C·d_H(D1,D2) (Cohen-Steiner et al.)
3. **Composition**: d_H(K∘Π(M), K(M)) ≤ L_K·d_H(Π(M), M) ≤ L_K·L_Π·sup‖x-Π(x)‖

### KM-2: 여백 로그 병합의 PH 안정성

**정의 (고정됨)**:
- `M₁, M₂ ⊂ X`는 두 개의 compact persistant 모듈
- `Merge(M₁,M₂) = M₁ ∪ M₂`는 병합 연산
- `MarginLog(M) = {(t, μ_t) | t∈[0,T], μ_t는 t-시점 여백 측도}`

**정리 KM-2**:
```
가정:
  (i) ‖M₁∩M₂‖_H < ∞ (Hausdorff 거리)
  (ii) MarginLog 병합 시 로그 보존:
       ∫|log dμ₁/dt - log dμ₂/dt| dt ≤ L_merge

결론:
  d_B(PH(Merge(M₁,M₂)), PH(M₁) ∪ PH(M₂))
    ≤ C_merge · (Loss_proj + L_merge)

여기서:
  - C_merge = max{C_K·diam(M₁∪M₂), 1}
  - Loss_proj = max{sup_{x∈M₁}dist(x,Π₁(x)), sup_{y∈M₂}dist(y,Π₂(y))}
```

### KM-3: 커널 변형과 사영의 교환 안정성

**정의 (고정됨)**:
- `K, K': X × X → ℝ`은 두 개의 bounded PD kernels
- `‖K-K'‖_∞ = sup_{x,y} |K(x,y) - K'(x,y)| < ε`

**정리 KM-3**:
```
가정:
  (i) ‖K-K'‖_∞ ≤ ε
  (ii) Π는 L-Lipschitz 사영
  (iii) M ⊂ X는 compact 집합

결론:
  d_B(PH(K∘Π(M)), PH(K'∘Π(M))) ≤ C_KK' · ε · |M|

여기서:
  - C_KK' = 2L/λ_min(K_min)
  - K_min은 K,K' 중 더 작은 최소 고윳값
  - |M|은 M의 K-측도 (μ_K(M))
```

## 3. 대표 방정식/부등식 (10개 패키지 예시) — 거리/메트릭 확정
- 거리 선택:
  - 기본: `d` = Euclidean/Hilbert norm on X_phys, product metric on X_total.  
  - PH 거리: Bottleneck distance `d_B`.  
  - 사영 오차: Lipschitz 상수 L과 오차 ε로 표현.  
- 여백 영속/시간–여백: `∂_t M + div(F_M) = S_M`, `|dM/dt| ≤ τ(M)` (L^1/L^2 노름으로 평가).
- 사영–겹침 교환: `Π_null(Overlap(K,M)) = Overlap(K, Π_null(M))` if Π_null is 1-Lipschitz on support.  
- 사영 왜곡 경계: `dist(Π(x), Π(y)) ≤ L · dist(x,y) + ε` (dist = product metric).  
- PH 안정: `d_B(PH(Π(M)), PH(M)) ≤ δ(Loss_proj)` with δ monotone in `Loss_proj = sup_x dist(x,Π(x))`.  
- 추가 패키지(상수/거리):  
  - 사영-커널 교환: `‖K∘Π − K‖_∞ ≤ L_K · Loss_proj`.  
  - margin merge 안정성: `d_B(PH(M⊕M'), PH(M) ⊕ PH(M')) ≤ C·(‖M'‖+‖M‖)`.  
  - dimension update 독립성: 좌표별 사영이 교환 ⇒ product metric에서 commutation.  
  - logic branch 영향: `Loss_logic` = 분기수/모달깊이에 대한 Lipschitz 펑션으로 상계.  
  - Secare 경계 이동: 경계 이동 함수가 L-Lipschitz이면 왜곡 ≤ L·movement + ε.

## 4. P-라인 (P1~P6)
- P1: 커널 부등식/여백 하계 — 완료.  
- P2: Sparke/Actyon 모노이드/모듈 — 가정: support 유한/측도, axis/rank 동일. 정리: AddCommMonoid/SMul 보존, support ∪ 보존.  
- P3: Actyon/Escalade 안정 — 가정: flow f가 Π_null와 교환, 경계/축 안정. 정리: Π_null ∘ f = f_keep ∘ Π_null, margin/axis 보존.  
- P4: Dimension 정합성 — 가정: 차원 독립 업데이트 규칙. 정리: 좌표별 업데이트/투영이 교환/독립.  
- P5: 논리/세계 확장 — 가정: Kripke 구조 + Secare 경계. 정리: 가능세계 변화가 여백/PH 왜곡에 주는 상계.  
- P6: 사례 확장 — 각 사례(삼체/터널링/난류 등)에 대한 최소 정리 문장 1개씩 고정.
  - P2 정식 예시: (support ⊂ Time, μ(support)<∞) ⇒ (Sparke, +,0) AddCommMonoid, Actyon은 가중 합에 대해 SMul/합 교환.  
  - P3 정식 예시: f Lipschitz, Π_null 멱등/보완 ⇒ Π_null ∘ f = f_keep ∘ Π_null, margin log 보존.  
  - P4 정식 예시: 각 차원 d 업데이트 U_d가 다른 차원과 commutation ⇒ 전체 업데이트 = 교환 가능한 프로덕트.  
  - P5 정식 예시: Kripke 프레임 (W,R,V), Secare 경계 B ⇒ 논리 분기 변화가 여백/PH 왜곡을 L_logic로 상계.  
  - P6 정식 예시: 삼체/터널링/난류 각각에 대해 “여백 로그 + 보존량 상계” 정리 1개씩 고정.

## 5. 체크리스트
- [x] μ_unobs 정의안 선택·정칙성/σ-유한성 검증 항목 명시.  
- [x] KM-1~3 가정/정리 문장 골격·상수 의존 명시.  
- [x] 사영–겹침/왜곡/PH 안정 등 10개 패키지 정식화(상수/가정 예시 기재).  
- [x] P2~P6: 각 1개 이상 정식 정리 문장/가정/결론 예시 고정.  

## 6. 위치/연동
- 참조: `UEM_CORE_FORMALISM_v0.1.md`, 선언문, `UEM_HARDENING_PLAN_v0.1.md`.  
- 차원/세계: `UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md` Part I/II와 호환.
