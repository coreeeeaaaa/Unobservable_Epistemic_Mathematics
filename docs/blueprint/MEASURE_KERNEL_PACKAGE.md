# μ_unobs · KM 부등식 · P2~P6 · SCD/AHS (정식화 고정안)

> 목표: 비관측 측도, 커널–여백–PH(KM), P2~P6, SCD/AHS 정리의 가정 블록과 최소 정식 문장을 고정하여 “증명만 하면 되는” 상태로 끌어올린다.

## 1. 비관측 측도 μ_unobs
- 정의: 관측 사영 \(\pi:\Omega\to\Omega_{obs}\)와 기존 측도 \(\mu\)로부터  
  \[
  \mu_{unobs}(B) := \mu(B) - \mu(\pi^{-1}(\pi(B))) \quad (\text{정칙/σ-유한하도록 Carathéodory 확장})
  \]
- 목표 정리(U2): \(\mu_{unobs}\)가 정칙, σ-유한이고, 관측 가능한 집합에 대해 0을 주는 측도임을 증명.
  - 가정: \(\mu\) 정칙, \(\mathcal{F}_{obs}\) 가산 생성, \(\pi\) 가측.

## 2. KM-1~3 (커널–여백–PH 부등식) 가정 블록
- 커널 K: RKHS 커널, bounded/positive definite.
- PH 대상: compact triangulable 집합, 사영/변형은 Lipshitz/bi-Lipschitz 조건.
- 여백/사영 허용 범위: \(\|\mathfrak{M}\|\)와 변형 크기가 \(\varepsilon\) 이하일 때, PH 거리/커널 평가 변화가 \(\delta(\varepsilon)\)로 상계.
- 정리 문장(스켈레톤): KM-1~3 각기 “PH 변화 ≤ f(\|\mathfrak{M}\|, K-bounds, 변형 크기)” 형태로 고정.

## 3. P2~P6 최소 정리 문장 고정
- P2(예: Sparke/Actyon 모노이드/모듈): support 유한/측도 조건 하에서 AddCommMonoid/SMul, support 합집합 보존, margin 병합 보존 정리.
- P3(Actyon/Escalade 안정성): 흐름 f와 사영 \(\Pi_{null}\) 교환, 경계/불변량 보존 정리.
- P4(Dimension 정합성): X_rec 투영/업데이트/독립성 lemma, 차원 구획 교환성.
- P5/P6: (스펙에서 정의된) 추가 정리(예: 시나리오 합성 안정성, AHS 억제 상계 등) 최소 1개씩 정의역/결론/오차 경계 포함한 문장 고정.

## 4. SCD/AHS 가정 블록
- SCD: UEM 라플라시안/리우빌 연산, 압축자 \(C_\lambda\), 비팽창/안정 조건, 에너지 단조 감소 조건.
- AHS: 불안정 방향 Lyapunov exponent와 압축 횟수 \(N(t)\) 상계 \(\|D\varphi_t|_{E^u}\|\cdot \lambda^{N(t)} \le \Gamma\).
- 정리 문장: (존재/유일/안정) + 에너지/거리 상계 정리 최소 1개씩.

## 5. 검증 체크리스트
1) μ_unobs 정의와 정칙/σ-유한성 정리(U2) 가정 명시.  
2) KM-1~3 가정 블록(K 조건, PH compactness, 변형 허용 범위)과 정리 문장 스켈레톤.  
3) P2~P6 각 최소 1개 정리 문장(정의역/결론/오차 경계) 고정.  
4) SCD/AHS 가정 블록과 (존재/유일/안정/상계) 정리 최소 1개씩.  
