# 정리 문장 고정집 (증명만 하면 되는 상태로)

> 각 모듈별 최소 정리 문장을 명시한다. 가정 블록을 적어두고, 증명은 별도 진행.

## 관측/비관측 · 커널–여백
- 관측 표현 정리 (A.3):  
  가정: \((\Omega,\mathcal{F},\mu)\), 가산 생성 \(\mathcal{F}_{obs}\subseteq\mathcal{F}\), \(\pi:\Omega\to\Omega_{obs}\) 정의.  
  결론: \(\exists \mathcal{G}\) s.t. \(\mathcal{F}_{obs} = \pi^{-1}(\mathcal{G})\) (측도 공간 동형 포함).
- 분해 정리 (A.5): \(\Omega = \bigsqcup_{z} \pi^{-1}(\{z\})\), \(A\in\mathcal{F}\Rightarrow A=\bigcup_z (A\cap \pi^{-1}(\{z\}))\).
- 커널–여백 피타고라스 (B.1): Hilbert \(H\), 사영 \(P\): \(|x|^2=|Px|^2+|(I-P)x|^2\).
- 사영-연산자 상호작용 (B.2): 유계선형 \(T\), \(TP=PT\): \(E(Tx)\le |T|^2E(x),\ M(Tx)\le |T|^2M(x)\).

## 텐서/객체 계층 · 세카레 축
- 랭크 승격/투영 교환: 동일 랭크에서 덧셈/스케일 보존, 승격/투영과 support/margin 병합 교환 조건 명시.  
- 축 보존/변환: 병합/분기/사영/flow에서 Axis(inner_gap, unobserved 등)가 일관되게 전파/변환됨.

## 한글 연산자(Γ)
- Γ-Total/Type/NF/Closed/Consv: FOL 문장으로 고정(재작성/병렬/중첩 후 타입 보존, 정규형 존재, 보수성).  
- Church–Rosser/종료성: 재작성 규칙 조건 하에 합류/종료(또는 표준형 수렴) 정리.

## μ_unobs · KM-1~3 · P2~P6 · SCD/AHS
- μ_unobs 정칙/σ-유한성(U2).  
- KM-1~3: PH 변화 ≤ f(‖M‖, K-bounds, 변형 크기) 가정/결론 명시.  
- P2~P6: 각 최소 1개 정리(정의역/결론/오차 경계).  
- SCD/AHS: 존재/유일/안정, Lyapunov-압축 상계 정리.

## 고교/전통 동치
- 문제 유형별(연속/미분/극값/부등식/삼각/수열/급수) “기존 풀이 ↔ UEM+한글연산자 풀이” 동치 정리, 정의역 필터 조건 포함.  
- HS 서브셋 종료성/합류/타입 보존 정리.

## 라운드트립
- Soundness: \(\vdash_{UEM}\varphi \Rightarrow \vdash_{ZFC} I_{U\to Z}(\varphi)\).  
- Round-trip truth: \(I_{Z\to U}(I_{U\to Z}(\varphi))\) ⇔ \(\varphi\) (적절한 동치).  
- (선택) Completeness 약형.
