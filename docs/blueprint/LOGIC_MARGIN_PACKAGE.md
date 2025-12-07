# 여백·논리공간·논리차원 패키지 (정의 고정안)

> 목표: 여백‧논리‧기하를 수학적으로 명확히 모델링하여, “증명만 하면 되는” 상태로 끌어올린다.  
> 사용: 관측/비관측 사영, 논리적 분기(가능세계), 여백 측도·노름·차원, 삼중 결합 정리의 가정 블록으로 활용.

## 1. 관측/비관측 사영 (기본 설정)
- 관측 공간: 측도공간 \((\Omega,\mathcal{F},\mu)\), 관측 가능한 σ-대수 \(\mathcal{F}_{obs}\subseteq\mathcal{F}\).
- 관측 동치: \(x\sim y \iff \forall A\in \mathcal{F}_{obs}, [x\in A \Leftrightarrow y\in A]\).
- 관측 사영: \(\pi:\Omega\to \Omega_{obs}:=\Omega/\sim\), \(\mathcal{G}\) = \(\sigma\)-algebra on \(\Omega_{obs}\) s.t. \(\mathcal{F}_{obs}=\pi^{-1}(\mathcal{G})\) (가산 생성 가정 시 표준 곱 공간에 매입 가능).
- 비관측 파이버: \(N_z := \pi^{-1}(\{z\})\), 여백 전체 \(\mathcal{N}:=\{N_z : z\in\Omega_{obs}\}\).

## 2. 여백 공간 \(\mathfrak{M}(P)\)
- 정의: 주어진 사영 \(P\)에 대해 \(\mathfrak{M}(P)\)는 “관측 실패/여백”을 담는 σ-대수/측도 공간.  
  - 보통 \(\mathfrak{M}(P)\)를 \((\Omega, \mathcal{F}\setminus \mathcal{F}_{obs}, \mu_{unobs})\)의 부분 σ-대수/측도 구조로 본다.  
  - \(\mu_{unobs}\)는 \(\mu\)와 \(\pi\)로부터 정의: 예시) \(\mu_{unobs}(B) := \mu(B) - \mu(\pi^{-1}(\pi(B)))\) 또는 Carathéodory 확장으로 정칙/σ-유한하도록 보강.
- 여백 노름: \(\|\mathfrak{M}\| := \mu_{unobs}(\Omega)\) 또는 적합한 \(L^p\)-norm(여백 밀도 기준).  
- 여백 차원: 기하 차원(Hausdorff 등) vs 논리 차원(가능세계 분기 수, modal depth)을 구분 정의.

## 3. 논리공간/논리차원 (Kripke 프레임 결합)
- 관찰자 상태 집합 \(W\), 접근 관계 \(R\subseteq W\times W\), 평가 함수 \(V: \text{Prop}\to \mathcal{P}(W)\).
- 논리 차원 수: 예) 분기 정도/독립 관찰 방향 개수/모달 깊이.  
  - 모달 깊이 md(\(\varphi\)) 또는 R-분기수의 상계 등을 “논리 차원”의 정량으로 사용.  
  - 여백과 논리 차원의 중첩: “여백이 많은 논리 방향” = R-분기 중 관측 불가 이벤트 비율을 여백 노름과 결합해 정의.
- UEM 관측 공간과 결합: \(\Omega_{obs}\)와 W를 짝지어, \(\pi: \Omega\to \Omega_{obs}\)와 \((W,R,V)\)를 동시에 고려하는 프레임 \((\Omega_{obs}\times W, \mathcal{G}\otimes \mathcal{P}(W), R, V\circ \text{proj}_W)\).

## 4. 여백–논리–기하 삼중 결합 (정리 목표 스켈레톤)
- 목표 정리(형식화 필요): 논리적 분기(가능세계)가 바코드/PH 혹은 여백 노름에 미치는 영향에 대한 상계.  
  - 예시 형태: 논리 분기수 \(b\)와 여백 노름 \(\|\mathfrak{M}\|\)이 작을 때, 관측/비관측 사영 후의 위상 변화(또는 커널–여백–PH 값)가 \(\varepsilon(b,\|\mathfrak{M}\|)\)로 상계됨.  
  - Assumption 블록: \(\Omega\) compact/triangulable, \(\pi\) 가측/측도 보존/리프팅 가능, \(R\) 정칙성(반사/추이/대칭 여부 명시).

## 5. 사용 지침 (Lean/문서)
- 문서: 본 정의를 여백/논리/차원 패키지의 기준으로 사용, KM/μ_unobs/PH/논리 결합 정리에 가정 블록으로 삽입.  
- 코드: \(\pi\), \(\mathcal{F}_{obs}\), \(\mu_{unobs}\)를 명시적 파라미터로 가지는 구조체를 정의하고, 피타고라스/사영 정리와 연계.  
- 검증 체크리스트:  
  1) \(\mathcal{F}_{obs}=\pi^{-1}(\mathcal{G})\) 가측성,  
  2) \(\mu_{unobs}\) 정칙/σ-유한성,  
  3) 논리 차원/여백 차원 정의 구분,  
  4) 삼중 결합 정리의 가정(regularity/compactness/R-성질) 명시.
