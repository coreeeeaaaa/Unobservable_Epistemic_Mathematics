# UEM Information Object Hierarchy v1.5
(UEM 정보 객체 계층 설계서 - 이원화된 완전 명세 및 메타 인지 공리)

> **Meta-Rule Compliance**: 본 문서는 UEM Meta-Rule에 따라 순수 수학적 정의(Part I)와 응용/실행 모델(Part II)을 엄격히 분리한다.
> 
> **Version 1.5 Changes**:
> - 배제 우선 원칙(Exclusion First) 및 배제 해상도 정의
> - 메타 인식 공리 (6^6 Meta Bound)
> - 연산 분류 함수 (Classify: FORBIDDEN/MEANINGLESS/...)
> - 한계 상태의 내재화 (Undecidable/Overload)

---

# Part I. Pure Theory (순수 이론)

## 1. 기본 전제 및 기호

### 1.1 기저 공간
- **체(Field) $\mathbb{F}$**: 실수 $\mathbb{R}$ 또는 복소수 $\mathbb{C}$.
- **벡터공간 $V$**: $\mathbb{F}$ 위의 유한차원 선형공간.
- **텐서공간 $\mathcal{T}^{(k)}(V)$**: Rank $k$ 텐서 공간.
- **여백 공간 $\mathcal{M}$**: 관측 불가능하거나 무시된 정보들의 집합 (위상 공간의 보수).
- **시간 $T$**: 순서가 있는 집합 (Ordered Set).

### 1.2 UEM 상태 $S$
$$ S = (E, U, M) $$
- $E$: Explicit Data (수식, 값, $V_{keep}$). 
- $U$: Universal Context.
- $M$: Margin (여백).

---

## 2. 정보 객체 계층 (Object Hierarchy)

### 2.1 수학적 객체 정의
1.  **Classic Objects**: Scalar($s$), Vector($\mathbf{v}$), Tensor($T$). 
2.  **Sparke (⛦)**: $\text{⛦} = (X, T, C, M_{spar}, \lambda, \tau)$. $S$의 국소 파편.
3.  **Actyon (ㆁ)**: $\text{ㆁ} = (A, R, W, D, M_{acty})$. Sparke의 유한 집합 $A$와 가중치/역할 구조.
4.  **Escalade (𓂌)**: $\text{𓂌} = (\Phi, \mathcal{T}, \mathcal{P}, M_{escul})$. 상태 전이 함수족 $\Phi$의 동역학.
5.  **Secare (♡)**: $\text{♡} = (S_{sub}, B, \Sigma, M_{seks})$. 부분 공간 $S_{sub}$와 경계 조건 $B$.

### 2.2 대수적 구조
- **Sparke Monoid**: $(\mathcal{S}, \oplus_{spar}, \text{⛦}_0)$는 모노이드를 이룬다.
- **Secare Lattice**: $(\mathcal{C}, \wedge, \vee)$는 격자 구조를 이룬다.

---

## 3. 배제와 한계의 공리 (Axioms of Exclusion & Limits)

### 3.1 배제 우선 원칙 (Exclusion First)
UEM의 최적화 목표는 데이터 해상도($\mathrm{Res}_{data}$)의 극대화가 아니라, **배제 적합성($\mathrm{Fit}_{excl}$)의 극대화**이다.
$$ \text{Objective}: \max \mathrm{Fit}_{excl}(\Pi, S) $$
즉, "무엇을 더 볼 것인가"보다 "무엇을 보지 않아도 되는가($\Pi_{null}$)"를 먼저 결정한다.

### 3.2 메타 인식 공리 (6^6 Meta Bound)
문제 해결을 위한 차원/배제 구조의 재구성(Meta Chain)은 무한하지 않으며, 다음 한계를 갖는다.
1.  **깊이 제한**: 메타 재구성 단계 $k \le 6$.
2.  **폭 제한**: 각 단계의 수정 차원 수 $|\Delta\mathcal{D}| \le 6$.
3.  **한계 도달**: $k=6$에 도달하면 한계 인식 차원 $\ell$이 `Saturation` 상태가 되며, 더 이상의 구조 변경은 금지된다.

### 3.3 연산 분류 함수 (Operation Classification)
모든 연산 $\alpha$는 실행 전 다음 함수에 의해 분류되고 필터링된다.
$$ \mathrm{Classify}(\alpha) \in \{\text{FORBIDDEN, MEANINGLESS, REDUNDANT, IMPOSSIBLE, OK}\} $$
- **OK**가 아닌 연산은 실행되지 않고, 그 사유와 함께 여백 $M$으로 이동한다. (정보 보존)

### 3.4 한계 상태의 내재화
시스템이 해결 불가능한 상태는 오류가 아니라 정당한 상태값이다.
- **Fallback-eligible**: 기존 수학/알고리즘으로 위임 가능.
- **Undecidable/Overload**: 논리적 불완전성이나 자원 한계. $M$에 `Suspended` 상태로 격리.

---

## 4. 연산 및 정리

### 4.1 무력화 사영과 커널 (Nullification & Kernel)
**정의**: $V = V_{keep} \oplus \ker L$ 일 때,
$$ \Pi_{null}(v) = \text{Proj}_{V_{keep}}(v) $$
**정리**: $\Pi_{null}$은 $S$의 정보 총량을 보존하며, 제거된 정보는 $M$으로 전이된다. ($I_{total}$ 불변)

### 4.2 객체 승격과 망각
- Functor $\mathcal{E} : \mathbf{Tensor} \to \mathbf{UEMObj}$ (Embedding)
- Functor $\mathcal{F} : \mathbf{UEMObj} \to \mathbf{Tensor}$ (Forgetful)
- $\mathcal{F} \circ \mathcal{E} = \text{Id}$

---

# Part II. Application & Execution Model (응용 및 실행 모델)

## 5. 시스템 매핑 (System Mapping)

### 5.1 한글 연산자 (Representation)
- 한글 음절 $\sigma$는 UEM 객체의 **표현체(Representation)**이다.
- 매핑 $J(\sigma)$를 통해 수학적 객체로 변환된다.

### 5.2 jiwol-큐브 (Visualization)
- 2D 그리드는 UEM 상태 공간의 **단면(Section)**을 시각화한 모델이다.

---

## 6. 실행 모델 (Execution Model)

> **주의**: 이 섹션은 UEM 수학 체계의 일부가 아니라, 이를 컴퓨터상에서 구현할 때의 **예시 모델**이다.

### 6.1 초병렬 실행 (Concurrency)
- 논리적 병렬성($\otimes_{par}$)을 물리적 스레드/GPU에 매핑한다.
- **Actyon Atomicity**: 구현 상에서 Actyon은 원자적 트랜잭션으로 처리됨을 권장한다.

### 6.2 사고 프로세스 (Reasoning Pipeline)
1.  **Classify**: 연산 분류 및 배제.
2.  **Meta-Check**: 6^6 한계 도달 여부 확인.
3.  **Execute**: OK 연산에 대해 Sparke/Actyon 실행.
4.  **Filter/Nullify**: 결과에서 불필요 정보 여백화.

---

## 7. 결론

UEM은 **Part I**에서 정의된 순수 수학적 체계이며, **Part II**는 이를 현실 세계에 구현하기 위한 모델링이다.
이 구조를 통해 UEM은 특정 기술에 종속되지 않는 **보편적 인식 수학**으로서의 지위를 갖는다.