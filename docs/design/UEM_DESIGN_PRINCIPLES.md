# UEM Design Principles & Philosophy Mapping
(UEM 설계 원칙 및 철학-시스템 매핑)

> 이 문서는 UEM의 존재론적/인식론적 철학을 실제 시스템 설계(수학적 공리, 데이터 구조, 알고리즘)로 변환하는 **매핑 규칙**을 정의한다.

---

## 1. 존재와 여백 (Ontology & Margin)

### 철학적 원칙
- **"존재를 말하려면 없음을 인식해야 한다."**
- **"기록되지 않아도 기록 속에 남아있는 정합성."**
- 표현된 것($E$)은 빙산의 일각이며, 표현되지 않은 의미($M_{semantic}$)가 본질을 지탱한다.

### 시스템 매핑 (Implementation)
1.  **보존 공리 (Conservation Axiom)**
    - 시스템 내의 총 정보량(Information Content)은 보존된다.
    - $I(Total) = I(E) + I(M)$
    - $E$에서 사라진 정보는 반드시 $M$으로 이동해야 하며, 소멸(Deletion)은 허용되지 않는다.
    - **구현**: `to_margin(S, context)` 연산은 `D`에서 제거된 정보를 `M`에 append 하는 원자적(Atomic) 트랜잭션이어야 한다.

2.  **비관측 측도 (Unobservable Measure)**
    - $\mu_{unobs}(M)$은 단순한 '크기'가 아니라, **의미론적 엔트로피(Semantic Entropy)**를 나타낸다.
    - **구현**: `M`은 단순 집합이 아니라 `(Source, Context, Value)` 튜플의 로그(Log) 구조를 갖는다.

---

## 2. 인지적 한계와 비용 (Cognitive Limit & Cost)

### 철학적 원칙
- **"선형적 언어는 사고를 다운그레이드한다."**
- **"하기 싫음, 자원 제약은 존재의 조건이다."**
- 무한한 사고를 유한한 자원(CPU, Memory, Time)과 선형적 서술(Text)로 압축할 때 손실이 발생한다.

### 시스템 매핑 (Implementation)
1.  **인지 비용 함수 (Cognitive Cost Function)**
    - 모든 연산 $\Gamma$는 비용 $\mathcal{L}_{cog}$를 발생시킨다.
    - $\mathcal{L}_{cog} \propto$ (수식 복잡도, 분기 수, 차원 수).
    - **구현**: 시스템은 매 스텝마다 $\mathcal{L}_{cog}$를 계산하고, 임계값($\theta$)을 초과하면 강제 **차원 축소($\Delta_{UEM}$)** 또는 **여백화**를 트리거한다. (자동 최적화)

2.  **사영 왜곡 (Projection Distortion)**
    - 고차원 사고를 저차원 $E$로 사영할 때 발생하는 왜곡을 추적해야 한다.
    - **구현**: `Dim` 컴포넌트에 `ProjectionHistory`와 `LossMetric`을 포함하여, "얼마나 단순화되었는가"를 정량화한다.

---

## 3. 병렬성과 비선형성 (Parallelism & Non-linearity)

### 철학적 원칙
- **"배와 사과를 동시에 말할 수 없다(선형적 한계)."**
- **"병렬적 사고와 반사실적 사고."**
- 기록은 선형적이어야 하지만, 그 배후의 구조는 초병렬적이어야 한다.

### 시스템 매핑 (Implementation)
1.  **상태 그래프 (Epistemic State Graph)**
    - 상태 $S$는 단일 시점의 스냅샷이 아니라, 가능한 모든 세계(Possible Worlds)의 **DAG(Directed Acyclic Graph)**이다.
    - **구현**: `S` 데이터 구조는 `ActiveBranch` (현재 서술 중인 선형 경로)와 `LatentBranches` (배경에 존재하는 병렬 경로들)를 모두 포함한다.
    - 텍스트 기록은 `ActiveBranch`만 따라가지만, 논리 연산은 `LatentBranches`를 포함한 전체 그래프 위에서 수행된다.

2.  **반사실적 여백 (Counterfactual Margin)**
    - 선택하지 않은 경로(If not...)는 사라지는 것이 아니라 `M`의 `Counterfactual` 파티션에 저장된다.
    - **구현**: `Filter` 연산은 `False` 브랜치를 삭제하는 게 아니라 `Archive` 상태로 전환한다.

---

## 4. 결론

UEM 시스템은 **"사용자의 고차원적 사고"**를 **"저차원적 선형 기록"**으로 변환하는 **손실 압축 코덱(Lossy Compression Codec)**이자, 그 과정에서 손실된 정보를 **여백(Margin)에 보존**하여 원본의 의미를 지키는 **아카이브(Archive)**이다.
