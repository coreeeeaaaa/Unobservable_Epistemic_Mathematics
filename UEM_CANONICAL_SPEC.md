# UEM Canonical Spec (정본) v1.0 — Pure Math Core

이 문서는 **UEM의 유일한 정본**이다.  
**헌법(UEM_CONSTITUTION.md)**을 준수하며, Lean 코드와 상충할 수 없다.

---

## 0. 정본 원칙
- 순수 수학/형식 논리만 포함
- 객체(Type)와 연산자(Operator) 엄격 분리
- “증명됨” 표기는 Lean 커널 검증 결과만 허용
- 외부 권위 인용 금지
- 물리/시스템/프로그래밍 적용은 정본 밖이며 증명 단계에 포함하지 않음

---

## 0.1 선언문(Declaration)의 정식화 원칙
- 선언문은 **정의/정리/추측**으로 변환된 항목만 정본에 포함한다.
- 서사/문학/메타 서술은 **비정본**이며 증명 근거로 사용하지 않는다.
- 선언문에서 요구되는 정식화 항목은 다음 문서에 명시한다:  
  `UEM-PROJECT-DOCS/UEM_DECLARATION_FORMALIZATION_SPEC.md`

## 1. 기반 체계 (Foundational Core)
### 1.1 World / Observer / Kernel
- `World := Type u`
- `Observer` 타입클래스:
  - `observe : O → ObsObject`
  - `kernel : O → O → Prop`
  - `kernel_spec : kernel x y ↔ observe x = observe y`
- **정리(Lean 증명)**: `kernel`은 동치관계

### 1.2 Thickness (두께)
- 두께는 **OuterMeasure**로 정의
- `ThicknessBasis.outerMeasure : OuterMeasure α`
- `thickness : Set α → ℝ≥0∞`
- **정리(Lean 증명)**: OuterMeasure 공리 만족

> 관련 Lean 소스:
> - `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Foundations.lean`

---

## 2. 객체 계층 (Objects as Types)
### 2.1 관측계 객체
- `Scalar : Type`
- `Vector : Nat → Type`
- `Tensor : Nat → Type`

### 2.2 비관측계 객체
- `Spark : Type` (⛦)
- `Actyon : Type` (ㆁ)
- `Escalade : Type` (𓂌)
- `Secare : Type` (♡)

### 2.3 메타 객체
- `WorldData : Type`
- `ObserverData : Type`
- `MarginData : Type`
- `PossibleWorld : Type`
- `Descriptor : Type`

> 관련 Lean 소스:
> - `UEM_Lean4_Proofs/UemProofs/UEM/UEM_Calculus.lean`

---

## 3. 연산자 계층 (Operators)
모든 연산자는 **도메인 → 코도메인**이 고정된 함수다.

### 3.1 코어 연산자 시그니처
- `CreateSpark : World → Spark`
- `Ignite : Spark → Actyon`
- `Escalate : Actyon → Nat → Escalade`
- `Collapse : Escalade → Secare`

### 3.2 연산자 구조
- `Operator` : `Carrier a → Carrier b`
- 합성: `Operator.comp`
- 병렬: `Operator.par`

---

## 4. 한글 연산자 체계 (Hangul Calculus)
### 4.1 자모 구조
- `Choseong`, `Jungseong`, `Jongseong`
- `Syllable := (C, V, F?)`

### 4.2 타입 매핑
- `CMap : ObjType → ObjType → Prop`
- `VMap : ObjType → ObjType → Prop`
- `FMap : ObjType → ObjType → Prop`
- 합성은 반드시 **C → V → F** 순서

### 4.3 연산항(자모 합성)
- `OpTerm`으로 타입 안전한 합성 보장

### 4.4 연산자 행렬 (C/V/F Matrix)
- 모든 음절은 (C,V,F?)에 의해 **분류(classification)**된다.
- `UEM_HangulMatrix.lean`은 다음을 제공한다:
  - CClass/VClass/FClass
  - `MatrixRel : Syllable → ObjType → ObjType → Prop`
  - **총분류(total classification)** 보조정리
- 이 행렬은 **정의적 관계**이며, 구체 CMap/VMap/FMap의 보조 근거로 사용된다.

---

## 5. 슬롯/큐브 구조
### 5.1 좌표
- `Coord side height depth := Fin side × Fin side × Fin height × Fin depth`

### 5.2 Slot
`Slot`은 다음을 포함한다:
- `coord : Coord`
- `glyph : Syllable`
- `payload : UEMEntity` (객체/연산자 분리)
- `dir : Direction`
- `dim : Dimension`
- `meta : Meta`

### 5.3 Cube
- Cube는 Slot들의 집합
- **정리(Lean 증명)**: 3×3=9, 3×3×3=27

---

## 6. 정리(Lean 증명 완료)
1. `kernel` 동치관계
2. `thickness` OuterMeasure 공리
3. 좌표 카드inality (3×3, 3×3×3)
4. **UEM 객체/연산자는 범주(Category)를 이룬다** (`ObjType` with `Operator`)

---

## 7. 확장 모듈 (정본 외 Extension)
다음은 정본 밖에서 Extension으로만 추가한다.
- 여백–중첩 기하학 (⊙)
- 차원축소 사영기하학 (Π, D_Π)
- SCD
- AHS
- Γ-calculus 정규화/정합성

Extension은 반드시 “Conjecture/Definition”으로 표기하며, Lean 증명 완료 후 정본 편입을 검토한다.

---

## 8. 정본 충돌 규칙
- 정본과 코드가 충돌하면 **코드가 우선**이다.
- 정본 문서 갱신은 반드시 Progress Log에 기록한다.

---

## 9. 버전 정책
- v1.0: 코어 정의 확정 + 핵심 정리 Lean 증명 완료
- v1.x: Extension 증명 확장
- v2.0: 코어 정의 변경 시 별도 계열로 분리

---

## 10. 정본 파일
- `UEM_CONSTITUTION.md`
- `UEM_CANONICAL_SPEC.md`
- `UEM_Lean4_Proofs/UemProofs/UEM/*.lean`
- `UEM_Lean4_Proofs/UEM_PROGRESS.md`
