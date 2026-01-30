# UEM 헌법 (UEM Constitution) v1.0

본 문서는 **UEM(비관측 인식 수학)**의 최상위 규범이다.  
이 문서가 모든 정의/증명/구현의 **유일한 규범(Constitution)**이며,  
정의 충돌·버전 난립·과장 선언을 **원천 차단**한다.

---

## 제0조: 목적과 범위
1. UEM은 **순수 수학/형식 논리 체계**로서만 정의된다.
2. 응용/철학/예언/난제 해결 선언은 **정본에 포함되지 않는다**.
3. 모든 명제는 다음 중 하나로만 기술된다.
   - **Definition** (정의)
   - **Theorem** (Lean 검증 완료)
   - **Conjecture** (미증명, 명확히 표기)
4. 물리/시스템/프로그래밍 확장은 **증명 단계에 포함되지 않으며** 별도 레벨에서 다룬다.

---

## 제1조: 기반 논리와 우주
1. UEM의 공식 언어는 **Lean 4 의존형 타입이론**이다.
2. 논리적 기본은 Lean kernel에 의해 검증된다.
3. **새 공리 추가는 금지**한다. (필요 시 Extension 모듈로 격리)
4. **World는 타입**으로 정의한다:
   - `World := Type u`

---

## 제2조: 객체(Types)와 연산자(Operators)의 분리
1. 객체는 타입이며, 연산자가 아니다.
2. 연산자는 **도메인/코도메인이 고정된 함수**다.
3. 객체 목록(코어):
   - Observed: `Scalar`, `Vector n`, `Tensor k`
   - Epistemic: `Spark(⛦)`, `Actyon(ㆁ)`, `Escalade(𓂌)`, `Secare(♡)`
   - Meta: `WorldData`, `ObserverData`, `MarginData`, `PossibleWorld`, `Descriptor`
4. 연산자 목록(코어 시그니처):
   - `CreateSpark : World → Spark`
   - `Ignite : Spark → Actyon`
   - `Escalate : Actyon → Nat → Escalade`
   - `Collapse : Escalade → Secare`

---

## 제3조: 관측자와 커널
1. Observer는 타입클래스로 정의한다:
   - `observe : O → ObsObject`
   - `kernel : O → O → Prop`
2. 커널의 정의는 관측 사영과 동치여야 한다:
   - `kernel x y ↔ observe x = observe y`
3. 커널은 **동치관계**여야 한다. (Lean 증명 필수)

---

## 제4조: 두께(Thickness)
1. 두께는 **외측측도(OuterMeasure)**로 정의한다.
2. `ThicknessBasis`를 통해 `OuterMeasure.ofFunction`으로 구성한다.
3. 두께는 **직관/비유가 아니라 엄밀한 측도론 객체**여야 한다.

---

## 제5조: 한글 연산자 체계 (Hangul Calculus)
1. 한글 음절은 **초성(C) + 중성(V) + 종성(F)**의 합성이다.
2. 합성 순서는 **C → V → F**로 고정한다.
3. 타입 매핑은 관계(`CMap/VMap/FMap`)로 정의한다.
4. 잘 타입된 조합만 연산 가능하다.

---

## 제6조: 큐브/슬롯 구조
1. 좌표는 유한형 `Fin` 기반으로 정의한다.
2. Slot은 **좌표 + 음절 + 역할 + 메타**를 포함한다.
3. Cube는 Slot들의 집합이다.
4. 좌표 카드inality 정리는 Lean에서 증명되어야 한다.

---

## 제7조: 확장 모듈 정책
다음 분과는 **Extension 모듈**로 분리한다.
- 여백–중첩 기하학 (⊙)
- 차원축소 사영기하학 (Π, D_Π)
- SCD (안정적 압축 동역학)
- AHS (반쌍곡 구조)

Extension 모듈은 다음 요건을 충족해야 한다.
1. 코어 정의를 수정하지 않는다.
2. 추가되는 공리/가정은 명시한다.
3. Lean 증명 완료 전에는 Theorem으로 승격하지 않는다.

---

## 제8조: 증명 정책
1. “증명됨” 표시는 **Lean에서 `--no-sorry` 통과한 정리**만 허용.
2. Lean에 없는 증명은 모두 Conjecture로 표기한다.
3. 권위 인용(인물/수상자/뉴스)을 증명 근거로 사용하지 않는다.

---

## 제9조: 버전 정책
- **v1.0**: 코어 정의 확정 + 코어 정리 Lean 증명 완료
- **v1.x**: Extension 모듈 증명 추가
- **v2.0**: 코어 정의 변경은 불가. 변경은 새로운 계열로 분리

---

## 제10조: 정본 파일과 변경 기록
정본 파일:
- `UEM_CANONICAL_SPEC.md` (정의/구조의 상세 명세)
- `UEM_Lean4_Proofs/UemProofs/UEM/*.lean` (형식 검증 소스)
- `UEM_Lean4_Proofs/UEM_PROGRESS.md` (작업 연속성 기록)

모든 변경은 **Progress Log에 기록**해야 한다.

---

## 부칙 (즉시 발효)
본 헌법 v1.0은 작성 즉시 효력을 가진다.  
본 문서에 반하는 모든 선언/정의/문서는 **비정본**이다.
