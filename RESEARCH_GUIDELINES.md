# UEM 연구 개발 지침 v1.0: 지속적 증명/개발을 위한 가이드
> **목적**: UEM 프로젝트의 지속적인 연구, 개발, 증명 활동을 위한 종합 지침
> **대상**: 모든 UEM 기여자 (개발자, 연구자, 증명자, 학생)
> **원칙**: 철저한 검증, 체계적 접근, 지속적 개선

---

## 1. UEM 연구 철학 및 원칙

### 1.1 핵심 연구 철학
> **"비관측 가능한 것의 인식 가능성을 수학적으로 정형화하고, 여백을 통해 정보의 보존을 증명한다"**

#### 연구 목표
1. **이론적 목표**: 비관측 인식의 수학적 틀 구축
2. **실용적 목표**: 기존 수학으로 해결 불가능한 문제 해결
3. **교육적 목표**: 새로운 수학적 사고방식 제시

#### 연구 원칙
- **보수성**: 기존 수학과 충돌하지 않음
- **일관성**: 내부 논리적 무모순성 유지
- **검증가능성**: 모든 주장은 증명 가능해야 함
- **확장성**: 기존 이론을 확장하는 방향

### 1.2 연구 윤리
- **지적 정직성**: 증명되지 않은 주장 제거
- **개방성**: 모든 과정과 결과를 투명하게 공유
- **협력**: 외부 전문가와 적극적 협력
- **학문적 책임**: 수학 공동체에 기여

---

## 2. 증명 중심 개발 방법론

### 2.1 증명 우선 원칙 (Proof-First Development)

#### 개발 단계
```
1. 정의 명확화 (Clear Definition)
   ↓
2. 명제 공식화 (Proposition Formalization)
   ↓
3. 증명 전략 수립 (Proof Strategy)
   ↓
4. Lean 4 형식화 (Formalization)
   ↓
5. 동료 검증 (Peer Review)
   ↓
6. 문서화 (Documentation)
```

#### 증명 품질 기준
- **완전성**: 모든 논리적 단계 포함
- **엄밀성**: 암묵적 가정 없음
- **가독성**: 다른 사람이 이해 가능
- **재사용성**: 일반화된 증명 패턴

### 2.2 증명 전략 수립 가이드

#### 단계별 증명 계획
```lean
-- 예시: P3_ActyonStability 증명 전략

-- 1. 정의 명확화
variable {S : Type} [AddCommMonoid S]
variable (f : S → S) (Π_null : S → S)

-- 2. 핵심 명제 공식화
theorem flow_projection_commutation
  (h_comm : ∀ x, Π_null (f x) = f (Π_null x)) :
  Π_null ∘ f = f ∘ Π_null := by
  -- 3. 증명 전략: 함수 확장성 사용
  ext x
  simp [h_comm]

-- 4. 보조 정리
lemma projection_idempotent
  (h_idem : Π_null ∘ Π_null = Π_null) :
  ∀ x, Π_null (Π_null x) = Π_null x := by
  simp [h_idem]
```

#### 증명 기법 분류
1. **구조적 증명**: 자료구조 활용
2. **귀납적 증명**: 자연수/구조적 귀납
3. **대수적 증명**: 대수적 성질 활용
4. **위상적 증명**: 위수/연속성 활용
5. **분석적 증명**: 극한/수렴성 활용

### 2.3 Lean 4 증명 모범 사례

#### 증명 작성 표준
```lean
namespace UEM

/--
## P3: Actyon/Escalade 흐름과 여백 사영의 교환성

정리: 흐름 f와 여백 사영 Π_null이 교환 가능할 필요충분조건은
f가 keep 공간에서만 정의된다는 것이다.

주요 전략: 함수 확장성(axiom ext)과 사영의 직합 분해 활용
-/
theorem flow_projection_commutation_iff
  {V_keep V_null : Type}
  [AddCommMonoid V_keep] [AddCommMonoid V_null]
  (f : V_keep ⊕ V_null → V_keep ⊕ V_null)
  (Π_null : V_keep ⊕ V_null → V_keep) :

  -- Main equivalence statement
  Π_null ∘ f = f ∘ Π_null ↔
    ∃ f_keep : V_keep → V_keep,
      ∀ v_keep v_null, f (v_keep, 0) = (f_keep v_keep, 0) := by

  -- Proof structure
  {
    -- Forward direction (→)
    intro h_comm
    -- Construct f_keep from f
    use fun v_keep => (f (v_keep, 0)).1
    intro v_keep v_null
    -- Show f preserves null component
    have h_null : (f (v_keep, v_null)).2 = 0 := by
      calc (f (v_keep, v_null)).2
        = (Π_null (f (v_keep, v_null))).2   -- by definition of Π_null
        _ = (f (Π_null (v_keep, v_null))).2 -- by h_comm
        _ = (f (v_keep, 0)).2               -- by definition of Π_null
        _ = 0                              -- by hypothesis
    simp [h_null]

    -- Backward direction (←)
    rintro ⟨f_keep, h_f⟩
    -- Show commutation using f_keep
    ext ⟨v_keep, v_null⟩
    calc Π_null (f (v_keep, v_null))
      = Π_null (f_keep v_keep, 0)    -- by h_f and Π_null definition
      = f_keep v_keep               -- by Π_null definition
      = f (v_keep, 0)              -- by h_f
      = f (Π_null (v_keep, v_null)) -- by Π_null definition
  }

end UEM
```

---

## 3. 개발 표준 및 가이드라인

### 3.1 코드 품질 표준

#### Lean 4 코딩 규칙
```lean
-- ✅ 좋은 예시
namespace UEM.Projection

variable {V : Type} [AddCommMonoid V]

/--
논리적 설명:
여백 사영의 핵심 원리를 설명한다.
이 정리는 사영의 기본적 성질을 증명한다.

의존성: P1_NullProjection의 결과 활용
-/
theorem projection_linearity
  (Π_null : V → V)
  (h_linear : IsLinearMap Π_null) :
  ∀ x y, Π_null (x + y) = Π_null x + Π_null y := by
  -- 증명의 각 단계에 주석 추가
  have h_add := h_linear.map_add x y
  simp [h_add]

-- ❌ 나쁜 예시
theorem bad_theorem (f : V → V) : f (x + y) = f x + f y := by
  sorry  -- 금지: 설명 없는 sorry
```

#### 명명 규칙
```lean
-- ✅ 좋은 명명
def margin_log                -- 명확한 용어
theorem projection_idempotent -- 직관적 명명
variable {V_keep V_null}       -- 의미있는 변수명

-- ❌ 나쁜 명명
def ml                      -- 약어 금지
theorem thm1              -- 의미없는 숫자
variable {A B C D}        -- 일반적 변수
```

### 3.2 문서화 표준

#### 주석 가이드라인
```lean
/-!
# UEM.Objects.Sparke

Sparke 객체는 UEM에서 가장 기본적인 단위 객체이다.
Tensor(n)를 support와 margin으로 확장한 구조이다.

## 주요 정의
- `Sparke`: 단위 spar 객체
- `AddCommMonoid`: 덧셈 모노이드 구조
- `support`: 시간적 지지 집합
- `margin`: 여백 정보 로그

## 주요 정리
- `sparke_add_comm`: 덧셈의 교환법칙
- `support_union`: support의 합집합 보존

## 사용 예시
```lean
def s1 : Sparke ℝ := ⟨3, {0, 1}, []⟩
def s2 : Sparke ℝ := ⟨5, {1, 2}, []⟩
#eval s1 + s2  -- 결과: ⟨8, {0, 1, 2}, []⟩
```
-/

/--
단위 spar 객체 정의

* `X`: Tensor(n) 타입의 값
* `support`: 이 spar가 활성화된 시간 집합
* `margin`: 여백 정보 로그

주의: support는 항상 유한 집합이어야 한다.
-/
structure Sparke (Val : Type) [AddCommMonoid Val] where
  X : Val
  support : Set ℕ  -- 시간 인덱스
  margin : MarginLog
```

### 3.3 테스트 표준

#### 증명 테스트
```lean
-- tests/SparkeTest.lean
import UEM.Objects.Sparke
import UEM.Theorems.P2_SparkeMonoid

namespace UEM.Test

/--
Sparke 덧셈의 기본 성질 테스트

이 테스트는 P2_SparkeMonoid의 결과를 검증한다.
-/
example "Sparke 덧셈 교환법칙" :
  let s1 := ⟨3, {0, 1}, []⟩
  let s2 := ⟨5, {1, 2}, []⟩
  s1 + s2 = s2 + s1 := by
    simp [Sparke.add_comm]

example "support 합집합 보존" :
  let s1 := ⟨3, {0, 1}, []⟩
  let s2 := ⟨5, {2, 3}, []⟩
  (s1 + s2).support = {0, 1, 2, 3} := by
    simp [Sparke.support_add]

end UEM.Test
```

---

## 4. 협업 및 검증 절차

### 4.1 동료 검토 (Peer Review) 절차

#### 코드 리뷰 체크리스트
```markdown
## UEM 코드 리뷰 체크리스트

### 논리적 검증
- [ ] 정의가 명확하고 일관적인가?
- [ ] 증명의 각 단계가 타당한가?
- [ ] 엣지 케이스가 모두 고려되었는가?
- [ ] 타입 일치성이 보장되는가?

### 기술적 검증
- [ ] Lean 4 문법이 올바른가?
- [ ] 성능 최적화가 필요한가?
- [ ] 재사용 가능한 코드 패턴인가?
- [ ] 테스트 케이 충분한가?

### 문서화 검증
- [ ] 주석이 충분하고 명확한가?
- [ ] 사용 예시가 포함되었는가?
- [ ] 관련 문서 링크가 있는가?
- [ ] 기여자 정보가 기록되었는가?
```

#### 검토 프로세스
```bash
#!/bin/bash
# scripts/peer_review.sh

PR_NUMBER=$1
REVIEWER=$2

echo "PR #$PR_NUMBER 리뷰 시작 (Reviewer: $REVIEWER)"

# 1. PR 정보 확인
echo "PR 정보:"
gh pr view $PR_NUMBER --json title,body,author

# 2. 변경 파일 확인
echo "변경된 파일:"
gh pr diff $PR_NUMBER --name-only

# 3. 자동화 검증
echo "자동화 검증 실행..."
bash scripts/verify_proofs.sh
bash scripts/test_coverage.sh

# 4. 리뷰어 할당
echo "리뷰어 지정..."
gh pr edit $PR_NUMBER --add-reviewer $REVIEWER

# 5. 검토 코멘트 템플릿
cat <<EOF > review_comment.md
## UEM 코드 리뷰 PR #$PR_NUMBER

### 논리적 검토
- [ ] 정의 명확성
- [ ] 증명 완전성
- [ ] 타입 안정성

### 기술적 검토
- [ ] Lean 문법
- [ ] 성능 고려
- [ ] 테스트 커버리지

### 문서화 검토
- [ ] 주석 충분성
- [ ] 사용 예시
- [ ] 관련 링크

### 총평
[ ] 승인 (Approve)
[ ] 변경 요청 (Request Changes)
EOF

gh pr comment $PR_NUMBER --body-file review_comment.md
```

### 4.2 협업 도구 및 플랫폼

#### GitHub 워크플로우
```yaml
# .github/workflows/collaboration.yml
name: UEM Collaboration Process

on:
  pull_request:
    branches: [main, develop]
  issue_comment:
    types: [created]

jobs:
  review:
    if: github.event_name == 'pull_request'
    runs-on: ubuntu-latest
    steps:
      - name: Auto Review
        run: |
          # 자동화 검증
          bash scripts/verify_proofs.sh

          # 리뷰어 자동 할당
          if [[ $GITHUB_ACTOR != "project-lead" ]]; then
            gh pr edit ${{ github.event.number }} --add-reviewer "lead-prover"
          fi

  discussion:
    if: github.event_name == 'issue_comment'
    runs-on: ubuntu-latest
    steps:
      - name: Process Discussion
        run: |
          # 토론 태그 분석
          comment_body=$(jq -r '.comment.body' $GITHUB_EVENT_PATH)

          if [[ $comment_body == *"question"* ]]; then
            gh issue edit ${{ github.issue.number }} --add-label "question"
          elif [[ $comment_body == *"proof"* ]]; then
            gh issue edit ${{ github.issue.number }} --add-label "proof-help"
          fi
```

---

## 5. 학생 및 신규 기여자 가이드

### 5.1 온보딩 절차

#### 1단계: 기초 교육 (1주)
```markdown
## UEM 온보딩 Week 1

### Day 1-2: UEM 소개
- [ ] 철학적 배경 학습 (`docs/philosophy/UEM_DECLARATION_ORIGINAL.md`)
- [ ] 핵심 개념 이해 (`UEM_MASTER_COMPLETE_v1.0.md` 1-3장)
- [ ] 기존 수학과의 차이점 파악

### Day 3-4: Lean 4 기초
- [ ] Lean 4 설치 및 설정
- [ ] 기본 문법 학습 (타입, 함수, 증명)
- [ ] 간단한 정리 증명 연습

### Day 5-7: UEM 구조 학습
- [ ] 객체 계층 이해 (Tensor → Sparke → Actyon → Escalade → Secare)
- [ ] 증명된 P1, P2 분석
- [ ] 간단한 증명 시도
```

#### 2단계: 실습 과제 (2주)
```lean
-- exercises/basic_exercises.lean
import UEM.Objects.Sparke
import UEM.Theorems.P1_NullProjection

namespace UEM.Exercise

/--
연습 1: Sparke의 덧셈 항등원 증명
-/
example : ∀ s : Sparke ℝ, s + 0 = s := by
  -- 힌트: AddCommMonoid의 zero_add 사용
  sorry

/--
연습 2: 여백 사영의 선형성 증명
-/
example
  (Π_null : ℝ → ℝ)
  (h_linear : ∀ a b x, Π_null (a * x + b) = a * Π_null x + b) :
  ∀ x y, Π_null (x + y) = Π_null x + Π_null y := by
  -- 힌트: 선형성 정의 활용
  sorry

end UEM.Exercise
```

### 5.2 연구 주제 제안

#### 입문용 연구 주제
1. **차원 독립성 증명**: 9차원 간 독립성 lemma 증명
2. **Sparke 성질 확장**: AddCommMonoid 이외의 대수 구조
3. **간단 한글 연산자**: 기본 C/V/F 조합의 수학적 성질
4. **여백 로그 최적화**: 효율적인 margin 로그 데이터구조

#### 중급 연구 주제
1. **P3-P4 정리 증명**: 흐름-사영 교환, 차원 정합성
2. **한글 연산자 LUT 완성**: 모든 C/V/F 조합 매핑
3. **KM-1 부등식**: 커널-여백-PH 관계 증명
4. **객체 계층 승격**: rank/axis 보존 증명

#### 고급 연구 주제
1. **UEM↔ZFC 라운드트립**: 보수성/무모순성 증명
2. **고차 한글 연산자**: 복잡한 조합의 대수 구조
3. **실제 응용**: 물리/논리 문제의 UEM 해석
4. **교육 시스템**: UEM을 위한 교육 도구 개발

### 5.3 멘토링 시스템

#### 멘토-멘티 매칭
```yaml
# mentoring/assignments.yaml
mentoring_pairs:
  - mentor: "senior_developer1"
    mentees: ["student1", "student2"]
    focus: "Lean proofs and Sparke theory"
    meeting_schedule: "weekly Tuesday 2pm"

  - mentor: "lead_prover"
    mentees: ["junior_developer1"]
    focus: "Advanced proof techniques"
    meeting_schedule: "biweekly Friday 3pm"
```

#### 멘토링 체크리스트
```markdown
## 월간 멘토링 체크리스트

### 멘티 진행 상황
- [ ] 이번 주 목표 달성 여부
- [ ] 기술적 장애 현황
- [ ] 필요한 추가 자료/도움

### 멘토 지원 사항
- [ ] 코드 리뷰 완료 여부
- [ ] 기술적 가이드 제공
- [ ] 다음 주 계획 수립

### 학습 목표
- [ ] 이번 주 학습 내용
- [ ] 다음 주 학습 계획
- [ ] 장기 목표 진행 상황
```

---

## 6. 지속적 개선 및 피드백

### 6.1 피드백 수집 시스템

#### 정기적 피드백
```markdown
## 분기별 프로젝트 피드백

### 개발 효율성
- [ ] 증명 속도 만족도 (1-5점)
- [ ] 코드 품질 만족도 (1-5점)
- [ ] 문서화 충분성 (1-5점)

### 협업 효과성
- [ ] 의사소통 효율성 (1-5점)
- [ ] 리뷰 프로세스 만족도 (1-5점)
- [ ] 도구/환경 충분성 (1-5점)

### 개인 발전
- [ ] 기술적 성장 정도
- [ ] 학습 기회 충분성
- [ ] 경력 개선 기회
```

#### 기술적 피드백
```bash
#!/bin/bash
# scripts/technical_feedback.sh

echo "UEM 기술적 피드백 수집..."

# 1. 증명 복잡도 분석
echo "증명 복잡도:"
find formal -name "*.lean" -exec wc -l {} \; | sort -n

# 2. 의존성 분석
echo "의존성 그래프:"
lake env print-deps

# 3. 성능 벤치마크
echo "빌드 성능:"
time lake build UEM

# 4. 테스트 커버리지
echo "테스트 커버리지:"
lake test --coverage
```

### 6.2 개선 프로세스

#### retrospective 템플릿
```markdown
## UEM 스프린트 Retrospective

### 시작 잘된 점
-
-

### 개선할 점
-
-

### 행동 약속
- [ ] 다음 스프린트에서 시도할 것
- [ ] 중단할 것
- [ ] 계속할 것
- [ ] 시작할 것

### 우선순위 결정
1. **즉시 실행**:
2. **다음 스프린트**:
3. **장기 계획**:
```

이 연구 개발 지침을 통해 UEM 프로젝트의 모든 기여자가 체계적으로 협력하고 지속적으로 발전할 수 있을 것입니다.