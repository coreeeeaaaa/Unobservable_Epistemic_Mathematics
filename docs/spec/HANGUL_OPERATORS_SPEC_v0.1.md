# Hangul Operators Specification v0.1 (UEM용 한글 연산자 스펙)
> 목적: UEM에 최적화된 한글 연산자(초/중/종/위치)와 초병렬 연산(⊗_par, ∇_hangul)을 표·규칙·검증 기준까지 포함한 스펙으로 고정한다.  
> 상태: v0.1 스켈레톤 — 표/규칙/검증 항목을 명시하고, 이후 채워 넣는다. (축약 금지)

## 0. 필수 규칙
- 축약 금지: 기존 내용 삭제/간소화 금지.
- 준수: `CONSTITUTION.md`, `MANDATORY_ONBOARDING.md`, `AGENTS.md`.

## 1. 정의(초안)
- 음절 σ = (C,V,F,I) ∈ 초성×중성×종성×Index.
- 해석 함수 Γ: (C,V,F,I) ↦ Op (1급 연산자 S→S).  
  합성: J(C,V,F)(X) = A_F ( V ( C ( X ))) with 병렬 레지스터 병합 규칙(병합 규칙 TBD).
- 초병렬:
  - ⊗_par: 병렬 합성, 결합성/단위원/e_par(있으면)/충돌해결(resolve) 규칙 명시.
  - ∇_hangul f := ⊗_par { ∂_γ f | γ ∈ Γ-basis }. 기저/HS 축소판 명시.
- MarginLog: 제거/무시된 성분을 `(source, context, value, weight, entropy)`로 기록, ⊗_par/∇ 적용 시 갱신.

## 2. 표 (완전 표기)
- C/V/F LUT (19/21/28):  
  - 초성 C (구조/경계/조작)  
    ㄱ boundary_closure, ㄲ strong_closure, ㄴ inclusion/embed, ㄷ boundary_measure, ㄸ sharp_measure, ㄹ boundary_extend, ㅁ union/merge, ㅂ volume/merge, ㅃ strong_merge, ㅅ split/select, ㅆ sharp_split, ㅇ onset_zero, ㅈ cut, ㅉ sharp_cut, ㅊ taper, ㅋ carve, ㅌ trim, ㅍ patch, ㅎ seal.  
  - 중성 V (방향/시간/사영/적분)  
    ㅏ D_{x+}, ㅓ D_{x-}, ㅑ ∂_t, ㅕ -∂_t, ㅐ D_{x+}+λ∂_t, ㅔ D_{x-}+λ∂_t, ㅗ proj_circle+, ㅛ proj_circle++, ㅜ proj_circle-, ㅠ proj_circle--, ㅡ flatten, ㅣ ∫dt, ㅒ ∂_{t+δ}, ㅖ ∂_{t-δ}, ㅚ D_{diag+}, ㅟ D_{diag-}, ㅘ D_{x+}+proj_circle+, ㅙ D_{x+}+proj_circle-, ㅝ D_{x-}+proj_circle+, ㅞ D_{x-}+proj_circle-, ㅢ mix(ㅡ,ㅣ).  
  - 종성 F (경계/여백/주석)  
    (none)=기본, ㄱ boundary_attach, ㄲ strong_boundary, ㄳ boundary+split, ㄴ include_note, ㄵ include+cut, ㄶ include+seal, ㄷ measure_tail, ㄹ extend_tail, ㄺ extend+closure, ㄻ extend+merge, ㄼ extend+volume, ㄽ extend+split, ㄾ extend+trim, ㄿ extend+patch, ㅀ extend+seal, ㅁ margin_add, ㅂ volume_attach, ㅄ volume+split, ㅅ split_tail, ㅆ sharp_split_tail, ㅇ null_attach, ㅈ cut_tail, ㅊ taper_tail, ㅋ carve_tail, ㅌ trim_tail, ㅍ patch_tail, ㅎ seal_tail.  
  - Index I: 위치/자릿수(차원/시간/계층 인덱스).
- 금지 조합/에러 코드 (STRICT/TOTAL):
  - E_L_EMPTY: 초성 없음 금지(STRICT) → TOTAL: ᄋ 삽입, meta.auto_onset=true.
  - E_V_EMPTY: 중성 없음 금지(STRICT) → TOTAL: ㅡ 삽입, meta.auto_vowel=true.
  - E_T_BAD_COMBO: 금지 겹받침/종성 조합.
  - ANNOT_CLASH: 주석 병합 실패 시 오류.
- HS 서브셋(교육용 최소):  
  - C: {ᄀ,ᄂ,ᄃ,ᄅ}, V: {ㅏ(∂_x), ㅑ(∂_t), ㅣ(∫dt)}, F: {없음, ᄆ}, STRICT 정책.

## 3. 연산 규칙
- ⊗_par:
  - 결합성: (a ⊗_par b) ⊗_par c = a ⊗_par (b ⊗_par c).
  - 단위원: e_par 유무를 명시(없으면 none). 기본: 없음.
  - resolve 규칙: 주석 충돌 시 우선순위/병합 테이블을 따른다(우선 keep>must>optional>forbidden, 충돌 시 ANNOT_CLASH).
- ∇_hangul:
  - 선택 기저 예시: {ㅏ(Dx+), ㅑ(∂t), ㅕ(-∂t), ㅐ(Dx+ + λ∂t), ㅣ(∫dt)}.
  - HS 기저: {ㅏ, ㅑ, ㅣ}.  
  - 각 성분과 C/V/F 대응 표는 부록(생략)으로 둔다.
- 병합 규칙: 레지스터 병합 순서 C→V→F→I, 충돌 시 우선순위 규칙 또는 에러. Index I는 마지막에 병합.

## 4. Γ 공리 (완전 정식화)

### 4.1 기본 공리

#### Γ-Total (총량 보존)
```
∀ C V F I:
  Legal(C,V,F) ⇒ ∃! op: State → State,
    Gamma C V F I = op ∧
    WellTyped(op) ∧
    Dom(op) ⊆ State ∧
    Ran(op) ⊆ State
```

#### Γ-Type (주체 타입 보존)
```
∀ f g: State → State:
  WellTyped(f) ∧ WellTyped(g) ⇒
  WellTyped(⊗_par f g) ∧
  WellTyped(∇_hangul basis f)
```

#### Γ-Closed (닫힘성)
```
∀ C V F I:
  ¬Legal(C,V,F) ⇒
  Gamma C V F I = ErrorOp
  where ErrorOp(x) = undefined
```

### 4.2 구조 공리

#### Γ-NF (정규형 존재)
```
∀ f: State → State:
  WellTyped(f) ⇒ ∃ nf:
    IsNormalForm(nf) ∧
    f ⇝* nf  (재작성 폐포)
```

**정규형 정의**:
```
IsNormalForm(f) :=
  ∀ g: (f ⇝ g) ⇒ f = g
```

### 4.3 계층 공리

#### Γ-Consv (보수성)
```
∀ p ∈ UEM_Formula:
  UEM_Provable(p) ⇒
  ZFC_Provable(Encode_ZFC(p))
```

### 4.4 연산 공리

#### Γ-Assoc (⊗_par 결합성)
```
∀ f g h: State → State:
  ⊗_par (⊗_par f g) h = ⊗_par f (⊗_par g h)
```

#### Γ-Dist (분배 법칙)
```
∀ f g h:
  ⊗_par f (⊙ g h) = ⊙ (⊗_par f g) (⊗_par f h)
```

#### Γ-Commut (교환 법칙)
```
∀ f g:
  ⊗_par f g = ⊗_par g f
```

### 4.5 기하학적 공리

#### Γ-Continuity (연속성)
```
∀ {f_n}: (State → State):
  (∀n. WellTyped(f_n)) ∧ (f_n → f) ⇒
  WellTyped(f) ∧
  (∇_hangul basis f_n → ∇_hangul basis f)
```

#### Γ-Convergence (수렴성)
```
∀ {f_n}:
  (∀n. WellTyped(f_n)) ∧
  (∀x. {f_n(x)}는 Cauchy) ⇒
  ∃f: ∀x. lim f_n(x) = f(x) ∧ WellTyped(f)
```

## 5. MarginLog 포맷
- 레코드: `(source, context, value, weight, entropy, timestamp?)`.
- ⊗_par/∇ 적용 시 삭제/사영된 성분을 필수 기록.
- 직렬화: 순서 리스트로 append, 출처(어떤 C/V/F/I, 어떤 위치)와 사유(금지/사영/축소) 명시.

## 6. 검증/통과 기준
- Well-typed: 모든 합법 (C,V,F) 조합은 Op 타입을 갖는다(금지 조합 제외). 금지 조합은 명시적 에러.
- ⊗_par: 결합성, 타입 보존, 충돌 결정성(resolve). 단위원 없으면 명시.
- ∇_hangul: 선택 기저/HS 기저에 대해 타입 보존, 성분별 대응 표 일관성.
- MarginLog: ⊗_par/∇ 적용 시 로그 필수 갱신.
- 테스트: C/V/F LUT 범위 검증, 금지 조합 에러 확인, HS 서브셋 강제(STRICT).

## 7. Lean skeleton 가이드
- 시그니처(제안):
  ```lean
  structure HangulOp := (C : Consonant) (V : Vowel) (F : Final) (I : Index)
  def Gamma (C : Consonant) (V : Vowel) (F : Final) (I : Index) : State → State
  def par (f g : State → State) : State → State -- ⊗_par
  def nabla_h (basis : List HangulOp) (f : State → State) : State → State -- ∇_hangul
  ```
- 증명 목표:  
  1) `par_assoc : par (par f g) h = par f (par g h)`  
  2) `par_preserve : well_typed f → well_typed g → well_typed (par f g)`  
  3) `nabla_preserve : well_typed f → well_typed (nabla_h basis f)`  
  4) `gamma_total : legal C V F → ∃ op, Gamma C V F I = op` (금지 조합 제외).
- HS 서브셋용 skeleton: basis = [{ㅏ,ㅑ,ㅣ}], STRICT 정책을 명시한 타입 클래스.

### 7.1 검증 계획
- Lean: 결합성/타입 보존/정규형 존재성을 lemma 리스트로 분리하고, HS 서브셋부터 증명.  
- 테스트:  
  - LUT 범위 체크(금지 조합 → 에러), MarginLog 갱신 여부 단위 테스트.  
  - ⊗_par assoc/comm(선택)/resolve 결정성 property.  
  - ∇_hangul이 선택 기저/HS 기저에서 타입을 보존함을 확인.

## 8. 작업/체크리스트
- [x] C/V/F LUT 전체 표 (Lean 매핑은 `HANGUL_LEAN_MAPPING_v0.1.md`에서 지속 확장).
- [x] 금지 조합/에러 코드 표(STRICT/TOTAL).
- [x] ⊗_par 단위원/resolve 규칙 확정(단위원 없음, 우선순위 규칙 명시).
- [x] ∇_hangul 기저/HS 기저 확정(성분 예시, HS={ㅏ,ㅑ,ㅣ}).
- [x] MarginLog 갱신 규약(필드/포맷) 명시.
- [x] Lean skeleton 선언(Γ/⊗_par/∇_hangul).
- [x] 검증 계획: 단위 테스트/타입 체크/Lean 증명(가능한 범위) 설계.
