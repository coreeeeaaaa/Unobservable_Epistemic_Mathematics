# UEM 객체 계층 스펙 v0.1 (스칼라→텐서→Sparke→Actyon→Escalade→Secare)
> 목적: 기존 수학의 Scalar/Vector/Tensor를 그대로 두고, UEM 상위 객체(Sparke, Actyon, Escalade, Secare)의 기호/단위/포함·승격·투영 규칙을 충돌 없이 고정한다. (축약 금지, 추가/정밀화만 허용)

## 0. 기호/단위 (기존 수학과 충돌 금지)
- Scalar/Vector/Tensor: 표준 선형대수 기호 유지(스칼라 s, 벡터 **v**, 텐서 T). Tensor(0)=Scalar, Tensor(1)=Vector, Tensor(n)=n-텐서.
- Sparke: 기호 ⛦, 단위 `spar`. 값은 Tensor(n) 포함 가능, rank는 텐서 랭크와 연동.
- Actyon: 기호 ㆁ, 단위 `acti`. Sparke의 유한/가중 멀티셋 + agent/role 메타.
- Escalade: 기호 𓂌, 단위 `escul`. Actyon의 시간/동역학 전개(흐름, 단계).
- Secare: 기호 ♡, 단위 `seks`. 세계/경계/축/시그마-대수/여백을 포함하는 상위 컨테이너.
- 사영: Π_null (무력화 사영), Margin: M, 경계: B, 축: Axis/Σ.
- 단위 일람: `spar`(⛦), `acti`(ㆁ), `escul`(𓂌), `seks`(♡)만 사용.

## 1. 계층/포함 원칙
- Tensor 계층 변경 없음: Scalar/Vector/Tensor 정의·연산을 그대로 사용.
- 포함: Tensor(n) ⊂ Sparke(rank=n) ⊂ Actyon(rank=n) ⊂ Escalade(rank=n) ⊂ Secare(rank=n).
- 승격/투영: embed_{n→n+1}, proj_{n+1→n}는 Tensor 계층 정의를 따르며, 상위 객체는 내부 Tensor 랭크에 맞춰 동일 규칙을 전파. (보존 조건은 아래 2참조)
- 랭크/축 보존: 병합·분기·flow·Archive 시 랭크·축 정보는 명시적 규칙으로 유지(충돌 시 에러 또는 우선순위 규칙 필요, TODO).
- 정책 기본값: rank가 다를 때는 높은 쪽으로 promote 후 병합(정책 A); 정책 B(에러 종료)를 선택할 수 있음을 문서화.

## 2. 필수 연산/규칙 (스펙 레벨)
- Sparke(⛦): (X:Tensor(n), support, margin M_spar, axis/σ-필요시)  
  덧셈: X 합 + support ∪ + margin 병합. 단위 `spar`.
- Actyon(ㆁ): (sparkes: List/Multiset ⛦, agent/role, weight/meta). 단위 `acti`.  
  병합: rank 동일 시 병합, 다르면 promote/demote로 맞춘 뒤 병합(정책 A).
- Escalade(𓂌): (flow f: S→S, time domain, invariants). 단위 `escul`.  
  흐름-사영 교환(Π_null ∘ f = f_keep ∘ Π_null) 및 경계/여백 보존 조건 명시(TODO).
- Secare(♡): (S_sub, B, Σ, axis, margin M_sek). 단위 `seks`.  
  경계 안정성/Archive 규칙, 축 병합 규칙 필요(TODO).
- 승격/투영 보존 조건(TODO 표 작성):
  - 랭크: promote/demote 시 rank = rank±1, margin/support/axis 보존 조건 명시.
  - support: 포함/합집합/교차 시 보존/제약 규칙.
  - margin: 병합/사영 시 여백 로그 보존 규칙.

### 2.1 랭크/축 정책 표
- 병합(Merge):  
  - rank 같음 → 병합 OK.  
  - rank 다름 → 정책 A(기본): 낮은 쪽을 promote해 맞춘 뒤 병합. 정책 B: 에러.  
  - axis 다름 → 충돌 에러 또는 우선순위 규칙(우선 axis_parent → axis_child) 적용.
- 분기/Archive: 부모 rank/axis를 자식에 상속, 자식이 덮어쓰면 에러.
- 흐름(𓂌): f가 rank/axis를 보존해야 함. 업데이트가 필요하면 명시된 규칙을 정의(예: axis 재정렬 함수).
- 승격(promote): rank→rank+1, support/axis/margin 그대로 유지, 불가능하면 에러.  
- 강등(demote): rank>0에서만, support/axis/margin 유지.  

### 2.2 보존/제약 규칙 (요약)
- support: ∪/∩ 시 차원/축 일치 필요, 불일치 시 사전 정의된 사상(예: 좌표 사영) 적용 또는 에러.
- margin: 병합 시 로그 append, 사영 시 버려진 성분을 M에 기록.
- axis: 병합 시 동일 축 요구, 다르면 우선순위 규칙으로 통일(예: 부모 축 우선).

### 2.3 랭크/axis 상세 표 (충돌/사상 규칙)
|연산|입력 조건|처리|결과/오류|
|---|---|---|---|
|merge(⛦/ㆁ/𓂌/♡)|rank 동일|직접 병합|OK|
|merge(⛦/ㆁ/𓂌/♡)|rank 다름|낮은 쪽 promote→병합(기본) / 정책 B: 오류|OK/ERROR|
|merge axis|axis 동일|유지|OK|
|merge axis|axis 다름|우선순위 규칙으로 통일(부모 우선), 불가 시 오류|OK/ERROR|
|promote|rank→rank+1, support/margin/axis 유지|OK, 불가 시 ERROR|
|demote|rank>0, support/margin/axis 유지|OK, 불가 시 ERROR|
|flow f|f가 rank/axis 불변 또는 규칙에 따라 재정렬|OK, 미지정 시 ERROR|
|Archive/branch|부모 rank/axis 상속, 덮어쓰기 금지|OK/ERROR|

### 2.4 margin/support/axis 보존 표
- support:  
  - 병합: `supp(out)=supp(a)∪supp(b)`; 차원 불일치 시 `π_align`로 사영 후 병합.  
  - 투영/강등: 해당 차원 사영 후 기록.
- margin:  
  - 병합: `M_out = M_a ++ M_b` (로그 append, 출처 기록).  
  - 사영: `log(v_null)`을 MarginLog에 추가.
- axis:  
  - 병합: 동일 요구, 다르면 우선순위 규칙.  
  - 승격/투영: 축 정보 그대로 전파, 불일치 시 오류.

### 2.5 Secare 6축(존재/비존재/무존재/반존재/공백/여백) 연동 규칙
- 축 태그: `exist, nonexist, outside, liminal, void, margin`.  
- 병합: 충돌 시 우선순위 `exist > liminal > margin > void > nonexist > outside`; 동일 우선순위 충돌은 오류.  
- 승격/강등/Archive: 상위로 승격 시 축 태그를 그대로 전파, 덮어쓰기 금지. Archive/branch 시 부모 축을 상속.  
- 사영(Π_null): margin 축으로 이동한 성분은 MarginLog에 기록, 다른 축은 보존.  
- Secare: 6축 전체를 보유, 하위 객체 축 누락 시 Secare가 부모 축으로 채우고 보강 로그 남김.

## 3. 차원/인식 호환 (문서 연동)
- 차원 정의는 스펙 Part I/II 복원 시 삽입: 인식 차원 X_rec, 기하 차원 X_phys, 곱공간 X_phys × X_rec.
- 객체 계층은 차원/좌표 구조와 호환: Secare가 세계(좌표·시그마-대수·축)를 정의하고, Escalade/Actyon/Sparke가 그 안에서 작동.
- 충돌 금지: 기존 Tensor 연산 기호와 UEM 기호(⛦,ㆁ,𓂌,♡, Π_null, M)를 구분하여 사용.

## 4. 체크리스트 (고정해야 할 미완 항목)
- [x] 랭크·축 포함/승격/투영 규칙 표 (충돌/에러 처리 포함, 2.1/2.2 참조).
- [x] Sparke/Actyon/Escalade/Secare 병합·분기·flow 보존 조건 요약(2.1/2.2).
- [x] Secare 6축(존재/비존재/무존재/반존재/공백/여백) 정의와 계층 연동 → `UEM_CORE_FORMALISM_v0.1.md` 참조 후 통일.
- [x] 단위·기호 표: spar/acti/escul/seks, 기호(⛦/ㆁ/𓂌/♡) 고정.
- [x] Part I/II 복원 시 계층 정의 본문화(스펙 v3.1에 삽입 완료).
- [x] Hangul→Lean 매핑 표 연동(기호 이름 충돌 방지) → `HANGUL_LEAN_MAPPING_v0.1.md`와 교차 참조.

## 5. 위치/연동
- 상위 인덱스: `README.md`, `UEM_STRUCTURE_GUIDE_v0.1.md`, `docs/blueprint/FINAL_INDEX.md`.
- 관련 문서: `docs/blueprint/HIERARCHY_PACKAGE.md`, `docs/spec/details/UEM_OBJECT_HIERARCHY_DETAIL.md`, `docs/blueprint/TODO_DEPTH.md`, `docs/roadmap/UEM_HARDENING_PLAN_v0.1.md`.

이 스펙은 Tensor 계층을 그대로 사용하면서, UEM 상위 객체와 단위/기호/포함 규칙을 정합적으로 고정하기 위한 기본 문서이다. 이후 버전에서 세부 표와 보존/에러 규칙을 채워 넣어야 한다.
