# 객체 계층 패키지 (Scalar/Vector/Tensor → Sparke → Actyon → Escalade → Secare)

> 목표: 스칼라(0-텐서)→벡터(1-텐서)→n-텐서, 그리고 이를 담는 Sparke→Actyon→Escalade→Secare 상위 객체 구조와 세카레 6축을 명확히 고정한다.

## 1. 텐서 기반 계층
- 랭크: `rank : Nat`, Tensor(0)=Scalar, Tensor(1)=Vector, Tensor(n)=n-텐서(일반).
- 포함/승격: `embed_{n→n+1} : Tensor n → Tensor (n+1)`, 조건부 투영 `proj_{n+1→n}`.
- Sparke: `(rank, X : Tensor rank, support, margin)`; 덧셈/스케일은 동일 랭크에서만, 승격/투영과 support/margin 보존 조건 명시.
- Actyon/Escalade/Secare: Sparke 멀티셋/flow/경계 등에서 랭크 승격/보존 규칙을 명시(병합/분기/flow/Archive 시 랭크 일관성).

## 2. 세카레 6축
- 축: `{existence, nonexistence, nullity, quasi, inner_gap, unobserved}`.  
  - inner_gap: 경계 내부, 비어있음 가능.  
  - unobserved: 경계 외부의 비관측 인식존재(비어있음 불가, 로그/기록 필수).
- Secare에 `axis` 필드 추가(Actyon/Escalade 단계에서 축 전파/병합 규칙 명시, 충돌 시 우선순위/오류 규칙 고정).

## 3. 정리 목표 (스켈레톤)
- 랭크 보존/승격 정리: 승격/투영이 덧셈/스케일, support/margin 병합과 교환/보존되는 조건을 명시.  
- 축 보존/변환 정리: 병합/분기/사영 시 6축이 어떻게 유지/변환되는지(공백↔여백 불변, 충돌 처리) 명시.  
- 일관성: Escalade flow와 Secare boundary/Archive 처리 시 랭크와 축이 일관되게 유지됨을 증명.

## 4. 검증 체크리스트
1) Tensor 랭크 타입 및 embed/proj 정의.  
2) Sparke/Actyon/Escalade/Secare 랭크·축 포함/보존 규칙 명시.  
3) 6축 정의(공백/여백 구분)와 전파/병합 규칙 명시.  
4) 보존/승격/변환 정리 문장 스켈레톤 설정.  
