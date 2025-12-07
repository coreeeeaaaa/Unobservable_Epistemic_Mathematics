# Hangul → Lean Mapping v0.1
> 목적: 한글 연산자/기호를 Lean 이름/notation으로 표준화하여 충돌을 방지한다. HS 서브셋을 명시해 교육/제한 환경에서 부분 매핑만 사용 가능하게 한다. (축약 금지)

## 1. 핵심 기호 매핑
- τ_margin → `UEM.Margin.tau`
- Π (무력화 사영) → `UEM.PiNull`
- K (커널) → `UEM.Kernel`
- μ, μ_unobs → `UEM.mu`, `UEM.mu_unobs`
- ⛦ (Sparke) → `UEM.Sparke`
- ㆁ (Actyon) → `UEM.Actyon`
- 𓂌 (Escalade) → `UEM.Escalade`
- ♡ (Secare) → `UEM.Secare`
- ⊗_par → `UEM.par`
- ∇_hangul → `UEM.nabla_h`
- Γ 토큰 예시:
  - ㄱ → `UEM.Boundary.closure`
  - ㄷ → `UEM.Boundary.measure`
  - ㅏ → `UEM.Dx_pos`
  - ㅑ → `UEM.Dt_pos`
  - ㅣ → `UEM.Int_t`
  - ㅁ → `UEM.Annot.margin`
- 추가 매핑(확장):
  - ㄴ → `UEM.Boundary.embed`
  - ㄹ → `UEM.Boundary.extend`
  - ㅂ/ㅃ → `UEM.Volume.merge/strongMerge`
  - ㅅ/ㅆ → `UEM.Split.select/sharp`
  - ㅓ → `UEM.Dx_neg`
  - ㅕ → `UEM.Dt_neg`
  - ㅡ → `UEM.Flatten`
  - ㅗ/ㅛ/ㅜ/ㅠ → `UEM.Proj.circle_pos/pos2/neg/neg2`
  - 종성 예시: ㄱ → `UEM.Final.boundaryAttach`, ㅁ → `UEM.Final.marginAdd`, ㅎ → `UEM.Final.sealTail`
  - axis 6축 태그: exist/nonexist/outside/liminal/void/margin → `UEM.Axis.exist` 등

## 2. HS 서브셋 (교육용)
- C: {ᄀ,ᄂ,ᄃ,ᄅ} → closure/include/measure/extend.
- V: {ㅏ(∂_x), ㅑ(∂_t), ㅣ(∫dt)}.
- F: {없음, ᄆ(margin)}.
- 정책: STRICT(빈 초/중성 금지, 자동 삽입 없음).

## 3. 네임스페이스 규칙
- Lean 네임스페이스 접두사 `UEM.` 사용, 토큰은 CamelCase/스네이크 케이스 혼용 금지.  
- 새 기호 도입 시: 한글 토큰 → `UEM.<domain>.<name>`로만 추가(임의 이름 금지).

## 4. 위치/연동
- 참조: `docs/spec/HANGUL_OPERATORS_SPEC_v0.1.md`, `UEM_CORE_FORMALISM_v0.1.md`.
- 코드: Lean 시그니처 추가 시 본 매핑을 우선 적용.
