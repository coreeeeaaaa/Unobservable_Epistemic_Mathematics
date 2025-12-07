# 비관측 인식수학 (UEM: Unobservable Epistemic Mathematics)

> 작업 시작 전 반드시 `MANDATORY_ONBOARDING.md`를 읽고 규칙을 따른다. (축약 금지·AGENTS 지침·필수 문서 경로·빌드/검증 절차)
> 공통 헌법: `CONSTITUTION.md` (모든 에이전트/개발자 공통 규칙)
> 총괄 백서: `UEM_STRUCTURE_GUIDE_v0.1.md` (루트, 강제 읽기 / 삭제 금지 / 수정 시 버전 관리·추가만)

> *자기가 아닌 것들의 공백 어딘가에 자아가 있다.*
> *그 어딘가가 어딘지는 알 수 없다.*
> *자아는 서술할 수 없고, 증명할 수 없고, 다만 인식할 수 있을 뿐이다.*
>
> *이미 그러한 것을 시작이 있고 끝이 있는 것들로는 인식하고 서술할 수 없다.*
> *이미 그러한 것은, 그저 인식할 수 있을 뿐이고,*
> ***여백은 원래 이 곳에 있었다.***

---

## 📜 UEM System Specification v1.0 (2025-12-08)

UEM(Unobservable Epistemic Mathematics)은 **비관측 가능한 것의 인식 가능성을 수학적으로 정형화하는 독립된 수리논리 체계**입니다. 물리적 실재(X_phys) 위에 9차원 인식 좌표계(X_rec)를 구축하여 존재와 인식을 통합적으로 기술합니다.

### 📘 핵심 문서
- **[UEM_MASTER_COMPLETE_v1.0.md](UEM_MASTER_COMPLETE_v1.0.md)**: 시스템 명세서 (437라인)
  - 철학, 수학적 틀, 객체 계층, 한글 연산자에 대한 정의와 구조 기술
- **[UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md](docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.1_2025-03.md)**: 핵심 수학 스펙
  - Part I: 순수 이론 (Sparke~Secare 객체 대수)
  - Part II: 9차원 인식 좌표계
  - Part III: 무력화 사영 증명

### 🔧 Lean 4 형식화
- **[Foundations](formal/UEM/Foundations/)**: 기초 구조 정의
  - State 공간, 차원 독립성, 여백 사영, 한글 연산자에 대한 형식화
- **[Theorems](formal/UEM/Theorems/)**: 핵심 정리 증명
  - P1_NullProjection, P2_SparkeMonoid 증명 완료

### [📕 UEM Advanced Applications v1.0](docs/examples/UEM_ADVANCED_APPLICATIONS_v1.0.md)
- **Quantum Entanglement**: 비국소성을 인식적 연결성($d_4$)과 여백화($	_{null}$)로 해석하는 관점 제시.
- **Category Theory**: 자연 변환(Natural Transformation)을 정보 보존 공리로 재해석.
- **Complex Systems**: 창발(Emergence) 현상을 여백 중첩($Overlap$)과 차원 확장으로 모델링.

---

## 🚀 Releases

- **v1.0 (2025-12-08)** - **Current Release** 🎯
  - **System Specification**: UEM System Specification v1.0 (437라인 명세서)
  - **Lean 4 Foundations**: 기초 구조 형식화 (Foundations/ 폴더)
    - State 공간 정의와 차원 독립성 기본 증명
    - 여백 사영 연산자와 한글 연산자 기본 구조 정의
    - 공리에서 정리로의 구조적 변환 작업
  - **Updated Specifications**: KM-1~3, μ_unobs, ZFC 호환성 명세
  - **Documentation Set**: 철학, 스펙, 설계 청사진 통합
  - **Project Structure**: 전문 프로젝트 구조 정립

- **v0.1.0 (2025-12-02)** - Initial Release
  - Lean formalization: `P1_NullProjection`와 `P2_SparkeMonoid` 모두 `lake build`로 검증 완료.
  - `Sparke`의 `AddCommMonoid` 인스턴스에서 `sorry` 제거, 표준 `nsmul` 정의 및 단순 `ext`/`simp` 증명으로 정리.
  - 빌드 방법: `cd formal && lake build` (Lean 4.26.0-rc2 toolchain 기준).

---

## 🛠️ Scope & Definition

**This is NOT**:
- A programming language or software library.
- A tool for specific exams or commercial applications.
- A personal essay or claim.

**This IS**:
- A formal **Branch of Mathematics** dealing with Epistemic Limits.
- A system of **Axioms and Logic** designed for compatibility with classical mathematics.
- An exploration of **Ontological Structures** beyond linear representation.

> ⚠️ **Note**: 본 문서는 기존 수학과의 호환성을 유지하며, 인식·여백 구조를 수학적으로 모델링하는 실험적 프레임워크입니다. 모든 내용은 수학적 정의와 논리적 구조에 기반합니다.
