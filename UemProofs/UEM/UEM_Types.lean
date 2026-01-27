import UemProofs.UEM.UEM_Calculus

namespace UEM

/-!
# UEM Typed Term Calculus (Applications Layer)
이 파일은 UEM_Applications.lean를 위한 타입 정의를 제공합니다.
불변 스펙(UEM_Calculus.lean)은 수정하지 않고 새로운 파일로 확장합니다.
-/

/-- Sorts for the typed term language. -/
inductive UEMSort : Type
  | unobs
  | obs
  | formula
  deriving DecidableEq, Repr

/-- Typed terms indexed by sort. -/
inductive UEMTerm : UEMSort → Type
  | unobs (name : String) : UEMTerm .unobs
  | obs (val : Scalar) : UEMTerm .obs
  | formula (expr : String) : UEMTerm .formula
  deriving DecidableEq

end UEM
