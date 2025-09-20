import UEM.Prelude
import UEM.HangulMonoid

namespace UEM

/-- 한글 조각(fragment): 파서가 처리할 수 있는 제한된 구문 -/
inductive HangulFragment : Type
  | single : HangulBase → HangulFragment
  | compound : HangulBase → HangulBase → HangulFragment
  | sequence : List HangulFragment → HangulFragment
  deriving DecidableEq, Repr

/-- 조각을 모노이드 원소로 파싱하는 함수 -/
def parseFragment : HangulFragment → HangulMonoid
  | HangulFragment.single b => [b]
  | HangulFragment.compound b₁ b₂ => [b₁, b₂]
  | HangulFragment.sequence frags => frags.map parseFragment |>.foldl (· * ·) 1

/-- 파서의 전정의성: 모든 조각에 대해 파싱이 정의됨 -/
theorem parser_total_on_fragment (frag : HangulFragment) :
  ∃ result : HangulMonoid, parseFragment frag = result := by
  use parseFragment frag
  rfl

/-- 파서가 모노이드 구조를 보존함 -/
theorem parseFragment_respects_sequence (frags : List HangulFragment) :
  parseFragment (HangulFragment.sequence frags) =
  frags.map parseFragment |>.foldl (· * ·) 1 := by
  rfl

/-- 단일 원소 파싱의 정확성 -/
theorem parseFragment_single (b : HangulBase) :
  parseFragment (HangulFragment.single b) = HangulMonoid.base b := by
  rfl

/-- 복합 원소 파싱의 정확성 -/
theorem parseFragment_compound (b₁ b₂ : HangulBase) :
  parseFragment (HangulFragment.compound b₁ b₂) =
  HangulMonoid.base b₁ * HangulMonoid.base b₂ := by
  simp [parseFragment, HangulMonoid.base]

/-- 파서의 결정적 속성: 같은 입력은 같은 출력 -/
theorem parseFragment_deterministic (frag : HangulFragment) :
  parseFragment frag = parseFragment frag := by
  rfl

/-- 빈 시퀀스는 모노이드 단위원으로 파싱됨 -/
theorem parseFragment_empty_sequence :
  parseFragment (HangulFragment.sequence []) = 1 := by
  simp [parseFragment]

end UEM