import UEM.Prelude
import UEM.Structure

namespace UEM

/-- 한글 기저원소 -/
inductive HangulBase : Type
  | cho : Fin 19 → HangulBase  -- 초성
  | jung : Fin 21 → HangulBase -- 중성
  | jong : Fin 28 → HangulBase -- 종성
  deriving DecidableEq, Repr

/-- 한글 모노이드: 기저원소들의 자유 모노이드 -/
def HangulMonoid : Type := List HangulBase

-- 모노이드 구조
instance : Monoid HangulMonoid where
  one := []
  mul := List.append
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

-- 기저원소에서 단원 모노이드 원소로의 삽입
def HangulMonoid.base (b : HangulBase) : HangulMonoid := [b]

-- 기저원소들이 생성원임을 보장하는 정리
theorem HangulMonoid.generated_by_base (x : HangulMonoid) :
  ∃ bases : List HangulBase, x = bases.map HangulMonoid.base |>.foldl (· * ·) 1 := by
  use x
  induction x with
  | nil => simp [HangulMonoid.base]
  | cons h t ih =>
    simp [List.map_cons, List.foldl_cons, HangulMonoid.base]
    rfl

-- 결합법칙이 성립함 (인스턴스에서 자동으로 증명됨)
theorem HangulMonoid.assoc (a b c : HangulMonoid) : (a * b) * c = a * (b * c) :=
  mul_assoc a b c

-- 단위원 법칙
theorem HangulMonoid.left_unit (a : HangulMonoid) : 1 * a = a := one_mul a
theorem HangulMonoid.right_unit (a : HangulMonoid) : a * 1 = a := mul_one a

end UEM