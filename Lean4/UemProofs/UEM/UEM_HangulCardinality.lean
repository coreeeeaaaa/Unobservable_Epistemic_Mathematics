import UemProofs.UEM.UEM_Calculus
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace UEM

/-!
Cardinality of Hangul syllable construction in the formal core.
This is purely combinatorial: the syllable space is a product of
choseong × jungseong × (optional jongseong).
-/

theorem card_choseong : Fintype.card Choseong = 19 := by
  decide

theorem card_jungseong : Fintype.card Jungseong = 21 := by
  decide

theorem card_jongseong : Fintype.card Jongseong = 27 := by
  decide

def syllableEquiv : Syllable ≃ (Choseong × Jungseong × Option Jongseong) where
  toFun := fun s => (s.c, s.v, s.f?)
  invFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
  left_inv := by
    intro s
    cases s
    rfl
  right_inv := by
    intro t
    cases t with
    | mk c t' =>
      cases t' with
      | mk v f =>
        rfl

theorem card_syllable_product :
    Fintype.card Syllable =
      Fintype.card Choseong * Fintype.card Jungseong * Fintype.card (Option Jongseong) := by
  classical
  -- Reduce to product cardinality via equivalence.
  simpa [Fintype.card_prod] using (Fintype.card_congr syllableEquiv)

theorem card_syllable : Fintype.card Syllable = 11172 := by
  classical
  -- Option card = card + 1
  have hopt : Fintype.card (Option Jongseong) = 28 := by
    simp [Fintype.card_option, card_jongseong]
  calc
    Fintype.card Syllable
        = Fintype.card Choseong * Fintype.card Jungseong * Fintype.card (Option Jongseong) := by
            simpa using card_syllable_product
    _ = 19 * 21 * 28 := by
            simp [card_choseong, card_jungseong, hopt]
    _ = 11172 := by
            norm_num

end UEM
