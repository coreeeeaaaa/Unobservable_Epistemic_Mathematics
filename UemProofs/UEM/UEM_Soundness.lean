import UemProofs.UEM.UEM_Theory
import UemProofs.UEM.UEM_Semantics

namespace UEM

/-- Semantic validity of an equation in a model. -/
def Holds (M : Model) (t u : UEM0OpTerm a b) : Prop :=
  ∀ x, evalM M t x = evalM M u x

/-- Soundness for the UEM-0 derivation system. -/
theorem soundness (M : Model) {t u : UEM0OpTerm a b} : Derives t u → Holds M t u := by
  intro h
  induction h with
  | refl t =>
      intro x
      rfl
  | symm h ih =>
      intro x
      exact (ih x).symm
  | trans h1 h2 ih1 ih2 =>
      intro x
      exact (ih1 x).trans (ih2 x)
  | congr_comp h1 h2 ih1 ih2 =>
      rename_i a b c g g' f f'
      intro x
      have hf := ih2 x
      have hg := ih1 (evalM M f' x)
      calc
        evalM M g (evalM M f x) = evalM M g (evalM M f' x) := by
          simp [hf]
        _ = evalM M g' (evalM M f' x) := hg
  | congr_lift h1 h2 ih1 ih2 =>
      rename_i c a b f f' g g'
      intro x
      have hf : evalM M f = evalM M f' := funext ih1
      have hg : evalM M g = evalM M g' := funext ih2
      simp [evalM, hf, hg]
  | prod_fst_lift f g =>
      intro x
      simp [evalM, M.fst_lift]
  | prod_snd_lift f g =>
      intro x
      simp [evalM, M.snd_lift]
  | prod_unique h f g hfst hsnd ihfst ihsnd =>
      intro x
      have hf : ∀ y, M.fst (evalM M h y) = evalM M f y := by
        intro y
        have h1 := ihfst y
        dsimp [evalM] at h1
        exact h1
      have hg : ∀ y, M.snd (evalM M h y) = evalM M g y := by
        intro y
        have h1 := ihsnd y
        dsimp [evalM] at h1
        exact h1
      have hfun : evalM M h = fun y => M.lift (evalM M f) (evalM M g) y := by
        exact M.lift_unique (evalM M h) (evalM M f) (evalM M g) hf hg
      change evalM M h x = M.lift (evalM M f) (evalM M g) x
      exact congrArg (fun k => k x) hfun

end UEM
