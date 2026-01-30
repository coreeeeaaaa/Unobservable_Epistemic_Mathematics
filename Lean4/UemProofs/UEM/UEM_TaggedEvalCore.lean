import UemProofs.UEM.UEM_CoreMetaBridge

namespace UEM

/-!
Canonical tagged evaluation for the core epistemic system.
Pure boundary-respecting totality (no external cases).
-/

instance (a : ObjType) : Decidable (IsObserved a) := by
  cases a with
  | scalar => exact isTrue trivial
  | vector _ => exact isTrue trivial
  | tensor _ => exact isTrue trivial
  | spark => exact isFalse (by intro h; cases h)
  | actyon => exact isFalse (by intro h; cases h)
  | escalade => exact isFalse (by intro h; cases h)
  | secare => exact isFalse (by intro h; cases h)
  | world => exact isFalse (by intro h; cases h)
  | observer => exact isFalse (by intro h; cases h)
  | margin => exact isFalse (by intro h; cases h)
  | possibleWorld => exact isFalse (by intro h; cases h)
  | descriptor => exact isFalse (by intro h; cases h)
  | nat => exact isFalse (by intro h; cases h)
  | prod _ _ => exact isFalse (by intro h; cases h)

def coreTaggedEval : TaggedEvalSystem coreEpistemicSystem where
  eval := fun x =>
    if _ : IsObserved x then (x, EvalTag.val) else (x, EvalTag.out)

theorem coreTaggedEval_val_of_recognizable (x : coreEpistemicSystem.Obj) :
    coreEpistemicSystem.Recognizable x →
      (coreTaggedEval.eval x).2 = EvalTag.val := by
  intro h
  have : IsObserved x := by simpa [coreEpistemicSystem] using h
  simp [coreTaggedEval, this]

theorem coreTaggedEval_out_of_unrecognizable (x : coreEpistemicSystem.Obj) :
    ¬ coreEpistemicSystem.Recognizable x →
      (coreTaggedEval.eval x).2 = EvalTag.out := by
  intro h
  have : ¬ IsObserved x := by simpa [coreEpistemicSystem] using h
  simp [coreTaggedEval, this]

def coreTaggedBridge : TaggedEvalBridge coreEpistemicSystem where
  tagged := coreTaggedEval
  val_of_recognizable := coreTaggedEval_val_of_recognizable
  out_of_unrecognizable := coreTaggedEval_out_of_unrecognizable

end UEM
