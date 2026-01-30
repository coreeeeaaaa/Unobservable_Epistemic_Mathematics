import UemProofs.UEM.UEM_Calculus
import UemProofs.UEM.UEM_MetaDefinability

noncomputable section
open scoped ENNReal

namespace UEM

/-!
Core–meta bridges: pure structural compatibility between the formal core
and the meta‑definability layer. No examples, no special cases.
-/

/-- Bridge from core object types into an epistemic system. -/
structure CoreEpistemicBridge (E : EpistemicSystem) where
  map_obj : ObjType → E.Obj
  observed_recognizable : ∀ a, IsObserved a → E.Recognizable (map_obj a)
  observed_measurable : ∀ a, IsObserved a → E.Measurable (map_obj a)

/-- Bridge from an epistemic system into a definability system. -/
structure EpistemicDefinabilityBridge (E : EpistemicSystem) (D : DefinabilitySystem) where
  map_obj : E.Obj → D.U
  recognizable_definable : ∀ x, E.Recognizable x → D.Definable (map_obj x)

/-- Bridge for tagged evaluation (boundary-respecting totality). -/
structure TaggedEvalBridge (E : EpistemicSystem) where
  tagged : TaggedEvalSystem E
  val_of_recognizable : ∀ x, E.Recognizable x → (tagged.eval x).2 = EvalTag.val
  out_of_unrecognizable : ∀ x, ¬ E.Recognizable x → (tagged.eval x).2 = EvalTag.out

/-- Recognizability implies membership in the definable core. -/
theorem recognizable_in_definable_core
    {E : EpistemicSystem} {D : DefinabilitySystem}
    (B : EpistemicDefinabilityBridge E D) (x : E.Obj) :
    E.Recognizable x → B.map_obj x ∈ DefinableCore D := by
  intro hrec
  simp [DefinableCore, B.recognizable_definable x hrec]

/-- Recognizable objects cannot lie on the undefinable boundary. -/
theorem recognizable_not_boundary
    {E : EpistemicSystem} {D : DefinabilitySystem}
    (B : EpistemicDefinabilityBridge E D) (x : E.Obj) :
    E.Recognizable x → B.map_obj x ∉ D.boundary := by
  intro hrec hbd
  have hdef : D.Definable (B.map_obj x) := B.recognizable_definable x hrec
  have hundef : Undefinable D (B.map_obj x) :=
    boundary_undefinable D (B.map_obj x) hbd
  exact hundef hdef

/-! ### Canonical core epistemic system (pure, structure‑only) -/

def coreEpistemicSystem : EpistemicSystem where
  Obj := ObjType
  Time := PUnit
  now := PUnit.unit
  Exists := fun _ => True
  Recognizable := IsObserved
  Measurable := IsObserved
  PossibleAt := fun _ _ => True
  measure := fun _ => (0 : ℝ≥0∞)
  Value := ObjType
  Eval := fun x => x

def coreEpistemicBridge : CoreEpistemicBridge coreEpistemicSystem where
  map_obj := fun a => a
  observed_recognizable := by
    intro a h
    simpa [coreEpistemicSystem] using h
  observed_measurable := by
    intro a h
    simpa [coreEpistemicSystem] using h

end UEM
