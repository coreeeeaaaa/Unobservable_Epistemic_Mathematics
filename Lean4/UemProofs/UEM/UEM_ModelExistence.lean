import UemProofs.UEM.UEM_Semantics

namespace UEM

/-- Nontriviality: some carrier has two distinct elements. -/
def NontrivialModel (M : Model) : Prop :=
  ∃ a : ObjType, ∃ x y : M.Carrier a, x ≠ y

/-- Existence of a nontrivial UEM-0 model. -/
theorem model_exists : ∃ M : Model, NontrivialModel M := by
  refine ⟨coreModel, ?_⟩
  refine ⟨.nat, (0 : Nat), (1 : Nat), ?_⟩
  change (0 : Nat) ≠ (1 : Nat)
  decide

end UEM
