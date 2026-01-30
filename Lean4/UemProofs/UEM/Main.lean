import UemProofs.UEM.UEM_Foundations
import UemProofs.UEM.UEM_Calculus
import UemProofs.UEM.UEM_CoreCompleteness
import UemProofs.UEM.UEM_CoreModels
import UemProofs.UEM.UEM_CoreMetaBridge
import UemProofs.UEM.UEM_TaggedEvalCore
import UemProofs.UEM.UEM_EpistemicEmbedding
import UemProofs.UEM.UEM_OperatorSemantics
import UemProofs.UEM.UEM_Structure
import UemProofs.UEM.UEM_HangulMatrix
import UemProofs.UEM.UEM_HangulCardinality
import UemProofs.UEM.UEM_HangulDirection
import UemProofs.UEM.UEM_ObservedSubcategory
import UemProofs.UEM.UEM_Conservativity
import UemProofs.UEM.UEM_Extensions.UEM_ProjectionGeometry
import UemProofs.UEM.UEM_Extensions.UEM_SCD_AHS
import UemProofs.UEM.UEM_Extensions.UEM_Fractal
import UemProofs.UEM.UEM_Extensions.UEM_Fractal_Theorems
import UemProofs.UEM.UEM_Extensions.UEM_PH_Stability
import UemProofs.UEM.UEM_MetaStrataBridge
import UemProofs.UEM.UEM_MetaStrata_Theorems

/-! # UEM Main Entry Point (Pure Formal Core) -/

namespace UEM

-- Re-export key theorems under the `UEM` namespace.

theorem observer_kernel_is_equivalence {O : Type _} [Observer O] :
    Equivalence (Observer.kernel (O := O)) :=
  Observer.kernel_is_equivalence


theorem thickness_is_outer_measure {O : Type _} (basis : ThicknessBasis O) :
    (basis.thickness ∅ = 0) ∧
      (∀ ⦃s t : Set O⦄, s ⊆ t → basis.thickness s ≤ basis.thickness t) ∧
      (∀ s : ℕ → Set O,
        basis.thickness (⋃ n, s n) ≤ ∑' n, basis.thickness (s n)) :=
  basis.thickness_is_outer_measure

/-- Coordinate cardinality sanity checks for 3×3 and 3×3×3. -/
example : Fintype.card (Coord 3 1 1) = 9 := coord_card_3x3
example : Fintype.card (Coord 3 3 1) = 27 := coord_card_3x3x3

end UEM
