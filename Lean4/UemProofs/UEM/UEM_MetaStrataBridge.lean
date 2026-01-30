import UemProofs.UEM.UEM_MetaStrata
import UemProofs.UEM.UEM_MetaDefinability

namespace UEM

/-!
Strata bridges: connect epistemic/definability layers to non‑linear strata.
Pure structure only; no external examples.
-/

structure EpistemicStrataBridge (E : EpistemicSystem) (S : StrataSystem)
    (T : ImpossibilityTopology S) where
  map_obj : E.Obj → S.Stratum
  recognizable_to_possible :
    ∀ x, E.Recognizable x → map_obj x ∈ T.possible
  unrecognizable_to_impossible :
    ∀ x, ¬ E.Recognizable x → map_obj x ∈ T.impossible

/-- Possible region is closed under boundary inclusion into impossible. -/
theorem boundary_of_possible_impossible
    {E : EpistemicSystem} {S : StrataSystem} {T : ImpossibilityTopology S}
    (B : EpistemicStrataBridge E S T) (x : E.Obj) :
    B.map_obj x ∈ (by
      classical
      let _ : TopologicalSpace S.Stratum := T.topo
      exact closure T.possible \ T.possible) →
      B.map_obj x ∈ T.impossible := by
  classical
  let _ : TopologicalSpace S.Stratum := T.topo
  exact T.boundary_possible_subset_impossible (B.map_obj x)

structure DefinabilityStrataBridge (D : DefinabilitySystem) (S : StrataSystem) where
  map_obj : D.U → S.Stratum
  definable_to_stratum : ∀ x, D.Definable x → True

end UEM
