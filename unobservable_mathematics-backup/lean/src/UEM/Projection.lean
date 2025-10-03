import UEM.Structure

namespace UEM
namespace OverlapSystem

/--
Theorem 5.2 (Projection–overlap exchange) from `docs/UEM_formal_spec_v2.md`.
Given the homomorphism axiom (A3), the proof is immediate.
-/
theorem projectionOverlapExchange (S : OverlapSystem)
    (A B : S.Obj) :
    S.projection (S.overlap A B) =
      S.phi (S.projection A) (S.projection B) :=
  S.projection_hom

end OverlapSystem
end UEM
