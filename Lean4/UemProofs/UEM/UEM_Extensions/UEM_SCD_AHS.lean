import UemProofs.UEM.UEM_Extensions.UEM_Dynamics
import Mathlib.Data.Set.Lattice

namespace UEM

/-!
Stable Compressed Dynamics (SCD) and Quasi-Hyperbolic Structure (AHS).
Pure structural definitions with laws carried as fields (no axioms).
-/

/-! ## SCD -/

structure SCDSystem (side height depth : Nat) where
  dyn : Dynamics side height depth
  compression : Cube side height depth → ℝ
  stable_step : ∀ x, dyn.invariant x → compression (dyn.next x) ≤ compression x

abbrev SCD (side height depth : Nat) := SCDSystem side height depth

theorem SCDSystem.stable_step' {side height depth : Nat} (S : SCDSystem side height depth)
    (x : Cube side height depth) (hx : S.dyn.invariant x) :
    S.compression (S.dyn.next x) ≤ S.compression x :=
  S.stable_step x hx

/-! ## AHS -/

structure QuasiHyperbolicStructure (X : Type u) where
  phaseSpace : Set X
  stableBundle : Set X
  unstableBundle : Set X
  stable_subset : stableBundle ⊆ phaseSpace
  unstable_subset : unstableBundle ⊆ phaseSpace
  bounded : Prop

abbrev AHS (X : Type u) := QuasiHyperbolicStructure X

theorem stable_in_phase {X : Type u} (A : QuasiHyperbolicStructure X) {x : X}
    (hx : x ∈ A.stableBundle) : x ∈ A.phaseSpace :=
  A.stable_subset hx

theorem unstable_in_phase {X : Type u} (A : QuasiHyperbolicStructure X) {x : X}
    (hx : x ∈ A.unstableBundle) : x ∈ A.phaseSpace :=
  A.unstable_subset hx

end UEM
