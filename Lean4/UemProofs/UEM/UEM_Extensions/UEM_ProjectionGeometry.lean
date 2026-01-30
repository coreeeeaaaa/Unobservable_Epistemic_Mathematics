import UemProofs.UEM.UEM_Calculus

namespace UEM

/-!
Projection/Dimension‑Reduction skeletons.
No axioms: laws are carried as structure fields.
-/

/-- Abstract projection system on objects and coordinates. -/
structure ProjectionSystem where
  projObj : ObjType → ObjType
  projCoord : ∀ {side height depth : Nat},
    Coord side height depth → Coord side height depth
  idempotent : ∀ a, projObj (projObj a) = projObj a
  coord_idempotent : ∀ {side height depth} (c : Coord side height depth),
    projCoord (projCoord c) = projCoord c

abbrev PiOp := ProjectionSystem

/-- Extract projection idempotence (structural law). -/
theorem projObj_idempotent (P : ProjectionSystem) (a : ObjType) :
    P.projObj (P.projObj a) = P.projObj a :=
  P.idempotent a

/-! ## Set-level projection exchange (idempotent image) -/

def projSet (P : ProjectionSystem) (S : Set ObjType) : Set ObjType :=
  P.projObj '' S

theorem projSet_idempotent (P : ProjectionSystem) (S : Set ObjType) :
    projSet P (projSet P S) = projSet P S := by
  classical
  ext a
  constructor
  · intro ha
    rcases ha with ⟨b, hb, hba⟩
    rcases hb with ⟨x, hxS, rfl⟩
    -- a = P.projObj (P.projObj x) = P.projObj x
    have : P.projObj (P.projObj x) = P.projObj x := P.idempotent x
    refine ⟨x, hxS, ?_⟩
    simpa [hba] using this.symm
  · intro ha
    rcases ha with ⟨x, hxS, rfl⟩
    refine ⟨P.projObj x, ?_, ?_⟩
    · exact ⟨x, hxS, rfl⟩
    · exact P.idempotent x

/-- Extract coordinate projection idempotence (structural law). -/
theorem projCoord_idempotent (P : ProjectionSystem)
    {side height depth : Nat} (c : Coord side height depth) :
    P.projCoord (P.projCoord c) = P.projCoord c :=
  P.coord_idempotent c

/-- Dimension reduction system (non‑material). -/
structure DimReduction where
  reduce : Nat → Nat
  monotone : ∀ {n m}, n ≤ m → reduce n ≤ reduce m
  idempotent : ∀ n, reduce (reduce n) = reduce n

abbrev D_Pi := DimReduction

/-- Extract idempotence for dimension reduction. -/
theorem DimReduction_idempotent (D : DimReduction) (n : Nat) :
    D.reduce (D.reduce n) = D.reduce n :=
  D.idempotent n

/-!
Generic projection/kernel/aliasing on arbitrary types (non-linear formal core).
-/

structure ProjectionSystem' (H L : Type u) where
  proj : H → L

def Alias {H L : Type u} (P : ProjectionSystem' H L) (x y : H) : Prop :=
  P.proj x = P.proj y

structure KernelizedProjection (H L : Type u) extends ProjectionSystem' H L where
  kernel : H → H → Prop
  kernel_iff : ∀ x y, kernel x y ↔ proj x = proj y

theorem kernel_iff_alias {H L : Type u} (P : KernelizedProjection H L) (x y : H) :
    P.kernel x y ↔ Alias (ProjectionSystem'.mk P.proj) x y :=
  P.kernel_iff x y

end UEM
