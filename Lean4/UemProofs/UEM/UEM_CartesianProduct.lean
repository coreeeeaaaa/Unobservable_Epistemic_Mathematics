import UemProofs.UEM.UEM_Calculus
import UemProofs.UEM.UEM_Structure

namespace UEM

/-!
Cartesian product universal property for ObjType with Operator morphisms.
This provides a categorical account of parallel pairing.
-/

def fstOp (a b : ObjType) : Operator (.prod a b) a :=
  ⟨Prod.fst⟩

def sndOp (a b : ObjType) : Operator (.prod a b) b :=
  ⟨Prod.snd⟩

def liftOp {c a b : ObjType} (f : Operator c a) (g : Operator c b) :
    Operator c (.prod a b) :=
  ⟨fun x => (f.apply x, g.apply x)⟩

theorem fstOp_comp_lift {c a b : ObjType} (f : Operator c a) (g : Operator c b) :
    Operator.comp (fstOp a b) (liftOp f g) = f := by
  ext x
  rfl

theorem sndOp_comp_lift {c a b : ObjType} (f : Operator c a) (g : Operator c b) :
    Operator.comp (sndOp a b) (liftOp f g) = g := by
  ext x
  rfl

theorem lift_unique {c a b : ObjType} (f : Operator c a) (g : Operator c b)
    (h : Operator c (.prod a b))
    (hfst : Operator.comp (fstOp a b) h = f)
    (hsnd : Operator.comp (sndOp a b) h = g) :
    h = liftOp f g := by
  apply Operator.ext
  intro x
  apply Prod.ext
  · have hf := congrArg (fun op => op.apply x) hfst
    simpa [Operator.comp, fstOp] using hf
  · have hg := congrArg (fun op => op.apply x) hsnd
    simpa [Operator.comp, sndOp] using hg

end UEM
