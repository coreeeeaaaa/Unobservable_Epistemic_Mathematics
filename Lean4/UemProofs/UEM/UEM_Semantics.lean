import UemProofs.UEM.UEM_Calculus
import UemProofs.UEM.UEM_Theory

namespace UEM

/-- Model for UEM-0: carriers and product operations with equations. -/
structure Model where
  Carrier : ObjType → Type
  interp : {a b : ObjType} → Operator a b → Carrier a → Carrier b
  fst : {a b : ObjType} → Carrier (.prod a b) → Carrier a
  snd : {a b : ObjType} → Carrier (.prod a b) → Carrier b
  lift : {c a b : ObjType} → (Carrier c → Carrier a) → (Carrier c → Carrier b) →
    Carrier c → Carrier (.prod a b)
  fst_lift : ∀ {c a b} (f : Carrier c → Carrier a) (g : Carrier c → Carrier b) (x : Carrier c),
    fst (lift f g x) = f x
  snd_lift : ∀ {c a b} (f : Carrier c → Carrier a) (g : Carrier c → Carrier b) (x : Carrier c),
    snd (lift f g x) = g x
  lift_unique : ∀ {c a b} (h : Carrier c → Carrier (.prod a b))
      (f : Carrier c → Carrier a) (g : Carrier c → Carrier b),
      (∀ x, fst (h x) = f x) →
      (∀ x, snd (h x) = g x) →
      h = lift f g

/-- Evaluation of operator terms in a model. -/
def evalM (M : Model) : UEM0OpTerm a b → M.Carrier a → M.Carrier b
  | .base f => M.interp f
  | .id => fun x => x
  | .comp g f => fun x => evalM M g (evalM M f x)
  | .fst => M.fst
  | .snd => M.snd
  | .lift f g => fun x => M.lift (evalM M f) (evalM M g) x

/-- The current UEM core forms a model of UEM-0. -/
def coreModel : Model where
  Carrier := Carrier
  interp := fun f => f.apply
  fst := fun x => x.1
  snd := fun x => x.2
  lift := fun f g x => (f x, g x)
  fst_lift := by
    intro c a b f g x
    rfl
  snd_lift := by
    intro c a b f g x
    rfl
  lift_unique := by
    intro c a b h f g hfst hsnd
    funext x
    apply Prod.ext
    · exact hfst x
    · exact hsnd x

end UEM
