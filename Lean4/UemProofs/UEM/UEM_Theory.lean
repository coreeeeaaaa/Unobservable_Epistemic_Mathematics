import UemProofs.UEM.UEM_Calculus
import UemProofs.UEM.UEM_CartesianProduct

namespace UEM

/-!
UEM-0 theory layer: operator terms and a rule-based derivation system.
The fragment is limited to ObjType, Operator, product objects, and
fst/snd/lift equations.
-/

inductive UEM0OpTerm : ObjType → ObjType → Type where
  | base : Operator a b → UEM0OpTerm a b
  | id : UEM0OpTerm a a
  | comp : UEM0OpTerm b c → UEM0OpTerm a b → UEM0OpTerm a c
  | fst : UEM0OpTerm (.prod a b) a
  | snd : UEM0OpTerm (.prod a b) b
  | lift : UEM0OpTerm c a → UEM0OpTerm c b → UEM0OpTerm c (.prod a b)

/-- Evaluation into core operators. -/
def eval : UEM0OpTerm a b → Operator a b
  | .base f => f
  | .id => ⟨fun x => x⟩
  | .comp g f => Operator.comp (eval g) (eval f)
  | .fst => fstOp _ _
  | .snd => sndOp _ _
  | .lift f g => liftOp (eval f) (eval g)

/-- Rule-based derivation system for UEM0OpTerm equations. -/
inductive Derives : UEM0OpTerm a b → UEM0OpTerm a b → Prop where
  | refl (t : UEM0OpTerm a b) : Derives t t
  | symm {t u : UEM0OpTerm a b} : Derives t u → Derives u t
  | trans {t u v : UEM0OpTerm a b} : Derives t u → Derives u v → Derives t v
  | congr_comp {a b c : ObjType}
      {g g' : UEM0OpTerm b c} {f f' : UEM0OpTerm a b} :
      Derives g g' → Derives f f' → Derives (.comp g f) (.comp g' f')
  | congr_lift {c a b : ObjType}
      {f f' : UEM0OpTerm c a} {g g' : UEM0OpTerm c b} :
      Derives f f' → Derives g g' → Derives (.lift f g) (.lift f' g')
  | prod_fst_lift {c a b : ObjType} (f : UEM0OpTerm c a) (g : UEM0OpTerm c b) :
      Derives (.comp (.fst (a:=a) (b:=b)) (.lift f g)) f
  | prod_snd_lift {c a b : ObjType} (f : UEM0OpTerm c a) (g : UEM0OpTerm c b) :
      Derives (.comp (.snd (a:=a) (b:=b)) (.lift f g)) g
  | prod_unique {c a b : ObjType} (h : UEM0OpTerm c (.prod a b))
      (f : UEM0OpTerm c a) (g : UEM0OpTerm c b) :
      Derives (.comp (.fst (a:=a) (b:=b)) h) f →
      Derives (.comp (.snd (a:=a) (b:=b)) h) g →
      Derives h (.lift f g)

end UEM
