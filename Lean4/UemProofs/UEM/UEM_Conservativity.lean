import UemProofs.UEM.UEM_Calculus

namespace UEM

/-!
Conservativity of the observed fragment inside the full UEM core.
This is a purely mathematical statement: the observed sublanguage embeds
into the full system without adding new equations about observed terms.
-/

/-! ## Observed object types -/

def ObservedObjType : Type := { a : ObjType // IsObserved a }

def obsInclusion : ObservedObjType → ObjType := Subtype.val

theorem obsInclusion_injective : Function.Injective obsInclusion := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

theorem exists_unobserved : ∃ a : ObjType, IsUnobserved a := by
  refine ⟨.spark, ?_⟩
  simp [IsUnobserved]

theorem obsInclusion_not_surjective : ¬Function.Surjective obsInclusion := by
  intro h
  rcases h .spark with ⟨a, ha⟩
  -- a is observed by construction, but maps to an unobserved type.
  have : IsObserved (.spark) := by
    -- transport the predicate from a to spark
    cases a with
    | mk a ha' =>
      -- ha : a = .spark
      have : a = .spark := by
        simpa [obsInclusion] using ha
      simpa [this] using ha'
  -- contradiction: spark is not observed
  cases this

/-! ## Observed operators and conservativity -/

structure ObservedOperator (a b : ObservedObjType) where
  apply : Carrier a.1 → Carrier b.1

def toFullOperator {a b : ObservedObjType} (f : ObservedOperator a b) :
    Operator a.1 b.1 :=
  ⟨f.apply⟩

def ofFullOperator {a b : ObservedObjType} (f : Operator a.1 b.1) :
    ObservedOperator a b :=
  ⟨f.apply⟩

def observed_operator_equiv (a b : ObservedObjType) :
    ObservedOperator a b ≃ Operator a.1 b.1 := by
  refine ⟨toFullOperator, ofFullOperator, ?_, ?_⟩
  · intro f
    cases f
    rfl
  · intro f
    cases f
    rfl

/-! ## Model existence for all core carriers -/

theorem carrier_nonempty : ∀ a : ObjType, Nonempty (Carrier a)
  | .scalar => ⟨0⟩
  | .vector _ => ⟨⟨fun _ => 0⟩⟩
  | .tensor _ => ⟨⟨fun _ => 0⟩⟩
  | .spark => ⟨{}⟩
  | .actyon => ⟨{}⟩
  | .escalade => ⟨{}⟩
  | .secare => ⟨{}⟩
  | .world => ⟨{}⟩
  | .observer => ⟨{}⟩
  | .margin => ⟨{}⟩
  | .possibleWorld => ⟨{ world := {}, mode := .possible }⟩
  | .descriptor => ⟨{}⟩
  | .nat => ⟨0⟩
  | .prod a b =>
      match carrier_nonempty a, carrier_nonempty b with
      | ⟨x⟩, ⟨y⟩ => ⟨(x, y)⟩

end UEM
