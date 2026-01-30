import UemProofs.UEM.UEM_Calculus

namespace UEM

/-!
# UEM Hangul Operator Matrix

This module formalizes the **C/V/F matrix** as a total classification over syllables.
It does *not* replace `CMap/VMap/FMap`; instead it provides a principled
relation that can be used to derive or validate concrete mappings.
-/

/-- Consonant (C) classes: domain origin categories. -/
inductive CClass
  | ignitor  -- void/spark origin
  | mover    -- vector/actyon origin
  | builder  -- tensor/escalade origin
  | base     -- scalar origin
  deriving DecidableEq, Repr

/-- Vowel (V) classes: operator logic categories. -/
inductive VClass
  | linear
  | vertical
  | horizontal
  | fractal
  deriving DecidableEq, Repr

/-- Final (F) classes: codomain target categories. -/
inductive FClass
  | solid   -- Secare
  | fluid   -- Actyon
  | null    -- Margin
  deriving DecidableEq, Repr

/-- Classification of choseong into domain classes. -/
def CClassOf : Choseong → CClass
  | .g  => .ignitor
  | .k  => .ignitor
  | .ch => .ignitor
  | .gg => .ignitor
  | .n  => .mover
  | .d  => .mover
  | .r  => .mover
  | .t  => .mover
  | .p  => .mover
  | .dd => .mover
  | .m  => .builder
  | .b  => .builder
  | .s  => .builder
  | .j  => .builder
  | .bb => .builder
  | .ss => .builder
  | .jj => .builder
  | .ng => .base
  | .h  => .base

/-- Classification of jungseong into operator classes. -/
def VClassOf : Jungseong → VClass
  | .eu => .linear
  | .a  => .vertical
  | .eo => .vertical
  | .o  => .horizontal
  | .u  => .horizontal
  | .oe => .horizontal
  | .wi => .horizontal
  | _   => .fractal

/-- Classification of jongseong into codomain classes.
    Rule: clusters reduce to their primary component. -/
def FClassOf : Option Jongseong → FClass
  | none => .null
  | some f =>
      match FPrimary f with
      | .g | .d | .b | .s | .ss | .j | .k | .t | .p | .ch => .solid
      | .n | .r | .m | .ng => .fluid
      | .h => .null
      | .gg | .gs | .nj | .nh | .rg | .rm | .rb | .rs | .rt | .rp | .rh | .bs => .solid

/-- Helper predicates for domains. -/
def IsVectorType : ObjType → Prop
  | .vector _ => True
  | _ => False

/-- Helper predicates for tensors. -/
def IsTensorType : ObjType → Prop
  | .tensor _ => True
  | _ => False

@[simp] lemma isVector_defaultVector : IsVectorType defaultVector := by
  simp [defaultVector, IsVectorType]

@[simp] lemma isTensor_defaultTensor : IsTensorType defaultTensor := by
  simp [defaultTensor, IsTensorType]

/-- Domain predicate induced by consonant class. -/
def DomPred : CClass → ObjType → Prop
  | .ignitor, a => a = .world ∨ a = .spark
  | .mover,   a => IsVectorType a ∨ a = .actyon
  | .builder, a => IsTensorType a ∨ a = .escalade
  | .base,    a => a = .scalar

/-- Codomain predicate induced by final class. -/
def CodPred : FClass → ObjType → Prop
  | .solid, a => a = .secare
  | .fluid, a => a = .actyon
  | .null,  a => a = .margin

/-- Logic predicate induced by vowel class. -/
def LogicPred : VClass → ObjType → ObjType → Prop
  | .linear, a, b => a = b
  | .vertical, _, b => IsVectorType b
  | .horizontal, _, b => IsVectorType b
  | .fractal, _, b => IsTensorType b

/-- Classification-only relation (pure class rules; not necessarily realized by C/V/F maps). -/
def MatrixClassRel (s : Syllable) (a b : ObjType) : Prop :=
  DomPred (CClassOf s.c) a ∧ LogicPred (VClassOf s.v) a b ∧ CodPred (FClassOf s.f?) b

/-- Exact matrix relation via term existence (actual C/V/F map chain). -/
def MatrixRel (s : Syllable) (a b : ObjType) : Prop :=
  ∃ t, syllableTerm a s = some ⟨b, t⟩

@[simp] theorem MatrixRel_def {s : Syllable} {a b : ObjType} :
    MatrixRel s a b ↔ (∃ t, syllableTerm a s = some ⟨b, t⟩) := by
  rfl

/-- Every syllable has a well-defined class triple. -/
lemma matrix_total (s : Syllable) :
    ∃ cc vc fc, cc = CClassOf s.c ∧ vc = VClassOf s.v ∧ fc = FClassOf s.f? := by
  refine ⟨CClassOf s.c, VClassOf s.v, FClassOf s.f?, rfl, rfl, rfl⟩

/-! ## Consistency with concrete maps (CMap/VMap/FMap) -/

lemma CMap_sound {c : Choseong} {a b : ObjType} (h : CMap c a = some b) :
    DomPred (CClassOf c) a := by
  cases c <;> cases a <;>
    simp [CMap, CClassOf, DomPred, IsVectorType, IsTensorType] at h ⊢

lemma VMap_sound {v : Jungseong} {a b : ObjType} (h : VMap v a = some b) :
    LogicPred (VClassOf v) a b := by
  cases v <;> cases a <;> cases h <;>
    simp [VClassOf, LogicPred]

lemma FMap_sound {f : Jongseong} {a b : ObjType} (h : FMap f a = some b) :
    CodPred (FClassOf (some f)) b := by
  cases f <;> cases a <;> cases h <;>
    simp [FClassOf, FPrimary, CodPred]

@[simp] lemma FClassOf_none : FClassOf none = .null := rfl

@[simp] lemma FClassOf_some_h : FClassOf (some Jongseong.h) = .null := by
  rfl

/-! ## Exact relation ↔ syllableTerm -/

theorem syllableTerm_of_MatrixRel {a b : ObjType} {s : Syllable}
    (h : MatrixRel s a b) : ∃ t, syllableTerm a s = some ⟨b, t⟩ := by
  simpa using h

theorem MatrixRel_of_syllableTerm {a b : ObjType} {s : Syllable}
    (h : ∃ t, syllableTerm a s = some ⟨b, t⟩) : MatrixRel s a b := by
  simpa using h

theorem MatrixRel_iff_syllableTerm {a b : ObjType} {s : Syllable} :
    (∃ t, syllableTerm a s = some ⟨b, t⟩) ↔ MatrixRel s a b := by
  rfl

end UEM
