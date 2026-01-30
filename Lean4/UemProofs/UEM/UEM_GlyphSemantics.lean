import UemProofs.UEM.UEM_Calculus

namespace UEM

/-!
Glyph semantics: operator × direction × state as a single container.
This encodes the non-linear Hangul composition requirement.
-/

/-- A Hangul glyph as (choseong, jungseong, jongseong). -/
structure Glyph where
  c : Choseong
  v : Jungseong
  f : Jongseong

/-- Abstract semantics for glyph components. -/
structure GlyphSemantics where
  Op : Type
  Dir : Type
  State : Type
  opOf : Choseong → Op
  dirOf : Jungseong → Dir
  stateOf : Jongseong → State

/-- Interpreted glyph (operator × direction × state). -/
structure GlyphOp (Op Dir State : Type) where
  op : Op
  dir : Dir
  st : State

/-- Evaluate a glyph under given semantics. -/
def evalGlyph (S : GlyphSemantics) (g : Glyph) : GlyphOp S.Op S.Dir S.State :=
  { op := S.opOf g.c, dir := S.dirOf g.v, st := S.stateOf g.f }

/-- Composition with a typing/constraint witness (non-commutativity allowed). -/
structure GlyphComposition (Op Dir State : Type) where
  compose : GlyphOp Op Dir State → GlyphOp Op Dir State → GlyphOp Op Dir State
  typing_ok : GlyphOp Op Dir State → GlyphOp Op Dir State → Prop

/-- Non-commutativity witness for directional composition. -/
structure NonCommutative (Op Dir State : Type) extends GlyphComposition Op Dir State where
  noncomm : ∃ a b, compose a b ≠ compose b a

/-- Definitional projection: eval uses the chosen component maps. -/
theorem evalGlyph_op (S : GlyphSemantics) (g : Glyph) :
    (evalGlyph S g).op = S.opOf g.c :=
  rfl

end UEM
