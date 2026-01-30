import UemProofs.UEM.UEM_Calculus

namespace UEM

/-- Extended coordinate carrying explicit time/world/observer metadata. -/
structure CoordPlus (side height depth : Nat) where
  base : Coord side height depth
  dimOrder : Nat
  time : Int
  world : WorldData
  observer : ObserverData
  descriptor : Descriptor
  modality : Modality

/-- Projection to the core coordinate. -/
def CoordPlus.toCoord {side height depth : Nat} (c : CoordPlus side height depth) :
    Coord side height depth :=
  c.base

/-- Extended slot using `CoordPlus` and reusing core metadata layout. -/
structure SlotPlus (side height depth : Nat) where
  coord : CoordPlus side height depth
  payload : TypedObject
  glyph : Option Syllable
  dir : Direction
  dim : Dimension

/-- Build core meta-info from the extended coordinate. -/
def CoordPlus.toMeta {side height depth : Nat} (c : CoordPlus side height depth) : Meta :=
  { world := c.world
    observer := c.observer
    modality := c.modality
    time := c.time
    descriptor := c.descriptor }

/-- Forgetful map from extended slots to core slots. -/
def SlotPlus.toSlot {side height depth : Nat} (s : SlotPlus side height depth) :
    Slot side height depth :=
  { coord := s.coord.base
    payload := s.payload
    glyph := s.glyph
    dir := s.dir
    dim := s.dim
    metaInfo := s.coord.toMeta }

end UEM
