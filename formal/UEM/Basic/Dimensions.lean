import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

/-! Epistemic dimensions and their coordinate types. -/
namespace UEM

/-- 9 Epistemic Dimensions -/
inductive Dimension : Type
| Time        -- d1: Physical/Epistemic Time
| Ontic       -- d2: Existence Strength [0,1]
| Logic       -- d3: Truth Value {T, F, U, C}
| Modality    -- d4: Possible Worlds
| Agency      -- d5: Agent * Role
| Epistemic   -- d6: Knowledge State {K, U, E, X}
| Value       -- d7: Utility * Norm
| Repr        -- d8: Theory * Language
| Limit       -- d9: Meta-limit (l, k, r)
deriving DecidableEq

/-! ### Coordinate carriers (concrete stubs to avoid implicit assumptions) -/

structure OnticCoord where
  val : ℝ
  h0 : 0 ≤ val
  h1 : val ≤ 1

inductive LogicCoord
| tt | ff | unknown | both

inductive ModalityCoord
| box | dia | bot

structure AgencyCoord where
  agent : String
  role  : String

structure ValueCoord where
  utility : Float
  norm    : Float

structure ReprCoord where
  theory   : String
  language : String

structure LimitCoord where
  level : Int

/-- Coordinate space per dimension. -/
def Coord : Dimension → Type
| Dimension.Time      => Int
| Dimension.Ontic     => OnticCoord
| Dimension.Logic     => LogicCoord
| Dimension.Modality  => ModalityCoord
| Dimension.Agency    => AgencyCoord
| Dimension.Epistemic => Unit
| Dimension.Value     => ValueCoord
| Dimension.Repr      => ReprCoord
| Dimension.Limit     => LimitCoord

/-- Epistemic record space as dependent product of all coordinates. -/
def X_rec : Type := (d : Dimension) → Coord d

namespace X_rec

/-- Project to a single dimension. -/
def proj (x : X_rec) (d : Dimension) : Coord d := x d

/-- Update one coordinate, keeping others unchanged. -/
def update (x : X_rec) (d : Dimension) (v : Coord d) : X_rec :=
  fun d' => if h : d' = d then by simpa [h] using v else by simpa [h] using x d'

@[simp] lemma update_self (x : X_rec) (d : Dimension) (v : Coord d) :
    (update x d v) d = v := by
  simp [update]

@[simp] lemma update_other (x : X_rec) {d d' : Dimension} (h : d' ≠ d) (v : Coord d) :
    (update x d v) d' = x d' := by
  simp [update, h]

end X_rec

end UEM
