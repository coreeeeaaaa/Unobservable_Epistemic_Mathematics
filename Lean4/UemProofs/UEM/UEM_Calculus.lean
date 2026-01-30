import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import UemProofs.UEM.UEM_Foundations

noncomputable section

open scoped ENNReal

namespace UEM

/-!
# UEM Calculus (Pure Formal Core)

This file formalizes the *purely mathematical* core requested:
- Object/operator separation (types vs. morphisms)
- Hangul syllable calculus via C/V/F decomposition
- Slot/Cube coordinate system with depth
- Typed composition and parallel composition
- No application layer, no axioms, no sorries
-/

/-- Observed scalar values. -/
abbrev Scalar : Type := ℝ

/-- Observed vectors (fixed dimension `n`). -/
structure Vector (n : Nat) where
  data : Fin n → Scalar

/-- Observed tensors (fixed rank `k`). -/
structure Tensor (k : Nat) where
  data : Fin k → Scalar

/-- Epistemic spark. -/
structure Spark where
  origin : Scalar := 0

/-- Epistemic actyon. -/
structure Actyon where
  direction : Scalar := 1
  intensity : Nat := 1

/-- Epistemic escalade. -/
structure Escalade where
  depth : Nat := 0

/-- Epistemic secare. -/
structure Secare where
  thickness : ℝ≥0∞ := 0

notation "⛦" => Spark
notation "ㆁ" => Actyon
notation "𓂌" => Escalade
notation "♡" => Secare

/-- A lightweight world tag used in the formal core. -/
structure WorldData where
  tag : Nat := 0

/-- A lightweight observer tag used in the formal core. -/
structure ObserverData where
  tag : Nat := 0

/-- Margin tag. -/
structure MarginData where
  tag : Nat := 0

/-- Descriptive tag for semantic/intent metadata. -/
structure Descriptor where
  text : String := ""

/-- Modal status for possible worlds. -/
inductive Modality
  | actual
  | past
  | future
  | counterfactual
  | possible
  | impossible
  | unknown
  deriving DecidableEq, Repr

/-- Possible world wrapper. -/
structure PossibleWorld where
  world : WorldData
  mode : Modality

/-- UEM object types (objects are *not* operators). -/
inductive ObjType : Type
  | scalar
  | vector (n : Nat)
  | tensor (k : Nat)
  | spark
  | actyon
  | escalade
  | secare
  | world
  | observer
  | margin
  | possibleWorld
  | descriptor
  | nat
  | prod (a b : ObjType)
  deriving DecidableEq, Repr

/-- Carrier for each object type. -/
abbrev Carrier : ObjType → Type
  | .scalar => Scalar
  | .vector n => Vector n
  | .tensor k => Tensor k
  | .spark => Spark
  | .actyon => Actyon
  | .escalade => Escalade
  | .secare => Secare
  | .world => WorldData
  | .observer => ObserverData
  | .margin => MarginData
  | .possibleWorld => PossibleWorld
  | .descriptor => Descriptor
  | .nat => Nat
  | .prod a b => Carrier a × Carrier b

/-- Observed (material) object types. -/
def IsObserved : ObjType → Prop
  | .scalar => True
  | .vector _ => True
  | .tensor _ => True
  | _ => False

/-- Unobserved (epistemic) object types. -/
def IsUnobserved : ObjType → Prop
  | .spark => True
  | .actyon => True
  | .escalade => True
  | .secare => True
  | _ => False

/-- Typed object value. -/
structure TypedObject where
  ty : ObjType
  val : Carrier ty

/-- Typed operator (morphism) between object types. -/
structure Operator (a b : ObjType) where
  apply : Carrier a → Carrier b

@[ext] theorem Operator.ext {a b : ObjType} (f g : Operator a b)
    (h : ∀ x, f.apply x = g.apply x) : f = g := by
  cases f with
  | mk f_apply =>
      cases g with
      | mk g_apply =>
          have h' : f_apply = g_apply := funext h
          cases h'
          rfl

/-- Operator composition. -/
def Operator.comp {a b c : ObjType} (g : Operator b c) (f : Operator a b) : Operator a c :=
  ⟨fun x => g.apply (f.apply x)⟩

/-- Parallel (tensor) composition on product objects. -/
def Operator.par {a b c d : ObjType} (f : Operator a b) (g : Operator c d) :
    Operator (.prod a c) (.prod b d) :=
  ⟨fun x => (f.apply x.1, g.apply x.2)⟩

infixl:70 " ⊙ " => Operator.par

/-- A sum type for objects vs. operators (disjoint by construction). -/
inductive UEMEntity where
  | obj (o : TypedObject)
  | op  {a b : ObjType} (t : Operator a b)

/-- Objects and operators are disjoint. -/
theorem object_ne_operator (o : TypedObject) {a b : ObjType} (t : Operator a b) :
    UEMEntity.obj o ≠ UEMEntity.op t := by
  intro h
  cases h

/-- Default dimension used in the core signature table. -/
def DefaultDim : Nat := 3

/-- Basic derived types used in the core signature table. -/
def defaultVector : ObjType := .vector DefaultDim

def defaultTensor : ObjType := .tensor DefaultDim

/-- Core progression operators (purely typed). -/
def CreateSpark : Operator .world .spark :=
  ⟨fun w => { origin := (w.tag : ℝ) }⟩

def Ignite : Operator .spark .actyon :=
  ⟨fun s => { direction := s.origin, intensity := Nat.succ 0 }⟩

def Escalate : Operator (.prod .actyon .nat) .escalade :=
  ⟨fun p => { depth := p.1.intensity + (p.2 : Nat) }⟩

def Commit : Operator .escalade .secare :=
  ⟨fun e => { thickness := e.depth }⟩

theorem CreateSpark_type_preserving (w : WorldData) :
    (CreateSpark.apply w : Carrier .spark) = { origin := (w.tag : ℝ) } := rfl

theorem Ignite_type_preserving (s : Spark) :
    (Ignite.apply s : Carrier .actyon) = { direction := s.origin, intensity := Nat.succ 0 } := rfl

theorem Escalate_type_preserving (a : Actyon) (n : Nat) :
    (Escalate.apply (a, n) : Carrier .escalade) = { depth := a.intensity + n } := rfl

theorem Commit_type_preserving (e : Escalade) :
    (Commit.apply e : Carrier .secare) = { thickness := e.depth } := rfl

/-! ## Hangul Syllable System (C/V/F) -/

/-- Choseong (initial consonants). -/
inductive Choseong
  | g | n | d | r | m | b | s | ng | j | ch | k | t | p | h
  | gg | dd | bb | ss | jj
  deriving DecidableEq, Repr

notation "ㄱ" => Choseong.g
notation "ㄴ" => Choseong.n
notation "ㄷ" => Choseong.d
notation "ㄹ" => Choseong.r
notation "ㅁ" => Choseong.m
notation "ㅂ" => Choseong.b
notation "ㅅ" => Choseong.s
notation "ㅇ" => Choseong.ng
notation "ㅈ" => Choseong.j
notation "ㅊ" => Choseong.ch
notation "ㅋ" => Choseong.k
notation "ㅌ" => Choseong.t
notation "ㅍ" => Choseong.p
notation "ㅎ" => Choseong.h
notation "ㄲ" => Choseong.gg
notation "ㄸ" => Choseong.dd
notation "ㅃ" => Choseong.bb
notation "ㅆ" => Choseong.ss
notation "ㅉ" => Choseong.jj

/-- Jungseong (vowels). -/
inductive Jungseong
  | a | ya | eo | yeo | o | yo | u | yu | eu | i
  | ae | e | oe | wi | ui | wa | wae | wo | we | ye | yae
  deriving DecidableEq, Repr

notation "ㅏ" => Jungseong.a
notation "ㅑ" => Jungseong.ya
notation "ㅓ" => Jungseong.eo
notation "ㅕ" => Jungseong.yeo
notation "ㅗ" => Jungseong.o
notation "ㅛ" => Jungseong.yo
notation "ㅜ" => Jungseong.u
notation "ㅠ" => Jungseong.yu
notation "ㅡ" => Jungseong.eu
notation "ㅣ" => Jungseong.i
notation "ㅐ" => Jungseong.ae
notation "ㅔ" => Jungseong.e
notation "ㅚ" => Jungseong.oe
notation "ㅟ" => Jungseong.wi
notation "ㅢ" => Jungseong.ui
notation "ㅘ" => Jungseong.wa
notation "ㅙ" => Jungseong.wae
notation "ㅝ" => Jungseong.wo
notation "ㅞ" => Jungseong.we
notation "ㅖ" => Jungseong.ye
notation "ㅒ" => Jungseong.yae

/-- Jongseong (final consonants). -/
inductive Jongseong
  | g | n | d | r | m | b | s | ng | j | ch | k | t | p | h
  | gg | gs | nj | nh | rg | rm | rb | rs | rt | rp | rh | bs
  deriving DecidableEq, Repr

notation "ㄱₓ" => Jongseong.g
notation "ㄴₓ" => Jongseong.n
notation "ㄷₓ" => Jongseong.d
notation "ㄹₓ" => Jongseong.r
notation "ㅁₓ" => Jongseong.m
notation "ㅂₓ" => Jongseong.b
notation "ㅅₓ" => Jongseong.s
notation "ㅇₓ" => Jongseong.ng
notation "ㅈₓ" => Jongseong.j
notation "ㅊₓ" => Jongseong.ch
notation "ㅋₓ" => Jongseong.k
notation "ㅌₓ" => Jongseong.t
notation "ㅍₓ" => Jongseong.p
notation "ㅎₓ" => Jongseong.h
notation "ㄲₓ" => Jongseong.gg
notation "ㄳₓ" => Jongseong.gs
notation "ㄵₓ" => Jongseong.nj
notation "ㄶₓ" => Jongseong.nh
notation "ㄺₓ" => Jongseong.rg
notation "ㄻₓ" => Jongseong.rm
notation "ㄼₓ" => Jongseong.rb
notation "ㄽₓ" => Jongseong.rs
notation "ㄾₓ" => Jongseong.rt
notation "ㄿₓ" => Jongseong.rp
notation "ㅀₓ" => Jongseong.rh
notation "ㅄₓ" => Jongseong.bs

/-- Primary base for compound finals (batchim clusters). -/
def FPrimary : Jongseong → Jongseong
  | .gg => .g
  | .gs => .g
  | .nj => .n
  | .nh => .n
  | .rg => .r
  | .rm => .r
  | .rb => .r
  | .rs => .r
  | .rt => .r
  | .rp => .r
  | .rh => .r
  | .bs => .b
  | f   => f

/-- A syllable is a (C, V, F?) triple. -/
structure Syllable where
  c : Choseong
  v : Jungseong
  f? : Option Jongseong
  deriving DecidableEq, Repr

/-- Consonant type map: input type ↦ output type (partial). -/
def CMap : Choseong → ObjType → Option ObjType
  -- ignitor class: world/spark → spark
  | .g, .world => some .spark
  | .g, .spark => some .spark
  | .k, .world => some .spark
  | .k, .spark => some .spark
  | .ch, .world => some .spark
  | .ch, .spark => some .spark
  | .gg, .world => some .spark
  | .gg, .spark => some .spark
  -- mover class: vector/actyon → vector/actyon
  | .n, .vector _ => some defaultVector
  | .n, .actyon => some .actyon
  | .d, .vector _ => some defaultVector
  | .d, .actyon => some .actyon
  | .r, .vector _ => some defaultVector
  | .r, .actyon => some .actyon
  | .t, .vector _ => some defaultVector
  | .t, .actyon => some .actyon
  | .p, .vector _ => some defaultVector
  | .p, .actyon => some .actyon
  | .dd, .vector _ => some defaultVector
  | .dd, .actyon => some .actyon
  -- builder class: tensor/escalade → tensor/escalade
  | .m, .tensor _ => some defaultTensor
  | .m, .escalade => some .escalade
  | .b, .tensor _ => some defaultTensor
  | .b, .escalade => some .escalade
  | .s, .tensor _ => some defaultTensor
  | .s, .escalade => some .escalade
  | .j, .tensor _ => some defaultTensor
  | .j, .escalade => some .escalade
  | .bb, .tensor _ => some defaultTensor
  | .bb, .escalade => some .escalade
  | .ss, .tensor _ => some defaultTensor
  | .ss, .escalade => some .escalade
  | .jj, .tensor _ => some defaultTensor
  | .jj, .escalade => some .escalade
  -- base class: scalar → scalar
  | .ng, .scalar => some .scalar
  | .h, .scalar => some .scalar
  | _, _ => none

/-- Admissible domain predicate for CMap. -/
def CAdmissible (c : Choseong) (a : ObjType) : Prop :=
  (CMap c a).isSome

/-- Vowel type map: input type ↦ output type (partial). -/
def VMap : Jungseong → ObjType → Option ObjType
  -- linear: identity (ㅡ)
  | .eu, a => some a
  -- vertical: map to vector
  | .a, _ => some defaultVector
  | .eo, _ => some defaultVector
  -- horizontal: map to vector
  | .o, _ => some defaultVector
  | .u, _ => some defaultVector
  | .oe, _ => some defaultVector
  | .wi, _ => some defaultVector
  -- fractal: map to tensor
  | _, _ => some defaultTensor

/-- Admissible domain predicate for VMap. -/
def VAdmissible (v : Jungseong) (a : ObjType) : Prop :=
  (VMap v a).isSome

/-! ## VMap Coverage Theorem -/

/-- VMap provides total coverage over all 21 Jungseong vowels.
    For every vowel, there exists some input type that maps to a valid output type. -/
theorem VMap_total_coverage :
    ∀ (v : Jungseong), ∃ (a : ObjType) (b : ObjType), VMap v a = some b := by
  intro v
  -- Case analysis on all 21 Jungseong constructors
  cases v
  -- Linear class (identity)
  case eu =>
    refine ⟨.scalar, .scalar, ?_⟩
    rfl
  -- Vertical class (vector)
  case a =>
    refine ⟨.scalar, defaultVector, ?_⟩
    rfl
  case eo =>
    refine ⟨.scalar, defaultVector, ?_⟩
    rfl
  -- Horizontal class (vector)
  case o =>
    refine ⟨.scalar, defaultVector, ?_⟩
    rfl
  case u =>
    refine ⟨.scalar, defaultVector, ?_⟩
    rfl
  case oe =>
    refine ⟨.scalar, defaultVector, ?_⟩
    rfl
  case wi =>
    refine ⟨.scalar, defaultVector, ?_⟩
    rfl
  -- Fractal class (tensor) - covered by wildcard
  case ya =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case yeo =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case yo =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case yu =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case i =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case ae =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case e =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case ui =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case wa =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case wae =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case wo =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case we =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case ye =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl
  case yae =>
    refine ⟨.scalar, defaultTensor, ?_⟩
    rfl

/-- VMap coverage rate: 21/21 = 100%.
    At least one Jungseong has a valid VMap mapping. -/
theorem VMap_coverage_nonempty :
    ∃ (v : Jungseong) (a b : ObjType), VMap v a = some b :=
  ⟨Jungseong.eu, .scalar, .scalar, rfl⟩

/-! ## Final Type Map -/

/-- Final type map: input type ↦ output type (identity, with boundary annotation in meta). -/
def FMap : Jongseong → ObjType → Option ObjType
  | f, _ =>
      let f' := FPrimary f
      some <|
        match f' with
        | .g | .d | .b | .s | .j | .k | .t | .p | .ch => .secare
        | .n | .r | .m | .ng => .actyon
        | .h => .margin
        | .gg | .gs | .nj | .nh | .rg | .rm | .rb | .rs | .rt | .rp | .rh | .bs => .secare

/-- Admissible domain predicate for FMap. -/
def FAdmissible (f : Jongseong) (a : ObjType) : Prop :=
  (FMap f a).isSome

/-! ## Determinism and Totality Lemmas -/

theorem CMap_deterministic {c : Choseong} {a b b' : ObjType}
    (h1 : CMap c a = some b) (h2 : CMap c a = some b') : b = b' := by
  have : (some b : Option ObjType) = some b' := by
    simpa [h1] using h2
  exact Option.some.inj this

theorem VMap_deterministic {v : Jungseong} {a b b' : ObjType}
    (h1 : VMap v a = some b) (h2 : VMap v a = some b') : b = b' := by
  have : (some b : Option ObjType) = some b' := by
    simpa [h1] using h2
  exact Option.some.inj this

theorem FMap_deterministic {f : Jongseong} {a b b' : ObjType}
    (h1 : FMap f a = some b) (h2 : FMap f a = some b') : b = b' := by
  have : (some b : Option ObjType) = some b' := by
    simpa [h1] using h2
  exact Option.some.inj this

theorem VMap_total (v : Jungseong) (a : ObjType) : ∃ b, VMap v a = some b := by
  cases v <;> simp [VMap]

theorem FMap_total (f : Jongseong) (a : ObjType) : ∃ b, FMap f a = some b := by
  cases f <;> simp [FMap, FPrimary]

/-- Operator terms: a typed free calculus with parallel composition. -/
inductive OpTerm : ObjType → ObjType → Type
  | id (a : ObjType) : OpTerm a a
  | comp {a b c : ObjType} : OpTerm b c → OpTerm a b → OpTerm a c
  | par  {a b c d : ObjType} : OpTerm a b → OpTerm c d → OpTerm (.prod a c) (.prod b d)
  | C {a b : ObjType} (c : Choseong) (h : CMap c a = some b) : OpTerm a b
  | V {a b : ObjType} (v : Jungseong) (h : VMap v a = some b) : OpTerm a b
  | F {a b : ObjType} (f : Jongseong) (h : FMap f a = some b) : OpTerm a b

/-- Syllable typing and term construction for a given input type. -/
def syllableTerm (a : ObjType) (s : Syllable) : Option (Sigma fun b => OpTerm a b) :=
  match s with
  | ⟨c, v, f?⟩ =>
      match hC : CMap c a with
      | none => none
      | some b =>
          match hV : VMap v b with
          | none => none
          | some c' =>
              match f? with
              | none =>
                  match hF : FMap Jongseong.h c' with
                  | none => none
                  | some d =>
                      some ⟨d, OpTerm.comp (OpTerm.F Jongseong.h hF)
                        (OpTerm.comp (OpTerm.V v hV) (OpTerm.C c hC))⟩
              | some f =>
                  match hF : FMap f c' with
                  | none => none
                  | some d =>
                      some ⟨d, OpTerm.comp (OpTerm.F f hF)
                        (OpTerm.comp (OpTerm.V v hV) (OpTerm.C c hC))⟩

/-- A syllable is well-typed on input `a` iff its term exists. -/
def WellTypedSyllable (a : ObjType) (s : Syllable) : Prop :=
  (syllableTerm a s).isSome

/-! ## Semantics Interface (optional, but fully typed) -/

/-- A semantics for the Hangul operator family. -/
structure Semantics where
  Csem : ∀ {c : Choseong} {a b : ObjType}, CMap c a = some b → Carrier a → Carrier b
  Vsem : ∀ {v : Jungseong} {a b : ObjType}, VMap v a = some b → Carrier a → Carrier b
  Fsem : ∀ {f : Jongseong} {a b : ObjType}, FMap f a = some b → Carrier a → Carrier b

/-- Interpret a term under a given semantics. -/
def interp (sem : Semantics) : ∀ {a b : ObjType}, OpTerm a b → Carrier a → Carrier b
  | _, _, .id _, x => x
  | _, _, .comp g f, x => interp sem g (interp sem f x)
  | _, _, .par f g, x => (interp sem f x.1, interp sem g x.2)
  | _, _, .C _ h, x => sem.Csem h x
  | _, _, .V _ h, x => sem.Vsem h x
  | _, _, .F _ h, x => sem.Fsem h x

/-! ## Slot/Cube Geometry -/

/-- Coordinate on a `side × side × height` grid with depth. -/
abbrev Coord (side height depth : Nat) :=
  Fin side × Fin side × Fin height × Fin depth

/-- Directions for slot flow. -/
inductive Direction
  | N | S | E | W | NE | NW | SE | SW | U | D | Hold

/-- Dimension tags. -/
inductive Dimension
  | spatial | temporal | margin | metaTag

/-- Slot metadata (world/observer/modality/time/descriptor). -/
structure Meta where
  world : WorldData
  observer : ObserverData
  modality : Modality
  time : Int
  descriptor : Descriptor

/-- A slot holds a coordinate, an optional glyph, and a typed payload. -/
structure Slot (side height depth : Nat) where
  coord : Coord side height depth
  payload : TypedObject
  glyph : Option Syllable
  dir : Direction
  dim : Dimension
  metaInfo : Meta

/-- A cube is a total assignment of slots over coordinates. -/
structure Cube (side height depth : Nat) where
  slot : Coord side height depth → Slot side height depth

/-- Cardinality of coordinates: side² * height * depth. -/
@[simp] theorem coord_card (side height depth : Nat) :
    Fintype.card (Coord side height depth) = side * side * height * depth := by
  classical
  -- Coord = Fin side × Fin side × Fin height × Fin depth
  simp [Coord, Fintype.card_prod, Nat.mul_left_comm, Nat.mul_comm]

/-- 3×3 square = 9 slots (height=1, depth=1). -/
theorem coord_card_3x3 : Fintype.card (Coord 3 1 1) = 9 := by
  -- 3 * 3 * 1 * 1 = 9
  simp

/-- 3×3×3 cube = 27 slots (depth=1). -/
theorem coord_card_3x3x3 : Fintype.card (Coord 3 3 1) = 27 := by
  -- 3 * 3 * 3 * 1 = 27
  simp

/-- Evaluate a slot by applying its glyph (if well-typed). -/
def Slot.eval (sem : Semantics) {side height depth : Nat} (s : Slot side height depth) :
    Option TypedObject :=
  match s.glyph with
  | none => some s.payload
  | some g =>
      match syllableTerm s.payload.ty g with
      | none => none
      | some tb => some ⟨tb.1, interp sem tb.2 s.payload.val⟩

theorem Slot.eval_glyph_none {sem : Semantics} {side height depth : Nat}
    (s : Slot side height depth) (h : s.glyph = none) :
    Slot.eval sem s = some s.payload := by
  classical
  simp [Slot.eval, h]

theorem Slot.eval_glyph_some {sem : Semantics} {side height depth : Nat}
    (s : Slot side height depth) {g : Syllable} {b : ObjType} {t : OpTerm s.payload.ty b}
    (hg : s.glyph = some g)
    (ht : syllableTerm s.payload.ty g = some ⟨b, t⟩) :
    Slot.eval sem s = some ⟨b, interp sem t s.payload.val⟩ := by
  classical
  simp [Slot.eval, hg, ht]

theorem Slot.eval_none_of_glyph_some_untyped {sem : Semantics} {side height depth : Nat}
    (s : Slot side height depth) {g : Syllable}
    (hg : s.glyph = some g)
    (ht : syllableTerm s.payload.ty g = none) :
    Slot.eval sem s = none := by
  classical
  simp [Slot.eval, hg, ht]

theorem Slot.eval_some_of_welltyped {sem : Semantics} {side height depth : Nat}
    (s : Slot side height depth) {g : Syllable}
    (hg : s.glyph = some g)
    (hwt : WellTypedSyllable s.payload.ty g) :
    ∃ o, Slot.eval sem s = some o := by
  classical
  rcases Option.isSome_iff_exists.mp hwt with ⟨tb, htb⟩
  refine ⟨⟨tb.1, interp sem tb.2 s.payload.val⟩, ?_⟩
  simp [Slot.eval, hg, htb]

/-! ### Determinism and Type Preservation (core formalization) -/

theorem Slot.eval_deterministic {sem : Semantics} {side height depth : Nat}
    (s : Slot side height depth) {o₁ o₂ : TypedObject}
    (h₁ : Slot.eval sem s = some o₁)
    (h₂ : Slot.eval sem s = some o₂) : o₁ = o₂ := by
  have : (some o₁ : Option TypedObject) = some o₂ := by
    simpa [h₁] using h₂
  exact Option.some.inj this

theorem Slot.eval_preserves_type {sem : Semantics} {side height depth : Nat}
    (s : Slot side height depth) {o : TypedObject}
    (h : Slot.eval sem s = some o) :
    o.ty = s.payload.ty ∨
      ∃ g b t, s.glyph = some g ∧
        syllableTerm s.payload.ty g = some ⟨b, t⟩ ∧ o.ty = b := by
  classical
  cases hg : s.glyph with
  | none =>
      left
      have := Slot.eval_glyph_none (sem := sem) (s := s) (h := hg)
      -- use uniqueness of evaluation
      have : o = s.payload := Slot.eval_deterministic (sem := sem) (s := s) h this
      simp [this]
  | some g =>
      right
      cases hterm : syllableTerm s.payload.ty g with
      | none =>
          have hnone := Slot.eval_none_of_glyph_some_untyped (sem := sem) (s := s) (g := g)
              (hg := hg) (ht := hterm)
          -- contradiction with h
          cases hnone ▸ h
      | some tb =>
          refine ⟨g, tb.1, tb.2, ?_, hterm, ?_⟩
          · exact rfl
          have hsome := Slot.eval_glyph_some (sem := sem) (s := s) (g := g) (b := tb.1) (t := tb.2)
              (hg := hg) (ht := hterm)
          have : o = ⟨tb.1, interp sem tb.2 s.payload.val⟩ :=
            Slot.eval_deterministic (sem := sem) (s := s) h hsome
          simp [this]

end UEM
