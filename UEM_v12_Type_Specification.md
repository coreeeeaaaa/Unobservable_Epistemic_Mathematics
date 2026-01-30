# UEM v12.0: Object & Operator Type Specification (Pure Math)

This document gives the **pure mathematical** type/operator specification
aligned with the Lean core.

---

## 1. Type Hierarchy

All UEM components must inhabit one of the following types.

### 1.1 Observed Types
- **Scalar**: `Scalar : Type` (defined as `ℝ`)
- **Vector**: `Vector (n : Nat) : Type`
- **Tensor**: `Tensor (k : Nat) : Type`

### 1.2 Epistemic Types
- **Spark**: `Spark : Type` (field `origin : Scalar`)
- **Actyon**: `Actyon : Type` (fields `direction : Scalar`, `intensity : Nat`)
- **Escalade**: `Escalade : Type` (field `depth : Nat`)
- **Secare**: `Secare : Type` (field `thickness : ℝ≥0∞`)

### 1.3 Meta Types
- **WorldData**: `WorldData : Type`
- **ObserverData**: `ObserverData : Type`
- **MarginData**: `MarginData : Type`
- **PossibleWorld**: `PossibleWorld : Type`
- **Descriptor**: `Descriptor : Type`

---

## 2. Core Operator Signatures

Operators are total functions with fixed domains and codomains.

- `CreateSpark : World → Spark`
- `Ignite : Spark → Actyon`
- `Escalate : Actyon → Nat → Escalade`
- `Commit : Escalade → Secare`

---

## 3. Hangul Calculus Mapping (Typed Composition)

Let a syllable be `Syllable := (C, V, F?)` with:
- `Choseong`, `Jungseong`, `Jongseong`.

Type mappings are relations:
- `CMap : ObjType → ObjType → Prop`
- `VMap : ObjType → ObjType → Prop`
- `FMap : ObjType → ObjType → Prop`

Composition order is fixed: **C → V → F**.

### 3.1 Direction Tagging
- `directionOfVowel : Jungseong → Direction`
- `syllableDirection s := directionOfVowel s.v`

---

## 4. Slot/Cube Structure

- `Coord side height depth := Fin side × Fin side × Fin height × Fin depth`
- `Slot` contains coordinates, glyph, payload, direction, dimension, meta.
- `Cube` is a total assignment of slots over coordinates.

---

## 5. Lean Alignment

All specifications above are **exactly** the structures and signatures
in the Lean core:
- `Lean4/UemProofs/UEM/UEM_Calculus.lean`
- `Lean4/UemProofs/UEM/UEM_HangulMatrix.lean`
- `Lean4/UemProofs/UEM/UEM_Foundations.lean`
