import UemProofs.UEM.UEM_Calculus

/-! # Core Completeness Lemmas (Admissible-domain totality)

This file adds the minimal pure-math totality lemmas needed for a
"sealed" core: totality on admissible domains and syllableTerm
existence from admissibility.
-/

namespace UEM

/-- CMap is total on its admissible domain. -/
theorem CMap_total_on_admissible {c : Choseong} {a : ObjType}
    (h : CAdmissible c a) : ∃ b, CMap c a = some b := by
  classical
  cases hC : CMap c a with
  | none =>
      simp [CAdmissible, hC] at h
  | some b =>
      exact ⟨b, rfl⟩

/-- VMap is total on its admissible domain. -/
theorem VMap_total_on_admissible {v : Jungseong} {a : ObjType}
    (h : VAdmissible v a) : ∃ b, VMap v a = some b := by
  classical
  cases hV : VMap v a with
  | none =>
      simp [VAdmissible, hV] at h
  | some b =>
      exact ⟨b, rfl⟩

/-- FMap is total on its admissible domain. -/
theorem FMap_total_on_admissible {f : Jongseong} {a : ObjType}
    (h : FAdmissible f a) : ∃ b, FMap f a = some b := by
  classical
  cases hF : FMap f a with
  | none =>
      simp [FAdmissible, hF] at h
  | some b =>
      exact ⟨b, rfl⟩

/-- Admissibility for a full syllable (C→V→F chain). -/
def SyllableAdmissibleChain (a : ObjType) (s : Syllable) : Prop :=
  ∃ b, CMap s.c a = some b ∧
    ∃ c', VMap s.v b = some c' ∧
      match s.f? with
      | none => ∃ d, FMap Jongseong.h c' = some d
      | some f => ∃ d, FMap f c' = some d

/-- Core admissibility: a syllable is admissible iff its term exists. -/
def SyllableAdmissible (a : ObjType) (s : Syllable) : Prop :=
  WellTypedSyllable a s

/-- If a syllable is admissible, its term exists (by definition). -/
theorem syllableTerm_of_admissible {a : ObjType} {s : Syllable}
    (h : SyllableAdmissible a s) : ∃ b t, syllableTerm a s = some ⟨b, t⟩ := by
  rcases Option.isSome_iff_exists.mp h with ⟨tb, htb⟩
  refine ⟨tb.1, tb.2, ?_⟩
  simpa using htb

/-- Admissibility implies well-typedness. -/
theorem wellTyped_of_admissible {a : ObjType} {s : Syllable}
    (h : SyllableAdmissible a s) : WellTypedSyllable a s := by
  simpa [SyllableAdmissible] using h

end UEM
