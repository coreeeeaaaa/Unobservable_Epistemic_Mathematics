import UemProofs.UEM.UEM_Theory

namespace UEM

/-!
UEM-0 observed-fragment derivations.
This file defines an observed closure on object types, observed terms,
observed derivations, and a transfer theorem from UEM-0 derivations.
-/

/-- Observed closure for the UEM-0 fragment (closed under products). -/
inductive Obs0 : ObjType → Prop
  | base : IsObserved a → Obs0 a
  | prod : Obs0 a → Obs0 b → Obs0 (.prod a b)

/-- Observed closure for UEM-0 operator terms. -/
inductive Obs0Term : {a b : ObjType} → UEM0OpTerm a b → Prop
  | base {a b : ObjType} (f : Operator a b) (ha : Obs0 a) (hb : Obs0 b) :
      Obs0Term (UEM0OpTerm.base f)
  | id {a : ObjType} (ha : Obs0 a) :
      Obs0Term (UEM0OpTerm.id (a := a))
  | comp {a b c : ObjType} {g : UEM0OpTerm b c} {f : UEM0OpTerm a b} :
      Obs0Term g → Obs0Term f → Obs0Term (UEM0OpTerm.comp g f)
  | fst {a b : ObjType} (ha : Obs0 a) (hb : Obs0 b) :
      Obs0Term (UEM0OpTerm.fst (a := a) (b := b))
  | snd {a b : ObjType} (ha : Obs0 a) (hb : Obs0 b) :
      Obs0Term (UEM0OpTerm.snd (a := a) (b := b))
  | lift {c a b : ObjType} {f : UEM0OpTerm c a} {g : UEM0OpTerm c b} :
      Obs0Term f → Obs0Term g → Obs0Term (UEM0OpTerm.lift f g)

/-- Projection of observedness from a product object. -/
theorem obs0_of_prod_left {a b : ObjType} : Obs0 (.prod a b) → Obs0 a := by
  intro h
  cases h with
  | base ha => cases ha
  | prod ha hb => exact ha

/-- Projection of observedness from a product object. -/
theorem obs0_of_prod_right {a b : ObjType} : Obs0 (.prod a b) → Obs0 b := by
  intro h
  cases h with
  | base ha => cases ha
  | prod ha hb => exact hb

/-- Observedness of the domain type of a term. -/
theorem obs0Term_dom {a b : ObjType} {t : UEM0OpTerm a b} (ht : Obs0Term t) : Obs0 a := by
  induction ht with
  | base f ha hb => exact ha
  | id ha => exact ha
  | comp hg hf ihg ihf => exact ihf
  | fst ha hb => exact Obs0.prod ha hb
  | snd ha hb => exact Obs0.prod ha hb
  | lift hf hg ihf ihg => exact ihf

/-- Observedness of the codomain type of a term. -/
theorem obs0Term_cod {a b : ObjType} {t : UEM0OpTerm a b} (ht : Obs0Term t) : Obs0 b := by
  induction ht with
  | base f ha hb => exact hb
  | id ha => exact ha
  | comp hg hf ihg ihf => exact ihg
  | fst ha hb => exact ha
  | snd ha hb => exact hb
  | lift hf hg ihf ihg => exact Obs0.prod ihf ihg

/-- Observed derivations: UEM-0 derivations restricted to observed terms. -/
inductive ObservedDerives : {a b : ObjType} → UEM0OpTerm a b → UEM0OpTerm a b → Prop
  | refl {a b : ObjType} (t : UEM0OpTerm a b) (ht : Obs0Term t) :
      ObservedDerives t t
  | symm {a b : ObjType} {t u : UEM0OpTerm a b} :
      ObservedDerives t u → ObservedDerives u t
  | trans {a b : ObjType} {t u v : UEM0OpTerm a b} :
      ObservedDerives t u → ObservedDerives u v → ObservedDerives t v
  | congr_comp {a b c : ObjType} {g g' : UEM0OpTerm b c} {f f' : UEM0OpTerm a b} :
      ObservedDerives g g' → ObservedDerives f f' →
      ObservedDerives (UEM0OpTerm.comp g f) (UEM0OpTerm.comp g' f')
  | congr_lift {c a b : ObjType} {f f' : UEM0OpTerm c a} {g g' : UEM0OpTerm c b} :
      ObservedDerives f f' → ObservedDerives g g' →
      ObservedDerives (UEM0OpTerm.lift f g) (UEM0OpTerm.lift f' g')
  | prod_fst_lift {c a b : ObjType} (f : UEM0OpTerm c a) (g : UEM0OpTerm c b)
      (hf : Obs0Term f) (hg : Obs0Term g) :
      ObservedDerives (UEM0OpTerm.comp (UEM0OpTerm.fst (a := a) (b := b))
        (UEM0OpTerm.lift f g)) f
  | prod_snd_lift {c a b : ObjType} (f : UEM0OpTerm c a) (g : UEM0OpTerm c b)
      (hf : Obs0Term f) (hg : Obs0Term g) :
      ObservedDerives (UEM0OpTerm.comp (UEM0OpTerm.snd (a := a) (b := b))
        (UEM0OpTerm.lift f g)) g
  | prod_unique {c a b : ObjType} (h : UEM0OpTerm c (.prod a b))
      (f : UEM0OpTerm c a) (g : UEM0OpTerm c b) :
      ObservedDerives (UEM0OpTerm.comp (UEM0OpTerm.fst (a := a) (b := b)) h) f →
      ObservedDerives (UEM0OpTerm.comp (UEM0OpTerm.snd (a := a) (b := b)) h) g →
      ObservedDerives h (UEM0OpTerm.lift f g)

/-- Observedness is preserved by UEM-0 derivations. -/
theorem obs0Term_preserved {a b : ObjType} {t u : UEM0OpTerm a b}
    (ht : Obs0Term t) (h : Derives t u) : Obs0Term u := by
  induction h with
  | refl t =>
      exact ht
  | symm h ih =>
      exact ih ht
  | trans h1 h2 ih1 ih2 =>
      have hu : Obs0Term _ := ih1 ht
      exact ih2 hu
  | congr_comp h1 h2 ih1 ih2 =>
      cases ht with
      | comp hg hf =>
          exact Obs0Term.comp (ih1 hg) (ih2 hf)
  | congr_lift h1 h2 ih1 ih2 =>
      cases ht with
      | lift hf hg =>
          exact Obs0Term.lift (ih1 hf) (ih2 hg)
  | prod_fst_lift f g =>
      cases ht with
      | comp hfst hlift =>
          cases hlift with
          | lift hf hg => exact hf
  | prod_snd_lift f g =>
      cases ht with
      | comp hfst hlift =>
          cases hlift with
          | lift hf hg => exact hg
  | prod_unique h f g hfst hsnd ihfst ihsnd =>
      have hcod : Obs0 (.prod a b) := obs0Term_cod (a := c) (b := .prod a b) ht
      have ha : Obs0 a := obs0_of_prod_left hcod
      have hb : Obs0 b := obs0_of_prod_right hcod
      have hfstTerm : Obs0Term (UEM0OpTerm.fst (a := a) (b := b)) :=
        Obs0Term.fst ha hb
      have hsndTerm : Obs0Term (UEM0OpTerm.snd (a := a) (b := b)) :=
        Obs0Term.snd ha hb
      have hcompFst : Obs0Term (UEM0OpTerm.comp (UEM0OpTerm.fst (a := a) (b := b)) h) :=
        Obs0Term.comp hfstTerm ht
      have hcompSnd : Obs0Term (UEM0OpTerm.comp (UEM0OpTerm.snd (a := a) (b := b)) h) :=
        Obs0Term.comp hsndTerm ht
      have hf : Obs0Term f := ihfst hcompFst
      have hg : Obs0Term g := ihsnd hcompSnd
      exact Obs0Term.lift hf hg

/-- Equational derivations on observed terms are derivable in the observed fragment. -/
theorem equational_conservativity {a b : ObjType} {t u : UEM0OpTerm a b}
    (ht : Obs0Term t) (hu : Obs0Term u) (h : Derives t u) : ObservedDerives t u := by
  induction h with
  | refl t =>
      exact ObservedDerives.refl t ht
  | symm h ih =>
      exact ObservedDerives.symm (ih hu ht)
  | trans h1 h2 ih1 ih2 =>
      have hu' : Obs0Term _ := obs0Term_preserved ht h1
      exact ObservedDerives.trans (ih1 ht hu') (ih2 hu' hu)
  | congr_comp h1 h2 ih1 ih2 =>
      cases ht with
      | comp hg hf =>
          cases hu with
          | comp hg' hf' =>
              exact ObservedDerives.congr_comp (ih1 hg hg') (ih2 hf hf')
  | congr_lift h1 h2 ih1 ih2 =>
      cases ht with
      | lift hf hg =>
          cases hu with
          | lift hf' hg' =>
              exact ObservedDerives.congr_lift (ih1 hf hf') (ih2 hg hg')
  | prod_fst_lift f g =>
      cases ht with
      | comp hfst hlift =>
          cases hlift with
          | lift hf hg =>
              exact ObservedDerives.prod_fst_lift f g hf hg
  | prod_snd_lift f g =>
      cases ht with
      | comp hfst hlift =>
          cases hlift with
          | lift hf hg =>
              exact ObservedDerives.prod_snd_lift f g hf hg
  | prod_unique h f g hfst hsnd ihfst ihsnd =>
      cases hu with
      | lift hf hg =>
          exact ObservedDerives.prod_unique h f g (ihfst (by
            have hcod : Obs0 (.prod a b) := obs0Term_cod (a := c) (b := .prod a b) ht
            have ha : Obs0 a := obs0_of_prod_left hcod
            have hb : Obs0 b := obs0_of_prod_right hcod
            have hfstTerm : Obs0Term (UEM0OpTerm.fst (a := a) (b := b)) :=
              Obs0Term.fst ha hb
            exact Obs0Term.comp hfstTerm ht) hf)
            (ihsnd (by
              have hcod : Obs0 (.prod a b) := obs0Term_cod (a := c) (b := .prod a b) ht
              have ha : Obs0 a := obs0_of_prod_left hcod
              have hb : Obs0 b := obs0_of_prod_right hcod
              have hsndTerm : Obs0Term (UEM0OpTerm.snd (a := a) (b := b)) :=
                Obs0Term.snd ha hb
              exact Obs0Term.comp hsndTerm ht) hg)

/-- Observed term constructor for scalar base operators. -/
def obs0_scalar : Obs0 ObjType.scalar := Obs0.base (by simp [IsObserved])

/-- Example 1: observed fst/lift equation on scalar operators. -/
example (f g : Operator ObjType.scalar ObjType.scalar) :
    ObservedDerives
      (UEM0OpTerm.comp
        (UEM0OpTerm.fst (a := ObjType.scalar) (b := ObjType.scalar))
        (UEM0OpTerm.lift (UEM0OpTerm.base f) (UEM0OpTerm.base g)))
      (UEM0OpTerm.base f) := by
  apply ObservedDerives.prod_fst_lift
  · exact Obs0Term.base f obs0_scalar obs0_scalar
  · exact Obs0Term.base g obs0_scalar obs0_scalar

/-- Example 2: observed snd/lift equation on scalar operators. -/
example (f g : Operator ObjType.scalar ObjType.scalar) :
    ObservedDerives
      (UEM0OpTerm.comp
        (UEM0OpTerm.snd (a := ObjType.scalar) (b := ObjType.scalar))
        (UEM0OpTerm.lift (UEM0OpTerm.base f) (UEM0OpTerm.base g)))
      (UEM0OpTerm.base g) := by
  apply ObservedDerives.prod_snd_lift
  · exact Obs0Term.base f obs0_scalar obs0_scalar
  · exact Obs0Term.base g obs0_scalar obs0_scalar

end UEM
