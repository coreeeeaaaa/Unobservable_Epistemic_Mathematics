import UemProofs.UEM.UEM_Calculus

namespace UEM

/-!
Pure‑math operator semantics (no examples, no named special cases).
Aligns with core order: Spark → Actyon → Escalade → Secare.
-/

/-- Pure semantic space for the 4‑stage pipeline. -/
structure UEMPureSemantics where
  World : Type
  Context : Type
  Param : Type
  SparkT : Type
  ActyonT : Type
  EscaladeT : Type
  SecareT : Type
  SparkOp : World → Context → SparkT
  ActyonOp : SparkT → ActyonT
  EscaladeOp : ActyonT → Param → EscaladeT
  SecareOp : EscaladeT → SecareT

/-- Mapping from UEM core objects to pure semantic objects. -/
structure UEMOperatorMapping (S : UEMPureSemantics) where
  spark_map : Spark → S.SparkT
  actyon_map : Actyon → S.ActyonT
  escalade_map : Escalade → S.EscaladeT
  secare_map : Secare → S.SecareT

/-- Composition: Spark → Actyon (typed). -/
def ActyonAfterSpark (P : UEMPureSemantics) (w : P.World) (ctx : P.Context) :
    P.ActyonT :=
  P.ActyonOp (P.SparkOp w ctx)

/-- Composition: Spark → Actyon → Escalade (typed). -/
def EscaladeAfterSpark (P : UEMPureSemantics) (w : P.World) (ctx : P.Context) (p : P.Param) :
    P.EscaladeT :=
  P.EscaladeOp (P.ActyonOp (P.SparkOp w ctx)) p

/-- Composition: Spark → Actyon → Escalade → Secare (typed). -/
def SecareAfterSpark (P : UEMPureSemantics) (w : P.World) (ctx : P.Context) (p : P.Param) :
    P.SecareT :=
  P.SecareOp (P.EscaladeOp (P.ActyonOp (P.SparkOp w ctx)) p)

/-! ### Core definitional mapping and equalities (pure math, no axioms) -/

/-- Core semantics aligned with the formal core operators. -/
def coreSemantics : UEMPureSemantics where
  World := WorldData
  Context := PUnit
  Param := Nat
  SparkT := Spark
  ActyonT := Actyon
  EscaladeT := Escalade
  SecareT := Secare
  SparkOp := fun w _ => (CreateSpark.apply w)
  ActyonOp := fun s => (Ignite.apply s)
  EscaladeOp := fun a n => (Escalate.apply (a, n))
  SecareOp := fun e => (Commit.apply e)

/-- Core mapping is definitional identity on objects. -/
def coreMapping : UEMOperatorMapping coreSemantics where
  spark_map := fun s => s
  actyon_map := fun a => a
  escalade_map := fun e => e
  secare_map := fun s => s

theorem core_SparkOp (w : WorldData) (u : PUnit) :
    coreSemantics.SparkOp w u = CreateSpark.apply w := rfl

theorem core_ActyonOp (s : Spark) :
    coreSemantics.ActyonOp s = Ignite.apply s := rfl

theorem core_EscaladeOp (a : Actyon) (n : Nat) :
    coreSemantics.EscaladeOp a n = Escalate.apply (a, n) := rfl

theorem core_SecareOp (e : Escalade) :
    coreSemantics.SecareOp e = Commit.apply e := rfl

theorem core_ActyonAfterSpark (w : WorldData) (u : PUnit) :
    ActyonAfterSpark coreSemantics w u = Ignite.apply (CreateSpark.apply w) := rfl

theorem core_EscaladeAfterSpark (w : WorldData) (u : PUnit) (n : Nat) :
    EscaladeAfterSpark coreSemantics w u n =
      Escalate.apply (Ignite.apply (CreateSpark.apply w), n) := rfl

theorem core_SecareAfterSpark (w : WorldData) (u : PUnit) (n : Nat) :
    SecareAfterSpark coreSemantics w u n =
      Commit.apply (Escalate.apply (Ignite.apply (CreateSpark.apply w), n)) := rfl

/-! ### Totality / closure (definitional completeness) -/

theorem core_pipeline_total (w : WorldData) (u : PUnit) (n : Nat) :
    ∃ s : Secare, s = SecareAfterSpark coreSemantics w u n :=
  ⟨SecareAfterSpark coreSemantics w u n, rfl⟩

/-! ### Global closure over core objects (no escape) -/

/-- The full core pipeline closes inside core Secare. -/
theorem core_pipeline_closure (w : WorldData) (u : PUnit) (n : Nat) :
    SecareAfterSpark coreSemantics w u n = Commit.apply
      (Escalate.apply (Ignite.apply (CreateSpark.apply w), n)) := rfl

end UEM
