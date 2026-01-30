import UemProofs.UEM.UEM_Calculus

open scoped ENNReal

namespace UEM

/-!
Epistemic embeddings: structural mappings from core epistemic objects into
scalar/vector/tensor/measure spaces. Pure definitions; no external cases.
-/

/-- Bundle of embeddings from epistemic objects to observed spaces. -/
structure EpistemicEmbedding where
  spark_to_scalar : Spark → Scalar
  actyon_to_vector : Actyon → Vector 2
  escalade_to_tensor : Escalade → Tensor 1
  secare_to_measure : Secare → ℝ≥0∞

/-- Core embedding: definitional mappings based on core fields. -/
def coreEmbedding : EpistemicEmbedding where
  spark_to_scalar := fun s => s.origin
  actyon_to_vector := fun a =>
    ⟨fun i => if i.1 = 0 then a.direction else (a.intensity : Scalar)⟩
  escalade_to_tensor := fun e =>
    ⟨fun _ => (e.depth : Scalar)⟩
  secare_to_measure := fun s => s.thickness

theorem coreEmbedding_spark (s : Spark) :
    coreEmbedding.spark_to_scalar s = s.origin := rfl

theorem coreEmbedding_actyon_zero (a : Actyon) :
    (coreEmbedding.actyon_to_vector a).data ⟨0, by decide⟩ = a.direction := by
  simp [coreEmbedding]

theorem coreEmbedding_actyon_one (a : Actyon) :
    (coreEmbedding.actyon_to_vector a).data ⟨1, by decide⟩ = (a.intensity : Scalar) := by
  simp [coreEmbedding]

theorem coreEmbedding_escalade (e : Escalade) :
    (coreEmbedding.escalade_to_tensor e).data ⟨0, by decide⟩ = (e.depth : Scalar) := rfl

theorem coreEmbedding_secare (s : Secare) :
    coreEmbedding.secare_to_measure s = s.thickness := rfl

end UEM
