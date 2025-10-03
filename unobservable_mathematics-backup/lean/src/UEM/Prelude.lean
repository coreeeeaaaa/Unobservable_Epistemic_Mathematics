/-!
`UEM` namespace collects core structures as they are formalised in Lean.
Each definition links back to `docs/UEM_formal_spec_v2.md` for traceability.
-/
namespace UEM

/-- Placeholder structure for observers, see spec §2.1. -/
structure Observer where
  id : String
  deriving Repr

/-- Placeholder alias for syllable margins, spec §3.4. -/
abbrev Margin := Float

end UEM
