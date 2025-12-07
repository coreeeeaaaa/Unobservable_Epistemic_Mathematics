namespace UEM

/-- Branch identifier (simple natural tag). -/
structure BranchId where
  id : Nat
deriving DecidableEq, Repr

/-- Parallel/Counterfactual state graph: active branches and archived branches. -/
structure StateGraph (S : Type _) where
  active  : List (BranchId × S)
  archive : List (BranchId × S)

namespace StateGraph

/-- Move a branch from active to archive (delete is forbidden). -/
def archiveBranch {S} (bid : BranchId) (g : StateGraph S) : StateGraph S :=
  let (hit, rest) := g.active.partition (fun p => p.fst = bid)
  { active := rest, archive := hit ++ g.archive }

/-- Add a new active branch. -/
def pushActive {S} (bid : BranchId) (s : S) (g : StateGraph S) : StateGraph S :=
  { active := (bid, s) :: g.active, archive := g.archive }

/-- Map over states (keeping branch ids). -/
def map {S T} (f : S → T) (g : StateGraph S) : StateGraph T :=
  { active := g.active.map (fun p => (p.fst, f p.snd))
    archive := g.archive.map (fun p => (p.fst, f p.snd)) }

end StateGraph

end UEM
