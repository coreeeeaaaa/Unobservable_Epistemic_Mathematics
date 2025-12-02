import Mathlib.Algebra.Group.Defs

/-!
# UEM Direct Sum
Basic direct sum structure for decomposing V into V_keep + V_null.
-/

namespace UEM

def DirectSum (V_keep V_null : Type _) := V_keep × V_null

end UEM
