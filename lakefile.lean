import Lake
open Lake DSL

package UEM where
  srcDir := "lean/src"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib UEM where
  roots := #[`UEM]

@[default_target]
lean_exe uem where
  root := `Main