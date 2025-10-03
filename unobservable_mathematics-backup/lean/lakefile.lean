import Lake
open Lake DSL

package uemFormalization where
  -- Add additional configuration as required.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

@[default_target]
lean_lib UEM where
  srcDir := "src"
  roots := #[`UEM]

lean_exe uemCli where
  srcDir := "src"
  root := `Main
