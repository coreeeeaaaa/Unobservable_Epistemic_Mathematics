import Lake
open Lake DSL

package UEM where
  srcDir := "lean/src"

lean_lib UEM where
  roots := #[`UEM]

@[default_target]
lean_exe uem where
  root := `Main