import Lake
open Lake DSL

package UEMFormal {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib UEM {
  -- add library configuration options here
}