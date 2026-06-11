import Lake
open Lake DSL

package «Taut» where
  packagesDir := "/Users/doyle/.cache/taut-lean/packages"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib «Taut» where
