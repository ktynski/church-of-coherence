import Lake
open Lake DSL

package «rh_framework» where
  moreLeanArgs := #["-Dpp.unicode.fun=true", "-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

@[default_target]
lean_lib «RHFramework» where
  globs := #[.submodules `RHFramework]
