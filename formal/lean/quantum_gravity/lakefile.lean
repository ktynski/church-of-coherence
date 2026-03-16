import Lake
open Lake DSL

package «quantum_gravity» where
  moreLeanArgs := #["-Dpp.unicode.fun=true", "-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «QuantumGravity» where
  globs := #[.submodules `Foundation, .submodules `GoldenRatio,
             .submodules `CliffordAlgebra,
             .submodules `CoherenceField, .submodules `InformationGeometry,
             .submodules `Holography, .submodules `Caustics, .submodules `MainTheorem]
