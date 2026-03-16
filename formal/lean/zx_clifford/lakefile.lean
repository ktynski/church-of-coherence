import Lake
open Lake DSL

package «zx_clifford» where
  -- Settings for the ZX-Hypergraph-Clifford factorization framework

-- Dependencies
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ZXClifford» where
  globs := #[
    .submodules `Data,
    .submodules `Foundation,
    .submodules `ZX,
    .submodules `Hypergraph,
    .submodules `Semantics,
    .submodules `Factorization,
    .submodules `Grace,
    .submodules `Tests
  ]
