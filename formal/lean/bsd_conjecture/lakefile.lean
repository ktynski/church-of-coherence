import Lake
open Lake DSL

package «bsd_conjecture» where
  moreLeanArgs := #["-Dpp.unicode.fun=true", "-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «BSDConjecture» where
  globs := #[.submodules `Foundation, .submodules `EllipticCurve,
             .submodules `LFunction, .submodules `Coherence,
             .submodules `BSD, .submodules `Lemma1, .submodules `Lemma2,
             .submodules `Lemma3, .submodules `MainTheorem]
