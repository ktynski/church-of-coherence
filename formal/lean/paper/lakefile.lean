import Lake
open Lake DSL

package «paper» where
  moreLeanArgs := #["-DautoImplicit=false"]

@[default_target]
lean_lib «Paper» where
  roots := #[
    `Octonion,
    `OctonionAutG2,
    `Hurwitz,
    `AlbertTheorem,
    `ExceptionalChain,
    `E8RootSystem,
    `DynkinCompleteness,
    `BreakingChainUniqueness,
    `SSubalgebra,
    `SSubalgebraComplete,
    `GeorgiGlashow,
    `SU9Elimination,
    `GaugeGroups,
    `BrokenGenerators,
    `Confinement,
    `MassRatios,
    `FullChain,
    `CliffordInnerProduct,
    `GravityEmergence,
    `LovelockTheorem,
    `CosmologicalDensity,
    `HierarchyDerivation,
    `DualRegulator
  ]
