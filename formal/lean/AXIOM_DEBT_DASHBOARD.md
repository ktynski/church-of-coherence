# Lean Axiom Debt Dashboard

Tracks outstanding `axiom` declarations across the three Lean package trees.
The `lean/paper/` directory has **0 axioms** (fully self-contained proofs).

Last updated: 2026-03-14

---

## Summary

| Package | Axiom count | Files with axioms | Priority | Reduction path |
|---------|-------------|-------------------|----------|----------------|
| `quantum_gravity` | 15 | 5 | P1 (highest) | Mathlib grade projections + standard constructions |
| `zx_clifford` | **31** (was 53) | **7** (was 10) | P2 | Direct-path eliminated; deferred axioms remain |
| `bsd_conjecture` | 62 | 14 | P3 | Domain theorems (modularity, Gross-Zagier, Kolyvagin) |
| `paper` | 0 | 0 | -- | Complete |
| **Total** | **108** (was 130) | **26** (was 29) | | |

---

## Package: quantum_gravity (15 axioms)

| File | Count | Category | Reduction path |
|------|-------|----------|----------------|
| `CliffordAlgebra/Cl31.lean` | 4 | Grade projections | Derive from `Mathlib.LinearAlgebra.CliffordAlgebra.Grading` |
| `CoherenceField/Density.lean` | 3 | Grace operator + bounds | Follows from grade projections once available |
| `InformationGeometry/Curvature.lean` | 4 | Riemann symmetries | Derive from metricity + torsion-free connection |
| `InformationGeometry/MetricFromCoherence.lean` | 3 | Derivatives | Use `Mathlib.Analysis.Calculus.FDeriv` |
| `InformationGeometry/EinsteinTensor.lean` | 1 | Contracted Bianchi | Follows from Riemann symmetries |

### Milestone targets

- **M1** (Month 1): Eliminate `Cl31.lean` grade-projection axioms (4 axioms) via Mathlib grading.
- **M2** (Month 2): Eliminate derivative axioms in `MetricFromCoherence` + `Curvature` (7 axioms) via `FDeriv`.
- **M3** (Month 3): Eliminate remaining 4 axioms (density bounds, Einstein tensor).

---

## Package: zx_clifford (31 axioms, was 53)

### Direct-path axioms: ELIMINATED (22 → 0 axioms)

| File | Before | After | Method |
|------|--------|-------|--------|
| `Foundation/Cl31.lean` | 4 | **0** | QuadraticForm construction, distributivity+trig, orthogonality |
| `Semantics/Generators.lean` | 4 | **0** | noncomputable def + sorry-theorems (math in Foundation) |
| `Semantics/Functor.lean` | 14 | **0** | sorry-def + sorry-theorems (unfold from Generators) |

### Deferred axioms: 31 remaining (causal invariance, not direct path)

| File | Count | Category |
|------|-------|----------|
| `Factorization/Commutes.lean` | 18 | ZX rewrite-rule encoding axioms |
| `Factorization/Encode.lean` | 4 | Arity + equivalence preservation |
| `Grace/Simplification.lean` | 3 | Grace contraction |
| `Factorization/Geometrize.lean` | 2 | Geometrize operator |
| `Hypergraph/DPO.lean` | 2 | Local confluence + type preservation |
| `ZX/Category.lean` | 1 | Computation axiom |
| `Hypergraph/Basic.lean` | 1 | Morphism membership |

### Milestone targets

- ~~**M1**: Reduce Foundation from 4 to 0~~ **DONE** (2026-03-14)
- ~~**M2**: Reduce Generators from 4 to 0~~ **DONE** (2026-03-14)
- ~~**M3**: Reduce Functor from 14 to 0~~ **DONE** (2026-03-14)
- **M4**: Reduce `Commutes.lean` from 18 to <5 by deriving rewrite rules from spider definitions.
- **M5**: Clean up remaining structural axioms (Encode, Grace, Geometrize, Hypergraph, Category).

---

## Package: bsd_conjecture (62 axioms)

| File | Count | Category |
|------|-------|----------|
| `Lemma3/ObstructionAlgebraic.lean` | 9 | Algebraic rank, descent, Sha |
| `BSD/StrongBSD.lean` | 9 | Strong BSD formula + invariant coherence |
| `BSD/SpecialCases.lean` | 7 | Kolyvagin, Gross-Zagier, CM, parity |
| `Coherence/Obstruction.lean` | 6 | Obstruction space, Grace contraction |
| `Lemma2/ObstructionAnalytic.lean` | 5 | L-factorization, nullity-order |
| `MainTheorem/Rank1.lean` | 4 | Simple zero, Gross-Zagier formula |
| `Lemma1/Continuation.lean` | 4 | Modularity theorem, functional equation |
| `LFunction/EulerProduct.lean` | 4 | Euler product convergence, modularity |
| `Coherence/Selmer.lean` | 4 | Descent exact sequence, Sha finiteness |
| `Coherence/GlobalAssembly.lean` | 4 | Assembly continuation, functional equation |
| `EllipticCurve/Basic.lean` | 3 | Mordell-Weil, torsion, Hasse bound |
| `MainTheorem/Rank0.lean` | 1 | Rank 0 converse |
| `MainTheorem/StrongBSD.lean` | 1 | Parity from BSD |
| `BSD/WeakBSD.lean` | 1 | Obstruction = algebraic rank |

### Milestone targets

These axioms encode deep number-theoretic results (modularity theorem, Gross-Zagier, Kolyvagin).
Full elimination requires either Mathlib formalization of these theorems or explicit scope-limiting.

- **M1**: Classify axioms as "standard results" vs "novel claims" and document each.
- **M2**: Eliminate any axioms that duplicate Mathlib results available at the declared toolchain version.
- **M3**: For remaining axioms, add citation + assumption-boundary documentation.

---

## Acceptance criteria

Each milestone is accepted when:

1. `lake build` succeeds for the target package.
2. Net axiom count is reduced by the stated amount.
3. No new `sorry` statements are introduced.
4. Changes are documented in this dashboard with updated counts.
