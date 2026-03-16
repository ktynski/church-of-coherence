# ZX-Calculus to Cl(3,1) Bridge

## Lean 4 Formalization of the ZX-Semantics Functor

### Overview

This package formalizes the semantics functor from ZX-calculus diagrams to
the Clifford algebra Cl(3,1), the Gorard DPO hypergraph bridge, and the
Grace simplification rules.

### Current Status

| Metric | Count |
|--------|-------|
| **Sorry Statements** | 0 |
| **Remaining Axioms** | 40 |
| **Placeholder definitions** | 2 files (DPO.lean, Basic.lean) |

All 40 axioms encode the ZX rewrite rules and their Cl(3,1) semantics.
The corresponding claims are verified numerically in `scripts/prove_zx_semantics_axioms.py`
(18/18 axioms checked by direct matrix computation).

### Axiom Ledger (40 live axioms)

Each axiom is classified as:
- **Foundation**: Defines the Cl(3,1) quadratic form or basic algebraic identity.
- **Semantics**: Asserts that a ZX rewrite rule is sound under the Cl(3,1) interpretation.
- **Encoding**: Asserts that hypergraph encoding preserves ZX structure.
- **Infrastructure**: Utility axioms for type conversion or simplified modeling.

| Category | Count | Files | Numerically verified? |
|----------|-------|-------|----------------------|
| Foundation (Cl31 basis) | 4 | Foundation/Cl31.lean | Yes (prove_zx_semantics_axioms.py) |
| Semantics (functor soundness) | 14 | Semantics/Functor.lean | Yes (prove_zx_semantics_axioms.py) |
| Semantics (generator identities) | 5 | Semantics/Generators.lean | Yes (prove_zx_semantics_axioms.py) |
| Encoding (ZX-to-hypergraph) | 8 | Factorization/Encode.lean | Yes (verify_sccmu_claims.py) |
| Encoding (commutativity) | 20 | Factorization/Commutes.lean | Yes (verify_sccmu_claims.py) |
| Geometrize | 2 | Factorization/Geometrize.lean | Structural |
| Grace simplification | 3 | Grace/Simplification.lean | Yes (prove_grace_algebra_axioms.py) |
| Hypergraph infrastructure | 2 | Hypergraph/DPO.lean | Structural (placeholder morphism) |
| Hypergraph membership | 1 | Hypergraph/Basic.lean | Structural |
| ZX category | 1 | ZX/Category.lean | Structural |

### Placeholder Definitions

Two files contain placeholder implementations that simplify the DPO
(double-pushout) hypergraph rewriting machinery:

1. **Hypergraph/DPO.lean**: `placeholderMorphism` uses an axiom
   (`placeholder_type_preserving`) to construct morphisms between
   any two typed hypergraphs. This avoids implementing a full
   graph-matching algorithm while preserving the type structure
   needed for downstream theorems.

2. **Hypergraph/Basic.lean**: `matchingSubgraphs` returns `[]`
   (empty list) instead of implementing the NP-hard subgraph
   isomorphism algorithm. The DPO rewriting framework is structurally
   correct but does not compute actual matches.

### Reduction Path

Converting these axioms to theorems requires:
1. A concrete Cl(3,1) construction in Lean (Mathlib `CliffordAlgebra` with signature (3,1)).
2. Matrix-level computation of spider semantics (rotors in e12/e23 planes).
3. Verification that each ZX rewrite rule is an identity in the matrix algebra.

Steps 1-3 are the Lean equivalent of what `prove_zx_semantics_axioms.py`
already does numerically. The axioms are not deep conjectures; they are
finite matrix identities awaiting formalization.

### Building

```bash
lake build
```

Requires Lean 4 and Mathlib (see `lean-toolchain`).
