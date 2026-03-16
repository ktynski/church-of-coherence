# Phase 2B: Spinor-Module Rewrite Plan

## Objective

Resolve the 2 remaining `sorry` statements (`semantics_hopf`, `semantics_hopf_x`) by replacing the current `QubitSpace = Cl31 × ...` representation with a spinor-module semantics where the Frobenius merge is correctly defined.

## Root Cause (Verified)

The Hopf law requires: `(copy ; swap ; merge) = (discard ; create)`.

Under current semantics:
- **LHS**: `x ↦ merge(copy(x)) = merge(x, x) = contractInputs(x, x) = mul x x`
- **RHS**: `x ↦ const(one)`
- **Failure**: `mul x x ≠ one` for generic `x ∈ Cl(3,1)` (e.g. `e12² = -1`, `(1+e1)² ≠ 1`)

The Frobenius merge must satisfy `merge(x, x) = one` (diagonal projection), not Clifford product.

## Representation Change

### Current (Incorrect for Hopf)

```
QubitSpace 0 = Unit
QubitSpace 1 = Cl31
QubitSpace (n+2) = Cl31 × QubitSpace (n+1)

contractInputs(n, q) = fold Clifford product over components
merge = contractInputs  (WRONG: gives mul, not diagonal projection)
```

### Target (Frobenius-Correct)

```
QubitSpace n = Fin (2^n) → ℝ   (or ℂ for full spinor module)

Alternative: Keep Cl31 as algebra, but interpret states as vectors in the spinor module ℝ⁴ (or ℂ⁴).
- Single qubit: ℝ² or ℂ² (Weyl spinor)
- Two qubits: ℝ⁴ or ℂ⁴ (full spinor module of Cl(3,1))
- Tensor: Kronecker product of vectors
- Merge (2→1): ⟨i| ⊗ ⟨j| → δ_ij ⟨i|  (diagonal projection)
- Copy (1→2): |i⟩ → |i⟩ ⊗ |i⟩
```

## Files to Modify (Dependency Order)

1. **Semantics/Generators.lean**
   - Replace `QubitSpace` definition
   - Redefine `contractInputs` → Frobenius merge (diagonal projection)
   - Redefine `copyToQubitSpace`, `zSpider_k_l`, `xSpider_k_l` for new representation
   - Update helper theorems (`contractInputs_two_one_left`, etc.)

2. **Semantics/Functor.lean**
   - Replace `splitQubitSpace` / `joinQubitSpace` with vector slicing / Kronecker product
   - Replace `tensorSemantics` with Kronecker product semantics
   - Update all proof terms; `semantics_hopf` and `semantics_hopf_x` become provable

3. **Grace/Simplification.lean**
   - Update `graceSemantics` signature if it uses `QubitSpace`

4. **Factorization/Geometrize.lean**
   - Update `geometrize` / `geometrizeWithGrace` if they use `QubitSpace`

5. **Hypergraph/GorardBridge.lean**
   - Uses `semantics` and `semantics_respects_equiv`; verify compatibility

6. **Factorization/Commutes.lean**
   - Uses `semantics`; verify compatibility

7. **Tests/AxiomElimination.lean**
   - Update status comments when sorries are eliminated

## Verification Strategy

1. **Python oracle**: Extend `test_zx_axiom_witnesses.py` with spinor-module Hopf test (4×4 matrix representation: merge = diagonal projection on computational basis).
2. **Lean**: Prove `semantics_hopf` and `semantics_hopf_x` by computation on the new merge.
3. **Regression**: All 206+ existing Python tests must pass; full `lake build` must succeed.

## Mathematical Prerequisites

- Cl(3,1) acts on ℝ⁴ (or ℂ⁴) via the standard representation (gamma matrices).
- Chirality projectors P± = (I ± iω)/2 decompose ℂ⁴ into ℂ² ⊕ ℂ² (Weyl spinors).
- The ZX Frobenius algebra merge on computational basis: `|ij⟩ ↦ δ_ij |i⟩`.
- Clifford algebra elements act as linear maps on the spinor module; composition = matrix multiplication.

## Risk Mitigation

- **Incremental**: Consider a parallel `QubitSpaceSpinor` type and gradual migration.
- **Tests first**: Implement Python spinor-module semantics and validate Hopf before Lean changes.
- **Minimal scope**: Change only merge/copy semantics; preserve single-qubit rotor semantics where possible.

## Status

- **Plan**: Documented
- **Implementation**: Not started
- **Blocking**: 2 sorry in Functor.lean
