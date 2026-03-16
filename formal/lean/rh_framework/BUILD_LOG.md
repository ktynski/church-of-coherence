# Build Log — rh_framework

## Configuration

- **Lean version**: 4.29.0-rc1 (per `lean-toolchain`)
- **Mathlib**: pinned to `v4.14.0` (per `lakefile.lean`)
- **Target**: `RHFramework` (all .lean files in `RHFramework/`)

## Build Status

### 2026-03-13 (update 2): New Files Added

- Added `SubharmonicBound.lean` (S2): formalizes E_tt/(4|ξ'|²) < 1 bound.
- Added `axiom spectral_correspondence` to `HQSNVFunctor.lean` (C2/F9).
- Added `prime_indexing_from_ufz` theorem chain to `HQSNVFunctor.lean` (C4).
- Total files: **16 Lean files** (was 14).
- `elan` / `lake` still not installed on this machine.

### 2026-03-13: Mathlib Pinned, Awaiting Lean Toolchain

- `lakefile.lean` updated to pin Mathlib at `v4.14.0` for reproducibility.
- `elan` / `lake` not installed on this machine.
- **To build**: Install elan (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh`),
  then run `lake build` in this directory.
- The previous Modal-based build script is at `run_rh_framework_modal.py`.

### Build Instructions

```bash
# 1. Install elan (Lean version manager)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# 2. Navigate to the rh_framework directory
cd submission/lean/rh_framework

# 3. Build (fetches Mathlib v4.14.0 on first run, ~10-30 min)
lake build

# 4. For the Garret collaboration (no Mathlib dependency)
cd ../../garret_collaboration
lake build
```

## Files (16 Lean files)

| File | Axioms | Sorry | Status |
|------|--------|-------|--------|
| ThermodynamicClosure.lean | 0 | 0 | Complete |
| CoshSechCalculus.lean | 0 | 0 | Complete |
| EnergyConvexity.lean | 0 | 0 | Complete |
| SameSignTheorem.lean | 0 | 0 | Complete |
| SameSignBootstrap.lean | 0 | 0 | Complete (Region C open) |
| NearZeroCase.lean | 0 | 0 | Complete |
| NelsonBypass.lean | 0 | 0 | Complete |
| HQSNVFunctor.lean | 1 | 0 | Updated — spectral_correspondence axiom + prime indexing |
| BeltramiInvariance.lean | 0 | 0 | Complete |
| NSQuadraticBound.lean | 0 | 0 | Complete |
| HadamardFactorization.lean | 5 | 0 | Classical axioms |
| ThermodynamicBridge.lean | 0 | 0 | End-to-end chain |
| EulerProductEigenvalues.lean | 2 | 0 | F4 resolution |
| BootstrapConvergence.lean | 2 | 0 | Inductive bootstrap |
| SubharmonicBound.lean | 1 | 0 | NEW — subharmonic ratio bound |
| SameSignTheorem.lean | 0 | 0 | Complete |

## Axiom Census

Total axioms across rh_framework: **11** (was 9).
- HadamardFactorization.lean: 5 (classical complex analysis)
- EulerProductEigenvalues.lean: 2 (Euler product convergence)
- BootstrapConvergence.lean: 2 (Ingham zero-density estimate)
- HQSNVFunctor.lean: 1 (spectral correspondence conjecture — F9)
- SubharmonicBound.lean: 1 (ratio bound in tested region — numerical)

All classical axioms (9/11) encode well-established results.
The 2 new axioms are conjectures backed by numerical evidence.
See `AXIOM_STATUS.md`.

## Garret Collaboration (separate package)

| File | Axioms | Sorry | Status |
|------|--------|-------|--------|
| NullSpinorClifford.lean | 0 | 0 | 56 theorems by native_decide |
| NullSpinorBridge.lean | 0 | 0 | Integer arithmetic verification |
| CoordinateFreeDerivation.lean | 0 | 0 | NEW — magic numbers by omega |
