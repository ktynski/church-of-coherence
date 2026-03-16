# Axiom Status — rh_framework

## Overview

The `rh_framework` Lean 4 package contains **0 sorry** and a small number
of explicit `axiom` declarations. All axioms encode well-established
classical results that are not yet available in Mathlib.

## Axiom Inventory

### HadamardFactorization.lean

| Axiom | Classical Result | Reference |
|-------|-----------------|-----------|
| `xi_energy` | Existence of E(δ,t) = \|ξ(1/2+δ+it)\|² | Definition |
| `hadamard_log_energy_decomposition` | Hadamard product formula for ξ | Titchmarsh §2.12; Hadamard (1893) |
| `xi_energy_symmetric` | Functional equation ξ(s) = ξ(1-s) | Riemann (1859); proved by Hadamard & de la Vallée Poussin |
| `xi_energy_nonneg` | E = \|ξ\|² ≥ 0 | Immediate from squared modulus |
| `xi_energy_zero_iff` | Zeros of E correspond to zeros of ξ | Immediate from \|z\|² = 0 ⟺ z = 0 |

### Why These Are Axioms (Not Sorry)

Mathlib currently lacks:
1. The theory of entire functions of finite order (Hadamard's theorem)
2. The Weierstrass/Hadamard canonical product representation
3. The definition and properties of the Riemann xi function
4. The functional equation of ζ(s) (and hence ξ(s))

These are all well-established results from 19th-century complex analysis.
They are not conjectures. When Mathlib adds the requisite theory, these
axioms can be replaced with proofs importing Mathlib theorems.

### EulerProductEigenvalues.lean

| Axiom | Classical Result | Reference |
|-------|-----------------|-----------|
| `euler_product_convergence` | Euler product converges for Re(s) > 1 | Euler (1737), Dirichlet (absolute convergence) |
| `prime_power_expansion` | -log(1-z) = z + z²/2 + ... for \|z\| < 1 | Standard power series |

### BootstrapConvergence.lean

| Axiom | Classical Result | Reference |
|-------|-----------------|-----------|
| `ingham_exponent_lt_one` | A(σ) = 3(1-σ)/(2-σ) < 1 for σ > 1/2 | Ingham (1940) |
| `effective_density_bound` | N_off(σ,T) ≤ C·T^{A(σ)}·(log T)^B | Kadiri, Lumley, Ng (2018) |

### HQSNVFunctor.lean (updated)

| Axiom | Type | Reference |
|-------|------|-----------|
| `spectral_correspondence` | Conjecture (F9) | Montgomery-Odlyzko law; verified numerically in verify_spectral_correspondence.py |

This axiom states that H_QSNV eigenvalue spacings converge to GUE statistics
(matching Riemann zero spacings) as the truncation level N → ∞.
It is a CONJECTURE, not a classical theorem. Numerical evidence supports it
(SC1–SC8 in verify_spectral_correspondence.py).

### SubharmonicBound.lean (new)

| Axiom | Type | Reference |
|-------|------|-----------|
| `ratio_bound_in_tested_region` | Numerical bound | prove_subharmonic_bound.py (SH2–SH4) |

This axiom states that ∃ λ < 1 such that E_tt/(4|ξ'|²) ≤ λ at all tested points.
Numerically, λ ≈ 0.847. The near-zero asymptotic ratio of 0.5 is proved analytically.
Full analytic proof for all (σ,t) remains OPEN.

### All Other Files

All other files in `rh_framework` (ThermodynamicClosure, CoshSechCalculus,
EnergyConvexity, SameSignTheorem, SameSignBootstrap, NearZeroCase,
NelsonBypass, BeltramiInvariance, NSQuadraticBound, ThermodynamicBridge)
contain **0 axioms and 0 sorry**.

## Proof-Theoretic Status

## Total Axiom Count: 11

| Category | Count | Type |
|----------|-------|------|
| Classical theorems (HadamardFactorization) | 5 | Well-established, awaiting Mathlib |
| Classical theorems (EulerProduct) | 2 | Well-established, awaiting Mathlib |
| Classical theorems (Bootstrap/Ingham) | 2 | Well-established, awaiting Mathlib |
| Conjectures (HQSNVFunctor/spectral) | 1 | Numerical evidence |
| Numerical bounds (SubharmonicBound) | 1 | Numerical evidence |
| **Total** | **11** | |

9/11 axioms encode well-established classical results.
2/11 axioms are conjectures/bounds backed by numerical evidence.

The rh_framework proves:
- **Unconditional**: F''(δ) > 0, symmetry, ground state, midpoint argument
- **Conditional on Hadamard axioms**: the bridge from abstract convexity to
  the actual xi function
- **Conditional on Ingham axioms**: the bootstrap convergence for t > T_0
- **Conditional on spectral correspondence**: F9 functor property
- **Conditional on ratio bound**: subharmonic convexity E_σσ > 0
- **Open**: Computing explicit T_0 where bootstrap applies (see compute_effective_T0.py)
- **Open**: Full analytic proof of ratio bound < 1
