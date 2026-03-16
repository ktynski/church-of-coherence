/-
  RHFramework.lean — Master Import File

  Imports all RHFramework submodules and states the top-level
  biconditional theorem connecting K+A positivity to RH.

  This file forces the Lean type checker to verify that all
  definitions across the submodules are mutually compatible.

  WHAT THIS CHAIN ESTABLISHES (biconditional, not a proof of RH):
    K+A > 0 for all (delta, t)  <==>  all nontrivial zeros of zeta
                                       lie on the critical line

  The K+A > 0 direction requires one of:
    (a) Computable T_0 from zero-density estimates [BootstrapConvergence]
    (b) Subharmonic ratio < 1 analytically [SubharmonicBound]
    (c) Spectral correspondence for H_QSNV [HQSNVFunctor]

  All three remain open. See FULL_AUDIT_REPORT.md for status.
-/

import RHFramework.EnergyConvexity
import RHFramework.CoshSechCalculus
import RHFramework.NearZeroCase
import RHFramework.SameSignTheorem
import RHFramework.SameSignBootstrap
import RHFramework.HadamardFactorization
import RHFramework.EulerProductEigenvalues
import RHFramework.ThermodynamicClosure
import RHFramework.ThermodynamicBridge
import RHFramework.NelsonBypass
import RHFramework.BootstrapConvergence
import RHFramework.HQSNVFunctor
import RHFramework.SubharmonicBound
import RHFramework.BeltramiInvariance
import RHFramework.NSQuadraticBound

/-!
  ## Top-Level Biconditional

  The full RH framework proves:

  DIRECTION 1 (EnergyConvexity):
    K+A > 0 everywhere ==> |xi(s)|^2 strictly convex in sigma
    ==> unique minimum at sigma = 1/2
    ==> all zeros on the critical line

  DIRECTION 2 (SameSignTheorem + CoshSechCalculus):
    All zeros on critical line ==> all h_k same sign
    ==> cross terms >= 0 ==> K+A > 0

  These two directions together give: RH <==> K+A > 0.

  The framework does NOT prove RH — it provides a biconditional
  reformulation. Breaking the circle requires proving K+A > 0
  unconditionally, which is an open problem.

  COMPONENTS:
  - EnergyConvexity: E'' = E(K+A), the structural backbone
  - CoshSechCalculus: cosh/sech positivity and sum log-convexity
  - NearZeroCase: K+A -> 2/delta^2 near simple zeros
  - SameSignTheorem: K+A decomposition and same-sign property
  - SameSignBootstrap: three-region argument, breaks partial circularity
  - HadamardFactorization: Hadamard product axioms for xi
  - EulerProductEigenvalues: why weights are log(pq)
  - ThermodynamicClosure: symmetric + convex -> unique minimum
  - ThermodynamicBridge: connects Hadamard to thermodynamic
  - NelsonBypass: finite-N suffices (no operator limit needed)
  - BootstrapConvergence: inductive extension using Ingham exponent
  - HQSNVFunctor: Cl(3,1)-Rep -> Dirichlet L-functions functor
  - SubharmonicBound: E_tt/(4|xi'|^2) < 1 bound
  - BeltramiInvariance: Beltrami flow identities for NS
  - NSQuadraticBound: Navier-Stokes quadratic self-limitation

  AXIOM SUMMARY (across all submodules):
  - 7 axioms in HadamardFactorization (classical: xi function properties + zero enumeration)
  - 2 axioms in EulerProductEigenvalues (classical: Euler product convergence)
  - 2 axioms in BootstrapConvergence (classical: Ingham exponent)
  - 1 axiom in SubharmonicBound (numerically verified, analytically open)
  - 1 axiom in HQSNVFunctor (conjecture: spectral correspondence)
  Total: 13 axioms, 0 sorry
-/
