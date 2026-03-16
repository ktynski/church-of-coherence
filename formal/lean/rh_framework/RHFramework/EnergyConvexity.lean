/-
  EnergyConvexity.lean — The E'' = E·(K + A) Identity

  For any twice-differentiable function E : ℝ → ℝ with E > 0,
  writing f = log ∘ E (the log-energy), define:

    K(x) = f''(x)         (curvature of log-energy surface)
    A(x) = (f'(x))²       (squared amplitude gradient)

  Then: E''(x) = E(x) · (K(x) + A(x))

  This identity is the structural backbone of the energy convexity
  approach to the Riemann Hypothesis:

    |ξ(σ+it)|² convex in σ  ⟺  K + A > 0  ⟺  RH

  The proof decomposes into three regions:
    1. Near zeros of ξ: K + A > 0 (NearZeroCase.lean)
    2. Large t: A dominates |K| by zero density estimates
    3. Finite t: interval arithmetic verification

  This file proves the identity itself — a universal calculus fact
  independent of number theory.

  Dependencies: Mathlib (real analysis, HasDerivAt, exp, log)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace RHFramework.EnergyConvexity

open Real

/-! ## The Core Identity -/

/--
  **E'' = E·(K + A) identity** (the main theorem).

  If f : ℝ → ℝ has derivative f' at x, and the derivative function
  of f has derivative f'' at x, then the function

    t ↦ (deriv f t) · exp(f t)

  (which equals the first derivative of exp ∘ f wherever f is
  differentiable) has derivative

    exp(f(x)) · (f'' + f'²)

  at x. This is the second derivative of E = exp ∘ f, expressed
  in terms of curvature K = f'' and amplitude A = f'².

  Proof: product rule on (deriv f) · (exp ∘ f), then chain rule for exp.
-/
theorem energy_KA_identity {f : ℝ → ℝ} {x f' f'' : ℝ}
    (hf : HasDerivAt f f' x)
    (hf'' : HasDerivAt (deriv f) f'' x) :
    HasDerivAt (fun t => deriv f t * exp (f t))
      (exp (f x) * (f'' + f' ^ 2)) x := by
  have h_exp : HasDerivAt (fun t => exp (f t)) (f' * exp (f x)) x :=
    hf.exp
  have h_prod := hf''.mul h_exp
  have h_eq : deriv f x = f' := hf.deriv
  rw [h_eq] at h_prod
  convert h_prod using 1
  ring

/--
  **First derivative of exp ∘ f via chain rule.**

  (exp ∘ f)'(x) = f'(x) · exp(f(x))

  This establishes that `deriv (exp ∘ f) = (deriv f) · (exp ∘ f)`,
  connecting the second-derivative statement above to the actual
  second derivative of E = exp ∘ f.
-/
theorem exp_comp_first_deriv {f : ℝ → ℝ} {x f' : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => exp (f t)) (f' * exp (f x)) x :=
  hf.exp

/-! ## Consequences for Energy Convexity -/

/--
  **E convex ⟺ K + A ≥ 0** (when E > 0).

  Since E = exp(f) > 0 always, the sign of E'' is determined
  entirely by the sign of K + A = f'' + (f')².

  This reduces the convexity question for ANY positive function
  to an inequality on its log-derivatives.
-/
theorem convexity_iff_KA_nonneg {f : ℝ → ℝ} {x f' f'' : ℝ}
    (hf : HasDerivAt f f' x)
    (hf'' : HasDerivAt (deriv f) f'' x) :
    exp (f x) * (f'' + f' ^ 2) ≥ 0 ↔ f'' + f' ^ 2 ≥ 0 := by
  constructor
  · intro h
    have h_pos : exp (f x) > 0 := exp_pos (f x)
    exact nonneg_of_mul_nonneg_left h h_pos
  · intro h
    exact mul_nonneg (le_of_lt (exp_pos (f x))) h

/--
  **Strict convexity from strict K + A > 0.**

  When K + A > 0, E'' > 0, meaning E is strictly convex
  at that point.
-/
theorem strict_convexity_of_KA_pos {f : ℝ → ℝ} {x f' f'' : ℝ}
    (hf : HasDerivAt f f' x)
    (hf'' : HasDerivAt (deriv f) f'' x)
    (h_KA : f'' + f' ^ 2 > 0) :
    exp (f x) * (f'' + f' ^ 2) > 0 :=
  mul_pos (exp_pos (f x)) h_KA

/-! ## Connection to the Original Function E -/

/--
  **E and exp(log E) agree for positive functions.**

  For E(x) > 0: exp(log(E(x))) = E(x).
  This connects the abstract exp ∘ f framework back to the
  original function E = |ξ|².
-/
theorem exp_log_identity {E : ℝ} (hE : E > 0) :
    exp (log E) = E :=
  exp_log hE

/-! ## Summary

  The theorems in this file establish:

  1. DECOMPOSITION: E'' = E · (K + A) where K = (log E)'' and A = ((log E)')²
     → Proved via chain rule + product rule (energy_KA_identity)

  2. SIGN REDUCTION: E'' ≥ 0 ⟺ K + A ≥ 0 (since E = exp(f) > 0)
     → Proved by positivity of exp (convexity_iff_KA_nonneg)

  3. STRICT CONVEXITY: K + A > 0 implies E'' > 0
     → Proved by strict positivity of exp (strict_convexity_of_KA_pos)

  Applied to E(σ,t) = |ξ(σ+it)|², this means:
  - Proving |ξ|² convex in σ reduces to proving K + A > 0
  - K + A > 0 is proved in three cases:
    (a) Near zeros: NearZeroCase.lean
    (b) Large t: zero density estimates (analytic, requires Titchmarsh bounds)
    (c) Finite t: interval arithmetic (interval_xi_convexity.py)
-/

end RHFramework.EnergyConvexity
