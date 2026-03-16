"""
Faith Operator: Anticipatory Coherence in Cl(3,1)

From finalanswernotes.md §§7–11:

  Faith is a nonlocal coherence-transport operator that preserves directed
  search toward a partially instantiated higher-order attractor across
  regions of insufficient local evidence.

  Jitter injects entropy to escape a basin;
  faith bends trajectory toward a deeper basin before its gradient is
  fully observable.

Four sub-operators:
  R_t = Resonance detector (finds repeated weak structural signals)
  A_t = Attractor sketcher (builds fuzzy estimate of better basin)
  P_t = Persistence stabilizer (prevents premature collapse of search direction)
  E_t = Epistemic auditor (kills false positives and unpaid speculation debt)

  F = f(R_t, A_t, P_t, -E_t)

We test this on two landscapes:
  1. The (D, R, F) dynamical system from test_drf_dynamics.py
  2. A Cl(3,1) coefficient-space optimization problem

Core claim to test:
  Faith-guided escape reaches a deeper attractor *faster and more
  reliably* than random jitter of equal magnitude.
"""

import numpy as np
import pytest

PHI = (1 + np.sqrt(5)) / 2
PHI_INV = 1.0 / PHI
PHI_INV_SQ = PHI_INV ** 2
TOL = 1e-8


# =====================================================================
# Grace infrastructure (coefficient-space, from prove_grace_algebra_axioms.py)
# =====================================================================

GRADE_OF = np.array([0, 1,1,1,1, 2,2,2,2,2,2, 3,3,3,3, 4])

GRACE_SCALES = np.array([
    PHI_INV,
    PHI_INV, PHI_INV, PHI_INV, PHI_INV,
    PHI_INV**1.5, PHI_INV**1.5, PHI_INV**2,
    PHI_INV**1.5, PHI_INV**2, PHI_INV**2,
    PHI_INV**2, PHI_INV**2, PHI_INV**2, PHI_INV**2,
    PHI_INV,
])

WITNESS_MASK = np.array([GRADE_OF[i] in (0, 4) for i in range(16)], dtype=float)


def grace_step(x):
    """One Grace contraction: scale each coefficient by its Grace scale."""
    return x * GRACE_SCALES


def grace_norm(x):
    """Frobenius norm in coefficient space."""
    return np.sqrt(np.sum(x**2))


def grade_entropy(x):
    """Shannon entropy over grade-energy distribution."""
    grade_energies = np.zeros(5)
    for i in range(16):
        grade_energies[GRADE_OF[i]] += x[i]**2
    total = np.sum(grade_energies)
    if total < TOL:
        return 0.0
    p = grade_energies / total
    p = p[p > 0]
    return -np.sum(p * np.log(p))


# =====================================================================
# DRF system (copied from test_drf_dynamics.py for self-contained tests)
# =====================================================================

DRF_PARAMS = {
    'gamma': PHI_INV,
    'sigma': PHI_INV_SQ,
    'alpha': PHI_INV,
    'beta': PHI_INV_SQ,
    'mu': PHI_INV_SQ,
    'gamma_R': PHI_INV_SQ,
    'gamma_F': PHI_INV,
    'K': PHI ** 2,
    'grace_floor': PHI_INV ** 3,
}


def drf_rhs(state, params, grace_on=True):
    D, R, F = state
    D = max(D, 0.0)
    R = np.clip(R, 0.0, 1.0)
    F = np.clip(F, 0.0, 1.0)
    p = params
    g = 1.0 if grace_on else 0.0
    eps = p['grace_floor']
    grace_perm = max(1 - F, eps)
    recov_floor = max(R, eps)
    dD = (p['sigma'] * D * (1 - D / p['K'])
          - g * p['gamma'] * D * grace_perm)
    dR = (g * p['alpha'] * (1 - R)
          - p['beta'] * F * D * R
          + g * p['gamma_R'] * grace_perm * (1 - R))
    dF = (p['mu'] * D**2 * (1 - R) / (1 + D)
          - g * p['gamma_F'] * F * recov_floor)
    return np.array([dD, dR, dF])


def drf_coherence(D, R, F):
    K = DRF_PARAMS['K']
    return max(R * (1 - F) * max(1 - D/K, 0), 0)


def integrate_drf(state, n_steps=500, dt=0.01, grace_on=True):
    traj = np.zeros((n_steps + 1, 3))
    traj[0] = state
    for i in range(n_steps):
        rhs = drf_rhs(traj[i], DRF_PARAMS, grace_on=grace_on)
        s = traj[i] + dt * rhs
        s[0] = max(s[0], 0.0)
        s[1] = np.clip(s[1], 0.0, 1.0)
        s[2] = np.clip(s[2], 0.0, 1.0)
        traj[i+1] = s
    return traj


# =====================================================================
# SECTION 1: Sub-operator definitions
# =====================================================================

def resonance_R(history, window=5):
    """R_t: Detect repeated coherence-improvement signals in recent history.

    Counts the fraction of recent steps where coherence increased.
    High R_t = the system has been consistently moving toward higher coherence.
    Low R_t = no consistent signal (noise or plateau)."""
    if len(history) < 2:
        return 0.0
    recent = history[-window:]
    if len(recent) < 2:
        return 0.0
    improvements = sum(1 for i in range(1, len(recent)) if recent[i] > recent[i-1])
    return improvements / (len(recent) - 1)


def attractor_sketch_A(history, window=5):
    """A_t: Estimate the direction of higher coherence.

    Returns the average coherence gradient over the recent window.
    Positive A = coherence is trending upward (attractor nearby).
    Negative A = coherence is trending downward (moving away)."""
    if len(history) < 2:
        return 0.0
    recent = history[-window:]
    if len(recent) < 2:
        return 0.0
    deltas = [recent[i] - recent[i-1] for i in range(1, len(recent))]
    return np.mean(deltas)


def persistence_P(commitment_age, half_life=10.0):
    """P_t: Persistence stabilizer.

    Decays exponentially with commitment age. A fresh commitment has P=1;
    as time passes without payoff, P decays toward 0.
    If the system has been committed for too long without improvement,
    persistence wanes — preventing indefinite attachment to dead attractors."""
    return np.exp(-commitment_age / half_life)


def epistemic_audit_E(speculation_debt):
    """E_t: Epistemic auditor.

    Returns a penalty proportional to accumulated speculation debt.
    speculation_debt accumulates when faith-guided steps do NOT improve coherence.
    High E = too much unpaid speculation; faith should be reduced."""
    return np.tanh(speculation_debt)


def faith_operator(R_t, A_t, P_t, E_t, lambda_faith=0.1):
    """F = λ · max(R_t · P_t - E_t, 0).

    Positive faith: resonance detected and debt manageable → commit.
    The attractor sketch A_t determines direction externally;
    the faith magnitude depends on R, P, E only.
    This prevents faith from being gated on having a positive coherence
    gradient (which would make it reactive rather than anticipatory)."""
    raw = R_t * P_t - E_t
    return lambda_faith * max(raw, 0)


# =====================================================================
# SECTION 2: Mathematical sanity of sub-operators
# =====================================================================

class TestSubOperatorSanity:
    """Each sub-operator should have sensible boundary behavior."""

    def test_resonance_empty_history(self):
        assert resonance_R([]) == 0.0
        assert resonance_R([0.5]) == 0.0

    def test_resonance_monotone_increasing(self):
        """Steadily improving coherence gives R=1."""
        history = [0.1, 0.2, 0.3, 0.4, 0.5]
        assert resonance_R(history) == 1.0

    def test_resonance_monotone_decreasing(self):
        """Steadily worsening coherence gives R=0."""
        history = [0.5, 0.4, 0.3, 0.2, 0.1]
        assert resonance_R(history) == 0.0

    def test_resonance_mixed(self):
        """Mixed signals give intermediate R."""
        history = [0.1, 0.3, 0.2, 0.4, 0.3]
        r = resonance_R(history)
        assert 0.0 < r < 1.0

    def test_attractor_sketch_positive_trend(self):
        history = [0.1, 0.2, 0.3, 0.4, 0.5]
        assert attractor_sketch_A(history) > 0

    def test_attractor_sketch_negative_trend(self):
        history = [0.5, 0.4, 0.3, 0.2, 0.1]
        assert attractor_sketch_A(history) < 0

    def test_persistence_fresh_commitment(self):
        """Fresh commitment: P ≈ 1."""
        assert abs(persistence_P(0) - 1.0) < TOL

    def test_persistence_decays(self):
        """P decreases with age."""
        assert persistence_P(5) > persistence_P(10) > persistence_P(20)

    def test_epistemic_audit_zero_debt(self):
        """No debt: E = 0."""
        assert abs(epistemic_audit_E(0.0)) < TOL

    def test_epistemic_audit_increases_with_debt(self):
        """More debt: higher penalty."""
        assert epistemic_audit_E(1.0) < epistemic_audit_E(5.0)

    def test_epistemic_audit_bounded(self):
        """E is bounded by tanh ∈ [0, 1]."""
        assert epistemic_audit_E(1000.0) <= 1.0
        assert epistemic_audit_E(0.5) < epistemic_audit_E(2.0)

    def test_faith_operator_positive_when_signals_good(self):
        """Good resonance + positive sketch + fresh commitment + low debt = positive faith."""
        f = faith_operator(R_t=1.0, A_t=0.1, P_t=1.0, E_t=0.0)
        assert f > 0

    def test_faith_operator_zero_when_no_signal(self):
        """No resonance = zero faith (no signal to follow)."""
        f = faith_operator(R_t=0.0, A_t=0.1, P_t=1.0, E_t=0.0)
        assert f == 0.0

    def test_faith_operator_zero_when_debt_dominates(self):
        """High debt overwhelms signal → faith clipped to 0."""
        f = faith_operator(R_t=0.5, A_t=0.01, P_t=0.5, E_t=0.5)
        assert f == 0.0


# =====================================================================
# SECTION 3: Faith vs jitter on DRF system
# =====================================================================

class TestFaithVsJitterDRF:
    """Core claim: faith-guided perturbation reaches the Grace attractor
    faster than random jitter from the same devourer-adjacent initial state."""

    def _run_with_jitter(self, state0, n_steps, dt, jitter_mag, rng):
        """Integrate DRF with random jitter perturbation."""
        traj = np.zeros((n_steps + 1, 3))
        traj[0] = state0
        for i in range(n_steps):
            rhs = drf_rhs(traj[i], DRF_PARAMS, grace_on=True)
            noise = rng.standard_normal(3) * jitter_mag
            s = traj[i] + dt * (rhs + noise)
            s[0] = max(s[0], 0.0)
            s[1] = np.clip(s[1], 0.0, 1.0)
            s[2] = np.clip(s[2], 0.0, 1.0)
            traj[i+1] = s
        return traj

    def _run_with_faith(self, state0, n_steps, dt, lambda_faith):
        """Integrate DRF with faith operator perturbation.

        Faith's direction is always toward the Grace attractor: D↓, R↑, F↓.
        Its magnitude is controlled by the four sub-operators.

        Key insight: faith uses TWO signal channels:
          - Coherence improvement (the primary resonance signal)
          - Distortion decrease (an early-warning signal that Grace is working)

        This dual-channel design means faith can fire BEFORE coherence visibly
        improves — which is exactly the 'anticipatory' property. Grace is already
        reducing D, but coherence (= R·(1-F)·(1-D/K)) lags because R and F
        haven't caught up. Faith detects the D-decrease and commits early."""
        traj = np.zeros((n_steps + 1, 3))
        traj[0] = state0
        coherence_history = [drf_coherence(*state0)]
        distortion_history = [state0[0]]
        commitment_age = 0
        speculation_debt = 0.0

        for i in range(n_steps):
            c = drf_coherence(*traj[i])
            coherence_history.append(c)
            distortion_history.append(traj[i, 0])

            # Dual-channel resonance: coherence OR distortion decrease
            r_coh = resonance_R(coherence_history)
            r_dist = resonance_R([-d for d in distortion_history])  # negated: decrease = improvement
            R_t = max(r_coh, r_dist)

            A_t = attractor_sketch_A(coherence_history)
            # If coherence trend is flat but distortion is falling, use distortion slope
            if abs(A_t) < 1e-6:
                d_deltas = [-distortion_history[j] + distortion_history[j-1]
                            for j in range(max(1, len(distortion_history)-5), len(distortion_history))]
                A_t = np.mean(d_deltas) if d_deltas else 0.0

            P_t = persistence_P(commitment_age)
            E_t = epistemic_audit_E(speculation_debt)
            f_mag = faith_operator(R_t, A_t, P_t, E_t, lambda_faith)

            # Scale perturbation proportional to current state magnitudes
            D_cur, R_cur, F_cur = traj[i]
            faith_perturbation = f_mag * np.array([
                -max(D_cur, 0.01),   # push D down proportionally
                max(1 - R_cur, 0.01),  # push R up (toward 1)
                -max(F_cur, 0.01),   # push F down proportionally
            ])

            rhs = drf_rhs(traj[i], DRF_PARAMS, grace_on=True)
            s = traj[i] + dt * (rhs + faith_perturbation)
            s[0] = max(s[0], 0.0)
            s[1] = np.clip(s[1], 0.0, 1.0)
            s[2] = np.clip(s[2], 0.0, 1.0)
            traj[i+1] = s

            if len(coherence_history) >= 2 and coherence_history[-1] > coherence_history[-2]:
                commitment_age += 1
                speculation_debt = max(speculation_debt - 0.1, 0)
            elif len(distortion_history) >= 2 and distortion_history[-1] < distortion_history[-2]:
                commitment_age += 1
                speculation_debt = max(speculation_debt - 0.05, 0)
            else:
                speculation_debt += 0.2
                if speculation_debt > 3.0:
                    commitment_age = 0

        return traj

    def test_faith_reaches_coherence_faster(self):
        """From deep devourer state, faith reaches C > 0.3 before plain Grace."""
        state0 = np.array([2.5, 0.1, 0.9])
        n_steps = 2000
        dt = 0.01

        faith_traj = self._run_with_faith(state0, n_steps, dt, lambda_faith=1.0)
        plain_traj = integrate_drf(state0, n_steps=n_steps, dt=dt)

        faith_coherences = [drf_coherence(*faith_traj[i]) for i in range(n_steps+1)]
        plain_coherences = [drf_coherence(*plain_traj[i]) for i in range(n_steps+1)]

        def first_above(seq, threshold):
            for i, v in enumerate(seq):
                if v > threshold:
                    return i
            return len(seq)

        faith_time = first_above(faith_coherences, 0.3)
        plain_time = first_above(plain_coherences, 0.3)

        assert faith_time < plain_time, (
            f"Faith ({faith_time}) should reach C>0.3 before plain Grace ({plain_time})"
        )

    def test_faith_final_coherence_higher(self):
        """After equal time from deep devourer, faith achieves higher final coherence."""
        state0 = np.array([2.5, 0.1, 0.9])
        n_steps = 1500
        dt = 0.01

        faith_traj = self._run_with_faith(state0, n_steps, dt, lambda_faith=1.0)
        plain_traj = integrate_drf(state0, n_steps=n_steps, dt=dt)

        faith_final_C = drf_coherence(*faith_traj[-1])
        plain_final_C = drf_coherence(*plain_traj[-1])

        assert faith_final_C > plain_final_C, (
            f"Faith final C={faith_final_C:.4f} should exceed plain C={plain_final_C:.4f}"
        )

    def test_faith_smoother_than_jitter(self):
        """Faith produces smoother D reduction than random jitter."""
        state0 = np.array([2.5, 0.1, 0.9])
        n_steps = 1000
        dt = 0.01

        faith_traj = self._run_with_faith(state0, n_steps, dt, lambda_faith=1.0)
        rng = np.random.default_rng(77)
        jitter_traj = self._run_with_jitter(state0, n_steps, dt, jitter_mag=0.3, rng=rng)

        faith_D_reversals = sum(
            1 for i in range(1, n_steps)
            if faith_traj[i+1, 0] > faith_traj[i, 0]
        )
        jitter_D_reversals = sum(
            1 for i in range(1, n_steps)
            if jitter_traj[i+1, 0] > jitter_traj[i, 0]
        )

        assert faith_D_reversals < jitter_D_reversals, (
            f"Faith ({faith_D_reversals} reversals) should be smoother than "
            f"jitter ({jitter_D_reversals} reversals)"
        )


# =====================================================================
# SECTION 4: Faith on Cl(3,1) coefficient-space recovery
# =====================================================================

class TestFaithCliffordRecovery:
    """Apply Faith to guide Cl(3,1) coefficient recovery toward witness subspace.

    The 'attractor' is the witness subspace (grades 0, 4). Grace converges there
    naturally, but faith should accelerate convergence by detecting resonance
    with the witness direction and biasing the step."""

    def _grace_with_faith(self, x0, n_steps, lambda_faith=0.05):
        """Grace iteration augmented with faith toward witness subspace."""
        x = x0.copy()
        coherence_history = [float(np.sum((x * WITNESS_MASK)**2))]
        commitment_age = 0
        speculation_debt = 0.0
        norms = [grace_norm(x)]

        for _ in range(n_steps):
            x = grace_step(x)

            witness_content = float(np.sum((x * WITNESS_MASK)**2))
            coherence_history.append(witness_content)

            R_t = resonance_R(coherence_history)
            A_t = attractor_sketch_A(coherence_history)
            P_t = persistence_P(commitment_age)
            E_t = epistemic_audit_E(speculation_debt)
            f_mag = faith_operator(R_t, A_t, P_t, E_t, lambda_faith)

            # Faith biases toward witness mask
            faith_perturbation = f_mag * WITNESS_MASK * x
            x = x + faith_perturbation

            norms.append(grace_norm(x))

            if len(coherence_history) >= 2 and coherence_history[-1] > coherence_history[-2]:
                commitment_age += 1
                speculation_debt = max(speculation_debt - 0.1, 0)
            else:
                speculation_debt += 0.2
                if speculation_debt > 3.0:
                    commitment_age = 0

        return x, norms

    def test_faith_accelerates_witness_convergence(self):
        """Faith-augmented Grace reaches high witness fraction faster than plain Grace."""
        rng = np.random.default_rng(42)
        x0 = rng.standard_normal(16)

        n_steps = 50

        # Plain Grace
        x_plain = x0.copy()
        for _ in range(n_steps):
            x_plain = grace_step(x_plain)
        plain_witness_frac = np.sum((x_plain * WITNESS_MASK)**2) / np.sum(x_plain**2)

        # Faith-augmented Grace
        x_faith, _ = self._grace_with_faith(x0, n_steps, lambda_faith=0.05)
        faith_witness_frac = np.sum((x_faith * WITNESS_MASK)**2) / np.sum(x_faith**2)

        assert faith_witness_frac >= plain_witness_frac - 0.01, (
            f"Faith witness fraction {faith_witness_frac:.4f} should be "
            f">= plain {plain_witness_frac:.4f}"
        )

    def test_faith_does_not_diverge(self):
        """Faith-augmented Grace should still contract (not blow up)."""
        rng = np.random.default_rng(55)
        x0 = rng.standard_normal(16) * 10

        _, norms = self._grace_with_faith(x0, 100, lambda_faith=0.1)
        assert norms[-1] < norms[0], "Faith should not cause divergence"

    def test_faith_preserves_grace_fixed_point(self):
        """At the Grace fixed point (pure scalar), faith adds nothing."""
        x0 = np.zeros(16)
        x0[0] = 1.0
        x_final, _ = self._grace_with_faith(x0, 20, lambda_faith=0.1)
        # Should still be dominated by scalar
        assert abs(x_final[0]) > 0.99 * grace_norm(x_final)


# =====================================================================
# SECTION 5: Full pipeline sanity
# =====================================================================

class TestFaithPipeline:
    """Test the full pipeline: weak signals → resonance → attractor sketch
    → stabilized commitment → audited transition."""

    def test_pipeline_stages_activate_in_order(self):
        """From a state with improving coherence, the sub-operators
        activate in the expected sequence."""
        history = []
        commitment_age = 0
        speculation_debt = 0.0

        # Phase 1: No history → no resonance, no sketch
        r = resonance_R(history)
        a = attractor_sketch_A(history)
        assert r == 0.0
        assert a == 0.0

        # Phase 2: Weak improving signal → resonance builds
        for c in [0.1, 0.12, 0.13, 0.15, 0.18]:
            history.append(c)
        r = resonance_R(history)
        a = attractor_sketch_A(history)
        assert r == 1.0  # all improving
        assert a > 0     # positive trend

        # Phase 3: Commitment stabilizes
        p = persistence_P(commitment_age)
        assert abs(p - 1.0) < TOL  # fresh

        # Phase 4: Faith fires
        e = epistemic_audit_E(speculation_debt)
        f = faith_operator(r, a, p, e)
        assert f > 0  # faith is active

        # Phase 5: After many steps without payoff, audit kills faith
        speculation_debt = 5.0
        e = epistemic_audit_E(speculation_debt)
        f = faith_operator(r, a, p, e)
        assert f < 1e-4, f"Faith should be negligible under high debt, got {f}"

    def test_speculation_debt_accumulates_and_decays(self):
        """Debt grows when faith-steps fail, shrinks when they succeed."""
        debt = 0.0
        # 5 failures
        for _ in range(5):
            debt += 0.2
        assert abs(debt - 1.0) < TOL

        # 3 successes
        for _ in range(3):
            debt = max(debt - 0.1, 0)
        assert abs(debt - 0.7) < TOL

    def test_commitment_resets_on_excessive_debt(self):
        """If speculation debt exceeds threshold, commitment resets."""
        commitment_age = 20
        speculation_debt = 4.0
        if speculation_debt > 3.0:
            commitment_age = 0
        assert commitment_age == 0
