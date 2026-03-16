"""
Phi Emergence: Test-Driven Investigation

From finalanswernotes.md: The inverse-signature self-relation may produce φ
as a fixed point if the unfolding obeys:

  whole / dominant = dominant / subordinate = φ

Equivalently: φ² = φ + 1, or φ = 1 + 1/φ.

This test suite proceeds methodically:
  1. Sanity: φ satisfies its defining equations (no Clifford needed)
  2. Golden partition: when does (a+b)/a = a/b = φ hold?
  3. Fibonacci: F_{n+1}/F_n → φ (archetypal emergence)
  4. Chirality split: can we construct states with golden sector ratio?
  5. Open: does a Clifford-based iterative process produce φ without putting it in?
"""

import numpy as np
import pytest

TOL = 1e-10
PHI = (1 + np.sqrt(5)) / 2


# =====================================================================
# SECTION 1: φ fixed-point (mathematical sanity)
# =====================================================================

class TestPhiFixedPoint:
    """φ satisfies its defining recurrence. No Clifford needed."""

    def test_phi_squared_equals_phi_plus_one(self):
        """φ² = φ + 1. The defining equation."""
        assert abs(PHI**2 - (PHI + 1)) < TOL

    def test_phi_equals_one_plus_one_over_phi(self):
        """φ = 1 + 1/φ. Equivalent fixed-point form."""
        assert abs(PHI - (1 + 1/PHI)) < TOL

    def test_whole_over_dominant_equals_phi(self):
        """When subordinate = dominant/φ, then (whole)/dominant = φ.
        whole = dominant + subordinate, so whole = dominant + dominant/φ = dominant(1 + 1/φ) = dominant·φ."""
        dominant = 1.0
        subordinate = dominant / PHI
        whole = dominant + subordinate
        ratio = whole / dominant
        assert abs(ratio - PHI) < TOL

    def test_dominant_over_subordinate_equals_phi(self):
        """When subordinate = dominant/φ, then dominant/subordinate = φ."""
        dominant = 1.0
        subordinate = dominant / PHI
        assert abs(dominant / subordinate - PHI) < TOL


# =====================================================================
# SECTION 2: Golden partition (ratio structure)
# =====================================================================

class TestGoldenPartition:
    """The golden partition: whole/dominant = dominant/subordinate = φ."""

    def test_golden_partition_consistency(self):
        """For any a > 0, if b = a/φ then (a+b)/a = a/b = φ."""
        a = 2.7
        b = a / PHI
        whole = a + b
        assert abs(whole / a - PHI) < TOL
        assert abs(a / b - PHI) < TOL

    def test_norm_golden_partition(self):
        """For state with ||P+ψ||² = a, ||P-ψ||² = b, golden means a/b = φ or b/a = φ."""
        # Dominant sector has norm² = φ, subordinate = 1 (so dominant/subordinate = φ)
        a = PHI
        b = 1.0
        assert abs(a / b - PHI) < TOL
        whole = a + b
        assert abs(whole / a - PHI) < TOL


# =====================================================================
# SECTION 3: Fibonacci ratio convergence (archetypal emergence)
# =====================================================================

class TestFibonacciEmergence:
    """Fibonacci recurrence produces φ as the limit ratio."""

    def test_fibonacci_ratio_converges_to_phi(self):
        """F_{n+1}/F_n → φ. The canonical emergence of φ from pure recurrence."""
        F = [1, 1]
        for _ in range(50):
            F.append(F[-1] + F[-2])
        ratio = F[-1] / F[-2]
        assert abs(ratio - PHI) < 1e-10

    def test_reciprocal_recurrence_converges_to_phi(self):
        """x_{n+1} = 1 + 1/x_n converges to φ from any x_0 > 0.
        This is the 'inverse' fixed-point without Fibonacci."""
        x = 1.0
        for _ in range(30):
            x = 1 + 1 / x
        assert abs(x - PHI) < 1e-10


# =====================================================================
# SECTION 4: Chirality split and golden ratio
# =====================================================================

def build_cl31():
    g = np.zeros((4, 4, 4), dtype=complex)
    g[0] = [[1,0,0,0],[0,1,0,0],[0,0,-1,0],[0,0,0,-1]]
    g[1] = [[0,0,1,0],[0,0,0,-1],[1,0,0,0],[0,-1,0,0]]
    g[2] = [[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]]
    g[3] = [[0,0,0,-1],[0,0,1,0],[0,-1,0,0],[1,0,0,0]]
    return g


G = build_cl31()
OMEGA = G[0] @ G[1] @ G[2] @ G[3]
P_PLUS = (np.eye(4, dtype=complex) + 1j * OMEGA) / 2
P_MINUS = (np.eye(4, dtype=complex) - 1j * OMEGA) / 2


class TestChiralityGoldenPartition:
    """Can we construct states whose chiral sector norms have golden ratio?"""

    def test_golden_partition_state_exists(self):
        """Construct psi = α·v₊ + β·v₋ with v₊∈S+, v₋∈S-, unit norm, and α²/β² = φ.
        Then ||P+ψ||²/||P-ψ||² = α²/β² = φ."""
        sqrt_phi = np.sqrt(PHI)
        # Use first nonzero column of each projector as basis vector in that sector
        col_plus = P_PLUS[:, 0]
        if np.linalg.norm(col_plus) < TOL:
            col_plus = P_PLUS[:, 1]
        v_plus = col_plus / np.linalg.norm(col_plus)
        col_minus = P_MINUS[:, 0]
        if np.linalg.norm(col_minus) < TOL:
            col_minus = P_MINUS[:, 1]
        v_minus = col_minus / np.linalg.norm(col_minus)
        # Verify they're in the right sectors (P± v = v)
        assert np.linalg.norm(P_PLUS @ v_plus - v_plus) < TOL
        assert np.linalg.norm(P_MINUS @ v_minus - v_minus) < TOL
        # psi = √φ·v₊ + v₋, normalized. Then ||P+ψ||² = φ/(φ+1), ||P-ψ||² = 1/(φ+1)
        psi = sqrt_phi * v_plus + 1.0 * v_minus
        psi = psi / np.linalg.norm(psi)
        a_sq = np.linalg.norm(P_PLUS @ psi)**2
        b_sq = np.linalg.norm(P_MINUS @ psi)**2
        ratio = a_sq / b_sq
        assert abs(ratio - PHI) < 0.01, f"Expected φ, got {ratio}"

    def test_sector_ratio_whole_over_dominant(self):
        """For golden partition state, (whole)/dominant ≈ φ."""
        sqrt_phi = np.sqrt(PHI)
        _, _, vh = np.linalg.svd(P_PLUS)
        v_plus = vh[0]
        _, _, vh = np.linalg.svd(P_MINUS)
        v_minus = vh[0]
        psi = sqrt_phi * v_plus + 1.0 * v_minus
        psi = psi / np.linalg.norm(psi)
        a_sq = np.linalg.norm(P_PLUS @ psi)**2
        b_sq = np.linalg.norm(P_MINUS @ psi)**2
        whole = a_sq + b_sq
        dominant = max(a_sq, b_sq)
        # whole/dominant should be φ when dominant is the larger sector
        assert abs(whole - 1.0) < TOL  # normalized
        # dominant = a_sq = φ/(φ+1), subordinate = b_sq = 1/(φ+1)
        # whole/dominant = 1/(φ/(φ+1)) = (φ+1)/φ = 1 + 1/φ = φ
        expected = PHI
        actual = whole / dominant
        assert abs(actual - expected) < 0.01, f"Expected φ, got {actual}"


# =====================================================================
# SECTION 5: Open question — emergence from iteration
# =====================================================================

class TestPhiEmergenceOpen:
    """Document and test the open question: does a Clifford process produce φ?

    The Lean Grace operator uses φ explicitly (1/φ^k for grade k).
    True emergence would mean: a process that does NOT use φ produces it
    as a fixed point. These tests document the current status."""

    def test_grace_grade_ratio_is_phi(self):
        """The Lean Grace operator scales grade k by 1/φ^k.
        So the ratio of scale factors between consecutive grades is φ.
        This is φ 'put in', not emerged. We document it."""
        scale_0 = 1.0
        scale_1 = 1.0 / PHI
        scale_2 = 1.0 / (PHI**2)
        assert abs(scale_0 / scale_1 - PHI) < TOL
        assert abs(scale_1 / scale_2 - PHI) < TOL

    def test_placeholder_emergence_iteration(self):
        """Placeholder: Does iterating a Clifford-based 'inverse' operation
        produce the recurrence x_{n+1} = 1 + 1/x_n?

        Status: OPEN. No such operation is yet formalized.
        This test asserts the recurrence converges (sanity)."""
        x = 0.5  # start off the fixed point
        for _ in range(50):
            x = 1 + 1 / x
        assert abs(x - PHI) < 1e-10
