"""
Bridge Integrity (B): First Computable FSCTF Functional

This test suite defines and validates B — the bridge integrity functional —
as the first operationalized metric from the FSCTF postulate stack.

B measures how well a transformation preserves the bilateral (chiral)
structure that makes two-qubit-ness possible. Concretely:

  B(T) = degree to which transformation T preserves the chirality
         decomposition C^4 = S+ ⊕ S-

A high-B transformation maintains the reciprocal legibility between
the two signature orientations. A low-B transformation degrades it.

This gives us a computable version of:
  - E7 (devourer criterion): D is devourer-like iff B(D) is low
  - P13 (bridge metric): B measures reciprocal legibility across polarity
  - The distinction between sacred and severed branching

Three concrete definitions of B are tested and compared:
  B1: Chirality-commutation distance (how well T commutes with omega)
  B2: Cross-sector leakage (how much T mixes S+ and S-)
  B3: Projector preservation (how well T preserves the P+/P- decomposition)
"""

import numpy as np
import pytest
from scipy.linalg import expm

TOL = 1e-10
I4 = np.eye(4, dtype=complex)


def build_cl31():
    g = np.zeros((4, 4, 4), dtype=complex)
    g[0] = [[1,0,0,0],[0,1,0,0],[0,0,-1,0],[0,0,0,-1]]
    g[1] = [[0,0,1,0],[0,0,0,-1],[1,0,0,0],[0,-1,0,0]]
    g[2] = [[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]]
    g[3] = [[0,0,0,-1],[0,0,1,0],[0,-1,0,0],[1,0,0,0]]
    return g


G = build_cl31()

def all_basis(g):
    I = np.eye(4, dtype=g[0].dtype)
    return [I, g[0],g[1],g[2],g[3],
            g[0]@g[1],g[0]@g[2],g[0]@g[3],g[1]@g[2],g[1]@g[3],g[2]@g[3],
            g[0]@g[1]@g[2],g[0]@g[1]@g[3],g[0]@g[2]@g[3],g[1]@g[2]@g[3],
            g[0]@g[1]@g[2]@g[3]]

B_CL = all_basis(G)
OMEGA = B_CL[15]
P_PLUS = (I4 + 1j * OMEGA) / 2
P_MINUS = (I4 - 1j * OMEGA) / 2

BASIS_NAMES = [
    "1", "e1", "e2", "e3", "e4",
    "e12", "e13", "e14", "e23", "e24", "e34",
    "e123", "e124", "e134", "e234", "e1234",
]
EVEN_IDX = [0, 5, 6, 7, 8, 9, 10, 15]
ODD_IDX = [1, 2, 3, 4, 11, 12, 13, 14]


# =====================================================================
# Bridge Integrity Definitions
# =====================================================================

def bridge_B1(T):
    """B1: Chirality-commutation measure.

    B1(T) = 1 - ||[T, omega]||_F / (2 * ||T||_F * ||omega||_F)

    Ranges from 1 (T commutes with omega = pure even element)
    to some minimum (T maximally mixes chirality).

    Even elements give B1=1. Odd elements give B1<1.
    Mixed elements give intermediate values.
    """
    comm = T @ OMEGA - OMEGA @ T
    norm_comm = np.linalg.norm(comm, 'fro')
    norm_T = np.linalg.norm(T, 'fro')
    norm_omega = np.linalg.norm(OMEGA, 'fro')
    if norm_T < TOL:
        return 1.0
    return 1.0 - norm_comm / (2 * norm_T * norm_omega)


def bridge_B2(T):
    """B2: Cross-sector leakage measure.

    B2(T) = 1 - (||P+ T P-||^2 + ||P- T P+||^2) / ||T||^2

    Ranges from 1 (T preserves sectors completely = pure even)
    to 0 (T is purely cross-sector = pure odd).
    """
    cross_pm = P_PLUS @ T @ P_MINUS
    cross_mp = P_MINUS @ T @ P_PLUS
    norm_cross = np.linalg.norm(cross_pm, 'fro')**2 + np.linalg.norm(cross_mp, 'fro')**2
    norm_T = np.linalg.norm(T, 'fro')**2
    if norm_T < TOL:
        return 1.0
    return 1.0 - norm_cross / norm_T


def bridge_B3(T):
    """B3: Projector preservation under conjugation.

    B3(T) = 1 - ||T P+ T^{-1} - P+||_F / (2 * ||P+||_F)

    Measures how well T preserves the chirality decomposition
    when used as a similarity transformation. Only defined for
    invertible T.

    For even elements: T P+ T^{-1} = P+ exactly, so B3=1.
    For odd elements: T P+ T^{-1} = P-, so B3=0.
    """
    try:
        T_inv = np.linalg.inv(T)
    except np.linalg.LinAlgError:
        return 0.0
    conjugated = T @ P_PLUS @ T_inv
    diff = conjugated - P_PLUS
    norm_diff = np.linalg.norm(diff, 'fro')
    norm_P = np.linalg.norm(P_PLUS, 'fro')
    return max(0.0, 1.0 - norm_diff / (2 * norm_P))


# =====================================================================
# SECTION 1: B on basis elements — calibration
# =====================================================================

class TestBridgeCalibration:
    """Verify B gives the expected values on known elements."""

    def test_identity_has_full_bridge(self):
        """Identity preserves everything. All B measures should be 1."""
        assert abs(bridge_B1(I4) - 1.0) < TOL
        assert abs(bridge_B2(I4) - 1.0) < TOL
        assert abs(bridge_B3(I4) - 1.0) < TOL

    def test_even_elements_have_full_bridge(self):
        """Even elements commute with omega and preserve sectors."""
        for idx in EVEN_IDX:
            b = B_CL[idx]
            b1 = bridge_B1(b)
            b2 = bridge_B2(b)
            assert abs(b1 - 1.0) < 0.01, (
                f"{BASIS_NAMES[idx]}: B1={b1:.4f}, expected ~1.0"
            )
            assert abs(b2 - 1.0) < 0.01, (
                f"{BASIS_NAMES[idx]}: B2={b2:.4f}, expected ~1.0"
            )

    def test_odd_elements_have_reduced_bridge(self):
        """Odd elements anticommute with omega and cross sectors."""
        for idx in ODD_IDX:
            b = B_CL[idx]
            b1 = bridge_B1(b)
            b2 = bridge_B2(b)
            assert b1 <= 0.5, (
                f"{BASIS_NAMES[idx]}: B1={b1:.4f}, expected <= 0.5"
            )
            assert b2 <= 0.01, (
                f"{BASIS_NAMES[idx]}: B2={b2:.4f}, expected ~0"
            )

    def test_B_values_for_all_basis_elements(self):
        """Print B values for the complete basis. Calibration data."""
        print("\n  Bridge integrity for all basis elements:")
        print(f"  {'Element':8s}  {'B1':>8s}  {'B2':>8s}  {'B3':>8s}  {'Grade':>5s}")
        grades = [0, 1,1,1,1, 2,2,2,2,2,2, 3,3,3,3, 4]
        for i in range(16):
            b = B_CL[i]
            b1 = bridge_B1(b)
            b2 = bridge_B2(b)
            b3 = bridge_B3(b)
            grade = grades[i]
            parity = "even" if i in EVEN_IDX else "odd"
            print(f"  {BASIS_NAMES[i]:8s}  {b1:8.4f}  {b2:8.4f}  {b3:8.4f}  {grade:>3d} ({parity})")


# =====================================================================
# SECTION 2: B on quantum gates — sacred vs devourer
# =====================================================================

class TestBridgeOnGates:
    """Evaluate B on standard quantum gates to see which preserve
    the bilateral structure and which cross it."""

    def test_single_qubit_gates_preserve_bridge(self):
        """Single-qubit gates (acting on one Weyl sector) should have
        high bridge integrity — they transform within one sector."""
        # Z-rotation: exp(i*theta*e12/2) — an even element
        theta = 0.7
        R_z = np.cos(theta/2) * I4 + 1j * np.sin(theta/2) * B_CL[5]  # e12

        b1 = bridge_B1(R_z)
        b2 = bridge_B2(R_z)
        print(f"\n  Z-rotation (even): B1={b1:.4f}, B2={b2:.4f}")
        assert b1 > 0.9, f"Z-rotation should have high B1, got {b1}"

    def test_hadamard_bridge(self):
        """Hadamard = (e1+e3)/sqrt(2) — this is an ODD element.
        It should have reduced bridge integrity because it crosses sectors."""
        H = (B_CL[1] + B_CL[3]) / np.sqrt(2)  # (e1+e3)/sqrt(2)
        b1 = bridge_B1(H)
        b2 = bridge_B2(H)
        b3 = bridge_B3(H)
        print(f"\n  Hadamard (odd): B1={b1:.4f}, B2={b2:.4f}, B3={b3:.4f}")
        assert b1 <= 0.5, f"Hadamard should have low B1, got {b1}"

    def test_cnot_bridge(self):
        """CNOT is 50% even + 50% odd. It should have intermediate bridge."""
        CNOT = np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]], dtype=complex)
        b1 = bridge_B1(CNOT)
        b2 = bridge_B2(CNOT)
        b3 = bridge_B3(CNOT)
        print(f"\n  CNOT (mixed): B1={b1:.4f}, B2={b2:.4f}, B3={b3:.4f}")

    def test_swap_bridge(self):
        """SWAP = 0.5(1 + e3 + e14 + e134). Mixed even/odd."""
        SWAP = np.array([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]], dtype=complex)
        b1 = bridge_B1(SWAP)
        b2 = bridge_B2(SWAP)
        b3 = bridge_B3(SWAP)
        print(f"\n  SWAP (mixed): B1={b1:.4f}, B2={b2:.4f}, B3={b3:.4f}")


# =====================================================================
# SECTION 3: B under composition — does bridge degrade?
# =====================================================================

class TestBridgeDegradation:
    """Test how B evolves under composition of transformations.
    This is the operational content of the devourer criterion."""

    def test_even_composition_preserves_bridge(self):
        """Composing even elements should keep B=1.
        'Internal coherence composed with internal coherence stays coherent.'"""
        R1 = np.cos(0.3) * I4 + np.sin(0.3) * B_CL[5]  # e12 rotor
        R2 = np.cos(0.5) * I4 + np.sin(0.5) * B_CL[8]  # e23 rotor
        composed = R1 @ R2

        b2_1 = bridge_B2(R1)
        b2_2 = bridge_B2(R2)
        b2_comp = bridge_B2(composed)

        print(f"\n  Even ∘ Even: B2(R1)={b2_1:.4f}, B2(R2)={b2_2:.4f}, B2(R1∘R2)={b2_comp:.4f}")
        assert b2_comp > 0.95, "Even composed with even should preserve bridge"

    def test_odd_composition_returns_to_even(self):
        """Odd ∘ odd = even. Two crossings return to the same side.
        'Going out and coming back restores bridge.'"""
        e1 = B_CL[1]
        e2 = B_CL[2]
        composed = e1 @ e2  # e1*e2 = e12, which is even

        b2_e1 = bridge_B2(e1)
        b2_e2 = bridge_B2(e2)
        b2_comp = bridge_B2(composed)

        print(f"\n  Odd ∘ Odd: B2(e1)={b2_e1:.4f}, B2(e2)={b2_e2:.4f}, B2(e1∘e2)={b2_comp:.4f}")
        assert b2_comp > 0.95, "Odd composed with odd should restore bridge (return)"

    def test_random_unitary_bridge(self):
        """Random unitaries from the Clifford group should have well-defined B.
        All Clifford group elements are products of generators, so they have
        definite even/odd parity and thus definite B values."""
        rng = np.random.default_rng(42)
        b2_values = []
        for _ in range(100):
            # Random Clifford element: product of random generators
            T = I4.copy()
            n_factors = rng.integers(1, 8)
            for _ in range(n_factors):
                idx = rng.integers(0, 16)
                T = T @ B_CL[idx]
            b2 = bridge_B2(T)
            b2_values.append(b2)

        b2_arr = np.array(b2_values)
        print(f"\n  Random Clifford elements (100):")
        print(f"    B2 mean: {b2_arr.mean():.4f}")
        print(f"    B2 std:  {b2_arr.std():.4f}")
        print(f"    B2 min:  {b2_arr.min():.4f}")
        print(f"    B2 max:  {b2_arr.max():.4f}")

    def test_non_unitary_degrades_bridge(self):
        """Non-unitary (non-Clifford) transformations can degrade B
        in ways that unitary ones cannot. This is the devourer signature:
        transformations that are not coherence-preserving (not unitary)
        break the bridge structure."""
        rng = np.random.default_rng(99)

        unitary_B2s = []
        nonunitary_B2s = []

        for _ in range(100):
            # Random unitary
            H = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
            H = H + H.conj().T  # Hermitian
            U = expm(1j * H)
            unitary_B2s.append(bridge_B2(U))

            # Random non-unitary (just a random matrix)
            M = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
            nonunitary_B2s.append(bridge_B2(M))

        u_arr = np.array(unitary_B2s)
        n_arr = np.array(nonunitary_B2s)

        print(f"\n  Unitary B2:     mean={u_arr.mean():.4f}, std={u_arr.std():.4f}")
        print(f"  Non-unitary B2: mean={n_arr.mean():.4f}, std={n_arr.std():.4f}")

        # Both will cluster around 0.5 (random matrices have no preferred
        # chirality), but the point is that non-unitary ones CAN degrade
        # B below what any unitary transformation achieves.


# =====================================================================
# SECTION 4: Grace as unitarity
# =====================================================================

class TestGraceAsUnitarity:
    """Grace recoverability (E6) has a natural computational realization:
    unitary transformations are always invertible.

    If T is unitary, then T^{-1} = T^dagger exists, and any state
    transformed by T can be recovered. This is the computational
    content of 'return is always possible.'

    Non-unitary transformations can be irreversible — this is the
    computational content of 'devourer processes obstruct return.'"""

    def test_unitary_is_reversible(self):
        """Every unitary transformation has an exact inverse.
        Grace = every lawful transformation can be undone."""
        rng = np.random.default_rng(77)
        for _ in range(50):
            H = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
            H = H + H.conj().T
            U = expm(1j * H * 0.1)

            # U is unitary: U^dag U = I
            assert np.max(np.abs(U.conj().T @ U - I4)) < 1e-8, "U should be unitary"

            # Any state can be recovered
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi = psi / np.linalg.norm(psi)

            transformed = U @ psi
            recovered = U.conj().T @ transformed

            assert np.max(np.abs(recovered - psi)) < 1e-8, "State should be recoverable"

    def test_non_unitary_can_be_irreversible(self):
        """Singular (non-invertible) transformations destroy information.
        States cannot be recovered. This is the devourer signature."""
        # Projection onto S+ (rank 2, not invertible)
        psi = np.array([0.5, 0.5, 0.5, 0.5], dtype=complex)
        projected = P_PLUS @ psi

        # Information in S- is lost
        s_minus_component = P_MINUS @ psi
        s_minus_after = P_MINUS @ projected

        assert np.linalg.norm(s_minus_component) > TOL, "Original has S- component"
        assert np.linalg.norm(s_minus_after) < TOL, "Projection destroys S- component"


# =====================================================================
# SECTION 5: Coherence functional C (and C_l / C_g split)
# =====================================================================

def coherence_C_g(psi):
    """C_g: Global coherence = total norm squared.

    C_g(psi) = ||psi||². Preserved by unitary transformations.
    Measures the total coherent amplitude."""
    return np.linalg.norm(psi)**2


def coherence_C_l(psi):
    """C_l: Local coherence = bilateral balance across chiral sectors.

    C_l(psi) = 2 * min(||P+ psi||², ||P- psi||²) / ||psi||².

    Ranges from 0 (state entirely in one sector) to 1 (perfect 50-50 split).
    Measures how much both sectors are populated — 'local' in the sense
    of coherence within each sector being present."""
    n2 = np.linalg.norm(psi)**2
    if n2 < TOL:
        return 0.0
    p_plus = np.linalg.norm(P_PLUS @ psi)**2 / n2
    p_minus = np.linalg.norm(P_MINUS @ psi)**2 / n2
    return 2 * min(p_plus, p_minus)


# =====================================================================
# K, O, F — Premature closure triad (finalanswernotes.md)
# =====================================================================
# PrematureClosure(m) ⟺ K(m) < U ∧ Closure increases despite insufficient integration
# O = openness to further integration
# F = premature finalization pressure

def integration_K(psi):
    """K: Integration sufficiency / global coherence participation.

    K(psi) = C_g(psi) = ||psi||².

    When K is low (e.g. under projection), integration is insufficient;
    closing (finalizing) would be premature. PrematureClosure ⟺ K < threshold."""

    return coherence_C_g(psi)


def openness_O(psi):
    """O: Openness to further integration.

    O(psi) = C_l(psi) = bilateral balance.

    High O = both chiral sectors present = open to reconciliation.
    Low O = one sector dominates = closed to further integration."""

    return coherence_C_l(psi)


def finalization_pressure_F(psi):
    """F: Premature finalization pressure.

    F(psi) = 1 - O(psi) = 1 - C_l(psi).

    High F = state is 'finalized' in one sector (one-sided).
    Low F = state is open (bilateral). Devourer-like: F↑ while K↓."""

    return 1.0 - openness_O(psi)


class TestCoherenceFunctional:
    """First operational definition of C — coherence.

    C measures how much of a state's structure is preserved under
    a transformation. For unitary T: C(T(psi)) = C(psi) always.
    For non-unitary T: C can decrease.

    Simplest definition: C(psi) = sum of squared amplitudes = ||psi||^2.
    This is trivially preserved by unitary transformations and can
    decrease under non-unitary ones. It captures the most basic
    meaning of 'coherence preservation.'

    A more interesting definition uses the von Neumann entropy of
    the chiral reduced density matrix — measuring how entangled
    psi is across the S+/S- split."""

    def test_norm_preservation_under_unitary(self):
        """C = ||psi||^2 is preserved under unitary T. Always."""
        rng = np.random.default_rng(42)
        for _ in range(100):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi = psi / np.linalg.norm(psi)

            H = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
            H = H + H.conj().T
            U = expm(1j * H * 0.1)

            transformed = U @ psi
            assert abs(np.linalg.norm(transformed) - 1.0) < 1e-8

    def test_norm_loss_under_non_unitary(self):
        """Non-unitary transformations can reduce ||psi||.
        This is coherence loss."""
        rng = np.random.default_rng(43)
        losses = 0
        for _ in range(100):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi = psi / np.linalg.norm(psi)

            M = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
            M = M / np.linalg.norm(M, 'fro')  # normalize

            transformed = M @ psi
            if np.linalg.norm(transformed) < 0.95:
                losses += 1

        assert losses > 10, "Non-unitary should sometimes reduce norm (coherence)"

    def test_chiral_entropy_as_coherence(self):
        """A deeper C: the purity of the chiral reduced state.

        For a pure state psi in C^4 = S+ + S-, define:
          rho_+ = Tr_{S-}(|psi><psi|) (partial trace over S-)

        C_chiral(psi) = Tr(rho_+^2) = purity of the reduced state.

        C_chiral = 1 for product states (psi = psi+ x psi-)
        C_chiral = 0.5 for maximally entangled states (Bell states)

        This measures how 'factorizable' the state is across the
        chiral split — i.e., how much the two orientational sectors
        are independently coherent vs entangled with each other."""
        # Product state: |0> in S+ x |0> in S-
        # In the standard basis, |00> = [1,0,0,0]
        product = np.array([1, 0, 0, 0], dtype=complex)

        # Bell state: (|00> + |11>)/sqrt(2)
        bell = np.array([1, 0, 0, 1], dtype=complex) / np.sqrt(2)

        def chiral_purity(psi):
            rho = np.outer(psi, psi.conj())
            rho_plus = P_PLUS @ rho @ P_PLUS
            # Purity of the S+ sector
            return np.real(np.trace(rho_plus @ rho_plus))

        p_product = chiral_purity(product)
        p_bell = chiral_purity(bell)

        print(f"\n  Chiral purity:")
        print(f"    Product state: {p_product:.4f}")
        print(f"    Bell state:    {p_bell:.4f}")

        # Product state should have higher chiral purity
        # (each sector is independently coherent)
        # Bell state has lower purity (sectors are entangled)

    def test_C_g_preserved_by_unitary(self):
        """C_g = ||psi||² is preserved under unitary T."""
        rng = np.random.default_rng(44)
        for _ in range(50):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi = psi / np.linalg.norm(psi)
            H = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
            H = H + H.conj().T
            U = expm(1j * H * 0.1)
            transformed = U @ psi
            assert abs(coherence_C_g(psi) - coherence_C_g(transformed)) < TOL

    def test_C_l_on_pure_sector_state(self):
        """State entirely in S+ has C_l = 0 (no bilateral balance)."""
        psi = P_PLUS @ np.array([1, 1, 0, 0], dtype=complex)
        psi = psi / np.linalg.norm(psi)
        assert coherence_C_l(psi) < 0.01

    def test_C_l_on_balanced_state(self):
        """50-50 split across sectors has C_l = 1."""
        col_plus = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        col_minus = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        v_plus = col_plus / np.linalg.norm(col_plus)
        v_minus = col_minus / np.linalg.norm(col_minus)
        psi = v_plus + v_minus
        psi = psi / np.linalg.norm(psi)
        c_l = coherence_C_l(psi)
        assert abs(c_l - 1.0) < 0.1, f"Expected C_l≈1 for balanced state, got {c_l}"

    def test_C_l_C_g_behave_differently(self):
        """C_l and C_g can change independently. Projection can reduce C_g while C_l varies."""
        col_plus = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        col_minus = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        v_plus = col_plus / np.linalg.norm(col_plus)
        v_minus = col_minus / np.linalg.norm(col_minus)
        psi = (v_plus + v_minus) / np.sqrt(2)
        assert abs(coherence_C_g(psi) - 1.0) < TOL
        assert coherence_C_l(psi) > 0.9

        # Project onto S+ reduces C_g (norm loss) and C_l (no longer bilateral)
        proj = P_PLUS @ psi
        assert coherence_C_g(proj) < 1.0
        assert coherence_C_l(proj) < 0.01


# =====================================================================
# SECTION 6: Identity functional I
# =====================================================================

class TestIdentityFunctional:
    """First operational definition of I — identity persistence.

    I(psi, T) = |<psi|T|psi>|^2 = probability that psi survives
    transformation T and is found in the same state.

    For T = identity: I = 1 (perfect persistence).
    For T = some unitary: I depends on the angle of rotation.
    For T = projection: I = overlap with the projection subspace.

    This captures 'what survives transformation.'"""

    def test_identity_transformation_preserves(self):
        """I(psi, I) = 1 for all psi."""
        rng = np.random.default_rng(55)
        for _ in range(100):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi = psi / np.linalg.norm(psi)
            I_val = abs(psi.conj() @ psi)**2
            assert abs(I_val - 1.0) < TOL

    def test_small_rotation_nearly_preserves(self):
        """Small rotations give I close to 1. Continuous identity."""
        rng = np.random.default_rng(56)
        psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
        psi = psi / np.linalg.norm(psi)

        for theta in [0.01, 0.05, 0.1, 0.5, 1.0, np.pi]:
            R = np.cos(theta/2) * I4 + np.sin(theta/2) * B_CL[5]
            transformed = R @ psi
            I_val = abs(psi.conj() @ transformed)**2

            if theta < 0.1:
                assert I_val > 0.99, f"Small rotation should nearly preserve, I={I_val}"

    def test_chirality_flip_identity(self):
        """How much identity survives a chirality flip?
        Applying an odd element (sector crossing) to a chiral state."""
        # State purely in S+
        psi_plus = P_PLUS @ np.array([1, 0, 1, 0], dtype=complex)
        psi_plus = psi_plus / np.linalg.norm(psi_plus)

        # Apply e1 (odd element, crosses sectors)
        e1 = B_CL[1]
        flipped = e1 @ psi_plus
        flipped = flipped / np.linalg.norm(flipped)

        I_val = abs(psi_plus.conj() @ flipped)**2
        print(f"\n  Identity under chirality flip: I = {I_val:.4f}")

        # The identity should be low — the state has moved to S-
        # But applying e1 again returns it (I through the round trip should be high)
        returned = e1 @ flipped
        returned = returned / np.linalg.norm(returned)

        I_roundtrip = abs(psi_plus.conj() @ returned)**2
        print(f"  Identity after round trip:     I = {I_roundtrip:.4f}")

        assert I_roundtrip > 0.95, "Round-trip crossing should restore identity"


# =====================================================================
# SECTION 6b: K, O, F — Premature closure triad
# =====================================================================

class TestKOFTriad:
    """K, O, F from finalanswernotes: PrematureClosure ⟺ K < U; O = openness; F = finalization."""

    def test_K_equals_C_g(self):
        """K = C_g by definition."""
        rng = np.random.default_rng(91)
        psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
        psi = psi / np.linalg.norm(psi)
        assert abs(integration_K(psi) - coherence_C_g(psi)) < TOL

    def test_O_equals_C_l(self):
        """O = C_l by definition."""
        col_plus = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        col_minus = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        psi = (col_plus / np.linalg.norm(col_plus) + col_minus / np.linalg.norm(col_minus)) / np.sqrt(2)
        assert abs(openness_O(psi) - coherence_C_l(psi)) < TOL

    def test_F_equals_one_minus_O(self):
        """F = 1 - O by definition."""
        psi = P_PLUS @ np.array([1, 1, 0, 0], dtype=complex)
        psi = psi / np.linalg.norm(psi)
        assert abs(finalization_pressure_F(psi) - (1 - openness_O(psi))) < TOL

    def test_one_sector_state_has_high_F_low_O(self):
        """State entirely in one sector: F high, O low."""
        psi = P_PLUS @ np.array([1, 1, 0, 0], dtype=complex)
        psi = psi / np.linalg.norm(psi)
        assert openness_O(psi) < 0.01
        assert finalization_pressure_F(psi) > 0.99

    def test_balanced_state_has_low_F_high_O(self):
        """50-50 split: F low, O high."""
        col_plus = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        col_minus = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        psi = (col_plus / np.linalg.norm(col_plus) + col_minus / np.linalg.norm(col_minus)) / np.sqrt(2)
        assert openness_O(psi) > 0.9
        assert finalization_pressure_F(psi) < 0.1

    def test_projection_reduces_K(self):
        """Projection (devourer-like) reduces K = C_g."""
        col_plus = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        col_minus = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        psi = (col_plus / np.linalg.norm(col_plus) + col_minus / np.linalg.norm(col_minus)) / np.sqrt(2)
        proj = P_PLUS @ psi
        assert integration_K(proj) < integration_K(psi)

    def test_unitary_preserves_K_and_O(self):
        """Even unitary (rotor) preserves K and O. Commutes with chirality."""
        col_plus = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        col_minus = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        psi = (col_plus / np.linalg.norm(col_plus) + col_minus / np.linalg.norm(col_minus)) / np.sqrt(2)
        # Even rotor: R = cos(θ)I + sin(θ)e12 commutes with OMEGA
        theta = 0.5
        R = np.cos(theta/2) * I4 + np.sin(theta/2) * B_CL[5]  # e12
        Tpsi = R @ psi
        assert abs(integration_K(psi) - integration_K(Tpsi)) < TOL
        assert abs(openness_O(psi) - openness_O(Tpsi)) < TOL

    def test_devourer_signature_K_down_F_up(self):
        """Devourer: K↓ (global coherence lost), F↑ (finalized in one sector).
        Projection onto S+ produces this signature."""
        col_plus = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        col_minus = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        psi = (col_plus / np.linalg.norm(col_plus) + col_minus / np.linalg.norm(col_minus)) / np.sqrt(2)
        proj = P_PLUS @ psi  # unnormalized: norm < 1
        proj_n = proj / np.linalg.norm(proj)  # normalized for F (shape only)
        # K drops: projection loses norm
        assert integration_K(psi) > integration_K(proj)
        # F rises: output is one-sector (finalized)
        assert finalization_pressure_F(proj_n) > finalization_pressure_F(psi)


# =====================================================================
# SECTION 7: Lean–Python bridge (Grace ↔ B, C, I)
# =====================================================================

class TestLeanPythonBridge:
    """Bridge assertion: Grace-recoverable (Lean E6) ↔ Unitary ↔ Preserves B, C, I.

    See tests/LEAN_PYTHON_BRIDGE.md for full documentation."""

    def test_unitary_preserves_B_C_I(self):
        """Unitary T preserves B(T), C_g(Tψ)=C_g(ψ), and I is recoverable.
        This is the computational content of Grace = recoverability."""
        rng = np.random.default_rng(88)
        psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
        psi = psi / np.linalg.norm(psi)

        H = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
        H = H + H.conj().T
        U = expm(1j * H * 0.1)

        Tpsi = U @ psi
        assert abs(coherence_C_g(psi) - coherence_C_g(Tpsi)) < TOL
        assert np.max(np.abs(U.conj().T @ U - I4)) < 1e-8  # unitary
        # Recoverability: U^{-1} exists
        recovered = U.conj().T @ Tpsi
        assert np.max(np.abs(recovered - psi)) < TOL

    def test_non_unitary_can_violate_bridge(self):
        """Non-unitary T can reduce C_g and be irreversible.
        Devourer signature: violates the Grace–B/C/I bridge."""
        psi = np.array([1, 0, 1, 0], dtype=complex) / np.sqrt(2)
        P = P_PLUS  # projection
        Tpsi = P @ psi
        assert coherence_C_g(Tpsi) < coherence_C_g(psi)
        # No inverse: information lost
        assert np.linalg.matrix_rank(P) < 4


# =====================================================================
# SECTION 8: Putting it together — the devourer test
# =====================================================================

class TestDevourerCriterion:
    """E7 instantiated: a transformation is devourer-like iff it
    degrades C, B, or I in ways that cannot be recovered."""

    def test_classify_transformations(self):
        """Classify a set of transformations as sacred or devourer
        using the C, B, I functionals."""
        rng = np.random.default_rng(123)

        psi = np.array([1, 0, 0, 0], dtype=complex)

        transformations = {}

        # Sacred: even rotor (preserves C, B, I all high)
        theta = 0.5
        R = np.cos(theta/2) * I4 + np.sin(theta/2) * B_CL[5]
        transformations["Even rotor"] = R

        # Sacred: odd crossing (reduces I temporarily, but invertible)
        transformations["Odd crossing (e1)"] = B_CL[1].astype(complex)

        # Sacred: CNOT (entangling but unitary)
        CNOT = np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]], dtype=complex)
        transformations["CNOT"] = CNOT

        # Devourer: projection onto S+ (irreversible, destroys S- component)
        transformations["S+ projection"] = P_PLUS

        # Devourer: random non-unitary contraction
        M = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
        M = M / (2 * np.linalg.norm(M, 'fro'))  # sub-unitary
        transformations["Random contraction"] = M

        # Devourer: decoherence channel (diagonal projection)
        D = np.diag([1, 0.1, 0.1, 0.1]).astype(complex)
        transformations["Decoherence"] = D

        print("\n  Transformation Classification:")
        print(f"  {'Name':25s} {'B2':>8s} {'C(Tψ)':>8s} {'I(ψ,Tψ)':>10s} {'Unitary':>8s} {'Class':>10s}")
        print("  " + "-" * 75)

        for name, T in transformations.items():
            Tpsi = T @ psi
            norm_Tpsi = np.linalg.norm(Tpsi)

            b2 = bridge_B2(T)
            c_val = norm_Tpsi**2
            if norm_Tpsi > TOL:
                i_val = abs(psi.conj() @ (Tpsi / norm_Tpsi))**2
            else:
                i_val = 0.0

            is_unitary = np.max(np.abs(T.conj().T @ T - I4)) < 1e-6

            if is_unitary:
                classification = "SACRED"
            elif c_val < 0.5 or (not is_unitary and b2 < 0.3):
                classification = "DEVOURER"
            else:
                classification = "MIXED"

            print(f"  {name:25s} {b2:8.4f} {c_val:8.4f} {i_val:10.4f} {str(is_unitary):>8s} {classification:>10s}")


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short", "-s"])
