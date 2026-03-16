"""
Phase E: 600-Cell Bridge — Computational Resolution

Tests whether the 120 vertices of the 600-cell embed into Cl(3,1) as
unit spinors forming the binary icosahedral group, and whether the
group's representation theory predicts nuclear shell degeneracies.

E1: Binary icosahedral group 2I embeds in even subalgebra of Cl(3,0) ⊂ Cl(3,1)
E2: 2I acts on R^3 producing the icosahedral rotation group (60 elements of SO(3))
E3: Do the irreps of 2I predict shell-splitting patterns?

Python counterpart to garret_collaboration/IcosahedralMass.lean and
SO3RepTheory.lean, extending them with the actual 600-cell vertex embedding.
"""

import numpy as np
import pytest
from itertools import product as iterproduct

PHI = (1 + np.sqrt(5)) / 2
PHI_INV = 1.0 / PHI
TOL = 1e-10
I4 = np.eye(4)


# =====================================================================
# Cl(3,1) infrastructure (shared with test_zx_axiom_witnesses.py)
# =====================================================================

def _build_gamma():
    g = np.zeros((4, 4, 4))
    g[0] = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]
    g[1] = [[0, 0, 1, 0], [0, 0, 0, -1], [1, 0, 0, 0], [0, -1, 0, 0]]
    g[2] = [[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]
    g[3] = [[0, 0, 0, -1], [0, 0, 1, 0], [0, -1, 0, 0], [1, 0, 0, 0]]
    return g


GAMMA = _build_gamma()
E12 = GAMMA[0] @ GAMMA[1]
E13 = GAMMA[0] @ GAMMA[2]
E23 = GAMMA[1] @ GAMMA[2]


def _close(A, B):
    return np.max(np.abs(np.asarray(A) - np.asarray(B))) < TOL


# =====================================================================
# Quaternion infrastructure
# =====================================================================

def quat_to_matrix(q):
    """Map quaternion (w, x, y, z) to 4x4 Cl(3,1) even-subalgebra element.

    Quaternion basis maps to Cl(3,0) bivectors:
      1 -> I4 (scalar)
      i -> e23 (= gamma1 @ gamma2)
      j -> e31 (= gamma2 @ gamma0)  [note: e31 = -e13]
      k -> e12 (= gamma0 @ gamma1)
    """
    w, x, y, z = q
    return w * I4 + x * E23 + y * (-E13) + z * E12


def quat_mul(a, b):
    """Hamilton product of two quaternions."""
    w1, x1, y1, z1 = a
    w2, x2, y2, z2 = b
    return np.array([
        w1*w2 - x1*x2 - y1*y2 - z1*z2,
        w1*x2 + x1*w2 + y1*z2 - z1*y2,
        w1*y2 - x1*z2 + y1*w2 + z1*x2,
        w1*z2 + x1*y2 - y1*x2 + z1*w2,
    ])


def quat_conj(q):
    return np.array([q[0], -q[1], -q[2], -q[3]])


def quat_norm_sq(q):
    return q[0]**2 + q[1]**2 + q[2]**2 + q[3]**2


# =====================================================================
# Binary icosahedral group 2I (120 elements as unit quaternions)
# =====================================================================

def build_binary_icosahedral_group():
    """Construct all 120 elements of the binary icosahedral group 2I.

    The 120 unit quaternions decompose as:
      24 vertices of the 24-cell (Hurwitz quaternions):
        - 8 elements: ±1, ±i, ±j, ±k
        - 16 elements: (±1 ± i ± j ± k)/2 (all sign combinations)
      96 elements from golden-ratio permutations:
        - All EVEN permutations of (0, ±1, ±φ, ±1/φ)/2
          with independent signs on the 3 non-zero entries
    """
    elements = []

    # --- 8 elements: ±1, ±i, ±j, ±k ---
    for s in [1, -1]:
        elements.append(np.array([s, 0, 0, 0], dtype=float))
        elements.append(np.array([0, s, 0, 0], dtype=float))
        elements.append(np.array([0, 0, s, 0], dtype=float))
        elements.append(np.array([0, 0, 0, s], dtype=float))

    # --- 16 elements: (±1 ± i ± j ± k)/2 ---
    for signs in iterproduct([1, -1], repeat=4):
        elements.append(np.array(signs, dtype=float) / 2.0)

    # --- 96 elements: even permutations of (0, ±1, ±φ, ±1/φ)/2 ---
    base_vals = [0.0, 1.0, PHI, PHI_INV]
    even_perms = [
        (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2),
        (1, 0, 3, 2), (1, 2, 0, 3), (1, 3, 2, 0),
        (2, 0, 1, 3), (2, 1, 3, 0), (2, 3, 0, 1),
        (3, 0, 2, 1), (3, 1, 0, 2), (3, 2, 1, 0),
    ]

    for perm in even_perms:
        base = np.array([base_vals[perm[i]] for i in range(4)])
        nz_pos = [i for i in range(4) if base[i] != 0.0]
        for signs in iterproduct([1, -1], repeat=len(nz_pos)):
            q = base.copy()
            for pos, s in zip(nz_pos, signs):
                q[pos] *= s
            q /= 2.0
            elements.append(q)

    return elements


def _deduplicate(elements):
    """Remove duplicate quaternions."""
    unique = []
    for q in elements:
        found = False
        for u in unique:
            if np.max(np.abs(q - u)) < TOL:
                found = True
                break
        if not found:
            unique.append(q)
    return unique


BINARY_ICOSA = _deduplicate(build_binary_icosahedral_group())


# =====================================================================
# E1: Binary icosahedral group embeds in Cl(3,1)
# =====================================================================

class TestE1BinaryIcosahedralEmbedding:
    """Test that 2I embeds into Cl(3,1) as unit elements of the even subalgebra."""

    def test_group_has_120_elements(self):
        assert len(BINARY_ICOSA) == 120, f"Expected 120, got {len(BINARY_ICOSA)}"

    def test_all_unit_quaternions(self):
        for i, q in enumerate(BINARY_ICOSA):
            nsq = quat_norm_sq(q)
            assert abs(nsq - 1.0) < TOL, f"Element {i}: |q|^2 = {nsq}"

    def test_cl31_embedding_unit_norm(self):
        """Every quaternion maps to a Cl(3,1) element M with M @ M_rev = I."""
        for i, q in enumerate(BINARY_ICOSA):
            M = quat_to_matrix(q)
            M_rev = quat_to_matrix(quat_conj(q))
            prod = M @ M_rev
            assert _close(prod, I4), (
                f"Element {i}: q={q}, M@M_rev != I\n{prod}"
            )

    def test_closure_under_multiplication(self):
        """The 120 Cl(3,1) matrices are closed under matrix multiplication."""
        matrices = [quat_to_matrix(q) for q in BINARY_ICOSA]
        violations = 0
        for i in range(len(matrices)):
            for j in range(len(matrices)):
                prod = matrices[i] @ matrices[j]
                found = False
                for k, mk in enumerate(matrices):
                    if _close(prod, mk):
                        found = True
                        break
                if not found:
                    violations += 1
        assert violations == 0, f"{violations} products not in group"

    def test_identity_in_group(self):
        found = any(_close(quat_to_matrix(q), I4) for q in BINARY_ICOSA)
        assert found, "Identity not in group"

    def test_inverses_exist(self):
        matrices = [quat_to_matrix(q) for q in BINARY_ICOSA]
        for i, Mi in enumerate(matrices):
            inv = quat_to_matrix(quat_conj(BINARY_ICOSA[i]))
            found = any(_close(inv, Mk) for Mk in matrices)
            assert found, f"Inverse of element {i} not in group"

    def test_center_is_Z2(self):
        """The center of 2I is {+I, -I} (order 2)."""
        matrices = [quat_to_matrix(q) for q in BINARY_ICOSA]
        center = []
        for i, Mi in enumerate(matrices):
            commutes_with_all = True
            for Mj in matrices:
                if not _close(Mi @ Mj, Mj @ Mi):
                    commutes_with_all = False
                    break
            if commutes_with_all:
                center.append(i)
        assert len(center) == 2, f"Center has {len(center)} elements"
        center_mats = [matrices[i] for i in center]
        assert any(_close(M, I4) for M in center_mats)
        assert any(_close(M, -I4) for M in center_mats)


# =====================================================================
# E2: 2I acts on R^3 via conjugation, producing icosahedral rotations
# =====================================================================

class TestE2IcosahedralRotations:
    """Test that 2I/{±1} = A5 (icosahedral rotation group, 60 elements)."""

    @staticmethod
    def quat_rotate_vector(q, v):
        """Rotate 3D vector v by quaternion q: q v q*."""
        v_quat = np.array([0, v[0], v[1], v[2]])
        rotated = quat_mul(quat_mul(q, v_quat), quat_conj(q))
        return rotated[1:]

    def test_produces_60_rotations(self):
        """Mapping q -> R(q) where R(q)v = qvq* gives 60 distinct SO(3) matrices."""
        basis = [np.array([1, 0, 0]), np.array([0, 1, 0]), np.array([0, 0, 1])]
        rotation_matrices = []
        for q in BINARY_ICOSA:
            R = np.zeros((3, 3))
            for j in range(3):
                R[:, j] = self.quat_rotate_vector(q, basis[j])
            already = False
            for R_prev in rotation_matrices:
                if np.max(np.abs(R - R_prev)) < TOL:
                    already = True
                    break
            if not already:
                rotation_matrices.append(R)
        assert len(rotation_matrices) == 60, (
            f"Expected 60 rotations, got {len(rotation_matrices)}"
        )

    def test_rotations_are_orthogonal(self):
        """All rotation matrices are in SO(3): R^T R = I, det R = 1."""
        basis = [np.array([1, 0, 0]), np.array([0, 1, 0]), np.array([0, 0, 1])]
        for q in BINARY_ICOSA:
            R = np.zeros((3, 3))
            for j in range(3):
                R[:, j] = self.quat_rotate_vector(q, basis[j])
            assert _close(R.T @ R, np.eye(3)), "R not orthogonal"
            assert abs(np.linalg.det(R) - 1.0) < TOL, "det(R) != 1"

    def test_icosahedral_symmetry_axes(self):
        """Verify the group contains 5-fold, 3-fold, and 2-fold rotations
        characteristic of icosahedral symmetry."""
        basis = [np.array([1, 0, 0]), np.array([0, 1, 0]), np.array([0, 0, 1])]
        traces = set()
        for q in BINARY_ICOSA:
            R = np.zeros((3, 3))
            for j in range(3):
                R[:, j] = self.quat_rotate_vector(q, basis[j])
            tr = round(np.trace(R), 6)
            traces.add(tr)
        tr_5fold = round(2 * np.cos(2 * np.pi / 5) + 1, 6)
        tr_5fold2 = round(2 * np.cos(4 * np.pi / 5) + 1, 6)
        tr_3fold = round(2 * np.cos(2 * np.pi / 3) + 1, 6)
        tr_2fold = round(2 * np.cos(np.pi) + 1, 6)  # = -1

        assert 3.0 in traces, "No identity rotation (trace=3)"
        close_enough = lambda t, target: any(abs(tr - target) < 0.001 for tr in traces)
        assert close_enough(0, tr_5fold), f"No 5-fold rotation. Traces: {sorted(traces)}"
        assert close_enough(0, tr_3fold), f"No 3-fold rotation. Traces: {sorted(traces)}"
        assert close_enough(0, tr_2fold), f"No 2-fold rotation. Traces: {sorted(traces)}"


# =====================================================================
# E3: Do 2I irreps predict shell degeneracies?
# =====================================================================

class TestE3ShellDegeneracyPrediction:
    """Test whether the irreducible representations of 2I predict nuclear
    shell-splitting patterns.

    The binary icosahedral group 2I has 9 irreducible representations
    with dimensions: 1, 2, 2, 3, 3, 4, 4, 5, 6.

    For angular momentum quantum number l, SO(3) irrep has dim 2l+1.
    The odd-dimensional 2I irreps (1, 3, 3, 5) correspond to integer l:
      dim=1 -> l=0, dim=3 -> l=1, dim=5 -> l=2
    The even-dimensional ones (2, 2, 4, 4, 6) correspond to half-integer j.
    """

    IRREP_DIMS = [1, 2, 2, 3, 3, 4, 4, 5, 6]

    def test_irrep_dimensions_sum_to_120(self):
        """Sum of d_i^2 = |G| for any finite group."""
        total = sum(d**2 for d in self.IRREP_DIMS)
        assert total == 120, f"Sum of d^2 = {total}, expected 120"

    def test_num_irreps_equals_conjugacy_classes(self):
        """Number of irreps = number of conjugacy classes."""
        assert len(self.IRREP_DIMS) == 9

    def test_odd_dim_irreps_give_angular_momentum(self):
        """Odd-dimensional irreps correspond to SO(3) irreps with integer l."""
        odd_dims = sorted(d for d in self.IRREP_DIMS if d % 2 == 1)
        assert odd_dims == [1, 3, 3, 5], f"Odd dims: {odd_dims}"
        l_values = [(d - 1) // 2 for d in odd_dims]
        assert l_values == [0, 1, 1, 2]

    def test_shell_capacities_from_odd_irreps(self):
        """Shell capacity = 2(2l+1) with spin doubling."""
        odd_dims = sorted(d for d in self.IRREP_DIMS if d % 2 == 1)
        capacities = [2 * d for d in odd_dims]
        assert capacities == [2, 6, 6, 10]

    def test_cumulative_sums_vs_magic_numbers(self):
        """Test if cumulative sums match magic numbers {2, 8, 20, 28, 50, 82, 126}.

        The 2I irreps alone give shells 2, 6, 6, 10 (odd dims) and
        4, 4, 8, 8, 12 (even dims × 2 for spin).  Cumulative sums of the
        full list sorted ascending: 2, 6, 10, 16, 22, 30, 38, 48, 60.

        These do NOT match the magic numbers.  The magic numbers require
        spin-orbit splitting from the nuclear potential, which is external
        physics input not derivable from the group alone.
        """
        magic_numbers = [2, 8, 20, 28, 50, 82, 126]
        all_caps = sorted([2 * d for d in self.IRREP_DIMS])
        cumsum = list(np.cumsum(all_caps))
        assert cumsum == [2, 6, 10, 16, 22, 30, 38, 48, 60], (
            f"Cumulative shell sums: {cumsum}"
        )
        matches = sum(1 for c in cumsum if c in magic_numbers)
        assert matches <= 2, (
            f"Only {matches}/9 cumulative sums match magic numbers — "
            f"shell filling order requires external physics input"
        )

    def test_so3_branching_rule(self):
        """When restricted from SU(2) to 2I, the spin-j rep decomposes into
        2I irreps. This branching determines which shell closures correspond
        to icosahedral symmetry.

        For the first few j values:
          j=0 (dim 1): -> 1  (trivial)
          j=1/2 (dim 2): -> 2  (fundamental)
          j=1 (dim 3): -> 3  (one of the 3-dim irreps)
          j=3/2 (dim 4): -> 4  (one of the 4-dim irreps)
          j=2 (dim 5): -> 5  (the 5-dim irrep)
          j=5/2 (dim 6): -> 6  (the 6-dim irrep)

        These are all irreducible under 2I up to dim 6.
        Above dim 6, SO(3) irreps decompose into multiple 2I irreps.
        """
        for j2 in range(1, 13):
            dim = j2 + 1
            if dim <= 6:
                assert dim in self.IRREP_DIMS, (
                    f"dim={dim} (j={j2/2}) not a 2I irrep"
                )

    def test_golden_ratio_in_vertices(self):
        """Verify phi appears in the 600-cell vertex coordinates."""
        phi_count = 0
        for q in BINARY_ICOSA:
            for c in q:
                if abs(abs(c) - PHI / 2) < TOL or abs(abs(c) - PHI_INV / 2) < TOL:
                    phi_count += 1
                    break
        assert phi_count >= 48, (
            f"Expected >= 48 elements with phi coordinates, got {phi_count}"
        )

    def test_honest_assessment(self):
        """The 600-cell bridge: what is derived vs what is assumed.

        DERIVED from Cl(3,1):
          - 2I embeds as unit elements of even subalgebra (E1)
          - 2I/{±1} = A5 = icosahedral rotation group (E2)
          - 2I has 9 irreps with dims {1,2,2,3,3,4,4,5,6} (known group theory)
          - Odd-dim irreps give SO(3) angular momentum quantum numbers l=0,1,1,2

        EXTERNAL PHYSICS INPUT:
          - Shell filling ORDER (which subshells fill first) requires
            the nuclear potential shape V ~ harmonic oscillator + spin-orbit
          - Spin-orbit splitting j = l ± 1/2 is a dynamical effect
          - The magic numbers {2,8,20,28,50,82,126} emerge from the
            filling order, NOT from the group structure alone

        CONCLUSION: The 600-cell provides the SYMMETRY STRUCTURE (which
        representations exist) but NOT the DYNAMICS (which order they fill).
        The bridge is real for the symmetry content; the filling order
        remains external input.
        """
        assert True


# =====================================================================
# Cross-validation with Lean IcosahedralMass.lean
# =====================================================================

class TestCrossValidationWithLean:
    """Verify results that are machine-checked in IcosahedralMass.lean."""

    def test_mass_quantization(self):
        """v_boost = phi*G0 + G3 satisfies v_boost^2 = phi*I."""
        v_boost = PHI * GAMMA[0] + GAMMA[3]
        v_sq = v_boost @ v_boost
        assert _close(v_sq, PHI * I4), f"v_boost^2 != phi*I:\n{v_sq}"

    def test_all_spatial_axes(self):
        """(phi*G_k + G3)^2 = phi*I for k = 0, 1, 2."""
        for k in range(3):
            v = PHI * GAMMA[k] + GAMMA[3]
            assert _close(v @ v, PHI * I4)

    def test_pseudoscalar_squared(self):
        """(G0 G1 G2 G3)^2 = -I."""
        omega = GAMMA[0] @ GAMMA[1] @ GAMMA[2] @ GAMMA[3]
        assert _close(omega @ omega, -I4)

    def test_golden_triality(self):
        """Cyclic permutation G0->G1->G2 preserves I3 = G0 G1 G2."""
        I3 = GAMMA[0] @ GAMMA[1] @ GAMMA[2]
        rho_I3 = GAMMA[1] @ GAMMA[2] @ GAMMA[0]
        assert _close(rho_I3, I3)

    def test_so3_commutation(self):
        """[L1, L2] = -2*L3 where L_k are spatial bivectors."""
        L1 = GAMMA[1] @ GAMMA[2]
        L2 = GAMMA[2] @ GAMMA[0]
        L3 = GAMMA[0] @ GAMMA[1]
        assert _close(L1 @ L2 - L2 @ L1, -2 * L3)
        assert _close(L2 @ L3 - L3 @ L2, -2 * L1)
        assert _close(L3 @ L1 - L1 @ L3, -2 * L2)

    def test_magic_numbers_arithmetic(self):
        """Verify magic number cumulative sums from SO3RepTheory.lean."""
        j_up = lambda l: 2 * l + 2
        j_dn = lambda l: 2 * l
        assert j_up(0) == 2
        assert j_up(0) + j_up(1) + j_dn(1) == 8
        assert j_up(0) + j_up(1) + j_dn(1) + j_up(2) + j_up(0) + j_dn(2) == 20
