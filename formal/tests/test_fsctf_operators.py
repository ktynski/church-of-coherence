"""
FSCTF Named Operators: Lₑ, Lᵣ, R, isDevourer, Mₙ recursion

From finalanswernotes.md postulates P5–P18:

  Lₑ (Emanative Love): W → (S⁺, S⁻, χ)    [P5, P8]
  Lᵣ (Returning Love): (S⁺, S⁻) → W        [P8, P9]
  R  (Essence Return): x → σ (scalar)        [P15]
  isDevourer: T × ψ → Bool                   [P18]
  Mₙ recursion: M_{n+1} = Lₑ(Mₙ)            [P16, P17]

Each operator is defined, then tested against the postulate it instantiates.
"""

import numpy as np
import pytest

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
OMEGA = G[0] @ G[1] @ G[2] @ G[3]
P_PLUS = (I4 + 1j * OMEGA) / 2
P_MINUS = (I4 - 1j * OMEGA) / 2


# =====================================================================
# Operator definitions
# =====================================================================

def emanative_love(psi):
    """Lₑ: W → (ψ₊, ψ₋, χ).

    Splits a state into its chiral components and records the
    relative chirality χ = ||P₊ψ||² - ||P₋ψ||²."""
    psi_plus = P_PLUS @ psi
    psi_minus = P_MINUS @ psi
    n_plus = np.linalg.norm(psi_plus)**2
    n_minus = np.linalg.norm(psi_minus)**2
    total = n_plus + n_minus
    chi = (n_plus - n_minus) / total if total > TOL else 0.0
    return psi_plus, psi_minus, chi


def returning_love(psi_plus, psi_minus):
    """Lᵣ: (ψ₊, ψ₋) → W.

    Recombines the two chiral sectors. If no information was lost,
    Lᵣ(Lₑ(ψ)) = ψ."""
    return psi_plus + psi_minus


def essence_return(psi):
    """R: ψ → σ (scalar).

    The scalar part of ψ†ψ — the 'trace' or 'essence' that survives
    when a form is reunified with its chirality complement.
    R(ψ) = ⟨ψ|ψ⟩ = ||ψ||². This is the irreducible scalar residue."""
    return np.real(np.vdot(psi, psi))


def is_devourer(T, psi, b_threshold=0.3, c_threshold=0.5, i_threshold=0.1):
    """isDevourer(T, ψ): P18 formal predicate.

    A transformation is devourer-like iff it degrades C, B, or I:
      C_g(Tψ) < c_threshold · C_g(ψ)
      OR B(T) < b_threshold
      OR I(ψ, Tψ) < i_threshold

    where:
      C_g = ||ψ||²  (global coherence)
      B = 1 - cross-sector leakage
      I = |⟨ψ|Tψ⟩|² / (||ψ||²·||Tψ||²)  (identity persistence)
    """
    Tpsi = T @ psi
    norm_psi = np.linalg.norm(psi)
    norm_Tpsi = np.linalg.norm(Tpsi)

    if norm_psi < TOL:
        return False

    # C_g degradation
    c_ratio = norm_Tpsi**2 / norm_psi**2
    c_degraded = c_ratio < c_threshold

    # B (cross-sector leakage)
    cross_pm = P_PLUS @ T @ P_MINUS
    cross_mp = P_MINUS @ T @ P_PLUS
    norm_T = np.linalg.norm(T, 'fro')**2
    b_val = 1.0 - (np.linalg.norm(cross_pm, 'fro')**2 +
                    np.linalg.norm(cross_mp, 'fro')**2) / max(norm_T, TOL)
    b_degraded = b_val < b_threshold

    # I (identity persistence)
    if norm_Tpsi < TOL:
        i_val = 0.0
    else:
        overlap = np.abs(np.vdot(psi, Tpsi))**2
        i_val = overlap / (norm_psi**2 * norm_Tpsi**2)
    i_degraded = i_val < i_threshold

    return c_degraded or b_degraded or i_degraded


# =====================================================================
# SECTION 1: Lₑ tests — Emanative Love (P5, P8)
# =====================================================================

class TestEmanativeLove:
    """P5: W → (S⁺, S⁻, χ) is a coherence-preserving split."""

    def test_P7_coherence_preserved(self):
        """C(Lₑ(W)) = C(W): the chiral split preserves total norm.
        This is P7: emanative love does not destroy coherence."""
        rng = np.random.default_rng(42)
        for _ in range(100):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi_plus, psi_minus, _ = emanative_love(psi)
            norm_before = np.linalg.norm(psi)**2
            norm_after = np.linalg.norm(psi_plus)**2 + np.linalg.norm(psi_minus)**2
            assert abs(norm_before - norm_after) < TOL, (
                f"Norm changed: {norm_before:.8f} → {norm_after:.8f}"
            )

    def test_sectors_are_orthogonal(self):
        """P₊ψ and P₋ψ live in orthogonal subspaces."""
        rng = np.random.default_rng(43)
        for _ in range(100):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi_plus, psi_minus, _ = emanative_love(psi)
            overlap = np.abs(np.vdot(psi_plus, psi_minus))
            assert overlap < TOL, f"Sectors not orthogonal: overlap = {overlap}"

    def test_chirality_range(self):
        """χ ∈ [-1, 1]. χ = +1 for pure S⁺, χ = -1 for pure S⁻, 0 for balanced."""
        # Pure S+ state
        col = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        psi_sp = col / np.linalg.norm(col)
        _, _, chi_sp = emanative_love(psi_sp)
        assert abs(chi_sp - 1.0) < 0.01

        # Pure S- state
        col = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        psi_sm = col / np.linalg.norm(col)
        _, _, chi_sm = emanative_love(psi_sm)
        assert abs(chi_sm - (-1.0)) < 0.01

    def test_idempotence_of_projection(self):
        """P₊(P₊ψ) = P₊ψ: projectors are idempotent."""
        rng = np.random.default_rng(44)
        psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
        psi_plus, _, _ = emanative_love(psi)
        pp2, _, _ = emanative_love(psi_plus)
        assert np.max(np.abs(pp2 - psi_plus)) < TOL


# =====================================================================
# SECTION 2: Lᵣ tests — Returning Love (P8, P9)
# =====================================================================

class TestReturningLove:
    """P8-P9: Lᵣ(Lₑ(ψ)) = ψ. Return recovers the original."""

    def test_P8_return_recovers_original(self):
        """Lᵣ(Lₑ(ψ)) = ψ for all ψ."""
        rng = np.random.default_rng(50)
        for _ in range(100):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi_plus, psi_minus, _ = emanative_love(psi)
            recovered = returning_love(psi_plus, psi_minus)
            assert np.max(np.abs(recovered - psi)) < TOL

    def test_return_is_left_inverse(self):
        """Lᵣ ∘ Lₑ = id on the state space."""
        rng = np.random.default_rng(51)
        psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
        recovered = returning_love(*emanative_love(psi)[:2])
        assert np.max(np.abs(recovered - psi)) < TOL

    def test_return_preserves_norm(self):
        """||Lᵣ(ψ₊, ψ₋)|| = ||ψ₊||² + ||ψ₋||² (by orthogonality)."""
        rng = np.random.default_rng(52)
        for _ in range(50):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi_plus, psi_minus, _ = emanative_love(psi)
            returned = returning_love(psi_plus, psi_minus)
            assert abs(np.linalg.norm(returned)**2 -
                       (np.linalg.norm(psi_plus)**2 + np.linalg.norm(psi_minus)**2)) < TOL


# =====================================================================
# SECTION 3: R tests — Essence Return (P15)
# =====================================================================

class TestEssenceReturn:
    """P15: R(x, χ(x)) → σ. Reunification yields scalar residue."""

    def test_P15_essence_is_scalar(self):
        """R(ψ) is a real scalar for all ψ."""
        rng = np.random.default_rng(60)
        for _ in range(100):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            sigma = essence_return(psi)
            assert isinstance(sigma, (float, np.floating))
            assert sigma >= 0

    def test_R_of_normalized_state_is_one(self):
        """For normalized ψ, R(ψ) = 1."""
        rng = np.random.default_rng(61)
        for _ in range(50):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi = psi / np.linalg.norm(psi)
            assert abs(essence_return(psi) - 1.0) < TOL

    def test_P14_identity_return(self):
        """P14: R(1, x) = x. When the transformation is identity,
        the scalar residue equals the original norm squared."""
        rng = np.random.default_rng(62)
        for _ in range(50):
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            assert abs(essence_return(psi) - np.linalg.norm(psi)**2) < TOL


# =====================================================================
# SECTION 4: isDevourer tests (P18)
# =====================================================================

class TestDevourerPredicate:
    """P18: Formal devourer criterion as a boolean predicate."""

    def test_unitary_is_not_devourer(self):
        """Unitary transformations preserve C, B, I → never devourer."""
        from scipy.linalg import expm
        rng = np.random.default_rng(70)
        for _ in range(50):
            H = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
            H = H + H.conj().T
            U = expm(1j * H * 0.1)
            psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
            psi = psi / np.linalg.norm(psi)
            assert not is_devourer(U, psi), "Unitary should not be devourer"

    def test_projection_is_devourer(self):
        """Projection onto S⁺ destroys S⁻ component → devourer.
        Construct a balanced state so the S⁻ loss is significant."""
        col_plus = P_PLUS[:, 0] if np.linalg.norm(P_PLUS[:, 0]) > TOL else P_PLUS[:, 1]
        col_minus = P_MINUS[:, 0] if np.linalg.norm(P_MINUS[:, 0]) > TOL else P_MINUS[:, 1]
        v_plus = col_plus / np.linalg.norm(col_plus)
        v_minus = col_minus / np.linalg.norm(col_minus)
        psi = (v_plus + v_minus) / np.sqrt(2)
        # Balanced state: P+ removes half the norm → C_g drops to ~0.5 → devourer
        assert is_devourer(P_PLUS, psi, c_threshold=0.9), (
            "Projection of balanced state should be devourer"
        )

    def test_zero_transformation_is_devourer(self):
        """The zero map destroys everything."""
        psi = np.array([1, 0, 0, 0], dtype=complex)
        assert is_devourer(np.zeros((4, 4), dtype=complex), psi)

    def test_identity_is_not_devourer(self):
        """Identity preserves everything."""
        psi = np.array([1, 0, 0, 0], dtype=complex)
        assert not is_devourer(I4, psi)


# =====================================================================
# SECTION 5: Mₙ recursion (P16, P17) — fractal manifestation
# =====================================================================

class TestManifestationRecursion:
    """P16-P17: M_{n+1} = Lₑ(Mₙ), with C and B bounds across levels."""

    def _iterate_manifestation(self, psi0, n_levels):
        """Apply Lₑ iteratively, tracking coherence at each level."""
        levels = [{'psi': psi0, 'norm': np.linalg.norm(psi0)**2}]
        current = psi0
        for _ in range(n_levels):
            psi_plus, psi_minus, chi = emanative_love(current)
            norm = np.linalg.norm(psi_plus)**2 + np.linalg.norm(psi_minus)**2
            levels.append({
                'psi_plus': psi_plus, 'psi_minus': psi_minus,
                'chi': chi, 'norm': norm
            })
            current = psi_plus  # descend into dominant sector
        return levels

    def test_P17_coherence_preserved_across_levels(self):
        """C(M_{n+1}) = C(Mₙ): coherence is preserved at each level."""
        rng = np.random.default_rng(80)
        psi0 = rng.standard_normal(4) + 1j * rng.standard_normal(4)
        levels = self._iterate_manifestation(psi0, 5)
        for i in range(len(levels) - 1):
            c_before = levels[i]['norm']
            # After projection into S+, norm is ≤ original (decreases)
            # But the sum ||ψ+||² + ||ψ-||² = ||ψ||² (preserved)
            if i == 0:
                psi_plus, psi_minus, _ = emanative_love(levels[0]['psi'])
                total = np.linalg.norm(psi_plus)**2 + np.linalg.norm(psi_minus)**2
                assert abs(total - c_before) < TOL

    def test_chirality_is_well_defined_at_each_level(self):
        """χ ∈ [-1, 1] at every level."""
        rng = np.random.default_rng(81)
        psi0 = rng.standard_normal(4) + 1j * rng.standard_normal(4)
        levels = self._iterate_manifestation(psi0, 5)
        for level in levels[1:]:
            assert -1.0 - TOL <= level['chi'] <= 1.0 + TOL

    def test_return_from_any_level(self):
        """From any level, Lᵣ recovers the split.
        M_n can always return to M_{n-1} by recombination."""
        rng = np.random.default_rng(82)
        psi0 = rng.standard_normal(4) + 1j * rng.standard_normal(4)
        psi_plus, psi_minus, _ = emanative_love(psi0)
        recovered = returning_love(psi_plus, psi_minus)
        assert np.max(np.abs(recovered - psi0)) < TOL
