# Lean–Python Bridge: Grace, B, C, I

This document records the alignment between the Lean formalization and the Python test suite for the FSCTF functionals.

## Grace (Lean)

**Location**: `submission/lean/zx_clifford/Semantics/Generators.lean`

```lean
noncomputable def grace (u : Cl31) : Cl31 :=
  ⟨u.scalar,
   fun i => u.vector i / φ,
   fun i => u.bivector i / (φ * φ),
   fun i => u.trivector i / (φ * φ * φ),
   u.pseudoscalar / (φ * φ * φ * φ)⟩
```

- **Semantics**: φ-weighted grade contraction. Grade k is scaled by 1/φ^k.
- **E6 (Grace recoverability)**: Lawful transformations are recoverable. Unitary = invertible = Grace-recoverable.

## B, C, I (Python)

**Location**: `submission/tests/test_bridge_integrity.py`

| Functional | Definition | Lean analogue |
|------------|------------|---------------|
| **B** (Bridge) | Chirality preservation: B(T) = 1 − cross-sector leakage | E7 devourer criterion; P13 bridge metric |
| **C** (Coherence) | C_g = \|\|ψ\|\|²; C_l = bilateral balance | Coherence preservation under unitary |
| **I** (Identity) | I(ψ,T) = \|<ψ\|T\|ψ>\|² | Identity persistence; "what survives" |
| **K** (Integration) | K(ψ) = C_g(ψ) | PrematureClosure ⟺ K < threshold |
| **O** (Openness) | O(ψ) = C_l(ψ) | Openness to further integration |
| **F** (Finalization) | F(ψ) = 1 − O(ψ) | Premature finalization pressure |

## Bridge Assertion

**Grace-recoverable** (Lean E6) ↔ **Unitary** (Python) ↔ **Preserves B, C, I**

- Unitary T: T†T = I ⇒ T is invertible ⇒ recoverable (Grace).
- Unitary T preserves \|\|Tψ\|\| = \|\|ψ\|\| ⇒ C_g preserved.
- Even elements (rotors) have B=1; odd elements (crossings) are invertible ⇒ B and I behave as specified.
- Non-unitary T can reduce C_g, reduce B, and make I unrecoverable ⇒ devourer signature.

## Verification

The following tests enforce the bridge:

1. **test_bridge_integrity.py::TestGraceAsUnitarity**: Unitary = reversible (Grace); non-unitary = can be irreversible.
2. **test_bridge_integrity.py::TestDevourerCriterion**: Sacred (unitary) vs devourer (non-unitary) classification using B, C, I.
3. **test_phi_emergence.py::test_grace_grade_ratio_is_phi**: Lean Grace grade scaling uses φ; ratio between consecutive grades = φ.

## Faith Operator

**Location**: `submission/tests/test_faith_operator.py`

From `finalanswernotes.md` §§7–11. Four sub-operators:

| Sub-operator | Symbol | Definition |
|-------------|--------|------------|
| Resonance detector | R_t | Fraction of recent steps with improving signal |
| Attractor sketcher | A_t | Average coherence gradient (direction) |
| Persistence stabilizer | P_t | exp(-age / half_life) |
| Epistemic auditor | E_t | tanh(speculation_debt) |

**Faith magnitude**: F = λ · max(R_t · P_t − E_t, 0)

**Dual-channel resonance**: Faith detects BOTH coherence improvement AND distortion decrease — enabling it to fire *before* coherence visibly improves (anticipatory property).

**Key tested claim**: From a deep devourer state (D=2.5, R=0.1, F=0.9), faith-augmented Grace reaches C > 0.3 faster than plain Grace, achieves higher final coherence, and produces smoother distortion reduction than random jitter.

## Open Items

- **Grace operator in Python**: `scripts/prove_grace_algebra_axioms.py` uses a different basis (gamma matrices) and scale convention. The grade scaling 1/φ^k matches conceptually; coefficient layout differs.
- **Lean graceSemantics**: `Grace/Simplification.lean` axioms `graceSemantics : ZXDiagram → (QubitSpace → QubitSpace)`. The connection to diagram semantics is not yet tested in Python.
- **True φ emergence**: Does a Clifford process produce φ without putting it in? Status: OPEN (documented in `test_phi_emergence.py`).
