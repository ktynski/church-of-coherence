# BSD-QSNV Connection

## Lean 4 Formalization of the BSD Conjecture via Coherence Obstruction

### Maturity: EXPLORATORY

This package explores the connection between the Birch and Swinnerton-Dyer
conjecture and the QSNV null-vector framework. It is **not** a completed
formal proof of BSD. The formalization encodes the structural argument
(coherence obstruction dimension equals algebraic rank) while relying on
deep number-theoretic results as axioms.

### Current Status

| Metric | Count |
|--------|-------|
| **Sorry Statements** | 0 |
| **Remaining Axioms** | 50 |
| **Placeholder definitions** | 19 occurrences across 8 files |

### Axiom Classification

Axioms fall into three tiers:

**Tier 1 -- Deep theorems from number theory (not formalizable without major Mathlib extensions)**

These axioms encode results that are either proved in the literature but
not yet in Mathlib, or are themselves open conjectures:

| Axiom | What it encodes | Status in mathematics |
|-------|----------------|---------------------|
| `modularity_theorem` | Every elliptic curve over Q is modular | Proved (Wiles et al. 1995) |
| `mordell_weil_finitely_generated` | E(Q) is finitely generated | Proved (Mordell 1922, Weil 1928) |
| `hasse_bound` | \|a_p\| <= 2 sqrt(p) | Proved (Hasse 1933) |
| `gross_zagier_formula_ax` | Gross-Zagier formula for Heegner points | Proved (Gross-Zagier 1986) |
| `kolyvagin_rank0_ax` | L(E,1) != 0 implies rank 0 | Proved (Kolyvagin 1990) |
| `gross_zagier_kolyvagin_ax` | ord(L,1)=1 implies rank 1 | Proved (Gross-Zagier + Kolyvagin) |
| `sha_finiteness_conjecture` | Sha(E/Q) is finite | OPEN CONJECTURE |
| `parity_conjecture_ax` | Parity of rank equals root number | Partially proved |

**Tier 2 -- Framework-specific axioms (QSNV/coherence interpretation)**

These axioms encode the novel claim that BSD invariants have Clifford-algebraic
interpretations:

| Axiom | What it claims |
|-------|---------------|
| `obstruction_equals_algebraic_rank_ax` | Coherence obstruction dim = algebraic rank |
| `regulator_coherence_ax` | BSD regulator = obstruction dimension |
| `strong_bsd_ax` | Full BSD leading-coefficient formula |
| `eigenvalue_obstruction_ax` | Grace eigenvalue zero-count = obstruction dim |
| `coherence_to_L` | Coherence assembly recovers L-function |

**Tier 3 -- Structural/trivial axioms**

Axioms that assert `True` as placeholders for properties not yet formalized:

| Count | Examples |
|-------|---------|
| 8 | `period_coherence`, `tamagawa_coherence`, `sha_coherence`, `descent_exact`, `assembly_continuation`, etc. |

### Placeholder Definitions (19 occurrences)

Several definitions return literal constants (`0`, `1`, or `infinity`) instead
of computing actual arithmetic invariants:

| File | Placeholder | What should be computed |
|------|------------|----------------------|
| BSD/StrongBSD.lean | `algebraicRank E` returns 0 | Mordell-Weil rank |
| BSD/StrongBSD.lean | `regulator E` returns 1 | Neron-Tate height pairing determinant |
| BSD/StrongBSD.lean | `tamagawaProduct E` returns 1 | Product of local Tamagawa numbers |
| BSD/StrongBSD.lean | `shaOrder E` returns 1 | Order of Tate-Shafarevich group |
| BSD/StrongBSD.lean | `torsionSquared E` returns 1 | |E(Q)_tors|^2 |
| BSD/StrongBSD.lean | `rootNumber E` placeholder | Functional equation sign |
| MainTheorem/StrongBSD.lean | 4 return-value placeholders | Period, Tamagawa, Sha, torsion |
| Lemma3/ObstructionAlgebraic.lean | `generatorObstruction` returns zero | Cl(3,1) obstruction mode |
| BSD/SpecialCases.lean | Heegner point returns infinity | Actual Heegner point |
| EllipticCurve/Basic.lean | `a_p` uses `Classical.choice` | Point counting mod p |

These placeholders allow the overall theorem structure to typecheck while
deferring concrete arithmetic to future work.

### Honest Assessment

This package demonstrates that **if** the coherence-obstruction interpretation
of BSD invariants is correct (Tier 2 axioms), **then** the BSD conjecture
follows from known results (Tier 1 axioms) plus finiteness of Sha. The
formalization is a structural scaffold, not a self-contained proof.

The corresponding Python verification (`open_problems/4_bsd_qsnv/verify_hasse_qsnv.py`)
checks the Hasse bound and Grace-norm structure numerically for specific curves
and primes. This provides exploratory evidence, not proof.

### Building

```bash
lake build
```

Requires Lean 4 and Mathlib (see `lean-toolchain`).
