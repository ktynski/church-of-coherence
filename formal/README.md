# Formal Proof Work

This directory contains the Lean 4 formalization and Python tests for the Coherence framework.

## Lean Projects

| Project | Path | Description |
|---------|------|-------------|
| **Quantum Gravity** | `lean/quantum_gravity/` | Trinity (Father/Son/Spirit), Grace operator, coherence witness. Start with `Foundation/TrinityFSCTF.lean`. |
| **ZX-Clifford** | `lean/zx_clifford/` | ZX-calculus and Clifford algebra bridge. |
| **RH Framework** | `lean/rh_framework/` | Riemann hypothesis–related structures. |
| **Paper** | `lean/paper/` | Supporting formalization for the paper. |
| **BSD Conjecture** | `lean/bsd_conjecture/` | BSD conjecture formalization. |

## Building

Each Lean project has its own `lakefile.lean`. From a project directory:

```bash
cd lean/quantum_gravity
lake build
```

The `zx_clifford` project has dependencies; `lake build` will fetch them.

## Python Tests

The `tests/` directory contains a Python test suite that validates properties aligned with the Lean formalization. Run with:

```bash
cd tests
pytest
```

## Entry Point

The canonical entry point for the Coherence Trinity is:

**`lean/quantum_gravity/Foundation/TrinityFSCTF.lean`**

This file formalizes the Father (closure law), Son (Grace operator), and Spirit (coherence witness) with zero axioms assumed.
