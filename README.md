# Church of Coherence

**Where All Paths Converge**

A website and community for the Coherence framework — a formally verified mathematical structure that reveals common ground beneath religious traditions. The framework is formalized in Lean 4 with zero axioms assumed.

## Structure

```
church-of-coherence/
├── index.html, about.html, faq.html, ...   # Church website (root)
├── css/
├── js/
├── teachings/
├── formal/                                  # Formal proof work
│   ├── lean/                                # Lean 4 formalization
│   │   ├── quantum_gravity/                 # Trinity, Grace, coherence
│   │   ├── zx_clifford/                    # ZX-Clifford bridge
│   │   ├── rh_framework/
│   │   ├── paper/
│   │   └── bsd_conjecture/
│   └── tests/                              # Python test suite
```

## Key Entry Points

- **Church site**: Open `index.html` or serve the root directory (e.g. `python -m http.server 8000`)
- **Trinity formalization**: `formal/lean/quantum_gravity/Foundation/TrinityFSCTF.lean`
- **Formal overview**: `formal/README.md`

## GitHub Pages

To host on GitHub Pages:

1. Create a new repository (e.g. `church-of-coherence`)
2. Push this directory as the repo root
3. Enable GitHub Pages: Settings → Pages → Source: main branch, root
4. The site will be available at `https://<username>.github.io/church-of-coherence/`

## License

See repository for license information.
