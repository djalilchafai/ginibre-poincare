# Ginibre Poincaré formalization

The principal numbered endpoints are compiled and audited, including Theorems 1.9 and 1.10, nonquadratic potentials and matrix-lift/eigenvector-overlap inequalities. The ordinary Gaussian derivative domain, canonical dbar solver, global entire Vandermonde factorization and literal representative distance formulas are complete; see [the numbered report](REPORT.md). Open Problems 1.11, 1.15 and 1.16 remain research questions, and numerical experiments are outside theorem certification. The public entry point is [FullPaper.lean](GinibrePoincare/Endgame/FullPaper.lean).
See [STATUS.md](STATUS.md) for exact domains, the full dashboard and validation.

Compiled result coverage does not certify every original or alternative paper
argument. The four requested independent proof groups now have concrete
endpoints: spectral and Hermite–Slater, integrated Bochner–Kodaira,
strongly convex Bakry–Émery radial LSI, and Gaussian matrix inequalities.
The nonquadratic endgame now uses the primary Euclidean-lift route, with
Brownian existence, Gibbs invariance, regularization and radial tensorization
proved internally. Its independent transport proof remains exported.
See the [proof-route inventory](REPORT.md#independent-proof-routes-and-remaining-gaps)
for domains, proof correspondence and audit evidence. Independent agents have now reviewed the paper correspondence and found unresolved
domain bridges and auxiliary assertions. Full-paper completion is not established;
see [the review findings](CORRESPONDENCE_REVIEW.md). Registry publication is not
confirmed by the [live checks](verification/registry-publication-check.md).

The library is grouped into 12 thematic [subprojects](SUBPROJECTS.md), including
complex Gaussian/Hermite analysis, Gaussian LSI, stochastic calculus, stochastic
dynamics, matrix lifts and nonquadratic potentials. Each has a Lean import entry
point; the [machine-readable inventory](subprojects.json) assigns every original
library module to one group. Existing module paths remain available.
The [dependency diagrams](DEPENDENCIES.md) show each subproject in a box with
arrows from its direct dependencies; SVG graphics display without Mermaid support,
and expandable Mermaid sources are included. Regenerate them with the inventory
using `python3 scripts/group_subprojects.py` (requires Graphviz `dot`).
The [formal Lean dependency graph](FORMAL_DEPENDENCIES.md) additionally extracts
constant references from compiled theorem statements and proof/definition bodies,
with static SVGs, a [live interactive explorer](https://djalilchafai.github.io/ginibre-poincare/formal_dependencies.html),
and an [offline copy](formal-dependencies.html).

The development proves full weak-domain sharp Poincaré and equality
classification (Theorem 1.1), both Theorem 1.9 deficits, radial log-Sobolev,
the full symmetric diffusion,
and its identification with the original singular Brownian SDE. It includes
independent center/relative processes, stopped two-driver CIR realizations, Ginibre invariance,
whole-path stationarity and reversal. Nonquadratic inequalities and actual
Gaussian matrix spectral laws and finite-overlap inequalities have compiled
endpoints; the literal matrix H¹ domain bridge remains unresolved. Appendix formulas, curvature, capacity, linear statistics and
explicit incompleteness/counterexample claims are included. Literal integrated
pointwise Γ₂, unrestricted operator/dynamics assertions, GUE contextual claims
and several explicit polynomial/Slater calculations remain unresolved in the review.

All library modules are publicly imported. Source and axiom audits reject proof
placeholders and nonstandard axioms, including in private helper declarations.

```sh
LEAN_NUM_THREADS=1 make check   # build, source coverage, public and all-local axiom audits
lake env lean TestImport.lean
make drafts                    # compatibility extension-module build
python3 scripts/count_lean_sources.py
python3 scripts/group_subprojects.py --check
```

The completed user-authorized migration pins Lean and matching Mathlib v4.35.0-rc2,
using only the existing `.lake/packages/mathlib` checkout. Dependency updates
and cache retrieval are permitted for this upgrade. The authoritative paper source
and reference is [arXiv:2608.19358v2](http://arxiv.org/abs/2608.19358v2). Use that version
for statements, numbering and normalization; local TeX is not the paper authority. The historical reports in `archive/` and older checkpoints are superseded
by the current status dashboard. Source counts include comments and blank lines
and count transitively imported Mathlib modules once in full.

## Palomar submission preparation

See [PALOMAR.md](PALOMAR.md) and [formalization.yaml](formalization.yaml) for registry packaging, provenance, and verified local readiness. The independent [Challenge](Challenge.lean) and proved [Solution](Solution.lean) target the full symmetric weak-H¹ inequality and exhaustive affine equality classification of Theorem 1.1 only; this Comparator configuration does not certify every result in the full-paper report.

```sh
make palomar-structure  # offline layout, source, metadata and configuration checks
make palomar            # readiness checks, then actual Comparator with independent kernels
```

Palomar currently requires Lean ≥ 4.35.0-rc2. The user authorized this upgrade and a deliberate proof hole only in the independent Challenge theorem; the Solution and proof library remain subject to the full soundness policy. The supported-toolchain full build, public/private axiom audits and actual Comparator with all three kernels pass. The dependency manifest is included in the final Git snapshot. Registry publication is a separate step.
