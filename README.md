# Ginibre Poincaré formalization

The 2026-10-09 readability revision adds mathematical reading routes, proof
outlines and named result interfaces for deficits, matrix bounds, CIR
localization and maximal-domain Bochner data. Its full build and public/private
axiom audits pass; [verification evidence](verification/readability-final-check.txt)
and the [independent semantic diff review](verification/readability-semantic-review.md)
record the scope. The mathematical correspondence findings remain the dated
2026-10-08 reviews.

The principal numbered endpoints are compiled and audited, including Theorems 1.9 and 1.10, nonquadratic potentials and matrix-lift/eigenvector-overlap inequalities. The ordinary Gaussian derivative domain, canonical dbar solver, global entire Vandermonde factorization and literal representative distance formulas are complete; see [the numbered report](REPORT.md). Open Problems 1.11, 1.15 and 1.16 remain research questions, and numerical experiments are outside theorem certification. The public entry point is [FullPaper.lean](GinibrePoincare/Endgame/FullPaper.lean).
See [STATUS.md](STATUS.md) for exact domains, the full dashboard and validation.

Compiled result coverage does not certify every original or alternative paper
argument. The four requested independent proof groups now have concrete
endpoints: spectral and Hermite–Slater, integrated Bochner–Kodaira,
strongly convex Bakry–Émery radial LSI, and Gaussian matrix inequalities.
The nonquadratic endgame now uses the primary Euclidean-lift route, with
Brownian existence, Gibbs invariance, regularization and radial tensorization
proved internally. Its independent transport proof remains exported.
See the [proof-route inventory](REPORT.md#independent-proof-routes-and-domain-qualifications)
for domains, proof correspondence and audit evidence. The new correspondence endpoints close the previously identified matrix H¹,
pointwise Γ₂, unrestricted operator/dynamics and auxiliary bridges. Independent
follow-up findings and exact domain qualifications are in
[the correspondence review](CORRESPONDENCE_REVIEW.md). The public registry confirms
[PALOMAR-2026-10-09-000001 v1](https://data.palomar-registry.org/entries/PALOMAR-2026-10-09-000001-v1.json),
registered at `2026-10-09T00:48:41Z` for the submitted Theorem 1.1 snapshot
`fb58b4fd765f19a65c46cb82fb647fb0d94e28ca`. This receipt concerns that immutable
snapshot; the later full-paper/readability revision has separate local verification.
See [registry evidence](verification/registry-publication-check.md).

For mathematical reading, start with [the human reading guide](HUMAN_READABILITY.md).
It gives ordered routes from definitions through the central lemmas to each
numbered theorem, explains weak domains and generator graphs, and distinguishes
the Hermite and differential proof routes.

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
and an [offline copy](formal-dependencies.html). The local 2026-10-09 export
includes the new named interfaces; the live explorer remains the previously
published version until redeployment is confirmed.

The development includes sharp symmetric weak-H¹ Poincaré and exhaustive
affine equality, both literal Theorem 1.9 deficits, differential deficits,
radial log-Sobolev, nonquadratic potentials and matrix H¹ overlap inequalities.
The unrestricted diffusion generator, ordinary weak form, square-root domain,
Brownian semigroup identification, full martingale problem, strong Markov paths,
unstopped independent CIR equations and uniqueness of invariant probability are
proved. The maximal Gaussian number operator has an actual compact smooth core,
full-domain Bochner–Kodaira identity, exact spectrum and literal square roots.
Auxiliary endpoints include real GUE inequalities on the paper's smooth-core H¹
completion, arbitrary positive-local-weight entire-space convergence, local L²
Dolbeault exactness in every dimension, Δlog|z|=2πδ₀, explicit polynomial/Slater
formulas, Gram–Schmidt and quantitative collision cutoff rates. General real
Brascamp–Lieb uses C² positive-definite Hessians and locally Lipschitz or ordinary
local weak-derivative observables with finite inverse-Hessian energy. See the
report for result-specific proof routes and domain extensions.

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

Palomar currently requires Lean ≥ 4.35.0-rc2. The user authorized this upgrade and a deliberate proof hole only in the independent Challenge theorem; the Solution and proof library remain subject to the full soundness policy. The supported-toolchain full build, public/private axiom audits and actual Comparator with all three kernels pass. The dependency manifest is included in the final Git snapshot. The public v1 receipt confirms the submitted immutable snapshot. Publishing a
later source revision is a separate registry update; see [PALOMAR.md](PALOMAR.md).
