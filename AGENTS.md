# Ginibre Poincaré formalization

## Objective

Fully formalize all asserted mathematical results of
[arXiv:2608.19358v2](https://arxiv.org/abs/2608.19358v2), including the numbered
theorems, lemmas, corollaries, mathematical claims in remarks, and Appendices A–B,
on their stated domains and with their stated hypotheses. This includes both
Theorem 1.9 sum-of-squares identities for the concrete Ginibre measure and
generator, the nonquadratic extensions, and the matrix-lift/eigenvector-overlap
results. Problems 1.11, 1.15 and 1.16 are open research questions, and Appendix C
numerical experiments are outside theorem certification; do not claim these solved.
Use the versioned arXiv paper as the authoritative source for every paper
statement, theorem number, normalization and citation; do not use local TeX
as the paper authority.

## Current user-authorized scope

Complete all remaining formalization goals, including nonquadratic potentials
and matrix-lift/eigenvector-overlap results, as explicitly requested on 2026-10-02.
This includes weak-Sobolev domain and equality results, the full diffusion
operator and semigroup, stochastic dynamical factorization, and all paper
extensions. The user explicitly requests agents; assign disjoint files.
Do not mark the broad objective complete at an intermediate analytic milestone.

The Palomar submission's `Challenge.lean`, `Solution.lean`, and `comparator.json`
select full symmetric weak-H¹ Theorem 1.1 and its exhaustive affine equality
classification. This is the current registry comparison surface, not a restriction
of the full proof-library objective or a comparison of every paper endpoint.
Use REPORT.md for numbered coverage and STATUS.md for current verification evidence.

## Soundness requirements

- Do not use `sorry`, `admit`, custom `axiom`, opaque placeholders, or
  inconsistent assumptions in the proof library or `Solution.lean`.
- User-authorized Palomar exception (2026-10-07): deliberate `sorry` is permitted
  only for the independent statement theorem in `Challenge.lean`. Never import
  Challenge into the Solution or proof-library audit closure. The Solution must
  prove the same statement using only the three permitted standard axioms.
- Do not replace concrete analytic claims with hypotheses, certificates, or
  weaker definitions and then describe the original theorem as proved.
- Preserve the paper's normalization exactly.
- Audit every public completion theorem with `#print axioms`.
- The standard axioms reported through Mathlib (`propext`, `Quot.sound`, and
  `Classical.choice`) are permitted.

## Dependency policy

- Use only `.lake/packages/mathlib`.
- User-authorized supported-toolchain migration (2026-10-07): upgrade Lean and
  the existing Mathlib checkout together to Palomar-supported v4.35.0-rc2;
  `lake update` and `lake exe cache get` are allowed as needed for this upgrade.
  Do not run `leanchecker --fresh`.
- Do not create or fetch another Mathlib checkout.
- Keep `LEAN_NUM_THREADS=1` for full builds.
- Prefer `lake env lean FILE` while developing and run `make` at milestones.

## Working rules

- Inspect Mathlib before creating foundational infrastructure.
- Put reusable results in focused, appropriately named modules.
- Parallel agents may edit only explicitly assigned, disjoint files.
- Do not modify another agent's active files.
- Keep `STATUS.md` synchronized with what has actually been proved.
- Whenever a formalized result uses a different proof route from the versioned
  paper, add a result-specific remark in `REPORT.md`: identify the paper route,
  the Lean route, and the relevant modules. Distinguish alternative proofs,
  expanded proofs of cited ingredients, and domain extensions. If the original
  route is also formalized, say so. Do not infer proof fidelity from compilation
  or claim an exhaustive correspondence review without supporting evidence.
- At every termination or checkpoint of a partial goal, include the full-project
  status dashboard in the final response and refresh the dashboard in `STATUS.md`.
  Report verified scope, open work, latest progress, build/audit evidence, and
  the next step. Include Lean line counts without Mathlib and with only the
  transitively imported part of Mathlib. Refresh these using
  `python3 scripts/count_lean_sources.py`; count imported modules once in full
  and state that comments and blank lines are included. Do not invent an
  overall completion percentage.
- A result whose analytic facts remain theorem arguments is a reduction, not
  a completed concrete theorem.

## Core analytic milestones

The following milestones organize the original Theorem 1.9 development. They
are part of the full-paper objective, not an exhaustive list of paper results.

1. Identify the Gaussian product measure with its explicit density.
2. Prove polynomial Gaussian integrability and Ginibre mass validity.
3. Define the concrete weighted `L²` spaces used by the paper.
4. Construct the normalized Vandermonde `L²` isometry.
5. Define univariate complex Hermite polynomials.
6. Construct their multivariate tensor-product basis.
7. Prove orthonormality, density, completeness, and Parseval.
8. Prove Wirtinger lowering relations.
9. Construct Hermite-level projections and their energy decomposition.
10. Identify alternating holomorphic functions via Vandermonde divisibility.
11. Prove holomorphic--antiholomorphic projection geometry.
12. Define the concrete Ginibre generator and its core/domain.
13. Prove generator/Dirichlet integration by parts and intertwining.
14. Prove the concrete Poincaré deficit identity.
15. Prove the concrete integrated `Γ₂` deficit identity.
16. Complete the required closure and approximation arguments.
17. Export and audit the exact Theorem 1.9 endpoint.

The wider scope also requires the sharp inequality and equality classification,
equilibrium and stochastic factorization, polynomial spectrum and curvature,
ordinary differential deficits, weak-domain/core results, radial log-Sobolev
inequalities, full diffusion and semigroup identification, matrix-overlap
inequalities, nonquadratic extensions, and the remaining asserted Section 2
and Appendix A–B claims. Preserve their individual domains and qualifications.

## Completion criteria

The proof-library objective is complete only when the core milestones and every
asserted result in the full-paper scope have compiled concrete Lean endpoints on
the paper's stated domains, with analytic completion inputs proved internally;
all local modules build; local source contains no placeholders except the
authorized independent Challenge theorem; and `AxiomAudit.lean` audits every
public completion endpoint. `AllLocalAxiomAudit.lean` must also cover private
helpers in the proof-library/Solution closure. REPORT.md and STATUS.md must
accurately identify coverage, restrictions and evidence.

Palomar mechanical verification, editorial review and final registration are
separate publication stages. A Comparator pass for Theorem 1.1 does not establish
full-paper statement correspondence or complete these publication stages.
