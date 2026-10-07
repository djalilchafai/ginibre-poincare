# Ginibre Poincaré formalization

## Objective

Fully formalize Theorem 1.9 of [arXiv:2608.19358v2](http://arxiv.org/abs/2608.19358v2), including both
sum-of-squares identities for the concrete Ginibre measure and generator.
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

## Milestones

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
17. Export and audit the exact final theorem.

## Completion criteria

The project is complete only when every milestone above is represented by
unconditional compiled Lean theorems, all local modules build, local source
contains no placeholders except the authorized independent Challenge theorem,
and `AxiomAudit.lean` audits the final theorem.
