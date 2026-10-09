# Reading the Ginibre proof library

Start with a mathematical question, then follow one of the routes below. The
public import [FullPaper.lean](GinibrePoincare/Endgame/FullPaper.lean) is the
export surface; its import list is not intended as a first reading order.
These guides explain selected proof dependencies and interfaces inspected in
the source. They are reading aids, not a new correspondence or soundness audit.
[REPORT.md](REPORT.md) records coverage and proof-route qualifications;
[STATUS.md](STATUS.md) records verification evidence.

The guides describe the 2026-10-09 readability interfaces. The
[semantic diff review](verification/readability-semantic-review.md) checked the
changed code and definition bodies; the
[full verification record](verification/readability-final-check.txt) records
build and axiom checks. The [offline declaration explorer](formal-dependencies.html)
includes the named-result shortcuts. A live deployment is tracked separately in
[STATUS.md](STATUS.md).

| Paper result or topic | Reading route |
| --- | --- |
| Theorem 1.1: sharp inequality and all equality cases | [Weak domains, Gaussian geometry and equality](docs/readability/analytic-inequalities.md#theorem-11-sharp-poincaré-and-equality) |
| Theorem 1.2: equilibrium independence and radius law | [Equilibrium coordinates](docs/readability/equilibrium-dynamics-spectrum.md#theorem-12-equilibrium-coordinates) |
| Theorem 1.3: original process, factorization and CIR | [Dynamics and localization](docs/readability/equilibrium-dynamics-spectrum.md#theorem-13-dynamics-and-localization) |
| Theorem 1.4, Corollary 1.5, Remark 1.6 | [Polynomial sector and operator spectrum](docs/readability/equilibrium-dynamics-spectrum.md#theorem-14-and-corollary-15-polynomials-and-spectrum) |
| Lemmas 1.7–1.8: pointwise curvature | [Curvature and capacity](docs/readability/domains-and-foundations.md#pointwise-curvature-and-collision-capacity) |
| Theorems 1.9–1.10: series and differential deficits | [Exact deficits](docs/readability/analytic-inequalities.md#theorems-19-and-110-exact-deficits) |
| Theorem 1.12: radial logarithmic Sobolev | [Radial Gaussian transfer](docs/readability/extensions.md#theorem-112-radial-logarithmic-sobolev) |
| Theorem 1.13: matrix overlaps | [Matrix lift](docs/readability/extensions.md#theorem-113-matrix-lift-and-overlaps) |
| Theorem 1.14: general potentials | [Nonquadratic inequalities](docs/readability/extensions.md#theorem-114-nonquadratic-potentials) |
| Section 2 and Appendix B: entire functions and dbar | [Gaussian and complex foundations](docs/readability/domains-and-foundations.md#gaussian-and-complex-foundations) |
| Appendix A: weak domains and collision removal | [Domains and cores](docs/readability/domains-and-foundations.md#domains-and-cores) |

Problems 1.11, 1.15 and 1.16 are open questions. Appendix C experiments are
outside theorem certification. The numbering here follows the versioned paper;
some older source comments use earlier numbering.

## Translate the interface before reading tactics

`Configuration n` means an indexed complex configuration. A gradient in
`EuclideanSpace ℝ (Fin n × Fin 2)` has two real components for each particle.
`Lp ... 2 μ` is an equivalence class modulo equality almost everywhere, with
its norm already carrying integrability. Coercing it to a function chooses a
representative; therefore identities about representatives often use `=ᵐ[μ]`.
The `.val` in a symmetric value is its underlying L² class.

`hn : 0 < n` is a mathematical dimension hypothesis. `hgraph : (u,v) ∈ L.graph`
means both domain membership and `L u = v`; it is stronger than weak-H¹
membership. Read the first two arguments together before interpreting a
second deficit involving `‖v‖²`. `ContDiff ℝ k` describes real differentiability,
even when the function values are complex. Complex differentiability and
vanishing Wirtinger derivatives appear separately.

An assembly proof often consists of `obtain` followed by `exact`: its purpose
is to combine already proved interfaces. Follow the called theorem to see the
mathematical argument. `simpa only [...]` usually reconciles definitions or
normalizations; `field_simp`, `ring`, and `linarith` close algebra after the
analytic ingredients have been established.

`set_option maxHeartbeats` increases the elaboration budget for a difficult
proof. Options controlling definitional equality affect how Lean searches for
a proof term. They do not add mathematical hypotheses; the resulting term is
still checked by the kernel. Read these lines as implementation settings, then
return to the definitions and theorem statements for the mathematical content.

## Choose an import and a question

For applications, import `GinibrePoincare.Endgame.FullPaper`. For work on one
topic, the thematic [subproject facades](SUBPROJECTS.md) give smaller entry
points. For proof study, use the ordered routes in these guides and inspect the
named declarations, rather than reading the exhaustive file inventory in order.

Before extending a result, check its domain, its speed normalization and whether
it uses real or complex L². Keep public statements explicit about those choices.
For mathematical explanations, document why the next lemma applies and which
hypothesis it consumes; do not merely paraphrase the tactic sequence. Introduce
named structures for packages whose components are reused together, while
preserving the existing theorem interface when compatibility matters.

## Maintain the reading paths

Give a major module a short mathematical outline: what it constructs, the
argument that proves its main result, and the domain on which that argument
works. Explain a limiting or localization step where it occurs in the proof.
For elementary algebra, a descriptive lemma name usually suffices. Name local
facts after their roles, such as a coefficient identity or a graph-norm limit.

Keep reusable foundations in their existing focused modules. The historical
`Full`, `Alternative` and `Correspondence` names remain compatible entry points;
use the named result records when applying their large conclusions. A record
of proved conclusions should be constructed by a theorem, rather than required
as an extra assumption by the paper endpoint.

Run `make readability` to check the conservative punctuation spacing and its
regression cases. To apply that spacing, run
`python3 scripts/format_lean_readability.py --write`, then regenerate the
thematic inventory with `python3 scripts/group_subprojects.py`. The formatter
preserves arithmetic and comparison operators, strings and comments; it skips
files defining syntax. This check does not enforce every aspect of Lean style.
Space dense mathematical operators by hand while preserving compound tokens
such as `=ᵐ[μ]`, `=ᶠ[l]` and `*ᵥ`.

Run `LEAN_NUM_THREADS=1 make check` after changes to Lean sources. Update the
corresponding topic guide when a proof route or domain interface changes, and
refresh source counts with `python3 scripts/count_lean_sources.py`.
