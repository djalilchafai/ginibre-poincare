# Full-paper correspondence review — 2026-10-08

## Readability revision — 2026-10-09

The [independent semantic diff review](verification/readability-semantic-review.md)
inspected the readability changes, including definition bodies, and found no
changed mathematical meaning. The [fresh mechanical verification](verification/readability-final-check.txt)
passes 5,814 build jobs, 6,920 public axiom queries and the all-local audit of
14,592 declarations. The refreshed compiled export and local diagrams include
the named interfaces. These checks do not constitute a new paper correspondence
review; the independent mathematical findings below retain their 2026-10-08 dates
and inspected snapshots. The public registry now confirms
[PALOMAR-2026-10-09-000001 v1](https://data.palomar-registry.org/entries/PALOMAR-2026-10-09-000001-v1.json),
registered at `2026-10-09T00:48:41Z` for source snapshot
`fb58b4fd765f19a65c46cb82fb647fb0d94e28ca`. This is the historical Theorem 1.1
submission, distinct from publication of the later full-paper/readability
revision. [The registry record](verification/registry-publication-check.md)
retains the receipt and dated earlier observations.

## Independent mathematical follow-up — 2026-10-08: reviewed inventory resolved

New concrete proofs resolve the historical matrix H¹, literal integrated pointwise Γ₂, unrestricted operator/form, global CIR, invariant-law uniqueness, GUE and Section 6 spectral-calculus findings. The [independent extension/dynamics follow-up](verification/correspondence-extensions-followup.md) gives an affirmative verdict for its assigned partition after inspecting the final operator additions. The [independent main follow-up](verification/correspondence-main-followup.md) gives an affirmative verdict for its assigned main/auxiliary/Appendix A–B inventory, including the final classical locally Lipschitz Brascamp–Lieb domain and genuine ordinary weak-gradient extension. Neither independent reviewer identified a remaining concrete mathematical conclusion gap in the assigned inventories. These are independent agent source-correspondence findings, not human certification, proof-route fidelity inferred from compilation, or a registry receipt. The final single-thread `make check` passed 5,814 build jobs, 6,865 public axiom queries and the all-local audit of 14,499 declarations, using only `propext`, `Classical.choice` and `Quot.sound`. Source audit covers all 1,719 library modules and seven root files; the only authorized proof hole is the independent Challenge, excluded from the proof audit closure. Focused `TestImport` and offline Palomar structural preflight passed; the latter scanned 1,727 Lean files with zero blockers. These mechanical results remain distinct from independent statement correspondence.

Domains remain explicit: GUE uses the actual smooth compact symmetric ordinary-gradient H¹ completion, with a separately proved C¹ endpoint; local Dolbeault covers ordinary locally-L² distributional coefficients, not arbitrary currents. The classical real Brascamp–Lieb statement uses an actual C² potential with everywhere positive Hessian and integrable Gibbs density, locally Lipschitz L² tests and finite actual inverse-Hessian derivative energy. No uniform curvature bound, global Lipschitz assumption or global ordinary-gradient L² assumption replaces those hypotheses. The separately proved ordinary distributional weak-gradient statement is a domain extension. The paper’s cited physical application descriptions do not specify additional Hamiltonian/vortex-model theorem statements, and no such external model theorem is claimed.

At the 2026-10-08 checkpoint, registry publication was unconfirmed. The public GET at **2026-10-08 16:11:40 UTC** returned HTTP 200 with no Ginibre entries (revision 190; 471 results, 383 projects), and the canonical repository record returned HTTP 404. An earlier authenticated status GET at `2026-10-08T12:42:55Z` returned HTTP 403; no cause is inferred. Accepted registration consent is not a public receipt. See [live evidence](verification/registry-publication-check.md).

## Historical verification and generated evidence — 2026-10-08

The 2026-10-08 compiled declaration export contains 14,499 local declarations, 12,546 theorems, 1,721 compiled local modules, 9,091 external boundary declarations and 1,240,777 direct reference pairs. Its SHA-256 is `907a3a29fcc34eee823a55d2f0c284b6f0ab486ab02ea22e95dd167bdede4aa9`. The source import graph has 1,726 nodes and 6,442 edges. The regenerated views include 27 endpoint SVGs and twelve thematic SVGs; all ten requested compiled route-independence checks pass from this export.

Source counts at the 2026-10-08 checkpoint: **185,400 project Lean lines in 1,727 files**, plus **1,256,051 transitively imported Mathlib lines in 3,813 modules**, totaling **1,441,451 lines in 5,540 files/modules**. Comments and blank lines are included; each imported Mathlib module is counted once in full. See [STATUS.md](STATUS.md) for the complete dashboard and verification evidence. Problems 1.11, 1.15 and 1.16 remain open; Appendix C is outside theorem certification. At this historical checkpoint the remaining external publication step was confirmation of the exact versioned public registry entry and source-preservation receipt; consult STATUS.md and the registry record for subsequent observations.

## Historical initial review (superseded by the follow-up above)

The following records the original `0779d08` review. Its unresolved table is historical; current classifications come from the follow-up reports above.

**Outcome: full-paper correspondence is not confirmed. Registry publication is not confirmed.** The review corrects earlier broad completion claims; it does not invalidate the compiled proofs of their actual Lean statements.

The mathematical source is [arXiv:2608.19358v2](https://arxiv.org/html/2608.19358v2). The reviewed proof snapshot is [`0779d080f22fcd93258f0e6e0cb34944bada110c`](https://github.com/djalilchafai/ginibre-poincare/tree/0779d080f22fcd93258f0e6e0cb34944bada110c). Reviewers read the versioned paper and actual Lean declarations/definitions, using the previous inventory as a locator rather than accepting its coverage claims. Two fresh agents separately reviewed the main and extension sections; a third independently checked live registry status. The integrating agent inspected dynamics/operator scope. These are independent agent reviews, not independent human mathematical certification. The scoped inventories retain unreviewed assertions and must not be represented as an exhaustive successful pass.

| Evidence | Scope |
| --- | --- |
| [Independent main review](verification/correspondence-main.md) | Main inequality, introductory/contextual claims, Sections 2–4 and Appendices A–B; item-specific matches, representations and unreviewed assertions |
| [Independent extension review](verification/correspondence-extensions.md) | Deficits, polynomial/curvature claims, radial/matrix/nonquadratic inequalities and Sections 5–7 |
| [Dynamics/operator inspection](verification/correspondence-dynamics.md) | Section 1.5, stochastic factorization and unrestricted versus symmetric analytic operator scope |
| [Independent live registry check](verification/registry-publication-check.md) / [JSON](verification/registry-publication-check.json) | Read-only authenticated status and public registry observations; sanitized, no credentials or private review reproduced |

The inspected main inequality, its weak-domain equality classification, many numbered analytic endpoints and deficit coefficients have corresponding compiled statements. The four requested alternative proof groups remain compiled and dependency-audited. Kernel/source audits establish soundness of those formal statements; they do not establish that their domains and conclusions cover every assertion in the paper.

| Historical unresolved correspondence | Required step at the original snapshot (now resolved in follow-ups) |
| --- | --- |
| Theorem 1.13 literal matrix H¹ domain | Prove or locate the identification of closed Gaussian gradient with the pointwise spectral-lift derivative from the paper's H¹ hypotheses. Existing literal H¹ exports require an additional identification hypothesis; finite-overlap exports instead prove membership internally. |
| Integrated pointwise Γ₂ identity (1.39) | Connect the concrete pointwise Γ₂ integral to the squared generator norm. Pointwise Bochner formulas and operator-norm deficits alone do not provide this literal bridge. |
| Unrestricted analytic generator/form in Section 1.5 | Identify full complex L² operator/form, Friedrichs extension and unrestricted polynomial domain. Existing analytic “full” generator is on symmetric L²; unrestricted stochastic semigroup existence does not itself complete the bridge. |
| Dynamics assertions | Trace invariant-probability uniqueness, regular/strongly local/Hunt/martingale-problem package and unrestricted CIR equations. The inspected two-driver theorem states stopped equations. These are unconfirmed, not proven absent. |
| GUE contextual assertions in Section 1.2 | Supply exact chamber/log-concavity/Poincaré/LSI endpoints or acknowledge them as uncovered asserted mathematics. |
| Explicit polynomial and Slater calculations | Match the holomorphic quadratic nonpreservation calculation, the final three low-degree polynomial identifications, the exceptional lowest orbital tuple and normalized ground-state determinant. |
| Remaining auxiliary/contextual assertions | Resolve the main review's explicit inventory, including equality-vector analyticity, arbitrary-weight closedness, literal spectral measures, Gram–Schmidt/leading coefficients and collision approximation rates. |

Each scoped report is the source of precise classifications and evidence. An unresolved search result is not proof that no local theorem exists. The work required is to establish the missing correspondence through actual theorem statements and their definitions, or to add internally proved endpoints, then repeat review. Problems 1.11, 1.15 and 1.16 remain open research questions; Appendix C remains outside theorem certification.

Palomar submission `7fh68vzqfjeu` targets only full symmetric weak-H¹ Theorem 1.1 and affine equality at immutable commit `fb58b4fd765f19a65c46cb82fb647fb0d94e28ca`. Historical mechanical verification, clean editorial readiness and accepted registration consent do not certify later full-paper additions or prove publication. Live checks on **2026-10-08 12:14 UTC** returned authenticated HTTP 500, public canonical repository HTTP 404, and empty successful searches. The public index was available. No versioned permalink, registry identifier or source-preservation receipt was confirmed. Completion requires remote service recovery and matching public evidence; no duplicate submission or registration was issued.

No Lean proofs changed during this review. Retained complete verification: 5,508 build jobs; 5,753 public axiom queries; 12,287 all-local declarations; only `propext`, `Classical.choice` and `Quot.sound`. See [proof checkpoint](verification/alternative-proof-check.txt) and [route dependency audit](verification/alternative-route-independence.txt). Source counts are refreshed in [STATUS.md](STATUS.md) and [lean-source-counts.json](lean-source-counts.json); comments and blank lines are included, each transitively imported Mathlib module counted once in full.
