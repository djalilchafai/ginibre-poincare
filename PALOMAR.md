# Palomar submission and verification

This is the substantive proof repository, licensed under the existing MIT
[LICENSE](LICENSE). Its mathematical source is
[arXiv:2608.19358v2](https://arxiv.org/abs/2608.19358v2).
The theorem-numbered inventory is in [REPORT.md](REPORT.md).
Structured provenance, AI use, review status, classifications, and known scope
qualifications are in [formalization.yaml](formalization.yaml).

Requirements were checked against the live
[submission guide](https://palomar-registry.org/how-to-submit), the
[metadata standard](https://github.com/mathlib-initiative/formalization.yaml), and
[mechanical policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
These requirements can change; recheck them before submitting an immutable snapshot.

## Submission report — 2026-10-07

Palomar accepted submission **`7fh68vzqfjeu`**. Its current API status is
`verifying`; official mechanical verification is running. Editorial review
and final registration remain pending.

| Submission field | Recorded value |
| --- | --- |
| Public repository | [djalilchafai/ginibre-poincare](https://github.com/djalilchafai/ginibre-poincare) |
| Immutable submitted commit | [`fb58b4fd765f19a65c46cb82fb647fb0d94e28ca`](https://github.com/djalilchafai/ginibre-poincare/tree/fb58b4fd765f19a65c46cb82fb647fb0d94e28ca) |
| Comparator configuration | `comparator.json` at the repository root |
| Compared statement | Full symmetric weak-H¹ Theorem 1.1 and exhaustive affine equality classification |
| Authorization | User-confirmed responsible maintainer of the substantive formalization |
| Required full mechanical preflight | [Passed](https://github.com/djalilchafai/ginibre-poincare/actions/runs/37679215651), with no errors or warnings; [committed report](palomar-preflight-report.json) |
| Official verification | [Palomar Actions run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/37681934359) — in progress |
| Ownership proof | Agent tag-and-secret-gist protocol; both temporary artifacts deleted after verification |
| Registration | Not requested or completed; requires the user's separate decision after reading the review |

This submission compares Theorem 1.1 and its equality classification. The wider
project coverage is documented in [REPORT.md](REPORT.md) and [STATUS.md](STATUS.md).
Later documentation commits do not change the immutable submitted snapshot.

The private status-page URL and access token are kept outside the repository.
They are omitted from this public report, as is any unpublished editorial review.

| Full-project dashboard | Current evidence / next work |
| --- | --- |
| Verified scope | Recorded builds and axiom audits cover the asserted paper results on the domains in STATUS.md; the official full preflight passed for the submitted snapshot |
| Open work | Palomar verification, editorial review and registration; Problems 1.11, 1.15 and 1.16 remain paper research questions, and Appendix C numerical experiments are not certified |
| Latest progress | Submission accepted, ownership proofs removed, public submission report recorded |
| Lean source counts | 142,364 project lines in 1,315 files; 1,251,826 transitively imported Mathlib lines in 3,794 modules; combined 1,394,190 lines |
| Next step | Read the verification outcome and editorial review, show the review to the user, then obtain their separate instruction before registration |

Source counts are refreshed with `python3 scripts/count_lean_sources.py`.
Comments and blank lines are included; imported Mathlib modules are counted
once in full. No Lean proof changes or new local full build were needed for
this documentation update.

## Completed upgrade and local verification

`Challenge.lean`, `Solution.lean`, and `comparator.json` prepare a comparison
of **the full symmetric weak-H¹ Theorem 1.1 and exhaustive affine equality
classification**, with constant `1/(2n)` and independently spelled-out concrete
Ginibre definitions. They do not compare the entire paper. The Solution supplies
the proved theorem. On 2026-10-07 the user authorized the deliberate statement-only
`sorry` in the independent Challenge and the supported Lean/Mathlib upgrade.
The exception does not permit proof holes in the library or Solution.

The completed migration pins `leanprover/lean4:v4.35.0-rc2` and matching Mathlib
commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` in the existing checkout.
This meets the current [Palomar minimum toolchain policy](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json).
The final full build passes 5,384 jobs. Both public/private axiom audits and root
compatibility checks pass; offline preflight reports zero blockers and the
metadata validates against the official v0.4 schema. Actual Comparator succeeds
with con-ron, nanoda and Lean’s default kernel. See the committed
[Comparator evidence](ginibre-upgrade-comparator.log) and [full check evidence](ginibre-upgrade-verified-check.log).

`definition_names` is intentionally empty: no concrete definition is treated as
a definition hole. The theorem explicitly spells out the ordinary distributional
weak-gradient predicate and normalized energy, avoiding generated auxiliary proof
names while preserving the exact mathematical statement. Concrete definitions
remaining in its closure are recursively compared. Challenge is 173 lines / 9,781
bytes; Solution is 87 lines / 3,892 bytes.

On this host `/home` is a symlink and the existing dependency store is outside the
project. The optional [sandbox mount wrapper](scripts/canonical_home_bwrap.py)
canonicalizes mount path operands, still hides the canonical home, and grants
read-only access only to that existing dependency store. Isolation and network
flags are preserved. Hosts with an ordinary `/home` use Comparator’s default
sandbox; an explicit `COMPARATOR_BWRAP` override is respected.

Palomar also requires `module` headers throughout the submitted repository,
including unused regular Lean sources outside `.git` and `.lake`. Porting must
preserve public declarations, imports, and exposed definition bodies, and then
rebuild. Adding a token header without checking module visibility does not establish
compatibility. The source tree has now been ported to `module` headers, public
imports, and exposed public sections; the v4.35.0-rc2 full build and both public/private axiom audits pass.
The refreshed project dashboard records the evidence. The manifest is now
included by Git's ignore rules and must be committed in the selected snapshot.
Every such file has a 10,000-physical-line cap; Lean symlinks are
refused. `lakefile.lean` is exempt only from the header requirement.

The independent Challenge must import only Lean core and the allowlisted pinned
Mathlib/Tau Ceti closure. A Challenge that imports this project's proof modules
would violate that rule. Its content must make the concrete Ginibre measure,
operator, hypotheses, and identities independently readable. Deliberate Challenge
proof holes are permitted by Palomar and now authorized by the user exclusively
for the independent Challenge theorem. A proved Solution and Comparator run
must establish identical compared declaration names and types, with only the three
standard axioms. Packaging files alone are not evidence of Comparator success.

## Required snapshot checks

- Keep exactly one Lake configuration, a pinned `lean-toolchain`, and the committed
  `lake-manifest.json`. Keep one conventional licence file at the repository root.
- Provide a short independent Challenge, proved Solution, and Comparator JSON
  naming the compared theorem; retain empty `definition_names` so concrete
  definitions are recursively checked. Challenge hard limits are 1,000
  lines and 100 KiB; the preferred review size is 300 lines and 32 KiB.
- Check every regular Lean source for the module header and line limit; rebuild all
  modules on the supported toolchain and run Comparator and the axiom audits.
- Validate `formalization.yaml` against its versioned schema and the current
  Palomar metadata rules. Confirm the responsible human attribution and complete
  any independent mathematical review before claiming such review.
- Select a public GitHub repository and push all intended files. Record its exact
  full 40-character commit SHA; uncommitted or unpushed changes are excluded.
  If this Lake project remains nested, supply its repository-relative path.
- Submit as a responsible maintainer or with that maintainer's approval. Actual
  submission, authentication, and registration are separate publication actions.

For reproducible validation of this snapshot, retain the project's existing
single-thread full check (`LEAN_NUM_THREADS=1 make check`), compatibility checks,
and source counts. Run the actual Comparator against `comparator.json` using the
version prescribed by Palomar. Do not describe a local configuration shape check
as a Comparator proof verification.

`python3 scripts/check_palomar.py` performs an offline structural preflight and
reports any remaining toolchain, source, or configuration blockers. The
`--structure-only` option skips the supported-toolchain gate, while retaining the
Challenge theorem declaration check. Neither mode runs Lean or Comparator, validates the
remote submission snapshot, or checks the live policy for updates.

`make palomar-structure` runs that structural preflight. Once its blockers are
resolved, `make palomar` invokes `scripts/verify_palomar.py`, which uses the
toolchain's actual `lake comparator` with the `nanoda` and `con-ron` independent
kernels. It fetches no cache and updates no dependency. The Lake default targets
now include the library, Challenge, and Solution; the all-local audit imports
each library module and the Solution so private proof bodies remain audited.

The Challenge and Solution must remain within the recorded source caps. The
metadata passes the official v0.4 JSON schema. See [STATUS.md](STATUS.md) for the
latest complete build/audit evidence and fresh source counts; a pre-migration log
is not evidence that the supported-toolchain checks pass.

## Fresh Git snapshot

Git was reinitialized on `main` at the user’s request, with one initial commit
containing the final source, reports, dependency manifest and verification logs.
The old Git metadata is preserved at
`/tmp/ginibre-git-before-reinit-2026-10-07/repository.git`.
The project is public at https://github.com/djalilchafai/ginibre-poincare.
GitHub authentication and publication succeeded. The pinned official full
mechanical preflight is configured in `.github/workflows/palomar-preflight.yml`;
the full report passed and agent intake accepted submission `7fh68vzqfjeu`.
Registration remains pending official verification, review and the user's
separate decision after reading that review.
