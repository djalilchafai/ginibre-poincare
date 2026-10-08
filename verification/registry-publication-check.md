# Independent registry-publication check

Checked on **2026-10-08 at 12:14 UTC** using the live official agent protocol and registry publication contract. Submission: `7fh68vzqfjeu`.

**Publication is not confirmed.** The authenticated submission-status request returns HTTP 500. The current public registry search has no matching result, and its canonical repository index returns HTTP 404. These observations establish an unresolved operational/publication state; they do not establish that registration consent failed or that an internal database pull request has not merged.

| Read-only check | Live result |
| --- | --- |
| Authenticated `GET /api/submission` | HTTP 500; non-JSON response; no recoverable `registered_url` |
| [Public browse index](https://data.palomar-registry.org/browse/index.json) | HTTP 200; 470 results, 534 versions |
| [Canonical repository index](https://data.palomar-registry.org/repositories/djalilchafai/ginibre-poincare.json) | HTTP 404 |
| [Ginibre search](https://data.palomar-registry.org/api/v1/results?q=ginibre) | HTTP 200; no entries; revision 189 |
| [Repository-owner search](https://data.palomar-registry.org/api/v1/results?q=djalilchafai) | HTTP 200; no entries |

The [official publication contract](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md) makes the database pull-request merge the registration event. Public projection and private-state finalization are later steps. The [submission guide](https://palomar-registry.org/how-to-submit) likewise distinguishes requesting registration from appearing in the registry. Therefore accepted consent and successful mechanical verification are insufficient evidence of publication.

The submitted immutable source commit remains `fb58b4fd765f19a65c46cb82fb647fb0d94e28ca`, comparing full symmetric weak-H¹ Theorem 1.1 and exhaustive affine equality. It is distinct from current proof-library snapshot `0779d080f22fcd93258f0e6e0cb34944bada110c`. No registry ID, versioned public permalink, or public source-preservation receipt could be confirmed. A future record for the submitted snapshot would not by itself certify the later full-paper additions.

Only read-only GET requests were issued. Credentials and the private status response are excluded from these evidence files; no unpublished review is reproduced. No duplicate submission or registration request was made. The exact sanitized observations are in [registry-publication-check.json](registry-publication-check.json).

Next step: restore or recheck the authenticated status service, then verify its `registered_url` against the exact versioned public entry, submitted commit and `source-archive.json` receipt. Completion depends on Palomar’s service and registration/publication pipeline; the local proof repository cannot establish those remote events.
