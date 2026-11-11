# Verification of the conditional partition bound

The release target and mathematical limitations are specified in [SCOPE.md](SCOPE.md).
The included Lean package comes from log-gas-lean base commit
`c8c7191bf834be29ca3680924a512544ed3523a5`, with an additive explicit-integrability
corollary and release verification tools. The source manifest, rather than the
base commit alone, identifies the distributed package.

`source-manifest.json` binds production Lean sources, project configuration,
scope documents, reference manuscripts and the checking tools. The original
frozen statements are additionally checked against their preserved hashes.
`domain_statements.sha256` records the new statement and corollary.

`verify_release.py` builds all distributed project targets into an initially
empty directory, binds the resulting objects to the source snapshot immediately,
and exports the five target proof closures. The official Comparator checks their
statements and dependencies against a separate challenge and enforces the
three-axiom policy (`propext`, `Classical.choice`, `Quot.sound`). Its kernel
checks include Nanoda and Lean's own kernel. A separate strict Nanoda invocation
also rejects any unlisted axiom present in the selected export. Missing-target,
changed-statement and forbidden-axiom controls must be rejected.

Project builds and exports, and the direct strict Nanoda run, use `bwrap` with
network access disabled and source inputs read-only. The trusted Comparator
frontend parses exports outside that sandbox and launches its kernels using
the official toolchain's sandbox implementation. These checks are not performed
by an independently administered machine or a human reviewer. Pinned dependency
artifacts are reused and are included transitively where the selected proof
exports depend on them; no full dependency-library audit is claimed.

`reviews/` holds separate mathematical-fidelity and verification reviews with
reviewer identities, scopes, qualifications and hashes of reviewed inputs.
AI review is not independent human certification. The author decisions do not
replace either review.

The machine receipt must say `machine_checks_passed`; the review/evidence gate
must separately say `release_checks_passed`. A partial run, missing review,
stale reviewed file, changed source manifest, failed control or missing log is
not a release pass. Run instructions are in [the Lean README](../lean/README.md).

Earlier runs remain historical evidence for their original snapshots. Their
reporting failures are retained alongside corrective receipts. The fresh public
package run is the controlling machine record for this package; neither a source
identity check nor an old receipt is described as a new kernel replay.

Raw exports and full operational receipts are retained in the release evidence
archive separately from this lightweight source distribution. The evidence index
records archive hashes and availability. The source package can be checked again
using the included commands without trusting an assertion of prior acceptance.
