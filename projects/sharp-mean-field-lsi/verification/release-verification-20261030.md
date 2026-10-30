# 30 October 2026 scoped release verification

**PASS — fresh current-root and combined public-declaration checks.**

- Code source: [`40f266f117e2ac74b447f5fa7372ba2d0355b327`](https://github.com/matthewrosenzweigwork-max/DGPS-LSI-/tree/40f266f117e2ac74b447f5fa7372ba2d0355b327).
- Separate DGPS evidence commit: [`915524b3d5ba1c89e29b7cba1af09848855a20f6`](https://github.com/matthewrosenzweigwork-max/DGPS-LSI-/commit/915524b3d5ba1c89e29b7cba1af09848855a20f6). This evidence commit does **not** replace the code pin.
- Distributed source/configuration/license files: **2,393**, with successful [exact-identity check](release-20261030/PACKAGE_INTEGRITY.log) against the [source manifest](source-manifest.json).

## Fresh checks

| Check | Exit | Elapsed | Peak RSS |
|---|---:|---:|---:|
| Current `DGPS` root | 0 | 176.670 s | 4,921,164 KiB |
| `CombinedReleaseGate` | 0 | 218.189 s | 3,954,164 KiB |

The [root receipt](release-20261030/receipts/dgps-root-current-v2.json) and [combined receipt](release-20261030/receipts/combined-release-current-v2.json) record exact commands, compiler hashes, limits, unchanged-source checks and output/log hashes. Checks used pinned Lean **v4.35.0-rc3**, `--trust=0`, one thread and the recorded bounded resource policy. The freshly built root object's SHA256 equals the pinned, source-bound prior object: `98e87a6de8cbf61d1bcc6ff4ae39448885d56d73b2f8adbd8fd6f1f164648310`.

The [probe](release-20261030/CombinedReleaseGate.lean) imports `DGPS`, `DGPS.Structural.PositiveRateCriterion` and `DGPS.Structural.T06Comparison`. All **35 selected public type outputs** are present; [per-declaration axiom results](release-20261030/PUBLIC_AXIOM_RESULTS.json) report no axioms outside `propext`, `Classical.choice` and `Quot.sound`. The [inventory](release-20261030/PUBLIC_DECLARATIONS.json) includes stronger and auxiliary exports; 35 is not a count of independent campaign obligations.

## Reused dependencies and resolved infrastructure failures

These are **two fresh module checks**, using a **2,064-module source/object-hash-bound project dependency namespace**, not a fresh rebuild of all 2,064 modules. [Compact provenance](release-20261030/SOURCE_OBJECT_PROVENANCE.json) records the exact identities and origin categories. [Sidecar bindings](release-20261030/SIDECAR_BINDINGS.json) and [256 exposed sidecar links](release-20261030/SIDECAR_LINK_BINDINGS.json) preserve the module-system import boundary. The static [proof-token scan](release-20261030/STATIC_PROOF_TOKEN_SCAN.json) found no `sorry`, `admit`, `axiom` or `sorryAx` tokens in this project closure after removing comments and strings; this scan is not itself proof verification.

Both first-attempt failures remain visible in the original [root v1](release-20261030/receipts/dgps-root-current-v1.json) and [combined v1](release-20261030/receipts/combined-release-current-v1.json) receipts and accompanying logs. Root v1 lacked required module-system sidecars; combined v1 encountered sparse-prefix namespace shadowing. The fixes exposed verified sidecars and [promoted the byte-identical fresh root in the isolated boundary](release-20261030/BOUNDARY_FRESH_ROOT_PROMOTION.json), without modifying production Lean source. These were resolved infrastructure failures, not theorem counterexamples. [Attempt dispositions](release-20261030/ATTEMPT_DISPOSITIONS.json) and [checker-version binding](release-20261030/CHECKER_VERSION_BINDING.json) retain the distinction.

## Scope retained, not enlarged

The [29 October T01 final-root acceptance](https://github.com/matthewrosenzweigwork-max/DGPS-LSI-/blob/40f266f117e2ac74b447f5fa7372ba2d0355b327/Campaign/repair/20261028/checks/T01_FINAL_ROOT_ACCEPTANCE.json) already recorded internal acceptance and the separate reproducible T01 verification. Its status was **applied-pending-review by author**; this cloud release does not manufacture author approval. Current repair and statement qualifications are summarized in the [project README](../README.md) and [verification index](README.md).

The separately selected `DGPS.SingularCounterexample.Main` has a [941-module unchanged project-source closure](release-20261030/SINGULAR_PRESERVATION_BINDING.json), preserving the [historical explicit exit-0 build](clean-build-20261029.md) at 20:22:46 UTC on 29 October. **No fresh cloud singular-entrypoint replay is claimed.** The six auxiliary source modules listed in the project README are distributed with exact hashes but remain outside this combined gate and unclaimed by it. Historical receipts/certificates are preserved for their original snapshots and scopes.

No new whole-repository independent Comparator/Nanoda audit, all-fresh dependency rebuild, blanket optional-module acceptance, author acceptance or manuscript certification is claimed. [The evidence hash manifest](release-20261030/HASH_MANIFEST.json) binds the actual distributed evidence bytes; neutral execution paths in original receipts are retained, while compact derived provenance omits private operational paths and device/account data.
