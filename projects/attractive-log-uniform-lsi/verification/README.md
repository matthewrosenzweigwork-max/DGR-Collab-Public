# Verification and package identity

## Accepted artifact

The final acceptance of October 1, 2026 identifies the candidate archive by SHA-256
`00e0d7612ceb1e6f19c184fdd3b87c068e5fae29531cedc72bfe9823db6b88f3`.
The containing final acceptance archive has SHA-256
`448a33968bd07619ad867a76232f12f710fbace43bb72d7c9b8a085db973422a`.

The registered solution manifest contains 407 files: 402 local proof modules, the generated `Solution.lean` entrypoint and `Audit.lean` checks, and the three project configuration files. All 407 are preserved exactly in `../lean/`. Necessary third-party license/provenance notices are additionally included.

The much larger development archive is not copied wholesale. Internal instructions, worker outputs, obsolete evidence and unrelated proof modules are excluded. No proof inside the accepted closure is rewritten.

## Evidence included

- [Accepted release summary](accepted-release-summary.json): selected fields from the original final acceptance, including scope and qualifications; its original report hash is retained. This is not a new audit certificate.
- [Required declarations and axioms](required-targets.json): unchanged protected specification.
- [Solution source manifest](solution-source-manifest.json): exact file hashes from the registered replay's solution manifest.
- [Package check](package-check.json): results of the reproducible hash/import-closure check.

The recorded accepted replays rebuilt candidate and challenge source using pinned official dependency artifacts, and exercised positive and negative controls. They included Comparator, Nanoda and Lean kernel checks. They did not rebuild or independently audit the whole of Mathlib.

## Packaging validation

`python3 verification/check_package.py` verifies all 407 hashes and resolves every local `LeanResearch` import. This is a structural and byte-integrity check, **not a Lean elaboration or kernel replay**. At initial packaging, the environment had no Lean/Elan executable. A subsequent clean compilation is recorded below; it does not replace the prior accepted independent replay. Build commands are provided in the project README for an environment with the pinned toolchain and dependencies.

The generated registered Lake configuration differs from the old broad development configuration by selecting `Solution` and `Audit`. The generated configuration is itself preserved from the accepted replay. The original broad aggregate would import unrelated work and is intentionally not shipped.

## Subsequent clean build

The pinned release-target compilation passed. See [the clean-build record](clean-build-20261029.md). This supplements the earlier packaging checks without broadening their certification scope.
