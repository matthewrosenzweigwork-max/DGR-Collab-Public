# Conditional partition bound: Lean package

Public target: `LogGasPaper.main_with_domain` in `PaperDomainSolution.lean`.
Read [the exact scope](../verification/SCOPE.md), including the assumed
log-HLS inequality and explicit integrability requirement.

Lean is pinned to `v4.36.0-rc1`; Mathlib to
`625d8914199bc567cca9b91f90e8e5afafa5ae51`. Keep `lake-manifest.json` unchanged.

```sh
lake exe cache get
lake build LogGas Challenge Solution PaperChallenge PaperSolution PaperDomainChallenge PaperDomainSolution VerificationAudit
```

For the full machine gate on Linux with `bwrap` and the pinned toolchain:

```sh
python3 ../verification/verify_release.py --output /tmp/loggas-release-check-UNIQUE
```

The output directory must not exist. The gate uses a fresh project build directory,
two CPU cores, pinned dependency artifacts, the official Comparator, and bundled
Nanoda. It records source/object identities immediately after building and checks
them again after replay. Dependency artifacts are reused; no whole-Mathlib rebuild
or independent system administration is claimed. The challenge's intentional
proof holes exist only in generated checking scaffolds, not production proofs.

Source checks and validation of saved reviews/evidence:

```sh
python3 ../verification/check_package.py
python3 ../verification/check_release.py --evidence /path/to/recorded-run
```

The second command validates recorded evidence; it does not execute a new replay.
Two distinct source-bound reviews are required for its release-check result.
AI reviews are labeled as AI reviews. Publication approval remains separate.
