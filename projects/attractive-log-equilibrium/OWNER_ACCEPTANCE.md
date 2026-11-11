# Owner acceptance guide: conditional log-gas partition bound

This contribution adds the checked log-gas Lean package to this DGR project.
It is submitted for the repository owner's review and merge; submission does
not assert owner approval or human mathematical certification.

## What you are accepting

The main added theorem is `LogGasPaper.main_with_domain`. It gives the uniform
partition bound conditional on the stated log-HLS inequality **and explicit
absolute integrability of its energy integrand**. These are hypotheses, not
results proved by this contribution. The Fourier-normalized kernel's existence
is also proved. Read [the exact scope](verification/SCOPE.md) before accepting.

This is not a formalization of the complete manuscript, Parts I and II, threshold
identification, determinant asymptotics, or fluctuations. The manuscript files
are unchanged. Fifty original Lean files are preserved byte for byte; two new
Lean files expose the explicit-integrability theorem and its derivation.

## Evidence already completed

- Fresh project build and verification on fac5 on 10 November 2026: 52 project
  objects and five selected theorem targets passed the official Comparator,
  including its Lean and Nanoda kernel checks.
- A separate strict Nanoda run checked 69,638 declarations with no errors.
  Only `propext`, `Classical.choice`, and `Quot.sound` were allowed.
- Missing-target, changed-statement, and forbidden-axiom controls were rejected.
  Source, object, export, and checker identities were bound to the same run.
- Two separately delegated, fresh-context **AI** reviews passed:
  [mathematical fidelity](verification/reviews/mathematical-fidelity.json) and
  [verification](verification/reviews/lean-verification.json). Neither is human
  certification. Pinned dependency artifacts were reused; Mathlib was not
  rebuilt from scratch.
- The saved-evidence gate reports
  [`release_checks_passed`](verification/evidence/release-gate.json).

The reviewed source-package commit is
`9fa016889614fa1cbfc5bae78b8adb66d622edfe`. This acceptance guide and later
publication metadata are administrative additions outside the frozen source
manifest; they do not change the reviewed Lean code or verification scripts.

## How to accept

1. Read the scope and the two AI reports above. Confirm that this conditional
   result, with its stated assumptions, is appropriate for the DGR catalogue.
2. Review the pull request's file changes. The additions are under this project's
   `lean/` and `verification/` directories, with catalogue descriptions updated
   in the repository and project READMEs.
3. Optionally validate the archived evidence using the commands below, or repeat
   the Linux machine run described in [the Lean README](lean/README.md).
4. Merge the pull request into `main` using GitHub's normal merge control.
   No secret, credential, or change to the manuscript is needed.

The owner controls the final merge. No claim that upstream DGR has accepted this
contribution should be made before that merge occurs.

## Full evidence and integrity check

The [contributor's evidence release](https://github.com/ZaytaM/DGR-Collab-Public/releases/tag/loggas-partition-bound-20261110)
holds the full archive, including raw proof exports, logs, and machine receipt.
The archive is about 182 MB and is distributed as a release asset rather than a
Git file. The release also contains a small reviewed source package and
`SHA256SUMS`. The earlier [evidence index](verification/evidence/index.json)
retains its historical pre-publication status; this guide supplies the
publication location without changing the reviewed record.

Download `loggas-public-package-complete-evidence-20261110.tar.gz` from that
release and verify its SHA-256:

```text
20a31a2ca999dd19f32ff5e579396a8cbfcc7292240adb1c3a61e396309aa151
```

On macOS, run `shasum -a 256` on the downloaded archive; on Linux use
`sha256sum`. Extract it into an empty directory. From this project directory:

```sh
python3 verification/check_package.py
python3 verification/check_release.py --evidence /absolute/path/to/extracted/evidence
```

Expect `PASS` and `release_checks_passed`, respectively. These commands validate
source identity and saved evidence; they are not a new kernel replay. The
reviewed source manifest SHA-256 is
`11e98d656f2b5d54d041190416abc3cf32250797011922fa76deb4ffaabbbdca`;
the machine receipt SHA-256 is
`e45f660455d356fd298f660c8437c7a8a90ac5dd549d7ba0b4261e318c5a68e6`.

After acceptance, the owner may mirror the release assets into upstream DGR's
own release storage, preserving the filenames and hashes. The contributor's
release remains the initial evidence location.
