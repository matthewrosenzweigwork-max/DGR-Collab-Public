# Verification record and limits

## Provenance

- Source repository: `matthewrosenzweigwork-max/DGRHS-Lean`
- Accepted tag: `dgrhs-release-20261010`
- Accepted commit: `babd87e77d20a7f1bb882ef22ac499f114c3ae3b`
- Original proof subtree: `eca8a4c3d0644f63e60ccc0ad968874caf38fcc5`
- Release entry point: `DGRHS.Original.Release`

## Historical acceptance evidence

The source release record dated October 10, 2026 reports 37 accepted rows, with comparator, Nanoda, and Lean-kernel checks. It reports a successful release-module build (5,376 jobs) and 4,047 axiom-report lines containing only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) or no axioms, without `sorryAx`. These are historical reports from the accepted campaign, not a new certification performed during packaging.

The source release module was augmented with three imports after the P8 freeze; the release record says these were outside accepted package closures. This distinction is retained rather than describing every file in the source repository as independently accepted.

## Scope qualifications

The accepted formal statements include the following qualifications:

- Theorem 2.13 and Proposition 8.2 have conditional Itô-admissibility hypotheses.
- Corollary 7.3 is accepted in the `C_pw = 0` form.
- The Riesz version of Theorem 2.8 is for laws with finite relative entropy.
- Remark 3.2 is in corrected inequality form.
- Proposition 3.1 uses a weaker, proved substitute.

The historical release record excludes several extensions, including the “decay of μ” phrase in the one-body exponential-integrability remark, kinetic attractive/sharpness variants, the kinetic spatial-observable marginal, unified constants for kinetic 2.22/2.23, and the torus–kinetic combination. These are not implied by release readiness.

## Manuscript correspondence is a separate gate

The subsequent audit at source commit `25f1b81b166f74ad4c64274a442c744b64bb0971` reviewed 534 occurrences and 191 aliases. Its 52 candidates were classified as 23 accepted, 14 qualified, 12 rejected, and 3 unresolved. These are audit dispositions, **not counts of proved theorems**.

It identified false auxiliary assertions as printed involving general-profile derivatives, a missing bounded-density hypothesis, and general-profile Riesz short-range bounds. It also requires domain clarification for the signed Riesz commutator and the positive-Riesz equilibrium correction written as separate potentially divergent integrals. No counterexample was found to the principal conclusions under the actual hypotheses and proof mechanisms examined; this limited negative finding is not whole-proof certification. Consequently, neither the original manuscript nor its repaired draft is bundled as a fully certified natural-language counterpart.

## Public-package checks

The public package retains **1,284 Lean modules** in the import closure of `DGRHS.Original.Release` and the original default `DGRHS` target; **396 unreachable Lean modules** are excluded. Five original upstream license notices and all three pinned build-configuration files are retained. All **1,292 source/configuration/notice files** match their Git blob identities at the accepted commit. No declarations were rewritten.

Run `python3 verification/check_source.py` from this project directory to check the packaged bytes against [the manifest](source-manifest.json). [The packaging check record](packaging-checks.json) also records the import-closure scope and limitations. File identity and import-closure checks are not substitutes for Lean compilation, axiom checking, or semantic correspondence review. A fresh Lean build has not been performed in the packaging environment unless explicitly recorded in that check record.

No operational logs, private discussion histories, credentials, machine paths, compiled caches, or obsolete manuscripts are needed to use the public source release.

## Subsequent clean build

The pinned release-target compilation passed. See [the clean-build record](clean-build-20261029.md). This supplements the earlier packaging checks without broadening their certification scope.
