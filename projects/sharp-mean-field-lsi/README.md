# Sharp mean-field LSI rates and singular counterexamples

Matias G. Delgadino, Rishabh Gvalani and Matthew Rosenzweig

This project brings together the originally accepted symmetric and unrestricted logarithmic Sobolev developments and later checked Lean declarations, including singular-interaction counterexamples.

## Release status

- **Lean:** the original protected verification runs were accepted; the later audit passed for its actual-declaration set and checked singular-extension statements.
- **Manuscript:** the authors are revising the natural-language manuscript. No manuscript is included in this initial release.
- **Correspondence:** **the entire original T01–T14 expanded natural-language campaign is not certified.** Declaration validity must not be confused with complete manuscript correspondence.

The release source is pinned to `matthewrosenzweigwork-max/DGPS-LSI-` commit `9285e3b551e9b6377021e75d0d11c56e4b87feb5`, which incorporates the approved N024 repair and three compilation-only `noncomputable` modifiers. It is not the earlier, pre-repair snapshot.

## What was verified?

### Original results

The protected Comparator and Nanoda runs accepted:

| Development | Accepted run |
|---|---|
| Frozen symmetric LSI layer: 110 theorems, 156 definition anchors | `sym-main-2` |
| 21 post-freeze symmetric results | `symx-main-1` |
| Unrestricted/labeled LSI development | `fl-main-1` |
| Proposition 8.2 non-vacuity | `prop82-main-2` |
| Section 9 examples | `sec9-main-1` |

The accepted proving targets depend only on `propext`, `Classical.choice` and `Quot.sound`. This is **not** a claim that every source file is free of `sorry`: the legacy default build has 22 documented warnings in frozen Section 9 statement/stub files. Their presence must not be confused with a missing proof in the separately checked proving targets.

### Later declarations and singular extension

The final audit certificate records:

- Source/artifact association and exact replay for **754 Campaign modules**, comprising 26,251 Campaign declarations and 121,902 dependency constants.
- A complete export of 123,075 declarations accepted by the official kernel and strict Nanoda, with no missing, unsafe or partial declarations and only the three permitted axioms.
- Source-origin reproduction through **102 renewed compilations and 652 source-bound prior compilations**, not a single fresh unified or bitwise rebuild.
- **120 isolated-reference Comparator targets plus a separate exact-original N024 check** for the singular extension, and completed G4 statement freezing. Overlapping target groups are not independent theorem counts.
- Scoped checks of nine audit-owned baseline corollaries, the STR028 full-graph corollary and eight interpretation probes. These are not an independent full-baseline Comparator certification or additional production API exports.

The singular-counterexample development constructs a circle collision barrier with strong integrability and subcritical Sobolev regularity. Under its exact stated hypotheses, arbitrarily small perturbations of admissible baselines can have zero finite-particle Poincaré and LSI rates while retaining positive mean-field PL rates. Explicit cosine and periodic Green specializations are included. Consult the precise Lean statements rather than treating this summary as a replacement for their hypotheses.

The production entrypoint is `Campaign/DGPS/SingularCounterexample/Main.lean`; its headline declarations include `barrier_exists_and_properties`, `singular_counterexample_generic`, `singular_counterexample_cosine`, `singular_counterexample_green` and `barrier_perturbative_smallness`.

## What is not certified?

The recorded outstanding correspondence/assembly differences include:

- **FOU014:** general probability-space tensorization versus the checked Haar-torus scope.
- **FIN007:** an additional density-continuity hypothesis.
- **EX017:** missing general ordinary-H1 infimum assembly.
- **LIP032:** the original unconditional assertion remains held.
- **N012:** the checked statement is the author-approved almost-everywhere replacement, not the original pointwise assertion.
- **O005–O013:** secondary unclaimed results must not be advertised as completed.

These qualifications do not negate the separately checked declarations. They do prevent describing the entire expanded campaign as a completed formalization of its original natural-language specifications. Protected comparison establishes statements under their definitions; manuscript fidelity additionally depends on the recorded definition review and author approvals. Comparator does not itself check Lean attributes such as `simp` and `instance`.

## Toolchain and package layout

Lean is pinned to **v4.35.0-rc3** and Mathlib to **ec6a61cec0d8f9fda04453e9bb5761a79aa43a70**. Retain both Lake manifests and both toolchain files.

The Lean distribution preserves the original nested-package relationship:

```text
lean/
  lakefile.toml, lake-manifest.json, lean-toolchain
  SharpSymmetricLSI.lean, SharpSymmetricLSI/
  FullLabeledLSI.lean, FullLabeledLSI/
  Campaign/
    lakefile.toml, lake-manifest.json, lean-toolchain
    DGPS.lean, DGPS/
```

`Campaign` requires its parent package by `path = ".."`. Do not flatten these packages, add a second Mathlib requirement, or replace the pinned manifests. Build caches and private operational history are not part of the public source distribution.

From `lean/`, the legacy commands are:

```sh
lake build
# Equivalent default targets:
lake build SharpSymmetricLSI FullLabeledLSI FullLabeledLSIVerified
```

The `FullLabeledLSIVerified` target preserves accepted examples and non-vacuity modules that are not imported by the main library roots. From `lean/Campaign/`, build both the Campaign root and the separately retained singular-counterexample entrypoint:

```sh
lake build DGPS DGPS.SingularCounterexample.Main
```

`DGPS.lean` does not import `DGPS.SingularCounterexample.Main`; building only `DGPS` therefore does not check that extension. Compilation alone does not repeat the independent Comparator/Nanoda procedure or prove manuscript correspondence.

## Verification provenance

The [source manifest](verification/source-manifest.json) records the 1,808 distributed files. Byte identity against the pinned Git objects and a static local import-closure check passed; no new Lean build or proof replay was run during initial packaging. Subsequent cleaned release-target builds passed; see [the clean-build record](verification/clean-build-20261029.md). Five unreachable legacy modules (including challenge/check files) were omitted, without editing any included Lean source. Vendor license and notice files are retained in their original locations.

See the bundled [verification records](verification/) and [Campaign certificate](verification/campaign-certificate.md).

The governing upstream records, pinned to the source commit, are the [final certificate](https://github.com/matthewrosenzweigwork-max/DGPS-LSI-/blob/9285e3b551e9b6377021e75d0d11c56e4b87feb5/Campaign/audit/n024-repair-20261027_155423_UTC/CERTIFICATION.md) and [final report](https://github.com/matthewrosenzweigwork-max/DGPS-LSI-/blob/9285e3b551e9b6377021e75d0d11c56e4b87feb5/Campaign/audit/n024-repair-20261027_155423_UTC/REPORT.md). These upstream links may require access to the source repository. The certificate was finalized on 28 October 2026 at 03:44 UTC (27 October at 11:44 PM EDT).

This packaging work does not claim a new independent proof replay. The original certificates and their precise scopes remain authoritative. No broader license is inferred from inclusion in this catalogue.
