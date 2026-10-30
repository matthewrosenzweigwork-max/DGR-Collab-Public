# Sharp mean-field LSI rates and singular counterexamples

Matias G. Delgadino, Rishabh Gvalani and Matthew Rosenzweig

This project brings together the originally accepted symmetric and unrestricted logarithmic Sobolev developments and later checked Lean declarations, including singular-interaction counterexamples.

## Release status

The distributed source is pinned to `matthewrosenzweigwork-max/DGPS-LSI-` commit `40f266f117e2ac74b447f5fa7372ba2d0355b327` on `codex/dgps-lsi-audit-certification`. This refresh preserves the accepted legacy and singular developments and includes the later T01-led repair campaign. It does not replace the separate DGPS `main` branch or alter the manuscript.

- **Current cloud release gate: PASS.** Fresh root and combined checks passed with unchanged source; all 35 selected type outputs are present and their axiom closures contain only `propext`, `Classical.choice` and `Quot.sound`. See the [dated release verification record](verification/release-verification-20261030.md) and [axiom results](verification/release-20261030/PUBLIC_AXIOM_RESULTS.json).
- **Prior T01 verification:** the [29 October final-root acceptance record](https://github.com/matthewrosenzweigwork-max/DGPS-LSI-/blob/40f266f117e2ac74b447f5fa7372ba2d0355b327/Campaign/repair/20261028/checks/T01_FINAL_ROOT_ACCEPTANCE.json) already reports internal acceptance; this is distinct from author review and from the new cloud integration gate. Author-facing status remains applied/pending review where recorded.
- **Manuscript:** no revised manuscript is included. This source release is not certification of every statement in the original expanded T01–T14 natural-language campaign.

The governing [repair contract](https://github.com/matthewrosenzweigwork-max/DGPS-LSI-/blob/40f266f117e2ac74b447f5fa7372ba2d0355b327/Campaign/repair/20261028/MASTER_EXECUTION_PROMPT.md) calls for T01 sharp limits and eventual subcritical inequalities, T14 and the subsequent repair queue, with targeted changed-closure checks and a separate final T01 verification—not a fresh global audit after every repair.

## Historical verification preserved in this release

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

### Earlier actual-declaration audit and singular extension

The preserved audit certificate for source `9285e3b5` records:

- Source/artifact association and exact replay for **754 Campaign modules**, comprising 26,251 Campaign declarations and 121,902 dependency constants.
- A complete export of 123,075 declarations accepted by the official kernel and strict Nanoda, with no missing, unsafe or partial declarations and only the three permitted axioms.
- Source-origin reproduction through **102 renewed compilations and 652 source-bound prior compilations**, not a single fresh unified or bitwise rebuild.
- **120 isolated-reference Comparator targets plus a separate exact-original N024 check** for the singular extension, and completed G4 statement freezing. Overlapping target groups are not independent theorem counts.
- Scoped checks of nine audit-owned baseline corollaries, the STR028 full-graph corollary and eight interpretation probes. These are not an independent full-baseline Comparator certification or additional production API exports.

The singular-counterexample development constructs a circle collision barrier with strong integrability and subcritical Sobolev regularity. Under its exact stated hypotheses, arbitrarily small perturbations of admissible baselines can have zero finite-particle Poincaré and LSI rates while retaining positive mean-field PL rates. Explicit cosine and periodic Green specializations are included. Consult the precise Lean statements rather than treating this summary as a replacement for their hypotheses.

The production entrypoint is `Campaign/DGPS/SingularCounterexample/Main.lean`; its headline declarations include `barrier_exists_and_properties`, `singular_counterexample_generic`, `singular_counterexample_cosine`, `singular_counterexample_green` and `barrier_perturbative_smallness`.

## Current scope and qualifications

The T01-led repair queue must be assessed against its current acceptance records, not by repeating the earlier snapshot's deficit list. In particular, historical missing-assembly labels are not evidence that the subsequently implemented T01/T02/T14 and downstream work remains missing. The dated release record separates prior targeted acceptance from the fresh combined integration result.

The governing contract retains these substantive qualifications:

- **FOU014:** the required Haar/unit-torus tensorization is not a theorem for arbitrary probability spaces.
- **FIN007:** the constant `200` is accepted; the additional continuity hypothesis must not be silently removed.
- **LIP032:** unconditional contractibility remains held; positive-rate conditional contractibility and the zero-rate noncontractible example are distinct accepted statements.
- **LIP051 / LIP051.37:** use positive/recentered Fourier modes and retain the required a.e. measurability hypothesis.
- **STR029.08 / STR029.56:** retain extended-real liminf and the segment/local-domain condition, respectively.
- **N012 / N024:** retain the approved a.e. weak-gradient formulation and repaired entropy-support statement.
- **EX049:** the implemented replacement proof is not recovery of the lost historical proof route.
- **T11:** the corrected barycenter identity is about the induced probability measure, not equality of a stored square-root record.

Optional FIN074 and stronger singular T4 specifications are not silently promoted into completed claims or prerequisites of the current scoped release. Historical unclaimed secondary results remain unclaimed unless a later exact acceptance record establishes otherwise. Author acceptance and manuscript fidelity remain separate from successful Lean checking. Comparator does not itself check attributes such as `simp` and `instance`.

### Included source beyond the current gate

The package retains these six auxiliary modules as source, without claiming that the combined root gate verifies them:

- `DGPS.Examples.PolynomialSpeciesSplit`
- `DGPS.FiniteN.AnisotropicQuarticRareCoreMass`
- `DGPS.FiniteN.AnisotropicQuarticRareShell`
- `DGPS.Lipschitz.T01ActualSpectralComparison`
- `DGPS.Lipschitz.T01OccupationUI`
- `DGPS.Lipschitz.T01ReferenceComparison`

Their bytes are pinned in the source manifest. They are outside the current root import closure. A file being distributed or explicitly buildable does not imply it was part of an accepted verification target.

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

The `FullLabeledLSIVerified` target preserves accepted examples and non-vacuity modules that are not imported by the main library roots. From `lean/Campaign/`, explicitly select the Campaign root, the separately retained singular-counterexample entrypoint and the later T05/T06 integration target:

```sh
lake build DGPS DGPS.SingularCounterexample.Main DGPS.Structural.T05T06IntegrationGate
```

`DGPS.lean` does not import the separately retained singular entrypoint or the new T05/T06 pair. The default `DGPS` Lake library follows its root imports; it does not automatically check every tracked file below `DGPS/`. For direct imports, T05 is `DGPS.Structural.PositiveRateCriterion` and T06 is `DGPS.Structural.T06Comparison`. Compilation alone does not repeat the independent Comparator/Nanoda procedure or prove manuscript correspondence.

## Verification provenance

The [source manifest](verification/source-manifest.json) binds each included file to the current source commit with Git blob identity, SHA256 and byte size. Its file count and exact exclusions are authoritative; no count from the previous release is reused. Static import closure and byte identity are packaging checks, not proof verification. Vendor licenses and notices are preserved. Unreachable legacy challenge/check stubs remain omitted unless the current import closure requires them.

The [29 October clean-build record](verification/clean-build-20261029.md), [earlier Campaign certificate](verification/campaign-certificate.md) and original JSON receipts remain historical records for their stated source and scope. They have not been rewritten as certification of `40f266f`.

See [verification records](verification/README.md) and the new [dated release record](verification/release-verification-20261030.md) for the exact current gate, evidence reuse, resource limits and source/artifact bindings. Current gate outcome: **PASS**. The distribution contains **2,393 source/configuration/license files**; its integrity check passed. The verification used a **2,064-module source/object-bound project dependency namespace** and **two fresh module checks** (`DGPS` and `CombinedReleaseGate`), not 2,064 fresh recompilations. See the [evidence hash manifest](verification/release-20261030/HASH_MANIFEST.json). No new whole-repository independent Comparator/Nanoda replay is implied by the source refresh or by targeted Lean checks. No broader license is inferred from inclusion in this catalogue.

## Preserved singular-entrypoint verification

`DGPS.SingularCounterexample.Main` is the separately selected production entrypoint. Its 941-module source closure matches the earlier verified release, and the historical explicit check recorded exit 0 on 29 October 2026 at 20:22:46 UTC. This supports preservation of the prior scoped acceptance; **no fresh cloud replay of this singular entrypoint is claimed**. The current combined gate imports the Campaign root plus T05/T06, not this separate entrypoint. The explicit build command above is a reproduction instruction, not a claim it was rerun in the current gate.

The separate [DGPS evidence commit](https://github.com/matthewrosenzweigwork-max/DGPS-LSI-/commit/915524b3d5ba1c89e29b7cba1af09848855a20f6) records this release verification. It does not replace the pinned code commit `40f266f117e2ac74b447f5fa7372ba2d0355b327`.
