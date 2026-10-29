# Uniform LSI for the homogeneous attractive logarithmic gas

**Matias G. Delgadino, Rishabh Gvalani, Matthew Rosenzweig**

This project formalizes a uniform logarithmic Sobolev inequality for the homogeneous-background attractive logarithmic gas on the two-dimensional square flat torus. For every fixed `0 ≤ β₀ < 4`, a finite constant is chosen uniformly for all `N ≥ 2` and `0 ≤ β ≤ β₀`, in the normalization of the formal statement. The critical endpoint `β = 4` is excluded.

The accepted statement uses the full labeled ambient smooth-form closure and the physical gradient energy. Normalization of the canonical Green Gibbs measure is a proved companion, not an assumption that permits a zero-measure interpretation.

- **Lean source:** [independent Lake project](lean/)
- **Main theorem:** [Theorem11.lean](lean/LeanResearch/PeriodicAttractiveLogGas/Theorem11.lean)
- **Verification:** [scope and reproduction notes](verification/README.md)
- **Natural-language informalization:** forthcoming.

## Main declarations

- `PeriodicAttractiveLogGas.Theorem11.theorem11`
- `PeriodicAttractiveLogGas.Theorem11.uniform_ambient_lsi`
- `PeriodicAttractiveLogGas.Theorem11.theorem11_with_normalization`

## Status and scope

The October 1, 2026 acceptance records report protected Comparator, Nanoda and Lean-kernel acceptance for the 402-module local proof closure, 22 required declarations and a 23-module frozen definition closure. The only permitted transitive axioms are `propext`, `Classical.choice` and `Quot.sound`.

This public package preserves those proof files and the registered solution project configuration byte for byte. Source identity and dependency-closure checks were performed for packaging; no fresh kernel replay is claimed by that packaging check.

Recorded qualifications include larger nonsharp fixed-particle constants than some manuscript displays and a formal geometric argument using coordinate cuts, signed-boundary cancellation and Brunn–Minkowski/coarea. The original geometric argument was validated separately, not formalized verbatim. Semantic review was independent AI review, not completed human certification. Protected official dependency artifacts were reused in the accepted replays.

## Building

Use an installation of Lean managed by Elan; the project pins Lean `v4.34.1` and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.

```sh
cd lean
lake exe cache get
lake build Solution Audit
```

Run the lightweight package identity check from this project directory:

```sh
python3 verification/check_package.py
```

The build is independent of the other projects in this repository. Do not replace its toolchain or dependency pins to combine the projects into a single build.

## Related work

[Attractive log gas Part I](../attractive-log-equilibrium/) and [Part II](../attractive-log-dynamics/) are related working manuscripts. This LSI result is separate and is **not a formalization of those manuscripts in full**.

## Attribution and third-party material

Imported mathematical developments retain their original license and provenance files under `lean/LeanResearch/Imported/`. No new blanket license is imposed by this packaging step.

## Release-package build

The cleaned release targets compiled successfully with the pinned toolchain. See [the build record](verification/clean-build-20261029.md) for the exact target and scope.
