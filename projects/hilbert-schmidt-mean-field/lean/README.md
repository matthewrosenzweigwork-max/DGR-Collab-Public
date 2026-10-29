# DGRHS Lean release

The formal release entry point is `DGRHS.Original.Release`.

With the pinned Lean toolchain available, run from this directory:

```sh
lake exe cache get
lake build DGRHS.Original.Release
```

The first command downloads mathlib's compiled cache. The second builds the release and its dependencies; it may require substantial resources. The original `lakefile.toml` is preserved, including its historical default target `DGRHS`. Use the explicit release target above instead of interpreting an unqualified default build as the release gate.

- Lean: `leanprover/lean4:v4.34.1`
- mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- All transitive package revisions: `lake-manifest.json`

See [verification](../verification/README.md) for the distinction between historical acceptance evidence and checks performed while assembling this public package. Do not update the toolchain or dependencies when reproducing the accepted snapshot.
