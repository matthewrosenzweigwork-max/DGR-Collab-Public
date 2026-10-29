# Hilbert–Schmidt mean-field estimates

**Matias G. Delgadino, Rishabh Gvalani, Matthew Rosenzweig**

Lean formalization associated with [*Sharp mean-field estimates for diffusive log/Riesz gases in the Hilbert–Schmidt regime* (arXiv:2609.02743)](https://arxiv.org/abs/2609.02743).

## What is released

The accepted DGRHS Lean release covers source-facing results on partition functions, Gibbs laws and fluctuations, entropic commutators, diffusive mean-field limits, and conditional dynamical central limit theorems. The exact formal statements—not the informal overview—determine the scope and hypotheses of each result.

- [Lean sources and build instructions](lean/README.md)
- [Verification and correspondence qualifications](verification/README.md)

This is the accepted `dgrhs-release-20261010` snapshot, commit `babd87e77d20a7f1bb882ef22ac499f114c3ae3b`, with operational material and unrelated modules excluded from the public source package. Retained Lean files and dependency pins are unchanged.

## Manuscript status

The arXiv manuscript is provided as a reference, **not as a claim of complete literal correspondence with this Lean release**. A subsequent correspondence audit identified qualifications and auxiliary assertions requiring repair. A surgically revised manuscript is being reviewed and is not included in this initial release. It will be added separately when ready.

Important qualifications include conditional Itô-admissibility assumptions for the dynamic results, a finite-relative-entropy domain for the Riesz entropic commutator, and corrected or weaker forms of some auxiliary results. See the verification note before citing a formal theorem as establishing a particular printed statement.

## AI assistance

AI systems assisted the formalization and its verification workflow. Machine checking of Lean declarations does not by itself establish that their statements accurately represent every assertion of the natural-language manuscript. The authors do not claim to have personally reviewed all AI-produced content. This release distinguishes formal proof acceptance from manuscript correspondence and author review.

## Release-package build

The cleaned release targets compiled successfully with the pinned toolchain. See [the build record](verification/clean-build-20261029.md) for the exact target and scope.
