# Delgadino–Gvalani–Rosenzweig: manuscripts and formalizations

Research manuscripts and Lean formalizations by **Matias G. Delgadino, Rishabh Gvalani and Matthew Rosenzweig**.

The catalogue is organized by research theme. Each project has one home, with its paper, formalization and verification information together when available. Closely related projects are cross-linked rather than duplicated.

## Diffusive log/Riesz gases in the Hilbert–Schmidt regime

- **[Sharp mean-field estimates](projects/hilbert-schmidt-mean-field/)** — accepted Lean release with its precise coverage and correspondence qualifications. [Existing preprint](https://arxiv.org/abs/2609.02743); a surgically revised manuscript will be added after author review.
- **[Sharp two-sided size of chaos](projects/hilbert-schmidt-size-of-chaos/)** — quantitative equilibrium chaos estimates. [Draft PDF](projects/hilbert-schmidt-size-of-chaos/manuscript/paper.pdf).
- **[Dynamical local propagation of chaos](projects/hilbert-schmidt-local-chaos/)** — local estimates for diffusive log/Riesz dynamics. [Draft PDF](projects/hilbert-schmidt-local-chaos/manuscript/paper.pdf).

## Attractive logarithmic gases

- **[Part I: partition functions and equilibrium fluctuations](projects/attractive-log-equilibrium/)** — all-order equilibrium expansions, marginals, cumulants and fluctuations. [Draft PDF](projects/attractive-log-equilibrium/manuscript/paper.pdf).
- **[Part II: mean-field dynamics](projects/attractive-log-dynamics/)** — modulated free energy and uniform-in-time near-equilibrium estimates under the stated assumptions. [Draft PDF](projects/attractive-log-dynamics/manuscript/paper.pdf).
- **[Uniform LSI on the homogeneous two-dimensional torus](projects/attractive-log-uniform-lsi/)** — completed formalization throughout the subcritical coupling range, uniformly on compact subintervals. A natural-language informalization will follow. This is a separate result, not a formalization of all of Parts I and II.

## Functional inequalities for mean-field systems

- **[Sharp mean-field LSI rates and singular counterexamples](projects/sharp-mean-field-lsi/)** — the originally accepted symmetric/unrestricted LSI formalization and later verified declarations, including singular-interaction counterexamples. The scope of verification is stated separately from broader manuscript claims. The manuscript is being revised by the authors.
- **[Singular Riesz functional inequalities](projects/singular-riesz-functional-inequalities/)** — links to the existing public formalization of periodic LSI/Poincaré inequalities and whole-space Riesz Poincaré inequalities.
- **[Homogeneous attractive-log LSI](projects/attractive-log-uniform-lsi/)** also belongs to this theme.

## Reading the status of a project

**Manuscript status**, **formal verification**, and **manuscript–Lean correspondence** are separate. A checked Lean result does not imply that every assertion in a companion working draft has been formalized, or that the authors have completed their review of the draft. Consult each project's scope and verification records.

The four working manuscripts carry a DRAFT watermark and a Statement on AI use. They are AI-generated working manuscripts, and the authors have not yet reviewed and independently verified all AI-generated content. The authors are formalizing results in Lean and reworking the natural-language presentation. Statements, proofs, references and exposition remain subject to correction.

## Using the Lean sources

Each formalization is an independent Lean project with its own pinned toolchain and dependencies. Follow its project README rather than running a repository-wide Lake build. Selected public source and verification records are included; development worktrees, caches and private operational material are not part of this catalogue.

All three included Lean packages passed their stated cleaned release-target compilation checks. Exact commands and scope are recorded in each project’s verification directory; compilation is distinct from manuscript correspondence and independent proof replay.

## Contact

- [Matias G. Delgadino](https://math.utexas.edu/directory/matias-delgadino) — matias.delgadino@math.utexas.edu
- [Rishabh Gvalani](https://webhomes.maths.ed.ac.uk/~rgvalani/) — rishabh.gvalani@ed.ac.uk
- [Matthew Rosenzweig](https://matthewrosenzweigwork-max.github.io/) — mrosenz2@andrew.cmu.edu

Licensing and third-party notices, where provided, apply to the relevant material; this catalogue does not impose a new blanket license on its component projects.
