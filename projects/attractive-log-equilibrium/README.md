# Attractive log gas I: partition functions and equilibrium fluctuations

Matias G. Delgadino, Rishabh Gvalani and Matthew Rosenzweig

**[Read the draft (127 pages)](manuscript/paper.pdf)** · **[LaTeX source](manuscript/source/)**

All-order equilibrium expansions for partition functions, fixed-particle marginals, cumulants and fluctuations of attractive logarithmic gases.

## Status

- **Manuscript:** public working draft; the authors have not yet reviewed and independently verified all AI-generated content.
- **Lean formalization:** [conditional uniform partition bound](lean/), assuming the log-HLS inequality and explicit integrability of its energy integrand, plus existence of the Fourier-normalized kernel. See the [exact scope](verification/SCOPE.md) and [verification records](verification/README.md).
- **Correspondence:** no claim of complete manuscript-to-Lean correspondence is made.

The manuscript includes a Statement on AI use and a diagonal DRAFT watermark. The authors are formalizing the results in Lean and revising the natural-language presentation. Statements, proofs, references and exposition remain subject to correction.

The homogeneous torus LSI formalization is a separate result: it is **not** a formalization of all of Parts I and II.

The partition-bound release covers the conditional implication corresponding to
the short draft's uniform bound. It does not establish the log-HLS assumption,
threshold identification, determinant asymptotics, fluctuations, or the rest of
this working manuscript. Its public declaration is
`LogGasPaper.main_with_domain`. AI fidelity and verification reviews, machine
acceptance and author scope decisions are recorded separately; none is presented
as independent human certification of the complete manuscript.

## Related projects

- [Part II: mean-field dynamics](../attractive-log-dynamics/)
- [Homogeneous two-dimensional torus LSI](../attractive-log-uniform-lsi/)

## Source and version

This distribution contains the author-selected manuscript, with author/contact formatting, draft markings and an updated AI-use disclosure prepared on 28 October 2026. Those presentation changes do not change the mathematical source. The accompanying [file manifest](manuscript/manifest.json) identifies the distributed PDF and source files; it is an integrity record, not a mathematical certificate.

To rebuild, run `pdflatex main.tex` in `manuscript/source/` with a standard TeX Live installation. Then run `bibtex main`, followed by `pdflatex main.tex` twice.
