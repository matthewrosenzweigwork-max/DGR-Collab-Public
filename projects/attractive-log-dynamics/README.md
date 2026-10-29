# The attractive logarithmic gas II: mean-field dynamics

Matias G. Delgadino, Rishabh Gvalani and Matthew Rosenzweig

**[Read the draft (30 pages)](manuscript/paper.pdf)** · **[LaTeX source](manuscript/source/)**

The modulated-free-energy method for attractive-log dynamics, including finite-time estimates and uniform-in-time near-equilibrium estimates under the stated additional assumptions. Periodic and confined planar settings are treated.

## Status

- **Manuscript:** public working draft; the authors have not yet reviewed and independently verified all AI-generated content.
- **Lean formalization:** no completed corresponding formalization is supplied with this manuscript.
- **Correspondence:** no claim of complete manuscript-to-Lean correspondence is made.

The manuscript includes a Statement on AI use and a diagonal DRAFT watermark. The authors are formalizing the results in Lean and revising the natural-language presentation. Statements, proofs, references and exposition remain subject to correction.

The homogeneous torus LSI formalization is a separate result: it is **not** a formalization of all of Parts I and II.

## Related projects

- [Part I: equilibrium expansions](../attractive-log-equilibrium/)
- [Homogeneous two-dimensional torus LSI](../attractive-log-uniform-lsi/)

## Source and version

This distribution contains the author-selected manuscript, with author/contact formatting, draft markings and an updated AI-use disclosure prepared on 28 October 2026. Those presentation changes do not change the mathematical source. The accompanying [file manifest](manuscript/manifest.json) identifies the distributed PDF and source files; it is an integrity record, not a mathematical certificate.

To rebuild, run `pdflatex main.tex` in `manuscript/source/` with a standard TeX Live installation. Run `pdflatex main.tex` twice more to resolve cross-references. The bibliography is included in the source.
