import DGPS.Frontier.LIP051.T32
import DGPS.Frontier.LIP051.T33
import DGPS.Frontier.LIP051.T34

/-!
# LIP051.06: Spectral-section convergence and coefficient symmetry

Task id `LIP051.06`, title "Spectral-section convergence and coefficient symmetry" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", category leaf formalization, verification V1).
Proved inputs: `LIP051.32` (`DGPS.Frontier.LIP051.T32`), `LIP051.33` (`DGPS.Frontier.LIP051.T33`)
and `LIP051.34` (`DGPS.Frontier.LIP051.T34`).

For the centered kernel `K` of `LIP051.03` and representatives `f j` of the basis classes `e j`,
with coefficients `T i j = ∬ K(x,y) f i(x) f j(y) dμ(x) dμ(y)`, the main theorem collects the
following conclusions. The coefficients are symmetric and vanish in row and column zero. The
positive sections `K_R` satisfy `‖K - K_R‖₂ → 0`, the positive Parseval identity holds, and the
positive tail identity holds for every `R`. Each `K_R` and `F_R = K - K_R` is `L²`, symmetric, and
centered in either variable almost everywhere.

## Provides

* `DGPS.Frontier.LIP051.lip051_06_spectral_section_convergence_coefficient_symmetry`: the main
  theorem, the conjunction of the twelve conclusions listed in its statement (see R5 notes).

No helper declaration is introduced. The proof is the assembly of `LIP051.33` (symmetry, zero row
and zero column) and `LIP051.34` (sections, tails, Parseval, membership, symmetry and centering).

## R5 notes

1. Kernel. `K` is `centeredKernelOf_LIP05103 μ W`, under exactly the hypotheses of `LIP051.03`:
   `Continuous (Function.uncurry W)`, symmetry of `W`, `0 ≤ M` and `|W| ≤ M`. No `Spec`, `KData`,
   `Hw`, Wick or Gaussian object occurs. The identifications of `S.mu` and `D.K` with `μ` and `K`
   belong to `LIP051.01` and are not used here.
2. Basis and normalization. `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)` with `he0 : e 0 = Lp.const 2 μ 1`,
   that is `e 0 = 1` almost everywhere, as the common setup states. It is a hypothesis of the
   theorem, not a consequence.
3. Representatives. The coefficients and sections are defined with functions, so the statement
   quantifies over every family `f` of measurable functions with `f j =ᵐ[μ] e j`. Every conclusion
   holds for every such family, so none depends on a selected representative.
4. Index convention (defect FD-002). Reading used: the coefficient symmetry and the zero row and
   zero column quantify over all `i, j : ℕ`, including `0`, as the specification writes `i, j ≥ 0`.
   The zero row and zero column are conclusions, not hypotheses. The sections `K_R`, the tails
   `F_R`, the Parseval identity and the tail identity use positive indices only: the sections sum
   over `i, j ∈ {1,…,R}`, and the sums run over the positive pairs `1 ≤ q.1 ∧ 1 ≤ q.2` and, for the
   tail, over those outside `{1,…,R}²`. No positive-mode restriction is added to the coefficient
   binder or to the hypotheses. The positive-mode convention of the Gaussian fluctuation does not
   apply to this unit, because it contains no Gaussian object.
5. Norms. `‖F‖₂` is `(eLpNorm F 2 (μ.prod μ)).toReal`, and `‖K‖₂²` is its square, as in
   `LIP051.34`. `K` is the pointwise continuous representative of the centered kernel, never an
   arbitrary representative of its product-L² class, so the original diagonal is retained.
6. Summability. Parseval and the tail identity are `HasSum` statements, so summability over the
   indexing subtypes is part of each conclusion.
7. Centering. The specification says "centered almost everywhere". The conclusion uses the `∀ᵐ`
   form for each variable. The proof gives the identities for every `y` (respectively every `x`).
8. Lean-exposed specification defects: none found.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- LIP051.06: spectral-section convergence and coefficient symmetry. For a probability measure
`μ` on the torus, a bounded continuous symmetric `W`, a real Hilbert basis `e` of `L²(μ)` with
`e 0 = 1`, and measurable representatives `f j` of the classes `e j`, with `K` the centered kernel
of `LIP051.03` and coefficients `T i j`: the coefficients are symmetric with zero row and zero
column; the `L²` norms of the tails `K - K_R` tend to zero; the positive Parseval identity and the
positive tail identity hold; and each `K_R` and `F_R` is `L²`, symmetric, and centered in either
variable almost everywhere. See the module docstring, R5 notes. -/
theorem lip051_06_spectral_section_convergence_coefficient_symmetry {d : ℕ}
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ)) :
    (∀ i j : ℕ, coefT_LIP05134 μ W f i j = coefT_LIP05134 μ W f j i) ∧
    (∀ j : ℕ, coefT_LIP05134 μ W f 0 j = 0) ∧
    (∀ i : ℕ, coefT_LIP05134 μ W f i 0 = 0) ∧
    Tendsto (fun R : ℕ => (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal) atTop
        (𝓝 0) ∧
    HasSum (fun q : {q : ℕ × ℕ // 1 ≤ q.1 ∧ 1 ≤ q.2} => coefT_LIP05134 μ W f q.1.1 q.1.2 ^ 2)
      ((eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d => centeredKernelOf_LIP05103 μ W p.1 p.2)
        2 (μ.prod μ)).toReal ^ 2) ∧
    (∀ R : ℕ, HasSum (fun q : {q : ℕ × ℕ // (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)} =>
        coefT_LIP05134 μ W f q.1.1 q.1.2 ^ 2)
      ((eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal ^ 2)) ∧
    (∀ R : ℕ, MemLp (sectionKR_LIP05134 μ W f R) 2 (μ.prod μ)) ∧
    (∀ R : ℕ, MemLp (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)) ∧
    (∀ R : ℕ, ∀ x y : DGPS.Torus d, sectionKR_LIP05134 μ W f R (x, y) =
        sectionKR_LIP05134 μ W f R (y, x)) ∧
    (∀ R : ℕ, ∀ x y : DGPS.Torus d, tailKR_LIP05134 μ W f R (x, y) =
        tailKR_LIP05134 μ W f R (y, x)) ∧
    (∀ R : ℕ, (∀ᵐ y ∂μ, ∫ x, sectionKR_LIP05134 μ W f R (x, y) ∂μ = 0) ∧
        ∀ᵐ x ∂μ, ∫ y, sectionKR_LIP05134 μ W f R (x, y) ∂μ = 0) ∧
    (∀ R : ℕ, (∀ᵐ y ∂μ, ∫ x, tailKR_LIP05134 μ W f R (x, y) ∂μ = 0) ∧
        ∀ᵐ x ∂μ, ∫ y, tailKR_LIP05134 μ W f R (x, y) ∂μ = 0) := by
  obtain ⟨hsymT, hrow0, hcol0⟩ :=
    lip051_33_symmetry_constant_row hWc hs hM hb e he0 f hfm hfe
  obtain ⟨hconv, hpar, htail, hsecL2, htailL2, hsecS, htailS, hsecC, htailC⟩ :=
    lip051_34_positive_spectral_sections_tails hWc hs hM hb e he0 f hfm hfe
  exact ⟨hsymT, hrow0, hcol0, hconv, hpar, htail, hsecL2, htailL2, hsecS, htailS, hsecC, htailC⟩

end DGPS.Frontier.LIP051
