import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Paper.CosineMeanField
import SharpSymmetricLSI.Paper.CosineExpansion
import SharpSymmetricLSI.Paper.CosineDissipation
import SharpSymmetricLSI.Paper.CosineStrict

/-!
# R12: Section 3.4, strict mean-field improvement and the upper bound on `r_{*,κ}`

Manuscript (3.4), (3.18)–(3.20) and the (unnumbered) `ρ_ε` expansions:
* (3.4) and the text before it: `W_κ(ρ,ρ) = κ(Q(ρ) - 1)`; `F` has minimum `-κ/2`, attained
  uniquely at `ρ = 1`; `G_κ(ρ) = H(ρ|m) + (κ/2) Q(ρ)`; for `√ρ ∈ H^1(m)`,
  `D_κ(ρ) = ∫ |2(√ρ)' + κ √ρ (g*ρ)'|² dm`.
* (3.18) for finite Fisher information: `D_κ = I(ρ|m) + 2aκ Q(ρ) + κ² ∫ ρ |(g*ρ)'|² dm`.
* (3.20) `Q(ρ) ≤ ‖ρ-1‖₁² ≤ 2H(ρ|m)` and `H(ρ|m) ≤ G_κ(ρ) ≤ (1+κ) H(ρ|m)`.
* `r_{*,κ} > a` (`cosine_strict`).
* `ρ_ε = 1 + ε cos(2πx)`: `G_κ(ρ_ε) = (ε²/4)(1+κ/2) + o(ε²)`,
  `D_κ(ρ_ε) = (aε²/2)(1+κ/2)² + o(ε²)`; second-mode perturbations `1 + ε cos(4πx)` give the
  quotient `→ 4a`; hence `r_{*,κ} ≤ a min{1+κ/2, 4}` (`cosine_rStar_le`).
`(g*ρ)'` is the weak derivative of the smooth function `g*ρ`; `(√ρ)'` the weak derivative.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

/-- (3.4): interaction energy, minimum, unique minimizer, gap and dissipation formulas. -/
theorem cosine_free_energy {κ : ℝ} (hκ : 0 < κ) :
    (∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      interE (cosW κ) (densMeasure ρ) (densMeasure ρ) = κ * (firstMode ρ - 1)) ∧
    Fstar cosV (cosW κ) = ((-κ / 2 : ℝ) : EReal) ∧
    (∀ μ : ProbabilityMeasure (Torus 1),
      IsMinimizer cosV (cosW κ) μ ↔ (μ : Measure (Torus 1)) = haar 1) ∧
    (∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      gap cosV (cosW κ) (densMeasure ρ) =
        ((klDiv (densMeasure ρ) (haar 1) : ENNReal) : EReal) + ((κ / 2 * firstMode ρ : ℝ) : EReal)) ∧
    (∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) →
      dissipation cosV (cosW κ) ρ =
        ∫⁻ x, ENNReal.ofReal ((2 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 +
          κ * Real.sqrt (ρ x) * weakGrad (gConv ρ) x 0) ^ 2) ∂haar 1) := by
  exact cosine_free_energy_aux hκ

/-- (3.18): expansion of the dissipation on the finite-Fisher-information domain. -/
theorem cosine_dissipation_expansion {κ : ℝ} (hκ : 0 < κ) {ρ : Torus 1 → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1)
    (hI : fisherInfo (densMeasure ρ) (haar 1) ≠ ⊤) :
    dissipation cosV (cosW κ) ρ = fisherInfo (densMeasure ρ) (haar 1) +
      ENNReal.ofReal (2 * aCos * κ * firstMode ρ) +
      ENNReal.ofReal (κ ^ 2 * ∫ x, ρ x * weakGrad (gConv ρ) x 0 ^ 2 ∂haar 1) := by
  exact cosine_dissipation_expansion_aux hκ hρ0 hρ1 hI

/-- (3.20): Pinsker and entropy comparisons. -/
theorem cosine_entropy_comparison {κ : ℝ} (hκ : 0 < κ) {ρ : Torus 1 → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    ENNReal.ofReal (firstMode ρ) ≤ eLpNorm (fun x => ρ x - 1) 1 (haar 1) ^ 2 ∧
    eLpNorm (fun x => ρ x - 1) 1 (haar 1) ^ 2 ≤ 2 * klDiv (densMeasure ρ) (haar 1) ∧
    ((klDiv (densMeasure ρ) (haar 1) : ENNReal) : EReal) ≤ gap cosV (cosW κ) (densMeasure ρ) ∧
    gap cosV (cosW κ) (densMeasure ρ) ≤
      ((1 + κ : ℝ) : EReal) * ((klDiv (densMeasure ρ) (haar 1) : ENNReal) : EReal) := by
  exact cosine_entropy_comparison_aux hκ hρ0 hρ1

/-- Section 3.4: `r_{*,κ} > a`. -/
theorem cosine_strict {κ : ℝ} (hκ : 0 < κ) :
    ENNReal.ofReal aCos < rStar cosV (cosW κ) := by
  exact cosine_strict_aux hκ

/-- Section 3.4: expansions along `ρ_ε = 1 + ε cos(2πx)` and the second-mode quotient. -/
theorem cosine_rho_eps_expansions {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ε : ℝ => (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * gCos x))).toReal /
        ε ^ 2) (𝓝[≠] 0) (𝓝 ((1 + κ / 2) / 4)) ∧
    Tendsto (fun ε : ℝ => (dissipation cosV (cosW κ) (fun x => 1 + ε * gCos x)).toReal / ε ^ 2)
        (𝓝[≠] 0) (𝓝 (aCos / 2 * (1 + κ / 2) ^ 2)) ∧
    Tendsto (fun ε : ℝ => dissipation cosV (cosW κ) (fun x => 1 + ε * gCos (2 • x)) /
        (2 * (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * gCos (2 • x)))).toENNReal))
        (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (4 * aCos))) := by
  exact cosine_rho_eps_expansions_aux hκ

/-- Section 3.4: `r_{*,κ} ≤ a min{1 + κ/2, 4}`. -/
theorem cosine_rStar_le {κ : ℝ} (hκ : 0 < κ) :
    rStar cosV (cosW κ) ≤ ENNReal.ofReal (aCos * min (1 + κ / 2) 4) := by
  exact cosine_rStar_le_aux hκ

end SharpLSI
