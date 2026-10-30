import DGPS.Examples.PolynomialSpeciesActualOriginInputs
import DGPS.Examples.PolynomialSpeciesScaledOriginExclusion

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- Actual full limit capture: the previously missing annular condition is derived from the origin IFT and actual Haar rate bound. -/
theorem polynomial_scalarMinimizer_full_limit_capture
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (h A B α σ : ℕ → ℝ) (A₀ B₀ α₀ σ₀ : ℝ)
    (hh : Tendsto h atTop (𝓝 0)) (hA : Tendsto A atTop (𝓝 A₀))
    (hB : Tendsto B atTop (𝓝 B₀)) (hα : Tendsto α atTop (𝓝 α₀))
    (hσ : Tendsto σ atTop (𝓝 σ₀))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hne : ∀ n, h n ≠ 0) (hs : ∀ n, (h n) ^ 4 * σ n = root_EX054 (h n))
    (hr : ∀ n, a0 * (1 + (h n) ^ 2 * α n) =
      (scalarRate (canonical_elementary_polynomial_model (h n)) (b n)).toReal)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n))
    (hρ : ∀ n, (ρ n).density =ᵐ[haar 1] (polynomialChartAbsolute (h n)
      ((h n * A n) • cosC2_STR02915 + (h n * B n) • sinC2_STR02915 +
        (ψ (polynomialScaledParameters (h n, (A n, B n, α n, σ n))) : PeriodicC2_STR02969))).density)
    (hpos : ∀ n, 0 < h n)
    (hp : ∀ n, polynomialScaledParameters (h n, (A n, B n, α n, σ n)) ∈ U) :
    α₀ = (3 - Real.sqrt 2) / 24 ∧
      A₀ = -(1 + Real.sqrt 2) / 2 ∧ B₀ ^ 2 = (1 + Real.sqrt 2) / 4 := by

  obtain ⟨δ, hδ, hupper⟩ := polynomial_scalarRate_scaled_coefficient_upper
  have hsmall : ∀ᶠ n in atTop, h n < δ :=
    hh.eventually (gt_mem_nhds hδ)
  have hαupper : ∀ᶠ n in atTop, α n ≤ 5 / 48 := by
    filter_upwards [hsmall] with n hn
    exact hupper (h n) (hpos n) hn (b n) (α n) (hr n)
  have hα₀ : α₀ ≤ 5 / 48 := le_of_tendsto hα hαupper
  obtain ⟨O, hO, h0O, _hOU, hcritical⟩ :=
    polynomial_scalarMinimizer_scaled_critical hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  have hq : Tendsto (fun n => (h n, (A n, B n, α n, σ n))) atTop
      (𝓝 (0, (A₀, B₀, α₀, σ₀))) :=
    hh.prodMk_nhds (hA.prodMk_nhds (hB.prodMk_nhds (hα.prodMk_nhds hσ)))
  have hmem : ∀ᶠ n in atTop, (h n, (A n, B n, α n, σ n)) ∈ O :=
    hq.eventually (hO.mem_nhds (h0O _))
  have hamp : (A₀, B₀) ≠ (0 : ℝ × ℝ) := by
    intro he
    have hq0 : Tendsto (fun n => ((h n, α n, σ n), (A n, B n))) atTop
        (𝓝 ((0, α₀, σ₀), (0 : ℝ × ℝ))) := by
      rw [← he]
      exact (hh.prodMk_nhds (hα.prodMk_nhds hσ)).prodMk_nhds (hA.prodMk_nhds hB)
    have hexcl := hq0.eventually (polynomialScaledAmplitudeGradient_origin_exclusion
      hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst α₀ σ₀ hα₀)
    have hfalse : ∀ᶠ n : ℕ in atTop, False := by
      filter_upwards [hmem, hexcl] with n hn hexc
      have hcrit := hcritical (h n) (σ n) ((A n, B n), α n) (b n) (ρ n)
        (hne n) hn (hs n) (hr n) (hG n) (hmin n) (hρ n)
      have hg : polynomialScaledAmplitudeGradient ψ ((h n, α n, σ n), (A n, B n)) = 0 := by
        exact congrArg Prod.fst hcrit
      have hz := hexc (hne n) hg
      exact polynomial_scalarMinimizer_scaled_amplitude_ne_zero hzero
        (h n) (A n) (B n) (α n) (σ n) (b n) (ρ n) (hp n) (hG n) (hρ n) hz
    obtain ⟨n, hn⟩ := hfalse.exists
    exact hn
  have hAnn : 0 < A₀ ^ 2 + B₀ ^ 2 := by
    by_contra hn
    have hAz : A₀ = 0 := by nlinarith [sq_nonneg A₀, sq_nonneg B₀]
    have hBz : B₀ = 0 := by nlinarith [sq_nonneg A₀, sq_nonneg B₀]
    exact hamp (by simp [hAz, hBz])
  exact polynomial_scalarMinimizer_annular_limit_capture
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
    h A B α σ A₀ B₀ α₀ σ₀ hh hA hB hα hσ hAnn b ρ hne hs hr hG hmin hρ

end DGPS.Examples.PolynomialSpecies
