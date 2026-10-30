import DGPS.Examples.PolynomialLogChart
import DGPS.Examples.PolynomialDeficitVariation
import DGPS.Examples.PolynomialSpeciesEulerStrong
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Genuine criticality in the actual retained chart, obtained from the global
original-domain variational minimum. The density dictionary is used before
Fermat's theorem; no Euler or chart-stationarity premise occurs. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.PositiveRankOne DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- An actual minimizer represented by the same chart is a true minimum of
its full polynomial deficit on the entire retained C2 chart space. -/
theorem polynomial_scalarMinimizer_chart_fderiv_zero (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b)
    (u : PeriodicC2_STR02969)
    (hu : ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h u).density) :
    fderiv ℝ (polynomialChartDeficit h (scalarRate (canonical_elementary_polynomial_model h) b).toReal) u = 0 := by
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  obtain ⟨hz, hn⟩ := polynomial_minimizer_deficit_zero_and_nonnegative h b ρ hG hmin
  have hμ : (densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1)) =
      (densityMeasure ρ : Measure (Torus 1)) :=
    (densityMeasure_eq_iff_STR02901 _ _).2 hu.symm
  have hvar : polynomialVariationalDeficit h r (polynomialChartAbsolute h u) =
      polynomialVariationalDeficit h r ρ := by
    unfold polynomialVariationalDeficit
    rw [hμ]
  have hzero : polynomialChartDeficit h r u = 0 := by
    rw [← polynomialChartAbsolute_deficit h r b u,
      ← polynomialVariationalDeficit_eq h r b (polynomialChartAbsolute h u),
      hvar, polynomialVariationalDeficit_eq h r b ρ]
    exact hz
  have hlocal : IsLocalMin (polynomialChartDeficit h r) u := by
    apply Eventually.of_forall
    intro v
    rw [hzero, ← polynomialChartAbsolute_deficit h r b v]
    exact hn (polynomialChartAbsolute h v)
  exact hlocal.fderiv_eq_zero

/-- Every actual original-domain minimizer sequence has the same centered
vanishing chart representatives and their full, genuine first variations
vanish in every retained C2 direction. -/
theorem polynomial_scalarMinimizer_critical_chart_capture (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) :
    ∃ φ : ℕ → ℕ, ∃ u : ℕ → PeriodicC2_STR02969, StrictMono φ ∧
      (∀ n, meanT_STR02901 (u n).val = 0) ∧
      (∀ n, (ρ (φ n)).density =ᵐ[haar 1] (polynomialChartAbsolute (h (φ n)) (u n)).density) ∧
      Tendsto (fun n => ‖u n‖) atTop (𝓝 0) ∧
      (∀ n v, polynomialEuler (h (φ n))
        (scalarRate (canonical_elementary_polynomial_model (h (φ n))) (b (φ n))).toReal (u n) v = 0) := by
  obtain ⟨φ, u, hφ, hm, hd, hn⟩ :=
    polynomial_scalarMinimizer_centered_chart_capture h hh b ρ hG hmin
  refine ⟨φ, u, hφ, hm, hd, hn, fun n v => ?_⟩
  have hf := polynomial_scalarMinimizer_chart_fderiv_zero (h (φ n)) (b (φ n)) (ρ (φ n))
    (hG (φ n)) (hmin (φ n)) (u n) (hd n)
  have he := congrArg (fun L : PeriodicC2_STR02969 →L[ℝ] ℝ => L v) hf
  rw [polynomialChartDeficit_fderiv] at he
  simpa only [ContinuousLinearMap.zero_apply] using he

end DGPS.Examples.PolynomialSpecies
