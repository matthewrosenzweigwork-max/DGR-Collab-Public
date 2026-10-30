import DGPS.Examples.PolynomialSpeciesDescentBridge
import DGPS.Variational.SpeciesInclusion

/-! Actual variational deficit at an original-domain polynomial scalar
minimizer. Finiteness is derived from the genuine full-domain family identity
before converting the rate and dissipation to real numbers. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
open DGPS.PositiveRankOne

namespace DGPS.Examples.PolynomialSpecies

/-- Every actual original-H1 scalar minimizer has zero deficit, while its
actual scalar rate gives a nonnegative deficit on EVERY original competitor,
including zero-gap competitors. No stationarity or Euler premise occurs. -/
theorem polynomial_minimizer_deficit_zero_and_nonnegative (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b) :
    let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
    (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal -
      2 * r * (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) = 0 ∧
    ∀ τ : AbsoluteDensity 1,
      0 ≤ (scalarDissipation (canonical_elementary_polynomial_model h) b τ).toReal -
        2 * r * (scalarGap (canonical_elementary_polynomial_model h) τ : ℝ) := by
  let A := canonical_elementary_polynomial_model h
  let r := (scalarRate A b).toReal
  have hDfin (τ : AbsoluteDensity 1) : scalarDissipation A b τ ≠ ⊤ := by
    have hi := (polynomial_family_gap_and_dissipation h b (SpeciesFamily.single τ)).2.2.1
    simpa only [speciesDissipation_single] using hi
  have hratefin : scalarRate A b ≠ ⊤ := by
    rw [← hmin]
    unfold scalarQuotient
    exact ENNReal.div_ne_top (hDfin ρ) (mul_ne_zero (by norm_num) (by exact_mod_cast hG.ne'))
  have hq := congrArg ENNReal.toReal hmin
  unfold scalarQuotient at hq
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] at hq
  have hGr : (0 : ℝ) < scalarGap A ρ := by exact_mod_cast hG
  have hz : (scalarDissipation A b ρ).toReal - 2 * r * (scalarGap A ρ : ℝ) = 0 := by
    have he := (div_eq_iff (by positivity : 2 * (scalarGap A ρ : ℝ) ≠ 0)).1 hq
    change _ = r * _ at he
    nlinarith
  refine ⟨hz, fun τ => ?_⟩
  by_cases hp : 0 < scalarGap A τ
  · have hQt : scalarQuotient A b τ ≠ ⊤ :=
      ENNReal.div_ne_top (hDfin τ) (mul_ne_zero (by norm_num) (by exact_mod_cast hp.ne'))
    have hr := ENNReal.toReal_mono hQt (scalarRate_le_quotient A b τ hp)
    unfold scalarQuotient at hr
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] at hr
    have hpr : (0 : ℝ) < scalarGap A τ := by exact_mod_cast hp
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (scalarGap A τ : ℝ))).1 hr
    change r * _ ≤ _ at hm
    nlinarith
  · have he : scalarGap A τ = 0 := le_antisymm (not_lt.mp hp) zero_le
    rw [he, NNReal.coe_zero, mul_zero, sub_zero]
    exact ENNReal.toReal_nonneg

end DGPS.Examples.PolynomialSpecies
