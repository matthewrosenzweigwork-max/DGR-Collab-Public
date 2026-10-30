import DGPS.Examples.PolynomialSpeciesReflectionGraph
import DGPS.Examples.PolynomialSpeciesRangeGap
import DGPS.Examples.PolynomialChartCriticality

/-! Same-field reflection preserves genuine original-domain scalar optimizers.
The transfer uses exact physical gaps and finite dissipations, not criticality
alone. AE chart representatives are handled before passing to the reflected law. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
namespace DGPS.Examples.PolynomialSpecies

/-- Gap and quotient depend on the original probability law, not the stored
choice of an almost-everywhere density representative. -/
theorem polynomial_same_density_gap_quotient (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (ρ τ : AbsoluteDensity 1) (hae : ρ.density =ᵐ[haar 1] τ.density) :
    scalarGap (canonical_elementary_polynomial_model h) ρ =
      scalarGap (canonical_elementary_polynomial_model h) τ ∧
    scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarQuotient (canonical_elementary_polynomial_model h) b τ := by
  have hμ : (densityMeasure ρ : Measure (Torus 1)) = densityMeasure τ :=
    (densityMeasure_eq_iff_STR02901 _ _).2 hae
  have hprob : densityMeasure ρ = densityMeasure τ := Subtype.ext hμ
  have hGap : scalarGap (canonical_elementary_polynomial_model h) ρ =
      scalarGap (canonical_elementary_polynomial_model h) τ := by
    apply NNReal.coe_injective
    change densityFreeEnergy _ ρ - freeEnergyMinimumReal _ = densityFreeEnergy _ τ - freeEnergyMinimumReal _
    congr 1
    apply EReal.coe_injective
    rw [coe_densityFreeEnergy, coe_densityFreeEnergy, hprob]
  have hfin (κ : AbsoluteDensity 1) : scalarDissipation (canonical_elementary_polynomial_model h) b κ ≠ ⊤ := by
    have hi := (polynomial_family_gap_and_dissipation h b (SpeciesFamily.single κ)).2.2.1
    simpa only [speciesDissipation_single] using hi
  have hdreal : (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal =
      (scalarDissipation (canonical_elementary_polynomial_model h) b τ).toReal := by
    have he : polynomialVariationalDeficit h 0 ρ = polynomialVariationalDeficit h 0 τ := by
      unfold polynomialVariationalDeficit
      rw [hμ]
    rw [polynomialVariationalDeficit_eq h 0 b ρ, polynomialVariationalDeficit_eq h 0 b τ] at he
    simpa only [mul_zero, zero_mul, sub_zero] using he
  have hd : scalarDissipation (canonical_elementary_polynomial_model h) b ρ =
      scalarDissipation (canonical_elementary_polynomial_model h) b τ := by
    calc
      _ = ENNReal.ofReal (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal :=
        (ENNReal.ofReal_toReal (hfin ρ)).symm
      _ = _ := congrArg ENNReal.ofReal hdreal
      _ = _ := ENNReal.ofReal_toReal (hfin τ)
  refine ⟨hGap, ?_⟩
  unfold scalarQuotient
  rw [hGap, hd]

/-- Reflection of a literal retained chart profile preserves its physical gap
and quotient at the SAME field and for the supplied original absolute drift. -/
theorem polynomial_reflected_chart_gap_quotient (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (u v : PeriodicC2_STR02969) (huv : ∀ t : ℝ, v.val (-t) = u.val t) :
    scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h v) =
      scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h u) ∧
    scalarQuotient (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h v) =
      scalarQuotient (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h u) := by
  obtain ⟨hH, _hI, hm, _hA, _hJ⟩ := polynomialRange_moments_reflection h (root_EX054 h) u v huv
  have hgRange : polynomialRangeGap (h, root_EX054 h) v = polynomialRangeGap (h, root_EX054 h) u := by
    unfold polynomialRangeGap
    dsimp only
    rw [hH, hm]
  have hGap : scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h v) =
      scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h u) := by
    apply NNReal.coe_injective
    rw [polynomialChartAbsolute_gap_eq_rangeGap h b v, polynomialChartAbsolute_gap_eq_rangeGap h b u]
    exact hgRange
  have hdreal : (scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h v)).toReal =
      (scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h u)).toReal := by
    have he := polynomialRangeDeficit_reflection h (root_EX054 h) 0 u v huv
    rw [polynomialRangeDeficit_actual, polynomialRangeDeficit_actual,
      ← polynomialChartAbsolute_deficit h 0 b v, ← polynomialChartAbsolute_deficit h 0 b u] at he
    simpa only [mul_zero, zero_mul, sub_zero] using he
  have hfin (w : PeriodicC2_STR02969) :
      scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h w) ≠ ⊤ :=
    (polynomialChartAbsolute_gap_and_dissipation h b w).2.1
  have hd : scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h v) =
      scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h u) := by
    calc
      _ = ENNReal.ofReal (scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h v)).toReal :=
        (ENNReal.ofReal_toReal (hfin v)).symm
      _ = _ := congrArg ENNReal.ofReal hdreal
      _ = _ := ENNReal.ofReal_toReal (hfin u)
  refine ⟨hGap, ?_⟩
  unfold scalarQuotient
  rw [hGap, hd]

/-- The reflected chart of ANY original minimizer is again an original-domain
positive-gap minimizer. In particular an IFT branch need not be declared a
minimizer merely because it solves its critical equations. -/
theorem polynomial_scalarMinimizer_reflected_chart (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b)
    (u v : PeriodicC2_STR02969)
    (hρ : ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h u).density)
    (huv : ∀ t : ℝ, v.val (-t) = u.val t) :
    0 < scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h v) ∧
    scalarQuotient (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h v) =
      scalarRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨hg, hq⟩ := polynomial_same_density_gap_quotient h b ρ (polynomialChartAbsolute h u) hρ
  obtain ⟨hgr, hqr⟩ := polynomial_reflected_chart_gap_quotient h b u v huv
  exact ⟨by rw [hgr, ← hg]; exact hG, hqr.trans (hq.symm.trans hmin)⟩

end DGPS.Examples.PolynomialSpecies
