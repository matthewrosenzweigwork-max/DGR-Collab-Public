import DGPS.Examples.PolynomialGaussianEndpoint

/-! Fixed-field actual scalar attainment below its genuine Gaussian endpoint.
The strict native rate comparison is retained explicitly until its separate
analytic producer is discharged. No compactness, positive limiting gap or
attainment conclusion is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.PolynomialExactGap
open DGPS.Examples.PolynomialEquilibrium DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem gap_zero_reference (h : ℝ) (ρ : AbsoluteDensity 1)
    (hG : scalarGap (canonical_elementary_polynomial_model h) ρ = 0) :
    ρ.sqrt =ᵐ[haar 1] fun x => Real.sqrt ((polynomialRankOne h).q x) := by
  let A := canonical_elementary_polynomial_model h
  have hreal : densityFreeEnergy A ρ = freeEnergyMinimumReal A := by
    have he := congrArg (fun t : NNReal => (t : ℝ)) hG
    change densityFreeEnergy A ρ - freeEnergyMinimumReal A = 0 at he
    linarith
  have hE : freeEnergy A (densityMeasure ρ) = freeEnergyMinimum A := by
    rw [← coe_densityFreeEnergy, hreal, coe_freeEnergyMinimumReal]
  have hprob := (freeEnergy_eq_min_iff_EX055 h (densityMeasure ρ)).1 hE
  let σ := (polynomialRankOne h).absQ
  have hμ : (densityMeasure ρ : Measure (Torus 1)) = densityMeasure σ := by
    rw [hprob]
    change (polyEq_EX055 h : Measure (Torus 1)) =
      (densityMeasure (polynomialRankOne h).absQ : Measure (Torus 1))
    rw [(polynomialRankOne h).densityMeasure_absQ, polynomialRankOne_reference]
    rfl
  exact AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq ((densityMeasure_eq_iff_STR02901 ρ σ).1 hμ)

/-- The scalar rate on the full original absolute H1 domain is attained at any
fixed physical field where its actual native rate is strictly below the actual
canonical inverse-Hessian Gaussian endpoint. This comparison is an explicit
bridge hypothesis, not an assumed attainment or positive-gap-limit assertion. -/
theorem polynomial_scalar_attainment_of_lt_gaussian (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (hstrict : scalarRate (canonical_elementary_polynomial_model h) b <
      gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu
        (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu)) :
    ∃ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ ∧
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b := by
  classical
  let A := canonical_elementary_polynomial_model h
  let r := scalarRate A b
  obtain ⟨Mq, hMq, hrMq, hMqG⟩ := ENNReal.lt_iff_exists_real_btwn.1 hstrict
  have hrfin : r ≠ ⊤ := (hrMq.trans_le le_top).ne
  have hex : ∀ n : ℕ, ∃ ρ : AbsoluteDensity 1, 0 < scalarGap A ρ ∧
      scalarQuotient A b ρ < min (ENNReal.ofReal Mq) (r + ((n : ℝ≥0∞) + 1)⁻¹) := by
    intro n
    have ht : r < min (ENNReal.ofReal Mq) (r + ((n : ℝ≥0∞) + 1)⁻¹) :=
      lt_min hrMq (ENNReal.lt_add_right hrfin (by simp))
    change (⨅ ρ : {ρ : AbsoluteDensity 1 // 0 < scalarGap A ρ}, scalarQuotient A b ρ.1) < _ at ht
    obtain ⟨⟨ρ, hρ⟩, hq⟩ := iInf_lt_iff.1 ht
    exact ⟨ρ, hρ, hq⟩
  choose ρ hpos hq using hex
  have hQ : ∀ n, scalarQuotient A b (ρ n) ≤ ENNReal.ofReal Mq :=
    fun n => (lt_min_iff.mp (hq n)).1.le
  have hδ : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have ht := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    refine ht.congr (fun n => ?_)
    simp [Function.comp]
  have hupper : Tendsto (fun n : ℕ => r + ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add hδ
  have hQconv : Tendsto (fun n => scalarQuotient A b (ρ n)) atTop (𝓝 r) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => scalarRate_le_quotient A b (ρ n) (hpos n))
      (fun n => (lt_min_iff.mp (hq n)).2.le)
  obtain ⟨B, hB, hBn, φ, ρL, η, R, hφ, hη, hae, hub, hRL, hH, hweak, hGconv, hDlsc⟩ :=
    polynomial_scalar_sublevel_compactness h Mq hMq b ρ hpos hQ
  have hGpos : 0 < scalarGap A ρL := by
    by_contra hn
    have hz : scalarGap A ρL = 0 := le_antisymm (not_lt.mp hn) zero_le
    have hroot := gap_zero_reference h ρL hz
    have haref : ∀ n, ∀ᵐ x ∂haar 1,
        |(ρ (φ n)).sqrt x - Real.sqrt ((polynomialRankOne h).q x)| ≤ η n := by
      intro n
      filter_upwards [hae n, hroot] with x hx hr
      rwa [hr] at hx
    have he := polynomial_scalar_gaussian_endpoint_lower_limit h b (fun n => ρ (φ n)) η hη haref
      (fun n => hpos (φ n)) ⟨ENNReal.ofReal Mq, ENNReal.ofReal_ne_top, fun n => hQ (φ n)⟩
    have hlim : liminf (fun n => scalarQuotient (canonical_elementary_polynomial_model h) b
        (ρ (φ n))) atTop = r := by
      simpa only [Function.comp_def] using (hQconv.comp hφ.tendsto_atTop).liminf_eq
    rw [hlim] at he
    exact not_le_of_gt hstrict he
  have hprod : Tendsto (fun n => scalarQuotient A b (ρ (φ n)) *
      (2 * (scalarGap A (ρ (φ n)) : ℝ≥0∞))) atTop
      (𝓝 (r * (2 * (scalarGap A ρL : ℝ≥0∞)))) :=
    ENNReal.Tendsto.mul (hQconv.comp hφ.tendsto_atTop)
      (Or.inr (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top))
      (ENNReal.Tendsto.const_mul hGconv (Or.inr (by norm_num))) (Or.inr hrfin)
  have hN (n : ℕ) : scalarDissipation A b (ρ (φ n)) ≤ scalarQuotient A b (ρ (φ n)) *
      (2 * (scalarGap A (ρ (φ n)) : ℝ≥0∞)) := by
    have hden0 : 2 * (scalarGap A (ρ (φ n)) : ℝ≥0∞) ≠ 0 :=
      mul_ne_zero (by norm_num) (by exact_mod_cast (hpos (φ n)).ne')
    have hdent : 2 * (scalarGap A (ρ (φ n)) : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
    exact (ENNReal.div_le_iff hden0 hdent).1 le_rfl
  have hDlim : scalarDissipation A b ρL ≤ r * (2 * (scalarGap A ρL : ℝ≥0∞)) := by
    refine hDlsc.trans ?_
    calc
      _ ≤ liminf (fun n => scalarQuotient A b (ρ (φ n)) *
          (2 * (scalarGap A (ρ (φ n)) : ℝ≥0∞))) atTop :=
            liminf_le_liminf (Eventually.of_forall hN)
      _ = _ := hprod.liminf_eq
  have hQlim : scalarQuotient A b ρL ≤ r := ENNReal.div_le_of_le_mul hDlim
  exact ⟨ρL, hGpos, le_antisymm hQlim (scalarRate_le_quotient A b ρL hGpos)⟩

end DGPS.Examples.PolynomialSpecies
