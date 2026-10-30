import DGPS.Examples.PolynomialScalarCompactness
import DGPS.Variational.LocalGaussianEndpoint
import DGPS.Lipschitz.GaussianKernelTilt
import DGPS.Foundations.CircleRegularity
import DGPS.Frontier.STR029.T01

/-! Exact canonical polynomial Gaussian endpoint and the original-domain
representative adapter for the existing positive-rank-one endpoint theorem.
The constant one-body gauge and the full original variational domain are retained. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.PolynomialExactGap
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- The actual canonical model and its proved rank-one representation have
the same inverse-Hessian rate on exactly the same moving reference. -/
theorem polynomial_gaussianRate_rankOne_eq (h : ℝ)
    (hH : IsCoerciveDensityHessian (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu) :
    gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu hH =
      gaussianRate (polynomialRankOne h).data (polynomialRankOne h).lgeMu
        (DGPS.LocalGaussianEndpoint.coercive (polynomialRankOne h)) := by
  let M := polynomialRankOne h
  let A := canonical_elementary_polynomial_model h
  let μ := M.lgeMu
  let hB := DGPS.LocalGaussianEndpoint.coercive M
  have hW : M.data.W = A.W := funext fun x => funext fun y => polynomialRankOne_W h x y
  have hK (x y : Torus 1) : centeredKernel A μ x y = centeredKernel M.data μ x y := by
    simp only [centeredKernel, interactionConvolution, meanInteraction, ← hW]
  have hHess := DGPS.Lipschitz.densityHessian_congr_LIP016 A M.data μ hK
  have hcov : densityCovariance A μ hH = densityCovariance M.data μ hB := by
    apply ContinuousLinearMap.ext
    intro f
    calc
      densityCovariance A μ hH f = densityCovariance A μ hH
          (densityHessian M.data μ (densityCovariance M.data μ hB f)) := by
        rw [densityHessian_densityCovariance]
      _ = densityCovariance M.data μ hB f := by
        rw [← hHess, densityCovariance_densityHessian]
  unfold gaussianRate gaussianQuotient gaussianDenominator
  rw [hcov]

/-- Replacing an original absolute density by another representative of the
same probability preserves its actual scalar gap, dissipation and quotient. -/
theorem polynomial_scalar_measure_congr (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ σ : AbsoluteDensity 1)
    (hμ : (densityMeasure ρ : Measure (Torus 1)) = (densityMeasure σ : Measure (Torus 1))) :
    scalarGap (canonical_elementary_polynomial_model h) ρ = scalarGap (canonical_elementary_polynomial_model h) σ ∧
    scalarDissipation (canonical_elementary_polynomial_model h) b ρ =
      scalarDissipation (canonical_elementary_polynomial_model h) b σ ∧
    scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarQuotient (canonical_elementary_polynomial_model h) b σ := by
  let A := canonical_elementary_polynomial_model h
  have hprob : densityMeasure ρ = densityMeasure σ := Subtype.ext hμ
  have hg : scalarGap A ρ = scalarGap A σ := by
    apply NNReal.coe_injective
    change densityFreeEnergy A ρ - freeEnergyMinimumReal A = densityFreeEnergy A σ - freeEnergyMinimumReal A
    congr 1
    apply EReal.coe_injective
    rw [coe_densityFreeEnergy, coe_densityFreeEnergy, hprob]
  have hdreal : (scalarDissipation A b ρ).toReal = (scalarDissipation A b σ).toReal := by
    have hρ := (polynomial_family_gap_and_dissipation h b (SpeciesFamily.single ρ)).2.2.2
    have hσ := (polynomial_family_gap_and_dissipation h b (SpeciesFamily.single σ)).2.2.2
    simp only [speciesDissipation_single, densityMeasure_barycenter_single, sum_single_count,
      SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul] at hρ hσ
    rw [hρ, hσ, hμ]
  have hfin (τ : AbsoluteDensity 1) : scalarDissipation A b τ ≠ ⊤ := by
    simpa only [speciesDissipation_single] using
      (polynomial_family_gap_and_dissipation h b (SpeciesFamily.single τ)).2.2.1
  have hd : scalarDissipation A b ρ = scalarDissipation A b σ := by
    rw [← ENNReal.ofReal_toReal (hfin ρ), ← ENNReal.ofReal_toReal (hfin σ), hdreal]
  exact ⟨hg, hd, by unfold scalarQuotient; rw [hg, hd]⟩

private theorem continuous_ae_bound (f g : Torus 1 → ℝ) (hf : Continuous f) (hg : Continuous g)
    (a : ℝ) (ha : ∀ᵐ x ∂haar 1, |f x - g x| ≤ a) : ∀ x, |f x - g x| ≤ a := by
  have hc := (hf.sub hg).abs
  have he : (fun x => |f x - g x|) = fun x => min |f x - g x| a :=
    Measure.eq_of_ae_eq (ha.mono fun x hx => (min_eq_left hx).symm) hc (hc.min continuous_const)
  intro x
  rw [congrFun he x]
  exact min_le_right _ _

private theorem continuous_absolute_rep (ρ : AbsoluteDensity 1) :
    ∃ σ : AbsoluteDensity 1, Continuous σ.sqrt ∧ σ.sqrt =ᵐ[haar 1] ρ.sqrt := by
  let G := weakGradient ρ.sqrt ρ.sqrt_mem
  have hG := isWeakGradient_weakGradient ρ.sqrt_mem
  obtain ⟨v, hv, hae, _, _⟩ := circle_H1_holder_half hG
  let σ : AbsoluteDensity 1 := {
    sqrt := v
    sqrt_mem := by
      rw [mem_H1Haar]
      exact ⟨G, hG.congr_ae hae.symm (EventuallyEq.refl _ _)⟩
    sqrt_nonneg := by filter_upwards [hae, ρ.sqrt_nonneg] with x hx hp; rwa [hx]
    mass_one := by
      calc
        (∫ x, v x ^ 2 ∂haar 1) = ∫ x, ρ.sqrt x ^ 2 ∂haar 1 :=
          integral_congr_ae (hae.mono fun x hx => congrArg (fun t : ℝ => t ^ 2) hx)
        _ = 1 := ρ.mass_one }
  exact ⟨σ, hv, hae⟩

/-- Actual canonical Gaussian endpoint lower limit on the full original
absolute domain. Only factual a.e.-uniform convergence of original roots to
the actual reference root is required; pointwise representative convergence
is derived internally before applying the existing rank-one endpoint theorem. -/
theorem polynomial_scalar_gaussian_endpoint_lower_limit (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (ρ : ℕ → AbsoluteDensity 1) (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - Real.sqrt ((polynomialRankOne h).q x)| ≤ η n)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model h) (ρ n))
    (hQ : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, scalarQuotient (canonical_elementary_polynomial_model h) b (ρ n) ≤ C) :
    gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu
      (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu) ≤
      liminf (fun n => scalarQuotient (canonical_elementary_polynomial_model h) b (ρ n)) atTop := by
  classical
  let M := polynomialRankOne h
  let A := canonical_elementary_polynomial_model h
  choose σ hc hs using fun n => continuous_absolute_rep (ρ n)
  have hμ (n : ℕ) : (densityMeasure (σ n) : Measure (Torus 1)) = densityMeasure (ρ n) := by
    apply (densityMeasure_eq_iff_STR02901 _ _).2
    exact (hs n).mono fun x hx => congrArg (fun t : ℝ => t ^ 2) hx
  have hq (n : ℕ) : scalarQuotient M.data (polynomialRankOneDrift h b) (σ n) = scalarQuotient A b (ρ n) := by
    have hg := polynomialRankOne_speciesGap h (SpeciesFamily.single (σ n))
    have hd := polynomialRankOne_speciesDissipation h b (SpeciesFamily.single (σ n))
    simp only [speciesGap_single] at hg
    simp only [speciesDissipation_single] at hd
    unfold scalarQuotient
    rw [hg, hd, (polynomial_scalar_measure_congr h b (σ n) (ρ n) (hμ n)).1,
      (polynomial_scalar_measure_congr h b (σ n) (ρ n) (hμ n)).2.1]
  have hpos (n : ℕ) : 0 < speciesGap M.data (SpeciesFamily.single (σ n)) := by
    rw [polynomialRankOne_speciesGap, speciesGap_single,
      (polynomial_scalar_measure_congr h b (σ n) (ρ n) (hμ n)).1]
    exact hG n
  have hb (n : ℕ) (x : Torus 1) : |(σ n).sqrt x - Real.sqrt (M.q x)| ≤ η n := by
    apply continuous_ae_bound _ _ (hc n) M.q_cont.sqrt (η n)
    filter_upwards [hs n, hae n] with x hx hp
    rwa [hx]
  have hU : TendstoUniformly (fun n x => (σ n).sqrt x) (fun x => Real.sqrt (M.q x)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro e he
    filter_upwards [hη.eventually (gt_mem_nhds he)] with n hn x
    have he := (hb n x).trans_lt hn
    simpa only [Real.dist_eq, abs_sub_comm] using he
  have hbd : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n,
      speciesQuotient M.data (polynomialRankOneDrift h b) (SpeciesFamily.single (σ n)) ≤ C := by
    obtain ⟨C, hC, hbound⟩ := hQ
    refine ⟨C, hC, fun n => ?_⟩
    simpa only [speciesQuotient_single, hq] using hbound n
  have he := DGPS.Examples.local_positive_rank_one_gaussian_endpoint_lower_limit M
    (polynomialRankOneDrift h b) σ hU hpos hbd
  rw [← polynomial_gaussianRate_rankOne_eq h (densityHessian_coercive_EX055 h M.lgeMu)] at he
  simpa only [speciesQuotient_single, hq] using he

end DGPS.Examples.PolynomialSpecies
