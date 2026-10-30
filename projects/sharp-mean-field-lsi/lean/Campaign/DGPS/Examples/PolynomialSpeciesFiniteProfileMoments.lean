import DGPS.Examples.PolynomialSpeciesFiniteProfileMomentCoefficient
import DGPS.Examples.PolynomialSpeciesHalfTurnValue

/-! The actual finite-profile scalar moments, with joint coefficient
regularity and origin jets. These supply compact-uniform Taylor bounds without
prescribing any remainder or differentiating the selected reference root. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

def polynomialFiniteMoment (a b h : ℝ) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, 0))) (polynomialMixedFiniteProfile a b h)
    (e0_STR02955 (polynomialRangeFeature (h, 0)))

def polynomialFiniteGeneratorMoment (a b h : ℝ) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, 0))) (polynomialMixedFiniteProfile a b h)
    (polynomialRangeGenerator (h, 0))

def polynomialFiniteGradientMoment (a b h : ℝ) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, 0))) (polynomialMixedFiniteProfile a b h)
    (polynomialRangeGradientSq (h, 0))

/-- Joint smoothness before any compact coefficient box is chosen. -/
theorem polynomialFiniteMoments_smooth :
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => polynomialFiniteMoment z.1.1 z.1.2 z.2) ∧
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => polynomialFiniteGeneratorMoment z.1.1 z.1.2 z.2) ∧
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => polynomialFiniteGradientMoment z.1.1 z.1.2 z.2) := by
  have hp : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => (z.2, (0 : ℝ))) :=
    contDiff_snd.prodMk contDiff_const
  have hu : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => polynomialMixedFiniteProfile z.1.1 z.1.2 z.2) := by
    unfold polynomialMixedFiniteProfile polynomialOriginMixedSecondCorrection polynomialOriginSecondCorrection
    fun_prop
  obtain ⟨hL, _, _, hφ, hB, hJ⟩ := polynomialRange_data_smooth
  have hlog := e0_STR02955.contDiff.comp (hL.comp hp)
  have hR := rho_smooth_STR02954.comp ((contDiff_const (c := (0 : ℝ))).prodMk (hlog.add (e0_STR02955.contDiff.comp hu)))
  exact ⟨meanCLM_STR02954.contDiff.comp ((e0_STR02955.contDiff.comp (hφ.comp hp)).mul hR),
    meanCLM_STR02954.contDiff.comp ((hB.comp hp).mul hR),
    meanCLM_STR02954.contDiff.comp ((hJ.comp hp).mul hR)⟩

private theorem even_derivative_zero (f : ℝ → ℝ) (he : ∀ t, f (-t) = f t) : deriv f 0 = 0 := by
  have h := congrArg (fun g : ℝ → ℝ => iteratedDeriv 1 g 0) (funext he)
  rw [iteratedDeriv_comp_neg] at h
  norm_num [iteratedDeriv_one] at h
  linarith

private theorem moments_even (a b t : ℝ) :
    polynomialFiniteMoment a b (-t) = polynomialFiniteMoment a b t ∧
      polynomialFiniteGeneratorMoment a b (-t) = polynomialFiniteGeneratorMoment a b t := by
  have hu : ∀ x : ℝ, (polynomialMixedFiniteProfile a b (-t)).val (x + Real.pi) =
      (polynomialMixedFiniteProfile a b t).val x := by
    intro x
    rw [polynomialMixedFiniteProfile_val, polynomialMixedFiniteProfile_val]
    unfold uFun_STR02945 pFun_STR02945 qFun_STR02945
    rw [Real.cos_add_pi, Real.sin_add_pi,
      show 2 * (x + Real.pi) = 2 * x + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.sin_add_two_pi]
    ring
  have hm := polynomialRange_moments_half_turn t 0
    (polynomialMixedFiniteProfile a b t) (polynomialMixedFiniteProfile a b (-t)) hu
  exact ⟨hm.2.2.1, hm.2.2.2.1⟩

/-- Actual zero/first/second jets and the actual zeroth gradient moment. No
jet or feature eigenrelation is an input. -/
theorem polynomialFiniteMoments_origin_jets (a b : ℝ) :
    polynomialFiniteMoment a b 0 = 0 ∧ polynomialFiniteGeneratorMoment a b 0 = 0 ∧
      deriv (polynomialFiniteMoment a b) 0 = 0 ∧
      deriv (polynomialFiniteGeneratorMoment a b) 0 = 0 ∧
      iteratedDeriv 2 (polynomialFiniteMoment a b) 0 = Real.sqrt 2 * (a ^ 2 - b ^ 2) / 12 ∧
      iteratedDeriv 2 (polynomialFiniteGeneratorMoment a b) 0 =
        DGPS.Circle.AngularNormalization.a0 * Real.sqrt 2 * (a ^ 2 - b ^ 2) / 3 ∧
      polynomialFiniteGradientMoment a b 0 = 4 * DGPS.Circle.AngularNormalization.a0 := by
  have hz : polynomialMixedFiniteProfile a b 0 = 0 := by simp [polynomialMixedFiniteProfile]
  have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
  have hm : polynomialFiniteMoment a b 0 = 0 := by
    simp only [polynomialFiniteMoment, hz, hL, map_zero, eulerMean, eulerDensity,
      zero_add, rho_zero_STR02955, mul_one, polynomialOriginFeature_eq,
      polynomialOriginFeature_mean_zero]
  have hB : polynomialFiniteGeneratorMoment a b 0 = 0 := by
    simp only [polynomialFiniteGeneratorMoment, hz, hL, map_zero, eulerMean, eulerDensity,
      zero_add, rho_zero_STR02955, mul_one, polynomialOriginGenerator_eq,
      map_smul, polynomialOriginFeature_mean_zero, smul_zero]
  refine ⟨hm, hB, even_derivative_zero _ (fun t => (moments_even a b t).1),
    even_derivative_zero _ (fun t => (moments_even a b t).2),
    polynomialMixedFiniteProfile_feature_moment_second a b,
    polynomialMixedFiniteProfile_generator_moment_second a b, ?_⟩
  simp only [polynomialFiniteGradientMoment, hz, hL, map_zero, eulerMean, eulerDensity,
    zero_add, rho_zero_STR02955, mul_one]
  exact polynomialOriginGradientSq_mean

end DGPS.Examples.PolynomialSpecies
