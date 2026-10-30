import DGPS.Examples.PolynomialSpeciesMixedFirstJets

/-! Second mixed derivative of the actual nonlocal Euler potential. Changing
feature, generator and gradient-square fields are retained in every product;
only their actual origin values survive the proved zero first scalar jets. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem scalar_product_second (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) :
    iteratedDeriv 2 (fun t => f t * g t) 0 = iteratedDeriv 2 f 0 * g 0 := by
  rw [iteratedDeriv_fun_mul ((hf.of_le (by simp)).contDiffAt) ((hg.of_le (by simp)).contDiffAt)]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, hf0, hf1]

private theorem scalar_field_second (f : ℝ → ℝ) (F : ℝ → PeriodicHolder_STR02968)
    (hf : ContDiff ℝ ∞ f) (hF : ContDiff ℝ ∞ F) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) :
    iteratedDeriv 2 (fun t => f t • F t) 0 = iteratedDeriv 2 f 0 • F 0 := by
  have hd := iteratedDerivWithin_smul (n := 2) (Set.mem_univ (0 : ℝ)) uniqueDiffOn_univ
    (((hf.of_le (by simp)).contDiffAt).contDiffWithinAt)
    (((hF.of_le (by simp)).contDiffAt).contDiffWithinAt)
  simp only [iteratedDerivWithin_univ] at hd
  change iteratedDeriv 2 (fun t : ℝ => f t • F t) 0 = _ at hd
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, hf0, hf1] using hd

private theorem expectation_smooth (a b : ℝ) (F : (ℝ × ℝ) → PeriodicHolder_STR02968)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fun t : ℝ =>
      eulerMean (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
        (t • (a • cosC2_STR02915 + b • sinC2_STR02915)) (F (t, 0))) := by
  have hp : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  have hu : ContDiff ℝ ∞ (fun t : ℝ => t • (a • cosC2_STR02915 + b • sinC2_STR02915)) :=
    contDiff_id.smul contDiff_const
  have hR : ContDiff ℝ ∞ (fun t : ℝ => rho_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (t, 0)) + e0_STR02955 (t • (a • cosC2_STR02915 + b • sinC2_STR02915)))) := rho_smooth_STR02954.comp (contDiff_const.prodMk
    ((e0_STR02955.contDiff.comp (polynomialRange_data_smooth.1.comp hp)).add (e0_STR02955.contDiff.comp hu)))
  exact meanCLM_STR02954.contDiff.comp ((hF.comp hp).mul hR)

/-- The true nonlocal part of the mixed Euler potential at physical rate a0. -/
def polynomialMixedNonlocalPotential (a b t : ℝ) : PeriodicHolder_STR02968 :=
  let m := polynomialMixedFeatureMoment a b t
  let A := polynomialMixedGeneratorMoment a b t
  let J := eulerMean (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
    (t • (a • cosC2_STR02915 + b • sinC2_STR02915)) (polynomialRangeGradientSq (t, 0))
  (2 * eta * (A + eta * (m * J) - DGPS.Circle.AngularNormalization.a0 * m)) •
      e0_STR02955 (polynomialRangeFeature (t, 0)) +
    (2 * eta * m) • polynomialRangeGenerator (t, 0) +
    (eta ^ 2 * (m * m)) • polynomialRangeGradientSq (t, 0)

/-- The actual changing nonlocal fields contribute the displayed second jet.
No scalar/field jet is supplied as a hypothesis; all come from actual model
centering, normalized expectations and the genuine mixed generator derivative. -/
theorem polynomialMixedNonlocalPotential_jets (a b : ℝ) :
    polynomialMixedNonlocalPotential a b 0 = 0 ∧
      deriv (polynomialMixedNonlocalPotential a b) 0 = 0 ∧
      iteratedDeriv 2 (polynomialMixedNonlocalPotential a b) 0 =
      (6 * DGPS.Circle.AngularNormalization.a0 *
        (Real.sqrt 2 * ((a ^ 2 - b ^ 2) / 4 + a / 6))) • e0_STR02955 polynomialOriginMode := by
  let m := polynomialMixedFeatureMoment a b
  let A := polynomialMixedGeneratorMoment a b
  let φ := fun t : ℝ => e0_STR02955 (polynomialRangeFeature (t, 0))
  let B := fun t : ℝ => polynomialRangeGenerator (t, 0)
  let j := fun t : ℝ => polynomialRangeGradientSq (t, 0)
  let J := fun t : ℝ => eulerMean (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
    (t • (a • cosC2_STR02915 + b • sinC2_STR02915)) (j t)
  let c := fun t : ℝ => 2 * eta * (A t + eta * (m t * J t) - DGPS.Circle.AngularNormalization.a0 * m t)
  let d := fun t : ℝ => 2 * eta * m t
  let e := fun t : ℝ => eta ^ 2 * (m t * m t)
  have hp : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  have hm : ContDiff ℝ ∞ m := expectation_smooth a b _
    (e0_STR02955.contDiff.comp polynomialRange_data_smooth.2.2.2.1)
  have hA : ContDiff ℝ ∞ A := expectation_smooth a b _ polynomialRange_data_smooth.2.2.2.2.1
  have hJ : ContDiff ℝ ∞ J := expectation_smooth a b _ polynomialRange_data_smooth.2.2.2.2.2
  have hφ : ContDiff ℝ ∞ φ := (e0_STR02955.contDiff.comp polynomialRange_data_smooth.2.2.2.1).comp hp
  have hB : ContDiff ℝ ∞ B := polynomialRange_data_smooth.2.2.2.2.1.comp hp
  have hj : ContDiff ℝ ∞ j := polynomialRange_data_smooth.2.2.2.2.2.comp hp
  obtain ⟨hm0, hA0, hm1, hA1⟩ := polynomialMixedMoments_zero_and_first a b
  change m 0 = 0 at hm0
  change A 0 = 0 at hA0
  change deriv m 0 = 0 at hm1
  change deriv A 0 = 0 at hA1
  have hc : ContDiff ℝ ∞ c := contDiff_const.mul
    ((hA.add (contDiff_const.mul (hm.mul hJ))).sub (contDiff_const.mul hm))
  have hd : ContDiff ℝ ∞ d := contDiff_const.mul hm
  have he : ContDiff ℝ ∞ e := contDiff_const.mul (hm.mul hm)
  have hc0 : c 0 = 0 := by simp only [c, hA0, hm0, zero_mul, mul_zero, add_zero, sub_zero]
  have hd0 : d 0 = 0 := by simp only [d, hm0, mul_zero]
  have he0 : e 0 = 0 := by simp only [Pi.mul_def, e, hm0, zero_mul, mul_zero]
  have hmD : HasDerivAt m 0 0 := (hm.differentiable (by simp) 0).hasDerivAt.congr_deriv hm1
  have hAD : HasDerivAt A 0 0 := (hA.differentiable (by simp) 0).hasDerivAt.congr_deriv hA1
  have hJD := (hJ.differentiable (by simp) 0).hasDerivAt
  have hc1 : deriv c 0 = 0 := by
    have hh := ((hAD.add ((hmD.mul hJD).const_mul eta)).sub
      (hmD.const_mul DGPS.Circle.AngularNormalization.a0)).const_mul (2 * eta)
    change HasDerivAt c _ 0 at hh
    simpa only [hm0, zero_mul, mul_zero, zero_add, sub_zero] using hh.deriv
  have hd1 : deriv d 0 = 0 := by
    simpa only [d, mul_zero] using (hmD.const_mul (2 * eta)).deriv
  have he1 : deriv e 0 = 0 := by
    simpa only [Pi.mul_def, e, hm0, zero_mul, mul_zero, zero_add] using ((hmD.mul hmD).const_mul (eta ^ 2)).deriv
  have hJ0 : J 0 = 4 * DGPS.Circle.AngularNormalization.a0 := by
    simpa only [J, j, eulerMean, eulerDensity, zero_smul, map_zero, add_zero,
      show polynomialRangeLogWeight (0, 0) = 0 by simp [polynomialRangeLogWeight],
      zero_add, rho_zero_STR02955, mul_one] using polynomialOriginGradientSq_mean
  have hφ0 : φ 0 = e0_STR02955 polynomialOriginMode := congrArg e0_STR02955 polynomialOriginFeature_eq
  have hB0 : B 0 = (4 * DGPS.Circle.AngularNormalization.a0) • e0_STR02955 polynomialOriginMode :=
    polynomialOriginGenerator_eq
  have hm2 := polynomialMixedFeatureMoment_second a b
  change iteratedDeriv 2 m 0 = _ at hm2
  have hA2 := polynomialMixedGeneratorMoment_second a b
  change iteratedDeriv 2 A 0 = 4 * DGPS.Circle.AngularNormalization.a0 * iteratedDeriv 2 m 0 at hA2
  have hmJ2 := scalar_product_second m J hm hJ hm0 hm1
  have hmm2 := scalar_product_second m m hm hm hm0 hm1
  have hc2 : iteratedDeriv 2 c 0 = 2 * eta *
      (4 * DGPS.Circle.AngularNormalization.a0 + 4 * eta * DGPS.Circle.AngularNormalization.a0 -
        DGPS.Circle.AngularNormalization.a0) * iteratedDeriv 2 m 0 := by
    rw [show c = fun t => 2 * eta * (A t + eta * (m t * J t) - DGPS.Circle.AngularNormalization.a0 * m t) from rfl,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_sub ((hA.add (contDiff_const.mul (hm.mul hJ))).of_le (by simp)).contDiffAt
        ((contDiff_const.mul hm).of_le (by simp)).contDiffAt,
      iteratedDeriv_fun_add (hA.of_le (by simp)).contDiffAt
        ((contDiff_const.mul (hm.mul hJ)).of_le (by simp)).contDiffAt,
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, hA2, hmJ2, hJ0]
    ring
  have hd2 : iteratedDeriv 2 d 0 = 2 * eta * iteratedDeriv 2 m 0 := by
    exact iteratedDeriv_const_mul_field _ _
  have he2 : iteratedDeriv 2 e 0 = 0 := by
    rw [show e = fun t => eta ^ 2 * (m t * m t) from rfl, iteratedDeriv_const_mul_field, hmm2, hm0]
    ring
  have hfun : polynomialMixedNonlocalPotential a b = fun t => c t • φ t + d t • B t + e t • j t := rfl
  have hzero : polynomialMixedNonlocalPotential a b 0 = 0 := by
    rw [hfun]
    simp only [hc0, hd0, he0, zero_smul, zero_add]
  have hfirst : deriv (polynomialMixedNonlocalPotential a b) 0 = 0 := by
    have hcφ : HasDerivAt (fun t : ℝ => c t • φ t) 0 0 := by
      have hh := (hc.differentiable (by simp) 0).hasDerivAt.smul
        (hφ.differentiable (by simp) 0).hasDerivAt
      change HasDerivAt (fun t : ℝ => c t • φ t) _ 0 at hh
      simpa only [hc0, hc1, zero_smul, zero_add] using hh
    have hdB : HasDerivAt (fun t : ℝ => d t • B t) 0 0 := by
      have hh := (hd.differentiable (by simp) 0).hasDerivAt.smul
        (hB.differentiable (by simp) 0).hasDerivAt
      change HasDerivAt (fun t : ℝ => d t • B t) _ 0 at hh
      simpa only [hd0, hd1, zero_smul, zero_add] using hh
    have hej : HasDerivAt (fun t : ℝ => e t • j t) 0 0 := by
      have hh := (he.differentiable (by simp) 0).hasDerivAt.smul
        (hj.differentiable (by simp) 0).hasDerivAt
      change HasDerivAt (fun t : ℝ => e t • j t) _ 0 at hh
      simpa only [he0, he1, zero_smul, zero_add] using hh
    rw [hfun]
    simpa only [Pi.add_def, zero_add] using ((hcφ.add hdB).add hej).deriv
  have hcf : ContDiff ℝ ∞ (fun t => c t • φ t) := hc.smul hφ
  have hdb : ContDiff ℝ ∞ (fun t => d t • B t) := hd.smul hB
  have hej : ContDiff ℝ ∞ (fun t => e t • j t) := he.smul hj
  refine ⟨hzero, hfirst, ?_⟩
  rw [hfun, iteratedDeriv_fun_add ((hcf.add hdb).of_le (by simp)).contDiffAt
      (hej.of_le (by simp)).contDiffAt,
    iteratedDeriv_fun_add (hcf.of_le (by simp)).contDiffAt (hdb.of_le (by simp)).contDiffAt,
    scalar_field_second c φ hc hφ hc0 hc1, scalar_field_second d B hd hB hd0 hd1,
    scalar_field_second e j he hj he0 he1, hc2, hd2, he2, hφ0, hB0, hm2]
  simp only [zero_smul, add_zero, smul_smul, ← add_smul]
  congr 1
  nlinarith [congrArg (fun z : ℝ => 2 * DGPS.Circle.AngularNormalization.a0 *
    (Real.sqrt 2 * ((a ^ 2 - b ^ 2) / 4 + a / 6)) * z) eta_relation]

end DGPS.Examples.PolynomialSpecies
