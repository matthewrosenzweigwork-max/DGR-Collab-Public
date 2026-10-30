import DGPS.Examples.PolynomialSpeciesMixedGeneratorSecond
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! True second moments on finite profiles with an arbitrary second C2 mode.
The origin identity for the generator is used only in the additional second
mode direction. Its mixed first-mode expectation was derived separately. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private abbrev Input := ℝ × PeriodicC2_STR02969

private theorem pair_second (f : ℝ → ℝ) (g : ℝ → PeriodicC2_STR02969)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    iteratedDeriv 2 (fun t => (f t, g t)) 0 =
      (iteratedDeriv 2 f 0, iteratedDeriv 2 g 0) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_prodMk hf hg (by simp)]
  rfl

private theorem second_curve (F : Input → ℝ) (hF : ContDiff ℝ ∞ F)
    (v w : PeriodicC2_STR02969) :
    iteratedDeriv 2 (fun t : ℝ => F (t, t • v + t ^ 2 • w)) 0 =
      iteratedDeriv 2 (fun t : ℝ => F (t, t • v)) 0 +
        fderiv ℝ F (0, 0) (0, (2 : ℝ) • w) := by
  let q := fun t : ℝ => (t, t • v + t ^ 2 • w)
  let q0 := fun t : ℝ => (t, t • v)
  have hq : ContDiff ℝ ∞ q := contDiff_id.prodMk
    ((contDiff_id.smul contDiff_const).add ((contDiff_id.pow 2).smul contDiff_const))
  have hq0 : ContDiff ℝ ∞ q0 := contDiff_id.prodMk (contDiff_id.smul contDiff_const)
  have hz : q 0 = (0, 0) := by simp [q]
  have hz0 : q0 0 = (0, 0) := by simp [q0]
  have hq1 : deriv q 0 = (1, v) := by
    have hd := (hasDerivAt_id (0 : ℝ)).prodMk
      (((hasDerivAt_id (0 : ℝ)).smul_const v).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const w))
    simpa [q] using hd.deriv
  have hq01 : deriv q0 0 = (1, v) := by
    simpa [q0] using ((hasDerivAt_id (0 : ℝ)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v)).deriv
  have hi : ContDiffAt ℝ 2 (fun t : ℝ => t) 0 := contDiff_id.contDiffAt
  have hv : ContDiffAt ℝ 2 (fun t : ℝ => t • v) 0 := (contDiff_id.smul contDiff_const).contDiffAt
  have hw : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2 • w) 0 := ((contDiff_id.pow 2).smul contDiff_const).contDiffAt
  have hp : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2) 0 := (contDiff_id.pow 2).contDiffAt
  have hq2 : iteratedDeriv 2 q 0 = (0, (2 : ℝ) • w) := by
    change iteratedDeriv 2 (fun t : ℝ => (t, t • v + t ^ 2 • w)) 0 = _
    rw [pair_second _ _ hi (hv.add hw), iteratedDeriv_fun_add hv hw,
      iteratedDeriv_smul_const hi, iteratedDeriv_smul_const hp]
    norm_num [iteratedDeriv_fun_id, iteratedDeriv_pow]
  have hq02 : iteratedDeriv 2 q0 0 = 0 := by
    change iteratedDeriv 2 (fun t : ℝ => (t, t • v)) 0 = _
    rw [pair_second _ _ hi hv, iteratedDeriv_smul_const hi]
    simp [iteratedDeriv_fun_id]
  have h1 := iteratedDeriv_vcomp_two (x := (0 : ℝ)) ((hF.of_le (by simp)).contDiffAt)
    ((hq.of_le (by simp)).contDiffAt)
  have h0 := iteratedDeriv_vcomp_two (x := (0 : ℝ)) ((hF.of_le (by simp)).contDiffAt)
    ((hq0.of_le (by simp)).contDiffAt)
  rw [hz, hq1, hq2] at h1
  rw [hz0, hq01, hq02, map_zero, add_zero] at h0
  dsimp only [Function.comp_def, q, q0] at h1 h0
  rw [h1, h0]

private def featureMoment (z : Input) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight (z.1, 0))) z.2
    (e0_STR02955 (polynomialRangeFeature (z.1, 0)))

private def generatorMoment (z : Input) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight (z.1, 0))) z.2
    (polynomialRangeGenerator (z.1, 0))

private theorem moment_smooth : ContDiff ℝ ∞ featureMoment ∧ ContDiff ℝ ∞ generatorMoment := by
  have hp : ContDiff ℝ ∞ (fun z : Input => (z.1, (0 : ℝ))) := contDiff_fst.prodMk contDiff_const
  obtain ⟨hL, _, _, hφ, hB, _⟩ := polynomialRange_data_smooth
  have hlog := e0_STR02955.contDiff.comp (hL.comp hp)
  have hu := e0_STR02955.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (fun z : Input => z.2))
  have hR := rho_smooth_STR02954.comp ((contDiff_const (c := (0 : ℝ))).prodMk (hlog.add hu))
  exact ⟨meanCLM_STR02954.contDiff.comp ((e0_STR02955.contDiff.comp (hφ.comp hp)).mul hR),
    meanCLM_STR02954.contDiff.comp ((hB.comp hp).mul hR)⟩

private theorem partial_mean (F : Input → ℝ) (hF : ContDiff ℝ ∞ F)
    (f : PeriodicHolder_STR02968)
    (he : (fun u : PeriodicC2_STR02969 => F (0, u)) = fun u => eulerMean 0 u f)
    (hf0 : meanCLM_STR02954 f = 0) (w : PeriodicC2_STR02969) :
    fderiv ℝ F (0, 0) (0, w) = meanCLM_STR02954 (f * e0_STR02955 w) := by
  let I : PeriodicC2_STR02969 →L[ℝ] Input :=
    (0 : PeriodicC2_STR02969 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ PeriodicC2_STR02969)
  have hd := (hF.differentiable (by simp) (0, 0)).hasFDerivAt.comp (0 : PeriodicC2_STR02969) I.hasFDerivAt
  have hc := congrArg (fun T : PeriodicC2_STR02969 →L[ℝ] ℝ => T w) hd.fderiv
  have hM := eulerMean_fderiv (0 : PeriodicHolder_STR02968) (fun _ => f) contDiff_const 0 w
  have hMI : fderiv ℝ (fun u : PeriodicC2_STR02969 => F (0, u)) 0 w =
      meanCLM_STR02954 (f * e0_STR02955 w) := by
    rw [he]
    simpa [eulerMean, eulerCov, eulerDensity, hf0, rho_zero_STR02955] using hM
  have hc' : fderiv ℝ (fun u : PeriodicC2_STR02969 => F (0, u)) 0 w =
      fderiv ℝ F (0, 0) (0, w) := by
    simpa [I, ContinuousLinearMap.comp_apply, Function.comp_def] using hc
  exact hc'.symm.trans hMI

/-- The true finite-profile feature moment's SECOND derivative. The added
second mode contributes exactly its actual Haar pairing with the origin
feature; no nonzero-field eigenfunction relation is used. -/
theorem polynomialFiniteProfile_feature_moment_second (a b : ℝ) (w : PeriodicC2_STR02969) :
    iteratedDeriv 2 (fun t : ℝ => eulerMean
      (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
      (t • (a • cosC2_STR02915 + b • sinC2_STR02915) + t ^ 2 • w)
      (e0_STR02955 (polynomialRangeFeature (t, 0)))) 0 =
      Real.sqrt 2 * ((a ^ 2 - b ^ 2) / 4 + a / 6) +
        2 * meanCLM_STR02954 (e0_STR02955 polynomialOriginMode * e0_STR02955 w) := by
  change iteratedDeriv 2 (fun t : ℝ => featureMoment (t,
    t • (a • cosC2_STR02915 + b • sinC2_STR02915) + t ^ 2 • w)) 0 = _
  rw [second_curve featureMoment moment_smooth.1]
  have he : (fun u : PeriodicC2_STR02969 => featureMoment (0, u)) =
      fun u => eulerMean 0 u (e0_STR02955 polynomialOriginMode) := by
    funext u
    simp only [featureMoment, show polynomialRangeLogWeight (0, 0) = 0 by simp [polynomialRangeLogWeight],
      map_zero, polynomialOriginFeature_eq]
  rw [show iteratedDeriv 2 (fun t : ℝ => featureMoment
      (t, t • (a • cosC2_STR02915 + b • sinC2_STR02915))) 0 =
      iteratedDeriv 2 (polynomialMixedFeatureMoment a b) 0 from rfl,
    polynomialMixedFeatureMoment_second,
    partial_mean featureMoment moment_smooth.1 _ he polynomialOriginFeature_mean_zero]
  rw [map_smul, mul_smul_comm, map_smul]
  simp only [smul_eq_mul]

/-- The true generator moment has FOUR TIMES a0 the feature moment's second
derivative on these finite profiles. This is an expectation-jet identity only. -/
theorem polynomialFiniteProfile_generator_moment_second (a b : ℝ) (w : PeriodicC2_STR02969) :
    iteratedDeriv 2 (fun t : ℝ => eulerMean
      (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
      (t • (a • cosC2_STR02915 + b • sinC2_STR02915) + t ^ 2 • w)
      (polynomialRangeGenerator (t, 0))) 0 =
      4 * DGPS.Circle.AngularNormalization.a0 *
        iteratedDeriv 2 (fun t : ℝ => eulerMean
          (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
          (t • (a • cosC2_STR02915 + b • sinC2_STR02915) + t ^ 2 • w)
          (e0_STR02955 (polynomialRangeFeature (t, 0)))) 0 := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  change iteratedDeriv 2 (fun t : ℝ => generatorMoment (t, t • v + t ^ 2 • w)) 0 =
    4 * DGPS.Circle.AngularNormalization.a0 *
      iteratedDeriv 2 (fun t : ℝ => featureMoment (t, t • v + t ^ 2 • w)) 0
  rw [second_curve generatorMoment moment_smooth.2, second_curve featureMoment moment_smooth.1]
  have hφ : (fun u : PeriodicC2_STR02969 => featureMoment (0, u)) =
      fun u => eulerMean 0 u (e0_STR02955 polynomialOriginMode) := by
    funext u
    simp only [featureMoment, show polynomialRangeLogWeight (0, 0) = 0 by simp [polynomialRangeLogWeight],
      map_zero, polynomialOriginFeature_eq]
  have hB : (fun u : PeriodicC2_STR02969 => generatorMoment (0, u)) =
      fun u => eulerMean 0 u ((4 * DGPS.Circle.AngularNormalization.a0) • e0_STR02955 polynomialOriginMode) := by
    funext u
    simp only [generatorMoment, show polynomialRangeLogWeight (0, 0) = 0 by simp [polynomialRangeLogWeight],
      map_zero, polynomialOriginGenerator_eq]
  have hB0 : meanCLM_STR02954 ((4 * DGPS.Circle.AngularNormalization.a0) •
      e0_STR02955 polynomialOriginMode) = 0 := by
    rw [map_smul, polynomialOriginFeature_mean_zero, smul_zero]
  rw [partial_mean generatorMoment moment_smooth.2 _ hB hB0,
    partial_mean featureMoment moment_smooth.1 _ hφ polynomialOriginFeature_mean_zero]
  have hbase := polynomialMixedGeneratorMoment_second a b
  change iteratedDeriv 2 (fun t : ℝ => generatorMoment (t, t • v)) 0 =
    4 * DGPS.Circle.AngularNormalization.a0 *
      iteratedDeriv 2 (fun t : ℝ => featureMoment (t, t • v)) 0 at hbase
  rw [hbase, smul_mul_assoc, map_smul]
  simp only [smul_eq_mul]
  ring

end DGPS.Examples.PolynomialSpecies
