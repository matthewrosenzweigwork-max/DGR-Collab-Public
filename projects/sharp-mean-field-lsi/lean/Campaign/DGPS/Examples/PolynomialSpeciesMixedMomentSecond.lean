import DGPS.Examples.PolynomialSpeciesMixedMoment
import DGPS.Examples.PolynomialSpeciesOriginMomentCoefficient
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The genuine mixed feature-moment second derivative. The moving reference
mean is differentiated through its exact normalized-expectation identity. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private def moment (a b : ℝ) (f : PeriodicHolder_STR02968) (t : ℝ) : ℝ :=
  eulerMean (0 : PeriodicHolder_STR02968)
    (t • (a • cosC2_STR02915 + b • sinC2_STR02915)) f

private theorem moment_smooth (a b : ℝ) (f : PeriodicHolder_STR02968) :
    ContDiff ℝ ∞ (moment a b f) := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  have hu : ContDiff ℝ ∞ (fun t : ℝ => t • v) := contDiff_id.smul contDiff_const
  have hR : ContDiff ℝ ∞ (fun t : ℝ => rho_STR02954 (0, (0 : PeriodicHolder_STR02968) + e0_STR02955 (t • v))) := rho_smooth_STR02954.comp (contDiff_const.prodMk
    (contDiff_const.add (e0_STR02955.contDiff.comp hu)))
  exact meanCLM_STR02954.contDiff.comp (contDiff_const.mul hR)

private theorem cosine_first (a b : ℝ) :
    deriv (moment a b (e0_STR02955 cosC2_STR02915)) 0 = a / 2 := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  let V := e0_STR02955 v
  let C := e0_STR02955 cosC2_STR02915
  have hV : meanCLM_STR02954 V = 0 := polynomial_first_amplitude_centered a b
  have hR : HasDerivAt (fun t : ℝ => rho_STR02954 (0, t • V)) V 0 := by
    simpa only [zero_add, rho_zero_STR02955, mul_one, one_mul, hV, zero_smul, sub_zero] using
      hasDerivAt_rho_path_STR02949 0 (0 : PeriodicHolder_STR02968) V
  have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) C).mul hR)
  have hd' : HasDerivAt (moment a b C) (meanCLM_STR02954 (C * V)) 0 := by
    change HasDerivAt (fun t => meanCLM_STR02954 (C * rho_STR02954 (0, (0 : PeriodicHolder_STR02968) + e0_STR02955 (t • v)))) (meanCLM_STR02954 (C * V)) 0
    convert hd using 1 <;>
      simp only [moment, v, V, eulerMean, eulerDensity, map_smul, zero_add,
        Function.comp_def, Pi.mul_apply, zero_mul, zero_add]
  rw [hd'.deriv]
  have hcs : meanCLM_STR02954 (e0_STR02955 cosC2_STR02915 * e0_STR02955 sinC2_STR02915) = 0 := by
    rw [mul_comm]
    exact meanT_sc_STR02955
  have hcc : meanCLM_STR02954 (e0_STR02955 cosC2_STR02915 * e0_STR02955 cosC2_STR02915) = 1 / 2 := meanT_cc_STR02955
  dsimp only [C, V, v]
  rw [map_add, map_smul, map_smul, mul_add, mul_smul_comm, mul_smul_comm,
    map_add, map_smul, map_smul, hcc, hcs]
  simp only [smul_eq_mul]
  ring

private theorem times_parameter_second (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    iteratedDeriv 2 (fun t : ℝ => t * g t) 0 = 2 * deriv g 0 := by
  rw [iteratedDeriv_fun_mul (show ContDiffAt ℝ 2 (fun t : ℝ => t) 0 from contDiffAt_id)
    ((hg.of_le (by simp)).contDiffAt)]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, iteratedDeriv_fun_id]

/-- The actual SECOND derivative on h=t,s=0,u=t*(a*cos+b*sin). The term a/6
comes from true moving-reference normalization and feature variation. -/
theorem polynomialMixedFeatureMoment_second (a b : ℝ) :
    iteratedDeriv 2 (polynomialMixedFeatureMoment a b) 0 =
      Real.sqrt 2 * ((a ^ 2 - b ^ 2) / 4 + a / 6) := by
  let φ := e0_STR02955 (polynomialRangeFeature (0, 0))
  let C := e0_STR02955 cosC2_STR02915
  let g := fun t : ℝ => moment (1 + a) b C t - moment 1 0 C t
  have hg : ContDiff ℝ ∞ g := (moment_smooth _ _ _).sub (moment_smooth _ _ _)
  have hgd : deriv g 0 = a / 2 := by
    rw [show g = moment (1 + a) b C - moment 1 0 C from rfl,
      deriv_sub ((moment_smooth _ _ _).differentiable (by simp) _)
        ((moment_smooth _ _ _).differentiable (by simp) _), cosine_first, cosine_first]
    ring
  have he : polynomialMixedFeatureMoment a b = fun t : ℝ =>
      moment (1 + a) b φ t - moment 1 0 φ t - (Real.sqrt 2 / 3) * (t * g t) := by
    funext t
    rw [polynomialMixedFeatureMoment_identity]
    have hv : cosC2_STR02915 + (a • cosC2_STR02915 + b • sinC2_STR02915) =
        (1 + a) • cosC2_STR02915 + b • sinC2_STR02915 := by
      simp only [add_smul, one_smul, add_assoc]
    rw [hv]
    simp only [moment, one_smul, zero_smul, add_zero, φ, C, g]
    ring
  have hm2 (x y : ℝ) : iteratedDeriv 2 (moment x y φ) 0 = Real.sqrt 2 * (x ^ 2 - y ^ 2) / 4 := by
    have hd := (polynomialOriginAmplitudeMoment_second_exact x y).deriv
    change iteratedDeriv 2 (fun t => eulerMean (0 : PeriodicHolder_STR02968) (t • (x • cosC2_STR02915 + y • sinC2_STR02915)) φ) 0 = _
    simpa only [φ, iteratedDeriv_succ, iteratedDeriv_zero] using hd
  have hprod : ContDiff ℝ ∞ (fun t : ℝ => (Real.sqrt 2 / 3) * (t * g t)) := contDiff_const.mul (contDiff_id.mul hg)
  rw [he, iteratedDeriv_fun_sub
    (((moment_smooth (1 + a) b φ).sub (moment_smooth 1 0 φ)).of_le (by simp)).contDiffAt
    (hprod.of_le (by simp)).contDiffAt,
    iteratedDeriv_fun_sub ((moment_smooth (1 + a) b φ).of_le (by simp)).contDiffAt
      ((moment_smooth 1 0 φ).of_le (by simp)).contDiffAt,
    iteratedDeriv_const_mul_field, hm2, hm2, times_parameter_second g hg, hgd]
  ring

end DGPS.Examples.PolynomialSpecies
