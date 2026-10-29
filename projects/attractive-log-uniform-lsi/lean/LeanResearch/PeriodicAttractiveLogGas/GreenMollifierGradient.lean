import LeanResearch.PeriodicAttractiveLogGas.GreenWeakFirstDerivative
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The actual first derivative of the prescribed Green convolution, and a
uniform inverse-distance estimate. Differentiation first falls on the smooth
compact mollifier. The weak identity in `GreenWeakFirstDerivative` then moves
the derivative across the logarithmic pole. The near-pole estimate uses the
finite integral of the inverse Euclidean radius on the radius-three ball and
its exact dilation law; evaluating that fixed integral as `6 * pi` is not
needed for the source's unspecified uniform constant.
-/

noncomputable section
open MeasureTheory Metric Set Filter InnerProductSpace
open scoped Topology ContDiff Convolution RealInnerProductSpace

namespace PeriodicAttractiveLogGas

theorem fderiv_torusLift_add_frequencyVector (f : Torus → ℝ)
    (x : PlanarSpace) (k : Frequency) :
    fderiv ℝ (fun y : PlanarSpace ↦ f (torusQuotient y)) (x + frequencyVector k) =
      fderiv ℝ (fun y : PlanarSpace ↦ f (torusQuotient y)) x := by
  simpa only [torusQuotient_add_frequencyVector] using
    (fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : PlanarSpace ↦ f (torusQuotient y))
      (x := x) (frequencyVector k)).symm

theorem fderiv_torusLift_eq_of_torusQuotient_eq (f : Torus → ℝ)
    {x y : PlanarSpace} (hxy : torusQuotient x = torusQuotient y) :
    fderiv ℝ (fun w : PlanarSpace ↦ f (torusQuotient w)) x =
      fderiv ℝ (fun w : PlanarSpace ↦ f (torusQuotient w)) y := by
  obtain ⟨k, rfl⟩ := exists_frequencyVector_of_torusQuotient_eq hxy
  exact (fderiv_torusLift_add_frequencyVector f x k).symm

def regularizedGreenDifferential (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    PlanarSpace →L[ℝ] ℝ :=
  fderiv ℝ (fun x : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient x))
    (centeredLift z)

def regularizedGreenGradient (ε : ℝ) (hε : 0 < ε) (z : Torus) : PlanarSpace :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm (regularizedGreenDifferential ε hε z)

theorem regularizedGreenDifferential_lift (ε : ℝ) (hε : 0 < ε) (x : PlanarSpace) :
    regularizedGreenDifferential ε hε (torusQuotient x) =
      fderiv ℝ (fun y : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient y)) x :=
  fderiv_torusLift_eq_of_torusQuotient_eq (regularizedGreen ε hε)
    (torusQuotient_centeredLift _)

theorem regularizedGreenGradient_inner (ε : ℝ) (hε : 0 < ε)
    (z : Torus) (v : PlanarSpace) :
    inner ℝ (regularizedGreenGradient ε hε z) v =
      regularizedGreenDifferential ε hε z v :=
  InnerProductSpace.toDual_symm_apply

theorem norm_regularizedGreenGradient (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    ‖regularizedGreenGradient ε hε z‖ = ‖regularizedGreenDifferential ε hε z‖ :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm.norm_map _

theorem continuous_regularizedGreenDifferential (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) : Continuous (regularizedGreenDifferential ε hε) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  apply isOpenQuotientMap_torusQuotient.continuousAt_comp_iff.mp
  have hc := (contDiff_regularizedGreen_lift ε hε hεsmall).continuous_fderiv (by simp)
  simpa only [Function.comp_def, regularizedGreenDifferential_lift] using hc.continuousAt

theorem continuous_regularizedGreenGradient (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) : Continuous (regularizedGreenGradient ε hε) :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm.continuous.comp
    (continuous_regularizedGreenDifferential ε hε hεsmall)

theorem integrable_regularGreenLift_mul_fderiv_scaledRadialMollifier_sub
    (ε : ℝ) (hε : 0 < ε) (x v : PlanarSpace) :
    Integrable (fun y : PlanarSpace ↦ regularGreenLift y *
      fderiv ℝ (scaledRadialMollifier ε) (x - y) v) volume :=
  ((hasCompactSupport_scaledRadialMollifier ε hε).fderiv_apply ℝ v).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) locallyIntegrable_regularGreenLift
    (((contDiff_scaledRadialMollifier ε).continuous_fderiv (by simp)).clm_apply continuous_const) x

/-- The derivative obtained by ordinary differentiation under convolution.
At this stage the derivative acts only on the smooth compact factor. -/
theorem fderiv_regularizedGreen_lift_apply (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) (x v : PlanarSpace) :
    fderiv ℝ (fun y : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient y)) x v =
      ∫ y, regularGreenLift y * fderiv ℝ (scaledRadialMollifier ε) (x - y) v := by
  have heq : (fun y : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient y)) =
      regularGreenLift ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] scaledRadialMollifier ε :=
    funext (regularizedGreen_lift_eq_convolution ε hε hεsmall)
  rw [heq,
    ((hasCompactSupport_scaledRadialMollifier ε hε).hasFDerivAt_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) locallyIntegrable_regularGreenLift
      ((contDiff_scaledRadialMollifier ε).of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ)
    locallyIntegrable_regularGreenLift
    ((hasCompactSupport_scaledRadialMollifier ε hε).fderiv ℝ)
    ((contDiff_scaledRadialMollifier ε).continuous_fderiv (by simp)) x v

/-- The actual weak first identity moves the derivative to the Green lift.
This is stronger than merely knowing its classical derivative is locally L1. -/
theorem regularizedGreenDifferential_eq_integral (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) (z : Torus) (v : PlanarSpace) :
    regularizedGreenDifferential ε hε z v =
      ∫ y, fderiv ℝ regularGreenLift y v *
        scaledRadialMollifier ε (centeredLift z - y) := by
  change fderiv ℝ (fun x : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient x))
    (centeredLift z) v = _
  rw [fderiv_regularizedGreen_lift_apply ε hε hεsmall]
  have h := integral_regularGreenLift_mul_fderiv_translatedScaledMollifier
    ε hε hεsmall z v
  simp only [fderiv_translatedScaledMollifier_apply, mul_neg, integral_neg,
    translatedScaledMollifier] at h
  exact neg_injective h

theorem regularizedGreenDifferential_eq_integral_sub (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) (z : Torus) (v : PlanarSpace) :
    regularizedGreenDifferential ε hε z v =
      ∫ y, scaledRadialMollifier ε y * greenDifferential (z - torusQuotient y) v := by
  rw [regularizedGreenDifferential_eq_integral ε hε hεsmall]
  have hs := integral_sub_left_eq_self
    (fun y : PlanarSpace ↦ fderiv ℝ regularGreenLift y v *
      scaledRadialMollifier ε (centeredLift z - y)) volume (centeredLift z)
  rw [← hs]
  apply integral_congr_ae
  filter_upwards with y
  rw [← greenDifferential_lift, torusQuotient_sub, torusQuotient_centeredLift]
  simp only [sub_sub_cancel, mul_comm]

theorem locallyIntegrable_greenGradient_lift :
    LocallyIntegrable (fun x : PlanarSpace ↦ greenGradient (torusQuotient x)) volume := by
  apply (locallyIntegrable_torus_lift integrable_greenGradient.norm).mono
    ((measurable_greenGradient.comp
      isOpenQuotientMap_torusQuotient.continuous.measurable).aestronglyMeasurable)
  filter_upwards with x
  simp only [Function.comp_apply, norm_norm, le_refl]

theorem integrable_scaledRadialMollifier_smul_greenGradient_sub
    (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    Integrable (fun y : PlanarSpace ↦ scaledRadialMollifier ε y •
      greenGradient (z - torusQuotient y)) volume := by
  have hi := locallyIntegrable_greenGradient_lift.integrable_smul_left_of_hasCompactSupport
    (contDiff_translatedScaledMollifier ε (centeredLift z)).continuous
    (hasCompactSupport_translatedScaledMollifier ε hε (centeredLift z))
  have ht := hi.comp_sub_left (centeredLift z)
  simpa only [translatedScaledMollifier, sub_sub_cancel,
    torusQuotient_sub, torusQuotient_centeredLift] using ht

/-- Exact Euclidean gradient commutation, with ordinary real Riesz
normalization one and a separately integrable vector-valued integrand. -/
theorem regularizedGreenGradient_eq_integral (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) (z : Torus) :
    regularizedGreenGradient ε hε z =
      ∫ y : PlanarSpace, scaledRadialMollifier ε y •
        greenGradient (z - torusQuotient y) := by
  apply ext_inner_right ℝ
  intro v
  rw [regularizedGreenGradient_inner,
    regularizedGreenDifferential_eq_integral_sub ε hε hεsmall]
  calc
    (∫ y : PlanarSpace, scaledRadialMollifier ε y *
        greenDifferential (z - torusQuotient y) v) =
        ∫ y : PlanarSpace, innerSL ℝ v
          (scaledRadialMollifier ε y • greenGradient (z - torusQuotient y)) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [map_smul, smul_eq_mul, innerSL_apply_apply]
      rw [real_inner_comm, greenGradient_inner]
    _ = innerSL ℝ v (∫ y : PlanarSpace, scaledRadialMollifier ε y •
        greenGradient (z - torusQuotient y)) :=
      (innerSL ℝ v).integral_comp_comm
        (integrable_scaledRadialMollifier_smul_greenGradient_sub ε hε z)
    _ = inner ℝ (∫ y : PlanarSpace, scaledRadialMollifier ε y •
        greenGradient (z - torusQuotient y)) v := by
      simp only [innerSL_apply_apply]
      exact real_inner_comm _ _

theorem integrable_scaledRadialMollifier_mul_torusRadius_inv
    (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    Integrable (fun y : PlanarSpace ↦ scaledRadialMollifier ε y *
      (torusEuclideanNorm (z - torusQuotient y))⁻¹) volume := by
  have hi := (locallyIntegrable_torus_lift integrable_torusEuclideanNorm_inv).integrable_smul_left_of_hasCompactSupport
      (contDiff_translatedScaledMollifier ε (centeredLift z)).continuous
      (hasCompactSupport_translatedScaledMollifier ε hε (centeredLift z))
  have ht := hi.comp_sub_left (centeredLift z)
  simpa only [translatedScaledMollifier, sub_sub_cancel, smul_eq_mul,
    torusQuotient_sub, torusQuotient_centeredLift] using ht

/-- The actual finite reference integral used in the near-pole estimate. -/
def planarInverseRadiusBallIntegral : ℝ :=
  ∫ y : PlanarSpace in closedBall 0 3, ‖y‖⁻¹

theorem integrableOn_planarInverseRadius_closedBall (R : ℝ) :
    IntegrableOn (fun y : PlanarSpace ↦ ‖y‖⁻¹) (closedBall 0 R) volume :=
  locallyIntegrable_planar_inv_norm.integrableOn_isCompact (isCompact_closedBall 0 R)

theorem planarInverseRadiusBallIntegral_nonneg : 0 ≤ planarInverseRadiusBallIntegral :=
  integral_nonneg (fun y ↦ inv_nonneg.mpr (norm_nonneg y))

/-- The inverse-radius integral scales with degree one in dimension two.
The integrability on both balls has been established independently. -/
theorem integral_planarInverseRadius_closedBall_mul (ε : ℝ) (hε : 0 < ε) :
    (∫ y : PlanarSpace in closedBall 0 (3 * ε), ‖y‖⁻¹) =
      ε * planarInverseRadiusBallIntegral := by
  let F : PlanarSpace → ℝ := (closedBall (0 : PlanarSpace) 3).indicator (fun y ↦ ‖y‖⁻¹)
  have heq : (closedBall (0 : PlanarSpace) (3 * ε)).indicator (fun y ↦ ‖y‖⁻¹) =
      (fun y ↦ ε⁻¹ * F (ε⁻¹ • y)) := by
    funext y
    have hn : ‖ε⁻¹ • y‖ = ‖y‖ / ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
      ring
    have hm : ε⁻¹ • y ∈ closedBall (0 : PlanarSpace) 3 ↔
        y ∈ closedBall (0 : PlanarSpace) (3 * ε) := by
      simp only [mem_closedBall, dist_zero_right, hn]
      exact div_le_iff₀ hε
    by_cases hy : y ∈ closedBall (0 : PlanarSpace) (3 * ε)
    · simp only [indicator_of_mem hy, F, indicator_of_mem (hm.mpr hy), hn,
        div_eq_mul_inv, mul_inv_rev, inv_inv]
      rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    · simp only [indicator_of_notMem hy, F, indicator_of_notMem (mt hm.mp hy), mul_zero]
  rw [← integral_indicator measurableSet_closedBall, heq, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume F hε.le]
  have hdim : Module.finrank ℝ PlanarSpace = 2 := by simp [PlanarSpace]
  rw [hdim, smul_eq_mul]
  have hF : (∫ y, F y) = planarInverseRadiusBallIntegral :=
    integral_indicator measurableSet_closedBall
  rw [hF]
  field_simp [hε.ne']

/-- Source far regime: every radius on the support is at least half the
radius of the center. The totalized inverse at zero is never used here. -/
theorem integral_scaledRadialMollifier_mul_torusRadius_inv_far
    (ε : ℝ) (hε : 0 < ε) {z : Torus} (hz : z ≠ 0)
    (hfar : 2 * ε ≤ torusEuclideanNorm z) :
    (∫ y : PlanarSpace, scaledRadialMollifier ε y *
      (torusEuclideanNorm (z - torusQuotient y))⁻¹) ≤ 2 / torusEuclideanNorm z := by
  have hr := (torusEuclideanNorm_pos_iff z).mpr hz
  calc
    (∫ y : PlanarSpace, scaledRadialMollifier ε y *
        (torusEuclideanNorm (z - torusQuotient y))⁻¹) ≤
        ∫ y : PlanarSpace, scaledRadialMollifier ε y * (2 / torusEuclideanNorm z) := by
      apply integral_mono (integrable_scaledRadialMollifier_mul_torusRadius_inv ε hε z)
        ((integrable_scaledRadialMollifier ε hε).mul_const _)
      intro y
      by_cases hy : scaledRadialMollifier ε y = 0
      · simp only [hy, zero_mul, le_refl]
      · have hyR := mem_ball_zero_iff.mp (support_scaledRadialMollifier_subset ε hε hy)
        have ht := torusEuclideanNorm_add_le (z - torusQuotient y) (torusQuotient y)
        rw [sub_add_cancel] at ht
        have hq := torusEuclideanNorm_quotient_le y
        have hl : torusEuclideanNorm z / 2 ≤ torusEuclideanNorm (z - torusQuotient y) := by
          linarith
        apply mul_le_mul_of_nonneg_left _ (scaledRadialMollifier_nonneg ε y)
        have hi := one_div_le_one_div_of_le (half_pos hr) hl
        calc
          (torusEuclideanNorm (z - torusQuotient y))⁻¹ ≤
              (torusEuclideanNorm z / 2)⁻¹ := by simpa only [one_div] using hi
          _ = 2 / torusEuclideanNorm z := by rw [inv_div]
    _ = 2 / torusEuclideanNorm z := by
      rw [integral_mul_const, integral_scaledRadialMollifier ε hε, one_mul]

/-- Source near regime: the translated support is contained in the radius
`3 * ε` Euclidean ball inside the injectivity radius. -/
theorem integral_scaledRadialMollifier_mul_torusRadius_inv_near
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 16 : ℝ))
    {z : Torus} (hnear : torusEuclideanNorm z < 2 * ε) :
    (∫ y : PlanarSpace, scaledRadialMollifier ε y *
      (torusEuclideanNorm (z - torusQuotient y))⁻¹) ≤
        (fixedRadialMollifier 0 * planarInverseRadiusBallIntegral) / ε := by
  let F : PlanarSpace → ℝ :=
    (closedBall (0 : PlanarSpace) (3 * ε)).indicator (fun y ↦ ‖y‖⁻¹)
  have hF : Integrable F volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_planarInverseRadius_closedBall (3 * ε))
  have hM := fixedRadialMollifier_zero_pos
  have hm : 0 ≤ fixedRadialMollifier 0 / ε ^ 2 := by positivity
  calc
    (∫ y : PlanarSpace, scaledRadialMollifier ε y *
        (torusEuclideanNorm (z - torusQuotient y))⁻¹) ≤
        ∫ y : PlanarSpace, (fixedRadialMollifier 0 / ε ^ 2) * F (centeredLift z - y) := by
      apply integral_mono (integrable_scaledRadialMollifier_mul_torusRadius_inv ε hε z)
        ((hF.comp_sub_left (centeredLift z)).const_mul _)
      intro y
      change scaledRadialMollifier ε y * (torusEuclideanNorm (z - torusQuotient y))⁻¹ ≤
        fixedRadialMollifier 0 / ε ^ 2 * F (centeredLift z - y)
      by_cases hy : scaledRadialMollifier ε y = 0
      · rw [hy, zero_mul]
        exact mul_nonneg hm (indicator_nonneg (fun w _ ↦ inv_nonneg.mpr (norm_nonneg w)) _)
      · have hyR := mem_ball_zero_iff.mp (support_scaledRadialMollifier_subset ε hε hy)
        have hn : ‖centeredLift z - y‖ < 3 * ε := by
          have ht := norm_sub_le (centeredLift z) y
          rw [norm_centeredLift] at ht
          linarith
        have hsmall : ‖centeredLift z - y‖ < (1 / 2 : ℝ) := by linarith
        have hq : torusEuclideanNorm (z - torusQuotient y) = ‖centeredLift z - y‖ := by
          simpa only [torusQuotient_sub, torusQuotient_centeredLift] using
            torusEuclideanNorm_quotient_eq_of_norm_lt_half hsmall
        rw [hq]
        change _ ≤ (fixedRadialMollifier 0 / ε ^ 2) *
          (closedBall (0 : PlanarSpace) (3 * ε)).indicator (fun w ↦ ‖w‖⁻¹) (centeredLift z - y)
        rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hn.le)]
        exact mul_le_mul_of_nonneg_right (scaledRadialMollifier_le_value_zero_div ε y)
          (inv_nonneg.mpr (norm_nonneg _))
    _ = (fixedRadialMollifier 0 / ε ^ 2) * (ε * planarInverseRadiusBallIntegral) := by
      rw [integral_const_mul, integral_sub_left_eq_self F volume (centeredLift z)]
      rw [show (∫ y, F y) = ∫ y : PlanarSpace in closedBall 0 (3 * ε), ‖y‖⁻¹ from
        integral_indicator measurableSet_closedBall,
        integral_planarInverseRadius_closedBall_mul ε hε]
    _ = (fixedRadialMollifier 0 * planarInverseRadiusBallIntegral) / ε := by
      field_simp [hε.ne']

/-- A single inverse-radius convolution bound, with the constant chosen
before the scale and the center. -/
theorem integral_scaledRadialMollifier_mul_torusRadius_inv_le
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 16 : ℝ))
    {z : Torus} (hz : z ≠ 0) :
    (∫ y : PlanarSpace, scaledRadialMollifier ε y *
      (torusEuclideanNorm (z - torusQuotient y))⁻¹) ≤
        (2 + 2 * fixedRadialMollifier 0 * planarInverseRadiusBallIntegral) /
          torusEuclideanNorm z := by
  have hr := (torusEuclideanNorm_pos_iff z).mpr hz
  have hB := planarInverseRadiusBallIntegral_nonneg
  have hM := fixedRadialMollifier_zero_pos
  by_cases hfar : 2 * ε ≤ torusEuclideanNorm z
  · apply (integral_scaledRadialMollifier_mul_torusRadius_inv_far ε hε hz hfar).trans
    apply div_le_div_of_nonneg_right _ hr.le
    have ht : 0 ≤ 2 * fixedRadialMollifier 0 * planarInverseRadiusBallIntegral := by positivity
    linarith
  · have hn := integral_scaledRadialMollifier_mul_torusRadius_inv_near
      ε hε hεsmall (lt_of_not_ge hfar)
    apply hn.trans
    apply (div_le_div_iff₀ hε hr).mpr
    nlinarith [mul_nonneg hM.le hB,
      mul_le_mul_of_nonneg_left (lt_of_not_ge hfar).le (mul_nonneg hM.le hB)]

/-- Bound the actual gradient convolution by the inverse-radius convolution.
The exceptional lattice is removed using its proved nullity under translation. -/
theorem norm_regularizedGreenGradient_le_radius_convolution {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ z : Torus, z ≠ 0 → ‖greenGradient z‖ ≤ C / torusEuclideanNorm z)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 16 : ℝ)) (z : Torus) :
    ‖regularizedGreenGradient ε hε z‖ ≤ C *
      (∫ y : PlanarSpace, scaledRadialMollifier ε y *
        (torusEuclideanNorm (z - torusQuotient y))⁻¹) := by
  rw [regularizedGreenGradient_eq_integral ε hε hεsmall]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae
    (integrable_scaledRadialMollifier_smul_greenGradient_sub ε hε z).norm
    ((integrable_scaledRadialMollifier_mul_torusRadius_inv ε hε z).const_mul C)
  have hae := (volume.measurePreserving_sub_left (centeredLift z)).quasiMeasurePreserving.ae
    ae_mem_offIntegerLattice
  filter_upwards [hae] with y hy
  have hz' : z - torusQuotient y ≠ 0 := by
    simpa only [offIntegerLattice, mem_ofPred_eq, torusQuotient_sub,
      torusQuotient_centeredLift] using hy
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (scaledRadialMollifier_nonneg ε y)]
  calc
    scaledRadialMollifier ε y * ‖greenGradient (z - torusQuotient y)‖ ≤
        scaledRadialMollifier ε y * (C / torusEuclideanNorm (z - torusQuotient y)) :=
      mul_le_mul_of_nonneg_left (hb _ hz') (scaledRadialMollifier_nonneg ε y)
    _ = C * (scaledRadialMollifier ε y *
        (torusEuclideanNorm (z - torusQuotient y))⁻¹) := by ring

/-- The gradient part of source Lemma 2.2 for the actual prescribed family.
The same positive constant works for every allowed scale and every nonzero
point of the square torus. -/
theorem exists_regularizedGreenGradient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
      ∀ z : Torus, z ≠ 0 → ‖regularizedGreenGradient ε hε z‖ ≤ C / torusEuclideanNorm z := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_regularGreenRepresentative_torus_bounds
  let A : ℝ := 2 + 2 * fixedRadialMollifier 0 * planarInverseRadiusBallIntegral
  have hA : 0 < A := by
    dsimp [A]
    have hB := planarInverseRadiusBallIntegral_nonneg
    have hM := fixedRadialMollifier_zero_pos
    positivity
  refine ⟨C₁ * A, mul_pos hC₁ hA, ?_⟩
  intro ε hε hεsmall z hz
  apply (norm_regularizedGreenGradient_le_radius_convolution hC₁.le
    (fun w hw ↦ (hb w hw).2.1) ε hε hεsmall z).trans
  calc
    C₁ * (∫ y : PlanarSpace, scaledRadialMollifier ε y *
        (torusEuclideanNorm (z - torusQuotient y))⁻¹) ≤
        C₁ * (A / torusEuclideanNorm z) :=
      mul_le_mul_of_nonneg_left
        (integral_scaledRadialMollifier_mul_torusRadius_inv_le ε hε hεsmall hz) hC₁.le
    _ = (C₁ * A) / torusEuclideanNorm z := by ring

theorem exists_fderiv_regularizedGreen_lift_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
      ∀ x : PlanarSpace, torusQuotient x ≠ 0 →
        ‖fderiv ℝ (fun y : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient y)) x‖ ≤
          C / torusEuclideanNorm (torusQuotient x) := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedGreenGradient_bound
  refine ⟨C, hC, ?_⟩
  intro ε hε hs x hx
  simpa only [norm_regularizedGreenGradient, regularizedGreenDifferential_lift] using
    hb ε hε hs (torusQuotient x) hx

end PeriodicAttractiveLogGas
