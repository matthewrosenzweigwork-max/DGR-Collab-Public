import DGPS.Examples.PolynomialSpeciesRangeOrigin
import DGPS.Examples.PolynomialSpeciesEuler
import DGPS.Frontier.STR029.T14
import DGPS.Frontier.STR029.T62
import DGPS.Frontier.STR029.T09

/-! The actual normalized second-mode correction to the polynomial origin inverse.
This constructs the corrected linear isomorphism, without assuming it is an
origin derivative. The derivative identification is a separate obligation. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
open DGPS.Examples.PolynomialCenteredResidual

namespace DGPS.Examples.PolynomialSpecies

/-- The normalized actual zero-field feature in the existing C2 carrier. -/
def polynomialOriginMode : PeriodicC2_STR02969 :=
  Real.sqrt 2 • PeriodicC2_STR02969.mk (fun t => Real.cos (2 * t)) (cosFreq_isC2_STR02962 2)

private theorem mode_val (t : ℝ) : polynomialOriginMode.val t = Real.sqrt 2 * Real.cos (2 * t) := rfl

/-- This mode is the actual polynomial feature, not a replacement away from zero field. -/
theorem polynomialOriginMode_actual : e0_STR02955 polynomialOriginMode = polynomialEulerFeature 0 := by
  apply ext_STR02954
  funext t
  change Real.sqrt 2 * Real.cos (2 * t) = (polynomialRankOne 0).φ (angEquiv.symm (t : AngCircle))
  rw [polynomial_feature_angular]
  simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply, phi_EX057,
    polynomial_mean_origin, feature_coe_EX057, zero_div, zero_mul, sub_zero]

private theorem mode_mean : meanT_STR02901 polynomialOriginMode.val = 0 := by
  have he : polynomialOriginMode.val = (Real.sqrt 2 : ℝ) • (fun t => Real.cos ((2 : ℝ) * t)) := rfl
  rw [he, meanT_smul_STR02953]
  have hc := meanT_cos_STR02962 (by decide : (2 : ℕ) ≠ 0)
  norm_num only [Nat.cast_ofNat] at hc
  rw [hc, mul_zero]

/-- Exact Haar normalization of the true zero-field feature. -/
theorem polynomialOriginMode_unit :
    meanCLM_STR02954 (e0_STR02955 polynomialOriginMode * e0_STR02955 polynomialOriginMode) = 1 := by
  rw [meanCLM_apply_STR02954]
  change meanT_STR02901 (fun t => (Real.sqrt 2 * Real.cos (2 * t)) *
    (Real.sqrt 2 * Real.cos (2 * t))) = 1
  rw [meanT_eq_normInt_STR02909]
  simpa [trigBasisFun_STR02934] using
    normInt_trigBasis_mul_STR02934 (some (false, 1)) (some (false, 1))

private theorem mode_deriv : deriv polynomialOriginMode.val = fun t => Real.sqrt 2 * Pd_EX057 0 t := by
  have he : polynomialOriginMode.val = Phi_EX057 0 0 := by
    funext t
    rw [mode_val]
    simp [Phi_EX057]
  rw [he]
  exact funext fun t => (hasDerivAt_Phi_EX057 0 0 t).deriv

/-- Its true second derivative is minus four times the mode. -/
theorem polynomialOriginMode_second (t : ℝ) :
    deriv (deriv polynomialOriginMode.val) t = -4 * polynomialOriginMode.val t := by
  rw [mode_deriv, (hasDerivAt_sqrtPd_EX057 0 t).deriv, mode_val]
  simp only [Pdd_EX057, zero_div, zero_mul, add_zero]
  ring

private theorem mode_inE : InE_STR02901 polynomialOriginMode.val := by
  have hf := c2_inE_STR02955 polynomialOriginMode.isC2 mode_mean
  have he : (fun t => deriv (deriv polynomialOriginMode.val) t + polynomialOriginMode.val t) =
      fun t => (-3 : ℝ) * polynomialOriginMode.val t := by
    funext t
    rw [polynomialOriginMode_second]
    ring
  rw [he] at hf
  have hs := inE_smul_STR02955 (-1 / 3) hf
  have he' : (fun t => (-1 / 3 : ℝ) * ((-3 : ℝ) * polynomialOriginMode.val t)) =
      polynomialOriginMode.val := by funext t; ring
  rw [he'] at hs
  exact hs

/-- The actual normalized second mode belongs to the existing amplitude complement. -/
def polynomialOriginModeE : E_STR02969 :=
  ⟨polynomialOriginMode, (str029_69_completeness_closed_complements_range_spaces_E.1 _).2 mode_inE⟩

def polynomialOriginModeY : Y_STR02969 :=
  ⟨e0_STR02955 polynomialOriginMode,
    (str029_69_completeness_closed_complements_range_spaces_Y.1 _).2 mode_inE⟩

def polynomialOriginCoefficient : E_STR02969 →L[ℝ] ℝ :=
  meanCLM_STR02954.comp ((ContinuousLinearMap.mul ℝ PeriodicHolder_STR02968
    (e0_STR02955 polynomialOriginMode)).comp (e0_STR02955.comp E_STR02969.subtypeL))

/-- The normalized Haar projection onto the actual second mode. -/
def polynomialOriginProjection : E_STR02969 →L[ℝ] E_STR02969 :=
  polynomialOriginCoefficient.smulRight polynomialOriginModeE

private theorem coefficient_mode : polynomialOriginCoefficient polynomialOriginModeE = 1 :=
  polynomialOriginMode_unit

/-- The exact projection identity, with its normalization derived rather than assumed. -/
theorem polynomialOriginProjection_idempotent (w : E_STR02969) :
    polynomialOriginProjection (polynomialOriginProjection w) = polynomialOriginProjection w := by
  change polynomialOriginCoefficient (polynomialOriginCoefficient w • polynomialOriginModeE) • polynomialOriginModeE =
    polynomialOriginCoefficient w • polynomialOriginModeE
  rw [map_smul, coefficient_mode, smul_eq_mul, mul_one]

/-- Id+P2 is an automorphism with the explicit inverse Id-P2/2. -/
def polynomialOriginDoubleMode : E_STR02969 ≃L[ℝ] E_STR02969 where
  toLinearEquiv :=
    { toLinearMap := (ContinuousLinearMap.id ℝ E_STR02969 + polynomialOriginProjection).toLinearMap
      invFun := fun w => w - (1 / 2 : ℝ) • polynomialOriginProjection w
      left_inv := by
        intro w
        change w + polynomialOriginProjection w - (1 / 2 : ℝ) •
          polynomialOriginProjection (w + polynomialOriginProjection w) = w
        rw [map_add, polynomialOriginProjection_idempotent]
        module
      right_inv := by
        intro w
        change w - (1 / 2 : ℝ) • polynomialOriginProjection w +
          polynomialOriginProjection (w - (1 / 2 : ℝ) • polynomialOriginProjection w) = w
        rw [map_sub, map_smul, polynomialOriginProjection_idempotent]
        module }
  continuous_toFun := (ContinuousLinearMap.id ℝ E_STR02969 + polynomialOriginProjection).continuous
  continuous_invFun := (ContinuousLinearMap.id ℝ E_STR02969 - (1 / 2 : ℝ) • polynomialOriginProjection).continuous

private theorem scale_ne_zero : (-2 : ℝ) * DGPS.Circle.AngularNormalization.a0 ≠ 0 :=
  mul_ne_zero (by norm_num) DGPS.Circle.AngularNormalization.a0_pos.ne'

private def physicalScale : Y_STR02969 ≃L[ℝ] Y_STR02969 where
  toLinearEquiv :=
    { toLinearMap := (((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0) •
        ContinuousLinearMap.id ℝ Y_STR02969).toLinearMap
      invFun := fun y => (((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0)⁻¹) • y
      left_inv := by
        intro y
        change (((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0)⁻¹) •
          (((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0) • y) = y
        rw [smul_smul, inv_mul_cancel₀ scale_ne_zero, one_smul]
      right_inv := by
        intro y
        change (((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0)) •
          ((((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0)⁻¹) • y) = y
        rw [smul_smul, mul_inv_cancel₀ scale_ne_zero, one_smul] }
  continuous_toFun := (((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0) •
    ContinuousLinearMap.id ℝ Y_STR02969).continuous
  continuous_invFun := ((((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0)⁻¹) •
    ContinuousLinearMap.id ℝ Y_STR02969).continuous

/-- The corrected actual-mode linear isomorphism, factored through the existing T14 inverse. -/
def polynomialOriginRangeEquiv : E_STR02969 ≃L[ℝ] Y_STR02969 :=
  (polynomialOriginDoubleMode.trans bij_STR02914).trans physicalScale

private theorem forward_mode : bij_STR02914 polynomialOriginModeE = (-3 : ℝ) • polynomialOriginModeY := by
  apply Subtype.ext
  apply ext_STR02954
  funext t
  change deriv (deriv polynomialOriginMode.val) t + polynomialOriginMode.val t =
    (-3 : ℝ) * polynomialOriginMode.val t
  rw [polynomialOriginMode_second]
  ring

/-- The forward operator has precisely the required positive rank-one correction.
No derivative identification is assumed in this statement. -/
theorem polynomialOriginRangeEquiv_apply (w : E_STR02969) (t : ℝ) :
    ((polynomialOriginRangeEquiv w : Y_STR02969) : PeriodicHolder_STR02968).val t =
      (-2 * DGPS.Circle.AngularNormalization.a0) *
        (deriv (deriv (w : PeriodicC2_STR02969).val) t + (w : PeriodicC2_STR02969).val t) +
        6 * DGPS.Circle.AngularNormalization.a0 * polynomialOriginCoefficient w * polynomialOriginMode.val t := by
  change ((((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0) •
    (bij_STR02914 (w + polynomialOriginProjection w) : Y_STR02969) : Y_STR02969) : PeriodicHolder_STR02968).val t = _
  change ((((-2 : ℝ) * DGPS.Circle.AngularNormalization.a0) •
    (bij_STR02914 (w + polynomialOriginCoefficient w • polynomialOriginModeE) : Y_STR02969) : Y_STR02969) : PeriodicHolder_STR02968).val t = _
  rw [map_add, map_smul, forward_mode]
  change (-2 * DGPS.Circle.AngularNormalization.a0) *
    ((deriv (deriv (w : PeriodicC2_STR02969).val) t + (w : PeriodicC2_STR02969).val t) +
      polynomialOriginCoefficient w * ((-3 : ℝ) * polynomialOriginMode.val t)) = _
  ring

/-- The actual radical coupling gives exactly the rank-one coefficient used above. -/
theorem polynomial_origin_coupling_coefficient :
    2 * DGPS.Circle.AngularNormalization.a0 * eta * (7 + 4 * eta) =
      6 * DGPS.Circle.AngularNormalization.a0 := by
  have h := congrArg (fun z : ℝ => 2 * DGPS.Circle.AngularNormalization.a0 * z) eta_relation
  nlinarith [h]

end DGPS.Examples.PolynomialSpecies
