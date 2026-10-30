import DGPS.Examples.PolynomialSpeciesEulerStrong
import DGPS.Examples.PolynomialResidualNormalization
import DGPS.Frontier.STR029.T62

/-! The genuine independent-(h,s) polynomial chart. The normalized reference and
centered feature remain those of EX054. This analytic extension avoids assuming
smoothness of the selected root; it does not alter the frozen canonical model. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux
open DGPS.Circle.BesselMoments
open DGPS.Examples.PolynomialEquilibrium DGPS.Examples.PolynomialCenteredResidual

namespace DGPS.Examples.PolynomialSpecies

private def modeC2 (k : ℕ) : PeriodicC2_STR02969 :=
  PeriodicC2_STR02969.mk (fun t => Real.cos ((k : ℝ) * t)) (cosFreq_isC2_STR02962 k)
private theorem modeC2_val (k : ℕ) (t : ℝ) :
    (modeC2 k).val t = Real.cos ((k : ℝ) * t) := by
  unfold modeC2 PeriodicC2_STR02969.val PeriodicC2_STR02969.mk
  rfl
private def oneC2 : PeriodicC2_STR02969 := modeC2 0
private theorem oneC2_val (t : ℝ) : oneC2.val t = 1 := by
  unfold oneC2
  rw [modeC2_val]
  simp
private theorem holder_val_neg (f : PeriodicHolder_STR02968) : (-f).val = -f.val := rfl

/-- The actual feature before centering, as a function of field. -/
def polynomialRangeBaseFeature (h : ℝ) : PeriodicC2_STR02969 := modeC2 2 - (h / 3) • modeC2 1

/-- The actual two-parameter logarithmic weight h*cos(theta)-s*P_h. -/
def polynomialRangeLogWeight (p : ℝ × ℝ) : PeriodicC2_STR02969 :=
  p.1 • modeC2 1 - p.2 • polynomialRangeBaseFeature p.1

/-- The normalized actual q_{h,s}, with no selected-root regularity premise. -/
def polynomialRangeReference (p : ℝ × ℝ) : PeriodicHolder_STR02968 :=
  rho_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight p))

def polynomialRangeMean (p : ℝ × ℝ) : ℝ :=
  meanCLM_STR02954 (e0_STR02955 (polynomialRangeBaseFeature p.1) * polynomialRangeReference p)

/-- The feature is centered against the same normalized reference for every (h,s). -/
def polynomialRangeFeature (p : ℝ × ℝ) : PeriodicC2_STR02969 :=
  Real.sqrt 2 • (polynomialRangeBaseFeature p.1 - polynomialRangeMean p • oneC2)

/-- The true physical weighted generator, including the actual logarithmic drift. -/
def polynomialRangeGenerator (p : ℝ × ℝ) : PeriodicHolder_STR02968 :=
  DGPS.Circle.AngularNormalization.a0 •
    (-e2_STR02955 (polynomialRangeFeature p) -
      e1_STR02955 (polynomialRangeLogWeight p) * e1_STR02955 (polynomialRangeFeature p))

def polynomialRangeGradientSq (p : ℝ × ℝ) : PeriodicHolder_STR02968 :=
  DGPS.Circle.AngularNormalization.a0 •
    (e1_STR02955 (polynomialRangeFeature p) * e1_STR02955 (polynomialRangeFeature p))

private theorem baseFeature_val (h t : ℝ) :
    (polynomialRangeBaseFeature h).val t = feature_EX054 h (t : AngCircle) := by
  rw [feature_coe_EX057]
  simp only [polynomialRangeBaseFeature, PeriodicC2_STR02969.val_sub,
    PeriodicC2_STR02969.val_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    modeC2_val, Nat.cast_ofNat, Nat.cast_one, one_mul]

private theorem logWeight_val (p : ℝ × ℝ) (t : ℝ) :
    (polynomialRangeLogWeight p).val t =
      p.1 * angCos (t : AngCircle) - p.2 * feature_EX054 p.1 (t : AngCircle) := by
  simp only [polynomialRangeLogWeight, PeriodicC2_STR02969.val_sub,
    PeriodicC2_STR02969.val_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, baseFeature_val]
  rw [angCos_coe_EX057]
  simp only [modeC2_val, Nat.cast_one, one_mul]

private theorem mean_lift_angular (f : AngCircle → ℝ) :
    meanT_STR02901 (lift f) = ∫ θ, f θ ∂angHaar := by
  change (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..2 * Real.pi, f (t : AngCircle)) = _
  rw [← integral_angSec_STR02962 (fun t : ℝ => f (t : AngCircle))]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by change f ((angSec θ : ℝ) : AngCircle) = f θ; rw [coe_angSec]

/-- The chart reference is pointwise the actual EX054 density for independent parameters. -/
theorem polynomialRangeReference_val (p : ℝ × ℝ) (t : ℝ) :
    (polynomialRangeReference p).val t = density_EX054 p.1 p.2 (t : AngCircle) := by
  rw [polynomialRangeReference, rho_val_STR02954]
  unfold rhoT_STR02901
  simp only [zero_mul, zero_add, e0_val_STR02955]
  simp_rw [logWeight_val]
  change weight_EX054 p.1 p.2 (t : AngCircle) /
    meanT_STR02901 (lift (weight_EX054 p.1 p.2)) = _
  rw [mean_lift_angular]
  rfl

/-- Its scalar centering is exactly the actual EX054 expectation. -/
theorem polynomialRangeMean_eq (p : ℝ × ℝ) :
    polynomialRangeMean p = moment_EX054 p.1 p.2 := by
  rw [polynomialRangeMean, meanCLM_apply_STR02954, moment_eq_integral_EX054]
  have he : (e0_STR02955 (polynomialRangeBaseFeature p.1) * polynomialRangeReference p).val =
      lift (fun θ => feature_EX054 p.1 θ * density_EX054 p.1 p.2 θ) := by
    funext t
    rw [val_mul_STR02954, Pi.mul_apply, e0_val_STR02955, baseFeature_val, polynomialRangeReference_val]
    rfl
  rw [he, mean_lift_angular]

/-- The actual centered feature, including its moving reference mean. -/
theorem polynomialRangeFeature_val (p : ℝ × ℝ) (t : ℝ) :
    (polynomialRangeFeature p).val t =
      Real.sqrt 2 * (feature_EX054 p.1 (t : AngCircle) - moment_EX054 p.1 p.2) := by
  simp only [polynomialRangeFeature, PeriodicC2_STR02969.val_smul,
    PeriodicC2_STR02969.val_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    baseFeature_val, polynomialRangeMean_eq]
  simp only [oneC2_val, mul_one]

/-- Exact feature restriction back to the frozen selected root. -/
theorem polynomialRangeFeature_actual (h : ℝ) :
    e0_STR02955 (polynomialRangeFeature (h, root_EX054 h)) = polynomialEulerFeature h := by
  apply ext_STR02954
  funext t
  rw [e0_val_STR02955, polynomialRangeFeature_val]
  change _ = (polynomialRankOne h).φ (angEquiv.symm (t : AngCircle))
  rw [polynomial_feature_angular]
  simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply, phi_EX057]

private theorem baseFeature_smooth : ContDiff ℝ ∞ polynomialRangeBaseFeature := by
  exact contDiff_const.sub ((contDiff_id.div_const 3).smul contDiff_const)
private theorem logWeight_smooth : ContDiff ℝ ∞ polynomialRangeLogWeight := by
  exact (contDiff_fst.smul contDiff_const).sub
    (contDiff_snd.smul (baseFeature_smooth.comp contDiff_fst))
private theorem reference_smooth : ContDiff ℝ ∞ polynomialRangeReference :=
  rho_smooth_STR02954.comp (contDiff_const.prodMk (e0_STR02955.contDiff.comp logWeight_smooth))
private theorem mean_smooth_range : ContDiff ℝ ∞ polynomialRangeMean :=
  meanCLM_STR02954.contDiff.comp
    ((e0_STR02955.contDiff.comp (baseFeature_smooth.comp contDiff_fst)).mul reference_smooth)
private theorem feature_smooth : ContDiff ℝ ∞ polynomialRangeFeature := by
  unfold polynomialRangeFeature
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => Real.sqrt 2)).smul
    ((baseFeature_smooth.comp contDiff_fst).sub
      (mean_smooth_range.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => oneC2))))

/-- Genuine joint smoothness of the actual analytic extension. -/
theorem polynomialRange_data_smooth :
    ContDiff ℝ ∞ polynomialRangeLogWeight ∧ ContDiff ℝ ∞ polynomialRangeReference ∧
      ContDiff ℝ ∞ polynomialRangeMean ∧ ContDiff ℝ ∞ polynomialRangeFeature ∧
      ContDiff ℝ ∞ polynomialRangeGenerator ∧ ContDiff ℝ ∞ polynomialRangeGradientSq := by
  refine ⟨logWeight_smooth, reference_smooth, mean_smooth_range, feature_smooth, ?_, ?_⟩
  · unfold polynomialRangeGenerator
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => DGPS.Circle.AngularNormalization.a0)).smul
      ((e2_STR02955.contDiff.comp feature_smooth).neg.sub
        ((e1_STR02955.contDiff.comp logWeight_smooth).mul (e1_STR02955.contDiff.comp feature_smooth)))
  · unfold polynomialRangeGradientSq
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => DGPS.Circle.AngularNormalization.a0)).smul
      ((e1_STR02955.contDiff.comp feature_smooth).mul (e1_STR02955.contDiff.comp feature_smooth))

private theorem reference_mass (p : ℝ × ℝ) : meanCLM_STR02954 (polynomialRangeReference p) = 1 := by
  rw [meanCLM_apply_STR02954]
  have he : (polynomialRangeReference p).val =
      rhoT_STR02901 0 (polynomialRangeLogWeight p).val := funext (rho_val_STR02954 _)
  rw [he]
  exact meanT_rho_STR02950 0 (polynomialRangeLogWeight p).isC2.2.1.continuous

/-- Centering holds for every independent (h,s), before restriction to a root. -/
theorem polynomialRangeFeature_centered (p : ℝ × ℝ) :
    meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature p) * polynomialRangeReference p) = 0 := by
  have he : e0_STR02955 (polynomialRangeFeature p) * polynomialRangeReference p =
      Real.sqrt 2 • (e0_STR02955 (polynomialRangeBaseFeature p.1) * polynomialRangeReference p -
        polynomialRangeMean p • polynomialRangeReference p) := by
    apply ext_STR02954
    funext t
    simp only [polynomialRangeFeature, map_smul, map_sub, PeriodicHolder_STR02968.val_smul,
      PeriodicHolder_STR02968.val_sub, val_mul_STR02954, Pi.smul_apply, Pi.sub_apply,
      Pi.mul_apply, smul_eq_mul, e0_val_STR02955]
    simp only [oneC2_val, mul_one]
    ring
  rw [he, map_smul, map_sub, map_smul, reference_mass]
  change Real.sqrt 2 * (polynomialRangeMean p - polynomialRangeMean p * 1) = 0
  ring

private theorem reference_spatial_derivative (p : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (polynomialRangeReference p).val
      ((polynomialRangeReference p).val t * deriv (polynomialRangeLogWeight p).val t) t := by
  have he : (polynomialRangeReference p).val =
      rhoT_STR02901 0 (polynomialRangeLogWeight p).val := funext (rho_val_STR02954 _)
  rw [he]
  simpa only [zero_mul, mul_zero, neg_zero, zero_add] using
    hasDerivAt_rho_STR02950 0 (polynomialRangeLogWeight p).isC2 t

/-- The generator observable really is the physical divergence-form generator of the same
normalized density and centered feature, for every independent parameter. -/
theorem polynomialRangeGenerator_true (p : ℝ × ℝ) (t : ℝ) :
    (polynomialRangeGenerator p).val t =
      -DGPS.Circle.AngularNormalization.a0 *
        deriv (fun s => (polynomialRangeReference p).val s * deriv (polynomialRangeFeature p).val s) t /
          (polynomialRangeReference p).val t := by
  have hd := (reference_spatial_derivative p t).mul
    ((polynomialRangeFeature p).isC2.2.2.1 t).hasDerivAt
  change HasDerivAt (fun s => (polynomialRangeReference p).val s *
    deriv (polynomialRangeFeature p).val s) _ t at hd
  rw [hd.deriv]
  have hq : 0 < (polynomialRangeReference p).val t := by
    rw [polynomialRangeReference_val]
    exact density_pos_EX054 _ _ _
  simp only [polynomialRangeGenerator, PeriodicHolder_STR02968.val_smul,
    PeriodicHolder_STR02968.val_sub, holder_val_neg, val_mul_STR02954,
    Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul,
    e1_val_STR02955, e2_val_STR02955]
  field_simp [hq.ne']
  <;> ring

/-- The true generator is centered by periodic integration by parts, for every parameter. -/
theorem polynomialRangeGenerator_centered (p : ℝ × ℝ) :
    meanCLM_STR02954 (polynomialRangeGenerator p * polynomialRangeReference p) = 0 := by
  let Q := polynomialRangeReference p
  let L := polynomialRangeLogWeight p
  let Φ := polynomialRangeFeature p
  let H := Q * (e1_STR02955 L * e1_STR02955 Φ + e2_STR02955 Φ)
  have hd : ∀ t, HasDerivAt (fun s => Q.val s * deriv Φ.val s) (H.val t) t := by
    intro t
    convert (reference_spatial_derivative p t).mul (Φ.isC2.2.2.1 t).hasDerivAt using 1
    simp only [H, Q, L, Φ, PeriodicHolder_STR02968.val_add, val_mul_STR02954,
      Pi.add_apply, Pi.mul_apply, e1_val_STR02955, e2_val_STR02955]
    ring
  have hper : Q.val (2 * Real.pi) * deriv Φ.val (2 * Real.pi) = Q.val 0 * deriv Φ.val 0 := by
    rw [show Q.val (2 * Real.pi) = Q.val 0 by simpa using Q.isPerHolder.1 0,
      show deriv Φ.val (2 * Real.pi) = deriv Φ.val 0 by
        simpa using (DGPS.Circle.StationaryFlux.periodic_deriv Φ.isC2.1) 0]
  have hm := ftc_mean_STR02955 hd H.isPerHolder.2.1 hper
  have he : polynomialRangeGenerator p * Q = (-DGPS.Circle.AngularNormalization.a0) • H := by
    apply ext_STR02954
    funext t
    simp only [polynomialRangeGenerator, H, Q, L, Φ, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_sub, holder_val_neg,
      PeriodicHolder_STR02968.val_smul, val_mul_STR02954, Pi.add_apply, Pi.sub_apply,
      Pi.neg_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [he, map_smul, meanCLM_apply_STR02954, hm, smul_zero]

end DGPS.Examples.PolynomialSpecies
