import LeanResearch.PeriodicAttractiveLogGas.BoundaryLayerComparison

/-! Smooth normalization of a regular level. On the zero level the
normalized gradient has norm at most one, while its reciprocal converges
to one uniformly as the positive regularization parameter tends to zero. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace PeriodicAttractiveLogGas.NormalizedLevelFunction
open StationarySard StationaryLevelGeometry StationaryLevelContinuity StationaryCoarea

def denominator (v : Torus → ℝ) (η : ℝ) (z : Torus) : ℝ :=
  Real.sqrt (‖torusOrdinaryGradient v z‖ ^ 2 + η ^ 2)

def normalized (v : Torus → ℝ) (η : ℝ) (z : Torus) : ℝ := v z * (denominator v η z)⁻¹

theorem denominator_pos (v : Torus → ℝ) {η : ℝ} (hη : 0 < η) (z : Torus) :
    0 < denominator v η z := by
  unfold denominator
  exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη))

theorem contDiff_ordinaryGradient_lift {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ContDiff ℝ 1 (fun x : PlanarSpace ↦ torusOrdinaryGradient v (torusQuotient x)) := by
  let R : (PlanarSpace →L[ℝ] ℝ) →L[ℝ] PlanarSpace :=
    (InnerProductSpace.toDual ℝ PlanarSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hh := R.contDiff.comp (hv.fderiv_right (m := 1) (by norm_num))
  simpa only [Function.comp_def, torusOrdinaryGradient_lift, rectangleOrdinaryGradient, R] using! hh

theorem denominator_contDiff {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ 1 (fun x : PlanarSpace ↦ denominator v η (torusQuotient x)) := by
  apply ((contDiff_ordinaryGradient_lift hv).norm_sq (𝕜 := ℝ) |>.add contDiff_const).sqrt
  intro x
  exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη)).ne'

theorem normalized_contDiff {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ 1 (fun x : PlanarSpace ↦ normalized v η (torusQuotient x)) :=
  (hv.of_le (by norm_num)).mul ((denominator_contDiff hv hη).inv
    (fun x ↦ (denominator_pos v hη (torusQuotient x)).ne'))

theorem normalized_eq_zero_iff (v : Torus → ℝ) {η : ℝ} (hη : 0 < η) (z : Torus) :
    normalized v η z = 0 ↔ v z = 0 := by
  rw [normalized, mul_eq_zero]
  simp only [inv_ne_zero (denominator_pos v hη z).ne', or_false]

theorem normalized_pos_iff (v : Torus → ℝ) {η : ℝ} (hη : 0 < η) (z : Torus) :
    0 < normalized v η z ↔ 0 < v z := by
  exact mul_pos_iff_of_pos_right (inv_pos.mpr (denominator_pos v hη z))

theorem normalized_neg_iff (v : Torus → ℝ) {η : ℝ} (hη : 0 < η) (z : Torus) :
    normalized v η z < 0 ↔ v z < 0 := by
  have hp := inv_pos.mpr (denominator_pos v hη z)
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hn) hp.le)) h
  · intro h
    exact mul_neg_of_neg_of_pos h hp

theorem normalized_gradient_at_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {η : ℝ} (hη : 0 < η) {z : Torus} (hz : v z = 0) :
    torusOrdinaryGradient (normalized v η) z =
      (denominator v η z)⁻¹ • torusOrdinaryGradient v z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  have hf := (hv.differentiable (by norm_num) x).hasFDerivAt
  have hd := (((denominator_contDiff hv hη).inv
    (fun y ↦ (denominator_pos v hη (torusQuotient y)).ne')).differentiable (by norm_num) x).hasFDerivAt
  have he : fderiv ℝ (fun y : PlanarSpace ↦ normalized v η (torusQuotient y)) x =
      (denominator v η (torusQuotient x))⁻¹ •
        fderiv ℝ (fun y : PlanarSpace ↦ v (torusQuotient y)) x := by
    simpa only [normalized, hz, zero_smul, zero_add, Pi.mul_apply, Pi.inv_apply] using! (hf.mul hd).fderiv
  rw [torusOrdinaryGradient_lift, rectangleOrdinaryGradient, he,
    torusOrdinaryGradient_lift, rectangleOrdinaryGradient]
  exact map_smul (InnerProductSpace.toDual ℝ PlanarSpace).symm _ _

theorem normalized_gradient_norm_at_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {η : ℝ} (hη : 0 < η) {z : Torus} (hz : v z = 0) :
    ‖torusOrdinaryGradient (normalized v η) z‖ =
      (denominator v η z)⁻¹ * ‖torusOrdinaryGradient v z‖ := by
  rw [normalized_gradient_at_zero hv hη hz, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (denominator_pos v hη z))]

theorem norm_gradient_le_denominator (v : Torus → ℝ) {η : ℝ} (hη : 0 < η) (z : Torus) :
    ‖torusOrdinaryGradient v z‖ ≤ denominator v η z := by
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg ‖torusOrdinaryGradient v z‖) (sq_nonneg η))
  have hd := (denominator_pos v hη z).le
  change 0 ≤ Real.sqrt (‖torusOrdinaryGradient v z‖ ^ 2 + η ^ 2) at hd
  unfold denominator
  nlinarith [norm_nonneg (torusOrdinaryGradient v z), sq_nonneg η]

theorem normalized_gradient_le_one {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {η : ℝ} (hη : 0 < η) {z : Torus} (hz : normalized v η z = 0) :
    ‖torusOrdinaryGradient (normalized v η) z‖ ≤ 1 := by
  rw [normalized_gradient_norm_at_zero hv hη ((normalized_eq_zero_iff v hη z).mp hz)]
  have hd := denominator_pos v hη z
  calc
    (denominator v η z)⁻¹ * ‖torusOrdinaryGradient v z‖ =
        ‖torusOrdinaryGradient v z‖ / denominator v η z := by ring
    _ ≤ 1 := (div_le_iff₀ hd).mpr (by simpa only [one_mul] using norm_gradient_le_denominator v hη z)

theorem normalized_zero_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (ht : (0 : ℝ) ∉ torusCriticalValues v) {η : ℝ} (hη : 0 < η) :
    (0 : ℝ) ∉ torusCriticalValues (normalized v η) := by
  rintro ⟨z, hzgrad, hz⟩
  have hvz := (normalized_eq_zero_iff v hη z).mp hz
  change torusOrdinaryGradient (normalized v η) z = 0 at hzgrad
  rw [normalized_gradient_at_zero hv hη hvz] at hzgrad
  have hg := (smul_eq_zero.mp hzgrad).resolve_left (inv_ne_zero (denominator_pos v hη z).ne')
  exact ht ⟨z, hg, hvz⟩



theorem denominator_le_norm_add (v : Torus → ℝ) {η : ℝ} (hη : 0 < η) (z : Torus) :
    denominator v η z ≤ ‖torusOrdinaryGradient v z‖ + η := by
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg ‖torusOrdinaryGradient v z‖) (sq_nonneg η))
  have hd := (denominator_pos v hη z).le
  have hn := norm_nonneg (torusOrdinaryGradient v z)
  have hm := mul_nonneg hn hη.le
  unfold denominator at hd ⊢
  nlinarith only [hs, hd, hn, hη, hm]

theorem normalized_inverse_gradient_le {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {η c : ℝ} (hη : 0 < η) (hc : 0 < c) {z : Torus}
    (hz : v z = 0) (hgrad : c ≤ ‖torusOrdinaryGradient v z‖) :
    ‖torusOrdinaryGradient (normalized v η) z‖⁻¹ ≤ 1 + η / c := by
  rw [normalized_gradient_norm_at_zero hv hη hz, mul_inv_rev, inv_inv, mul_comm,
    ← div_eq_mul_inv]
  have hn : 0 < ‖torusOrdinaryGradient v z‖ := hc.trans_le hgrad
  apply (div_le_iff₀ hn).mpr
  have hd := denominator_le_norm_add v hη z
  have hm := mul_le_mul_of_nonneg_left hgrad (div_nonneg hη.le hc.le)
  rw [div_mul_cancel₀ η hc.ne'] at hm
  nlinarith only [hd, hm]

theorem normalized_inverse_level_integral_le {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (ht : (0 : ℝ) ∉ torusCriticalValues v) {η c : ℝ} (hη : 0 < η) (hc : 0 < c)
    (hgrad : ∀ z : Torus, v z = 0 → c ≤ ‖torusOrdinaryGradient v z‖) :
    (∫ z in {z | normalized v η z = 0}, ‖torusOrdinaryGradient (normalized v η) z‖⁻¹ ∂physicalCurveMeasure) ≤
      (1 + η / c) * physicalCurveMeasure.real {z | v z = 0} := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by norm_num)
  have hqn := normalized_zero_regular hv ht hη
  have hi := (inverseGradient_integrable_continuousAt_regular (normalized_contDiff hv hη) hqn).1
  have he : {z | normalized v η z = 0} = {z | v z = 0} := by
    ext z
    exact normalized_eq_zero_iff v hη z
  rw [he] at hi ⊢
  let : IsFiniteMeasure (physicalCurveMeasure.restrict {z | v z = 0}) := ⟨by
    simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      StationaryLevelCircles.physicalCurveMeasure_level_lt_top hv1 ht⟩
  have hm : MeasurableSet {z | v z = 0} :=
    (isClosed_eq (continuous_of_contDiff_lift hv1) continuous_const).measurableSet
  have hh := integral_mono_ae hi (integrable_const (1 + η / c)) (by
    filter_upwards [ae_restrict_mem hm] with z hz
    exact normalized_inverse_gradient_le hv hη hc hz (hgrad z hz))
  simpa only [integral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smul_eq_mul, Measure.real, mul_comm] using hh

/-- One positive lower bound for the original regular level controls all
normalizations. The error tends to zero with the regularization parameter. -/
theorem exists_normalized_inverse_level_bound {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (ht : (0 : ℝ) ∉ torusCriticalValues v) :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η →
      (∫ z in {z | normalized v η z = 0}, ‖torusOrdinaryGradient (normalized v η) z‖⁻¹ ∂physicalCurveMeasure) ≤
        (1 + η / c) * physicalCurveMeasure.real {z | v z = 0} := by
  obtain ⟨c, hc, hg⟩ := exists_regular_band_gradient_lower (hv.of_le (by norm_num)) ht
  refine ⟨c, hc, fun η hη ↦ normalized_inverse_level_integral_le hv ht hη hc ?_⟩
  intro z hz
  exact hg z (by rw [hz, sub_self, abs_zero]; exact hc.le)

end PeriodicAttractiveLogGas.NormalizedLevelFunction
