import LeanResearch.PeriodicAttractiveLogGas.TorusDistance
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Actual integrability of the Euclidean quotient singularities for the
specified probability Haar measure. The radial exponent is real. Transport
uses the entire centered half-open fundamental square, on which the quotient
norm agrees exactly with the Euclidean norm. No Green-function bound is used.
-/

noncomputable section
open MeasureTheory Set Filter Metric

namespace PeriodicAttractiveLogGas

theorem torusEuclideanNorm_quotient_eq_of_mem_centeredBox {x : PlanarSpace}
    (hx : x ∈ euclideanFundamentalBox (centeredBoxAnchor 0)) :
    torusEuclideanNorm (torusQuotient x) = ‖x‖ := by
  rw [← norm_centeredLift, centeredLift_torusQuotient_of_mem_box hx]

theorem centeredFundamentalBox_subset_closedBall :
    euclideanFundamentalBox (centeredBoxAnchor 0) ⊆
      closedBall (0 : PlanarSpace) (Real.sqrt (1 / 2 : ℝ)) := by
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  rw [← torusEuclideanNorm_quotient_eq_of_mem_centeredBox hx]
  exact torusEuclideanNorm_le_sqrt_half _

/-- The finite-dimensional radial-integrability theorem applies to every real
exponent below two; a nonnegative-exponent hypothesis is not needed. -/
theorem locallyIntegrable_planar_norm_rpow_neg (p : ℝ) (hp : p < 2) :
    LocallyIntegrable (fun x : PlanarSpace ↦ ‖x‖ ^ (-p)) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := p) (by simp)
    (by simpa [PlanarSpace] using hp) ?_ ?_
  · exact Eventually.of_forall fun x ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),
        one_mul, le_refl]
  · exact (measurable_norm.pow_const (-p)).aestronglyMeasurable

theorem integrableOn_centeredBox_norm_rpow_neg (p : ℝ) (hp : p < 2) :
    IntegrableOn (fun x : PlanarSpace ↦ ‖x‖ ^ (-p))
      (euclideanFundamentalBox (centeredBoxAnchor 0)) volume :=
  ((locallyIntegrable_planar_norm_rpow_neg p hp).integrableOn_isCompact
    (isCompact_closedBall (0 : PlanarSpace) (Real.sqrt (1 / 2 : ℝ)))).mono_set
      centeredFundamentalBox_subset_closedBall

/-- In particular this gives the full requested range `0 ≤ p < 2`, without
replacing the exponent by a natural number. Powers at zero are totalized. -/
theorem integrable_torusEuclideanNorm_rpow_neg (p : ℝ) (hp : p < 2) :
    Integrable (fun z : Torus ↦ torusEuclideanNorm z ^ (-p)) torusMeasure := by
  have hbox : IntegrableOn
      (fun x : PlanarSpace ↦ torusEuclideanNorm (torusQuotient x) ^ (-p))
      (euclideanFundamentalBox (centeredBoxAnchor 0)) volume := by
    apply (integrableOn_centeredBox_norm_rpow_neg p hp).congr_fun
      (hs := measurableSet_euclideanFundamentalBox _)
    intro x hx
    change ‖x‖ ^ (-p) = torusEuclideanNorm (torusQuotient x) ^ (-p)
    rw [torusEuclideanNorm_quotient_eq_of_mem_centeredBox hx]
  exact ((measurePreserving_torusQuotient_box (centeredBoxAnchor 0)).integrable_comp
    (measurable_torusEuclideanNorm.pow_const (-p)).aestronglyMeasurable).mp hbox

theorem integrable_torusEuclideanNorm_inv :
    Integrable (fun z : Torus ↦ (torusEuclideanNorm z)⁻¹) torusMeasure := by
  simpa only [Real.rpow_neg_one] using
    integrable_torusEuclideanNorm_rpow_neg 1 (by norm_num)

theorem torusEuclideanNorm_le_one (z : Torus) : torusEuclideanNorm z ≤ 1 := by
  calc
    torusEuclideanNorm z ≤ Real.sqrt (1 / 2 : ℝ) := torusEuclideanNorm_le_sqrt_half z
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
    _ = 1 := Real.sqrt_one

/-- A direct real-exponent logarithmic moment bound. It is valid also at
`r = 0` with the library's totalized logarithm and inverse. -/
theorem abs_log_rpow_le_const_mul_inv {p r : ℝ} (hp : 0 < p)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.log r| ^ p ≤ p ^ p * r⁻¹ := by
  have hi : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0
  have hlog : |Real.log r| ≤ p * ((r⁻¹) ^ p⁻¹) := by
    calc
      |Real.log r| = Real.log r⁻¹ := by
        rw [abs_of_nonpos (Real.log_nonpos hr0 hr1), Real.log_inv]
      _ ≤ (r⁻¹) ^ p⁻¹ / p⁻¹ := Real.log_le_rpow_div hi (inv_pos.mpr hp)
      _ = p * ((r⁻¹) ^ p⁻¹) := by rw [div_eq_mul_inv, inv_inv, mul_comm]
  calc
    |Real.log r| ^ p ≤ (p * ((r⁻¹) ^ p⁻¹)) ^ p :=
      Real.rpow_le_rpow (abs_nonneg _) hlog hp.le
    _ = p ^ p * r⁻¹ := by
      rw [Real.mul_rpow hp.le (Real.rpow_nonneg hi _), Real.rpow_inv_rpow hi hp.ne']

/-- Every strictly positive real logarithmic moment is integrable; in
particular this covers every real exponent at least one. -/
theorem integrable_abs_log_torusEuclideanNorm_rpow (p : ℝ) (hp : 0 < p) :
    Integrable (fun z : Torus ↦ |Real.log (torusEuclideanNorm z)| ^ p) torusMeasure := by
  have hm : Measurable (fun z : Torus ↦ |Real.log (torusEuclideanNorm z)| ^ p) := by
    simpa only [Real.norm_eq_abs] using
      (measurable_torusEuclideanNorm.log.norm.pow_const p)
  refine (integrable_torusEuclideanNorm_inv.const_mul (p ^ p)).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact abs_log_rpow_le_const_mul_inv hp (torusEuclideanNorm_nonneg z)
    (torusEuclideanNorm_le_one z)

theorem integrable_abs_log_torusEuclideanNorm_rpow_of_one_le (p : ℝ) (hp : 1 ≤ p) :
    Integrable (fun z : Torus ↦ |Real.log (torusEuclideanNorm z)| ^ p) torusMeasure :=
  integrable_abs_log_torusEuclideanNorm_rpow p (lt_of_lt_of_le zero_lt_one hp)

theorem integrable_abs_log_torusEuclideanNorm :
    Integrable (fun z : Torus ↦ |Real.log (torusEuclideanNorm z)|) torusMeasure := by
  simpa only [Real.rpow_one] using
    integrable_abs_log_torusEuclideanNorm_rpow 1 zero_lt_one

theorem integrable_log_torusEuclideanNorm :
    Integrable (fun z : Torus ↦ Real.log (torusEuclideanNorm z)) torusMeasure := by
  refine integrable_abs_log_torusEuclideanNorm.mono'
    measurable_torusEuclideanNorm.log.aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
  simp only [Real.norm_eq_abs, le_refl]

end PeriodicAttractiveLogGas
