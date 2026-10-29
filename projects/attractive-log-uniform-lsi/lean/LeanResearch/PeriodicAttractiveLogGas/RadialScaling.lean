import LeanResearch.PeriodicAttractiveLogGas.RadialMollifier
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! A single fixed radial probability kernel and its planar dilations.

The fixed function is the already constructed radial kernel at radius `1 / 2`.
Thus its topological support is compactly contained in the open unit ball. The
scaled function is exactly `ε⁻² φ(x / ε)`, where vector division means scalar
multiplication by `ε⁻¹`. Its mass is computed using two-dimensional Lebesgue
measure, without introducing another normalization depending on `ε`.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff Topology

namespace PeriodicAttractiveLogGas

/-- The one fixed nonnegative radial probability kernel used for regularization. -/
def fixedRadialMollifier : PlanarSpace → ℝ :=
  radialMollifier (1 / 2) (by norm_num)

theorem contDiff_fixedRadialMollifier : ContDiff ℝ ∞ fixedRadialMollifier :=
  contDiff_radialMollifier (1 / 2) (by norm_num)

theorem fixedRadialMollifier_nonneg (x : PlanarSpace) :
    0 ≤ fixedRadialMollifier x :=
  radialMollifier_nonneg (1 / 2) (by norm_num) x

theorem integrable_fixedRadialMollifier : Integrable fixedRadialMollifier volume :=
  integrable_radialMollifier (1 / 2) (by norm_num)

theorem integral_fixedRadialMollifier : ∫ x, fixedRadialMollifier x = 1 :=
  integral_radialMollifier (1 / 2) (by norm_num)

theorem fixedRadialMollifier_eq_of_norm_eq {x y : PlanarSpace} (hxy : ‖x‖ = ‖y‖) :
    fixedRadialMollifier x = fixedRadialMollifier y :=
  radialMollifier_eq_of_norm_eq (1 / 2) (by norm_num) hxy

theorem fixedRadialMollifier_neg (x : PlanarSpace) :
    fixedRadialMollifier (-x) = fixedRadialMollifier x :=
  radialMollifier_neg (1 / 2) (by norm_num) x

theorem support_fixedRadialMollifier_subset :
    Function.support fixedRadialMollifier ⊆ ball (0 : PlanarSpace) (1 / 2) :=
  support_radialMollifier_subset (1 / 2) (by norm_num)

theorem tsupport_fixedRadialMollifier_subset_closedBall :
    tsupport fixedRadialMollifier ⊆ closedBall (0 : PlanarSpace) (1 / 2) :=
  tsupport_radialMollifier_subset (1 / 2) (by norm_num)

theorem tsupport_fixedRadialMollifier_subset_ball :
    tsupport fixedRadialMollifier ⊆ ball (0 : PlanarSpace) 1 := by
  intro x hx
  have hx' := tsupport_fixedRadialMollifier_subset_closedBall hx
  rw [mem_closedBall_zero_iff] at hx'
  rw [mem_ball_zero_iff]
  linarith

theorem hasCompactSupport_fixedRadialMollifier : HasCompactSupport fixedRadialMollifier :=
  hasCompactSupport_radialMollifier (1 / 2) (by norm_num)

/-- Compact containment uses the topological support, not only the nonzero set. -/
theorem fixedRadialMollifier_compactlySupportedIn_unitBall :
    IsCompact (tsupport fixedRadialMollifier) ∧
      tsupport fixedRadialMollifier ⊆ ball (0 : PlanarSpace) 1 :=
  ⟨hasCompactSupport_fixedRadialMollifier, tsupport_fixedRadialMollifier_subset_ball⟩

theorem fixedRadialMollifier_eq_zero_of_half_le_norm {x : PlanarSpace}
    (hx : (1 / 2 : ℝ) ≤ ‖x‖) : fixedRadialMollifier x = 0 :=
  radialMollifier_eq_zero_of_le_norm (1 / 2) (by norm_num) hx

theorem fixedRadialMollifier_zero_pos : 0 < fixedRadialMollifier 0 := by
  unfold fixedRadialMollifier radialMollifier
  rw [rawRadialMollifier_zero]
  exact div_pos zero_lt_one (integral_rawRadialMollifier_pos (1 / 2) (by norm_num))

/-- The fixed bump attains its finite maximum at the origin. -/
theorem fixedRadialMollifier_le_value_zero (x : PlanarSpace) :
    fixedRadialMollifier x ≤ fixedRadialMollifier 0 := by
  unfold fixedRadialMollifier radialMollifier
  rw [rawRadialMollifier_zero]
  exact div_le_div_of_nonneg_right
    (rawRadialMollifier_le_one (1 / 2) (by norm_num) x)
    (integral_rawRadialMollifier_pos (1 / 2) (by norm_num)).le

theorem isGreatest_range_fixedRadialMollifier :
    IsGreatest (Set.range fixedRadialMollifier) (fixedRadialMollifier 0) := by
  refine ⟨⟨0, rfl⟩, ?_⟩
  rintro y ⟨x, rfl⟩
  exact fixedRadialMollifier_le_value_zero x

theorem sSup_range_fixedRadialMollifier :
    sSup (Set.range fixedRadialMollifier) = fixedRadialMollifier 0 :=
  isGreatest_range_fixedRadialMollifier.csSup_eq

/-- The source scaling of the fixed kernel. Positive scales are used below. -/
def scaledRadialMollifier (ε : ℝ) (x : PlanarSpace) : ℝ :=
  (ε ^ 2)⁻¹ * fixedRadialMollifier (ε⁻¹ • x)

/-- Scalar division on the Euclidean domain is ordinary coordinate division. -/
theorem scaledRadialMollifier_argument_apply (ε : ℝ) (x : PlanarSpace) (j : Fin 2) :
    (ε⁻¹ • x) j = x j / ε := by
  change ε⁻¹ * x j = x j / ε
  rw [div_eq_mul_inv, mul_comm]

/-- The real-power convention gives exactly the source's factor `ε ^ (-2)`. -/
theorem scaledRadialMollifier_eq_rpow (ε : ℝ) (hε : 0 < ε) (x : PlanarSpace) :
    scaledRadialMollifier ε x =
      ε ^ (-2 : ℝ) * fixedRadialMollifier (ε⁻¹ • x) := by
  rw [Real.rpow_neg hε.le, Real.rpow_ofNat]
  rfl

theorem contDiff_scaledRadialMollifier (ε : ℝ) :
    ContDiff ℝ ∞ (scaledRadialMollifier ε) := by
  unfold scaledRadialMollifier
  exact contDiff_const.mul
    (contDiff_fixedRadialMollifier.comp
      (by
        convert (ε⁻¹ • ContinuousLinearMap.id ℝ PlanarSpace).contDiff using 1
        ext x
        rfl))

theorem scaledRadialMollifier_nonneg (ε : ℝ) (x : PlanarSpace) :
    0 ≤ scaledRadialMollifier ε x :=
  mul_nonneg (inv_nonneg.mpr (sq_nonneg ε))
    (fixedRadialMollifier_nonneg (ε⁻¹ • x))

theorem scaledRadialMollifier_eq_of_norm_eq (ε : ℝ) {x y : PlanarSpace}
    (hxy : ‖x‖ = ‖y‖) : scaledRadialMollifier ε x = scaledRadialMollifier ε y := by
  unfold scaledRadialMollifier
  congr 1
  exact fixedRadialMollifier_eq_of_norm_eq (by simp only [norm_smul, hxy])

theorem scaledRadialMollifier_neg (ε : ℝ) (x : PlanarSpace) :
    scaledRadialMollifier ε (-x) = scaledRadialMollifier ε x :=
  scaledRadialMollifier_eq_of_norm_eq ε (norm_neg x)

theorem support_scaledRadialMollifier_subset (ε : ℝ) (hε : 0 < ε) :
    Function.support (scaledRadialMollifier ε) ⊆ ball (0 : PlanarSpace) (ε / 2) := by
  intro x hx
  have hf : fixedRadialMollifier (ε⁻¹ • x) ≠ 0 := by
    intro hf
    exact hx (by simp only [scaledRadialMollifier, hf, mul_zero])
  have hb := support_fixedRadialMollifier_subset hf
  have hn : ε⁻¹ * ‖x‖ < (1 / 2 : ℝ) := by
    simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε)] using hb
  have hn' := mul_lt_mul_of_pos_left hn hε
  rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at hn'
  rw [mem_ball_zero_iff]
  simpa only [div_eq_mul_inv, one_mul] using hn'

theorem tsupport_scaledRadialMollifier_subset_closedBall (ε : ℝ) (hε : 0 < ε) :
    tsupport (scaledRadialMollifier ε) ⊆ closedBall (0 : PlanarSpace) (ε / 2) :=
  closure_minimal
    ((support_scaledRadialMollifier_subset ε hε).trans ball_subset_closedBall)
    isClosed_closedBall

theorem tsupport_scaledRadialMollifier_subset_ball (ε : ℝ) (hε : 0 < ε) :
    tsupport (scaledRadialMollifier ε) ⊆ ball (0 : PlanarSpace) ε := by
  intro x hx
  have hx' := tsupport_scaledRadialMollifier_subset_closedBall ε hε hx
  rw [mem_closedBall_zero_iff] at hx'
  rw [mem_ball_zero_iff]
  linarith

theorem hasCompactSupport_scaledRadialMollifier (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (scaledRadialMollifier ε) :=
  (isCompact_closedBall (0 : PlanarSpace) (ε / 2)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_scaledRadialMollifier_subset_closedBall ε hε)

theorem scaledRadialMollifier_compactlySupportedIn_ball (ε : ℝ) (hε : 0 < ε) :
    IsCompact (tsupport (scaledRadialMollifier ε)) ∧
      tsupport (scaledRadialMollifier ε) ⊆ ball (0 : PlanarSpace) ε :=
  ⟨hasCompactSupport_scaledRadialMollifier ε hε,
    tsupport_scaledRadialMollifier_subset_ball ε hε⟩

theorem scaledRadialMollifier_eq_zero_of_half_le_norm (ε : ℝ) (hε : 0 < ε)
    {x : PlanarSpace} (hx : ε / 2 ≤ ‖x‖) : scaledRadialMollifier ε x = 0 := by
  apply Function.notMem_support.mp
  intro hs
  exact (not_lt_of_ge hx)
    (mem_ball_zero_iff.mp (support_scaledRadialMollifier_subset ε hε hs))

theorem integrable_scaledRadialMollifier (ε : ℝ) (hε : 0 < ε) :
    Integrable (scaledRadialMollifier ε) volume :=
  (contDiff_scaledRadialMollifier ε).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_scaledRadialMollifier ε hε)

/-- The inverse dilation contributes exactly `ε²` under planar Lebesgue measure. -/
theorem integral_fixedRadialMollifier_inv_smul (ε : ℝ) (hε : 0 < ε) :
    (∫ x : PlanarSpace, fixedRadialMollifier (ε⁻¹ • x)) = ε ^ 2 := by
  simpa [PlanarSpace, integral_fixedRadialMollifier, smul_eq_mul] using
    (Measure.integral_comp_inv_smul_of_nonneg (volume : Measure PlanarSpace)
      fixedRadialMollifier hε.le)

theorem integral_scaledRadialMollifier (ε : ℝ) (hε : 0 < ε) :
    ∫ x, scaledRadialMollifier ε x = 1 := by
  simp only [scaledRadialMollifier, integral_const_mul,
    integral_fixedRadialMollifier_inv_smul ε hε]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hε.ne')

/-- The fixed maximum supplies a uniform constant, independent of the scale. -/
theorem scaledRadialMollifier_le_value_zero_div (ε : ℝ) (x : PlanarSpace) :
    scaledRadialMollifier ε x ≤ fixedRadialMollifier 0 / ε ^ 2 := by
  calc
    scaledRadialMollifier ε x ≤ (ε ^ 2)⁻¹ * fixedRadialMollifier 0 :=
      mul_le_mul_of_nonneg_left (fixedRadialMollifier_le_value_zero (ε⁻¹ • x))
        (inv_nonneg.mpr (sq_nonneg ε))
    _ = fixedRadialMollifier 0 / ε ^ 2 := by rw [div_eq_mul_inv, mul_comm]

theorem norm_scaledRadialMollifier_le (ε : ℝ) (hε : 0 < ε) (x : PlanarSpace) :
    ‖scaledRadialMollifier ε x‖ ≤ fixedRadialMollifier 0 * ε ^ (-2 : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (scaledRadialMollifier_nonneg ε x),
    Real.rpow_neg hε.le, Real.rpow_ofNat, ← div_eq_mul_inv]
  exact scaledRadialMollifier_le_value_zero_div ε x

theorem exists_uniform_bound_scaledRadialMollifier :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ x : PlanarSpace,
      ‖scaledRadialMollifier ε x‖ ≤ C * ε ^ (-2 : ℝ) :=
  ⟨fixedRadialMollifier 0, fixedRadialMollifier_zero_pos,
    fun ε hε x => norm_scaledRadialMollifier_le ε hε x⟩

end PeriodicAttractiveLogGas
