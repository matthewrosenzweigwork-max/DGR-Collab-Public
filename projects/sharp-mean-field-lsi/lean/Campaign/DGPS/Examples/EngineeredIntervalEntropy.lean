import DGPS.Examples.EngineeredIntervalWeak
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Interval supremum and entropy estimates for EX040

The supremum estimate uses FTC for the square and Young's inequality. It requires no
periodic extension and imposes no condition on endpoint traces.
-/

open MeasureTheory Real Set Filter Topology

namespace DGPS.Examples

/-- The interval Sobolev supremum estimate in a form adapted to entropy optimization. -/
theorem interval_sup_sq_young_EX040 {a b ε : ℝ} (hab : a < b) (hε : 0 < ε)
    {w : ℝ → ℝ} (hw : AbsolutelyContinuousOnInterval w a b)
    (hE : IntervalIntegrable (fun x => deriv w x ^ 2) volume a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    w t ^ 2 ≤ (∫ x in a..b, w x ^ 2) / (b - a) +
      (∫ x in a..b, w x ^ 2) / ε + ε * (∫ x in a..b, deriv w x ^ 2) := by
  have hwc : ContinuousOn w (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hw.continuousOn
  have hwi : IntervalIntegrable (fun x => w x ^ 2) volume a b :=
    (hw.continuousOn.pow 2).intervalIntegrable
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab.le) (hwc.pow 2)
  have hmean : w s ^ 2 ≤ (∫ x in a..b, w x ^ 2) / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    have hmono := intervalIntegral.integral_mono_on hab.le
      (intervalIntegrable_const (c := w s ^ 2)) hwi (fun x hx => hmin hx)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (w s ^ 2)]
      using hmono
  let B : ℝ → ℝ := fun x => w x ^ 2 / ε + ε * deriv w x ^ 2
  have hBi : IntervalIntegrable B volume a b := (hwi.div_const ε).add (hE.const_mul ε)
  have hB0 : ∀ x : ℝ, 0 ≤ B x := fun x =>
    add_nonneg (div_nonneg (sq_nonneg _) hε.le) (mul_nonneg hε.le (sq_nonneg _))
  have hY : ∀ x : ℝ, |deriv w x * w x + w x * deriv w x| ≤ B x := by
    intro x
    have heq : B x = (w x ^ 2 + (ε * deriv w x) ^ 2) / ε := by
      dsimp [B]
      field_simp [hε.ne']
    rw [heq, le_div_iff₀ hε]
    have habs : |deriv w x * w x + w x * deriv w x| * ε =
        |(deriv w x * w x + w x * deriv w x) * ε| := by
      rw [abs_mul, abs_of_pos hε]
    rw [habs, abs_le]
    constructor <;> nlinarith [sq_nonneg (w x - ε * deriv w x),
      sq_nonneg (w x + ε * deriv w x)]
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact uIcc_subset_Icc hs ht
  have hwsub := hw.mono hsub
  have hftc : (∫ x in s..t, deriv w x * w x + w x * deriv w x) =
      w t ^ 2 - w s ^ 2 := by
    simpa only [pow_two] using hwsub.integral_deriv_mul_eq_sub hwsub
  have hdiff : |w t ^ 2 - w s ^ 2| ≤ ∫ x in a..b, B x := by
    calc
      _ = ‖∫ x in s..t, deriv w x * w x + w x * deriv w x‖ := by
        rw [hftc, Real.norm_eq_abs]
      _ ≤ |∫ x in s..t, B x| :=
        intervalIntegral.norm_integral_le_abs_of_norm_le
          (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hY x)
          (hBi.mono_set hsub)
      _ ≤ |∫ x in a..b, B x| :=
        intervalIntegral.abs_integral_mono_interval
          (uIoc_subset_uIoc_of_uIcc_subset_uIcc hsub)
          (Eventually.of_forall hB0) hBi
      _ = ∫ x in a..b, B x :=
        abs_of_nonneg (intervalIntegral.integral_nonneg hab.le fun x _ => hB0 x)
  have hBint : (∫ x in a..b, B x) =
      (∫ x in a..b, w x ^ 2) / ε + ε * (∫ x in a..b, deriv w x ^ 2) := by
    change (∫ x in a..b, w x ^ 2 / ε + ε * deriv w x ^ 2) = _
    rw [intervalIntegral.integral_add (hwi.div_const ε) (hE.const_mul ε),
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  rw [hBint] at hdiff
  linarith [le_abs_self (w t ^ 2 - w s ^ 2)]

/-- Pointwise logarithmic form of the interval estimate. Integrating it against w² gives
the fixed-interval entropy estimate with the exact one-half logarithmic defect. -/
theorem interval_log_sup_EX040 {a b δ : ℝ} (hab : a < b) (hL : 1 ≤ b - a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {w : ℝ → ℝ}
    (hw : AbsolutelyContinuousOnInterval w a b)
    (hE : IntervalIntegrable (fun x => deriv w x ^ 2) volume a b)
    (hM : 0 < ∫ x in a..b, w x ^ 2) {t : ℝ} (ht : t ∈ Icc a b) (hwt : w t ≠ 0) :
    Real.log (w t ^ 2 / (∫ x in a..b, w x ^ 2)) ≤
      δ * ((∫ x in a..b, deriv w x ^ 2) / (∫ x in a..b, w x ^ 2)) +
        Real.log 2 - (1 / 2) * Real.log δ := by
  let M : ℝ := ∫ x in a..b, w x ^ 2
  let E : ℝ := ∫ x in a..b, deriv w x ^ 2
  let ε : ℝ := Real.sqrt δ
  have hMp : 0 < M := hM
  have hEp : 0 ≤ E := intervalIntegral.integral_nonneg hab.le fun _ _ => sq_nonneg _
  have hεp : 0 < ε := Real.sqrt_pos.mpr hδ
  have hεsq : ε ^ 2 = δ := Real.sq_sqrt hδ.le
  have hε1 : ε ≤ 1 := by nlinarith [Real.sqrt_nonneg δ]
  have hMdiv : M / (b - a) ≤ M := by
    apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
    nlinarith [mul_nonneg hMp.le (sub_nonneg.mpr hL)]
  have hsup : w t ^ 2 ≤ M + M / ε + ε * E := by
    have hs := interval_sup_sq_young_EX040 hab hεp hw hE ht
    change w t ^ 2 ≤ M / (b - a) + M / ε + ε * E at hs
    linarith
  have hY : ε * (w t ^ 2 / M) ≤ 2 + δ * (E / M) := by
    calc
      _ ≤ ε * ((M + M / ε + ε * E) / M) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsup hMp.le) hεp.le
      _ = ε + 1 + δ * (E / M) := by
        rw [← hεsq]
        field_simp [hMp.ne', hεp.ne']
      _ ≤ 2 + δ * (E / M) := by linarith
  have hwp : 0 < w t ^ 2 / M := div_pos (sq_pos_of_ne_zero hwt) hMp
  have hl := Real.log_le_sub_one_of_pos (show 0 < ε * (w t ^ 2 / M) / 2 by positivity)
  rw [Real.log_div (mul_pos hεp hwp).ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_mul hεp.ne' hwp.ne'] at hl
  have hlogε : Real.log ε = Real.log δ / 2 := Real.log_sqrt hδ.le
  rw [hlogε] at hl
  change Real.log (w t ^ 2 / M) ≤ δ * (E / M) + Real.log 2 - (1 / 2) * Real.log δ
  nlinarith [mul_nonneg hδ.le (div_nonneg hEp hMp.le)]

/-- The fixed-interval entropy estimate on the full AC finite-energy domain, including the
zero-mass case. The logarithmic defect has coefficient exactly one half. -/
theorem interval_entropy_estimate_EX040 {a b δ : ℝ} (hab : a < b) (hL : 1 ≤ b - a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {w : ℝ → ℝ}
    (hw : AbsolutelyContinuousOnInterval w a b)
    (hE : IntervalIntegrable (fun x => deriv w x ^ 2) volume a b) :
    (∫ x in a..b, w x ^ 2 * Real.log (w x ^ 2 / (∫ y in a..b, w y ^ 2))) ≤
      δ * (∫ x in a..b, deriv w x ^ 2) +
        (Real.log 2 - (1 / 2) * Real.log δ) * (∫ x in a..b, w x ^ 2) := by
  let M : ℝ := ∫ x in a..b, w x ^ 2
  let E : ℝ := ∫ x in a..b, deriv w x ^ 2
  let K : ℝ := Real.log 2 - (1 / 2) * Real.log δ
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg hab.le fun _ _ => sq_nonneg _
  have hE0 : 0 ≤ E := intervalIntegral.integral_nonneg hab.le fun _ _ => sq_nonneg _
  change (∫ x in a..b, w x ^ 2 * Real.log (w x ^ 2 / M)) ≤ δ * E + K * M
  by_cases hMz : M = 0
  · simp only [hMz, div_zero, Real.log_zero, mul_zero, intervalIntegral.integral_zero,
      add_zero]
    exact mul_nonneg hδ.le hE0
  have hMp : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hMz)
  have hw2 : ContinuousOn (fun x => w x ^ 2) (uIcc a b) := hw.continuousOn.pow 2
  have heq : (fun x => w x ^ 2 * Real.log (w x ^ 2 / M)) =
      fun x => w x ^ 2 * Real.log (w x ^ 2) - Real.log M * w x ^ 2 := by
    funext x
    by_cases hx : w x = 0
    · simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, mul_zero, sub_zero]
    · rw [Real.log_div (pow_ne_zero 2 hx) hMz]
      ring
  have hEi : IntervalIntegrable (fun x => w x ^ 2 * Real.log (w x ^ 2 / M)) volume a b := by
    rw [heq]
    exact ((Real.continuous_mul_log.comp_continuousOn hw2).sub
      (continuousOn_const.mul hw2)).intervalIntegrable
  have hRi : IntervalIntegrable (fun x => (δ * (E / M) + K) * w x ^ 2) volume a b :=
    (continuousOn_const.mul hw2).intervalIntegrable
  have hle : (∫ x in a..b, w x ^ 2 * Real.log (w x ^ 2 / M)) ≤
      ∫ x in a..b, (δ * (E / M) + K) * w x ^ 2 := by
    apply intervalIntegral.integral_mono_on hab.le hEi hRi
    intro x hx
    by_cases hwx : w x = 0
    · simp only [hwx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, mul_zero, le_refl]
    · have hl := interval_log_sup_EX040 hab hL hδ hδ1 hw hE hMp hx hwx
      have hl2 : Real.log (w x ^ 2 / M) ≤ δ * (E / M) + K := by
        simpa only [K, add_sub_assoc] using hl
      exact (mul_le_mul_of_nonneg_left hl2 (sq_nonneg _)).trans_eq (mul_comm _ _)
  rw [intervalIntegral.integral_const_mul] at hle
  change (∫ x in a..b, w x ^ 2 * Real.log (w x ^ 2 / M)) ≤
    (δ * (E / M) + K) * M at hle
  have hr : (δ * (E / M) + K) * M = δ * E + K * M := by
    field_simp [hMz]
  rwa [hr] at hle

end DGPS.Examples
