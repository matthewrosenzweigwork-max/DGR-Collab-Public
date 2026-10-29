import LeanResearch.PeriodicAttractiveLogGas.SharpPoleMoments
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! The exact positive-logarithm moment in source `eq:log-factorial-integral`.
Disk tail volumes, layer cake and the Gamma integral are an exact equivalent
of the supplied polar calculation. The totalized pole is removed only on its
actual null set; p = 0 is deliberately excluded from the planar integral. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.PositiveLogPoleMoments

def positiveLogPole (Y Z : PlanarSpace) : ℝ := max 0 (-Real.log ‖Z - Y‖)

theorem positiveLogPole_nonneg (Y Z : PlanarSpace) : 0 ≤ positiveLogPole Y Z :=
  le_max_left _ _

@[simp] theorem positiveLogPole_self (Y : PlanarSpace) : positiveLogPole Y Y = 0 := by
  simp [positiveLogPole]

theorem measurable_positiveLogPole (Y : PlanarSpace) : Measurable (positiveLogPole Y) :=
  measurable_const.max (((measurable_id.sub measurable_const).norm.log).neg)

theorem measurable_uncurry_positiveLogPole : Measurable (Function.uncurry positiveLogPole) :=
  measurable_const.max (((measurable_snd.sub measurable_fst).norm.log).neg)

/-- Strict positive tails are disks up to the single totalized pole. -/
theorem positiveLogPole_tail_ae (Y : PlanarSpace) {t : ℝ} (ht : 0 < t) :
    {Z | t < positiveLogPole Y Z} =ᵐ[volume] ball Y (Real.exp (-t)) := by
  filter_upwards [(volume : Measure PlanarSpace).ae_ne Y] with Z hZ
  apply propext
  change t < max 0 (-Real.log ‖Z - Y‖) ↔ dist Z Y < Real.exp (-t)
  rw [lt_max_iff, dist_eq_norm]
  have ht0 : ¬t < 0 := not_lt.mpr ht.le
  simp only [ht0, false_or]
  have hn : 0 < ‖Z - Y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hZ)
  constructor
  · intro h
    have hh := Real.exp_lt_exp.mpr (show Real.log ‖Z - Y‖ < -t by linarith)
    simpa only [Real.exp_log hn] using hh
  · intro h
    have hh : Real.exp (Real.log ‖Z - Y‖) < Real.exp (-t) := by
      simpa only [Real.exp_log hn] using h
    have hh' := Real.exp_lt_exp.mp hh
    linarith

theorem volume_positiveLogPole_tail (Y : PlanarSpace) {t : ℝ} (ht : 0 < t) :
    volume {Z | t < positiveLogPole Y Z} = ENNReal.ofReal (Real.pi * Real.exp (-(2 * t))) := by
  rw [measure_congr (positiveLogPole_tail_ae Y ht), EuclideanSpace.volume_ball_fin_two]
  have he : Real.exp (-t) ^ 2 = Real.exp (-(2 * t)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [← ENNReal.ofReal_pow (Real.exp_pos (-t)).le, he]
  rw [ENNReal.ofReal_mul Real.pi_nonneg]
  exact mul_comm _ _

/-- The radial Gamma integral, with its exact natural exponent and constant. -/
theorem integral_gamma_tail (n : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ n * Real.exp (-(2 * t))) =
      (n.factorial : ℝ) / (2 : ℝ) ^ (n + 1) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, t ^ (((n + 1 : ℕ) : ℝ) - 1) * Real.exp (-(2 * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast]
    _ = (1 / 2 : ℝ) ^ ((n + 1 : ℕ) : ℝ) * Real.Gamma ((n + 1 : ℕ) : ℝ) :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) (by norm_num)
    _ = _ := by
      rw [Real.rpow_natCast, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial]
      simp [div_eq_mul_inv, mul_comm]

/-- Gamma convergence is established before any conversion to a finite real integral. -/
theorem integrable_gamma_tail (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(2 * t))) (Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ n) (Ioi 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast] using
      (Real.GammaIntegral_convergent (s := ((n + 1 : ℕ) : ℝ)) (by positivity))
  have hs : IntegrableOn (fun t : ℝ => Real.exp (-(2 * t)) * (2 * t) ^ n) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u) * u ^ n) 0
      (a := 2) (by norm_num)).mpr (by simpa only [mul_zero] using hi)
  have he : (fun t : ℝ => t ^ n * Real.exp (-(2 * t))) =
      fun t => ((2 : ℝ) ^ n)⁻¹ * (Real.exp (-(2 * t)) * (2 * t) ^ n) := by
    funext t
    rw [mul_pow]
    field_simp
  rw [he]
  exact hs.const_mul _

theorem lintegral_ofReal_gamma_tail (n : ℕ) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t ^ n * Real.exp (-(2 * t)))) =
      ENNReal.ofReal ((n.factorial : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gamma_tail n)]
  · rw [integral_gamma_tail]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le

/-- The exact extended polar moment, derived without assuming its finiteness. -/
theorem lintegral_positiveLogPole_pow (Y : PlanarSpace) {p : ℕ} (hp : 1 ≤ p) :
    (∫⁻ Z, ENNReal.ofReal (positiveLogPole Y Z ^ p)) =
      ENNReal.ofReal (Real.pi * (p.factorial : ℝ) / (2 : ℝ) ^ p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hcast : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp, Nat.cast_one]
  have hcake := lintegral_rpow_eq_lintegral_meas_lt_mul (volume : Measure PlanarSpace)
    (Eventually.of_forall (positiveLogPole_nonneg Y))
    (measurable_positiveLogPole Y).aemeasurable hpR
  calc
    _ = ENNReal.ofReal (p : ℝ) * ∫⁻ t : ℝ in Ioi 0,
        volume {Z | t < positiveLogPole Y Z} * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) := by
      simpa only [Real.rpow_natCast] using hcake
    _ = ENNReal.ofReal (p : ℝ) * ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal Real.pi * ENNReal.ofReal (t ^ (p - 1) * Real.exp (-(2 * t))) := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [volume_positiveLogPole_tail Y ht, hcast, Real.rpow_natCast,
        ENNReal.ofReal_mul Real.pi_nonneg,
        ENNReal.ofReal_mul (pow_nonneg ht.le _)]
      ring
    _ = ENNReal.ofReal (p : ℝ) * (ENNReal.ofReal Real.pi *
        ENNReal.ofReal (((p - 1).factorial : ℝ) / (2 : ℝ) ^ p)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_gamma_tail,
        Nat.sub_add_cancel hp]
    _ = _ := by
      rw [← ENNReal.ofReal_mul Real.pi_nonneg, ← ENNReal.ofReal_mul (Nat.cast_nonneg p)]
      congr 1
      have hf : (p : ℝ) * ((p - 1).factorial : ℝ) = (p.factorial : ℝ) := by
        exact_mod_cast Nat.mul_factorial_pred (show p ≠ 0 by omega)
      rw [← hf]
      ring

theorem integrable_positiveLogPole_pow (Y : PlanarSpace) {p : ℕ} (hp : 1 ≤ p) :
    Integrable (fun Z => positiveLogPole Y Z ^ p) volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_positiveLogPole Y).pow_const p).aestronglyMeasurable
    (Eventually.of_forall fun Z => pow_nonneg (positiveLogPole_nonneg Y Z) p)).mp
  rw [lintegral_positiveLogPole_pow Y hp]
  exact ENNReal.ofReal_ne_top

/-- Source `eq:log-factorial-integral`, including actual integrability. -/
theorem integral_positiveLogPole_pow (Y : PlanarSpace) {p : ℕ} (hp : 1 ≤ p) :
    (∫ Z, positiveLogPole Y Z ^ p) = Real.pi * (p.factorial : ℝ) / (2 : ℝ) ^ p := by
  have hn : 0 ≤ ∫ Z, positiveLogPole Y Z ^ p :=
    integral_nonneg fun Z => pow_nonneg (positiveLogPole_nonneg Y Z) p
  have hc : 0 ≤ Real.pi * (p.factorial : ℝ) / (2 : ℝ) ^ p := by positivity
  have he : ENNReal.ofReal (∫ Z, positiveLogPole Y Z ^ p) =
      ENNReal.ofReal (Real.pi * (p.factorial : ℝ) / (2 : ℝ) ^ p) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_positiveLogPole_pow Y hp)
      (Eventually.of_forall fun Z => pow_nonneg (positiveLogPole_nonneg Y Z) p)]
    exact lintegral_positiveLogPole_pow Y hp
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hc] using hh

/-- Domination by planar volume transfers the exact moment bound, with no
probability or a priori integrability assumption on the dominated measure. -/
theorem positiveLogPole_moment_le_of_measure_le {μ : Measure PlanarSpace}
    (hμ : μ ≤ volume) (Y : PlanarSpace) {p : ℕ} (hp : 1 ≤ p) :
    Integrable (fun Z => positiveLogPole Y Z ^ p) μ ∧
    (∫ Z, positiveLogPole Y Z ^ p ∂μ) ≤ Real.pi * (p.factorial : ℝ) / (2 : ℝ) ^ p ∧
    (∫⁻ Z, ENNReal.ofReal (positiveLogPole Y Z ^ p) ∂μ) ≤
      ENNReal.ofReal (Real.pi * (p.factorial : ℝ) / (2 : ℝ) ^ p) := by
  have hv := integrable_positiveLogPole_pow Y hp
  have hi := hv.mono_measure hμ
  have hb : (∫ Z, positiveLogPole Y Z ^ p ∂μ) ≤ Real.pi * (p.factorial : ℝ) / (2 : ℝ) ^ p := by
    calc
      _ ≤ ∫ Z, positiveLogPole Y Z ^ p := integral_mono_measure hμ
        (Eventually.of_forall fun Z => pow_nonneg (positiveLogPole_nonneg Y Z) p) hv
      _ = _ := integral_positiveLogPole_pow Y hp
  refine ⟨hi, hb, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun Z => pow_nonneg (positiveLogPole_nonneg Y Z) p)]
  exact ENNReal.ofReal_le_ofReal hb

end PeriodicAttractiveLogGas.PositiveLogPoleMoments
