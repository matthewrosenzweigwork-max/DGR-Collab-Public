import DGPS.Examples.ThreeSpeciesCircle.InteractingHolderCaptureControl

/-! Exact physical-to-angular scaling in the FULL retained C2 Holder norm.
Mean-zero normalization costs at most one further profile sup norm. This is
an actual norm estimate, with bounded physical derivatives justified by smooth
periodicity, not a supplied norm-equivalence premise. -/

noncomputable section
open MeasureTheory Filter Topology Function
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The profile is in the physical period-one coordinate. The chart is in the
angular period-two-pi coordinate. All three derivative scaling factors are
retained, including the factor in the full Holder seminorm bound. -/
theorem physicalLog_chart_norm_bound (z : PeriodicC2_STR02969) (F : ℝ → ℝ) (C : ℝ)
    (hF : ContDiff ℝ ∞ F) (hp : Periodic F 1)
    (hz : meanT_STR02901 z.val = 0)
    (he : z.val = fun t => F ((2*Real.pi)⁻¹*t)+C) :
    ‖z‖ ≤ 2*supNorm F + (2*Real.pi)⁻¹*supNorm (deriv F) +
      ((2*Real.pi)⁻¹)^2*supNorm (deriv (deriv F)) +
        Real.pi^(1/2 : ℝ)*((2*Real.pi)⁻¹)^3*supNorm (deriv (deriv (deriv F))) := by
  let c := (2*Real.pi)⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  have hfc : ContDiff ℝ ∞ (fun t : ℝ => F (c*t)) :=
    hF.comp (contDiff_const.mul contDiff_id)
  have hzc : ContDiff ℝ ∞ z.val := by rw [he]; exact hfc.add contDiff_const
  have hF1 := (contDiff_infty_iff_deriv.mp hF).2
  have hF2 := (contDiff_infty_iff_deriv.mp hF1).2
  have hF3 := (contDiff_infty_iff_deriv.mp hF2).2
  have b0 := periodic_bdd hp hF.continuous
  have b1 := periodic_bdd (periodic_deriv hp) hF1.continuous
  have b2 := periodic_bdd (periodic_deriv (periodic_deriv hp)) hF2.continuous
  have b3 := periodic_bdd (periodic_deriv (periodic_deriv (periodic_deriv hp))) hF3.continuous
  have hu (t : ℝ) : z.val (2*Real.pi*t) = F t+C := by
    rw [he]
    congr 2
    dsimp only [c]
    field_simp
  have hm : (∫ t in (0 : ℝ)..1, F t)+C=0 := by
    rw [← meanT_eq_unit_STR02901] at hz
    simp_rw [hu] at hz
    rw [intervalIntegral.integral_add (hF.continuous.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const] at hz
    simpa using hz
  have hmean : |∫ t in (0 : ℝ)..1, F t| ≤ supNorm F := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, |F t| := by
        simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
          (f := F) (by norm_num : (0 : ℝ) ≤ 1)
      _ ≤ ∫ _ in (0 : ℝ)..1, supNorm F :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hF.continuous.abs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
          (fun t _ => b0.abs_le_supNorm t)
      _ = supNorm F := by simp
  have hC : |C| ≤ supNorm F := by
    have heC : C = -(∫ t in (0 : ℝ)..1, F t) := by linarith
    rw [heC, abs_neg]
    exact hmean
  have hd1 : deriv z.val = fun t => c*deriv F (c*t) := by
    rw [he]
    funext t
    rw [deriv_add_const, deriv_dil_STR02901]
  have hd2 : deriv (deriv z.val) = fun t => c*(c*deriv (deriv F) (c*t)) := by
    rw [hd1]
    funext t
    rw [deriv_const_mul_field, deriv_dil_STR02901]
  have hd3 : deriv (deriv (deriv z.val)) =
      fun t => c*(c*(c*deriv (deriv (deriv F)) (c*t))) := by
    rw [hd2]
    funext t
    rw [deriv_const_mul_field, deriv_const_mul_field, deriv_dil_STR02901]
  have hs0 : supNorm z.val ≤ 2*supNorm F := by
    apply supNorm_le
    intro t
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [b0.abs_le_supNorm (c*t)])
  have hs1 : supNorm (deriv z.val) ≤ c*supNorm (deriv F) := by
    apply supNorm_le
    intro t
    rw [hd1, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (b1.abs_le_supNorm _) hc.le
  have hs2 : supNorm (deriv (deriv z.val)) ≤ c^2*supNorm (deriv (deriv F)) := by
    apply supNorm_le
    intro t
    rw [hd2, abs_mul, abs_mul, abs_of_pos hc]
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (b2.abs_le_supNorm (c*t)) hc.le) hc.le
    nlinarith only [ht]
  have hs3 : supNorm (deriv (deriv (deriv z.val))) ≤
      c^3*supNorm (deriv (deriv (deriv F))) := by
    apply supNorm_le
    intro t
    rw [hd3, abs_mul, abs_mul, abs_mul, abs_of_pos hc]
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (b3.abs_le_supNorm (c*t)) hc.le) hc.le) hc.le
    nlinarith only [ht]
  have hzc1 := (contDiff_infty_iff_deriv.mp hzc).2
  have hzc2 := (contDiff_infty_iff_deriv.mp hzc1).2
  have bz3 : Bdd (deriv (deriv (deriv z.val))) := by
    refine ⟨c^3*supNorm (deriv (deriv (deriv F))), fun t => ?_⟩
    rw [hd3, abs_mul, abs_mul, abs_mul, abs_of_pos hc]
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (b3.abs_le_supNorm (c*t)) hc.le) hc.le) hc.le
    nlinarith only [ht]
  have hb := c2Holder_norm_le_third_derivative z (hzc2.differentiable (by simp)) bz3
  have hm3 := mul_le_mul_of_nonneg_left hs3 (Real.rpow_nonneg Real.pi_pos.le (1/2 : ℝ))
  change ‖z‖ ≤ 2*supNorm F+c*supNorm (deriv F)+c^2*supNorm (deriv (deriv F))+
    Real.pi^(1/2 : ℝ)*c^3*supNorm (deriv (deriv (deriv F)))
  nlinarith only [hb, hs0, hs1, hs2, hm3]

/-- Actual physical derivative sup norms through order three tending to zero
imply convergence in the angular FULL retained Holder norm. -/
theorem physicalLog_chart_norm_tendsto_zero (z : ℕ → PeriodicC2_STR02969)
    (F : ℕ → ℝ → ℝ) (C : ℕ → ℝ)
    (hF : ∀ n, ContDiff ℝ ∞ (F n)) (hp : ∀ n, Periodic (F n) 1)
    (hz : ∀ n, meanT_STR02901 (z n).val = 0)
    (he : ∀ n, (z n).val = fun t => F n ((2*Real.pi)⁻¹*t)+C n)
    (h0 : Tendsto (fun n => supNorm (F n)) atTop (𝓝 0))
    (h1 : Tendsto (fun n => supNorm (deriv (F n))) atTop (𝓝 0))
    (h2 : Tendsto (fun n => supNorm (deriv (deriv (F n)))) atTop (𝓝 0))
    (h3 : Tendsto (fun n => supNorm (deriv (deriv (deriv (F n))))) atTop (𝓝 0)) :
    Tendsto (fun n => ‖z n‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    physicalLog_chart_norm_bound (z n) (F n) (C n) (hF n) (hp n) (hz n) (he n))
  simpa using (((h0.const_mul 2).add (h1.const_mul (2*Real.pi)⁻¹)).add
    (h2.const_mul (((2*Real.pi)⁻¹)^2))).add
      (h3.const_mul (Real.pi^(1/2 : ℝ)*((2*Real.pi)⁻¹)^3))


private theorem usmall_supNorm_tendsto {F : ℕ → ℝ → ℝ}
    (hb : ∀ n, Bdd (F n)) (h : USmall F) :
    Tendsto (fun n => supNorm (F n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro e he
  filter_upwards [h (e/2) (by positivity)] with n hn
  have hlo : 0 ≤ supNorm (F n) := (abs_nonneg _).trans ((hb n).abs_le_supNorm 0)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  exact (supNorm_le hn).trans_lt (by linarith)

/-- Uniform physical derivatives through order three enter the FULL retained
angular Holder topology. Smooth periodicity supplies actual boundedness at
every index, including the finite prefix. -/
theorem physicalLog_chart_norm_tendsto_of_usmall (z : ℕ → PeriodicC2_STR02969)
    (F : ℕ → ℝ → ℝ) (C : ℕ → ℝ)
    (hF : ∀ n, ContDiff ℝ ∞ (F n)) (hp : ∀ n, Periodic (F n) 1)
    (hz : ∀ n, meanT_STR02901 (z n).val = 0)
    (he : ∀ n, (z n).val = fun t => F n ((2*Real.pi)⁻¹*t)+C n)
    (h0 : USmall F) (h1 : USmall (fun n => deriv (F n)))
    (h2 : USmall (fun n => deriv (deriv (F n))))
    (h3 : USmall (fun n => deriv (deriv (deriv (F n))))) :
    Tendsto (fun n => ‖z n‖) atTop (𝓝 0) := by
  have hF1 := fun n => (contDiff_infty_iff_deriv.mp (hF n)).2
  have hF2 := fun n => (contDiff_infty_iff_deriv.mp (hF1 n)).2
  have hF3 := fun n => (contDiff_infty_iff_deriv.mp (hF2 n)).2
  exact physicalLog_chart_norm_tendsto_zero z F C hF hp hz he
    (usmall_supNorm_tendsto (fun n => periodic_bdd (hp n) (hF n).continuous) h0)
    (usmall_supNorm_tendsto (fun n => periodic_bdd (periodic_deriv (hp n)) (hF1 n).continuous) h1)
    (usmall_supNorm_tendsto (fun n => periodic_bdd (periodic_deriv (periodic_deriv (hp n)))
      (hF2 n).continuous) h2)
    (usmall_supNorm_tendsto (fun n => periodic_bdd
      (periodic_deriv (periodic_deriv (periodic_deriv (hp n)))) (hF3 n).continuous) h3)

end DGPS.Examples.ThreeSpeciesCircle
