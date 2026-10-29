import DGRHS.Gaussian.GaussianLogFrullani

/-! Actual anchored finite infrared truncations of the literal logarithmic kernel.
Fixed sign and the genuine Frullani integral give absolute log domination;
actual T->infinity convergence uses that proper dominating function.
This alternate finite counterterm is not identified with the printed C_phi,T.
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology
namespace DGRHS.Gaussian

def gaussianLogAnchored (T r : ℝ) : ℝ :=
  ∫ t : ℝ in Ioc 0 T, t⁻¹ *
    (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))

lemma gaussianLog_profile_difference_nonneg (r t : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 < t) :
    0 ≤ t⁻¹ * (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2))) := by
  apply mul_nonneg (inv_nonneg.mpr ht.le)
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right
  · nlinarith
  · positivity

lemma gaussianLog_profile_difference_nonpos (r t : ℝ)
    (hr1 : 1 ≤ r) (ht : 0 < t) :
    t⁻¹ * (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2))) ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le)
  apply sub_nonpos.mpr
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right
  · nlinarith
  · positivity

lemma integral_norm_gaussianLog_profile_difference (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, ‖t⁻¹ *
      (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))‖) = |Real.log r| := by
  by_cases hr1 : r ≤ 1
  · have he : (fun t : ℝ => ‖t⁻¹ *
        (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))‖) =ᵐ[volume.restrict (Ioi 0)]
        (fun t => t⁻¹ * (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianLog_profile_difference_nonneg r t hr.le hr1 ht)]
    rw [integral_congr_ae he, integral_gaussianLog_profile_difference r hr,
      abs_of_nonpos (Real.log_nonpos hr.le hr1)]
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have he : (fun t : ℝ => ‖t⁻¹ *
        (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))‖) =ᵐ[volume.restrict (Ioi 0)]
        (fun t => -(t⁻¹ * (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2))))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonpos (gaussianLog_profile_difference_nonpos r t hr1' ht)]
    rw [integral_congr_ae he, integral_neg, integral_gaussianLog_profile_difference r hr,
      abs_of_nonneg (Real.log_nonneg hr1')]
    ring

lemma gaussianLogAnchored_eq_indicator (T r : ℝ) :
    gaussianLogAnchored T r = ∫ t : ℝ in Ioi 0, (Iic T).indicator
      (fun t => t⁻¹ * (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))) t := by
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have he : Iic T ∩ Ioi (0 : ℝ) = Ioc 0 T := by ext t; simp [and_comm]
  rw [he]
  rfl

lemma gaussianLogAnchored_abs_le (T r : ℝ) (hr : 0 < r) :
    |gaussianLogAnchored T r| ≤ |Real.log r| := by
  let F : ℝ → ℝ := fun t => t⁻¹ *
    (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))
  have hi := integrableOn_gaussianLog_profile_difference r hr
  have hj := (show Integrable F (volume.restrict (Ioi 0)) from hi).indicator
    (s := Iic T) measurableSet_Iic
  rw [gaussianLogAnchored_eq_indicator, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖(Iic T).indicator F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 0, ‖F t‖ := by
      apply integral_mono hj.norm hi.norm
      intro t
      by_cases ht : t ∈ Iic T
      · simp only [indicator_of_mem ht]
        exact le_rfl
      · simp only [indicator_of_notMem ht, norm_zero]
        exact norm_nonneg _
    _ = _ := integral_norm_gaussianLog_profile_difference r hr

lemma tendsto_gaussianLogAnchored (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun j => gaussianLogAnchored (T j) r) atTop (𝓝 (-Real.log r)) := by
  let F : ℝ → ℝ := fun t => t⁻¹ *
    (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))
  have hm : Measurable F := by dsimp [F]; fun_prop
  have hi := integrableOn_gaussianLog_profile_difference r hr
  have ht : Tendsto (fun j => ∫ t : ℝ in Ioi 0, (Iic (T j)).indicator F t) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, F t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t => ‖F t‖)
    · intro j
      exact (hm.indicator measurableSet_Iic).aestronglyMeasurable
    · exact hi.norm
    · intro j
      exact Eventually.of_forall (fun t => by
        by_cases h : t ∈ Iic (T j)
        · simp only [indicator_of_mem h, le_refl]
        · simp only [indicator_of_notMem h, norm_zero]; exact norm_nonneg _)
    · exact Eventually.of_forall (fun t => by
        have he : ∀ᶠ j : ℕ in atTop, t ≤ T j := hT.eventually (eventually_ge_atTop t)
        apply tendsto_const_nhds.congr'
        filter_upwards [he] with j hj
        rw [indicator_of_mem (show t ∈ Iic (T j) from hj)])
  dsimp [F] at ht
  simp_rw [← gaussianLogAnchored_eq_indicator] at ht
  rw [integral_gaussianLog_profile_difference r hr] at ht
  exact ht

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogAnchored
#print axioms DGRHS.Gaussian.gaussianLogAnchored

#check DGRHS.Gaussian.gaussianLog_profile_difference_nonneg
#print axioms DGRHS.Gaussian.gaussianLog_profile_difference_nonneg

#check DGRHS.Gaussian.gaussianLog_profile_difference_nonpos
#print axioms DGRHS.Gaussian.gaussianLog_profile_difference_nonpos

#check DGRHS.Gaussian.integral_norm_gaussianLog_profile_difference
#print axioms DGRHS.Gaussian.integral_norm_gaussianLog_profile_difference

#check DGRHS.Gaussian.gaussianLogAnchored_eq_indicator
#print axioms DGRHS.Gaussian.gaussianLogAnchored_eq_indicator

#check DGRHS.Gaussian.gaussianLogAnchored_abs_le
#print axioms DGRHS.Gaussian.gaussianLogAnchored_abs_le

#check DGRHS.Gaussian.tendsto_gaussianLogAnchored
#print axioms DGRHS.Gaussian.tendsto_gaussianLogAnchored
