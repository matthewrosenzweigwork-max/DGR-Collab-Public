import DGPS.Examples.ThreeSpeciesCircle.OrdinaryHessianSchur
import DGPS.Frontier.STR029.T31

/-! Uniform density bounds on the same three ordinary-root branches. The only small-field
input is the existing C0 logarithmic remainder estimate, on a fixed interval before h.
The weights here are the actual explicit exponential chart densities. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029 DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem root_logRemainder_eq (ψ : Par_STR02916 → E_STR02969)
    (Z : ℝ → Fin 3 → ℝ) (h : ℝ) :
    logRemainder_STR02931 ψ Z h = fun t => chartU_STR02924 ψ h (Z h) t -
      2 * h * Real.cos t - h ^ 2 * ((2 / 3 : ℝ) * Real.cos (2 * t) -
        (1 / 5 : ℝ) * Real.cos (4 * t)) := by
  funext t
  unfold logRemainder_STR02931
  linear_combination log_density_identity_STR02931 ψ Z h t

/-- The supplied C0 remainder norm controls the actual remainder at every angular point. -/
theorem ordinaryRoot_logRemainder_pointwise (ψ : Par_STR02916 → E_STR02969)
    (Z : ℝ → Fin 3 → ℝ) (h C : ℝ)
    (hrem : cmN_STR02966 0 (logRemainder_STR02931 ψ Z h) ≤ C * |h| ^ 3) :
    ∀ t, |logRemainder_STR02931 ψ Z h t| ≤ C * |h| ^ 3 := by
  have hu := chartU_isC2_STR02924 ψ h (Z h)
  have hp2 : Function.Periodic (fun t : ℝ => Real.cos (2 * t)) (2 * π) :=
    (cos_test_STR02933 2).2
  have hp4 : Function.Periodic (fun t : ℝ => Real.cos (4 * t)) (2 * π) :=
    (cos_test_STR02933 4).2
  have hper : Function.Periodic (logRemainder_STR02931 ψ Z h) (2 * π) := by
    rw [root_logRemainder_eq]
    intro t
    dsimp only
    have hp2t : Real.cos (2 * (t + 2 * π)) = Real.cos (2 * t) := hp2 t
    have hp4t : Real.cos (4 * (t + 2 * π)) = Real.cos (4 * t) := hp4 t
    rw [hu.1 t, Real.cos_periodic t, hp2t, hp4t]
  have hcont : Continuous (logRemainder_STR02931 ψ Z h) := by
    rw [root_logRemainder_eq]
    have hc := hu.2.1.continuous
    fun_prop
  have hCm : IsPerCm_STR02966 0 (logRemainder_STR02931 ψ Z h) :=
    ⟨hper, contDiff_zero.mpr hcont⟩
  intro t
  exact (abs_le_supNorm_STR02966 hCm t).trans (by
    simpa only [cmN_zero_STR02966] using hrem)

/-- The exact logarithmic expansion controls the unnormalized chart exponent. -/
theorem ordinaryRoot_exponent_bound_of_logRemainder
    (ψ : Par_STR02916 → E_STR02969) (Z : ℝ → Fin 3 → ℝ) (h C : ℝ)
    (hrem : ∀ t, |logRemainder_STR02931 ψ Z h t| ≤ C * |h| ^ 3) :
    ∀ t, |h * Real.cos (3 * t) + chartU_STR02924 ψ h (Z h) t| ≤
      3 * |h| + (13 / 15 : ℝ) * h ^ 2 + C * |h| ^ 3 := by
  intro t
  have he : h * Real.cos (3 * t) + chartU_STR02924 ψ h (Z h) t =
      h * Real.cos (3 * t) + 2 * h * Real.cos t +
        h ^ 2 * ((2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)) +
          logRemainder_STR02931 ψ Z h t := by
    rw [root_logRemainder_eq]
    ring
  have h3 : |h * Real.cos (3 * t)| ≤ |h| := by
    simpa only [abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (3 * t)) (abs_nonneg h)
  have h1 : |2 * h * Real.cos t| ≤ 2 * |h| := by
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (by positivity : 0 ≤ 2 * |h|)
  have htrig : |(2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)| ≤
      (13 / 15 : ℝ) := by
    have hh : |(2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)| ≤
        |(2 / 3 : ℝ) * Real.cos (2 * t)| + |(1 / 5 : ℝ) * Real.cos (4 * t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((2 / 3 : ℝ) * Real.cos (2 * t)) (-((1 / 5 : ℝ) * Real.cos (4 * t)))
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at hh
    nlinarith [Real.abs_cos_le_one (2 * t), Real.abs_cos_le_one (4 * t)]
  have h2 : |h ^ 2 * ((2 / 3 : ℝ) * Real.cos (2 * t) -
      (1 / 5 : ℝ) * Real.cos (4 * t))| ≤ (13 / 15 : ℝ) * h ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
    nlinarith [mul_le_mul_of_nonneg_left htrig (sq_nonneg h)]
  rw [he]
  calc
    _ ≤ |h * Real.cos (3 * t) + 2 * h * Real.cos t +
          h ^ 2 * ((2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t))| +
        |logRemainder_STR02931 ψ Z h t| := abs_add_le _ _
    _ ≤ _ := by
      have hh2 := abs_add_le (h * Real.cos (3 * t) + 2 * h * Real.cos t)
        (h ^ 2 * ((2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)))
      have hh1 := abs_add_le (h * Real.cos (3 * t)) (2 * h * Real.cos t)
      linarith [hrem t]

/-- A fixed C0 logarithmic remainder estimate makes the SAME explicit branch density
uniformly close to one. The branch witness is never reselected. -/
theorem ordinaryRoot_branch_density_near_one (ψ : Par_STR02916 → E_STR02969)
    (Z : ℝ → Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hrem : ∀ h : ℝ, |h| ≤ δ →
      cmN_STR02966 0 (logRemainder_STR02931 ψ Z h) ≤ C * |h| ^ 3) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ∀ h : ℝ, |h| < ε → ∀ t : ℝ,
      (3 / 4 : ℝ) ≤ rhoT_STR02901 h (chartU_STR02924 ψ h (Z h)) t ∧
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z h)) t ≤ (5 / 4 : ℝ) := by
  let E : ℝ → ℝ := fun h => 3 * |h| + (13 / 15 : ℝ) * h ^ 2 + C * |h| ^ 3
  have hEc : Continuous E := by dsimp [E]; fun_prop
  have hlow : Tendsto (fun h => Real.exp (-2 * E h)) (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt (fun h => Real.exp (-2 * E h)) 0 := by fun_prop
    simpa only [E, abs_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
      mul_zero, add_zero, Real.exp_zero] using hc.tendsto
  have hhigh : Tendsto (fun h => Real.exp (2 * E h)) (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt (fun h => Real.exp (2 * E h)) 0 := by fun_prop
    simpa only [E, abs_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
      mul_zero, add_zero, Real.exp_zero] using hc.tendsto
  have hev : ∀ᶠ h : ℝ in 𝓝 0,
      (3 / 4 : ℝ) < Real.exp (-2 * E h) ∧ Real.exp (2 * E h) < (5 / 4 : ℝ) :=
    (hlow.eventually (lt_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1))).and
      (hhigh.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 5 / 4)))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min r δ, lt_min hr hδ, min_le_right _ _, fun h hh t => ?_⟩
  have hhδ : |h| ≤ δ := (lt_of_lt_of_le hh (min_le_right _ _)).le
  have hhr : dist h 0 < r := by
    simpa only [Real.dist_eq, sub_zero] using lt_of_lt_of_le hh (min_le_left _ _)
  have hb := ordinaryChart_density_bounds_of_exponent_bound h (E h)
    (chartU_STR02924 ψ h (Z h)) (chartU_isC2_STR02924 ψ h (Z h)).2.1.continuous
    (ordinaryRoot_exponent_bound_of_logRemainder ψ Z h C
      (ordinaryRoot_logRemainder_pointwise ψ Z h C (hrem h hhδ))) t
  exact ⟨(hball hhr).1.le.trans hb.1, hb.2.trans (hball hhr).2.le⟩


/-- The actual rotations carry the same C0 density bounds to all three retained branches. -/
theorem ordinaryRoot_threefold_density_near_one (ψ : Par_STR02916 → E_STR02969)
    (Z : Fin 3 → ℝ → Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hrem : ∀ h : ℝ, |h| ≤ δ →
      cmN_STR02966 0 (logRemainder_STR02931 ψ (Z 0) h) ≤ C * |h| ^ 3)
    (hrot : ∀ h ∈ Set.Ioo (-δ) δ, ∀ t : ℝ,
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z 1 h)) t =
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (t - 2 * π / 3) ∧
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z 2 h)) t =
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (t - 4 * π / 3)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ∀ h : ℝ, |h| < ε → ∀ j : Fin 3, ∀ t : ℝ,
      (3 / 4 : ℝ) ≤ rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t ∧
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t ≤ (5 / 4 : ℝ) := by
  obtain ⟨ε, hε, hεδ, hb⟩ := ordinaryRoot_branch_density_near_one ψ (Z 0) δ hδ C hrem
  refine ⟨ε, hε, hεδ, fun h hh j t => ?_⟩
  have hhδ : h ∈ Set.Ioo (-δ) δ := abs_lt.mp (lt_of_lt_of_le hh hεδ)
  fin_cases j
  · exact hb h hh t
  · change (3 / 4 : ℝ) ≤ rhoT_STR02901 h (chartU_STR02924 ψ h (Z (1 : Fin 3) h)) t ∧
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z (1 : Fin 3) h)) t ≤ (5 / 4 : ℝ)
    rw [(hrot h hhδ t).1]
    exact hb h hh (t - 2 * π / 3)
  · change (3 / 4 : ℝ) ≤ rhoT_STR02901 h (chartU_STR02924 ψ h (Z (2 : Fin 3) h)) t ∧
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z (2 : Fin 3) h)) t ≤ (5 / 4 : ℝ)
    rw [(hrot h hhδ t).2]
    exact hb h hh (t - 4 * π / 3)

end DGPS.Examples.ThreeSpeciesCircle
