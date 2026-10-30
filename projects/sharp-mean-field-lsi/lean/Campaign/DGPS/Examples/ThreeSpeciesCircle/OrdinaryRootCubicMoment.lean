import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentLimits
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootParameterBounds

/-! The actual leading cubic logarithmic moment. The genuine Euler residual and
same-branch parameter bounds determine this limit without a third-order implicit
jet, reflection premise, or formal-series coefficient assumption. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A quantitative actual cubic logarithmic moment with constants before h. -/
theorem ordinaryRoot_cubic_logMoment_estimate (D : OrdinaryRootGraphData) :
    ∃ M δ : ℝ, 0 < M ∧ 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ →
        |normInt_STR02933 (fun t => chartU_STR02924 D.ψ h (D.Z 0 h) t * Real.cos (3 * t)) /
          h ^ 3 + (2 / 15 : ℝ)| ≤ M * h := by
  obtain ⟨K, δK, hK, hδK, hδKr, hKb⟩ := ordinaryRoot_cubic_logMoment_balance D
  obtain ⟨δa, hδa, _, hab⟩ := ordinaryRoot_angular_parameter_bounds D
  have hZ : ContinuousAt (fun h : ℝ => D.Z 0 h 2) 0 :=
    (continuous_apply 2).continuousAt.comp
      ((D.smoothZ 0).continuousOn.continuousAt
        (Ioo_mem_nhds (by linarith [D.radius_pos]) D.radius_pos))
  have hz0 : |D.Z 0 0 2| < (3 : ℝ) := by rw [D.Z_zero]; norm_num
  have hz : ∀ᶠ h : ℝ in 𝓝 0, |D.Z 0 h 2| < (3 : ℝ) :=
    hZ.abs.eventually (gt_mem_nhds hz0)
  obtain ⟨δZ, hδZ, hzball⟩ := Metric.eventually_nhds_iff.1 hz
  let δ := min δK (min δa (min δZ 1))
  let M := (K + 1) / 15
  have hM : 0 < M := by dsimp [M]; positivity
  have hδ : 0 < δ := lt_min hδK (lt_min hδa (lt_min hδZ (by norm_num)))
  refine ⟨M, δ, hM, hδ, (min_le_left _ _).trans hδKr, fun h hh hhd => ?_⟩
  have hhK : h < δK := hhd.trans_le (min_le_left _ _)
  have hha : h < δa := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhZ : h < δZ := hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hh1 : h ≤ 1 := (hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hsz : |D.Z 0 h 2| ≤ 3 :=
    (hzball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hh] using hhZ)).le
  let γ := h ^ 2 * D.Z 0 h 2
  let A := 16 - 2 * γ
  let m := normInt_STR02933 (fun t =>
    chartU_STR02924 D.ψ h (D.Z 0 h) t * Real.cos (3 * t))
  have hA : 15 ≤ A := by
    have ha := (hab h (by rwa [abs_of_pos hh]) (0 : Fin 3)).2
    dsimp [A, γ]
    linarith
  have hγ : |γ| ≤ 3 * h ^ 2 := by
    dsimp [γ]
    rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
    nlinarith [mul_le_mul_of_nonneg_left hsz (sq_nonneg h)]
  have hnum : |A * m + (32 / 15 : ℝ) * h ^ 3| ≤ K * h ^ 4 := by
    simpa only [A, m, γ, mul_assoc] using hKb h hh hhK
  have hscaled : |A * (m / h ^ 3) + (32 / 15 : ℝ)| ≤ K * h := by
    calc
      _ = |(A * m + (32 / 15 : ℝ) * h ^ 3) / h ^ 3| := by
        congr 1
        field_simp [hh.ne']
      _ = |A * m + (32 / 15 : ℝ) * h ^ 3| / h ^ 3 := by
        rw [abs_div, abs_of_pos (pow_pos hh 3)]
      _ ≤ (K * h ^ 4) / h ^ 3 := div_le_div_of_nonneg_right hnum (pow_nonneg hh.le 3)
      _ = K * h := by field_simp [hh.ne']
  have he : A * (m / h ^ 3 + (2 / 15 : ℝ)) =
      (A * (m / h ^ 3) + (32 / 15 : ℝ)) - (4 / 15 : ℝ) * γ := by
    dsimp [A]
    ring
  have hbound : |A * (m / h ^ 3 + (2 / 15 : ℝ))| ≤ (K + 1) * h := by
    rw [he]
    have ht : |(A * (m / h ^ 3) + (32 / 15 : ℝ)) - (4 / 15 : ℝ) * γ| ≤
        |A * (m / h ^ 3) + (32 / 15 : ℝ)| + (4 / 15 : ℝ) * |γ| := by
      simpa only [sub_eq_add_neg, abs_neg, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 4 / 15)] using
        abs_add_le (A * (m / h ^ 3) + (32 / 15 : ℝ)) (-((4 / 15 : ℝ) * γ))
    have hhsq : h ^ 2 ≤ h := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
    nlinarith
  rw [abs_mul, abs_of_pos (by linarith : 0 < A)] at hbound
  have hmul := mul_le_mul_of_nonneg_right hA (abs_nonneg (m / h ^ 3 + (2 / 15 : ℝ)))
  change |m / h ^ 3 + (2 / 15 : ℝ)| ≤ M * h
  dsimp [M]
  nlinarith

/-- The leading cubic logarithmic moment is fixed by the actual critical equation.
This is a one-sided positive-field limit, as needed for the canonical model. -/
theorem ordinaryRoot_cubic_logMoment_limit (D : OrdinaryRootGraphData) :
    Tendsto (fun h : ℝ =>
      normInt_STR02933 (fun t => chartU_STR02924 D.ψ h (D.Z 0 h) t * Real.cos (3 * t)) / h ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 / 15 : ℝ))) := by
  obtain ⟨M, δ, hM, hδ, _, hb⟩ := ordinaryRoot_cubic_logMoment_estimate D
  apply Metric.tendsto_nhds.2
  intro ε hε
  let r := min δ (ε / M)
  have hr : 0 < r := lt_min hδ (div_pos hε hM)
  have hnear : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Metric.ball 0 r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hr)
  filter_upwards [self_mem_nhdsWithin, hnear] with h hh hhr
  have hh0 : 0 < h := hh
  have hhsmall : h < r := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hh0] using hhr
  have hhδ : h < δ := hhsmall.trans_le (min_le_left _ _)
  have hhε : h < ε / M := hhsmall.trans_le (min_le_right _ _)
  rw [Real.dist_eq, sub_neg_eq_add]
  have hprod : M * h < ε := by nlinarith [(lt_div_iff₀ hM).mp hhε]
  exact (hb h hh0 hhδ).trans_lt hprod

end DGPS.Examples.ThreeSpeciesCircle
