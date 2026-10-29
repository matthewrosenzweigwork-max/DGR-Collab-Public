import LeanResearch.PeriodicAttractiveLogGas.NormalizedLevelFunction
import LeanResearch.Imported.Isoperimetric.Isoperimetric

/-! The planar Minkowski inequality in finite real form, with the exact
Euclidean unit-ball constant. The upper neighborhood comparison is proved
from the actual defining function and the fundamental-square measure map. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal Pointwise
namespace PeriodicAttractiveLogGas.PlanarMinkowskiComparison
open StationaryCutDomain BoundaryLayerComparison StationaryDistribution StationaryLevelGeometry

theorem planar_minkowski_real {A : Set PlanarSpace} {ε : ℝ}
    (hε : 0 < ε) (hne : A.Nonempty) (hA : MeasurableSet A) (hfinite : volume A ≠ ⊤)
    (hfinite' : volume (A + Metric.ball 0 ε) ≠ ⊤) :
    2 * Real.sqrt (volume.real A) * Real.sqrt Real.pi ≤
      (volume.real (A + Metric.ball 0 ε) - volume.real A) / ε := by
  have hh := LeanResearch.Imported.Isoperimetric.isoperimetric_inequality
    (d := 1) hε hne hA hfinite
  have hsub : A ⊆ A + Metric.ball 0 ε := by
    intro x hx
    exact ⟨x, hx, 0, Metric.mem_ball_self hε, by simp⟩
  have ht : (volume (A + Metric.ball 0 ε) - volume A) / ENNReal.ofReal ε ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.sub_ne_top hfinite') (ENNReal.ofReal_pos.mpr hε).ne'
  have hball : volume (Metric.ball (0 : PlanarSpace) 1) = ENNReal.ofReal Real.pi := by
    simpa only [ENNReal.ofReal_one, one_pow, one_mul] using
      EuclideanSpace.volume_ball_fin_two (0 : PlanarSpace) 1
  rw [hball] at hh
  have hr := ENNReal.toReal_mono ht hh
  norm_num only [Nat.cast_one] at hr
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_div, ENNReal.toReal_sub_of_le (measure_mono hsub) hfinite',
    ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal Real.pi_pos.le] at hr
  norm_num only [ENNReal.toReal_ofNat] at hr
  simpa only [Measure.real, Real.sqrt_eq_rpow] using hr

theorem exists_dilation_layer_bound (a : PlanarSpace) {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hc : ∀ z ∈ coordinateCross (torusQuotient a), v z < 0)
    (hzero : ∀ z : Torus, v z = 0 → ‖torusOrdinaryGradient v z‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : ℝ, 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε < e →
      volume (closedPhase a v + Metric.ball 0 ε) ≤
        torusMeasure {z | -((1 + δ) * ε) < v z} := by
  have hvc := continuous_of_contDiff_lift hv
  obtain ⟨ρ, hρ, hρbox⟩ := exists_phase_thickening a hvc hc
  obtain ⟨L, hL⟩ := exists_lipschitz_scalar_lift hv
  obtain ⟨r, hr, hband⟩ := exists_gradient_band hv hzero hδ
  have hLp : 0 < 2 * (L : ℝ) + 1 := by positivity
  refine ⟨min ρ (r / (2 * (L : ℝ) + 1)), lt_min hρ (div_pos hr hLp), ?_⟩
  intro ε hε he
  have heρ : ε < ρ := he.trans_le (min_le_left _ _)
  have her : ε < r / (2 * (L : ℝ) + 1) := he.trans_le (min_le_right _ _)
  have hsmall : 2 * (L : ℝ) * ε < r := by
    have hh := (lt_div_iff₀ hLp).mp her
    nlinarith only [hh, hε]
  let B : Set Torus := {z | -((1 + δ) * ε) < v z}
  have hBm : MeasurableSet B := (isOpen_lt continuous_const hvc).measurableSet
  have hpre : MeasurableSet (torusQuotient ⁻¹' B) :=
    isOpenQuotientMap_torusQuotient.continuous.measurable hBm
  have hsub : closedPhase a v + Metric.ball 0 ε ⊆
      torusQuotient ⁻¹' B ∩ euclideanFundamentalBox a := by
    rw [add_ball_zero]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Metric.mem_thickening_iff.mp hy
    refine ⟨?_, ?_⟩
    · exact value_layer_of_dist_lt (hv.differentiable (by norm_num)) hL
        (fun z hz ↦ by rw [← torus_gradient_norm_eq_fderiv]; exact hband _ hz)
        (by linarith : 0 < 1 + δ) hε hsmall hx.2 hxy
    · apply euclideanOpenBox_subset_fundamentalBox a
      apply hρbox
      exact Metric.mem_thickening_iff.mpr ⟨x, hx, hxy.trans heρ⟩
  calc
    volume (closedPhase a v + Metric.ball 0 ε) ≤
        volume (torusQuotient ⁻¹' B ∩ euclideanFundamentalBox a) := measure_mono hsub
    _ = torusMeasure B := by
      rw [← Measure.restrict_apply hpre,
        (measurePreserving_torusQuotient_box a).measure_preimage hBm.nullMeasurableSet]

end PeriodicAttractiveLogGas.PlanarMinkowskiComparison
