import LeanResearch.PeriodicAttractiveLogGas.PlanarMinkowskiComparison

/-! Sharp isoperimetry for a phase contained between the proved coordinate
cuts. Euclidean Brunn--Minkowski is combined with the actual coarea rank
derivative. Smooth normalization removes the auxiliary gradient factor. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal Pointwise
namespace PeriodicAttractiveLogGas.CutPhaseIsoperimetry
open StationaryCutDomain StationaryCoarea StationarySard StationaryDistribution
  StationaryLevelGeometry StationaryLevelContinuity PlanarMinkowskiComparison NormalizedLevelFunction

theorem minkowski_le_inverse_gradient (a : PlanarSpace) {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hc : ∀ z ∈ coordinateCross (torusQuotient a), v z < 0)
    (ht : (0 : ℝ) ∉ torusCriticalValues v)
    (hzero : ∀ z : Torus, v z = 0 → ‖torusOrdinaryGradient v z‖ ≤ 1) :
    2 * Real.sqrt (rank v 0) * Real.sqrt Real.pi ≤
      ∫ z in {z | v z = 0}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure := by
  let D : ℝ := ∫ z in {z | v z = 0}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure
  have hDn : 0 ≤ D := integral_nonneg fun _ ↦ inv_nonneg.mpr (norm_nonneg _)
  by_cases hs : rank v 0 = 0
  · simpa only [hs, Real.sqrt_zero, mul_zero, zero_mul] using hDn
  have hpos : 0 < rank v 0 := lt_of_le_of_ne (rank_nonneg v 0) (Ne.symm hs)
  have hvc := continuous_of_contDiff_lift hv
  have hA : IsCompact (closedPhase a v) := closedPhase_compact a hvc
  have harea : volume.real (closedPhase a v) = rank v 0 := by
    exact congrArg ENNReal.toReal (closedPhase_volume a hvc hc (torusMeasure_regular_level_eq_zero hv ht))
  have hne : (closedPhase a v).Nonempty := by
    by_contra hn
    have he : closedPhase a v = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [← harea, he] at hpos
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero, lt_self_iff_false] at hpos
  have hfinite : volume (closedPhase a v) ≠ ⊤ := hA.measure_lt_top.ne
  have hall (δ : ℝ) (hδ : 0 < δ) :
      2 * Real.sqrt (rank v 0) * Real.sqrt Real.pi ≤ (1 + δ) * D := by
    obtain ⟨e, he, hbound⟩ := exists_dilation_layer_bound a hv hc hzero hδ
    have hineq (ε : ℝ) (hε : 0 < ε) (hεe : ε < e) :
        2 * Real.sqrt (rank v 0) * Real.sqrt Real.pi ≤
          (rank v (-((1 + δ) * ε)) - rank v 0) / ε := by
      have hm := hbound ε hε hεe
      have hf : volume (closedPhase a v + Metric.ball 0 ε) ≠ ⊤ :=
        ne_top_of_le_ne_top (measure_ne_top torusMeasure _) hm
      have hreal : volume.real (closedPhase a v + Metric.ball 0 ε) ≤ rank v (-((1 + δ) * ε)) :=
        ENNReal.toReal_mono (measure_ne_top torusMeasure _) hm
      have hM := planar_minkowski_real hε hne hA.measurableSet hfinite hf
      rw [harea] at hM
      exact hM.trans (div_le_div_of_nonneg_right (sub_le_sub_right hreal _) hε.le)
    have hd : HasDerivAt (fun ε : ℝ ↦ rank v (-((1 + δ) * ε))) ((1 + δ) * D) 0 := by
      have hs : HasDerivAt (fun ε : ℝ ↦ -((1 + δ) * ε)) (-(1 + δ)) 0 := by
        simpa only [id_eq, mul_one, Pi.neg_apply] using! ((hasDerivAt_id (0 : ℝ)).const_mul (1 + δ)).neg
      have hr : HasDerivAt (rank v) (-D) (-((1 + δ) * (0 : ℝ))) := by
        simpa only [D, mul_zero, neg_zero] using hasDerivAt_rank_regular hv ht
      simpa only [Function.comp_def, neg_mul_neg, mul_comm] using hr.comp 0 hs
    have hlim : Tendsto (fun ε : ℝ ↦ (rank v (-((1 + δ) * ε)) - rank v 0) / ε)
        (𝓝[>] 0) (𝓝 ((1 + δ) * D)) := by
      simpa only [zero_add, mul_zero, zero_mul, neg_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
        hd.tendsto_slope_zero_right
    have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        2 * Real.sqrt (rank v 0) * Real.sqrt Real.pi ≤
          (rank v (-((1 + δ) * ε)) - rank v 0) / ε := by
      have hu : Iio e ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds he)
      filter_upwards [hu, self_mem_nhdsWithin] with ε hupper hpositive
      exact hineq ε hpositive hupper
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hevent
  have hδlim : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun n : ℕ ↦ (1 + 1 / ((n : ℝ) + 1)) * D) atTop (𝓝 D) := by
    simpa only [one_mul] using hδlim.mul_const D
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun n ↦ hall (1 / ((n : ℝ) + 1)) (by positivity))

theorem cut_phase_isoperimetric (a : PlanarSpace) {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hc : ∀ z ∈ coordinateCross (torusQuotient a), v z < 0)
    (ht : (0 : ℝ) ∉ torusCriticalValues v) :
    2 * Real.sqrt (rank v 0) * Real.sqrt Real.pi ≤ physicalCurveMeasure.real {z | v z = 0} := by
  obtain ⟨c, hcpos, hbound⟩ := exists_normalized_inverse_level_bound hv ht
  have hrank (η : ℝ) (hη : 0 < η) : rank (normalized v η) 0 = rank v 0 := by
    unfold rank
    congr 1
    ext z
    exact normalized_pos_iff v hη z
  have he (η : ℝ) (hη : 0 < η) :
      2 * Real.sqrt (rank v 0) * Real.sqrt Real.pi ≤
        (1 + η / c) * physicalCurveMeasure.real {z | v z = 0} := by
    have hm := minkowski_le_inverse_gradient a (normalized_contDiff hv hη)
      (fun z hz ↦ (normalized_neg_iff v hη z).mpr (hc z hz))
      (normalized_zero_regular hv ht hη) (fun z hz ↦ normalized_gradient_le_one hv hη hz)
    rw [hrank η hη] at hm
    exact hm.trans (hbound η hη)
  have hηlim : Tendsto (fun n : ℕ ↦ (1 : ℝ) + (1 / ((n : ℝ) + 1)) / c) atTop (𝓝 1) := by
    simpa only [zero_div, add_zero] using
      tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const c)
  have hlim : Tendsto (fun n : ℕ ↦ (1 + (1 / ((n : ℝ) + 1)) / c) *
      physicalCurveMeasure.real {z | v z = 0}) atTop
      (𝓝 (physicalCurveMeasure.real {z | v z = 0})) := by
    simpa only [one_mul] using hηlim.mul_const (physicalCurveMeasure.real {z | v z = 0})
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun n ↦ he (1 / ((n : ℝ) + 1)) (by positivity))

end PeriodicAttractiveLogGas.CutPhaseIsoperimetry
