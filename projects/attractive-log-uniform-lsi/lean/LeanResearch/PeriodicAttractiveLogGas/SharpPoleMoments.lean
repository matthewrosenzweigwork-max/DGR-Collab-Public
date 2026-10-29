import LeanResearch.PeriodicAttractiveLogGas.SingularRectangleMoments
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.Real.Pi.Bounds

/-! The literal layer-cake and disk-maximization step in the proof of
the source label-ratio lemma. Measures of mass one dominated by planar
volume are compared to a disk of area one, before generalized Holder.
All powers use the existing totalized representative at the null pole. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.SharpPoleMoments
open SingularRectangleMoments

theorem integrableOn_ball_norm_rpow {u R : ℝ} (hu : u < 2) (_hR : 0 < R) :
    IntegrableOn (fun Z : PlanarSpace ↦ ‖Z‖ ^ (-u)) (ball 0 R) volume := by
  refine integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure PlanarSpace))
    (C := 1) (α := u) (by simp) (by simpa using hu) ?_ ?_
  · exact ae_of_all _ fun Z ↦ by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg Z) _), one_mul]
  · exact (measurable_norm.pow_const (-u)).aestronglyMeasurable

theorem integral_ball_norm_rpow {u R : ℝ} (hu : u < 2) (hR : 0 < R) :
    (∫ Z in ball (0 : PlanarSpace) R, ‖Z‖ ^ (-u)) =
      2 * Real.pi * R ^ (2 - u) / (2 - u) := by
  have hvol : (volume : Measure PlanarSpace).real (ball 0 1) = Real.pi := by
    change (volume (ball (0 : PlanarSpace) 1)).toReal = Real.pi
    rw [EuclideanSpace.volume_ball_fin_two]
    simp [Real.pi_nonneg]
  have hradial :
      (∫ r in Ioi (0 : ℝ), r * (Iio R).indicator (fun t ↦ t ^ (-u)) r) =
        R ^ (2 - u) / (2 - u) := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator (fun t ↦ t * t ^ (-u)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases h : r < R <;> simp [Set.indicator, h]
      _ = ∫ r in Ioo (0 : ℝ) R, r ^ (1 - u) := by
        rw [setIntegral_indicator measurableSet_Iio]
        change (∫ r in Ioo (0 : ℝ) R, r * r ^ (-u)) = _
        apply setIntegral_congr_fun measurableSet_Ioo
        intro r hr
        calc
          r * r ^ (-u) = r ^ (1 : ℝ) * r ^ (-u) := by rw [Real.rpow_one]
          _ = r ^ (1 - u) := by rw [← Real.rpow_add hr.1]; congr 1
      _ = ∫ r in (0 : ℝ)..R, r ^ (1 - u) := by
        rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]
      _ = R ^ (2 - u) / (2 - u) := by
        rw [integral_rpow (Or.inl (by linarith : -1 < 1 - u))]
        have hne : 2 - u ≠ 0 := by linarith
        simp [show 1 - u + 1 = 2 - u by ring, Real.zero_rpow hne]
  calc
    _ = ∫ Z : PlanarSpace, (Iio R).indicator (fun t ↦ t ^ (-u)) ‖Z‖ := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact ae_of_all _ fun Z ↦ by
        by_cases h : ‖Z‖ < R <;> simp [Set.indicator, h]
    _ = 2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * (Iio R).indicator (fun t ↦ t ^ (-u)) r := by
      rw [integral_fun_norm_addHaar (volume : Measure PlanarSpace)]
      simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat, hvol, Nat.reduceSub,
        pow_one, smul_eq_mul, nsmul_eq_mul]
      ring
    _ = _ := by rw [hradial]; ring

theorem integrableOn_ball_inverseDistancePower (Y : PlanarSpace) {u R : ℝ}
    (hu : u < 2) (hR : 0 < R) :
    IntegrableOn (inverseDistancePower Y u) (ball Y R) volume := by
  have hi := ((integrable_indicator_iff measurableSet_ball).mpr
    (integrableOn_ball_norm_rpow hu hR)).comp_sub_right Y
  apply (integrable_indicator_iff measurableSet_ball).mp
  apply hi.congr
  filter_upwards with Z
  by_cases h : ‖Z - Y‖ < R <;>
    simp [Set.indicator, Metric.mem_ball, dist_eq_norm, inverseDistancePower, h]

theorem integral_ball_inverseDistancePower (Y : PlanarSpace) {u R : ℝ}
    (hu : u < 2) (hR : 0 < R) :
    (∫ Z in ball Y R, inverseDistancePower Y u Z) =
      2 * Real.pi * R ^ (2 - u) / (2 - u) := by
  rw [← integral_indicator measurableSet_ball]
  calc
    _ = ∫ Z : PlanarSpace, ((ball (0 : PlanarSpace) R).indicator
        (fun W ↦ ‖W‖ ^ (-u))) (Z - Y) := by
      apply integral_congr_ae
      filter_upwards with Z
      by_cases h : ‖Z - Y‖ < R <;>
        simp [Set.indicator, Metric.mem_ball, dist_eq_norm, inverseDistancePower, h]
    _ = _ := by
      rw [integral_sub_right_eq_self, integral_indicator measurableSet_ball,
        integral_ball_norm_rpow hu hR]

def areaOneRadius : ℝ := Real.pi ^ (-1 / 2 : ℝ)

theorem areaOneRadius_pos : 0 < areaOneRadius := Real.rpow_pos_of_pos Real.pi_pos _

theorem volume_areaOneBall (Y : PlanarSpace) :
    volume (ball Y areaOneRadius) = (1 : ℝ≥0∞) := by
  rw [EuclideanSpace.volume_ball_fin_two]
  have he : Real.pi * areaOneRadius ^ 2 = 1 := by
    rw [← Real.rpow_natCast, areaOneRadius, ← Real.rpow_mul Real.pi_nonneg]
    norm_num [Real.rpow_neg_one, Real.pi_ne_zero]
  rw [mul_comm, ← ENNReal.ofReal_pow areaOneRadius_pos.le,
    ← ENNReal.ofReal_mul Real.pi_nonneg, he, ENNReal.ofReal_one]

theorem inverseDistancePower_tail_le_ball {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (Y : PlanarSpace) {u : ℝ}
    (hu : 0 ≤ u) (t : ℝ) :
    μ {Z | t < inverseDistancePower Y u Z} ≤
      (volume.restrict (ball Y areaOneRadius)) {Z | t < inverseDistancePower Y u Z} := by
  let A := {Z : PlanarSpace | t < inverseDistancePower Y u Z}
  have hm : MeasurableSet A := measurableSet_lt measurable_const (measurable_inverseDistancePower Y u)
  by_cases ht : areaOneRadius ^ (-u) ≤ t
  · have hAB : A ⊆ ball Y areaOneRadius := by
      intro Z hZ
      by_contra hz
      have hr : areaOneRadius ≤ ‖Z - Y‖ := by
        simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hz
      have hb := Real.rpow_le_rpow_of_nonpos areaOneRadius_pos hr (neg_nonpos.mpr hu)
      exact (not_lt_of_ge (hb.trans ht)) hZ
    change μ A ≤ (volume.restrict (ball Y areaOneRadius)) A
    rw [Measure.restrict_apply hm, inter_eq_left.mpr hAB]
    exact hμ A
  · have ht' : t < areaOneRadius ^ (-u) := lt_of_not_ge ht
    have ha : ∀ᵐ Z ∂volume.restrict (ball Y areaOneRadius), Z ∈ A := by
      filter_upwards [ae_restrict_mem measurableSet_ball,
        (ae_restrict_of_ae ((volume : Measure PlanarSpace).ae_ne Y))] with Z hZ hne
      have hp : 0 < ‖Z - Y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hr : ‖Z - Y‖ ≤ areaOneRadius := by
        exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hZ)
      exact ht'.trans_le (Real.rpow_le_rpow_of_nonpos hp hr (neg_nonpos.mpr hu))
    change μ A ≤ (volume.restrict (ball Y areaOneRadius)) A
    have he := congrArg (fun ν : Measure PlanarSpace ↦ ν univ)
      (Measure.restrict_eq_self_of_ae_mem ha)
    simp only [Measure.restrict_apply_univ] at he
    rw [he, volume_areaOneBall]
    exact prob_le_one

/-- Layer cake gives the maximizing area-one disk, with no rearrangement
result assumed and no exceptional pole included as a pointwise bound. -/
theorem integral_inverseDistancePower_le_ball {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (Y : PlanarSpace) {u : ℝ}
    (hu0 : 0 ≤ u) (hu2 : u < 2) :
    (∫ Z, inverseDistancePower Y u Z ∂μ) ≤
      ∫ Z in ball Y areaOneRadius, inverseDistancePower Y u Z := by
  have hi := (inverseDistancePower_integrable_and_integral_le hμ Y hu0 hu2).1
  have hb := integrableOn_ball_inverseDistancePower Y hu2 areaOneRadius_pos
  have hn (ν : Measure PlanarSpace) : 0 ≤ᵐ[ν] inverseDistancePower Y u :=
    Eventually.of_forall fun Z ↦ inverseDistancePower_nonneg Y Z u
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun Z ↦ inverseDistancePower_nonneg Y Z u)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (hn μ),
    ofReal_integral_eq_lintegral_ofReal hb (hn _),
    lintegral_eq_lintegral_meas_lt μ (hn μ) (measurable_inverseDistancePower Y u).aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (hn _) (measurable_inverseDistancePower Y u).aemeasurable]
  exact lintegral_mono fun t ↦ inverseDistancePower_tail_le_ball hμ Y hu0 t

theorem sharp_inverseDistancePower_moment {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (Y : PlanarSpace) {u : ℝ}
    (hu0 : 0 ≤ u) (hu2 : u < 2) :
    Integrable (inverseDistancePower Y u) μ ∧
      (∫ Z, inverseDistancePower Y u Z ∂μ) ≤ 2 * Real.pi ^ (u / 2) / (2 - u) := by
  refine ⟨(inverseDistancePower_integrable_and_integral_le hμ Y hu0 hu2).1, ?_⟩
  have he : Real.pi * areaOneRadius ^ (2 - u) = Real.pi ^ (u / 2) := by
    calc
      _ = Real.pi ^ (1 : ℝ) * Real.pi ^ ((-1 / 2 : ℝ) * (2 - u)) := by
        rw [Real.rpow_one, areaOneRadius, ← Real.rpow_mul Real.pi_nonneg]
      _ = _ := by rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
  calc
    _ ≤ ∫ Z in ball Y areaOneRadius, inverseDistancePower Y u Z :=
      integral_inverseDistancePower_le_ball hμ Y hu0 hu2
    _ = _ := by rw [integral_ball_inverseDistancePower Y hu2 areaOneRadius_pos, mul_assoc, he]

theorem sharp_constant_le_two {u : ℝ} (hu : u ≤ 1 / 16) :
    2 * Real.pi ^ (u / 2) / (2 - u) ≤ 2 := by
  have hp : Real.pi ^ (u / 2) ≤ Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  have hs : Real.sqrt Real.pi ≤ 15 / 8 := by
    nlinarith [Real.sq_sqrt Real.pi_nonneg, Real.sqrt_nonneg Real.pi, Real.pi_lt_d2]
  apply (div_le_iff₀ (by linarith : 0 < 2 - u)).mpr
  nlinarith

/-- The same generalized Holder step as in the source, now with the exact
maximal disk moment. Zero total weight and coincident poles are included. -/
theorem sharp_poleProduct_moment {ι : Type*} [Fintype ι]
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : (∑ i, w i) < 2) :
    Integrable (poleProduct Y w) μ ∧
      (∫ Z, poleProduct Y w Z ∂μ) ≤
        2 * Real.pi ^ ((∑ i, w i) / 2) / (2 - ∑ i, w i) := by
  classical
  have hk0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ ↦ hw i
  rcases eq_or_lt_of_le hk0 with hk | hk
  · have hz : ∑ i, w i = 0 := hk.symm
    have he : poleProduct Y w = fun _ ↦ (1 : ℝ) :=
      funext (poleProduct_eq_one_of_sum_eq_zero Y w hw hz)
    rw [he, hz]
    simp
  · obtain ⟨hi, hholder, _⟩ := poleProduct_moment_of_sum_pos hμ Y w hw hk
      (s := 1) (by norm_num) (by simpa using hκ)
    simp only [Real.rpow_one, one_mul] at hi hholder
    refine ⟨hi, hholder.trans ?_⟩
    let C := 2 * Real.pi ^ ((∑ i, w i) / 2) / (2 - ∑ i, w i)
    have hC : 0 < C := by dsimp [C]; positivity
    calc
      _ ≤ ∏ i, C ^ (w i / ∑ j, w j) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact Real.rpow_nonneg (integral_nonneg fun Z ↦ inverseDistancePower_nonneg (Y i) Z _) _
        · intro i hi
          exact Real.rpow_le_rpow
            (integral_nonneg fun Z ↦ inverseDistancePower_nonneg (Y i) Z _)
            (sharp_inverseDistancePower_moment hμ (Y i) hk0 hκ).2 (div_nonneg (hw i) hk.le)
      _ = C := by
        rw [← Real.rpow_sum_of_pos hC _ Finset.univ, ← Finset.sum_div, div_self hk.ne', Real.rpow_one]

theorem small_poleProduct_moment {ι : Type*} [Fintype ι]
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : (∑ i, w i) ≤ 1 / 16) :
    Integrable (poleProduct Y w) μ ∧ (∫ Z, poleProduct Y w Z ∂μ) ≤ 2 := by
  obtain ⟨hi, hb⟩ := sharp_poleProduct_moment hμ Y w hw (by linarith)
  exact ⟨hi, hb.trans (sharp_constant_le_two hκ)⟩

end PeriodicAttractiveLogGas.SharpPoleMoments
