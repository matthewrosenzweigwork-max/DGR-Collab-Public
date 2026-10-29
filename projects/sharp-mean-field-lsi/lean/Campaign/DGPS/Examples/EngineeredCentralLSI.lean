import DGPS.Examples.EngineeredCentralHardy
import DGPS.FiniteN.Tools.Rothaus

/-!
# Central conditional logarithmic Sobolev inequality for EX040

This module assembles interval weak representatives, the fixed-interval entropy estimate,
ground-state absorption, and Rothaus tightening for the conditioned engineered law.
-/

open MeasureTheory Real Set Filter Topology
open scoped NNReal ENNReal ContDiff
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredGroundState
  DGPS.Examples.EngineeredHardy

/-- The density of the conditioned law is this scalar times qAng. -/
noncomputable def centralNormFactor_EX040 (h : ℝ) (hh : 0 < h) : ℝ :=
  ((centralFiniteMeasure_EX040 h hh).mass : ℝ)⁻¹ / (2 * π)

theorem central_mass_pos_EX040 (h : ℝ) (hh : 0 < h) :
    0 < ((centralFiniteMeasure_EX040 h hh).mass : ℝ) := by
  have hn : centralFiniteMeasure_EX040 h hh ≠ 0 := by
    intro hz
    exact central_raw_ne_zero_EX040 h hh
      (congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) hz)
  have hm : (centralFiniteMeasure_EX040 h hh).mass ≠ 0 :=
    (FiniteMeasure.mass_nonzero_iff _).mpr hn
  have hmne : ((centralFiniteMeasure_EX040 h hh).mass : ℝ) ≠ 0 := by exact_mod_cast hm
  exact lt_of_le_of_ne (by positivity) (Ne.symm hmne)

theorem central_mass_le_one_EX040 (h : ℝ) (hh : 0 < h) :
    ((centralFiniteMeasure_EX040 h hh).mass : ℝ) ≤ 1 := by
  have hd := hardyData_qAng hh
  let : IsProbabilityMeasure (muOf (qAng h)) :=
    isProbabilityMeasure_muOf_hardy hd.cont hd.pos hd.int_one
  have hm : ((centralFiniteMeasure_EX040 h hh).mass : ℝ≥0∞) ≤ 1 := by
    rw [FiniteMeasure.ennreal_mass]
    exact (central_raw_measure_le_EX040 h univ).trans_eq (measure_univ)
  exact_mod_cast hm

theorem central_norm_factor_pos_EX040 (h : ℝ) (hh : 0 < h) :
    0 < centralNormFactor_EX040 h hh := by
  have hm := central_mass_pos_EX040 h hh
  unfold centralNormFactor_EX040
  positivity

theorem central_raw_integral_q_EX040 (h : ℝ) (hh : 0 < h) (F : ℝ → ℝ) :
    (∫ x, F x ∂centralRawMeasure_EX040 h) =
      (2 * π)⁻¹ * (∫ x in -(π / 2)..π / 2, F x * qAng h (x : AngCircle)) := by
  have hd := hardyData_qAng hh
  have hp := continuous_pOf_hardy hd.cont
  unfold centralRawMeasure_EX040 DGPS.FiniteN.densityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hp.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ x in Ioo (-(π / 2)) (π / 2),
        (2 * π)⁻¹ * (F x * qAng h (x : AngCircle)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (pOf_nonneg_hardy hd.pos x), smul_eq_mul]
      unfold pOf
      ring
    _ = (2 * π)⁻¹ * ∫ x in Ioo (-(π / 2)) (π / 2), F x * qAng h (x : AngCircle) :=
      integral_const_mul _ _
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        integral_Ioc_eq_integral_Ioo]

theorem central_probability_integral_q_EX040 (h : ℝ) (hh : 0 < h) (F : ℝ → ℝ) :
    (∫ x, F x ∂(centralProbability_EX040 h hh : Measure ℝ)) =
      centralNormFactor_EX040 h hh *
        (∫ x in -(π / 2)..π / 2, F x * qAng h (x : AngCircle)) := by
  rw [central_probability_coe_EX040 h hh, integral_smul_nnreal_measure,
    central_raw_integral_q_EX040 h hh]
  simp only [NNReal.smul_def, NNReal.coe_inv, smul_eq_mul]
  unfold centralNormFactor_EX040
  ring

theorem central_continuousOn_integrable_EX040 (h : ℝ) (hh : 0 < h) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Icc (-(π / 2)) (π / 2))) :
    Integrable F (centralProbability_EX040 h hh : Measure ℝ) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  have hraw : AEStronglyMeasurable F (centralRawMeasure_EX040 h) :=
    ((hF.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hfa : AEStronglyMeasurable F (centralProbability_EX040 h hh : Measure ℝ) := by
    rw [central_probability_coe_EX040]
    exact hraw.smul_measure _
  apply (integrable_const C).mono' hfa
  apply central_probability_ae_EX040 h hh
  filter_upwards with x hx
  exact hC x ⟨hx.1.le, hx.2.le⟩

/-- The h-dependent logarithmic normalization cancels the one-half logarithmic entropy
defect at delta = 32/h, with a constant independent of h. -/
theorem central_log_normalization_EX040 :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ) (h32 : 32 ≤ h),
      Real.log (Zh h) - Real.log (centralNormFactor_EX040 h (by linarith)) -
        (1 / 2) * Real.log (32 / h) ≤ C := by
  let C0 : ℝ := (2 * π)⁻¹ * Real.sqrt (π / (2 / π ^ 2))
  let K : ℝ := Real.log C0 + Real.log (2 * π) - (1 / 2) * Real.log 32
  refine ⟨|K| + 1, by positivity, fun h hh => ?_⟩
  have hp : 0 < h := by linarith
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hz := Real.log_le_log (Zh_pos h hp) (Zh_le h hp)
  change Real.log (Zh h) ≤ Real.log (C0 * (Real.sqrt h)⁻¹) at hz
  rw [Real.log_mul hC0.ne' (inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne',
    Real.log_inv, Real.log_sqrt hp.le] at hz
  have hmpos := central_mass_pos_EX040 h hp
  have hmle := central_mass_le_one_EX040 h hp
  have hmlog : Real.log ((centralFiniteMeasure_EX040 h hp).mass : ℝ) ≤ 0 := by
    simpa only [Real.log_one] using Real.log_le_log hmpos hmle
  have hα : Real.log (centralNormFactor_EX040 h hp) =
      -Real.log ((centralFiniteMeasure_EX040 h hp).mass : ℝ) - Real.log (2 * π) := by
    unfold centralNormFactor_EX040
    rw [Real.log_div (inv_pos.mpr hmpos).ne' (by positivity), Real.log_inv]
  have hδ : Real.log (32 / h) = Real.log 32 - Real.log h :=
    Real.log_div (by norm_num) hp.ne'
  rw [hα, hδ]
  have hK : K ≤ |K| + 1 := by linarith [le_abs_self K]
  dsimp [K] at hK
  linarith

/-- Finite conditional integrals give finite raw weighted interval integrals. -/
theorem central_integrable_weighted_EX040 (h : ℝ) (hh : 0 < h) {F : ℝ → ℝ}
    (hF : Integrable F (centralProbability_EX040 h hh : Measure ℝ)) :
    IntervalIntegrable (fun x => F x * qAng h (x : AngCircle)) volume
      (-(π / 2)) (π / 2) := by
  have hd := hardyData_qAng hh
  have hp := continuous_pOf_hardy hd.cont
  have hraw : Integrable F (centralRawMeasure_EX040 h) := by
    rw [central_raw_eq_mass_smul_EX040]
    exact hF.smul_measure_nnreal
  change Integrable F ((volume.restrict (Ioo (-(π / 2)) (π / 2))).withDensity
    (fun x => ENNReal.ofReal (pOf (qAng h) x))) at hraw
  have hi := (integrable_withDensity_iff_integrable_smul' hp.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hraw
  have hi' : Integrable (fun x => pOf (qAng h) x * F x)
      (volume.restrict (Ioo (-(π / 2)) (π / 2))) := by
    apply hi.congr
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (pOf_nonneg_hardy hd.pos x), smul_eq_mul]
  have hj := hi'.const_mul (2 * π)
  have heq : (fun x => (2 * π) * (pOf (qAng h) x * F x)) =
      fun x => F x * qAng h (x : AngCircle) := by
    funext x
    unfold pOf
    field_simp [show (2 * π : ℝ) ≠ 0 by positivity]
  rw [heq] at hj
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by linarith [Real.pi_pos] : -(π / 2) ≤ π / 2)).mpr hj

/-- Exact entropy conjugation for a positive-mass AC test. The zero-mass case is handled
separately in the defective inequality. -/
theorem central_entropy_conjugation_EX040 (h : ℝ) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f (-(π / 2)) (π / 2))
    (hM : 0 < ∫ x in -(π / 2)..π / 2, liftGroundStateConj h f x ^ 2) :
    DGPS.homogeneousEntropy (centralProbability_EX040 h hh : Measure ℝ) (fun x => f x ^ 2) =
      ENNReal.ofReal (centralNormFactor_EX040 h hh *
        ((∫ x in -(π / 2)..π / 2,
          liftGroundStateConj h f x ^ 2 *
            Real.log (liftGroundStateConj h f x ^ 2 /
              (∫ y in -(π / 2)..π / 2, liftGroundStateConj h f y ^ 2))) +
          (∫ x in -(π / 2)..π / 2,
            (h * (1 - Real.cos x) + corr h (1 - Real.cos x) +
              Real.log (Zh h) - Real.log (centralNormFactor_EX040 h hh)) *
              liftGroundStateConj h f x ^ 2))) := by
  let w := liftGroundStateConj h f
  let α := centralNormFactor_EX040 h hh
  let M : ℝ := ∫ x in -(π / 2)..π / 2, w x ^ 2
  let Φ : ℝ → ℝ := fun x => h * (1 - Real.cos x) + corr h (1 - Real.cos x)
  have hα : 0 < α := central_norm_factor_pos_EX040 h hh
  have hMp : 0 < M := hM
  have hw2 : ∀ x : ℝ, w x ^ 2 = f x ^ 2 * qAng h (x : AngCircle) := by
    intro x
    have hs : sqrtQ h x ^ 2 = qAng h (x : AngCircle) := sqrtQ_sqrtQ h hh x
    change (f x * sqrtQ h x) ^ 2 = _
    rw [mul_pow, hs]
  have hMf : (∫ x, f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) = α * M := by
    rw [central_probability_integral_q_EX040]
    congr 1
    exact intervalIntegral.integral_congr fun x _ => (hw2 x).symm
  have hfc : ContinuousOn f (Icc (-(π / 2)) (π / 2)) := by
    simpa only [uIcc_of_le (show -(π / 2) ≤ π / 2 by linarith [Real.pi_pos])]
      using hf.continuousOn
  have hfi := central_continuousOn_integrable_EX040 h hh (hfc.pow 2)
  have hfli := central_continuousOn_integrable_EX040 h hh
    (Real.continuous_mul_log.comp_continuousOn (hfc.pow 2))
  rw [DGPS.homogeneousEntropy_eq_formula
    (Eventually.of_forall fun _ => sq_nonneg _) hfi hfli,
    central_probability_integral_q_EX040, hMf]
  have hpt : ∀ x : ℝ,
      f x ^ 2 * Real.log (f x ^ 2) * qAng h (x : AngCircle) -
        Real.log (α * M) * w x ^ 2 =
      w x ^ 2 * Real.log (w x ^ 2 / M) +
        (Φ x + Real.log (Zh h) - Real.log α) * w x ^ 2 := by
    intro x
    by_cases hx : f x = 0
    · have hwz : w x ^ 2 = 0 := by rw [hw2, hx]; simp
      simp [hx, hwz]
    · have hq : 0 < qAng h (x : AngCircle) := qAng_pos h hh _
      have hwpos : 0 < w x ^ 2 := by rw [hw2]; positivity
      have hlogq : Real.log (qAng h (x : AngCircle)) = -Φ x - Real.log (Zh h) := by
        rw [qAng_coe_hardy, Real.log_mul (inv_pos.mpr (Zh_pos h hh)).ne' (Real.exp_pos _).ne',
          Real.log_inv, Real.log_exp]
        dsimp [Φ]
        ring
      rw [Real.log_div hwpos.ne' hMp.ne', Real.log_mul hα.ne' hMp.ne',
        hw2, Real.log_mul (pow_ne_zero 2 hx) hq.ne', hlogq]
      ring
  have hleft : IntervalIntegrable (fun x => f x ^ 2 * Real.log (f x ^ 2) *
      qAng h (x : AngCircle)) volume (-(π / 2)) (π / 2) :=
    central_integrable_weighted_EX040 h hh hfli
  have hwc : ContinuousOn w (uIcc (-(π / 2)) (π / 2)) :=
    hf.continuousOn.mul (contDiff_sqrtQ h hh).continuous.continuousOn
  have hwi : IntervalIntegrable (fun x => w x ^ 2) volume (-(π / 2)) (π / 2) :=
    (hwc.pow 2).intervalIntegrable
  have hΦc : Continuous Φ := by
    have hc := (contDiff_corr h hh).continuous
    dsimp [Φ]
    fun_prop
  have hpot : IntervalIntegrable (fun x => (Φ x + Real.log (Zh h) - Real.log α) * w x ^ 2)
      volume (-(π / 2)) (π / 2) :=
    (((hΦc.add continuous_const).sub continuous_const).continuousOn.mul
      (hwc.pow 2)).intervalIntegrable
  have hraw : IntervalIntegrable (fun x => w x ^ 2 * Real.log (w x ^ 2 / M))
      volume (-(π / 2)) (π / 2) := by
    have hi := (hleft.sub (hwi.const_mul (Real.log (α * M)))).sub hpot
    exact hi.congr (fun x _ => by rw [hpt]; ring)
  have hint :
      (∫ x in -(π / 2)..π / 2, f x ^ 2 * Real.log (f x ^ 2) * qAng h (x : AngCircle) -
        Real.log (α * M) * w x ^ 2) =
      ∫ x in -(π / 2)..π / 2, w x ^ 2 * Real.log (w x ^ 2 / M) +
        (Φ x + Real.log (Zh h) - Real.log α) * w x ^ 2 :=
    intervalIntegral.integral_congr (fun x _ => hpt x)
  rw [intervalIntegral.integral_sub hleft (hwi.const_mul (Real.log (α * M))),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hraw hpot] at hint
  congr 1
  change α * (∫ x in -(π / 2)..π / 2, f x ^ 2 * Real.log (f x ^ 2) * qAng h (x : AngCircle)) -
      (α * M) * Real.log (α * M) =
    α * ((∫ x in -(π / 2)..π / 2, w x ^ 2 * Real.log (w x ^ 2 / M)) +
      ∫ x in -(π / 2)..π / 2, (Φ x + Real.log (Zh h) - Real.log α) * w x ^ 2)
  calc
    _ = α * ((∫ x in -(π / 2)..π / 2,
        f x ^ 2 * Real.log (f x ^ 2) * qAng h (x : AngCircle)) -
          Real.log (α * M) * M) := by ring
    _ = _ := by rw [hint]


theorem central_ground_mass_EX040 (h : ℝ) (hh : 0 < h) (f : ℝ → ℝ) :
    (∫ x, f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) =
      centralNormFactor_EX040 h hh *
        ∫ x in -(π / 2)..π / 2, liftGroundStateConj h f x ^ 2 := by
  rw [central_probability_integral_q_EX040]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  have hs : sqrtQ h x ^ 2 = qAng h (x : AngCircle) := sqrtQ_sqrtQ h hh x
  change f x ^ 2 * qAng h (x : AngCircle) = (f x * sqrtQ h x) ^ 2
  rw [mul_pow, hs]

/-- Uniform defective central LSI, before Rothaus removes the bounded mass defect. -/
theorem central_defective_lsi_EX040 :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (h : ℝ) (hh : 0 < h), 32 ≤ h → ∀ f : ℝ → ℝ,
      AbsolutelyContinuousOnInterval f (-(π / 2)) (π / 2) →
      Integrable (fun x => deriv f x ^ 2) (centralProbability_EX040 h hh : Measure ℝ) →
      DGPS.homogeneousEntropy (centralProbability_EX040 h hh : Measure ℝ) (fun x => f x ^ 2) ≤
        ENNReal.ofReal ((32 / h) *
          (∫ x, deriv f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) +
            B * (∫ x, f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ))) := by
  obtain ⟨C0, hC0, habs⟩ := central_potential_absorption_EX040
  obtain ⟨C1, hC1, hnorm⟩ := central_log_normalization_EX040
  let B : ℝ := C0 + C1 + Real.log 2
  have hB : 0 ≤ B := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp [B]
    linarith
  refine ⟨B, hB, fun h hh h32 f hf hEP => ?_⟩
  let w := liftGroundStateConj h f
  let α := centralNormFactor_EX040 h hh
  let δ : ℝ := 32 / h
  let M : ℝ := ∫ x in -(π / 2)..π / 2, w x ^ 2
  let Eq : ℝ := ∫ x in -(π / 2)..π / 2, deriv f x ^ 2 * qAng h (x : AngCircle)
  let Ew : ℝ := ∫ x in -(π / 2)..π / 2, deriv w x ^ 2
  let V : ℝ := ∫ x in -(π / 2)..π / 2, groundPot h x * w x ^ 2
  let Φ : ℝ → ℝ := fun x => h * (1 - Real.cos x) + corr h (1 - Real.cos x)
  let Fm : ℝ := ∫ x in -(π / 2)..π / 2, Φ x * w x ^ 2
  let H : ℝ := ∫ x in -(π / 2)..π / 2, w x ^ 2 * Real.log (w x ^ 2 / M)
  let T : ℝ := ∫ x in -(π / 2)..π / 2,
    (Φ x + Real.log (Zh h) - Real.log α) * w x ^ 2
  have hM0 : 0 ≤ M :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun _ _ => sq_nonneg _
  have hMf := central_ground_mass_EX040 h hh f
  change (∫ x, f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) = α * M at hMf
  by_cases hMz : M = 0
  · have hmzero : (∫ x, f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) = 0 := by
      rw [hMf, hMz, mul_zero]
    rw [DGPS.homogeneousEntropy_of_integral_eq_zero hmzero]
    exact bot_le
  have hMp : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hMz)
  have hα : 0 < α := central_norm_factor_pos_EX040 h hh
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one hh).mpr h32
  have hab : -(π / 2) < π / 2 := by linarith [Real.pi_pos]
  have hEqI := central_integrable_weighted_EX040 h hh hEP
  have hwH := interval_ground_state_H1_EX040 h hh hf hEqI
  have hw2 : ContinuousOn (fun x => w x ^ 2) (uIcc (-(π / 2)) (π / 2)) :=
    hwH.1.continuousOn.pow 2
  have hwI : IntervalIntegrable (fun x => w x ^ 2) volume (-(π / 2)) (π / 2) :=
    hw2.intervalIntegrable
  have hVI : IntervalIntegrable (fun x => groundPot h x * w x ^ 2) volume
      (-(π / 2)) (π / 2) :=
    ((continuous_groundPot h hh).continuousOn.mul hw2).intervalIntegrable
  have hΦc : Continuous Φ := by
    have hc := (contDiff_corr h hh).continuous
    dsimp [Φ]
    fun_prop
  have hFI : IntervalIntegrable (fun x => Φ x * w x ^ 2) volume (-(π / 2)) (π / 2) :=
    (hΦc.continuousOn.mul hw2).intervalIntegrable
  have hground := central_ground_state_energy_le_EX040 h hh hf hEqI
  rw [intervalIntegral.integral_add hwH.2 hVI] at hground
  change Ew + V ≤ Eq at hground
  have hFbound : Fm ≤ δ * V + C0 * M := by
    have hi : (∫ x in -(π / 2)..π / 2, Φ x * w x ^ 2) ≤
        ∫ x in -(π / 2)..π / 2, δ * (groundPot h x * w x ^ 2) + C0 * w x ^ 2 := by
      apply intervalIntegral.integral_mono_on hab.le hFI
        ((hVI.const_mul δ).add (hwI.const_mul C0))
      intro x hx
      have hp := mul_le_mul_of_nonneg_right (habs h h32 x hx) (sq_nonneg (w x))
      change (Φ x - δ * groundPot h x) * w x ^ 2 ≤ C0 * w x ^ 2 at hp
      nlinarith
    rw [intervalIntegral.integral_add (hVI.const_mul δ) (hwI.const_mul C0),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
    exact hi
  have hent := interval_entropy_estimate_EX040 hab
    (by linarith [Real.pi_gt_three] : 1 ≤ π / 2 - -(π / 2)) hδ hδ1 hwH.1 hwH.2
  change H ≤ δ * Ew + (Real.log 2 - (1 / 2) * Real.log δ) * M at hent
  have hT : T = Fm + (Real.log (Zh h) - Real.log α) * M := by
    have heq : (fun x => (Φ x + Real.log (Zh h) - Real.log α) * w x ^ 2) =
        fun x => Φ x * w x ^ 2 + (Real.log (Zh h) - Real.log α) * w x ^ 2 := by
      funext x
      ring
    change (∫ x in -(π / 2)..π / 2,
      (Φ x + Real.log (Zh h) - Real.log α) * w x ^ 2) = _
    rw [heq, intervalIntegral.integral_add hFI
      (hwI.const_mul (Real.log (Zh h) - Real.log α)), intervalIntegral.integral_const_mul]
  have hn := hnorm h h32
  change Real.log (Zh h) - Real.log α - (1 / 2) * Real.log δ ≤ C1 at hn
  have hnM := mul_le_mul_of_nonneg_right hn hM0
  have hgδ := mul_le_mul_of_nonneg_left hground hδ.le
  have hbound : H + T ≤ δ * Eq + B * M := by
    rw [hT]
    dsimp [B]
    linarith
  have hep := central_probability_integral_q_EX040 h hh (fun x => deriv f x ^ 2)
  change (∫ x, deriv f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) = α * Eq at hep
  rw [central_entropy_conjugation_EX040 h hh hf hMp]
  apply ENNReal.ofReal_le_ofReal
  change α * (H + T) ≤ δ *
    (∫ x, deriv f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) +
      B * (∫ x, f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ))
  calc
    _ ≤ α * (δ * Eq + B * M) := mul_le_mul_of_nonneg_left hbound hα.le
    _ = _ := by rw [hep, hMf]; ring


/-- Rothaus removes the uniform bounded defect using the central conditional Poincare bound. -/
theorem central_ac_lsi_EX040 :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ) (hh : 0 < h), 32 ≤ h → ∀ f : ℝ → ℝ,
      AbsolutelyContinuousOnInterval f (-(π / 2)) (π / 2) →
      Integrable (fun x => deriv f x ^ 2) (centralProbability_EX040 h hh : Measure ℝ) →
      DGPS.homogeneousEntropy (centralProbability_EX040 h hh : Measure ℝ) (fun x => f x ^ 2) ≤
        ENNReal.ofReal ((C / h) *
          ∫ x, deriv f x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) := by
  obtain ⟨B, hB, hdef⟩ := central_defective_lsi_EX040
  let C : ℝ := 32 + 4 * π * (B + 2)
  refine ⟨C, by dsimp [C]; positivity, fun h hh h32 f hf hE => ?_⟩
  let P : Measure ℝ := centralProbability_EX040 h hh
  let E : ℝ := ∫ x, deriv f x ^ 2 ∂P
  let V : ℝ := ProbabilityTheory.variance f P
  let c : ℝ := ∫ x, f x ∂P
  let g : ℝ → ℝ := fun x => f x - c
  have hEV : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hV : 0 ≤ V := ProbabilityTheory.variance_nonneg _ _
  have hpoin := central_probability_ac_poincare_EX040 h hh hf hE
  have hmem : MemLp f 2 P := hpoin.1
  have hvar : V ≤ (4 * π / h) * E := hpoin.2
  have hcac : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) (-(π / 2)) (π / 2) :=
    (show ContDiff ℝ 1 (fun _ : ℝ => c) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  have hgc : AbsolutelyContinuousOnInterval g (-(π / 2)) (π / 2) := hf.fun_sub hcac
  have hge : Integrable (fun x => deriv g x ^ 2) P := by
    change Integrable (fun x => deriv (fun x => f x - c) x ^ 2) P
    simpa only [deriv_sub_const] using hE
  have hdf := hdef h hh h32 g hgc hge
  have hcent : (∫ x, g x ^ 2 ∂P) = V := by
    exact (ProbabilityTheory.variance_eq_integral hmem.aemeasurable).symm
  have hgen : (∫ x, deriv g x ^ 2 ∂P) = E := by
    simp only [g, deriv_sub_const, E]
  rw [hcent, hgen] at hdf
  have hr := DGPS.FiniteN.Tools.Rothaus.rothaus_centering_variance hmem
  change DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
    DGPS.homogeneousEntropy P (fun x => g x ^ 2) + ENNReal.ofReal (2 * V) at hr
  have hraw : DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
      ENNReal.ofReal ((32 / h) * E + (B + 2) * V) := by
    calc
      _ ≤ DGPS.homogeneousEntropy P (fun x => g x ^ 2) + ENNReal.ofReal (2 * V) := hr
      _ ≤ ENNReal.ofReal ((32 / h) * E + B * V) + ENNReal.ofReal (2 * V) :=
        add_le_add hdf le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  have hv := mul_le_mul_of_nonneg_left hvar (show 0 ≤ B + 2 by linarith)
  have heq : (32 / h) * E + (B + 2) * ((4 * π / h) * E) = (C / h) * E := by
    dsimp [C]
    ring
  rw [← heq]
  linarith

/-- EX040: the conditioned engineered law on [-pi/2,pi/2] has a uniform C/h logarithmic
Sobolev inequality for every interval weighted weak-H1 test. The threshold is the explicit
absolute constant 32; endpoint traces are unrestricted. -/
theorem central_weak_lsi_EX040 :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ) (h32 : 32 ≤ h) (u g : ℝ → ℝ),
      MemLp u 2 (centralProbability_EX040 h (by linarith) : Measure ℝ) →
      MemLp g 2 (centralProbability_EX040 h (by linarith) : Measure ℝ) →
      (∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioo (-(π / 2)) (π / 2) →
        (∫ x in -(π / 2)..π / 2, u x * deriv ψ x) =
          -(∫ x in -(π / 2)..π / 2, g x * ψ x)) →
      DGPS.homogeneousEntropy (centralProbability_EX040 h (by linarith) : Measure ℝ)
        (fun x => u x ^ 2) ≤
        ENNReal.ofReal ((C / h) * ∫ x, g x ^ 2
          ∂(centralProbability_EX040 h (by linarith) : Measure ℝ)) := by
  obtain ⟨C, hC, hAC⟩ := central_ac_lsi_EX040
  refine ⟨C, hC, fun h h32 u g hu hg hw => ?_⟩
  have hh : 0 < h := by linarith
  obtain ⟨v, hvac, huv, hdv⟩ := interval_weak_ac_rep_EX040
    (show -(π / 2) < π / 2 by linarith [Real.pi_pos])
    (central_memLp_intervalIntegrable_EX040 h hh hu)
    (central_memLp_intervalIntegrable_EX040 h hh hg) hw
  have huvP := central_probability_ae_EX040 h hh huv
  have hdvP : deriv v =ᵐ[(centralProbability_EX040 h hh : Measure ℝ)] g := by
    apply central_probability_ae_EX040 h hh
    filter_upwards [hdv] with x hx hmem
    exact (hx (Icc_subset_uIcc ⟨hmem.1.le, hmem.2.le⟩)).deriv
  have hvi : Integrable (fun x => deriv v x ^ 2)
      (centralProbability_EX040 h hh : Measure ℝ) := by
    apply hg.integrable_sq.congr
    filter_upwards [hdvP] with x hx
    rw [hx]
  calc
    _ = DGPS.homogeneousEntropy (centralProbability_EX040 h hh : Measure ℝ)
        (fun x => v x ^ 2) :=
      DGPS.homogeneousEntropy_congr_ae (huvP.mono fun x hx => by simpa only using congrArg (fun r : ℝ => r ^ 2) hx)
    _ ≤ ENNReal.ofReal ((C / h) * ∫ x, deriv v x ^ 2
        ∂(centralProbability_EX040 h hh : Measure ℝ)) := hAC h hh h32 v hvac hvi
    _ = _ := by
      rw [integral_congr_ae (hdvP.mono fun x hx => by simpa only using congrArg (fun r : ℝ => r ^ 2) hx)]


/-- EX040 in the preparation's existential-constant form. Positivity of h is redundant
once h is above the positive threshold; it supplies the conditioned-law representation. -/
theorem central_conditional_lsi_for_engineered_law :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧ ∀ (h : ℝ) (hh : 0 < h), h0 ≤ h →
      ∀ u g : ℝ → ℝ,
        MemLp u 2 (centralProbability_EX040 h hh : Measure ℝ) →
        MemLp g 2 (centralProbability_EX040 h hh : Measure ℝ) →
        (∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ Ioo (-(π / 2)) (π / 2) →
          (∫ x in -(π / 2)..π / 2, u x * deriv ψ x) =
            -(∫ x in -(π / 2)..π / 2, g x * ψ x)) →
        DGPS.homogeneousEntropy (centralProbability_EX040 h hh : Measure ℝ)
          (fun x => u x ^ 2) ≤
          ENNReal.ofReal ((C / h) *
            ∫ x, g x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ)) := by
  obtain ⟨C, hC, hweak⟩ := central_weak_lsi_EX040
  refine ⟨C, 32, hC, by norm_num, fun h hh h32 u g hu hg hw => ?_⟩
  exact hweak h h32 u g hu hg hw


end DGPS.Examples
