import DGPS.Examples.EngineeredCentralInterval
import DGPS.Examples.EngineeredIntervalWeak
import DGPS.Examples.EngineeredIntervalEntropy
import DGPS.Examples.EngineeredHardy

/-!
# Central interval estimates for EX040

The circle resistance estimate restricts to the central interval and yields a uniform
Poincare bound for its conditioned probability on both AC representatives and the full
weighted weak-H1 domain. Ground-state finite-energy preservation and potential absorption
are also proved. Endpoint values and traces are unrestricted.
This module does not assert the full weak-domain central conditional LSI.
-/

open MeasureTheory Real Set Filter Topology
open DGPS.Circle.AngularNormalization DGPS.FiniteN
open scoped NNReal ENNReal ContDiff

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredHardy

/-- Unnormalized restriction of the engineered probability to the central interval. -/
noncomputable abbrev centralRawMeasure_EX040 (h : ℝ) : Measure ℝ :=
  DGPS.FiniteN.densityMeasure (Ioo (-(π / 2)) (π / 2)) (pOf (qAng h))

theorem central_raw_measure_eq_restrict_EX040 (h : ℝ) :
    centralRawMeasure_EX040 h =
      (muOf (qAng h)).restrict (Ioo (-(π / 2)) (π / 2)) := by
  have hsub : Ioo (-(π / 2)) (π / 2) ⊆ Ioo (-π) π := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  unfold centralRawMeasure_EX040 muOf DGPS.FiniteN.densityMeasure
  rw [restrict_withDensity measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hsub]

theorem central_raw_measure_le_EX040 (h : ℝ) :
    centralRawMeasure_EX040 h ≤ muOf (qAng h) := by
  rw [central_raw_measure_eq_restrict_EX040]
  exact Measure.restrict_le_self

/-- The central interval has the same uniform upper bound on both anchored resistance
products as the whole circle. -/
theorem central_hardy_products_EX040 (h : ℝ) (hh : 0 < h) :
    (∀ x ∈ Ioo (-(π / 2)) (π / 2), 0 < x →
      (centralRawMeasure_EX040 h (Ici x)).toReal *
        (∫ t in (0 : ℝ)..x, (pOf (qAng h) t)⁻¹) ≤ π / h) ∧
    (∀ x ∈ Ioo (-(π / 2)) (π / 2), x < 0 →
      (centralRawMeasure_EX040 h (Iic x)).toReal *
        (∫ t in x..(0 : ℝ), (pOf (qAng h) t)⁻¹) ≤ π / h) := by
  have hd := hardyData_qAng hh
  let : IsProbabilityMeasure (muOf (qAng h)) :=
    isProbabilityMeasure_muOf_hardy hd.cont hd.pos hd.int_one
  constructor
  · intro x hx hx0
    have hxπ : x ∈ Ioo (-π) π :=
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
    have htail := ENNReal.toReal_mono (measure_ne_top (muOf (qAng h)) (Ici x))
      (central_raw_measure_le_EX040 h (Ici x))
    have hres : 0 ≤ ∫ t in (0 : ℝ)..x, (pOf (qAng h) t)⁻¹ :=
      intervalIntegral.integral_nonneg hx0.le fun t _ =>
        inv_nonneg.mpr (pOf_nonneg_hardy hd.pos t)
    exact (mul_le_mul_of_nonneg_right htail hres).trans (right_term_hardy hd hxπ hx0)
  · intro x hx hx0
    have hxπ : x ∈ Ioo (-π) π :=
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
    have htail := ENNReal.toReal_mono (measure_ne_top (muOf (qAng h)) (Iic x))
      (central_raw_measure_le_EX040 h (Iic x))
    have hres : 0 ≤ ∫ t in x..(0 : ℝ), (pOf (qAng h) t)⁻¹ :=
      intervalIntegral.integral_nonneg hx0.le fun t _ =>
        inv_nonneg.mpr (pOf_nonneg_hardy hd.pos t)
    exact (mul_le_mul_of_nonneg_right htail hres).trans (left_term_hardy hd hxπ hx0)

/-- An absolutely continuous interval representative supplies the exact FTC interface
consumed by FIN006, with no conditions on its endpoint traces. -/
theorem central_ac_ftc_EX040 {g : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g (-(π / 2)) (π / 2)) :
    (∀ x ∈ Ioo (-(π / 2)) (π / 2), ∀ y ∈ Ioo (-(π / 2)) (π / 2),
      g y - g x = ∫ t in x..y, deriv g t) ∧
    LocallyIntegrableOn (deriv g) (Ioo (-(π / 2)) (π / 2)) volume := by
  have hab : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  constructor
  · intro x hx y hy
    apply Eq.symm
    apply (hg.mono ?_).integral_deriv_eq_sub
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩
  · have hi := hg.intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hi
    exact (hi.mono_set Ioo_subset_Icc_self).locallyIntegrableOn

/-- Uniform anchored Hardy inequality on the full AC interval domain. This is a genuine
central-interval bound, with arbitrary endpoint traces. -/
theorem central_ac_hardy_EX040 (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g (-(π / 2)) (π / 2)) :
    (∫⁻ t, ENNReal.ofReal ((g t - g 0) ^ 2) ∂centralRawMeasure_EX040 h) ≤
      ENNReal.ofReal (4 * π / h) *
        ∫⁻ t, ENNReal.ofReal (deriv g t ^ 2) ∂centralRawMeasure_EX040 h := by
  have hd := hardyData_qAng hh
  let : IsProbabilityMeasure (muOf (qAng h)) :=
    isProbabilityMeasure_muOf_hardy hd.cont hd.pos hd.int_one
  let : IsFiniteMeasure (centralRawMeasure_EX040 h) :=
    isFiniteMeasure_of_le (muOf (qAng h)) (central_raw_measure_le_EX040 h)
  have hp : Continuous (pOf (qAng h)) := continuous_pOf_hardy hd.cont
  have hp0 : ∀ t ∈ Ioo (-(π / 2)) (π / 2), 0 < pOf (qAng h) t := by
    intro t _
    unfold pOf
    exact div_pos (hd.pos _) (by positivity)
  have hprod := central_hardy_products_EX040 h hh
  have hftc := central_ac_ftc_EX040 hg
  have hhdy := hardy_of_bounds isOpen_Ioo (ordConnected_Ioo) (by
      constructor <;> linarith [Real.pi_pos] : (0 : ℝ) ∈ Ioo (-(π / 2)) (π / 2))
    hp.continuousOn hp0 hprod.1 hprod.2 hftc.1 hftc.2
  simpa only [max_self, mul_div_assoc] using hhdy

/-- The ground-state conjugate has finite unweighted interval energy whenever the original
AC representative has finite weighted energy. -/
theorem interval_ground_state_H1_EX040 (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hE : IntervalIntegrable (fun t => deriv g t ^ 2 * qAng h (t : AngCircle)) volume a b) :
    AbsolutelyContinuousOnInterval
        (DGPS.Examples.EngineeredGroundState.liftGroundStateConj h g) a b ∧
      IntervalIntegrable (fun t =>
        deriv (DGPS.Examples.EngineeredGroundState.liftGroundStateConj h g) t ^ 2) volume a b := by
  have hi := interval_ground_state_identity_EX040 h hh hg hE
  refine ⟨hi.1, ?_⟩
  have hpot : IntervalIntegrable (fun t => groundPot h t *
      DGPS.Examples.EngineeredGroundState.liftGroundStateConj h g t ^ 2) volume a b :=
    ((DGPS.Examples.EngineeredGroundState.continuous_groundPot h hh).continuousOn.mul
      (hi.1.continuousOn.pow 2)).intervalIntegrable
  have hd := hi.2.1.sub hpot
  simpa using hd

/-- The large-parameter potential absorption used in the central defective-LSI route.
The constant is independent of the test function, parameter, and point in the interval. -/
theorem central_potential_absorption_EX040 :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 32 ≤ h →
      ∀ t ∈ Icc (-(π / 2)) (π / 2),
        h * (1 - Real.cos t) + corr h (1 - Real.cos t) -
          (32 / h) * groundPot h t ≤ C := by
  obtain ⟨C, hC, hpot⟩ := engineered_drift_and_ground_potential
  refine ⟨32 * C, by positivity, fun h hh t ht => ?_⟩
  have hh2 : 2 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  have hcos0 : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ht
  have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have hU0 : 0 ≤ 1 - Real.cos t := by linarith
  have hsin : 1 - Real.cos t ≤ Real.sin t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t, mul_nonneg hcos0 (sub_nonneg.mpr hcos1)]
  have hcorr := corr_le h hh2 (show 1 - Real.cos t ∈ Icc (0 : ℝ) 2 by
    constructor <;> linarith)
  have hlo := (hpot h hh2 t).2.2
  have hmul := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 32 / h by positivity)
  have heq : (32 / h) * (h ^ 2 * Real.sin t ^ 2 / 4 - C * h) =
      8 * h * Real.sin t ^ 2 - 32 * C := by
    field_simp [hh0.ne']
    ring
  rw [heq] at hmul
  have hsin2 := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 8 * h by positivity)
  nlinarith [mul_nonneg hh0.le hU0]

/-- Finiteness needed to normalize the central restriction. -/
theorem central_raw_finite_EX040 (h : ℝ) (hh : 0 < h) :
    IsFiniteMeasure (centralRawMeasure_EX040 h) := by
  have hd := hardyData_qAng hh
  let : IsProbabilityMeasure (muOf (qAng h)) :=
    isProbabilityMeasure_muOf_hardy hd.cont hd.pos hd.int_one
  exact isFiniteMeasure_of_le (muOf (qAng h)) (central_raw_measure_le_EX040 h)

/-- The central restriction has strictly positive mass. -/
theorem central_raw_ne_zero_EX040 (h : ℝ) (hh : 0 < h) :
    centralRawMeasure_EX040 h ≠ 0 := by
  have hd := hardyData_qAng hh
  have hp : Continuous (pOf (qAng h)) := continuous_pOf_hardy hd.cont
  have hp0 : ∀ t : ℝ, 0 < pOf (qAng h) t := by
    intro t
    exact div_pos (qAng_pos h hh _) (by positivity)
  have hm : Measurable (fun t => ENNReal.ofReal (pOf (qAng h) t)) :=
    hp.measurable.ennreal_ofReal
  intro hz
  have hmass : centralRawMeasure_EX040 h univ = 0 := by rw [hz]; simp
  unfold centralRawMeasure_EX040 DGPS.FiniteN.densityMeasure at hmass
  have hnull := (withDensity_apply_eq_zero hm).mp hmass
  have hs : {t : ℝ | ENNReal.ofReal (pOf (qAng h) t) ≠ 0} = univ := by
    ext t
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (hp0 t)).ne'
  rw [hs, inter_self, Measure.restrict_apply_univ, Real.volume_Ioo] at hnull
  have : 0 < ENNReal.ofReal (π / 2 - -(π / 2)) :=
    ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
  exact this.ne' hnull

/-- The finite central restriction, before normalization. -/
noncomputable def centralFiniteMeasure_EX040 (h : ℝ) (hh : 0 < h) : FiniteMeasure ℝ :=
  ⟨centralRawMeasure_EX040 h, central_raw_finite_EX040 h hh⟩

/-- The probability obtained by conditioning on the central interval. -/
noncomputable def centralProbability_EX040 (h : ℝ) (hh : 0 < h) : ProbabilityMeasure ℝ :=
  (centralFiniteMeasure_EX040 h hh).normalize

theorem central_probability_coe_EX040 (h : ℝ) (hh : 0 < h) :
    (centralProbability_EX040 h hh : Measure ℝ) =
      (centralFiniteMeasure_EX040 h hh).mass⁻¹ • centralRawMeasure_EX040 h := by
  apply FiniteMeasure.toMeasure_normalize_eq_of_nonzero
  intro hz
  apply central_raw_ne_zero_EX040 h hh
  exact congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) hz

/-- Uniform anchored Hardy bound for the conditioned probability and every absolutely
continuous interval test, without a boundary restriction. -/
theorem central_probability_ac_hardy_EX040 (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g (-(π / 2)) (π / 2)) :
    (∫⁻ t, ENNReal.ofReal ((g t - g 0) ^ 2)
      ∂(centralProbability_EX040 h hh : Measure ℝ)) ≤
      ENNReal.ofReal (4 * π / h) *
        ∫⁻ t, ENNReal.ofReal (deriv g t ^ 2)
          ∂(centralProbability_EX040 h hh : Measure ℝ) := by
  rw [central_probability_coe_EX040, lintegral_smul_measure, lintegral_smul_measure]
  have hi := central_ac_hardy_EX040 h hh hg
  calc
    _ ≤ ((centralFiniteMeasure_EX040 h hh).mass⁻¹ : ℝ≥0) •
        (ENNReal.ofReal (4 * π / h) *
          ∫⁻ t, ENNReal.ofReal (deriv g t ^ 2) ∂centralRawMeasure_EX040 h) :=
      smul_le_smul_of_nonneg_left hi (by positivity)
    _ = _ := by simp only [ENNReal.smul_def]; ring

/-- Conditional Poincare inequality for every AC finite-energy interval test, with the same
uniform coefficient as the anchored Hardy bound. The L2 hypothesis follows from finite energy. -/
theorem central_probability_ac_poincare_EX040 (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g (-(π / 2)) (π / 2))
    (hE : Integrable (fun t => deriv g t ^ 2)
      (centralProbability_EX040 h hh : Measure ℝ)) :
    MemLp g 2 (centralProbability_EX040 h hh : Measure ℝ) ∧
      ProbabilityTheory.variance g (centralProbability_EX040 h hh : Measure ℝ) ≤
        (4 * π / h) * ∫ t, deriv g t ^ 2
          ∂(centralProbability_EX040 h hh : Measure ℝ) := by
  let μ : Measure ℝ := centralProbability_EX040 h hh
  have hfc : ContinuousOn g (Ioo (-(π / 2)) (π / 2)) := by
    have hc := hg.continuousOn
    rw [uIcc_of_le (show -(π / 2) ≤ π / 2 by linarith [Real.pi_pos])] at hc
    exact hc.mono Ioo_subset_Icc_self
  have hraw : AEStronglyMeasurable g (centralRawMeasure_EX040 h) :=
    (hfc.aestronglyMeasurable measurableSet_Ioo).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hfa : AEStronglyMeasurable g μ := by
    change AEStronglyMeasurable g (centralProbability_EX040 h hh : Measure ℝ)
    rw [central_probability_coe_EX040]
    exact hraw.smul_measure _
  have hua : AEStronglyMeasurable (fun t => g t - g 0) μ :=
    hfa.sub aestronglyMeasurable_const
  have hmain := central_probability_ac_hardy_EX040 h hh hg
  have hE' : (∫⁻ t, ENNReal.ofReal (deriv g t ^ 2) ∂μ) =
      ENNReal.ofReal (∫ t, deriv g t ^ 2 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hE
      (Eventually.of_forall fun t => sq_nonneg _)).symm
  change (∫⁻ t, ENNReal.ofReal ((g t - g 0) ^ 2) ∂μ) ≤
    ENNReal.ofReal (4 * π / h) * ∫⁻ t, ENNReal.ofReal (deriv g t ^ 2) ∂μ at hmain
  rw [hE'] at hmain
  have hlt : (∫⁻ t, ENNReal.ofReal ((g t - g 0) ^ 2) ∂μ) < ⊤ :=
    hmain.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hint : Integrable (fun t => (g t - g 0) ^ 2) μ :=
    ⟨hua.pow 2,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => sq_nonneg _)).2 hlt⟩
  have hreal : (∫ t, (g t - g 0) ^ 2 ∂μ) ≤
      (4 * π / h) * ∫ t, deriv g t ^ 2 ∂μ := by
    have hK : 0 ≤ 4 * π / h := by positivity
    have hE0 : 0 ≤ ∫ t, deriv g t ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have h1 := ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun t => sq_nonneg (g t - g 0))
    rw [← h1, ← ENNReal.ofReal_mul hK] at hmain
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK hE0)).1 hmain
  have hmem : MemLp g 2 μ := by
    have h0 : MemLp (fun t => g t - g 0) 2 μ :=
      (memLp_two_iff_integrable_sq hua).2 hint
    have h3 := h0.add (memLp_const (g 0))
    have heq : ((fun t => g t - g 0) + (fun _ => g 0)) =ᵐ[μ] g :=
      Eventually.of_forall fun t => sub_add_cancel (g t) (g 0)
    exact (memLp_congr_ae heq).mp h3
  refine ⟨hmem, ?_⟩
  have hv := ProbabilityTheory.variance_sub_const hfa (g 0)
  have hv2 := ProbabilityTheory.variance_le_expectation_sq hua
  rw [← hv]
  exact hv2.trans hreal

/-- Closing the endpoints leaves the central restriction unchanged. -/
theorem central_raw_closed_interval_EX040 (h : ℝ) :
    centralRawMeasure_EX040 h =
      DGPS.FiniteN.densityMeasure (Icc (-(π / 2)) (π / 2)) (pOf (qAng h)) := by
  unfold centralRawMeasure_EX040 DGPS.FiniteN.densityMeasure
  rw [restrict_Ioo_eq_restrict_Icc]

/-- The raw restriction is its total mass times the conditioned probability. -/
theorem central_raw_eq_mass_smul_EX040 (h : ℝ) (hh : 0 < h) :
    centralRawMeasure_EX040 h =
      (centralFiniteMeasure_EX040 h hh).mass •
        (centralProbability_EX040 h hh : Measure ℝ) := by
  have hn : centralFiniteMeasure_EX040 h hh ≠ 0 := by
    intro hz
    exact central_raw_ne_zero_EX040 h hh
      (congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) hz)
  have hm : (centralFiniteMeasure_EX040 h hh).mass ≠ 0 :=
    (FiniteMeasure.mass_nonzero_iff _).mpr hn
  rw [central_probability_coe_EX040, smul_smul, mul_inv_cancel₀ hm, one_smul]

/-- A Lebesgue-a.e. statement on the central interval holds a.e. for its conditioned law. -/
theorem central_probability_ae_EX040 (h : ℝ) (hh : 0 < h) {p : ℝ → Prop}
    (hp : ∀ᵐ x, x ∈ Ioo (-(π / 2)) (π / 2) → p x) :
    ∀ᵐ x ∂(centralProbability_EX040 h hh : Measure ℝ), p x := by
  have hv : ∀ᵐ x ∂volume.restrict (Ioo (-(π / 2)) (π / 2)), p x :=
    (ae_restrict_iff' measurableSet_Ioo).mpr hp
  have hr : ∀ᵐ x ∂centralRawMeasure_EX040 h, p x :=
    (withDensity_absolutelyContinuous _ _).ae_le hv
  rw [central_probability_coe_EX040]
  exact Measure.ae_smul_measure hr _

/-- Weighted L2 tests lie in unweighted L1 on the fixed central interval. The comparison
constant here may depend on h; the later Poincare and entropy constants are uniform. -/
theorem central_memLp_intervalIntegrable_EX040 (h : ℝ) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : MemLp f 2 (centralProbability_EX040 h hh : Measure ℝ)) :
    IntervalIntegrable f volume (-(π / 2)) (π / 2) := by
  have hr : MemLp f 2 (centralRawMeasure_EX040 h) := by
    apply hf.of_measure_le_smul
      (c := ((centralFiniteMeasure_EX040 h hh).mass : ℝ≥0∞)) (by finiteness)
    rw [central_raw_eq_mass_smul_EX040]
    exact le_of_eq (by ext s hs; rfl)
  have hd := hardyData_qAng hh
  obtain ⟨m, M, hm, hbounds⟩ := exists_bounds_hardy hd.cont hd.pos
  let m0 : ℝ := m / (2 * π)
  have hm0 : 0 < m0 := div_pos hm (by positivity)
  have hmp : ∀ t : ℝ, m0 ≤ pOf (qAng h) t := fun t =>
    div_le_div_of_nonneg_right (hbounds (t : AngCircle)).1 (by positivity)
  have hle : volume.restrict (Ioo (-(π / 2)) (π / 2)) ≤
      ENNReal.ofReal m0⁻¹ • centralRawMeasure_EX040 h := by
    rw [Measure.le_iff']
    intro s
    change (volume.restrict (Ioo (-(π / 2)) (π / 2))) s ≤
      (ENNReal.ofReal m0⁻¹ •
        ((volume.restrict (Ioo (-(π / 2)) (π / 2))).withDensity
          (fun t => ENNReal.ofReal (pOf (qAng h) t)))) s
    rw [Measure.smul_apply, withDensity_apply' _ s, smul_eq_mul]
    have h1 : ENNReal.ofReal m0 *
        (volume.restrict (Ioo (-(π / 2)) (π / 2))) s ≤
        ∫⁻ t in s, ENNReal.ofReal (pOf (qAng h) t)
          ∂volume.restrict (Ioo (-(π / 2)) (π / 2)) := by
      rw [← setLIntegral_const]
      exact lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hmp t)
    calc
      _ = ENNReal.ofReal m0⁻¹ *
          (ENNReal.ofReal m0 * (volume.restrict (Ioo (-(π / 2)) (π / 2))) s) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hm0.le),
          inv_mul_cancel₀ hm0.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr
  have hv : MemLp f 2 (volume.restrict (Ioo (-(π / 2)) (π / 2))) :=
    hr.of_measure_le_smul ENNReal.ofReal_ne_top hle
  let : IsFiniteMeasure (volume.restrict (Ioo (-(π / 2)) (π / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by linarith [Real.pi_pos] : -(π / 2) ≤ π / 2)).mpr (hv.integrable one_le_two)

/-- The conditional Poincare bound on the full interval weighted weak-H1 domain. -/
theorem central_probability_weak_poincare_EX040 (h : ℝ) (hh : 0 < h) {u g : ℝ → ℝ}
    (hu : MemLp u 2 (centralProbability_EX040 h hh : Measure ℝ))
    (hg : MemLp g 2 (centralProbability_EX040 h hh : Measure ℝ))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (-(π / 2)) (π / 2) →
      (∫ x in -(π / 2)..π / 2, u x * deriv ψ x) =
        -(∫ x in -(π / 2)..π / 2, g x * ψ x)) :
    ProbabilityTheory.variance u (centralProbability_EX040 h hh : Measure ℝ) ≤
      (4 * π / h) * ∫ x, g x ^ 2 ∂(centralProbability_EX040 h hh : Measure ℝ) := by
  obtain ⟨v, hvac, huv, hdv⟩ := interval_weak_ac_rep_EX040
    (show -(π / 2) < π / 2 by linarith [Real.pi_pos])
    (central_memLp_intervalIntegrable_EX040 h hh hu)
    (central_memLp_intervalIntegrable_EX040 h hh hg) hweak
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
  have hp := (central_probability_ac_poincare_EX040 h hh hvac hvi).2
  rw [ProbabilityTheory.variance_congr huvP]
  refine hp.trans_eq ?_
  congr 1
  exact integral_congr_ae (hdvP.mono fun x hx => by simpa only using congrArg (fun r : ℝ => r ^ 2) hx)

end DGPS.Examples
