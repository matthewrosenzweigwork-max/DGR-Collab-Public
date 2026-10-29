import LeanResearch.PeriodicAttractiveLogGas.Rothaus
import LeanResearch.PeriodicAttractiveLogGas.DensityMoments

/-! The source relative-entropy variational inequality (lines 2680–2702).
The existing extended entropy and the literal withDensity law are retained.
The bounded-density, lower-bounded observable case derives all integrability. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace PeriodicAttractiveLogGas.RelativeEntropyVariational

variable {α : Type*} [MeasurableSpace α] {P Q : Measure α}

theorem abs_mul_log_le_one_add_sq {t : ℝ} (ht : 0 ≤ t) :
    |t * Real.log t| ≤ 1 + t ^ 2 := by
  have hlo := Real.self_sub_one_le_mul_log ht
  have hhi : t * Real.log t ≤ t ^ 2 := by
    rcases eq_or_lt_of_le ht with rfl | ht
    · simp
    · have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ht) ht.le
      nlinarith
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg t], by linarith⟩

/-- Both density and entropy density are genuinely integrable, including zeros
and arbitrary exceptional values off the support of the base law. -/
theorem bounded_density_integrable [IsFiniteMeasure P] {q : α → ℝ}
    (hq : Measurable q) {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ K) :
    Integrable q P ∧ Integrable (fun x => q x * Real.log (q x)) P := by
  constructor
  · apply Integrable.of_bound hq.aestronglyMeasurable |K|
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2.trans (le_abs_self K)
  · apply Integrable.of_bound (Real.continuous_mul_log.measurable.comp hq).aestronglyMeasurable (1 + K ^ 2)
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_mul_log_le_one_add_sq hx.1).trans (by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)])

theorem density_exp_pointwise {q G Z : ℝ} (hq : 0 ≤ q) (hZ : 0 < Z) :
    q * G ≤ q * Real.log q + q * Real.log Z + Real.exp G / Z - q := by
  have h := Rothaus.log_variational_pointwise hq (Real.exp_pos G) zero_lt_one hZ
  simp only [Real.log_exp, Real.log_one, mul_zero, sub_zero, one_div] at h
  rw [div_eq_mul_inv]
  nlinarith only [h]

/-- Finite-expression Jensen inequality, with every integral hypothesis explicit.
No logarithm of a density is integrated without its density factor. -/
theorem integral_mul_le_entropy_add_log [IsProbabilityMeasure P] {q G : α → ℝ}
    (hq0 : ∀ᵐ x ∂P, 0 ≤ q x) (hqi : Integrable q P) (hmass : ∫ x, q x ∂P = 1)
    (hqlog : Integrable (fun x => q x * Real.log (q x)) P)
    (hqG : Integrable (fun x => q x * G x) P)
    (hexp : Integrable (fun x => Real.exp (G x)) P) :
    ((∫ x, q x * G x ∂P : ℝ) : EReal) ≤
      entropy P q + ((Real.log (∫ x, Real.exp (G x) ∂P) : ℝ) : EReal) := by
  let Z := ∫ x, Real.exp (G x) ∂P
  have hZ : 0 < Z := integral_exp_pos hexp
  have hqZ : Integrable (fun x => q x * Real.log Z) P := hqi.mul_const _
  have hEZ : Integrable (fun x => Real.exp (G x) / Z) P := hexp.div_const _
  have hr : Integrable (fun x => q x * Real.log (q x) + q x * Real.log Z +
      Real.exp (G x) / Z - q x) P := ((hqlog.add hqZ).add hEZ).sub hqi
  have hi := integral_mono_ae hqG hr (hq0.mono fun x hx => density_exp_pointwise hx hZ)
  have hA : Integrable (fun x => q x * Real.log (q x) + q x * Real.log Z) P := hqlog.add hqZ
  have hB : Integrable (fun x => q x * Real.log (q x) + q x * Real.log Z + Real.exp (G x) / Z) P := hA.add hEZ
  have he : (∫ x, q x * Real.log (q x) + q x * Real.log Z + Real.exp (G x) / Z - q x ∂P) =
      (∫ x, q x * Real.log (q x) ∂P) + Real.log Z := by
    rw [integral_sub hB hqi,
      integral_add hA hEZ, integral_add hqlog hqZ,
      integral_mul_const, integral_div, hmass]
    change _ + 1 * Real.log Z + Z / Z - 1 = _
    rw [div_self hZ.ne']
    ring
  rw [he] at hi
  rw [entropy_eq_integral hq0 hqlog, hmass, Real.log_one, mul_zero, sub_zero, ← EReal.coe_add]
  exact_mod_cast hi

/-- A finite positive exponential moment controls both tails when the observable
is bounded below. This is the precise integrability mechanism used by the source. -/
theorem integrable_of_lower_bound_exp [IsFiniteMeasure P] {G : α → ℝ}
    (hG : Measurable G) {B : ℝ} (hlo : ∀ᵐ x ∂P, B ≤ G x)
    (hexp : Integrable (fun x => Real.exp (G x)) P) : Integrable G P := by
  apply (hexp.add (integrable_const |B|)).mono' hG.aestronglyMeasurable
  filter_upwards [hlo] with x hx
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hB := neg_abs_le B
    have he := (Real.exp_pos (G x)).le
    dsimp only [Pi.add_apply]
    linarith
  · have he := Real.add_one_le_exp (G x)
    dsimp only [Pi.add_apply]
    linarith [abs_nonneg B]

theorem integrable_bounded_density_mul [IsFiniteMeasure P] {q G : α → ℝ}
    (hq : Measurable q) (hG : Measurable G) {K : ℝ}
    (hb : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ K) (hGi : Integrable G P) :
    Integrable (fun x => q x * G x) P := by
  have hnorm : ∀ᵐ x ∂P, ‖q x * G x‖ ≤ |K| * ‖G x‖ := by
    filter_upwards [hb] with x hx
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (show |q x| ≤ |K| by
      rw [abs_of_nonneg hx.1]
      exact hx.2.trans (le_abs_self K)) (abs_nonneg _)
  exact (hGi.norm.const_mul |K|).mono' (hq.mul hG).aestronglyMeasurable hnorm

/-- The actual density law, with AE nonnegativity, gives the integral conversion
and genuine integrability equivalence; no representative change is imposed. -/
theorem integrable_density_iff {q G : α → ℝ}
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hq : Measurable q) (hq0 : ∀ᵐ x ∂P, 0 ≤ q x) :
    Integrable G Q ↔ Integrable (fun x => q x * G x) P := by
  rw [hQ, integrable_withDensity_iff_integrable_smul' hq.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [hq0] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

/-- Source bounded tilts: finite entropy and G-integrability are conclusions.
The inequality uses the existing extended entropy of the actual probability density. -/
theorem bounded_tilt_variational [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {q G : α → ℝ} (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hq : Measurable q) {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ K)
    (hG : Measurable G) {B : ℝ} (hlo : ∀ᵐ x ∂P, B ≤ G x)
    (hexp : Integrable (fun x => Real.exp (G x)) P) :
    Integrable G Q ∧ entropy P q ≠ ⊤ ∧ entropy P q ≠ ⊥ ∧
      ((∫ x, G x ∂Q : ℝ) : EReal) ≤
        entropy P q + ((Real.log (∫ x, Real.exp (G x) ∂P) : ℝ) : EReal) := by
  have hq0 := hb.mono fun _ hx => hx.1
  obtain ⟨hqi, hqlog⟩ := bounded_density_integrable hq hb
  have hmass := DensityMoments.integral_density_one hQ hq hq0
  have hGi := integrable_of_lower_bound_exp hG hlo hexp
  have hqGi := integrable_bounded_density_mul hq hG hb hGi
  have hfinite := entropy_eq_integral hq0 hqlog
  refine ⟨(integrable_density_iff hQ hq hq0).mpr hqGi, ?_, ?_, ?_⟩
  · rw [hfinite]
    exact EReal.coe_ne_top _
  · rw [hfinite]
    exact EReal.coe_ne_bot _
  · rw [DensityMoments.integral_density hQ hq hq0]
    exact integral_mul_le_entropy_add_log hq0 hqi hmass hqlog hqGi hexp

/-- Identification with the source definition H(Q|P)=integral(log q,dQ).
Zeros of q cause no missing logarithmic integrability premise. -/
theorem bounded_tilt_entropy_eq [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {q : α → ℝ} (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hq : Measurable q) {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ K) :
    Integrable (fun x => Real.log (q x)) Q ∧
      entropy P q = ((∫ x, Real.log (q x) ∂Q : ℝ) : EReal) := by
  have hq0 := hb.mono fun _ hx => hx.1
  have hqlog := (bounded_density_integrable hq hb).2
  have hmass := DensityMoments.integral_density_one hQ hq hq0
  refine ⟨(integrable_density_iff hQ hq hq0).mpr hqlog, ?_⟩
  rw [DensityMoments.integral_density hQ hq hq0, entropy_eq_integral hq0 hqlog,
    hmass, Real.log_one, mul_zero, sub_zero]

/-- The literal finite source inequality for a bounded tilt and a lower-bounded
observable with finite positive exponential moment. -/
theorem bounded_tilt_relativeEntropy [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {q G : α → ℝ} (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hq : Measurable q) {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ K)
    (hG : Measurable G) {B : ℝ} (hlo : ∀ᵐ x ∂P, B ≤ G x)
    (hexp : Integrable (fun x => Real.exp (G x)) P) :
    Integrable G Q ∧ Integrable (fun x => Real.log (q x)) Q ∧
      (∫ x, G x ∂Q) ≤ (∫ x, Real.log (q x) ∂Q) + Real.log (∫ x, Real.exp (G x) ∂P) := by
  have hv := bounded_tilt_variational hQ hq hb hG hlo hexp
  have he := bounded_tilt_entropy_eq hQ hq hb
  refine ⟨hv.1, he.1, ?_⟩
  have hh := hv.2.2.2
  rw [he.2, ← EReal.coe_add] at hh
  exact_mod_cast hh

end PeriodicAttractiveLogGas.RelativeEntropyVariational
