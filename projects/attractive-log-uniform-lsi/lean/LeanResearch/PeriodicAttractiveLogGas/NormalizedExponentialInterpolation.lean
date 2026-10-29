import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! Source Lemma `lem:exponential-interpolation`, lines 615–632.
The reference measure is explicitly nonzero when normalized probabilities
are asserted. The manuscript's finite-measure quantification needs this
qualification. Real representatives u,w are explicitly AE measurable.

All helpers have public namespace-visible names. Development evidence and
the distinct protected-acceptance status are recorded outside this source.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace PeriodicAttractiveLogGas.NormalizedExponentialInterpolation

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An actual L1 element when integrable, extended by zero elsewhere.
All uses on the interpolation interval separately prove integrability. -/
def liftL1 (μ : Measure α) (f : α → ℝ) : α →₁[μ] ℝ := by
  classical
  exact if h : Integrable f μ then h.toL1 f else 0

theorem liftL1_of_integrable {f : α → ℝ} (hf : Integrable f μ) :
    liftL1 μ f = hf.toL1 f := by
  classical
  simp only [liftL1, dite_eq_left hf]

theorem coe_liftL1 {f : α → ℝ} (hf : Integrable f μ) : liftL1 μ f =ᵐ[μ] f := by
  rw [liftL1_of_integrable hf]
  exact hf.coeFn_toL1

theorem liftL1_sub {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    liftL1 μ (fun x ↦ f x - g x) = liftL1 μ f - liftL1 μ g := by
  change liftL1 μ (f - g) = liftL1 μ f - liftL1 μ g
  rw [liftL1_of_integrable (hf.sub hg), liftL1_of_integrable hf, liftL1_of_integrable hg]
  simpa only using! Integrable.toL1_sub f g hf hg

theorem liftL1_add {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    liftL1 μ (fun x ↦ f x + g x) = liftL1 μ f + liftL1 μ g := by
  change liftL1 μ (f + g) = liftL1 μ f + liftL1 μ g
  rw [liftL1_of_integrable (hf.add hg), liftL1_of_integrable hf, liftL1_of_integrable hg]
  simpa only using! Integrable.toL1_add f g hf hg

theorem liftL1_smul {f : α → ℝ} (hf : Integrable f μ) (c : ℝ) :
    liftL1 μ (fun x ↦ c * f x) = c • liftL1 μ f := by
  rw [liftL1_of_integrable (hf.const_mul c), liftL1_of_integrable hf]
  exact Integrable.toL1_smul f hf c

theorem norm_liftL1 {f : α → ℝ} (hf : Integrable f μ) :
    ‖liftL1 μ f‖ = ∫ x, |f x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  exact (coe_liftL1 hf).mono fun x hx ↦ by
    change ‖(liftL1 μ f : α → ℝ) x‖ = |f x|
    rw [hx, Real.norm_eq_abs]

theorem integralCLM_liftL1 (f : α → ℝ) :
    L1.integralCLM (liftL1 μ f) = ∫ x, f x ∂μ := by
  classical
  by_cases hf : Integrable f μ
  · rw [liftL1_of_integrable hf, ← L1.integral_eq, ← integral_eq f hf]
  · simp only [liftL1, dite_eq_right hf, map_zero, integral_undef hf]

/-- The dominated difference-quotient argument in the actual Banach L1
space. The hypotheses are pointwise derivative and integrable domination
data; L1 differentiability is the conclusion. -/
theorem hasDerivWithinAt_liftL1_of_dominated
    {S : Set ℝ} {t : ℝ} (ht : t ∈ S) {F : ℝ → α → ℝ} {D B : α → ℝ}
    (hF : ∀ s ∈ S, Integrable (F s) μ) (hD : Integrable D μ) (hB : Integrable B μ)
    (hB0 : ∀ᵐ x ∂μ, 0 ≤ B x)
    (hLip : ∀ᵐ x ∂μ, ∀ s ∈ S, |F s x - F t x| ≤ B x * |s - t|)
    (hDbound : ∀ᵐ x ∂μ, |D x| ≤ B x)
    (hDiff : ∀ᵐ x ∂μ, HasDerivWithinAt (fun s ↦ F s x) (D x) S t) :
    HasDerivWithinAt (fun s ↦ liftL1 μ (F s)) (liftL1 μ D) S t := by
  let R : ℝ → α → ℝ := fun s x ↦ ‖s - t‖⁻¹ * ‖F s x - F t x - (s - t) * D x‖
  have hRm : ∀ᶠ s in 𝓝[S] t, AEStronglyMeasurable (R s) μ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (((hF s hs).aestronglyMeasurable.sub (hF t ht).aestronglyMeasurable).sub
      (hD.aestronglyMeasurable.const_mul (s - t))).norm.const_mul _
  have hRb : ∀ᶠ s in 𝓝[S] t, ∀ᵐ x ∂μ, ‖R s x‖ ≤ 2 * B x := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [hB0, hLip, hDbound] with x hB0x hLx hDx
    have hr : |F s x - F t x - (s - t) * D x| ≤ 2 * B x * |s - t| := by
      calc
        _ ≤ |F s x - F t x| + |(s - t) * D x| := abs_sub _ _
        _ ≤ B x * |s - t| + |s - t| * B x := by
          rw [abs_mul]
          exact add_le_add (hLx s hs) (mul_le_mul_of_nonneg_left hDx (abs_nonneg _))
        _ = _ := by ring
    by_cases hst : s = t
    · subst s
      simp only [R, sub_self, norm_zero, inv_zero, zero_mul, norm_zero]
      positivity
    · have hab : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
      change ‖‖s - t‖⁻¹ * ‖F s x - F t x - (s - t) * D x‖‖ ≤ 2 * B x
      rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)),
        Real.norm_eq_abs, Real.norm_eq_abs]
      calc
        _ ≤ |s - t|⁻¹ * (2 * B x * |s - t|) := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hab.le)
        _ = _ := by field_simp [ne_of_gt hab]
  have hRt : ∀ᵐ x ∂μ, Tendsto (fun s ↦ R s x) (𝓝[S] t) (𝓝 0) :=
    hDiff.mono fun x hx ↦ by simpa only [R, smul_eq_mul] using hasDerivWithinAt_iff_tendsto.mp hx
  have hlim := tendsto_integral_filter_of_dominated_convergence (fun x ↦ 2 * B x)
    hRm hRb (hB.const_mul 2) hRt
  apply hasDerivWithinAt_iff_tendsto.mpr
  apply (show Tendsto (fun s ↦ ∫ x, R s x ∂μ) (𝓝[S] t) (𝓝 0) by simpa using hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hi : Integrable (fun x ↦ F s x - F t x - (s - t) * D x) μ :=
    ((hF s hs).sub (hF t ht)).sub (hD.const_mul (s - t))
  have he : liftL1 μ (F s) - liftL1 μ (F t) - (s - t) • liftL1 μ D =
      liftL1 μ (fun x ↦ F s x - F t x - (s - t) * D x) := by
    have hsplit : liftL1 μ (fun x ↦ F s x - F t x - (s - t) * D x) =
        liftL1 μ (fun x ↦ F s x - F t x) - liftL1 μ (fun x ↦ (s - t) * D x) := by
      simpa only [Pi.sub_apply] using!
        liftL1_sub ((hF s hs).sub (hF t ht)) (hD.const_mul (s - t))
    rw [hsplit, liftL1_sub (hF s hs) (hF t ht), liftL1_smul hD]
  change (∫ x, R s x ∂μ) =
    ‖s - t‖⁻¹ * ‖liftL1 μ (F s) - liftL1 μ (F t) - (s - t) • liftL1 μ D‖
  rw [he, norm_liftL1 hi]
  simp only [R, Real.norm_eq_abs]
  exact integral_const_mul _ _

def weight (u w : α → ℝ) (t : ℝ) (x : α) : ℝ := Real.exp (u x + t * w x)
def endpointBound (u w : α → ℝ) (x : α) : ℝ := Real.exp (u x) + Real.exp (u x + w x)
def derivativeBound (u w : α → ℝ) (x : α) : ℝ := endpointBound u w x * |w x|
def majorant (u w : α → ℝ) (x : α) : ℝ := endpointBound u w x * (1 + |w x|)
def weightSlope (u w : α → ℝ) (t : ℝ) (x : α) : ℝ := weight u w t x * w x

structure Admissible (μ : Measure α) (u w : α → ℝ) : Prop where
  u_measurable : AEMeasurable u μ
  w_measurable : AEMeasurable w μ
  majorant_integrable : Integrable (majorant u w) μ

omit [MeasurableSpace α] in
theorem weight_pos (u w : α → ℝ) (t : ℝ) (x : α) : 0 < weight u w t x := Real.exp_pos _
omit [MeasurableSpace α] in
theorem endpointBound_nonneg (u w : α → ℝ) (x : α) : 0 ≤ endpointBound u w x :=
  add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
omit [MeasurableSpace α] in
theorem derivativeBound_nonneg (u w : α → ℝ) (x : α) : 0 ≤ derivativeBound u w x :=
  mul_nonneg (endpointBound_nonneg _ _ _) (abs_nonneg _)

omit [MeasurableSpace α] in
theorem weight_le_endpointBound (u w : α → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : α) :
    weight u w t x ≤ endpointBound u w x := by
  change Real.exp (u x + t * w x) ≤ Real.exp (u x) + Real.exp (u x + w x)
  by_cases hw : 0 ≤ w x
  · have htw : t * w x ≤ w x := by nlinarith [ht.2]
    calc
      _ ≤ Real.exp (u x + w x) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by linarith [Real.exp_pos (u x)]
  · have htw : t * w x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_not_ge hw)
    calc
      _ ≤ Real.exp (u x) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by linarith [Real.exp_pos (u x + w x)]

omit [MeasurableSpace α] in
theorem abs_weightSlope_le (u w : α → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : α) :
    |weightSlope u w t x| ≤ derivativeBound u w x := by
  rw [weightSlope, abs_mul, abs_of_pos (weight_pos _ _ _ _)]
  exact mul_le_mul_of_nonneg_right (weight_le_endpointBound u w ht x) (abs_nonneg _)

omit [MeasurableSpace α] in
theorem hasDerivAt_weight (u w : α → ℝ) (t : ℝ) (x : α) :
    HasDerivAt (fun s ↦ weight u w s x) (weightSlope u w t x) t := by
  simpa only [weight, weightSlope, one_mul, id_eq] using!
    (((hasDerivAt_id t).mul_const (w x)).const_add (u x)).exp

omit [MeasurableSpace α] in
theorem weight_lipschitzOn (u w : α → ℝ) (x : α) :
    LipschitzOnWith ⟨derivativeBound u w x, derivativeBound_nonneg u w x⟩
      (fun t ↦ weight u w t x) (Icc (0 : ℝ) 1) := by
  apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht ↦ (hasDerivAt_weight u w t x).hasDerivWithinAt)
  intro t ht
  apply NNReal.coe_le_coe.mp
  change |weightSlope u w t x| ≤ derivativeBound u w x
  exact abs_weightSlope_le u w ht x

variable {u w : α → ℝ}

theorem Admissible.aemeasurable_weight (h : Admissible μ u w) (t : ℝ) :
    AEMeasurable (weight u w t) μ :=
  (h.u_measurable.add (h.w_measurable.const_mul t)).exp

theorem Admissible.aemeasurable_weightSlope (h : Admissible μ u w) (t : ℝ) :
    AEMeasurable (weightSlope u w t) μ := (h.aemeasurable_weight t).mul h.w_measurable

theorem Admissible.integrable_endpointBound (h : Admissible μ u w) :
    Integrable (endpointBound u w) μ := by
  apply h.majorant_integrable.mono'
    (h.u_measurable.exp.add (h.u_measurable.add h.w_measurable).exp).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    change ‖endpointBound u w x‖ ≤ majorant u w x
    rw [Real.norm_of_nonneg (endpointBound_nonneg u w x)]
    unfold majorant
    nlinarith [endpointBound_nonneg u w x, abs_nonneg (w x)]

theorem Admissible.integrable_derivativeBound (h : Admissible μ u w) :
    Integrable (derivativeBound u w) μ := by
  apply h.majorant_integrable.mono'
    ((h.u_measurable.exp.add (h.u_measurable.add h.w_measurable).exp).mul
      (continuous_abs.measurable.comp_aemeasurable h.w_measurable)).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    change ‖derivativeBound u w x‖ ≤ majorant u w x
    rw [Real.norm_of_nonneg (derivativeBound_nonneg u w x)]
    unfold derivativeBound majorant
    nlinarith [endpointBound_nonneg u w x]

theorem Admissible.integrable_weight (h : Admissible μ u w) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (weight u w t) μ := by
  apply h.integrable_endpointBound.mono' (h.aemeasurable_weight t).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    rw [Real.norm_of_nonneg (weight_pos u w t x).le]
    exact weight_le_endpointBound u w ht x

theorem Admissible.integrable_weightSlope (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : Integrable (weightSlope u w t) μ :=
  h.integrable_derivativeBound.mono' (h.aemeasurable_weightSlope t).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ abs_weightSlope_le u w ht x)

def weightL1 (μ : Measure α) (u w : α → ℝ) (t : ℝ) : α →₁[μ] ℝ := liftL1 μ (weight u w t)
def normalizer (μ : Measure α) (u w : α → ℝ) (t : ℝ) : ℝ := ∫ x, weight u w t x ∂μ

theorem Admissible.hasDerivWithinAt_weightL1 (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (weightL1 μ u w) (liftL1 μ (weightSlope u w t)) (Icc (0 : ℝ) 1) t := by
  apply hasDerivWithinAt_liftL1_of_dominated ht
    (fun s hs ↦ h.integrable_weight hs) (h.integrable_weightSlope ht) h.integrable_derivativeBound
    (Eventually.of_forall fun x ↦ derivativeBound_nonneg u w x)
  · exact Eventually.of_forall fun x s hs ↦ by
      have hl := (weight_lipschitzOn u w x).dist_le_mul s hs t ht
      change |weight u w s x - weight u w t x| ≤ derivativeBound u w x * |s - t| at hl
      exact hl
  · exact Eventually.of_forall fun x ↦ abs_weightSlope_le u w ht x
  · exact Eventually.of_forall fun x ↦ (hasDerivAt_weight u w t x).hasDerivWithinAt

theorem normalizer_eq_integralCLM (μ : Measure α) (u w : α → ℝ) (t : ℝ) :
    normalizer μ u w t = L1.integralCLM (weightL1 μ u w t) :=
  (integralCLM_liftL1 (weight u w t)).symm

theorem Admissible.hasDerivWithinAt_normalizer (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (normalizer μ u w) (∫ x, weightSlope u w t x ∂μ) (Icc (0 : ℝ) 1) t := by
  have hd := (L1.integralCLM (α := α) (E := ℝ) (μ := μ)).hasFDerivAt.comp_hasDerivWithinAt t
    (h.hasDerivWithinAt_weightL1 ht)
  simpa only [Function.comp_def, ← normalizer_eq_integralCLM, integralCLM_liftL1] using hd

theorem Admissible.continuousOn_normalizer (h : Admissible μ u w) :
    ContinuousOn (normalizer μ u w) (Icc (0 : ℝ) 1) :=
  fun _t ht ↦ (h.hasDerivWithinAt_normalizer ht).continuousWithinAt

theorem Admissible.normalizer_pos [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 < normalizer μ u w t :=
  integral_exp_pos (h.integrable_weight ht)

theorem Admissible.lintegral_weight_eq (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, ENNReal.ofReal (weight u w t x) ∂μ) = ENNReal.ofReal (normalizer μ u w t) :=
  (ofReal_integral_eq_lintegral_ofReal (h.integrable_weight ht)
    (Eventually.of_forall fun x ↦ (weight_pos u w t x).le)).symm

theorem Admissible.lintegral_weight_lt_top (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, ENNReal.ofReal (weight u w t x) ∂μ) < ∞ := by
  rw [h.lintegral_weight_eq ht]
  exact ENNReal.ofReal_lt_top

theorem Admissible.normalizer_uniform_lower [NeZero μ] (h : Admissible μ u w) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc (0 : ℝ) 1, m ≤ normalizer μ u w t := by
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) h.continuousOn_normalizer
  exact ⟨normalizer μ u w t, h.normalizer_pos ht, hmin⟩

def density (μ : Measure α) (u w : α → ℝ) (t : ℝ) (x : α) : ℝ :=
  (normalizer μ u w t)⁻¹ * weight u w t x

def law (μ : Measure α) (u w : α → ℝ) (t : ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (density μ u w t x))

def densityL1 (μ : Measure α) (u w : α → ℝ) (t : ℝ) : α →₁[μ] ℝ :=
  (normalizer μ u w t)⁻¹ • weightL1 μ u w t

def meanW (μ : Measure α) (u w : α → ℝ) (t : ℝ) : ℝ :=
  ∫ x, w x ∂law μ u w t

def meanAbs (μ : Measure α) (u w : α → ℝ) (t : ℝ) : ℝ :=
  ∫ x, |w x| ∂law μ u w t

def densitySlope (μ : Measure α) (u w : α → ℝ) (t : ℝ) (x : α) : ℝ :=
  density μ u w t x * (w x - meanW μ u w t)

theorem Admissible.aemeasurable_density (h : Admissible μ u w) (t : ℝ) :
    AEMeasurable (density μ u w t) μ :=
  (h.aemeasurable_weight t).const_mul _

theorem Admissible.integrable_density (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : Integrable (density μ u w t) μ :=
  (h.integrable_weight ht).const_mul _

theorem Admissible.density_pos [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : α) : 0 < density μ u w t x :=
  mul_pos (inv_pos.mpr (h.normalizer_pos ht)) (weight_pos u w t x)

theorem Admissible.integral_density [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (∫ x, density μ u w t x ∂μ) = 1 := by
  change (∫ x, (normalizer μ u w t)⁻¹ * weight u w t x ∂μ) = 1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (h.normalizer_pos ht).ne'

theorem Admissible.law_probability [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : IsProbabilityMeasure (law μ u w t) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (h.integrable_density ht)
      (Eventually.of_forall fun x ↦ (h.density_pos ht x).le),
    h.integral_density ht, ENNReal.ofReal_one]

theorem Admissible.densityL1_eq [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : densityL1 μ u w t = liftL1 μ (density μ u w t) :=
  (liftL1_smul (h.integrable_weight ht) _).symm

theorem Admissible.coe_densityL1 [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : densityL1 μ u w t =ᵐ[μ] density μ u w t := by
  rw [h.densityL1_eq ht]
  exact coe_liftL1 (h.integrable_density ht)

theorem Admissible.integral_law [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (f : α → ℝ) :
    (∫ x, f x ∂law μ u w t) = ∫ x, density μ u w t x * f x ∂μ := by
  rw [law, integral_withDensity_eq_integral_toReal_smul₀
    (h.aemeasurable_density t).ennreal_ofReal (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    change (ENNReal.ofReal (density μ u w t x)).toReal * f x = density μ u w t x * f x
    rw [ENNReal.toReal_ofReal (h.density_pos ht x).le]

theorem Admissible.integrable_law_iff [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (f : α → ℝ) :
    Integrable f (law μ u w t) ↔ Integrable (fun x ↦ density μ u w t x * f x) μ := by
  rw [law, integrable_withDensity_iff_integrable_smul₀'
    (h.aemeasurable_density t).ennreal_ofReal (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have he : (fun x ↦ (ENNReal.ofReal (density μ u w t x)).toReal • f x) =
      (fun x ↦ density μ u w t x * f x) := by
    funext x
    change (ENNReal.ofReal (density μ u w t x)).toReal * f x = density μ u w t x * f x
    rw [ENNReal.toReal_ofReal (h.density_pos ht x).le]
  rw [he]

theorem Admissible.integrable_density_mul_w (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x ↦ density μ u w t x * w x) μ := by
  simpa only [density, weightSlope, mul_assoc] using
    (h.integrable_weightSlope ht).const_mul ((normalizer μ u w t)⁻¹)

theorem Admissible.integrable_weight_mul_abs (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x ↦ weight u w t x * |w x|) μ := by
  convert (h.integrable_weightSlope ht).abs using 1
  funext x
  rw [weightSlope, abs_mul, abs_of_pos (weight_pos u w t x)]

theorem Admissible.integrable_w_law [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : Integrable w (law μ u w t) :=
  (h.integrable_law_iff ht w).mpr (h.integrable_density_mul_w ht)

theorem Admissible.meanW_eq [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    meanW μ u w t = (normalizer μ u w t)⁻¹ * ∫ x, weightSlope u w t x ∂μ := by
  rw [meanW, h.integral_law ht]
  simp only [density, weightSlope, mul_assoc, integral_const_mul]

theorem Admissible.meanAbs_eq [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    meanAbs μ u w t = (normalizer μ u w t)⁻¹ * ∫ x, weight u w t x * |w x| ∂μ := by
  rw [meanAbs, h.integral_law ht]
  simp only [density, mul_assoc, integral_const_mul]

theorem meanAbs_nonneg (μ : Measure α) (u w : α → ℝ) (t : ℝ) :
    0 ≤ meanAbs μ u w t := integral_nonneg fun x ↦ abs_nonneg (w x)

theorem abs_meanW_le_meanAbs (μ : Measure α) (u w : α → ℝ) (t : ℝ) :
    |meanW μ u w t| ≤ meanAbs μ u w t := by
  simpa only [meanW, meanAbs, Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (w) :
      ‖∫ x, w x ∂law μ u w t‖ ≤ ∫ x, ‖w x‖ ∂law μ u w t)

theorem Admissible.integrable_densitySlope (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : Integrable (densitySlope μ u w t) μ := by
  unfold densitySlope
  simp only [mul_sub]
  exact (h.integrable_density_mul_w ht).sub
    ((h.integrable_density ht).mul_const (meanW μ u w t))

/-- Actual normalized Banach-L1 derivative, including the one-sided
endpoint derivatives on the closed interval. -/
theorem Admissible.hasDerivWithinAt_densityL1 [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (densityL1 μ u w) (liftL1 μ (densitySlope μ u w t))
      (Icc (0 : ℝ) 1) t := by
  have hz := (h.hasDerivWithinAt_normalizer ht).inv (h.normalizer_pos ht).ne'
  have hd := hz.smul (h.hasDerivWithinAt_weightL1 ht)
  simp only [Pi.inv_apply] at hd
  apply hd.congr_deriv
  rw [← liftL1_smul (h.integrable_weightSlope ht), weightL1,
    ← liftL1_smul (h.integrable_weight ht),
    ← liftL1_add ((h.integrable_weightSlope ht).const_mul _)
      ((h.integrable_weight ht).const_mul _)]
  congr 1
  funext x
  change (normalizer μ u w t)⁻¹ * weightSlope u w t x +
    (-(∫ y, weightSlope u w t y ∂μ) / (normalizer μ u w t) ^ 2) * weight u w t x =
      densitySlope μ u w t x
  rw [densitySlope, density, h.meanW_eq ht, weightSlope]
  field_simp [(h.normalizer_pos ht).ne']
  ring

theorem Admissible.continuousOn_densityL1 [NeZero μ] (h : Admissible μ u w) :
    ContinuousOn (densityL1 μ u w) (Icc (0 : ℝ) 1) :=
  fun _t ht ↦ (h.hasDerivWithinAt_densityL1 ht).continuousWithinAt

theorem Admissible.half_norm_densitySlope [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 / 2 : ℝ) * ‖liftL1 μ (densitySlope μ u w t)‖ ≤ meanAbs μ u w t := by
  have hpoint : ∀ x, |densitySlope μ u w t x| ≤
      density μ u w t x * |w x| + density μ u w t x * |meanW μ u w t| := by
    intro x
    rw [densitySlope, abs_mul, abs_of_pos (h.density_pos ht x), ← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (h.density_pos ht x).le
  have habs : Integrable (fun x ↦ density μ u w t x * |w x|) μ := by
    simpa only [density, mul_assoc] using
      (h.integrable_weight_mul_abs ht).const_mul ((normalizer μ u w t)⁻¹)
  have hi := integral_mono (h.integrable_densitySlope ht).abs
    (habs.add ((h.integrable_density ht).mul_const |meanW μ u w t|)) hpoint
  change (∫ x, |densitySlope μ u w t x| ∂μ) ≤
    ∫ x, density μ u w t x * |w x| + density μ u w t x * |meanW μ u w t| ∂μ at hi
  rw [integral_add habs ((h.integrable_density ht).mul_const _),
    integral_mul_const, h.integral_density ht, one_mul,
    ← h.integral_law ht (fun x ↦ |w x|)] at hi
  rw [norm_liftL1 (h.integrable_densitySlope ht)]
  change _ ≤ meanAbs μ u w t
  have hm := abs_meanW_le_meanAbs μ u w t
  change _ ≤ meanAbs μ u w t + |meanW μ u w t| at hi
  linarith

theorem Admissible.continuousOn_abs_numerator (h : Admissible μ u w) :
    ContinuousOn (fun t ↦ ∫ x, weight u w t x * |w x| ∂μ) (Icc (0 : ℝ) 1) := by
  intro t _ht
  apply tendsto_integral_filter_of_dominated_convergence (derivativeBound u w)
  · exact Eventually.of_forall fun s ↦
      ((h.aemeasurable_weight s).mul
        (continuous_abs.measurable.comp_aemeasurable h.w_measurable)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact Eventually.of_forall fun x ↦ by
      change ‖weight u w s x * |w x|‖ ≤ derivativeBound u w x
      rw [Real.norm_of_nonneg (mul_nonneg (weight_pos u w s x).le (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_right (weight_le_endpointBound u w hs x) (abs_nonneg _)
  · exact h.integrable_derivativeBound
  · exact Eventually.of_forall fun x ↦
      ((hasDerivAt_weight u w t x).continuousAt.continuousWithinAt.mul_const |w x|)

theorem Admissible.continuousOn_meanAbs [NeZero μ] (h : Admissible μ u w) :
    ContinuousOn (meanAbs μ u w) (Icc (0 : ℝ) 1) := by
  apply ((h.continuousOn_normalizer.inv₀ fun t ht ↦ (h.normalizer_pos ht).ne').mul
    h.continuousOn_abs_numerator).congr
  exact fun t ht ↦ h.meanAbs_eq ht

theorem Admissible.intervalIntegrable_meanAbs [NeZero μ] (h : Admissible μ u w) :
    IntervalIntegrable (meanAbs μ u w) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) h.continuousOn_meanAbs

/-- The actual real supremum of the first absolute moments on the closed
interpolation interval. Its boundedness is proved below, not assumed. -/
def meanAbsSup (μ : Measure α) (u w : α → ℝ) : ℝ :=
  sSup (meanAbs μ u w '' Icc (0 : ℝ) 1)

theorem Admissible.bddAbove_meanAbs [NeZero μ] (h : Admissible μ u w) :
    BddAbove (meanAbs μ u w '' Icc (0 : ℝ) 1) :=
  isCompact_Icc.bddAbove_image h.continuousOn_meanAbs

theorem Admissible.meanAbs_le_sup [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : meanAbs μ u w t ≤ meanAbsSup μ u w :=
  le_csSup h.bddAbove_meanAbs (mem_image_of_mem _ ht)

theorem Admissible.meanAbsSup_nonneg [NeZero μ] (h : Admissible μ u w) :
    0 ≤ meanAbsSup μ u w :=
  (meanAbs_nonneg μ u w 0).trans (h.meanAbs_le_sup ⟨le_rfl, by norm_num⟩)

theorem Admissible.lipschitzOn_densityL1 [NeZero μ] (h : Admissible μ u w) :
    LipschitzOnWith ⟨2 * meanAbsSup μ u w, mul_nonneg (by norm_num) h.meanAbsSup_nonneg⟩
      (densityL1 μ u w) (Icc (0 : ℝ) 1) := by
  apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht ↦ h.hasDerivWithinAt_densityL1 ht)
  intro t ht
  have hs := h.half_norm_densitySlope ht
  have hm := h.meanAbs_le_sup ht
  change ‖liftL1 μ (densitySlope μ u w t)‖₊ ≤ _
  apply NNReal.coe_le_coe.mp
  change ‖liftL1 μ (densitySlope μ u w t)‖ ≤ 2 * meanAbsSup μ u w
  linarith

theorem Admissible.absolutelyContinuous_densityL1 [NeZero μ] (h : Admissible μ u w) :
    AbsolutelyContinuousOnInterval (densityL1 μ u w) 0 1 := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h.lipschitzOn_densityL1

theorem Admissible.hasDerivAt_densityL1 [NeZero μ] (h : Admissible μ u w) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (densityL1 μ u w) (liftL1 μ (densitySlope μ u w t)) t :=
  (h.hasDerivWithinAt_densityL1 ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem Admissible.norm_densityL1_endpoints_le [NeZero μ] (h : Admissible μ u w) :
    ‖densityL1 μ u w 1 - densityL1 μ u w 0‖ ≤ ∫ t in (0 : ℝ)..1, 2 * meanAbs μ u w t := by
  apply _root_.norm_sub_le_integral_of_norm_deriv_le_of_le (by norm_num)
    h.continuousOn_densityL1
  · exact fun t ht ↦ (h.hasDerivAt_densityL1 ht).differentiableAt.differentiableWithinAt
  · exact Eventually.of_forall fun t ht ↦ by
      change ‖deriv (densityL1 μ u w) t‖ ≤ 2 * meanAbs μ u w t
      rw [(h.hasDerivAt_densityL1 ht).deriv]
      have hs := h.half_norm_densitySlope ⟨ht.1.le, ht.2.le⟩
      linarith
  · exact h.intervalIntegrable_meanAbs.const_mul 2

/-- Common-reference half-L1 convention for total variation. The next
results bound this literal integral, with actual probability laws above. -/
def halfL1Distance (μ : Measure α) (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x, |p x - q x| ∂μ

theorem Admissible.halfL1_endpoints_eq [NeZero μ] (h : Admissible μ u w) :
    halfL1Distance μ (density μ u w 1) (density μ u w 0) =
      (1 / 2 : ℝ) * ‖densityL1 μ u w 1 - densityL1 μ u w 0‖ := by
  have ht₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have ht₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  unfold halfL1Distance
  rw [h.densityL1_eq ht₁, h.densityL1_eq ht₀,
    ← liftL1_sub (h.integrable_density ht₁) (h.integrable_density ht₀)]
  have hi : Integrable (fun x ↦ density μ u w 1 x - density μ u w 0 x) μ :=
    (h.integrable_density ht₁).sub (h.integrable_density ht₀)
  rw [norm_liftL1 hi]

theorem Admissible.halfL1_endpoints_le_integral [NeZero μ] (h : Admissible μ u w) :
    halfL1Distance μ (density μ u w 1) (density μ u w 0) ≤
      ∫ t in (0 : ℝ)..1, meanAbs μ u w t := by
  rw [h.halfL1_endpoints_eq]
  have hd := h.norm_densityL1_endpoints_le
  rw [intervalIntegral.integral_const_mul] at hd
  linarith

theorem Admissible.integral_meanAbs_le_sup [NeZero μ] (h : Admissible μ u w) :
    (∫ t in (0 : ℝ)..1, meanAbs μ u w t) ≤ meanAbsSup μ u w := by
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    h.intervalIntegrable_meanAbs (intervalIntegrable_const (c := meanAbsSup μ u w))
    (fun t ht ↦ h.meanAbs_le_sup ht)
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hi

/-- Both estimates in source equation (TV-interpolation), in the literal
common-density half-L1 convention, and the complete actual L1 path data. -/
theorem Admissible.normalized_interpolation [NeZero μ] (h : Admissible μ u w) :
    (∀ t ∈ Icc (0 : ℝ) 1, IsProbabilityMeasure (law μ u w t)) ∧
    AbsolutelyContinuousOnInterval (densityL1 μ u w) 0 1 ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (densityL1 μ u w) (liftL1 μ (densitySlope μ u w t))
        (Icc (0 : ℝ) 1) t) ∧
    halfL1Distance μ (density μ u w 1) (density μ u w 0) ≤
      (∫ t in (0 : ℝ)..1, meanAbs μ u w t) ∧
    (∫ t in (0 : ℝ)..1, meanAbs μ u w t) ≤ meanAbsSup μ u w :=
  ⟨fun _ ht ↦ h.law_probability ht, h.absolutelyContinuous_densityL1,
    fun _ ht ↦ h.hasDerivWithinAt_densityL1 ht,
    h.halfL1_endpoints_le_integral, h.integral_meanAbs_le_sup⟩

/-- A zero-total-mass real integrand has at most half its L1 mass on
any measurable set. Both the set and its complement enter the proof. -/
theorem abs_setIntegral_le_half_of_integral_zero {f : α → ℝ}
    (hf : Integrable f μ) (hz : (∫ x, f x ∂μ) = 0)
    {s : Set α} (hs : MeasurableSet s) :
    |∫ x in s, f x ∂μ| ≤ (1 / 2 : ℝ) * ∫ x, |f x| ∂μ := by
  have hsplit := integral_add_compl hs hf
  rw [hz] at hsplit
  have hc : (∫ x in sᶜ, f x ∂μ) = -(∫ x in s, f x ∂μ) := by linarith
  have ha : |∫ x in s, f x ∂μ| ≤ ∫ x in s, |f x| ∂μ := abs_integral_le_integral_abs
  have hb : |∫ x in sᶜ, f x ∂μ| ≤ ∫ x in sᶜ, |f x| ∂μ := abs_integral_le_integral_abs
  rw [hc, abs_neg] at hb
  have hab := integral_add_compl hs hf.abs
  linarith

/-- A measurable representative of an AE measurable integrand supplies
a measurable positive set attaining the half-L1 mass. -/
theorem exists_set_abs_integral_eq_half {f : α → ℝ}
    (hf : Integrable f μ) (hz : (∫ x, f x ∂μ) = 0) :
    ∃ s : Set α, MeasurableSet s ∧
      |∫ x in s, f x ∂μ| = (1 / 2 : ℝ) * ∫ x, |f x| ∂μ := by
  let hm : AEMeasurable f μ := hf.aestronglyMeasurable.aemeasurable
  let s : Set α := {x | 0 ≤ hm.mk f x}
  have hs : MeasurableSet s := measurableSet_le measurable_const hm.measurable_mk
  have ha : (∫ x in s, |f x| ∂μ) = ∫ x in s, f x ∂μ := by
    apply integral_congr_ae
    change ∀ᵐ x ∂μ.restrict s, |f x| = f x
    rw [ae_restrict_iff' hs]
    filter_upwards [hm.ae_eq_mk] with x hx hxs
    change 0 ≤ hm.mk f x at hxs
    exact abs_of_nonneg (by simpa only [hx] using hxs)
  have hb : (∫ x in sᶜ, |f x| ∂μ) = -(∫ x in sᶜ, f x ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    change ∀ᵐ x ∂μ.restrict sᶜ, |f x| = -f x
    rw [ae_restrict_iff' hs.compl]
    filter_upwards [hm.ae_eq_mk] with x hx hxs
    change ¬ 0 ≤ hm.mk f x at hxs
    have hneg : hm.mk f x < 0 := lt_of_not_ge hxs
    exact abs_of_neg (by simpa only [hx] using hneg)
  have hz' := integral_add_compl hs hf
  rw [hz] at hz'
  have hab := integral_add_compl hs hf.abs
  rw [ha, hb] at hab
  have hnonneg : 0 ≤ ∫ x in s, f x ∂μ := by
    rw [← ha]
    exact integral_nonneg fun x ↦ abs_nonneg (f x)
  refine ⟨s, hs, ?_⟩
  rw [abs_of_nonneg hnonneg]
  linarith

def setTotalVariation (ν η : Measure α) : ℝ :=
  sSup ((fun s : Set α ↦ |(ν s).toReal - (η s).toReal|) '' {s | MeasurableSet s})

theorem setTotalVariation_comm (ν η : Measure α) :
    setTotalVariation ν η = setTotalVariation η ν := by
  unfold setTotalVariation
  have he : (fun s : Set α ↦ |(ν s).toReal - (η s).toReal|) =
      (fun s : Set α ↦ |(η s).toReal - (ν s).toReal|) :=
    funext fun s ↦ abs_sub_comm _ _
  rw [he]

theorem toReal_withDensity_apply {p : α → ℝ} (hp : Integrable p μ)
    (hp0 : ∀ x, 0 ≤ p x) {s : Set α} (hs : MeasurableSet s) :
    ((μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) s).toReal = ∫ x in s, p x ∂μ := by
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (Eventually.of_forall hp0),
    ENNReal.toReal_ofReal (integral_nonneg hp0)]

theorem withDensity_set_difference {p q : α → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    {s : Set α} (hs : MeasurableSet s) :
    |((μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) s).toReal -
        ((μ.withDensity (fun x ↦ ENNReal.ofReal (q x))) s).toReal| =
      |∫ x in s, p x - q x ∂μ| := by
  rw [toReal_withDensity_apply hp hp0 hs, toReal_withDensity_apply hq hq0 hs,
    integral_sub hp.integrableOn hq.integrableOn]

/-- Exact set-supremum / half-L1 bridge, including AE measurable
densities. No total-variation equivalence is taken as a premise. -/
theorem setTotalVariation_withDensity_eq_halfL1 {p q : α → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : (∫ x, p x ∂μ) = 1) (hq1 : (∫ x, q x ∂μ) = 1) :
    setTotalVariation (μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
      (μ.withDensity (fun x ↦ ENNReal.ofReal (q x))) = halfL1Distance μ p q := by
  have hz : (∫ x, p x - q x ∂μ) = 0 := by rw [integral_sub hp hq, hp1, hq1, sub_self]
  let V : Set ℝ := (fun s : Set α ↦
    |((μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) s).toReal -
      ((μ.withDensity (fun x ↦ ENNReal.ofReal (q x))) s).toReal|) '' {s | MeasurableSet s}
  have hbound : ∀ v ∈ V, v ≤ halfL1Distance μ p q := by
    rintro v ⟨s, hs, rfl⟩
    change |((μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) s).toReal -
      ((μ.withDensity (fun x ↦ ENNReal.ofReal (q x))) s).toReal| ≤ halfL1Distance μ p q
    rw [withDensity_set_difference hp hq hp0 hq0 hs]
    exact abs_setIntegral_le_half_of_integral_zero (hp.sub hq) hz hs
  have hbdd : BddAbove V := ⟨halfL1Distance μ p q, hbound⟩
  have hne : V.Nonempty := ⟨_, ∅, MeasurableSet.empty, rfl⟩
  change sSup V = halfL1Distance μ p q
  apply le_antisymm (csSup_le hne hbound)
  obtain ⟨s, hs, hatt⟩ := exists_set_abs_integral_eq_half (hp.sub hq) hz
  change |∫ x in s, p x - q x ∂μ| = halfL1Distance μ p q at hatt
  have hmem :
      |((μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) s).toReal -
        ((μ.withDensity (fun x ↦ ENNReal.ofReal (q x))) s).toReal| ∈ V :=
    mem_image_of_mem _ hs
  have hle := le_csSup hbdd hmem
  rw [withDensity_set_difference hp hq hp0 hq0 hs, hatt] at hle
  exact hle

theorem Admissible.setTV_endpoints_eq_halfL1 [NeZero μ] (h : Admissible μ u w) :
    setTotalVariation (law μ u w 1) (law μ u w 0) =
      halfL1Distance μ (density μ u w 1) (density μ u w 0) := by
  have ht₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have ht₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  exact setTotalVariation_withDensity_eq_halfL1 (h.integrable_density ht₁)
    (h.integrable_density ht₀) (fun x ↦ (h.density_pos ht₁ x).le)
    (fun x ↦ (h.density_pos ht₀ x).le) (h.integral_density ht₁) (h.integral_density ht₀)

theorem Admissible.setTV_interpolation [NeZero μ] (h : Admissible μ u w) :
    setTotalVariation (law μ u w 0) (law μ u w 1) ≤
      (∫ t in (0 : ℝ)..1, meanAbs μ u w t) ∧
    (∫ t in (0 : ℝ)..1, meanAbs μ u w t) ≤ meanAbsSup μ u w := by
  rw [setTotalVariation_comm (law μ u w 0) (law μ u w 1), h.setTV_endpoints_eq_halfL1]
  exact ⟨h.halfL1_endpoints_le_integral, h.integral_meanAbs_le_sup⟩

omit [MeasurableSpace α] in
theorem weight_shift (u w : α → ℝ) (a b t : ℝ) (x : α) :
    weight (fun x ↦ u x + a) (fun x ↦ w x + b) t x =
      Real.exp (a + t * b) * weight u w t x := by
  unfold weight
  rw [← Real.exp_add]
  congr 1
  ring

theorem normalizer_shift (μ : Measure α) (u w : α → ℝ) (a b t : ℝ) :
    normalizer μ (fun x ↦ u x + a) (fun x ↦ w x + b) t =
      Real.exp (a + t * b) * normalizer μ u w t := by
  simp only [normalizer, weight_shift, integral_const_mul]

/-- The actual normalized density is unchanged by either constant shift.
This identity even holds for the totalized definitions off the interval. -/
theorem density_shift (μ : Measure α) (u w : α → ℝ) (a b t : ℝ) (x : α) :
    density μ (fun x ↦ u x + a) (fun x ↦ w x + b) t x = density μ u w t x := by
  simp only [density, normalizer_shift, weight_shift]
  rw [mul_inv_rev, mul_assoc, ← mul_assoc (Real.exp (a + t * b))⁻¹,
    inv_mul_cancel₀ (Real.exp_ne_zero _), one_mul]

theorem law_shift (μ : Measure α) (u w : α → ℝ) (a b t : ℝ) :
    law μ (fun x ↦ u x + a) (fun x ↦ w x + b) t = law μ u w t := by
  simp only [law, density_shift]

theorem Admissible.shift (h : Admissible μ u w) (a b : ℝ) :
    Admissible μ (fun x ↦ u x + a) (fun x ↦ w x + b) := by
  refine ⟨h.u_measurable.add_const a, h.w_measurable.add_const b, ?_⟩
  let C : ℝ := (Real.exp a + Real.exp (a + b)) * (1 + |b|)
  have hmeas : AEMeasurable (majorant (fun x ↦ u x + a) (fun x ↦ w x + b)) μ := by
    exact (((h.u_measurable.add_const a).exp.add
      ((h.u_measurable.add_const a).add (h.w_measurable.add_const b)).exp).mul
      ((continuous_abs.measurable.comp_aemeasurable (h.w_measurable.add_const b)).const_add 1))
  apply (h.majorant_integrable.const_mul C).mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    let A : ℝ := Real.exp (u x)
    let B : ℝ := Real.exp (u x + w x)
    let E : ℝ := Real.exp a + Real.exp (a + b)
    have hA : 0 ≤ A := (Real.exp_pos _).le
    have hB : 0 ≤ B := (Real.exp_pos _).le
    have hE : 0 ≤ E := add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have hend : endpointBound (fun x ↦ u x + a) (fun x ↦ w x + b) x ≤ E * (A + B) := by
      have he₀ : Real.exp (u x + a) = Real.exp a * A := by
        rw [Real.exp_add, mul_comm]
      have he₁ : Real.exp ((u x + a) + (w x + b)) = Real.exp (a + b) * B := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [endpointBound, he₀, he₁]
      dsimp [E]
      nlinarith [mul_nonneg (Real.exp_pos a).le hB,
        mul_nonneg (Real.exp_pos (a + b)).le hA]
    have hab : 1 + |w x + b| ≤ (1 + |w x|) * (1 + |b|) := by
      nlinarith [abs_add_le (w x) b, mul_nonneg (abs_nonneg (w x)) (abs_nonneg b)]
    have hn : 0 ≤ majorant (fun x ↦ u x + a) (fun x ↦ w x + b) x := by
      exact mul_nonneg (endpointBound_nonneg _ _ _) (by positivity)
    change ‖majorant (fun x ↦ u x + a) (fun x ↦ w x + b) x‖ ≤ C * majorant u w x
    rw [Real.norm_of_nonneg hn]
    calc
      _ ≤ (E * (A + B)) * ((1 + |w x|) * (1 + |b|)) :=
        mul_le_mul hend hab (by positivity) (mul_nonneg hE (add_nonneg hA hB))
      _ = C * majorant u w x := by
        dsimp [C, E, A, B, majorant, endpointBound]
        ring

theorem normalizer_zero (u w : α → ℝ) (t : ℝ) :
    normalizer (0 : Measure α) u w t = 0 := by simp [normalizer]

theorem law_zero (u w : α → ℝ) (t : ℝ) : law (0 : Measure α) u w t = 0 := by simp [law]

/-- The source estimate may be applied after removing either constant:
the laws on the left are the original laws, while the right uses the
first absolute moment of the shifted perturbation. -/
theorem Admissible.setTV_interpolation_shift [NeZero μ] (h : Admissible μ u w) (a b : ℝ) :
    setTotalVariation (law μ u w 0) (law μ u w 1) ≤
      (∫ t in (0 : ℝ)..1, meanAbs μ (fun x ↦ u x + a) (fun x ↦ w x + b) t) ∧
    (∫ t in (0 : ℝ)..1, meanAbs μ (fun x ↦ u x + a) (fun x ↦ w x + b) t) ≤
      meanAbsSup μ (fun x ↦ u x + a) (fun x ↦ w x + b) := by
  simpa only [law_shift] using (h.shift a b).setTV_interpolation

end PeriodicAttractiveLogGas.NormalizedExponentialInterpolation
