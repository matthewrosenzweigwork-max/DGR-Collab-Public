import DGRHS.Concentration.EntropyBasic

noncomputable section
open MeasureTheory
namespace DGRHS.Concentration

lemma logarithmic_variational_pointwise {f m A u : ℝ}
    (hf : 0 < f) (hm : 0 < m) (hA : 0 < A) :
    f * u ≤ f * Real.log f + f * (Real.log A - Real.log m - 1) +
      Real.exp u * (m / A) := by
  have hz : 0 < Real.exp u * m / (f * A) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hz
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) hm.ne', Real.log_mul hf.ne' hA.ne',
    Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hf.le
  have hcancel : f * (Real.exp u * m / (f * A) - 1) = Real.exp u * (m / A) - f := by
    field_simp
  rw [hcancel] at hmul
  nlinarith

lemma bounded_variational {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f u : Ω → ℝ} {c C B : ℝ}
    (hf : PositiveBounded μ f c C) (hu : AEStronglyMeasurable u μ)
    (hB : ∀ᵐ x ∂μ, |u x| ≤ B) :
    (∫ x, f x * u x ∂μ) ≤ functionalEntropy μ f +
      (∫ x, f x ∂μ) * Real.log (∫ x, Real.exp (u x) ∂μ) := by
  let m := ∫ x, f x ∂μ
  let A := ∫ x, Real.exp (u x) ∂μ
  have hm : 0 < m := hf.integral_pos
  have he := bounded_exp_positive hu hB
  have hA : 0 < A := he.integral_pos
  have hfu : Integrable (fun x ↦ f x * u x) μ :=
    bounded_mul_integrable (B := |c| + |C|) (D := B) hf.measurable hu
      (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) hB
  have hr : Integrable (fun x ↦ f x * Real.log (f x) +
      f x * (Real.log A - Real.log m - 1) + Real.exp (u x) * (m / A)) μ :=
    (hf.mul_log_integrable.add (hf.integrable.mul_const _)).add (he.integrable.mul_const _)
  have h := integral_mono_ae hfu hr (hf.bounds.mono fun x hx ↦
    logarithmic_variational_pointwise (hf.lower_pos.trans_le hx.1) hm hA)
  have hfc : Integrable (fun x ↦ f x * (Real.log A - Real.log m - 1)) μ :=
    hf.integrable.mul_const _
  have hec : Integrable (fun x ↦ Real.exp (u x) * (m / A)) μ := he.integrable.mul_const _
  have hsum : Integrable (fun x ↦ f x * Real.log (f x) +
      f x * (Real.log A - Real.log m - 1)) μ := hf.mul_log_integrable.add hfc
  rw [integral_add hsum hec, integral_add hf.mul_log_integrable hfc,
      integral_mul_const, integral_mul_const] at h
  change _ ≤ functionalEntropy μ f + m * Real.log A
  unfold functionalEntropy
  change _ ≤ (∫ x, f x * Real.log (f x) ∂μ) - m * Real.log m + m * Real.log A
  have hAm : A * (m / A) = m := by field_simp
  change _ ≤ _ + m * (Real.log A - Real.log m - 1) + A * (m / A) at h
  rw [hAm] at h
  linarith

lemma entropy_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {c C : ℝ}
    (hf : PositiveBounded μ f c C) : 0 ≤ functionalEntropy μ f := by
  have h := bounded_variational hf (u := fun _ ↦ 0) (B := 0)
    aestronglyMeasurable_const (Filter.Eventually.of_forall fun _ ↦ by simp)
  simpa using h

lemma PositiveBounded.div_positive_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} {c C m : ℝ}
    (hf : PositiveBounded μ f c C) (hm : 0 < m) :
    PositiveBounded μ (fun x ↦ f x / m) (c / m) (C / m) := by
  refine ⟨?_, div_pos hf.lower_pos hm,
    (div_le_div_iff_of_pos_right hm).mpr hf.lower_le_upper, ?_⟩
  · simpa only [div_eq_mul_inv, Pi.mul_def] using hf.measurable.mul
      (aestronglyMeasurable_const (b := m⁻¹))
  · filter_upwards [hf.bounds] with x hx
    exact ⟨(div_le_div_iff_of_pos_right hm).mpr hx.1,
      (div_le_div_iff_of_pos_right hm).mpr hx.2⟩

lemma entropy_optimizer {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {c C : ℝ}
    (hf : PositiveBounded μ f c C) :
    let m := ∫ x, f x ∂μ
    let u := fun x ↦ Real.log (f x / m)
    AEStronglyMeasurable u μ ∧
    (∀ᵐ x ∂μ, |u x| ≤ |Real.log (c / m)| + |Real.log (C / m)|) ∧
    Integrable (fun x ↦ Real.exp (u x)) μ ∧
    Integrable (fun x ↦ f x * u x) μ ∧
    (∫ x, Real.exp (u x) ∂μ) = 1 ∧ (∫ x, f x * u x ∂μ) = functionalEntropy μ f := by
  dsimp
  let m := ∫ x, f x ∂μ
  have hm : 0 < m := hf.integral_pos
  have hd := hf.div_positive_const hm
  have hu := hd.log_measurable
  have hB := hd.log_abs_bound
  have he := (bounded_exp_positive hu hB).integrable
  have hfu : Integrable (fun x ↦ f x * Real.log (f x / m)) μ :=
    bounded_mul_integrable (B := |c| + |C|) hf.measurable hu
      (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) hB
  refine ⟨hu, hB, he, hfu, ?_, ?_⟩
  · calc
      (∫ x, Real.exp (Real.log (f x / m)) ∂μ) = ∫ x, f x / m ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf.bounds] with x hx
        exact Real.exp_log (div_pos (hf.lower_pos.trans_le hx.1) hm)
      _ = 1 := by rw [integral_div]; exact div_self hm.ne'
  · calc
      (∫ x, f x * Real.log (f x / m) ∂μ) =
          ∫ x, f x * Real.log (f x) - f x * Real.log m ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf.bounds] with x hx
        rw [Real.log_div (hf.lower_pos.trans_le hx.1).ne' hm.ne']
        ring
      _ = functionalEntropy μ f := by
        rw [integral_sub hf.mul_log_integrable (hf.integrable.mul_const _), integral_mul_const]
        rfl

#print axioms DGRHS.Concentration.bounded_variational
#print axioms DGRHS.Concentration.entropy_nonneg
#print axioms DGRHS.Concentration.entropy_optimizer
end DGRHS.Concentration
