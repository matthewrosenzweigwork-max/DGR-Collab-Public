import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory
namespace DGRHS.Concentration

/-- Probability-space positive functional entropy, with its original normalization. -/
def functionalEntropy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂μ) - (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)

/-- Branch-local support data: measurability and uniform positive bounds hold almost everywhere. -/
structure PositiveBounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (c C : ℝ) : Prop where
  measurable : AEStronglyMeasurable f μ
  lower_pos : 0 < c
  lower_le_upper : c ≤ C
  bounds : ∀ᵐ x ∂μ, c ≤ f x ∧ f x ≤ C

lemma integrable_of_ae_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f μ) (hB : ∀ᵐ x ∂μ, |f x| ≤ B) : Integrable f μ := by
  apply (integrable_const B).mono' hf
  simpa only [Real.norm_eq_abs] using hB

lemma abs_le_of_bounds {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    |x| ≤ |a| + |b| := by
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le a, abs_nonneg b]
  · linarith [le_abs_self b, abs_nonneg a]

lemma PositiveBounded.integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {c C : ℝ}
    (h : PositiveBounded μ f c C) : Integrable f μ := by
  apply integrable_of_ae_abs_le h.measurable
  filter_upwards [h.bounds] with x hx
  exact abs_le_of_bounds hx.1 hx.2

lemma PositiveBounded.integral_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {c C : ℝ}
    (h : PositiveBounded μ f c C) : c ≤ (∫ x, f x ∂μ) ∧ (∫ x, f x ∂μ) ≤ C := by
  constructor
  · simpa using integral_mono_ae (integrable_const c) h.integrable (h.bounds.mono fun _ hx ↦ hx.1)
  · simpa using integral_mono_ae h.integrable (integrable_const C) (h.bounds.mono fun _ hx ↦ hx.2)

lemma PositiveBounded.integral_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {c C : ℝ}
    (h : PositiveBounded μ f c C) : 0 < (∫ x, f x ∂μ) :=
  h.lower_pos.trans_le h.integral_bounds.1

lemma PositiveBounded.log_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} {c C : ℝ} (h : PositiveBounded μ f c C) :
    AEStronglyMeasurable (fun x ↦ Real.log (f x)) μ :=
  h.measurable.aemeasurable.log.aestronglyMeasurable

lemma PositiveBounded.log_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} {c C : ℝ} (h : PositiveBounded μ f c C) :
    ∀ᵐ x ∂μ, |Real.log (f x)| ≤ |Real.log c| + |Real.log C| := by
  filter_upwards [h.bounds] with x hx
  exact abs_le_of_bounds (Real.log_le_log h.lower_pos hx.1)
    (Real.log_le_log (h.lower_pos.trans_le hx.1) hx.2)

lemma PositiveBounded.log_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {c C : ℝ}
    (h : PositiveBounded μ f c C) : Integrable (fun x ↦ Real.log (f x)) μ :=
  integrable_of_ae_abs_le h.log_measurable h.log_abs_bound

lemma bounded_mul_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → ℝ} {B D : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hB : ∀ᵐ x ∂μ, |f x| ≤ B) (hD : ∀ᵐ x ∂μ, |g x| ≤ D) :
    Integrable (fun x ↦ f x * g x) μ := by
  apply integrable_of_ae_abs_le (B := B * D) (hf.mul hg)
  filter_upwards [hB, hD] with x hx hy
  change |f x * g x| ≤ B * D
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

lemma PositiveBounded.mul_log_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {c C : ℝ}
    (h : PositiveBounded μ f c C) : Integrable (fun x ↦ f x * Real.log (f x)) μ := by
  refine bounded_mul_integrable (B := |c| + |C|)
    (D := |Real.log c| + |Real.log C|) h.measurable h.log_measurable ?_ h.log_abs_bound
  exact h.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2

lemma bounded_exp_positive {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {u : Ω → ℝ} {B : ℝ}
    (hu : AEStronglyMeasurable u μ) (hB : ∀ᵐ x ∂μ, |u x| ≤ B) :
    PositiveBounded μ (fun x ↦ Real.exp (u x)) (Real.exp (-|B|)) (Real.exp |B|) := by
  refine ⟨Real.continuous_exp.comp_aestronglyMeasurable hu, Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_exp.mpr (by linarith [abs_nonneg B])
  · filter_upwards [hB] with x hx
    have hx' : |u x| ≤ |B| := hx.trans (le_abs_self _)
    exact ⟨Real.exp_le_exp.mpr (abs_le.mp hx').1,
      Real.exp_le_exp.mpr (abs_le.mp hx').2⟩

end DGRHS.Concentration
