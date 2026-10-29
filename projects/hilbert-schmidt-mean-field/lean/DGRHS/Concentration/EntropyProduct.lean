import DGRHS.Concentration.EntropyVariational

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace DGRHS.Concentration

lemma PositiveBounded.prod_swap {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    PositiveBounded (ν.prod μ) (fun z ↦ f z.swap) c C := by
  refine ⟨hf.measurable.prod_swap, hf.lower_pos, hf.lower_le_upper, ?_⟩
  exact (measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hf.bounds

lemma PositiveBounded.sections_right {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    ∀ᵐ x ∂μ, PositiveBounded ν (fun y ↦ f (x,y)) c C := by
  filter_upwards [hf.measurable.prodMk_left, ae_ae_of_ae_prod hf.bounds] with x hx hb
  exact ⟨hx, hf.lower_pos, hf.lower_le_upper, hb⟩

lemma PositiveBounded.sections_left {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    ∀ᵐ y ∂ν, PositiveBounded μ (fun x ↦ f (x,y)) c C :=
  hf.prod_swap.sections_right

lemma PositiveBounded.average_right {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    PositiveBounded μ (fun x ↦ ∫ y, f (x,y) ∂ν) c C :=
  ⟨hf.measurable.integral_prod_right', hf.lower_pos, hf.lower_le_upper,
    hf.sections_right.mono fun _ hx ↦ hx.integral_bounds⟩

lemma PositiveBounded.average_left {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    PositiveBounded ν (fun y ↦ ∫ x, f (x,y) ∂μ) c C :=
  hf.prod_swap.average_right

lemma section_entropy_integrable_right {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    Integrable (fun x ↦ functionalEntropy ν (fun y ↦ f (x,y))) μ :=
  hf.mul_log_integrable.integral_prod_left.sub hf.average_right.mul_log_integrable

lemma section_entropy_integrable_left {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    Integrable (fun y ↦ functionalEntropy μ (fun x ↦ f (x,y))) ν :=
  section_entropy_integrable_right hf.prod_swap

lemma entropy_chain_right {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    functionalEntropy (μ.prod ν) f =
      (∫ x, functionalEntropy ν (fun y ↦ f (x,y)) ∂μ) +
      functionalEntropy μ (fun x ↦ ∫ y, f (x,y) ∂ν) := by
  simp only [functionalEntropy]
  rw [integral_sub hf.mul_log_integrable.integral_prod_left hf.average_right.mul_log_integrable,
    integral_prod _ hf.mul_log_integrable, integral_prod _ hf.integrable]
  ring

lemma entropy_chain_left {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    functionalEntropy (μ.prod ν) f =
      (∫ y, functionalEntropy μ (fun x ↦ f (x,y)) ∂ν) +
      functionalEntropy ν (fun y ↦ ∫ x, f (x,y) ∂μ) := by
  simp only [functionalEntropy]
  rw [integral_sub hf.mul_log_integrable.integral_prod_right hf.average_left.mul_log_integrable,
    integral_prod_symm _ hf.mul_log_integrable, integral_prod_symm _ hf.integrable]
  ring

lemma integral_entropy_jensen {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    functionalEntropy ν (fun y ↦ ∫ x, f (x,y) ∂μ) ≤
      ∫ x, functionalEntropy ν (fun y ↦ f (x,y)) ∂μ := by
  let H := fun y ↦ ∫ x, f (x,y) ∂μ
  let g := fun y ↦ Real.log (H y / (∫ z, H z ∂ν))
  rcases entropy_optimizer hf.average_left with ⟨hu, hB, he, hHg, hE, hEnt⟩
  have hug : AEStronglyMeasurable g ν := hu
  have hfg : Integrable (fun z : Ω × Ξ ↦ f z * g z.2) (μ.prod ν) :=
    bounded_mul_integrable (B := |c| + |C|) hf.measurable hug.comp_snd
      (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2)
      (quasiMeasurePreserving_snd.ae hB)
  have hs : ∀ᵐ x ∂μ, (∫ y, f (x,y) * g y ∂ν) ≤
      functionalEntropy ν (fun y ↦ f (x,y)) := by
    filter_upwards [hf.sections_right] with x hx
    have h := bounded_variational hx hug hB
    rw [hE] at h
    simpa only [Real.log_one, mul_zero, add_zero] using h
  have hi := integral_mono_ae hfg.integral_prod_left
    (section_entropy_integrable_right hf) hs
  have hi_eq : (∫ x, ∫ y, f (x,y) * g y ∂ν ∂μ) = ∫ y, H y * g y ∂ν := by
    calc
      _ = ∫ z, f z * g z.2 ∂μ.prod ν := (integral_prod _ hfg).symm
      _ = ∫ y, ∫ x, f (x,y) * g y ∂μ ∂ν := integral_prod_symm _ hfg
      _ = ∫ y, H y * g y ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦ integral_mul_const _ _
  rw [hi_eq] at hi
  exact hEnt ▸ hi

lemma two_factor_entropy_tensorization {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded (μ.prod ν) f c C) :
    functionalEntropy (μ.prod ν) f ≤
      (∫ x, functionalEntropy ν (fun y ↦ f (x,y)) ∂μ) +
      (∫ y, functionalEntropy μ (fun x ↦ f (x,y)) ∂ν) := by
  rw [entropy_chain_left hf]
  have h := integral_entropy_jensen hf
  linarith

#print axioms DGRHS.Concentration.entropy_chain_right
#print axioms DGRHS.Concentration.entropy_chain_left
#print axioms DGRHS.Concentration.integral_entropy_jensen
#print axioms DGRHS.Concentration.two_factor_entropy_tensorization
end DGRHS.Concentration
