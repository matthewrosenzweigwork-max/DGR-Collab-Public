import DGRHS.Concentration.EntropyProduct

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace DGRHS.Concentration

/-- The checked probability entropy interface requires no pointwise bounds or measurability. -/
theorem bounded_log_variational_of_ae_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f u : Ω → ℝ) (c C B : ℝ)
    (hf : AEStronglyMeasurable f μ) (hc : 0 < c) (hcC : c ≤ C)
    (hfc : ∀ᵐ x ∂μ, c ≤ f x ∧ f x ≤ C)
    (hu : AEStronglyMeasurable u μ) (hB : ∀ᵐ x ∂μ, |u x| ≤ B) :
    (∫ x, f x * u x ∂μ) ≤ functionalEntropy μ f +
      (∫ x, f x ∂μ) * Real.log (∫ x, Real.exp (u x) ∂μ) :=
  bounded_variational ⟨hf, hc, hcC, hfc⟩ hu hB

/-- Every integral entering the variational comparison has genuine finite L1 data. -/
theorem bounded_entropy_integrability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f u : Ω → ℝ) (c C B : ℝ)
    (hf : AEStronglyMeasurable f μ) (hc : 0 < c) (hcC : c ≤ C)
    (hfc : ∀ᵐ x ∂μ, c ≤ f x ∧ f x ≤ C)
    (hu : AEStronglyMeasurable u μ) (hB : ∀ᵐ x ∂μ, |u x| ≤ B) :
    Integrable f μ ∧ Integrable u μ ∧ Integrable (fun x ↦ Real.log (f x)) μ ∧
    Integrable (fun x ↦ f x * Real.log (f x)) μ ∧
    Integrable (fun x ↦ Real.exp (u x)) μ ∧ Integrable (fun x ↦ f x * u x) μ ∧
    0 < (∫ x, f x ∂μ) ∧ 0 < (∫ x, Real.exp (u x) ∂μ) := by
  have hp : PositiveBounded μ f c C := ⟨hf, hc, hcC, hfc⟩
  have he := bounded_exp_positive hu hB
  refine ⟨hp.integrable, integrable_of_ae_abs_le hu hB, hp.log_integrable,
    hp.mul_log_integrable, he.integrable, ?_, hp.integral_pos, he.integral_pos⟩
  exact bounded_mul_integrable (B := |c| + |C|) hf hu
    (hfc.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) hB

theorem entropy_nonneg_of_ae_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (c C : ℝ)
    (hf : AEStronglyMeasurable f μ) (hc : 0 < c) (hcC : c ≤ C)
    (hfc : ∀ᵐ x ∂μ, c ≤ f x ∧ f x ≤ C) : 0 ≤ functionalEntropy μ f :=
  entropy_nonneg ⟨hf, hc, hcC, hfc⟩

theorem integral_entropy_jensen_of_ae_bounds {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × Ξ → ℝ) (c C : ℝ) (hf : AEStronglyMeasurable f (μ.prod ν))
    (hc : 0 < c) (hcC : c ≤ C) (hfc : ∀ᵐ z ∂μ.prod ν, c ≤ f z ∧ f z ≤ C) :
    functionalEntropy ν (fun y ↦ ∫ x, f (x,y) ∂μ) ≤
      ∫ x, functionalEntropy ν (fun y ↦ f (x,y)) ∂μ :=
  integral_entropy_jensen ⟨hf, hc, hcC, hfc⟩

theorem two_factor_entropy_tensorization_of_ae_bounds {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × Ξ → ℝ) (c C : ℝ) (hf : AEStronglyMeasurable f (μ.prod ν))
    (hc : 0 < c) (hcC : c ≤ C) (hfc : ∀ᵐ z ∂μ.prod ν, c ≤ f z ∧ f z ≤ C) :
    functionalEntropy (μ.prod ν) f ≤
      (∫ x, functionalEntropy ν (fun y ↦ f (x,y)) ∂μ) +
      (∫ y, functionalEntropy μ (fun x ↦ f (x,y)) ∂ν) :=
  two_factor_entropy_tensorization ⟨hf, hc, hcC, hfc⟩

/-- Concrete downstream specialization: bounded real functions give admissible exponentials. -/
theorem bounded_exponential_two_factor_entropy {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω × Ξ → ℝ) (B : ℝ) (hu : AEStronglyMeasurable u (μ.prod ν))
    (hB : ∀ᵐ z ∂μ.prod ν, |u z| ≤ B) :
    functionalEntropy (μ.prod ν) (fun z ↦ Real.exp (u z)) ≤
      (∫ x, functionalEntropy ν (fun y ↦ Real.exp (u (x,y))) ∂μ) +
      (∫ y, functionalEntropy μ (fun x ↦ Real.exp (u (x,y))) ∂ν) :=
  two_factor_entropy_tensorization (bounded_exp_positive hu hB)

lemma functionalEntropy_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) :
    functionalEntropy μ (fun _ ↦ a) = 0 := by
  simp [functionalEntropy]

lemma functionalEntropy_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) :
    functionalEntropy μ f = functionalEntropy μ g := by
  have hm := integral_congr_ae hfg
  have hq : (∫ x, f x * Real.log (f x) ∂μ) = ∫ x, g x * Real.log (g x) ∂μ :=
    integral_congr_ae (hfg.mono fun _ hx ↦ by dsimp only; rw [hx])
  unfold functionalEntropy
  rw [hq, hm]

lemma entropy_eq_zero_of_ae_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {a : ℝ}
    (hf : f =ᵐ[μ] fun _ ↦ a) : functionalEntropy μ f = 0 := by
  rw [functionalEntropy_congr_ae hf, functionalEntropy_const]

lemma PositiveBounded.comp_fst {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → ℝ} {c C : ℝ} (hf : PositiveBounded μ f c C) :
    PositiveBounded (μ.prod ν) (fun z ↦ f z.1) c C :=
  ⟨hf.measurable.comp_fst, hf.lower_pos, hf.lower_le_upper, quasiMeasurePreserving_fst.ae hf.bounds⟩

lemma PositiveBounded.comp_snd {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded ν f c C) :
    PositiveBounded (μ.prod ν) (fun z ↦ f z.2) c C :=
  ⟨hf.measurable.comp_snd, hf.lower_pos, hf.lower_le_upper, quasiMeasurePreserving_snd.ae hf.bounds⟩

lemma functionalEntropy_fst {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → ℝ} {c C : ℝ} (hf : PositiveBounded μ f c C) :
    functionalEntropy (μ.prod ν) (fun z ↦ f z.1) = functionalEntropy μ f := by
  rw [entropy_chain_right hf.comp_fst]
  simp [functionalEntropy_const]

lemma functionalEntropy_snd {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ξ → ℝ} {c C : ℝ} (hf : PositiveBounded ν f c C) :
    functionalEntropy (μ.prod ν) (fun z ↦ f z.2) = functionalEntropy ν f := by
  rw [entropy_chain_left hf.comp_snd]
  simp [functionalEntropy_const]

#print axioms DGRHS.Concentration.bounded_log_variational_of_ae_bounds
#print axioms DGRHS.Concentration.bounded_entropy_integrability
#print axioms DGRHS.Concentration.entropy_optimizer
#print axioms DGRHS.Concentration.entropy_nonneg_of_ae_bounds
#print axioms DGRHS.Concentration.integral_entropy_jensen_of_ae_bounds
#print axioms DGRHS.Concentration.two_factor_entropy_tensorization_of_ae_bounds
#print axioms DGRHS.Concentration.bounded_exponential_two_factor_entropy
#print axioms DGRHS.Concentration.functionalEntropy_fst
#print axioms DGRHS.Concentration.functionalEntropy_snd
#check @DGRHS.Concentration.functionalEntropy
#check @DGRHS.Concentration.PositiveBounded
#check @DGRHS.Concentration.bounded_log_variational_of_ae_bounds
#check @DGRHS.Concentration.bounded_entropy_integrability
#check @DGRHS.Concentration.entropy_optimizer
#check @DGRHS.Concentration.entropy_nonneg_of_ae_bounds
#check @DGRHS.Concentration.integral_entropy_jensen_of_ae_bounds
#check @DGRHS.Concentration.two_factor_entropy_tensorization_of_ae_bounds
#check @DGRHS.Concentration.bounded_exponential_two_factor_entropy
#check @DGRHS.Concentration.entropy_chain_right
#check @DGRHS.Concentration.entropy_chain_left
end DGRHS.Concentration
