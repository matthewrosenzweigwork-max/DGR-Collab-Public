import LeanResearch.PeriodicAttractiveLogGas.SobolevEntropy

/-! Appendix A bounded perturbation. The entropy comparison uses the
nonnegative variational integrand, and the variance comparison retains
separate upper and lower density factors until their product is taken. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal
namespace PeriodicAttractiveLogGas.BoundedPerturbation
open DensityMoments
variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

def entropyIntegrand (b t : ℝ) : ℝ := t * Real.log t - t * Real.log b - t + b

lemma entropyIntegrand_nonneg {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    0 ≤ entropyIntegrand b t := by
  by_cases hz : t = 0
  · simpa only [entropyIntegrand, hz, zero_mul, sub_zero, zero_sub, zero_add] using hb.le
  have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  have hl := Real.log_le_sub_one_of_pos (div_pos hb hp)
  rw [Real.log_div hb.ne' hp.ne'] at hl
  have hh := mul_le_mul_of_nonneg_left hl hp.le
  have he : t * (b / t - 1) = b - t := by field_simp [hp.ne']
  rw [he] at hh
  unfold entropyIntegrand
  nlinarith only [hh]

lemma integrable_entropyIntegrand [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (b : ℝ) :
    Integrable (fun x => entropyIntegrand b (f x ^ 2)) μ := by
  obtain ⟨M, hM⟩ := hb
  have hc : Continuous (fun t : ℝ => entropyIntegrand b (t ^ 2)) :=
    (((Real.continuous_mul_log.comp (continuous_id.pow 2)).sub
      ((continuous_id.pow 2).mul continuous_const)).sub (continuous_id.pow 2)).add continuous_const
  exact EntropyMoment.integrable_continuous_comp_bounded hf hM hc

lemma integral_entropyIntegrand [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (b : ℝ) :
    (∫ x, entropyIntegrand b (f x ^ 2) ∂μ) =
      Rothaus.squareEntropy μ f + entropyIntegrand b (∫ x, f x ^ 2 ∂μ) := by
  obtain ⟨M, hM⟩ := hb
  have h2 : Integrable (fun x => f x ^ 2) μ := (memLp_of_bounded hf ⟨M, hM⟩ 2).integrable_sq
  have hlog : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
    EntropyMoment.integrable_sq_mul_log_sq_of_integrable_abs_cube hf
      (EntropyMoment.integrable_abs_cube_bounded hf hM)
  have hsub1 : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log b) μ :=
    hlog.sub (h2.mul_const (Real.log b))
  have hsub2 : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log b - f x ^ 2) μ :=
    hsub1.sub h2
  unfold entropyIntegrand Rothaus.squareEntropy
  rw [integral_add hsub2 (integrable_const b),
    integral_sub hsub1 h2, integral_sub hlog (h2.mul_const (Real.log b)),
    integral_mul_const]
  simp only [integral_const, probReal_univ, one_smul]
  ring

lemma integral_nonneg_comparison {M : ℝ} (hM : 0 ≤ M)
    (hμν : μ ≤ ENNReal.ofReal M • ν) {F : α → ℝ}
    (hF : ∀ x, 0 ≤ F x) (hi : Integrable F ν) :
    (∫ x, F x ∂μ) ≤ M * ∫ x, F x ∂ν := by
  have hh := integral_mono_measure hμν (Eventually.of_forall hF)
    (hi.smul_measure ENNReal.ofReal_ne_top)
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hM, smul_eq_mul] using hh

/-- The source entropy comparison, including zero mass under the reference
probability. The optimizing positive scalar is its actual squared mean. -/
theorem entropy_comparison [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (hM : 0 ≤ M) (hμν : μ ≤ ENNReal.ofReal M • ν)
    {f : α → ℝ} (hf : Measurable f) (hb : ∃ K : ℝ, ∀ x, |f x| ≤ K) :
    Rothaus.squareEntropy μ f ≤ M * Rothaus.squareEntropy ν f := by
  let b := ∫ x, f x ^ 2 ∂ν
  have hb0 : 0 ≤ b := integral_nonneg fun x => sq_nonneg (f x)
  by_cases hz : b = 0
  · have hm := integral_nonneg_comparison hM hμν (fun x => sq_nonneg (f x))
      (memLp_of_bounded hf hb 2).integrable_sq
    have hmass : (∫ x, f x ^ 2 ∂μ) = 0 := by
      have hn : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (f x)
      change _ ≤ M * b at hm
      rw [hz, mul_zero] at hm
      exact le_antisymm hm hn
    rw [EntropyScaling.squareEntropy_zero_mass hf hb hmass,
      EntropyScaling.squareEntropy_zero_mass hf hb hz, mul_zero]
  have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hz)
  have hnon := entropyIntegrand_nonneg hbp
    (integral_nonneg (μ := μ) fun x => sq_nonneg (f x))
  have hleft := integral_entropyIntegrand (μ := μ) hf hb b
  have hright := integral_entropyIntegrand (μ := ν) hf hb b
  have he : entropyIntegrand b b = 0 := by unfold entropyIntegrand; ring
  change (∫ x, entropyIntegrand b (f x ^ 2) ∂ν) = Rothaus.squareEntropy ν f + entropyIntegrand b b at hright
  rw [he, add_zero] at hright
  have hc := integral_nonneg_comparison hM hμν
    (fun x => entropyIntegrand_nonneg hbp (sq_nonneg (f x)))
    (integrable_entropyIntegrand (μ := ν) hf hb b)
  rw [hleft, hright] at hc
  linarith only [hc, hnon]

/-- Variance comparison with the two actual measure factors, rather than
a prematurely squared common bound. -/
theorem poincare_comparison [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u v C : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hμν : μ ≤ ENNReal.ofReal u • ν) (hνμ : ν ≤ ENNReal.ofReal v • μ)
    {f G : α → ℝ} (hf : Measurable f) (hb : ∃ K : ℝ, ∀ x, |f x| ≤ K)
    (hG : ∀ x, 0 ≤ G x) (hi : Integrable G μ)
    (hPI : variance f ν ≤ C * ∫ x, G x ∂ν) :
    variance f μ ≤ (u * v * C) * ∫ x, G x ∂μ := by
  have hc := integral_nonneg_comparison hu hμν
    (fun x => sq_nonneg (f x - ∫ y, f y ∂ν))
    (memLp_of_bounded (hf.sub measurable_const) (bounded_sub_const hb _) 2).integrable_sq
  rw [← variance_eq_integral hf.aemeasurable] at hc
  have he := integral_nonneg_comparison hv hνμ hG hi
  calc
    _ ≤ ∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂μ := variance_le_integral_sub_sq hf _
    _ ≤ u * variance f ν := hc
    _ ≤ u * (C * ∫ x, G x ∂ν) := mul_le_mul_of_nonneg_left hPI hu
    _ ≤ u * (C * (v * ∫ x, G x ∂μ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hC) hu
    _ = _ := by ring

/-- Source defective-entropy transfer with the common two-sided density
bound. Both nonnegative terms acquire the permitted factor M squared. -/
theorem defective_comparison [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M A B : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμν : μ ≤ ENNReal.ofReal M • ν) (hνμ : ν ≤ ENNReal.ofReal M • μ)
    {f G : α → ℝ} (hf : Measurable f) (hb : ∃ K : ℝ, ∀ x, |f x| ≤ K)
    (hG : ∀ x, 0 ≤ G x) (hi : Integrable G μ)
    (hD : Rothaus.squareEntropy ν f ≤ A * ∫ x, G x ∂ν + B * ∫ x, f x ^ 2 ∂ν) :
    Rothaus.squareEntropy μ f ≤ M ^ 2 * A * ∫ x, G x ∂μ + M ^ 2 * B * ∫ x, f x ^ 2 ∂μ := by
  have he := integral_nonneg_comparison hM hνμ hG hi
  have hm := integral_nonneg_comparison hM hνμ (fun x => sq_nonneg (f x))
    (memLp_of_bounded hf hb 2).integrable_sq
  calc
    _ ≤ M * Rothaus.squareEntropy ν f := entropy_comparison hM hμν hf hb
    _ ≤ M * (A * ∫ x, G x ∂ν + B * ∫ x, f x ^ 2 ∂ν) := mul_le_mul_of_nonneg_left hD hM
    _ ≤ M * (A * (M * ∫ x, G x ∂μ) + B * (M * ∫ x, f x ^ 2 ∂μ)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left he hA)
        (mul_le_mul_of_nonneg_left hm hB)) hM
    _ = _ := by ring

end PeriodicAttractiveLogGas.BoundedPerturbation
