import LeanResearch.PeriodicAttractiveLogGas.Rothaus

/-! Exact homogeneity of the finite square entropy, including zero mass.
This supplies the normalization step in source Lemma 3.2. -/

noncomputable section

open MeasureTheory Filter

namespace PeriodicAttractiveLogGas.EntropyScaling

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}

theorem mul_log_mul (u v : ℝ) :
    (u * v) * Real.log (u * v) = u * (v * Real.log v) +
      (u * Real.log u) * v := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  rw [Real.log_mul hu hv]
  ring

omit [MeasurableSpace A] in
theorem bounded_const_mul {f : A → ℝ}
    (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (a : ℝ) :
    ∃ M : ℝ, ∀ x, |a * f x| ≤ M := by
  obtain ⟨M, hM⟩ := hb
  exact ⟨|a| * M, fun x ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg a)⟩

theorem squareEntropy_const_mul [IsFiniteMeasure μ] {f : A → ℝ}
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (a : ℝ) :
    Rothaus.squareEntropy μ (fun x ↦ a * f x) = a ^ 2 * Rothaus.squareEntropy μ f := by
  obtain ⟨M, hM⟩ := hb
  have hi : Integrable (fun x ↦ f x ^ 2) μ :=
    Rothaus.integrable_continuous_comp_bounded hf hM (continuous_id.pow 2)
  have hl : Integrable (fun x ↦ f x ^ 2 * Real.log (f x ^ 2)) μ :=
    Rothaus.integrable_continuous_comp_bounded hf hM
      (Real.continuous_mul_log.comp (continuous_id.pow 2))
  have he (x : A) : (a * f x) ^ 2 * Real.log ((a * f x) ^ 2) =
      a ^ 2 * (f x ^ 2 * Real.log (f x ^ 2)) +
        (a ^ 2 * Real.log (a ^ 2)) * f x ^ 2 := by
    rw [mul_pow]
    exact mul_log_mul (a ^ 2) (f x ^ 2)
  have hm : (∫ x, (a * f x) ^ 2 ∂μ) = a ^ 2 * ∫ x, f x ^ 2 ∂μ := by
    simp only [mul_pow, integral_const_mul]
  unfold Rothaus.squareEntropy
  simp_rw [he]
  rw [integral_add (hl.const_mul _) (hi.const_mul _),
    integral_const_mul, integral_const_mul, hm, mul_log_mul]
  ring

theorem squareEntropy_zero_mass [IsFiniteMeasure μ] {f : A → ℝ}
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hm : ∫ x, f x ^ 2 ∂μ = 0) : Rothaus.squareEntropy μ f = 0 := by
  obtain ⟨M, hM⟩ := hb
  have hi : Integrable (fun x ↦ f x ^ 2) μ :=
    Rothaus.integrable_continuous_comp_bounded hf hM (continuous_id.pow 2)
  have hz := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (f x)) hi).mp hm
  have he : (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) = 0 := by
    calc
      _ = ∫ _, (0 : ℝ) ∂μ := integral_congr_ae (hz.mono fun x hx ↦ by simp [hx])
      _ = 0 := integral_zero _ _
  simp only [Rothaus.squareEntropy, he, hm, zero_mul, sub_zero]

end PeriodicAttractiveLogGas.EntropyScaling
