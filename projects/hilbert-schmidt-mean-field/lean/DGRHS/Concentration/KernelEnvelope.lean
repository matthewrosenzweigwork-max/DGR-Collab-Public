import DGRHS.Concentration.IntegratedRosenthal

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

lemma absolute_power_square_envelope (x A : ℝ) (hx : |x| ≤ A) (m : ℕ) (hm : 2 ≤ m) :
    |x|^m ≤ A^(m-2)*x^2 := by
  calc
    |x|^m = |x|^(m-2)*|x|^2 := by rw [← pow_add]; congr 1; omega
    _ ≤ A^(m-2)*x^2 := by
      rw [sq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx _) (sq_nonneg x)

lemma nonnegative_power_square_envelope (x B : ℝ) (hx : 0 ≤ x) (hB : x ≤ B^2)
    (k : ℕ) (hk : 1 ≤ k) : x^k ≤ B^(2*k-2)*x := by
  calc
    x^k = x^(k-1)*x := by rw [← pow_succ]; congr 1; omega
    _ ≤ (B^2)^(k-1)*x := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hB _) hx
    _ = B^(2*k-2)*x := by rw [← pow_mul]; congr 2; omega

lemma bounded_kernel_abs_moment_integrable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) (m : ℕ) :
    Integrable (fun p ↦ |h p|^m) (μ.prod ν) := by
  have ha : AEStronglyMeasurable (fun p ↦ |h p|) (μ.prod ν) := by
    simpa only [Real.norm_eq_abs] using hAES.norm
  apply integrable_of_ae_abs_le (ha.fun_pow m)
  filter_upwards [hBound] with p hp
  rw [abs_pow,abs_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hp m

/-- The actual bounded-kernel A envelope, with all product moment integrability
proved before integral comparison. Zero A and C are permitted; m=2 is included. -/
theorem kernel_high_moment_envelope {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n r : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A C : ℝ) (hA : 0 ≤ A)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (m : ℕ) (hm : 2 ≤ m) :
    (∑ i, ∑ j, ∫ p, |h i j p|^m ∂(μ i).prod (ν j)) ≤ A^(m-2)*C^2 := by
  classical
  have hHigh := fun i j ↦ bounded_kernel_abs_moment_integrable (μ i) (ν j) (h i j)
    A (hAES i j) (hBound i j) m
  have hSquare : ∀ i j, Integrable (fun p ↦ (h i j p)^2) ((μ i).prod (ν j)) := fun i j ↦ by
    simpa only [sq_abs] using bounded_kernel_abs_moment_integrable (μ i) (ν j) (h i j)
      A (hAES i j) (hBound i j) 2
  have hp : ∀ i j, (∫ p, |h i j p|^m ∂(μ i).prod (ν j)) ≤
      A^(m-2)*(∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) := by
    intro i j
    have hi := integral_mono_ae (hHigh i j) ((hSquare i j).const_mul (A^(m-2)))
      ((hBound i j).mono fun p hp ↦ absolute_power_square_envelope (h i j p) A hp m hm)
    simpa only [integral_const_mul] using hi
  calc
    _ ≤ ∑ i, ∑ j, A^(m-2)*(∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hp i j
    _ = A^(m-2)*(∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hTrace (pow_nonneg hA _)

def kernelColumnEnergy {Ω Ψ : Type*} [MeasurableSpace Ω] {n r : ℕ}
    (μ : Fin n → Measure Ω) (h : Fin n → Fin r → Ω × Ψ → ℝ) (j : Fin r) (y : Ψ) : ℝ :=
  ∑ i, ∫ x, (h i j (x,y))^2 ∂μ i

/-- The actual B envelope; the AE column square bound is the source B definition,
not a moment conclusion. All section/marginal power integrability is proved here. -/
theorem kernel_column_energy_envelope {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n r : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A B C : ℝ) (hB : 0 ≤ B)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hColumn : ∀ j, ∀ᵐ y ∂ν j, kernelColumnEnergy μ h j y ≤ B^2)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ j, ∫ y, (kernelColumnEnergy μ h j y)^k ∂ν j) ≤ B^(2*k-2)*C^2 := by
  classical
  have hSquare : ∀ i j, Integrable (fun p ↦ (h i j p)^2) ((μ i).prod (ν j)) := fun i j ↦ by
    simpa only [sq_abs] using bounded_kernel_abs_moment_integrable (μ i) (ν j) (h i j)
      A (hAES i j) (hBound i j) 2
  have hEI : ∀ j, Integrable (kernelColumnEnergy μ h j) (ν j) := by
    intro j
    change Integrable (fun y ↦ ∑ i, ∫ x, (h i j (x,y))^2 ∂μ i) (ν j)
    simpa only [Finset.sum_apply] using
      integrable_finsetSum Finset.univ (fun i _ ↦ (hSquare i j).integral_prod_right)
  have hNonneg : ∀ j y, 0 ≤ kernelColumnEnergy μ h j y := fun j y ↦
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  have hPower : ∀ j, Integrable (fun y ↦ (kernelColumnEnergy μ h j y)^k) (ν j) := by
    intro j
    apply integrable_of_ae_abs_le ((hEI j).aestronglyMeasurable.fun_pow k)
    filter_upwards [hColumn j] with y hy
    rw [abs_pow,abs_of_nonneg (hNonneg j y)]
    exact pow_le_pow_left₀ (hNonneg j y) hy k
  have hIntegral : ∀ j, (∫ y, kernelColumnEnergy μ h j y ∂ν j) =
      ∑ i, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j) := by
    intro j
    unfold kernelColumnEnergy
    rw [integral_finsetSum _ (fun i _ ↦ (hSquare i j).integral_prod_right)]
    apply Finset.sum_congr rfl
    intro i hi
    exact (integral_prod_symm _ (hSquare i j)).symm
  have hOne : ∀ j, (∫ y, (kernelColumnEnergy μ h j y)^k ∂ν j) ≤
      B^(2*k-2)*(∫ y, kernelColumnEnergy μ h j y ∂ν j) := by
    intro j
    have hi := integral_mono_ae (hPower j) ((hEI j).const_mul (B^(2*k-2)))
      ((hColumn j).mono fun y hy ↦ nonnegative_power_square_envelope
        (kernelColumnEnergy μ h j y) B (hNonneg j y) hy k hk)
    simpa only [integral_const_mul] using hi
  calc
    _ ≤ ∑ j, B^(2*k-2)*(∫ y, kernelColumnEnergy μ h j y ∂ν j) :=
      Finset.sum_le_sum fun j _ ↦ hOne j
    _ = B^(2*k-2)*(∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) := by
      simp only [hIntegral,← Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hTrace (pow_nonneg hB _)

#print axioms DGRHS.Concentration.kernel_high_moment_envelope
#print axioms DGRHS.Concentration.kernel_column_energy_envelope
end DGRHS.Concentration
