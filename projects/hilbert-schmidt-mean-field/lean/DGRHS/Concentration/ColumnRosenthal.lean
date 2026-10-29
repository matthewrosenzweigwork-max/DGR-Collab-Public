import DGRHS.Concentration.KernelEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

def parameterEnergy {Ω Ψ : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) (h : Fin n → Ω × Ψ → ℝ) (y : Ψ) : ℝ :=
  ∑ i, ∫ x, (h i (x,y))^2 ∂μ i

/-- Reversed conditional Rosenthal, integrated against the actual parameter law.
All parameter section/outer moments and the energy power are proved integrable. -/
theorem column_rosenthal_integrated {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n : ℕ} (μ : Fin n → Measure Ω) (ν : Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (h : Fin n → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i, AEStronglyMeasurable (h i) ((μ i).prod ν))
    (hBound : ∀ i, ∀ᵐ p ∂(μ i).prod ν, |h i p| ≤ A)
    (hMean : ∀ i, ∀ᵐ y ∂ν, ∫ x, h i (x,y) ∂μ i = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ p : (Fin n → Ω) × Ψ, |∑ i, h i (p.1 i,p.2)|^(2*k)
      ∂(Measure.pi μ).prod ν) ≤
    (6*Real.sqrt ((2*k : ℕ) : ℝ))^(2*k)*(∫ y, (parameterEnergy μ h y)^k ∂ν)+
    (6*((2*k : ℕ) : ℝ))^(2*k)*(∑ i, ∫ p, |h i p|^(2*k) ∂(μ i).prod ν) := by
  classical
  have hRows : ∀ᵐ y ∂ν, ∀ i,
      AEStronglyMeasurable (fun x ↦ h i (x,y)) (μ i) ∧
      (∀ᵐ x ∂μ i, |h i (x,y)| ≤ A) ∧
      (∫ x, h i (x,y) ∂μ i) = 0 := by
    apply ae_all_iff.mpr
    intro i
    have hSwap : ∀ᵐ p ∂ν.prod (μ i), |h i p.swap| ≤ A :=
      (Measure.measurePreserving_swap (μ := ν) (ν := μ i)).quasiMeasurePreserving.ae (hBound i)
    filter_upwards [(hAES i).prod_swap.prodMk_left,
      Measure.ae_ae_of_ae_prod hSwap, hMean i] with y hy hb hm
    exact ⟨hy,hb,hm⟩
  have hJoint : Integrable (fun p : (Fin n → Ω) × Ψ ↦ |∑ i, h i (p.1 i,p.2)|^(2*k))
      ((Measure.pi μ).prod ν) := by
    simpa only [kernelColumnSum] using kernel_column_joint_moment_integrable
      μ (fun _ : Fin 1 ↦ ν) (fun i _ ↦ h i) A (fun i _ ↦ hAES i)
      (fun i _ ↦ hBound i) 0 (2*k)
  have hHigh := fun i ↦ bounded_kernel_abs_moment_integrable (μ i) ν (h i) A
    (hAES i) (hBound i) (2*k)
  have hSquare : ∀ i, Integrable (fun p ↦ (h i p)^2) ((μ i).prod ν) := fun i ↦ by
    simpa only [sq_abs] using bounded_kernel_abs_moment_integrable (μ i) ν (h i) A
      (hAES i) (hBound i) 2
  have hEI : Integrable (parameterEnergy μ h) ν := by
    change Integrable (fun y ↦ ∑ i, ∫ x, (h i (x,y))^2 ∂μ i) ν
    simpa only [Finset.sum_apply] using integrable_finsetSum Finset.univ
      (fun i _ ↦ (hSquare i).integral_prod_right)
  have hENonneg : ∀ y, 0 ≤ parameterEnergy μ h y := fun y ↦
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  have hEBound : ∀ᵐ y ∂ν, |parameterEnergy μ h y| ≤ (n : ℝ)*A^2 := by
    filter_upwards [hRows] with y hy
    have hOne : ∀ i, (∫ x, (h i (x,y))^2 ∂μ i) ≤ A^2 := by
      intro i
      have hi : Integrable (fun x ↦ (h i (x,y))^2) (μ i) := by
        apply integrable_of_ae_abs_le ((hy i).1.fun_pow 2)
        filter_upwards [(hy i).2.1] with x hx
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      have ht := integral_mono_ae hi (integrable_const (A^2))
        ((hy i).2.1.mono fun x hx ↦ by simpa only [sq_abs] using
          (pow_le_pow_left₀ (abs_nonneg _) hx 2))
      simpa using ht
    rw [abs_of_nonneg (hENonneg y)]
    simpa [parameterEnergy] using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hOne i)
  have hEPower : Integrable (fun y ↦ (parameterEnergy μ h y)^k) ν := by
    apply integrable_of_ae_abs_le (hEI.aestronglyMeasurable.fun_pow k)
    filter_upwards [hEBound] with y hy
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hy k
  have hOuter := integrable_finsetSum Finset.univ (fun i _ ↦ (hHigh i).integral_prod_right)
  have hp : ∀ᵐ y ∂ν,
      (∫ ω, |∑ i, h i (ω i,y)|^(2*k) ∂Measure.pi μ) ≤
      (6*Real.sqrt ((2*k : ℕ) : ℝ))^(2*k)*(parameterEnergy μ h y)^k+
      (6*((2*k : ℕ) : ℝ))^(2*k)*(∑ i, ∫ x, |h i (x,y)|^(2*k) ∂μ i) := by
    filter_upwards [hRows] with y hy
    have hMom : ∀ i, Integrable (fun x ↦ |h i (x,y)|^(2*k)) (μ i) := by
      intro i
      have ha : AEStronglyMeasurable (fun x ↦ |h i (x,y)|) (μ i) := by
        simpa only [Real.norm_eq_abs] using (hy i).1.norm
      apply integrable_of_ae_abs_le (ha.fun_pow (2*k))
      filter_upwards [(hy i).2.1] with x hx
      rw [abs_pow,abs_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx _
    have hr := scalar_even_rosenthal_pi μ (fun i x ↦ h i (x,y)) k hk
      (fun i ↦ (hy i).1) hMom (fun i ↦ (hy i).2.2)
    exact rosenthal_root_to_power (integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg _) _)
      (hENonneg y) (Finset.sum_nonneg fun i _ ↦ integral_nonneg fun x ↦ pow_nonneg (abs_nonneg _) _)
      k hk hr
  have hb := integral_mono_ae hJoint.integral_prod_right
    ((hEPower.const_mul _).add (hOuter.const_mul _)) hp
  rw [← integral_prod_symm _ hJoint] at hb
  simp only [Pi.add_apply] at hb
  rw [integral_add (hEPower.const_mul _) (hOuter.const_mul _),integral_const_mul,
    integral_const_mul,integral_finsetSum _ (fun i _ ↦ (hHigh i).integral_prod_right)] at hb
  simpa only [← integral_prod_symm _ (hHigh _)] using hb

#print axioms DGRHS.Concentration.column_rosenthal_integrated
end DGRHS.Concentration
