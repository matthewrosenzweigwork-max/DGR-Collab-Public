import DGRHS.Concentration.ColumnRosenthal

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

/-- Both actual conditional Rosenthal steps and the deterministic A/B envelopes.
The sole remaining moment term is the genuine row-Hilbert variance expression. -/
theorem scalar_even_moment_reduction {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n r : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (hColumn : ∀ j, ∀ᵐ y ∂ν j, kernelColumnEnergy μ h j y ≤ B^2)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (k : ℕ) (hk : 1 ≤ k) :
    let m := 2*k
    let c := (6*Real.sqrt (m : ℝ))^m
    let d := (6*(m : ℝ))^m
    (∫ p, |kernelDecoupledSum h p|^m ∂(Measure.pi μ).prod (Measure.pi ν)) ≤
      c*(∫ ω, (kernelColumnVariance ν h ω)^k ∂Measure.pi μ)+
      d*(c*B^(m-2)*C^2+d*A^(m-2)*C^2) := by
  classical
  dsimp only
  let m := 2*k
  let c := (6*Real.sqrt (m : ℝ))^m
  let d := (6*(m : ℝ))^m
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hCols : ∀ j, (∫ p : (Fin n → Ω) × Ψ, |kernelColumnSum h p.1 j p.2|^m
      ∂(Measure.pi μ).prod (ν j)) ≤
      c*(∫ y, (kernelColumnEnergy μ h j y)^k ∂ν j)+
      d*(∑ i, ∫ p, |h i j p|^m ∂(μ i).prod (ν j)) := by
    intro j
    exact column_rosenthal_integrated μ (ν j) (fun i ↦ h i j) A
      (fun i ↦ hAES i j) (fun i ↦ hBound i j) (fun i ↦ hMeanLeft i j) k hk
  have hEnergy := kernel_column_energy_envelope μ ν h A B C hB hAES hBound hColumn hTrace k hk
  have hHigh := kernel_high_moment_envelope μ ν h A C hA hAES hBound hTrace m
    (by dsimp [m]; omega)
  have hSum : (∑ j, ∫ p : (Fin n → Ω) × Ψ, |kernelColumnSum h p.1 j p.2|^m
      ∂(Measure.pi μ).prod (ν j)) ≤ c*B^(m-2)*C^2+d*A^(m-2)*C^2 := by
    calc
      _ ≤ ∑ j, (c*(∫ y, (kernelColumnEnergy μ h j y)^k ∂ν j)+
        d*(∑ i, ∫ p, |h i j p|^m ∂(μ i).prod (ν j))) :=
        Finset.sum_le_sum fun j _ ↦ hCols j
      _ = c*(∑ j, ∫ y, (kernelColumnEnergy μ h j y)^k ∂ν j)+
        d*(∑ i, ∑ j, ∫ p, |h i j p|^m ∂(μ i).prod (ν j)) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,Finset.sum_comm]
      _ ≤ c*(B^(m-2)*C^2)+d*(A^(m-2)*C^2) :=
        add_le_add (mul_le_mul_of_nonneg_left hEnergy hc) (mul_le_mul_of_nonneg_left hHigh hd)
      _ = _ := by ring
  have hFirst := integrated_kernel_rosenthal μ ν h A hAES hBound hMeanRight k hk
  exact hFirst.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hSum hd))

#check @DGRHS.Concentration.scalar_even_moment_reduction
#print axioms DGRHS.Concentration.scalar_even_moment_reduction
end DGRHS.Concentration
