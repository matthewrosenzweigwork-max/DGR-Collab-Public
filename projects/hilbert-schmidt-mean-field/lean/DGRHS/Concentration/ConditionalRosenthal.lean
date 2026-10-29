import DGRHS.Concentration.Rosenthal
import DGRHS.Concentration.Hilbert

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

/-- The scalar theorem instantiated on the actual finite product law. Full coordinate
independence and all evaluation-law/integrability bridges are proved here. -/
theorem scalar_even_rosenthal_pi {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : Fin n → Ω → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hX : ∀ i, AEStronglyMeasurable (X i) (μ i))
    (hh : ∀ i, Integrable (fun x ↦ |X i x|^(2*k)) (μ i))
    (hc : ∀ i, ∫ x, X i x ∂μ i = 0) :
    (∫ ω, |∑ i, X i (ω i)|^(2*k) ∂Measure.pi μ)^(1/((2*k : ℕ) : ℝ)) ≤
      3*(Real.sqrt ((2*k : ℕ) : ℝ)*Real.sqrt (∑ i, ∫ x, (X i x)^2 ∂μ i) +
        ((2*k : ℕ) : ℝ)*(∑ i, ∫ x, |X i x|^(2*k) ∂μ i)^(1/((2*k : ℕ) : ℝ))) := by
  have hInd := iIndepFun_pi (fun i ↦ (hX i).aemeasurable)
  have hEval : ∀ i, AEStronglyMeasurable (fun ω : Fin n → Ω ↦ X i (ω i))
      (Measure.pi μ) := fun i ↦ (hX i).comp_quasiMeasurePreserving
        (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving
  have hHigh : ∀ i, Integrable (fun ω : Fin n → Ω ↦ |X i (ω i)|^(2*k))
      (Measure.pi μ) := fun i ↦ integrable_comp_eval
        (μ := μ) (i := i) (f := fun x ↦ |X i x|^(2*k)) (hh i)
  have hMean : ∀ i, ∫ ω : Fin n → Ω, X i (ω i) ∂Measure.pi μ = 0 := fun i ↦ by
    rw [integral_comp_eval (hX i), hc i]
  have ht := scalar_even_rosenthal_integrable (Measure.pi μ) (fun i ω ↦ X i (ω i))
    k hk hInd hEval hHigh hMean
  have hAbs : ∀ i, AEStronglyMeasurable (fun x ↦ |X i x|) (μ i) := fun i ↦ by
    simpa only [Real.norm_eq_abs] using (hX i).norm
  have hSq : ∀ i, (∫ ω : Fin n → Ω, (X i (ω i))^2 ∂Measure.pi μ) =
      ∫ x, (X i x)^2 ∂μ i := fun i ↦ integral_comp_eval (μ := μ)
        (i := i) (f := fun x ↦ (X i x)^2) ((hX i).fun_pow 2)
  have hPow : ∀ i, (∫ ω : Fin n → Ω, |X i (ω i)|^(2*k) ∂Measure.pi μ) =
      ∫ x, |X i x|^(2*k) ∂μ i := fun i ↦ integral_comp_eval (μ := μ)
        (i := i) (f := fun x ↦ |X i x|^(2*k)) ((hAbs i).fun_pow (2*k))
  simpa only [hSq, hPow] using ht

def kernelColumnSum {Ω Ψ : Type*} {n r : ℕ}
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (ω : Fin n → Ω) (j : Fin r) (y : Ψ) : ℝ :=
  ∑ i, h i j (ω i,y)

/-- Actual canonical bounded sections for the second-coordinate Rosenthal step. -/
lemma kernel_column_sections {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n r : ℕ} (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMean : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0) :
    ∀ᵐ ω ∂Measure.pi μ, ∀ j,
      AEStronglyMeasurable (kernelColumnSum h ω j) (ν j) ∧
      (∀ᵐ y ∂ν j, |kernelColumnSum h ω j y| ≤ (n : ℝ)*A) ∧
      (∫ y, kernelColumnSum h ω j y ∂ν j) = 0 := by
  classical
  have hRow : ∀ i, ∀ᵐ x ∂μ i, ∀ j,
      AEStronglyMeasurable (fun y ↦ h i j (x,y)) (ν j) ∧
      (∀ᵐ y ∂ν j, |h i j (x,y)| ≤ A) ∧
      (∫ y, h i j (x,y) ∂ν j) = 0 := by
    intro i
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(hAES i j).prodMk_left,
      Measure.ae_ae_of_ae_prod (hBound i j), hMean i j] with x hx hb hm
    exact ⟨hx,hb,hm⟩
  have hAll : ∀ᵐ ω ∂Measure.pi μ, ∀ i j,
      AEStronglyMeasurable (fun y ↦ h i j (ω i,y)) (ν j) ∧
      (∀ᵐ y ∂ν j, |h i j (ω i,y)| ≤ A) ∧
      (∫ y, h i j (ω i,y) ∂ν j) = 0 :=
    ae_all_iff.mpr fun i ↦ (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae
      (hRow i)
  filter_upwards [hAll] with ω hω
  intro j
  have hI : ∀ i, Integrable (fun y ↦ h i j (ω i,y)) (ν j) := fun i ↦
    integrable_of_ae_abs_le (hω i j).1 (hω i j).2.1
  have hSumI := integrable_finsetSum Finset.univ (fun i _ ↦ hI i)
  refine ⟨?_, ?_, ?_⟩
  · change AEStronglyMeasurable (fun y ↦ ∑ i, h i j (ω i,y)) (ν j)
    simpa only [Finset.sum_apply] using hSumI.aestronglyMeasurable
  · have hall : ∀ᵐ y ∂ν j, ∀ i, |h i j (ω i,y)| ≤ A :=
      ae_all_iff.mpr fun i ↦ (hω i j).2.1
    filter_upwards [hall] with y hy
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa using (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hy i)))
  · change (∫ y, ∑ i, h i j (ω i,y) ∂ν j) = 0
    rw [integral_finsetSum _ (fun i _ ↦ hI i)]
    simp [(hω _ j).2.2]

/-- Conditional scalar Rosenthal with the actual section laws and all high moments
provided by the bounded canonical kernel, including empty index sets. -/
theorem conditional_kernel_rosenthal {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n r : ℕ} (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMean : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ ω ∂Measure.pi μ,
      (∫ ξ, |∑ j, kernelColumnSum h ω j (ξ j)|^(2*k) ∂Measure.pi ν)^
        (1/((2*k : ℕ) : ℝ)) ≤
      3*(Real.sqrt ((2*k : ℕ) : ℝ)*
        Real.sqrt (∑ j, ∫ y, (kernelColumnSum h ω j y)^2 ∂ν j) +
        ((2*k : ℕ) : ℝ)*(∑ j, ∫ y, |kernelColumnSum h ω j y|^(2*k) ∂ν j)^
          (1/((2*k : ℕ) : ℝ))) := by
  filter_upwards [kernel_column_sections μ ν h A hAES hBound hMean] with ω hω
  apply scalar_even_rosenthal_pi ν (kernelColumnSum h ω) k hk
    (fun j ↦ (hω j).1) _ (fun j ↦ (hω j).2.2)
  intro j
  have hAbs : AEStronglyMeasurable (fun y ↦ |kernelColumnSum h ω j y|) (ν j) := by
    simpa only [Real.norm_eq_abs] using (hω j).1.norm
  apply integrable_of_ae_abs_le (hAbs.fun_pow (2*k))
  filter_upwards [(hω j).2.1] with y hy
  rw [abs_pow, abs_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hy _

#print axioms DGRHS.Concentration.scalar_even_rosenthal_pi
#print axioms DGRHS.Concentration.kernel_column_sections
#print axioms DGRHS.Concentration.conditional_kernel_rosenthal
end DGRHS.Concentration
