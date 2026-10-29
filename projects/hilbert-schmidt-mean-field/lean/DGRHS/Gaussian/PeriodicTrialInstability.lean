import DGRHS.Gaussian.PeriodicCosineConvolution

noncomputable section
open MeasureTheory
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- A genuine positive bounded normalized cosine trial has negative source
free energy above the actual Fourier stability threshold. No instability,
energy, entropy or asymptotic conclusion is a premise. -/
theorem exists_periodic_cosine_negative_free_energy (β : ℝ)
    (hβ : periodicStabilityThreshold ι < β) (i : ι) :
    ∃ ε : ℝ,0 < ε ∧ |ε| ≤ 1/2 ∧
      (∫ x,periodicCosineTrialDensity i ε x * Real.log (periodicCosineTrialDensity i ε x) ∂periodicHaar ι) -
        β/2*(∫ p : PeriodicTorus ι × PeriodicTorus ι,
          periodicCosineTrialDensity i ε p.1*periodicCosineTrialDensity i ε p.2*periodicLogKernel (p.1-p.2)
            ∂((periodicHaar ι).prod (periodicHaar ι))) < 0 := by
  let δ := β/periodicStabilityThreshold ι-1
  have hS : 0 < periodicStabilityThreshold ι := periodicStabilityThreshold_pos
  have hδ : 0 < δ := by
    dsimp [δ]
    have hratio : 1 < β/periodicStabilityThreshold ι := (lt_div_iff₀ hS).mpr (by simpa using hβ)
    linarith
  let ε := min (1/4:ℝ) (δ/32)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεsmall : ε ≤ δ/32 := min_le_right _ _
  have hεbound : |ε| ≤ 1/2 := by
    rw [abs_of_pos hε]
    exact (min_le_left _ _).trans (by norm_num)
  refine ⟨ε,hε,hεbound,?_⟩
  rw [periodicLog_cosine_trial_pair_energy i ε hεbound]
  have hEnt := periodicCosineTrial_entropy_bound i ε hεbound
  rw [abs_of_pos hε] at hEnt
  have hE : β/2*(ε^2/(2*periodicStabilityThreshold ι)) = (δ+1)*ε^2/4 := by
    dsimp [δ]
    ring
  rw [hE]
  have hc : 4*ε^3 ≤ δ*ε^2/8 := by
    have h := mul_le_mul_of_nonneg_right hεsmall (sq_nonneg ε)
    nlinarith
  have hp : 0 < δ*ε^2 := mul_pos hδ (sq_pos_of_pos hε)
  nlinarith

end DGRHS.Periodic
#print axioms DGRHS.Periodic.exists_periodic_cosine_negative_free_energy
#check @DGRHS.Periodic.exists_periodic_cosine_negative_free_energy
