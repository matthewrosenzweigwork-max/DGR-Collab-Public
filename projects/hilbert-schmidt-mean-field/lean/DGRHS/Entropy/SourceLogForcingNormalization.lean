/- Exact logarithmic Appendix forcing normalization. Partition upper constants
may be chosen at least one. Jensen's actual lower bound then cancels the
exp(-beta I) factor in Cem; Cem itself need not be at least one. -/
import DGRHS.Entropy.SourceLogPartitionBounds
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy

theorem log_prefactor_forcing_nonnegative (m Cpf B : ℝ)
    (hCpf : Real.exp m ≤ Cpf) (hB : 1 ≤ B) :
    0 ≤ Real.log Cpf + Real.log (Real.exp (-m) * B) := by
  have hp : 0 < Cpf := lt_of_lt_of_le (Real.exp_pos m) hCpf
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hc : Real.exp m * Real.exp (-m) = 1 := by rw [← Real.exp_add]; simp
  have hbase : 1 ≤ Cpf * Real.exp (-m) := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_right hCpf (Real.exp_pos _).le
  have hprod : 1 ≤ Cpf * (Real.exp (-m) * B) := by
    calc
      1 ≤ (Cpf * Real.exp (-m)) * B := by
        simpa only [one_mul] using mul_le_mul hbase hB zero_le_one
          (zero_le_one.trans hbase)
      _ = _ := by ring
  rw [← Real.log_mul hp.ne' (mul_pos (Real.exp_pos _) hBp).ne']
  exact Real.log_nonneg hprod

theorem log_small_Cem_forcing_nonnegative (m Cpf L : ℝ)
    (hCpf : Real.exp m ≤ Cpf) (hL : 0 ≤ L) :
    0 ≤ Real.log Cpf + Real.log (Real.exp (-m) * (Real.exp 1 + L)) := by
  apply log_prefactor_forcing_nonnegative m Cpf _ hCpf
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  linarith

theorem log_large_Cem_forcing_nonnegative (m Cpf L Cub : ℝ)
    (hCpf : Real.exp m ≤ Cpf) (hL : 0 ≤ L) (hCub : 1 ≤ Cub) :
    0 ≤ Real.log Cpf +
      Real.log (Real.exp (-m) * Real.sqrt (Real.exp 1 + L) * Real.sqrt Cub) := by
  have he : 1 ≤ Real.exp 1 + L := by
    have := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hB : 1 ≤ Real.sqrt (Real.exp 1 + L) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt he
  have hC : 1 ≤ Real.sqrt Cub := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hCub
  simpa only [mul_assoc] using log_prefactor_forcing_nonnegative m Cpf
    (Real.sqrt (Real.exp 1 + L) * Real.sqrt Cub) hCpf
      (by simpa only [one_mul] using mul_le_mul hB hC zero_le_one (zero_le_one.trans hB))

open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLogPartition_original_bounds_one_le (β : ℝ≥0)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ Cpf : ℝ, 1 ≤ Cpf ∧ ∀ N : ℕ, 1 ≤ N →
      Real.exp ((β : ℝ) * DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
        (fun a b => logPhysicalPair (a,b))) ≤ (sourceLogSingularPartition β ρ N).toReal ∧
      (sourceLogSingularPartition β ρ N).toReal ≤ Cpf := by
  obtain ⟨C, _, hC⟩ := sourceLogPartition_original_bounds β hd ρ M hM hρ hpair
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro N hN
  exact ⟨(hC N hN).1, (hC N hN).2.trans (le_max_left _ _)⟩

end DGRHS.Entropy
#check @DGRHS.Entropy.log_prefactor_forcing_nonnegative
#check @DGRHS.Entropy.log_small_Cem_forcing_nonnegative
#check @DGRHS.Entropy.log_large_Cem_forcing_nonnegative
#check @DGRHS.Entropy.sourceLogPartition_original_bounds_one_le
#print axioms DGRHS.Entropy.log_prefactor_forcing_nonnegative
#print axioms DGRHS.Entropy.log_small_Cem_forcing_nonnegative
#print axioms DGRHS.Entropy.log_large_Cem_forcing_nonnegative
#print axioms DGRHS.Entropy.sourceLogPartition_original_bounds_one_le
