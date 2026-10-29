import DGRHS.Gaussian.PeriodicPhysicalGreenFourier
import DGRHS.Gaussian.PeriodicL1FourierUniqueness
import DGRHS.Gaussian.PeriodicSupercriticalPartition

/-! Identification of the constructed physical Green function with the exact
source spectral kernel, and transfer to every actual finite-particle partition.
No kernel equality, properness, or comparison is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The heat construction is the manuscript's actual Fourier Green kernel. -/
theorem periodicPhysicalGreen_eq_kernel_ae :
    periodicPhysicalGreen (ι := ι)=ᵐ[periodicHaar ι]periodicLogKernel := by
  have h := periodicL1_fourier_unique (fun x : PeriodicTorus ι => (periodicPhysicalGreen x:ℂ))
    (fun x => (periodicLogKernel x:ℂ)) periodicPhysicalGreen_integrable.ofReal
    periodicLogKernel_integrable.ofReal (fun k =>
      (periodicPhysicalGreen_fourierCoeff k).trans (periodicLogKernel_fourierCoeff k).symm)
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx

lemma periodicPhysicalGreen_memLp : MemLp (periodicPhysicalGreen (ι := ι)) 2 (periodicHaar ι) :=
  (memLp_congr_ae periodicPhysicalGreen_eq_kernel_ae).mpr periodicLogKernel_memLp

lemma periodicPhysicalGreen_integral_zero :
    (∫ x,periodicPhysicalGreen (ι := ι) x ∂periodicHaar ι)=0 :=
  (integral_congr_ae periodicPhysicalGreen_eq_kernel_ae).trans periodicLogKernel_integral_zero

lemma periodicPhysicalGreen_pair_eq_ae :
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicPhysicalGreen (p.1-p.2)) =ᵐ[(periodicHaar ι).prod (periodicHaar ι)]
      (fun p => periodicLogKernel (p.1-p.2)) :=
  (periodicHaar_preserving_difference (ι := ι)).quasiMeasurePreserving.ae periodicPhysicalGreen_eq_kernel_ae

lemma periodicPhysicalGreen_offdiagonal_eq_ae (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus ι ∂Measure.pi (fun _ : Fin N => periodicHaar ι),
      ∀ i j : Fin N,i≠j → periodicPhysicalGreen (x i-x j)=periodicLogKernel (x i-x j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i=j
  · exact Eventually.of_forall (fun _ h => False.elim (h hij))
  · have h := (DGRHS.Decoupling.pair_eval_measurePreserving (periodicHaar ι) i j hij).quasiMeasurePreserving.ae
      periodicPhysicalGreen_pair_eq_ae
    exact h.mono (fun _ hx _ => hx)

/-- The exact source partition equals the physical Green partition for every
N and beta, including infinite partitions; no collision set is discarded by
an unjustified pointwise replacement. -/
theorem periodicAttractivePartition_eq_physical (β : ℝ) (N : ℕ) :
    periodicAttractivePartition (ι := ι) β N =
      ∫⁻ x : Fin N → PeriodicTorus ι,ENNReal.ofReal (Real.exp
        (β/(2*(N:ℝ))*∑ i,∑ j,if i=j then 0 else periodicPhysicalGreen (x i-x j)))
        ∂Measure.pi (fun _ : Fin N => periodicHaar ι) := by
  apply lintegral_congr_ae
  filter_upwards [periodicPhysicalGreen_offdiagonal_eq_ae (ι := ι) N] with x hx
  congr 2
  unfold periodicParticleExponent
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · simp [hij]
  · simp only [if_neg hij,hx i j hij]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicPhysicalGreen_eq_kernel_ae
#print axioms DGRHS.Periodic.periodicPhysicalGreen_memLp
#print axioms DGRHS.Periodic.periodicAttractivePartition_eq_physical
#check @DGRHS.Periodic.periodicPhysicalGreen_eq_kernel_ae
#check @DGRHS.Periodic.periodicAttractivePartition_eq_physical
