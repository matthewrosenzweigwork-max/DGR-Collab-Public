import DGRHS.Gaussian.PeriodicD11Partition

noncomputable section
open MeasureTheory Filter
open scoped Convolution
namespace DGRHS.Periodic
open DGRHS.Gaussian.D11Imported.HighDim
open DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma periodicD11_centeredGreenEnergy_eq :
    (∫ x,(periodizedProfile x-1)*(∫ y,(periodizedProfile y-1)*periodicLogKernel (x-y)
      ∂periodicHaar (Fin 11)) ∂periodicHaar (Fin 11))=periodicD11GreenEnergy := by
  obtain ⟨B,hB⟩ := periodizedProfile_bounded
  have hrow (x : Torus 11) : Integrable (fun y => periodizedProfile y*periodicLogKernel (x-y))
      (periodicHaar (Fin 11)) :=
    (periodicLog_row_integrable x).bdd_mul periodizedProfile_measurable.aestronglyMeasurable
      (Eventually.of_forall hB)
  have hroweq (x : Torus 11) :
      (∫ y,(periodizedProfile y-1)*periodicLogKernel (x-y) ∂periodicHaar (Fin 11))=
        ∫ y,periodizedProfile y*periodicLogKernel (x-y) ∂periodicHaar (Fin 11) := by
    simp_rw [sub_mul,one_mul]
    rw [integral_sub (hrow x) (periodicLog_row_integrable x),periodicLog_row_mean_zero,sub_zero]
  have hj : Integrable (fun p : Torus 11 × Torus 11 => periodizedProfile p.2*periodicLogKernel (p.1-p.2))
      ((periodicHaar (Fin 11)).prod (periodicHaar (Fin 11))) :=
    periodizedProfile_integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) periodicLogKernel_integrable
  have hzero : (∫ x,∫ y,periodizedProfile y*periodicLogKernel (x-y)
      ∂periodicHaar (Fin 11) ∂periodicHaar (Fin 11))=0 := by
    rw [integral_integral_swap hj]
    simp_rw [integral_const_mul,integral_sub_right_eq_self,periodicLogKernel_integral_zero,mul_zero]
    simp
  have hw : Integrable (fun x => periodizedProfile x*
      (∫ y,periodizedProfile y*periodicLogKernel (x-y) ∂periodicHaar (Fin 11)))
      (periodicHaar (Fin 11)) := by
    simpa only [mul_assoc,integral_const_mul] using periodicD11_pair_integrable.integral_prod_left
  simp_rw [hroweq,sub_mul,one_mul]
  rw [integral_sub hw hj.integral_prod_left,hzero,sub_zero]
  rfl

/-- The original centered free energy of the literal wrapped-Cauchy competitor
is strictly negative below the displayed source ratio. -/
theorem periodic_d11_centered_negative_free_energy :
    (∫ x,periodizedProfile x*Real.log (periodizedProfile x) ∂periodicHaar (Fin 11))-
      ((8653/8680:ℝ)*periodicStabilityThreshold (Fin 11))/2*
      (∫ x,(periodizedProfile x-1)*(∫ y,(periodizedProfile y-1)*periodicLogKernel (x-y)
        ∂periodicHaar (Fin 11)) ∂periodicHaar (Fin 11))<0 := by
  rw [periodicD11_centeredGreenEnergy_eq]
  exact periodicD11_negative_free_energy_stronger

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicD11_centeredGreenEnergy_eq
#print axioms DGRHS.Periodic.periodic_d11_centered_negative_free_energy
