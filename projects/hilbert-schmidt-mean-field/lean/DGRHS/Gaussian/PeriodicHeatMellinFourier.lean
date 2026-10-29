import DGRHS.Gaussian.PeriodicHeatMellinIntegrable
import DGRHS.Gaussian.PeriodicHeatMellinLaplace

/-! Exact Fourier coefficients of the actual translated Mellin heat
integral, with every interchange justified by proper product integration. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicMellinHeatIntegrand_fourier_product_integrable (p τ : ℝ) (hp : 0≤p) (hτ : 0≤τ)
    (k : PeriodicFrequency ι) :
    Integrable (fun q : ℝ × PeriodicTorus ι =>
      UnitAddTorus.mFourier (-k) q.2*periodicMellinHeatIntegrand p τ q.1 q.2)
      ((volume.restrict (Ioi 0)).prod (periodicHaar ι)) := by
  apply (periodicMellinHeatIntegrand_product_integrable p τ hp hτ).norm.mono'
  · exact (((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_snd).mul
      (periodicMellinHeatIntegrand_measurable p τ)).aestronglyMeasurable
  · exact Eventually.of_forall (fun q => by
      simp only [norm_mul,periodic_mFourier_norm_apply,one_mul];exact le_rfl)

lemma periodicMellinHeatGreen_fourier_integral (p τ : ℝ) (hp : 0≤p) (hτ : 0≤τ)
    (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicMellinHeatGreen p τ x:ℂ)) k =
      ∫ s : ℝ in Ioi 0,(periodicHeatMellinWeight p τ s:ℂ)*
        ((Real.exp (-s*‖periodicFrequencyVector k‖^2):ℂ)-if k=0 then 1 else 0) := by
  rw [periodic_mFourierCoeff_eq_integral]
  simp_rw [periodicMellinHeatGreen_coe_integral,← integral_const_mul]
  rw [← integral_integral_swap (periodicMellinHeatIntegrand_fourier_product_integrable p τ hp hτ k)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  simp only [periodicMellinHeatIntegrand]
  conv_lhs => arg 2;ext x;rw [mul_left_comm]
  rw [integral_const_mul,periodicGaussianHeat_centered_fourier s hs]

lemma periodicMellinHeatGreen_fourier_zero (p τ : ℝ) (hp : 0≤p) (hτ : 0≤τ) :
    UnitAddTorus.mFourierCoeff (fun x : PeriodicTorus ι => (periodicMellinHeatGreen p τ x:ℂ)) 0=0 := by
  rw [periodicMellinHeatGreen_fourier_integral p τ hp hτ]
  simp [periodicFrequencyVector_zero]

/-- Actual coefficients, including the exact heat multiplier. -/
theorem periodicMellinHeatGreen_fourier_nonzero (p τ : ℝ) (hp : 0≤p) (hτ : 0≤τ)
    (k : PeriodicFrequency ι) (hk : k≠0) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicMellinHeatGreen p τ x:ℂ)) k =
      ((Real.exp (-(‖periodicFrequencyVector k‖^2*τ))*
        ((1/‖periodicFrequencyVector k‖^2)^(p+1)*Real.Gamma (p+1)):ℝ):ℂ) := by
  rw [periodicMellinHeatGreen_fourier_integral p τ hp hτ]
  simp only [if_neg hk,sub_zero,← Complex.ofReal_mul]
  have he : (fun s : ℝ => periodicHeatMellinWeight p τ s*Real.exp (-s*‖periodicFrequencyVector k‖^2)) =
      fun s : ℝ => periodicHeatMellinWeight p τ s*Real.exp (-(‖periodicFrequencyVector k‖^2*s)) := by
    funext s;congr 2;ring
  calc
    _ = ((∫ s : ℝ in Ioi 0,periodicHeatMellinWeight p τ s*Real.exp (-s*‖periodicFrequencyVector k‖^2):ℝ):ℂ) :=
      (@RCLike.ofRealLI ℂ _).integral_comp_comm _
    _ = _ := by
      congr 1
      rw [he]
      exact periodicHeatMellinWeight_laplace p τ _ (by linarith) hτ (sq_pos_of_pos (periodicFrequency_norm_pos hk))


end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicMellinHeatGreen_fourier_zero
#print axioms DGRHS.Periodic.periodicMellinHeatGreen_fourier_nonzero
#check @DGRHS.Periodic.periodicMellinHeatGreen_fourier_nonzero
