import DGRHS.Gaussian.PeriodicUnshiftedMellinIntegrable
import DGRHS.Gaussian.PeriodicUnshiftedMellinScalar

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Exact Fourier coefficients of the actual
unshifted heat integral. Proper product integration precedes every Fubini step.
The scalar Gamma identity is checked separately; no physical Riesz
representative, common all-τ exceptional set or full torus factory is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicUnshiftedMellinHeatIntegrand_fourier_product_integrable (p τ : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) (k : PeriodicFrequency ι) :
    Integrable (fun q : ℝ × PeriodicTorus ι =>
      UnitAddTorus.mFourier (-k) q.2 * periodicUnshiftedMellinHeatIntegrand p τ q.1 q.2)
      ((volume.restrict (Ioi 0)).prod (periodicHaar ι)) := by
  apply (periodicUnshiftedMellinHeatIntegrand_product_integrable p τ hp hτ).norm.mono'
  · exact (((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_snd).mul
      (periodicUnshiftedMellinHeatIntegrand_measurable p τ)).aestronglyMeasurable
  · exact Eventually.of_forall (fun q => by
      simp only [norm_mul, periodic_mFourier_norm_apply, one_mul]
      exact le_rfl)

lemma periodicUnshiftedMellinHeatGreen_fourier_integral (p τ : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicUnshiftedMellinHeatGreen p τ x : ℂ)) k =
      ∫ u : ℝ in Ioi 0, ((u ^ p : ℝ) : ℂ) *
        ((Real.exp (-(u + τ) * ‖periodicFrequencyVector k‖ ^ 2) : ℂ) -
          if k = 0 then 1 else 0) := by
  rw [periodic_mFourierCoeff_eq_integral]
  simp_rw [periodicUnshiftedMellinHeatGreen_coe_integral p τ hτ, ← integral_const_mul]
  rw [← integral_integral_swap
    (periodicUnshiftedMellinHeatIntegrand_fourier_product_integrable p τ hp hτ k)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [periodicUnshiftedMellinHeatIntegrand]
  conv_lhs => arg 2; ext x; rw [mul_left_comm]
  rw [integral_const_mul, periodicGaussianHeat_centered_fourier (u + τ) (add_pos_of_pos_of_nonneg hu hτ)]

lemma periodicUnshiftedMellinHeatGreen_fourier_zero (p τ : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) :
    UnitAddTorus.mFourierCoeff
      (fun x : PeriodicTorus ι => (periodicUnshiftedMellinHeatGreen p τ x : ℂ)) 0 = 0 := by
  rw [periodicUnshiftedMellinHeatGreen_fourier_integral p τ hp hτ]
  simp [periodicFrequencyVector_zero]

theorem periodicUnshiftedMellinHeatGreen_fourier_nonzero (p τ : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) (k : PeriodicFrequency ι) (hk : k ≠ 0) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicUnshiftedMellinHeatGreen p τ x : ℂ)) k =
      ((Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) *
        ((1 / ‖periodicFrequencyVector k‖ ^ 2) ^ (p + 1) * Real.Gamma (p + 1)) : ℝ) : ℂ) := by
  rw [periodicUnshiftedMellinHeatGreen_fourier_integral p τ hp hτ]
  simp only [if_neg hk, sub_zero, ← Complex.ofReal_mul]
  have he : (fun u : ℝ => u ^ p * Real.exp (-(u + τ) * ‖periodicFrequencyVector k‖ ^ 2)) =
      fun u : ℝ => u ^ p * Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * (u + τ))) := by
    funext u
    congr 2
    ring
  calc
    _ = ((∫ u : ℝ in Ioi 0,
        u ^ p * Real.exp (-(u + τ) * ‖periodicFrequencyVector k‖ ^ 2) : ℝ) : ℂ) :=
      (@RCLike.ofRealLI ℂ _).integral_comp_comm _
    _ = _ := by
      congr 1
      rw [he]
      exact periodicUnshiftedMellin_laplace p τ _ hp
        (sq_pos_of_pos (periodicFrequency_norm_pos hk))

end DGRHS.Periodic
