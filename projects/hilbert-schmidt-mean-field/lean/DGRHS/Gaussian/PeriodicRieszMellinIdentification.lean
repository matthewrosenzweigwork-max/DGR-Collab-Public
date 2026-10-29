import DGRHS.Gaussian.PeriodicRieszHeatL2
import DGRHS.Gaussian.PeriodicUnshiftedMellinFourier
import DGRHS.Gaussian.PeriodicL1FourierUniqueness

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Exact real-power coefficient algebra and proper
Mellin-to-L2 identification. Source478–484 prescribes |x|^(-s)/s; source492–496
uses its periodic spectral counterpart. This module proves a Gaussian-Laplace
normalization and the selected spectral multiplier. A Euclidean-to-periodic
local singularity/periodization theorem is not silently inferred from it. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal lp Topology
namespace DGRHS.Periodic
universe u

lemma periodic_inverse_square_rpow (r a : ℝ) (hr : 0 ≤ r) :
    (1 / r ^ 2) ^ a = r ^ (-2 * a) := by
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_two r,
    ← Real.rpow_mul hr]
  congr 1
  ring

/-- Actual proper scalar Gaussian representation of the source Riesz power. -/
lemma sourceRiesz_gaussian_laplace (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (∫ v : ℝ in Ioi 0, v ^ (s / 2 - 1) * Real.exp (-(r ^ 2 * v))) =
      Real.Gamma (s / 2) * r ^ (-s) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : 0 < s / 2)
    (sq_pos_of_pos hr), periodic_inverse_square_rpow r (s / 2) hr.le]
  rw [show -2 * (s / 2) = -s by ring]
  ring

lemma sourceRiesz_gaussian_laplace_integrable (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => v ^ (s / 2 - 1) * Real.exp (-(r ^ 2 * v))) (Ioi 0) := by
  have h := periodicUnshiftedMellin_integrable (s / 2 - 1) 0 (r ^ 2)
    (by linarith) (sq_pos_of_pos hr)
  simpa only [add_zero] using h

lemma sourceRiesz_gaussian_laplace_normalized (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (1 / (s * Real.Gamma (s / 2))) *
      (∫ v : ℝ in Ioi 0, v ^ (s / 2 - 1) * Real.exp (-(r ^ 2 * v))) = r ^ (-s) / s := by
  rw [sourceRiesz_gaussian_laplace s r hs hr]
  have hG : Real.Gamma (s / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp [hs.ne', hG]

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- This selected kernel is the actual real proper-time integral, not a supplied
abstract Fourier representative. The zero heat shift is included. -/
def periodicRieszMellinGreen (s τ : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicRieszMellinFactor ι s *
    periodicUnshiftedMellinHeatGreen (((Fintype.card ι : ℝ) - s) / 2 - 1) τ x

lemma periodicRieszMellinGreen_integrable (s τ : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) :
    Integrable (periodicRieszMellinGreen (ι := ι) s τ) (periodicHaar ι) :=
  (periodicUnshiftedMellinHeatGreen_integrable _ τ
    (periodicUnshiftedMellin_spectralExponent _ s hsd) hτ).const_mul _

lemma periodic_mFourierCoeff_real_const_mul (c : ℝ) (f : PeriodicTorus ι → ℝ)
    (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => ((c * f x : ℝ) : ℂ)) k =
      (c : ℂ) * UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k := by
  simp only [periodic_mFourierCoeff_eq_integral, Complex.ofReal_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by ring)

lemma periodicRieszMellinGreen_fourier (s τ : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicRieszMellinGreen s τ x : ℂ)) k =
      periodicRieszHeatFourierCoeff s τ k := by
  unfold periodicRieszMellinGreen
  rw [periodic_mFourierCoeff_real_const_mul]
  have hp := periodicUnshiftedMellin_spectralExponent (Fintype.card ι : ℝ) s hsd
  by_cases hk : k = 0
  · subst k
    rw [periodicUnshiftedMellinHeatGreen_fourier_zero _ τ hp hτ]
    simp
  · rw [periodicUnshiftedMellinHeatGreen_fourier_nonzero _ τ hp hτ k hk]
    simp only [sub_add_cancel]
    rw [periodic_inverse_square_rpow _ _ (norm_nonneg _)]
    rw [show -2 * (((Fintype.card ι : ℝ) - s) / 2) = s - (Fintype.card ι : ℝ) by ring]
    simp only [periodicRieszHeatFourierCoeff, periodicRieszFourierCoeff, if_neg hk,
      periodicRieszFourierAmplitude, Complex.ofReal_mul]
    ring

/-- L1 uniqueness identifies the genuine Mellin integral with the independently
constructed L2 class. No desired identity or kernel properness is a premise. -/
theorem periodicRieszMellinGreen_coe_ae_heatL2 (s τ : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) :
    (fun x => (periodicRieszMellinGreen s τ x : ℂ)) =ᵐ[periodicHaar ι]
      periodicRieszHeatL2 s τ hs hτ := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  apply periodicL1_fourier_unique _ _
    (periodicRieszMellinGreen_integrable s τ hsd hτ).ofReal
    (MemLp.integrable (by norm_num) (Lp.memLp _))
  intro k
  exact (periodicRieszMellinGreen_fourier (ι := ι) s τ hsd hτ k).trans
    (periodicRieszHeatL2_fourierCoeff (ι := ι) s τ hs hτ k).symm

lemma periodicRieszHeatL2_zero_time (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    periodicRieszHeatL2 s 0 hs (le_refl 0) = periodicRieszL2 s hs := by
  apply periodicRieszL2_unique
  intro k
  rw [periodicRieszHeatL2_fourierCoeff, periodicRieszHeatFourierCoeff_zero_time]

theorem periodicRieszMellinGreen_coe_ae_L2 (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    (fun x => (periodicRieszMellinGreen s 0 x : ℂ)) =ᵐ[periodicHaar ι]
      periodicRieszL2 s hs := by
  simpa only [periodicRieszHeatL2_zero_time] using
    periodicRieszMellinGreen_coe_ae_heatL2 s 0 hs (le_refl 0)

theorem periodicRieszMellinGreen_memLp (s τ : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) :
    MemLp (periodicRieszMellinGreen (ι := ι) s τ) 2 (periodicHaar ι) := by
  have h : MemLp (fun x => (periodicRieszMellinGreen s τ x : ℂ)) 2 (periodicHaar ι) :=
    (memLp_congr_ae (periodicRieszMellinGreen_coe_ae_heatL2 s τ hs hτ)).2 (Lp.memLp _)
  exact h.re

theorem periodicRieszMellinGreen_ae_kernel (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    periodicRieszMellinGreen s 0 =ᵐ[periodicHaar ι] periodicRieszKernel s hs := by
  filter_upwards [periodicRieszMellinGreen_coe_ae_L2 s hs, periodicRieszKernel_coe_ae s hs]
    with x hx hy
  exact Complex.ofReal_injective (hx.trans hy.symm)

lemma periodicRieszMellinGreen_integral_zero (s τ : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) :
    (∫ x, periodicRieszMellinGreen s τ x ∂periodicHaar ι) = 0 := by
  have h := periodicRieszMellinGreen_fourier s τ hsd hτ (0 : PeriodicFrequency ι)
  simp only [periodicRieszHeatFourierCoeff_zero_mode, UnitAddTorus.mFourierCoeff,
    neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul] at h
  have hc : ((∫ x, periodicRieszMellinGreen s τ x ∂periodicHaar ι : ℝ) : ℂ) = 0 := by
    exact ((@RCLike.ofRealLI ℂ _).integral_comp_comm _).symm.trans h
  exact Complex.ofReal_injective (by simpa using hc)

end DGRHS.Periodic
