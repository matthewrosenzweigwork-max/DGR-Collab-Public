import DGRHS.Gaussian.PeriodicPositiveMellinCutoff
import DGRHS.Gaussian.PeriodicHeatDiagonalScale
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Positive-cutoff tails are proper at every
point and satisfy an actual uniform sup norm bound. No diagonal value or
bounded-feature hypothesis is assumed. The zero-cutoff singular kernel
remains a separate almost-everywhere representative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicRieszMellin_tail_weight_bound (s τ t : ℝ) (ht : 0 < t)
    (hτ : 0 ≤ τ) (x : PeriodicTorus ι) :
    ‖t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
      ((periodicGaussianHeat (t + τ) x).re - 1)‖ ≤
      periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1) := by
  let p : ℝ := ((Fintype.card ι : ℝ) - s) / 2 - 1
  have hp : 0 ≤ t ^ p := Real.rpow_nonneg ht.le _
  have hre : ‖(periodicGaussianHeat (t + τ) x).re - 1‖ ≤
      ‖periodicGaussianHeat (t + τ) x - 1‖ := by
    simpa only [Real.norm_eq_abs, Complex.sub_re, Complex.one_re] using
      Complex.abs_re_le_norm (periodicGaussianHeat (t + τ) x - 1)
  calc
    _ = t ^ p * ‖(periodicGaussianHeat (t + τ) x).re - 1‖ := by
      rw [norm_mul, Real.norm_of_nonneg hp]
    _ ≤ t ^ p * ‖periodicGaussianHeat (t + τ) x - 1‖ :=
      mul_le_mul_of_nonneg_left hre hp
    _ ≤ t ^ p * (periodicHeatDiagonalGlobalConstant ι *
        t ^ (-((Fintype.card ι : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left (periodicGaussianHeat_centered_shifted_power_bound t τ ht hτ x) hp
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add ht]
      congr 1
      congr 1
      dsimp [p]
      ring

lemma periodicRieszMellin_tail_integrable (s τ ε : ℝ) (hs : 0 < s)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (x : PeriodicTorus ι) :
    IntegrableOn (fun t : ℝ => t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
      ((periodicGaussianHeat (t + τ) x).re - 1)) (Ioi ε) := by
  have hm : Measurable (fun t : ℝ => (periodicGaussianHeat (t + τ) x).re) :=
    Complex.continuous_re.measurable.comp (periodicGaussianHeat_joint_measurable.comp
      (show Measurable (fun t : ℝ => (t + τ, x)) by fun_prop))
  apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -s / 2 - 1 < -1) hε).const_mul
    (periodicHeatDiagonalGlobalConstant ι)).mono'
      ((show Measurable (fun t : ℝ => t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1)) by
        fun_prop).mul (hm.sub measurable_const)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact periodicRieszMellin_tail_weight_bound s τ t (hε.trans ht) hτ x

def periodicRieszMellinTail (s τ ε : ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∫ t : ℝ in Ioi ε, t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
    ((periodicGaussianHeat (t + τ) x).re - 1)

lemma periodicRieszMellinTail_norm_bound (s τ ε : ℝ) (hs : 0 < s)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (x : PeriodicTorus ι) :
    ‖periodicRieszMellinTail s τ ε x‖ ≤
      periodicHeatDiagonalGlobalConstant ι * (ε ^ (-s / 2) / (s / 2)) := by
  have hi := periodicRieszMellin_tail_integrable s τ ε hs hτ hε x
  have he := (integrableOn_Ioi_rpow_of_lt (by linarith : -s / 2 - 1 < -1) hε).const_mul
    (periodicHeatDiagonalGlobalConstant ι)
  calc
    _ ≤ ∫ t : ℝ in Ioi ε, ‖t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
        ((periodicGaussianHeat (t + τ) x).re - 1)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi ε, periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1) := by
      apply integral_mono_ae hi.norm he
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact periodicRieszMellin_tail_weight_bound s τ t (hε.trans ht) hτ x
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s / 2 - 1 < -1) hε]
      rw [show -s / 2 - 1 + 1 = -(s / 2) by ring]
      congr 1
      simp only [div_neg, neg_div, neg_neg]

lemma periodicRieszMellinTail_eq_cutoff_ae (s τ ε : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    periodicRieszMellinTail (ι := ι) s τ ε =ᵐ[periodicHaar ι]
      periodicMellinCutoff (((Fintype.card ι : ℝ) - s) / 2 - 1) τ ε :=
  (periodicMellinCutoff_ae_tail _ τ ε
    (periodicUnshiftedMellin_spectralExponent _ s hsd) hτ hε).symm

lemma periodicRieszMellinTail_integrable (s τ ε : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    Integrable (periodicRieszMellinTail (ι := ι) s τ ε) (periodicHaar ι) :=
  (periodicMellinCutoff_integrable _ τ ε
    (periodicUnshiftedMellin_spectralExponent _ s hsd) hτ).congr
      (periodicRieszMellinTail_eq_cutoff_ae s τ ε hsd hτ hε).symm

def periodicRieszPhysicalTail (s τ ε : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicRieszMellinFactor ι s * periodicRieszMellinTail s τ ε x

lemma periodicRieszPhysicalTail_norm_bound (s τ ε : ℝ) (hs : 0 < s)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (x : PeriodicTorus ι) :
    ‖periodicRieszPhysicalTail s τ ε x‖ ≤
      periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
        (ε ^ (-s / 2) / (s / 2)) := by
  have hc := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  simpa only [periodicRieszPhysicalTail, norm_mul, Real.norm_of_nonneg hc, mul_assoc] using
    mul_le_mul_of_nonneg_left (periodicRieszMellinTail_norm_bound s τ ε hs hτ hε x) hc


lemma periodicRieszPhysicalTail_integrable (s τ ε : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    Integrable (periodicRieszPhysicalTail (ι := ι) s τ ε) (periodicHaar ι) :=
  (periodicRieszMellinTail_integrable s τ ε hsd hτ hε).const_mul _

lemma periodicRieszPhysicalTail_eq_cutoff_ae (s τ ε : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    periodicRieszPhysicalTail (ι := ι) s τ ε =ᵐ[periodicHaar ι]
      (fun x => periodicRieszMellinFactor ι s *
        periodicMellinCutoff (((Fintype.card ι : ℝ) - s) / 2 - 1) τ ε x) := by
  filter_upwards [periodicRieszMellinTail_eq_cutoff_ae (ι := ι) s τ ε hsd hτ hε] with x hx
  exact congrArg (fun z : ℝ => periodicRieszMellinFactor ι s * z) hx

/-- The zero-mode mass is retained explicitly; later Hoeffding centering
cancels this constant. No particle or background cancellation is assumed here. -/
lemma periodicRieszMellinGreen_sub_tail_ae (s τ ε : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    (fun x => periodicRieszMellinGreen (ι := ι) s τ x -
      periodicRieszPhysicalTail s τ ε x) =ᵐ[periodicHaar ι]
      (fun x => periodicRieszPositiveShort s τ ε x - periodicRieszMellinFactor ι s *
        (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2))) := by
  filter_upwards [periodicRieszPhysicalTail_eq_cutoff_ae (ι := ι) s τ ε hsd hτ hε] with x hx
  rw [hx]
  dsimp only [periodicRieszMellinGreen, periodicMellinCutoff, periodicRieszPositiveShort]
  rw [sub_add_cancel]
  ring

end DGRHS.Periodic
