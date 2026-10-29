import DGRHS.Gaussian.PeriodicRieszMellinIdentification
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. A positive short-time Mellin truncation,
with the weight at u and heat time u+τ. Its exact mass controls the
short-range potential against a bounded density. No pointwise monotonicity
of heat regularization is used or claimed. The zero-mode constant is explicit.
These lemmas alone do not establish a particle exponential envelope. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace DGRHS.Periodic
universe u

lemma periodicMellinWeight_short_integrable (p ε : ℝ) (hp : -1 < p) :
    IntegrableOn (fun u : ℝ => u ^ p) (Ioc 0 ε) :=
  (intervalIntegral.intervalIntegrable_rpow' hp : IntervalIntegrable (fun u : ℝ => u ^ p) volume 0 ε).1

lemma periodicMellinWeight_short_mass (p ε : ℝ) (hp : -1 < p) (hε : 0 ≤ ε) :
    (∫ u : ℝ in Ioc 0 ε, u ^ p) = ε ^ (p + 1) / (p + 1) := by
  rw [← intervalIntegral.integral_of_le hε, _root_.integral_rpow (Or.inl hp)]
  rw [Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]

variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicPositiveMellinIntegrand (p τ u : ℝ) (x : PeriodicTorus ι) : ℝ :=
  u ^ p * (periodicGaussianHeat (u + τ) x).re

lemma periodicPositiveMellinIntegrand_measurable (p τ : ℝ) :
    Measurable (fun q : ℝ × PeriodicTorus ι =>
      periodicPositiveMellinIntegrand p τ q.1 q.2) := by
  have hm : Measurable (fun q : ℝ × PeriodicTorus ι => (q.1 + τ, q.2)) := by
    fun_prop
  exact (show Measurable (fun q : ℝ × PeriodicTorus ι => q.1 ^ p) by fun_prop).mul
    (Complex.continuous_re.measurable.comp (periodicGaussianHeat_joint_measurable.comp hm))

lemma periodicPositiveMellinIntegrand_nonneg (p τ u : ℝ) (hτ : 0 ≤ τ)
    (hu : 0 < u) (x : PeriodicTorus ι) :
    0 ≤ periodicPositiveMellinIntegrand p τ u x :=
  mul_nonneg (Real.rpow_nonneg hu.le p)
    (periodicGaussianHeat_real_nonneg (u + τ) (add_pos_of_pos_of_nonneg hu hτ) x).1

lemma periodicPositiveMellinIntegrand_row_integrable (p τ u : ℝ) (hτ : 0 ≤ τ)
    (hu : 0 < u) :
    Integrable (periodicPositiveMellinIntegrand (ι := ι) p τ u) (periodicHaar ι) :=
  ((periodicGaussianHeat_integrable (u + τ) (add_pos_of_pos_of_nonneg hu hτ)).re).const_mul _

lemma periodicPositiveMellinIntegrand_row_mass (p τ u : ℝ) (hτ : 0 ≤ τ)
    (hu : 0 < u) :
    (∫ x, periodicPositiveMellinIntegrand p τ u x ∂periodicHaar ι) = u ^ p := by
  simp only [periodicPositiveMellinIntegrand, integral_const_mul,
    periodicGaussianHeat_real_integral (u + τ) (add_pos_of_pos_of_nonneg hu hτ), mul_one]

lemma periodicPositiveMellinIntegrand_row_norm_mass (p τ u : ℝ) (hτ : 0 ≤ τ)
    (hu : 0 < u) :
    (∫ x, ‖periodicPositiveMellinIntegrand p τ u x‖ ∂periodicHaar ι) = u ^ p := by
  calc
    _ = ∫ x, periodicPositiveMellinIntegrand p τ u x ∂periodicHaar ι := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x =>
        Real.norm_of_nonneg (periodicPositiveMellinIntegrand_nonneg p τ u hτ hu x))
    _ = _ := periodicPositiveMellinIntegrand_row_mass (ι := ι) p τ u hτ hu

lemma periodicPositiveMellinIntegrand_product_integrable (p τ ε : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) :
    Integrable (fun q : ℝ × PeriodicTorus ι =>
      periodicPositiveMellinIntegrand p τ q.1 q.2)
      ((volume.restrict (Ioc 0 ε)).prod (periodicHaar ι)) := by
  apply (integrable_prod_iff
    (periodicPositiveMellinIntegrand_measurable p τ).aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact periodicPositiveMellinIntegrand_row_integrable p τ u hτ hu.1
  · apply (periodicMellinWeight_short_integrable p ε hp).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (periodicPositiveMellinIntegrand_row_norm_mass p τ u hτ hu.1).symm

def periodicPositiveMellinShort (p τ ε : ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∫ u : ℝ in Ioc 0 ε, periodicPositiveMellinIntegrand p τ u x

lemma periodicPositiveMellinShort_measurable (p τ ε : ℝ) :
    Measurable (periodicPositiveMellinShort (ι := ι) p τ ε) := by
  exact (periodicPositiveMellinIntegrand_measurable p τ).stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Ioc 0 ε)) |>.measurable

lemma periodicPositiveMellinShort_nonneg (p τ ε : ℝ) (hτ : 0 ≤ τ)
    (x : PeriodicTorus ι) : 0 ≤ periodicPositiveMellinShort p τ ε x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact periodicPositiveMellinIntegrand_nonneg p τ u hτ hu.1 x

lemma periodicPositiveMellinShort_integrable (p τ ε : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) :
    Integrable (periodicPositiveMellinShort (ι := ι) p τ ε) (periodicHaar ι) :=
  (periodicPositiveMellinIntegrand_product_integrable p τ ε hp hτ).integral_prod_right

lemma periodicPositiveMellinShort_mass (p τ ε : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    (∫ x, periodicPositiveMellinShort p τ ε x ∂periodicHaar ι) =
      ε ^ (p + 1) / (p + 1) := by
  change (∫ x, (∫ u : ℝ in Ioc 0 ε,
    periodicPositiveMellinIntegrand p τ u x) ∂periodicHaar ι) = _
  rw [← integral_integral_swap
    (periodicPositiveMellinIntegrand_product_integrable (ι := ι) p τ ε hp hτ)]
  calc
    _ = ∫ u : ℝ in Ioc 0 ε, u ^ p := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact periodicPositiveMellinIntegrand_row_mass p τ u hτ hu.1
    _ = _ := periodicMellinWeight_short_mass p ε hp hε

/-- Canonical integrable truncation representative. The following theorem
identifies it almost everywhere with the actual tail integral. -/
def periodicMellinCutoff (p τ ε : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicUnshiftedMellinHeatGreen p τ x - periodicPositiveMellinShort p τ ε x +
    ε ^ (p + 1) / (p + 1)

lemma periodicMellinCutoff_integrable (p τ ε : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) :
    Integrable (periodicMellinCutoff (ι := ι) p τ ε) (periodicHaar ι) :=
  ((periodicUnshiftedMellinHeatGreen_integrable p τ hp hτ).sub
    (periodicPositiveMellinShort_integrable p τ ε hp hτ)).add (integrable_const _)

lemma periodicMellinCutoff_ae_tail (p τ ε : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    periodicMellinCutoff p τ ε =ᵐ[periodicHaar ι]
      (fun x => ∫ u : ℝ in Ioi ε,
        u ^ p * ((periodicGaussianHeat (u + τ) x).re - 1)) := by
  have hfull := (periodicUnshiftedMellinHeatIntegrand_product_integrable
    (ι := ι) p τ hp hτ).re.prod_left_ae
  have hshort := (periodicPositiveMellinIntegrand_product_integrable
    (ι := ι) p τ ε hp hτ).prod_left_ae
  filter_upwards [hfull, hshort] with x hx hxshort
  have hxreal : IntegrableOn (fun u : ℝ =>
      u ^ p * ((periodicGaussianHeat (u + τ) x).re - 1)) (Ioi 0) := by
    simpa only [IntegrableOn, periodicUnshiftedMellinHeatIntegrand, RCLike.re_eq_complex_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re,
      zero_mul, sub_zero] using hx
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hxreal hε
  rw [intervalIntegral.integral_of_le hε] at hsplit
  have hshortval : (∫ u : ℝ in Ioc 0 ε,
      u ^ p * ((periodicGaussianHeat (u + τ) x).re - 1)) =
      periodicPositiveMellinShort p τ ε x - ε ^ (p + 1) / (p + 1) := by
    simp only [mul_sub, mul_one]
    change (∫ u : ℝ in Ioc 0 ε, periodicPositiveMellinIntegrand p τ u x - u ^ p) =
      periodicPositiveMellinShort p τ ε x - ε ^ (p + 1) / (p + 1)
    rw [integral_sub hxshort (periodicMellinWeight_short_integrable p ε hp),
      periodicMellinWeight_short_mass p ε hp hε]
    rfl
  rw [hshortval] at hsplit
  dsimp [periodicMellinCutoff, periodicUnshiftedMellinHeatGreen]
  linarith

/-- Pointwise lower comparison from the NONNEGATIVE removed kernel.
The sign is appropriate for a repulsive energy; it is not heat monotonicity. -/
lemma periodicMellinGreen_sub_cutoff_lower (p τ ε : ℝ) (hτ : 0 ≤ τ)
    (x : PeriodicTorus ι) :
    -(ε ^ (p + 1) / (p + 1)) ≤
      periodicUnshiftedMellinHeatGreen p τ x - periodicMellinCutoff p τ ε x := by
  have h := periodicPositiveMellinShort_nonneg p τ ε hτ x
  dsimp [periodicMellinCutoff]
  linarith

/-- Physical normalization is exactly the previously proved source multiplier. -/
def periodicRieszPositiveShort (s τ ε : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicRieszMellinFactor ι s *
    periodicPositiveMellinShort (((Fintype.card ι : ℝ) - s) / 2 - 1) τ ε x

lemma periodicRieszPositiveShort_integrable (s τ ε : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) :
    Integrable (periodicRieszPositiveShort (ι := ι) s τ ε) (periodicHaar ι) :=
  (periodicPositiveMellinShort_integrable _ τ ε
    (periodicUnshiftedMellin_spectralExponent _ s hsd) hτ).const_mul _

lemma periodicRieszPositiveShort_mass (s τ ε : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    (∫ x, periodicRieszPositiveShort s τ ε x ∂periodicHaar ι) =
      periodicRieszMellinFactor ι s *
        (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) := by
  unfold periodicRieszPositiveShort
  rw [integral_const_mul, periodicPositiveMellinShort_mass _ τ ε
    (periodicUnshiftedMellin_spectralExponent _ s hsd) hτ hε]
  simp only [sub_add_cancel]

lemma periodicRieszPositiveShort_nonneg (s τ ε : ℝ) (hs : 0 < s) (hτ : 0 ≤ τ)
    (x : PeriodicTorus ι) : 0 ≤ periodicRieszPositiveShort s τ ε x :=
  mul_nonneg (periodicRieszMellinFactor_pos s hs).le
    (periodicPositiveMellinShort_nonneg _ τ ε hτ x)

end DGRHS.Periodic
