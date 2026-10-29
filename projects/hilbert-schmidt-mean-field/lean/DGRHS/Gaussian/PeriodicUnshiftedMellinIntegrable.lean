import DGRHS.Gaussian.PeriodicHeatTimeEnvelope

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Actual unshifted Mellin heat product integrals.
This adapts the checked PeriodicHeatMellinIntegrable Fubini proof, retaining
u^p at the integration variable and shifting only the heat time to u+τ.
No pointwise heat monotonicity or zero-time Green comparison is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicUnshiftedMellinHeatIntegrand (p τ u : ℝ) (x : PeriodicTorus ι) : ℂ :=
  ((u ^ p : ℝ) : ℂ) * (periodicGaussianHeat (u + τ) x - 1)

lemma periodicUnshiftedMellinHeatIntegrand_measurable (p τ : ℝ) :
    Measurable (fun q : ℝ × PeriodicTorus ι =>
      periodicUnshiftedMellinHeatIntegrand p τ q.1 q.2) := by
  have hm : Measurable (fun q : ℝ × PeriodicTorus ι => (q.1 + τ, q.2)) := by
    fun_prop
  have hh := (periodicGaussianHeat_joint_measurable (ι := ι)).comp hm
  exact (Complex.continuous_ofReal.measurable.comp
    (show Measurable (fun q : ℝ × PeriodicTorus ι => q.1 ^ p) by fun_prop)).mul
      (hh.sub measurable_const)

lemma periodicUnshiftedMellinHeatIntegrand_row (p τ u : ℝ)
    (hτ : 0 ≤ τ) (hu : 0 < u) :
    Integrable (periodicUnshiftedMellinHeatIntegrand p τ u) (periodicHaar ι) :=
  ((periodicGaussianHeat_integrable (u + τ) (by linarith)).sub
    (integrable_const _)).const_mul _

lemma periodicUnshiftedMellinHeatIntegrand_mass_bound (p τ u : ℝ)
    (hτ : 0 ≤ τ) (hu : 0 < u) :
    (∫ x, ‖periodicUnshiftedMellinHeatIntegrand p τ u x‖ ∂periodicHaar ι) ≤
      u ^ p * periodicHeatTimeEnvelope ι u := by
  have hp : 0 ≤ u ^ p := Real.rpow_nonneg hu.le p
  have hc : 0 ≤ periodicHeatTimeEnvelopeConstant ι := by
    unfold periodicHeatTimeEnvelopeConstant
    exact add_nonneg (by positivity) periodicHeatTailMass_nonneg
  have he : periodicHeatTimeEnvelope ι (u + τ) ≤ periodicHeatTimeEnvelope ι u := by
    unfold periodicHeatTimeEnvelope
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hc
  simp only [periodicUnshiftedMellinHeatIntegrand, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hp, integral_const_mul]
  exact (mul_le_mul_of_nonneg_left
    (periodicGaussianHeat_centered_envelope_mass (u + τ) (by linarith)) hp).trans
      (mul_le_mul_of_nonneg_left he hp)

lemma periodicUnshiftedMellinHeatIntegrand_product_integrable (p τ : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) :
    Integrable (fun q : ℝ × PeriodicTorus ι =>
      periodicUnshiftedMellinHeatIntegrand p τ q.1 q.2)
      ((volume.restrict (Ioi 0)).prod (periodicHaar ι)) := by
  apply (integrable_prod_iff
    (periodicUnshiftedMellinHeatIntegrand_measurable p τ).aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact periodicUnshiftedMellinHeatIntegrand_row p τ u hτ hu
  · apply (periodicHeatTimeEnvelope_weight_integrable (ι := ι) p hp).mono'
      (periodicUnshiftedMellinHeatIntegrand_measurable p τ).stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    exact periodicUnshiftedMellinHeatIntegrand_mass_bound p τ u hτ hu

def periodicUnshiftedMellinHeatGreen (p τ : ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∫ u : ℝ in Ioi 0, u ^ p * ((periodicGaussianHeat (u + τ) x).re - 1)

lemma periodicUnshiftedMellinHeatGreen_coe_integral (p τ : ℝ) (hτ : 0 ≤ τ)
    (x : PeriodicTorus ι) :
    (periodicUnshiftedMellinHeatGreen p τ x : ℂ) =
      ∫ u : ℝ in Ioi 0, periodicUnshiftedMellinHeatIntegrand p τ u x := by
  calc
    _ = ∫ u : ℝ in Ioi 0,
        ((u ^ p * ((periodicGaussianHeat (u + τ) x).re - 1) : ℝ) : ℂ) :=
      ((@RCLike.ofRealLI ℂ _).integral_comp_comm _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simp only [periodicUnshiftedMellinHeatIntegrand, Complex.ofReal_mul,
        Complex.ofReal_sub, Complex.ofReal_one]
      rw [← periodicGaussianHeat_eq_re (u + τ) (add_pos_of_pos_of_nonneg hu hτ)]

lemma periodicUnshiftedMellinHeatGreen_integrable (p τ : ℝ)
    (hp : -1 < p) (hτ : 0 ≤ τ) :
    Integrable (periodicUnshiftedMellinHeatGreen (ι := ι) p τ) (periodicHaar ι) := by
  have hi :=
    (periodicUnshiftedMellinHeatIntegrand_product_integrable (ι := ι) p τ hp hτ).integral_prod_right
  have he : (fun x : PeriodicTorus ι => (periodicUnshiftedMellinHeatGreen p τ x : ℂ)) =
      fun x => ∫ u : ℝ in Ioi 0, periodicUnshiftedMellinHeatIntegrand p τ u x :=
    funext (periodicUnshiftedMellinHeatGreen_coe_integral p τ hτ)
  have hic : Integrable
      (fun x : PeriodicTorus ι => (periodicUnshiftedMellinHeatGreen p τ x : ℂ))
      (periodicHaar ι) := he ▸ hi
  exact hic.re

end DGRHS.Periodic
