import DGRHS.Gaussian.PeriodicHeatMellinWeight

/-! Proper product integration for the translated Mellin heat integral.
No singular Green comparison or integrability hypothesis is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicMellinHeatIntegrand (p τ s : ℝ) (x : PeriodicTorus ι) : ℂ :=
  (periodicHeatMellinWeight p τ s : ℂ)*(periodicGaussianHeat s x-1)

lemma periodicMellinHeatIntegrand_measurable (p τ : ℝ) :
    Measurable (fun q : ℝ × PeriodicTorus ι => periodicMellinHeatIntegrand p τ q.1 q.2) := by
  exact (Complex.continuous_ofReal.measurable.comp
    ((periodicHeatMellinWeight_measurable p τ).comp measurable_fst)).mul
      (periodicGaussianHeat_joint_measurable.sub measurable_const)

lemma periodicMellinHeatIntegrand_row (p τ s : ℝ) (hs : 0<s) :
    Integrable (periodicMellinHeatIntegrand p τ s) (periodicHaar ι) :=
  ((periodicGaussianHeat_integrable s hs).sub (integrable_const _)).const_mul _

lemma periodicMellinHeatIntegrand_mass_bound (p τ s : ℝ) (hp : 0≤p) (hτ : 0≤τ) (hs : 0<s) :
    (∫ x,‖periodicMellinHeatIntegrand p τ s x‖ ∂periodicHaar ι) ≤
      s^p*periodicHeatTimeEnvelope ι s := by
  simp only [periodicMellinHeatIntegrand,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (periodicHeatMellinWeight_nonneg p τ s),integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (periodicGaussianHeat_centered_envelope_mass s hs)
    (periodicHeatMellinWeight_nonneg p τ s)).trans
      (mul_le_mul_of_nonneg_right (periodicHeatMellinWeight_le p τ s hp hτ hs.le)
        (periodicHeatTimeEnvelope_nonneg s))

lemma periodicMellinHeatIntegrand_product_integrable (p τ : ℝ) (hp : 0≤p) (hτ : 0≤τ) :
    Integrable (fun q : ℝ × PeriodicTorus ι => periodicMellinHeatIntegrand p τ q.1 q.2)
      ((volume.restrict (Ioi 0)).prod (periodicHaar ι)) := by
  apply (integrable_prod_iff (periodicMellinHeatIntegrand_measurable p τ).aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact periodicMellinHeatIntegrand_row p τ s hs
  · apply (periodicHeatTimeEnvelope_weight_integrable (ι := ι) p (by linarith)).mono'
      (periodicMellinHeatIntegrand_measurable p τ).stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    exact periodicMellinHeatIntegrand_mass_bound p τ s hp hτ hs

def periodicMellinHeatGreen (p τ : ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∫ s : ℝ in Ioi 0,periodicHeatMellinWeight p τ s*((periodicGaussianHeat s x).re-1)

lemma periodicMellinHeatGreen_coe_integral (p τ : ℝ) (x : PeriodicTorus ι) :
    (periodicMellinHeatGreen p τ x : ℂ)=∫ s : ℝ in Ioi 0,periodicMellinHeatIntegrand p τ s x := by
  calc
    _ = ∫ s : ℝ in Ioi 0,((periodicHeatMellinWeight p τ s*((periodicGaussianHeat s x).re-1):ℝ):ℂ) :=
      ((@RCLike.ofRealLI ℂ _).integral_comp_comm _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      simp only [periodicMellinHeatIntegrand,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
      rw [← periodicGaussianHeat_eq_re s hs]

lemma periodicMellinHeatGreen_integrable (p τ : ℝ) (hp : 0≤p) (hτ : 0≤τ) :
    Integrable (periodicMellinHeatGreen (ι := ι) p τ) (periodicHaar ι) := by
  have hi := (periodicMellinHeatIntegrand_product_integrable (ι := ι) p τ hp hτ).integral_prod_right
  have he : (fun x : PeriodicTorus ι => (periodicMellinHeatGreen p τ x:ℂ))=
      fun x => ∫ s : ℝ in Ioi 0,periodicMellinHeatIntegrand p τ s x :=
    funext (periodicMellinHeatGreen_coe_integral p τ)
  have hic : Integrable (fun x : PeriodicTorus ι => (periodicMellinHeatGreen p τ x:ℂ)) (periodicHaar ι) := he ▸ hi
  exact hic.re

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicMellinHeatIntegrand_product_integrable
#print axioms DGRHS.Periodic.periodicMellinHeatGreen_integrable
