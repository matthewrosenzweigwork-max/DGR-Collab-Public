import DGRHS.Gaussian.PeriodicShortGreenPhysical

/-! Haar L1 construction and actual Fourier coefficients of the proper short
heat Green integral. The only interchange is justified by a product L1 bound
from the genuine mass-one positive heat kernel. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicShortHeatIntegrand (t : ℝ) (x : PeriodicTorus ι) : ℂ :=
  (periodicHeatScaleFactor ι*t^(Fintype.card ι-1):ℝ) *
    (periodicGaussianHeat (2*Real.pi^2*t^2) x-1)

lemma periodicShortHeatIntegrand_measurable :
    Measurable (fun p : ℝ × PeriodicTorus ι => periodicShortHeatIntegrand p.1 p.2) := by
  exact (Complex.continuous_ofReal.measurable.comp (show Measurable
    (fun p : ℝ × PeriodicTorus ι => periodicHeatScaleFactor ι*p.1^(Fintype.card ι-1)) by fun_prop)).mul
    ((periodicGaussianHeat_joint_measurable.comp (show Measurable
      (fun p : ℝ × PeriodicTorus ι => (2*Real.pi^2*p.1^2,p.2)) by fun_prop)).sub measurable_const)

lemma periodicShortHeatIntegrand_row (t : ℝ) (ht : 0<t) :
    Integrable (periodicShortHeatIntegrand t) (periodicHaar ι) := by
  exact ((periodicGaussianHeat_integrable (ι := ι) (2*Real.pi^2*t^2) (by positivity)).sub
    (integrable_const _)).const_mul _

lemma periodicShortHeatIntegrand_mass_bound (t : ℝ) (ht : 0<t) :
    (∫ x,‖periodicShortHeatIntegrand t x‖ ∂periodicHaar ι) ≤
      2*(periodicHeatScaleFactor ι*t^(Fintype.card ι-1)) := by
  have hw : 0≤periodicHeatScaleFactor ι*t^(Fintype.card ι-1) := by
    unfold periodicHeatScaleFactor
    positivity
  simp only [periodicShortHeatIntegrand,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg hw,integral_const_mul]
  nlinarith [periodicGaussianHeat_centered_mass_bound (ι := ι) (2*Real.pi^2*t^2) (by positivity)]

lemma periodicShortHeatIntegrand_product_integrable :
    Integrable (fun p : ℝ × PeriodicTorus ι => periodicShortHeatIntegrand p.1 p.2)
      ((volume.restrict (Ioc 0 1)).prod (periodicHaar ι)) := by
  apply (integrable_prod_iff periodicShortHeatIntegrand_measurable.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact periodicShortHeatIntegrand_row t ht.1
  · apply ((periodicShortHeatMean_integrable (ι := ι)).const_mul 2).mono'
      periodicShortHeatIntegrand_measurable.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    exact periodicShortHeatIntegrand_mass_bound t ht.1

lemma periodicShortGreen_coe_integral (x : PeriodicTorus ι) :
    (periodicShortGreen x : ℂ) =
      ∫ t : ℝ in Ioc 0 1,periodicShortHeatIntegrand t x := by
  calc
    _ = ∫ t : ℝ in Ioc 0 1,
      ((periodicHeatScaleFactor ι*t^(Fintype.card ι-1)*
        ((periodicGaussianHeat (2*Real.pi^2*t^2) x).re-1):ℝ):ℂ) :=
      ((@RCLike.ofRealLI ℂ _).integral_comp_comm _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [periodicShortHeatIntegrand,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
      have ht0 : 0<t := ht.1
      rw [← periodicGaussianHeat_eq_re (2*Real.pi^2*t^2) (by positivity)]

lemma periodicShortGreen_integrable :
    Integrable (periodicShortGreen (ι := ι)) (periodicHaar ι) := by
  have hi := periodicShortHeatIntegrand_product_integrable (ι := ι)
  have he : (fun x : PeriodicTorus ι => (periodicShortGreen x : ℂ)) =
      (fun x => ∫ t : ℝ in Ioc 0 1,periodicShortHeatIntegrand t x) :=
    funext periodicShortGreen_coe_integral
  have hic : Integrable (fun x => (periodicShortGreen x : ℂ)) (periodicHaar ι) :=
    he ▸ hi.integral_prod_right
  exact hic.re

lemma periodicShortHeatIntegrand_fourier_product_integrable (k : PeriodicFrequency ι) :
    Integrable (fun p : ℝ × PeriodicTorus ι =>
      UnitAddTorus.mFourier (-k) p.2 * periodicShortHeatIntegrand p.1 p.2)
      ((volume.restrict (Ioc 0 1)).prod (periodicHaar ι)) := by
  apply (periodicShortHeatIntegrand_product_integrable (ι := ι)).norm.mono'
  · exact (((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_snd).mul
      periodicShortHeatIntegrand_measurable).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      simp only [norm_mul,periodic_mFourier_norm_apply,one_mul]; exact le_rfl)

lemma periodicGaussianHeat_centered_fourier (a : ℝ) (ha : 0<a) (k : PeriodicFrequency ι) :
    (∫ x,UnitAddTorus.mFourier (-k) x*(periodicGaussianHeat a x-1) ∂periodicHaar ι) =
      (Real.exp (-a*‖periodicFrequencyVector k‖^2):ℂ) - if k=0 then 1 else 0 := by
  have hi : Integrable (fun x => UnitAddTorus.mFourier (-k) x*periodicGaussianHeat a x)
      (periodicHaar ι) :=
    (((UnitAddTorus.mFourier (-k)).continuous).mul (periodicGaussianHeat_continuous a ha)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (fun x => UnitAddTorus.mFourier (-k) x) (periodicHaar ι) :=
    (UnitAddTorus.mFourier (-k)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [mul_sub,mul_one]
  rw [integral_sub hi hc]
  change UnitAddTorus.mFourierCoeff (periodicGaussianHeat a) k - _ = _
  rw [periodicGaussianHeat_fourierCoeff a ha]
  congr 1
  simpa only [neg_eq_zero] using periodic_mFourier_integral (-k)

/-- Actual coefficients of the Haar-integrable short Green function. -/
theorem periodicShortGreen_fourierCoeff (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicShortGreen x : ℂ)) k =
      ∫ t : ℝ in Ioc 0 1,(periodicHeatScaleFactor ι*t^(Fintype.card ι-1):ℝ)*
        ((Real.exp (-(2*Real.pi^2*t^2)*‖periodicFrequencyVector k‖^2):ℂ)-if k=0 then 1 else 0) := by
  rw [periodic_mFourierCoeff_eq_integral]
  simp_rw [periodicShortGreen_coe_integral,← integral_const_mul]
  rw [← integral_integral_swap (periodicShortHeatIntegrand_fourier_product_integrable k)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [periodicShortHeatIntegrand]
  conv_lhs => arg 2; ext x; rw [mul_left_comm]
  have ht0 : 0<t := ht.1
  rw [integral_const_mul,periodicGaussianHeat_centered_fourier _ (by positivity)]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicShortHeatIntegrand_product_integrable
#print axioms DGRHS.Periodic.periodicShortGreen_integrable
#print axioms DGRHS.Periodic.periodicShortGreen_fourierCoeff
#check @DGRHS.Periodic.periodicShortGreen_fourierCoeff
