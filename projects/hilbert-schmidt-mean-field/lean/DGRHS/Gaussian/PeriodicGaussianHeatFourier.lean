import DGRHS.Gaussian.PeriodicMultidimensionalPoisson
import DGRHS.Gaussian.PeriodicCosineConvolution

/-! Actual uniformly convergent Gaussian Fourier heat series, with its
computed normalized-Haar Fourier coefficients. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodic_mFourier_integral (k : PeriodicFrequency ι) :
    (∫ x,UnitAddTorus.mFourier k x ∂periodicHaar ι) = if k=0 then 1 else 0 := by
  simp only [periodicHaar,UnitAddTorus.mFourier,ContinuousMap.coe_mk,
    integral_fintype_prod_eq_prod,periodicCircle_fourier_integral]
  by_cases hk : k=0
  · simp [hk]
  · rw [if_neg hk]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hk
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)

lemma periodic_mFourier_orthogonality (m k : PeriodicFrequency ι) :
    (∫ x,UnitAddTorus.mFourier (-m) x * UnitAddTorus.mFourier k x ∂periodicHaar ι) =
      if k=m then 1 else 0 := by
  simp only [← UnitAddTorus.mFourier_add,periodic_mFourier_integral]
  congr 1
  apply propext
  constructor
  · intro h
    have hh := congrArg (fun z => m+z) h
    simpa only [← add_assoc,add_neg_cancel,zero_add,add_zero] using hh
  · intro h
    subst k
    simp

lemma periodicFourierSeries_continuous (c : PeriodicFrequency ι → ℂ)
    (hc : Summable (fun k => ‖c k‖)) :
    Continuous (fun x : PeriodicTorus ι => ∑' k,c k*UnitAddTorus.mFourier k x) := by
  apply continuous_tsum (fun k => continuous_const.mul (UnitAddTorus.mFourier k).continuous) hc
  intro k x
  simp [periodic_mFourier_norm_apply]

lemma periodicFourierSeries_coefficient (c : PeriodicFrequency ι → ℂ)
    (hc : Summable (fun k => ‖c k‖)) (m : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x : PeriodicTorus ι => ∑' k,c k*UnitAddTorus.mFourier k x) m = c m := by
  let F := fun (k : PeriodicFrequency ι) (x : PeriodicTorus ι) =>
    UnitAddTorus.mFourier (-m) x*(c k*UnitAddTorus.mFourier k x)
  have hnorm (k : PeriodicFrequency ι) (x : PeriodicTorus ι) : ‖F k x‖=‖c k‖ := by
    simp only [F,norm_mul,periodic_mFourier_norm_apply,one_mul,mul_one]
  have hi (k : PeriodicFrequency ι) : Integrable (F k) (periodicHaar ι) := by
    apply (integrable_const ‖c k‖).mono'
      ((UnitAddTorus.mFourier (-m)).continuous.mul
        (continuous_const.mul (UnitAddTorus.mFourier k).continuous)).aestronglyMeasurable
    exact Eventually.of_forall (fun x => (hnorm k x).le)
  have hs : Summable (fun k : PeriodicFrequency ι => ∫ x,‖F k x‖ ∂periodicHaar ι) := by
    simpa only [hnorm,integral_const,probReal_univ,one_smul] using hc
  rw [periodic_mFourierCoeff_eq_integral]
  simp only [← tsum_mul_left]
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  have he (k : PeriodicFrequency ι) : (∫ x,F k x ∂periodicHaar ι) = if k=m then c m else 0 := by
    have he' : F k = fun x => c k*(UnitAddTorus.mFourier (-m) x*UnitAddTorus.mFourier k x) := by
      funext x
      simp only [F]
      ring
    rw [he',integral_const_mul,periodic_mFourier_orthogonality]
    by_cases hk : k=m <;> simp [hk]
  simp only [he,tsum_ite_eq]

def periodicGaussianHeat (a : ℝ) (x : PeriodicTorus ι) : ℂ :=
  ∑' k : PeriodicFrequency ι,(Real.exp (-a*‖periodicFrequencyVector k‖^2):ℂ)*UnitAddTorus.mFourier k x

lemma periodicGaussianHeat_continuous (a : ℝ) (ha : 0<a) :
    Continuous (periodicGaussianHeat (ι := ι) a) := by
  apply periodicFourierSeries_continuous
  simpa only [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le] using
    summable_periodicGaussian (ι := ι) a ha

lemma periodicGaussianHeat_fourierCoeff (a : ℝ) (ha : 0<a) (m : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (periodicGaussianHeat a) m =
      (Real.exp (-a*‖periodicFrequencyVector m‖^2):ℂ) := by
  apply periodicFourierSeries_coefficient
  simpa only [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le] using
    summable_periodicGaussian (ι := ι) a ha

lemma periodicGaussianHeat_integral (a : ℝ) (ha : 0<a) :
    (∫ x,periodicGaussianHeat (ι := ι) a x ∂periodicHaar ι) = 1 := by
  have h := periodicGaussianHeat_fourierCoeff (ι := ι) a ha 0
  simpa only [periodic_mFourierCoeff_eq_integral,neg_zero,UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply,one_mul,periodicFrequencyVector_zero,norm_zero,zero_pow (by norm_num : 2≠0),
    mul_zero,Real.exp_zero,Complex.ofReal_one] using h

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_mFourier_integral
#print axioms DGRHS.Periodic.periodic_mFourier_orthogonality
#print axioms DGRHS.Periodic.periodicFourierSeries_coefficient
#print axioms DGRHS.Periodic.periodicGaussianHeat_fourierCoeff
#print axioms DGRHS.Periodic.periodicGaussianHeat_integral
#check @DGRHS.Periodic.periodicGaussianHeat_fourierCoeff
