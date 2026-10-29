import DGRHS.Gaussian.PeriodicGaussianHeatFourier
import DGRHS.Gaussian.PeriodicLongHeatBound

/-! Fourier coefficients of the actual bounded long-scale Green correction.
The real series is identified with its complex Fourier series using the exact
evenness of the proper Gaussian tail coefficients. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ComplexConjugate
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLongHeatCoefficient_neg (a : ℝ) (k : PeriodicFrequency ι) :
    periodicLongHeatCoefficient a (-k)=periodicLongHeatCoefficient a k := by
  simp only [periodicLongHeatCoefficient,neg_eq_zero,periodicFrequencyVector_neg,norm_neg]

lemma periodicLongHeatSeries_summable (a : ℝ) (ha : 0<a) (x : PeriodicTorus ι) :
    Summable (fun k : PeriodicFrequency ι =>
      (periodicLongHeatCoefficient a k:ℂ)*UnitAddTorus.mFourier k x) := by
  apply Summable.of_norm
  simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (periodicLongHeatCoefficient_nonneg a _),
    periodic_mFourier_norm_apply,mul_one] using summable_periodicLongHeatCoefficient (ι := ι) a ha

lemma periodicLongHeatSeries_conj (a : ℝ) (ha : 0<a) (x : PeriodicTorus ι) :
    conj (∑' k : PeriodicFrequency ι,(periodicLongHeatCoefficient a k:ℂ)*UnitAddTorus.mFourier k x) =
      ∑' k : PeriodicFrequency ι,(periodicLongHeatCoefficient a k:ℂ)*UnitAddTorus.mFourier k x := by
  rw [Complex.conj_tsum]
  simp only [map_mul,Complex.conj_ofReal,← UnitAddTorus.mFourier_neg]
  have he := (Equiv.neg (PeriodicFrequency ι)).tsum_eq
    (fun k : PeriodicFrequency ι => (periodicLongHeatCoefficient a k:ℂ)*UnitAddTorus.mFourier k x)
  simpa only [Equiv.neg_apply,periodicLongHeatCoefficient_neg] using he

lemma periodicLongHeatRemainder_coe (a : ℝ) (ha : 0<a) (x : PeriodicTorus ι) :
    (periodicLongHeatRemainder a x:ℂ) =
      ∑' k : PeriodicFrequency ι,(periodicLongHeatCoefficient a k:ℂ)*UnitAddTorus.mFourier k x := by
  have hr : periodicLongHeatRemainder a x =
      (∑' k : PeriodicFrequency ι,(periodicLongHeatCoefficient a k:ℂ)*UnitAddTorus.mFourier k x).re := by
    rw [Complex.re_tsum (periodicLongHeatSeries_summable a ha x)]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,periodicLongHeatRemainder]
  rw [hr]
  exact RCLike.conj_eq_iff_re.mp (periodicLongHeatSeries_conj a ha x)

lemma periodicLongHeatRemainder_integrable (a : ℝ) (ha : 0<a) :
    Integrable (periodicLongHeatRemainder (ι := ι) a) (periodicHaar ι) :=
  (periodicLongHeatRemainder_continuous a ha).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem periodicLongHeatRemainder_fourierCoeff (a : ℝ) (ha : 0<a) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicLongHeatRemainder a x:ℂ)) k =
      (periodicLongHeatCoefficient a k:ℂ) := by
  simp only [periodicLongHeatRemainder_coe a ha]
  apply periodicFourierSeries_coefficient
  simpa only [Complex.norm_real,Real.norm_of_nonneg (periodicLongHeatCoefficient_nonneg a _)] using
    summable_periodicLongHeatCoefficient (ι := ι) a ha

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLongHeatSeries_conj
#print axioms DGRHS.Periodic.periodicLongHeatRemainder_coe
#print axioms DGRHS.Periodic.periodicLongHeatRemainder_fourierCoeff
#check @DGRHS.Periodic.periodicLongHeatRemainder_fourierCoeff
