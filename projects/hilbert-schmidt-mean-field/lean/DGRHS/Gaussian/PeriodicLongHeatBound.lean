import DGRHS.Gaussian.PeriodicGaussianLatticeBounds
import DGRHS.Gaussian.PeriodicCosineConvolution
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Uniform summable coefficients of the genuine large-scale Gaussian tail.
All bounds are derived from the lattice gap and the native proper Gaussian
integral. No Green-kernel boundedness is assumed. -/
noncomputable section
open MeasureTheory Set Filter Real
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicLongHeatMass (ι : Type u) [Fintype ι] (a : ℝ) : ℝ :=
  ∫ t in Ioi (1:ℝ), t^(Fintype.card ι-1)*Real.exp (-a*t^2)

def periodicLongHeatCoefficient (a : ℝ) (k : PeriodicFrequency ι) : ℝ :=
  if k=0 then 0 else
    ∫ t in Ioi (1:ℝ),t^(Fintype.card ι-1)*Real.exp (-2*a*t^2*‖periodicFrequencyVector k‖^2)

lemma periodicLongHeatMass_integrable (a : ℝ) (ha : 0<a) :
    IntegrableOn (fun t : ℝ => t^(Fintype.card ι-1)*Real.exp (-a*t^2)) (Ioi 1) := by
  have he : (-1:ℝ)<((Fintype.card ι-1:ℕ):ℝ) :=
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)
  have hi := integrableOn_rpow_mul_exp_neg_mul_sq (b := a) ha he
  have hsub : Ioi (1:ℝ) ⊆ Ioi 0 := by
    intro t ht
    change (1:ℝ)<t at ht
    change (0:ℝ)<t
    linarith
  simpa only [Real.rpow_natCast] using hi.mono_set hsub

lemma periodicLongHeatMass_nonneg (a : ℝ) : 0≤periodicLongHeatMass ι a := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (pow_nonneg (zero_lt_one.trans ht).le _) (Real.exp_pos _).le

lemma periodicLongHeatCoefficient_integrable (a : ℝ) (ha : 0<a)
    (k : PeriodicFrequency ι) (hk : k≠0) :
    IntegrableOn (fun t : ℝ => t^(Fintype.card ι-1)*
      Real.exp (-2*a*t^2*‖periodicFrequencyVector k‖^2)) (Ioi 1) := by
  have hn := periodicFrequency_norm_pos hk
  convert periodicLongHeatMass_integrable (ι := ι) (2*a*‖periodicFrequencyVector k‖^2)
    (by positivity) using 1
  ext t
  congr 2
  ring

lemma periodicLongHeat_gaussian_bound (a : ℝ) (ha : 0≤a)
    (t : ℝ) (ht : 1≤t) (k : PeriodicFrequency ι) (hk : k≠0) :
    Real.exp (-2*a*t^2*‖periodicFrequencyVector k‖^2) ≤
      Real.exp (-a*t^2)*Real.exp (-a*‖periodicFrequencyVector k‖^2) := by
  rw [← Real.exp_add,Real.exp_le_exp]
  have ht2 : 1≤t^2 := by nlinarith
  have hk2 := periodicFrequency_norm_sq_ge_one hk
  have h1 : t^2≤t^2*‖periodicFrequencyVector k‖^2 := by nlinarith [sq_nonneg t]
  have h2 : ‖periodicFrequencyVector k‖^2≤t^2*‖periodicFrequencyVector k‖^2 := by
    nlinarith [sq_nonneg ‖periodicFrequencyVector k‖]
  nlinarith [mul_nonneg ha (by linarith : 0≤2*t^2*‖periodicFrequencyVector k‖^2-t^2-‖periodicFrequencyVector k‖^2)]

lemma periodicLongHeatCoefficient_nonneg (a : ℝ) (k : PeriodicFrequency ι) :
    0≤periodicLongHeatCoefficient a k := by
  unfold periodicLongHeatCoefficient
  split_ifs
  · rfl
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg (zero_lt_one.trans ht).le _) (Real.exp_pos _).le

lemma periodicLongHeatCoefficient_bound (a : ℝ) (ha : 0<a) (k : PeriodicFrequency ι) :
    periodicLongHeatCoefficient a k ≤
      periodicLongHeatMass ι a * Real.exp (-a*‖periodicFrequencyVector k‖^2) := by
  unfold periodicLongHeatCoefficient
  split_ifs with hk
  · exact mul_nonneg (periodicLongHeatMass_nonneg a) (Real.exp_pos _).le
  · have h := integral_mono_ae (periodicLongHeatCoefficient_integrable a ha k hk)
      ((periodicLongHeatMass_integrable (ι := ι) a ha).mul_const
        (Real.exp (-a*‖periodicFrequencyVector k‖^2)))
      (show ∀ᵐ t ∂volume.restrict (Ioi (1:ℝ)),
          t^(Fintype.card ι-1)*Real.exp (-2*a*t^2*‖periodicFrequencyVector k‖^2) ≤
          (t^(Fintype.card ι-1)*Real.exp (-a*t^2))*Real.exp (-a*‖periodicFrequencyVector k‖^2) from by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (periodicLongHeat_gaussian_bound a ha.le t ht.le k hk)
          (pow_nonneg (zero_lt_one.trans ht).le _))
    simpa only [integral_mul_const,periodicLongHeatMass] using h

lemma summable_periodicLongHeatCoefficient (a : ℝ) (ha : 0<a) :
    Summable (periodicLongHeatCoefficient (ι := ι) a) :=
  ((summable_periodicGaussian (ι := ι) a ha).mul_left (periodicLongHeatMass ι a)).of_nonneg_of_le
    (periodicLongHeatCoefficient_nonneg a) (periodicLongHeatCoefficient_bound a ha)

def periodicLongHeatRemainder (a : ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∑' k : PeriodicFrequency ι,periodicLongHeatCoefficient a k*(UnitAddTorus.mFourier k x).re

lemma periodicLongHeatRemainder_term_norm (a : ℝ) (k : PeriodicFrequency ι) (x : PeriodicTorus ι) :
    ‖periodicLongHeatCoefficient a k*(UnitAddTorus.mFourier k x).re‖ ≤
      periodicLongHeatCoefficient a k := by
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (periodicLongHeatCoefficient_nonneg a k)]
  have hb : ‖(UnitAddTorus.mFourier k x).re‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs,periodic_mFourier_norm_apply] using Complex.abs_re_le_norm (UnitAddTorus.mFourier k x)
  nlinarith [periodicLongHeatCoefficient_nonneg a k]

lemma periodicLongHeatRemainder_continuous (a : ℝ) (ha : 0<a) :
    Continuous (periodicLongHeatRemainder (ι := ι) a) := by
  apply continuous_tsum (fun k => ?_) (summable_periodicLongHeatCoefficient a ha)
    (periodicLongHeatRemainder_term_norm a)
  exact continuous_const.mul (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous)

lemma periodicLongHeatRemainder_norm_bound (a : ℝ) (ha : 0<a) (x : PeriodicTorus ι) :
    ‖periodicLongHeatRemainder a x‖ ≤
      periodicLongHeatMass ι a * ∑' k : PeriodicFrequency ι,Real.exp (-a*‖periodicFrequencyVector k‖^2) := by
  have hs := summable_periodicLongHeatCoefficient (ι := ι) a ha
  have hsn : Summable (fun k : PeriodicFrequency ι =>
      ‖periodicLongHeatCoefficient a k*(UnitAddTorus.mFourier k x).re‖) :=
    hs.of_nonneg_of_le (fun k => norm_nonneg _) (periodicLongHeatRemainder_term_norm a · x)
  have h := (norm_tsum_le_tsum_norm hsn).trans
    (Summable.tsum_le_tsum (periodicLongHeatRemainder_term_norm a · x) hsn hs)
  apply h.trans
  simpa only [tsum_mul_left] using Summable.tsum_le_tsum (periodicLongHeatCoefficient_bound a ha)
    hs ((summable_periodicGaussian (ι := ι) a ha).mul_left (periodicLongHeatMass ι a))

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLongHeatCoefficient_bound
#print axioms DGRHS.Periodic.summable_periodicLongHeatCoefficient
#print axioms DGRHS.Periodic.periodicLongHeatRemainder_continuous
#print axioms DGRHS.Periodic.periodicLongHeatRemainder_norm_bound
#check @DGRHS.Periodic.periodicLongHeatRemainder_norm_bound
