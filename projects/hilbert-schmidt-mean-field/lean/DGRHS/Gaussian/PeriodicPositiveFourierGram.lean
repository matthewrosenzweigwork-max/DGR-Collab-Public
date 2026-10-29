import DGRHS.Gaussian.PeriodicHeatFeatureGram
import DGRHS.Gaussian.FeatureRatePhysical
import DGRHS.Gaussian.HoeffdingLinearity

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. A positive summable Fourier coefficient sequence
produces an actual pointwise Hilbert Gram kernel on the normalized unit torus.
Centering uses the true Bochner mean for any probability law; no PSD, diagonal,
particle bound or centered-kernel identity is an input. Square-root summability
is used only for continuity of the feature. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ComplexConjugate lp InnerProductSpace ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicPositiveFourierKernel (a : PeriodicFrequency ι → ℝ) (x : PeriodicTorus ι) : ℝ :=
  (∑' k : PeriodicFrequency ι, (a k : ℂ) * UnitAddTorus.mFourier k x).re

def periodicPositiveFourierFeatureCoefficient (a : PeriodicFrequency ι → ℝ)
    (x : PeriodicTorus ι) (k : PeriodicFrequency ι) : ℂ :=
  (Real.sqrt (a k) : ℂ) * UnitAddTorus.mFourier k x

lemma periodicPositiveFourierFeatureCoefficient_norm (a : PeriodicFrequency ι → ℝ)
    (x : PeriodicTorus ι) (k : PeriodicFrequency ι) :
    ‖periodicPositiveFourierFeatureCoefficient a x k‖ = Real.sqrt (a k) := by
  simp only [periodicPositiveFourierFeatureCoefficient, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), periodic_mFourier_norm_apply, mul_one]

lemma periodicPositiveFourierFeatureCoefficient_mem (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (x : PeriodicTorus ι) :
    Memℓp (periodicPositiveFourierFeatureCoefficient a x) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  simpa only [ENNReal.toReal_ofNat, periodicPositiveFourierFeatureCoefficient_norm,
    Real.rpow_two, Real.sq_sqrt (ha _)] using hs

def periodicPositiveFourierFeature (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (x : PeriodicTorus ι) :
    PeriodicHeatFeatureSpace ι :=
  ⟨periodicPositiveFourierFeatureCoefficient a x,
    periodicPositiveFourierFeatureCoefficient_mem a ha hs x⟩

lemma periodicPositiveFourierFeature_apply (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (x : PeriodicTorus ι)
    (k : PeriodicFrequency ι) :
    periodicPositiveFourierFeature a ha hs x k =
      periodicPositiveFourierFeatureCoefficient a x k := rfl

lemma periodicPositiveFourierSeries_summable (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (x : PeriodicTorus ι) :
    Summable (fun k : PeriodicFrequency ι => (a k : ℂ) * UnitAddTorus.mFourier k x) := by
  apply Summable.of_norm
  simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha _),
    periodic_mFourier_norm_apply, mul_one] using hs

lemma periodicPositiveFourierFeatureCoefficient_inner (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (x y : PeriodicTorus ι) (k : PeriodicFrequency ι) :
    inner ℝ (periodicPositiveFourierFeatureCoefficient a y k)
      (periodicPositiveFourierFeatureCoefficient a x k) =
      ((a k : ℂ) * UnitAddTorus.mFourier k (x - y)).re := by
  rw [Complex.inner]
  unfold periodicPositiveFourierFeatureCoefficient
  rw [map_mul, Complex.conj_ofReal, periodic_mFourier_argument_sub]
  have hroot : (Real.sqrt (a k) : ℂ) * (Real.sqrt (a k) : ℂ) = (a k : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    exact Real.mul_self_sqrt (ha k)
  congr 1
  calc
    _ = ((Real.sqrt (a k) : ℂ) * (Real.sqrt (a k) : ℂ)) *
        (UnitAddTorus.mFourier k x * conj (UnitAddTorus.mFourier k y)) := by ring
    _ = _ := by rw [hroot]

lemma periodicPositiveFourierFeature_gram (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (x y : PeriodicTorus ι) :
    inner ℝ (periodicPositiveFourierFeature a ha hs x)
      (periodicPositiveFourierFeature a ha hs y) = periodicPositiveFourierKernel a (x - y) := by
  rw [real_inner_comm, lp.inner_eq_tsum]
  simp only [periodicPositiveFourierFeature_apply, periodicPositiveFourierFeatureCoefficient_inner a ha]
  exact (Complex.re_tsum (periodicPositiveFourierSeries_summable a ha hs (x - y))).symm

lemma periodicPositiveFourierKernel_zero (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) :
    periodicPositiveFourierKernel a 0 = ∑' k, a k := by
  have hzero (k : PeriodicFrequency ι) : UnitAddTorus.mFourier k (0 : PeriodicTorus ι) = 1 := by
    simp [UnitAddTorus.mFourier, fourier_apply]
  unfold periodicPositiveFourierKernel
  rw [Complex.re_tsum (periodicPositiveFourierSeries_summable a ha hs 0)]
  simp only [hzero, mul_one, Complex.ofReal_re]

lemma periodicPositiveFourierFeature_norm_sq (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (x : PeriodicTorus ι) :
    ‖periodicPositiveFourierFeature a ha hs x‖ ^ 2 = ∑' k, a k := by
  simpa only [real_inner_self_eq_norm_sq, sub_self,
    periodicPositiveFourierKernel_zero a ha hs] using periodicPositiveFourierFeature_gram a ha hs x x

lemma periodicPositiveFourierFeature_norm_le (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (x : PeriodicTorus ι) :
    ‖periodicPositiveFourierFeature a ha hs x‖ ≤ Real.sqrt (∑' k, a k) := by
  have hsum : (0 : ℝ) ≤ ∑' k : PeriodicFrequency ι, a k := tsum_nonneg ha
  nlinarith [periodicPositiveFourierFeature_norm_sq a ha hs x, Real.sq_sqrt hsum,
    Real.sqrt_nonneg (∑' k, a k), norm_nonneg (periodicPositiveFourierFeature a ha hs x)]

lemma periodicPositiveFourierFeature_continuous (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (hr : Summable (fun k => Real.sqrt (a k))) :
    Continuous (periodicPositiveFourierFeature a ha hs) := by
  have he : periodicPositiveFourierFeature a ha hs = fun x =>
      ∑' k : PeriodicFrequency ι, lp.single 2 k (periodicPositiveFourierFeatureCoefficient a x k) := by
    funext x
    exact (lp.hasSum_single (by norm_num) (periodicPositiveFourierFeature a ha hs x)).tsum_eq.symm
  rw [he]
  apply continuous_tsum (fun k =>
    (lp.isometry_single (p := 2) (E := fun _ : PeriodicFrequency ι => ℂ) k).continuous.comp
      (continuous_const.mul (UnitAddTorus.mFourier k).continuous)) hr
  intro k x
  change ‖(lp.single 2 k (periodicPositiveFourierFeatureCoefficient a x k) :
    PeriodicHeatFeatureSpace ι)‖ ≤ _
  rw [lp.norm_single (by norm_num), periodicPositiveFourierFeatureCoefficient_norm]

lemma periodicPositiveFourierFeature_integrable (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (hr : Summable (fun k => Real.sqrt (a k)))
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    Integrable (periodicPositiveFourierFeature a ha hs) μ :=
  (integrable_const (Real.sqrt (∑' k, a k))).mono'
    (periodicPositiveFourierFeature_continuous a ha hs hr).aestronglyMeasurable
    (Eventually.of_forall (periodicPositiveFourierFeature_norm_le a ha hs))

lemma periodicPositiveFourierKernel_continuous (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) :
    Continuous (periodicPositiveFourierKernel a) := by
  apply Complex.continuous_re.comp
  apply periodicFourierSeries_continuous
  simpa only [Complex.norm_real, Real.norm_of_nonneg (ha _)] using hs

lemma periodicPositiveFourierKernel_pair_integrable (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveFourierKernel a (p.1 - p.2)) (μ.prod μ) :=
  ((periodicPositiveFourierKernel_continuous a ha hs).comp
    (continuous_fst.sub continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

def periodicCenteredPositiveFourierFeature (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (μ : Measure (PeriodicTorus ι)) (x : PeriodicTorus ι) : PeriodicHeatFeatureSpace ι :=
  periodicPositiveFourierFeature a ha hs x - ∫ y, periodicPositiveFourierFeature a ha hs y ∂μ

lemma periodicCenteredPositiveFourierFeature_norm_le (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (hr : Summable (fun k => Real.sqrt (a k)))
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (x : PeriodicTorus ι) :
    ‖periodicCenteredPositiveFourierFeature a ha hs μ x‖ ≤ 2 * Real.sqrt (∑' k, a k) := by
  have hi := periodicPositiveFourierFeature_integrable a ha hs hr μ
  have hm : ‖∫ y, periodicPositiveFourierFeature a ha hs y ∂μ‖ ≤ Real.sqrt (∑' k, a k) := by
    calc
      _ ≤ ∫ y, ‖periodicPositiveFourierFeature a ha hs y‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : PeriodicTorus ι, Real.sqrt (∑' k, a k) ∂μ :=
        integral_mono_ae hi.norm (integrable_const _)
          (Eventually.of_forall (periodicPositiveFourierFeature_norm_le a ha hs))
      _ = _ := by simp
  unfold periodicCenteredPositiveFourierFeature
  exact (norm_sub_le _ _).trans (by
    have hx := periodicPositiveFourierFeature_norm_le a ha hs x
    linarith)

lemma periodicCenteredPositiveFourierFeature_gram (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (hr : Summable (fun k => Real.sqrt (a k)))
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (x y : PeriodicTorus ι) :
    inner ℝ (periodicCenteredPositiveFourierFeature a ha hs μ x)
      (periodicCenteredPositiveFourierFeature a ha hs μ y) =
      hoeffdingCentered μ (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        periodicPositiveFourierKernel a (p.1 - p.2)) (x,y) := by
  let κ := periodicPositiveFourierFeature a ha hs
  let m := ∫ z, κ z ∂μ
  have hi : Integrable κ μ := periodicPositiveFourierFeature_integrable a ha hs hr μ
  have hp := periodicPositiveFourierKernel_pair_integrable a ha hs μ
  have hl (v : PeriodicHeatFeatureSpace ι) : (∫ z, inner ℝ (κ z) v ∂μ) = inner ℝ m v := by
    simp_rw [real_inner_comm v (κ _)]
    rw [integral_inner hi]
    exact real_inner_comm _ _
  have hd : (∫ z, (∫ w, inner ℝ (κ z) (κ w) ∂μ) ∂μ) = inner ℝ m m := by
    simp_rw [integral_inner hi]
    exact hl m
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  rw [integral_prod _ hp]
  simp_rw [← periodicPositiveFourierFeature_gram a ha hs]
  change inner ℝ (κ x - m) (κ y - m) = inner ℝ (κ x) (κ y) -
    (∫ w, inner ℝ (κ x) (κ w) ∂μ) - (∫ z, inner ℝ (κ z) (κ y) ∂μ) +
    (∫ z, (∫ w, inner ℝ (κ z) (κ w) ∂μ) ∂μ)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, integral_inner hi, hl, hd]
  ring

lemma periodicCenteredPositiveFourierFeature_norm_sq_le (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (hr : Summable (fun k => Real.sqrt (a k)))
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (x : PeriodicTorus ι) :
    ‖periodicCenteredPositiveFourierFeature a ha hs μ x‖ ^ 2 ≤ 4 * (∑' k, a k) := by
  have hsum : (0 : ℝ) ≤ ∑' k : PeriodicFrequency ι, a k := tsum_nonneg ha
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (periodicCenteredPositiveFourierFeature_norm_le a ha hs hr μ x) 2
  simpa only [mul_pow, Real.sq_sqrt hsum, show (2 : ℝ)^2 = 4 by norm_num] using h

lemma periodicPositiveFourier_centered_bound (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (hr : Summable (fun k => Real.sqrt (a k)))
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    ‖hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveFourierKernel a (q.1 - q.2)) p‖ ≤ 4 * (∑' k, a k) := by
  have hsum : (0 : ℝ) ≤ ∑' k : PeriodicFrequency ι, a k := tsum_nonneg ha
  rw [← periodicCenteredPositiveFourierFeature_gram a ha hs hr μ p.1 p.2]
  calc
    _ ≤ ‖periodicCenteredPositiveFourierFeature a ha hs μ p.1‖ *
        ‖periodicCenteredPositiveFourierFeature a ha hs μ p.2‖ := norm_inner_le_norm _ _
    _ ≤ (2 * Real.sqrt (∑' k, a k)) * (2 * Real.sqrt (∑' k, a k)) :=
      mul_le_mul (periodicCenteredPositiveFourierFeature_norm_le a ha hs hr μ p.1)
        (periodicCenteredPositiveFourierFeature_norm_le a ha hs hr μ p.2) (norm_nonneg _) (by positivity)
    _ = _ := by nlinarith [Real.sq_sqrt hsum]

lemma periodicPositiveFourier_centered_particle_cap (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a)
    (hr : Summable (fun k => Real.sqrt (a k)))
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    -(∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else
      hoeffdingCentered μ (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        periodicPositiveFourierKernel a (p.1 - p.2)) (x i,x j)) / (2 * (N : ℝ)) ≤
      2 * (∑' k, a k) := by
  let κ := periodicCenteredPositiveFourierFeature a ha hs μ
  simp_rw [← periodicCenteredPositiveFourierFeature_gram a ha hs hr μ]
  change -(∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else inner ℝ (κ (x i)) (κ (x j))) /
    (2 * (N : ℝ)) ≤ _
  rw [feature_particle_off_diagonal_sum]
  have hsum : (∑ i : Fin N, ‖κ (x i)‖ ^ 2) ≤ (N : ℝ) * (4 * (∑' k, a k)) := by
    calc
      _ ≤ ∑ _ : Fin N, 4 * (∑' k, a k) := Finset.sum_le_sum
        (fun i _ => periodicCenteredPositiveFourierFeature_norm_sq_le a ha hs hr μ (x i))
      _ = _ := by simp
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hN)
  rw [div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))]
  nlinarith [sq_nonneg ‖∑ i : Fin N, κ (x i)‖]

end DGRHS.Periodic
