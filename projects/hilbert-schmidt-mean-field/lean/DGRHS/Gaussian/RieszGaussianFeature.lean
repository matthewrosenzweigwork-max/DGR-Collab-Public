import DGRHS.Gaussian.GaussianScaleMixtureFeature
import DGRHS.Gaussian.RieszGaussianScale

/-! Actual Fourier feature for the Gaussian-profile truncated Riesz scale
integral in arxiv2609.02743v1, eq:HCRStruncDef. The coefficient c is explicit;
its profile normalization, continuity/centering, and Euclidean norm adapter
are subsequent obligations. The Gram identity is derived, not assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def rieszGaussianTruncatedKernel (c s η : ℝ) (v : ι → ℝ) : ℝ :=
  c * ∫ t in Ioi η, t ^ (-s - 1) * Real.exp (-(∑ i, (v i) ^ 2) / (2 * t ^ 2))

def rieszGaussianFourierFeature (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (a : ι → ℝ) : Lp ℂ 2 ((rieszGaussianScaleMeasure c s η).prod (finiteStandardGaussian ι)) := by
  letI := finite_rieszGaussianScaleMeasure c s η hc hs hη
  exact gaussianScaleMixtureFeature (rieszGaussianScaleMeasure c s η) a

lemma integral_rieszGaussianScaleMeasure (c s η : ℝ) (hc : 0 ≤ c) (hη : 0 < η)
    (F : ℝ → ℝ) :
    ∫ t, F t ∂rieszGaussianScaleMeasure c s η =
      c * ∫ t in Ioi η, t ^ (-s - 1) * F t := by
  have hm : Measurable (fun t => ENNReal.ofReal (rieszGaussianScaleWeight c s t)) := by
    unfold rieszGaussianScaleWeight
    fun_prop
  unfold rieszGaussianScaleMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))]
  have he : (fun t => (ENNReal.ofReal (rieszGaussianScaleWeight c s t)).toReal • F t)
      =ᵐ[volume.restrict (Ioi η)] fun t => c * (t ^ (-s - 1) * F t) := by
    filter_upwards [ae_nonneg_rieszGaussianScaleWeight c s η hc hη] with t ht
    rw [ENNReal.toReal_ofReal ht]
    simp only [smul_eq_mul, rieszGaussianScaleWeight]
    ring
  rw [integral_congr_ae he, integral_const_mul]

lemma inner_rieszGaussianFourierFeature (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (a b : ι → ℝ) :
    inner ℝ (rieszGaussianFourierFeature c s η hc hs hη a)
      (rieszGaussianFourierFeature c s η hc hs hη b) =
      rieszGaussianTruncatedKernel c s η (fun i => b i - a i) := by
  letI := finite_rieszGaussianScaleMeasure c s η hc hs hη
  unfold rieszGaussianFourierFeature
  rw [inner_gaussianScaleMixtureFeature, integral_rieszGaussianScaleMeasure c s η hc hη]
  rfl

lemma norm_sq_rieszGaussianFourierFeature (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (a : ι → ℝ) :
    ‖rieszGaussianFourierFeature c s η hc hs hη a‖ ^ 2 = c / s * η ^ (-s) := by
  letI := finite_rieszGaussianScaleMeasure c s η hc hs hη
  unfold rieszGaussianFourierFeature
  rw [norm_sq_gaussianScaleMixtureFeature, mass_rieszGaussianScaleMeasure c s η hc hs hη]

lemma rieszGaussianTruncatedKernel_zero (c s η : ℝ) (hs : 0 < s) (hη : 0 < η) :
    rieszGaussianTruncatedKernel c s η (fun _ : ι => 0) = c / s * η ^ (-s) := by
  unfold rieszGaussianTruncatedKernel
  simp only [zero_pow, Finset.sum_const_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
  have hi := integral_rieszGaussianScaleWeight c s η hs hη
  simpa [rieszGaussianScaleWeight, integral_const_mul] using hi

end DGRHS.Gaussian
#check DGRHS.Gaussian.rieszGaussianTruncatedKernel
#check DGRHS.Gaussian.rieszGaussianFourierFeature
#check DGRHS.Gaussian.integral_rieszGaussianScaleMeasure
#check DGRHS.Gaussian.inner_rieszGaussianFourierFeature
#check DGRHS.Gaussian.norm_sq_rieszGaussianFourierFeature
#check DGRHS.Gaussian.rieszGaussianTruncatedKernel_zero
#print axioms DGRHS.Gaussian.rieszGaussianTruncatedKernel
#print axioms DGRHS.Gaussian.rieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.integral_rieszGaussianScaleMeasure
#print axioms DGRHS.Gaussian.inner_rieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.norm_sq_rieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.rieszGaussianTruncatedKernel_zero
