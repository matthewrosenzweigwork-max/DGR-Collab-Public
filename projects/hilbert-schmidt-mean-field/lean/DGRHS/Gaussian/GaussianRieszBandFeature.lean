import DGRHS.Gaussian.RieszGaussianFeature
import DGRHS.Gaussian.GaussianScaleMixtureRegularity

/-! Actual positive finite Gaussian scale-band measure and its Fourier Gram
feature. The band is identified with the difference of the two actual physical
truncations; independence/covariance are not supplied as hypotheses. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def rieszGaussianBandMeasure (c s η δ : ℝ) : Measure ℝ :=
  (rieszGaussianScaleMeasure c s η).restrict (Iic δ)

lemma finite_rieszGaussianBandMeasure (c s η δ : ℝ) (hc : 0 ≤ c)
    (hs : 0 < s) (hη : 0 < η) : IsFiniteMeasure (rieszGaussianBandMeasure c s η δ) := by
  letI := finite_rieszGaussianScaleMeasure c s η hc hs hη
  unfold rieszGaussianBandMeasure
  infer_instance

lemma rieszGaussianScaleMeasure_restrict_above (c s η δ : ℝ) (hηδ : η ≤ δ) :
    (rieszGaussianScaleMeasure c s η).restrict (Ioi δ) = rieszGaussianScaleMeasure c s δ := by
  unfold rieszGaussianScaleMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict_of_subset]
  exact fun t ht => lt_of_le_of_lt hηδ ht

lemma mass_rieszGaussianBandMeasure_le (c s η δ : ℝ) (hc : 0 ≤ c)
    (hs : 0 < s) (hη : 0 < η) :
    (rieszGaussianBandMeasure c s η δ univ).toReal ≤ c/s*η^(-s) := by
  letI := finite_rieszGaussianScaleMeasure c s η hc hs hη
  rw [← mass_rieszGaussianScaleMeasure c s η hc hs hη]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  unfold rieszGaussianBandMeasure
  rw [Measure.restrict_apply_univ]
  exact measure_mono (subset_univ _)

def rieszGaussianBandKernel (c s η δ : ℝ) (v : ι → ℝ) : ℝ :=
  ∫ t, Real.exp (-(∑ i, (v i)^2)/(2*t^2)) ∂rieszGaussianBandMeasure c s η δ

lemma integrable_rieszGaussianProfile_scale (c s η : ℝ) (hc : 0 ≤ c)
    (hs : 0 < s) (hη : 0 < η) (v : ι → ℝ) :
    Integrable (fun t => Real.exp (-(∑ i, (v i)^2)/(2*t^2)))
      (rieszGaussianScaleMeasure c s η) := by
  letI := finite_rieszGaussianScaleMeasure c s η hc hs hη
  have hm : Measurable (fun t : ℝ => Real.exp (-(∑ i, (v i)^2)/(2*t^2))) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.2
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Finset.sum_nonneg (fun i hi => sq_nonneg _))) (by positivity)

lemma rieszGaussianBandKernel_eq_difference (c s η δ : ℝ) (hc : 0 ≤ c)
    (hs : 0 < s) (hη : 0 < η) (hηδ : η ≤ δ) (v : ι → ℝ) :
    rieszGaussianBandKernel c s η δ v =
      rieszGaussianTruncatedKernel c s η v - rieszGaussianTruncatedKernel c s δ v := by
  have hδ : 0 < δ := lt_of_lt_of_le hη hηδ
  have hi := integrable_rieszGaussianProfile_scale c s η hc hs hη v
  have he := integral_add_compl (s := Iic δ) measurableSet_Iic hi
  rw [compl_Iic, rieszGaussianScaleMeasure_restrict_above c s η δ hηδ,
    integral_rieszGaussianScaleMeasure c s δ hc hδ,
    integral_rieszGaussianScaleMeasure c s η hc hη] at he
  change rieszGaussianBandKernel c s η δ v + rieszGaussianTruncatedKernel c s δ v =
    rieszGaussianTruncatedKernel c s η v at he
  linarith

def rieszGaussianBandFeature (c s η δ : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (a : ι → ℝ) : Lp ℂ 2 ((rieszGaussianBandMeasure c s η δ).prod (finiteStandardGaussian ι)) := by
  letI := finite_rieszGaussianBandMeasure c s η δ hc hs hη
  exact gaussianScaleMixtureFeature (rieszGaussianBandMeasure c s η δ) a

lemma inner_rieszGaussianBandFeature (c s η δ : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (a b : ι → ℝ) :
    inner ℝ (rieszGaussianBandFeature c s η δ hc hs hη a)
      (rieszGaussianBandFeature c s η δ hc hs hη b) =
      rieszGaussianBandKernel c s η δ (fun i => b i-a i) := by
  letI := finite_rieszGaussianBandMeasure c s η δ hc hs hη
  unfold rieszGaussianBandFeature rieszGaussianBandKernel
  exact inner_gaussianScaleMixtureFeature _ a b

lemma norm_sq_rieszGaussianBandFeature_le (c s η δ : ℝ) (hc : 0 ≤ c)
    (hs : 0 < s) (hη : 0 < η) (a : ι → ℝ) :
    ‖rieszGaussianBandFeature c s η δ hc hs hη a‖^2 ≤ c/s*η^(-s) := by
  letI := finite_rieszGaussianBandMeasure c s η δ hc hs hη
  unfold rieszGaussianBandFeature
  rw [norm_sq_gaussianScaleMixtureFeature]
  exact mass_rieszGaussianBandMeasure_le c s η δ hc hs hη

end DGRHS.Gaussian

#check DGRHS.Gaussian.rieszGaussianBandMeasure
#print axioms DGRHS.Gaussian.rieszGaussianBandMeasure

#check DGRHS.Gaussian.finite_rieszGaussianBandMeasure
#print axioms DGRHS.Gaussian.finite_rieszGaussianBandMeasure

#check DGRHS.Gaussian.rieszGaussianScaleMeasure_restrict_above
#print axioms DGRHS.Gaussian.rieszGaussianScaleMeasure_restrict_above

#check DGRHS.Gaussian.mass_rieszGaussianBandMeasure_le
#print axioms DGRHS.Gaussian.mass_rieszGaussianBandMeasure_le

#check DGRHS.Gaussian.rieszGaussianBandKernel
#print axioms DGRHS.Gaussian.rieszGaussianBandKernel

#check DGRHS.Gaussian.integrable_rieszGaussianProfile_scale
#print axioms DGRHS.Gaussian.integrable_rieszGaussianProfile_scale

#check DGRHS.Gaussian.rieszGaussianBandKernel_eq_difference
#print axioms DGRHS.Gaussian.rieszGaussianBandKernel_eq_difference

#check DGRHS.Gaussian.rieszGaussianBandFeature
#print axioms DGRHS.Gaussian.rieszGaussianBandFeature

#check DGRHS.Gaussian.inner_rieszGaussianBandFeature
#print axioms DGRHS.Gaussian.inner_rieszGaussianBandFeature

#check DGRHS.Gaussian.norm_sq_rieszGaussianBandFeature_le
#print axioms DGRHS.Gaussian.norm_sq_rieszGaussianBandFeature_le
