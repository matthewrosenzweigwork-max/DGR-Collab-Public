import DGRHS.Gaussian.GaussianLogShortRangeSource

/-! Genuine finite logarithmic scale measure, exact mass and Fourier Gram
feature. This new construction uses coefficient one and covers empty bands.
No full infrared normalization or physical moment conclusion is assumed. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators
namespace DGRHS.Gaussian

def gaussianLogBandMeasure (η δ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc η δ)).withDensity (fun t => ENNReal.ofReal t⁻¹)

lemma integrable_gaussianLogBandWeight (η δ : ℝ) (hη : 0 < η) :
    Integrable (fun t : ℝ => t⁻¹) (volume.restrict (Ioc η δ)) := by
  refine (integrable_const η⁻¹).mono' measurable_inv.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 := hη.trans ht.1
  rw [Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)]
  simpa only [one_div] using one_div_le_one_div_of_le hη ht.1.le

lemma ae_nonneg_gaussianLogBandWeight (η δ : ℝ) (hη : 0 < η) :
    ∀ᵐ t ∂volume.restrict (Ioc η δ), 0 ≤ t⁻¹ := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact inv_nonneg.mpr (hη.trans ht.1).le

lemma finite_gaussianLogBandMeasure (η δ : ℝ) (hη : 0 < η) :
    IsFiniteMeasure (gaussianLogBandMeasure η δ) := by
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable
    (integrable_gaussianLogBandWeight η δ hη).aestronglyMeasurable
    (ae_nonneg_gaussianLogBandWeight η δ hη)).2
    (integrable_gaussianLogBandWeight η δ hη)

lemma mass_gaussianLogBandMeasure (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ) :
    (gaussianLogBandMeasure η δ univ).toReal = Real.log (δ/η) := by
  unfold gaussianLogBandMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_nonneg_gaussianLogBandWeight η δ hη)
    (integrable_gaussianLogBandWeight η δ hη).aestronglyMeasurable]
  rw [← intervalIntegral.integral_of_le hηδ]
  exact integral_inv_of_pos hη (hη.trans_le hηδ)

lemma integral_gaussianLogBandMeasure (η δ : ℝ) (hη : 0 < η) (F : ℝ → ℝ) :
    (∫ t, F t ∂gaussianLogBandMeasure η δ) = ∫ t in Ioc η δ, t⁻¹*F t := by
  unfold gaussianLogBandMeasure
  rw [integral_withDensity_eq_integral_toReal_smul measurable_inv.ennreal_ofReal
    (Filter.Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_nonneg_gaussianLogBandWeight η δ hη] with t ht
  rw [ENNReal.toReal_ofReal ht]
  rfl

variable {ι : Type*} [Fintype ι]

def gaussianLogBand (η δ : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫ t in Ioc η δ, t⁻¹*Real.exp (-‖x‖^2/(2*t^2))

def gaussianLogBandFeature (η δ : ℝ) (hη : 0 < η) (x : EuclideanSpace ℝ ι) :
    Lp ℂ 2 ((gaussianLogBandMeasure η δ).prod (finiteStandardGaussian ι)) := by
  letI := finite_gaussianLogBandMeasure η δ hη
  exact gaussianScaleMixtureFeature (gaussianLogBandMeasure η δ) (gaussianRieszEuclideanCoordinates x)

lemma inner_gaussianLogBandFeature (η δ : ℝ) (hη : 0 < η) (x y : EuclideanSpace ℝ ι) :
    inner ℝ (gaussianLogBandFeature η δ hη x) (gaussianLogBandFeature η δ hη y) =
      gaussianLogBand η δ (x-y) := by
  letI := finite_gaussianLogBandMeasure η δ hη
  unfold gaussianLogBandFeature
  rw [inner_gaussianScaleMixtureFeature, integral_gaussianLogBandMeasure η δ hη]
  unfold gaussianRieszEuclideanCoordinates gaussianLogBand
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have he : (∑ i, (y i-x i)^2) = (∑ i, (x i-y i)^2) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change t⁻¹*Real.exp (-(∑ i, (y i-x i)^2)/(2*t^2)) =
    t⁻¹*Real.exp (-(∑ i, (x i-y i)^2)/(2*t^2))
  rw [he]

lemma norm_sq_gaussianLogBandFeature (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (x : EuclideanSpace ℝ ι) :
    ‖gaussianLogBandFeature η δ hη x‖^2 = Real.log (δ/η) := by
  letI := finite_gaussianLogBandMeasure η δ hη
  unfold gaussianLogBandFeature
  rw [norm_sq_gaussianScaleMixtureFeature, mass_gaussianLogBandMeasure η δ hη hηδ]

lemma stronglyMeasurable_gaussianLogBandFeature (η δ : ℝ) (hη : 0 < η) :
    StronglyMeasurable (gaussianLogBandFeature (ι := ι) η δ hη) := by
  letI := finite_gaussianLogBandMeasure η δ hη
  exact ((continuous_gaussianScaleMixtureFeature (gaussianLogBandMeasure η δ)).comp
    continuous_gaussianRieszEuclideanCoordinates).stronglyMeasurable

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogBandMeasure
#print axioms DGRHS.Gaussian.gaussianLogBandMeasure

#check @DGRHS.Gaussian.integrable_gaussianLogBandWeight
#print axioms DGRHS.Gaussian.integrable_gaussianLogBandWeight

#check @DGRHS.Gaussian.ae_nonneg_gaussianLogBandWeight
#print axioms DGRHS.Gaussian.ae_nonneg_gaussianLogBandWeight

#check @DGRHS.Gaussian.finite_gaussianLogBandMeasure
#print axioms DGRHS.Gaussian.finite_gaussianLogBandMeasure

#check @DGRHS.Gaussian.mass_gaussianLogBandMeasure
#print axioms DGRHS.Gaussian.mass_gaussianLogBandMeasure

#check @DGRHS.Gaussian.integral_gaussianLogBandMeasure
#print axioms DGRHS.Gaussian.integral_gaussianLogBandMeasure

#check @DGRHS.Gaussian.gaussianLogBand
#print axioms DGRHS.Gaussian.gaussianLogBand

#check @DGRHS.Gaussian.gaussianLogBandFeature
#print axioms DGRHS.Gaussian.gaussianLogBandFeature

#check @DGRHS.Gaussian.inner_gaussianLogBandFeature
#print axioms DGRHS.Gaussian.inner_gaussianLogBandFeature

#check @DGRHS.Gaussian.norm_sq_gaussianLogBandFeature
#print axioms DGRHS.Gaussian.norm_sq_gaussianLogBandFeature

#check @DGRHS.Gaussian.stronglyMeasurable_gaussianLogBandFeature
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogBandFeature
