import DGRHS.Gaussian.GaussianRieszBandOperator

/-! Actual Bochner-centered Fourier feature for the SAME physical band. The
Gram identity, canonical condition and boundedness are derived; no positive
definiteness or desired diagonal/cap premise is assumed. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszEuclideanBandFeature (s η δ : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) : Lp ℂ 2
      ((rieszGaussianBandMeasure (gaussianRieszSourceCoefficient s) s η δ).prod (finiteStandardGaussian ι)) :=
  rieszGaussianBandFeature _ s η δ (gaussianRieszSourceCoefficient_pos s hs).le hs hη
    (gaussianRieszEuclideanCoordinates x)

lemma stronglyMeasurable_gaussianRieszEuclideanBandFeature (s η δ : ℝ) (hs : 0 < s) (hη : 0 < η) :
    StronglyMeasurable (gaussianRieszEuclideanBandFeature (ι := ι) s η δ hs hη) := by
  letI := finite_rieszGaussianBandMeasure (gaussianRieszSourceCoefficient s) s η δ
    (gaussianRieszSourceCoefficient_pos s hs).le hs hη
  exact (continuous_gaussianScaleMixtureFeature _).comp
    continuous_gaussianRieszEuclideanCoordinates |>.stronglyMeasurable

lemma inner_gaussianRieszEuclideanBandFeature (s η δ : ℝ) (hs : 0 < s) (hη : 0 < η)
    (hηδ : η ≤ δ) (x y : EuclideanSpace ℝ ι) :
    inner ℝ (gaussianRieszEuclideanBandFeature s η δ hs hη x)
      (gaussianRieszEuclideanBandFeature s η δ hs hη y) = gaussianRieszEuclideanBand s η δ (x-y) := by
  unfold gaussianRieszEuclideanBandFeature
  rw [inner_rieszGaussianBandFeature]
  change rieszGaussianBandKernel (gaussianRieszSourceCoefficient s) s η δ
    (gaussianRieszEuclideanCoordinates (y-x)) = _
  rw [← gaussianRieszEuclideanBand_eq_scaleKernel s η δ hs hη hηδ (y-x)]
  unfold gaussianRieszEuclideanBand gaussianRieszEuclideanTruncation
  rw [norm_sub_rev]

lemma norm_gaussianRieszEuclideanBandFeature_le (s η δ : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) :
    ‖gaussianRieszEuclideanBandFeature s η δ hs hη x‖ ≤
      Real.sqrt (gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  have hD : 0 ≤ gaussianRieszSourceCoefficient s/s*η^(-s) := by
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  have hb := norm_sq_rieszGaussianBandFeature_le (gaussianRieszSourceCoefficient s) s η δ
    (gaussianRieszSourceCoefficient_pos s hs).le hs hη (gaussianRieszEuclideanCoordinates x)
  change ‖gaussianRieszEuclideanBandFeature s η δ hs hη x‖^2 ≤ _ at hb
  nlinarith [Real.sq_sqrt hD, Real.sqrt_nonneg (gaussianRieszSourceCoefficient s/s*η^(-s)),
    norm_nonneg (gaussianRieszEuclideanBandFeature s η δ hs hη x)]

lemma integrable_gaussianRieszEuclideanBandFeature (s η δ : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    Integrable (gaussianRieszEuclideanBandFeature s η δ hs hη) μ :=
  (integrable_const (Real.sqrt (gaussianRieszSourceCoefficient s/s*η^(-s)))).mono'
    (stronglyMeasurable_gaussianRieszEuclideanBandFeature s η δ hs hη).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_gaussianRieszEuclideanBandFeature_le s η δ hs hη))

def centeredGaussianRieszEuclideanBandFeature (s η δ : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) : Lp ℂ 2
      ((rieszGaussianBandMeasure (gaussianRieszSourceCoefficient s) s η δ).prod (finiteStandardGaussian ι)) :=
  gaussianRieszEuclideanBandFeature s η δ hs hη x - ∫ y,gaussianRieszEuclideanBandFeature s η δ hs hη y ∂μ

lemma norm_centeredGaussianRieszEuclideanBandFeature_le (s η δ : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    ‖centeredGaussianRieszEuclideanBandFeature s η δ hs hη μ x‖ ≤
      2*Real.sqrt (gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  have hi := integrable_gaussianRieszEuclideanBandFeature (ι := ι) s η δ hs hη μ
  have hm : ‖∫ y,gaussianRieszEuclideanBandFeature s η δ hs hη y ∂μ‖ ≤
      Real.sqrt (gaussianRieszSourceCoefficient s/s*η^(-s)) := by
    calc
      _ ≤ ∫ y,‖gaussianRieszEuclideanBandFeature s η δ hs hη y‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, Real.sqrt (gaussianRieszSourceCoefficient s/s*η^(-s)) ∂μ :=
        integral_mono_ae hi.norm (integrable_const _)
          (Filter.Eventually.of_forall (norm_gaussianRieszEuclideanBandFeature_le s η δ hs hη))
      _ = _ := by simp
  unfold centeredGaussianRieszEuclideanBandFeature
  exact (norm_sub_le _ _).trans (by
    have hx := norm_gaussianRieszEuclideanBandFeature_le (ι := ι) s η δ hs hη x
    linarith)

lemma inner_centeredGaussianRieszEuclideanBandFeature (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (a b : EuclideanSpace ℝ ι) :
    inner ℝ (centeredGaussianRieszEuclideanBandFeature s η δ hs hη (gaussianRieszDensityMeasure ρ) a)
      (centeredGaussianRieszEuclideanBandFeature s η δ hs hη (gaussianRieszDensityMeasure ρ) b) =
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ) (a,b) := by
  let μ := gaussianRieszDensityMeasure ρ
  let κ := gaussianRieszEuclideanBandFeature (ι := ι) s η δ hs hη
  let m := ∫ x, κ x ∂μ
  have hi : Integrable κ μ := integrable_gaussianRieszEuclideanBandFeature s η δ hs hη μ
  have hp := (memLp_gaussianRieszBandPair s η δ hs hη hηδ ha ρ M hM hρ).integrable (by norm_num)
  have hl (v : Lp ℂ 2 ((rieszGaussianBandMeasure (gaussianRieszSourceCoefficient s) s η δ).prod (finiteStandardGaussian ι))) :
      (∫ x, inner ℝ (κ x) v ∂μ) = inner ℝ m v := by
    simp_rw [real_inner_comm v (κ _)]
    rw [integral_inner hi]
    exact real_inner_comm _ _
  have hd : (∫ x, (∫ y,inner ℝ (κ x) (κ y) ∂μ) ∂μ) = inner ℝ m m := by
    simp_rw [integral_inner hi]
    exact hl m
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  rw [integral_prod _ hp]
  unfold gaussianRieszBandPair
  simp_rw [← inner_gaussianRieszEuclideanBandFeature s η δ hs hη hηδ]
  change inner ℝ (κ a-m) (κ b-m) = inner ℝ (κ a) (κ b) -
    (∫ y,inner ℝ (κ a) (κ y) ∂μ) - (∫ x,inner ℝ (κ x) (κ b) ∂μ) +
    (∫ x, (∫ y,inner ℝ (κ x) (κ y) ∂μ) ∂μ)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, integral_inner hi, hl, hd]
  ring

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszEuclideanBandFeature
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanBandFeature

#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanBandFeature
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanBandFeature

#check DGRHS.Gaussian.inner_gaussianRieszEuclideanBandFeature
#print axioms DGRHS.Gaussian.inner_gaussianRieszEuclideanBandFeature

#check DGRHS.Gaussian.norm_gaussianRieszEuclideanBandFeature_le
#print axioms DGRHS.Gaussian.norm_gaussianRieszEuclideanBandFeature_le

#check DGRHS.Gaussian.integrable_gaussianRieszEuclideanBandFeature
#print axioms DGRHS.Gaussian.integrable_gaussianRieszEuclideanBandFeature

#check DGRHS.Gaussian.centeredGaussianRieszEuclideanBandFeature
#print axioms DGRHS.Gaussian.centeredGaussianRieszEuclideanBandFeature

#check DGRHS.Gaussian.norm_centeredGaussianRieszEuclideanBandFeature_le
#print axioms DGRHS.Gaussian.norm_centeredGaussianRieszEuclideanBandFeature_le

#check DGRHS.Gaussian.inner_centeredGaussianRieszEuclideanBandFeature
#print axioms DGRHS.Gaussian.inner_centeredGaussianRieszEuclideanBandFeature
