import DGRHS.Gaussian.RieszGaussianEuclidean

/-! Actual Euclidean Bochner centering of the source-normalized Gaussian Riesz cutoff.
The SAME constructed Fourier feature has the exact source centered physical kernel. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma norm_gaussianRieszEuclideanFourierFeature (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (a : EuclideanSpace ℝ ι) :
    ‖gaussianRieszEuclideanFourierFeature s η hs hη a‖ = Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_gaussianRieszEuclideanFourierFeature]

lemma integrable_gaussianRieszEuclideanFourierFeature (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    Integrable (gaussianRieszEuclideanFourierFeature s η hs hη) μ := by
  apply (integrable_const (Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)))).mono'
    (stronglyMeasurable_gaussianRieszEuclideanFourierFeature s η hs hη).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a => (norm_gaussianRieszEuclideanFourierFeature s η hs hη a).le)

def centeredGaussianRieszEuclideanFourierFeature (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) (a : EuclideanSpace ℝ ι) :
    Lp ℂ 2 ((rieszGaussianScaleMeasure (gaussianRieszSourceCoefficient s) s η).prod (finiteStandardGaussian ι)) :=
  gaussianRieszEuclideanFourierFeature s η hs hη a - ∫ x, gaussianRieszEuclideanFourierFeature s η hs hη x ∂μ

def centeredGaussianRieszEuclideanTruncatedKernel (s η : ℝ) (μ : Measure (EuclideanSpace ℝ ι)) (a b : EuclideanSpace ℝ ι) : ℝ :=
  gaussianRieszEuclideanTruncation s η (a - b) -
    (∫ y, gaussianRieszEuclideanTruncation s η (a - y) ∂μ) -
    (∫ x, gaussianRieszEuclideanTruncation s η (x - b) ∂μ) +
    ∫ x, ∫ y, gaussianRieszEuclideanTruncation s η (x - y) ∂μ ∂μ

lemma stronglyMeasurable_centeredGaussianRieszEuclideanFourierFeature (s η : ℝ)
     (hs : 0 < s) (hη : 0 < η) (μ : Measure (EuclideanSpace ℝ ι)) :
    StronglyMeasurable (centeredGaussianRieszEuclideanFourierFeature s η hs hη μ) :=
  (stronglyMeasurable_gaussianRieszEuclideanFourierFeature s η hs hη).sub stronglyMeasurable_const

lemma integral_centeredGaussianRieszEuclideanFourierFeature (s η : ℝ)
     (hs : 0 < s) (hη : 0 < η) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    ∫ a, centeredGaussianRieszEuclideanFourierFeature s η hs hη μ a ∂μ = 0 := by
  unfold centeredGaussianRieszEuclideanFourierFeature
  rw [integral_sub (integrable_gaussianRieszEuclideanFourierFeature s η hs hη μ) (integrable_const _)]
  simp

lemma norm_centeredGaussianRieszEuclideanFourierFeature_le (s η : ℝ)
     (hs : 0 < s) (hη : 0 < η) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (a : EuclideanSpace ℝ ι) :
    ‖centeredGaussianRieszEuclideanFourierFeature s η hs hη μ a‖ ≤ 2 * Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)) := by
  have hm : ‖∫ x, gaussianRieszEuclideanFourierFeature s η hs hη x ∂μ‖ ≤
      Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)) := by
    calc
      _ ≤ ∫ x, ‖gaussianRieszEuclideanFourierFeature s η hs hη x‖ ∂μ := norm_integral_le_integral_norm _
      _ = _ := by simp_rw [norm_gaussianRieszEuclideanFourierFeature]; simp
  unfold centeredGaussianRieszEuclideanFourierFeature
  calc
    _ ≤ ‖gaussianRieszEuclideanFourierFeature s η hs hη a‖ +
        ‖∫ x, gaussianRieszEuclideanFourierFeature s η hs hη x ∂μ‖ := norm_sub_le _ _
    _ ≤ 2 * Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)) := by rw [norm_gaussianRieszEuclideanFourierFeature]; linarith

lemma norm_sq_centeredGaussianRieszEuclideanFourierFeature_le (s η : ℝ)
     (hs : 0 < s) (hη : 0 < η) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (a : EuclideanSpace ℝ ι) :
    ‖centeredGaussianRieszEuclideanFourierFeature s η hs hη μ a‖ ^ 2 ≤ 4 * (gaussianRieszSourceCoefficient s / s * η ^ (-s)) := by
  have hnonneg : 0 ≤ gaussianRieszSourceCoefficient s / s * η ^ (-s) :=
    mul_nonneg (div_nonneg (gaussianRieszSourceCoefficient_pos s hs).le hs.le) (Real.rpow_nonneg hη.le _)
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (norm_centeredGaussianRieszEuclideanFourierFeature_le s η hs hη μ a) 2
  simpa only [mul_pow, Real.sq_sqrt hnonneg, show (2 : ℝ) ^ 2 = 4 by norm_num] using hb

lemma memLp_centeredGaussianRieszEuclideanFourierFeature (s η : ℝ)
     (hs : 0 < s) (hη : 0 < η) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) : MemLp (centeredGaussianRieszEuclideanFourierFeature s η hs hη μ) p μ := by
  apply (memLp_const (2 * Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)))).of_le
    (stronglyMeasurable_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ).aestronglyMeasurable
  filter_upwards with a
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
  exact norm_centeredGaussianRieszEuclideanFourierFeature_le s η hs hη μ a

lemma inner_centeredGaussianRieszEuclideanFourierFeature (s η : ℝ)
     (hs : 0 < s) (hη : 0 < η) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (a b : EuclideanSpace ℝ ι) :
    inner ℝ (centeredGaussianRieszEuclideanFourierFeature s η hs hη μ a)
      (centeredGaussianRieszEuclideanFourierFeature s η hs hη μ b) =
      centeredGaussianRieszEuclideanTruncatedKernel s η μ a b := by
  let κ := gaussianRieszEuclideanFourierFeature (ι := ι) s η hs hη
  let m := ∫ x, κ x ∂μ
  have hi : Integrable κ μ := integrable_gaussianRieszEuclideanFourierFeature s η hs hη μ
  have hl (v : Lp ℂ 2 ((rieszGaussianScaleMeasure (gaussianRieszSourceCoefficient s) s η).prod (finiteStandardGaussian ι))) :
      (∫ x, inner ℝ (κ x) v ∂μ) = inner ℝ m v := by
    simp_rw [real_inner_comm v (κ _)]
    rw [integral_inner hi]
    exact real_inner_comm _ _
  have hd : (∫ x, ∫ y, inner ℝ (κ x) (κ y) ∂μ ∂μ) = inner ℝ m m := by
    simp_rw [integral_inner hi]
    exact hl m
  unfold centeredGaussianRieszEuclideanTruncatedKernel
  simp_rw [← inner_gaussianRieszEuclideanFourierFeature s η hs hη]
  change inner ℝ (κ a - m) (κ b - m) =
    inner ℝ (κ a) (κ b) - (∫ y, inner ℝ (κ a) (κ y) ∂μ) -
      (∫ x, inner ℝ (κ x) (κ b) ∂μ) + ∫ x, ∫ y, inner ℝ (κ x) (κ y) ∂μ ∂μ
  rw [inner_sub_left, inner_sub_right, inner_sub_right, integral_inner hi, hl, hd]
  ring

end DGRHS.Gaussian
#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.norm_gaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.integrable_gaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.centeredGaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel
#check DGRHS.Gaussian.stronglyMeasurable_centeredGaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.integral_centeredGaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.norm_centeredGaussianRieszEuclideanFourierFeature_le
#check DGRHS.Gaussian.norm_sq_centeredGaussianRieszEuclideanFourierFeature_le
#check DGRHS.Gaussian.memLp_centeredGaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.inner_centeredGaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.norm_gaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.integrable_gaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.centeredGaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel
#print axioms DGRHS.Gaussian.stronglyMeasurable_centeredGaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.integral_centeredGaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.norm_centeredGaussianRieszEuclideanFourierFeature_le
#print axioms DGRHS.Gaussian.norm_sq_centeredGaussianRieszEuclideanFourierFeature_le
#print axioms DGRHS.Gaussian.memLp_centeredGaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.inner_centeredGaussianRieszEuclideanFourierFeature
