import DGRHS.Gaussian.RieszGaussianFeature
import DGRHS.Gaussian.GaussianScaleMixtureRegularity

/-! Bochner centering of the SAME constructed Gaussian cutoff Fourier feature.
The centered physical scale-integral kernel and uniform diagonal bound are
proved here. The source profile coefficient and Euclidean adapter remain separate. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma stronglyMeasurable_rieszGaussianFourierFeature (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) :
    StronglyMeasurable (rieszGaussianFourierFeature (ι := ι) c s η hc hs hη) := by
  letI := finite_rieszGaussianScaleMeasure c s η hc hs hη
  exact stronglyMeasurable_gaussianScaleMixtureFeature _

lemma norm_rieszGaussianFourierFeature (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (a : ι → ℝ) :
    ‖rieszGaussianFourierFeature c s η hc hs hη a‖ = Real.sqrt (c / s * η ^ (-s)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_rieszGaussianFourierFeature]

lemma integrable_rieszGaussianFourierFeature (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] :
    Integrable (rieszGaussianFourierFeature c s η hc hs hη) μ := by
  apply (integrable_const (Real.sqrt (c / s * η ^ (-s)))).mono'
    (stronglyMeasurable_rieszGaussianFourierFeature c s η hc hs hη).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a => (norm_rieszGaussianFourierFeature c s η hc hs hη a).le)

def centeredRieszGaussianFourierFeature (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (ι → ℝ)) (a : ι → ℝ) :
    Lp ℂ 2 ((rieszGaussianScaleMeasure c s η).prod (finiteStandardGaussian ι)) :=
  rieszGaussianFourierFeature c s η hc hs hη a - ∫ x, rieszGaussianFourierFeature c s η hc hs hη x ∂μ

def centeredRieszGaussianTruncatedKernel (c s η : ℝ) (μ : Measure (ι → ℝ)) (a b : ι → ℝ) : ℝ :=
  rieszGaussianTruncatedKernel c s η (fun i => b i - a i) -
    (∫ y, rieszGaussianTruncatedKernel c s η (fun i => y i - a i) ∂μ) -
    (∫ x, rieszGaussianTruncatedKernel c s η (fun i => b i - x i) ∂μ) +
    ∫ x, ∫ y, rieszGaussianTruncatedKernel c s η (fun i => y i - x i) ∂μ ∂μ

lemma stronglyMeasurable_centeredRieszGaussianFourierFeature (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (μ : Measure (ι → ℝ)) :
    StronglyMeasurable (centeredRieszGaussianFourierFeature c s η hc hs hη μ) :=
  (stronglyMeasurable_rieszGaussianFourierFeature c s η hc hs hη).sub stronglyMeasurable_const

lemma integral_centeredRieszGaussianFourierFeature (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] :
    ∫ a, centeredRieszGaussianFourierFeature c s η hc hs hη μ a ∂μ = 0 := by
  unfold centeredRieszGaussianFourierFeature
  rw [integral_sub (integrable_rieszGaussianFourierFeature c s η hc hs hη μ) (integrable_const _)]
  simp

lemma norm_centeredRieszGaussianFourierFeature_le (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (a : ι → ℝ) :
    ‖centeredRieszGaussianFourierFeature c s η hc hs hη μ a‖ ≤ 2 * Real.sqrt (c / s * η ^ (-s)) := by
  have hm : ‖∫ x, rieszGaussianFourierFeature c s η hc hs hη x ∂μ‖ ≤
      Real.sqrt (c / s * η ^ (-s)) := by
    calc
      _ ≤ ∫ x, ‖rieszGaussianFourierFeature c s η hc hs hη x‖ ∂μ := norm_integral_le_integral_norm _
      _ = _ := by simp_rw [norm_rieszGaussianFourierFeature]; simp
  unfold centeredRieszGaussianFourierFeature
  calc
    _ ≤ ‖rieszGaussianFourierFeature c s η hc hs hη a‖ +
        ‖∫ x, rieszGaussianFourierFeature c s η hc hs hη x ∂μ‖ := norm_sub_le _ _
    _ ≤ 2 * Real.sqrt (c / s * η ^ (-s)) := by rw [norm_rieszGaussianFourierFeature]; linarith

lemma norm_sq_centeredRieszGaussianFourierFeature_le (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (a : ι → ℝ) :
    ‖centeredRieszGaussianFourierFeature c s η hc hs hη μ a‖ ^ 2 ≤ 4 * (c / s * η ^ (-s)) := by
  have hnonneg : 0 ≤ c / s * η ^ (-s) :=
    mul_nonneg (div_nonneg hc hs.le) (Real.rpow_nonneg hη.le _)
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (norm_centeredRieszGaussianFourierFeature_le c s η hc hs hη μ a) 2
  simpa only [mul_pow, Real.sq_sqrt hnonneg, show (2 : ℝ) ^ 2 = 4 by norm_num] using hb

lemma memLp_centeredRieszGaussianFourierFeature (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) : MemLp (centeredRieszGaussianFourierFeature c s η hc hs hη μ) p μ := by
  apply (memLp_const (2 * Real.sqrt (c / s * η ^ (-s)))).of_le
    (stronglyMeasurable_centeredRieszGaussianFourierFeature c s η hc hs hη μ).aestronglyMeasurable
  filter_upwards with a
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
  exact norm_centeredRieszGaussianFourierFeature_le c s η hc hs hη μ a

lemma inner_centeredRieszGaussianFourierFeature (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (a b : ι → ℝ) :
    inner ℝ (centeredRieszGaussianFourierFeature c s η hc hs hη μ a)
      (centeredRieszGaussianFourierFeature c s η hc hs hη μ b) =
      centeredRieszGaussianTruncatedKernel c s η μ a b := by
  let κ := rieszGaussianFourierFeature (ι := ι) c s η hc hs hη
  let m := ∫ x, κ x ∂μ
  have hi : Integrable κ μ := integrable_rieszGaussianFourierFeature c s η hc hs hη μ
  have hl (v : Lp ℂ 2 ((rieszGaussianScaleMeasure c s η).prod (finiteStandardGaussian ι))) :
      (∫ x, inner ℝ (κ x) v ∂μ) = inner ℝ m v := by
    simp_rw [real_inner_comm v (κ _)]
    rw [integral_inner hi]
    exact real_inner_comm _ _
  have hd : (∫ x, ∫ y, inner ℝ (κ x) (κ y) ∂μ ∂μ) = inner ℝ m m := by
    simp_rw [integral_inner hi]
    exact hl m
  unfold centeredRieszGaussianTruncatedKernel
  simp_rw [← inner_rieszGaussianFourierFeature c s η hc hs hη]
  change inner ℝ (κ a - m) (κ b - m) =
    inner ℝ (κ a) (κ b) - (∫ y, inner ℝ (κ a) (κ y) ∂μ) -
      (∫ x, inner ℝ (κ x) (κ b) ∂μ) + ∫ x, ∫ y, inner ℝ (κ x) (κ y) ∂μ ∂μ
  rw [inner_sub_left, inner_sub_right, inner_sub_right, integral_inner hi, hl, hd]
  ring

end DGRHS.Gaussian
#check DGRHS.Gaussian.stronglyMeasurable_rieszGaussianFourierFeature
#check DGRHS.Gaussian.norm_rieszGaussianFourierFeature
#check DGRHS.Gaussian.integrable_rieszGaussianFourierFeature
#check DGRHS.Gaussian.centeredRieszGaussianFourierFeature
#check DGRHS.Gaussian.centeredRieszGaussianTruncatedKernel
#check DGRHS.Gaussian.stronglyMeasurable_centeredRieszGaussianFourierFeature
#check DGRHS.Gaussian.integral_centeredRieszGaussianFourierFeature
#check DGRHS.Gaussian.norm_centeredRieszGaussianFourierFeature_le
#check DGRHS.Gaussian.norm_sq_centeredRieszGaussianFourierFeature_le
#check DGRHS.Gaussian.memLp_centeredRieszGaussianFourierFeature
#check DGRHS.Gaussian.inner_centeredRieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.stronglyMeasurable_rieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.norm_rieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.integrable_rieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.centeredRieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.centeredRieszGaussianTruncatedKernel
#print axioms DGRHS.Gaussian.stronglyMeasurable_centeredRieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.integral_centeredRieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.norm_centeredRieszGaussianFourierFeature_le
#print axioms DGRHS.Gaussian.norm_sq_centeredRieszGaussianFourierFeature_le
#print axioms DGRHS.Gaussian.memLp_centeredRieszGaussianFourierFeature
#print axioms DGRHS.Gaussian.inner_centeredRieszGaussianFourierFeature
