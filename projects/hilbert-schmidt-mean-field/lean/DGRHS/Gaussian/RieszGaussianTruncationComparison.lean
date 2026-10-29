import DGRHS.Gaussian.RieszGaussianFullScale

/-! Actual full/short/long scale split for the source-normalized Gaussian Riesz
kernel away from its singular origin. The short integral uses Ioc; the single
upper endpoint is volume-null. No comparison or kernel identity is a premise. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszEuclideanShortRange (s η : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  gaussianRieszSourceCoefficient s * ∫ t in Ioc 0 η,
    t ^ (-s - 1) * Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))

lemma integrableOn_gaussianRieszEuclidean_full_scale (s : ℝ) (hs : 0 < s)
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (-s - 1) * Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))) (Ioi 0) := by
  have hi := integrableOn_gaussianRiesz_full_scale s (‖x‖ ^ 2 / 2) hs
    (by have h := norm_pos_iff.mpr hx; positivity)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  congr 2
  ring

lemma gaussianRieszEuclideanTruncation_nonneg (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) : 0 ≤ gaussianRieszEuclideanTruncation s η x := by
  apply mul_nonneg (gaussianRieszSourceCoefficient_pos s hs).le
  exact setIntegral_nonneg measurableSet_Ioi (fun t ht =>
    mul_nonneg (Real.rpow_nonneg (hη.trans ht).le _) (Real.exp_pos _).le)

lemma gaussianRieszEuclideanShortRange_nonneg (s η : ℝ) (hs : 0 < s)
    (x : EuclideanSpace ℝ ι) : 0 ≤ gaussianRieszEuclideanShortRange s η x := by
  apply mul_nonneg (gaussianRieszSourceCoefficient_pos s hs).le
  exact setIntegral_nonneg measurableSet_Ioc (fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le)

lemma gaussianRieszEuclideanShortRange_source_formula (s η : ℝ)
    (x : EuclideanSpace ℝ ι) :
    gaussianRieszEuclideanShortRange s η x = gaussianRieszSourceCoefficient s *
      ∫ t in Ioc 0 η, t ^ ((Fintype.card ι : ℝ) - s) * gaussianRieszEuclideanScaleProfile t x / t := by
  unfold gaussianRieszEuclideanShortRange
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc (fun t ht =>
    (gaussianRieszEuclideanScaleProfile_source_integrand s t ht.1 x).symm)

lemma gaussianRieszEuclidean_full_short_long_split (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    ‖x‖ ^ (-s) / s =
      gaussianRieszEuclideanShortRange s η x + gaussianRieszEuclideanTruncation s η x := by
  have hi := integrableOn_gaussianRieszEuclidean_full_scale s hs x hx
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi hη.le))
  rw [intervalIntegral.integral_of_le hη.le] at hsplit
  rw [← gaussianRieszEuclidean_full_scale s hs x hx]
  unfold gaussianRieszEuclideanShortRange gaussianRieszEuclideanTruncation
  rw [← mul_add, hsplit]

lemma gaussianRieszEuclideanShortRange_eq_remainder (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    gaussianRieszEuclideanShortRange s η x = ‖x‖ ^ (-s) / s - gaussianRieszEuclideanTruncation s η x := by
  have h := gaussianRieszEuclidean_full_short_long_split s η hs hη x hx
  linarith

lemma gaussianRieszEuclidean_truncation_bounds (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    0 ≤ gaussianRieszEuclideanTruncation s η x ∧
    gaussianRieszEuclideanTruncation s η x ≤ ‖x‖ ^ (-s) / s ∧
    0 ≤ gaussianRieszEuclideanShortRange s η x ∧
    gaussianRieszEuclideanShortRange s η x ≤ ‖x‖ ^ (-s) / s := by
  have h := gaussianRieszEuclidean_full_short_long_split s η hs hη x hx
  have hg := gaussianRieszEuclideanTruncation_nonneg s η hs hη x
  have hf := gaussianRieszEuclideanShortRange_nonneg s η hs x
  exact ⟨hg, by linarith, hf, by linarith⟩

end DGRHS.Gaussian
#check DGRHS.Gaussian.gaussianRieszEuclideanShortRange
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanShortRange
#check DGRHS.Gaussian.integrableOn_gaussianRieszEuclidean_full_scale
#print axioms DGRHS.Gaussian.integrableOn_gaussianRieszEuclidean_full_scale
#check DGRHS.Gaussian.gaussianRieszEuclideanTruncation_nonneg
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanTruncation_nonneg
#check DGRHS.Gaussian.gaussianRieszEuclideanShortRange_nonneg
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanShortRange_nonneg
#check DGRHS.Gaussian.gaussianRieszEuclideanShortRange_source_formula
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanShortRange_source_formula
#check DGRHS.Gaussian.gaussianRieszEuclidean_full_short_long_split
#print axioms DGRHS.Gaussian.gaussianRieszEuclidean_full_short_long_split
#check DGRHS.Gaussian.gaussianRieszEuclideanShortRange_eq_remainder
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanShortRange_eq_remainder
#check DGRHS.Gaussian.gaussianRieszEuclidean_truncation_bounds
#print axioms DGRHS.Gaussian.gaussianRieszEuclidean_truncation_bounds
