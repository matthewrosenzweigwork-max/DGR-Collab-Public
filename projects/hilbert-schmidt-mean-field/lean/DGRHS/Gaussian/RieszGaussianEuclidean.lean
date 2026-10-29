import DGRHS.Gaussian.RieszGaussianFeature
import DGRHS.Gaussian.RieszGaussianNormalization
import DGRHS.Gaussian.GaussianScaleMixtureRegularity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Euclidean/source adapter for the actual normalized Gaussian-profile
truncation in arxiv2609.02743v1, eq:HCRStruncDef. No coordinate-norm or
profile-normalization identity is assumed. The Gaussian coefficient is the
checked actual source reciprocal/Gamma integral. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszEuclideanCoordinates (x : EuclideanSpace ℝ ι) : ι → ℝ := fun i => x i

lemma continuous_gaussianRieszEuclideanCoordinates :
    Continuous (gaussianRieszEuclideanCoordinates (ι := ι)) := by
  unfold gaussianRieszEuclideanCoordinates
  fun_prop

def gaussianRieszEuclideanProfile (x : EuclideanSpace ℝ ι) : ℝ := Real.exp (-‖x‖ ^ 2 / 2)

def gaussianRieszEuclideanScaleProfile (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  t ^ (-(Fintype.card ι : ℝ)) * gaussianRieszEuclideanProfile (t⁻¹ • x)

def gaussianRieszEuclideanTruncation (s η : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  gaussianRieszSourceCoefficient s * ∫ t in Ioi η,
    t ^ (-s - 1) * Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))

def gaussianRieszEuclideanFourierFeature (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) : Lp ℂ 2
      ((rieszGaussianScaleMeasure (gaussianRieszSourceCoefficient s) s η).prod (finiteStandardGaussian ι)) :=
  rieszGaussianFourierFeature (gaussianRieszSourceCoefficient s) s η
    (gaussianRieszSourceCoefficient_pos s hs).le hs hη (gaussianRieszEuclideanCoordinates x)

lemma stronglyMeasurable_gaussianRieszEuclideanFourierFeature (s η : ℝ) (hs : 0 < s) (hη : 0 < η) :
    StronglyMeasurable (gaussianRieszEuclideanFourierFeature (ι := ι) s η hs hη) := by
  letI := finite_rieszGaussianScaleMeasure (gaussianRieszSourceCoefficient s) s η
    (gaussianRieszSourceCoefficient_pos s hs).le hs hη
  exact (continuous_gaussianScaleMixtureFeature _).comp
    continuous_gaussianRieszEuclideanCoordinates |>.stronglyMeasurable

lemma gaussianRieszEuclideanTruncation_coordinates (s η : ℝ) (x : EuclideanSpace ℝ ι) :
    gaussianRieszEuclideanTruncation s η x =
      rieszGaussianTruncatedKernel (gaussianRieszSourceCoefficient s) s η
        (gaussianRieszEuclideanCoordinates x) := by
  unfold gaussianRieszEuclideanTruncation rieszGaussianTruncatedKernel gaussianRieszEuclideanCoordinates
  rw [EuclideanSpace.real_norm_sq_eq]

lemma inner_gaussianRieszEuclideanFourierFeature (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (gaussianRieszEuclideanFourierFeature s η hs hη x)
      (gaussianRieszEuclideanFourierFeature s η hs hη y) = gaussianRieszEuclideanTruncation s η (x - y) := by
  unfold gaussianRieszEuclideanFourierFeature
  rw [inner_rieszGaussianFourierFeature]
  change rieszGaussianTruncatedKernel (gaussianRieszSourceCoefficient s) s η
    (gaussianRieszEuclideanCoordinates (y - x)) = _
  rw [← gaussianRieszEuclideanTruncation_coordinates s η (y - x)]
  unfold gaussianRieszEuclideanTruncation
  rw [norm_sub_rev]

lemma norm_sq_gaussianRieszEuclideanFourierFeature (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) :
    ‖gaussianRieszEuclideanFourierFeature s η hs hη x‖ ^ 2 =
      gaussianRieszSourceCoefficient s / s * η ^ (-s) :=
  norm_sq_rieszGaussianFourierFeature _ _ _ _ _ _ _

lemma gaussianRieszEuclideanScaleProfile_source_integrand (s t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℝ ι) :
    t ^ ((Fintype.card ι : ℝ) - s) * gaussianRieszEuclideanScaleProfile t x / t =
      t ^ (-s - 1) * Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2)) := by
  have hn : ‖t⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / t ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, mul_pow, inv_pow]
    ring
  have hc : t ^ ((Fintype.card ι : ℝ) - s) * t ^ (-(Fintype.card ι : ℝ)) / t =
      t ^ (-s - 1) := by
    rw [← Real.rpow_add ht, show (Fintype.card ι : ℝ) - s + -(Fintype.card ι : ℝ) = -s by ring,
      ← Real.rpow_sub_one ht.ne']
  unfold gaussianRieszEuclideanScaleProfile gaussianRieszEuclideanProfile
  rw [hn]
  have he : -(‖x‖ ^ 2 / t ^ 2) / 2 = -‖x‖ ^ 2 / (2 * t ^ 2) := by ring
  rw [he]
  calc
    _ = (t ^ ((Fintype.card ι : ℝ) - s) * t ^ (-(Fintype.card ι : ℝ)) / t) *
        Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2)) := by ring
    _ = _ := by rw [hc]

lemma gaussianRieszEuclideanTruncation_source_formula (s η : ℝ) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) :
    gaussianRieszEuclideanTruncation s η x =
      gaussianRieszSourceCoefficient s * ∫ t in Ioi η,
        t ^ ((Fintype.card ι : ℝ) - s) * gaussianRieszEuclideanScaleProfile t x / t := by
  unfold gaussianRieszEuclideanTruncation
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (gaussianRieszEuclideanScaleProfile_source_integrand s t (hη.trans ht) x).symm

end DGRHS.Gaussian
#check DGRHS.Gaussian.gaussianRieszEuclideanCoordinates
#check DGRHS.Gaussian.continuous_gaussianRieszEuclideanCoordinates
#check DGRHS.Gaussian.gaussianRieszEuclideanProfile
#check DGRHS.Gaussian.gaussianRieszEuclideanScaleProfile
#check DGRHS.Gaussian.gaussianRieszEuclideanTruncation
#check DGRHS.Gaussian.gaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.gaussianRieszEuclideanTruncation_coordinates
#check DGRHS.Gaussian.inner_gaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.norm_sq_gaussianRieszEuclideanFourierFeature
#check DGRHS.Gaussian.gaussianRieszEuclideanScaleProfile_source_integrand
#check DGRHS.Gaussian.gaussianRieszEuclideanTruncation_source_formula
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanCoordinates
#print axioms DGRHS.Gaussian.continuous_gaussianRieszEuclideanCoordinates
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanProfile
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanScaleProfile
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanTruncation
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanTruncation_coordinates
#print axioms DGRHS.Gaussian.inner_gaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.norm_sq_gaussianRieszEuclideanFourierFeature
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanScaleProfile_source_integrand
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanTruncation_source_formula
