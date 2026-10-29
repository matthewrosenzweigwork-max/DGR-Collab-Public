import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The actual finite scale measure c t^(-s-1) dt for a truncated Gaussian
Riesz feature. Here c is an explicit nonnegative coefficient; its identification
with the source's profile normalization is a subsequent obligation. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian

def rieszGaussianScaleWeight (c s t : ℝ) : ℝ := c * t ^ (-s - 1)

def rieszGaussianScaleMeasure (c s η : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi η)).withDensity
    (fun t => ENNReal.ofReal (rieszGaussianScaleWeight c s t))

lemma integrable_rieszGaussianScaleWeight (c s η : ℝ) (hs : 0 < s) (hη : 0 < η) :
    Integrable (rieszGaussianScaleWeight c s) (volume.restrict (Ioi η)) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) hη).const_mul c

lemma ae_nonneg_rieszGaussianScaleWeight (c s η : ℝ) (hc : 0 ≤ c) (hη : 0 < η) :
    ∀ᵐ t ∂volume.restrict (Ioi η), 0 ≤ rieszGaussianScaleWeight c s t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg hc (Real.rpow_nonneg (le_of_lt (hη.trans ht)) _)

lemma integral_rieszGaussianScaleWeight (c s η : ℝ) (hs : 0 < s) (hη : 0 < η) :
    ∫ t in Ioi η, rieszGaussianScaleWeight c s t = c / s * η ^ (-s) := by
  unfold rieszGaussianScaleWeight
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) hη]
  rw [show -s - 1 + 1 = -s by ring]
  ring

lemma finite_rieszGaussianScaleMeasure (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) :
    IsFiniteMeasure (rieszGaussianScaleMeasure c s η) := by
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable
    (integrable_rieszGaussianScaleWeight c s η hs hη).aestronglyMeasurable
    (ae_nonneg_rieszGaussianScaleWeight c s η hc hη)).2
    (integrable_rieszGaussianScaleWeight c s η hs hη)

lemma mass_rieszGaussianScaleMeasure (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) :
    (rieszGaussianScaleMeasure c s η Set.univ).toReal = c / s * η ^ (-s) := by
  unfold rieszGaussianScaleMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_nonneg_rieszGaussianScaleWeight c s η hc hη)
    (integrable_rieszGaussianScaleWeight c s η hs hη).aestronglyMeasurable]
  exact integral_rieszGaussianScaleWeight c s η hs hη

end DGRHS.Gaussian
#check DGRHS.Gaussian.rieszGaussianScaleWeight
#check DGRHS.Gaussian.rieszGaussianScaleMeasure
#check DGRHS.Gaussian.integrable_rieszGaussianScaleWeight
#check DGRHS.Gaussian.ae_nonneg_rieszGaussianScaleWeight
#check DGRHS.Gaussian.integral_rieszGaussianScaleWeight
#check DGRHS.Gaussian.finite_rieszGaussianScaleMeasure
#check DGRHS.Gaussian.mass_rieszGaussianScaleMeasure
#print axioms DGRHS.Gaussian.rieszGaussianScaleWeight
#print axioms DGRHS.Gaussian.rieszGaussianScaleMeasure
#print axioms DGRHS.Gaussian.integrable_rieszGaussianScaleWeight
#print axioms DGRHS.Gaussian.ae_nonneg_rieszGaussianScaleWeight
#print axioms DGRHS.Gaussian.integral_rieszGaussianScaleWeight
#print axioms DGRHS.Gaussian.finite_rieszGaussianScaleMeasure
#print axioms DGRHS.Gaussian.mass_rieszGaussianScaleMeasure
