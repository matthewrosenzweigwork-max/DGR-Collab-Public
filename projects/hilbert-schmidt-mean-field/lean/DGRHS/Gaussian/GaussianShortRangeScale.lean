import DGRHS.Gaussian.GaussianEuclideanIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual probability scale law for the sharp Gaussian short-range L2 estimate.
For a=d/2-s>0, density a eta^(-a)t^(a-1) on (0,eta] has mass1. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian

def gaussianShortRangeScaleWeight (a η t : ℝ) : ℝ := a * η ^ (-a) * t ^ (a - 1)
def gaussianShortRangeScaleMeasure (a η : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 η)).withDensity (fun t => ENNReal.ofReal (gaussianShortRangeScaleWeight a η t))

lemma integrable_gaussianShortRangeScaleWeight (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    Integrable (gaussianShortRangeScaleWeight a η) (volume.restrict (Ioc 0 η)) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hη.le).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < a - 1))
  exact hi.const_mul (a * η ^ (-a))

lemma ae_nonneg_gaussianShortRangeScaleWeight (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 η), 0 ≤ gaussianShortRangeScaleWeight a η t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg hη.le _)) (Real.rpow_nonneg ht.1.le _)

lemma integral_gaussianShortRangeScaleWeight (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    (∫ t in Ioc 0 η, gaussianShortRangeScaleWeight a η t) = 1 := by
  unfold gaussianShortRangeScaleWeight
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hη.le,
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < a - 1)),
    show a - 1 + 1 = a by ring, Real.zero_rpow ha.ne', sub_zero,
    Real.rpow_neg hη.le]
  have hp := (Real.rpow_pos_of_pos hη a).ne'
  field_simp

lemma mass_gaussianShortRangeScaleMeasure (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    (gaussianShortRangeScaleMeasure a η Set.univ).toReal = 1 := by
  unfold gaussianShortRangeScaleMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_nonneg_gaussianShortRangeScaleWeight a η ha hη)
    (integrable_gaussianShortRangeScaleWeight a η ha hη).aestronglyMeasurable]
  exact integral_gaussianShortRangeScaleWeight a η ha hη

lemma probability_gaussianShortRangeScaleMeasure (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    IsProbabilityMeasure (gaussianShortRangeScaleMeasure a η) :=
  ⟨(ENNReal.toReal_eq_one_iff _).mp (mass_gaussianShortRangeScaleMeasure a η ha hη)⟩

lemma ae_pos_gaussianShortRangeScaleMeasure (a η : ℝ) :
    ∀ᵐ t ∂gaussianShortRangeScaleMeasure a η, 0 < t := by
  unfold gaussianShortRangeScaleMeasure
  apply withDensity_absolutelyContinuous
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ht.1

end DGRHS.Gaussian
#check DGRHS.Gaussian.gaussianShortRangeScaleWeight
#print axioms DGRHS.Gaussian.gaussianShortRangeScaleWeight
#check DGRHS.Gaussian.gaussianShortRangeScaleMeasure
#print axioms DGRHS.Gaussian.gaussianShortRangeScaleMeasure
#check DGRHS.Gaussian.integrable_gaussianShortRangeScaleWeight
#print axioms DGRHS.Gaussian.integrable_gaussianShortRangeScaleWeight
#check DGRHS.Gaussian.ae_nonneg_gaussianShortRangeScaleWeight
#print axioms DGRHS.Gaussian.ae_nonneg_gaussianShortRangeScaleWeight
#check DGRHS.Gaussian.integral_gaussianShortRangeScaleWeight
#print axioms DGRHS.Gaussian.integral_gaussianShortRangeScaleWeight
#check DGRHS.Gaussian.mass_gaussianShortRangeScaleMeasure
#print axioms DGRHS.Gaussian.mass_gaussianShortRangeScaleMeasure
#check DGRHS.Gaussian.probability_gaussianShortRangeScaleMeasure
#print axioms DGRHS.Gaussian.probability_gaussianShortRangeScaleMeasure
#check DGRHS.Gaussian.ae_pos_gaussianShortRangeScaleMeasure
#print axioms DGRHS.Gaussian.ae_pos_gaussianShortRangeScaleMeasure
