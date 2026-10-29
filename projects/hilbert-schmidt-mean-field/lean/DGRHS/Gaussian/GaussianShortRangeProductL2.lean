import DGRHS.Gaussian.GaussianShortRangeScale
import DGRHS.Gaussian.FeatureRateMoments

/-! Actual normalized Gaussian scale product-L2 construction and Jensen estimate.
All section integrability is derived from the actual product square integral. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianNormalizedScale (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  t ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))

lemma measurable_gaussianNormalizedScale :
    Measurable (fun p : ℝ × EuclideanSpace ℝ ι => gaussianNormalizedScale p.1 p.2) := by
  unfold gaussianNormalizedScale
  fun_prop

lemma integrable_gaussianNormalizedScale_sq (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : EuclideanSpace ℝ ι => gaussianNormalizedScale t x ^ 2) := by
  simpa only [gaussianNormalizedScale, mul_pow] using
    (integrable_gaussianEuclidean_scale_sq (ι := ι) t ht).const_mul
      ((t ^ (-(Fintype.card ι : ℝ) / 2)) ^ 2)

lemma integral_gaussianNormalizedScale_sq (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ ι, gaussianNormalizedScale t x ^ 2) =
      Real.pi ^ ((Fintype.card ι : ℝ) / 2) := by
  simp_rw [gaussianNormalizedScale, mul_pow]
  rw [integral_const_mul, integral_gaussianEuclidean_scale_sq t ht,
    ← Real.rpow_natCast, ← Real.rpow_mul ht.le,
    show (-(Fintype.card ι : ℝ) / 2) * ((2 : ℕ) : ℝ) = -(Fintype.card ι : ℝ) by norm_num]
  calc
    _ = Real.pi ^ ((Fintype.card ι : ℝ) / 2) *
        (t ^ (-(Fintype.card ι : ℝ)) * t ^ (Fintype.card ι : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, mul_one]

lemma integrable_gaussianNormalizedScale_sq_product (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ ι => gaussianNormalizedScale p.1 p.2 ^ 2)
      ((gaussianShortRangeScaleMeasure a η).prod volume) := by
  letI := probability_gaussianShortRangeScaleMeasure a η ha hη
  apply (integrable_prod_iff (measurable_gaussianNormalizedScale.pow_const 2).aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_pos_gaussianShortRangeScaleMeasure a η] with t ht
    exact integrable_gaussianNormalizedScale_sq t ht
  · apply (integrable_const (Real.pi ^ ((Fintype.card ι : ℝ) / 2))).congr
    filter_upwards [ae_pos_gaussianShortRangeScaleMeasure a η] with t ht
    simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (integral_gaussianNormalizedScale_sq t ht).symm

def gaussianNormalizedScaleMean (a η : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫ t, gaussianNormalizedScale t x ∂gaussianShortRangeScaleMeasure a η

lemma stronglyMeasurable_gaussianNormalizedScaleMean (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    StronglyMeasurable (gaussianNormalizedScaleMean (ι := ι) a η) := by
  letI := probability_gaussianShortRangeScaleMeasure a η ha hη
  exact measurable_gaussianNormalizedScale.stronglyMeasurable.integral_prod_left'

lemma ae_gaussianNormalizedScaleMean_sq_le (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    ∀ᵐ x : EuclideanSpace ℝ ι ∂volume,
      gaussianNormalizedScaleMean a η x ^ 2 ≤
        ∫ t, gaussianNormalizedScale t x ^ 2 ∂gaussianShortRangeScaleMeasure a η := by
  letI := probability_gaussianShortRangeScaleMeasure a η ha hη
  have hi := integrable_gaussianNormalizedScale_sq_product (ι := ι) a η ha hη
  filter_upwards [hi.prod_left_ae] with x hx
  have hm : MemLp (fun t => gaussianNormalizedScale t x) 2 (gaussianShortRangeScaleMeasure a η) :=
    (memLp_two_iff_integrable_sq (by unfold gaussianNormalizedScale; fun_prop)).2 hx
  exact integral_sq_mean_le _ (hm.integrable (by norm_num)) hx

lemma memLp_gaussianNormalizedScaleMean (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    MemLp (gaussianNormalizedScaleMean (ι := ι) a η) 2 volume := by
  letI := probability_gaussianShortRangeScaleMeasure a η ha hη
  apply (memLp_two_iff_integrable_sq
    (stronglyMeasurable_gaussianNormalizedScaleMean a η ha hη).aestronglyMeasurable).2
  apply (integrable_gaussianNormalizedScale_sq_product (ι := ι) a η ha hη).integral_prod_right.mono'
    ((stronglyMeasurable_gaussianNormalizedScaleMean a η ha hη).pow 2).aestronglyMeasurable
  filter_upwards [ae_gaussianNormalizedScaleMean_sq_le (ι := ι) a η ha hη] with x hx
  change ‖gaussianNormalizedScaleMean a η x ^ 2‖ ≤ _
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx

lemma integral_gaussianNormalizedScaleMean_sq_le (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    (∫ x : EuclideanSpace ℝ ι, gaussianNormalizedScaleMean a η x ^ 2) ≤
      Real.pi ^ ((Fintype.card ι : ℝ) / 2) := by
  letI := probability_gaussianShortRangeScaleMeasure a η ha hη
  have hi := integrable_gaussianNormalizedScale_sq_product (ι := ι) a η ha hη
  have hm := (memLp_two_iff_integrable_sq
    (stronglyMeasurable_gaussianNormalizedScaleMean a η ha hη).aestronglyMeasurable).1
    (memLp_gaussianNormalizedScaleMean (ι := ι) a η ha hη)
  calc
    _ ≤ ∫ x : EuclideanSpace ℝ ι, ∫ t, gaussianNormalizedScale t x ^ 2
        ∂gaussianShortRangeScaleMeasure a η :=
      integral_mono_ae hm hi.integral_prod_right (ae_gaussianNormalizedScaleMean_sq_le a η ha hη)
    _ = ∫ t, (∫ x : EuclideanSpace ℝ ι, gaussianNormalizedScale t x ^ 2)
        ∂gaussianShortRangeScaleMeasure a η := (integral_integral_swap hi).symm
    _ = _ := by
      have he : (fun t => ∫ x : EuclideanSpace ℝ ι, gaussianNormalizedScale t x ^ 2) =ᵐ[gaussianShortRangeScaleMeasure a η]
          (fun _ => Real.pi ^ ((Fintype.card ι : ℝ) / 2)) := by
        filter_upwards [ae_pos_gaussianShortRangeScaleMeasure a η] with t ht
        exact integral_gaussianNormalizedScale_sq t ht
      rw [integral_congr_ae he]
      simp

end DGRHS.Gaussian
#check DGRHS.Gaussian.gaussianNormalizedScale
#print axioms DGRHS.Gaussian.gaussianNormalizedScale
#check DGRHS.Gaussian.measurable_gaussianNormalizedScale
#print axioms DGRHS.Gaussian.measurable_gaussianNormalizedScale
#check DGRHS.Gaussian.integrable_gaussianNormalizedScale_sq
#print axioms DGRHS.Gaussian.integrable_gaussianNormalizedScale_sq
#check DGRHS.Gaussian.integral_gaussianNormalizedScale_sq
#print axioms DGRHS.Gaussian.integral_gaussianNormalizedScale_sq
#check DGRHS.Gaussian.integrable_gaussianNormalizedScale_sq_product
#print axioms DGRHS.Gaussian.integrable_gaussianNormalizedScale_sq_product
#check DGRHS.Gaussian.gaussianNormalizedScaleMean
#print axioms DGRHS.Gaussian.gaussianNormalizedScaleMean
#check DGRHS.Gaussian.stronglyMeasurable_gaussianNormalizedScaleMean
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianNormalizedScaleMean
#check DGRHS.Gaussian.ae_gaussianNormalizedScaleMean_sq_le
#print axioms DGRHS.Gaussian.ae_gaussianNormalizedScaleMean_sq_le
#check DGRHS.Gaussian.memLp_gaussianNormalizedScaleMean
#print axioms DGRHS.Gaussian.memLp_gaussianNormalizedScaleMean
#check DGRHS.Gaussian.integral_gaussianNormalizedScaleMean_sq_le
#print axioms DGRHS.Gaussian.integral_gaussianNormalizedScaleMean_sq_le
