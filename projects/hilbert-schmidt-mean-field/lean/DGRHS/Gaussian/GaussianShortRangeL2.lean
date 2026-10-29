import DGRHS.Gaussian.GaussianShortRangeProductL2
import DGRHS.Gaussian.RieszGaussianTruncationComparison

/-! Actual source-normalized Gaussian short-range kernel L2 estimate.
The probability scale measure is constructed, and no integrability or rate
conclusion is supplied as a premise. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma integral_gaussianShortRangeScaleMeasure (a η : ℝ) (ha : 0 < a) (hη : 0 < η)
    (F : ℝ → ℝ) :
    (∫ t, F t ∂gaussianShortRangeScaleMeasure a η) =
      ∫ t in Ioc 0 η, gaussianShortRangeScaleWeight a η t * F t := by
  have hm : Measurable (fun t => ENNReal.ofReal (gaussianShortRangeScaleWeight a η t)) := by
    unfold gaussianShortRangeScaleWeight
    fun_prop
  unfold gaussianShortRangeScaleMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_nonneg_gaussianShortRangeScaleWeight a η ha hη] with t ht
  rw [ENNReal.toReal_ofReal ht]
  rfl

lemma gaussianRieszEuclideanShortRange_eq_scaleMean (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s) (x : EuclideanSpace ℝ ι) :
    gaussianRieszEuclideanShortRange s η x =
      (gaussianRieszSourceCoefficient s * η ^ ((Fintype.card ι : ℝ) / 2 - s) /
        ((Fintype.card ι : ℝ) / 2 - s)) *
      gaussianNormalizedScaleMean ((Fintype.card ι : ℝ) / 2 - s) η x := by
  let a : ℝ := (Fintype.card ι : ℝ) / 2 - s
  have ha' : 0 < a := ha
  have hcancel : η ^ a * η ^ (-a) = 1 := by
    rw [← Real.rpow_add hη, add_neg_cancel, Real.rpow_zero]
  have hc : (gaussianRieszSourceCoefficient s * η ^ a / a) * (a * η ^ (-a)) =
      gaussianRieszSourceCoefficient s := by
    calc
      _ = gaussianRieszSourceCoefficient s * (η ^ a * η ^ (-a)) := by
        field_simp [ha'.ne']
      _ = _ := by rw [hcancel, mul_one]
  have ht (t : ℝ) (ht : 0 < t) :
      t ^ (a - 1) * t ^ (-(Fintype.card ι : ℝ) / 2) = t ^ (-s - 1) := by
    rw [← Real.rpow_add ht]
    congr 1
    dsimp [a]
    ring
  unfold gaussianNormalizedScaleMean
  rw [integral_gaussianShortRangeScaleMeasure a η ha' hη, ← integral_const_mul]
  unfold gaussianRieszEuclideanShortRange
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht0
  unfold gaussianShortRangeScaleWeight gaussianNormalizedScale
  change _ = (gaussianRieszSourceCoefficient s * η ^ a / a) *
    ((a * η ^ (-a) * t ^ (a - 1)) *
      (t ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))))
  symm
  calc
    _ = ((gaussianRieszSourceCoefficient s * η ^ a / a) * (a * η ^ (-a))) *
      (t ^ (a - 1) * t ^ (-(Fintype.card ι : ℝ) / 2)) *
        Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2)) := by ring
    _ = _ := by rw [hc, ht t ht0.1]; ring

lemma memLp_gaussianRieszEuclideanShortRange (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s) :
    MemLp (gaussianRieszEuclideanShortRange (ι := ι) s η) 2 volume := by
  have he := funext (gaussianRieszEuclideanShortRange_eq_scaleMean (ι := ι) s η hη ha)
  rw [he]
  exact (memLp_gaussianNormalizedScaleMean _ η ha hη).const_mul _

lemma integral_gaussianRieszEuclideanShortRange_sq_le (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s) :
    (∫ x : EuclideanSpace ℝ ι, gaussianRieszEuclideanShortRange s η x ^ 2) ≤
      (gaussianRieszSourceCoefficient s * η ^ ((Fintype.card ι : ℝ) / 2 - s) /
        ((Fintype.card ι : ℝ) / 2 - s)) ^ 2 * Real.pi ^ ((Fintype.card ι : ℝ) / 2) := by
  simp_rw [gaussianRieszEuclideanShortRange_eq_scaleMean s η hη ha, mul_pow]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_gaussianNormalizedScaleMean_sq_le _ η ha hη)
    (sq_nonneg _)

lemma stronglyMeasurable_gaussianRieszEuclideanShortRange (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s) :
    StronglyMeasurable (gaussianRieszEuclideanShortRange (ι := ι) s η) := by
  have he := funext (gaussianRieszEuclideanShortRange_eq_scaleMean (ι := ι) s η hη ha)
  rw [he]
  exact (stronglyMeasurable_gaussianNormalizedScaleMean _ η ha hη).const_mul _

lemma integral_gaussianRieszEuclideanShortRange_sq_sharp (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s) :
    (∫ x : EuclideanSpace ℝ ι, gaussianRieszEuclideanShortRange s η x ^ 2) ≤
      (gaussianRieszSourceCoefficient s ^ 2 * Real.pi ^ ((Fintype.card ι : ℝ) / 2) /
        (((Fintype.card ι : ℝ) / 2 - s) ^ 2)) * η ^ ((Fintype.card ι : ℝ) - 2 * s) := by
  have hp : (η ^ ((Fintype.card ι : ℝ) / 2 - s)) ^ 2 =
      η ^ ((Fintype.card ι : ℝ) - 2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    congr 1
    norm_num
    <;> ring
  have he : (gaussianRieszSourceCoefficient s * η ^ ((Fintype.card ι : ℝ) / 2 - s) /
        ((Fintype.card ι : ℝ) / 2 - s)) ^ 2 * Real.pi ^ ((Fintype.card ι : ℝ) / 2) =
      (gaussianRieszSourceCoefficient s ^ 2 * Real.pi ^ ((Fintype.card ι : ℝ) / 2) /
        (((Fintype.card ι : ℝ) / 2 - s) ^ 2)) * η ^ ((Fintype.card ι : ℝ) - 2 * s) := by
    rw [div_pow, mul_pow, hp]
    ring
  exact he ▸ integral_gaussianRieszEuclideanShortRange_sq_le s η hη ha

end DGRHS.Gaussian

#check DGRHS.Gaussian.integral_gaussianShortRangeScaleMeasure
#print axioms DGRHS.Gaussian.integral_gaussianShortRangeScaleMeasure
#check DGRHS.Gaussian.gaussianRieszEuclideanShortRange_eq_scaleMean
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanShortRange_eq_scaleMean
#check DGRHS.Gaussian.memLp_gaussianRieszEuclideanShortRange
#print axioms DGRHS.Gaussian.memLp_gaussianRieszEuclideanShortRange
#check DGRHS.Gaussian.integral_gaussianRieszEuclideanShortRange_sq_le
#print axioms DGRHS.Gaussian.integral_gaussianRieszEuclideanShortRange_sq_le

#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanShortRange
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanShortRange
#check DGRHS.Gaussian.integral_gaussianRieszEuclideanShortRange_sq_sharp
#print axioms DGRHS.Gaussian.integral_gaussianRieszEuclideanShortRange_sq_sharp
