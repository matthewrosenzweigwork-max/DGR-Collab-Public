import DGRHS.Gaussian.GaussianShortRangeL2

/-! Actual proper Gaussian short-range L1 scale identity, used for uniform
near-field source convolution in the physical master estimate. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianNormalizedScaleL1 (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  t ^ (-(Fintype.card ι : ℝ)) * Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))

lemma measurable_gaussianNormalizedScaleL1 :
    Measurable (fun p : ℝ × EuclideanSpace ℝ ι => gaussianNormalizedScaleL1 p.1 p.2) := by
  unfold gaussianNormalizedScaleL1
  fun_prop

lemma integrable_gaussianNormalizedScaleL1 (t : ℝ) (ht : 0 < t) :
    Integrable (gaussianNormalizedScaleL1 (ι := ι) t) := by
  have hi := integrable_gaussianEuclidean_neg_norm_sq (ι := ι) (1 / (2*t^2)) (by positivity)
  have he : (fun x : EuclideanSpace ℝ ι => Real.exp (-(1/(2*t^2))*‖x‖^2)) =
      (fun x => Real.exp (-‖x‖^2/(2*t^2))) := by funext x; congr 1; ring
  rw [he] at hi
  exact hi.const_mul _

lemma integral_gaussianNormalizedScaleL1 (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ ι, gaussianNormalizedScaleL1 t x) =
      (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) := by
  have he : (fun x : EuclideanSpace ℝ ι => Real.exp (-‖x‖^2/(2*t^2))) =
      (fun x => Real.exp (-(1/(2*t^2))*‖x‖^2)) := by funext x; congr 1; ring
  unfold gaussianNormalizedScaleL1
  rw [integral_const_mul, he, integral_gaussianEuclidean_neg_norm_sq _ (by positivity),
    one_div, div_inv_eq_mul, show Real.pi * (2*t^2) = (2*Real.pi)*t^2 by ring,
    Real.mul_rpow (by positivity : 0 ≤ 2*Real.pi) (sq_nonneg t), ← Real.rpow_two,
    ← Real.rpow_mul ht.le, show (2 : ℝ) * ((Fintype.card ι : ℝ)/2) = (Fintype.card ι : ℝ) by ring]
  calc
    _ = (2*Real.pi) ^ ((Fintype.card ι : ℝ)/2) *
        (t ^ (-(Fintype.card ι : ℝ)) * t ^ (Fintype.card ι : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, mul_one]

lemma integrable_gaussianNormalizedScaleL1_product (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ ι => gaussianNormalizedScaleL1 p.1 p.2)
      ((gaussianShortRangeScaleMeasure a η).prod volume) := by
  letI := probability_gaussianShortRangeScaleMeasure a η ha hη
  apply (integrable_prod_iff measurable_gaussianNormalizedScaleL1.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_pos_gaussianShortRangeScaleMeasure a η] with t ht
    exact integrable_gaussianNormalizedScaleL1 t ht
  · apply (integrable_const ((2*Real.pi)^((Fintype.card ι : ℝ)/2))).congr
    filter_upwards [ae_pos_gaussianShortRangeScaleMeasure a η] with t ht
    have hn (x : EuclideanSpace ℝ ι) : 0 ≤ gaussianNormalizedScaleL1 t x := by
      unfold gaussianNormalizedScaleL1
      positivity
    simp_rw [Real.norm_of_nonneg (hn _)]
    exact (integral_gaussianNormalizedScaleL1 t ht).symm

lemma gaussianRieszEuclideanShortRange_eq_scaleMeanL1 (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) - s) (x : EuclideanSpace ℝ ι) :
    gaussianRieszEuclideanShortRange s η x =
      (gaussianRieszSourceCoefficient s * η ^ ((Fintype.card ι : ℝ) - s) /
        ((Fintype.card ι : ℝ) - s)) *
      ∫ t, gaussianNormalizedScaleL1 t x ∂gaussianShortRangeScaleMeasure ((Fintype.card ι : ℝ)-s) η := by
  let a : ℝ := (Fintype.card ι : ℝ)-s
  have ha' : 0 < a := ha
  have hc : (gaussianRieszSourceCoefficient s * η ^ a/a)*(a*η^(-a)) = gaussianRieszSourceCoefficient s := by
    calc
      _ = gaussianRieszSourceCoefficient s * (η^a*η^(-a)) := by field_simp [ha'.ne']
      _ = _ := by rw [← Real.rpow_add hη, add_neg_cancel, Real.rpow_zero, mul_one]
  have ht (t : ℝ) (ht : 0 < t) : t^(a-1)*t^(-(Fintype.card ι : ℝ)) = t^(-s-1) := by
    rw [← Real.rpow_add ht]
    congr 1
    dsimp [a]
    ring
  rw [integral_gaussianShortRangeScaleMeasure a η ha' hη, ← integral_const_mul]
  unfold gaussianRieszEuclideanShortRange
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht0
  unfold gaussianNormalizedScaleL1 gaussianShortRangeScaleWeight
  change gaussianRieszSourceCoefficient s * (t^(-s-1)*Real.exp (-‖x‖^2/(2*t^2))) =
    (gaussianRieszSourceCoefficient s * η^a/a) * ((a*η^(-a)*t^(a-1))*
      (t^(-(Fintype.card ι : ℝ))*Real.exp (-‖x‖^2/(2*t^2))))
  symm
  calc
    _ = ((gaussianRieszSourceCoefficient s * η^a/a)*(a*η^(-a)))*
      (t^(a-1)*t^(-(Fintype.card ι : ℝ)))*Real.exp (-‖x‖^2/(2*t^2)) := by ring
    _ = _ := by rw [hc, ht t ht0.1]; ring

lemma integrable_gaussianRieszEuclideanShortRange (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) - s) :
    Integrable (gaussianRieszEuclideanShortRange (ι := ι) s η) := by
  letI := probability_gaussianShortRangeScaleMeasure ((Fintype.card ι : ℝ)-s) η ha hη
  have he := funext (gaussianRieszEuclideanShortRange_eq_scaleMeanL1 (ι := ι) s η hη ha)
  rw [he]
  exact (integrable_gaussianNormalizedScaleL1_product _ η ha hη).integral_prod_right.const_mul _

lemma integral_gaussianRieszEuclideanShortRange (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) - s) :
    (∫ x : EuclideanSpace ℝ ι, gaussianRieszEuclideanShortRange s η x) =
      gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
        ((Fintype.card ι : ℝ)-s) * η^((Fintype.card ι : ℝ)-s) := by
  letI := probability_gaussianShortRangeScaleMeasure ((Fintype.card ι : ℝ)-s) η ha hη
  simp_rw [gaussianRieszEuclideanShortRange_eq_scaleMeanL1 s η hη ha]
  rw [integral_const_mul,
    ← integral_integral_swap (integrable_gaussianNormalizedScaleL1_product _ η ha hη)]
  have he : (fun t => ∫ x : EuclideanSpace ℝ ι, gaussianNormalizedScaleL1 t x)
      =ᵐ[gaussianShortRangeScaleMeasure ((Fintype.card ι : ℝ)-s) η]
        (fun _ => (2*Real.pi)^((Fintype.card ι : ℝ)/2)) := by
    filter_upwards [ae_pos_gaussianShortRangeScaleMeasure ((Fintype.card ι : ℝ)-s) η] with t ht
    exact integral_gaussianNormalizedScaleL1 t ht
  rw [integral_congr_ae he]
  simp
  <;> ring

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianNormalizedScaleL1
#print axioms DGRHS.Gaussian.gaussianNormalizedScaleL1
#check DGRHS.Gaussian.measurable_gaussianNormalizedScaleL1
#print axioms DGRHS.Gaussian.measurable_gaussianNormalizedScaleL1
#check DGRHS.Gaussian.integrable_gaussianNormalizedScaleL1
#print axioms DGRHS.Gaussian.integrable_gaussianNormalizedScaleL1
#check DGRHS.Gaussian.integral_gaussianNormalizedScaleL1
#print axioms DGRHS.Gaussian.integral_gaussianNormalizedScaleL1
#check DGRHS.Gaussian.integrable_gaussianNormalizedScaleL1_product
#print axioms DGRHS.Gaussian.integrable_gaussianNormalizedScaleL1_product
#check DGRHS.Gaussian.gaussianRieszEuclideanShortRange_eq_scaleMeanL1
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanShortRange_eq_scaleMeanL1
#check DGRHS.Gaussian.integrable_gaussianRieszEuclideanShortRange
#print axioms DGRHS.Gaussian.integrable_gaussianRieszEuclideanShortRange
#check DGRHS.Gaussian.integral_gaussianRieszEuclideanShortRange
#print axioms DGRHS.Gaussian.integral_gaussianRieszEuclideanShortRange
