import DGRHS.Gaussian.LogPhysicalCenteredL2

/-! Literal zero-exponent Gaussian short-range scale integral with logarithmic
coefficient ONE. The positive-Riesz normalization at s=0 is never reused.
This is the admissible normalized Gaussian profile specialization; arbitrary
Schwartz-profile truncation remains an explicit later obligation.
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianLogShortRange (η : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫ t in Ioc 0 η, t⁻¹*Real.exp (-‖x‖^2/(2*t^2))

lemma gaussianLogShortRange_nonneg (η : ℝ) (x : EuclideanSpace ℝ ι) :
    0 ≤ gaussianLogShortRange η x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (Real.exp_pos _).le

lemma gaussianLogShortRange_eq_scaleMean (a η : ℝ) (ha : 0 < a) (hη : 0 < η)
    (d : ℝ) (hda : a = d) (x : EuclideanSpace ℝ ι)
    (F : ℝ → EuclideanSpace ℝ ι → ℝ)
    (hF : ∀ t, 0 < t → F t x = t^(-d)*Real.exp (-‖x‖^2/(2*t^2))) :
    gaussianLogShortRange η x = (η^a/a)*∫ t, F t x ∂gaussianShortRangeScaleMeasure a η := by
  have hc : (η^a/a)*(a*η^(-a)) = 1 := by
    calc
      _ = η^a*η^(-a) := by field_simp [ha.ne']
      _ = 1 := by rw [← Real.rpow_add hη, add_neg_cancel, Real.rpow_zero]
  rw [integral_gaussianShortRangeScaleMeasure a η ha hη, ← integral_const_mul]
  unfold gaussianLogShortRange
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change t⁻¹*Real.exp (-‖x‖^2/(2*t^2)) =
    (η^a/a)*(gaussianShortRangeScaleWeight a η t * F t x)
  rw [hF t ht.1]
  unfold gaussianShortRangeScaleWeight
  have hp : t^(a-1)*t^(-d) = t⁻¹ := by
    rw [← Real.rpow_add ht.1, hda]
    convert Real.rpow_neg_one t using 1 <;> congr 1 <;> ring
  calc
    _ = 1*t⁻¹*Real.exp (-‖x‖^2/(2*t^2)) := by ring
    _ = ((η^a/a)*(a*η^(-a)))*(t^(a-1)*t^(-d))*Real.exp (-‖x‖^2/(2*t^2)) := by rw [hc,hp]
    _ = _ := by ring

lemma gaussianLogShortRange_eq_L2mean (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (x : EuclideanSpace ℝ ι) :
    gaussianLogShortRange η x = (η^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2))*
      gaussianNormalizedScaleMean ((Fintype.card ι : ℝ)/2) η x := by
  exact gaussianLogShortRange_eq_scaleMean _ η (by positivity) hη _ rfl x
    gaussianNormalizedScale (fun t ht => by simp only [gaussianNormalizedScale, neg_div])

lemma gaussianLogShortRange_eq_L1mean (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (x : EuclideanSpace ℝ ι) :
    gaussianLogShortRange η x = (η^(Fintype.card ι : ℝ)/(Fintype.card ι : ℝ))*
      ∫ t, gaussianNormalizedScaleL1 t x ∂gaussianShortRangeScaleMeasure (Fintype.card ι : ℝ) η :=
  gaussianLogShortRange_eq_scaleMean _ η hd hη _ rfl x gaussianNormalizedScaleL1 (fun t ht => rfl)

lemma stronglyMeasurable_gaussianLogShortRange (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) : StronglyMeasurable (gaussianLogShortRange (ι := ι) η) := by
  rw [funext (gaussianLogShortRange_eq_L2mean η hη hd)]
  exact (stronglyMeasurable_gaussianNormalizedScaleMean _ η (by positivity) hη).const_mul _

lemma memLp_gaussianLogShortRange (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) : MemLp (gaussianLogShortRange (ι := ι) η) 2 volume := by
  rw [funext (gaussianLogShortRange_eq_L2mean η hη hd)]
  exact (memLp_gaussianNormalizedScaleMean _ η (by positivity) hη).const_mul _

lemma integral_gaussianLogShortRange_sq_le (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) :
    (∫ x : EuclideanSpace ℝ ι, gaussianLogShortRange η x ^ 2) ≤
      (η^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2))^2*Real.pi^((Fintype.card ι : ℝ)/2) := by
  simp_rw [gaussianLogShortRange_eq_L2mean η hη hd, mul_pow]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_gaussianNormalizedScaleMean_sq_le _ η (by positivity) hη) (sq_nonneg _)

lemma integrable_gaussianLogShortRange (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) : Integrable (gaussianLogShortRange (ι := ι) η) := by
  letI := probability_gaussianShortRangeScaleMeasure (Fintype.card ι : ℝ) η hd hη
  rw [funext (gaussianLogShortRange_eq_L1mean η hη hd)]
  exact (integrable_gaussianNormalizedScaleL1_product _ η hd hη).integral_prod_right.const_mul _

lemma integral_gaussianLogShortRange (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) :
    (∫ x : EuclideanSpace ℝ ι, gaussianLogShortRange η x) =
      (2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*η^(Fintype.card ι : ℝ) := by
  letI := probability_gaussianShortRangeScaleMeasure (Fintype.card ι : ℝ) η hd hη
  simp_rw [gaussianLogShortRange_eq_L1mean η hη hd]
  rw [integral_const_mul, ← integral_integral_swap (integrable_gaussianNormalizedScaleL1_product _ η hd hη)]
  have he : (fun t => ∫ x : EuclideanSpace ℝ ι, gaussianNormalizedScaleL1 t x)
      =ᵐ[gaussianShortRangeScaleMeasure (Fintype.card ι : ℝ) η]
        (fun _ => (2*Real.pi)^((Fintype.card ι : ℝ)/2)) := by
    filter_upwards [ae_pos_gaussianShortRangeScaleMeasure (Fintype.card ι : ℝ) η] with t ht
    exact integral_gaussianNormalizedScaleL1 t ht
  rw [integral_congr_ae he]
  simp
  <;> ring

lemma integrable_gaussianLogShortRange_convolution (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianLogShortRange η (x-y)) (gaussianRieszDensityMeasure ρ) :=
  (((integrable_gaussianLogShortRange η hη hd).comp_sub_left x).smul_measure ENNReal.ofReal_ne_top).mono_measure
    (gaussianRieszDensityMeasure_le ρ M hρ)

lemma gaussianLogShortRange_convolution_le (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    (∫ y, gaussianLogShortRange η (x-y) ∂gaussianRieszDensityMeasure ρ) ≤
      M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*η^(Fintype.card ι : ℝ)) := by
  calc
    _ ≤ ∫ y, gaussianLogShortRange η (x-y) ∂(ENNReal.ofReal M • volume) :=
      integral_mono_measure (gaussianRieszDensityMeasure_le ρ M hρ)
        (Filter.Eventually.of_forall (fun y => gaussianLogShortRange_nonneg η _))
        (((integrable_gaussianLogShortRange η hη hd).comp_sub_left x).smul_measure ENNReal.ofReal_ne_top)
    _ = M*∫ z : EuclideanSpace ℝ ι, gaussianLogShortRange η z := by
      rw [integral_smul_measure, integral_sub_left_eq_self (gaussianLogShortRange η) volume x, ENNReal.toReal_ofReal hM]
      rfl
    _ = _ := by rw [integral_gaussianLogShortRange η hη hd]

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogShortRange
#print axioms DGRHS.Gaussian.gaussianLogShortRange

#check @DGRHS.Gaussian.gaussianLogShortRange_nonneg
#print axioms DGRHS.Gaussian.gaussianLogShortRange_nonneg

#check @DGRHS.Gaussian.gaussianLogShortRange_eq_scaleMean
#print axioms DGRHS.Gaussian.gaussianLogShortRange_eq_scaleMean

#check @DGRHS.Gaussian.gaussianLogShortRange_eq_L2mean
#print axioms DGRHS.Gaussian.gaussianLogShortRange_eq_L2mean

#check @DGRHS.Gaussian.gaussianLogShortRange_eq_L1mean
#print axioms DGRHS.Gaussian.gaussianLogShortRange_eq_L1mean

#check @DGRHS.Gaussian.stronglyMeasurable_gaussianLogShortRange
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogShortRange

#check @DGRHS.Gaussian.memLp_gaussianLogShortRange
#print axioms DGRHS.Gaussian.memLp_gaussianLogShortRange

#check @DGRHS.Gaussian.integral_gaussianLogShortRange_sq_le
#print axioms DGRHS.Gaussian.integral_gaussianLogShortRange_sq_le

#check @DGRHS.Gaussian.integrable_gaussianLogShortRange
#print axioms DGRHS.Gaussian.integrable_gaussianLogShortRange

#check @DGRHS.Gaussian.integral_gaussianLogShortRange
#print axioms DGRHS.Gaussian.integral_gaussianLogShortRange

#check @DGRHS.Gaussian.integrable_gaussianLogShortRange_convolution
#print axioms DGRHS.Gaussian.integrable_gaussianLogShortRange_convolution

#check @DGRHS.Gaussian.gaussianLogShortRange_convolution_le
#print axioms DGRHS.Gaussian.gaussianLogShortRange_convolution_le
