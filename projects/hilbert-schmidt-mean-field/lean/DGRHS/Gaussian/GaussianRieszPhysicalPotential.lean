import DGRHS.Gaussian.GaussianRieszBandScaling
import DGRHS.Gaussian.GaussianShortRangeConvolution

/-! Actual full physical potential is proper at every x and uniformly bounded.
The fixed split is short at1 plus long at1. Density-section null singletons
justify the singular off-origin identity; no potential bound is assumed. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszPhysicalPotentialConstant (s M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  M*gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
    ((Fintype.card ι : ℝ)-s) + gaussianRieszSourceCoefficient s/s

lemma gaussianRieszEuclideanTruncation_le_diagonal (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) :
    ‖gaussianRieszEuclideanTruncation s η x‖ ≤ gaussianRieszSourceCoefficient s/s*η^(-s) := by
  have hD : 0 ≤ gaussianRieszSourceCoefficient s/s*η^(-s) := by
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  have he := inner_gaussianRieszEuclideanFourierFeature s η hs hη x 0
  rw [sub_zero] at he
  rw [← he]
  calc
    _ ≤ ‖gaussianRieszEuclideanFourierFeature s η hs hη x‖ *
        ‖gaussianRieszEuclideanFourierFeature s η hs hη 0‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_gaussianRieszEuclideanFourierFeature, norm_gaussianRieszEuclideanFourierFeature]; nlinarith [Real.sq_sqrt hD]

lemma integrable_gaussianRieszTruncation_convolution (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianRieszEuclideanTruncation s η (x-y)) μ :=
  (integrable_const (gaussianRieszSourceCoefficient s/s*η^(-s))).mono'
    ((stronglyMeasurable_gaussianRieszEuclideanTruncation s η hs hη).comp_measurable
      (by fun_prop : Measurable (fun y : EuclideanSpace ℝ ι => x-y))).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => gaussianRieszEuclideanTruncation_le_diagonal s η hs hη (x-y)))

lemma gaussianRieszPhysicalPotential_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianRieszPhysicalPair s (x,y)) (gaussianRieszDensityMeasure ρ) ∧
    0 ≤ (∫ y,gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ) ∧
    (∫ y,gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ) ≤
      gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure; infer_instance
  have ha1 : 0 < (Fintype.card ι : ℝ)-s := by
    have hc' : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    linarith
  have he : (fun y => gaussianRieszPhysicalPair s (x,y)) =ᵐ[μ]
      (fun y => gaussianRieszEuclideanShortRange s 1 (x-y)+gaussianRieszEuclideanTruncation s 1 (x-y)) := by
    filter_upwards [μ.ae_ne x] with y hy
    exact gaussianRieszEuclidean_full_short_long_split s 1 hs (by norm_num) _ (sub_ne_zero.mpr hy.symm)
  have hiS := integrable_gaussianRieszShortRange_convolution s 1 (by norm_num) ha1 ρ M hρ x
  have hiL := integrable_gaussianRieszTruncation_convolution s 1 hs (by norm_num) μ x
  refine ⟨(hiS.add hiL).congr he.symm, integral_nonneg (fun y => ?_), ?_⟩
  · unfold gaussianRieszPhysicalPair
    positivity
  · rw [integral_congr_ae he, integral_add hiS hiL]
    have hS := gaussianRieszShortRange_convolution_le s 1 hs (by norm_num) ha1 ρ M hM hρ x
    have hL : (∫ y,gaussianRieszEuclideanTruncation s 1 (x-y) ∂μ) ≤ gaussianRieszSourceCoefficient s/s := by
      calc
        _ ≤ ∫ _ : EuclideanSpace ℝ ι, gaussianRieszSourceCoefficient s/s ∂μ :=
          integral_mono_ae hiL (integrable_const _) (Filter.Eventually.of_forall (fun y =>
            (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, Real.one_rpow, mul_one] using
              gaussianRieszEuclideanTruncation_le_diagonal s 1 hs (by norm_num) (x-y))))
        _ = _ := by simp
    simp only [Real.one_rpow, mul_one] at hS
    unfold gaussianRieszPhysicalPotentialConstant
    convert add_le_add hS hL using 1 <;> ring

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszPhysicalPotentialConstant
#print axioms DGRHS.Gaussian.gaussianRieszPhysicalPotentialConstant

#check DGRHS.Gaussian.gaussianRieszEuclideanTruncation_le_diagonal
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanTruncation_le_diagonal

#check DGRHS.Gaussian.integrable_gaussianRieszTruncation_convolution
#print axioms DGRHS.Gaussian.integrable_gaussianRieszTruncation_convolution

#check DGRHS.Gaussian.gaussianRieszPhysicalPotential_bound
#print axioms DGRHS.Gaussian.gaussianRieszPhysicalPotential_bound
