import DGRHS.Gaussian.GaussianShortRangeL1
import DGRHS.Gaussian.GaussianRieszCenteredComparison

/-! Proper every-point short-range convolution and actual lower bound on its
Hoeffding-centered kernel. The density bound is transferred from Lebesgue
measure; no desired convolution or near-field estimate is assumed. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma integrable_gaussianRieszShortRange_convolution (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianRieszEuclideanShortRange s η (x-y))
      (gaussianRieszDensityMeasure ρ) := by
  exact (((integrable_gaussianRieszEuclideanShortRange s η hη ha).comp_sub_left x).smul_measure ENNReal.ofReal_ne_top).mono_measure (gaussianRieszDensityMeasure_le ρ M hρ)

lemma gaussianRieszShortRange_convolution_le (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    (∫ y, gaussianRieszEuclideanShortRange s η (x-y) ∂gaussianRieszDensityMeasure ρ) ≤
      M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
        ((Fintype.card ι : ℝ)-s) * η^((Fintype.card ι : ℝ)-s)) := by
  calc
    _ ≤ ∫ y, gaussianRieszEuclideanShortRange s η (x-y) ∂(ENNReal.ofReal M • volume) :=
      integral_mono_measure (gaussianRieszDensityMeasure_le ρ M hρ)
        (Filter.Eventually.of_forall (fun y => gaussianRieszEuclideanShortRange_nonneg s η hs _))
        (((integrable_gaussianRieszEuclideanShortRange s η hη ha).comp_sub_left x).smul_measure ENNReal.ofReal_ne_top)
    _ = M * ∫ z : EuclideanSpace ℝ ι, gaussianRieszEuclideanShortRange s η z := by
      rw [integral_smul_measure,
        integral_sub_left_eq_self (gaussianRieszEuclideanShortRange s η) volume x,
        ENNReal.toReal_ofReal hM]
      rfl
    _ = _ := by rw [integral_gaussianRieszEuclideanShortRange s η hη ha]

lemma gaussianRieszShortRange_symmetric (s η : ℝ) (x y : EuclideanSpace ℝ ι) :
    gaussianRieszEuclideanShortRange s η (x-y) = gaussianRieszEuclideanShortRange s η (y-x) := by
  unfold gaussianRieszEuclideanShortRange
  simp only [norm_sub_rev]

lemma gaussianRieszCenteredShortRange_lower_bound (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    -hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s η) p ≤
      2 * (M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
        ((Fintype.card ι : ℝ)-s) * η^((Fintype.card ι : ℝ)-s))) := by
  have h1 := gaussianRieszShortRange_convolution_le s η hs hη ha ρ M hM hρ p.1
  have h2 := gaussianRieszShortRange_convolution_le s η hs hη ha ρ M hM hρ p.2
  have he : (fun x => gaussianRieszEuclideanShortRange s η (x-p.2)) =
      (fun x => gaussianRieszEuclideanShortRange s η (p.2-x)) := by
    funext x
    exact gaussianRieszShortRange_symmetric s η x p.2
  have hn := gaussianRieszEuclideanShortRange_nonneg s η hs (p.1-p.2)
  have hm : 0 ≤ ∫ z, gaussianRieszShortPair s η z
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) :=
    integral_nonneg (fun z => gaussianRieszEuclideanShortRange_nonneg s η hs _)
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change -(gaussianRieszEuclideanShortRange s η (p.1-p.2) -
    (∫ y, gaussianRieszEuclideanShortRange s η (p.1-y) ∂gaussianRieszDensityMeasure ρ) -
    (∫ x, gaussianRieszEuclideanShortRange s η (x-p.2) ∂gaussianRieszDensityMeasure ρ) +
    (∫ z, gaussianRieszShortPair s η z
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) ≤ _
  rw [he]
  linarith

end DGRHS.Gaussian

#check DGRHS.Gaussian.integrable_gaussianRieszShortRange_convolution
#print axioms DGRHS.Gaussian.integrable_gaussianRieszShortRange_convolution

#check DGRHS.Gaussian.gaussianRieszShortRange_convolution_le
#print axioms DGRHS.Gaussian.gaussianRieszShortRange_convolution_le

#check DGRHS.Gaussian.gaussianRieszShortRange_symmetric
#print axioms DGRHS.Gaussian.gaussianRieszShortRange_symmetric

#check DGRHS.Gaussian.gaussianRieszCenteredShortRange_lower_bound
#print axioms DGRHS.Gaussian.gaussianRieszCenteredShortRange_lower_bound
