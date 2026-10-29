import DGRHS.Gaussian.GaussianShortRangeSourceL2
import DGRHS.Kernel.Separated

/-! Actual source eq:fetaL2Rate in the Gaussian profile specialization:
short-range L2(mu product mu) norm is at most a cutoff-independent constant
 times eta^(d/2-s). The L2 element is constructed from the physical kernel. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszShortRangeSourceL2 (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Lp ℝ 2 ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  (memLp_gaussianRieszEuclideanShortRange_source s η hη ha ρ M hM hρ).toLp
    (fun p => gaussianRieszEuclideanShortRange s η (p.1 - p.2))

def gaussianRieszShortRangeRateConstant (s M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  Real.sqrt (M * (gaussianRieszSourceCoefficient s ^ 2 * Real.pi ^ ((Fintype.card ι : ℝ) / 2) /
    (((Fintype.card ι : ℝ) / 2 - s) ^ 2)))

lemma norm_gaussianRieszShortRangeSourceL2_le (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ‖gaussianRieszShortRangeSourceL2 s η hη ha ρ M hM hρ‖ ≤
      gaussianRieszShortRangeRateConstant s M ι * η ^ ((Fintype.card ι : ℝ) / 2 - s) := by
  let K : ℝ := M * (gaussianRieszSourceCoefficient s ^ 2 *
    Real.pi ^ ((Fintype.card ι : ℝ) / 2) / (((Fintype.card ι : ℝ) / 2 - s) ^ 2))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp : (η ^ ((Fintype.card ι : ℝ) / 2 - s)) ^ 2 =
      η ^ ((Fintype.card ι : ℝ) - 2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    congr 1
    norm_num
    <;> ring
  have hsquare : (gaussianRieszShortRangeRateConstant s M ι *
      η ^ ((Fintype.card ι : ℝ) / 2 - s)) ^ 2 = K * η ^ ((Fintype.card ι : ℝ) - 2 * s) := by
    unfold gaussianRieszShortRangeRateConstant
    rw [mul_pow, Real.sq_sqrt hK, hp]
  have hbound : ‖gaussianRieszShortRangeSourceL2 s η hη ha ρ M hM hρ‖ ^ 2 ≤
      K * η ^ ((Fintype.card ι : ℝ) - 2 * s) := by
    unfold gaussianRieszShortRangeSourceL2
    rw [DGRHS.Kernel.norm_toLp_sq]
    exact integral_gaussianRieszEuclideanShortRange_source_sq_sharp s η hη ha ρ M hM hρ
  have hn : 0 ≤ gaussianRieszShortRangeRateConstant s M ι * η ^ ((Fintype.card ι : ℝ) / 2 - s) := by
    unfold gaussianRieszShortRangeRateConstant
    positivity
  nlinarith [norm_nonneg (gaussianRieszShortRangeSourceL2 s η hη ha ρ M hM hρ)]

lemma eLpNorm_toReal_gaussianRieszEuclideanShortRange_source_le (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (eLpNorm (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      gaussianRieszEuclideanShortRange s η (p.1 - p.2)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))).toReal ≤
      gaussianRieszShortRangeRateConstant s M ι * η ^ ((Fintype.card ι : ℝ) / 2 - s) := by
  simpa only [gaussianRieszShortRangeSourceL2, Lp.norm_toLp] using
    norm_gaussianRieszShortRangeSourceL2_le s η hη ha ρ M hM hρ

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszShortRangeSourceL2
#print axioms DGRHS.Gaussian.gaussianRieszShortRangeSourceL2
#check DGRHS.Gaussian.gaussianRieszShortRangeRateConstant
#print axioms DGRHS.Gaussian.gaussianRieszShortRangeRateConstant
#check DGRHS.Gaussian.norm_gaussianRieszShortRangeSourceL2_le
#print axioms DGRHS.Gaussian.norm_gaussianRieszShortRangeSourceL2_le
#check DGRHS.Gaussian.eLpNorm_toReal_gaussianRieszEuclideanShortRange_source_le
#print axioms DGRHS.Gaussian.eLpNorm_toReal_gaussianRieszEuclideanShortRange_source_le
