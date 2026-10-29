import DGRHS.Gaussian.GaussianRieszCenteredComparison

/-! SAME actual physical full/truncated source integral operators and their
exact centered remainder difference. Norm bound is derived from physical L2. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszPhysicalOperator (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Lp ℝ 2 (gaussianRieszDensityMeasure ρ) →L[ℝ] Lp ℝ 2 (gaussianRieszDensityMeasure ρ) :=
  DGRHS.Kernel.integralOperator (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
    (memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ)

def gaussianRieszTruncatedOperator (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ρ : EuclideanSpace ℝ ι → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Lp ℝ 2 (gaussianRieszDensityMeasure ρ) →L[ℝ] Lp ℝ 2 (gaussianRieszDensityMeasure ρ) :=
  DGRHS.Kernel.integralOperator (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η))
    (memLp_gaussianRieszCenteredTruncatedPair s η hs hη (gaussianRieszDensityMeasure ρ))

def gaussianRieszShortOperator (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Lp ℝ 2 (gaussianRieszDensityMeasure ρ) →L[ℝ] Lp ℝ 2 (gaussianRieszDensityMeasure ρ) :=
  DGRHS.Kernel.integralOperator (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s η))
    (memLp_gaussianRieszCenteredShortPair s η hη ha ρ M hM hρ)

lemma gaussianRieszPhysicalOperator_sub_cutoff (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    gaussianRieszPhysicalOperator s hs ha ρ M hM hρ - gaussianRieszTruncatedOperator s η hs hη ρ =
      gaussianRieszShortOperator s η hη ha ρ M hM hρ := by
  unfold gaussianRieszPhysicalOperator gaussianRieszTruncatedOperator gaussianRieszShortOperator
  rw [← gaussian_integralOperator_sub (gaussianRieszDensityMeasure ρ)]
  exact gaussian_integralOperator_congr (gaussianRieszDensityMeasure ρ) _ _ _ _
    (ae_gaussianRiesz_centered_difference s η hs hη ha ρ M hM hρ)

lemma norm_gaussianRieszPhysicalOperator_sub_cutoff_le (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ‖gaussianRieszPhysicalOperator s hs ha ρ M hM hρ - gaussianRieszTruncatedOperator s η hs hη ρ‖ ≤
      4 * gaussianRieszShortRangeRateConstant s M ι * η ^ ((Fintype.card ι : ℝ) / 2 - s) := by
  rw [gaussianRieszPhysicalOperator_sub_cutoff s η hs hη ha ρ M hM hρ]
  exact (DGRHS.Kernel.norm_integralOperator_le _ _).trans
    (norm_gaussianRieszCenteredShortPair_le s η hη ha ρ M hM hρ)

lemma gaussianRieszTruncatedOperator_eq_source (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ρ : EuclideanSpace ℝ ι → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hh : MemLp (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      centeredGaussianRieszEuclideanTruncatedKernel s η (gaussianRieszDensityMeasure ρ) p.1 p.2) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    gaussianRieszTruncatedOperator s η hs hη ρ = DGRHS.Kernel.integralOperator _ hh := by
  exact gaussian_integralOperator_congr (gaussianRieszDensityMeasure ρ) _ _ _ _
    (Filter.Eventually.of_forall (gaussianRieszCenteredTruncatedPair_eq_source s η hs hη (gaussianRieszDensityMeasure ρ)))

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszPhysicalOperator
#print axioms DGRHS.Gaussian.gaussianRieszPhysicalOperator
#check DGRHS.Gaussian.gaussianRieszTruncatedOperator
#print axioms DGRHS.Gaussian.gaussianRieszTruncatedOperator
#check DGRHS.Gaussian.gaussianRieszShortOperator
#print axioms DGRHS.Gaussian.gaussianRieszShortOperator
#check DGRHS.Gaussian.gaussianRieszPhysicalOperator_sub_cutoff
#print axioms DGRHS.Gaussian.gaussianRieszPhysicalOperator_sub_cutoff
#check DGRHS.Gaussian.norm_gaussianRieszPhysicalOperator_sub_cutoff_le
#print axioms DGRHS.Gaussian.norm_gaussianRieszPhysicalOperator_sub_cutoff_le
#check DGRHS.Gaussian.gaussianRieszTruncatedOperator_eq_source
#print axioms DGRHS.Gaussian.gaussianRieszTruncatedOperator_eq_source
