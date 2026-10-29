import DGRHS.Gaussian.GaussianLogShortRangeSource
import DGRHS.Gaussian.GaussianRieszOperatorDifference

/-! Supporting development. Actual full/cutoff logarithmic operator difference,
with the proper centered short-range L2 bound. Only generic linear operator
identities are reused from the positive-power module; no s=0 Riesz identity.
The cutoff pair is the totalized off-origin physical expression. Its diagonal
value is not the smooth Gaussian-cutoff Gram diagonal. Source integral operators
and distinct-particle statistics require an actual AE identification, not a
pointwise diagonal equality. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma memLp_gaussianLogCenteredShortPair (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  memLp_hoeffdingCentered _ _ (stronglyMeasurable_gaussianLogShortPair η hη hd)
    (memLp_gaussianLogShortPair η hη hd ρ M hM hρ)

lemma norm_gaussianLogCenteredShortPair_le (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ‖(memLp_gaussianLogCenteredShortPair η hη hd ρ M hM hρ).toLp
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η))‖ ≤
      4*(Real.sqrt (M*Real.pi^((Fintype.card ι : ℝ)/2))/((Fintype.card ι : ℝ)/2)*
        η^((Fintype.card ι : ℝ)/2)) := by
  have hc := norm_hoeffdingCentered_le (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η)
    (stronglyMeasurable_gaussianLogShortPair η hη hd) (memLp_gaussianLogShortPair η hη hd ρ M hM hρ)
  exact hc.trans (mul_le_mul_of_nonneg_left (norm_gaussianLogShortPair_toLp_le η hη hd ρ M hM hρ) (by norm_num))

lemma ae_logPhysical_centered_difference (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair -
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)
      =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η) := by
  filter_upwards [ae_logPhysical_centered_truncation_difference η hη hd ρ M hM hρ hpair] with p hp
  change _ = _ at hp
  change hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair p -
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η) p = _
  simp only [Pi.sub_apply] at hp
  linarith

def logPhysicalCenteredOperator (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    Lp ℝ 2 (gaussianRieszDensityMeasure ρ) →L[ℝ] Lp ℝ 2 (gaussianRieszDensityMeasure ρ) :=
  DGRHS.Kernel.integralOperator (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
    (memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair)

def gaussianLogTruncatedOperator (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    Lp ℝ 2 (gaussianRieszDensityMeasure ρ) →L[ℝ] Lp ℝ 2 (gaussianRieszDensityMeasure ρ) :=
  DGRHS.Kernel.integralOperator (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η))
    (memLp_logPhysicalCenteredTruncatedPair η hη hd ρ M hM hρ hpair)

def gaussianLogShortOperator (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Lp ℝ 2 (gaussianRieszDensityMeasure ρ) →L[ℝ] Lp ℝ 2 (gaussianRieszDensityMeasure ρ) :=
  DGRHS.Kernel.integralOperator (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η))
    (memLp_gaussianLogCenteredShortPair η hη hd ρ M hM hρ)

lemma logPhysicalCenteredOperator_sub_cutoff (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    logPhysicalCenteredOperator hd ρ M hM hρ hpair - gaussianLogTruncatedOperator η hη hd ρ M hM hρ hpair =
      gaussianLogShortOperator η hη hd ρ M hM hρ := by
  unfold logPhysicalCenteredOperator gaussianLogTruncatedOperator gaussianLogShortOperator
  rw [← gaussian_integralOperator_sub (gaussianRieszDensityMeasure ρ)]
  exact gaussian_integralOperator_congr (gaussianRieszDensityMeasure ρ) _ _ _ _
    (ae_logPhysical_centered_difference η hη hd ρ M hM hρ hpair)

lemma norm_logPhysicalCenteredOperator_sub_cutoff_le (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ‖logPhysicalCenteredOperator hd ρ M hM hρ hpair - gaussianLogTruncatedOperator η hη hd ρ M hM hρ hpair‖ ≤
      4*(Real.sqrt (M*Real.pi^((Fintype.card ι : ℝ)/2))/((Fintype.card ι : ℝ)/2)*
        η^((Fintype.card ι : ℝ)/2)) := by
  rw [logPhysicalCenteredOperator_sub_cutoff]
  exact (DGRHS.Kernel.norm_integralOperator_le _ _).trans
    (norm_gaussianLogCenteredShortPair_le η hη hd ρ M hM hρ)

end DGRHS.Gaussian

#check @DGRHS.Gaussian.memLp_gaussianLogCenteredShortPair
#print axioms DGRHS.Gaussian.memLp_gaussianLogCenteredShortPair
#check @DGRHS.Gaussian.norm_gaussianLogCenteredShortPair_le
#print axioms DGRHS.Gaussian.norm_gaussianLogCenteredShortPair_le
#check @DGRHS.Gaussian.ae_logPhysical_centered_difference
#print axioms DGRHS.Gaussian.ae_logPhysical_centered_difference
#check @DGRHS.Gaussian.logPhysicalCenteredOperator
#print axioms DGRHS.Gaussian.logPhysicalCenteredOperator
#check @DGRHS.Gaussian.gaussianLogTruncatedOperator
#print axioms DGRHS.Gaussian.gaussianLogTruncatedOperator
#check @DGRHS.Gaussian.gaussianLogShortOperator
#print axioms DGRHS.Gaussian.gaussianLogShortOperator
#check @DGRHS.Gaussian.logPhysicalCenteredOperator_sub_cutoff
#print axioms DGRHS.Gaussian.logPhysicalCenteredOperator_sub_cutoff
#check @DGRHS.Gaussian.norm_logPhysicalCenteredOperator_sub_cutoff_le
#print axioms DGRHS.Gaussian.norm_logPhysicalCenteredOperator_sub_cutoff_le
