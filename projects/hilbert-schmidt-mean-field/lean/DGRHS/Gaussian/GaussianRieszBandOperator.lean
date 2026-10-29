import DGRHS.Gaussian.GaussianRieszBandCentered

/-! The SAME actual centered physical band integral operator has the derived
small-scale norm bound. No favorable spectral or operator premise is used. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma memLp_gaussianRieszCenteredBand (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  memLp_hoeffdingCentered _ _ (stronglyMeasurable_gaussianRieszBandPair s η δ hs hη hηδ)
    (memLp_gaussianRieszBandPair s η δ hs hη hηδ ha ρ M hM hρ)

set_option maxHeartbeats 1000000 in
lemma norm_gaussianRieszCenteredBand_operator_le (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ‖DGRHS.Kernel.integralOperator
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ))
      (memLp_gaussianRieszCenteredBand s η δ hs hη hηδ ha ρ M hM hρ)‖ ≤
        4*Real.sqrt (gaussianRieszBandRowControl s δ M ι) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := hoeffdingCentered μ (gaussianRieszBandPair (ι := ι) s η δ)
  let hW := memLp_gaussianRieszCenteredBand s η δ hs hη hηδ ha ρ M hM hρ
  have hδ : 0 < δ := lt_of_lt_of_le hη hηδ
  have hK : 0 ≤ gaussianRieszBandRowControl s δ M ι := by
    unfold gaussianRieszBandRowControl
    positivity
  have hb : ‖hW.toLp W‖^2 ≤ 16*gaussianRieszBandRowControl s δ M ι := by
    rw [DGRHS.Kernel.norm_toLp_sq]
    exact (gaussianRieszCenteredBand_square_controls s η δ hs hη hηδ ha ρ M hM hρ).2
  have hn : ‖hW.toLp W‖ ≤ 4*Real.sqrt (gaussianRieszBandRowControl s δ M ι) := by
    nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg (gaussianRieszBandRowControl s δ M ι), norm_nonneg (hW.toLp W)]
  exact (DGRHS.Kernel.norm_integralOperator_le W hW).trans hn

end DGRHS.Gaussian
#check DGRHS.Gaussian.memLp_gaussianRieszCenteredBand
#print axioms DGRHS.Gaussian.memLp_gaussianRieszCenteredBand
#check DGRHS.Gaussian.norm_gaussianRieszCenteredBand_operator_le
#print axioms DGRHS.Gaussian.norm_gaussianRieszCenteredBand_operator_le
