import DGRHS.Gaussian.GaussianLogBandCentered
import DGRHS.Gaussian.GaussianLogBandPositivity
import DGRHS.Gaussian.GaussianLogBandDiagonalControl
import DGRHS.Gaussian.GaussianLogCutoffIdentification
import DGRHS.Gaussian.GaussianLogOperatorDifference
import DGRHS.Gaussian.GaussianLogL2Domination

/-! Supporting development. Positivity of the SAME literal Gaussian logarithmic cutoff
by actual finite-band product-L2 convergence. No favorable sign/spectrum is a premise. -/
noncomputable section
open MeasureTheory Filter Real
open scoped ENNReal Topology InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma norm_sq_centeredGaussianLogBandFeature_general_majorized (η T : ℝ)
    (hη : 0 < η) (hηT : η ≤ T) (hT : 1 ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    ‖centeredGaussianLogBandFeature η T hη (gaussianRieszDensityMeasure ρ) x‖^2 ≤
      gaussianLogBandDiagonalMajorant η M (gaussianRieszDensityMeasure ρ) x := by
  have hc := gaussianLog_source_low_diagonal_cancellation η T 1 hη hηT hd ρ M hM hρ x
  have hs := gaussianLogShortRange_convolution_le η hη hd ρ M hM hρ x
  change (∫ y, gaussianLogShortPair η (x,y) ∂gaussianRieszDensityMeasure ρ) ≤
    M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*η^(Fintype.card ι : ℝ)) at hs
  have hmS : 0 ≤ ∫ p, gaussianLogShortPair η p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) :=
    integral_nonneg (fun p => gaussianLogShortRange_nonneg η _)
  have ht := gaussianLogCounterterm_low_scale_bound η T hη hT
  have hp := gaussianLogInfrared_potential_norm_le T hd ρ M hM hρ hpair x
  have hm := gaussianLogInfrared_pairMean_le T hd ρ hpair
  have hp' := neg_le_abs (∫ y,gaussianLogInfraredPair T (x,y) ∂gaussianRieszDensityMeasure ρ)
  rw [← Real.norm_eq_abs] at hp'
  unfold gaussianLogBandDiagonalMajorant
  nlinarith [neg_le_abs (Real.log η),
    le_abs_self (gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ)/4) M ι),
    le_abs_self (logPhysicalTailIntegral (gaussianRieszDensityMeasure ρ))]

lemma gaussianLogCenteredBand_general_sq_majorized (η T : ℝ)
    (hη : 0 < η) (hηT : η ≤ T) (hT : 1 ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η T) p^2 ≤
      gaussianLogBandDiagonalMajorant η M (gaussianRieszDensityMeasure ρ) p.1 *
      gaussianLogBandDiagonalMajorant η M (gaussianRieszDensityMeasure ρ) p.2 := by
  rw [← inner_centeredGaussianLogBandFeature η T hη hηT]
  have hi := norm_inner_le_norm (𝕜 := ℝ)
    (centeredGaussianLogBandFeature η T hη (gaussianRieszDensityMeasure ρ) p.1)
    (centeredGaussianLogBandFeature η T hη (gaussianRieszDensityMeasure ρ) p.2)
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  rw [mul_pow, Real.norm_eq_abs, sq_abs] at hi2
  exact hi2.trans (mul_le_mul
    (norm_sq_centeredGaussianLogBandFeature_general_majorized η T hη hηT hT hd ρ M hM hρ hpair p.1)
    (norm_sq_centeredGaussianLogBandFeature_general_majorized η T hη hηT hT hd ρ M hM hρ hpair p.2)
    (sq_nonneg _) (gaussianLogBandDiagonalMajorant_nonneg η M hη.le hM _ p.1))

lemma gaussianLogTruncatedOperator_positive (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∀ v, 0 ≤ inner ℝ v (gaussianLogTruncatedOperator η hη hd ρ M hM hρ hpair v) := by
  let μ := gaussianRieszDensityMeasure ρ
  let T : ℕ → ℝ := fun j => max η (j+1 : ℕ)
  have hT1 (j : ℕ) : 1 ≤ T j := by
    have hj : (1 : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 j)
    exact hj.trans (le_max_right _ _)
  have hηT (j : ℕ) : η ≤ T j := le_max_left _ _
  have hT : Tendsto T atTop atTop := by
    exact tendsto_atTop_mono (fun j => le_max_right _ _)
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  let a := fun j => hoeffdingCentered μ (gaussianLogBandPair η (T j))
  let ha := fun j => memLp_gaussianLogCenteredBand η (T j) hη (hηT j) hd ρ M hM hρ
  let h := hoeffdingCentered μ (gaussianLogTruncatedPair η)
  let hh := memLp_logPhysicalCenteredTruncatedPair η hη hd ρ M hM hρ hpair
  let m := gaussianLogBandDiagonalMajorant η M μ
  let B := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => m p.1*m p.2
  have hm : Integrable m μ := integrable_gaussianLogBandDiagonalMajorant η M μ hpair
  have hB : Integrable B (μ.prod μ) := hm.mul_prod hm
  have hab : ∀ j, ∀ᵐ p ∂μ.prod μ, (a j p)^2 ≤ B p := fun j =>
    Filter.Eventually.of_forall (gaussianLogCenteredBand_general_sq_majorized η (T j) hη (hηT j) (hT1 j) hd ρ M hM hρ hpair)
  have hc := ae_tendsto_gaussianLogCenteredBand_to_cutoff η hη T hT
    hηT hd ρ M hM hρ hpair
  have hlp := toLp_two_tendsto_of_sq_domination a h ha hh B hB hab hc
  exact DGRHS.Kernel.integralOperator_nonnegative_of_toLp_limit h hh a ha hlp
    (fun j v => gaussianLogCenteredBand_operator_nonnegative η (T j) hη
      (hηT j) μ (ha j) v)

lemma gaussianLogCenteredTruncatedPair_operator_positive (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (hh : MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∀ v, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)) hh v) := by
  simpa only [gaussianLogTruncatedOperator] using
    gaussianLogTruncatedOperator_positive η hη hd ρ M hM hρ hpair

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogTruncatedOperator_positive
#print axioms DGRHS.Gaussian.gaussianLogTruncatedOperator_positive

#check @DGRHS.Gaussian.norm_sq_centeredGaussianLogBandFeature_general_majorized
#print axioms DGRHS.Gaussian.norm_sq_centeredGaussianLogBandFeature_general_majorized
#check @DGRHS.Gaussian.gaussianLogCenteredBand_general_sq_majorized
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_general_sq_majorized

#check @DGRHS.Gaussian.gaussianLogCenteredTruncatedPair_operator_positive
#print axioms DGRHS.Gaussian.gaussianLogCenteredTruncatedPair_operator_positive
