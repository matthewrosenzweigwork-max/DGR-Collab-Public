import DGRHS.Gaussian.GaussianLogScaleCancellation
import DGRHS.Gaussian.LogPhysicalTailComparison
import DGRHS.Gaussian.GaussianLogInfraredConvergence

/-! Supporting development. A uniform proper diagonal majorant uses first pair-log L1,
not a squared logarithmic tail. The finite-band diagonal is its genuine Gram
diagonal and is never read off a product-AE source equality. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianLogBandDiagonalMajorant (η M : ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) : ℝ :=
  2*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*η^(Fintype.card ι : ℝ))) +
  |Real.log η|+1 +
  2*|gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ)/4) M ι| +
  2*|logPhysicalTailIntegral μ| + (∫ p, ‖logPhysicalPair p‖ ∂μ.prod μ) +
  2*Real.log (1+‖x‖)

lemma gaussianLogBandDiagonalMajorant_nonneg (η M : ℝ) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (μ : Measure (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) :
    0 ≤ gaussianLogBandDiagonalMajorant η M μ x := by
  unfold gaussianLogBandDiagonalMajorant
  have hl : 0 ≤ Real.log (1+‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
  have hi : 0 ≤ ∫ p, ‖logPhysicalPair p‖ ∂μ.prod μ := integral_nonneg (fun p => norm_nonneg _)
  positivity

lemma integrable_gaussianLogBandDiagonalMajorant (η M : ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hpair : Integrable logPhysicalPair (μ.prod μ)) :
    Integrable (gaussianLogBandDiagonalMajorant η M μ) μ :=
  (integrable_const _).add ((integrable_log_one_add_norm_of_pair_log μ hpair).const_mul 2)

lemma gaussianLogInfrared_potential_norm_le (T : ℝ)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    ‖∫ y, gaussianLogInfraredPair T (x,y) ∂gaussianRieszDensityMeasure ρ‖ ≤
      gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ)/4) M ι +
        Real.log (1+‖x‖) + logPhysicalTailIntegral (gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure; infer_instance
  have hi := integrable_gaussianLogInfrared_potential T hd ρ M hM hρ hpair x
  have hl := (logPhysical_source_proper_bounds hd ρ M hM hρ hpair x).1
  calc
    _ ≤ ∫ y, ‖gaussianLogInfraredPair T (x,y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖logPhysicalPair (x,y)‖ ∂μ := by
      apply integral_mono_ae hi.norm hl.norm
      filter_upwards [μ.ae_ne x] with y hy
      change ‖gaussianLogAnchored T ‖x-y‖‖ ≤ ‖-Real.log ‖x-y‖‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
      exact gaussianLogAnchored_abs_le T _ (norm_pos_iff.mpr (sub_ne_zero.mpr hy.symm))
    _ ≤ _ := integral_norm_logPhysicalPair_section_le hd ρ M hM hρ hpair x

lemma gaussianLogInfrared_pairMean_le (T : ℝ)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    (∫ p, gaussianLogInfraredPair T p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
    (∫ p, ‖logPhysicalPair p‖
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  apply integral_mono_ae (integrable_gaussianLogInfraredPair_source T hd ρ hpair) hpair.norm
  filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
  have hb := gaussianLogAnchored_abs_le T ‖p.1-p.2‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
  change gaussianLogAnchored T ‖p.1-p.2‖ ≤ ‖-Real.log ‖p.1-p.2‖‖
  simpa only [Real.norm_eq_abs, abs_neg] using (le_abs_self _).trans hb

lemma norm_sq_centeredGaussianLogBandFeature_majorized (η T : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 1 ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    ‖centeredGaussianLogBandFeature η T hη (gaussianRieszDensityMeasure ρ) x‖^2 ≤
      gaussianLogBandDiagonalMajorant η M (gaussianRieszDensityMeasure ρ) x := by
  have hc := gaussianLog_source_low_diagonal_bound η T 1 hη hη1 hT (by norm_num) hd ρ M hM hρ x
  have hp := gaussianLogInfrared_potential_norm_le T hd ρ M hM hρ hpair x
  have hm := gaussianLogInfrared_pairMean_le T hd ρ hpair
  have hp' := neg_le_abs (∫ y,gaussianLogInfraredPair T (x,y) ∂gaussianRieszDensityMeasure ρ)
  rw [← Real.norm_eq_abs] at hp'
  unfold gaussianLogBandDiagonalMajorant
  nlinarith [neg_le_abs (Real.log η),
    le_abs_self (gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ)/4) M ι),
    le_abs_self (logPhysicalTailIntegral (gaussianRieszDensityMeasure ρ))]

lemma gaussianLogCenteredBand_sq_majorized (η T : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 1 ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η T) p^2 ≤
      gaussianLogBandDiagonalMajorant η M (gaussianRieszDensityMeasure ρ) p.1 *
      gaussianLogBandDiagonalMajorant η M (gaussianRieszDensityMeasure ρ) p.2 := by
  rw [← inner_centeredGaussianLogBandFeature η T hη (hη1.trans hT)]
  have hi := norm_inner_le_norm (𝕜 := ℝ)
    (centeredGaussianLogBandFeature η T hη (gaussianRieszDensityMeasure ρ) p.1)
    (centeredGaussianLogBandFeature η T hη (gaussianRieszDensityMeasure ρ) p.2)
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  rw [mul_pow, Real.norm_eq_abs, sq_abs] at hi2
  exact hi2.trans (mul_le_mul
    (norm_sq_centeredGaussianLogBandFeature_majorized η T hη hη1 hT hd ρ M hM hρ hpair p.1)
    (norm_sq_centeredGaussianLogBandFeature_majorized η T hη hη1 hT hd ρ M hM hρ hpair p.2)
    (sq_nonneg _) (gaussianLogBandDiagonalMajorant_nonneg η M hη.le hM _ p.1))

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogBandDiagonalMajorant
#print axioms DGRHS.Gaussian.gaussianLogBandDiagonalMajorant
#check @DGRHS.Gaussian.gaussianLogBandDiagonalMajorant_nonneg
#print axioms DGRHS.Gaussian.gaussianLogBandDiagonalMajorant_nonneg
#check @DGRHS.Gaussian.integrable_gaussianLogBandDiagonalMajorant
#print axioms DGRHS.Gaussian.integrable_gaussianLogBandDiagonalMajorant
#check @DGRHS.Gaussian.gaussianLogInfrared_potential_norm_le
#print axioms DGRHS.Gaussian.gaussianLogInfrared_potential_norm_le
#check @DGRHS.Gaussian.gaussianLogInfrared_pairMean_le
#print axioms DGRHS.Gaussian.gaussianLogInfrared_pairMean_le
#check @DGRHS.Gaussian.norm_sq_centeredGaussianLogBandFeature_majorized
#print axioms DGRHS.Gaussian.norm_sq_centeredGaussianLogBandFeature_majorized
#check @DGRHS.Gaussian.gaussianLogCenteredBand_sq_majorized
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_sq_majorized
