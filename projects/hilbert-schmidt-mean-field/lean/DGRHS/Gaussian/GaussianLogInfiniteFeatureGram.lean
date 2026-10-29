import DGRHS.Gaussian.GaussianLogFeatureMeanZero

/-! Supporting development. The SAME actual infinite centered phase has the SAME
literal cutoff Gram kernel product-AE, obtained from genuine proper band exhaustion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma tendsto_integral_gaussianLogPhase_band (η : ℝ) (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (F : (ℝ × (ι → ℝ)) → ℝ) (hF : Integrable F (gaussianLogPhaseMeasure ι η)) :
    Tendsto (fun j => ∫ p,F p ∂(gaussianLogBandMeasure η (T j)).prod (finiteStandardGaussian ι))
      atTop (𝓝 (∫ p,F p ∂gaussianLogPhaseMeasure ι η)) := by
  let ν := gaussianLogPhaseMeasure ι η
  let E := fun j => Iic (T j) ×ˢ (univ : Set (ι → ℝ))
  have hEj (j : ℕ) : MeasurableSet (E j) := measurableSet_Iic.prod MeasurableSet.univ
  have he (j : ℕ) : (∫ p,(E j).indicator F p ∂ν) =
      ∫ p,F p ∂(gaussianLogBandMeasure η (T j)).prod (finiteStandardGaussian ι) := by
    rw [integral_indicator (hEj j),gaussianLogPhaseMeasure_restrict]
  change Tendsto (fun j => ∫ p,F p ∂(gaussianLogBandMeasure η (T j)).prod (finiteStandardGaussian ι))
    atTop (𝓝 (∫ p,F p ∂ν))
  simp_rw [← he]
  apply tendsto_integral_of_dominated_convergence (fun p => ‖F p‖)
  · intro j;exact hF.aestronglyMeasurable.indicator (hEj j)
  · exact hF.norm
  · intro j
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ E j
      · simp only [indicator_of_mem hp,le_refl]
      · simp only [indicator_of_notMem hp,norm_zero];exact norm_nonneg _)
  · exact Eventually.of_forall (fun p => by
      have hp : ∀ᶠ j in atTop,p ∈ E j := by
        filter_upwards [(tendsto_atTop.1 hT) p.1] with j hj
        exact ⟨hj,mem_univ _⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [hp] with j hj
      simp only [indicator_of_mem hj])

variable (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
variable (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
variable (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
variable [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
variable (hpair : Integrable logPhysicalPair
  ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
include hη hd M hM hρ hpair

lemma integrable_gaussianLogCenteredPhase_inner (x y : EuclideanSpace ℝ ι) :
    Integrable (fun p => inner ℝ (gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p)
      (gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) y p)) (gaussianLogPhaseMeasure ι η) := by
  have hi := L2.integrable_inner (𝕜 := ℝ)
    (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x)
    (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair y)
  apply hi.congr
  filter_upwards [coeFn_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x,
    coeFn_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair y] with p hx hy
  rw [hx,hy]

lemma inner_gaussianLogCenteredInfiniteFeature (x y : EuclideanSpace ℝ ι) :
    inner ℝ (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x)
      (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair y) =
    ∫ p,inner ℝ (gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p)
      (gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) y p) ∂gaussianLogPhaseMeasure ι η := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x,
    coeFn_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair y] with p hx hy
  rw [hx,hy]

lemma ae_gaussianLogTruncatedPair_eq_infiniteFeatureGram :
    ∀ᵐ p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ),
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η) p =
      inner ℝ (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair p.1)
        (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair p.2) := by
  let μ := gaussianRieszDensityMeasure ρ
  let T : ℕ → ℝ := fun j => max η (j+1 : ℕ)
  have hT : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun j => le_max_right _ _)
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hTη (j : ℕ) : η ≤ T j := le_max_left _ _
  filter_upwards [ae_tendsto_gaussianLogCenteredBand_to_cutoff η hη T hT hTη hd ρ M hM hρ hpair] with p hp
  have hc := tendsto_integral_gaussianLogPhase_band η T hT
    (fun q => inner ℝ (gaussianLogCenteredPhase μ p.1 q) (gaussianLogCenteredPhase μ p.2 q))
    (integrable_gaussianLogCenteredPhase_inner η hη hd ρ M hM hρ hpair p.1 p.2)
  change Tendsto (fun j => ∫ q,inner ℝ (gaussianLogCenteredPhase μ p.1 q) (gaussianLogCenteredPhase μ p.2 q)
    ∂(gaussianLogBandMeasure η (T j)).prod (finiteStandardGaussian ι)) atTop
    (𝓝 (∫ q,inner ℝ (gaussianLogCenteredPhase μ p.1 q) (gaussianLogCenteredPhase μ p.2 q)
      ∂gaussianLogPhaseMeasure ι η)) at hc
  simp_rw [integral_gaussianLogCenteredPhase_inner_band η _ hη (hTη _) μ] at hc
  rw [← inner_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair] at hc
  exact tendsto_nhds_unique hp hc

end DGRHS.Gaussian
#check @DGRHS.Gaussian.tendsto_integral_gaussianLogPhase_band
#print axioms DGRHS.Gaussian.tendsto_integral_gaussianLogPhase_band
#check @DGRHS.Gaussian.integrable_gaussianLogCenteredPhase_inner
#print axioms DGRHS.Gaussian.integrable_gaussianLogCenteredPhase_inner
#check @DGRHS.Gaussian.inner_gaussianLogCenteredInfiniteFeature
#print axioms DGRHS.Gaussian.inner_gaussianLogCenteredInfiniteFeature
#check @DGRHS.Gaussian.ae_gaussianLogTruncatedPair_eq_infiniteFeatureGram
#print axioms DGRHS.Gaussian.ae_gaussianLogTruncatedPair_eq_infiniteFeatureGram
