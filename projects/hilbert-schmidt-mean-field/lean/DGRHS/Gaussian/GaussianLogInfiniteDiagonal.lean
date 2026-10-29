import DGRHS.Gaussian.GaussianLogPhaseProductL2

/-! Supporting development. Genuine infinite-phase diagonal convergence and the
sharp diagonal bound retaining the SAME physical logarithmic potential. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
variable (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
variable (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
variable (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
variable [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
variable (hpair : Integrable logPhysicalPair
  ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
include hη hd M hM hρ hpair

lemma tendsto_integral_gaussianLogCenteredPhase_sq_band (T : ℕ → ℝ)
    (hT : Tendsto T atTop atTop) (x : EuclideanSpace ℝ ι) :
    Tendsto (fun j => ∫ p, ‖gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p‖^2
      ∂(gaussianLogBandMeasure η (T j)).prod (finiteStandardGaussian ι)) atTop
      (𝓝 (∫ p, ‖gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p‖^2
        ∂gaussianLogPhaseMeasure ι η)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let ν := gaussianLogPhaseMeasure ι η
  let F := fun p => ‖gaussianLogCenteredPhase μ x p‖^2
  let E := fun j => Iic (T j) ×ˢ (univ : Set (ι → ℝ))
  have hEj (j : ℕ) : MeasurableSet (E j) := measurableSet_Iic.prod MeasurableSet.univ
  have he (j : ℕ) : (∫ p,(E j).indicator F p ∂ν) =
      ∫ p,F p ∂(gaussianLogBandMeasure η (T j)).prod (finiteStandardGaussian ι) := by
    rw [integral_indicator (hEj j),gaussianLogPhaseMeasure_restrict]
  change Tendsto (fun j => ∫ p,F p ∂(gaussianLogBandMeasure η (T j)).prod (finiteStandardGaussian ι)) atTop (𝓝 (∫ p,F p ∂ν))
  simp_rw [← he]
  apply tendsto_integral_of_dominated_convergence F
  · intro j
    exact (((stronglyMeasurable_gaussianLogCenteredPhase_section μ x).norm.pow 2).indicator
      (hEj j)).aestronglyMeasurable
  · exact (integrable_gaussianLogCenteredPhase_sq η hη hd ρ M hM hρ hpair x).1
  · intro j
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ E j
      · simp only [indicator_of_mem hp,Real.norm_of_nonneg (sq_nonneg _),F,le_refl]
      · simp only [indicator_of_notMem hp,norm_zero];exact sq_nonneg _)
  · exact Eventually.of_forall (fun p => by
      have hp : ∀ᶠ j in atTop,p ∈ E j := by
        filter_upwards [(tendsto_atTop.1 hT) p.1] with j hj
        exact ⟨hj,mem_univ _⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [hp] with j hj
      simp only [indicator_of_mem hj])

lemma norm_sq_gaussianLogCenteredInfiniteFeature_le_sourcePotential (x : EuclideanSpace ℝ ι) :
    ‖gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x‖^2 ≤
      2*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*η^(Fintype.card ι : ℝ)))
        -Real.log η+1/4-2*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x +
        (∫ p,logPhysicalPair p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let T : ℕ → ℝ := fun j => max η (j+1 : ℕ)
  have hT : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun j => le_max_right _ _)
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hTη (j : ℕ) : η ≤ T j := le_max_left _ _
  have hT1 (j : ℕ) : 1 ≤ T j := by
    have hj : (1 : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 j)
    exact hj.trans (le_max_right _ _)
  have hD := tendsto_integral_gaussianLogCenteredPhase_sq_band η hη hd ρ M hM hρ hpair T hT x
  have hP := tendsto_gaussianLogInfrared_potential T hT hd ρ M hM hρ hpair x
  have hI := tendsto_gaussianLogInfrared_pairMean T hT hd ρ hpair
  have hB (j : ℕ) :
      (∫ p,‖gaussianLogCenteredPhase μ x p‖^2 ∂(gaussianLogBandMeasure η (T j)).prod (finiteStandardGaussian ι)) +
      2*(∫ y,gaussianLogInfraredPair (T j) (x,y) ∂μ) -
      (∫ p,gaussianLogInfraredPair (T j) p ∂μ.prod μ) ≤
      2*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*η^(Fintype.card ι : ℝ))) -Real.log η+1/4 := by
    rw [integral_gaussianLogCenteredPhase_sq_band η (T j) hη (hTη j) μ x]
    have hc := gaussianLog_source_low_diagonal_cancellation η (T j) 1 hη (hTη j) hd ρ M hM hρ x
    have hs := gaussianLogShortRange_convolution_le η hη hd ρ M hM hρ x
    change (∫ y,gaussianLogShortPair η (x,y) ∂μ) ≤ _ at hs
    have ht := gaussianLogCounterterm_low_scale_bound η (T j) hη (hT1 j)
    have hn : 0 ≤ ∫ p,gaussianLogShortPair η p ∂μ.prod μ :=
      integral_nonneg (fun p => gaussianLogShortRange_nonneg η _)
    linarith
  have hb := le_of_tendsto ((hD.add (hP.const_mul 2)).sub hI) (Eventually.of_forall hB)
  rw [norm_sq_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair]
  linarith

end DGRHS.Gaussian
#check @DGRHS.Gaussian.tendsto_integral_gaussianLogCenteredPhase_sq_band
#print axioms DGRHS.Gaussian.tendsto_integral_gaussianLogCenteredPhase_sq_band
#check @DGRHS.Gaussian.norm_sq_gaussianLogCenteredInfiniteFeature_le_sourcePotential
#print axioms DGRHS.Gaussian.norm_sq_gaussianLogCenteredInfiniteFeature_le_sourcePotential
