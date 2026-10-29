import DGRHS.Gaussian.GaussianLogFiniteCutoff

/-! Supporting development: actual finite-band near cap, with the empty near band included.
No totalized literal diagonal is substituted for the smooth finite-band diagonal. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma gaussianLogCenteredBand_lower_short_bound (η α : ℝ) (hη : 0 < η) (hηα : η ≤ α)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    -hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η α) p ≤
      2*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) := by
  have h1 := gaussianLogBand_potential_le_short_bound η α hη hηα hd ρ M hM hρ p.1
  have h2 := gaussianLogBand_potential_le_short_bound η α hη hηα hd ρ M hM hρ p.2
  have he : (fun x => gaussianLogBand η α (x-p.2)) =
      (fun x => gaussianLogBand η α (p.2-x)) := by
    funext x
    simp only [gaussianLogBand,norm_sub_rev]
  have hn := gaussianLogBand_nonneg η α hη (p.1-p.2)
  have hm : 0 ≤ ∫ z,gaussianLogBandPair η α z
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) :=
    integral_nonneg (fun z => gaussianLogBand_nonneg η α hη _)
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change -(gaussianLogBand η α (p.1-p.2) -
    (∫ y,gaussianLogBand η α (p.1-y) ∂gaussianRieszDensityMeasure ρ) -
    (∫ x,gaussianLogBand η α (x-p.2) ∂gaussianRieszDensityMeasure ρ) +
    (∫ z,gaussianLogBandPair η α z ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) ≤ _
  rw [he]
  change (∫ y,gaussianLogBand η α (p.1-y) ∂gaussianRieszDensityMeasure ρ) ≤ _ at h1
  change (∫ y,gaussianLogBand η α (p.2-y) ∂gaussianRieszDensityMeasure ρ) ≤ _ at h2
  linarith

lemma gaussianLogBand_self_zero (η : ℝ) : gaussianLogBand (ι := ι) η η = 0 := by
  funext x
  simp [gaussianLogBand]

lemma gaussianLogCentered_near_max_lower (η α : ℝ) (hη : 0 < η) (hα : 0 < α)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    -hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η (max η α)) p ≤
      2*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) := by
  by_cases h : η ≤ α
  · rw [max_eq_right h]
    exact gaussianLogCenteredBand_lower_short_bound η α hη h hd ρ M hM hρ p
  · rw [max_eq_left (le_of_not_ge h)]
    have he : gaussianLogBandPair (ι := ι) η η = 0 := by
      funext q
      change gaussianLogBand η η (q.1-q.2) = 0
      rw [gaussianLogBand_self_zero]
      rfl
    rw [he]
    simp only [hoeffdingCentered,DGRHS.centeredKernel,DGRHS.potential,DGRHS.secondPotential,
      Pi.zero_apply,integral_zero,sub_zero,zero_add,neg_zero]
    positivity

lemma ae_gaussianLogCutoff_near_particle_cap (η α : ℝ) (hη : 0 < η) (hα : 0 < α)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianLogBandPair η (max η α))) ω ≤
      (n : ℝ)*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) := by
  apply ae_physical_iidNegativeStatistic_bound _ n hn _ _ (by positivity)
  exact Filter.Eventually.of_forall (gaussianLogCentered_near_max_lower η α hη hα hd ρ M hM hρ)

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogCenteredBand_lower_short_bound
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_lower_short_bound
#check @DGRHS.Gaussian.gaussianLogBand_self_zero
#print axioms DGRHS.Gaussian.gaussianLogBand_self_zero
#check @DGRHS.Gaussian.gaussianLogCentered_near_max_lower
#print axioms DGRHS.Gaussian.gaussianLogCentered_near_max_lower
#check @DGRHS.Gaussian.ae_gaussianLogCutoff_near_particle_cap
#print axioms DGRHS.Gaussian.ae_gaussianLogCutoff_near_particle_cap
