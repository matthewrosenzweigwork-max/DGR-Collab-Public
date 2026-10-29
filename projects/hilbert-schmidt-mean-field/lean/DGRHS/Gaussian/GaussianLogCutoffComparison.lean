import DGRHS.Gaussian.GaussianLogCutoffSplit

/-! Supporting development: same actual finite-band source comparison, uniform in the physical cutoff. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma ae_gaussianLogCutoffApproxExponent_comparison (η α δ T β : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ)
    (hα : 0 < α) (hαδ : α ≤ δ) (hδ1 : δ ≤ 1) (hT : 1 ≤ T) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      gaussianLogCutoffApproxExponent (gaussianRieszDensityMeasure ρ) β η T n ω ≤
      β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair (max η α) δ)) ω +
      β*(n : ℝ)*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) +
      β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4) := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  have hℓ : 0 < max η α := hη.trans_le (le_max_left _ _)
  have hℓδ : max η α ≤ δ := max_le hηδ hαδ
  let C := β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4)
  have hδ := lt_of_lt_of_le hα hαδ
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  filter_upwards [ae_gaussianLogCutoff_particle_split η (max η α) δ T hη (le_max_left _ _) hℓδ (hδ1.trans hT) μ n,
    ae_gaussianLogCutoff_near_particle_cap η α hη hα hd ρ M hM hρ n hn] with ω hsplit hnear
  have hlow := gaussianLogCenteredBand_particle_diagonal_cap δ T hδ (hδ1.trans hT) μ n hn ω
  have hlow' := (le_div_iff₀ (by positivity : 0 < 2*(n : ℝ))).mp hlow
  have hs : (∑ i : Fin n,
      (β*(∫ y,gaussianLogBandPair η T (ω i,y) ∂μ) +
      β/2*‖centeredGaussianLogBandFeature δ T hδ μ (ω i)‖^2 -
      β/2*(∫ p,gaussianLogBandPair η T p ∂μ.prod μ) - β/2*gaussianLogCounterterm T)) ≤ (n : ℝ)*C := by
    calc
      _ ≤ ∑ _ : Fin n,C := Finset.sum_le_sum (fun i hi =>
        gaussianLog_cutoff_low_diagonal_bound η δ T β hη hηδ hδ1 hT hβ hd ρ M hM hρ (ω i))
      _ = _ := by simp
  have he : (∑ i : Fin n,
      (β*(∫ y,gaussianLogBandPair η T (ω i,y) ∂μ) +
      β/2*‖centeredGaussianLogBandFeature δ T hδ μ (ω i)‖^2 -
      β/2*(∫ p,gaussianLogBandPair η T p ∂μ.prod μ) - β/2*gaussianLogCounterterm T)) =
      β*(∑ i : Fin n,(∫ y,gaussianLogBandPair η T (ω i,y) ∂μ)) +
      β/2*(∑ i : Fin n,‖centeredGaussianLogBandFeature δ T hδ μ (ω i)‖^2) -
      (n : ℝ)*β/2*(∫ p,gaussianLogBandPair η T p ∂μ.prod μ) -
      (n : ℝ)*β/2*gaussianLogCounterterm T := by
    simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    simp
    ring
  rw [he] at hs
  have hloβ := mul_le_mul_of_nonneg_left hlow' hβ
  have hneβ := mul_le_mul_of_nonneg_left hnear hβ
  have hneβn := mul_le_mul_of_nonneg_left hneβ hn'.le
  have hex : (n : ℝ)*gaussianLogCutoffApproxExponent μ β η T n ω =
      (n : ℝ)*β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η T)) ω +
      β*(∑ i : Fin n,(∫ y,gaussianLogBandPair η T (ω i,y) ∂μ)) -
      (n : ℝ)*β/2*(∫ p,gaussianLogBandPair η T p ∂μ.prod μ) -
      (n : ℝ)*β/2*gaussianLogCounterterm T := by
    unfold gaussianLogCutoffApproxExponent
    field_simp <;> ring
  change gaussianLogCutoffApproxExponent μ β η T n ω ≤ _
  change iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η T)) ω = _ at hsplit
  have hnle : 0 ≤ (n : ℝ) := hn'.le
  suffices hscaled : (n : ℝ)*gaussianLogCutoffApproxExponent μ β η T n ω ≤
      (n : ℝ)*(β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair (max η α) δ)) ω +
      β*(n : ℝ)*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) +
      β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4)) by
    exact (mul_le_mul_iff_right₀ hn').mp (by simpa only [mul_comm] using hscaled)
  rw [hex,hsplit]
  dsimp [C] at hs
  nlinarith


end DGRHS.Gaussian

#check @DGRHS.Gaussian.ae_gaussianLogCutoffApproxExponent_comparison
#print axioms DGRHS.Gaussian.ae_gaussianLogCutoffApproxExponent_comparison
