import DGRHS.Gaussian.GaussianRieszParticleSplit

/-! The physical cutoff event is reduced to the SAME positive band using an
actual proper near/low/band decomposition. Only explicit deterministic scale
inequalities remain for the adaptive choice. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma ae_gaussianRieszParticle_low_near_bound (s η α δ β : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηα : η ≤ α) (hαδ : α ≤ δ) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
          (gaussianRieszTruncatedPair s η)) ω ≤
        β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
          (gaussianRieszBandPair s α δ)) ω +
        2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) +
        β*(n : ℝ)*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s)*α^((Fintype.card ι : ℝ)-s))) := by
  let μ := gaussianRieszDensityMeasure ρ
  let C := M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s)*α^((Fintype.card ι : ℝ)-s))
  have hC : 0 ≤ C := by
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    have hd : 0 < (Fintype.card ι : ℝ)-s := by linarith
    have hα := lt_of_lt_of_le hη hηα
    unfold C
    positivity
  have hnear := ae_physical_iidNegativeStatistic_bound μ n hn
    (hoeffdingCentered μ (gaussianRieszNearPair s η α)) C hC
    (ae_gaussianRieszCenteredNearPair_lower_bound s η α hs hη hηα ha ρ M hM hρ)
  have he := ae_physical_iidNegativeStatistic_congr μ n _ _
    (ae_gaussianRieszCenteredTruncated_split s η α δ hs hη hηα hαδ ha ρ M hM hρ)
  filter_upwards [he,hnear] with ω heω hnω
  rw [heω,physical_iidNegativeStatistic_add,physical_iidNegativeStatistic_add]
  have hl := gaussianRieszCenteredTruncated_particle_cap s δ hs
    (lt_of_lt_of_le (lt_of_lt_of_le hη hηα) hαδ) μ n hn ω
  have hb1 := mul_le_mul_of_nonneg_left hl hβ
  have hb2 := mul_le_mul_of_nonneg_left hnω hβ
  dsimp only [C] at hb2
  nlinarith only [hb1,hb2]

lemma ae_gaussianRieszParticle_band_comparison (s η α δ β u : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηα : η ≤ α) (hαδ : α ≤ δ) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (n : ℕ) (hn : 1 ≤ n)
    (hsmall : 2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) +
        β*(n : ℝ)*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s)*α^((Fintype.card ι : ℝ)-s))) ≤ u/2) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      u ≤ β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszTruncatedPair s η)) ω →
          u ≤ iidNegativeStatistic n (gaussianRieszMasterBand s α δ (2*β) ρ) ω := by
  filter_upwards [ae_gaussianRieszParticle_low_near_bound s η α δ β hs hη hηα hαδ hβ ha ρ M hM hρ n hn] with ω hω
  intro hx
  unfold gaussianRieszMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  linarith

end DGRHS.Gaussian

#check DGRHS.Gaussian.ae_gaussianRieszParticle_low_near_bound
#print axioms DGRHS.Gaussian.ae_gaussianRieszParticle_low_near_bound

#check DGRHS.Gaussian.ae_gaussianRieszParticle_band_comparison
#print axioms DGRHS.Gaussian.ae_gaussianRieszParticle_band_comparison
