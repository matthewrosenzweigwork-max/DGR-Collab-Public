import DGRHS.Gaussian.GaussianRieszAdaptiveScale

/-! Genuine adaptive physical event comparison, including the empty near
band. Deterministic cutoffs depend on height and particle number; the fixed
low scale and constants do not depend on the regularization. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def gaussianRieszShortConstant (s M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
    ((Fintype.card ι : ℝ)-s))

lemma ae_gaussianRieszParticle_empty_near_comparison (s η δ β u : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (n : ℕ) (hn : 1 ≤ n)
    (hsmall : 2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) ≤ u/2) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      u ≤ β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszTruncatedPair s η)) ω →
          u ≤ iidNegativeStatistic n (gaussianRieszMasterBand s η δ (2*β) ρ) ω := by
  let μ := gaussianRieszDensityMeasure ρ
  have he := ae_physical_iidNegativeStatistic_congr μ n _ _
    (ae_gaussianRieszCenteredTruncated_split s η η δ hs hη le_rfl hηδ ha ρ M hM hρ)
  have hz : hoeffdingCentered μ (gaussianRieszNearPair (ι := ι) s η η) = 0 := by
    rw [gaussianRieszNearPair_zero]
    funext p
    simp [hoeffdingCentered,DGRHS.centeredKernel,DGRHS.potential,DGRHS.secondPotential]
  filter_upwards [he] with ω heω
  rw [hz,add_zero,physical_iidNegativeStatistic_add] at heω
  intro hx
  have hl := mul_le_mul_of_nonneg_left (gaussianRieszCenteredTruncated_particle_cap s δ hs
    (lt_of_lt_of_le hη hηδ) μ n hn ω) hβ
  unfold gaussianRieszMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  rw [heω] at hx
  nlinarith only [hl,hx,hsmall]

lemma ae_gaussianRieszParticle_adaptive_comparison (s η δ β A u₀ u : ℝ)
    (hs : 0 < s) (hη : 0 < η) (hηδ : η ≤ δ) (hδ : 0 < δ) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (hAcontrol : 4*β*gaussianRieszShortConstant s M ι ≤ A)
    (hu₀ : 1 ≤ u₀) (hlow : 8*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) ≤ u₀)
    (hu : u₀ ≤ u) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      u ≤ β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszTruncatedPair s η)) ω →
          u ≤ iidNegativeStatistic n (gaussianRieszMasterBand s
            (max (gaussianRieszAdaptiveScale δ A (n : ℝ) u (Fintype.card ι : ℝ) s) η)
            δ (2*β) ρ) ω := by
  let d := gaussianRieszAdaptiveScale δ A (n : ℝ) u (Fintype.card ι : ℝ) s
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  have hu' : 0 < u := by linarith
  have hdim : 0 < (Fintype.card ι : ℝ)-s := by linarith
  have hd := gaussianRieszAdaptiveScale_pos_le δ A (n : ℝ) u (Fintype.card ι : ℝ) s hδ hA hn' hu'
  change ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
    u ≤ β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszTruncatedPair s η)) ω →
      u ≤ iidNegativeStatistic n (gaussianRieszMasterBand s (max d η) δ (2*β) ρ) ω
  by_cases hηd : η ≤ d
  · have hp := gaussianRieszAdaptiveScale_power_le δ A (n : ℝ) u (Fintype.card ι : ℝ) s hδ hA hn' hu' hdim
    have hp' : d^((Fintype.card ι : ℝ)-s)*(A*(n : ℝ)) ≤ u :=
      (le_div_iff₀ (mul_pos hA hn')).1 hp
    have hprod := mul_le_mul_of_nonneg_right hAcontrol
      (mul_nonneg hn'.le (Real.rpow_nonneg hd.1.le ((Fintype.card ι : ℝ)-s)))
    have hnear : β*(n : ℝ)*gaussianRieszShortConstant s M ι*d^((Fintype.card ι : ℝ)-s) ≤ u/4 := by
      nlinarith only [hp',hprod]
    have hsmall : 2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) +
        β*(n : ℝ)*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s)*d^((Fintype.card ι : ℝ)-s))) ≤ u/2 := by
      dsimp [gaussianRieszShortConstant] at hnear
      nlinarith only [hnear,hlow,hu]
    rw [max_eq_left hηd]
    exact ae_gaussianRieszParticle_band_comparison s η d δ β u hs hη hηd hd.2 hβ ha ρ M hM hρ n hn hsmall
  · have hdη : d ≤ η := le_of_not_ge hηd
    rw [max_eq_right hdη]
    exact ae_gaussianRieszParticle_empty_near_comparison s η δ β u hs hη hηδ hβ ha ρ M hM hρ n hn
        (by linarith : 2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) ≤ u/2)

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszShortConstant
#print axioms DGRHS.Gaussian.gaussianRieszShortConstant

#check DGRHS.Gaussian.ae_gaussianRieszParticle_empty_near_comparison
#print axioms DGRHS.Gaussian.ae_gaussianRieszParticle_empty_near_comparison

#check DGRHS.Gaussian.ae_gaussianRieszParticle_adaptive_comparison
#print axioms DGRHS.Gaussian.ae_gaussianRieszParticle_adaptive_comparison
