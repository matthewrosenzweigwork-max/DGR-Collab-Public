import DGRHS.Gaussian.GaussianLogParticleSplit
import DGRHS.Gaussian.GaussianLogAdaptiveBounds
import DGRHS.Gaussian.GaussianLogMasterNorms

/-! The genuine logarithmic source exponent large event
implies the actual high-band statistic large event. No event premise is supplied. -/
noncomputable section
open MeasureTheory Real
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def gaussianLogShortConstant (M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ))

def gaussianLogSourceLowConstant (δ β M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  β*gaussianLogShortConstant M ι*δ^(Fintype.card ι : ℝ)+β/2*(-Real.log δ+1/4)

lemma gaussianLogShortConstant_nonneg (M : ℝ) (hM : 0 ≤ M)
    (hd : 0 < (Fintype.card ι : ℝ)) : 0 ≤ gaussianLogShortConstant M ι := by
  unfold gaussianLogShortConstant
  positivity

lemma ae_gaussianLogSource_adaptive_comparison (δ T β A u₀ u : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 1 ≤ T) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n)
    (hA : 0 < A) (hAC : 8*gaussianLogShortConstant M ι ≤ A)
    (hu₀ : 1 ≤ u₀) (hlow : 4*gaussianLogSourceLowConstant δ β M ι ≤ u₀) (hu : u₀ ≤ u) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      u ≤ gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β T n ω →
      u ≤ iidNegativeStatistic n
        (gaussianLogMasterBand (gaussianLogAdaptiveScale δ A β (n : ℝ) u (Fintype.card ι : ℝ))
          δ (2*β) (gaussianRieszDensityMeasure ρ)) ω := by
  let α := gaussianLogAdaptiveScale δ A β (n : ℝ) u (Fintype.card ι : ℝ)
  have hu' : 0 < u := by linarith
  have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp := gaussianLogAdaptiveScale_pos_le δ A β (n : ℝ) u (Fintype.card ι : ℝ) hδ hA hβ hn' hu'
  have hnear := gaussianLogAdaptiveScale_near_error_le δ A β (n : ℝ) u (Fintype.card ι : ℝ)
    (gaussianLogShortConstant M ι) hδ hA hβ hn' hu' hd
    (gaussianLogShortConstant_nonneg M hM hd) hAC
  filter_upwards [ae_gaussianLogSourceApproxExponent_comparison α δ T β hp.1 hp.2 hδ1 hT hβ hd ρ M hM hρ n hn]
    with ω hω
  intro hx
  unfold gaussianLogMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  have hnerewrite : β*(n : ℝ)*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) =
      β*(n : ℝ)*gaussianLogShortConstant M ι*α^(Fintype.card ι : ℝ) := by
    unfold gaussianLogShortConstant
    ring
  have hlowrewrite : β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4) = gaussianLogSourceLowConstant δ β M ι := by
    unfold gaussianLogSourceLowConstant gaussianLogShortConstant
    ring
  rw [hnerewrite] at hω
  change β*(n : ℝ)*gaussianLogShortConstant M ι*α^(Fintype.card ι : ℝ) ≤ u/8 at hnear
  have hω' : gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β T n ω ≤
      β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair α δ)) ω +
      β*(n : ℝ)*gaussianLogShortConstant M ι*α^(Fintype.card ι : ℝ) + gaussianLogSourceLowConstant δ β M ι := by
    rw [← hlowrewrite]
    simpa only [add_assoc] using hω
  nlinarith only [hx,hω',hnear,hlow,hu,hu']

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogShortConstant
#print axioms DGRHS.Gaussian.gaussianLogShortConstant
#check DGRHS.Gaussian.gaussianLogSourceLowConstant
#print axioms DGRHS.Gaussian.gaussianLogSourceLowConstant
#check DGRHS.Gaussian.gaussianLogShortConstant_nonneg
#print axioms DGRHS.Gaussian.gaussianLogShortConstant_nonneg
#check DGRHS.Gaussian.ae_gaussianLogSource_adaptive_comparison
#print axioms DGRHS.Gaussian.ae_gaussianLogSource_adaptive_comparison
