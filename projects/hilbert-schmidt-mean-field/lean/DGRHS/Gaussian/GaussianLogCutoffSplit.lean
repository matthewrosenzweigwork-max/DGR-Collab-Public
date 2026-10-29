import DGRHS.Gaussian.GaussianLogCutoffNear

/-! Supporting development: finite-band split at the actual max-cutoff scale. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma ae_gaussianLogCutoff_centered_split (η ℓ δ T : ℝ)
    (hη : 0 < η) (hηℓ : η ≤ ℓ) (hℓδ : ℓ ≤ δ) (hδT : δ ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    hoeffdingCentered μ (gaussianLogBandPair η T) =ᵐ[μ.prod μ]
      (hoeffdingCentered μ (gaussianLogBandPair δ T)+
       hoeffdingCentered μ (gaussianLogBandPair ℓ δ))+
       hoeffdingCentered μ (gaussianLogBandPair η ℓ) := by
  let W := gaussianLogBandPair (ι := ι) δ T
  let V := gaussianLogBandPair (ι := ι) ℓ δ
  let R := gaussianLogBandPair (ι := ι) η ℓ
  have hℓ := hη.trans_le hηℓ
  have hδ := hℓ.trans_le hℓδ
  have hW : Integrable W (μ.prod μ) := integrable_gaussianLogBandPair δ T hδ hδT μ
  have hV : Integrable V (μ.prod μ) := integrable_gaussianLogBandPair ℓ δ hℓ hℓδ μ
  have hR : Integrable R (μ.prod μ) := integrable_gaussianLogBandPair η ℓ hη hηℓ μ
  have he : gaussianLogBandPair η T = (W+V)+R := by
    funext q
    change gaussianLogBand η T (q.1-q.2) =
      (gaussianLogBand δ T (q.1-q.2)+gaussianLogBand ℓ δ (q.1-q.2))+
        gaussianLogBand η ℓ (q.1-q.2)
    rw [gaussianLogBand_split η δ T hη (hηℓ.trans hℓδ) hδT,
      gaussianLogBand_split η ℓ δ hη hηℓ hℓδ]
    ring
  rw [he]
  have h1 := ae_hoeffdingCentered_add μ (W+V) R (hW.add hV) hR
  have h2 := ae_hoeffdingCentered_add μ W V hW hV
  filter_upwards [h1,h2] with q hq1 hq2
  rw [hq1]
  simp only [Pi.add_apply]
  rw [hq2]
  rfl

lemma ae_gaussianLogCutoff_particle_split (η ℓ δ T : ℝ)
    (hη : 0 < η) (hηℓ : η ≤ ℓ) (hℓδ : ℓ ≤ δ) (hδT : δ ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (n : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => μ),
      iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η T)) ω =
      iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair ℓ δ)) ω +
      iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η ℓ)) ω +
      iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair δ T)) ω := by
  have he := ae_physical_iidNegativeStatistic_congr μ n _ _
    (ae_gaussianLogCutoff_centered_split η ℓ δ T hη hηℓ hℓδ hδT μ)
  filter_upwards [he] with ω hω
  rw [hω,physical_iidNegativeStatistic_add,physical_iidNegativeStatistic_add]
  ring

end DGRHS.Gaussian

#check @DGRHS.Gaussian.ae_gaussianLogCutoff_centered_split
#print axioms DGRHS.Gaussian.ae_gaussianLogCutoff_centered_split
#check @DGRHS.Gaussian.ae_gaussianLogCutoff_particle_split
#print axioms DGRHS.Gaussian.ae_gaussianLogCutoff_particle_split
