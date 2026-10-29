import DGRHS.Gaussian.GaussianLogFeatureMeasurability

/-! Supporting development. Weighted proper product-L1 and genuine Fubini prove
Bochner mean zero of the SAME infinite centered Fourier feature. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
variable (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
variable (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
variable (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
variable [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
variable (hpair : Integrable logPhysicalPair
  ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
include hη hd M hM hρ hpair

lemma integrable_gaussianLogCenteredPhase_weighted_product (ψ : Lp ℂ 2 (gaussianLogPhaseMeasure ι η)) :
    Integrable (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) =>
      inner ℝ (ψ q.2) (gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) q.1 q.2))
      ((gaussianRieszDensityMeasure ρ).prod (gaussianLogPhaseMeasure ι η)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let ν := gaussianLogPhaseMeasure ι η
  let F := fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) => gaussianLogCenteredPhase μ q.1 q.2
  let G := fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) => ψ q.2
  have hF : MemLp F 2 (μ.prod ν) := memLp_gaussianLogCenteredPhase_product η hη hd ρ M hM hρ hpair
  have hG : MemLp G 2 (μ.prod ν) := (Lp.memLp ψ).comp_measurePreserving measurePreserving_snd
  have hi := L2.integrable_inner (𝕜 := ℝ) (hG.toLp G) (hF.toLp F)
  apply hi.congr
  filter_upwards [hG.coeFn_toLp,hF.coeFn_toLp] with q hqG hqF
  rw [hqG,hqF]

lemma inner_gaussianLogCenteredInfiniteFeature_raw_pairing (ψ : Lp ℂ 2 (gaussianLogPhaseMeasure ι η))
    (x : EuclideanSpace ℝ ι) :
    inner ℝ ψ (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x) =
      ∫ p,inner ℝ (ψ p) (gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p)
        ∂gaussianLogPhaseMeasure ι η := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x] with p hp
  rw [hp]

lemma integral_inner_gaussianLogCenteredInfiniteFeature_eq_zero
    (ψ : Lp ℂ 2 (gaussianLogPhaseMeasure ι η)) :
    (∫ x,inner ℝ ψ (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x)
      ∂gaussianRieszDensityMeasure ρ) = 0 := by
  let μ := gaussianRieszDensityMeasure ρ
  let ν := gaussianLogPhaseMeasure ι η
  simp_rw [inner_gaussianLogCenteredInfiniteFeature_raw_pairing η hη hd ρ M hM hρ hpair]
  rw [integral_integral_swap (integrable_gaussianLogCenteredPhase_weighted_product η hη hd ρ M hM hρ hpair ψ)]
  change (∫ p,(∫ x,inner ℝ (ψ p) (gaussianLogCenteredPhase μ x p) ∂μ) ∂ν) = 0
  have hz (p : ℝ × (ι → ℝ)) : (∫ x,inner ℝ (ψ p) (gaussianLogCenteredPhase μ x p) ∂μ) = 0 := by
    have hi : Integrable (fun x => gaussianLogCenteredPhase μ x p) μ :=
      (integrable_gaussianLogSpatialPhase μ p).sub (integrable_const _)
    rw [integral_inner hi,integral_gaussianLogCenteredPhase_eq_zero μ p,inner_zero_right]
  simp_rw [hz]
  exact integral_zero _ _

lemma integral_gaussianLogCenteredInfiniteFeature_eq_zero :
    (∫ x,gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x
      ∂gaussianRieszDensityMeasure ρ) = 0 := by
  let μ := gaussianRieszDensityMeasure ρ
  let k := gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  have hi : Integrable k μ := (memLp_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair).integrable (by norm_num)
  have hz := integral_inner_gaussianLogCenteredInfiniteFeature_eq_zero η hη hd ρ M hM hρ hpair (∫ x,k x ∂μ)
  rw [integral_inner hi] at hz
  exact inner_self_eq_zero.mp hz

end DGRHS.Gaussian
#check @DGRHS.Gaussian.integrable_gaussianLogCenteredPhase_weighted_product
#print axioms DGRHS.Gaussian.integrable_gaussianLogCenteredPhase_weighted_product
#check @DGRHS.Gaussian.inner_gaussianLogCenteredInfiniteFeature_raw_pairing
#print axioms DGRHS.Gaussian.inner_gaussianLogCenteredInfiniteFeature_raw_pairing
#check @DGRHS.Gaussian.integral_inner_gaussianLogCenteredInfiniteFeature_eq_zero
#print axioms DGRHS.Gaussian.integral_inner_gaussianLogCenteredInfiniteFeature_eq_zero
#check @DGRHS.Gaussian.integral_gaussianLogCenteredInfiniteFeature_eq_zero
#print axioms DGRHS.Gaussian.integral_gaussianLogCenteredInfiniteFeature_eq_zero
