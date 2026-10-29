import DGRHS.Gaussian.SharpnessRieszPotential

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- Genuine pair L1 throughout0<s<d, derived from every proper bounded physical section. -/
theorem sharpness_riesz_pair_integrable (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Integrable (gaussianRieszPhysicalPair s)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  have hm := stronglyMeasurable_gaussianRieszPhysicalPair (ι := ι) s
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun x => (sharpness_riesz_potential_bound s hs ha ρ M hM hρ x).1
  · refine (integrable_const B).mono' hm.norm.integral_prod_right'.aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro x
    have hx := sharpness_riesz_potential_bound s hs ha ρ M hM hρ x
    have he : (fun y => ‖gaussianRieszPhysicalPair s (x,y)‖) =
        (fun y => gaussianRieszPhysicalPair s (x,y)) := by
      funext y
      apply Real.norm_of_nonneg
      unfold gaussianRieszPhysicalPair
      positivity
    rw [he, Real.norm_of_nonneg hx.2.1]
    exact hx.2.2

/-- The same canonical centered physical kernel is genuinely proper at the threshold. -/
theorem sharpness_centered_riesz_integrable (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Integrable (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  exact DGRHS.integrable_centeredKernel (gaussianRieszDensityMeasure ρ)
    (fun x y => gaussianRieszPhysicalPair s (x,y))
    (sharpness_riesz_pair_integrable s hs ha ρ M hM hρ)

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_riesz_pair_integrable
#print axioms DGRHS.Gaussian.sharpness_centered_riesz_integrable
#check @DGRHS.Gaussian.sharpness_riesz_pair_integrable
