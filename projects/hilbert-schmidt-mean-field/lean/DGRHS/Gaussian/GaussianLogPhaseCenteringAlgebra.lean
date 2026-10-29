import DGRHS.Gaussian.GaussianLogCenteredPhase

/-! Supporting development. Pointwise raw-phase centering algebra with proper EVERY-frequency
source integrals. No point-evaluation functional on L2 is used. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma gaussianLogPhase_double_mean_inner
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (p : ℝ × (ι → ℝ)) :
    (∫ x, (∫ y, inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhase y p) ∂μ) ∂μ) =
      ‖gaussianLogSpatialPhaseMean μ p‖^2 := by
  let χ := fun x : EuclideanSpace ℝ ι => gaussianLogSpatialPhase x p
  let m := gaussianLogSpatialPhaseMean μ p
  have hi : Integrable χ μ := integrable_gaussianLogSpatialPhase μ p
  have hl (v : ℂ) : (∫ x, inner ℝ (χ x) v ∂μ) = inner ℝ m v := by
    simp_rw [real_inner_comm v (χ _)]
    rw [integral_inner hi]
    exact real_inner_comm _ _
  have hd : (∫ x, (∫ y, inner ℝ (χ x) (χ y) ∂μ) ∂μ) = inner ℝ m m := by
    simp_rw [integral_inner hi]
    exact hl m
  rw [real_inner_self_eq_norm_sq] at hd
  exact hd

lemma gaussianLogCenteredPhase_inner_expansion
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (x y : EuclideanSpace ℝ ι) (p : ℝ × (ι → ℝ)) :
    inner ℝ (gaussianLogCenteredPhase μ x p) (gaussianLogCenteredPhase μ y p) =
      inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhase y p) -
      (∫ z, inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhase z p) ∂μ) -
      (∫ z, inner ℝ (gaussianLogSpatialPhase z p) (gaussianLogSpatialPhase y p) ∂μ) +
      (∫ a, (∫ b, inner ℝ (gaussianLogSpatialPhase a p) (gaussianLogSpatialPhase b p) ∂μ) ∂μ) := by
  let χ := fun z : EuclideanSpace ℝ ι => gaussianLogSpatialPhase z p
  let m := gaussianLogSpatialPhaseMean μ p
  have hi : Integrable χ μ := integrable_gaussianLogSpatialPhase μ p
  have hl (v : ℂ) : (∫ z, inner ℝ (χ z) v ∂μ) = inner ℝ m v := by
    simp_rw [real_inner_comm v (χ _)]
    rw [integral_inner hi]
    exact real_inner_comm _ _
  have hd : (∫ a, (∫ b, inner ℝ (χ a) (χ b) ∂μ) ∂μ) = inner ℝ m m := by
    simp_rw [integral_inner hi]
    exact hl m
  change inner ℝ (χ x-m) (χ y-m) = inner ℝ (χ x) (χ y) -
    (∫ z, inner ℝ (χ x) (χ z) ∂μ) - (∫ z, inner ℝ (χ z) (χ y) ∂μ) +
    (∫ a, (∫ b, inner ℝ (χ a) (χ b) ∂μ) ∂μ)
  rw [inner_sub_left,inner_sub_right,inner_sub_right,integral_inner hi,hl,hd]
  dsimp [m, gaussianLogSpatialPhaseMean, χ]
  ring

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogPhase_double_mean_inner
#print axioms DGRHS.Gaussian.gaussianLogPhase_double_mean_inner
#check @DGRHS.Gaussian.gaussianLogCenteredPhase_inner_expansion
#print axioms DGRHS.Gaussian.gaussianLogCenteredPhase_inner_expansion
