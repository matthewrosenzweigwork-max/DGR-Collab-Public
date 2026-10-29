/- Source836 uses the operator on FULL L2. Its actual restriction to the
mean-zero subspace has smaller norm; the SAME inverse therefore satisfies
exactly the printed full-space covariance comparison. -/
import DGRHS.Kernel.PositiveResolventBounds
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.Kernel
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
lemma norm_integralOperatorOnMeanZero_le (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p) (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0) :
    ‖integralOperatorOnMeanZero h hh hs hc‖ ≤ ‖integralOperator h hh‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖integralOperator h hh (v : Lp ℝ 2 μ)‖ ≤
    ‖integralOperator h hh‖ * ‖(v : Lp ℝ 2 μ)‖
  exact (integralOperator h hh).le_opNorm v

theorem meanZero_kernel_resolvent_fullnorm_bounds [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p) (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
    (hp : ∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (integralOperator h hh v))
    (β : ℝ) (hβ : 0 ≤ β) (R : meanZeroL2 μ →L[ℝ] meanZeroL2 μ)
    (hR : ∀ v,R v+β • integralOperatorOnMeanZero h hh hs hc (R v)=v)
    (v : meanZeroL2 μ) :
    ‖v‖^2/(1+β*‖integralOperator h hh‖) ≤ inner ℝ v (R v) ∧
      inner ℝ v (R v) ≤ ‖v‖^2 := by
  obtain ⟨hl,hu⟩ := meanZero_kernel_resolvent_quadratic_bounds h hh hs hc hp β hβ R hR v
  refine ⟨le_trans ?_ hl,hu⟩
  apply div_le_div_of_nonneg_left (sq_nonneg _)
    (by nlinarith [mul_nonneg hβ (norm_nonneg (integralOperatorOnMeanZero h hh hs hc))])
  nlinarith [mul_le_mul_of_nonneg_left (norm_integralOperatorOnMeanZero_le h hh hs hc) hβ]
end DGRHS.Kernel
#check @DGRHS.Kernel.norm_integralOperatorOnMeanZero_le
#check @DGRHS.Kernel.meanZero_kernel_resolvent_fullnorm_bounds
#print axioms DGRHS.Kernel.norm_integralOperatorOnMeanZero_le
#print axioms DGRHS.Kernel.meanZero_kernel_resolvent_fullnorm_bounds
