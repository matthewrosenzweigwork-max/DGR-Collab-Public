/- Supporting draft: actual Gram kernel and its factorization through the
feature readout and its adjoint. Not Lean checked. FeatureSynthesis is the
worker-owned prerequisite; no factorization or positivity field is assumed. -/
import DGRHS.Gaussian.FeatureSynthesis
import DGRHS.Kernel.SpectralBounds
open MeasureTheory
open scoped InnerProductSpace ENNReal
namespace DGRHS.Gaussian
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
noncomputable def featureKernel (k : X → H) : X × X → ℝ :=
  fun p ↦ inner ℝ (k p.1) (k p.2)

lemma memLp_featureKernel (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) : MemLp (featureKernel k) 2 (μ.prod μ) := by
  have hf : StronglyMeasurable (fun p : X × X ↦ k p.1) := hk.comp_measurable measurable_fst
  have hg : StronglyMeasurable (fun p : X × X ↦ k p.2) := hk.comp_measurable measurable_snd
  apply (DGRHS.Kernel.memLp_separated_mul μ hk2.norm hk2.norm).of_le
    (hf.inner hg).aestronglyMeasurable
  filter_upwards [] with p
  change ‖inner ℝ (k p.1) (k p.2)‖ ≤ ‖‖k p.1‖ * ‖k p.2‖‖
  simpa only [norm_mul, norm_norm] using norm_inner_le_norm (𝕜 := ℝ) (k p.1) (k p.2)

lemma featureKernel_symmetric (k : X → H) (p : X × X) :
    featureKernel k p.swap = featureKernel k p := real_inner_comm _ _

lemma integral_featureKernel_right (k : X → H) (hk2 : MemLp k 2 μ)
    (hmean : (∫ y, k y ∂μ) = 0) (x : X) :
    (∫ y, featureKernel k (x,y) ∂μ) = 0 := by
  have hi : Integrable k μ := hk2.integrable (by norm_num)
  change (∫ y, inner ℝ (k x) (k y) ∂μ) = 0
  rw [integral_inner hi, hmean, inner_zero_right]

/-- Actual kernel operator T=B B†, established by its integral action. -/
theorem integralOperator_featureKernel_eq (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) :
    DGRHS.Kernel.integralOperator (featureKernel k) (memLp_featureKernel k hk hk2) =
      (featureReadout k hk2).comp (featureSynthesis k hk2) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [DGRHS.Kernel.integralOperator_apply_ae (featureKernel k)
    (memLp_featureKernel k hk hk2) f,
    coeFn_featureReadout k hk2 (featureSynthesis k hk2 f)] with x hT hB
  change _ = featureReadout k hk2 (featureSynthesis k hk2 f) x
  rw [hT, hB, featureSynthesis_eq_integral k hk2 f]
  rw [← integral_inner (integrable_featureSynthesis_integrand k hk2 f)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [featureKernel, inner_smul_right]
  ring

/-- Positivity is a consequence of the actual Gram representation. -/
theorem integralOperator_featureKernel_nonneg (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (f : Lp ℝ 2 μ) :
    0 ≤ inner ℝ (DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2) f) f := by
  rw [integralOperator_featureKernel_eq k hk hk2]
  change 0 ≤ inner ℝ (featureReadout k hk2 ((featureReadout k hk2).adjoint f)) f
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_self_eq_norm_sq]
  positivity

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.memLp_featureKernel
#print axioms DGRHS.Gaussian.integralOperator_featureKernel_eq
#print axioms DGRHS.Gaussian.integralOperator_featureKernel_nonneg
