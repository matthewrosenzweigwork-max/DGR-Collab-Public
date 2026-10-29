import DGRHS.Gaussian.FiniteLaplace
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
Explicit finite feature evaluation. Finite sums give a jointly measurable honest
representative and exact pointwise centering in x. This does not address the
countable-series representative or an infinite-dimensional Hilbert-valued Gaussian.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DGRHS.Gaussian

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

noncomputable def finiteFeatureEvaluation (k : X → ι → ℝ) (x : X) (z : ι → ℝ) : ℝ :=
  ∑ i, k x i * z i

/-- Joint measurability in the feature variable and the actual Gaussian sample. -/
theorem measurable_finiteFeatureEvaluation {k : X → ι → ℝ} (hk : Measurable k) :
    Measurable (fun p : X × (ι → ℝ) => finiteFeatureEvaluation k p.1 p.2) := by
  classical
  unfold finiteFeatureEvaluation
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp (hk.comp measurable_fst)).mul
    ((measurable_pi_apply i).comp measurable_snd)

theorem integrable_finiteFeatureEvaluation_in_feature
    (μ : Measure X) (k : X → ι → ℝ) (hk : ∀ i, Integrable (fun x => k x i) μ)
    (z : ι → ℝ) : Integrable (fun x => finiteFeatureEvaluation k x z) μ := by
  classical
  exact integrable_finsetSum _ (fun i _ => (hk i).mul_const (z i))

/-- Centering is pointwise for every finite Gaussian sample, stronger than a.s. -/
theorem integral_finiteFeatureEvaluation_eq_zero
    (μ : Measure X) (k : X → ι → ℝ) (hk : ∀ i, Integrable (fun x => k x i) μ)
    (hmean : ∀ i, ∫ x, k x i ∂μ = 0) (z : ι → ℝ) :
    ∫ x, finiteFeatureEvaluation k x z ∂μ = 0 := by
  classical
  unfold finiteFeatureEvaluation
  rw [integral_finsetSum _ (fun i _ => (hk i).mul_const (z i))]
  simp_rw [integral_mul_const, hmean, zero_mul]
  simp

/-- Every fixed finite feature readout has an actual Gaussian law. -/
theorem hasGaussianLaw_finiteFeatureEvaluation (k : X → ι → ℝ) (x : X) :
    HasGaussianLaw (finiteFeatureEvaluation k x) (finiteStandardGaussian ι) := by
  classical
  have hcoord : ∀ i : ι,
      HasGaussianLaw (fun z : ι → ℝ => z i) (finiteStandardGaussian ι) := by
    intro i
    letI : IsGaussian ((finiteStandardGaussian ι).map (fun z => z i)) := by
      rw [finiteStandardGaussian, (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq]
      infer_instance
    exact IsGaussian.hasGaussianLaw (measurable_pi_apply i).aemeasurable
  have hGauss : ∀ i : ι,
      HasGaussianLaw (fun z : ι → ℝ => k x i * z i) (finiteStandardGaussian ι) := by
    intro i
    simpa only [smul_eq_mul] using (hcoord i).fun_smul (k x i)
  have hIndep : iIndepFun (fun i (z : ι → ℝ) => k x i * z i)
      (finiteStandardGaussian ι) := by
    exact iIndepFun_pi (X := fun i (t : ℝ) => k x i * t) (fun i => by fun_prop)
  exact hIndep.hasGaussianLaw_fun_sum hGauss

/-- Exact diagonal variance in finite feature coordinates. -/
theorem variance_finiteFeatureEvaluation (k : X → ι → ℝ) (x : X) :
    Var[finiteFeatureEvaluation k x; finiteStandardGaussian ι] = ∑ i, (k x i) ^ 2 := by
  classical
  have heq : finiteFeatureEvaluation k x = ∑ i, fun z : ι → ℝ => k x i * z i := by
    funext z
    simp only [finiteFeatureEvaluation, Finset.sum_apply]
  rw [heq, finiteStandardGaussian]
  have hv := variance_sum_pi (X := fun i (t : ℝ) => k x i * t) (fun i =>
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).const_mul (k x i))
  have hi : ∀ i : ι, Var[fun t : ℝ => k x i * t; gaussianReal 0 1] = (k x i) ^ 2 := by
    intro i
    rw [variance_const_mul (k x i) (fun t : ℝ => t) (gaussianReal 0 1),
      variance_fun_id_gaussianReal]
    norm_num
  simpa only [hi] using hv

/-- Integrability under the actual finite Gaussian product law. -/
theorem integrable_finiteFeatureEvaluation (k : X → ι → ℝ) (x : X) :
    Integrable (finiteFeatureEvaluation k x) (finiteStandardGaussian ι) :=
  (hasGaussianLaw_finiteFeatureEvaluation k x).integrable

/-- The Gaussian-sample mean is zero for every fixed feature point. -/
theorem integral_finiteFeatureEvaluation_eq_zero_gaussian (k : X → ι → ℝ) (x : X) :
    ∫ z, finiteFeatureEvaluation k x z ∂finiteStandardGaussian ι = 0 := by
  classical
  have hcoord : ∀ i : ι, Integrable (fun z : ι → ℝ => z i) (finiteStandardGaussian ι) := by
    intro i
    exact ((memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)).integrable (by norm_num)
  have hmean : ∀ i : ι, ∫ z : ι → ℝ, z i ∂finiteStandardGaussian ι = 0 := by
    intro i
    have hmap : (finiteStandardGaussian ι).map (fun z : ι → ℝ => z i) =
        gaussianReal 0 1 :=
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq
    have hi := integral_map (measurable_pi_apply i).aemeasurable aestronglyMeasurable_id
      (μ := finiteStandardGaussian ι)
    rw [hmap] at hi
    change (∫ t : ℝ, t ∂gaussianReal 0 1) = (∫ z : ι → ℝ, z i ∂finiteStandardGaussian ι) at hi
    rw [← hi]
    simp [integral_id_gaussianReal]
  unfold finiteFeatureEvaluation
  rw [integral_finsetSum _ (fun i _ => (hcoord i).const_mul (k x i))]
  simp_rw [integral_const_mul, hmean, mul_zero]
  simp

/-- Exact pushforward, including the centering and variance normalization. -/
theorem map_finiteFeatureEvaluation_eq_gaussianReal (k : X → ι → ℝ) (x : X) :
    (finiteStandardGaussian ι).map (finiteFeatureEvaluation k x) =
      gaussianReal 0 (Real.toNNReal (∑ i, (k x i) ^ 2)) := by
  rw [(hasGaussianLaw_finiteFeatureEvaluation k x).map_eq_gaussianReal,
    integral_finiteFeatureEvaluation_eq_zero_gaussian, variance_finiteFeatureEvaluation]

end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.measurable_finiteFeatureEvaluation
#print axioms DGRHS.Gaussian.integrable_finiteFeatureEvaluation_in_feature
#print axioms DGRHS.Gaussian.integral_finiteFeatureEvaluation_eq_zero
#print axioms DGRHS.Gaussian.hasGaussianLaw_finiteFeatureEvaluation

#print axioms DGRHS.Gaussian.variance_finiteFeatureEvaluation

#print axioms DGRHS.Gaussian.integrable_finiteFeatureEvaluation
#print axioms DGRHS.Gaussian.integral_finiteFeatureEvaluation_eq_zero_gaussian
#print axioms DGRHS.Gaussian.map_finiteFeatureEvaluation_eq_gaussianReal

#check DGRHS.Gaussian.finiteFeatureEvaluation
#check DGRHS.Gaussian.measurable_finiteFeatureEvaluation
#check DGRHS.Gaussian.integrable_finiteFeatureEvaluation_in_feature
#check DGRHS.Gaussian.integral_finiteFeatureEvaluation_eq_zero
#check DGRHS.Gaussian.hasGaussianLaw_finiteFeatureEvaluation
#check DGRHS.Gaussian.variance_finiteFeatureEvaluation
#check DGRHS.Gaussian.integrable_finiteFeatureEvaluation
#check DGRHS.Gaussian.integral_finiteFeatureEvaluation_eq_zero_gaussian
#check DGRHS.Gaussian.map_finiteFeatureEvaluation_eq_gaussianReal
