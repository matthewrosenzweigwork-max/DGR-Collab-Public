import DGRHS.Gaussian.GaussianScaleMixtureFeature
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Continuity and separability of the constructed scale-mixture Fourier
Hilbert feature. Continuity uses a fixed bound in the actual finite scale
measure and the proved Gram identity, not an assumed covariance or limit. -/
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped BigOperators Topology ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma continuous_gaussianScaleMixtureFeature (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Continuous (gaussianScaleMixtureFeature (ι := ι) ν) := by
  classical
  apply continuous_iff_continuousAt.2
  intro a₀
  let J (a : ι → ℝ) := ∫ t, Real.exp (-(∑ i, (a₀ i - a i) ^ 2) / (2 * t ^ 2)) ∂ν
  let m := (ν Set.univ).toReal
  have hJ : Tendsto J (𝓝 a₀) (𝓝 m) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := ν)
      (F := fun a : ι → ℝ => fun t : ℝ =>
        Real.exp (-(∑ i, (a₀ i - a i) ^ 2) / (2 * t ^ 2)))
      (f := fun _ : ℝ => (1 : ℝ)) (fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall (fun a => by
        have hm : Measurable (fun t : ℝ =>
          Real.exp (-(∑ i, (a₀ i - a i) ^ 2) / (2 * t ^ 2))) := by fun_prop
        exact hm.aestronglyMeasurable))
      (Filter.Eventually.of_forall (fun a => Filter.Eventually.of_forall (fun t => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        apply Real.exp_le_one_iff.2
        exact div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (Finset.sum_nonneg (fun i hi => sq_nonneg _))) (by positivity))))
      (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall (fun t => by
        have hcont : Continuous (fun a : ι → ℝ =>
          Real.exp (-(∑ i, (a₀ i - a i) ^ 2) / (2 * t ^ 2))) := by fun_prop
        simpa using hcont.tendsto a₀))
    simpa [J, m, Measure.real] using ht
  have hs : Tendsto (fun a : ι → ℝ =>
      ‖gaussianScaleMixtureFeature ν a - gaussianScaleMixtureFeature ν a₀‖ ^ 2)
      (𝓝 a₀) (𝓝 0) := by
    have ht : Tendsto (fun a => m - 2 * J a + m) (𝓝 a₀) (𝓝 (m - 2 * m + m)) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hJ)).add tendsto_const_nhds
    have he : (fun a : ι → ℝ =>
        ‖gaussianScaleMixtureFeature ν a - gaussianScaleMixtureFeature ν a₀‖ ^ 2) =
        fun a => m - 2 * J a + m := by
      funext a
      rw [norm_sub_sq_real, norm_sq_gaussianScaleMixtureFeature,
        norm_sq_gaussianScaleMixtureFeature, inner_gaussianScaleMixtureFeature]
    rw [he]
    convert ht using 1 <;> ring
  change Tendsto (gaussianScaleMixtureFeature ν) (𝓝 a₀)
    (𝓝 (gaussianScaleMixtureFeature ν a₀))
  rw [tendsto_iff_dist_tendsto_zero]
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa [Function.comp_def, dist_eq_norm, Real.sqrt_sq_eq_abs] using ht

lemma stronglyMeasurable_gaussianScaleMixtureFeature (ν : Measure ℝ) [IsFiniteMeasure ν] :
    StronglyMeasurable (gaussianScaleMixtureFeature (ι := ι) ν) :=
  (continuous_gaussianScaleMixtureFeature ν).stronglyMeasurable

lemma separableSpace_gaussianScaleMixtureHilbert (ν : Measure ℝ) [IsFiniteMeasure ν] :
    SeparableSpace (Lp ℂ 2 (ν.prod (finiteStandardGaussian ι))) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℂ 2 (ν.prod (finiteStandardGaussian ι))) := inferInstance
  infer_instance

end DGRHS.Gaussian
#check DGRHS.Gaussian.continuous_gaussianScaleMixtureFeature
#check DGRHS.Gaussian.stronglyMeasurable_gaussianScaleMixtureFeature
#check DGRHS.Gaussian.separableSpace_gaussianScaleMixtureHilbert
#print axioms DGRHS.Gaussian.continuous_gaussianScaleMixtureFeature
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianScaleMixtureFeature
#print axioms DGRHS.Gaussian.separableSpace_gaussianScaleMixtureHilbert
