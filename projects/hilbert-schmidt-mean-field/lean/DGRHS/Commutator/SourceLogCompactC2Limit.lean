import DGRHS.Commutator.SourceLogCompactC2Cutoff
import DGRHS.Commutator.SourceLogStaticGenerator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! RECORDS-ONLY / UNCOMPILED. Spatial and time dominated-convergence
lemmas, with properness retained. All drifts below are the existing actual
canceled LOG drift. No desired weak identity is assumed here. -/
noncomputable section
open MeasureTheory Laplacian Set Filter
open scoped Topology NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Properness of the limit is proved as well as convergence of integrals. -/
lemma sourceLog_integrable_tendsto_of_bounded
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F : ℕ → X → ℝ) (f : X → ℝ) (C : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Integrable f μ ∧
      Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hF hl
  have hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
    filter_upwards [hl, ae_all_iff.2 hb] with x hx hbx
    exact le_of_tendsto hx.norm (Filter.Eventually.of_forall hbx)
  exact ⟨(integrable_const C).mono' hm hfb,
    tendsto_integral_of_dominated_convergence (fun _ => C) hF
      (integrable_const C) hb hl⟩

lemma SourceLogCompactC2Approximation.bounded_test
    {φ : E → ℝ} (a : SourceLogCompactC2Approximation φ) (n : ℕ) :
    SourceBoundedC2Test (a.test n) :=
  ⟨a.smooth n,a.bound,a.bound_nonneg,a.deriv_bound n⟩

lemma SourceLogCompactC2Approximation.laplacian_bound
    {φ : E → ℝ} (a : SourceLogCompactC2Approximation φ) (n : ℕ) (x : E) :
    |laplacian (a.test n) x| ≤ (Fintype.card ι : ℝ)*a.bound :=
  source_laplacian_bound_of_hessian (EuclideanSpace.basisFun ι ℝ) _ _
    (a.deriv_bound n 2 le_rfl) x

lemma SourceLogCompactC2Approximation.kernel_bound
    {φ : E → ℝ} (a : SourceLogCompactC2Approximation φ) (n : ℕ) (p : E×E) :
    |sourceLogTransportKernel 1 (gradient (a.test n)) p| ≤ a.bound := by
  let K : ℝ≥0 := ⟨a.bound,a.bound_nonneg⟩
  exact abs_sourceLogTransportKernel_one_le
    (sourceAdjoint_gradient_lipschitz_of_hessian_bound (a.test n) (a.smooth n) K
      (a.deriv_bound n 2 le_rfl)) p

lemma SourceLogCompactC2Approximation.spatial_limits
    {φ : E → ℝ} (a : SourceLogCompactC2Approximation φ)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    Tendsto (fun n => ∫ x, a.test n x ∂μ) atTop (𝓝 (∫ x, φ x ∂μ)) ∧
    Tendsto (fun n => ∫ x, laplacian (a.test n) x ∂μ) atTop
      (𝓝 (∫ x, laplacian φ x ∂μ)) ∧
    Tendsto (fun n => ∫ p, sourceLogTransportKernel 1 (gradient (a.test n)) p ∂μ.prod μ)
      atTop (𝓝 (∫ p, sourceLogTransportKernel 1 (gradient φ) p ∂μ.prod μ)) := by
  have hi n := (a.bounded_test n).log_spatial_properness (a.test n) μ
  have hv : ∀ x, Tendsto (fun n => a.test n x) atTop (𝓝 (φ x)) := by
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [a.local_eq x] with n hn
    exact hn.eq_of_nhds.symm
  have hL : ∀ x, Tendsto (fun n => laplacian (a.test n) x) atTop
      (𝓝 (laplacian φ x)) := by
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [a.local_eq x] with n hn
    exact (InnerProductSpace.laplacian_congr_nhds hn).eq_of_nhds.symm
  have hK : ∀ p : E×E,
      Tendsto (fun n => sourceLogTransportKernel 1 (gradient (a.test n)) p)
        atTop (𝓝 (sourceLogTransportKernel 1 (gradient φ) p)) := by
    intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [a.local_eq p.1,a.local_eq p.2] with n h1 h2
    rw [sourceLogTransportKernel_one,sourceLogTransportKernel_one,
      h1.gradient_eq,h2.gradient_eq]
  refine ⟨?_,?_,?_⟩
  · apply tendsto_integral_of_dominated_convergence (fun _ => a.bound)
      (fun n => (hi n).1.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [norm_iteratedFDeriv_zero] using a.deriv_bound n 0 (by omega) x)
    · exact Filter.Eventually.of_forall hv
  · apply tendsto_integral_of_dominated_convergence
      (fun _ => (Fintype.card ι : ℝ)*a.bound)
      (fun n => (hi n).2.1.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using a.laplacian_bound n x)
    · exact Filter.Eventually.of_forall hL
  · apply tendsto_integral_of_dominated_convergence (fun _ => a.bound)
      (fun n => (hi n).2.2.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact Filter.Eventually.of_forall (fun p => by
        simpa only [Real.norm_eq_abs] using a.kernel_bound n p)
    · exact Filter.Eventually.of_forall hK

lemma SourceLogCompactC2Approximation.drift_bound
    {φ : E → ℝ} (a : SourceLogCompactC2Approximation φ)
    (β : ℝ) (ρ : E → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (n : ℕ) :
    |sourceLogStaticMeanTestDrift β ρ (a.test n)| ≤
      |β⁻¹| * ((Fintype.card ι : ℝ)*a.bound)+(1/2:ℝ)*a.bound := by
  have hL : |∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ| ≤
      (Fintype.card ι : ℝ)*a.bound := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := gaussianRieszDensityMeasure ρ) (f := laplacian (a.test n))
        (Filter.Eventually.of_forall (fun x => by
          simpa only [Real.norm_eq_abs] using a.laplacian_bound n x))
  have hK : |∫ p, sourceLogTransportKernel 1 (gradient (a.test n)) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)| ≤ a.bound := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := (gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))
        (f := sourceLogTransportKernel 1 (gradient (a.test n)))
        (Filter.Eventually.of_forall (fun p => by
          simpa only [Real.norm_eq_abs] using a.kernel_bound n p))
  unfold sourceLogStaticMeanTestDrift
  calc
    _ ≤ |β⁻¹ * (∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ)| +
        |(1/2:ℝ) * (∫ p, sourceLogTransportKernel 1 (gradient (a.test n)) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))| :=
      abs_sub _ _
    _ = |β⁻¹| * |∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ| +
        (1/2:ℝ) * |∫ p, sourceLogTransportKernel 1 (gradient (a.test n)) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)| := by
      rw [abs_mul,abs_mul]; norm_num
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hL (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hK (by norm_num))

lemma SourceLogCompactC2Approximation.drift_tendsto
    {φ : E → ℝ} (a : SourceLogCompactC2Approximation φ)
    (β : ℝ) (ρ : E → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Tendsto (fun n => sourceLogStaticMeanTestDrift β ρ (a.test n)) atTop
      (𝓝 (sourceLogStaticMeanTestDrift β ρ φ)) := by
  obtain ⟨_,hL,hK⟩ := a.spatial_limits (gaussianRieszDensityMeasure ρ)
  exact (tendsto_const_nhds.mul hL).sub (tendsto_const_nhds.mul hK)

end DGRHS.Commutator
