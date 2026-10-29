import DGRHS.Commutator.SourceC2PointwiseApproximation
import DGRHS.Commutator.SourceLogStaticGenerator

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Pointwise C2 approximation with ONE uniform derivative bound through order two
passes the actual canceled LOG drift, every fixed-law value integral and the
proper time integrals to the limit. This generalizes the eventual
neighbourhood-equality field of the compact-C2 cutoff drafts to pointwise
convergence of value, gradient and Laplacian, so that the same passage serves
the cutoff route (compact C2 -> bounded C2) and the mollifier route (compact
C-infinity -> compact C2).

The canceled kernel converges pointwise because it is an explicit continuous
function of the two gradient values off the diagonal and is zero on it; it is
dominated by the uniform Hessian bound. No continuity of the full LOG kernel on
the diagonal is used. No desired weak identity, density bound, moment, narrow
continuity, joint density measurability or uncanceled force integrability is a
premise. The quantitative section proves that the generator error is bounded,
uniformly in the probability law, by `(|β⁻¹|*d + 1/2)` times the uniform
Hessian difference. -/
noncomputable section
open MeasureTheory Laplacian Set Filter
open scoped Topology NNReal Interval RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

namespace SourceC2PointwiseApproximation

lemma log_kernel_bound {κ : Type*} [Fintype κ]
    {φ : EuclideanSpace ℝ κ → ℝ} (a : SourceC2PointwiseApproximation φ) (n : ℕ) (p : (EuclideanSpace ℝ κ) × (EuclideanSpace ℝ κ)) :
    |sourceLogTransportKernel 1 (gradient (a.test n)) p| ≤ a.bound := by
  let K : ℝ≥0 := ⟨a.bound, a.bound_nonneg⟩
  exact abs_sourceLogTransportKernel_one_le
    (sourceAdjoint_gradient_lipschitz_of_hessian_bound (a.test n) (a.smooth n) K
      (a.deriv_bound n 2 le_rfl)) p

lemma log_tendsto_kernel {κ : Type*} [Fintype κ]
    {φ : EuclideanSpace ℝ κ → ℝ} (a : SourceC2PointwiseApproximation φ) (p : (EuclideanSpace ℝ κ) × (EuclideanSpace ℝ κ)) :
    Tendsto (fun n => sourceLogTransportKernel 1 (gradient (a.test n)) p) atTop
      (𝓝 (sourceLogTransportKernel 1 (gradient φ) p)) := by
  simp only [sourceLogTransportKernel_one]
  have hc : Tendsto (fun _ : ℕ => p.1 - p.2) atTop (𝓝 (p.1 - p.2)) := tendsto_const_nhds
  exact ((hc.inner ((a.tendsto_gradient p.1).sub (a.tendsto_gradient p.2))).neg).div_const _

/-- Fixed-law value, Laplacian and canceled-pair limits, each with properness of
the limit integrand. -/
lemma log_spatial_limits {κ : Type*} [Fintype κ]
    {φ : EuclideanSpace ℝ κ → ℝ} (a : SourceC2PointwiseApproximation φ) (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] :
    (Integrable φ μ ∧
      Tendsto (fun n => ∫ x, a.test n x ∂μ) atTop (𝓝 (∫ x, φ x ∂μ))) ∧
    (Integrable (laplacian φ) μ ∧
      Tendsto (fun n => ∫ x, laplacian (a.test n) x ∂μ) atTop
        (𝓝 (∫ x, laplacian φ x ∂μ))) ∧
    (Integrable (sourceLogTransportKernel 1 (gradient φ)) (μ.prod μ) ∧
      Tendsto (fun n => ∫ p, sourceLogTransportKernel 1 (gradient (a.test n)) p ∂μ.prod μ)
        atTop (𝓝 (∫ p, sourceLogTransportKernel 1 (gradient φ) p ∂μ.prod μ))) := by
  have hi (n : ℕ) := (a.bounded_test n).log_spatial_properness (a.test n) μ
  refine ⟨?_, ?_, ?_⟩
  · exact sourcePointwise_integrable_tendsto_of_bounded μ (fun n x => a.test n x) φ a.bound
      (fun n => (hi n).1.aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (fun x => by
        simpa only [norm_iteratedFDeriv_zero] using a.deriv_bound n 0 (by omega) x))
      (Filter.Eventually.of_forall a.tendsto_value)
  · exact sourcePointwise_integrable_tendsto_of_bounded μ
      (fun n x => laplacian (a.test n) x) (laplacian φ) ((Fintype.card κ : ℝ) * a.bound)
      (fun n => (hi n).2.1.aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using a.laplacian_bound n x))
      (Filter.Eventually.of_forall a.tendsto_laplacian)
  · exact sourcePointwise_integrable_tendsto_of_bounded (μ.prod μ)
      (fun n p => sourceLogTransportKernel 1 (gradient (a.test n)) p)
      (sourceLogTransportKernel 1 (gradient φ)) a.bound
      (fun n => (hi n).2.2.aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (fun p => by
        simpa only [Real.norm_eq_abs] using a.log_kernel_bound n p))
      (Filter.Eventually.of_forall a.log_tendsto_kernel)

/-- The actual drift of every approximant is bounded uniformly in the index and
in the probability law, with the source `β⁻¹` diffusion and half pair factor. -/
lemma log_drift_bound {κ : Type*} [Fintype κ]
    {φ : EuclideanSpace ℝ κ → ℝ} (a : SourceC2PointwiseApproximation φ) (β : ℝ) (ρ : (EuclideanSpace ℝ κ) → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (n : ℕ) :
    |sourceLogStaticMeanTestDrift β ρ (a.test n)| ≤
      |β⁻¹| * ((Fintype.card κ : ℝ) * a.bound) + (1/2 : ℝ) * a.bound := by
  have hL : |∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ| ≤
      (Fintype.card κ : ℝ) * a.bound := by
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
          simpa only [Real.norm_eq_abs] using a.log_kernel_bound n p))
  unfold sourceLogStaticMeanTestDrift
  calc
    _ ≤ |β⁻¹ * (∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ)| +
        |(1/2 : ℝ) * (∫ p, sourceLogTransportKernel 1 (gradient (a.test n)) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))| :=
      abs_sub _ _
    _ = |β⁻¹| * |∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ| +
        (1/2 : ℝ) * |∫ p, sourceLogTransportKernel 1 (gradient (a.test n)) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)| := by
      rw [abs_mul, abs_mul]; norm_num
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hL (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hK (by norm_num))

lemma log_drift_tendsto {κ : Type*} [Fintype κ]
    {φ : EuclideanSpace ℝ κ → ℝ} (a : SourceC2PointwiseApproximation φ) (β : ℝ) (ρ : (EuclideanSpace ℝ κ) → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Tendsto (fun n => sourceLogStaticMeanTestDrift β ρ (a.test n)) atTop
      (𝓝 (sourceLogStaticMeanTestDrift β ρ φ)) := by
  obtain ⟨_, ⟨_, hL⟩, ⟨_, hK⟩⟩ := a.log_spatial_limits (gaussianRieszDensityMeasure ρ)
  exact (tendsto_const_nhds.mul hL).sub (tendsto_const_nhds.mul hK)

/-- Proper time dominated convergence on each `[0,r] ⊆ [0,T]`. Time
measurability of the limit is derived from the approximants. -/
lemma log_time_limit {κ : Type*} [Fintype κ]
    {φ : EuclideanSpace ℝ κ → ℝ} (a : SourceC2PointwiseApproximation φ) (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → (EuclideanSpace ℝ κ) → ℝ)
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t)))
    (hi : ∀ n, IntervalIntegrable
      (fun t => sourceLogStaticMeanTestDrift β (ρ t) (a.test n)) volume 0 T)
    (r : ℝ) (hr : r ∈ Icc 0 T) :
    IntervalIntegrable (fun t => sourceLogStaticMeanTestDrift β (ρ t) φ) volume 0 r ∧
    Tendsto (fun n => ∫ t in 0..r, sourceLogStaticMeanTestDrift β (ρ t) (a.test n))
      atTop (𝓝 (∫ t in 0..r, sourceLogStaticMeanTestDrift β (ρ t) φ)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 r)
  have hsub : Ioc 0 r ⊆ Ioc 0 T := fun t ht => ⟨ht.1, ht.2.trans hr.2⟩
  have him (n : ℕ) : AEStronglyMeasurable
      (fun t => sourceLogStaticMeanTestDrift β (ρ t) (a.test n)) μ :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hi n)).mono_set hsub).1
  have hb (n : ℕ) : ∀ᵐ t ∂μ,
      ‖sourceLogStaticMeanTestDrift β (ρ t) (a.test n)‖ ≤
        |β⁻¹| * ((Fintype.card κ : ℝ) * a.bound) + (1/2 : ℝ) * a.bound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    letI := hprob t ⟨ht.1.le, ht.2.trans hr.2⟩
    simpa only [Real.norm_eq_abs] using a.log_drift_bound β (ρ t) n
  have hl : ∀ᵐ t ∂μ,
      Tendsto (fun n => sourceLogStaticMeanTestDrift β (ρ t) (a.test n))
        atTop (𝓝 (sourceLogStaticMeanTestDrift β (ρ t) φ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    letI := hprob t ⟨ht.1.le, ht.2.trans hr.2⟩
    exact a.log_drift_tendsto β (ρ t)
  obtain ⟨hproper, hlim⟩ := sourcePointwise_integrable_tendsto_of_bounded μ
    (fun n t => sourceLogStaticMeanTestDrift β (ρ t) (a.test n))
    (fun t => sourceLogStaticMeanTestDrift β (ρ t) φ) _ him hb hl
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1).mpr hproper, ?_⟩
  simpa only [intervalIntegral.integral_of_le hr.1] using hlim

/-- The every-time integrated identity passes from the approximants to the
limit test. This is the only place where the weak identity enters, and it is
the identity of the APPROXIMANTS, never of the target. -/
theorem log_integrated_identity {κ : Type*} [Fintype κ]
    {φ : EuclideanSpace ℝ κ → ℝ} (a : SourceC2PointwiseApproximation φ) (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → (EuclideanSpace ℝ κ) → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hi : ∀ n, IntervalIntegrable
      (fun r => sourceLogStaticMeanTestDrift β (ρ r) (a.test n)) volume 0 T)
    (he : ∀ n, ∀ r ∈ Icc 0 T,
      (∫ x, a.test n x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, a.test n x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceLogStaticMeanTestDrift β (ρ u) (a.test n)) :
    IntervalIntegrable (fun r => sourceLogStaticMeanTestDrift β (ρ r) φ) volume 0 T ∧
    ∀ r ∈ Icc 0 T,
      (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceLogStaticMeanTestDrift β (ρ u) φ := by
  have ht := a.log_time_limit β T hT ρ hprob hi
  refine ⟨(ht T ⟨hT, le_rfl⟩).1, ?_⟩
  intro r hr
  letI := hprob r hr
  letI := hprob 0 ⟨le_rfl, hT⟩
  have hleft := (a.log_spatial_limits (gaussianRieszDensityMeasure (ρ r))).1.2
  have hright := ((a.log_spatial_limits (gaussianRieszDensityMeasure (ρ 0))).1.2).add
    (ht r hr).2
  have hright' : Tendsto (fun n => ∫ x, a.test n x ∂gaussianRieszDensityMeasure (ρ r))
      atTop (𝓝 ((∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) +
        ∫ u in 0..r, sourceLogStaticMeanTestDrift β (ρ u) φ)) :=
    hright.congr (fun n => ((he n) r hr).symm)
  exact tendsto_nhds_unique hleft hright'

end SourceC2PointwiseApproximation

/-! ## Quantitative generator stability under a uniform Hessian difference -/

/-- The canceled kernel is linear in the frozen velocity field. -/
lemma sourceLogTransportKernel_one_sub (v w : E → E) (p : E × E) :
    sourceLogTransportKernel 1 v p - sourceLogTransportKernel 1 w p =
      sourceLogTransportKernel 1 (fun z => v z - w z) p := by
  simp only [sourceLogTransportKernel_one]
  have he : v p.1 - v p.2 - (w p.1 - w p.2) = (v p.1 - w p.1) - (v p.2 - w p.2) := by abel
  rw [← he]
  simp only [inner_sub_right]
  ring

/-- Gradient of a difference of differentiable functions. -/
lemma source_gradient_sub (φ ψ : E → ℝ) (x : E)
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    gradient (fun y => φ y - ψ y) x = gradient φ x - gradient ψ x := by
  simp only [gradient, fderiv_fun_sub hφ hψ, map_sub]

/-- For two bounded C2 tests with uniform Hessian difference `δ`, the actual
drifts differ by at most `(|β⁻¹|*d + 1/2)*δ`, uniformly in the probability law. -/
theorem sourceLogStaticMeanTestDrift_sub_le
    (β : ℝ) (ρ : E → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (φ ψ : E → ℝ) (hφ : SourceBoundedC2Test φ) (hψ : SourceBoundedC2Test ψ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 φ x - iteratedFDeriv ℝ 2 ψ x‖ ≤ δ) :
    |sourceLogStaticMeanTestDrift β ρ φ - sourceLogStaticMeanTestDrift β ρ ψ| ≤
      (|β⁻¹| * (Fintype.card ι : ℝ) + 1/2) * δ := by
  set μ := gaussianRieszDensityMeasure ρ with hμ
  have pφ := hφ.log_spatial_properness φ μ
  have pψ := hψ.log_spatial_properness ψ μ
  let q : E → ℝ := fun y => φ y - ψ y
  have hq : ContDiff ℝ 2 q := hφ.1.sub hψ.1
  have hqH (x : E) : ‖iteratedFDeriv ℝ 2 q x‖ ≤ δ := by
    have he : iteratedFDeriv ℝ 2 q x = iteratedFDeriv ℝ 2 φ x - iteratedFDeriv ℝ 2 ψ x :=
      iteratedFDeriv_sub_apply hφ.1.contDiffAt hψ.1.contDiffAt
    rw [he]; exact hH x
  -- Laplacian difference
  have hlap (x : E) : laplacian φ x - laplacian ψ x = laplacian q x :=
    (hφ.1.contDiffAt.laplacian_sub hψ.1.contDiffAt).symm
  have hLq (x : E) : |laplacian q x| ≤ (Fintype.card ι : ℝ) * δ :=
    source_laplacian_bound_of_hessian (EuclideanSpace.basisFun ι ℝ) q δ hqH x
  have hIL : |(∫ x, laplacian φ x ∂μ) - ∫ x, laplacian ψ x ∂μ| ≤
      (Fintype.card ι : ℝ) * δ := by
    rw [← integral_sub pφ.2.1 pψ.2.1]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => laplacian φ x - laplacian ψ x)
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, hlap x]; exact hLq x))
    simpa [Real.norm_eq_abs] using h
  -- Kernel difference
  let K : ℝ≥0 := ⟨δ, hδ⟩
  have hv : LipschitzWith K (gradient q) :=
    sourceAdjoint_gradient_lipschitz_of_hessian_bound q hq K hqH
  have hgq (z : E) : gradient q z = gradient φ z - gradient ψ z :=
    source_gradient_sub φ ψ z (hφ.1.differentiable (by norm_num) z)
      (hψ.1.differentiable (by norm_num) z)
  have hker (p : E × E) :
      sourceLogTransportKernel 1 (gradient φ) p - sourceLogTransportKernel 1 (gradient ψ) p =
        sourceLogTransportKernel 1 (gradient q) p := by
    have hgq' : gradient q = fun z => gradient φ z - gradient ψ z := funext hgq
    rw [sourceLogTransportKernel_one_sub, hgq']
  have hIK : |(∫ p, sourceLogTransportKernel 1 (gradient φ) p ∂μ.prod μ) -
      ∫ p, sourceLogTransportKernel 1 (gradient ψ) p ∂μ.prod μ| ≤ δ := by
    rw [← integral_sub pφ.2.2 pψ.2.2]
    have h := norm_integral_le_of_norm_le_const (μ := μ.prod μ) (C := δ)
      (f := fun p => sourceLogTransportKernel 1 (gradient φ) p -
        sourceLogTransportKernel 1 (gradient ψ) p)
      (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, hker p]; exact abs_sourceLogTransportKernel_one_le hv p))
    simpa [Real.norm_eq_abs] using h
  unfold sourceLogStaticMeanTestDrift
  rw [← hμ]
  have hsplit :
      β⁻¹ * (∫ x, laplacian φ x ∂μ) - (1/2 : ℝ) * (∫ p, sourceLogTransportKernel 1
          (gradient φ) p ∂μ.prod μ) -
        (β⁻¹ * (∫ x, laplacian ψ x ∂μ) - (1/2 : ℝ) * (∫ p, sourceLogTransportKernel 1
          (gradient ψ) p ∂μ.prod μ)) =
      β⁻¹ * ((∫ x, laplacian φ x ∂μ) - ∫ x, laplacian ψ x ∂μ) -
        (1/2 : ℝ) * ((∫ p, sourceLogTransportKernel 1 (gradient φ) p ∂μ.prod μ) -
          ∫ p, sourceLogTransportKernel 1 (gradient ψ) p ∂μ.prod μ) := by ring
  rw [hsplit]
  calc
    _ ≤ |β⁻¹ * ((∫ x, laplacian φ x ∂μ) - ∫ x, laplacian ψ x ∂μ)| +
        |(1/2 : ℝ) * ((∫ p, sourceLogTransportKernel 1 (gradient φ) p ∂μ.prod μ) -
          ∫ p, sourceLogTransportKernel 1 (gradient ψ) p ∂μ.prod μ)| := abs_sub _ _
    _ = |β⁻¹| * |(∫ x, laplacian φ x ∂μ) - ∫ x, laplacian ψ x ∂μ| +
        (1/2 : ℝ) * |(∫ p, sourceLogTransportKernel 1 (gradient φ) p ∂μ.prod μ) -
          ∫ p, sourceLogTransportKernel 1 (gradient ψ) p ∂μ.prod μ| := by
      rw [abs_mul, abs_mul]; norm_num
    _ ≤ |β⁻¹| * ((Fintype.card ι : ℝ) * δ) + (1/2 : ℝ) * δ :=
      add_le_add (mul_le_mul_of_nonneg_left hIL (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hIK (by norm_num))
    _ = _ := by ring

end DGRHS.Commutator
