import DGRHS.Commutator.SourceC2PointwiseApproximation
import DGRHS.Commutator.SourceRieszStaticWeakForm
import DGRHS.Commutator.SourceRieszLocalEnergy
import DGRHS.Commutator.SourceRieszForceSymmetry
import DGRHS.Dynamics.SourceAdjointHessianLipschitz

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Positive-Riesz analogue of `SourceLogC2PointwiseLimit`. The canceled Riesz
kernel is no longer bounded: the checked local bound gives
`|K_v(x,y)| ≤ A_s * Lip(v) * |x-y|^{-s}/s`, and `|x-y|^{-s}/s` is square
integrable (hence integrable) for the product of probability laws with density
at most `M` when `0 < s` and `2s < d` (checked
`memLp_gaussianRieszPhysicalPair`). This SINGULAR LOCAL DOMINATION, uniform in
the approximation index through the uniform Hessian bound, replaces the bounded
domination of the LOG proof; the LOG cancellation argument is not reused for
Riesz and no `s = 0` specialization occurs. The density cap is the source
uniform background control (source 878) and is required at every time used.

Pointwise convergence of the canceled kernel uses the checked force form
`K_v(x,y) = ⟪∇g_s(x-y), v x - v y⟫`. -/
noncomputable section
open MeasureTheory Laplacian Set Filter
open scoped Topology NNReal Interval RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

namespace SourceC2PointwiseApproximation

lemma riesz_lipschitz {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (n : ℕ) :
    LipschitzWith ⟨a.bound, a.bound_nonneg⟩ (gradient (a.test n)) :=
  sourceAdjoint_gradient_lipschitz_of_hessian_bound (a.test n) (a.smooth n)
    ⟨a.bound, a.bound_nonneg⟩ (a.deriv_bound n 2 le_rfl)

/-- Uniform singular local domination of the approximant kernels. -/
lemma riesz_kernel_bound {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (s : ℝ) (hs : 0 < s) (n : ℕ) (p : (EuclideanSpace ℝ κ) × (EuclideanSpace ℝ κ)) :
    |sourceRieszTransportKernel 1 s (gradient (a.test n)) p| ≤
      sourceRieszLocalProfileConstant (ι := κ) s 1 * a.bound * gaussianRieszPhysicalPair s p := by
  have h := sourceRieszLocal_full_transport_bound s 1 hs (a.riesz_lipschitz n) p
  change |sourceRieszTransportKernel 1 s (gradient (a.test n)) p| ≤
    sourceRieszLocalProfileConstant (ι := κ) s 1 * a.bound ^ (1 : ℕ) *
      gaussianRieszPhysicalPair s p at h
  simpa only [pow_one] using h

lemma riesz_tendsto_kernel {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (s : ℝ) (hs : 0 < s) (p : (EuclideanSpace ℝ κ) × (EuclideanSpace ℝ κ)) :
    Tendsto (fun n => sourceRieszTransportKernel 1 s (gradient (a.test n)) p) atTop
      (𝓝 (sourceRieszTransportKernel 1 s (gradient φ) p)) := by
  obtain ⟨x, y⟩ := p
  simp only [sourceRieszTransportKernel_force s hs]
  have hc : Tendsto (fun _ : ℕ => sourceRieszForce s (x - y)) atTop
      (𝓝 (sourceRieszForce s (x - y))) := tendsto_const_nhds
  exact hc.inner ((a.tendsto_gradient x).sub (a.tendsto_gradient y))

/-- Fixed-law limits under the density cap, with properness of the limits. -/
lemma riesz_spatial_limits {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (s : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card κ : ℝ))
    (ρ : (EuclideanSpace ℝ κ) → ℝ) (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (Integrable φ (gaussianRieszDensityMeasure ρ) ∧
      Tendsto (fun n => ∫ x, a.test n x ∂gaussianRieszDensityMeasure ρ) atTop
        (𝓝 (∫ x, φ x ∂gaussianRieszDensityMeasure ρ))) ∧
    (Integrable (laplacian φ) (gaussianRieszDensityMeasure ρ) ∧
      Tendsto (fun n => ∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ) atTop
        (𝓝 (∫ x, laplacian φ x ∂gaussianRieszDensityMeasure ρ))) ∧
    (Integrable (sourceRieszTransportKernel 1 s (gradient φ))
        ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ∧
      Tendsto (fun n => ∫ p, sourceRieszTransportKernel 1 s (gradient (a.test n)) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) atTop
        (𝓝 (∫ p, sourceRieszTransportKernel 1 s (gradient φ) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))) := by
  obtain ⟨hv, hl⟩ := a.value_laplacian_limits (gaussianRieszDensityMeasure ρ)
  refine ⟨hv, hl, ?_⟩
  have hpair : Integrable (gaussianRieszPhysicalPair (ι := κ) s)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
    (memLp_gaussianRieszPhysicalPair s hs (by linarith) ρ M hM hρ).integrable (by norm_num)
  exact sourcePointwise_integrable_tendsto_of_dominated
    ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))
    (fun n p => sourceRieszTransportKernel 1 s (gradient (a.test n)) p)
    (sourceRieszTransportKernel 1 s (gradient φ))
    (fun p => sourceRieszLocalProfileConstant (ι := κ) s 1 * a.bound *
      gaussianRieszPhysicalPair s p)
    (hpair.const_mul _)
    (fun n => (measurable_sourceRieszTransportKernel s 1 (a.riesz_lipschitz n)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs] using a.riesz_kernel_bound s hs n p))
    (Filter.Eventually.of_forall (a.riesz_tendsto_kernel s hs))

/-- Uniform drift bound under the density cap (same statement shape as B's
`sourceRieszStaticMeanTestDrift_bound`, reproved here from checked inputs only). -/
lemma riesz_drift_bound {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (s β : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card κ : ℝ))
    (ρ : (EuclideanSpace ℝ κ) → ℝ) (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (n : ℕ) :
    |sourceRieszStaticMeanTestDrift s β ρ (a.test n)| ≤
      |β⁻¹| * ((Fintype.card κ : ℝ) * a.bound) +
        (1/2 : ℝ) * (sourceRieszLocalProfileConstant (ι := κ) s 1 * a.bound *
          gaussianRieszPhysicalPotentialConstant s M κ) := by
  have hL : |∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ| ≤
      (Fintype.card κ : ℝ) * a.bound := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := gaussianRieszDensityMeasure ρ) (f := laplacian (a.test n))
        (Filter.Eventually.of_forall (fun x => by
          simpa only [Real.norm_eq_abs] using a.laplacian_bound n x))
  have hK := (sourceRieszLocalTransport_pair s 1 hs hd (a.riesz_lipschitz n) ρ M hM hρ).2
  have hK' : |∫ p, sourceRieszTransportKernel 1 s (gradient (a.test n)) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)| ≤
      sourceRieszLocalProfileConstant (ι := κ) s 1 * a.bound *
        gaussianRieszPhysicalPotentialConstant s M κ := by
    change |∫ p, sourceRieszTransportKernel 1 s (gradient (a.test n)) p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)| ≤
      sourceRieszLocalProfileConstant (ι := κ) s 1 * a.bound ^ (1 : ℕ) *
        gaussianRieszPhysicalPotentialConstant s M κ at hK
    simpa only [pow_one] using hK
  unfold sourceRieszStaticMeanTestDrift
  calc
    _ ≤ |β⁻¹ * (∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ)| +
        |(1/2 : ℝ) * (∫ p, sourceRieszTransportKernel 1 s (gradient (a.test n)) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))| :=
      abs_sub _ _
    _ = |β⁻¹| * |∫ x, laplacian (a.test n) x ∂gaussianRieszDensityMeasure ρ| +
        (1/2 : ℝ) * |∫ p, sourceRieszTransportKernel 1 s (gradient (a.test n)) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)| := by
      rw [abs_mul, abs_mul]; norm_num
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hL (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hK' (by norm_num))

lemma riesz_drift_tendsto {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (s β : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card κ : ℝ))
    (ρ : (EuclideanSpace ℝ κ) → ℝ) (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Tendsto (fun n => sourceRieszStaticMeanTestDrift s β ρ (a.test n)) atTop
      (𝓝 (sourceRieszStaticMeanTestDrift s β ρ φ)) := by
  obtain ⟨_, ⟨_, hL⟩, ⟨_, hK⟩⟩ := a.riesz_spatial_limits s hs hd ρ M hM hρ
  exact (tendsto_const_nhds.mul hL).sub (tendsto_const_nhds.mul hK)

/-- Proper time dominated convergence; the density cap is used at every time of
the horizon (it is uniform, as in source 878). -/
lemma riesz_time_limit {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (s β T : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card κ : ℝ))
    (hT : 0 ≤ T) (ρ : ℝ → (EuclideanSpace ℝ κ) → ℝ)
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ t ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ t x ≤ M)
    (hi : ∀ n, IntervalIntegrable
      (fun t => sourceRieszStaticMeanTestDrift s β (ρ t) (a.test n)) volume 0 T)
    (r : ℝ) (hr : r ∈ Icc 0 T) :
    IntervalIntegrable (fun t => sourceRieszStaticMeanTestDrift s β (ρ t) φ) volume 0 r ∧
    Tendsto (fun n => ∫ t in 0..r, sourceRieszStaticMeanTestDrift s β (ρ t) (a.test n))
      atTop (𝓝 (∫ t in 0..r, sourceRieszStaticMeanTestDrift s β (ρ t) φ)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 r)
  have hsub : Ioc 0 r ⊆ Ioc 0 T := fun t ht => ⟨ht.1, ht.2.trans hr.2⟩
  have him (n : ℕ) : AEStronglyMeasurable
      (fun t => sourceRieszStaticMeanTestDrift s β (ρ t) (a.test n)) μ :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hi n)).mono_set hsub).1
  have hb (n : ℕ) : ∀ᵐ t ∂μ,
      ‖sourceRieszStaticMeanTestDrift s β (ρ t) (a.test n)‖ ≤
        |β⁻¹| * ((Fintype.card κ : ℝ) * a.bound) +
          (1/2 : ℝ) * (sourceRieszLocalProfileConstant (ι := κ) s 1 * a.bound *
            gaussianRieszPhysicalPotentialConstant s M κ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.trans hr.2⟩
    letI := hprob t htT
    simpa only [Real.norm_eq_abs] using a.riesz_drift_bound s β hs hd (ρ t) M hM (hρ t htT) n
  have hl : ∀ᵐ t ∂μ,
      Tendsto (fun n => sourceRieszStaticMeanTestDrift s β (ρ t) (a.test n))
        atTop (𝓝 (sourceRieszStaticMeanTestDrift s β (ρ t) φ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.trans hr.2⟩
    letI := hprob t htT
    exact a.riesz_drift_tendsto s β hs hd (ρ t) M hM (hρ t htT)
  obtain ⟨hproper, hlim⟩ := sourcePointwise_integrable_tendsto_of_bounded μ
    (fun n t => sourceRieszStaticMeanTestDrift s β (ρ t) (a.test n))
    (fun t => sourceRieszStaticMeanTestDrift s β (ρ t) φ) _ him hb hl
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1).mpr hproper, ?_⟩
  simpa only [intervalIntegral.integral_of_le hr.1] using hlim

/-- The every-time integrated Riesz identity passes from approximants to the
limit test. -/
theorem riesz_integrated_identity {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (s β T : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card κ : ℝ)) (hT : 0 ≤ T) (ρ : ℝ → (EuclideanSpace ℝ κ) → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (hi : ∀ n, IntervalIntegrable
      (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) (a.test n)) volume 0 T)
    (he : ∀ n, ∀ r ∈ Icc 0 T,
      (∫ x, a.test n x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, a.test n x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceRieszStaticMeanTestDrift s β (ρ u) (a.test n)) :
    IntervalIntegrable (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) φ) volume 0 T ∧
    ∀ r ∈ Icc 0 T,
      (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceRieszStaticMeanTestDrift s β (ρ u) φ := by
  have ht := a.riesz_time_limit s β T hs hd hT ρ hprob M hM hρ hi
  refine ⟨(ht T ⟨hT, le_rfl⟩).1, ?_⟩
  intro r hr
  letI := hprob r hr
  letI := hprob 0 ⟨le_rfl, hT⟩
  have hleft := (a.value_laplacian_limits (gaussianRieszDensityMeasure (ρ r))).1.2
  have hright := ((a.value_laplacian_limits (gaussianRieszDensityMeasure (ρ 0))).1.2).add
    (ht r hr).2
  have hright' : Tendsto (fun n => ∫ x, a.test n x ∂gaussianRieszDensityMeasure (ρ r))
      atTop (𝓝 ((∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) +
        ∫ u in 0..r, sourceRieszStaticMeanTestDrift s β (ρ u) φ)) :=
    hright.congr (fun n => ((he n) r hr).symm)
  exact tendsto_nhds_unique hleft hright'

end SourceC2PointwiseApproximation

end DGRHS.Commutator
