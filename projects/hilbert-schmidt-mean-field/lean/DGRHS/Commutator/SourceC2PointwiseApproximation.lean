import DGRHS.Commutator.SourceBoundedC2Spatial
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Kernel-independent pointwise C2 approximation data: one uniform bound on all
derivatives through order two, and pointwise convergence of value, gradient and
Laplacian. Used by both the LOG (`SourceLogC2PointwiseLimit`) and positive-Riesz
(`SourceRieszC2PointwiseLimit`) passages, by the compact-C2 cutoff route and by
the compact mollifier route. Contains no measure, law, weak identity or desired
conclusion. -/
noncomputable section
open MeasureTheory Laplacian Set Filter
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Pointwise C2 approximation data. It contains no measure, law, drift limit,
weak identity or desired conclusion. -/
structure SourceC2PointwiseApproximation (φ : E → ℝ) where
  test : ℕ → E → ℝ
  smooth : ∀ n, ContDiff ℝ 2 (test n)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  deriv_bound : ∀ n j, j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j (test n) x‖ ≤ bound
  tendsto_value : ∀ x, Tendsto (fun n => test n x) atTop (𝓝 (φ x))
  tendsto_gradient : ∀ x, Tendsto (fun n => gradient (test n) x) atTop (𝓝 (gradient φ x))
  tendsto_laplacian : ∀ x,
    Tendsto (fun n => laplacian (test n) x) atTop (𝓝 (laplacian φ x))

/-- Dominated convergence with an integrable dominating function, returning
properness of the limit as well. -/
lemma sourcePointwise_integrable_tendsto_of_dominated
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : ℕ → X → ℝ) (f : X → ℝ) (g : X → ℝ) (hg : Integrable g μ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Integrable f μ ∧
      Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hF hl
  have hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x := by
    filter_upwards [hl, ae_all_iff.2 hb] with x hx hbx
    exact le_of_tendsto hx.norm (Filter.Eventually.of_forall hbx)
  exact ⟨hg.mono' hm hfb, tendsto_integral_of_dominated_convergence g hF hg hb hl⟩

/-- Finite-measure dominated convergence that also returns properness of the
limit (a totalized Bochner value is never used as a substitute). -/
lemma sourcePointwise_integrable_tendsto_of_bounded
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

namespace SourceC2PointwiseApproximation

lemma bounded_test {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (n : ℕ) : SourceBoundedC2Test (a.test n) :=
  ⟨a.smooth n, a.bound, a.bound_nonneg, a.deriv_bound n⟩

lemma laplacian_bound {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (n : ℕ) (x : EuclideanSpace ℝ κ) :
    |laplacian (a.test n) x| ≤ (Fintype.card κ : ℝ) * a.bound :=
  source_laplacian_bound_of_hessian (EuclideanSpace.basisFun κ ℝ) _ _
    (a.deriv_bound n 2 le_rfl) x

lemma value_bound {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (n : ℕ) (x : EuclideanSpace ℝ κ) : ‖a.test n x‖ ≤ a.bound := by
  simpa only [norm_iteratedFDeriv_zero] using a.deriv_bound n 0 (by omega) x

lemma continuous_laplacian_test {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (n : ℕ) : Continuous (laplacian (a.test n)) := by
  have hH : Continuous (fun p : Unit × EuclideanSpace ℝ κ => iteratedFDeriv ℝ 2 (a.test n) p.2) :=
    ((a.smooth n).continuous_iteratedFDeriv le_rfl).comp continuous_snd
  have hL := continuous_laplacian_of_joint_hessian
    (EuclideanSpace.basisFun κ ℝ) (fun _ : Unit => a.test n) hH
  have he : Continuous (fun x : EuclideanSpace ℝ κ => ((), x)) := continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using hL.comp he

lemma integrable_test {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (μ : Measure (EuclideanSpace ℝ κ)) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (a.test n) μ :=
  (integrable_const a.bound).mono' (a.smooth n).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (a.value_bound n))

lemma integrable_laplacian_test {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (μ : Measure (EuclideanSpace ℝ κ)) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (laplacian (a.test n)) μ :=
  (integrable_const ((Fintype.card κ : ℝ) * a.bound)).mono'
    (a.continuous_laplacian_test n).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using a.laplacian_bound n x))

/-- Fixed-law value and Laplacian limits with properness, for any finite law. -/
lemma value_laplacian_limits {κ : Type*} [Fintype κ] {φ : EuclideanSpace ℝ κ → ℝ}
    (a : DGRHS.Commutator.SourceC2PointwiseApproximation (ι := κ) φ) (μ : Measure (EuclideanSpace ℝ κ)) [IsFiniteMeasure μ] :
    (Integrable φ μ ∧
      Tendsto (fun n => ∫ x, a.test n x ∂μ) atTop (𝓝 (∫ x, φ x ∂μ))) ∧
    (Integrable (laplacian φ) μ ∧
      Tendsto (fun n => ∫ x, laplacian (a.test n) x ∂μ) atTop
        (𝓝 (∫ x, laplacian φ x ∂μ))) :=
  ⟨sourcePointwise_integrable_tendsto_of_bounded μ (fun n x => a.test n x) φ a.bound
      (fun n => (a.integrable_test μ n).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (a.value_bound n))
      (Filter.Eventually.of_forall a.tendsto_value),
    sourcePointwise_integrable_tendsto_of_bounded μ
      (fun n x => laplacian (a.test n) x) (laplacian φ) ((Fintype.card κ : ℝ) * a.bound)
      (fun n => (a.integrable_laplacian_test μ n).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using a.laplacian_bound n x))
      (Filter.Eventually.of_forall a.tendsto_laplacian)⟩

end SourceC2PointwiseApproximation
end DGRHS.Commutator
