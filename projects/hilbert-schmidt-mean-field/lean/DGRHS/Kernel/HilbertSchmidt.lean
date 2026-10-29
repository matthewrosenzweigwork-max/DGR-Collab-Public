/- Unchecked draft: actual kernel Bessel/Parseval bridge. Move to active proof
only after the pending root snapshot finishes; no acceptance by this file. -/
import DGRHS.Kernel.Operator
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real
open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators
namespace DGRHS.Kernel
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

lemma norm_Lp_sq (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  simpa only [Lp.toLp_coeFn] using norm_toLp_sq (Lp.memLp f)

lemma kernel_row_inner_ae (κ : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, ∀ (hr : MemLp (fun y ↦ κ (x,y)) 2 μ),
      Operator.l2KernelOp κ f x = inner ℝ f (hr.toLp (fun y ↦ κ (x,y))) := by
  filter_upwards [Operator.l2KernelOp_apply_ae κ f] with x hx
  intro hr
  rw [hx, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hr.coeFn_toLp] with y hy
  simp [hy, RCLike.inner_apply', mul_comm]

lemma sum_norm_kernelOp_sq_le (κ : Lp ℝ 2 (μ.prod μ))
    (v : ι → Lp ℝ 2 μ) (hv : Orthonormal ℝ v) (s : Finset ι) :
    (∑ i ∈ s, ‖Operator.l2KernelOp κ (v i)‖ ^ 2) ≤ ‖κ‖ ^ 2 := by
  classical
  have hK : Integrable (fun p : α × α ↦ κ p ^ 2) (μ.prod μ) := (Lp.memLp κ).integrable_sq
  have hout (i : ι) : Integrable (fun x ↦ (Operator.l2KernelOp κ (v i) x) ^ 2) μ :=
    (Lp.memLp _).integrable_sq
  have hae : ∀ᵐ x ∂μ, ∀ i ∈ s, ∀ (hr : MemLp (fun y ↦ κ (x,y)) 2 μ),
      Operator.l2KernelOp κ (v i) x = inner ℝ (v i) (hr.toLp (fun y ↦ κ (x,y))) :=
    (Filter.eventually_all_finset s).2 (fun i _ ↦ kernel_row_inner_ae κ (v i))
  have hpoint : ∀ᵐ x ∂μ, (∑ i ∈ s, (Operator.l2KernelOp κ (v i) x)^2)
      ≤ ∫ y, κ (x,y)^2 ∂μ := by
    filter_upwards [Operator.l2Kernel_slice_memLp κ, hae] with x hr he
    have hb := hv.sum_inner_products_le (hr.toLp (fun y ↦ κ (x,y))) (s := s)
    rw [norm_toLp_sq hr] at hb
    calc
      (∑ i ∈ s, (Operator.l2KernelOp κ (v i) x)^2)
          = ∑ i ∈ s, ‖inner ℝ (v i) (hr.toLp (fun y ↦ κ (x,y)))‖^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [he i hi hr, Real.norm_eq_abs, sq_abs]
      _ ≤ ∫ y, κ (x,y)^2 ∂μ := hb
  calc
    (∑ i ∈ s, ‖Operator.l2KernelOp κ (v i)‖ ^ 2)
        = ∫ x, (∑ i ∈ s, (Operator.l2KernelOp κ (v i) x)^2) ∂μ := by
      simp_rw [norm_Lp_sq]
      exact (integral_finsetSum s (fun i _ ↦ hout i)).symm
    _ ≤ ∫ x, ∫ y, κ (x,y)^2 ∂μ ∂μ :=
      integral_mono_ae (integrable_finsetSum s (fun i _ ↦ hout i)) hK.integral_prod_left hpoint
    _ = ∫ p, κ p ^ 2 ∂(μ.prod μ) := (integral_prod _ hK).symm
    _ = ‖κ‖ ^ 2 := (norm_Lp_sq κ).symm

lemma summable_norm_kernelOp_sq (κ : Lp ℝ 2 (μ.prod μ))
    (v : ι → Lp ℝ 2 μ) (hv : Orthonormal ℝ v) :
    Summable (fun i ↦ ‖Operator.l2KernelOp κ (v i)‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _) (sum_norm_kernelOp_sq_le κ v hv)

lemma tsum_norm_kernelOp_sq [Countable ι] (κ : Lp ℝ 2 (μ.prod μ))
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    (∑' i, ‖Operator.l2KernelOp κ (b i)‖ ^ 2) = ‖κ‖ ^ 2 := by
  have hK : Integrable (fun p : α × α ↦ κ p ^ 2) (μ.prod μ) := (Lp.memLp κ).integrable_sq
  have hout (i : ι) : Integrable (fun x ↦ (Operator.l2KernelOp κ (b i) x) ^ 2) μ :=
    (Lp.memLp _).integrable_sq
  have hsum : Summable (fun i ↦ ∫ x, ‖(Operator.l2KernelOp κ (b i) x)^2‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (sq_nonneg _), ← norm_Lp_sq] using
      summable_norm_kernelOp_sq κ b b.orthonormal
  have hae : ∀ᵐ x ∂μ, ∀ i : ι, ∀ (hr : MemLp (fun y ↦ κ (x,y)) 2 μ),
      Operator.l2KernelOp κ (b i) x = inner ℝ (b i) (hr.toLp (fun y ↦ κ (x,y))) := by
    exact ae_all_iff.2 (fun i ↦ kernel_row_inner_ae κ (b i))
  have hpoint : ∀ᵐ x ∂μ, (∑' i, (Operator.l2KernelOp κ (b i) x)^2)
      = ∫ y, κ (x,y)^2 ∂μ := by
    filter_upwards [Operator.l2Kernel_slice_memLp κ, hae] with x hr he
    have hp := b.tsum_inner_mul_inner (hr.toLp (fun y ↦ κ (x,y))) (hr.toLp (fun y ↦ κ (x,y)))
    rw [real_inner_self_eq_norm_sq, norm_toLp_sq hr] at hp
    convert hp using 1
    congr 1
    funext i
    rw [he i hr, real_inner_comm (hr.toLp (fun y ↦ κ (x,y))) (b i)]
    ring
  calc
    (∑' i, ‖Operator.l2KernelOp κ (b i)‖ ^ 2)
        = ∑' i, ∫ x, (Operator.l2KernelOp κ (b i) x)^2 ∂μ := by simp_rw [norm_Lp_sq]
    _ = ∫ x, (∑' i, (Operator.l2KernelOp κ (b i) x)^2) ∂μ :=
      integral_tsum_of_summable_integral_norm hout hsum
    _ = ∫ x, ∫ y, κ (x,y)^2 ∂μ ∂μ := integral_congr_ae hpoint
    _ = ∫ p, κ p ^ 2 ∂(μ.prod μ) := (integral_prod _ hK).symm
    _ = ‖κ‖ ^ 2 := (norm_Lp_sq κ).symm
end DGRHS.Kernel
#print axioms DGRHS.Kernel.sum_norm_kernelOp_sq_le
#print axioms DGRHS.Kernel.summable_norm_kernelOp_sq
#print axioms DGRHS.Kernel.tsum_norm_kernelOp_sq
