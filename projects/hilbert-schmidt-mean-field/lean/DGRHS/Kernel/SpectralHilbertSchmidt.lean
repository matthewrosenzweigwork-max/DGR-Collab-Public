/- Preparation: actual integral-operator eigenvalue square summability and kernel norm.
Depends on checked versions of Spectrum and HilbertSchmidt; not yet Lean checked. -/
import DGRHS.Kernel.Spectrum
import DGRHS.Kernel.HilbertSchmidt
import DGRHS.Kernel.RegularizedDeterminant
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace DGRHS.Kernel
universe u v
variable {α : Type u} {ι : Type v} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

lemma norm_eigenbasis_image_sq (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator k hk (b i) = eig i • b i) (i : ι) :
    ‖integralOperator k hk (b i)‖ ^ 2 = eig i ^ 2 := by
  rw [hb i, norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs, sq_abs]

theorem summable_integralOperator_eigenvalue_sq (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ)) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator k hk (b i) = eig i • b i) :
    Summable (fun i ↦ eig i ^ 2) := by
  have h := summable_norm_kernelOp_sq (hk.toLp k) b b.orthonormal
  exact h.congr (fun i ↦ norm_eigenbasis_image_sq k hk eig b hb i)

theorem tsum_integralOperator_eigenvalue_sq [Countable ι] (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ)) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator k hk (b i) = eig i • b i) :
    (∑' i, eig i ^ 2) = ∫ p, k p ^ 2 ∂(μ.prod μ) := by
  calc
    (∑' i, eig i ^ 2) = ∑' i, ‖integralOperator k hk (b i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      exact (norm_eigenbasis_image_sq k hk eig b hb i).symm
    _ = ‖hk.toLp k‖ ^ 2 := tsum_norm_kernelOp_sq (hk.toLp k) b
    _ = ∫ p, k p ^ 2 ∂(μ.prod μ) := norm_toLp_sq hk

theorem exists_integralOperator_HS_eigenbasis [MeasurableSpace.CountablyGenerated α]
    (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, k p.swap = k p) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧ (∀ i, integralOperator k hk (b i) = eig i • b i) ∧
      Summable (fun i ↦ eig i ^ 2) ∧
      (∑' i, eig i ^ 2) = ∫ p, k p ^ 2 ∂(μ.prod μ) := by
  obtain ⟨ι, eig, b, hcount, hb⟩ := exists_integralOperator_eigenbasis k hk hsym
  letI := hcount
  exact ⟨ι, eig, b, hcount, hb, summable_integralOperator_eigenvalue_sq k hk eig b hb,
    tsum_integralOperator_eigenvalue_sq k hk eig b hb⟩

lemma summable_scaled_eigenvalue_sq (eig : ι → ℝ)
    (h : Summable (fun i ↦ eig i ^ 2)) (β : ℝ) :
    Summable (fun i ↦ (β * eig i) ^ 2) := by
  simpa only [mul_pow] using h.mul_left (β ^ 2)
end DGRHS.Kernel
#print axioms DGRHS.Kernel.exists_integralOperator_HS_eigenbasis
#print axioms DGRHS.Kernel.summable_scaled_eigenvalue_sq
