/- Preparation: spectral factor conditions derived from the actual operator.
Kernel positivity itself must be proved from each source interaction/feature representation. -/
import DGRHS.Kernel.SpectralHilbertSchmidt
namespace DGRHS.Kernel
open MeasureTheory
open scoped InnerProductSpace
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
lemma integralOperator_eigenvalue_norm_le (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ)) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator k hk (b i) = eig i • b i) (i : ι) :
    ‖eig i‖ ≤ ‖integralOperator k hk‖ := by
  have h := (integralOperator k hk).le_opNorm (b i)
  simpa only [hb i, norm_smul, b.orthonormal.1 i, mul_one] using h

lemma integralOperator_eigenvalue_nonneg (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ)) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator k hk (b i) = eig i • b i)
    (hpositive : ∀ f : Lp ℝ 2 μ, 0 ≤ inner ℝ (integralOperator k hk f) f) (i : ι) :
    0 ≤ eig i := by
  have h := hpositive (b i)
  simpa only [hb i, real_inner_smul_left, real_inner_self_eq_norm_sq,
    b.orthonormal.1 i, one_pow, mul_one] using h

lemma attractive_eigenvalue_factor_pos (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ)) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator k hk (b i) = eig i • b i)
    {β : ℝ} (hβ : 0 ≤ β) (hgap : β * ‖integralOperator k hk‖ < 1) (i : ι) :
    0 < 1 - β * eig i := by
  have he : eig i ≤ ‖integralOperator k hk‖ :=
    (le_abs_self _).trans (integralOperator_eigenvalue_norm_le k hk eig b hb i)
  have h := mul_le_mul_of_nonneg_left he hβ
  linarith
end DGRHS.Kernel
#print axioms DGRHS.Kernel.integralOperator_eigenvalue_nonneg
#print axioms DGRHS.Kernel.attractive_eigenvalue_factor_pos
