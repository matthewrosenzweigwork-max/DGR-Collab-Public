/- Actual centered-kernel spectral adapter. Reuses the licensed basis assembly,
and compactness/symmetry proved for the actual integral operator. No eigenbasis
or favorable spectral sequence is assumed in the existence theorem. -/
import DGRHS.Kernel.Operator
import DGRHS.Kernel.Imported.SpectralBasis
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import DGRHS.Kernel.Imported.BasisCountability

open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.Kernel
universe u
variable {α : Type u} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem integralOperator_isSelfAdjoint (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ)) (hsym : ∀ᵐ p ∂μ.prod μ, k p.swap = k p) :
    IsSelfAdjoint (integralOperator k hk) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 (integralOperator_isSymmetric k hk hsym)

theorem exists_integralOperator_eigenbasis [MeasurableSpace.CountablyGenerated α]
    (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, k p.swap = k p) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧ ∀ i, integralOperator k hk (b i) = eig i • b i := by
  letI : TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) := separable_L2
  obtain ⟨ι, eig, b, hb⟩ :=
    Spectral.exists_hilbertBasis_hasEigenvector_of_isCompactOperator_of_isSelfAdjoint
      (integralOperator k hk) (integralOperator_isSelfAdjoint k hk hsym)
      (integralOperator_isCompact k hk)
  refine ⟨ι, eig, b, countable_of_separable_index b, ?_⟩
  intro i
  exact (hb i).apply_eq_smul

theorem separable_euclidean_L2 (d : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν] :
    TopologicalSpace.SeparableSpace (Lp ℝ 2 ν) := by
  apply separable_L2

lemma inner_oneL2_eq_integral (f : Lp ℝ 2 μ) :
    inner ℝ (oneL2 (μ := μ)) f = ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneL2_coeFn (μ := μ)] with x hx
  simp [hx]

lemma integral_eigenfunction_eq_zero (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ)) (hsym : ∀ᵐ p ∂μ.prod μ, k p.swap = k p)
    (hmean : ∀ᵐ x ∂μ, ∫ y, k (x,y) ∂μ = 0)
    (f : Lp ℝ 2 μ) {eig : ℝ} (heig : eig ≠ 0)
    (hf : integralOperator k hk f = eig • f) : ∫ x, f x ∂μ = 0 := by
  have hz := inner_one_integralOperator_eq_zero k hk hsym hmean f
  rw [hf, inner_smul_right, inner_oneL2_eq_integral] at hz
  exact (mul_eq_zero.mp hz).resolve_left heig

end DGRHS.Kernel
#print axioms DGRHS.Kernel.integralOperator_isSelfAdjoint
#print axioms DGRHS.Kernel.exists_integralOperator_eigenbasis
#print axioms DGRHS.Kernel.separable_euclidean_L2
#check DGRHS.Kernel.exists_integralOperator_eigenbasis

#print axioms DGRHS.Kernel.integral_eigenfunction_eq_zero
