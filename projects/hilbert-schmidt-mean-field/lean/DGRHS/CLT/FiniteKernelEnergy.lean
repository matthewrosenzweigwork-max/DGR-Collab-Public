/- UNCHECKED outside frozen proof. Finite spectral kernel energy identity.
Off-diagonal refers to unequal particle indices; spatial coincidences are
not deleted. No convention on the spatial diagonal is used in this lemma. -/
import DGRHS.CLT.FiniteRankChaosCLT
import DGRHS.CanonicalVariance.ParticleVariance
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.CLT
variable {S j : Type*} [MeasurableSpace S] [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

lemma offDiag_sum_mul {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    (∑ p ∈ s.offDiag, u p.1 * u p.2) = (∑ i ∈ s, u i)^2 - ∑ i ∈ s, (u i)^2 := by
  classical
  have hsplit := Finset.sum_union (f := fun p : ι × ι => u p.1 * u p.2)
    (Finset.disjoint_diag_offDiag s)
  rw [Finset.diag_union_offDiag, Finset.sum_product] at hsplit
  have hdiag : (∑ p ∈ s.diag, u p.1 * u p.2) = ∑ i ∈ s, (u i)^2 := by
    simp [Finset.diag, ← sq]
  rw [hdiag] at hsplit
  have hprod : (∑ i ∈ s, ∑ l ∈ s, u i * u l) = (∑ i ∈ s, u i)^2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [hprod] at hsplit
  linarith

def finiteSpectralKernel (a : j → ℝ) (e : j → Lp ℝ 2 μ) (p : S × S) : ℝ :=
  ∑ l, a l * e l p.1 * e l p.2

lemma offDiagonalSum_finiteSpectralKernel {ι : Type*} [Fintype ι]
    (a : j → ℝ) (e : j → Lp ℝ 2 μ) (x : ι → S) :
    DGRHS.CanonicalVariance.offDiagonalSum (finiteSpectralKernel a e) x =
      ∑ l, a l * ((∑ i : ι, e l (x i))^2 - ∑ i : ι, (e l (x i))^2) := by
  classical
  unfold DGRHS.CanonicalVariance.offDiagonalSum finiteSpectralKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, offDiag_sum_mul Finset.univ (fun i => e l (x i))]

lemma normalizedOffDiagonalSum_finiteSpectralKernel {N : ℕ}
    (a : j → ℝ) (e : j → Lp ℝ 2 μ) (x : Fin N → S) :
    DGRHS.CanonicalVariance.normalizedOffDiagonalSum (finiteSpectralKernel a e) x =
      ∑ l, a l * ((N : ℝ)⁻¹ * (∑ i : Fin N, e l (x i))^2 -
        (N : ℝ)⁻¹ * ∑ i : Fin N, (e l (x i))^2) := by
  classical
  rw [DGRHS.CanonicalVariance.normalizedOffDiagonalSum,
    offDiagonalSum_finiteSpectralKernel]
  simp only [Fintype.card_fin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.mul_sum]
  ring

lemma inverse_sqrt_sum_sq (N : ℕ) (r : ℝ) :
    ((Real.sqrt N)⁻¹ * r)^2 = (N : ℝ)⁻¹ * r^2 := by
  rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

lemma finiteSpectralQuadratic_finiteEigenFeature_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : j → ℝ) (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ)
    (N : ℕ) (x : Fin N → S) :
    finiteSpectralQuadratic a b ((Real.sqrt N)⁻¹ • ∑ i : Fin N, finiteEigenFeature b e (x i)) =
      ∑ l, a l * ((N : ℝ)⁻¹ * (∑ i : Fin N, e l (x i))^2) := by
  classical
  unfold finiteSpectralQuadratic
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  rw [inner_smul_right, inner_sum]
  have heval : ∀ i : Fin N, inner ℝ (b l) (finiteEigenFeature b e (x i)) = e l (x i) := by
    intro i
    unfold finiteEigenFeature
    simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    simp
  simp_rw [heval]
  exact inverse_sqrt_sum_sq N _

end DGRHS.CLT
#print axioms DGRHS.CLT.offDiag_sum_mul
#print axioms DGRHS.CLT.offDiagonalSum_finiteSpectralKernel
#print axioms DGRHS.CLT.normalizedOffDiagonalSum_finiteSpectralKernel
#print axioms DGRHS.CLT.finiteSpectralQuadratic_finiteEigenFeature_sum
