/- Exact all-N sign/normalization adapter. The finite off-diagonal expansion
reuses worker A's SourcePartitionRate proof structure (frozen five-body packet
20261001_114059_UTC), with no change to index or spatial-diagonal conventions. -/
import DGRHS.Concentration.MasterTail
import DGRHS.Gaussian.FeatureRateSourceKernel
import DGRHS.CLT.SourceWeightCorrection
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.CLT

lemma sourceStatistic_eq_normalized {S : Type*} [MeasurableSpace S]
    (h : S × S → ℝ) (N : ℕ) (x : Fin N → S) :
    DGRHS.Gaussian.sourceKernelParticleStatistic h N x =
      DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
  classical
  unfold DGRHS.Gaussian.sourceKernelParticleStatistic
    DGRHS.CanonicalVariance.normalizedOffDiagonalSum DGRHS.CanonicalVariance.offDiagonalSum
  rw [Fintype.card_fin]
  congr 1
  symm
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        if p.1=p.2 then 0 else h (x p.1,x p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [(Finset.mem_offDiag.mp hp).2.2,ite_false]
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N))×ˢFinset.univ,
        if p.1=p.2 then 0 else h (x p.1,x p.2) := by
      apply Finset.sum_subset
      · intro p hp
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_univ _⟩
      · intro p hp hnot
        have he : p.1=p.2 := by
          by_contra hn
          exact hnot (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hn⟩)
        simp only [he,ite_true]
    _ = _ := by rw [Finset.sum_product]

lemma iidCanonicalExponent_eq {S : Type*} [MeasurableSpace S]
    (γ : ℝ) (h : S × S → ℝ) (N : ℕ) (x : Fin N → S) :
    γ*DGRHS.Concentration.iidNegativeStatistic N h x =
      -γ/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
  have hSum : DGRHS.Concentration.iidCoupledSum N h x =
      ∑ i : Fin N,∑ j : Fin N,if i=j then 0 else h (x i,x j) := by
    unfold DGRHS.Concentration.iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    simp only [ne_eq,ite_not]
  rw [←sourceStatistic_eq_normalized]
  unfold DGRHS.Concentration.iidNegativeStatistic DGRHS.Gaussian.sourceKernelParticleStatistic
  rw [hSum]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
end DGRHS.CLT
#print axioms DGRHS.CLT.sourceStatistic_eq_normalized
#print axioms DGRHS.CLT.iidCanonicalExponent_eq
#check @DGRHS.CLT.iidCanonicalExponent_eq
