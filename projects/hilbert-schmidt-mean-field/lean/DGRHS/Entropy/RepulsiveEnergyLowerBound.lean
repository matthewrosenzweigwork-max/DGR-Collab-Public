/- Actual raw source energy lower bound. The one-body logarithmic tail
cancels the ordered-pair lower bound with the exact finite-N coefficients. -/
import DGRHS.CLT.SourceRawEnergy
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Entropy

lemma sourceRawEnergy_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Ω→Ω→ℝ) (hW : ∀ x y,W x y=W y x)
    (ell : Ω→ℝ) (hell : ∀ x,0≤ell x) (C : ℝ)
    (hp : ∀ x y,-ell x-ell y≤W x y)
    (hF : ∀ x,DGRHS.potential μ W x≤C-ell x)
    (N : ℕ) (hN : 0<N) (x : Fin N→Ω) :
    DGRHS.interactionEnergy μ W-C+(N:ℝ)^(-2:ℤ)*(∑ i,ell (x i)) ≤
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p=>DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x := by
  classical
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hw : -2*((N:ℝ)-1)*(∑ i,ell (x i)) ≤
      DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) x := by
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)).offDiag)
      (fun p _=>hp (x p.1) (x p.2))
    change (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,(-ell (x p.1)-ell (x p.2))) ≤ _ at hs
    rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib,
      DGRHS.CLT.offDiag_sum_fst,DGRHS.CLT.offDiag_sum_snd] at hs
    unfold DGRHS.CanonicalVariance.offDiagonalSum Function.uncurry
    nlinarith
  have hfs : (∑ i,DGRHS.potential μ W (x i)) ≤ (N:ℝ)*C-∑ i,ell (x i) := by
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun i _=>hF (x i))
    simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul] using hs
  rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ W hW N hN x]
  have h1 := mul_le_mul_of_nonneg_left hw (show 0≤(2*(N:ℝ)^2)⁻¹ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hfs (show 0≤(N:ℝ)⁻¹ by positivity)
  have he : DGRHS.interactionEnergy μ W-C+(N:ℝ)^(-2:ℤ)*(∑ i,ell (x i))=
      (2*(N:ℝ)^2)⁻¹*(-2*((N:ℝ)-1)*(∑ i,ell (x i)))-
        (N:ℝ)⁻¹*((N:ℝ)*C-∑ i,ell (x i))+DGRHS.interactionEnergy μ W := by
    simp only [zpow_neg,zpow_ofNat]
    field_simp
    <;> ring
  rw [he]
  linarith

lemma sourceRawEnergy_uniform_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Ω→Ω→ℝ) (hW : ∀ x y,W x y=W y x)
    (ell : Ω→ℝ) (hell : ∀ x,0≤ell x) (C : ℝ)
    (hp : ∀ x y,-ell x-ell y≤W x y)
    (hF : ∀ x,DGRHS.potential μ W x≤C-ell x)
    (N : ℕ) (hN : 0<N) (x : Fin N→Ω) :
    DGRHS.interactionEnergy μ W-C ≤
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p=>DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x := by
  apply (le_add_of_nonneg_right (show 0≤(N:ℝ)^(-2:ℤ)*(∑ i,ell (x i)) by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _=>hell _))).trans
  exact sourceRawEnergy_lower_bound μ W hW ell hell C hp hF N hN x
end DGRHS.Entropy
#check @DGRHS.Entropy.sourceRawEnergy_lower_bound
#check @DGRHS.Entropy.sourceRawEnergy_uniform_lower_bound
#print axioms DGRHS.Entropy.sourceRawEnergy_lower_bound
#print axioms DGRHS.Entropy.sourceRawEnergy_uniform_lower_bound
