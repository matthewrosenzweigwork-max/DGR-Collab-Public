/- Source TeX 380–387: the raw ordered-pair splitting and centered FNdef
are identical for positive N. This finite identity does not remove spatial
collisions; singular physical use still needs its properness/null-set bridge. -/
import DGRHS.CLT.SourceEnergyTilt
import DGRHS.Kernel.Centering
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.CLT

lemma offDiag_sum_fst {S : Type*} (N : ℕ) (F : S → ℝ) (x : Fin N → S) :
    (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,F (x p.1)) =
      ((N : ℝ)-1)*∑ i : Fin N,F (x i) := by
  classical
  have hs := Finset.sum_union (f := fun p : Fin N × Fin N => F (x p.1))
    (Finset.disjoint_diag_offDiag (Finset.univ : Finset (Fin N)))
  rw [Finset.diag_union_offDiag,Finset.sum_product] at hs
  have hd : (∑ p ∈ (Finset.univ : Finset (Fin N)).diag,F (x p.1)) =
      ∑ i : Fin N,F (x i) := by simp [Finset.diag]
  have hp : (∑ i : Fin N,∑ _j : Fin N,F (x i)) =
      (N : ℝ)*∑ i : Fin N,F (x i) := by simp [←Finset.mul_sum]
  rw [hd,hp] at hs
  linarith

lemma offDiag_sum_snd {S : Type*} (N : ℕ) (F : S → ℝ) (x : Fin N → S) :
    (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,F (x p.2)) =
      ((N : ℝ)-1)*∑ i : Fin N,F (x i) := by
  classical
  have hs := Finset.sum_union (f := fun p : Fin N × Fin N => F (x p.2))
    (Finset.disjoint_diag_offDiag (Finset.univ : Finset (Fin N)))
  rw [Finset.diag_union_offDiag,Finset.sum_product] at hs
  have hd : (∑ p ∈ (Finset.univ : Finset (Fin N)).diag,F (x p.2)) =
      ∑ i : Fin N,F (x i) := by simp [Finset.diag]
  have hp : (∑ _i : Fin N,∑ j : Fin N,F (x j)) =
      (N : ℝ)*∑ i : Fin N,F (x i) := by simp
  rw [hd,hp] at hs
  linarith

lemma offDiagonalSum_centered {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (W : S → S → ℝ) (hW : ∀ x y,W x y=W y x)
    (N : ℕ) (x : Fin N → S) :
    DGRHS.CanonicalVariance.offDiagonalSum
      (fun p => DGRHS.centeredKernel μ W p.1 p.2) x =
      DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) x -
        2*((N : ℝ)-1)*(∑ i : Fin N,DGRHS.potential μ W (x i)) +
        2*DGRHS.interactionEnergy μ W*(N : ℝ)*((N : ℝ)-1) := by
  classical
  have hc := offDiag_sum_fst N (fun _ : S => (1 : ℝ)) x
  have hn : (∑ _p ∈ (Finset.univ : Finset (Fin N)).offDiag,(1 : ℝ)) =
      (N : ℝ)*((N : ℝ)-1) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      mul_comm] using hc
  unfold DGRHS.CanonicalVariance.offDiagonalSum DGRHS.centeredKernel
  simp only [DGRHS.secondPotential_eq_potential μ W hW,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [offDiag_sum_fst,offDiag_sum_snd]
  have hconst : (∑ _p ∈ (Finset.univ : Finset (Fin N)).offDiag,
      ∫ z,W z.1 z.2 ∂μ.prod μ) =
      (∫ z,W z.1 z.2 ∂μ.prod μ)*((N : ℝ)*((N : ℝ)-1)) := by
    rw [←hn,Finset.mul_sum]
    simp
  rw [hconst]
  dsimp [DGRHS.interactionEnergy,Function.uncurry]
  ring

theorem sourceCanonicalModulatedEnergy_raw {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (W : S → S → ℝ) (hW : ∀ x y,W x y=W y x)
    (N : ℕ) (hN : 0 < N) (x : Fin N → S) :
    sourceCanonicalModulatedEnergy
      (fun p => DGRHS.centeredKernel μ W p.1 p.2)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x =
      (2*(N : ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) x -
        (N : ℝ)⁻¹*(∑ i : Fin N,DGRHS.potential μ W (x i)) +
        DGRHS.interactionEnergy μ W := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [sourceCanonicalModulatedEnergy_FNdef,offDiagonalSum_centered μ W hW]
  field_simp
  <;> ring

end DGRHS.CLT
#check @DGRHS.CLT.offDiagonalSum_centered
#print axioms DGRHS.CLT.offDiagonalSum_centered
#check @DGRHS.CLT.sourceCanonicalModulatedEnergy_raw
#print axioms DGRHS.CLT.sourceCanonicalModulatedEnergy_raw
