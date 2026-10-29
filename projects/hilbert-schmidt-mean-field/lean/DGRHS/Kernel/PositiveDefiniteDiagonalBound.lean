/- Full source lem:PDdeterministicDiagonalBound for every configuration.
Unequal indices are the existing univ.offDiag particle statistic. -/
import DGRHS.Kernel.PositiveDefiniteKernelCentering
import DGRHS.CanonicalVariance.ParticleVariance
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Kernel

lemma full_sum_eq_diagonal_add_offDiagonal {Ω : Type*} (N : ℕ)
    (q : Ω→Ω→ℝ) (x : Fin N→Ω) :
    (∑ i,∑ j,q (x i) (x j))=(∑ i,q (x i) (x i))+
      DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry q) x := by
  classical
  have h := Finset.sum_union (s₁ := (Finset.univ : Finset (Fin N)).diag)
    (s₂ := (Finset.univ : Finset (Fin N)).offDiag)
    (f := fun p => q (x p.1) (x p.2)) (Finset.disjoint_diag_offDiag _)
  rw [Finset.diag_union_offDiag,Finset.sum_product] at h
  simpa [Finset.diag,Finset.sum_product,DGRHS.CanonicalVariance.offDiagonalSum,
    Function.uncurry] using h

 theorem positiveDefiniteKernel_deterministic_diagonal_bound {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω→Ω→ℝ) (hq : IsPositiveDefiniteKernel q)
    (hmeas : Measurable (Function.uncurry q)) (M : ℝ) (hcap : ∀ x,q x x≤M)
    (N : ℕ) (hN : 0<N) (x : Fin N→Ω) :
    (∀ y z,|DGRHS.centeredKernel μ q y z|≤4*M) ∧
    0 ≤ (∑ i,∑ j,DGRHS.centeredKernel μ q (x i) (x j)) ∧
    -DGRHS.CanonicalVariance.normalizedOffDiagonalSum
      (Function.uncurry (DGRHS.centeredKernel μ q)) x ≤
      (N:ℝ)⁻¹*(∑ i,DGRHS.centeredKernel μ q (x i) (x i)) ∧
    (N:ℝ)⁻¹*(∑ i,DGRHS.centeredKernel μ q (x i) (x i)) ≤
      sSup (Set.range (fun y=>DGRHS.centeredKernel μ q y y)) ∧
    sSup (Set.range (fun y=>DGRHS.centeredKernel μ q y y)) ≤ 4*M := by
  classical
  let h := DGRHS.centeredKernel μ q
  have hc : ∀ y z,|h y z|≤4*M :=
    (positiveDefiniteKernel_centered_cap μ q hq hmeas M hcap).2.2.2
  have hpd := positiveDefiniteKernel_centering μ q hq hmeas M hcap
  have hf : 0 ≤ ∑ i,∑ j,h (x i) (x j) := by
    simpa only [one_mul] using hpd.gram_nonneg N x (fun _ => 1)
  have he := full_sum_eq_diagonal_add_offDiagonal N h x
  have hsplit : -DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry h) x ≤
      ∑ i,h (x i) (x i) := by linarith
  have hnr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hs : -DGRHS.CanonicalVariance.normalizedOffDiagonalSum (Function.uncurry h) x ≤
      (N:ℝ)⁻¹*(∑ i,h (x i) (x i)) := by
    simpa only [DGRHS.CanonicalVariance.normalizedOffDiagonalSum,Fintype.card_fin,mul_neg]
      using mul_le_mul_of_nonneg_left hsplit (inv_nonneg.mpr (le_of_lt hnr))
  have hb : BddAbove (Set.range (fun y=>h y y)) := ⟨4*M,by
    rintro _ ⟨y,rfl⟩
    exact (le_abs_self _).trans (hc y y)⟩
  have havg : (N:ℝ)⁻¹*(∑ i,h (x i) (x i)) ≤ sSup (Set.range (fun y=>h y y)) := by
    have hsum : (∑ i,h (x i) (x i)) ≤ (N:ℝ)*sSup (Set.range (fun y=>h y y)) := by
      simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun i _ => le_csSup hb (Set.mem_range_self (x i)))
    have hm := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (le_of_lt hnr))
    simpa only [←mul_assoc,inv_mul_cancel₀ (ne_of_gt hnr),one_mul] using hm
  have hsup : sSup (Set.range (fun y=>h y y)) ≤ 4*M := by
    have hne : (Set.range (fun y=>h y y)).Nonempty :=
      ⟨h (x ⟨0,hN⟩) (x ⟨0,hN⟩),⟨x ⟨0,hN⟩,rfl⟩⟩
    apply csSup_le hne
    rintro _ ⟨y,rfl⟩
    exact (le_abs_self _).trans (hc y y)
  exact ⟨hc,hf,hs,havg,hsup⟩

/-- The literal source supremum formulation; finite-Gram positivity supplies
all off-diagonal boundedness from the bounded diagonal. -/
theorem positiveDefiniteKernel_original_diagonal_bound {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω→Ω→ℝ) (hq : IsPositiveDefiniteKernel q)
    (hmeas : Measurable (Function.uncurry q))
    (hb : BddAbove (Set.range (fun y=>q y y)))
    (N : ℕ) (hN : 0<N) (x : Fin N→Ω) :
    (∀ y z,|DGRHS.centeredKernel μ q y z|≤4*sSup (Set.range (fun y=>q y y))) ∧
    0 ≤ (∑ i,∑ j,DGRHS.centeredKernel μ q (x i) (x j)) ∧
    -DGRHS.CanonicalVariance.normalizedOffDiagonalSum
      (Function.uncurry (DGRHS.centeredKernel μ q)) x ≤
      (N:ℝ)⁻¹*(∑ i,DGRHS.centeredKernel μ q (x i) (x i)) ∧
    (N:ℝ)⁻¹*(∑ i,DGRHS.centeredKernel μ q (x i) (x i)) ≤
      sSup (Set.range (fun y=>DGRHS.centeredKernel μ q y y)) ∧
    sSup (Set.range (fun y=>DGRHS.centeredKernel μ q y y)) ≤
      4*sSup (Set.range (fun y=>q y y)) :=
  positiveDefiniteKernel_deterministic_diagonal_bound μ q hq hmeas
    (sSup (Set.range (fun y=>q y y))) (fun y=>le_csSup hb (Set.mem_range_self y)) N hN x
end DGRHS.Kernel
#check @DGRHS.Kernel.positiveDefiniteKernel_deterministic_diagonal_bound
#print axioms DGRHS.Kernel.full_sum_eq_diagonal_add_offDiagonal
#print axioms DGRHS.Kernel.positiveDefiniteKernel_deterministic_diagonal_bound

#check @DGRHS.Kernel.positiveDefiniteKernel_original_diagonal_bound
#print axioms DGRHS.Kernel.positiveDefiniteKernel_original_diagonal_bound
