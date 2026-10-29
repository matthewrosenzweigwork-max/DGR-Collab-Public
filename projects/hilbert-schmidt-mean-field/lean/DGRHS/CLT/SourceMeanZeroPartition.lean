/- The source partition normalization uses the determinant of the genuine
mean-zero restriction, derived from the actual full-source partition limit. -/
import DGRHS.CLT.SourcePartitionFactory
import DGRHS.Kernel.MeanZeroDeterminant
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem exists_sourceMeanZeroPartitionLimit [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0)
    (hpos : ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) :
    ∃ (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ j, DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e j) = eig j • e j) ∧
      ∀ (F : S → ℝ), Integrable F μ → ∀ (I β p C : ℝ), 0 ≤ β → 1 < p →
      (∀ N, Integrable (fun x : Fin N → S => Real.exp (p*sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ))) →
      (∀ N, (∫ x : Fin N → S, Real.exp (p*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) →
      0 < DGRHS.Kernel.regularizedDet (fun j => β*eig j) ∧
      HasProd (fun j => (1+β*eig j)*Real.exp (-(β*eig j)))
        (DGRHS.Kernel.regularizedDet (fun j => β*eig j)) ∧
      Tendsto (fun N => ∫ x : Fin N → S, Real.exp (sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) atTop
        (𝓝 (Real.exp (β*(∫ x,F x ∂μ)-β*I)*
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun j => β*eig j)))⁻¹)) := by
  obtain ⟨ι,a,b,f,hf,hcount,hb,hlimit⟩ := exists_originalKernelPartitionLimit h hh hs hc hpos
  obtain ⟨κ,c,e,hκ,he⟩ := DGRHS.Kernel.exists_integralOperatorOnMeanZero_eigenbasis h hh hs hc
  have hsign : ∀ i, 0 ≤ a i := by
    intro i
    have hi := hpos (b i)
    rw [hb,real_inner_smul_right,real_inner_self_eq_norm_sq,b.orthonormal.1 i,one_pow,mul_one] at hi
    exact hi
  refine ⟨κ,c,e,hκ,he,fun F hF I β p C hβ hp hm hC => ?_⟩
  have hmargin : ∀ i, 0 < 1+β*a i := fun i => by nlinarith [mul_nonneg hβ (hsign i)]
  obtain ⟨hprod,hdet,hpositive⟩ := DGRHS.Kernel.regularizedDet_full_eq_meanZero
    h hh hs hc a b hb c e he β hmargin
  rw [hdet] at hprod
  have ht := hlimit F hF I β p C hβ hp hm hC
  rw [hdet] at ht
  exact ⟨hpositive,hprod,ht⟩
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_sourceMeanZeroPartitionLimit
#check @DGRHS.CLT.exists_sourceMeanZeroPartitionLimit
