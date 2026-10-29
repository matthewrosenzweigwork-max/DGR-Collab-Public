import DGRHS.Concentration.SourcePhysicalRate
import DGRHS.Kernel.MeanZeroDeterminant

/-! Genuine regularized product for any SAME actual positive centered-kernel
mean-zero eigenbasis. Compactness/Hilbert-Schmidt square summability and actual
nonzero spectral multiplicities are derived by native checked operator lemmas.
No desired product or independently selected favorable spectrum is a premise. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.SourceRepulsiveRieszRate
universe u
variable {S : Type u} [MeasurableSpace S] [MeasurableSpace.CountablyGenerated S]
    {μ : Measure S} [IsProbabilityMeasure μ]

lemma hasProd_actual_meanZero_spectrum (h : S×S→ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
    (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
    (hpos : ∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v))
    {κ : Type u} (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ))
    (he : ∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i)=eig i • e i)
    (β : ℝ) (hβ : 0≤β) :
    HasProd (fun i=>(1+β*eig i)*Real.exp (-(β*eig i))) (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)) := by
  obtain ⟨ι,a,b,_,hb⟩ := DGRHS.Kernel.exists_integralOperator_eigenbasis h hh hs
  have ha : ∀ i,0≤a i := by
    intro i
    have hp := hpos (b i)
    rw [hb,real_inner_smul_right,real_inner_self_eq_norm_sq,b.orthonormal.1 i,one_pow,mul_one] at hp
    exact hp
  have hm : ∀ i,0<1+β*a i := fun i=>by nlinarith [mul_nonneg hβ (ha i)]
  obtain ⟨hp,heq,_⟩ := DGRHS.Kernel.regularizedDet_full_eq_meanZero h hh hs hc a b hb eig e he β hm
  rw [heq] at hp
  exact hp
end DGRHS.SourceRepulsiveRieszRate
#check @DGRHS.SourceRepulsiveRieszRate.hasProd_actual_meanZero_spectrum
#print axioms DGRHS.SourceRepulsiveRieszRate.hasProd_actual_meanZero_spectrum
