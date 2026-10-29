/- Literal repulsive-log source partition limit with all physical inputs
constructed. Source potential/half energy gives the exp(beta*I) prefactor.
This physical logarithmic branch still requires actual compiler and protected verification. -/
import DGRHS.CLT.SourceLogKernelData
import DGRHS.CLT.SourceMeanZeroPartition
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
 theorem exists_sourceLogPartitionLimit {ι : Type u} [Fintype ι]
    (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι) => logPhysicalPair (x,y)
    let h := hoeffdingCentered μ (logPhysicalPair)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ j,DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e j)=eig j • e j) ∧
      0 < DGRHS.Kernel.regularizedDet (fun j => β*eig j) ∧
      HasProd (fun j => (1+β*eig j)*Real.exp (-(β*eig j)))
        (DGRHS.Kernel.regularizedDet (fun j => β*eig j)) ∧
      (∀ N,Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
        Real.exp (sourceParticleExponent h F I β N x)) (Measure.pi (fun _ : Fin N => μ))) ∧
      Tendsto (fun N => ∫ x : Fin N → EuclideanSpace ℝ ι,
        Real.exp (-β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)
        ∂Measure.pi (fun _ : Fin N => μ)) atTop
        (𝓝 (Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun j => β*eig j)))⁻¹)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun (x y : EuclideanSpace ℝ ι) => logPhysicalPair (x,y)
  let h := hoeffdingCentered μ (logPhysicalPair)
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  obtain ⟨hSym,hCan,hPos⟩ := sourceLogKernel_properties hd ρ M hM hρ hpair
  obtain ⟨κ,eig,e,hκ,he,hFactory⟩ := exists_sourceMeanZeroPartitionLimit h hh hSym hCan hPos
  obtain ⟨hF,C,hC⟩ := sourceLogWeight_higher β 2 hβ (by norm_num) hd ρ M hM hρ hpair
  obtain ⟨hD,hProd,hLimit⟩ := hFactory F hF I β 2 C hβ (by norm_num)
    (fun N => (hC N).1) (fun N => (hC N).2)
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    hpair
  have hMean : (∫ x,F x ∂μ)=2*I := DGRHS.integral_potential μ W hW
  have hAffine : β*(∫ x,F x ∂μ)-β*I=β*I := by rw [hMean];ring
  rw [hAffine] at hLimit
  obtain ⟨_,C1,hC1⟩ := sourceLogWeight_uniform β hβ hd ρ M hM hρ hpair
  exact ⟨hSym,hCan,κ,eig,e,hκ,he,hD,hProd,(fun N => (hC1 N).1),
    sourceEnergy_partition_tendsto h F I β _ hLimit⟩
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_sourceLogPartitionLimit
#check @DGRHS.CLT.exists_sourceLogPartitionLimit
