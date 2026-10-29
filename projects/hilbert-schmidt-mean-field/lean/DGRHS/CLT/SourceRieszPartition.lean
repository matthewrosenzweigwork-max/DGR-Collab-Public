/- Literal positive-Riesz source partition limit with all physical inputs
constructed. Source potential/half energy gives the exp(beta*I) prefactor.
This positive branch is not a logarithmic or whole-paper completion claim. -/
import DGRHS.CLT.SourceRieszKernelData
import DGRHS.CLT.SourceMeanZeroPartition
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
 theorem exists_sourceRieszPartitionLimit {ι : Type u} [Fintype ι]
    (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ
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
  let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  let hh := memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ
  obtain ⟨hSym,hCan,hPos⟩ := sourceRieszKernel_properties s hs ha ρ M hM hρ
  obtain ⟨κ,eig,e,hκ,he,hFactory⟩ := exists_sourceMeanZeroPartitionLimit h hh hSym hCan hPos
  obtain ⟨hF,C,hC⟩ := sourceRieszWeight_higher s β 2 hs hβ (by norm_num) ha ρ M hM hρ
  obtain ⟨hD,hProd,hLimit⟩ := hFactory F hF I β 2 C hβ (by norm_num)
    (fun N => (hC N).1) (fun N => (hC N).2)
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num)
  have hMean : (∫ x,F x ∂μ)=2*I := DGRHS.integral_potential μ W hW
  have hAffine : β*(∫ x,F x ∂μ)-β*I=β*I := by rw [hMean];ring
  rw [hAffine] at hLimit
  obtain ⟨_,C1,hC1⟩ := sourceRieszWeight_uniform s β hs hβ ha ρ M hM hρ
  exact ⟨hSym,hCan,κ,eig,e,hκ,he,hD,hProd,(fun N => (hC1 N).1),
    sourceEnergy_partition_tendsto h F I β _ hLimit⟩
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_sourceRieszPartitionLimit
#check @DGRHS.CLT.exists_sourceRieszPartitionLimit
