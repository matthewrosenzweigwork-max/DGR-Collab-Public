/- Original positive-Riesz one-body instance: proper potential, exact mean
and all hypotheses are derived from the actual physical kernel/density. -/
import DGRHS.Concentration.SourcePhysicalAffineRate
import DGRHS.Gaussian.GaussianRieszPhysicalPotential
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.Concentration
universe u
open DGRHS.Gaussian

lemma memLp_gaussianRieszPhysicalPotential {ι : Type u} [Fintype ι]
    (s : ℝ) (hs : 0<s) (ha : 0<(Fintype.card ι:ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    MemLp (DGRHS.potential (gaussianRieszDensityMeasure ρ)
      (fun x y ↦ gaussianRieszPhysicalPair s (x,y))) 2 (gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : EuclideanSpace ℝ ι ↦ gaussianRieszPhysicalPair s (x,y)
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num)
  have hF := DGRHS.integrable_potential μ W hW
  apply (memLp_const (gaussianRieszPhysicalPotentialConstant s M ι)).of_le hF.aestronglyMeasurable
  filter_upwards [] with x
  have hb := gaussianRieszPhysicalPotential_bound s hs ha ρ M hM hρ x
  change ‖(∫ y,gaussianRieszPhysicalPair s (x,y) ∂μ)‖≤‖gaussianRieszPhysicalPotentialConstant s M ι‖
  rw [Real.norm_eq_abs,abs_of_nonneg hb.2.1,Real.norm_eq_abs]
  exact hb.2.2.trans (le_abs_self _)

def physicalRieszSourcePartition {ι : Type u} [Fintype ι]
    (s β : ℝ) (ρ : EuclideanSpace ℝ ι→ℝ) (N : ℕ) : ℝ :=
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : EuclideanSpace ℝ ι ↦ gaussianRieszPhysicalPair s (x,y)
  ∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) (DGRHS.potential μ W)
    (DGRHS.interactionEnergy μ W) N x) ∂Measure.pi (fun _ : Fin N ↦ μ)

/-- The literal physical source normalizer and its logarithm have the original
positive-Riesz rate. No proper-potential, moment, operator, determinant,
variance, Gaussian-law or rate conclusion is supplied as a premise. -/
theorem physicalRieszSource_partition_rate {ι : Type u} [Fintype ι]
    (s β : ℝ) (hs : 0<s) (hβ : 0≤β) (ha : 0<(Fintype.card ι:ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun x y : EuclideanSpace ℝ ι ↦ gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let I := DGRHS.interactionEnergy μ W
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i)=eig i•e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i) ∧
      Tendsto (physicalRieszSourcePartition s β ρ) atTop
        (𝓝 (Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) ∧
      Tendsto (fun N ↦ Real.log (physicalRieszSourcePartition s β ρ N)) atTop
        (𝓝 (β*I+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))) ∧
      ∃ C : ℝ,0≤C ∧ ∀ N,1≤N→
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
          (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h (DGRHS.potential μ W) I N x))
          (Measure.pi (fun _ : Fin N ↦ μ)) ∧
        Real.exp (β*I)≤physicalRieszSourcePartition s β ρ N ∧
        |physicalRieszSourcePartition s β ρ N-
          Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) ∧
        |Real.log (physicalRieszSourcePartition s β ρ N)-
          (β*I+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : EuclideanSpace ℝ ι ↦ gaussianRieszPhysicalPair s (x,y)
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  have hF := memLp_gaussianRieszPhysicalPotential s hs ha ρ M hM hρ
  have hK : ∀ᵐ x ∂μ,F x≤gaussianRieszPhysicalPotentialConstant s M ι :=
    Eventually.of_forall fun x ↦ (gaussianRieszPhysicalPotential_bound s hs ha ρ M hM hρ x).2.2
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num)
  have hc : β*(∫ y,F y ∂μ)-β*I=β*I := by
    rw [DGRHS.integral_potential μ W hW]
    ring
  obtain ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hT,hLog,C,hC,hRate⟩ :=
    gaussianRieszPhysical_affine_partition_rate s β hs hβ ha ρ M hM hρ
      F hF (gaussianRieszPhysicalPotentialConstant s M ι) I hK
  rw [hc] at hT hLog hRate
  have hEq (N : ℕ) (hN : 1≤N) : physicalRieszSourcePartition s β ρ N=sourceAffinePartition μ β I h F N :=
    sourceEnergy_partition_eq_affine μ β I h F N hN
  have hEv : physicalRieszSourcePartition s β ρ =ᶠ[atTop] sourceAffinePartition μ β I h F :=
    (eventually_ge_atTop 1).mono fun N hN ↦ hEq N hN
  refine ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hT.congr' hEv.symm,
    hLog.congr' (hEv.symm.mono fun N hN ↦ congrArg Real.log hN),C,hC,?_⟩
  intro N hN
  rw [hEq N hN]
  exact hRate N hN

end DGRHS.Concentration
#print axioms DGRHS.Concentration.memLp_gaussianRieszPhysicalPotential
#check @DGRHS.Concentration.memLp_gaussianRieszPhysicalPotential
#print axioms DGRHS.Concentration.physicalRieszSource_partition_rate
#check @DGRHS.Concentration.physicalRieszSource_partition_rate
