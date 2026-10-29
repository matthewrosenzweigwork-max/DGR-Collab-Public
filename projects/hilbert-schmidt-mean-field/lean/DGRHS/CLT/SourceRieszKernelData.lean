/- Actual full source kernel hypotheses from bounded-density physical data. -/
import DGRHS.CLT.SourceRieszWeight
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
 theorem sourceRieszKernel_properties {ι : Type u} [Fintype ι]
    (s : ℝ) (hs : 0 < s) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let hh := memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ
    (∀ᵐ p ∂μ.prod μ,h p.swap=h p) ∧
    (∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0) ∧
    (∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) := by
  let μ := gaussianRieszDensityMeasure ρ
  refine ⟨Filter.Eventually.of_forall (fun p => ?_),?_,?_⟩
  · exact DGRHS.centeredKernel_symmetric μ (fun a b => gaussianRieszPhysicalPair s (a,b))
      (fun a b => by simp only [gaussianRieszPhysicalPair,norm_sub_rev]) p.2 p.1
  · exact DGRHS.integral_centeredKernel_right μ (fun a b => gaussianRieszPhysicalPair s (a,b))
      ((memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num))
  · exact gaussianRieszPhysicalOperator_positive s hs ha ρ M hM hρ
end DGRHS.CLT
#print axioms DGRHS.CLT.sourceRieszKernel_properties
#check @DGRHS.CLT.sourceRieszKernel_properties
