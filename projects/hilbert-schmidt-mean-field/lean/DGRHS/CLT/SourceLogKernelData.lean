/- Actual original logarithmic kernel data: physical density and first pair
log L1 only. Operator positivity is supplied by its independently owned
finite-band/L2-limit proof, not a favorable theorem premise. -/
import DGRHS.CLT.SourceLogWeight
import DGRHS.Gaussian.GaussianLogFullPositivity
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
 theorem sourceLogKernel_properties {ι : Type u} [Fintype ι]
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    (∀ᵐ z ∂μ.prod μ,h z.swap=h z) ∧
    (∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0) ∧
    (∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) := by
  let μ := gaussianRieszDensityMeasure ρ
  refine ⟨Filter.Eventually.of_forall (fun z=>?_),?_,?_⟩
  · exact DGRHS.centeredKernel_symmetric μ (fun a b=>logPhysicalPair (a,b))
      (fun a b=>by simp only [logPhysicalPair,norm_sub_rev]) z.2 z.1
  · exact DGRHS.integral_centeredKernel_right μ (fun a b=>logPhysicalPair (a,b)) hpair
  · exact logPhysicalCenteredOperator_positive hd ρ M hM hρ hpair
end DGRHS.CLT
#check @DGRHS.CLT.sourceLogKernel_properties
#print axioms DGRHS.CLT.sourceLogKernel_properties
