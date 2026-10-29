/- Original repulsive logarithm: a global configuration energy floor from
bounded density and first pair logarithmic L1 only, uniform in N>=1. -/
import DGRHS.Entropy.RepulsiveEnergyLowerBound
import DGRHS.Gaussian.LogPhysicalTailComparison
noncomputable section
open MeasureTheory
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLogEnergy_uniform_lower_bound
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 0<N) (x : Fin N→EuclideanSpace ℝ ι) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    DGRHS.interactionEnergy μ W-
      (gaussianRieszPhysicalPotentialConstant ((Fintype.card ι:ℝ)/4) M ι+
        logPhysicalTailIntegral μ+Real.log 2) ≤
      sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let ell := fun a : EuclideanSpace ℝ ι=>Real.log (1+‖a‖)
  let C := gaussianRieszPhysicalPotentialConstant ((Fintype.card ι:ℝ)/4) M ι+
    logPhysicalTailIntegral μ+Real.log 2
  have hsym : ∀ a b,W a b=W b a := by
    intro a b
    simp only [W,logPhysicalPair,norm_sub_rev]
  have hF : ∀ a,DGRHS.potential μ W a≤C-ell a := by
    intro a
    have h := logPhysicalPotential_tail_upper hd ρ M hM hρ hpair a
    change logPhysicalPotential μ a≤C-ell a
    dsimp only [C,ell,μ]
    linarith
  have h := sourceRawEnergy_uniform_lower_bound μ W hsym ell
    (fun a=>Real.log_nonneg (by linarith [norm_nonneg a])) C
    (fun a b=>logPhysicalPair_lower (a,b)) hF N hN x
  exact h
end DGRHS.Entropy
#check @DGRHS.Entropy.sourceLogEnergy_uniform_lower_bound
#print axioms DGRHS.Entropy.sourceLogEnergy_uniform_lower_bound
