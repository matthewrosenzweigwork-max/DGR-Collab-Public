/- Original repulsive logarithmic uniform modulated partition bound:
source thm:partitionFunctionBound(i), eq:logEnergyAssumption and eq:FNdef.
No quantitative-limit tail or centered-L2 assumption is introduced. -/
import DGRHS.Gaussian.GaussianLogSourceMoment
import DGRHS.CLT.IidCanonicalNormalization
import DGRHS.CLT.SourceRawEnergy
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.CLT
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sourceLogMomentExponent_eq (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (β : ℝ) (N : ℕ) (x : Fin N→EuclideanSpace ℝ ι) :
    logPhysicalMomentExponent μ β N x = sourceParticleExponent
      (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ (fun a b=>logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy μ (fun a b=>logPhysicalPair (a,b))) β N x := by
  unfold logPhysicalMomentExponent sourceParticleExponent
  rw [iidCanonicalExponent_eq]
  unfold logPhysicalPotential DGRHS.potential DGRHS.interactionEnergy
  simp only [div_eq_mul_inv]
  ring

theorem sourceLogPartition_uniform (β : ℝ) (hβ : 0≤β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    ∃ C : ℝ,0<C ∧ ∀ N,1≤N →
      Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
        (-β*(N:ℝ)*sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
          (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
        (Measure.pi (fun _ : Fin N=>μ)) ∧
      (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
        (-β*(N:ℝ)*sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
          (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
        ∂Measure.pi (fun _ : Fin N=>μ))≤C := by
  dsimp only
  obtain ⟨C,hC⟩ := logPhysicalSource_uniform_exponential β hβ hd ρ M hM hρ hpair
  refine ⟨max C 1,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _),?_⟩
  intro N hN
  simp_rw [sourceCanonicalModulatedEnergy_exponent _ _ _ _ (show 0<N by omega)]
  have he := hC N hN
  simp_rw [sourceLogMomentExponent_eq] at he
  exact ⟨he.1,he.2.trans (le_max_left _ _)⟩
end DGRHS.CLT
#check @DGRHS.CLT.sourceLogPartition_uniform
#print axioms DGRHS.CLT.sourceLogMomentExponent_eq
#print axioms DGRHS.CLT.sourceLogPartition_uniform
