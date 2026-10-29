/- Original positive-particle canonical identification plus verified empty
product convention. No limiting theorem or law equality is a hypothesis. -/
import DGRHS.CLT.SourceEquilibriumPhysical
import DGRHS.CLT.EquilibriumZeroParticle
noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
lemma sourceLog_equilibrium_law_allN (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (V : EuclideanSpace ℝ ι → ℝ)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -(β : ℝ)*
      (V x+DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)) x))=
      gaussianRieszDensityMeasure ρ) (N : ℕ) :
    sourceLogSingularGibbs β ρ N=canonicalSingularLaw volume
      (fun a b => logPhysicalPair (a,b)) V (β : ℝ) N := by
  by_cases hz : N=0
  · subst N
    rw [sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair 0,
      ←sourceEnergyTilt_eq _ _ _ (β : ℝ) 0,canonicalSingularLaw_zero]
    norm_num only [Nat.cast_zero]
    exact sourceEnergyTilt_zero (volume : Measure (EuclideanSpace ℝ ι))
      (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
      (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
      (β : ℝ)
  · exact (sourceLog_equilibrium_canonical β hβ hd ρ M hM hρ hpair V hEL N
      (Nat.one_le_iff_ne_zero.mpr hz)).2.2.2
lemma sourceRiesz_equilibrium_law_allN (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (V : EuclideanSpace ℝ ι → ℝ)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -β*
      (V x+DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => gaussianRieszPhysicalPair s (a,b)) x))=gaussianRieszDensityMeasure ρ) (N : ℕ) :
    sourceRieszSingularGibbs s β ρ N=canonicalSingularLaw volume
      (fun a b => gaussianRieszPhysicalPair s (a,b)) V β N := by
  by_cases hz : N=0
  · subst N
    rw [sourceRieszSingularGibbs_eq s β hs hβ.le ha ρ M hM hρ 0,
      ←sourceEnergyTilt_eq _ _ _ β 0,canonicalSingularLaw_zero]
    norm_num only [Nat.cast_zero]
    exact sourceEnergyTilt_zero (volume : Measure (EuclideanSpace ℝ ι))
      (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => gaussianRieszPhysicalPair s (a,b)))
      (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => gaussianRieszPhysicalPair s (a,b))) β
  · exact (sourceRiesz_equilibrium_canonical s β hs hβ ha ρ M hM hρ V hEL N
      (Nat.one_le_iff_ne_zero.mpr hz)).2.2.2
end DGRHS.CLT
#check @DGRHS.CLT.sourceLog_equilibrium_law_allN
#check @DGRHS.CLT.sourceRiesz_equilibrium_law_allN
#print axioms DGRHS.CLT.sourceLog_equilibrium_law_allN
#print axioms DGRHS.CLT.sourceRiesz_equilibrium_law_allN
