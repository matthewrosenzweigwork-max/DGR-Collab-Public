/- Original logarithmic thermal-interpolation pointwise averaging step.
Actual energy global measurability and its floor are derived from the source
kernel. All competitor laws, including infinite entropy/energy, are included.
The physical commutator and its stated pointwise bound are upstream. -/
import DGRHS.Entropy.BoundedObservablePointwise
import DGRHS.Entropy.SourceLogExtendedVariational
import DGRHS.CLT.SourceEnergyMeasurable
import DGRHS.Gaussian.GaussianLogFullPositivity
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLog_bounded_pointwise_transfer (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (a : (Fin N→EuclideanSpace ℝ ι)→ℝ) (ha : StronglyMeasurable a)
    (A : ℝ) (hA : ∀ x,|a x|≤A) (Cpw Cpt scale : ℝ) (hCpw : 0≤Cpw) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
    (∀ x,|a x|≤Cpw*((N:ℝ)*E x+Cpt*scale)) →
      Integrable a ν ∧ ((|∫ x,a x ∂ν| : ℝ):EReal)≤
        (Cpw*(N:ℝ) : ℝ)*sourceLogExtendedFreeEnergy β ρ M N ν+
        (Cpw*Cpt*scale : ℝ) := by
  dsimp only
  intro hpoint
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  have hF : StronglyMeasurable (DGRHS.potential μ W) :=
    stronglyMeasurable_logPhysicalPair.integral_prod_right'
  have hE : StronglyMeasurable E := stronglyMeasurable_sourceCanonicalModulatedEnergy _ _ _
    (stronglyMeasurable_logPhysicalCenteredPair μ) hF N
  have hfloor : ∀ x,sourceLogEnergyFloor ρ M≤E x :=
    fun x=>sourceLogEnergy_uniform_lower_bound hd ρ M hM hρ hpair N (by omega) x
  exact bounded_observable_pointwise_freeEnergy (Measure.pi (fun _ : Fin N=>μ)) ν a E ha hE A
    (sourceLogEnergyFloor ρ M) ((β:ℝ)*(N:ℝ)) (Cpw*(N:ℝ)) (Cpw*Cpt*scale) hA hfloor
    (mul_pos hβ (by exact_mod_cast (by omega : 0<N))) (mul_nonneg hCpw (Nat.cast_nonneg N))
    (fun x=>by convert hpoint x using 1 <;> ring)

end DGRHS.Entropy
#check @DGRHS.Entropy.sourceLog_bounded_pointwise_transfer
#print axioms DGRHS.Entropy.sourceLog_bounded_pointwise_transfer
