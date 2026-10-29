/- Literal singular Riesz Gibbs law, including beta=0 and N=0.
Actual properness and collision-nullness identify its normalized density
with the physical canonical exponential tilt before a probability claim. -/
import DGRHS.CLT.SourceRieszSingularIdentification
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sourceRieszSingularGibbs (s β : ℝ) (ρ : EuclideanSpace ℝ ι → ℝ) (N : ℕ) :
    Measure (Fin N → EuclideanSpace ℝ ι) :=
  (Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)).withDensity
    (fun x => sourceRieszSingularWeight s β ρ N x/sourceRieszSingularPartition s β ρ N)

lemma sourceRieszSingularGibbs_eq (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    sourceRieszSingularGibbs s β ρ N = (Measure.pi (fun _ : Fin N => μ)).tilted
      (sourceParticleExponent (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) β N) := by
  dsimp only
  rw [←sourceEnergyTilt_eq _ _ _ β N]
  have hi := sourceRieszEnergyWeight_integrable s β hs hβ ha ρ M hM hρ N
  unfold sourceRieszSingularGibbs Measure.tilted
  apply withDensity_congr_ae
  filter_upwards [sourceRieszSingularWeight_ae s β hs ha ρ N] with x hx
  rw [hx, sourceRieszSingularPartition_eq_integral s β hs hβ ha ρ M hM hρ N]
  unfold DGRHS.Concentration.physicalRieszSourcePartition
  exact (ENNReal.ofReal_div_of_pos (integral_exp_pos hi)).symm

lemma sourceRieszSingularGibbs_probability (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) :
    IsProbabilityMeasure (sourceRieszSingularGibbs s β ρ N) := by
  rw [sourceRieszSingularGibbs_eq s β hs hβ ha ρ M hM hρ N, ←sourceEnergyTilt_eq _ _ _ β N]
  exact isProbabilityMeasure_tilted (sourceRieszEnergyWeight_integrable s β hs hβ ha ρ M hM hρ N)

end DGRHS.CLT
#check @DGRHS.CLT.sourceRieszSingularGibbs
#check @DGRHS.CLT.sourceRieszSingularGibbs_eq
#check @DGRHS.CLT.sourceRieszSingularGibbs_probability
#print axioms DGRHS.CLT.sourceRieszSingularGibbs
#print axioms DGRHS.CLT.sourceRieszSingularGibbs_eq
#print axioms DGRHS.CLT.sourceRieszSingularGibbs_probability
