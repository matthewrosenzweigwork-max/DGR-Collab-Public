import DGRHS.Commutator.SourceRieszOriginalGibbsConstant
import DGRHS.CLT.SourceRieszSingularIdentification

/-! Standalone Jensen lower bound for the positive-Riesz modulated partition function
(source eq. `eq:KlowerJensen`, TeX 432-436):
`K_{N,β}(μ) ≥ exp(-β N E_{μ^{⊗N}}[F_N(X_N,μ)]) = exp(β I_μ)`,
for `0 < s < d/2`, `μ` a probability density bounded by `M`, `β ≥ 0`, `N ≥ 1`.
No integrability premise and no import of the Riesz CLT rate theorem: the
integrability of the exponential weight is derived from the checked uniform
partition moment, and the Jensen step is the checked affine-partition lower bound
(`sourceAffinePartition_lower`, via `sourceRieszLocalParticleWeight_jensen_original`).
The statements are given for the particle form of the exponent, for the physical
canonical partition, and for the literal collision-zero `ENNReal` normalizer
`sourceRieszSingularPartition`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Jensen lower bound, particle form: `exp (β I_μ) ≤ ∫ exp(-β N F_N) dμ^{⊗N}`, with
`I_μ = interactionEnergy μ W`, `W = ‖x-y‖^{-s}/s`. -/
theorem sourceRieszJensen_lower_particle (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (β * DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
      (fun a b : E => gaussianRieszPhysicalPair s (a, b))) ≤
    ∫ ω, Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ) := by
  obtain ⟨C, _, hC⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ hd ρ M hM hρ
  exact sourceRieszLocalParticleWeight_jensen_original s β hs hd ρ M hM hρ N hN (hC N hN).1

/-- Jensen lower bound for the literal collision-zero Riesz normalizer
`K_{N,β}(μ) = ∫⁻ e^{-β N F_N} 1_{no collision} dμ^{⊗N}` (real part). -/
theorem sourceRieszJensen_singularPartition (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (β * DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
      (fun a b : E => gaussianRieszPhysicalPair s (a, b))) ≤
    (DGRHS.CLT.sourceRieszSingularPartition s β ρ N).toReal := by
  have ha : 0 < (Fintype.card ι : ℝ) / 2 - s := by linarith
  have hnonneg : 0 ≤ DGRHS.Concentration.physicalRieszSourcePartition s β ρ N :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  rw [DGRHS.CLT.sourceRieszSingularPartition_eq_integral s β hs hβ ha ρ M hM hρ N,
    ENNReal.toReal_ofReal hnonneg]
  exact sourceRieszJensen_lower_particle s β hs hβ hd ρ M hM hρ N hN

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszJensen_lower_particle
#print axioms DGRHS.Commutator.sourceRieszJensen_lower_particle
#check @DGRHS.Commutator.sourceRieszJensen_singularPartition
#print axioms DGRHS.Commutator.sourceRieszJensen_singularPartition
