/- Actual positive-Riesz source weights. Uniform moments are derived from the
reviewed singular physical moment and proper potential; none is an input.
The exponent is the paper's affine canonical form with its actual half energy. -/
import DGRHS.CLT.IidCanonicalNormalization
import DGRHS.Gaussian.GaussianRieszFullMoment
import DGRHS.Gaussian.GaussianRieszFullPositivity
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

theorem sourceRieszWeight_uniform (s γ : ℝ) (hs : 0 < s) (hγ : 0 ≤ γ)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable F μ ∧ ∃ C : ℝ,∀ N,
      Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
        Real.exp (sourceParticleExponent h F I γ N x)) (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ ι,Real.exp (sourceParticleExponent h F I γ N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num)
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hW
  have hK : ∀ᵐ x ∂μ,F x ≤ gaussianRieszPhysicalPotentialConstant s M ι := by
    exact Filter.Eventually.of_forall (fun x =>
      (gaussianRieszPhysicalPotential_bound s hs ha ρ M hM hρ x).2.2)
  obtain ⟨C,hC⟩ := gaussianRieszPhysical_uniform_exponential s γ hs hγ ha ρ M hM hρ
  have he (N : ℕ) : (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp (γ*DGRHS.Concentration.iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-γ/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [iidCanonicalExponent_eq]
  have hProper : ∀ N,1 ≤ N → Integrable
      (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp (-γ/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    intro N hN
    have hi := (hC N hN).1
    rw [he N] at hi
    exact hi
  have hBound : ∀ N,1 ≤ N → (∫ x : Fin N → EuclideanSpace ℝ ι,
      Real.exp (-γ/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
    intro N hN
    have hb := (hC N hN).2
    rw [he N] at hb
    exact hb
  exact ⟨hF,max (Real.exp (γ*(gaussianRieszPhysicalPotentialConstant s M ι-I))*C)
    (Real.exp (-γ*I)),sourceWeight_of_canonical_moments h F hF _ hK I γ hγ C hProper hBound⟩

theorem sourceRieszWeight_higher (s β p : ℝ) (hs : 0 < s) (hβ : 0 ≤ β) (hp : 0 ≤ p)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable F μ ∧ ∃ C : ℝ,∀ N,
      Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
        Real.exp (p*sourceParticleExponent h F I β N x)) (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ ι,Real.exp (p*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  simpa only [sourceParticleExponent_mul_parameter] using
    sourceRieszWeight_uniform s (p*β) hs (mul_nonneg hp hβ) ha ρ M hM hρ
end DGRHS.CLT
#print axioms DGRHS.CLT.sourceRieszWeight_uniform
#print axioms DGRHS.CLT.sourceRieszWeight_higher
#check @DGRHS.CLT.sourceRieszWeight_higher
