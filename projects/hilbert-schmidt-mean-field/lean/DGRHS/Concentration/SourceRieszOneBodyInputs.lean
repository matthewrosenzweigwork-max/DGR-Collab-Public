/- Uniform moment inputs for the positive-Riesz one-body comparison. The
canonical moment is used at 2*β, so the normalized off-diagonal exponent has
the exact -β normalization required by sourceAffinePartition_comparison. -/
import DGRHS.Concentration.SourcePhysicalRate
import DGRHS.CLT.SourceWeightCorrection
import DGRHS.Gaussian.GaussianRieszCenteredComparison

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Concentration
universe u
open DGRHS.Gaussian

/-- Derive, uniformly in particle number, the two doubled-exponential moment
inputs used by the generic affine one-body comparison for the physical Riesz
kernel. The one-body potential `F` and its AE upper bound are left in the
source-facing hypotheses, as in `lem:oneBodyReduction`. -/
theorem gaussianRieszPhysical_oneBodyComparison_inputs {ι : Type u} [Fintype ι]
    (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : MemLp F 2 (gaussianRieszDensityMeasure ρ))
    (K I : ℝ)
    (hK : ∀ᵐ x ∂gaussianRieszDensityMeasure ρ, F x ≤ K) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair (ι := ι) s)
    ∃ (_hh : MemLp h 2 (μ.prod μ)) (MS MC : ℝ),
      (∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp
          (2 * DGRHS.CLT.sourceParticleExponent h F I β N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        (∫ x : Fin N → EuclideanSpace ℝ ι, Real.exp
          (2 * DGRHS.CLT.sourceParticleExponent h F I β N x)
          ∂Measure.pi (fun _ : Fin N => μ)) ≤ MS) ∧
      (∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp
          (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        (∫ x : Fin N → EuclideanSpace ℝ ι, Real.exp
          (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
          ∂Measure.pi (fun _ : Fin N => μ)) ≤ MC) := by
  let μ := gaussianRieszDensityMeasure ρ
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair (ι := ι) s)
  have hh : MemLp h 2 (μ.prod μ) := by
    simpa [h, μ] using
      (memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ)
  obtain ⟨MC, hMC⟩ :=
    gaussianRieszPhysical_uniform_exponential s (2 * β) hs (by positivity) ha ρ M hM hρ
  have hC (N : ℕ) (hN : 1 ≤ N) :
      Integrable (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp
        (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ ι, Real.exp
        (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ MC := by
    have he :
        (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp
          ((2 * β) * iidNegativeStatistic N h x)) =
        (fun x => Real.exp
          (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
      funext x
      rw [iidNegativeStatistic_exponent_eq_normalized]
      congr 1
      ring
    have hbound := hMC N hN
    change Integrable (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp
      ((2 * β) * iidNegativeStatistic N h x)) (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ ι, Real.exp
        ((2 * β) * iidNegativeStatistic N h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ MC at hbound
    rw [he] at hbound
    exact hbound
  let MS := max (Real.exp ((2 * β) * (K - I)) * MC)
    (Real.exp (-(2 * β) * I))
  have hS := DGRHS.CLT.sourceWeight_of_canonical_moments h F
    (hF.integrable (by norm_num)) K hK I (2 * β) (by positivity) MC
    (fun N hN => by
      convert (hC N hN).1 using 1
      funext x
      congr 1
      ring)
    (fun N hN => by
      convert (hC N hN).2 using 1
      congr 1
      funext x
      congr 1
      ring)
  have hS' (N : ℕ) :
      Integrable (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp
        (2 * DGRHS.CLT.sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ ι, Real.exp
        (2 * DGRHS.CLT.sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ MS := by
    simpa only [DGRHS.CLT.sourceParticleExponent_mul_parameter] using hS N
  exact ⟨hh, MS, MC, fun N hN => hS' N, hC⟩

end DGRHS.Concentration

#print axioms DGRHS.Concentration.gaussianRieszPhysical_oneBodyComparison_inputs
#check @DGRHS.Concentration.gaussianRieszPhysical_oneBodyComparison_inputs
