/- Literal ENNReal positive-Riesz normalizer. Collision-free iid equality,
properness and positivity precede conversion to the real source normalizer.
The original 0<s<d/2 and bounded probability density are the only data. -/
import DGRHS.CLT.SourceRieszRawWeight
import DGRHS.CLT.SourceEnergyTilt
import DGRHS.Concentration.SourceRieszRate
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι]

lemma sourceRieszEnergyWeight_integrable (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    Integrable (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp (-β*(N:ℝ)*
      sourceCanonicalModulatedEnergy (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
      (Measure.pi (fun _ : Fin N => μ)) := by
  dsimp only
  by_cases hn : N=0
  · subst N
    simpa only [Nat.cast_zero,mul_zero,zero_mul,Real.exp_zero] using
      (integrable_const (1:ℝ) : Integrable (fun _ : Fin 0 → EuclideanSpace ℝ ι => (1:ℝ))
        (Measure.pi (fun _ : Fin 0 => gaussianRieszDensityMeasure ρ)))
  · obtain ⟨_,_,hU⟩ := sourceRieszPartition_uniform s β hs hβ ha ρ M hM hρ
    exact (hU N (by omega)).1

lemma sourceRieszSingularPartition_eq_integral (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) :
    sourceRieszSingularPartition s β ρ N = ENNReal.ofReal (physicalRieszSourcePartition s β ρ N) := by
  have hi := sourceRieszEnergyWeight_integrable s β hs hβ ha ρ M hM hρ N
  unfold sourceRieszSingularPartition physicalRieszSourcePartition
  rw [lintegral_congr_ae (sourceRieszSingularWeight_ae s β hs ha ρ N)]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm

lemma sourceRieszSingularPartition_pos_finite (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) :
    0 < sourceRieszSingularPartition s β ρ N ∧ sourceRieszSingularPartition s β ρ N < ∞ := by
  rw [sourceRieszSingularPartition_eq_integral s β hs hβ ha ρ M hM hρ N]
  refine ⟨ENNReal.ofReal_pos.mpr ?_, ENNReal.ofReal_lt_top⟩
  exact integral_exp_pos (sourceRieszEnergyWeight_integrable s β hs hβ ha ρ M hM hρ N)

end DGRHS.CLT
#check @DGRHS.CLT.sourceRieszEnergyWeight_integrable
#check @DGRHS.CLT.sourceRieszSingularPartition_eq_integral
#check @DGRHS.CLT.sourceRieszSingularPartition_pos_finite
#print axioms DGRHS.CLT.sourceRieszEnergyWeight_integrable
#print axioms DGRHS.CLT.sourceRieszSingularPartition_eq_integral
#print axioms DGRHS.CLT.sourceRieszSingularPartition_pos_finite
