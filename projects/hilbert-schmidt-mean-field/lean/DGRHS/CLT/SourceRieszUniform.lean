/- Original positive-Riesz uniform modulated partition bound, under the
actual product law, with source one-body correction and all moments derived. -/
import DGRHS.CLT.SourceRieszWeight
noncomputable section
open MeasureTheory
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
 theorem sourceRieszPartition_uniform {ι : Type u} [Fintype ι]
    (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    ∃ C : ℝ,0 < C ∧ ∀ N,1 ≤ N →
      Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
        Real.exp (-β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ ι,
        Real.exp (-β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)
          ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  obtain ⟨hF,C,hC⟩ := sourceRieszWeight_uniform s β hs hβ ha ρ M hM hρ
  refine ⟨max C 1,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _),?_⟩
  intro N hN
  simp_rw [sourceCanonicalModulatedEnergy_exponent _ _ _ _ (show 0 < N by omega)]
  exact ⟨(hC N).1,((hC N).2).trans (le_max_left _ _)⟩
end DGRHS.CLT
#print axioms DGRHS.CLT.sourceRieszPartition_uniform
#check @DGRHS.CLT.sourceRieszPartition_uniform
