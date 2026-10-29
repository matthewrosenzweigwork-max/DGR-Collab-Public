/- Literal repulsive logarithmic partition under nonnegative temperature.
Unequal labels at spatial collisions carry zero weight for beta>0; beta=0
carries one. Actual bounded-density atomlessness identifies the proper real
representative only almost everywhere under the genuine iid product law. -/
import DGRHS.CLT.SourceLogUniform
import DGRHS.CLT.SourceRieszRawWeight
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sourceLogSingularWeight (β : ℝ≥0) (ρ : EuclideanSpace ℝ ι→ℝ)
    (N : ℕ) (x : Fin N→EuclideanSpace ℝ ι) : ℝ≥0∞ := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  exact if β=0 then 1 else
    if ∀ i j : Fin N,i≠j → x i≠x j then
      ENNReal.ofReal (Real.exp (-(β:ℝ)*(N:ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ logPhysicalPair) (DGRHS.potential μ W)
        (DGRHS.interactionEnergy μ W) N x))
    else 0

def sourceLogSingularPartition (β : ℝ≥0) (ρ : EuclideanSpace ℝ ι→ℝ)
    (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x,sourceLogSingularWeight β ρ N x
    ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)

lemma sourceLogSingularWeight_ae (β : ℝ≥0) (hd : 0<(Fintype.card ι:ℝ))
    (ρ : EuclideanSpace ℝ ι→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    sourceLogSingularWeight β ρ N =ᵐ[Measure.pi (fun _ : Fin N=>μ)]
      (fun x=>ENNReal.ofReal (Real.exp (-(β:ℝ)*(N:ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ logPhysicalPair) (DGRHS.potential μ W)
        (DGRHS.interactionEnergy μ W) N x))) := by
  have hc : 0<Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  filter_upwards [density_iid_collision_free ρ N] with x hx
  by_cases hb : β=0
  · simp [sourceLogSingularWeight,hb]
  · simp only [sourceLogSingularWeight,if_neg hb,if_pos hx]

theorem sourceLogSingularPartition_uniform (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ C : ℝ,0<C ∧ ∀ N,1≤N →
      sourceLogSingularPartition β ρ N≤ENNReal.ofReal C ∧
      sourceLogSingularPartition β ρ N<∞ := by
  obtain ⟨C,hC,hU⟩ := sourceLogPartition_uniform (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair
  refine ⟨C,hC,?_⟩
  intro N hN
  obtain ⟨hi,hb⟩ := hU N hN
  have he : sourceLogSingularPartition β ρ N=ENNReal.ofReal
      (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-(β:ℝ)*(N:ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b))) N x)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by
    unfold sourceLogSingularPartition
    rw [lintegral_congr_ae (sourceLogSingularWeight_ae β hd ρ N)]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x=>(Real.exp_pos _).le)).symm
  rw [he]
  exact ⟨ENNReal.ofReal_le_ofReal hb,ENNReal.ofReal_lt_top⟩
end DGRHS.CLT
#check @DGRHS.CLT.sourceLogSingularPartition_uniform
#print axioms DGRHS.CLT.sourceLogSingularWeight_ae
#print axioms DGRHS.CLT.sourceLogSingularPartition_uniform
