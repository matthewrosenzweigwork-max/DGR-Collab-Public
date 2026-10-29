/- Literal positive-Riesz singular Boltzmann weight and partition.
For beta>0 collisions of unequal labels have weight zero; beta=0 has weight
one. Density and positive dimension derive actual iid collision-nullness.
The original uniform bound supplies all proper integrals, not a new premise. -/
import DGRHS.CLT.SourceRieszUniform
import DGRHS.CLT.SourceRieszPartition
import DGRHS.CLT.SourceRawEnergy
import DGRHS.Gaussian.GaussianRieszRemainder
import DGRHS.Decoupling.Product
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.CLT
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sourceRieszSingularWeight (s β : ℝ) (ρ : EuclideanSpace ℝ ι → ℝ)
    (N : ℕ) (x : Fin N → EuclideanSpace ℝ ι) : ℝ≥0∞ := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
  exact if β=0 then 1 else
    if ∀ i j : Fin N,i≠j → x i≠x j then
      ENNReal.ofReal (Real.exp (-β*(N:ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
    else 0

def sourceRieszSingularPartition (s β : ℝ) (ρ : EuclideanSpace ℝ ι → ℝ)
    (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x,sourceRieszSingularWeight s β ρ N x
    ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)

lemma density_iid_collision_free (ρ : EuclideanSpace ℝ ι → ℝ)
    [Nonempty ι] [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (N : ℕ) :
    ∀ᵐ x : Fin N → EuclideanSpace ℝ ι
      ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ),
      ∀ i j : Fin N,i≠j → x i≠x j := by
  classical
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall fun x h => (h hij).elim
  · exact (DGRHS.Decoupling.pair_eval_measurePreserving
      (gaussianRieszDensityMeasure ρ) i j hij).quasiMeasurePreserving.ae
      (ae_gaussianRieszDensity_pair_ne ρ) |>.mono (fun x hx _ => hx)

theorem sourceRieszSingularWeight_ae (s β : ℝ) (hs : 0<s)
    (ha : 0<(Fintype.card ι:ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
    sourceRieszSingularWeight s β ρ N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => ENNReal.ofReal (Real.exp (-β*(N:ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))) := by
  have hc : 0<Fintype.card ι := by
    exact_mod_cast (show (0:ℝ)<(Fintype.card ι:ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  filter_upwards [density_iid_collision_free ρ N] with x hx
  by_cases hb : β=0
  · simp [sourceRieszSingularWeight,hb]
  · simp only [sourceRieszSingularWeight,if_neg hb,if_pos hx]

theorem sourceRieszSingularPartition_uniform (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (ha : 0<(Fintype.card ι:ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    ∃ C : ℝ,0<C ∧ ∀ N,1≤N →
      sourceRieszSingularPartition s β ρ N≤ENNReal.ofReal C ∧
      sourceRieszSingularPartition s β ρ N<∞ := by
  obtain ⟨C,hC,hU⟩ := sourceRieszPartition_uniform s β hs hβ ha ρ M hM hρ
  refine ⟨C,hC,?_⟩
  intro N hN
  obtain ⟨hi,hb⟩ := hU N hN
  have he : sourceRieszSingularPartition s β ρ N =
      ENNReal.ofReal (∫ x : Fin N → EuclideanSpace ℝ ι,
        Real.exp (-β*(N:ℝ)*sourceCanonicalModulatedEnergy
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
          (DGRHS.potential (gaussianRieszDensityMeasure ρ)
            (fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)))
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
            (fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y))) N x)
        ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) := by
    unfold sourceRieszSingularPartition
    rw [lintegral_congr_ae (sourceRieszSingularWeight_ae s β hs ha ρ N)]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm
  rw [he]
  exact ⟨ENNReal.ofReal_le_ofReal hb,ENNReal.ofReal_lt_top⟩

end DGRHS.CLT
#check @DGRHS.CLT.sourceRieszSingularWeight_ae
#print axioms DGRHS.CLT.density_iid_collision_free
#print axioms DGRHS.CLT.sourceRieszSingularWeight_ae
#check @DGRHS.CLT.sourceRieszSingularPartition_uniform
#print axioms DGRHS.CLT.sourceRieszSingularPartition_uniform
