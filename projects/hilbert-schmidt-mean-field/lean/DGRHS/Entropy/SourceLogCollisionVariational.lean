/- Literal collision-infinite REPULSIVE energy and all probability laws.
The original density makes the excluded collision set null for iid samples;
infinite entropy deals with competitors charging that set without coercion. -/
import DGRHS.Entropy.SourceLogExtendedVariational
import DGRHS.Entropy.NullSingularEnergy
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

def sourceLogCollisionFreeEnergy (β : ℝ≥0) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (N : ℕ) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) : EReal :=
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N=>μ)
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  singularBoundedEnergyFreeEnergy P ν E (sourceLogEnergyFloor ρ M) ((β:ℝ)*(N:ℝ))
    (fun x=>∀ i j : Fin N,i≠j → x i≠x j)

theorem sourceLogCollisionFreeEnergy_eq (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (M : ℝ)
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν] :
    sourceLogCollisionFreeEnergy β ρ M N ν=sourceLogExtendedFreeEnergy β ρ M N ν := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hd)
  exact singularBoundedEnergyFreeEnergy_eq _ _ _ _ _
    (mul_pos hβ (by exact_mod_cast (by omega : 0<N))) _ (density_iid_collision_free ρ N)

def sourceLogCollisionFreeEnergyValues (β : ℝ≥0) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (N : ℕ) : Set EReal :=
  {r | ∃ ν : Measure (Fin N→EuclideanSpace ℝ ι), IsProbabilityMeasure ν ∧
    r=sourceLogCollisionFreeEnergy β ρ M N ν}

theorem sourceLogCollisionFreeEnergyValues_eq (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (M : ℝ) (N : ℕ) (hN : 1≤N) :
    sourceLogCollisionFreeEnergyValues β ρ M N=sourceLogExtendedFreeEnergyValues β ρ M N := by
  ext r
  constructor <;> rintro ⟨ν,hν,hr⟩
  · letI := hν
    exact ⟨ν,hν,hr.trans (sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν)⟩
  · letI := hν
    exact ⟨ν,hν,hr.trans (sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν).symm⟩

theorem sourceLogCollisionFreeEnergy_inf (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) :
    sInf (sourceLogCollisionFreeEnergyValues β ρ M N)=
      ((-Real.log (sourceLogSingularPartition β ρ N).toReal/((β:ℝ)*(N:ℝ)) : ℝ):EReal) := by
  rw [sourceLogCollisionFreeEnergyValues_eq β hβ hd ρ M N hN]
  exact sourceLogExtendedFreeEnergy_inf β hβ hd ρ M hM hρ hpair N hN
theorem sourceLogCollisionFreeEnergy_isLeast (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) :
    IsLeast (sourceLogCollisionFreeEnergyValues β ρ M N)
      ((-Real.log (sourceLogSingularPartition β ρ N).toReal/((β:ℝ)*(N:ℝ)) : ℝ):EReal) := by
  rw [sourceLogCollisionFreeEnergyValues_eq β hβ hd ρ M N hN]
  exact sourceLogExtendedFreeEnergy_isLeast β hβ hd ρ M hM hρ hpair N hN
theorem sourceLogCollisionFreeEnergy_optimizer (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) :
    IsProbabilityMeasure (sourceLogSingularGibbs β ρ N) ∧
      sourceLogCollisionFreeEnergy β ρ M N (sourceLogSingularGibbs β ρ N)=
        ((-Real.log (sourceLogSingularPartition β ρ N).toReal/((β:ℝ)*(N:ℝ)) : ℝ):EReal) := by
  have h := sourceLogExtendedFreeEnergy_optimizer β hβ hd ρ M hM hρ hpair N hN
  letI := h.1
  refine ⟨h.1,?_⟩
  rw [sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN (sourceLogSingularGibbs β ρ N)]
  exact h.2

end DGRHS.Entropy
#check @DGRHS.Entropy.sourceLogCollisionFreeEnergy_eq
#print axioms DGRHS.Entropy.sourceLogCollisionFreeEnergy_eq
#print axioms DGRHS.Entropy.sourceLogCollisionFreeEnergyValues_eq
#check @DGRHS.Entropy.sourceLogCollisionFreeEnergy_inf
#print axioms DGRHS.Entropy.sourceLogCollisionFreeEnergy_inf

#check @DGRHS.Entropy.sourceLogCollisionFreeEnergy_isLeast
#print axioms DGRHS.Entropy.sourceLogCollisionFreeEnergy_isLeast
#check @DGRHS.Entropy.sourceLogCollisionFreeEnergy_optimizer
#print axioms DGRHS.Entropy.sourceLogCollisionFreeEnergy_optimizer
