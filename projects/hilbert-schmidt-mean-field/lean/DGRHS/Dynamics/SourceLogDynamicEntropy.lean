/- Source lem:dynamicEntropyTransfers(i), logarithmic physical branch.
Gibbs initial data, the original free-energy Gronwall bound and the original
partition bounds imply a common finite entropy bound. Finite entropy is proved
before its real value is used. No desired entropy estimate is a premise. -/
import DGRHS.Entropy.SourceLogFiniteEnergyDomain
import DGRHS.Entropy.SourceLogPartitionBounds
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem sourceLog_dynamic_entropy_from_gronwall (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ₀ ρ : EuclideanSpace ℝ ι→ℝ)
    (M₀ M : ℝ) (hM₀ : 0≤M₀) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ₀)]
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ₀ : ∀ᵐ x ∂volume,ρ₀ x≤M₀) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hp₀ : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ₀).prod (gaussianRieszDensityMeasure ρ₀)))
    (hp : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (A B : ℝ)
    (hE : sourceLogCollisionFreeEnergy β ρ M N ν≤
      (A:EReal)*sourceLogCollisionFreeEnergy β ρ₀ M₀ N (sourceLogSingularGibbs β ρ₀ N)+
        (B/(N:ℝ):ℝ)) :
    klDiv ν (sourceLogSingularGibbs β ρ N)≠∞ ∧
      (klDiv ν (sourceLogSingularGibbs β ρ N)).toReal≤
        -A*Real.log (sourceLogSingularPartition β ρ₀ N).toReal+
          (β:ℝ)*B+Real.log (sourceLogSingularPartition β ρ N).toReal := by
  have hopt := (sourceLogCollisionFreeEnergy_optimizer β hβ hd ρ₀ M₀ hM₀ hρ₀ hp₀ N hN).2
  rw [hopt,←EReal.coe_mul,←EReal.coe_add] at hE
  have hKL := sourceLogCollisionFreeEnergy_finite_gibbsKL β hβ hd ρ M hM hρ hp N hN ν _ hE
  rw [sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν,
    sourceLogExtendedFreeEnergy_rewrite β hβ hd ρ M hM hρ hp N hN ν,
    ←EReal.coe_ennreal_toReal hKL,←EReal.coe_mul,←EReal.coe_sub,EReal.coe_le_coe_iff] at hE
  have hnr : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have hbr : 0<(β:ℝ)*(N:ℝ) := mul_pos hβ hnr
  have hs := mul_le_mul_of_nonneg_right hE hbr.le
  have hl : ((klDiv ν (sourceLogSingularGibbs β ρ N)).toReal*((β:ℝ)*(N:ℝ))⁻¹-
      Real.log (sourceLogSingularPartition β ρ N).toReal/((β:ℝ)*(N:ℝ)))*((β:ℝ)*(N:ℝ))=
      (klDiv ν (sourceLogSingularGibbs β ρ N)).toReal-Real.log (sourceLogSingularPartition β ρ N).toReal := by
    field_simp [hbr.ne']
  have hr : (A*(-Real.log (sourceLogSingularPartition β ρ₀ N).toReal/((β:ℝ)*(N:ℝ)))+
      B/(N:ℝ))*((β:ℝ)*(N:ℝ))=
      -A*Real.log (sourceLogSingularPartition β ρ₀ N).toReal+(β:ℝ)*B := by
    field_simp [hβ.ne',hnr.ne']
    <;> ring
  rw [hl,hr] at hs
  exact ⟨hKL,by linarith⟩

theorem exists_sourceLog_dynamic_uniform_entropy (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (c C Amax Bmax : ℝ)
    (hc : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax) :
    ∃ H : ℝ,0≤H ∧ ∀ (N : ℕ),1≤N →
      ∀ (ρ₀ ρ : EuclideanSpace ℝ ι→ℝ) (M₀ M : ℝ),0≤M₀ → 0≤M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ₀)]
        [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ₀ x≤M₀) → (∀ᵐ x ∂volume,ρ x≤M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ₀).prod (gaussianRieszDensityMeasure ρ₀)) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) →
      ∀ (ν : Measure (Fin N→EuclideanSpace ℝ ι)),∀ [IsProbabilityMeasure ν],
      ∀ (A B : ℝ),0≤A → A≤Amax → B≤Bmax →
      c≤(sourceLogSingularPartition β ρ₀ N).toReal →
      (sourceLogSingularPartition β ρ N).toReal≤C →
      sourceLogCollisionFreeEnergy β ρ M N ν≤
        (A:EReal)*sourceLogCollisionFreeEnergy β ρ₀ M₀ N (sourceLogSingularGibbs β ρ₀ N)+(B/(N:ℝ):ℝ) →
      klDiv ν (sourceLogSingularGibbs β ρ N)≠∞ ∧
        (klDiv ν (sourceLogSingularGibbs β ρ N)).toReal≤H := by
  refine ⟨Amax*|Real.log c|+(β:ℝ)*Bmax+|Real.log C|,
    add_nonneg (add_nonneg (mul_nonneg hAmax (abs_nonneg _)) (mul_nonneg β.coe_nonneg hBmax)) (abs_nonneg _),?_⟩
  intro N hN ρ₀ ρ M₀ M hM₀ hM hμ₀ hμ hρ₀ hρ hp₀ hp ν hν A B hA hAA hBB hlow hcap hE
  obtain ⟨hKL,hbound⟩ := sourceLog_dynamic_entropy_from_gronwall β hβ hd ρ₀ ρ M₀ M hM₀ hM hρ₀ hρ hp₀ hp N hN ν A B hE
  have hlog₀ := Real.log_le_log hc hlow
  obtain ⟨Cpf,hCpf,hbounds⟩ := sourceLogPartition_original_bounds β hd ρ M hM hρ hp
  have hpos : 0<(sourceLogSingularPartition β ρ N).toReal :=
    lt_of_lt_of_le (Real.exp_pos _) (hbounds N hN).1
  have hlog := Real.log_le_log hpos hcap
  have h1 : -A*Real.log (sourceLogSingularPartition β ρ₀ N).toReal≤Amax*|Real.log c| := by
    calc
      _ ≤ -A*Real.log c := mul_le_mul_of_nonpos_left hlog₀ (by linarith)
      _ ≤ A*|Real.log c| := by nlinarith [neg_le_abs (Real.log c)]
      _ ≤ Amax*|Real.log c| := mul_le_mul_of_nonneg_right hAA (abs_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hBB β.coe_nonneg
  exact ⟨hKL,by linarith [le_abs_self (Real.log C)]⟩
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLog_dynamic_entropy_from_gronwall
#print axioms DGRHS.Dynamics.sourceLog_dynamic_entropy_from_gronwall
#check @DGRHS.Dynamics.exists_sourceLog_dynamic_uniform_entropy
#print axioms DGRHS.Dynamics.exists_sourceLog_dynamic_uniform_entropy
