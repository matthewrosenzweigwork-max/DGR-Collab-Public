/- Source lem:dynamicEntropyTransfers(i)-(iii), actual logarithmic branch.
Uniform constants precede both densities, all particle numbers and test families.
Original free-energy Gronwall and partition controls imply finite entropy;
absolute commutator and empirical errors are conclusions, never premises. -/
import DGRHS.Dynamics.SourceLogDynamicEntropy
import DGRHS.Dynamics.SourceLogDynamicCommutator
import DGRHS.Dynamics.SourceLogDynamicOscillation
noncomputable section
open MeasureTheory InformationTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_dynamic_entropy_transfers
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (K : ℝ≥0) (hK : 0<(K:ℝ)) (M : ℝ) (hM : 0≤M)
    (J c C C₂ Amax Bmax L : ℝ) (hc : 0<c)
    (hAmax : 0≤Amax) (hBmax : 0≤Bmax) (hL : 0≤L) :
    ∃ H Dc Dl : ℝ,0≤H ∧ 0≤Dc ∧ 0≤Dl ∧
      ∀ (N : ℕ),1≤N → ∀ (ρ₀ ρ : EuclideanSpace ℝ ι→ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ₀)]
        [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ₀ x≤M) → (∀ᵐ x ∂volume,ρ x≤M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ₀).prod (gaussianRieszDensityMeasure ρ₀)) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) →
      -J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun x y=>logPhysicalPair (x,y)) →
      ∀ (ν : Measure (Fin N→EuclideanSpace ℝ ι)),∀ [IsProbabilityMeasure ν],
      ∀ (A B : ℝ),0≤A → A≤Amax → B≤Bmax →
      c≤(sourceLogSingularPartition β ρ₀ N).toReal →
      (sourceLogSingularPartition β ρ N).toReal≤C →
      (sourceLogSingularPartition (⟨2*(β:ℝ),by positivity⟩:ℝ≥0) ρ N).toReal≤C₂ →
      sourceLogCollisionFreeEnergy β ρ M N ν≤
        (A:EReal)*sourceLogCollisionFreeEnergy β ρ₀ M N (sourceLogSingularGibbs β ρ₀ N)+(B/(N:ℝ):ℝ) →
      klDiv ν (sourceLogSingularGibbs β ρ N)≠∞ ∧
      (klDiv ν (sourceLogSingularGibbs β ρ N)).toReal≤H ∧
      (∀ (v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι),LipschitzWith K v →
        Integrable (sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel 1 v) N) ν ∧
        (∫ x,|sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel 1 v) N x| ∂ν)≤Dc/(N:ℝ)) ∧
      ∀ (q : EuclideanSpace ℝ ι→ℝ),Measurable q →
        BddBelow (Set.range q) → BddAbove (Set.range q) →
        sSup (Set.range q)-sInf (Set.range q)≤L →
        Integrable q (gaussianRieszDensityMeasure ρ) ∧
        (∀ x,Integrable q (transportEmpiricalLaw N x)) ∧
        Integrable (fun x=>(∫ y,q y ∂transportEmpiricalLaw N x)-(∫ y,q y ∂gaussianRieszDensityMeasure ρ)) ν ∧
        (∫ x,|(∫ y,q y ∂transportEmpiricalLaw N x)-(∫ y,q y ∂gaussianRieszDensityMeasure ρ)| ∂ν)≤Dl/Real.sqrt N := by
  obtain ⟨H,hH,hentropy⟩ := exists_sourceLog_dynamic_uniform_entropy β hβ hd c C Amax Bmax hc hAmax hBmax
  obtain ⟨Dc,hDc,hcomm⟩ := exists_sourceLog_dynamic_commutator_absolute_bound β hβ hd K hK M hM J H
  obtain ⟨Dl,hDl,hlinear⟩ := exists_sourceLog_dynamic_oscillation_absolute_bound β hβ hd J H L C₂ hL
  refine ⟨H,Dc,Dl,hH,hDc,hDl,?_⟩
  intro N hN ρ₀ ρ hμ₀ hμ hρ₀ hρ hp₀ hp hI ν hν A B hA hAA hBB hlow hcap hcap₂ hE
  obtain ⟨hKL,hbound⟩ := hentropy N hN ρ₀ ρ M M hM hM hρ₀ hρ hp₀ hp ν A B hA hAA hBB hlow hcap hE
  refine ⟨hKL,hbound,?_,?_⟩
  · intro v hv
    exact hcomm v hv ρ hρ hp hI N hN ν hKL hbound
  · intro q hq hlo hup hosc
    exact hlinear ρ M hM hρ hp hI N hN hcap₂ q hq hlo hup hosc ν hKL hbound
end DGRHS.Dynamics
#check @DGRHS.Dynamics.exists_sourceLog_dynamic_entropy_transfers
#print axioms DGRHS.Dynamics.exists_sourceLog_dynamic_entropy_transfers
