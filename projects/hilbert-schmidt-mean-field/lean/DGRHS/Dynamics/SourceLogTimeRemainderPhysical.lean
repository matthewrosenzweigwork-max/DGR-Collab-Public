/- Original finiteNAdjointDuality negligible remainder, logarithmic branch.
The actual free-energy Gronwall assumption with literal initial Gibbs and
the original partition controls derive the entropy input internally.
Proper product/time integrals and the rate are conclusions. -/
import DGRHS.Dynamics.SourceLogTimeRemainder
import DGRHS.Dynamics.SourceLogDynamicEntropy
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_physical_time_commutator_remainder
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (K : ℝ≥0) (hK : 0<(K:ℝ)) (M : ℝ) (hM : 0≤M)
    (J c C Amax Bmax : ℝ) (hc : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→EuclideanSpace ℝ ι→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ x ∂volume,ρ r x≤M) →
      (∀ r∈Icc 0 T,Integrable logPhysicalPair
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) →
      (∀ r∈Icc 0 T,-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
        (fun x y=>logPhysicalPair (x,y))) →
      ∀ (v : ℝ→EuclideanSpace ℝ ι→EuclideanSpace ℝ ι),Measurable (Function.uncurry v) →
      (∀ r∈Icc 0 T,LipschitzWith K (v r)) →
      ∀ (X : ℝ→Ω→Fin N→EuclideanSpace ℝ ι),Measurable (Function.uncurry X) →
      ∀ (a b : ℝ→ℝ),(∀ r∈Icc 0 T,0≤a r) →
      (∀ r∈Icc 0 T,a r≤Amax) → (∀ r∈Icc 0 T,b r≤Bmax) →
      c≤(sourceLogSingularPartition β (ρ 0) N).toReal →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition β (ρ r) N).toReal≤C) →
      (∀ r∈Icc 0 T,sourceLogCollisionFreeEnergy β (ρ r) M N (ν.map (X r))≤
        (a r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(b r/(N:ℝ):ℝ)) →
      let A := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
        (sourceLogTransportKernel 1 (v r)) N (X r ω)
      Integrable (Function.uncurry A) ((volume.restrict (Ioc 0 T)).prod ν) ∧
      Integrable (fun ω=>(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)) ν ∧
      (∫ ω,|(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)| ∂ν)≤T*D/(2*Real.sqrt N) := by
  obtain ⟨H,hH,hentropy⟩ := exists_sourceLog_dynamic_uniform_entropy
    β hβ hd c C Amax Bmax hc hAmax hBmax
  obtain ⟨D,hD,hrem⟩ := exists_sourceLog_time_commutator_remainder β hβ hd K hK M hM J H
  refine ⟨D,hD,?_⟩
  intro T hT N hN Ω _ ν _ ρ hρm hprob hρ hp hI v hvm hv X hXm a b ha haA hbB hlow hcap hE
  have hz : (0:ℝ)∈Icc 0 T := ⟨le_rfl,hT⟩
  have hbounds : ∀ r∈Icc 0 T,klDiv (ν.map (X r)) (sourceLogSingularGibbs β (ρ r) N)≠∞ ∧
      (klDiv (ν.map (X r)) (sourceLogSingularGibbs β (ρ r) N)).toReal≤H := by
    intro r hr
    letI := hprob 0 hz
    letI := hprob r hr
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    exact hentropy N hN (ρ 0) (ρ r) M M hM hM (hρ 0 hz) (hρ r hr) (hp 0 hz) (hp r hr)
      (ν.map (X r)) (a r) (b r) (ha r hr) (haA r hr) (hbB r hr) hlow (hcap r hr) (hE r hr)
  exact hrem T hT N hN Ω ν ρ hρm hprob hρ hp hI v hvm hv X hXm
    (fun r hr=>(hbounds r hr).1) (fun r hr=>(hbounds r hr).2)
end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.exists_sourceLog_physical_time_commutator_remainder
#print axioms DGRHS.Dynamics.exists_sourceLog_physical_time_commutator_remainder
