/- Original logarithmic adjoint remainder: actual classical backward test,
actual moving density and actual paths. Joint regularity is required only
on the source closed time interval. Auxiliary interval extensions preserve
all actual integrals there and introduce no time derivative assumption. -/
import DGRHS.Dynamics.SourceLogTimeRemainderPhysical
import DGRHS.Dynamics.SourceAdjointHessianLipschitz
import Mathlib.Topology.Order.ProjIcc
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 800000 in
theorem exists_sourceLog_physical_adjoint_time_remainder
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (K : ℝ≥0) (hK : 0<(K:ℝ)) (M : ℝ) (hM : 0≤M)
    (J c C Amax Bmax : ℝ) (hc : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→EuclideanSpace ℝ ι→ℝ),Measurable (fun p : Icc (0:ℝ) T×EuclideanSpace ℝ ι=>ρ p.1 p.2) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ x ∂volume,ρ r x≤M) →
      (∀ r∈Icc 0 T,Integrable logPhysicalPair
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) →
      (∀ r∈Icc 0 T,-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
        (fun x y=>logPhysicalPair (x,y))) →
      ∀ (q : ℝ→EuclideanSpace ℝ ι→ℝ),
      (∀ r∈Icc 0 T,ContDiff ℝ 2 (q r)) →
      (∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ)) →
      Continuous (fun p : Icc (0:ℝ) T×EuclideanSpace ℝ ι=>gradient (q p.1) p.2) →
      ∀ (X : ℝ→Ω→Fin N→EuclideanSpace ℝ ι),Measurable (Function.uncurry X) →
      ∀ (a b : ℝ→ℝ),(∀ r∈Icc 0 T,0≤a r) →
      (∀ r∈Icc 0 T,a r≤Amax) → (∀ r∈Icc 0 T,b r≤Bmax) →
      c≤(sourceLogSingularPartition β (ρ 0) N).toReal →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition β (ρ r) N).toReal≤C) →
      (∀ r∈Icc 0 T,sourceLogCollisionFreeEnergy β (ρ r) M N (ν.map (X r))≤
        (a r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(b r/(N:ℝ):ℝ)) →
      let A := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
        (sourceLogTransportKernel 1 (gradient (q r))) N (X r ω)
      Integrable (Function.uncurry A) ((volume.restrict (Ioc 0 T)).prod ν) ∧
      Integrable (fun ω=>(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)) ν ∧
      (∫ ω,|(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)| ∂ν)≤T*D/(2*Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceLog_physical_time_commutator_remainder
    β hβ hd K hK M hM J c C Amax Bmax hc hAmax hBmax
  refine ⟨D,hD,?_⟩
  intro T hT N hN Ω _ ν _ ρ hρm hprob hρ hp hI q hq hqK hgrad X hXm a b ha haA hbB hlow hcap hE
  let ρe := fun r=>ρ (projIcc 0 T hT r)
  let ve := fun r=>gradient (q (projIcc 0 T hT r))
  have hρeq (r : ℝ) (hr : r∈Icc 0 T) : ρe r=ρ r := by
    dsimp only [ρe]
    rw [projIcc_of_mem hT hr]
  have hveq (r : ℝ) (hr : r∈Icc 0 T) : ve r=gradient (q r) := by
    dsimp only [ve]
    rw [projIcc_of_mem hT hr]
  have hproj : Measurable (fun p : ℝ×EuclideanSpace ℝ ι=>(projIcc 0 T hT p.1,p.2)) :=
    ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd).measurable
  have hρem : Measurable (Function.uncurry ρe) := hρm.comp hproj
  have hvem : Measurable (Function.uncurry ve) := hgrad.measurable.comp hproj
  have hve (r : ℝ) (hr : r∈Icc 0 T) : LipschitzWith K (ve r) := by
    rw [hveq r hr]
    exact sourceAdjoint_gradient_lipschitz_of_hessian_bound (q r) (hq r hr) K (hqK r hr)
  have hz : (0:ℝ)∈Icc 0 T := ⟨le_rfl,hT⟩
  obtain ⟨hi,hRi,hb⟩ := hfactory T hT N hN Ω ν ρe hρem
    (fun r hr=>by simpa only [hρeq r hr] using hprob r hr)
    (fun r hr=>by simpa only [hρeq r hr] using hρ r hr)
    (fun r hr=>by simpa only [hρeq r hr] using hp r hr)
    (fun r hr=>by simpa only [hρeq r hr] using hI r hr)
    ve hvem hve X hXm a b ha haA hbB
    (by simpa only [hρeq 0 hz] using hlow)
    (fun r hr=>by simpa only [hρeq r hr] using hcap r hr)
    (fun r hr=>by simpa only [hρeq r hr,hρeq 0 hz] using hE r hr)
  let η := volume.restrict (Ioc 0 T)
  let Ae := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρe r))
    (sourceLogTransportKernel 1 (ve r)) N (X r ω)
  let A := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
    (sourceLogTransportKernel 1 (gradient (q r))) N (X r ω)
  have htime : ∀ᵐ p : ℝ×Ω ∂η.prod ν,p.1∈Ioc 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Filter.Eventually.of_forall (fun _=>hr)
  have heq : Function.uncurry Ae=ᵐ[η.prod ν]Function.uncurry A := by
    filter_upwards [htime] with p hp
    have hr : p.1∈Icc 0 T := ⟨hp.1.le,hp.2⟩
    change sourceTransportEnergy (gaussianRieszDensityMeasure (ρe p.1))
      (sourceLogTransportKernel 1 (ve p.1)) N (X p.1 p.2)=
      sourceTransportEnergy (gaussianRieszDensityMeasure (ρ p.1))
        (sourceLogTransportKernel 1 (gradient (q p.1))) N (X p.1 p.2)
    rw [hρeq p.1 hr,hveq p.1 hr]
  have hint (ω : Ω) : (∫ r,Ae r ω ∂η)=∫ r,A r ω ∂η := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    dsimp only [Ae,A]
    rw [hρeq r hr',hveq r hr']
  change Integrable (Function.uncurry Ae) (η.prod ν) at hi
  change Integrable (fun ω=>(Real.sqrt N/2)*(∫ r,Ae r ω ∂η)) ν at hRi
  change (∫ ω,|(Real.sqrt N/2)*(∫ r,Ae r ω ∂η)| ∂ν)≤T*D/(2*Real.sqrt N) at hb
  simp_rw [hint] at hRi hb
  exact ⟨hi.congr heq,hRi,hb⟩
end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.exists_sourceLog_physical_adjoint_time_remainder
#print axioms DGRHS.Dynamics.exists_sourceLog_physical_adjoint_time_remainder
