import DGRHS.Dynamics.SourceLogAdjointTimeRemainder

/-! Original logarithmic classical remainder on its original horizon.
The actual paths need joint measurability only on Icc0T, and any nonnegative
Hessian envelope includingK0 is allowed. A positive auxiliary envelope K+1
is selected internally; no clamped-test derivative is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 800000 in
theorem exists_sourceLog_physical_adjoint_interval_remainder
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (K : ℝ≥0) (M : ℝ) (hM : 0≤M)
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
      ∀ (X : ℝ→Ω→Fin N→EuclideanSpace ℝ ι),Measurable (fun p : Icc (0:ℝ) T×Ω=>X p.1 p.2) →
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
      (∀ᵐ ω ∂ν,Integrable (fun r=>A r ω) (volume.restrict (Ioc 0 T))) ∧
      Integrable (fun ω=>(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)) ν ∧
      (∫ ω,|(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)| ∂ν)≤T*D/(2*Real.sqrt N) := by
  let Kp : ℝ≥0 := K+1
  have hKp : 0<(Kp:ℝ) := by dsimp [Kp];positivity
  obtain ⟨D,hD,hfactory⟩ := exists_sourceLog_physical_adjoint_time_remainder
    β hβ hd Kp hKp M hM J c C Amax Bmax hc hAmax hBmax
  refine ⟨D,hD,?_⟩
  intro T hT N hN Ω _ ν _ ρ hρm hprob hρ hp hI q hq hqK hgrad X hXm a b ha haA hbB hlow hcap hE
  let Xe := fun r=>X (projIcc 0 T hT r)
  have hXeq (r : ℝ) (hr : r∈Icc 0 T) : Xe r=X r := by
    dsimp only [Xe];rw [projIcc_of_mem hT hr]
  have hXem : Measurable (Function.uncurry Xe) :=
    hXm.comp (((continuous_projIcc : Continuous (projIcc 0 T hT)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hqKp : ∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(Kp:ℝ) := by
    intro r hr z
    exact (hqK r hr z).trans (by dsimp [Kp];norm_num)
  obtain ⟨hi,hRi,hb⟩ := hfactory T hT N hN Ω ν ρ hρm hprob hρ hp hI
    q hq hqKp hgrad Xe hXem a b ha haA hbB hlow hcap
    (fun r hr=>by simpa only [hXeq r hr] using hE r hr)
  let η := volume.restrict (Ioc 0 T)
  let Ae := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
    (sourceLogTransportKernel 1 (gradient (q r))) N (Xe r ω)
  let A := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
    (sourceLogTransportKernel 1 (gradient (q r))) N (X r ω)
  have heqTime (ω : Ω) : (fun r=>Ae r ω)=ᵐ[η](fun r=>A r ω) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    dsimp only [Ae,A]
    rw [hXeq r hr']
  have htime : ∀ᵐ p : ℝ×Ω ∂η.prod ν,p.1∈Ioc 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Filter.Eventually.of_forall (fun _=>hr)
  have heq : Function.uncurry Ae=ᵐ[η.prod ν]Function.uncurry A := by
    filter_upwards [htime] with p hp
    have hr : p.1∈Icc 0 T := ⟨hp.1.le,hp.2⟩
    change sourceTransportEnergy (gaussianRieszDensityMeasure (ρ p.1))
      (sourceLogTransportKernel 1 (gradient (q p.1))) N (Xe p.1 p.2)=
      sourceTransportEnergy (gaussianRieszDensityMeasure (ρ p.1))
        (sourceLogTransportKernel 1 (gradient (q p.1))) N (X p.1 p.2)
    rw [hXeq p.1 hr]
  have hint (ω : Ω) : (∫ r,Ae r ω ∂η)=∫ r,A r ω ∂η := integral_congr_ae (heqTime ω)
  change Integrable (Function.uncurry Ae) (η.prod ν) at hi
  change Integrable (fun ω=>(Real.sqrt N/2)*(∫ r,Ae r ω ∂η)) ν at hRi
  change (∫ ω,|(Real.sqrt N/2)*(∫ r,Ae r ω ∂η)| ∂ν)≤T*D/(2*Real.sqrt N) at hb
  simp_rw [hint] at hRi hb
  have hiActual := hi.congr heq
  exact ⟨hiActual,hiActual.prod_left_ae,hRi,hb⟩
end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.exists_sourceLog_physical_adjoint_interval_remainder
#print axioms DGRHS.Dynamics.exists_sourceLog_physical_adjoint_interval_remainder
