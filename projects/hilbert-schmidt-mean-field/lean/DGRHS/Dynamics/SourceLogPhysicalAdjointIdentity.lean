import DGRHS.Dynamics.SourceLogAdjointRemainderMeasurable
import DGRHS.Dynamics.SourceLogAdjointIntervalIdentity
import DGRHS.Commutator.SourceLogCovarianceReplacement

/-! Actual logarithmic adjoint terminal identity and negligible remainder.
Only primitive particle time-test Ito, mean-field weak identity and native
backward equation are assumptions. Source physical free-energy and partition
controls derive the proper remainder and its family-uniform rate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1000000 in
theorem exists_sourceLog_physical_adjoint_interval_identity
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
      ∀ (L : ℝ),(∀ r∈Icc 0 T,∀ z,|q r z|≤L) →
      (∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ z,
        deriv (fun u=>q u z) r+(β:ℝ)⁻¹*laplacian (q r) z=
          ∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y)
            ∂gaussianRieszDensityMeasure (ρ r)) →
      ∀ (X : ℝ→Ω→Fin N→EuclideanSpace ℝ ι),Measurable (fun p : Icc (0:ℝ) T×Ω=>X p.1 p.2) →
      ∀ (a b : ℝ→ℝ),(∀ r∈Icc 0 T,0≤a r) →
      (∀ r∈Icc 0 T,a r≤Amax) → (∀ r∈Icc 0 T,b r≤Bmax) →
      c≤(sourceLogSingularPartition β (ρ 0) N).toReal →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition β (ρ r) N).toReal≤C) →
      (∀ r∈Icc 0 T,sourceLogCollisionFreeEnergy β (ρ r) M N (ν.map (X r))≤
        (a r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(b r/(N:ℝ):ℝ)) →
      ∀ (m : Ω→ℝ),
      (∀ᵐ ω ∂ν,(∫ z,q T z ∂transportEmpiricalLaw N (X T ω))-
        (∫ z,q 0 z ∂transportEmpiricalLaw N (X 0 ω))=
        (∫ r in Ioc 0 T,sourceLogEmpiricalTestDrift (β:ℝ) q N r (X r ω))+m ω) →
      ((∫ z,q T z ∂gaussianRieszDensityMeasure (ρ T))-
        (∫ z,q 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 T,sourceLogMeanTestDrift (β:ℝ) q r (gaussianRieszDensityMeasure (ρ r))) →
      let A := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
        (sourceLogTransportKernel 1 (gradient (q r))) N (X r ω)
      let R := fun ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω))
      (∀ r∈Icc 0 T,Integrable (q r) (gaussianRieszDensityMeasure (ρ r)) ∧
        ∀ x : Fin N→EuclideanSpace ℝ ι,Integrable (q r) (transportEmpiricalLaw N x)) ∧
      (∀ᵐ ω ∂ν,Integrable (fun r=>A r ω) (volume.restrict (Ioc 0 T)) ∧
        Integrable (fun r=>sourceLogEmpiricalTestDrift (β:ℝ) q N r (X r ω)) (volume.restrict (Ioc 0 T)) ∧
        Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ T) (q T) N (X T ω)=
          Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ 0) (q 0) N (X 0 ω)+
            Real.sqrt N*m ω+R ω) ∧
      Measurable R ∧ Integrable R ν ∧ (∫ ω,|R ω| ∂ν)≤T*D/(2*Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceLog_physical_adjoint_interval_remainder
    (ι:=ι) β hβ hd K M hM J c C Amax Bmax hc hAmax hBmax
  refine ⟨D,hD,?_⟩
  intro T hT N hN Ω _ ν _ ρ hρm hprob hρ hp hI q hq hqK hgrad L hL hback
    X hXm a b ha haA hbB hlow hcap hE m hIto hweak
  obtain ⟨_,_,hRi,hRb⟩ := hfactory T hT N hN Ω ν ρ hρm hprob hρ hp hI
    q hq hqK hgrad X hXm a b ha haA hbB hlow hcap hE
  have hRm := measurable_sourceLog_adjoint_interval_remainder T hT ρ hρm q hgrad
    N (by omega) X hXm
  refine ⟨?_,?_,hRm,hRi.neg,by simpa only [abs_neg] using hRb⟩
  · intro r hr
    letI := hprob r hr
    have hi (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] : Integrable (q r) μ := by
      apply (integrable_const L).mono' (hq r hr).continuous.measurable.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hL r hr z
    refine ⟨hi _,?_⟩
    intro x
    letI := transportEmpiricalLaw_probability (by omega : 0<N) x
    exact hi _
  · filter_upwards [hIto] with ω hit
    have hXω : Measurable (fun r : Icc (0:ℝ) T=>X r ω) :=
      hXm.comp (measurable_id.prodMk measurable_const)
    obtain ⟨_,hie,_,hia,he⟩ := sourceLog_adjoint_interval_time_identity
      (β:ℝ) T hT ρ hρm hprob q K L hq hqK hL hgrad hback N (by omega)
      (fun r=>X r ω) hXω (m ω) hit hweak
    exact ⟨hia,hie,by simpa only [sourceLogDynamicEmpiricalDifference,sub_eq_add_neg] using he⟩

end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.exists_sourceLog_physical_adjoint_interval_identity
#print axioms DGRHS.Dynamics.exists_sourceLog_physical_adjoint_interval_identity
