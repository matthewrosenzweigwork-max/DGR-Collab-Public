import DGRHS.Commutator.SourceRieszAdjointTimeRemainder

/-! Source finite-N adjoint duality for the actual Riesz force, native
gradient, Laplacian and time derivative. Only primitive particle time-test
Ito and mean-field weak formulas are admissibility inputs. The physical
factory derives singular time properness from the original Gr estimate;
the requested terminal decomposition is a conclusion. Stochastic-integral
realization and source-admissibility review retain separate statuses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRiesz_adjoint_time_identity
    (s β T M : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M)
    (q : ℝ→E→ℝ) (K : ℝ≥0)
    (hq : ∀ r∈Icc 0 T,ContDiff ℝ 2 (q r))
    (hK : ∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (hgrad : ContinuousOn (fun p : ℝ×E=>gradient (q p.1) p.2) (Icc 0 T ×ˢ univ))
    (hback : ∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ z,
      deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z=
        ∫ y,⟪sourceRieszForce s (z-y),gradient (q r) z-gradient (q r) y⟫
          ∂gaussianRieszDensityMeasure (ρ r))
    (N : ℕ) (hN : 0<N) (X : ℝ→Fin N→E) (m : ℝ)
    (hiA : Integrable (fun r=>sourceRieszLocalTransportEnergy (ρ r) s 1
      (gradient (q r)) N (X r)) (volume.restrict (Ioc 0 T)))
    (hIto : (∫ z,q T z ∂sourceRieszLocalEmpiricalLaw N (X T))-
      (∫ z,q 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0))=
      (∫ r in Ioc 0 T,sourceRieszEmpiricalTestDrift s β q N r (X r))+m)
    (hweak : (∫ z,q T z ∂gaussianRieszDensityMeasure (ρ T))-
      (∫ z,q 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
      ∫ r in Ioc 0 T,sourceRieszMeanTestDrift s β (ρ r) q r) :
    Integrable (fun r=>sourceRieszEmpiricalTestDrift s β q N r (X r))
      (volume.restrict (Ioc 0 T)) ∧
    Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ T) (q T) N (X T)=
      Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (q 0) N (X 0)+
      Real.sqrt N*m-(Real.sqrt N/2)*(∫ r in Ioc 0 T,
        sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (q r)) N (X r)) := by
  let η := volume.restrict (Ioc 0 T)
  let ge := fun r=>sourceRieszEmpiricalTestDrift s β q N r (X r)
  let gm := fun r=>sourceRieszMeanTestDrift s β (ρ r) q r
  let A := fun r=>sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (q r)) N (X r)
  have him : Integrable gm η := sourceRiesz_adjoint_mean_drift_time_integrable
    s β T M hs hd hM ρ hρm hprob hρ q K hq hK hgrad hback
  have he : ∀ᵐ r ∂η,ge r-gm r=-(1/2:ℝ)*A r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hback] with r hr hb
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    letI := hprob r hr'
    exact (sourceRiesz_adjoint_physical_drift s β hs hβ hd (ρ r) M hM (hρ r hr')
      q r (hq r hr') K (hK r hr') hb N hN (X r)).2.2.2.2
  have hie : Integrable ge η := (him.sub (hiA.const_mul (1/2:ℝ))).congr
    (he.mono fun r hr=>by
      change gm r-(1/2:ℝ)*A r=ge r
      linarith)
  have hdint : (∫ r,ge r ∂η)-(∫ r,gm r ∂η)=-(1/2:ℝ)*(∫ r,A r ∂η) := by
    rw [←integral_sub hie him]
    calc
      _ = ∫ r,-(1/2:ℝ)*A r ∂η := integral_congr_ae he
      _ = _ := integral_const_mul _ _
  refine ⟨hie,?_⟩
  unfold sourceRieszDynamicEmpiricalDifference
  change (∫ z,q T z ∂sourceRieszLocalEmpiricalLaw N (X T))-
    (∫ z,q 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0))=(∫ r,ge r ∂η)+m at hIto
  change (∫ z,q T z ∂gaussianRieszDensityMeasure (ρ T))-
    (∫ z,q 0 z ∂gaussianRieszDensityMeasure (ρ 0))=(∫ r,gm r ∂η) at hweak
  linear_combination (Real.sqrt N)*hIto-(Real.sqrt N)*hweak+(Real.sqrt N)*hdint

theorem exists_sourceRiesz_physical_adjoint_time_identity
    (s β M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (K : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      ∀ (q : ℝ→E→ℝ),(∀ r∈Icc 0 T,ContDiff ℝ 2 (q r)) →
      (∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ)) →
      ContinuousOn (fun p : ℝ×E=>gradient (q p.1) p.2) (Icc 0 T ×ˢ univ) →
      ∀ (L : ℝ),(∀ r∈Icc 0 T,∀ z,|q r z|≤L) →
      (∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ z,
        deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z=
          ∫ y,⟪sourceRieszForce s (z-y),gradient (q r) z-gradient (q r) y⟫
            ∂gaussianRieszDensityMeasure (ρ r)) →
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (Function.uncurry X) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) → (∀ r∈Icc 0 T,B r≤Bmax) →
      (∀ r∈Icc 0 T,sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N (ν.map (X r))≤
        (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
          (sourceRieszSingularGibbs s β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      ∀ (m : Ω→ℝ),
      (∀ᵐ ω ∂ν,(∫ z,q T z ∂sourceRieszLocalEmpiricalLaw N (X T ω))-
        (∫ z,q 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω))=
        (∫ r in Ioc 0 T,sourceRieszEmpiricalTestDrift s β q N r (X r ω))+m ω) →
      ((∫ z,q T z ∂gaussianRieszDensityMeasure (ρ T))-
        (∫ z,q 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 T,sourceRieszMeanTestDrift s β (ρ r) q r) →
      let A := fun r ω=>sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (q r)) N (X r ω)
      let R := fun ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω))
      (∀ r∈Icc 0 T,Integrable (q r) (gaussianRieszDensityMeasure (ρ r)) ∧
        ∀ x : Fin N→E,Integrable (q r) (sourceRieszLocalEmpiricalLaw N x)) ∧
      Integrable (fun r=>sourceRieszMeanTestDrift s β (ρ r) q r) (volume.restrict (Ioc 0 T)) ∧
      (∀ᵐ ω ∂ν,Integrable (fun r=>A r ω) (volume.restrict (Ioc 0 T)) ∧
        Integrable (fun r=>sourceRieszEmpiricalTestDrift s β q N r (X r ω)) (volume.restrict (Ioc 0 T)) ∧
        Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ T) (q T) N (X T ω)=
          Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (q 0) N (X 0 ω)+
            Real.sqrt N*m ω+R ω) ∧
      Measurable R ∧ Integrable R ν ∧ (∫ ω,|R ω| ∂ν)≤T*D/(2*Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_adjoint_time_remainder
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax K
  refine ⟨D,hD,?_⟩
  intro T hT N hN Ω _ ν _ ρ hρm hprob hρ q hq hK hgrad L hqB hback
    X hXm G B hG hB hE m hIto hweak
  obtain ⟨_,hAi,hRm,hRi,hRb⟩ := hfactory T hT N hN Ω ν ρ hρm hprob hρ
    q hq hK hgrad X hXm G B hG hB hE
  refine ⟨?_,sourceRiesz_adjoint_mean_drift_time_integrable s β T M hs hd hM
    ρ hρm hprob hρ q K hq hK hgrad hback,?_,hRm,hRi,hRb⟩
  · intro r hr
    letI := hprob r hr
    have hi (μ : Measure E) [IsProbabilityMeasure μ] : Integrable (q r) μ := by
      apply (integrable_const L).mono' (hq r hr).continuous.measurable.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hqB r hr z
    refine ⟨hi _,?_⟩
    intro x
    letI := sourceRieszLocalEmpiricalLaw_probability N (by omega : 0<N) x
    exact hi _
  · filter_upwards [hAi,hIto] with ω ha hit
    obtain ⟨hie,he⟩ := sourceRiesz_adjoint_time_identity s β T M hs hβ hd hM
      ρ hρm hprob hρ q K hq hK hgrad hback N (by omega) (fun r=>X r ω) (m ω) ha hit hweak
    exact ⟨ha,hie,by simpa only [sub_eq_add_neg] using he⟩

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.sourceRiesz_adjoint_time_identity
#print axioms DGRHS.Commutator.sourceRiesz_adjoint_time_identity
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceRiesz_physical_adjoint_time_identity
#print axioms DGRHS.Commutator.exists_sourceRiesz_physical_adjoint_time_identity
