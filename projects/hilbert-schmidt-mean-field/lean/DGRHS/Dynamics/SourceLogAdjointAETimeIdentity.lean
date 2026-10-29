/- Exact source finiteNAdjointDuality time algebra from the original
particle time-test Ito identity and mean-field weak time-test identity.
Time properness is derived from the physical Hessian cap; no terminal
fluctuation decomposition is supplied. Process/admissibility realization
and time-measurability bridges remain separate original obligations. -/
import DGRHS.Dynamics.SourceLogAdjointAETimeMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem sourceLog_adjoint_ae_time_identity (β T : ℝ) (hT : 0≤T)
    (q : ℝ→E→ℝ) (K : ℝ≥0)
    (hq : ∀ r∈Icc 0 T,ContDiff ℝ 2 (q r))
    (hK : ∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (μ : ℝ→Measure E) (hμ : ∀ r∈Icc 0 T,IsProbabilityMeasure (μ r))
    (hback : ∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ z,deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z)=
      ∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y) ∂μ r)
    (N : ℕ) (hN : 0<N) (X : ℝ→Fin N→E) (M : ℝ)
    (hme : AEStronglyMeasurable (fun r=>sourceLogEmpiricalTestDrift β q N r (X r))
      (volume.restrict (Ioc 0 T)))
    (hmm : AEStronglyMeasurable (fun r=>sourceLogMeanTestDrift β q r (μ r))
      (volume.restrict (Ioc 0 T)))
    (hIto : (∫ z,q T z ∂transportEmpiricalLaw N (X T))-
      (∫ z,q 0 z ∂transportEmpiricalLaw N (X 0))=
      (∫ r in Ioc 0 T,sourceLogEmpiricalTestDrift β q N r (X r))+M)
    (hweak : (∫ z,q T z ∂μ T)-(∫ z,q 0 z ∂μ 0)=
      ∫ r in Ioc 0 T,sourceLogMeanTestDrift β q r (μ r)) :
    Integrable (fun r=>sourceLogEmpiricalTestDrift β q N r (X r)) (volume.restrict (Ioc 0 T)) ∧
    Integrable (fun r=>sourceLogMeanTestDrift β q r (μ r)) (volume.restrict (Ioc 0 T)) ∧
    Integrable (fun r=>sourceTransportEnergy (μ r) (sourceLogTransportKernel 1 (gradient (q r))) N (X r))
      (volume.restrict (Ioc 0 T)) ∧
    Real.sqrt N*((∫ z,q T z ∂transportEmpiricalLaw N (X T))-(∫ z,q T z ∂μ T))=
      Real.sqrt N*((∫ z,q 0 z ∂transportEmpiricalLaw N (X 0))-(∫ z,q 0 z ∂μ 0))+
      Real.sqrt N*M-(Real.sqrt N/2)*
        (∫ r in Ioc 0 T,sourceTransportEnergy (μ r)
          (sourceLogTransportKernel 1 (gradient (q r))) N (X r)) := by
  let η := volume.restrict (Ioc 0 T)
  let ge := fun r=>sourceLogEmpiricalTestDrift β q N r (X r)
  let gm := fun r=>sourceLogMeanTestDrift β q r (μ r)
  let A := fun r=>sourceTransportEnergy (μ r) (sourceLogTransportKernel 1 (gradient (q r))) N (X r)
  have hb : ∀ᵐ r ∂η,ge r-gm r=-(1/2:ℝ)*A r ∧
      |ge r|≤(3/2:ℝ)*(K:ℝ) ∧ |gm r|≤(3/2:ℝ)*(K:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hback] with r hr hb
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    letI := hμ r hr'
    exact (sourceLog_adjoint_physical_drift β q r (hq r hr') K (hK r hr')
      (μ r) hb N hN (X r)).2.2
  have hie : Integrable ge η := (integrable_const ((3/2:ℝ)*(K:ℝ))).mono' hme
    (hb.mono fun r hr=>by simpa only [Real.norm_eq_abs] using hr.2.1)
  have him : Integrable gm η := (integrable_const ((3/2:ℝ)*(K:ℝ))).mono' hmm
    (hb.mono fun r hr=>by simpa only [Real.norm_eq_abs] using hr.2.2)
  have hA : A=ᵐ[η](fun r=>(-2:ℝ)*(ge r-gm r)) := hb.mono fun r hr=>by linarith [hr.1]
  have hiA : Integrable A η := ((hie.sub him).const_mul (-2)).congr hA.symm
  have hd : (∫ r,ge r ∂η)-(∫ r,gm r ∂η)=-(1/2:ℝ)*(∫ r,A r ∂η) := by
    rw [←integral_sub hie him]
    calc
      _ = ∫ r,-(1/2:ℝ)*A r ∂η := integral_congr_ae (hb.mono fun r hr=>hr.1)
      _ = _ := integral_const_mul _ _
  refine ⟨hie,him,hiA,?_⟩
  change (∫ z,q T z ∂transportEmpiricalLaw N (X T))-
      (∫ z,q 0 z ∂transportEmpiricalLaw N (X 0))=(∫ r,ge r ∂η)+M at hIto
  change (∫ z,q T z ∂μ T)-(∫ z,q 0 z ∂μ 0)=∫ r,gm r ∂η at hweak
  change Real.sqrt N*((∫ z,q T z ∂transportEmpiricalLaw N (X T))-(∫ z,q T z ∂μ T))=
      Real.sqrt N*((∫ z,q 0 z ∂transportEmpiricalLaw N (X 0))-(∫ z,q 0 z ∂μ 0))+
      Real.sqrt N*M-(Real.sqrt N/2)*(∫ r,A r ∂η)
  linear_combination (Real.sqrt N)*hIto-(Real.sqrt N)*hweak+(Real.sqrt N)*hd
set_option maxHeartbeats 800000 in
theorem sourceLog_adjoint_regular_ae_time_identity (β T : ℝ) (hT : 0≤T)
    (q : ℝ→E→ℝ) (K : ℝ≥0) (L : ℝ)
    (hq : ∀ r∈Icc 0 T,ContDiff ℝ 2 (q r))
    (hK : ∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (hqbound : ∀ r∈Icc 0 T,∀ z,|q r z|≤L)
    (hgrad : Continuous (fun p : Icc (0:ℝ) T×E=>gradient (q p.1) p.2))
    (κ : Kernel ℝ E) [IsSFiniteKernel κ]
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (κ r))
    (hback : ∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ z,deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z)=
      ∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y) ∂κ r)
    (N : ℕ) (hN : 0<N) (X : ℝ→Fin N→E) (hX : Measurable X) (M : ℝ)
    (hIto : (∫ z,q T z ∂transportEmpiricalLaw N (X T))-
      (∫ z,q 0 z ∂transportEmpiricalLaw N (X 0))=
      (∫ r in Ioc 0 T,sourceLogEmpiricalTestDrift β q N r (X r))+M)
    (hweak : (∫ z,q T z ∂κ T)-(∫ z,q 0 z ∂κ 0)=
      ∫ r in Ioc 0 T,sourceLogMeanTestDrift β q r (κ r)) :
    (∀ r∈Icc 0 T,Integrable (q r) (κ r) ∧
      ∀ x : Fin N→E,Integrable (q r) (transportEmpiricalLaw N x)) ∧
    Integrable (fun r=>sourceLogEmpiricalTestDrift β q N r (X r)) (volume.restrict (Ioc 0 T)) ∧
    Integrable (fun r=>sourceLogMeanTestDrift β q r (κ r)) (volume.restrict (Ioc 0 T)) ∧
    Integrable (fun r=>sourceTransportEnergy (κ r) (sourceLogTransportKernel 1 (gradient (q r))) N (X r))
      (volume.restrict (Ioc 0 T)) ∧
    Real.sqrt N*((∫ z,q T z ∂transportEmpiricalLaw N (X T))-(∫ z,q T z ∂κ T))=
      Real.sqrt N*((∫ z,q 0 z ∂transportEmpiricalLaw N (X 0))-(∫ z,q 0 z ∂κ 0))+
      Real.sqrt N*M-(Real.sqrt N/2)*
        (∫ r in Ioc 0 T,sourceTransportEnergy (κ r)
          (sourceLogTransportKernel 1 (gradient (q r))) N (X r)) := by
  obtain ⟨hme,hmm⟩ := sourceLog_adjoint_ae_time_drifts_aestronglyMeasurable
    β T hT q K hq hK hgrad κ hprob hback N hN X hX
  refine ⟨?_,sourceLog_adjoint_ae_time_identity β T hT q K hq hK
    (fun r=>κ r) hprob hback N hN X M hme hmm hIto hweak⟩
  intro r hr
  letI := hprob r hr
  have hm := (hq r hr).continuous.measurable
  refine ⟨integrable_of_abs_bound (κ r) hm (hqbound r hr),?_⟩
  intro x
  letI := transportEmpiricalLaw_probability hN x
  exact integrable_of_abs_bound (transportEmpiricalLaw N x) hm (hqbound r hr)

end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceLog_adjoint_ae_time_identity
#print axioms DGRHS.Dynamics.sourceLog_adjoint_ae_time_identity
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceLog_adjoint_regular_ae_time_identity
#print axioms DGRHS.Dynamics.sourceLog_adjoint_regular_ae_time_identity
