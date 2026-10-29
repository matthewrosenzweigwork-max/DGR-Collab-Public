/- Actual backward drift time measurability.  The backward equation
identifies the mean drift with a proper half pair integral; instantaneous
cancellation then identifies the particle drift with a measurable physical
commutator expression.  No drift measurability assumption is supplied. -/
import DGRHS.Dynamics.SourceLogAdjointPhysicalDrift
import DGRHS.Dynamics.SourceLogTimeMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.ProjIcc
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem sourceLog_adjoint_mean_drift_eq_half_pair (β : ℝ) (q : ℝ→E→ℝ) (r : ℝ)
    (hq : ContDiff ℝ 2 (q r)) (K : ℝ≥0)
    (hK : ∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hback : ∀ z,deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z)=
      ∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y) ∂μ) :
    sourceLogMeanTestDrift β q r μ=
      (1/2:ℝ)*(∫ p,sourceLogTransportKernel 1 (gradient (q r)) p ∂μ.prod μ) := by
  have hv := sourceAdjoint_gradient_lipschitz_of_hessian_bound (q r) hq K hK
  have hi := integrable_sourceLogTransport_kernel_pair 1 (by omega) hv μ μ
  have he : (fun z=>deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z))=
      (fun z=>∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y) ∂μ) := funext hback
  unfold sourceLogMeanTestDrift
  rw [he,←integral_prod _ hi]
  ring

set_option maxHeartbeats 800000 in
theorem sourceLog_adjoint_time_drifts_aestronglyMeasurable (β T : ℝ) (hT : 0≤T)
    (q : ℝ→E→ℝ) (K : ℝ≥0)
    (hq : ∀ r∈Icc 0 T,ContDiff ℝ 2 (q r))
    (hK : ∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (hgrad : Continuous (fun p : Icc (0:ℝ) T×E=>gradient (q p.1) p.2))
    (κ : Kernel ℝ E) [IsSFiniteKernel κ]
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (κ r))
    (hback : ∀ r∈Icc 0 T,∀ z,deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z)=
      ∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y) ∂κ r)
    (N : ℕ) (hN : 0<N) (X : ℝ→Fin N→E) (hX : Measurable X) :
    AEStronglyMeasurable (fun r=>sourceLogEmpiricalTestDrift β q N r (X r))
      (volume.restrict (Ioc 0 T)) ∧
    AEStronglyMeasurable (fun r=>sourceLogMeanTestDrift β q r (κ r))
      (volume.restrict (Ioc 0 T)) := by
  let v := fun r=>gradient (q (projIcc 0 T hT r))
  have hv : Measurable (Function.uncurry v) := by
    have ht := hgrad.comp (((continuous_projIcc : Continuous (projIcc 0 T hT)).comp
      continuous_fst).prodMk continuous_snd)
    exact ht.measurable
  have hvr (r : ℝ) (hr : r∈Icc 0 T) : v r=gradient (q r) := by
    dsimp only [v]
    rw [projIcc_of_mem hT hr]
  have hk := measurable_sourceLogTransportKernel_time v hv
  have hI : Measurable (fun r=>∫ p,sourceLogTransportKernel 1 (v r) p ∂(κ r).prod (κ r)) := by
    have ht := hk.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ.prod κ)
    simpa only [Kernel.prod_apply] using ht.measurable
  have hAn : Measurable (fun r=>sourceTransportEnergy (κ r)
      (sourceLogTransportKernel 1 (v r)) N (X r)) := by
    have ht := measurable_sourceLogTransportEnergy_time (Ω:=Unit) κ v hv N hN
      (fun p : ℝ×Unit=>X p.1) (hX.comp measurable_fst)
    have hm : Measurable (fun r : ℝ=>(r,())) := measurable_id.prodMk measurable_const
    simpa only [Function.comp_def] using ht.comp hm
  have hmean : (fun r=>(1/2:ℝ)*(∫ p,sourceLogTransportKernel 1 (v r) p ∂(κ r).prod (κ r)))
      =ᵐ[volume.restrict (Ioc 0 T)] (fun r=>sourceLogMeanTestDrift β q r (κ r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    letI := hprob r hr'
    simpa only [hvr r hr'] using
      (sourceLog_adjoint_mean_drift_eq_half_pair β q r (hq r hr') K (hK r hr')
        (κ r) (hback r hr')).symm
  have hemp : (fun r=>(1/2:ℝ)*(∫ p,sourceLogTransportKernel 1 (v r) p ∂(κ r).prod (κ r))-
      (1/2:ℝ)*sourceTransportEnergy (κ r) (sourceLogTransportKernel 1 (v r)) N (X r))
      =ᵐ[volume.restrict (Ioc 0 T)] (fun r=>sourceLogEmpiricalTestDrift β q N r (X r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hmean] with r hr hm
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    letI := hprob r hr'
    have he := (sourceLog_adjoint_physical_drift β q r (hq r hr') K (hK r hr')
      (κ r) (hback r hr') N hN (X r)).2.2.1
    rw [←hvr r hr'] at he
    linarith
  exact ⟨((hI.const_mul (1/2:ℝ)).sub (hAn.const_mul (1/2:ℝ))).aestronglyMeasurable.congr hemp,
    (hI.const_mul (1/2:ℝ)).aestronglyMeasurable.congr hmean⟩
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLog_adjoint_mean_drift_eq_half_pair
#check @DGRHS.Dynamics.sourceLog_adjoint_time_drifts_aestronglyMeasurable
#print axioms DGRHS.Dynamics.sourceLog_adjoint_mean_drift_eq_half_pair
#print axioms DGRHS.Dynamics.sourceLog_adjoint_time_drifts_aestronglyMeasurable
