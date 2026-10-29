import DGRHS.Commutator.SourceCompactTestTrace
import DGRHS.Commutator.SourceLogCompactSmoothWeakForm
import DGRHS.Commutator.SourceScalarDistributionalTrace
import DGRHS.Commutator.SourceLogPrincipalValueForce

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Source-class identification for the LOG mean-field trajectory (source 865,
1046, 3897--3908).

`SourceLogPVDistributionalWeakMeanField` is the distributional-in-time weak
formulation tested against compact C-infinity spatial tests, with the
interaction written as the PRINCIPAL VALUE of the literal unsymmetrized force
term `∬ ∇g(x-y)·∇ψ(x)`, and with the compact-test generator a proper L1 time
function. `SourceCompactTestContinuousTrace` is the trace convention: every
compact smooth test pairing of the SUPPLIED every-time law is continuous on the
closed horizon; it follows from narrow continuity of the supplied probability
path (`sourceCompactTestContinuousTrace_of_narrow`). The initial trace is the
supplied law at time zero.

Main theorem: the PV-distributional class with the continuous trace implies
the existing every-time bounded-C2 class `SourceLogStaticWeakMeanField`. No
moving-test identity, force L1, density bound, moment or desired conclusion is
a premise. The continuous-trace hypothesis cannot be dropped
(`source_scalar_trace_needs_continuity`: changing the law at one interior time
preserves the distributional equation and every time integral but changes the
every-time identity). -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval ContDiff
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Distributional-in-time weak formulation with the canceled drift. -/
def SourceLogDistributionalWeakMeanField (β T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    IntervalIntegrable (fun r => sourceLogStaticMeanTestDrift β (ρ r) ψ) volume 0 T ∧
    SourceScalarDistributionalDerivOn
      (fun r => ∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r))
      (fun r => sourceLogStaticMeanTestDrift β (ρ r) ψ) 0 T

/-- Distributional-in-time weak formulation with the principal-value reading of
the literal unsymmetrized force term. -/
def SourceLogPVDistributionalWeakMeanField (β T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    IntervalIntegrable
      (fun r => sourceLogPVMeanTestDrift β (gaussianRieszDensityMeasure (ρ r)) ψ) volume 0 T ∧
    SourceScalarDistributionalDerivOn
      (fun r => ∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r))
      (fun r => sourceLogPVMeanTestDrift β (gaussianRieszDensityMeasure (ρ r)) ψ) 0 T

/-- The PV and canceled formulations coincide whenever the supplied laws are
probabilities on the closed horizon. -/
lemma sourceLogPVDistributional_iff (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) :
    SourceLogPVDistributionalWeakMeanField β T ρ ↔ SourceLogDistributionalWeakMeanField β T ρ := by
  have he (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      EqOn (fun r => sourceLogPVMeanTestDrift β (gaussianRieszDensityMeasure (ρ r)) ψ)
        (fun r => sourceLogStaticMeanTestDrift β (ρ r) ψ) (Icc 0 T) := by
    intro r hr
    letI := hprob r hr
    exact sourceLogPVMeanTestDrift_eq β (ρ r) ψ
      (sourceBoundedC2Test_of_compact ψ (hψ.of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hc)
  have hI (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
      {F G : ℝ → ℝ} (hFG : EqOn F G (Icc 0 T)) :
      IntervalIntegrable F volume 0 T ↔ IntervalIntegrable G volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT,
      intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact ⟨fun h => h.congr_fun (hFG.mono Ioc_subset_Icc_self) measurableSet_Ioc,
      fun h => h.congr_fun (hFG.symm.mono Ioc_subset_Icc_self) measurableSet_Ioc⟩
  constructor
  · intro h ψ hψ hc
    obtain ⟨hi, hd⟩ := h ψ hψ hc
    exact ⟨(hI ψ hψ hc (he ψ hψ hc)).mp hi, hd.congr_right hT (he ψ hψ hc)⟩
  · intro h ψ hψ hc
    obtain ⟨hi, hd⟩ := h ψ hψ hc
    exact ⟨(hI ψ hψ hc (he ψ hψ hc)).mpr hi, hd.congr_right hT (he ψ hψ hc).symm⟩

/-- Distributional formulation plus continuous trace gives the every-time compact
smooth formulation (scalar distributional FTC with the prescribed trace). -/
theorem SourceLogDistributionalWeakMeanField.to_compactSmooth
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hdist : SourceLogDistributionalWeakMeanField β T ρ)
    (htrace : SourceCompactTestContinuousTrace T ρ) :
    SourceLogCompactSmoothStaticWeakMeanField β T ρ := by
  intro ψ hψ hc
  obtain ⟨hi, hd⟩ := hdist ψ hψ hc
  exact ⟨hi, source_scalar_trace_eq_primitive hT _ _ (htrace ψ hψ hc) hi hd⟩

/-- **LOG source-class bridge.** Distributional formulation plus continuous trace
gives the existing every-time bounded-C2 LOG class. -/
theorem SourceLogDistributionalWeakMeanField.to_static
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hdist : SourceLogDistributionalWeakMeanField β T ρ)
    (htrace : SourceCompactTestContinuousTrace T ρ) :
    SourceLogStaticWeakMeanField β T ρ :=
  SourceLogCompactSmoothStaticWeakMeanField.to_bounded β T hT ρ hprob
    (hdist.to_compactSmooth β T hT ρ htrace)

/-- **LOG source-class bridge, principal-value reading of the literal force.** -/
theorem SourceLogPVDistributionalWeakMeanField.to_static
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hdist : SourceLogPVDistributionalWeakMeanField β T ρ)
    (htrace : SourceCompactTestContinuousTrace T ρ) :
    SourceLogStaticWeakMeanField β T ρ :=
  SourceLogDistributionalWeakMeanField.to_static β T hT ρ hprob
    ((sourceLogPVDistributional_iff β T hT ρ hprob).mp hdist) htrace

/-- Conversely the every-time bounded-C2 class (with probability laws) gives the
distributional formulation and the continuous trace, so on probability paths
the three formulations are equivalent. -/
theorem SourceLogStaticWeakMeanField.to_distributional
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (h : SourceLogStaticWeakMeanField β T ρ) :
    SourceLogDistributionalWeakMeanField β T ρ ∧ SourceCompactTestContinuousTrace T ρ := by
  have hb (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      SourceBoundedC2Test ψ :=
    sourceBoundedC2Test_of_compact ψ (hψ.of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hc
  refine ⟨fun ψ hψ hc => ⟨(h ψ (hb ψ hψ hc)).1, ?_⟩, fun ψ hψ hc => ?_⟩
  · obtain ⟨hi, he⟩ := h ψ (hb ψ hψ hc)
    exact source_scalar_distributional_of_primitive hT _ _ hi he
  · obtain ⟨μ, hμ, hρμ⟩ := h.exists_continuous_probability_path β T hT ρ hprob
    refine sourceCompactTestContinuousTrace_of_narrow T ρ μ hμ.continuousOn
      (fun r hr => ?_) ψ hψ hc
    rw [hρμ r, min_eq_right hr.2, max_eq_right hr.1]

end DGRHS.Commutator
