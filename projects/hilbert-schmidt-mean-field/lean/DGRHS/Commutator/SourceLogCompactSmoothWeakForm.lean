import DGRHS.Commutator.SourceC2ApproximationConstructions
import DGRHS.Commutator.SourceLogC2PointwiseLimit
import DGRHS.Commutator.SourceLogCompactStaticWeakForm

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Every-time compact C-infinity testing implies every-time compact C2 testing,
hence (by the compact-C2 cutoff adapter `SourceLogCompactStaticWeakMeanField.to_bounded`)
the existing every-time bounded-C2 LOG class `SourceLogStaticWeakMeanField`.

Each compact C2 test is the pointwise limit, with derivatives through order two
and one uniform bound, of its mollifications, which are compact smooth tests;
`SourceC2PointwiseApproximation.log_integrated_identity` passes their proper
every-time identities to the limit. Only probability of each time slice is
added. No density bound, moment, narrow continuity, joint measurability or
desired bounded-test identity is a premise.

`SourceLogCompactStaticWeakForm` is the coordinator/A draft module of that
name (read-only starting material, reserved revised copy in this return). -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval ContDiff
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The starting compact-smooth identity, with actual every-time traces. -/
def SourceLogCompactSmoothStaticWeakMeanField (β T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    IntervalIntegrable (fun r => sourceLogStaticMeanTestDrift β (ρ r) ψ) volume 0 T ∧
    ∀ r ∈ Icc 0 T,
      (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceLogStaticMeanTestDrift β (ρ u) ψ

/-- Compact C-infinity testing implies compact C2 testing. -/
theorem SourceLogCompactSmoothStaticWeakMeanField.to_compactC2
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hweak : SourceLogCompactSmoothStaticWeakMeanField β T ρ) :
    SourceLogCompactStaticWeakMeanField β T ρ := by
  intro ψ hψ hc
  obtain ⟨a, ha⟩ := exists_source_mollifier_pointwiseApproximation ψ hψ hc
  have hw (n : ℕ) := hweak (a.test n) (ha n).1 (ha n).2
  exact a.log_integrated_identity β T hT ρ hprob (fun n => (hw n).1) (fun n => (hw n).2)

/-- Compact C-infinity testing implies the existing bounded-C2 LOG class. -/
theorem SourceLogCompactSmoothStaticWeakMeanField.to_bounded
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hweak : SourceLogCompactSmoothStaticWeakMeanField β T ρ) :
    SourceLogStaticWeakMeanField β T ρ :=
  SourceLogCompactStaticWeakMeanField.to_bounded β T hT ρ hprob
    (hweak.to_compactC2 β T hT ρ hprob)

end DGRHS.Commutator
