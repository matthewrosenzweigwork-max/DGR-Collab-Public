import DGRHS.Gaussian.GaussianShortRangeSourceL2
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Trace convention for a SUPPLIED every-time density path: every compact smooth
test pairing is continuous on the closed horizon. This is the minimal
continuity that lets a distributional-in-time equation determine the supplied
trajectory at every time (see `source_scalar_trace_needs_continuity`). It
follows from narrow continuity of the supplied probability path. It is
kernel-independent and is used for both LOG and positive Riesz. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Continuous compact-smooth-test trace of the SUPPLIED every-time law. -/
def SourceCompactTestContinuousTrace (T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    ContinuousOn (fun r => ∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r)) (Icc 0 T)

/-- Narrow continuity of the supplied probability path on the closed horizon gives
the continuous trace. -/
lemma sourceCompactTestContinuousTrace_of_narrow (T : ℝ) (ρ : ℝ → E → ℝ)
    (μ : ℝ → ProbabilityMeasure E) (hμ : ContinuousOn μ (Icc 0 T))
    (hρμ : ∀ r ∈ Icc 0 T, (μ r : Measure E) = gaussianRieszDensityMeasure (ρ r)) :
    SourceCompactTestContinuousTrace T ρ := by
  intro ψ hψ hc
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hc
  let f : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.ofNormedAddCommGroup ψ hψ.continuous C hC
  have hcont : ContinuousOn (fun r => ∫ x, f x ∂(μ r : Measure E)) (Icc 0 T) :=
    fun r hr => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hμ r hr) f
  exact hcont.congr (fun r hr => by
    change (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r)) = ∫ x, ψ x ∂(μ r : Measure E)
    exact congrArg (fun m : Measure E => ∫ x, ψ x ∂m) (hρμ r hr).symm)

end DGRHS.Commutator
