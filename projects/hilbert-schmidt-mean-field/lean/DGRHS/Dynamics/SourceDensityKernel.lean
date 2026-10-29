/- A moving physical density gives a genuine native measurable kernel.
No desired dynamical estimates or time-integral properness are fields. -/
import Mathlib.Probability.Kernel.WithDensity
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Dynamics
variable {τ E : Type*} [MeasurableSpace τ] [MeasurableSpace E]

def sourceDensityKernel (m : Measure E) [SFinite m] (ρ : τ→E→ℝ) : Kernel τ E :=
  (Kernel.const τ m).withDensity (fun r z=>ENNReal.ofReal (ρ r z))

theorem sourceDensityKernel_apply (m : Measure E) [SFinite m] (ρ : τ→E→ℝ)
    (hρ : Measurable (Function.uncurry ρ)) (r : τ) :
    sourceDensityKernel m ρ r=m.withDensity (fun z=>ENNReal.ofReal (ρ r z)) := by
  exact Kernel.withDensity_apply (Kernel.const τ m)
    (f:=fun t z=>ENNReal.ofReal (ρ t z)) (ENNReal.measurable_ofReal.comp hρ) r

theorem sourceDensityKernel_sfinite (m : Measure E) [SFinite m] (ρ : τ→E→ℝ) :
    IsSFiniteKernel (sourceDensityKernel m ρ) := by
  exact Kernel.IsSFiniteKernel.withDensity (Kernel.const τ m)
    (f:=fun r z=>ENNReal.ofReal (ρ r z)) (fun _ _=>ENNReal.ofReal_ne_top)

theorem sourceDensityKernel_probability (m : Measure E) [SFinite m] (ρ : τ→E→ℝ)
    (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r,IsProbabilityMeasure (m.withDensity (fun z=>ENNReal.ofReal (ρ r z)))) :
    IsMarkovKernel (sourceDensityKernel m ρ) := by
  constructor
  intro r
  rw [sourceDensityKernel_apply m ρ hρ r]
  exact hp r
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceDensityKernel_apply
#check @DGRHS.Dynamics.sourceDensityKernel_probability
#print axioms DGRHS.Dynamics.sourceDensityKernel
#print axioms DGRHS.Dynamics.sourceDensityKernel_apply
#print axioms DGRHS.Dynamics.sourceDensityKernel_probability

#check @DGRHS.Dynamics.sourceDensityKernel_sfinite
#print axioms DGRHS.Dynamics.sourceDensityKernel_sfinite
