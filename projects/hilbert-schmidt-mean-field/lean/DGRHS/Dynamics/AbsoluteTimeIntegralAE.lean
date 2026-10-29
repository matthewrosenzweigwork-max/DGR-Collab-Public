/- Proper Fubini with an almost-everywhere time-product cap, allowing
source regularity on the finite horizon without hypotheses outside it. -/
import DGRHS.Dynamics.AbsoluteTimeIntegral
noncomputable section
open MeasureTheory
namespace DGRHS.Dynamics

theorem absolute_time_integral_bound_ae
    {τ Ω : Type*} [MeasurableSpace τ] [MeasurableSpace Ω]
    (η : Measure τ) [IsFiniteMeasure η] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : τ→Ω→ℝ) (hA : AEStronglyMeasurable (Function.uncurry A) (η.prod ν))
    (U C : ℝ) (hcap : ∀ᵐ z ∂η.prod ν,|A z.1 z.2|≤U)
    (hbound : ∀ᵐ t ∂η,(∫ ω,|A t ω| ∂ν)≤C) :
    Integrable (Function.uncurry A) (η.prod ν) ∧
    Integrable (fun ω=>∫ t,A t ω ∂η) ν ∧
    (∫ ω,|∫ t,A t ω ∂η| ∂ν)≤η.real Set.univ*C := by
  have hi : Integrable (Function.uncurry A) (η.prod ν) :=
    (integrable_const U).mono' hA (hcap.mono fun z hz=>by
      change ‖A z.1 z.2‖≤U
      simpa only [Real.norm_eq_abs] using hz)
  have ha : Integrable (fun z : τ×Ω=>|A z.1 z.2|) (η.prod ν) := hi.abs
  refine ⟨hi,hi.integral_prod_right,?_⟩
  calc
    (∫ ω,|∫ t,A t ω ∂η| ∂ν)≤∫ ω,∫ t,|A t ω| ∂η ∂ν :=
      integral_mono hi.integral_prod_right.abs ha.integral_prod_right (fun ω=>abs_integral_le_integral_abs)
    _ = ∫ t,∫ ω,|A t ω| ∂ν ∂η := (integral_integral_swap ha).symm
    _ ≤ ∫ _ : τ,C ∂η := integral_mono_ae ha.integral_prod_left (integrable_const C) hbound
    _ = η.real Set.univ*C := by simp only [integral_const,smul_eq_mul]
end DGRHS.Dynamics
#check @DGRHS.Dynamics.absolute_time_integral_bound_ae
#print axioms DGRHS.Dynamics.absolute_time_integral_bound_ae
