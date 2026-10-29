/- Backward-adjoint cancellation in the genuine logarithmic weak drift.
Actual bounded physical transport makes all scalar integrals proper.
The only equation supplied is the original backward-adjoint pointwise PDE. -/
import DGRHS.Dynamics.SourceLogDynamicQuadratic
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem sourceLog_backward_adjoint_drift
    (β : ℝ) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (μ : Measure E) [IsProbabilityMeasure μ] (dt lap : E→ℝ)
    (hback : ∀ z,dt z+β⁻¹*lap z=∫ y,sourceLogTransportKernel 1 v (z,y) ∂μ)
    (N : ℕ) (hN : 0<N) (x : Fin N→E) :
    let e := transportEmpiricalLaw N x
    let h := sourceLogTransportKernel 1 v
    Integrable (fun z=>dt z+β⁻¹*lap z) e ∧
    Integrable (fun z=>dt z+β⁻¹*lap z) μ ∧
    ((∫ z,dt z+β⁻¹*lap z ∂e)-(∫ z,dt z+β⁻¹*lap z ∂μ))-
      (1/2:ℝ)*((∫ p in {p : E×E|p.1≠p.2},h p ∂e.prod e)-(∫ p,h p ∂μ.prod μ)) =
      -(1/2:ℝ)*sourceTransportEnergy μ h N x := by
  let e := transportEmpiricalLaw N x
  let h := sourceLogTransportKernel 1 v
  obtain ⟨h1,h2,h3,h4,he⟩ := sourceLog_dynamic_quadratic_expansion hv μ N hN x
  have hp : (fun z=>dt z+β⁻¹*lap z)=(fun z=>∫ y,h (z,y) ∂μ) := funext hback
  refine ⟨by rw [hp];exact h2.integral_prod_left,by rw [hp];exact h4.integral_prod_left,?_⟩
  rw [hp,←integral_prod h h2,←integral_prod h h4]
  change ((∫ p,h p ∂e.prod μ)-(∫ p,h p ∂μ.prod μ))-
      (1/2:ℝ)*((∫ p in {p : E×E|p.1≠p.2},h p ∂e.prod e)-(∫ p,h p ∂μ.prod μ)) =
      -(1/2:ℝ)*sourceTransportEnergy μ h N x
  change (∫ p in {p : E×E|p.1≠p.2},h p ∂e.prod e)-(∫ p,h p ∂μ.prod μ) =
      2*((∫ p,h p ∂e.prod μ)-(∫ p,h p ∂μ.prod μ))+sourceTransportEnergy μ h N x at he
  rw [he]
  ring
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLog_backward_adjoint_drift
#print axioms DGRHS.Dynamics.sourceLog_backward_adjoint_drift
