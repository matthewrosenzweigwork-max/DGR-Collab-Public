/- Source dynamicSymmetrization with the true atomic empirical law.
Repeated spatial coordinates and the physical zero collision representative
are retained, with actual proper derivative-kernel integrals. -/
import DGRHS.Dynamics.SourceLogForceSymmetry
import DGRHS.Commutator.SourceLogTransportEmpirical
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace
namespace DGRHS.Dynamics
open DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem sourceLog_dynamic_drift_empirical
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (N : ℕ) (hN : 0<N) (x : Fin N→E) :
    Integrable (sourceLogTransportKernel 1 v)
      ((transportEmpiricalLaw N x).prod (transportEmpiricalLaw N x)) ∧
    ((N:ℝ)^2)⁻¹*(∑ i : Fin N,∑ j : Fin N,⟪sourceLogForce (x i-x j),v (x i)⟫) =
      (1/2:ℝ)*(∫ p in {p : E×E|p.1≠p.2},sourceLogTransportKernel 1 v p
        ∂(transportEmpiricalLaw N x).prod (transportEmpiricalLaw N x)) := by
  letI := transportEmpiricalLaw_probability hN x
  refine ⟨integrable_sourceLogTransport_kernel_pair 1 (by omega) hv _ _,?_⟩
  rw [integral_restrict_offCollision,
    integral_transportEmpirical_square (sourceLogTransportKernel 1 v)
      (measurable_sourceLogTransportKernel_one hv) (K:ℝ) (abs_sourceLogTransportKernel_one_le hv) N hN x,
    sourceLog_dynamic_force_symmetrization]
  ring
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLog_dynamic_drift_empirical
#print axioms DGRHS.Dynamics.sourceLog_dynamic_drift_empirical
