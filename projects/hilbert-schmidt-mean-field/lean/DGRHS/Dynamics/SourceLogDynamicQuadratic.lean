/- Actual source eq:dynamicQuadraticExpansion, logarithmic branch.
All probability integrals are proper and diagonal exclusion is justified
by the actual collision-zero derivative contraction. -/
import DGRHS.Commutator.SourceLogTransportAllLaws
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Dynamics
open DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem sourceLog_dynamic_quadratic_expansion
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0<N) (x : Fin N→E) :
    let e := transportEmpiricalLaw N x
    let h := sourceLogTransportKernel 1 v
    Integrable h (e.prod e) ∧ Integrable h (e.prod μ) ∧
    Integrable h (μ.prod e) ∧ Integrable h (μ.prod μ) ∧
    (∫ p in {p : E×E|p.1≠p.2},h p ∂e.prod e)-(∫ p,h p ∂μ.prod μ) =
      2*((∫ p,h p ∂e.prod μ)-(∫ p,h p ∂μ.prod μ))+
        sourceTransportEnergy μ h N x := by
  let e := transportEmpiricalLaw N x
  let h := sourceLogTransportKernel 1 v
  letI := transportEmpiricalLaw_probability hN x
  have h1 := integrable_sourceLogTransport_kernel_pair 1 (by omega) hv e e
  have h2 := integrable_sourceLogTransport_kernel_pair 1 (by omega) hv e μ
  have h3 := integrable_sourceLogTransport_kernel_pair 1 (by omega) hv μ e
  have h4 := integrable_sourceLogTransport_kernel_pair 1 (by omega) hv μ μ
  refine ⟨h1,h2,h3,h4,?_⟩
  have hs : (∫ p,h p ∂μ.prod e)=(∫ p,h p ∂e.prod μ) := by
    rw [←integral_prod_swap]
    congr 1
    funext p
    exact sourceLogTransportKernel_swap 1 v p
  have ha := sourceLogTransportEnergy_offCollision 1 (by omega) hv μ N hN x
  simp_rw [integral_restrict_offCollision] at ha ⊢
  rw [ha,hs]
  ring
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLog_dynamic_quadratic_expansion
#print axioms DGRHS.Dynamics.sourceLog_dynamic_quadratic_expansion
