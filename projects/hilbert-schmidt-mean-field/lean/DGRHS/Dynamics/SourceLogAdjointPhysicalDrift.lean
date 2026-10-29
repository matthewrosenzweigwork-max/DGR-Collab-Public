/- Source dynamicItoEmpirical / dynamicMeanFieldWeakIdentity with the
actual time derivative, native Laplacian and native gradient.  The original
backward equation and Hessian bound derive cancellation and proper bounds. -/
import DGRHS.Dynamics.SourceAdjointHessianLipschitz
import DGRHS.Dynamics.SourceLogAdjointDrift
import DGRHS.Dynamics.SourceLogDynamicForceEmpirical
import Mathlib.Analysis.InnerProductSpace.Laplacian
noncomputable section
open MeasureTheory Laplacian
open scoped BigOperators NNReal RealInnerProductSpace
namespace DGRHS.Dynamics
open DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def sourceLogEmpiricalTestDrift (β : ℝ) (q : ℝ→E→ℝ) (N : ℕ)
    (r : ℝ) (x : Fin N→E) : ℝ :=
  (∫ z,deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z) ∂transportEmpiricalLaw N x)-
    ((N:ℝ)^2)⁻¹*(∑ i : Fin N,∑ j : Fin N,
      ⟪sourceLogForce (x i-x j),gradient (q r) (x i)⟫)

def sourceLogMeanTestDrift (β : ℝ) (q : ℝ→E→ℝ) (r : ℝ) (μ : Measure E) : ℝ :=
  (∫ z,deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z) ∂μ)-
    (1/2:ℝ)*(∫ p,sourceLogTransportKernel 1 (gradient (q r)) p ∂μ.prod μ)

theorem sourceLog_adjoint_physical_drift (β : ℝ) (q : ℝ→E→ℝ) (r : ℝ)
    (hq : ContDiff ℝ 2 (q r)) (K : ℝ≥0)
    (hK : ∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hback : ∀ z,deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z)=
      ∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y) ∂μ)
    (N : ℕ) (hN : 0<N) (x : Fin N→E) :
    Integrable (fun z=>deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z)) (transportEmpiricalLaw N x) ∧
    Integrable (fun z=>deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z)) μ ∧
    sourceLogEmpiricalTestDrift β q N r x-sourceLogMeanTestDrift β q r μ =
      -(1/2:ℝ)*sourceTransportEnergy μ (sourceLogTransportKernel 1 (gradient (q r))) N x ∧
    |sourceLogEmpiricalTestDrift β q N r x|≤(3/2:ℝ)*(K:ℝ) ∧
    |sourceLogMeanTestDrift β q r μ|≤(3/2:ℝ)*(K:ℝ) := by
  have hv := sourceAdjoint_gradient_lipschitz_of_hessian_bound (q r) hq K hK
  let e := transportEmpiricalLaw N x
  let h := sourceLogTransportKernel 1 (gradient (q r))
  let g := fun z=>deriv (fun t=>q t z) r+β⁻¹*(laplacian (q r) z)
  letI := transportEmpiricalLaw_probability hN x
  obtain ⟨hi1,hi2,he⟩ := sourceLog_backward_adjoint_drift β hv μ
    (fun z=>deriv (fun t=>q t z) r) (laplacian (q r)) hback N hN x
  have hm : Measurable h := measurable_sourceLogTransportKernel_one hv
  have hb : ∀ p,|h p|≤(K:ℝ) := abs_sourceLogTransportKernel_one_le hv
  have hg : g=(fun z=>∫ y,h (z,y) ∂μ) := funext hback
  have hgm : Measurable g := by rw [hg];exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hgb (z : E) : |g z|≤(K:ℝ) := by
    rw [hg]
    exact abs_integral_le_bound μ (hm.comp (measurable_const.prodMk measurable_id)) (fun y=>hb (z,y))
  have hbe := abs_integral_le_bound e hgm hgb
  have hbm := abs_integral_le_bound μ hgm hgb
  have hbpe := abs_integral_le_bound (e.prod e) hm hb
  have hbpm := abs_integral_le_bound (μ.prod μ) hm hb
  have hf := (sourceLog_dynamic_drift_empirical hv N hN x).2
  rw [integral_restrict_offCollision] at hf he
  refine ⟨hi1,hi2,?_,?_,?_⟩
  · unfold sourceLogEmpiricalTestDrift sourceLogMeanTestDrift
    rw [hf]
    linarith
  · unfold sourceLogEmpiricalTestDrift
    rw [hf]
    have ht := abs_sub (∫ z,g z ∂e) ((1/2:ℝ)*(∫ p,h p ∂e.prod e))
    rw [abs_mul] at ht
    norm_num at ht
    dsimp only [g,e,h] at hbe hbpe ht
    linarith
  · unfold sourceLogMeanTestDrift
    have ht := abs_sub (∫ z,g z ∂μ) ((1/2:ℝ)*(∫ p,h p ∂μ.prod μ))
    rw [abs_mul] at ht
    norm_num at ht
    dsimp only [g,h] at hbm hbpm ht
    linarith
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLog_adjoint_physical_drift
#print axioms DGRHS.Dynamics.sourceLogEmpiricalTestDrift
#print axioms DGRHS.Dynamics.sourceLogMeanTestDrift
#print axioms DGRHS.Dynamics.sourceLog_adjoint_physical_drift
