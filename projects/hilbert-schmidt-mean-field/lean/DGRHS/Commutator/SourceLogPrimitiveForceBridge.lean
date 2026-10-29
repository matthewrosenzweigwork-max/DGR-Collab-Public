import DGRHS.Commutator.SourceRieszPrimitiveDynamics
import DGRHS.Commutator.SourceRieszClassicalBackwardInterface
import DGRHS.Dynamics.SourceLogAdjointPhysicalDrift
import DGRHS.Commutator.SourceLogCovarianceReplacement

/-! Logarithmic specialization of the checked Brownian infrastructure.
The force at exponent zero equals the actual logarithmic force, including its
zero collision representative. This does not specialize the Riesz potential,
transport kernel or Gibbs law at zero. Native logarithmic gradient and canceled
transport identities are used separately. The source primitive Itô assumption
contains the actual logarithmic empirical drift and actual Brownian integral.
This new body has no compiler verdict until its restricted diagnostics exist. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι Ω : Type*} [Fintype ι] [mΩ : MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszForce_zero_eq_logForce (z : E) :
    sourceRieszForce 0 z=sourceLogForce z := by
  simp [sourceRieszForce,sourceLogForce,Real.rpow_neg (norm_nonneg z)]

lemma sourceRieszLocalEmpiricalLaw_eq_transport (N : ℕ) (x : Fin N→E) :
    sourceRieszLocalEmpiricalLaw N x=transportEmpiricalLaw N x := rfl

lemma sourceRieszDynamicEmpiricalDifference_eq_log (ρ q : E→ℝ) (N : ℕ) (x : Fin N→E) :
    sourceRieszDynamicEmpiricalDifference ρ q N x=sourceLogDynamicEmpiricalDifference ρ q N x := rfl

lemma sourceRieszEmpiricalTestDrift_zero_eq_log
    (β : ℝ) (q : ℝ→E→ℝ) (N : ℕ) (r : ℝ) (x : Fin N→E) :
    sourceRieszEmpiricalTestDrift 0 β q N r x=sourceLogEmpiricalTestDrift β q N r x := by
  unfold sourceRieszEmpiricalTestDrift sourceLogEmpiricalTestDrift
  simp_rw [sourceRieszForce_zero_eq_logForce]
  rfl

lemma sourceLogForce_eq_gradient {z : E} (hz : z≠0) :
    sourceLogForce z=gradient sourceLogPotential z := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [gradient,(InnerProductSpace.toDual ℝ E).apply_symm_apply]
  ext w
  exact sourceLogForce_fderiv hz w

lemma sourceLogParticleSDEDrift_eq_physical
    (N : ℕ) (x : Fin N→E) (hx : ∀ i j:Fin N,i≠j → x i≠x j) (i : Fin N) :
    sourceRieszParticleSDEDrift 0 N x i=
      -((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,gradient sourceLogPotential (x i-x j) := by
  classical
  unfold sourceRieszParticleSDEDrift
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [sourceRieszForce_zero_eq_logForce]
  exact sourceLogForce_eq_gradient (sub_ne_zero.mpr (hx i j (Finset.mem_erase.mp hj).1.symm))

lemma SourceRieszClassicalBackwardSolution.zero_backward_log_ae
    (β : ℝ) (ρ : ℝ→E→ℝ) (t : ℝ≥0) (φ : E→ℝ) (f : ℝ→E→ℝ)
    (h : SourceRieszClassicalBackwardSolution 0 β ρ t φ f) :
    ∀ᵐ r ∂volume.restrict (Ioc 0 (t:ℝ)),∀ z,
      deriv (fun u=>f u z) r+β⁻¹*Laplacian.laplacian (f r) z=
        ∫ y,sourceLogTransportKernel 1 (gradient (f r)) (z,y)
          ∂gaussianRieszDensityMeasure (ρ r) := by
  have hb := h.backward_ae 0 β ρ t φ f
  simpa only [sourceRieszForce_zero_eq_logForce,←sourceLogTransportKernel_force] using hb

/-- The literal logarithmic primitive empirical Itô identity authorized by
source865(i)/1046. Its stochastic term is the checked actual driver integral. -/
def SourceLogPrimitiveEmpiricalIto
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) : Prop :=
  ∀ a,∀ r : ℝ≥0,r≤t a → ∀ᵐ ω ∂P,
    (∫ z,f a r z ∂transportEmpiricalLaw N (X r ω))-
      (∫ z,f a 0 z ∂transportEmpiricalLaw N (X 0 ω))=
      (∫ u in Ioc 0 (r:ℝ),sourceLogEmpiricalTestDrift β (f a) N u (X u ω))+
        sourceRieszBrownianFamilyProcess P F B T (g a) r ω/Real.sqrt N

lemma sourceLogPrimitiveEmpiricalIto_iff_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    SourceLogPrimitiveEmpiricalIto P F T β N k t f X B g ↔
      SourceRieszPrimitiveEmpiricalIto P F T 0 β N k t f X B g := by
  unfold SourceLogPrimitiveEmpiricalIto SourceRieszPrimitiveEmpiricalIto
  simp_rw [sourceRieszLocalEmpiricalLaw_eq_transport,sourceRieszEmpiricalTestDrift_zero_eq_log]

lemma sourceLog_primitive_empirical_Ito_normalized_version
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (hN : 0<N) (t : Fin k→ℝ≥0) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (hIto : SourceLogPrimitiveEmpiricalIto P F T β N k t f X B g)
    (m : Fin k→ℝ→Ω→ℝ)
    (hme : ∀ᵐ ω ∂P,∀ (a : Fin k) (r : ℝ≥0),Real.sqrt N*m a r ω=
      sourceRieszBrownianFamilyProcess P F B T (g a) r ω) :
    ∀ a,∀ r : ℝ≥0,r≤t a → ∀ᵐ ω ∂P,
      (∫ z,f a r z ∂transportEmpiricalLaw N (X r ω))-
        (∫ z,f a 0 z ∂transportEmpiricalLaw N (X 0 ω))=
        (∫ u in Ioc 0 (r:ℝ),sourceLogEmpiricalTestDrift β (f a) N u (X u ω))+m a r ω := by
  have h := sourceRiesz_primitive_empirical_Ito_normalized_version P F T 0 β N k hN t f X B g
    ((sourceLogPrimitiveEmpiricalIto_iff_zero P F T β N k t f X B g).mp hIto) m hme
  simpa only [sourceRieszLocalEmpiricalLaw_eq_transport,sourceRieszEmpiricalTestDrift_zero_eq_log] using h

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceRieszForce_zero_eq_logForce
#print axioms DGRHS.Commutator.sourceRieszForce_zero_eq_logForce
#check @DGRHS.Commutator.sourceRieszLocalEmpiricalLaw_eq_transport
#print axioms DGRHS.Commutator.sourceRieszLocalEmpiricalLaw_eq_transport
#check @DGRHS.Commutator.sourceRieszDynamicEmpiricalDifference_eq_log
#print axioms DGRHS.Commutator.sourceRieszDynamicEmpiricalDifference_eq_log
#check @DGRHS.Commutator.sourceRieszEmpiricalTestDrift_zero_eq_log
#print axioms DGRHS.Commutator.sourceRieszEmpiricalTestDrift_zero_eq_log
#check @DGRHS.Commutator.sourceLogForce_eq_gradient
#print axioms DGRHS.Commutator.sourceLogForce_eq_gradient
#check @DGRHS.Commutator.sourceLogParticleSDEDrift_eq_physical
#print axioms DGRHS.Commutator.sourceLogParticleSDEDrift_eq_physical
#check @DGRHS.Commutator.SourceRieszClassicalBackwardSolution.zero_backward_log_ae
#print axioms DGRHS.Commutator.SourceRieszClassicalBackwardSolution.zero_backward_log_ae
#check @DGRHS.Commutator.SourceLogPrimitiveEmpiricalIto
#print axioms DGRHS.Commutator.SourceLogPrimitiveEmpiricalIto
#check @DGRHS.Commutator.sourceLogPrimitiveEmpiricalIto_iff_zero
#print axioms DGRHS.Commutator.sourceLogPrimitiveEmpiricalIto_iff_zero
#check @DGRHS.Commutator.sourceLog_primitive_empirical_Ito_normalized_version
#print axioms DGRHS.Commutator.sourceLog_primitive_empirical_Ito_normalized_version
