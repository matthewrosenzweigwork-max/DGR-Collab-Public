import DGRHS.Commutator.SourceLogStaticWeakForm
import DGRHS.Commutator.SourceBoundedC2Spatial
import DGRHS.Commutator.SourceLogCutoffIntegral
import DGRHS.Dynamics.SourceAdjointHessianLipschitz

/-! Frozen bounded-C2 tests have proper logarithmic generators. Continuity
under the actual probability law follows from the checked cutoff estimate,
not from diagonal continuity or an assumed moving-test equation. The density
bound is uniform in law time. The source's positive-dimensional domain is
retained in the continuity theorem; physical beta positivity is imposed by
the later source-facing constructor. -/
noncomputable section
open MeasureTheory Laplacian Set
open scoped NNReal Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma SourceBoundedC2Test.continuous_laplacian
    (φ : E → ℝ) (hφ : SourceBoundedC2Test φ) : Continuous (laplacian φ) := by
  have hH : Continuous (fun p : Unit × E => iteratedFDeriv ℝ 2 φ p.2) :=
    (hφ.1.continuous_iteratedFDeriv le_rfl).comp continuous_snd
  have hL := continuous_laplacian_of_joint_hessian
    (EuclideanSpace.basisFun ι ℝ) (fun _ : Unit => φ) hH
  have he : Continuous (fun x : E => ((),x)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using hL.comp he

lemma SourceBoundedC2Test.log_spatial_properness
    (φ : E → ℝ) (hφ : SourceBoundedC2Test φ)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    Integrable φ μ ∧ Integrable (laplacian φ) μ ∧
      Integrable (sourceLogTransportKernel 1 (gradient φ)) (μ.prod μ) := by
  obtain ⟨hc,C,hC,hb⟩ := (sourceBoundedC2Test_iff_classical_bounds φ).mp hφ
  let K : ℝ≥0 := ⟨C,hC⟩
  have hv := sourceAdjoint_gradient_lipschitz_of_hessian_bound φ hc K
    (fun x => (hb x).2.2)
  refine ⟨integrable_of_abs_bound μ hc.continuous.measurable (fun x => (hb x).1),
    integrable_of_abs_bound μ (hφ.continuous_laplacian φ).measurable
      (source_laplacian_bound_of_hessian (EuclideanSpace.basisFun ι ℝ) φ C
        (fun x => (hb x).2.2)),
    integrable_of_abs_bound (μ.prod μ) (measurable_sourceLogTransportKernel_one hv)
      (abs_sourceLogTransportKernel_one_le hv)⟩

section Continuity
variable [Nonempty ι] {P : Type*} [MetricSpace P] [SecondCountableTopology P]

lemma SourceBoundedC2Test.continuous_log_static_generator_probability
    (φ : E → ℝ) (hφ : SourceBoundedC2Test φ) (β : ℝ)
    (μ : P → ProbabilityMeasure E) (hμ : Continuous μ)
    (ρ : P → E → ℝ)
    (hρμ : ∀ a, (μ a : Measure E) = gaussianRieszDensityMeasure (ρ a))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ a, ∀ᵐ x ∂volume, ρ a x ≤ M) :
    Continuous (fun a => sourceLogStaticMeanTestDrift β (ρ a) φ) := by
  obtain ⟨hc,C,hC,hb⟩ := (sourceBoundedC2Test_iff_classical_bounds φ).mp hφ
  let K : ℝ≥0 := ⟨C,hC⟩
  have hv := sourceAdjoint_gradient_lipschitz_of_hessian_bound φ hc K
    (fun x => (hb x).2.2)
  have hL : Continuous (fun p : Unit × E => laplacian φ p.2) :=
    (hφ.continuous_laplacian φ).comp continuous_snd
  have hLint := continuous_integral_moving_probability
    (fun _ : P => ()) continuous_const μ hμ
    (fun p : Unit × E => laplacian φ p.2) hL
    ((Fintype.card ι : ℝ) * C)
    (fun p => source_laplacian_bound_of_hessian (EuclideanSpace.basisFun ι ℝ)
      φ C (fun x => (hb x).2.2) p.2)
  have hKint := continuous_integral_sourceLogKernel_one_probability
    (fun _ : P => gradient φ) (hv.continuous.comp continuous_snd) K
    (fun _ => hv) μ hμ ρ hρμ M hM hρ
  have h : Continuous (fun a =>
      β⁻¹ * (∫ x, laplacian φ x ∂(μ a : Measure E)) -
        (1/2 : ℝ) * (∫ p, sourceLogTransportKernel 1 (gradient φ) p
          ∂(μ a : Measure E).prod (μ a : Measure E))) :=
    (continuous_const.mul hLint).sub (continuous_const.mul hKint)
  apply h.congr
  intro a
  simp only [sourceLogStaticMeanTestDrift, hρμ a]

end Continuity
end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceBoundedC2Test.continuous_laplacian
#print axioms DGRHS.Commutator.SourceBoundedC2Test.continuous_laplacian
#check @DGRHS.Commutator.SourceBoundedC2Test.log_spatial_properness
#print axioms DGRHS.Commutator.SourceBoundedC2Test.log_spatial_properness
#check @DGRHS.Commutator.SourceBoundedC2Test.continuous_log_static_generator_probability
#print axioms DGRHS.Commutator.SourceBoundedC2Test.continuous_log_static_generator_probability
