import DGRHS.Commutator.SourceLogClassicalBackwardInterface
import DGRHS.Commutator.SourceLogMeanFieldTestEvolution
import DGRHS.Commutator.SourceLogTransportEmpirical

/-! Records-only draft. Actual logarithmic classical backward test support.
Only the checked force-zero equality is reused. Logarithmic spatial properness
follows directly from canceled bounded transport, with no uncanceled force
integrability assumption. The original weak-PDE adapter remains separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def SourceLogMeanFieldClassicalTested
    (T : ℝ≥0) (β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ)) : Prop :=
  ∀ t:ℝ≥0,t≤T → ∀ φ:E→ℝ,φ∈D → ∀ f:ℝ→E→ℝ,
    SourceLogClassicalBackwardSolution β ρ t φ f →
      SourceLogMeanFieldTestEvolution β (t:ℝ) ρ f

/-- Properness uses the actual canceled logarithmic kernel, on every time
slice including both endpoints. No separate singular convolution is needed. -/
theorem SourceLogClassicalBackwardSolution.spatial_properness
    (β : ℝ) (t : ℝ≥0) (ρ : ℝ→E→ℝ)
    (hprob : ∀ r∈Icc 0 (t:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (φ : E→ℝ) (f : ℝ→E→ℝ)
    (h : SourceLogClassicalBackwardSolution β ρ t φ f) :
    (∀ r∈Icc 0 (t:ℝ),
      Integrable (f r) (gaussianRieszDensityMeasure (ρ r)) ∧
      (∀ z,Integrable (fun y=>sourceLogTransportKernel 1 (gradient (f r)) (z,y))
        (gaussianRieszDensityMeasure (ρ r))) ∧
      Integrable (sourceLogTransportKernel 1 (gradient (f r)))
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) ∧
    ∀ᵐ r ∂volume.restrict (Ioc 0 (t:ℝ)),
      Integrable (fun z=>deriv (fun u=>f u z) r+β⁻¹*laplacian (f r) z)
        (gaussianRieszDensityMeasure (ρ r)) := by
  obtain ⟨C,hC,hb⟩ := h.bounded
  let K : ℝ≥0 := ⟨C,hC⟩
  have hspace : ∀ r∈Icc 0 (t:ℝ),
      Integrable (f r) (gaussianRieszDensityMeasure (ρ r)) ∧
      (∀ z,Integrable (fun y=>sourceLogTransportKernel 1 (gradient (f r)) (z,y))
        (gaussianRieszDensityMeasure (ρ r))) ∧
      Integrable (sourceLogTransportKernel 1 (gradient (f r)))
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r))) := by
    intro r hr
    letI := hprob r hr
    have hg := sourceAdjoint_gradient_lipschitz_of_hessian_bound (f r)
      (h.spatial_contdiff r hr) K (fun z=>(hb r hr z).2.2)
    refine ⟨?_,?_,integrable_sourceLogTransport_kernel_pair 1 (by omega) hg _ _⟩
    · apply (integrable_const C).mono' (h.spatial_contdiff r hr).continuous.measurable.aestronglyMeasurable
      exact ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using (hb r hr z).1)
    · intro z
      exact integrable_of_abs_bound (gaussianRieszDensityMeasure (ρ r))
        ((measurable_sourceLogTransportKernel_one hg).comp (measurable_const.prodMk measurable_id))
        (fun y=>abs_sourceLogTransportKernel_one_le hg (z,y))
  refine ⟨hspace,?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc,h.backward_ae β ρ t φ f] with r hr hback
  letI := hprob r ⟨hr.1.le,hr.2⟩
  have he : (fun z=>deriv (fun u=>f u z) r+β⁻¹*laplacian (f r) z)=
      (fun z=>∫ y,sourceLogTransportKernel 1 (gradient (f r)) (z,y)
        ∂gaussianRieszDensityMeasure (ρ r)) := funext hback
  rw [he]
  exact ((hspace r ⟨hr.1.le,hr.2⟩).2.2).integral_prod_left

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceLogMeanFieldClassicalTested
#print axioms DGRHS.Commutator.SourceLogMeanFieldClassicalTested
#check @DGRHS.Commutator.SourceLogClassicalBackwardSolution.spatial_properness
#print axioms DGRHS.Commutator.SourceLogClassicalBackwardSolution.spatial_properness
