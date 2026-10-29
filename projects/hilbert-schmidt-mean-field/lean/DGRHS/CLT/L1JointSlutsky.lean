/- Source one-body average joined to an actual changing-domain particle CLT.
The untilted joint limit is an input to this general composition adapter; paper
factories below supply it from the checked kernel CLT. Only proper L1 F is used. -/
import DGRHS.CLT.L1EmpiricalAverage
import DGRHS.CLT.LawPullback
import DGRHS.CLT.ProductTransport
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace DGRHS.CLT
variable {S E Ω' : Type*} [MeasurableSpace S] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [IsProbabilityMeasure μ] {ν : Measure Ω'} [IsProbabilityMeasure ν]

lemma finite_iid_average_aemeasurable (F : S → ℝ) (hi : Integrable F μ) (N : ℕ) :
    AEMeasurable (fun x : Fin N → S => (N : ℝ)⁻¹*∑ i : Fin N, F (x i))
      (Measure.pi (fun _ : Fin N => μ)) := by
  apply aemeasurable_const.mul
  convert Finset.aemeasurable_sum Finset.univ
    (fun (i : Fin N) _ => ((measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable hi).aestronglyMeasurable.aemeasurable) using 1
  funext x
  simp only [Finset.sum_apply,Function.comp_apply,Function.eval]

lemma finiteParticle_joint_with_L1_average
    (X : ∀ N, (Fin N → S) → E) (Z : Ω' → E)
    (hweak : TendstoInDistribution X atTop Z
      (fun N => Measure.pi (fun _ : Fin N => μ)) ν)
    (F : S → ℝ) (hi : Integrable F μ) :
    TendstoInDistribution
      (fun N (x : Fin N → S) => (X N x,(N : ℝ)⁻¹*∑ i : Fin N, F (x i))) atTop
      (fun ω => (Z ω,∫ x, F x ∂μ))
      (fun N => Measure.pi (fun _ : Fin N => μ)) ν := by
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  let samplePrefix : ∀ N, (ℕ → S) → (Fin N → S) := fun N ω i => ω i
  have hx := tendstoInDistribution_pullback_source X Z samplePrefix
    (prefixSample_measurePreserving μ) hweak
  have hy := tendstoInMeasure_iid_average_L1 μ F hi
  have hym : ∀ N : ℕ, AEMeasurable
      (fun ω : ℕ → S => (N : ℝ)⁻¹*∑ i ∈ Finset.range N, F (ω i)) P := by
    intro N
    apply aemeasurable_const.mul
    convert Finset.aemeasurable_sum (Finset.range N)
      (fun i _ => ((measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i).integrable_comp_of_integrable hi).aestronglyMeasurable.aemeasurable) using 1
    funext ω
    simp only [Finset.sum_apply,Function.comp_apply,Function.eval]
  have hj := hx.prodMk_of_tendstoInMeasure_const
    (fun N => X N ∘ samplePrefix N)
    (fun (N : ℕ) (ω : ℕ → S) => (N : ℝ)⁻¹*∑ i ∈ Finset.range N, F (ω i)) Z hy hym
  apply tendstoInDistribution_transport_source
    (f := samplePrefix) (hf := prefixSample_measurePreserving μ)
  · intro N
    exact (hweak.forall_aemeasurable N).prodMk (finite_iid_average_aemeasurable F hi N)
  · convert hj using 1
    funext N ω
    simp only [Function.comp_apply,Finset.sum_range,samplePrefix]
end DGRHS.CLT
#print axioms DGRHS.CLT.finite_iid_average_aemeasurable
#print axioms DGRHS.CLT.finiteParticle_joint_with_L1_average
#check @DGRHS.CLT.finiteParticle_joint_with_L1_average
