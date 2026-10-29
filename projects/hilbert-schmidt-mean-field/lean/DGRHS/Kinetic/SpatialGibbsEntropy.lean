import DGRHS.Kinetic.SpatialTensorization
import DGRHS.Entropy.GibbsEntropicTransfer

/-! The actual entropy-plus-spatial-energy estimate on a joint phase-space
law. The joint competitor may correlate positions and velocities. Its proper
energy, base entropy and observable are derived from finite full Gibbs KL. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Kinetic
variable {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]

theorem spatial_gibbs_entropic_transfer (μ : Measure X) (η : Measure V)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (ν : Measure (X × V)) [IsProbabilityMeasure ν]
    (E : X → ℝ) (hE : Measurable E) (L β : ℝ) (hβ : 0 < β)
    (hL : ∀ x, L ≤ E x) (hZ : Integrable (fun x => Real.exp (-β*E x)) μ)
    (a : X → ℝ) (ha : StronglyMeasurable a) (ε : ℝ) (hε : 0 < ε)
    (hp : Integrable (fun x => Real.exp (ε*a x)) (μ.tilted (fun x => -β*E x)))
    (hm : Integrable (fun x => Real.exp (-(ε*a x))) (μ.tilted (fun x => -β*E x)))
    (hKL : klDiv ν ((μ.tilted (fun x => -β*E x)).prod η) ≠ ∞)
    (Cpf Cem : ℝ) (hCpf : (∫ x, Real.exp (-β*E x) ∂μ) ≤ Cpf)
    (hCp : (∫ x, Real.exp (ε*a x) ∂μ.tilted (fun x => -β*E x)) ≤ Cem)
    (hCm : (∫ x, Real.exp (-(ε*a x)) ∂μ.tilted (fun x => -β*E x)) ≤ Cem) :
    ν ≪ μ.prod η ∧ Integrable (fun z => E z.1) ν ∧
      Integrable (llr ν (μ.prod η)) ν ∧ Integrable (fun z => a z.1) ν ∧
      |∫ z, a z.1 ∂ν| ≤ ε⁻¹*((klDiv ν (μ.prod η)).toReal + β*(∫ z, E z.1 ∂ν)) +
        ε⁻¹*(Real.log Cpf + Real.log Cem) := by
  have ht := spatial_gibbs_tensor μ η (fun x => -β*E x) (hE.const_mul _)
  have hp' : Integrable (fun z : X × V => Real.exp (ε*a z.1))
      ((μ.prod η).tilted (fun z => -β*E z.1)) := by
    rw [ht]
    exact hp.comp_fst η
  have hm' : Integrable (fun z : X × V => Real.exp (-(ε*a z.1)))
      ((μ.prod η).tilted (fun z => -β*E z.1)) := by
    rw [ht]
    exact hm.comp_fst η
  have hCp' : (∫ z : X × V, Real.exp (ε*a z.1)
      ∂(μ.prod η).tilted (fun z => -β*E z.1)) ≤ Cem := by
    rw [ht]
    rw [integral_fun_fst (μ := μ.tilted (fun x => -β*E x)) (ν := η)
      (fun x => Real.exp (ε*a x)), probReal_univ, one_smul]
    exact hCp
  have hCm' : (∫ z : X × V, Real.exp (-(ε*a z.1))
      ∂(μ.prod η).tilted (fun z => -β*E z.1)) ≤ Cem := by
    rw [ht]
    rw [integral_fun_fst (μ := μ.tilted (fun x => -β*E x)) (ν := η)
      (fun x => Real.exp (-(ε*a x))), probReal_univ, one_smul]
    exact hCm
  apply DGRHS.Entropy.gibbs_entropic_transfer (μ.prod η) ν (fun z => E z.1)
    L β hβ (fun z => hL z.1) (hZ.comp_fst η) (fun z => a z.1)
    (ha.comp_measurable measurable_fst) ε hε hp' hm' (by simpa only [ht] using hKL)
    Cpf Cem _ hCp' hCm'
  simpa only [spatial_partition_tensor μ η (fun x => -β*E x)] using hCpf

end DGRHS.Kinetic
#check @DGRHS.Kinetic.spatial_gibbs_entropic_transfer
#print axioms DGRHS.Kinetic.spatial_gibbs_entropic_transfer
